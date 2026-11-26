// L2260 tight component case (k,r)=(6,5), no SAT solver.
// See graph_partition_v2.md for soundness of the relaxations.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <set>
#include <tuple>
#include <unordered_map>
#include <vector>
using namespace std;

constexpr int N=11,E=16,M=1<<E,RAW=(1<<N)-1,J0=1<<N,J1=1<<(N+1);
constexpr int ed[E][2]={{0,9},{0,10},{1,4},{1,8},{2,5},{2,10},
    {3,6},{3,7},{4,8},{4,10},{5,8},{5,9},{6,7},{6,10},{7,9},{8,9}};
int cover[M],inc[N],p[N],groups[N*N],blocks[N],lb[M];
uint64_t truth[1<<N],negmask;
long long pairs=0,passmerge=0,passcover=0;
int countp=0,survive=0,types[3]={};
int pc(int x){return __builtin_popcount((unsigned)x);}

int cross(int A,int B){
    int z=0;
    for(int e=0;e<E;e++){
        int a=1<<ed[e][0],b=1<<ed[e][1];
        if(((A&a)&&(B&b))||((A&b)&&(B&a)))z|=1<<e;
    }
    return z;
}
int merge_mask(int A,int B){return cross(A&~B,B&~A);}

struct Sup{int mask,block,single;uint64_t val;};

// All nonempty symbolic supports inside one component, bounded by
// the number of original vertices in that component. An isolated
// singleton-free junk atom is a separate singleton support.
vector<Sup> supports(int b,int j0block=-2,uint64_t j0val=0,int s0=0,
                     int j1block=-2,uint64_t j1val=0,int s1=0){
    vector<Sup> v;
    for(int a=0;a<b;a++){
        int m=blocks[a]|(j0block==a?J0:0)|(j1block==a?J1:0);
        for(int s=m;s;s=(s-1)&m){
            if(pc(s)>pc(blocks[a]))continue;
            v.push_back({s,a,(s&RAW)|(s&J0?s0:0)|(s&J1?s1:0),
                truth[s&RAW]|(s&J0?j0val:0)|(s&J1?j1val:0)});
        }
    }
    if(j0block==-1)v.push_back({J0,b,0,j0val});
    if(j1block==-1)v.push_back({J1,b+1,0,j1val});
    return v;
}

// Relaxed top cover: fix one allowed operand A, then take the
// union of ALL atoms compatible with A in each possible B component.
// This only enlarges the cover choices, ignoring shared OR costs,
// B's size bound, antichain minimality, and mandatory junk readers.
bool top_cover(int k,int b,int a0,uint64_t t0,int s0,
               int a1,uint64_t t1,int s1){
    auto v=supports(b,a0,t0,s0,a1,t1,s1);
    int all=0;
    vector<int> masks;
    vector<Sup> atoms;
    for(auto A:v)if(pc(A.mask)==1)atoms.push_back(A);
    for(auto A:v){
        uint64_t val[N+2]={};
        for(auto B:atoms)if(!(A.val&B.val&negmask))val[B.block]|=B.val;
        for(int j=0;j<b+2;j++){
            int m=(A.val&val[j])&(M-1);
            if(m){all|=m;masks.push_back(m);}
        }
    }
    if(all!=M-1)return false;
    sort(masks.begin(),masks.end());
    masks.erase(unique(masks.begin(),masks.end()),masks.end());
    vector<int> maximal;
    for(int m:masks){
        bool dom=false;
        for(int q:masks)if(m!=q&&(m&q)==m){dom=true;break;}
        if(!dom)maximal.push_back(m);
    }
    vector<int> lists[E];
    for(int m:maximal)for(int e=0;e<E;e++)if(m>>e&1)lists[e].push_back(m);
    unordered_map<int,int> memo;
    function<int(int)> solve=[&](int rem){
        if(!rem)return 0;
        auto it=memo.find(rem);
        if(it!=memo.end())return it->second;
        int e=-1;
        for(int i=0;i<E;i++)if(rem>>i&1&&(e<0||lists[i].size()<lists[e].size()))e=i;
        int best=99;
        for(int m:lists[e])best=min(best,1+solve(rem&~m));
        return memo[rem]=best;
    };
    return solve(M-1)<=k;
}

bool check(int k,int b){
    auto raw=supports(b);
    bool ok[3]={};
    set<tuple<int,uint64_t,int>> seen0;
    set<tuple<int,uint64_t,int,int,uint64_t,int>> seen1;
    for(auto A:raw)for(auto B:raw){
        if(A.mask>=B.mask||!(A.mask&~B.mask)||!(B.mask&~A.mask))continue;
        auto t0=A.val&B.val;
        if(!(t0&negmask))continue;
        int s0=A.single&B.single,a0=s0?A.block:-1;
        int m0=merge_mask(A.single,B.single);
        // For J0, m0 is exactly the pair-true / both-singletons-false
        // edge mask, hence determined by t0 and s0.
        if(!seen0.emplace(a0,t0,s0).second)continue;
        if(!s0&&1+lb[m0]>k)continue;
        auto ext=supports(b,a0,t0,s0);
        for(auto X:ext){
            if(!(X.mask&J0))continue;
            for(auto Y:ext){
                if(!(X.mask&~Y.mask)||!(Y.mask&~X.mask))continue;
                if((Y.mask&J0)&&X.mask>=Y.mask)continue;
                auto t1=X.val&Y.val;
                if(!(t1&negmask))continue;
                int s1=X.single&Y.single,a1=s1?X.block:-1;
                int typ=!s0?0:!s1?1:2;
                pairs++;
                if(ok[typ])continue;
                int m1=merge_mask(X.single,Y.single);
                // Deleting all potential junk first merges is a
                // relaxation. The isolated J1 consumes one clean AND
                // that cannot be a first merge.
                if((s1?0:1)+lb[m0|m1]>k)continue;
                // Deduplicate only AFTER the structural edge bound.
                if(!seen1.emplace(a0,t0,s0,a1,t1,s1).second)continue;
                passmerge++;
                if(!top_cover(k,b,a0,t0,s0,a1,t1,s1))continue;
                passcover++;
                ok[typ]=true;
            }
        }
    }
    for(int i=0;i<3;i++)types[i]+=ok[i];
    return ok[0]||ok[1]||ok[2];
}

void ev(int b){
    if(b!=6)return;
    fill(groups,groups+N*N,0);
    fill(blocks,blocks+N,0);
    for(int v=0;v<N;v++)blocks[p[v]]|=1<<v;
    for(int e=0;e<E;e++){
        int a=p[ed[e][0]],d=p[ed[e][1]];
        if(a>d)swap(a,d);
        groups[a*N+d]|=1<<e;
    }
    int s=0,first=0,second=0,loop=0,incident=0;
    vector<int> gg;
    for(int j=0;j<N*N;j++){
        int t=cover[groups[j]];
        if(t)gg.push_back(groups[j]);
        s+=t;
        if(t>first){second=first;first=t;}
        else second=max(second,t);
        if(j/N==j%N)loop=max(loop,t);
    }
    for(int a=0;a<b;a++)for(int d=0;d<b;d++)if(a!=d)
        incident=max(incident,cover[groups[a*N+a]]+cover[groups[min(a,d)*N+max(a,d)]]);
    if(s-first-second>6||min({s-first+1,s-incident+1,s-loop})>6)return;
    countp++;
    for(int m=0;m<M;m++){
        lb[m]=0;
        for(int g:gg)lb[m]+=cover[g&~m];
    }
    if(check(6,b)){
        survive++;
        for(int v=0;v<N;v++)cout<<p[v];
        cout<<" survives\n";
    }
    cerr<<"[PARTITION] "<<countp<<" survivors="<<survive
        <<" pairs="<<pairs<<" merge="<<passmerge<<" cover="<<passcover<<'\n';
}
void gen(int i,int b){
    if(b>6||b+N-i<6)return;
    if(i==N){ev(b);return;}
    for(int x=0;x<=b;x++){p[i]=x;gen(i+1,max(b,x+1));}
}
int main(){
    // v1 independently establishes that b>=7 is impossible for k=6
    // and checks all subgraph vertex-cover costs by two algorithms.
    fill(cover,cover+M,N+1);
    for(int e=0;e<E;e++)for(int v:ed[e])inc[v]|=1<<e;
    for(int s=0;s<1<<N;s++){
        int m=0;
        for(int v=0;v<N;v++)if(s>>v&1)m|=inc[v];
        cover[m]=min(cover[m],pc(s));
    }
    for(int e=0;e<E;e++)for(int m=0;m<M;m++)if(!(m>>e&1))
        cover[m]=min(cover[m],cover[m|1<<e]);
    vector<int> rows;
    for(auto &e:ed)rows.push_back((1<<e[0])|(1<<e[1]));
    auto independent=[](int x){
        for(auto &e:ed)if((x>>e[0]&1)&&(x>>e[1]&1))return false;
        return true;
    };
    for(int x=0;x<=RAW;x++)if(independent(x)){
        bool maximal=true;
        for(int v=0;v<N;v++)if(!(x>>v&1)&&independent(x|1<<v))maximal=false;
        if(maximal)rows.push_back(x);
    }
    assert(rows.size()==40);
    negmask=((1ULL<<rows.size())-1)&~uint64_t(M-1);
    for(int s=0;s<=RAW;s++)for(size_t i=0;i<rows.size();i++)
        if(s&rows[i])truth[s]|=1ULL<<i;
    gen(1,1);
    cout<<"before "<<countp<<" after "<<survive<<" pairs "<<pairs
        <<" merge "<<passmerge<<" cover "<<passcover<<" types "
        <<types[0]<<" "<<types[1]<<" "<<types[2]<<'\n';
    if(countp!=69||survive!=0||pairs!=205347379||passmerge!=226281||passcover!=0){
        cerr<<"EXPECTED RESULT MISMATCH\n";return 1;
    }
    cout<<"L2260 (6,5) GRAPH CHECK OK; not Lean-certified\n";
}
