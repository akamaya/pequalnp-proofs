// L2260 (k,r)=(5,6): component slack + first merge + h6 bounds.
// Usage: executable [shard_index shard_count [first_id last_id]]
// Partition IDs are stable, one-based. No SAT solver is required.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int N=11,E=16,M=1<<E, RAW=(1<<N)-1,J0=1<<N,J1=1<<(N+1);
constexpr int ed[E][2]={{0,9},{0,10},{1,4},{1,8},{2,5},{2,10},{3,6},{3,7},{4,8},{4,10},{5,8},{5,9},{6,7},{6,10},{7,9},{8,9}};
int cover[M],inc[N],p[N],groups[N*N],blocks[N],lb[M];
uint64_t truth[1<<N],negmask;
int pc(int x){return __builtin_popcount((unsigned)x);}
int cross(int A,int B){int z=0;for(int e=0;e<E;e++){int a=1<<ed[e][0],b=1<<ed[e][1];if(((A&a)&&(B&b))||((A&b)&&(B&a)))z|=1<<e;}return z;}
uint16_t cross_table[1<<N][1<<N];
int merge_mask(int A,int B){return cross_table[A&~B][B&~A];}
struct Sup{int mask,block,single;uint64_t val;};
// Relax allocation of slack by allowing every original block to use all of it.
int slack=0;
vector<Sup> supports(int b,int a0=-2,uint64_t t0=0,int s0=0,int a1=-2,uint64_t t1=0,int s1=0){
 vector<Sup> v;
 for(int a=0;a<b+2;a++){
  int raw=a<b?blocks[a]:0;
  int m=raw|(a0==a?J0:0)|(a1==a?J1:0);
  int cap=a<b?pc(raw)+slack:pc(m);
  for(int s=m;s;s=(s-1)&m){if(pc(s)>cap)continue;
   v.push_back({s,a,(s&RAW)|(s&J0?s0:0)|(s&J1?s1:0),truth[s&RAW]|(s&J0?t0:0)|(s&J1?t1:0)});}
 }
 return v;
}
long long pairs=0,passmerge=0,passcover=0;
int countp=0,survive=0,shard=0,shards=1,examined=0,first_id=1,last_id=878;
// Relaxed edge cover. Include at least one top with a J1-containing operand.
// The other operand is enlarged to all compatible atoms in one component.
bool top_cover(int k,int b,int a0,uint64_t t0,int s0,int a1,uint64_t t1,int s1){
 auto v=supports(b,a0,t0,s0,a1,t1,s1);int all=0; vector<int> masks,withj;
 vector<Sup> atoms;for(auto A:v)if(pc(A.mask)==1)atoms.push_back(A);
 for(auto A:v){
  uint64_t val[N+2]={};int bm[N+2]={};
  for(auto B:atoms)if(!(A.val&B.val&negmask)){val[B.block]|=B.val;bm[B.block]|=B.mask;}
  for(int j=0;j<b+2;j++)if(bm[j]){
   int m=(A.val&val[j])&(M-1);if(!m)continue;all|=m;
   masks.push_back(m);if((A.mask|bm[j])&J1)withj.push_back(m);
  }
 }
 if(all!=M-1)return false;
 sort(masks.begin(),masks.end());masks.erase(unique(masks.begin(),masks.end()),masks.end());
 vector<int> maximal;for(int m:masks){bool dom=false;for(int q:masks)if(m!=q&&(m&q)==m){dom=true;break;}if(!dom)maximal.push_back(m);}
 vector<int> lists[E];for(int m:maximal)for(int e=0;e<E;e++)if(m>>e&1)lists[e].push_back(m);
 unordered_map<int,int> memo;
 function<int(int)> solve=[&](int rem){if(!rem)return 0;auto it=memo.find(rem);if(it!=memo.end())return it->second;int e=-1;for(int i=0;i<E;i++)if(rem>>i&1&&(e<0||lists[i].size()<lists[e].size()))e=i;int best=99;for(int m:lists[e])best=min(best,1+solve(rem&~m));return memo[rem]=best;};
 if(solve(M-1)>k)return false;
 for(int m:withj)if(solve((M-1)&~m)<=k-1)return true;
 return false;
}
// Nonbearing junk attached to a raw block, or two junk atoms sharing
// a junk-only component, uses one extra OR edge per such attachment.
int excess(int b,int a0,int s0,int a1,int s1){return (!s0&&a0<b)+(!s1&&a1<b)+(a0>=b&&a0==a1);}
// If an OR belongs to lambda, its output AND a raw vertex is clean.
// In a tight component forest, OR operands have disjoint supports;
// therefore both nonempty raw sides require at least two raw atoms.
bool nonlambda(Sup S){
 if(pc(S.mask)<=1)return false;
 int raw=pc(S.mask&RAW);
 if(raw==0||(slack==0&&raw<2))return true;
 for(int v=0;v<N;v++)if(!(S.val&truth[1<<v]&negmask))return false;
 return true;
}
uint64_t route_raw(uint64_t t){
 uint64_t m=0;
 for(int v=0;v<N;v++){uint64_t z=t&truth[1<<v];if(!(z&negmask))m|=z;}
 return m;
}
int raw_needed(uint64_t t0,uint64_t t1,uint64_t routed0){
 uint64_t z=t0&t1;
 return E-pc((routed0|route_raw(t1)|((z&negmask)?0:z))&(M-1));
}
bool check(int k,int b){
 auto raw=supports(b);
 // Preserve the MINIMUM forced-nonlambda count over equivalent J0
 // representations. J0's first-merge mask is determined by its
 // truth on edges and singletons, since it reads only raw supports.
 struct State{int nlam,ma,mb,m0;};
 map<tuple<int,uint64_t,int>,State> states;
 set<tuple<int,uint64_t,int,int,uint64_t,int>> seen1;
 for(auto A:raw)for(auto B:raw){
  if(A.mask>=B.mask||!(A.mask&~B.mask)||!(B.mask&~A.mask))continue;
  auto t0=A.val&B.val;if(!(t0&negmask))continue;
  int s0=A.single&B.single,m0=merge_mask(A.single,B.single),nl=nonlambda(A)+nonlambda(B);
  for(int a0=0;a0<=b;a0++){
   if(s0?(a0!=A.block):(a0<b&&slack==0))continue;
   int lo=lb[m0];
   if(a0<b)for(int j=0;j<b;j++)lo=min(lo,lb[m0|groups[min(a0,j)*N+max(a0,j)]]);
   if(lo>k)continue;
   if(a0==b&&slack==0&&lo+1>k)continue;
   auto key=make_tuple(a0,t0,s0);auto it=states.find(key);
   if(it==states.end()||nl<it->second.nlam)states[key]={nl,A.mask,B.mask,m0};
  }
 }
 for(auto [key,st]:states){
   auto [a0,t0,s0]=key;
   auto ext=supports(b,a0,t0,s0);
   uint64_t routed0=route_raw(t0);
   for(auto X:ext){if(!(X.mask&J0))continue;
    for(auto Y:ext){
     if(!(X.mask&~Y.mask)||!(Y.mask&~X.mask))continue;
     if((Y.mask&J0)&&X.mask>=Y.mask)continue;
     auto t1=X.val&Y.val;if(!(t1&negmask))continue;
     int s1=X.single&Y.single,m1=merge_mask(X.single,Y.single);
     pairs++;
     if(lb[st.m0|m1]>k)continue;
     // Distinct J0-containing roots cannot equal raw-only J0 roots.
     // Other J1 roots are deliberately omitted from the lower bound.
     int nl=st.nlam+nonlambda(X)+((Y.mask&J0)?nonlambda(Y):0);
     if(raw_needed(t0,t1,routed0)+nl>k+6)continue;
     for(int a1=0;a1<b+2;a1++){
      if(s1&&a1!=X.block)continue;
      if(excess(b,a0,s0,a1,s1)>slack)continue;
      if((a1>=b?1:0)+lb[st.m0|m1]>k)continue;
      if(!seen1.emplace(a0,t0,s0,a1,t1,s1).second)continue;
      passmerge++;
      if(!top_cover(k,b,a0,t0,s0,a1,t1,s1))continue;
      passcover++;cout<<"[RELAXED WITNESS] partition="<<countp<<" a0="<<a0<<" t0="<<t0<<" s0="<<s0<<" a1="<<a1<<" t1="<<t1<<" s1="<<s1<<" A="<<st.ma<<" B="<<st.mb<<" X="<<X.mask<<" Y="<<Y.mask<<endl;return true;
     }
    }
   }
 }
 return false;
}
void ev(int b){
 if(b<5||b>6)return;
 slack=b-5;fill(groups,groups+N*N,0);fill(blocks,blocks+N,0);
 for(int v=0;v<N;v++)blocks[p[v]]|=1<<v;
 for(int e=0;e<E;e++){int a=p[ed[e][0]],d=p[ed[e][1]];if(a>d)swap(a,d);groups[a*N+d]|=1<<e;}
 int s=0,first=0,second=0,loop=0,incident=0;vector<int> gg;
 for(int j=0;j<N*N;j++){int t=cover[groups[j]];if(t)gg.push_back(groups[j]);s+=t;if(t>first){second=first;first=t;}else second=max(second,t);if(j/N==j%N)loop=max(loop,t);}
 for(int a=0;a<b;a++)for(int d=0;d<b;d++)if(a!=d)incident=max(incident,cover[groups[a*N+a]]+cover[groups[min(a,d)*N+max(a,d)]]);
 if(s-first-second>5||(b==5&&min({s-first+1,s-incident+1,s-loop})>5))return;
 countp++;
 if(countp<first_id||countp>last_id||(countp-1)%shards!=shard)return;
 examined++;
 for(int m=0;m<M;m++){lb[m]=0;for(int g:gg)lb[m]+=cover[g&~m];}
 if(check(5,b)){survive++;for(int v=0;v<N;v++)cout<<p[v];cout<<" survives"<<endl;}
 cout<<"[PARTITION] "<<countp<<" survivors="<<survive<<" pairs="<<pairs<<" merge="<<passmerge<<" cover="<<passcover<<endl;
}
void gen(int i,int b){if(b>6||b+N-i<5)return;if(i==N){ev(b);return;}for(int x=0;x<=b;x++){p[i]=x;gen(i+1,max(b,x+1));}}
int main(int argc,char** argv){
 if(argc==3||argc==5){shard=atoi(argv[1]);shards=atoi(argv[2]);if(shards<1||shard<0||shard>=shards)return 2;
  if(argc==5){first_id=atoi(argv[3]);last_id=atoi(argv[4]);if(first_id<1||last_id<first_id||last_id>878)return 2;}}
 else if(argc!=1)return 2;
 for(int a=0;a<=RAW;a++)for(int b=0;b<=RAW;b++)cross_table[a][b]=cross(a,b);
 fill(cover,cover+M,N+1);
 for(int e=0;e<E;e++)for(int v:ed[e])inc[v]|=1<<e;
 for(int s=0;s<1<<N;s++){int m=0;for(int v=0;v<N;v++)if(s>>v&1)m|=inc[v];cover[m]=min(cover[m],pc(s));}
 for(int e=0;e<E;e++)for(int m=0;m<M;m++)if(!(m>>e&1))cover[m]=min(cover[m],cover[m|1<<e]);
 vector<int> rows;for(auto &e:ed)rows.push_back((1<<e[0])|(1<<e[1]));
 auto independent=[](int x){for(auto &e:ed)if((x>>e[0]&1)&&(x>>e[1]&1))return false;return true;};
 for(int x=0;x<=RAW;x++)if(independent(x)){bool maximal=true;for(int v=0;v<N;v++)if(!(x>>v&1)&&independent(x|1<<v))maximal=false;if(maximal)rows.push_back(x);}
 assert(rows.size()==40);
 negmask=((1ULL<<rows.size())-1)&~uint64_t(M-1);
 for(int s=0;s<=RAW;s++)for(size_t i=0;i<rows.size();i++)if(s&rows[i])truth[s]|=1ULL<<i;
 gen(1,1);
 if(countp!=878){cerr<<"partition count mismatch\n";return 1;}
 cout<<"before "<<countp<<" examined "<<examined<<" after "<<survive<<" pairs "<<pairs<<" merge "<<passmerge<<" cover "<<passcover<<endl;
}
