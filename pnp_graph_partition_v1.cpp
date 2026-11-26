// L2260: finite graph-only quotient bound. No SAT library required.
// See graph_partition_v1.md for the first-merge and equality-case arguments.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
using namespace std;
constexpr int N=11,E=16,M=1<<E;
constexpr int edges[E][2]={{0,9},{0,10},{1,4},{1,8},{2,5},{2,10},
    {3,6},{3,7},{4,8},{4,10},{5,8},{5,9},{6,7},{6,10},{7,9},{8,9}};
constexpr int cases[12][2]={{7,4},{7,5},{7,6},{6,5},{6,6},{6,7},{6,8},
    {5,6},{5,7},{5,8},{5,9},{5,10}};
int cover[M],memo[M],incident[N],p[N];
int minimum[N+1][6];
uint64_t partitions[N+1]={},generic[12]={},refined[12]={};
int recurrence(int mask){
    if(!mask)return 0;
    int &v=memo[mask];if(v>=0)return v;
    int e=__builtin_ctz((unsigned)mask);
    return v=1+min(recurrence(mask&~incident[edges[e][0]]),
                   recurrence(mask&~incident[edges[e][1]]));
}
void init(){
    for(int e=0;e<E;e++)for(int v:edges[e])incident[v]|=1<<e;
    // Independent vertex-subset enumeration + superset minimum DP.
    fill(cover,cover+M,N+1);
    for(int s=0;s<(1<<N);s++){
        int m=0;for(int v=0;v<N;v++)if(s>>v&1)m|=incident[v];
        cover[m]=min(cover[m],__builtin_popcount((unsigned)s));
    }
    for(int e=0;e<E;e++)for(int m=0;m<M;m++)if(!(m>>e&1))
        cover[m]=min(cover[m],cover[m|(1<<e)]);
    fill(memo,memo+M,-1);
    for(int m=0;m<M;m++)if(cover[m]!=recurrence(m)){
        cerr<<"cover cross-check failed "<<m<<'\n';exit(1);
    }
    // Cross-rectangle star assumption requires no four-cycle.
    for(int u=0;u<N;u++)for(int v=u+1;v<N;v++){
        int common=0;
        for(int w=0;w<N;w++)if(w!=u&&w!=v){
            bool a=false,b=false;
            for(const auto &e:edges){a|=(e[0]==u&&e[1]==w)||(e[1]==u&&e[0]==w);
                b|=(e[0]==v&&e[1]==w)||(e[1]==v&&e[0]==w);}
            common+=a&&b;
        }
        if(common>1){cerr<<"four-cycle found\n";exit(1);}
    }
    for(auto &row:minimum)fill(begin(row),end(row),N+E);
}
void insert2(int x,int &a,int &b){if(x>a){b=a;a=x;}else if(x>b)b=x;}
void evaluate(int blocks){
    int groups[N*N]={};
    for(int e=0;e<E;e++){
        int a=p[edges[e][0]],b=p[edges[e][1]];
        if(a>b)swap(a,b);
        groups[a*N+b]|=1<<e;
    }
    int sum=0,a=0,b=0,c=0,d=0;
    for(int j=0;j<N*N;j++)if(groups[j]){
        int t=cover[groups[j]];sum+=t;insert2(t,a,b);
        if(j/N==j%N)insert2(t,c,d);
    }
    // Tight-count cases: both singleton-bearing junk gates must share
    // a block (junk0 is read by junk1). If only junk0 carries a
    // singleton, its loop and junk1's block pair share that block.
    int incident_discount=0;
    for(int u=0;u<blocks;u++){
        int loop=cover[groups[u*N+u]],best=0;
        for(int v=0;v<blocks;v++)if(v!=u){
            int lo=min(u,v),hi=max(u,v);
            best=max(best,cover[groups[lo*N+hi]]);
        }
        incident_discount=max(incident_discount,loop+best);
    }
    const int two=sum-a-b,one=sum-a,loops=sum-c-d;
    const int same_loop=sum-c,loop_incident=sum-incident_discount;
    const int equality=min({one+1,loop_incident+1,same_loop});
    partitions[blocks]++;
    minimum[blocks][0]=min(minimum[blocks][0],two);
    minimum[blocks][1]=min(minimum[blocks][1],one);
    minimum[blocks][2]=min(minimum[blocks][2],loops);
    minimum[blocks][3]=min(minimum[blocks][3],same_loop);
    minimum[blocks][4]=min(minimum[blocks][4],loop_incident);
    minimum[blocks][5]=min(minimum[blocks][5],equality);
    for(int i=0;i<12;i++){
        int k=cases[i][0],r=cases[i][1];
        if(blocks<N-r||two>k)continue;
        generic[i]++;
        // Tight OR-component count: at least one of the three cases
        // (junk0 singleton-free, only junk1 singleton-free, neither)
        // must satisfy its corresponding lower bound.
        if(blocks==N-r && equality>k)continue;
        refined[i]++;
    }
}
void enumerate(int i,int blocks){
    if(i==N){evaluate(blocks);return;}
    for(int j=0;j<=blocks;j++){
        p[i]=j;enumerate(i+1,max(blocks,j+1));
    }
}
int main(){
    init();p[0]=0;enumerate(1,1);
    uint64_t total=0;
    cout<<"blocks partitions two_any one_any two_loops one_loop loop_incident tight_bound\n";
    for(int b=1;b<=N;b++){
        total+=partitions[b];
        cout<<b<<' '<<partitions[b];for(int x:minimum[b])cout<<' '<<x;cout<<'\n';
    }
    if(total!=678570){cerr<<"partition count mismatch\n";return 1;}
    cout<<"total="<<total<<" cover_crosscheck="<<M<<" tau="<<cover[M-1]<<'\n';
    cout<<"k r generic_partitions refined_partitions\n";
    for(int i=0;i<12;i++)cout<<cases[i][0]<<' '<<cases[i][1]<<' '
        <<generic[i]<<' '<<refined[i]<<'\n';
    if(generic[0]!=82||refined[0]!=0){cerr<<"expected L2260 bound failed\n";return 1;}
    cout<<"L2260 PARTITION CHECK OK; (7,4) excluded by graph argument, not yet Lean-certified\n";
}
