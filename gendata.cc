#include "rtree.h"
#include "blk_file.h"
#include "gendef.h"
#include "hilbert.h"
#include <stdlib.h>
#include <assert.h>
#include <algorithm>
#include <vector>
#include <stack>
#include <float.h>
#include <math.h>
#include <string.h>
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <time.h>
#include <sys/dir.h>
#include <sys/stat.h>

#define DOM_SZ (10000.0)
#define MAXLEVEL (8)
#define RTFILE "Rtree"
unsigned gBits=12;	// 10
int blk_len=4096;
int LastBlockId=0;
char* gBlock=NULL;
float part, sim_degree, topk_option, delta;
float vmax=-DBL_MAX;
float dmax=-DBL_MAX;
int data_size;
int opt; // query option
const float Sentinel=-DBL_MAX;

clock_t t0, t1, t2, t3, t4;

#define PATH "/Users/lizbai/Downloads/DataSett"
#define FILENAME "Overview"


typedef pair<int,float> lvalue; //for candidate streaks ending at position k
struct lrvalue
{
    int l;
    int r;
    float value;
};

int MakeMaximalStreaks(vector<float> data, float part, vector<lrvalue> & MaximalStreaks, vector<lrvalue> & LPSK)
{//for making maximal streaks give dataset
    int k=0;
    stack<lvalue> CandidateStreaks;
    lvalue InitialPair(k,Sentinel);
    CandidateStreaks.push(InitialPair);
    for(int it=0;it<int(data.size()*part)-1;it++)
    {
        k++;
        float s=data[it];
        bool HaveInsert=false;
        while(!CandidateStreaks.empty())
        {
            float v=CandidateStreaks.top().second;
            if(v>s)
            {
                lrvalue TempStreak={CandidateStreaks.top().first,k-1,v};
                CandidateStreaks.pop();
                //UpdateRange(MaximalStreaks,TempStreak,range);
                MaximalStreaks.push_back(TempStreak);
                HaveInsert=true;
            }
            else if(v==s)
                break;
            else
            {
                if(HaveInsert)//some elements were inserted to MaximalStreaks in previous step
                {
                    vector<lrvalue>::iterator it=MaximalStreaks.end();
                    --it;
                    lvalue TempCandidate(it->l,s);
                    CandidateStreaks.push(TempCandidate);
                }
                else//no elements inserted in this iteration
                {
                    lvalue TempCandidate(k,s);
                    CandidateStreaks.push(TempCandidate);
                }
                break;
            }
        }
    }
    k+=1;
    while(CandidateStreaks.top().second>Sentinel)
    {
        float v=CandidateStreaks.top().second;
        //lvalue Temp(k,v);
        lrvalue TempStreak={CandidateStreaks.top().first,k-1,v};//Temp);
        CandidateStreaks.pop();
        LPSK.push_back(TempStreak);
    }
    return k;
}

bool CompareLPSk (lrvalue i, lrvalue j){
    return (i.value>j.value);	
}


void SortLPSk (vector<lrvalue> & _LPSk){
	sort(_LPSk.begin(),_LPSk.end(),CompareLPSk);
}

vector<lrvalue> MakeOverPruner(vector<lrvalue> &LPSk , vector<lrvalue> &skyline, float t, float &vmax, float &dmax)
{
	float vmin = DBL_MAX;
	float lmax = -DBL_MAX;
    SortLPSk(LPSk);

    vector<lrvalue> overpruner;

    vector<lrvalue>::iterator ss;    
    vector<lrvalue>::iterator oo;
    vector<int> set;

    for(ss=skyline.begin();ss!=skyline.end();ss++)//traverse
    {
    	float lenth_tp = ss->r - ss->l;
    	lmax = max (lmax, lenth_tp);
    	vmax = max (vmax, ss->value);
    	vmin = min (vmin, ss->value);
        for(oo=LPSk.begin();oo!=skyline.end();oo++)
        {
            if(oo->l <= ss->l)
                break;
        }
        if((ss->r - ss->l)>=((oo->r - oo->l)*t))
        {
            overpruner.push_back(*ss);
            set.push_back(ss - skyline.begin());
        }
    }
    dmax= sqrt(pow(lmax,2)+pow(vmax-vmin,2));
    if(set.size()==0)
        return overpruner;
    for(vector<int>::iterator se = set.end()-1;se>=set.begin();se--)
    {
        skyline.erase(skyline.begin()+*se);
    }
    return overpruner;
}

void GetDataTable (vector<string> &_Time, vector<float> &_Data, string File)
{//read data and time tables from file
    fstream _file;
    _file.open(File.c_str(),ios::in);
    if(!_file)
    {
        cout<<File<<" does not exist! "<<endl;
        return;
    }
    string s1;
    float s2;
    while(!_file.eof())
    {
        _file>>s1>>s2;
        _Time.push_back(s1);
        _Data.push_back(s2);
    }
    return;
}

long GetFileSize(char * filename)
{
	FILE *pFile;
	long size;

	pFile = fopen(filename, "rb");
	if(pFile==NULL) perror ("Error opening file");
	else
	{
		fseek(pFile, 0 , SEEK_END);
		size = ftell (pFile);
		fclose(pFile);
	}
	return size;
}

// assume all coordinate values >=0
inline float MIN_FVALUE(float* bounces) {
	float sum=0;
	for (int j=0;j<DIMENSION;j++)
		sum+=bounces[2*j];
	return sum;
}

bool isDomed(HeapEntry& he, Entry* New_Added) 
{// true: he is overlapped/in the domination area of New_Add
	//for (int i=0;i<pruner_set.size();i++)
	{
		for (int j=0;j<DIMENSION;j++) 
		{
			if (New_Added->bounces[2*j+1] < he.bounces[2*j]) 
			{
				return false;
			}
		}
	}
	return true; 
}

void BBS_Sky(RTree* rt, Entry* New_Added) //given a new entry New_Added, prune/delete all points in rt that New_Added dominates
{
	Heap hp;
	while (hp.size()>0) hp.pop();	// clear the heap first
	rt->load_root();
	{
		RTNode* cur_node=rt->root_ptr;	// enqueue root entries
		for (int i=0;i<cur_node->num_entries;i++)
		{
			HeapEntry he;
			he.key=MIN_FVALUE(cur_node->entries[i].bounces);  // bounces are just MBR or points
			he.level=cur_node->level;
				he.end=cur_node->entries[i].end; // for attribute "end"
			he.son=cur_node->entries[i].son;
			for (int j=0;j<2*DIMENSION;j++)
				he.bounces[j]=cur_node->entries[i].bounces[j];
			hp.push(he);
		}
	}

	while (hp.size()>0) {
		HeapEntry he=hp.top();	// dequeue next entry
		hp.pop();
		if (!isDomed(he, New_Added))
		{
			continue;
		}			
		// if not pruned
		if (he.level!= '\0') {
			RTNode *rtn=new RTNode(rt,he.son);
			assert(rtn);
			//printf("%d %d\n",he.level,he.son);
			for (int i=0;i<rtn->num_entries;i++)
				//if (rtn->entries[i].section(qmbr)!=S_NONE)
			{
				HeapEntry new_he;
				new_he.key=MIN_FVALUE(rtn->entries[i].bounces);
				new_he.level=rtn->level;
					new_he.end=rtn->entries[i].end;//for attribute "end"
				new_he.son=rtn->entries[i].son;
				for (int j=0;j<2*DIMENSION;j++)
					new_he.bounces[j]=rtn->entries[i].bounces[j];

				if (isDomed(new_he, New_Added))
					hp.push(new_he);
			}
			delete rtn;
			rtn=NULL;
		} 
		else
		{ // "he" must be a skyline point
			if(((DIMENSION==2)&&(he.end < New_Added->end)) || (DIMENSION==3) )
			{
				Entry* d = new Entry(DIMENSION,NULL);
				assert(d);
				d->son = he.son;
				d->level = he.level;
				d->end= he.end;
				for (int j=0;j<2*DIMENSION;j++)
				{
					d->bounces[j]=he.bounces[j];
				}		
				rt->delete_entry(d);
				delete d;
				d=NULL;
			}
		}
	}
//	printf("\n");
	//printf("rslt: %d,  %d %d\n",results.size(),start_pos,len);
	return;
}

bool Containing(HeapEntry& he, Entry* New_Added)
{//true : he contain newadd
	if((he.bounces[0]<=New_Added->bounces[0])&&(he.bounces[1]>=New_Added->bounces[1])&&(he.bounces[2]<=New_Added->bounces[2])&&(he.bounces[3]>=New_Added->bounces[3]))
		return true;
	return false;
}

void MakeCoverline(RTree* rt, Entry* New_Added) 
{
	Heap hp;
	while (hp.size()>0) hp.pop();	// clear the heap first
	rt->load_root();

	{
		RTNode* cur_node=rt->root_ptr;	// enqueue root entries
		for (int i=0;i<cur_node->num_entries;i++)
			//if (cur_node->entries[i].section(qmbr)!=S_NONE)
		{
			HeapEntry he;
			he.key=1;  //use the heap as vector, for convenience
			he.level=cur_node->level;
				he.end=cur_node->entries[i].end;
			he.son=cur_node->entries[i].son;
			for (int j=0;j<2*DIMENSION;j++)
				he.bounces[j]=cur_node->entries[i].bounces[j];
			if(Containing(he, New_Added))
				hp.push(he);
			//cout<<"p";
		}
	}

	while (hp.size()>0) 
	{
		HeapEntry he=hp.top();	// dequeue next entry
		hp.pop();
		if (!Containing(he, New_Added))
		{
			continue;
		}			
		// if not pruned
		if (he.level!= '\0') {
			RTNode *rtn=new RTNode(rt,he.son);
			//printf("%d %d\n",he.level,he.son);
			for (int i=0;i<rtn->num_entries;i++)
				//if (rtn->entries[i].section(qmbr)!=S_NONE)
			{
				HeapEntry new_he;
				new_he.key=1;
				new_he.level=rtn->level;
					new_he.end=rtn->entries[i].end;//for attribute "end"
				new_he.son=rtn->entries[i].son;
				for (int j=0;j<2*DIMENSION;j++)
					new_he.bounces[j]=rtn->entries[i].bounces[j];

				if (Containing(new_he, New_Added))
					hp.push(new_he);
			}
			delete rtn;
			rtn=NULL;
		} 
		else
		//if ((he.level == 0) && (Containing(he, New_Added)))
		{
			if(he.end < New_Added->end)//when 3D
			{ // "he" must be a skyline point		
				Entry* d = new Entry(DIMENSION,NULL);
				d->son = he.son;
				d->level = he.level;
				for (int j=0;j<2*DIMENSION;j++)
					d->bounces[j]=he.bounces[j];
			//printf("%d ",results.size());
				rt->delete_entry(d);
				delete d;
				d=NULL;

			}			
		}
	}
//	printf("\n");
	//printf("rslt: %d,  %d %d\n",results.size(),start_pos,len);
	return;
}

void RepeatInsertion_Skylined(Entry** dataAry,int data_size,RTree* rt) {
	printf("Create the tree by repeated insertions\n");
	for (int i=0;i<data_size;i++) {
		BBS_Sky(rt, dataAry[i]);
		rt->insert(dataAry[i]); // entry deleted inside insertion function
		dataAry[i]=NULL;

		if (i % 100 == 0)
			printf("\rinserting record %d",i);
	}
	printf("\n");
}

void RepeatInsertion_Coverlined(Entry** dataAry,int data_size,RTree* rt) {
	printf("Create the tree by repeated insertions\n");
	for (int i=0;i<data_size;i++) {
		MakeCoverline(rt, dataAry[i]);
		rt->insert(dataAry[i]); // entry deleted inside insertion function
		dataAry[i]=NULL;

		if (i % 10 == 0)
			printf("\rinserting record %d",i);
	}
	printf("\n");
}

inline float dis(float low, float high, float axis)
{
	if(axis < low)
		return fabs(low - axis);
	else if (axis > high)
		return fabs(axis - high);
	else
		return 0.0;
}
float Distance(float *Rect_bounces, float *Ask_bounces)
{
	float x_l = dis(Rect_bounces[0], Rect_bounces[1], Ask_bounces[1]);
	float y_l = dis(Rect_bounces[2], Rect_bounces[3], Ask_bounces[3]);
	if(DIMENSION == 2)
		return sqrt(pow(x_l,2)+pow(y_l,2));
	float z_l = dis(Rect_bounces[3], Rect_bounces[4], Ask_bounces[5]);
	return sqrt(pow(x_l,2)+pow(y_l,2)+pow(z_l,2));
}

float Evaluation(float* bounces, Entry* Ask, int Query_Type) {
	switch(Query_Type){
		case 1: return bounces[3];
		case 2: return bounces[3]+bounces[5]*vmax;
		case 3: return -Distance(bounces, Ask->bounces);
		case 4: return bounces[5]*dmax - Distance(bounces, Ask->bounces);
	}
}

bool InSearchRange(HeapEntry he, Entry *Ask)
{//true: he is overlapped with the search range of Ask
	for( int j=0; j<DIMENSION; j++)
	{
		if(he.bounces[2*j+1] < Ask->bounces[2*j]*sim_degree)
			return false;
	}
	return true;
}

lrvalue Query_Baseline(RTree* rt, Entry* Ask, int Query_Type) 
{
	Heap hp;
	while (hp.size()>0) hp.pop();	// clear the heap first
	rt->load_root();

	float MaxEva = Sentinel;
	lrvalue Answer = {0,0,0}; 

	{
		RTNode* cur_node=rt->root_ptr;	// enqueue root entries
		for (int i=0;i<cur_node->num_entries;i++)
		{
			HeapEntry he;
			he.key=Evaluation(cur_node->entries[i].bounces, Ask, Query_Type);  // bounces are just MBR or points
			he.level=cur_node->level;
				he.end=cur_node->entries[i].end; // for attribute "end"
			he.son=cur_node->entries[i].son;
			for (int j=0;j<2*DIMENSION;j++)
				he.bounces[j]=cur_node->entries[i].bounces[j];
			hp.push(he);
		}
	}

	while (hp.size()>0) {
		HeapEntry he=hp.top();	// dequeue next entry
		//cout<<he.key<<"**";
		hp.pop();
		if (!InSearchRange(he, Ask))
		{
			continue;
		}			
		// if not pruned
		if (he.level!= '\0') {
			RTNode *rtn=new RTNode(rt,he.son);
			assert(rtn);
			//printf("%d %d\n",he.level,he.son);
			for (int i=0;i<rtn->num_entries;i++)
				//if (rtn->entries[i].section(qmbr)!=S_NONE)
			{
				HeapEntry new_he;
				new_he.key=Evaluation(rtn->entries[i].bounces, Ask, Query_Type);
				new_he.level=rtn->level;
					new_he.end=rtn->entries[i].end;//for attribute "end"
				new_he.son=rtn->entries[i].son;
				for (int j=0;j<2*DIMENSION;j++)
					new_he.bounces[j]=rtn->entries[i].bounces[j];

				if (InSearchRange(new_he, Ask))
					hp.push(new_he);
			}
			delete rtn;
			rtn=NULL;
		} 
		else
		{ // Candidate Points
			if(he.key > MaxEva)
			{
				MaxEva = he.key;
				Answer.l = he.end-he.bounces[1];
				Answer.r = he.end;
				Answer.value = he.bounces[3];
			}
		}
	}
	return Answer;
//	printf("\n");
	//printf("rslt: %d,  %d %d\n",results.size(),start_pos,len);
}

lrvalue Query_BBS(RTree* rt, Entry* Ask, int Query_Type) 
{
	Heap hp;
	while (hp.size()>0) hp.pop();	// clear the heap first
	rt->load_root();

	//float MaxEva = Sentinel;
	lrvalue Answer = {0,0,0};

	{
		RTNode* cur_node=rt->root_ptr;	// enqueue root entries
		for (int i=0;i<cur_node->num_entries;i++)
		{
			HeapEntry he;
			he.key=Evaluation(cur_node->entries[i].bounces, Ask, Query_Type);  // bounces are just MBR or points
			he.level=cur_node->level;
				he.end=cur_node->entries[i].end; // for attribute "end"
			he.son=cur_node->entries[i].son;
			for (int j=0;j<2*DIMENSION;j++)
				he.bounces[j]=cur_node->entries[i].bounces[j];
			hp.push(he);
		}
	}

	while (hp.size()>0) {
		HeapEntry he;
        he.key = hp.top().key;
        he.level = hp.top().level;
        he.son=hp.top().son;
        for (int j=0;j<2*DIMENSION;j++)
            he.bounces[j]=hp.top().bounces[j];
		hp.pop();
		if (!InSearchRange(he, Ask))
		{
			continue;
		}			
		// if not pruned
		if (he.level!= '\0') {
			RTNode *rtn=new RTNode(rt,he.son);
			assert(rtn);
			//printf("%d %d\n",he.level,he.son);
			for (int i=0;i<rtn->num_entries;i++)
				//if (rtn->entries[i].section(qmbr)!=S_NONE)
			{
				HeapEntry new_he;
				new_he.key=Evaluation(rtn->entries[i].bounces, Ask, Query_Type);
				new_he.level=rtn->level;
					new_he.end=rtn->entries[i].end;//for attribute "end"
				new_he.son=rtn->entries[i].son;
				for (int j=0;j<2*DIMENSION;j++)
					new_he.bounces[j]=rtn->entries[i].bounces[j];

				if (InSearchRange(new_he, Ask)){
					hp.push(new_he);
				}
					
			}
			delete rtn;
			rtn=NULL;
		} 
		else
		{ // Candidate Points
			//if(he.key > MaxEva)
			{
				//MaxEva = he.key;
				Answer.l = he.end-he.bounces[1];
				Answer.r = he.end;
				Answer.value = he.bounces[3];
				return Answer;
			}
		}
	}
	return Answer;
//	printf("\n");
	//printf("rslt: %d,  %d %d\n",results.size(),start_pos,len);
}

void UpdateOneData (RTree *rt, float NewData, vector<lrvalue> &LPSK, vector<lrvalue> &OverPruner)
{
	bool judge = false;
	for(vector<lrvalue>::iterator it = LPSK.end()-1; it >= LPSK.begin(); it--)
	{
		if(it->value > NewData)
		{
			OverPruner.push_back(*it);
			{// insert into rtree
				Entry * d = new Entry(DIMENSION, NULL);
				d->bounces[0] = d->bounces[1] = it->r - it->l;
				d->bounces[2] = d->bounces[3] = it->value;
				if(DIMENSION == 3)
					d->bounces[4] = d->bounces[5] = it->r;
				d->end=it->r;
				rt->insert(d);
				d=NULL;
			}
			vector<lrvalue>::iterator iit = it;
			LPSK.erase(iit);			
		}
		else
		{
			it->r+=1; //lps_{k+1}
			judge = true;
		}
	}
	if(judge)
	{
		lrvalue temp = {LPSK.begin()->r, LPSK.begin()->r, NewData};
		LPSK.insert(LPSK.begin(), temp);
	}
	return;
}

void Rule(RTree *rt, lrvalue overpruner, lrvalue lpsk) //opt: rule 1 or 2
{
	
		Entry * d_o = new Entry(DIMENSION, NULL);
		d_o->bounces[0] = d_o->bounces[1] = overpruner.r - overpruner.l;
		d_o->bounces[2] = d_o->bounces[3] = overpruner.value;
		if(DIMENSION == 3)
			d_o->bounces[4] = d_o->bounces[5] = overpruner.r;
		d_o->end=overpruner.r;
	

	Heap hp;
	while (hp.size()>0) hp.pop();	// clear the heap first
	rt->load_root();
	{
		RTNode* cur_node=rt->root_ptr;	// enqueue root entries
		for (int i=0;i<cur_node->num_entries;i++)
		{
			HeapEntry he;
			he.key=MIN_FVALUE(cur_node->entries[i].bounces);  // bounces are just MBR or points
			he.level=cur_node->level;
				he.end=cur_node->entries[i].end; // for attribute "end"
			he.son=cur_node->entries[i].son;
			for (int j=0;j<2*DIMENSION;j++)
				he.bounces[j]=cur_node->entries[i].bounces[j];
			hp.push(he);
		}
	}

	while (hp.size()>0) 
	{
		HeapEntry he=hp.top();	// dequeue next entry
		hp.pop();
		if ((!isDomed(he, d_o))&&(opt<3) || ((opt>2)&&(!Containing(he, d_o))) )
		{
			continue;
		}			
		// if not pruned
		if (he.level!= '\0') {
			RTNode *rtn=new RTNode(rt,he.son);
			assert(rtn);
			//printf("%d %d\n",he.level,he.son);
			for (int i=0;i<rtn->num_entries;i++)
				//if (rtn->entries[i].section(qmbr)!=S_NONE)
			{
				HeapEntry new_he;
				new_he.key=MIN_FVALUE(rtn->entries[i].bounces);
				new_he.level=rtn->level;
					new_he.end=rtn->entries[i].end;//for attribute "end"
				new_he.son=rtn->entries[i].son;
				for (int j=0;j<2*DIMENSION;j++)
					new_he.bounces[j]=rtn->entries[i].bounces[j];

				if ((!isDomed(he, d_o))&&(opt<3) || ((opt>2)&&(!Containing(he, d_o))) )
					hp.push(new_he);
			}
			delete rtn;
			rtn=NULL;
		} 
		else
		{ // data point in domination 
			if(he.end < d_o->end)
			{
				if((he.bounces[1] < (lpsk.r - lpsk.l)*sim_degree) || (he.bounces[3] < lpsk.value *sim_degree))
				{
					Entry* d = new Entry(DIMENSION,NULL);
					assert(d);
					d->son = he.son;
					d->level = he.level;
					d->end= he.end;
					for (int j=0;j<2*DIMENSION;j++)
					{
						d->bounces[j]=he.bounces[j];
					}		
					rt->delete_entry(d);
					delete d;
					d=NULL;
				}
				
			}
		}
	}
	delete d_o;
	return;
}

vector<int> UpdateTree(RTree *rt, vector<lrvalue> OverPruner, vector<lrvalue> LPSK)
{
	vector<int> Removal;
	vector<lrvalue>::iterator oo, ll;
	for(oo=OverPruner.begin(); oo!=OverPruner.end(); oo++)
	{
		for(ll=LPSK.begin(); ll!=LPSK.end(); ll++)
		{
			if(ll->l <= oo->l)
				break;
		}
		Rule(rt, *oo, *ll);
		if((ll->r - ll->l) * sim_degree > (oo->r - oo->l))// oo is not a overpruner
			Removal.push_back(oo - OverPruner.begin());
	}
	return Removal;
}

void OverPrunerUpdate(vector<lrvalue> &OverPruner, vector<int> Removal)
{
	if(Removal.size()!=0)
	{
		sort(Removal.begin(), Removal.end());
		for(vector<int>::iterator it = Removal.end()-1; it>=Removal.begin(); it--)
			OverPruner.erase(OverPruner.begin() + *it);
	}
}
///////////////////////above are new functions from Ran////////////////////////////


void RT_addnode(RTree *rt,int *top_level,int capacity,int level,Entry *node_cover,RTNode** cur_node) {
	if (cur_node[level]->num_entries==0) { //new node to be created
        cur_node[level]->dirty=false;
        if ((*top_level)<level) //new root
        	*top_level=level;
        cur_node[level]->level=(char)level;	//init. cur_node[level]
    }

    cur_node[level]->entries[cur_node[level]->num_entries]=*node_cover;
	cur_node[level]->num_entries++;

    if (cur_node[level]->num_entries == capacity) { //node is full
        Entry sup_cover(DIMENSION,rt);

        // write the node back to disk
        if (level>0)
        	rt->num_of_inodes++;
        else
        	rt->num_of_dnodes++;

        cur_node[level]->write_to_buffer(gBlock);
        LastBlockId = rt -> file -> append_block(gBlock);
        //printf("write block %d\n",LastBlockId);

        // set MBR and son ptr
        sup_cover.son = LastBlockId;
        sup_cover.num_data=0;
        for (int i=0;i<cur_node[level]->num_entries;i++) {
        	sup_cover.num_data+=cur_node[level]->entries[i].num_data;
        	float* ref_bounces=cur_node[level]->entries[i].bounces;
        	for (int j=0;j<DIMENSION;j++) {
        		if (i==0) {
        			sup_cover.bounces[2*j]=ref_bounces[2*j];
        			sup_cover.bounces[2*j+1]=ref_bounces[2*j+1];
        		} else {
        			sup_cover.bounces[2*j]=min(sup_cover.bounces[2*j],ref_bounces[2*j]);
	    			sup_cover.bounces[2*j+1]=max(sup_cover.bounces[2*j+1],ref_bounces[2*j+1]);
        		}
        	}
        }

        cur_node[level]->num_entries=0;	// empty cur_node[level] after all updates!
        RT_addnode(rt, top_level, capacity, level+1, &sup_cover, cur_node);
    }
}

RTree *RT_bulkload(RTree *rt, Entry **objs, int count) {
    int top_level=0;
    const float util_rate=0.7;	// typical util. rate=0.7

	int capacity = rt->root_ptr->capacity;	// all nodes have the same capacity
    printf("capacity=%d\n",capacity);

    RTNode** cur_node=new RTNode*[MAXLEVEL];
    for (int i=0; i<MAXLEVEL; i++)
        cur_node[i]=new RTNode(DIMENSION,capacity);

	capacity=(int)(util_rate*capacity);
    printf("util_cap=%d\n", capacity);

	// assume objs sorted based on key
    rt->num_of_data = count;
    rt->num_of_dnodes = 0;

	printf("start\n");

    for (int i=0;i<count;i++) {
        RT_addnode(rt,&top_level,capacity,0,objs[i],cur_node);
        objs[i]=NULL;
        if (i % 10 == 0)
			printf("\rinserting record %d",i);
	}
	printf("\n");

    //flush non-empty blocks
    int level=0;
    while (level<=top_level) {
    	printf("level: %d %d\n",level,top_level);
    	if (cur_node[level]!=NULL) {
	        if (level>0)
	        	rt->num_of_inodes++;
	        else
	        	rt->num_of_dnodes++;

		    if (level<top_level) {
	        	Entry sup_cover(DIMENSION,rt);

		        // write the node back to disk
		        cur_node[level]->write_to_buffer(gBlock);
		        LastBlockId = rt -> file -> append_block(gBlock);

		        // set MBR and son ptr
		        sup_cover.son = LastBlockId;
		        sup_cover.num_data=0;
		        for (int i=0;i<cur_node[level]->num_entries;i++) {
		        	sup_cover.num_data+=cur_node[level]->entries[i].num_data;
		        	float* ref_bounces=cur_node[level]->entries[i].bounces;
		        	for (int j=0;j<DIMENSION;j++) {
		        		if (i==0) {
		        			sup_cover.bounces[2*j]=ref_bounces[2*j];
		        			sup_cover.bounces[2*j+1]=ref_bounces[2*j+1];
		        		} else {
		        			sup_cover.bounces[2*j]=min(sup_cover.bounces[2*j],ref_bounces[2*j]);
			    			sup_cover.bounces[2*j+1]=max(sup_cover.bounces[2*j+1],ref_bounces[2*j+1]);
		        		}
		        	}
		        }

		        cur_node[level]->num_entries=0;	// empty cur_node[level] after all updates!
	        	RT_addnode(rt,&top_level,capacity,level+1,&sup_cover,cur_node);
	        } else {	// root
	            rt->root_ptr->dirty=false;
	            rt->del_root();	// clear old root

	            // write new root
	            cur_node[level]->write_to_buffer(gBlock);
		        rt->file->write_block(gBlock, rt->root);
	            if (level>0)
	            	rt->root_is_data=false;
	        }
	    }
	    level++;
    }
    return rt;
}

int sort_tmpvalue(const void *d1, const void *d2) {
    Entry *s1=*((Entry **) d1), *s2=*((Entry **) d2);
    float diff=s1->sort_key-s2->sort_key;
    //printf("%f\n",diff);
    if (diff<0)
        return -1;
    else if (diff>0)
        return 1;
    else
    	return 0;
}

void BulkLoadData(Entry** dataAry,int data_size,RTree* rt) {
	printf("Create the tree by bulk-loading\n");
	unsigned cDOM=1<<gBits;
	bitmask_t coord[DIMENSION];

	for (int i=0;i<data_size;i++) {
		for (int j=0;j<DIMENSION;j++) {
			coord[j]=(bitmask_t)( ((float) cDOM)*(dataAry[i]->bounces[2*j]/(DOM_SZ+1.0)) );
			//printf("%f\n",(float)(coord[j]));	printf("%f\n",(float)(cDOM));
			assert(0<=coord[j]&&coord[j]<cDOM);
		}

		bitmask_t hrt_value=hilbert_c2i(DIMENSION,gBits,coord);
		dataAry[i]->sort_key=(float)hrt_value;
		assert(dataAry[i]->sort_key>=0);
		if (i % 100 == 0)
			printf("\rcomputing record %d",i);
	}
	printf("\nbegin sorting\n");


	qsort(dataAry,data_size,sizeof(Entry*),sort_tmpvalue);	// for testing
	printf("sorted %d rect.\n", data_size);

	gBlock = new char[blk_len];
	RT_bulkload(rt,dataAry,data_size);

	rt->write_header(gBlock);
    rt->file->set_header(gBlock);
	printf("This R-Tree contains %d internal, %d data nodes and %d data\n",
		   	rt->num_of_inodes, rt->num_of_dnodes, rt->num_of_data);

	delete[] gBlock;
}

void RepeatInsertion(Entry** dataAry,int data_size,RTree* rt) {
	printf("Create the tree by repeated insertions\n");
	for (int i=0;i<data_size;i++) {
		rt->insert(dataAry[i]); // entry deleted inside insertion function
		dataAry[i]=NULL;

		if (i % 100 == 0)
			printf("\rinserting record %d",i);
	}
	printf("\n");
}

void gen_syn_data(Entry** dataAry,int data_size) {
	float pt[DIMENSION];

	for (int i=0;i<data_size;i++) {
		for (int j=0;j<DIMENSION;j++)	// UI distribution
			pt[j]=drand48();

		for (int j=0;j<DIMENSION;j++) {
			assert(pt[j]>=0&&pt[j]<=1.0);

			pt[j]=pt[j]*DOM_SZ;
			dataAry[i]->bounces[2*j]=dataAry[i]->bounces[2*j+1]=pt[j];
			//printf("%f ",pt[j]);
		}
		//printf("\n");
	}
}

void write_dtfile(char* dtfile,Entry** dataAry,int data_size) {
	FILE* fout=fopen(dtfile,"wb");

	int dim=DIMENSION;
	fwrite(&(dim),1,sizeof(int),fout);
	fwrite(&(data_size),1,sizeof(int),fout);
	for (int i=0;i<data_size;i++)
		fwrite(dataAry[i]->bounces,2*DIMENSION,sizeof(float),fout);
	fclose(fout);
}


void read_real_data(char* rawfn,Entry** dataAry,int& data_size) {
	FILE* fin=fopen(rawfn,"r");

	assert(DIMENSION==2);

	int rec_id=0;
	float xmin,ymin,xmax,ymax;
	float xval,yval;
	float lastx=-1.0,lasty=-1.0;

	xmin=ymin=MAXREAL;
	xmax=ymax=-MAXREAL;

	while (!feof(fin)) {
		fscanf(fin,"%f %f\n",&xval,&yval);

		xmin=min(xval,xmin);
		xmax=max(xval,xmax);

		ymin=min(yval,ymin);
		ymax=max(yval,ymax);


		// remove adjacent duplicaates
		if (xval==lastx&&yval==lasty)
			continue;
		lastx=xval;
		lasty=yval;


		if (rec_id>=data_size) {
			printf("error data size\n");
			exit(0);
		}

		Entry* cur_data=dataAry[rec_id];
		cur_data->bounces[0]=cur_data->bounces[1]=xval;
		cur_data->bounces[2]=cur_data->bounces[3]=yval;

		if (rec_id%10000==0)
			printf("rec %d ok (%f %f)\n",rec_id,xval,yval);

		rec_id++;
		if (rec_id>data_size) {
			printf("input size invalid\n");
			exit(0);
		}
	}
	fclose(fin);

	printf("orig. map: [%f %f] [%f %f]\n",xmin,xmax,ymin,ymax);
	printf("|rec|: %d\n",rec_id);
	data_size=rec_id;

	for (int i=0;i<data_size;i++) {
		Entry* cur_data=dataAry[i];
		float x=cur_data->bounces[0];
		float y=cur_data->bounces[2];

		x=(x-xmin)/(xmax-xmin)*DOM_SZ;
		y=(y-ymin)/(ymax-ymin)*DOM_SZ;

		cur_data->bounces[0]=cur_data->bounces[1]=x;
		cur_data->bounces[2]=cur_data->bounces[3]=y;
	}
}


int main(int argc, char* argv[]) {
	if(argc!=2){
		cout<<"error"<<endl;
		return 0;
	}

	//delta=atof(argv[2]);
	int choice = atoi(argv[1]);//baseline or optimized 
	/*
	part=float(atof(argv[3])); //dataset-partition to run 
	sim_degree=atof(argv[4]);
	topk_option=atof(argv[5]);
	*/
	part = 1; // pre-calculated part
	opt = 1; //query type
	sim_degree = 0.8;
	topk_option = 3;
	delta = 0; // update part
	//blk_len=4096;
	blk_len=1024;	// default: 1 K page size (better for join)

	string path = PATH;
	DIR *pdir;  
    struct dirent *pdirent;  
    char temp[256];
    char tp[256];
    try {  
        pdir = opendir(path.c_str());  
    }  
    catch(const char *str)  
    {printf("failed open dir");} 

    if(pdir)
    {    	
    	ofstream fout(FILENAME);//for overview... position
    	if(choice ==1)
    	{
    		fout<<"Overview\tOptimized\tOptimized"<<endl; //
    	}
    	else
    	{
    		fout<<"Overview\tBaseline\tBaseline"<<endl; //
    	}
    	while((pdirent = readdir(pdir)))
        {    
            if(pdirent->d_name[0]!='.')
            {
            	//strcpy(tp, pdirent->d_name);
            	//strcat(tp, "_Query");
            	//strcat(tp, argv[1]);
            	//ofstream fout(tp);

            	fout<<pdirent->d_name<<"\t";
          //  	fout<<23<<" Optimized Optimized"<<endl;

				remove(RTFILE);			// remove file if exists

//MODIFICATION BY RAN
				vector<string> Ttable;
				vector<float> Data;
				sprintf(temp, "%s/%s", path.c_str(), pdirent->d_name);
				//GetDataTable( Ttable, Data, "ge");
				GetDataTable( Ttable, Data, temp);
				vector<lrvalue> MaxStreaks, LPSK;
				int k = MakeMaximalStreaks(Data, part, MaxStreaks, LPSK);
				vector<lrvalue> overpruner = MakeOverPruner(LPSK, MaxStreaks, sim_degree, vmax, dmax);
            	data_size = MaxStreaks.size();
/*
				Entry** dataAry=new Entry*[data_size];

            	for (int i=0;i<data_size;i++) {
            		Entry* d = new Entry(DIMENSION,NULL);
            		assert(d);
            		d->num_data=1;
            		d->son=i;
            		d->bounces[0] = d->bounces[1] = MaxStreaks[i].r - MaxStreaks[i].l;
            		d->bounces[2] = d->bounces[3] = MaxStreaks[i].value;
            		if(DIMENSION == 3)
            			d->bounces[4] = d->bounces[5] = MaxStreaks[i].r;
            		//if(DIMENSION == 2)
            		d->end=MaxStreaks[i].r;
            		dataAry[i]=d;            
            	}
 */           	
	//exit(0);

	//write_dtfile(dtfile,dataAry,data_size);

	//BulkLoadData(dataAry,data_size,rt); 

				//RepeatInsertion(dataAry, data_size, rt);

//////parameter sensitivity
            //for(sim_degree=0.65; sim_degree<=1; sim_degree+=0.05)

            //for(part=0.6; part<1.1; part+=0.1)
            {
            	//part=0.8;
            	remove(RTFILE);
				Cache *c=new Cache(10000,blk_len);
				RTree* rt=new RTree(RTFILE, blk_len,c,DIMENSION);
				Entry** dataAry=new Entry*[data_size];

            	for (int i=0;i<data_size;i++) {
            		Entry* d = new Entry(DIMENSION,NULL);
            		assert(d);
            		d->num_data=1;
            		d->son=i;
            		d->bounces[0] = d->bounces[1] = MaxStreaks[i].r - MaxStreaks[i].l;
            		d->bounces[2] = d->bounces[3] = MaxStreaks[i].value;
            		if(DIMENSION == 3)
            			d->bounces[4] = d->bounces[5] = MaxStreaks[i].r;
            		//if(DIMENSION == 2)
            		d->end=MaxStreaks[i].r;
            		dataAry[i]=d;            
            	}

            	//fout<<sim_degree<<" ";
            	//fout<<topk_option<<" ";
          //  	fout<<part<<" ";


            	if(choice == 1)
            	{
					if(opt<3)
						RepeatInsertion_Skylined(dataAry,data_size*( part - delta),rt);
					else
						RepeatInsertion_Coverlined(dataAry, data_size*( part - delta), rt);
            	}
				else
				{
					if(opt<3)
						RepeatInsertion(dataAry,data_size*( part - delta),rt);
					else
						RepeatInsertion(dataAry, data_size*( part - delta), rt);
				}

//Update Zone
/*
	vector<int> removal;
	
	float next = Data[int(Data.size()*part)-1];
	UpdateOneData(rt, next, LPSK, overpruner);
	removal = UpdateTree(rt, overpruner, LPSK);
	OverPrunerUpdate(overpruner, removal);
	k+=1;
*/
/* 

				for( int j = int(data_size * (part - delta)); j< int(data_size * part); j++)
				{
					float next = Data[j];
					UpdateOneData(rt, next, LPSK, overpruner);
				}

					vector<int> removal;
	t2=clock();
	removal = UpdateTree(rt, overpruner, LPSK);

	OverPrunerUpdate(overpruner, removal);
*/
				
				SortLPSk(LPSK);
				t0=clock();
				for( int i=0; i<topk_option; i++)
				{
					Entry *ask = new Entry(DIMENSION, NULL);
					ask->bounces[0] = ask->bounces[1] = LPSK[i].r - LPSK[i].l;
					ask->bounces[2] = ask->bounces[3] = LPSK[i].value;
					ask->end = LPSK[i].r;
					if(DIMENSION == 3)
						ask->bounces[4] = ask->bounces[5] = LPSK[i].r;

					lrvalue answer; 
					if(choice == 0)
					{
						answer = Query_Baseline( rt, ask, opt);
						answer = Query_Baseline( rt, ask, opt+1);
					}
					else
					{
						answer = Query_BBS( rt, ask, opt);
						answer = Query_BBS( rt, ask, opt+1);
					}
						
					delete ask;			
				}
				t1=clock();
				//f
				//cout<<1000*double(t3-t0)/CLOCKS_PER_SEC<<" "<<1000*double(t3-t2+t1-t0)/CLOCKS_PER_SEC<<" "<<1000*double(t3-t4)/CLOCKS_PER_SEC<<endl;
				fout<<1000*double(t1-t0)/CLOCKS_PER_SEC<<"\t";
//	
				long tree_size = GetFileSize(RTFILE);
//				cout<<"Rtree size:  "<<tree_size<<";  overpruner:  "<<overpruner.size()<<endl;
				fout<<tree_size<<endl;

    			rt->load_root();	// just close them currently
				rt->root_ptr->update_count();

				delete rt;
				delete[] dataAry;
			}
	//		fout.close();
			}
		}//while
		fout.close(); //overview position
	}

/*
	Heap hp;
	// while (hp.size()>0) hp.pop();	// clear the heap first
	rt->load_root();
	{
		RTNode* cur_node=rt->root_ptr;	// enqueue root entries
		for (int i=0;i<cur_node->num_entries;i++)
			//if (cur_node->entries[i].section(qmbr)!=S_NONE)
		{
			HeapEntry he;
			he.key=1;  // bounces are just MBR or points
			he.level=cur_node->level;
				//he.end=cur_node->entries[i].end;
			he.son=cur_node->entries[i].son;
			for (int j=0;j<2*DIMENSION;j++)
				he.bounces[j]=cur_node->entries[i].bounces[j];
			hp.push(he);
			//cout<<"p";
		}
	}

	while (hp.size()>0) 
	{
		HeapEntry he=hp.top();	// dequeue next entry
		hp.pop();
		
		// if not pruned
		if (he.level!= '\0') { 
			RTNode *rtn=new RTNode(rt,he.son);
			//printf("%d %d\n",he.level,he.son);
			for (int i=0;i<rtn->num_entries;i++)
				//if (rtn->entries[i].section(qmbr)!=S_NONE)
			{
				HeapEntry new_he;
				new_he.key=1;
				new_he.level=rtn->level;
					//new_he.end=rtn->entries[i].end;
				new_he.son=rtn->entries[i].son;
				for (int j=0;j<2*DIMENSION;j++)
					new_he.bounces[j]=rtn->entries[i].bounces[j];
				hp.push(new_he); 
			}
			delete rtn;
			rtn=NULL;
		} 
		else
		{ 
			for (int j=0;j<2*DIMENSION;j++)
			{
				cout<<he.bounces[j]<<" ";
			}
			cout<<endl;
		}
	}

*/	

	return 0;
}
