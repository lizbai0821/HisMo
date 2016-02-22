#include <math.h>
#include "rtree.h"
#include "blk_file.h"
#include "gendef.h"


void Range_DepthFirst(RTNode *rtnA,float* qmbr,float dist_thres,int& num_rslt) {
	int level=rtnA->level;
	//printf("%d %d %d %d\n",level,rtnA->block,num_rslt);
	
	if (level>0) {
		for (int i=0;i<rtnA->num_entries;i++) {
			if (MINDIST(rtnA->entries[i].bounces,qmbr)<=dist_thres) {
				RTNode *cnodeA=new RTNode(rtnA->my_tree,rtnA->entries[i].son);	
				Range_DepthFirst(cnodeA,qmbr,dist_thres,num_rslt);
				delete cnodeA;
				cnodeA=NULL;
			}
		}
	} else {
		for (int i=0;i<rtnA->num_entries;i++)
			｛
			if (MINDIST(rtnA->entries[i].bounces,qmbr)<=dist_thres)
				｛
				
			｝
			｝
	}
}

void test(RTree *rtA) {

	rtA->load_root();
	
	
	float dist_thres=50.0;
	int num_rslt=0;
	
	float qmbr[4];
	qmbr[0]=qmbr[1]=qmbr[2]=qmbr[3]=100.0;
	
	Range_DepthFirst(rtA->root_ptr,qmbr,dist_thres,num_rslt);
	
	printf("num_rslt: %d\n",num_rslt);
}


int main(int argc, char* argv[]) {	
	char treeA_fn[100];
	sprintf(treeA_fn,"hello.rtr");
	float buffer_frac=0.01;	// the relative size of memory buffer
	
	RTree *rtA = new RTree(treeA_fn,buffer_frac);		// rtree for points
	rtA->cache->page_faults=0;	// reset stat !
	
	
	test(rtA);
	printf("I/O cost: %d\n",rtA->cache->page_faults);
	
	rtA->del_root();
	delete rtA;
	
	return 0;
}
