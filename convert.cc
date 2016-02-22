#include "utility.h"

typedef map<int,int> SEQ_I;
typedef map<string,int> SEQ_S;


SEQ_I H1_I,H2_I,H3_I,H4_I;
SEQ_S H1_S,H2_S,H3_S;

struct widetuple {
	float value;
	int gid1,gid2,gid3;
};

struct WtupComp { // descending order
	bool operator () (widetuple left,widetuple right) const
	{ return left.value > right.value; }
};

int getSeqS(SEQ_S& H,string& id) {
	if (H.count(id)==0)
		H[id]=H.size();

	return H[id];
}


int getSeqI(SEQ_I& H,int id) {
	if (H.count(id)==0)
		H[id]=H.size();

	return H[id];
}

void cvt_textfile() {
	FILE* fin=fopen("raw/text_file.txt","r");
	FILE* fout=fopen("data/text_file.txt","w");

	int rec_id=0;
	int i1;
	char str[200];
	while (!feof(fin)) {
		fscanf(fin,"%s",str);
		int slen=strlen(str);
		if (slen==0) continue;

		for (int z=0;z<slen;z++)
			str[z]=(char)tolower(str[z]);
		while (slen>0&&(str[slen-1]<'a'||str[slen-1]>'z')) {
			str[slen-1]='\0';
			slen--;
		}
		if (slen==0) continue;

		string tmp_s=str;
		i1=getSeqS(H1_S,tmp_s);

		if (rec_id<10)
			printf("%s\n",str);
		fprintf(fout,"%d\n",i1);
		rec_id++;

		if (rec_id%100000==0)
			printf("rec %d ok\n",rec_id);
	}
	printf("rec num: %d\n",rec_id);
	printf("distinct words: %d\n",H1_S.size());


	fclose(fin);
	fclose(fout);
}

/*
rec num: 1868822
distinct words: 64
[Mapping]
Airport (20): 19335


Populated Place (17): 177983

Church (14): 181367
School (13): 172188
Cemetery (21): 124336
Building (28): 46959
Post Office (16): 22618



Hospital (33): 11336
Tower (10): 16610
*/


//Feature_ID	Feature_Name	Class	ST_alpha	ST_num	County	County_num	Primary_lat_DMS	Primary_lon_DMS	Primary_lat_dec	Primary_lon_dec	Source_lat_DMS	Source_lon_DMS	Source_lat_dec	Source_lon_dec	Elev(Meters)	Map_Name

void read_gis_features(char* feature) {
	FILE* fin=fopen("raw/NationalFile.txt","r");


	char outfn[100];
	sprintf(outfn,"raw/tmp_%s.txt",feature);
	FILE* fout=fopen(outfn,"w");


	int rec_id=0;
	int ikey;

	char tmpbuf[100];


	const int MAX_CATEGORY=200;
	int stat[MAX_CATEGORY];
	for (int i=0;i<MAX_CATEGORY;i++)
		stat[i]=0;




	const int MAX_LINE_LEN=500;
	char str[MAX_LINE_LEN];
	float xval,yval;

	while (!feof(fin)) {
		fgets(str,MAX_LINE_LEN,fin);
		int slen=strlen(str);
		if (slen==0) continue;
		bool isResult=false;

		if (rec_id>0) {

			// extract required fields
			int col=0;
			char * pch=NULL;
			pch = strtok (str,"\t");
			while (pch != NULL) {
				col++;
				//printf ("[%d] %s\n",col,pch);

				if (col==3) { // type
					if (strcmp(pch,feature)==0)
						isResult=true;
					else
						isResult=false;

					string tmp_s=pch;
					ikey=getSeqS(H1_S,tmp_s);
					assert(ikey<MAX_CATEGORY);
					stat[ikey]++;
				}

				if (col==10)
					xval=atof(pch);

				if (col==11)
					yval=atof(pch);

				pch = strtok (NULL, "\t");
			}

			if (isResult)
				fprintf(fout,"%f %f\n",xval,yval);

			//if (rec_id>10)
			//	break;
		}

		rec_id++;

		if (rec_id%10000==0)
			printf("rec %d ok\n",rec_id);
	}
	printf("rec num: %d\n",rec_id);
	printf("distinct words: %d\n",H1_S.size());

	SEQ_S::iterator iter=H1_S.begin();

	printf("[Mapping]\n");
	while (iter!=H1_S.end()) {
		string skey=iter->first;
		int slot=iter->second;
		printf("%s (%d): %d\n",skey.c_str(),slot,stat[slot]);
		iter++;
	}

	fclose(fin);
	fclose(fout);
}

void read_all_gis_features() {
	FILE* fin=fopen("raw/NationalFile.txt","r");


	char outfn[100];
	sprintf(outfn,"raw/tmp_all_features.txt");
	FILE* fout=fopen(outfn,"w");


	int rec_id=0;
	int ikey;

	char tmpbuf[100],full_keyname[200];


	const int MAX_CATEGORY=200;
	int stat[MAX_CATEGORY];
	for (int i=0;i<MAX_CATEGORY;i++)
		stat[i]=0;




	const int MAX_LINE_LEN=500;
	char str[MAX_LINE_LEN];
	float xval,yval;

	while (!feof(fin)) {
		fgets(str,MAX_LINE_LEN,fin);
		int slen=strlen(str);
		if (slen==0) continue;
		string cur_feature;

		if (rec_id>0) {

			// extract required fields
			int col=0;
			char * pch=NULL;
			pch = strtok (str,"\t");
			while (pch != NULL) {
				col++;
				//printf ("[%d] %s\n",col,pch);

				if (col==2) {
					strcpy(full_keyname,pch);
					for (int z=0;z<strlen(full_keyname);z++)	// add a separator
						if (full_keyname[z]==' ')
							full_keyname[z]=',';
				}

				if (col==3) { // type
					string tmp_s=pch;
					cur_feature=pch;

					ikey=getSeqS(H1_S,tmp_s);
					assert(ikey<MAX_CATEGORY);
					stat[ikey]++;
				}

				if (col==10)
					xval=atof(pch);

				if (col==11)
					yval=atof(pch);

				pch = strtok (NULL, "\t");
			}

			fprintf(fout,"%f,%f,%s,%s\n",xval,yval,cur_feature.c_str(),full_keyname);

			//if (rec_id>10)
			//	break;
		}

		rec_id++;

		if (rec_id%10000==0)
			printf("rec %d ok\n",rec_id);
	}
	printf("rec num: %d\n",rec_id);
	printf("distinct words: %d\n",H1_S.size());

	SEQ_S::iterator iter=H1_S.begin();

	printf("[Mapping]\n");
	while (iter!=H1_S.end()) {
		string skey=iter->first;
		int slot=iter->second;
		printf("%s (%d): %d\n",skey.c_str(),slot,stat[slot]);
		iter++;
	}

	fclose(fin);
	fclose(fout);
}

int main(int argc,char** argv) {
  	char srcfn[100],destfn[100];
  	/*ConfigType cr;
	AddConfigFromFile(cr,"config.prop");
	AddConfigFromCmdLine(cr,argc,argv);
	ListConfig(cr);*/

	srand(0); srand48(0);



/*Church (CH): 181367
School (SC): 172188
Cemetery (CE): 124336
Building (BD): 46959
Post Office (PO): 22618
Populated Place (PP): 177983
Dam (DA): 56919
Locale (LO): 128476
Park (PA): 58312

Reservoir (2): 75175
Valley (37): 70969
Spring (7): 35837
Stream (1): 236339
*/

	//read_gis_features("Park");

	read_all_gis_features();


	//printf("prefix: %s\n",argv[1]);
	//sprintf(srcfn,"data/s%s.dat",argv[1]);
	//sprintf(destfn,"data/u%s.dat",argv[1]);



	return 0;
}

