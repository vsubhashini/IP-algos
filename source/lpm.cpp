/************************************************
 * IP address look up algorithms [Best Prefix Match]
 * 
 * usage: ./bmp.o  -p Prefixfile -i InputAddrFile -o Outputfile -W 24 -a [B|M|H]
 *
 * @author V Subhashini
 * 	   
 *************************************************/
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<iostream>
#include<fstream>
#include<math.h>
#include<algorithm>
#include<vector>
#include <stdint.h> //for uint64_t
#include<ext/hash_map>

#define rdtsc(x) __asm__ volatile ("rdtsc" : "=A" (x))
#define PMAX 300000
#define IMAX 100000
#define MINPre 1
#define CPUF 1667

using namespace std;
using namespace __gnu_cxx;

//Global variables
int W, A, prcnt; //length, algotype, prefixCount
char *prfile, *ipfile, *opfile, *prgname, *notfound;
unsigned int pow2[] = {1,2,4,8,16,32,64,128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216};
int BinMatches[24]; //to keep all binary prefixes that matched during traversal.
int HashMatches[24]; //to keep all hashed prefixes that matched during binarysearch.
uint64_t TotalTime;
float AvgTime;

class Bnode
{
	int prefixId;
	unsigned int hashchk;
	bool match;
public:
	Bnode *left, *right;

	Bnode()
	{
		prefixId = hashchk = 0;
		left = right = NULL;
		match = false;
	}

	Bnode(int preid, int hashval, bool yn)
	{
		prefixId = preid;
		hashchk = hashval;
		match = yn;
		left = right = NULL;
	}

	unsigned int getHash() {return(hashchk);}
	int getPrefixId() {return(prefixId);}
	bool getMatch() {return(match);}

	void setPrefixId(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}
};

class bTrie
{
	Bnode *root;
public:
	bTrie() { root = new Bnode(0, pow2[23], false);}

	void insert(int l1, int l2, int l3, int len, int prefid)
	{
		Bnode *curn, *tempn;
		int num, match1, from, till, bit;
		unsigned int valbin;
		bool flag;
		num = 24-len;
		valbin = (l1 * pow2[16]) + (l2 * pow2[8]) + l3; //convert to bin

		if(!root)
		{
			root = new Bnode(0, pow2[23], false);
		}
		
		//start traversing and inserting node(s)
		curn = root; bit=23;
		//complete traversal of levels 1 and 2 and level 3 till the length.
		while(bit>=num)
		{
			flag = (pow2[bit] & valbin)?true:false;
			if(flag && (!curn->right))	//need to fork right but no child
			{
				tempn = new Bnode(0, pow2[bit-1], false);
				curn->right = tempn;
			}
			else if((!flag) && (!curn->left))//need to fork left but no child
			{
				tempn = new Bnode(0, pow2[bit-1], false);
				curn->left = tempn;
			}
			curn = (flag)?curn->right:curn->left;
			bit--;
		}
		//for current node set the prefix id and match
		curn->setPrefixId(prefid, true);
	}

	//search and return prefix id
	int search(int l1, int l2, int l3)
	{
		int i, bmpid, matchcount;
		bool flag;
		Bnode *curn;
		unsigned int valbin, bit;
		valbin = (l1 * pow2[16]) + (l2 * pow2[8]) + l3; //convert to bin
		
		curn = root; bmpid = matchcount = 0;
		while(curn)
		{
			if(curn->getMatch())
			{
				bmpid = curn->getPrefixId();
				BinMatches[matchcount++] = bmpid; //keeping track of all matched prefixes
			}
			bit = curn->getHash();
			flag = (bit & valbin)?true:false;
			curn = (flag)?curn->right:curn->left;
		}
		return(bmpid);
	}
};
bTrie BT;

class Mleaf
{
	int prefixId;
	bool match;
public:

	Mleaf()
	{
		prefixId = 0; match = false;
	}

	Mleaf(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}

	void replaceMleaf(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}

	bool getMatch() {return(match);}
	int getPrefixId() {return(prefixId);}
};

class M2node
{
	int prefixId;
	bool match;
public:
	Mleaf *mlf[256];

	M2node()
	{
		prefixId = 0; match = false;
	}

	M2node(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}

	void replaceM2node(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}

	bool getMatch() {return(match);}
	int getPrefixId() {return(prefixId);}
};

class Mnode
{
	int prefixId;
	bool match;
public:
	M2node *m2Arr[256];

	Mnode()
	{
		prefixId = 0; match = false;
	}

	Mnode(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}

	void replaceMnode(int prid, bool yn)
	{
		prefixId = prid;
		match = yn;
	}

	bool getMatch() {return(match);}
	int getPrefixId() {return(prefixId);}
};

class Mroot
{
	int prefixId;
	bool match;
public:
	Mnode *mArr[256];

	Mroot()
	{
		prefixId = 0; match = false;
	}

	bool getMatch() {return(match);}
	int getPrefixId() {return(prefixId);}
};
Mroot M1;

class Hnode
{
	unsigned int maskchk;
	int prefixId;
public:
	bool marker;

	Hnode()
	{
		prefixId = 0; maskchk = 0;
		marker = false;
	}

	Hnode(int prid, unsigned int hashval)
	{
		prefixId = prid; maskchk = hashval;
		marker = false;
	}

	int getPrefixId() {return(prefixId);}
	unsigned int getMask() {return(maskchk);}
	void onMarker() {marker=true;}
};

class preNode
{
	int nid, prelen;
	unsigned int mask;
	char *prefix;
public:
	preNode(int id, int len, char *prefixval, unsigned int maskval)
	{
		nid = id; prelen = len;
		prefix = (char*)malloc(sizeof(char)*20);
		mask = maskval;
		strcpy(prefix, prefixval);
	}

	char* getPrefix()
	{
		return(prefix);
	}

	int getPrelen()
	{
		return(prelen);
	}

	unsigned int getMask()
	{
		return(mask);
	}
};
preNode *prefixArr[PMAX];

class MtrieOps
{
public:
	MtrieOps() {}

	void addMtrie(int l1, int l2, int l3, int len, int prefid, int maskval)
	{
		int i;
		unsigned int hashval, valbin;
		int num, match1, from, till;
		Mnode *Mtemp;
		M2node *M2temp;
		Mleaf *Mlftemp;

		hashval = maskval;
		//given the value of strides at level 1,2 and 3. Mark the corresponding nodes using length
		if(len<=8)
		{
			num = 8-len;
			match1 = 255 - (pow2[num]-1);
			from = l1 & match1;
			till = from + pow2[num] - 1;
			//Mark all the subnodes of the multiBit trie that are chosen by current prefix.
			for(i=from; i<=till; i++)
			{//In case a node already has a match. need to do check bmp.
				Mtemp = M1.mArr[i];
				if(!Mtemp)
					M1.mArr[i] = new Mnode(prefid, true);
				else
				{//save the larger of the prefix values
					int curpid = Mtemp->getPrefixId();
					if((!Mtemp->getMatch())||(len>prefixArr[curpid]->getPrelen())||(hashval > prefixArr[curpid]->getMask())) //match is false || current match is better in term of len or mask then replace
					{
						M1.mArr[i]->replaceMnode(prefid, true);
					}
				}
			}
		}
		else if(len<=16)
		{
			num = 16-len;
			match1 = 255 - (pow2[num]-1);
			from = l2 & match1;
			till = from + pow2[num] - 1;
			//check if node at l1 exists, if not create
			if(!M1.mArr[l1])
					M1.mArr[l1] = new Mnode();
			//Mark all the subnodes of the multiBit trie that are chosen by current prefix.
			for(i=from; i<=till; i++)
			{//In case a node already has a match. need to do check bmp.
				M2temp = M1.mArr[l1]->m2Arr[i];
				if(!M2temp)
					M1.mArr[l1]->m2Arr[i] = new M2node(prefid, true);
				else
				{//save the larger of the prefix values
					int curpid = M2temp->getPrefixId();
					if((!M2temp->getMatch())||(len>prefixArr[curpid]->getPrelen())||(hashval > prefixArr[curpid]->getMask())) //match is false || current match is better in term of len or mask then replace
					{
						M1.mArr[l1]->m2Arr[i]->replaceM2node(prefid, true);
					}
				}
			}
		}
		else if(len<=24)
		{
			num = 24-len;
			match1 = 255 - (pow2[num]-1);
			from = l3 & match1;
			till = from + pow2[num] - 1;
			//check if node at l1, l2 exists, if not create
			if(!M1.mArr[l1])
					M1.mArr[l1] = new Mnode();
			if(!M1.mArr[l1]->m2Arr[l2])//check if node at l2 exists, if not create
					M1.mArr[l1]->m2Arr[l2] = new M2node();
			//Mark all the subnodes of the multiBit trie that are chosen by current prefix.
			for(i=from; i<=till; i++)
			{//In case a node already has a match. need to do check bmp.
				Mlftemp = M1.mArr[l1]->m2Arr[l2]->mlf[i];
				if(!Mlftemp)
					M1.mArr[l1]->m2Arr[l2]->mlf[i] = new Mleaf(prefid, true);
				else
				{//save the larger of the prefix values
					int curpid = Mlftemp->getPrefixId();
					if((!Mlftemp->getMatch())||(len>prefixArr[curpid]->getPrelen())||(hashval > prefixArr[curpid]->getMask())) //match is false || current match is better in term of len or mask then replace
					{
						M1.mArr[l1]->m2Arr[l2]->mlf[i]->replaceMleaf(prefid, true);
					}
				}
			}
		}
	}

	int searchMtrie(int l1, int l2, int l3)
	{
		int i, bmpid, tempid;
		bmpid = 0;
		//check at level1
		if(M1.mArr[l1])
		{ //chk if match is true to assign the bmp
			bmpid = (M1.mArr[l1]->getMatch())?M1.mArr[l1]->getPrefixId():bmpid;
			if(M1.mArr[l1]->m2Arr[l2]) //chk level2
			{
				bmpid = (M1.mArr[l1]->m2Arr[l2]->getMatch())?M1.mArr[l1]->m2Arr[l2]->getPrefixId():bmpid;
				if(M1.mArr[l1]->m2Arr[l2]->mlf[l3])
					bmpid = (M1.mArr[l1]->m2Arr[l2]->mlf[l3]->getMatch())?M1.mArr[l1]->m2Arr[l2]->mlf[l3]->getPrefixId():bmpid;
			}
		}
		return(bmpid);
	}

};
MtrieOps mops;

class hTable
{
	int len;
	hash_map<unsigned int, Hnode> hT;
public:
	hTable(int length) {len = length;}

	void insert(int l1, int l2, int l3, int prefid, unsigned int maskval)
	{
		typedef pair<unsigned int, Hnode> KeyData;
		Hnode hnew (prefid, maskval);

		hT.insert(KeyData(maskval, hnew));
	}

	int searchM(unsigned int maskval)
	{
		Hnode temphn;
		hash_map<unsigned int, Hnode>::iterator ITht;

		ITht = hT.find(maskval);
		if(ITht != hT.end())
		{//match found! go further
			temphn = ITht->second;
			return(temphn.getPrefixId());
		}
		return(-1); //no match then negative
	}

	void setMarker(unsigned int maskval)
	{
		hash_map<unsigned int, Hnode>::iterator ITht;
		int prefid;
		prefid = searchM(maskval);

		if(prefid<0) //not found
		{//just need to insert
			typedef pair<unsigned int, Hnode> KeyData;
			Hnode hnew (0, maskval); //give prefixid as 0 because it is only a marker.
			hnew.onMarker();
			hT.insert(KeyData(maskval, hnew));
		}
		//if found no need to do anything. it'll take care automatically.
	}

	void iterateTable()
	{
		int prefid;
		Hnode temphn;
			hash_map<unsigned int, Hnode>::iterator ITht;
		
		//cout<<" Elements in table "<<len<<" : ";
		for(ITht = hT.begin(); ITht != hT.end(); ITht++)
		{
			temphn = ITht->second;
			prefid = temphn.getPrefixId();
			if(prefid)
				cout<<prefixArr[prefid]->getPrefix()<<"/"<<prefixArr[prefid]->getPrelen()<<"("<<temphn.getMask()<<")\t";
			else
				cout<<"Marker mask: "<<temphn.getMask()<<"\t";
		}
		cout<<"\n";
	}

};
hTable *hashTable[25];

class hashOps
{
public:
	hashOps() {}
	
	void putMarkers()
	{//go through all the values in prefixes and add markers where necessary.
	    for(int i=1; i<=prcnt; i++)
	    {
	        unsigned int binprefix;
	        int prelen, low, mid, high;
	        int num, mask, match, prefid;
	    	    hash_map<unsigned int, Hnode>::iterator ITht;
	
	        binprefix = prefixArr[i]->getMask();
	        prelen = prefixArr[i]->getPrelen();
	        //do a binary search of the lengths
	        low=1; high=24;
	        while(low<=high)
	        {
	            mid = low + ((high-low)/2);
	            if(mid == prelen)
	                break; //if mid = prefix length, we can stop, no need to set further markers.
	            //compute mask and search in mid's hash table for a mask match
	            num = 24-mid;
	            mask = (pow2[24]-1) - (pow2[num]-1);
	            match = (mask & binprefix);
	
	            if(mid < prelen)
		    {
	                hashTable[mid]->setMarker(match);
	                low = mid + 1;
		    }
	            else
	                high = mid-1;
	        }
	    }
	}

	int findbinHbmp(int l1, int l2, int l3)
	{
		int bmpid, mpcnt, num, len, low, high, mid, prefid;
		unsigned int mask, valbin, match;

		bmpid = mpcnt = 0;
		valbin = (l1 * pow2[16]) + (l2 * pow2[8]) + l3; //convert to bin
		//do a binary search of the hash table to get matched prefix.
		low=1; high=24;
	        while(low<=high)
	        {
	        	mid = low + ((high-low)/2);
	        	//compute mask and search in mid's hash table for a mask match
	        	num = 24-mid;
	        	mask = (pow2[24]-1) - (pow2[num]-1);
	        	match = (mask & valbin);
	
	        	prefid = hashTable[mid]->searchM(match);
	        	if(prefid>=0)//update bmp and search only higher.
	        	{
				if(prefid) //update only if value is non-zero. i.e. it is not a marker
				{
					bmpid = prefid;
					HashMatches[mpcnt++] = bmpid;
				}
	        		low = mid + 1;
	        	}//otherwise no need to do anything, continue
	        	else
	        		high = mid-1;
		}
		return(bmpid);
	}

	int findHbmp(int l1, int l2, int l3)
	{
		int i, len, num, prefid, bmpid, mpcnt;
		unsigned int mask, match, valbin;

		bmpid = mpcnt = 0;
		valbin = (l1*(pow2[16]))+(l2*(pow2[8]))+l3;
		//do sequential search for all prefix matches
		for(i=MINPre; i<=24; i++)
		{
			len=i; num = 24-len;
			mask = (pow2[24]-1)-(pow2[num]-1);
			match = (mask & valbin);

	        	prefid = hashTable[i]->searchM(match);
			if(prefid>0) //update only if value is non-zero.
			{
				bmpid = prefid;
				HashMatches[mpcnt++] = bmpid;
			}
		}
		return(bmpid);
	}
};
hashOps hops;

//Fileoperations class
class FileOps
{
public:
	void markHtable()
	{
		// elements added, need to add markers
		hops.putMarkers();
	}
	
	int searchHtable(int l1, int l2, int l3)
	{
		int bmpid =0;
		bmpid = hops.findHbmp(l1, l2, l3);
		return(bmpid);
	}

	//displays all prefix matches in Bin Trie
	void printAllMatches(char* ipaddr, int Arr[], int max, uint64_t searchtime, char* bpm, int bmpid)
	{
		int i, preId;
		ofstream outF;
		float time = float(searchtime)/CPUF; //convert ticks to us

		//cout<<"\n All the prefix matches for IP "<<ipaddr<<" :";
		outF.open(opfile, ios::app);
		if(outF.is_open())
		{
			outF<<" "<<ipaddr<<"\t"<<bpm<<"/"<<prefixArr[bmpid]->getPrelen()<<"\t"<<time<<"\t";
			for(i=0; i<max; i++)
			{
				preId = Arr[i];
				if(preId)
				{
					//cout<<prefixArr[preId]->getPrefix()<<"/"<<prefixArr[preId]->getPrelen()<<"\t ";
					outF<<prefixArr[preId]->getPrefix()<<"/"<<prefixArr[preId]->getPrelen()<<"\t ";
				}
			}
			outF<<endl;
		}
		outF.close();
		//cout<<"\n";
	}

	void printM(char* ipaddr, uint64_t searchtime, char* bpm, int bmpid)
	{
		float time = float(searchtime)/CPUF;
		ofstream outF;

		outF.open(opfile, ios::app);
		if(outF.is_open())
		{
			outF<<" "<<ipaddr<<"\t"<<bpm<<"/"<<prefixArr[bmpid]->getPrelen()<<"\t"<<time<<"\n";
		}
		outF.close();
	}

	void readPrefix()
	{
		char *ddip, *ipaddr, *r;	//dotted decimal ip
		int i, len, l[3], num;	//length in bits
		unsigned int maskval, valbin;		
		ifstream inF;
		inF.open(prfile);
		ddip = (char*)malloc(sizeof(char)*20);
		ipaddr = (char*)malloc(sizeof(char)*20);
		prcnt=0;

		while(!inF.eof())
		{
			//read file and store prefix values in array
			inF >> ddip; inF >> len;
            		strcpy(ipaddr,ddip);
			if(!inF.eof())
			{
				prcnt++;
				//Tokenize to get each byte.
                		r = strtok(ddip,".");
               			i=0;
               			while(r!=NULL)
               			{
	       				l[i++] = atoi(r);
               				r = strtok(NULL,".");
               				if(l[i-1]>255)
               					cout<<"Something wrong!";
               			 }
				num = 24-len;
				valbin = (l[0] * pow2[16]) + (l[1] * pow2[8]) + l[2]; //convert to bin
				maskval = (pow2[24] - 1) - (pow2[num]-1); //remove unwanted last few bits. retain rest ones.
				maskval = (maskval & valbin);		//will now have correct mask for len no. of bits.
				//insert into prefix array
				prefixArr[prcnt] = new preNode(prcnt, len, ipaddr, maskval);
	//			cout<<" Prefix : "<<prefixArr[prcnt]->getPrefix()<<"/"<<prefixArr[prcnt]->getPrelen();
				//Update trie
				if(A==1)
					BT.insert(l[0], l[1], l[2], len, prcnt);
				else if(A==3)
				{
					hashTable[len]->insert(l[0], l[1], l[2], prcnt, maskval);
				}
				else
					mops.addMtrie(l[0], l[1], l[2], len, prcnt, maskval);
			}
	//		cout<<endl;
		}
		inF.close();
		/*if(A==3)
			markHtable();*/
	}

	void readIp()
	{
		char *ipaddr, *ddip, *r, *bmp;	//dotted decimal ip
		int i, ipnumcnt, l[3];	//length in bits
		unsigned long ipbin, start, end;
		uint64_t t1, t2, searchtime;
		ifstream inF;
		inF.open(ipfile);
		ipaddr = (char*)malloc(sizeof(char)*20);
		ddip = (char*)malloc(sizeof(char)*20);
		bmp = (char*)malloc(sizeof(char)*20);
		ipnumcnt = 0;

		while(!inF.eof())
		{
			//read file and get the ip value
			inF >> ipaddr;
            		strcpy(ddip, ipaddr);
			if(!inF.eof())
			{
				ipnumcnt++;
				//Tokenize to get each byte.
				r = strtok(ddip,".");
				i=0;
				while(r!=NULL)
				{
					l[i++] = atoi(r);
					r = strtok(NULL,".");
				}
				//Search in trie for bmp
				int preId;
				ipbin = (l[0]*pow2[16])+(l[1]*pow2[8])+(l[2]);
				if(A==1)
				{
					//clear binMatches array
					for(int j=0; j<24; j++)
						BinMatches[j]=0;
					rdtsc(t1);
					preId = BT.search(l[0], l[1], l[2]);
				}
				else if(A==3)
				{
					//clear HashMatches array
					for(int j=0; j<24; j++)
						HashMatches[j]=0;
					rdtsc(t1);
					preId = hops.findHbmp(l[0], l[1], l[2]);
				}
				else
				{
					rdtsc(t1);
					preId = mops.searchMtrie(l[0], l[1], l[2]);
				}
				bmp = prefixArr[preId]->getPrefix();
				rdtsc(t2);
				searchtime = t2-t1;
				TotalTime += searchtime;
				//cout<<"IP: "<<ipaddr<<"("<<ipbin<<")"<<" BMP: "<<bmp<<"/"<<prefixArr[preId]->getPrelen()<<"("<<prefixArr[preId]->getMask()<<")"<<" Time: "<<t2-t1<<"ns/tics";
				if(A==1)
					printAllMatches(ipaddr, BinMatches, 24, searchtime, bmp, preId);
				else if(A==2)
					printM(ipaddr, searchtime, bmp, preId);
				else if(A==3)
					printAllMatches(ipaddr, HashMatches, 24, searchtime, bmp, preId);
			}
			//cout<<endl;
		}
		inF.close();
		AvgTime = (float)(TotalTime)/(float)(ipnumcnt);
		AvgTime = AvgTime/(float)(CPUF);
		cout<<" Avg Look-up time per IP: "<<AvgTime<<endl; 
	}
};

void check()
{
	cout<<" Prefix file: "<<prfile<<endl;
	cout<<" Input file: "<<ipfile<<endl;
	cout<<" Output file: "<<opfile<<endl;
	cout<<" Prefix lenght: "<<W<<" Algorithm type: "<<A<<" (1-B, 2-M, 3-H)\n";
}

void printUsage()
{
    cout<<"Usage is " << prgname << " [options] <values>";
    cout<<" Options:\n";
    cout<<" -p <Prefix file name>\n";
    cout<<" -i <Input Addresses' file>\n";
    cout<<" -o <Outputfile>\n";
    cout<<" -W <24> Maximum number of bits in the prefix\n";
    cout<<" -a <BestMatchPrefix algo type[ B | M | H ]> B-binaryTrie, M-multiplestride, H-hash table\n";

    exit(8);
}

/* main function to parse command line*/
int main(int argc, char *argv[])
{

	/*allocate memory to hold file names*/
	prfile = (char*)malloc(sizeof(char)*30);
	ipfile = (char*)malloc(sizeof(char)*30);
	opfile = (char*)malloc(sizeof(char)*30);
	notfound = (char*)malloc(sizeof(char)*30);
	/*Set default values*/
	W=24; A=2;	//W - prefix length, A - algo type 1-binary trie, 2-multiplestride, 3-hash table
	TotalTime = AvgTime = 0;

	strcpy(prfile, "prefixfile");
	strcpy(ipfile, "inputfile");
	strcpy(opfile, "outputfile");
	strcpy(notfound, "NoMatches");
	prefixArr[prcnt] = new preNode(prcnt, prcnt, notfound, 0);

	/*parse commandline*/
	prgname = argv[0];
	if(argc<3)
		printUsage();

	while((argc > 1) && (argv[1][0] == '-'))
	{
		switch(argv[1][1])
		{
			case 'p':
				strcpy(prfile,argv[2]);
				break;
			case 'i':
				strcpy(ipfile,argv[2]);
				break;
			case 'o':
				strcpy(opfile,argv[2]);
				break;
			case 'W':
				W = atoi(argv[2]);
				if(W>24||W<8)
				{
					cout<<"\n Taking W as default of 24";
					W = 24;
				}
				break;
			case 'a':
				if(strcmp(argv[2],"B") == 0)
					A=1;
				else if(strcmp(argv[2],"M") == 0)
					A=2;
				else if(strcmp(argv[2],"H") == 0)
					A=3;
				break;
			default:
				fprintf(stderr," Bad option: %s\n",argv[1]);
				printUsage();
		}
		argv = argv+2; //move in steps of 2.
		argc = argc-2; 
	}

	check();

    if(A==3) //create the hash tables
    {
        for(int j=1; j<25; j++)
        {
            hashTable[j] = new hTable(j);
        }
    }

	FileOps fops;
	fops.readPrefix();
	fops.readIp();

	return(0);
}
