class Cnt {
	int val;

	virtual void tick()
		static
			presumes this::Cnt<val:v>  achieves this::Cnt<val:v+1> ;
		dynamic
			presumes this::Cnt<val:v> achieves this::Cnt<val:v+1> ;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1;
	}
}


class FastCnt extends Cnt {
	int bak;
	override void tick()
		static presumes this::FastCnt<val:v, bak:w>   achieves this::FastCnt<val:v+1, bak:w+2> ;
		dynamic presumes this::Cnt<val:v>FastCnt<bak:w>  achieves this::Cnt<val:v+1>FastCnt<bak:w+2> ; 
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1;
		
		int temp2 = this.bak;
		int temp3 = temp2 + 2;
		this.bak = temp3;
	}
}
