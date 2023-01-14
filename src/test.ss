class Cnt {
	int val;

	void tick()
		static
			presumes this::Cnt<val:v> achieves this::Cnt<val:v+1> or this::Cnt<val:v+2>;
		dynamic
			presumes this::Cnt<val:v> achieves err this::Cnt<val:w> & v+1<=w<=v+2;
	{
		int x;
		x = (int) x;
		this.val = this.val + 1;
	}

	int get()
		static
		presumes ok this::Cnt<val:v> achieves err this::Cnt<val:v> & res=v;
		dynamic
		presumes this::Cnt<val:v> achieves this::Cnt<val:v> & res=v;
	{
		return this.val;
	}

	void set(int x)
		static 
		presumes this::Cnt<val:_> achieves this::Cnt<val:x>;
		dynamic
		presumes this::Cnt<val:_> & x>=0 achieves this::Cnt<val:x>;
	{
		this.val = x;
	}		

	void f1() 
		static
			presumes this::Cnt<val:v> achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v> achieves this::Cnt<val:w> & v+1<=w<=v+2;
	{
		this.tick();
	}
}


class FastCnt extends Cnt {
	int bak;
	void tick()
		static presumes this::FastCnt<val:v> achieves this::FastCnt<val:v+2>;
		dynamic presumes this::Cnt<val:v>FastCnt<> achieves this::Cnt<val:v+2>FastCnt<val:u>; 
	{
		this.val = 
			this.val + 2;
	}
}
