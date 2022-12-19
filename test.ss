class Cnt {
	int val;

	void tick()
		static
			presumes this::Cnt<v> achieves this::Cnt<v+1> or this::Cnt<v+2>;
		dynamic
			presumes this::Cnt<v> achieves err this::Cnt<w> & v+1<=w<=v+2;
	{
		int x;
		x = (int) x;
		this.val = this.val + 1;
	}

	int get()
		static
		presumes ok this::Cnt<v> achieves err this::Cnt<v> & res=v;
		dynamic
		presumes this::Cnt<v> achieves this::Cnt<v> & res=v;
	{
		return this.val;
	}

	void set(int x)
		static 
		presumes this::Cnt<_> achieves this::Cnt<x>;
		dynamic
		presumes this::Cnt<_> & x>=0 achieves this::Cnt<x>;
	{
		this.val = x;
	}		

	void f1() 
		static
			presumes this::Cnt<v> achieves this::Cnt<v+1>;
		dynamic
			presumes this::Cnt<v> achieves this::Cnt<w> & v+1<=w<=v+2;
	{
		this.tick();
	}
}


class FastCnt extends Cnt {
	int bak;
	void tick()
		static presumes this::FastCnt<v> achieves this::FastCnt<v+2>;
		dynamic presumes this::Cnt<v>FastCnt<> achieves this::Cnt<v+2>FastCnt<u>; 
	{
		this.val = 
			this.val + 2;
	}
}
