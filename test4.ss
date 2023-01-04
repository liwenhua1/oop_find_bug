class Cnt {
	int val;
	int val1;
    
	void test1()
		static
			presumes this::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1; 
		int temp2 = this.val1;
		int temp3 = temp2 - 1;
		this.val1 = temp3; 
		
	}

	void test2()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
	{
		x.val = 1;
		
	}

	void instanceof1()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
	{
		y = x instanceof FastCnt;
		
	}
	void instanceof2()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
	{
		y = x instanceof Cnt;
		
	}
    void instanceof3()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves this::Cnt<val:v+1>;
	{
		y = x instanceof FastCnt;
		
	}
	 void instanceof4()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n> achieves this::Cnt<val:v+1>;
	{
		y = x instanceof Cnt;
		
	}

	void normal_cast()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
	{
		y = (Cnt) x;
		
	}

	void cast_error1()
		static
			presumes x::Cnt<val:v, val1:w>  achieves this::Cnt<val:v+1>;
	{
		y = (FastCnt) x;
		
	}
	void cast_error2()
		static
			presumes x::Cnt<val:v, val1:w>FastCnt<bak:n>  achieves this::Cnt<val:v+1>;
	{
		y = (FastCnt) x;
		
	}

	void load_error()
		static
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves this::Cnt<val:v+1>;
	{
		y = x.val;
		
	}

	void write_error()
		static
			presumes this::Cnt<val:v, val1:w>FastCnt<bak:n> & x = null  achieves this::Cnt<val:v+1>;
	{
		x.val = this.val;
		
	}
	
}

class FastCnt extends Cnt {
	int bak;
}