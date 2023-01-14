class Cnt {
	int val;
	int val1;

	void tick()
		static
			presumes this::Cnt<val:v, val1:w> achieves this::Cnt<val:v+1>;
		dynamic
			presumes this::Cnt<val:v, val1:w> achieves err this::Cnt<val1:w> & v+1<=w<=v+2;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1; 
		int temp = this.val1;
		int temp1 = temp - 1;
		this.val1 = temp1; 
	}

    void normal_cast()
         static
			presumes x::Cnt<val:v, val1:w>FastCnt<> achieves this::Cnt<val:v+1>;
        {
            y = (Cnt) x;
        }

     void instanceof1()
         static
			presumes x::Cnt<val:v, val1:w>FastCnt<> achieves this::Cnt<val:v+1>;
        {
            y = x instanceof Cnt;
            z = x instanceof FastCnt;
        }

	void bug1()
		static
			presumes this::Cnt<val:v, val1:w> & x=null achieves this::Cnt<val:v+1>;
	{
		x.val = 5;
	}

    void bug2()
		static
			presumes this::Cnt<val:v, val1:w> & x=null achieves this::Cnt<val:v+1>;
	{
		y = x.val ;
	}

	void bug3()
		static
			presumes x::Cnt<val:v, val1:w> achieves this::Cnt<val:v+1>;
		
	{
		y = (FastCnt) x;
 	}
}

class FastCnt extends Cnt {
	int bak;
}