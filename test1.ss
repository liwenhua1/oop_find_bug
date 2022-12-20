class Cnt {
	int val;

	void tick()
		static
			presumes this::Cnt<v> achieves this::Cnt<v+1>;
		dynamic
			presumes this::Cnt<v> achieves err this::Cnt<w> & v+1<=w<=v+2;
	{
		int temp = this.val;
		int temp1 = temp + 1;
		this.val = temp1; 
	}
}
