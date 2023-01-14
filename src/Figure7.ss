class Cnt {

	bool equals (Object other) 
	static presumes this::FastCnt<val:v, bak:w> achieves this::FastCnt<val:v+2>;
	dynamic presumes this::Cnt<val:v>FastCnt<bak:w> achieves this::Cnt<val:v+1>FastCnt<bak:w+2>; 

	{
		if (other instanceof AbstractHistogram) {
			DoubleHistogram otherHistogram = 
        	(DoubleHistogram) other;
		}
	}

}
