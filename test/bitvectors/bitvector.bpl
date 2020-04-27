
// Note (Seth) this test stolen from boogie/Test/bitvectors/bv1.bpl
// seems like a good test of basic bv functionality, we can split 
// it into multiple files to test more incrementally


procedure main(x : bv32) returns(r : bv32)
{
  var q : bv64;

  block1:
  	r := 17bv32;
	assert r == r;
    assert r[32:0] == r[32:0];
    assert 0bv2 ++ r[12:0] == 0bv2 ++ r[12:0];
    r := 17bv10 ++ 17bv22;
  	// r := 17;
    q := 420000000000bv64;
    q := 8444249301319680000bv64;
    q := 16444249301319680000bv64;
  return;
}

