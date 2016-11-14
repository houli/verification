predicate isPrefixPred(pre: string, str: string)
{
	(|pre| == 0) || ((|pre| <= |str|) && pre == str[..|pre|])
}

predicate isNotPrefixPred(pre: string, str: string)
{
	// (|pre| > 0) && ((|pre| > |str|) || pre != str[..|pre|])
	// converted to disjunctive normal form

	!((|pre| <= 0) || (|pre| <= |str|)) || !((|pre| <= 0) || (pre == str[..|pre|]))

}

// Sanity check: Dafny should be able to automatically prove the following lemma
	lemma PrefixNegationLemma(pre: string, str: string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


predicate isSubstringPred(sub: string, str: string)
{
	exists i :: (0 <= i < |str| && isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub: string, str: string)
{
	forall i :: (0 <= i < |str| ==> isNotPrefixPred(sub, str[i..]) )
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub: string, str: string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k: nat, str1: string, str2: string)
{
	k == 0 || exists x :: (isSubstringPred(x, str1) && |x| == k && isSubstringPred(x, str2))
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	 k > 0 && forall x :: (isSubstringPred(x, str1) && |x| == k ==> isNotSubstringPred(x, str2))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k: nat, str1: string, str2: string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
