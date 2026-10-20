import TailBound

-- No refresh or analytic conclusions are assumed by these theorem statements.
#check TailBound.lemma2_sharp
#check TailBound.lemma2_sharp_of_bounds
#check TailBound.RefreshData.fixed_band_sharp_explicit
#check TailBound.main_theorem
#print axioms TailBound.lemma2_sharp
#print axioms TailBound.lemma2_sharp_of_bounds
#print axioms TailBound.RefreshData.fixed_band_sharp_explicit
#print axioms TailBound.main_theorem
#print TailBound.marginalBandConstant
#print TailBound.refreshRatioBound
example : TailBound.ManuscriptTheorem1 := TailBound.main_theorem
