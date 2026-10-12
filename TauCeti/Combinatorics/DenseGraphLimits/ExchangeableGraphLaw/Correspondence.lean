/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Existence
import TauCeti.Combinatorics.DenseGraphLimits.Separation.Inverse
import TauCeti.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Exchangeable graph laws correspond to mixing measures on graphon space

The mixture map from probability measures on the graphon space over the unit interval to
exchangeable graph laws is injective (`mixtureExchangeableLaw_injective`): a mixture law determines
its mixing measure. Together with existence (`exists_mixtureExchangeableLaw_eq`) this makes the
mixture map a bijection, packaged as `mixtureExchangeableLawEquiv`. This is the Diaconis–Janson
correspondence at the level of the finite marginals. Uniqueness holds on the graphon quotient
`GraphonSpaceI`, not among graphon representatives.

## Main definitions

* `TauCeti.DenseGraphLimits.mixtureExchangeableLawEquiv` — the mixture map, as an equivalence
  between probability measures on `GraphonSpaceI` and exchangeable graph laws.

## Main results

* `TauCeti.DenseGraphLimits.mixtureExchangeableLaw_injective` — **a mixture law determines its
  mixing measure.**
* `TauCeti.DenseGraphLimits.mixtureExchangeableLawEquiv_apply` — the equivalence is the mixture
  map.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Section 11.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

/-- **Uniqueness of the mixing measure.** Two probability measures on `GraphonSpaceI` with the same
mixture law are equal. -/
theorem mixtureExchangeableLaw_injective :
    Function.Injective
      (mixtureExchangeableLaw : ProbabilityMeasure GraphonSpaceI → ExchangeableGraphLaw) := by
  intro P Q h
  -- the homomorphism densities are test functions that separate the points of graphon space
  refine ProbabilityMeasure.toMeasure_injective
    (TauCeti.MeasureTheory.ext_of_forall_mem_submonoid_integral_eq_of_polish
      (S := homDensitySubmonoid) (fun x y hxy => ?_) (mixtureExchangeableLaw_eq_iff.1 h))
  by_contra! hsep
  exact hxy ((graphonSpace_ext_iff_homDensity x y).2 fun n F _ => by
    simpa using hsep _ (homDensityBCF_mem_homDensitySubmonoid F))

/-- **The Diaconis–Janson correspondence.** The mixture map is an equivalence between probability
measures on `GraphonSpaceI` and exchangeable graph laws. -/
def mixtureExchangeableLawEquiv : ProbabilityMeasure GraphonSpaceI ≃ ExchangeableGraphLaw :=
  Equiv.ofBijective mixtureExchangeableLaw
    ⟨mixtureExchangeableLaw_injective, exists_mixtureExchangeableLaw_eq⟩

/-- The forward map of `mixtureExchangeableLawEquiv` is the mixture map. -/
@[simp]
theorem mixtureExchangeableLawEquiv_apply (P : ProbabilityMeasure GraphonSpaceI) :
    mixtureExchangeableLawEquiv P = mixtureExchangeableLaw P := (rfl)

end DenseGraphLimits

end TauCeti
