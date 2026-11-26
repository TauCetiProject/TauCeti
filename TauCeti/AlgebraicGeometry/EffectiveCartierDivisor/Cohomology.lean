/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.IdealSheaf.MulSequence
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal

/-!
# Cohomology on a sum of divisors

Let `X` be a scheme over a field `k`, let `J` be the ideal sheaf of an effective Cartier divisor
`D` and `I` an ideal sheaf, for instance that of a second effective Cartier divisor `E`, so that
`V(I * J)` is the possibly nonreduced divisor `D + E`. Twisting the exact sequence
`0 ⟶ J ⊗ ι_* 𝒪_{V(I)} ⟶ ι_* 𝒪_{V(I * J)} ⟶ ι_* 𝒪_{V(J)} ⟶ 0`
(`Scheme.IdealSheafData.shortExact_mulSequence`) by a vector bundle `F` on `X` and applying the
projection formula identifies its terms with the direct images of the restrictions of `F ⊗ J`,
`F` and `F` to `V(I)`, `V(I * J)` and `V(J)`; here `F ⊗ J` is a vector bundle because `J` is
invertible. So, degree by degree, if the restrictions of `F` to `V(J)` and of `F ⊗ J` to `V(I)`
have finite-dimensional `H^i` then so does the restriction of `F` to `V(I * J)`
(`FiniteLocallyFreeSheaf.finiteDimensional_cohomology_pullback_subschemeι_mul`).

If these restrictions have finite-dimensional `H^i` for all `i < n`, and `Hⁿ` of the restriction
of `F ⊗ J` to `V(I)` vanishes, then the Euler characteristics truncated at `n` satisfy

  `χ(F|_{V(I * J)}) = χ(F|_{V(J)}) + χ((F ⊗ J)|_{V(I)})`

(`FiniteLocallyFreeSheaf.eulerCharBelow_pullback_subschemeι_mul`). For curves this is used with
`n = 2`, where `χ = dim H⁰ - dim H¹`. The line-bundle cases, with `F ⊗ J` written as the tensor
product of line bundles, are `InvertibleSheaf.finiteDimensional_cohomology_pullback_subschemeι_mul`
and `InvertibleSheaf.eulerCharBelow_pullback_subschemeι_mul`.

## References

* [The Stacks Project, Section 33.44, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ):
  degrees on proper curves, computed through exact sequences of this kind.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules Scheme.Modules Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

namespace FiniteLocallyFreeSheaf

variable (F : FiniteLocallyFreeSheaf X) (I : X.IdealSheafData) {J : X.IdealSheafData}
  (hJ : J.IsEffectiveCartier)

/-- The exact sequence of the product `I * J` of ideal sheaves, twisted by `F`. -/
private abbrev twistedMulSequence (J : X.IdealSheafData) : ShortComplex X.Modules :=
  (mulSequence I J).map (tensorLeft F.obj)

private lemma shortExact_twistedMulSequence (J : X.IdealSheafData) :
    (twistedMulSequence F I J).ShortExact :=
  Scheme.Modules.shortExact_map_tensorLeft F.obj (shortExact_mulSequence I J)

/-- The first term of the twisted sequence is `(F ⊗ J) ⊗ ι_* 𝒪_{V(I)}`. -/
private def twistedMulSequenceX₁Iso : (twistedMulSequence F I J).X₁ ≅
    (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf).obj ⊗
      I.pushforwardSubscheme :=
  (α_ F.obj J.sheaf I.pushforwardSubscheme).symm ≪≫
    whiskerRightIso (whiskerLeftIso F.obj (eqToIso hJ.toInvertibleSheaf_obj.symm)) _

private lemma finiteDimensional_cohomology_twistedMulSequence_X₂ {i : ℕ}
    (hI : FiniteDimensional k (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
      (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj i))
    (hJF : FiniteDimensional k
      (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj i)) :
    FiniteDimensional k (Cohomology (twistedMulSequence F I J).X₂ i) := by
  have : FiniteDimensional k (Cohomology (twistedMulSequence F I J).X₁ i) :=
    (finiteDimensional_cohomology_congr k (twistedMulSequenceX₁Iso F I hJ) i).mpr
      ((I.finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k _ i).mpr hI)
  have : FiniteDimensional k (Cohomology (twistedMulSequence F I J).X₃ i) :=
    (J.finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k F i).mpr hJF
  exact finiteDimensional_cohomology_X₂ k X (shortExact_twistedMulSequence F I J) i

/-- **Finiteness of cohomology on a sum of divisors.** Let `J` be the ideal sheaf of an effective
Cartier divisor and `F` a vector bundle. If the restrictions of `F` to `V(J)` and of `F ⊗ J` to
`V(I)` have finite-dimensional `H^i`, then so does the restriction of `F` to `V(I * J)`. -/
theorem finiteDimensional_cohomology_pullback_subschemeι_mul {i : ℕ}
    (hI : FiniteDimensional k (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
      (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj i))
    (hJF : FiniteDimensional k
      (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj i)) :
    FiniteDimensional k
      (Cohomology ((FiniteLocallyFreeSheaf.pullback (I * J).subschemeι).obj F).obj i) :=
  ((I * J).finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k F i).mp
    (finiteDimensional_cohomology_twistedMulSequence_X₂ k F I hJ hI hJF)

/-- **Euler characteristics on a sum of divisors.** Let `J` be the ideal sheaf of an effective
Cartier divisor on a scheme `X` over `k`, `I` an ideal sheaf and `F` a vector bundle. If the
restrictions of `F` to `V(J)` and of `F ⊗ J` to `V(I)` have finite-dimensional `H^i` for `i < n`,
and `Hⁿ` of the restriction of `F ⊗ J` to `V(I)` vanishes, then the Euler characteristics
truncated at `n` satisfy `χ(F|_{V(I * J)}) = χ(F|_{V(J)}) + χ((F ⊗ J)|_{V(I)})`. -/
theorem eulerCharBelow_pullback_subschemeι_mul (n : ℕ)
    (hI : ∀ i < n, FiniteDimensional k (Cohomology ((FiniteLocallyFreeSheaf.pullback
      I.subschemeι).obj (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj
        i))
    (hJF : ∀ i < n, FiniteDimensional k
      (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj i))
    (hIn : Subsingleton (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
      (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj n)) :
    eulerCharBelow k (I * J).subscheme
        ((FiniteLocallyFreeSheaf.pullback (I * J).subschemeι).obj F).obj n =
      eulerCharBelow k J.subscheme ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj n +
        eulerCharBelow k I.subscheme ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
          (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj n := by
  have hS := shortExact_twistedMulSequence F I J
  have h₁ (i : ℕ) (hi : i < n) (_ : 0 < i) :
      FiniteDimensional k (Cohomology (twistedMulSequence F I J).X₁ i) :=
    (finiteDimensional_cohomology_congr k (twistedMulSequenceX₁Iso F I hJ) i).mpr
      ((I.finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k _ i).mpr (hI i hi))
  have hvan : Subsingleton (Cohomology (twistedMulSequence F I J).X₁ n) :=
    (cohomologyBaseLinearEquivOfIso k (twistedMulSequenceX₁Iso F I hJ)
      n).toEquiv.subsingleton_congr.mpr
        ((I.subsingleton_cohomology_tensor_pushforwardSubscheme_iff _ n).mpr hIn)
  have h := eulerCharBelow_eq_add k hS n h₁
    (fun i hi ↦ finiteDimensional_cohomology_twistedMulSequence_X₂ k F I hJ (hI i hi) (hJF i hi))
    hvan
  rw [eulerCharBelow_congr k (twistedMulSequenceX₁Iso F I hJ) n] at h
  -- The other two terms are `(tensorLeft F).obj` of `ι_* 𝒪_{V(I * J)}` and `ι_* 𝒪_{V(J)}`, which
  -- unfold to `F ⊗ ι_* 𝒪_{V(I * J)}` and `F ⊗ ι_* 𝒪_{V(J)}`; `change` displays them in this form
  -- for the projection formula.
  change eulerCharBelow k X (F.obj ⊗ (I * J).pushforwardSubscheme) n = _ + eulerCharBelow k X
    (F.obj ⊗ J.pushforwardSubscheme) n at h
  rw [eulerCharBelow_tensor_pushforwardSubscheme, eulerCharBelow_tensor_pushforwardSubscheme,
    eulerCharBelow_tensor_pushforwardSubscheme] at h
  rw [h, add_comm]

end FiniteLocallyFreeSheaf

namespace InvertibleSheaf

variable (L : InvertibleSheaf X) (I : X.IdealSheafData) {J : X.IdealSheafData}
  (hJ : J.IsEffectiveCartier)

/-- **Finiteness of cohomology on a sum of divisors**, for a line bundle `L`: if the restrictions of
`L` to `V(J)` and of `L ⊗ J` to `V(I)` have finite-dimensional `H^i`, where `J` is the ideal sheaf
of an effective Cartier divisor, then so does the restriction of `L` to `V(I * J)`. -/
theorem finiteDimensional_cohomology_pullback_subschemeι_mul {i : ℕ}
    (hI : FiniteDimensional k
      (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj i))
    (hJL : FiniteDimensional k (Cohomology ((pullback J.subschemeι).obj L).obj i)) :
    FiniteDimensional k (Cohomology ((pullback (I * J).subschemeι).obj L).obj i) := by
  have h := FiniteLocallyFreeSheaf.finiteDimensional_cohomology_pullback_subschemeι_mul k
    ((toFiniteLocallyFree X).obj L) I hJ
    ((finiteDimensional_cohomology_congr k (pullbackToFiniteLocallyFreeTensorIso _ _ _) i).mpr
      hI)
    (by rwa [pullback_toFiniteLocallyFree_obj_obj])
  rwa [pullback_toFiniteLocallyFree_obj_obj] at h

/-- **Euler characteristics on a sum of divisors**, for a line bundle `L`: if the restrictions of
`L` to `V(J)` and of `L ⊗ J` to `V(I)` have finite-dimensional `H^i` for `i < n`, where `J` is the
ideal sheaf of an effective Cartier divisor, and `Hⁿ` of the restriction of `L ⊗ J` to `V(I)`
vanishes, then `χ(L|_{V(I * J)}) = χ(L|_{V(J)}) + χ((L ⊗ J)|_{V(I)})` for the Euler
characteristics truncated at `n`. -/
theorem eulerCharBelow_pullback_subschemeι_mul (n : ℕ)
    (hI : ∀ i < n, FiniteDimensional k
      (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj i))
    (hJL : ∀ i < n, FiniteDimensional k (Cohomology ((pullback J.subschemeι).obj L).obj i))
    (hIn : Subsingleton
      (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj n)) :
    eulerCharBelow k (I * J).subscheme ((pullback (I * J).subschemeι).obj L).obj n =
      eulerCharBelow k J.subscheme ((pullback J.subschemeι).obj L).obj n +
        eulerCharBelow k I.subscheme
          ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj n := by
  have e := pullbackToFiniteLocallyFreeTensorIso I.subschemeι L hJ.toInvertibleSheaf
  have h := FiniteLocallyFreeSheaf.eulerCharBelow_pullback_subschemeι_mul k
    ((toFiniteLocallyFree X).obj L) I hJ n
    (fun i hi ↦ (finiteDimensional_cohomology_congr k e i).mpr (hI i hi))
    (fun i hi ↦ by rw [pullback_toFiniteLocallyFree_obj_obj]; exact hJL i hi)
    ((cohomologyBaseLinearEquivOfIso k e n).toEquiv.subsingleton_congr.mpr hIn)
  rwa [eulerCharBelow_congr k e n, pullback_toFiniteLocallyFree_obj_obj,
    pullback_toFiniteLocallyFree_obj_obj] at h

end InvertibleSheaf

end

end TauCeti.AlgebraicGeometry
