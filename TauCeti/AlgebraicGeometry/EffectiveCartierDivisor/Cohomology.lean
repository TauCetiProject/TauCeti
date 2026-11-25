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

When `X` lies over a commutative ring `R` rather than a field, the same sequence gives the same
relations between the `R`-lengths of the cohomology groups, with no finiteness hypotheses:
`FiniteLocallyFreeSheaf.length_cohomology_pullback_subschemeι_mul_le` bounds the length of
`Hⁱ(F|_{V(I * J)})`, and `FiniteLocallyFreeSheaf.length_cohomology_pullback_subschemeι_mul` is the
additivity of `χ = ℓ H⁰ - ℓ H¹` written without subtraction, given the vanishing of `H²` of the
restriction of `F ⊗ J` to `V(I)`; the line-bundle cases are
`InvertibleSheaf.length_cohomology_pullback_subschemeι_mul_le` and
`InvertibleSheaf.length_cohomology_pullback_subschemeι_mul`. This is the form needed for divisors
inside the special fibre of a scheme over a local ring, which are schemes over the residue field
although `X` is not.

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

section Length

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- The first term of the twisted sequence has the cohomology, as an `R`-module, of the
restriction of `F ⊗ J` to `V(I)`. -/
private lemma length_cohomology_twistedMulSequence_X₁ (i : ℕ) :
    Module.length R (Cohomology (twistedMulSequence F I J).X₁ i) =
      Module.length R (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
        (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj i) :=
  ((cohomologyBaseLinearEquivOfIso R (twistedMulSequenceX₁Iso F I hJ ≪≫
    I.tensorPushforwardSubschemeIso _) i).trans
      (I.subschemeι.cohomologyPushforwardBaseLinearEquiv R _ i)).length_eq

/-- `F ⊗ ι_* 𝒪_{V(K)}` has the cohomology, as an `R`-module, of the restriction of `F` to
`V(K)`. -/
private lemma length_cohomology_tensor_pushforwardSubscheme (K : X.IdealSheafData) (i : ℕ) :
    Module.length R (Cohomology (F.obj ⊗ K.pushforwardSubscheme) i) =
      Module.length R
        (Cohomology ((FiniteLocallyFreeSheaf.pullback K.subschemeι).obj F).obj i) :=
  ((cohomologyBaseLinearEquivOfIso R (K.tensorPushforwardSubschemeIso F) i).trans
    (K.subschemeι.cohomologyPushforwardBaseLinearEquiv R _ i)).length_eq

/-- The middle term of the twisted sequence has the cohomology, as an `R`-module, of the
restriction of `F` to `V(I * J)`. The term unfolds to `F ⊗ ι_* 𝒪_{V(I * J)}`. -/
private lemma length_cohomology_twistedMulSequence_X₂ (i : ℕ) :
    Module.length R (Cohomology (twistedMulSequence F I J).X₂ i) =
      Module.length R
        (Cohomology ((FiniteLocallyFreeSheaf.pullback (I * J).subschemeι).obj F).obj i) :=
  length_cohomology_tensor_pushforwardSubscheme F R (I * J) i

/-- The last term of the twisted sequence has the cohomology, as an `R`-module, of the
restriction of `F` to `V(J)`. The term unfolds to `F ⊗ ι_* 𝒪_{V(J)}`. -/
private lemma length_cohomology_twistedMulSequence_X₃ (i : ℕ) :
    Module.length R (Cohomology (twistedMulSequence F I J).X₃ i) =
      Module.length R
        (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj i) :=
  length_cohomology_tensor_pushforwardSubscheme F R J i

/-- **Lengths of cohomology on a sum of divisors.** Let `X` be a scheme over a commutative ring
`R`, `J` the ideal sheaf of an effective Cartier divisor, `I` an ideal sheaf and `F` a vector
bundle. Then the `R`-length of `Hⁱ` of the restriction of `F` to `V(I * J)` is at most the sum of
those of the restrictions of `F ⊗ J` to `V(I)` and of `F` to `V(J)`. -/
theorem length_cohomology_pullback_subschemeι_mul_le (i : ℕ) :
    Module.length R
        (Cohomology ((FiniteLocallyFreeSheaf.pullback (I * J).subschemeι).obj F).obj i) ≤
      Module.length R (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
          (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj i) +
        Module.length R
          (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj i) := by
  have h := length_cohomology_X₂_le_add R (shortExact_twistedMulSequence F I J) i
  rwa [length_cohomology_twistedMulSequence_X₁ F I hJ R, length_cohomology_twistedMulSequence_X₂,
    length_cohomology_twistedMulSequence_X₃] at h

/-- **Euler characteristics on a sum of divisors, over a base ring.** Let `X` be a scheme over a
commutative ring `R`, `J` the ideal sheaf of an effective Cartier divisor, `I` an ideal sheaf and
`F` a vector bundle, and suppose that `H²` of the restriction of `F ⊗ J` to `V(I)` vanishes. Then
the `R`-lengths `ℓ` of the cohomology of the restrictions satisfy
`ℓ H⁰((F ⊗ J)|_{V(I)}) + ℓ H⁰(F|_{V(J)}) + ℓ H¹(F|_{V(I * J)}) =
  ℓ H⁰(F|_{V(I * J)}) + ℓ H¹((F ⊗ J)|_{V(I)}) + ℓ H¹(F|_{V(J)})`,
that is, `χ(F|_{V(I * J)}) = χ(F|_{V(J)}) + χ((F ⊗ J)|_{V(I)})` for `χ = ℓ H⁰ - ℓ H¹` when these
lengths are finite. Unlike `FiniteLocallyFreeSheaf.eulerCharBelow_pullback_subschemeι_mul`, `X`
need not lie over a field. -/
theorem length_cohomology_pullback_subschemeι_mul
    (hI₂ : Subsingleton (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
      (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj 2)) :
    Module.length R (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
          (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj 0) +
        Module.length R
          (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj 0) +
        Module.length R
          (Cohomology ((FiniteLocallyFreeSheaf.pullback (I * J).subschemeι).obj F).obj 1) =
      Module.length R
          (Cohomology ((FiniteLocallyFreeSheaf.pullback (I * J).subschemeι).obj F).obj 0) +
        Module.length R (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj
          (F ⊗ (InvertibleSheaf.toFiniteLocallyFree X).obj hJ.toInvertibleSheaf)).obj 1) +
        Module.length R
          (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj F).obj 1) := by
  have hvan : Subsingleton (Cohomology (twistedMulSequence F I J).X₁ 2) :=
    (cohomologyBaseLinearEquivOfIso R (twistedMulSequenceX₁Iso F I hJ)
      2).toEquiv.subsingleton_congr.mpr
        ((I.subsingleton_cohomology_tensor_pushforwardSubscheme_iff _ 2).mpr hI₂)
  have h := length_cohomology_add_eq_add R (shortExact_twistedMulSequence F I J) hvan
  rwa [length_cohomology_twistedMulSequence_X₁ F I hJ R, length_cohomology_twistedMulSequence_X₁,
    length_cohomology_twistedMulSequence_X₂, length_cohomology_twistedMulSequence_X₂,
    length_cohomology_twistedMulSequence_X₃, length_cohomology_twistedMulSequence_X₃] at h

end Length

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

section Length

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- **Lengths of cohomology on a sum of divisors**, for a line bundle `L` on a scheme over a
commutative ring `R`: the `R`-length of `Hⁱ` of the restriction of `L` to `V(I * J)` is at most
the sum of those of the restrictions of `L ⊗ J` to `V(I)` and of `L` to `V(J)`, where `J` is the
ideal sheaf of an effective Cartier divisor. -/
theorem length_cohomology_pullback_subschemeι_mul_le (i : ℕ) :
    Module.length R (Cohomology ((pullback (I * J).subschemeι).obj L).obj i) ≤
      Module.length R
          (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj i) +
        Module.length R (Cohomology ((pullback J.subschemeι).obj L).obj i) := by
  have e := pullbackToFiniteLocallyFreeTensorIso I.subschemeι L hJ.toInvertibleSheaf
  have h := FiniteLocallyFreeSheaf.length_cohomology_pullback_subschemeι_mul_le
    ((toFiniteLocallyFree X).obj L) I hJ R i
  rwa [(cohomologyBaseLinearEquivOfIso R e i).length_eq, pullback_toFiniteLocallyFree_obj_obj,
    pullback_toFiniteLocallyFree_obj_obj] at h

/-- **Euler characteristics on a sum of divisors, over a base ring**, for a line bundle `L`: if
`J` is the ideal sheaf of an effective Cartier divisor on a scheme over a commutative ring `R` and
`H²` of the restriction of `L ⊗ J` to `V(I)` vanishes, then the `R`-lengths `ℓ` of the cohomology
of the restrictions satisfy
`ℓ H⁰((L ⊗ J)|_{V(I)}) + ℓ H⁰(L|_{V(J)}) + ℓ H¹(L|_{V(I * J)}) =
  ℓ H⁰(L|_{V(I * J)}) + ℓ H¹((L ⊗ J)|_{V(I)}) + ℓ H¹(L|_{V(J)})`. -/
theorem length_cohomology_pullback_subschemeι_mul
    (hI₂ : Subsingleton
      (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj 2)) :
    Module.length R
          (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj 0) +
        Module.length R (Cohomology ((pullback J.subschemeι).obj L).obj 0) +
        Module.length R (Cohomology ((pullback (I * J).subschemeι).obj L).obj 1) =
      Module.length R (Cohomology ((pullback (I * J).subschemeι).obj L).obj 0) +
        Module.length R
          (Cohomology ((pullback I.subschemeι).obj (L.tensorProduct hJ.toInvertibleSheaf)).obj 1) +
        Module.length R (Cohomology ((pullback J.subschemeι).obj L).obj 1) := by
  have e := pullbackToFiniteLocallyFreeTensorIso I.subschemeι L hJ.toInvertibleSheaf
  have h := FiniteLocallyFreeSheaf.length_cohomology_pullback_subschemeι_mul
    ((toFiniteLocallyFree X).obj L) I hJ R
    ((cohomologyBaseLinearEquivOfIso R e 2).toEquiv.subsingleton_congr.mpr hI₂)
  rwa [(cohomologyBaseLinearEquivOfIso R e 0).length_eq,
    (cohomologyBaseLinearEquivOfIso R e 1).length_eq, pullback_toFiniteLocallyFree_obj_obj,
    pullback_toFiniteLocallyFree_obj_obj] at h

end Length

end InvertibleSheaf

end

end TauCeti.AlgebraicGeometry
