/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.Weight.Fundamental
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
import TauCeti.Algebra.Lie.Basis.Root
import TauCeti.Algebra.Lie.HighestWeight.Integrability

/-!
# The fundamental modules of the pinned rational Lie algebra

For a valid Dynkin type `t`, the pinned rational Lie algebra `TauCeti.DynkinType.lieAlgebra t ht`
carries the Bourbaki-numbered Chevalley generators `eᵢ, hᵢ, fᵢ` of
`TauCeti.DynkinType.lieBasis`, and the Cartan generators `hᵢ` are the simple coroots of the base of
that basis. The **fundamental weight** `ϖᵢ` is the linear form on the Cartan subalgebra with
`ϖᵢ (hⱼ) = δᵢⱼ`, and the **fundamental module** `L(ϖᵢ)` is the irreducible highest-weight module
`TauCeti.irreducibleQuotient` of weight `ϖᵢ` over `ℚ`.

The fundamental weights are dominant integral, so `L(ϖᵢ)` is finite-dimensional over `ℚ` by the
split-field finite-dimensionality theorem
`TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral`; it is nonzero because its
canonical generator `v⁺ᵢ` is a highest weight vector. On `v⁺ᵢ` the pinned generators act as
follows: every `eⱼ` kills it, `hⱼ` acts by `δᵢⱼ`, `fⱼ` kills it for `j ≠ i`, and `fᵢ v⁺ᵢ` is a
nonzero vector killed by a second `fᵢ`. These modules are the summands of the full-weight module
from which the simply connected Chevalley group is built (Steinberg, *Lectures on Chevalley
Groups*, Chapter 3, remark after Lemma 27).

## Main definitions

* `TauCeti.DynkinType.fundamentalWeight t ht i`: the `i`-th fundamental weight `ϖᵢ`.
* `TauCeti.DynkinType.fundamentalModule t ht i`: the fundamental module `L(ϖᵢ)` over `ℚ`.
* `TauCeti.DynkinType.fundamentalGenerator t ht i`: its canonical highest weight vector `v⁺ᵢ`.

## Main results

* `TauCeti.DynkinType.isDominantIntegral_fundamentalWeight`: `ϖᵢ` is dominant integral.
* `TauCeti.DynkinType.instFiniteDimensionalFundamentalModule`: `L(ϖᵢ)` is finite-dimensional.
* `TauCeti.DynkinType.instNontrivialFundamentalModule`: `L(ϖᵢ)` is nonzero.
* `TauCeti.DynkinType.isHighestWeightVector_fundamentalGenerator`: `v⁺ᵢ` is a highest weight
  vector of weight `ϖᵢ`.
* `TauCeti.DynkinType.lie_lieBasis_f_fundamentalGenerator_ne_zero` and
  `TauCeti.DynkinType.lie_lieBasis_f_lie_lieBasis_f_fundamentalGenerator`: `fᵢ v⁺ᵢ ≠ 0` and
  `fᵢ² v⁺ᵢ = 0`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2 and Chapter 3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.1 and
  §21.2.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieModule Module

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ### Fundamental weights -/

/-- The **`i`-th fundamental weight** `ϖᵢ` of the pinned rational Lie algebra: the fundamental
weight of the base of `TauCeti.DynkinType.lieBasis` at its `i`-th simple root, so that
`ϖᵢ (hⱼ) = δᵢⱼ` on the Bourbaki-numbered Cartan generators. -/
def fundamentalWeight (i : Fin t.rank) : Dual ℚ (t.cartanSubalgebra ht) :=
  fundamentalWeightBasis (t.lieBasis ht).base ((t.lieBasis ht).baseSupportEquiv i)

/-- The value of `ϖᵢ` on the Cartan generator `hⱼ`, read as the value of the fundamental weight of
the base on the simple coroot `hⱼ`. -/
private theorem fundamentalWeight_apply_h' (i j : Fin t.rank) :
    t.fundamentalWeight ht i ((t.lieBasis ht).h' j) =
      fundamentalWeightBasis (t.lieBasis ht).base ((t.lieBasis ht).baseSupportEquiv i)
        (IsKilling.coroot (((t.lieBasis ht).baseSupportEquiv j : _) : Weight ℚ _ _)) :=
  congrArg (fundamentalWeightBasis (t.lieBasis ht).base ((t.lieBasis ht).baseSupportEquiv i))
    ((t.lieBasis ht).coroot_eq_h' j).symm

/-- `ϖᵢ (hᵢ) = 1`. -/
@[simp]
theorem fundamentalWeight_apply_h'_self (i : Fin t.rank) :
    t.fundamentalWeight ht i ((t.lieBasis ht).h' i) = 1 :=
  (t.fundamentalWeight_apply_h' ht i i).trans (fundamentalWeightBasis_apply_coroot_self _ _)

/-- `ϖᵢ (hⱼ) = 0` for `j ≠ i`. -/
theorem fundamentalWeight_apply_h'_of_ne {i j : Fin t.rank} (hji : j ≠ i) :
    t.fundamentalWeight ht i ((t.lieBasis ht).h' j) = 0 :=
  (t.fundamentalWeight_apply_h' ht i j).trans <| fundamentalWeightBasis_apply_coroot_of_ne _
    ((t.lieBasis ht).baseSupportEquiv.injective.ne hji)

/-- **The fundamental weights are dominant integral.** -/
theorem isDominantIntegral_fundamentalWeight (i : Fin t.rank) :
    IsDominantIntegral (t.lieBasis ht).base (t.fundamentalWeight ht i) :=
  isDominantIntegral_fundamentalWeightBasis _

/-! ### Fundamental modules -/

/-- The **`i`-th fundamental module** `L(ϖᵢ)` of the pinned rational Lie algebra: the irreducible
highest-weight module of highest weight `ϖᵢ` over `ℚ`. -/
abbrev fundamentalModule (i : Fin t.rank) : Type :=
  irreducibleQuotient (t.lieBasis ht).base (t.fundamentalWeight ht i)

/-- The canonical highest weight vector `v⁺ᵢ` of the fundamental module `L(ϖᵢ)`. -/
abbrev fundamentalGenerator (i : Fin t.rank) : t.fundamentalModule ht i :=
  irreducibleQuotientGenerator (t.lieBasis ht).base (t.fundamentalWeight ht i)

/-- **The fundamental modules are finite-dimensional over `ℚ`**, their highest weights being
dominant integral. -/
instance instFiniteDimensionalFundamentalModule (i : Fin t.rank) :
    FiniteDimensional ℚ (t.fundamentalModule ht i) :=
  finiteDimensional_irreducibleQuotient_of_isDominantIntegral
    (t.isDominantIntegral_fundamentalWeight ht i)

/-- `v⁺ᵢ` is a highest weight vector of weight `ϖᵢ`. -/
theorem isHighestWeightVector_fundamentalGenerator (i : Fin t.rank) :
    IsHighestWeightVector (t.lieBasis ht).base (t.fundamentalWeight ht i)
      (t.fundamentalGenerator ht i) :=
  isHighestWeightVector_irreducibleQuotientGenerator _ _

/-- `v⁺ᵢ` is nonzero. -/
theorem fundamentalGenerator_ne_zero (i : Fin t.rank) : t.fundamentalGenerator ht i ≠ 0 :=
  (t.isHighestWeightVector_fundamentalGenerator ht i).ne_zero

/-- **The fundamental modules are nonzero.** -/
instance instNontrivialFundamentalModule (i : Fin t.rank) :
    Nontrivial (t.fundamentalModule ht i) :=
  ⟨⟨_, 0, t.fundamentalGenerator_ne_zero ht i⟩⟩

/-! ### The pinned generators on the highest weight vector -/

/-- `hᵢ v⁺ᵢ = v⁺ᵢ`. -/
@[simp]
theorem lie_lieBasis_h_fundamentalGenerator_self (i : Fin t.rank) :
    ⁅(t.lieBasis ht).h i, t.fundamentalGenerator ht i⁆ = t.fundamentalGenerator ht i := by
  -- `LieAlgebra.Basis.h'` is the subtype element with value `hᵢ`, so its coercion is `hᵢ`.
  have h := (t.isHighestWeightVector_fundamentalGenerator ht i).lie_eq_smul ((t.lieBasis ht).h' i)
  rwa [fundamentalWeight_apply_h'_self, one_smul] at h

/-- `hⱼ v⁺ᵢ = 0` for `j ≠ i`. -/
theorem lie_lieBasis_h_fundamentalGenerator_of_ne {i j : Fin t.rank} (hji : j ≠ i) :
    ⁅(t.lieBasis ht).h j, t.fundamentalGenerator ht i⁆ = 0 := by
  -- `LieAlgebra.Basis.h'` is the subtype element with value `hⱼ`, so its coercion is `hⱼ`.
  have h := (t.isHighestWeightVector_fundamentalGenerator ht i).lie_eq_smul ((t.lieBasis ht).h' j)
  rwa [fundamentalWeight_apply_h'_of_ne t ht hji, zero_smul] at h

/-- `eⱼ v⁺ᵢ = 0` for every `j`. -/
@[simp]
theorem lie_lieBasis_e_fundamentalGenerator (i j : Fin t.rank) :
    ⁅(t.lieBasis ht).e j, t.fundamentalGenerator ht i⁆ = 0 :=
  (t.isHighestWeightVector_fundamentalGenerator ht i).lie_eq_zero_of_mem_positiveNilradical
    (mem_positiveNilradical_of_mem_rootSpace _ _
      (support_subset_posRoots _ _ ((t.lieBasis ht).baseSupportEquiv j).property)
      (lieBasis_e_mem_rootSpace (t.lieBasis ht) j))

/-- `fⱼᵏ⁺¹ v⁺ᵢ = 0` whenever `ϖᵢ (hⱼ) = k`: the integrability relation on the highest weight
vector, read on the pinned generators. -/
private theorem pow_toEnd_lieBasis_f_fundamentalGenerator {i j : Fin t.rank} {k : ℕ}
    (hk : t.fundamentalWeight ht i ((t.lieBasis ht).h' j) = k) :
    ((toEnd ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i) ((t.lieBasis ht).f j)) ^ (k + 1))
      (t.fundamentalGenerator ht i) = 0 := by
  refine pow_toEnd_eq_zero_of_isHighestWeightVector_of_isIrreducible
    (t.isHighestWeightVector_fundamentalGenerator ht i)
    ((t.lieBasis ht).baseSupportEquiv j).property ?_ ?_
  · exact (t.fundamentalWeight_apply_h' ht i j).symm.trans hk
  · exact lieBasis_f_mem_rootSpace (t.lieBasis ht) j

/-- `fⱼ v⁺ᵢ = 0` for `j ≠ i`. -/
theorem lie_lieBasis_f_fundamentalGenerator_of_ne {i j : Fin t.rank} (hji : j ≠ i) :
    ⁅(t.lieBasis ht).f j, t.fundamentalGenerator ht i⁆ = 0 := by
  simpa using t.pow_toEnd_lieBasis_f_fundamentalGenerator ht (k := 0)
    (by rw [fundamentalWeight_apply_h'_of_ne t ht hji, Nat.cast_zero])

/-- `fᵢ² v⁺ᵢ = 0`. -/
@[simp]
theorem lie_lieBasis_f_lie_lieBasis_f_fundamentalGenerator (i : Fin t.rank) :
    ⁅(t.lieBasis ht).f i, ⁅(t.lieBasis ht).f i, t.fundamentalGenerator ht i⁆⁆ = 0 := by
  simpa [pow_two] using t.pow_toEnd_lieBasis_f_fundamentalGenerator ht (k := 1)
    (by rw [fundamentalWeight_apply_h'_self, Nat.cast_one])

/-- `fᵢ v⁺ᵢ ≠ 0`: lowering the highest weight vector of `L(ϖᵢ)` by its own simple root does not
give zero. -/
theorem lie_lieBasis_f_fundamentalGenerator_ne_zero (i : Fin t.rank) :
    ⁅(t.lieBasis ht).f i, t.fundamentalGenerator ht i⁆ ≠ 0 := by
  intro h
  -- `eᵢ fᵢ v⁺ᵢ = ⁅eᵢ, fᵢ⁆ v⁺ᵢ + fᵢ eᵢ v⁺ᵢ = hᵢ v⁺ᵢ = v⁺ᵢ`, which would vanish if `fᵢ v⁺ᵢ` did.
  have key : ⁅(t.lieBasis ht).e i, ⁅(t.lieBasis ht).f i, t.fundamentalGenerator ht i⁆⁆ =
      t.fundamentalGenerator ht i := by
    rw [leibniz_lie, ((t.lieBasis ht).sl2 i).lie_e_f,
      lie_lieBasis_h_fundamentalGenerator_self, lie_lieBasis_e_fundamentalGenerator, lie_zero,
      add_zero]
  rw [h, lie_zero] at key
  exact t.fundamentalGenerator_ne_zero ht i key.symm

end

end TauCeti.DynkinType
