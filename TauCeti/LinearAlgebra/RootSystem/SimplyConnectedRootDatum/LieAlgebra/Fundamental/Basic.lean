/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Basis
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
import TauCeti.Algebra.Lie.HighestWeight.Module

/-!
# The fundamental modules of the pinned rational Lie algebra

For a valid Dynkin type `t`, the pinned Lie algebra `TauCeti.DynkinType.lieAlgebra t ht` over `ℚ`
carries the Bourbaki-numbered Chevalley generators `TauCeti.DynkinType.lieBasis`, whose Cartan
generators `hᵢ` are the simple coroots of the pinned base `(t.lieBasis ht).base`. This file names
the fundamental weights `ϖᵢ`, the basis of the dual of the Cartan subalgebra dual to the `hᵢ`, and
the fundamental modules `L(ϖᵢ)`, the irreducible highest weight modules of these weights.

Over `ℚ` no algebraic closure is needed: the Cartan action is triangularizable over `ℚ`
(`TauCeti.DynkinType.instIsTriangularizableLieAlgebra`), and finite-dimensionality of `L(λ)` for a
dominant integral `λ` holds over any field of characteristic zero with a splitting Cartan
subalgebra (`TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral`). The fundamental
modules are therefore finite-dimensional, nonzero and irreducible rational representations, and
the line through the highest weight vector `v⁺ᵢ` is their whole `ϖᵢ`-weight space. They are the
input of the simply connected Chevalley group: since each `ϖᵢ` is a weight of `L(ϖᵢ)`, the weights
of the direct sum of the fundamental modules span the full weight lattice (Steinberg, Chapter 3,
the remark after Lemma 27).

## Main declarations

* `TauCeti.DynkinType.fundamentalWeight`: the basis of fundamental weights `ϖᵢ`.
* `TauCeti.DynkinType.isDominantIntegral_fundamentalWeight`: each `ϖᵢ` is dominant integral for
  the pinned base.
* `TauCeti.DynkinType.span_fundamentalWeight_eq_integralWeightLattice`: the `ϖᵢ` span the integral
  weight lattice over `ℤ`.
* `TauCeti.DynkinType.fundamentalModule`: the fundamental module `L(ϖᵢ)` over `ℚ`.
* `TauCeti.DynkinType.fundamentalModuleGenerator`: its highest weight vector `v⁺ᵢ`.
* `TauCeti.DynkinType.instFiniteDimensionalFundamentalModule` and
  `TauCeti.DynkinType.instNontrivialFundamentalModule`: `L(ϖᵢ)` is finite-dimensional and nonzero.
* `TauCeti.DynkinType.genWeightSpace_fundamentalModule_fundamentalWeight`: the `ϖᵢ`-weight space
  of `L(ϖᵢ)` is the line through `v⁺ᵢ`.
* `TauCeti.DynkinType.lie_lieBasis_e_fundamentalModuleGenerator`,
  `TauCeti.DynkinType.lie_lieBasis_h_fundamentalModuleGenerator_self` and
  `TauCeti.DynkinType.lie_lieBasis_f_fundamentalModuleGenerator_of_ne`: the pinned generators act
  on `v⁺ᵢ` by `eⱼ v⁺ᵢ = 0`, `hⱼ v⁺ᵢ = δᵢⱼ v⁺ᵢ`, and `fⱼ v⁺ᵢ = 0` for `j ≠ i`.
* `TauCeti.DynkinType.lie_lieBasis_f_fundamentalModuleGenerator_ne_zero` and
  `TauCeti.DynkinType.lie_lieBasis_f_lie_lieBasis_f_fundamentalModuleGenerator`: `fᵢ v⁺ᵢ ≠ 0` and
  `fᵢ² v⁺ᵢ = 0`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2 and Chapter 3, the remark after Lemma 27.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.1 and
  §21.2.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule Module

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ### The fundamental weights -/

/-- **The fundamental weights of the pinned Lie algebra**, as a basis of the dual of its Cartan
subalgebra: `ϖᵢ` is the vector of the basis dual to the Bourbaki-numbered Cartan generators `hᵢ`,
the simple coroots of the pinned base, so that `ϖᵢ(hⱼ) = δᵢⱼ`
(`TauCeti.DynkinType.fundamentalWeight_apply_coroot`). -/
def fundamentalWeight : Basis (Fin t.rank) ℚ (Dual ℚ (t.cartanSubalgebra ht)) :=
  (t.lieBasis ht).cartanBasis.dualBasis

/-- The fundamental weight `ϖᵢ` takes the value `δᵢⱼ` on the Cartan generator `hⱼ`. -/
@[simp] theorem fundamentalWeight_apply_h' (i j : Fin t.rank) :
    t.fundamentalWeight ht i ((t.lieBasis ht).h' j) = if j = i then 1 else 0 := by
  rw [fundamentalWeight, ← LieAlgebra.Basis.cartanBasis_apply, Basis.dualBasis_apply_self]

/-- **The fundamental weights are dual to the simple coroots.** The fundamental weight `ϖᵢ` takes
the value `δᵢⱼ` on the coroot of the `j`-th simple root of the pinned base. -/
theorem fundamentalWeight_apply_coroot (i j : Fin t.rank) :
    t.fundamentalWeight ht i
        ((IsKilling.rootSystem (t.cartanSubalgebra ht)).coroot
          ((t.lieBasis ht).baseSupportEquiv j)) =
      if j = i then 1 else 0 := by
  rw [IsKilling.rootSystem_coroot_apply, LieAlgebra.Basis.coroot_eq_h',
    fundamentalWeight_apply_h']

/-- Each fundamental weight is dominant integral for the pinned base. -/
theorem isDominantIntegral_fundamentalWeight (i : Fin t.rank) :
    IsDominantIntegral (t.lieBasis ht).base (t.fundamentalWeight ht i) :=
  (t.lieBasis ht).isDominantIntegral_cartanBasis_dualBasis i

/-- **The fundamental weights span the weight lattice**: over `ℤ`, the `ϖᵢ` span the lattice of
integral weights of the pinned Lie algebra. -/
theorem span_fundamentalWeight_eq_integralWeightLattice :
    Submodule.span ℤ (Set.range (t.fundamentalWeight ht)) =
      integralWeightLattice (t.cartanSubalgebra ht) :=
  (t.lieBasis ht).span_cartanBasis_dualBasis_eq_integralWeightLattice

/-! ### The fundamental modules -/

/-- **The `i`-th fundamental module** `L(ϖᵢ)` of the pinned Lie algebra over `ℚ`: the irreducible
quotient `TauCeti.irreducibleQuotient` of the Verma module of the fundamental weight `ϖᵢ` for the
pinned base. It is an abbreviation, so the API of `L(λ)` applies to it directly; in particular it
is irreducible (`TauCeti.isIrreducible_irreducibleQuotient`). -/
abbrev fundamentalModule (i : Fin t.rank) : Type :=
  irreducibleQuotient (t.lieBasis ht).base (t.fundamentalWeight ht i)

/-- The highest weight vector `v⁺ᵢ` of the fundamental module `L(ϖᵢ)`, its canonical generator
`TauCeti.irreducibleQuotientGenerator`. -/
abbrev fundamentalModuleGenerator (i : Fin t.rank) : t.fundamentalModule ht i :=
  irreducibleQuotientGenerator (t.lieBasis ht).base (t.fundamentalWeight ht i)

/-- `v⁺ᵢ` is a highest weight vector of weight `ϖᵢ` for the pinned base. -/
theorem isHighestWeightVector_fundamentalModuleGenerator (i : Fin t.rank) :
    IsHighestWeightVector (t.lieBasis ht).base (t.fundamentalWeight ht i)
      (t.fundamentalModuleGenerator ht i) :=
  isHighestWeightVector_irreducibleQuotientGenerator _ _

/-- The highest weight vector `v⁺ᵢ` of `L(ϖᵢ)` is nonzero. -/
theorem fundamentalModuleGenerator_ne_zero (i : Fin t.rank) :
    t.fundamentalModuleGenerator ht i ≠ 0 :=
  (t.isHighestWeightVector_fundamentalModuleGenerator ht i).ne_zero

/-- **The fundamental modules are nonzero.** -/
instance instNontrivialFundamentalModule (i : Fin t.rank) :
    Nontrivial (t.fundamentalModule ht i) :=
  ⟨⟨_, 0, t.fundamentalModuleGenerator_ne_zero ht i⟩⟩

/-- **The fundamental modules are finite-dimensional over `ℚ`**, their highest weights being
dominant integral. -/
instance instFiniteDimensionalFundamentalModule (i : Fin t.rank) :
    FiniteDimensional ℚ (t.fundamentalModule ht i) :=
  finiteDimensional_irreducibleQuotient_of_isDominantIntegral
    (t.isDominantIntegral_fundamentalWeight ht i)

/-- **The highest weight space of `L(ϖᵢ)` is a line**: its `ϖᵢ`-weight space is spanned by the
highest weight vector `v⁺ᵢ`. -/
theorem genWeightSpace_fundamentalModule_fundamentalWeight (i : Fin t.rank) :
    (genWeightSpace (t.fundamentalModule ht i)
        (t.fundamentalWeight ht i : t.cartanSubalgebra ht → ℚ) : Submodule ℚ _) =
      ℚ ∙ t.fundamentalModuleGenerator ht i :=
  genWeightSpace_eq_span_singleton_of_isHighestWeightVector_of_lieSpan_eq_top
    (t.isHighestWeightVector_fundamentalModuleGenerator ht i)
    (lieSpan_irreducibleQuotientGenerator_eq_top _ _)

/-! ### The pinned generators on the highest weight vector -/

/-- `hᵢ v⁺ᵢ = v⁺ᵢ`. -/
@[simp]
theorem lie_lieBasis_h_fundamentalModuleGenerator_self (i : Fin t.rank) :
    ⁅(t.lieBasis ht).h i, t.fundamentalModuleGenerator ht i⁆ =
      t.fundamentalModuleGenerator ht i := by
  -- `LieAlgebra.Basis.h'` is the subtype element with value `hᵢ`, so its coercion is `hᵢ`.
  have h := (t.isHighestWeightVector_fundamentalModuleGenerator ht i).lie_eq_smul
    ((t.lieBasis ht).h' i)
  simp only [fundamentalWeight_apply_h', ↓reduceIte, one_smul] at h
  exact h

/-- `hⱼ v⁺ᵢ = 0` for `j ≠ i`. -/
@[simp]
theorem lie_lieBasis_h_fundamentalModuleGenerator_of_ne {i j : Fin t.rank} (hji : j ≠ i) :
    ⁅(t.lieBasis ht).h j, t.fundamentalModuleGenerator ht i⁆ = 0 := by
  -- `LieAlgebra.Basis.h'` is the subtype element with value `hⱼ`, so its coercion is `hⱼ`.
  have h := (t.isHighestWeightVector_fundamentalModuleGenerator ht i).lie_eq_smul
    ((t.lieBasis ht).h' j)
  simp only [fundamentalWeight_apply_h', hji, ↓reduceIte, zero_smul] at h
  exact h

/-- `eⱼ v⁺ᵢ = 0` for every `j`. -/
@[simp]
theorem lie_lieBasis_e_fundamentalModuleGenerator (i j : Fin t.rank) :
    ⁅(t.lieBasis ht).e j, t.fundamentalModuleGenerator ht i⁆ = 0 :=
  (t.isHighestWeightVector_fundamentalModuleGenerator ht i).lie_eq_zero_of_mem_positiveNilradical
    (mem_positiveNilradical_of_mem_rootSpace _ _
      (support_subset_posRoots _ _ ((t.lieBasis ht).baseSupportEquiv j).property)
      (lieBasis_e_mem_rootSpace (t.lieBasis ht) j))

/-- `fⱼᵏ⁺¹ v⁺ᵢ = 0` whenever `ϖᵢ (hⱼ) = k`: the integrability relation on the highest weight
vector, read on the pinned generators. -/
private theorem pow_toEnd_lieBasis_f_fundamentalModuleGenerator {i j : Fin t.rank} {k : ℕ}
    (hk : t.fundamentalWeight ht i ((t.lieBasis ht).h' j) = k) :
    ((toEnd ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i) ((t.lieBasis ht).f j)) ^ (k + 1))
      (t.fundamentalModuleGenerator ht i) = 0 :=
  pow_toEnd_eq_zero_of_isHighestWeightVector_of_isIrreducible
    (t.isHighestWeightVector_fundamentalModuleGenerator ht i)
    ((t.lieBasis ht).baseSupportEquiv j).property
    (by rwa [IsKilling.rootSystem_coroot_apply, LieAlgebra.Basis.coroot_eq_h'])
    (lieBasis_f_mem_rootSpace (t.lieBasis ht) j)

/-- `fⱼ v⁺ᵢ = 0` for `j ≠ i`. -/
@[simp]
theorem lie_lieBasis_f_fundamentalModuleGenerator_of_ne {i j : Fin t.rank} (hji : j ≠ i) :
    ⁅(t.lieBasis ht).f j, t.fundamentalModuleGenerator ht i⁆ = 0 := by
  simpa using t.pow_toEnd_lieBasis_f_fundamentalModuleGenerator ht (k := 0) (by simp [hji])

/-- `fᵢ² v⁺ᵢ = 0`. -/
@[simp]
theorem lie_lieBasis_f_lie_lieBasis_f_fundamentalModuleGenerator (i : Fin t.rank) :
    ⁅(t.lieBasis ht).f i, ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆⁆ = 0 := by
  simpa [pow_two] using t.pow_toEnd_lieBasis_f_fundamentalModuleGenerator ht (k := 1) (by simp)

/-- `fᵢ v⁺ᵢ ≠ 0`: lowering the highest weight vector of `L(ϖᵢ)` by its own simple root does not
give zero, since `v⁺ᵢ` is a primitive vector of weight `1` for the `sl₂`-triple `(hᵢ, eᵢ, fᵢ)`. -/
theorem lie_lieBasis_f_fundamentalModuleGenerator_ne_zero (i : Fin t.rank) :
    ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆ ≠ 0 := by
  have hv : ((t.lieBasis ht).sl2 i).HasPrimitiveVectorWith (t.fundamentalModuleGenerator ht i)
      (1 : ℚ) :=
    ⟨t.fundamentalModuleGenerator_ne_zero ht i, by simp, by simp⟩
  simpa using hv.pow_toEnd_f_ne_zero_of_eq_nat Nat.cast_one.symm le_rfl

end

end TauCeti.DynkinType
