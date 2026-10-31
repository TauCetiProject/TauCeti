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

end

end TauCeti.DynkinType
