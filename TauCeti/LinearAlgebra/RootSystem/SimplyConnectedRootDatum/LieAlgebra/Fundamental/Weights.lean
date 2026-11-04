/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Lattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Comparison

/-!
# The weights of the fundamental lattices

The integral weight slices of the fundamental lattice span the corresponding rational generalized
weight spaces of `L(ϖᵢ)`. Thus the lattice and the rational fundamental module have the same
weights. Coordinates are values on the numbered simple coroots, that is, fundamental-weight
coordinates. The comparison is over `ℚ` and requires no algebraic closure.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2, Corollary 1 to Theorem 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.1.
-/

public section

namespace TauCeti.DynkinType

open LieModule Module _root_.TauCeti.UniversalEnvelopingAlgebra

variable (t : DynkinType) (ht : t.Valid)

/-- The generalized weight space of a rational fundamental module is spanned by the integral
weight slice of its fundamental lattice. -/
theorem span_weightSublattice_fundamentalLattice_eq_genWeightSpace (i : Fin t.rank)
    (χ : Dual ℚ (t.cartanSubalgebra ht)) (μ : Fin t.rank → ℤ)
    (hχ : ∀ j, χ ((t.lieBasis ht).h' j) = (μ j : ℚ)) :
    Submodule.span ℚ
        ((fun x : (t.fundamentalLattice ht i).toAddSubgroup =>
          (x : t.fundamentalModule ht i)) ''
          (weightSublattice (t.lieBasis ht).h
            (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i))
            (t.fundamentalLattice ht i).toAddSubgroup μ :
              Set (t.fundamentalLattice ht i).toAddSubgroup)) =
      (genWeightSpace (t.fundamentalModule ht i) (χ : t.cartanSubalgebra ht → ℚ)).toSubmodule :=
  (t.lieBasis ht).span_weightSublattice_eq_genWeightSpace (t.fundamentalLattice ht i)
    (fun u hu x hx => t.representation_mem_fundamentalLattice ht
      (by rwa [t.kostantForm_def ht]) hx)
    (fun _ hx => t.mem_iSup_jointWeightSpace_of_mem_fundamentalLattice ht hx) χ μ hχ

/-- An integral weight occurs in the fundamental lattice if and only if the corresponding
rational weight occurs in `L(ϖᵢ)`. -/
theorem weightSublattice_fundamentalLattice_ne_bot_iff (i : Fin t.rank)
    (χ : Dual ℚ (t.cartanSubalgebra ht)) (μ : Fin t.rank → ℤ)
    (hχ : ∀ j, χ ((t.lieBasis ht).h' j) = (μ j : ℚ)) :
    weightSublattice (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i))
        (t.fundamentalLattice ht i).toAddSubgroup μ ≠ ⊥ ↔
      genWeightSpace (t.fundamentalModule ht i) (χ : t.cartanSubalgebra ht → ℚ) ≠ ⊥ :=
  (t.lieBasis ht).weightSublattice_ne_bot_iff (t.fundamentalLattice ht i)
    (fun u hu x hx => t.representation_mem_fundamentalLattice ht
      (by rwa [t.kostantForm_def ht]) hx)
    (fun _ hx => t.mem_iSup_jointWeightSpace_of_mem_fundamentalLattice ht hx) χ μ hχ

/-- Every rational weight of a fundamental module has integral fundamental-weight coordinates
and occurs in the corresponding weight slice of the fundamental lattice. -/
theorem exists_weightSublattice_fundamentalLattice_ne_bot (i : Fin t.rank)
    (χ : Weight ℚ (t.cartanSubalgebra ht) (t.fundamentalModule ht i)) :
    ∃ μ : Fin t.rank → ℤ,
      (∀ j, χ ((t.lieBasis ht).h' j) = (μ j : ℚ)) ∧
      weightSublattice (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i))
        (t.fundamentalLattice ht i).toAddSubgroup μ ≠ ⊥ := by
  choose μ hμ using fun j => (isIntegralWeight_of_weight χ).exists_int_apply_coroot
    ((t.lieBasis ht).baseSupportEquiv j : Weight ℚ (t.cartanSubalgebra ht) (t.lieAlgebra ht))
  have hχ : ∀ j, χ ((t.lieBasis ht).h' j) = (μ j : ℚ) := by
    intro j
    simpa only [LieAlgebra.Basis.coroot_eq_h', Weight.toLinear_apply] using hμ j
  exact ⟨μ, hχ, (t.weightSublattice_fundamentalLattice_ne_bot_iff ht i
    (χ : Dual ℚ (t.cartanSubalgebra ht)) μ hχ).mpr χ.genWeightSpace_ne_bot⟩

end TauCeti.DynkinType
