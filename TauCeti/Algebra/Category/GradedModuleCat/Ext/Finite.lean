/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# Finite internal support of Ext over a Noetherian graded algebra

Let `A` be a left Noetherian graded algebra over a field `k`. For a finitely generated graded
module `X` and a finite-dimensional graded module `Y`, the groups `Extⁿ(X,Y{j})` are
finite-dimensional and vanish outside a finite set of internal degrees `j`, for each fixed `n`.
Neither a nonnegative algebra grading nor finite-dimensionality of `A` is required.

The internal support may depend on `n`. In particular, this theorem asserts no eventual
cohomological vanishing: Euler-admissibility of these pairs is equivalent to a separate uniform
cohomological bound. This distinction allows finite internal support to be used even for
algebras of infinite global dimension.

The proof extends the finite Laurent support of Hom by dimension shifting along finite graded
free presentations. Left Noetherianity ensures that each successive kernel is finitely generated.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.4, for graded Ext over
  Noetherian graded rings.
* Mathlib's `ModuleCat.finite_ext` proves the ungraded finite-generation result for commutative
  Noetherian rings by the same dimension-shifting argument. Here `A` may be noncommutative and
  the conclusion also controls internal support.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedModuleCat

open CategoryTheory CategoryTheory.Abelian

universe w v uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsNoetherianRing A]
  [HasExt.{w} (GradedModuleCat.{max uA v} 𝒜)]

/-- **Finite generation bounds the internal support of every Ext degree.** Over a left
Noetherian graded algebra, Ext from a finitely generated graded module to the shifts of a
finite-dimensional graded module has finite Laurent support in each cohomological degree.
No eventual cohomological vanishing is asserted. -/
theorem isGradedExtInternallyFinite_of_finite
    (X Y : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A X] [Module.Finite k Y] :
    IsGradedExtInternallyFinite.{w} k (shift 𝒜) X Y := by
  refine ⟨fun n ↦ ?_⟩
  induction n generalizing X with
  | zero =>
    exact (hasFiniteLaurentSupport_hom_shiftObj X Y).of_equiv fun j ↦
      (homShiftPowEquiv 𝒜 X Y j).symm.trans (Ext.linearEquiv₀ (R := k)).symm
  | succ n ih =>
    obtain ⟨I, _, d, π, hπ⟩ := exists_finite_free_surjection X
    have : Module.Finite A (kernelObj π) :=
      inferInstanceAs (Module.Finite A (LinearMap.ker π.hom))
    let S := ShortComplex.mk (kernelι π) π (kernelι_comp π)
    have hS : S.ShortExact :=
      { exact := exact_iff.2 (by simpa [S, hom_kernelι] using LinearMap.exact_subtype_ker_map π.hom)
        mono_f := (mono_iff_injective _).2 (by simp [S, hom_kernelι])
        epi_g := (epi_iff_surjective _).2 hπ }
    have : Module.Projective A (free 𝒜 d) := inferInstanceAs (Module.Projective A (⨁ _ : I, A))
    have : Projective S.X₂ := projective_of_module_projective _
    have hfree := isGradedEulerAdmissible_of_projective k (shift 𝒜) S.X₂ Y
      ((hasFiniteLaurentSupport_hom_shiftObj S.X₂ Y).of_equiv fun j ↦
        (homShiftPowEquiv 𝒜 S.X₂ Y j).symm)
    exact (ih S.X₁).of_exact (hfree.internallyFinite.finiteLaurentSupport (n + 1))
      (fun j ↦ hS.extClass.precompOfLinear k (((shift 𝒜) ^ j).functor.obj Y) (add_comm 1 n))
      (fun j ↦ (Ext.mk₀ S.g).precompOfLinear k (((shift 𝒜) ^ j).functor.obj Y)
        (zero_add (n + 1)))
      (fun j ↦ exact_precompOfLinear₃ k hS (((shift 𝒜) ^ j).functor.obj Y) n (n + 1)
        (add_comm 1 n))

/-- For a finitely generated source and a finite-dimensional target over a left Noetherian
algebra, graded Euler-admissibility requires precisely uniform eventual Ext-vanishing.
The internal finiteness condition follows from the module hypotheses. -/
theorem isGradedEulerAdmissible_iff_isGradedExtBounded
    (X Y : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A X] [Module.Finite k Y] :
    IsGradedEulerAdmissible.{w} k (shift 𝒜) X Y ↔
      IsGradedExtBounded.{w} (shift 𝒜) X Y :=
  ⟨fun h ↦ h.bounded, fun h ↦ ⟨isGradedExtInternallyFinite_of_finite X Y, h⟩⟩

end TauCeti.GradedModuleCat
