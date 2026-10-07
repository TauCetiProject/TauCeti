/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic

/-!
# Spanning the graded projective Grothendieck group

Over a finite-dimensional algebra, every finite graded projective is a finite direct sum of
indecomposable graded projectives. If a family meets all such indecomposables up to internal
shift, its classes span `K₀^gr(proj A)` over `ℤ[q,q⁻¹]`: shifting a summand by `d` multiplies its
class by `qᵈ`.

No uniqueness of decomposition or splitting-field hypothesis is needed. This result supplies the
spanning half of a projective-class basis, whose coordinates can then express the graded Cartan
map. Indecomposability is taken in the full category of finite graded projectives.

## Main results

* `TauCeti.span_range_laurentK0_projective_of_eq_top`: a family exhaustive among indecomposable
  graded projectives up to shift spans the Laurent Grothendieck group.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* C. A. Weibel, *The K-book*, Chapter II, Sections 5 and 7.
* `TauCeti.RepresentationTheory.GrothendieckGroup.ProjectiveBasis`: this result is the graded
  analogue of its ungraded projective-class spanning theorem and exhaustiveness API.
* `TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis`: the graded simple-class basis.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe uk uA uI

section Exhaustive

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

/-- A family of finite graded projectives is exhaustive up to shift if every indecomposable
object of their full subcategory is isomorphic to an internal shift of a member of the family. -/
def IsExhaustiveGradedIndecomposableProjectiveFamily
    (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) : Prop :=
  ∀ M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory, Indecomposable M →
    ∃ i d, Nonempty (M ≅
      ⟨(P i).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P i).property d⟩)

/-- Characterization of exhaustiveness up to shift without unfolding the definition. -/
theorem isExhaustiveGradedIndecomposableProjectiveFamily_iff
    (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    IsExhaustiveGradedIndecomposableProjectiveFamily P ↔
      ∀ M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory, Indecomposable M →
        ∃ i d, Nonempty (M ≅
          ⟨(P i).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P i).property d⟩) :=
  Iff.rfl

end Exhaustive

section Span

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}
  (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)

private theorem finrank_pos_of_not_isZero
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (hM : ¬IsZero M) :
    0 < Module.finrank k M.obj := by
  have : Module.Finite k M.obj := Module.Finite.trans A M.obj
  by_contra h
  have : Subsingleton M.obj := (Module.finrank_zero_iff (R := k)).mp (by omega)
  exact hM <| (IsZero.iff_id_eq_zero M).2 <| ObjectProperty.hom_ext _ <|
    GradedModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

private theorem finrank_eq_add_of_iso_biprod
    (M Y Z : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (e : M ≅ Y ⊞ Z) :
    Module.finrank k M.obj = Module.finrank k Y.obj + Module.finrank k Z.obj := by
  have : Module.Finite k Y.obj := Module.Finite.trans A Y.obj
  have : Module.Finite k Z.obj := Module.Finite.trans A Z.obj
  -- Forgetting the grading sends this biproduct decomposition to a product of modules.
  let F := (gradedFiniteProjectiveModules 𝒜).ι ⋙ GradedModuleCat.toModuleCat
  let : PreservesBinaryBiproduct Y Z F :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  let e' : ModuleCat.of A M.obj ≅ ModuleCat.of A (Y.obj × Z.obj) :=
    F.mapIso e ≪≫ F.mapBiprod Y Z ≪≫
    ModuleCat.biprodIsoProd (F.obj Y) (F.obj Z)
  exact (e'.toLinearEquiv.restrictScalars k).finrank_eq.trans Module.finrank_prod

private theorem laurentK0_projective_of_mem_span
    (hP : IsExhaustiveGradedIndecomposableProjectiveFamily P)
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M ∈
      Submodule.span (LaurentPolynomial ℤ)
        (Set.range fun i =>
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i)) := by
  classical
  set G := Submodule.span (LaurentPolynomial ℤ)
    (Set.range fun i =>
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i))
  induction hn : Module.finrank k M.obj using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    by_cases hM : IsZero M
    · rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hM,
        map_zero]
      exact G.zero_mem
    by_cases hind : Indecomposable M
    · obtain ⟨i, d, ⟨e⟩⟩ := hP M hind
      rw [LaurentK0.of_congr.{uA} _ e, laurentK0_projective_of_shiftObj]
      exact G.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    -- A nonzero decomposable object has two nonzero projective summands.
    obtain ⟨Y, Z, e, hY, hZ⟩ :
        ∃ Y Z, ∃ e : M ≅ Y ⊞ Z, ¬IsZero Y ∧ ¬IsZero Z := by
      simpa only [Indecomposable, hM, not_false_eq_true, true_and, not_forall,
        not_or, exists_prop] using hind
    have hdim := finrank_eq_add_of_iso_biprod M Y Z e
    have hYpos := finrank_pos_of_not_isZero Y hY
    have hZpos := finrank_pos_of_not_isZero Z hZ
    have hclass : LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M =
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) Y +
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) Z := by
      exact (LaurentK0.of_congr.{uA} _ e).trans <| LaurentK0.of_conflation.{uA} _
        (ExactStructure.conflation_biprodShortComplex
          (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure Y Z)
    rw [hclass]
    exact G.add_mem (ih _ (by omega) Y rfl) (ih _ (by omega) Z rfl)

/-- **The classes of a family exhaustive among indecomposable graded projectives up to shift span
`K₀^gr(proj A)` over `ℤ[q,q⁻¹]`.** Every finite graded projective splits into finitely many
indecomposable summands, and the class of a shifted summand is a Laurent monomial times the class
of a member of the family. No independence or uniqueness of decomposition is assumed. -/
theorem span_range_laurentK0_projective_of_eq_top
    (hP : IsExhaustiveGradedIndecomposableProjectiveFamily P) :
    Submodule.span (LaurentPolynomial ℤ)
        (Set.range fun i =>
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i)) = ⊤ := by
  refine top_unique fun x _ => ?_
  clear ‹x ∈ ⊤›
  obtain ⟨x, rfl⟩ :=
    (LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)).surjective x
  induction x using ExactK0.induction_on with
  | zero => simp
  | of M => simpa using laurentK0_projective_of_mem_span P hP M
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | neg x hx => simpa using Submodule.neg_mem _ hx

end Span

end TauCeti
