/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ForgetGrading
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head

/-!
# Forgetting a nonnegative grading with split degree-zero part

Let `A` be a finite-dimensional nonnegatively graded algebra over a field. Suppose that its
degree-zero part is spanned by a complete family of nonzero orthogonal idempotents. Forgetting
the grading identifies graded `G₀` specialized at `q = 1` with ordinary `G₀`.

The heads `Sᵢ = A eᵢ / A₊ eᵢ` provide the comparison: their underlying modules are pairwise
nonisomorphic simples and exhaust the ordinary simples. Their graded classes are already a
Laurent basis, so the forgetful map carries the specialized basis to the ordinary simple-class
basis. The inverse sends an ordinary simple class to the corresponding specialized head class.
No finite-global-dimension assumption is needed, and arbitrary ordinary modules need not admit
a grading.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Sections 2.3--2.4, for graded
  simple modules and the passage to underlying modules.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for specialization
  of the graded Grothendieck group at `q = 1`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e)) (hne : ∀ i, e i ≠ 0)

local notation "S" => (fun i : I ↦
  (ObjectProperty.FullSubcategory.mk (gradedPositiveMulQuotient 𝒜 (he₀ i))
    (gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)) :
      ObjectProperty.FullSubcategory (gradedFiniteModules 𝒜)))

local notation "T" => (fun i : I ↦ FGModuleCat.of A (gradedPositiveMulQuotient 𝒜 (he₀ i)))

include hneg he hspan hne in
/-- The underlying idempotent heads exhaust the ordinary simple modules. Thus every ordinary
simple admits a grading concentrated in degree zero, even though arbitrary modules need not. -/
theorem isExhaustiveSimpleFamily_gradedIdempotentHead : IsExhaustiveSimpleFamily T := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  exact isExhaustiveSimpleFamily_of_isExhaustiveGradedSimpleFamily S T
    (isExhaustiveGradedSimpleFamily_gradedIdempotentHead (hcomplete := he) hneg he₀ hspan)
    (fun _ ↦ ⟨Iso.refl _⟩)

include hneg he hspan hne in
/-- **Forgetting grading identifies `G₀^gr` at `q = 1` with ordinary `G₀`** for a
finite-dimensional nonnegatively graded algebra whose degree-zero part is spanned by nonzero
complete orthogonal idempotents. -/
def gradedIdempotentHeadForgetK0Equiv :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) ≃ₗ[ℤ]
      ExactK0.{uA} (finiteModulesExactStructure A) := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies S T he.idem he₀
    (fun j i hji ↦ by
      simpa [hji] using smulGradedDimension_gradedIdempotentHead
        hneg he.toOrthogonalIdempotents he₀ hspan j i (hne i))
    (fun i ↦ by
      simpa using smulGradedDimension_gradedIdempotentHead
        hneg he.toOrthogonalIdempotents he₀ hspan i i (hne i))
    (isExhaustiveGradedSimpleFamily_gradedIdempotentHead (hcomplete := he) hneg he₀ hspan)
    (fun i j hij ↦ isEmpty_linearEquiv_gradedIdempotentHead
      hneg he.toOrthogonalIdempotents he₀ hspan hij (hne i))
    (isExhaustiveSimpleFamily_gradedIdempotentHead hneg he he₀ hspan hne)
    (fun _ ↦ ⟨Iso.refl _⟩)

/-- The comparison equivalence has the actual forgetful map as its forward map. -/
@[simp]
theorem gradedIdempotentHeadForgetK0Equiv_toLinearMap :
    (gradedIdempotentHeadForgetK0Equiv hneg he he₀ hspan hne).toLinearMap =
      gradedFiniteModulesForgetK0 𝒜 := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  unfold gradedIdempotentHeadForgetK0Equiv
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies_toLinearMap ..

/-- A specialized graded module class maps to the class of its underlying module. -/
-- Keep this a named rewrite so equivalence inverse laws can match before child normalization.
theorem gradedIdempotentHeadForgetK0Equiv_mk_of (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedIdempotentHeadForgetK0Equiv hneg he he₀ hspan hne
        (LaurentSpecialization.mk 1 (LaurentK0.of.{uA} _ M)) =
      ExactK0.of.{uA} ((gradedFiniteModulesForget 𝒜).obj M) := by
  rw [← LinearEquiv.coe_coe, gradedIdempotentHeadForgetK0Equiv_toLinearMap]
  exact gradedFiniteModulesForgetK0_mk_of 𝒜 M

/-- The inverse sends the class of an ordinary idempotent head to its graded class at `q = 1`. -/
-- As above, avoid rewriting inside generic equivalence inverse laws automatically.
theorem gradedIdempotentHeadForgetK0Equiv_symm_head (i : I) :
    (gradedIdempotentHeadForgetK0Equiv hneg he he₀ hspan hne).symm (ExactK0.of.{uA} (T i)) =
      LaurentSpecialization.mk 1 (LaurentK0.of.{uA} _ (S i)) := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  unfold gradedIdempotentHeadForgetK0Equiv
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies_symm_simple ..

end TauCeti
