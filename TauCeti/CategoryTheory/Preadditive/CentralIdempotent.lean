/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Hom-orthogonal splittings of a biproduct with connected endomorphism ring

Let `G` be an object of a preadditive category whose endomorphism ring has no central idempotents
other than `0` and `1`, and suppose that `G` is a biproduct of nonzero objects `P j`. Any splitting
of the summands into two groups with no nonzero morphisms between them makes the projection onto
the first group a central idempotent of `End G`, so such a splitting is trivial
(`TauCeti.forall_or_forall_not_of_forall_hom_eq_zero`).

For the regular module of a connected ring this is the connectedness step in Auslander's theorem on
classes of bounded length closed under irreducible maps,
`TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/Component.lean`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

variable {C : Type*} [Category* C] [Preadditive C]

/-- **Objects with connected endomorphism ring admit no Hom-orthogonal splitting.** Let `G` be an
object whose endomorphism ring has no central idempotents other than `0` and `1`, and a biproduct of
nonzero objects `P j`. If no nonzero morphism, in either direction, joins a summand satisfying a
predicate `p` to one that does not, then either all summands satisfy `p` or none does. -/
theorem forall_or_forall_not_of_forall_hom_eq_zero {G : C}
    (hG : centralIdempotents (End G) ⊆ {0, 1}) {J : Type*} {P : J → C} [HasBiproduct P]
    (e : G ≅ ⨁ P) (hP : ∀ j, ¬ IsZero (P j)) (p : J → Prop)
    (hp : ∀ a b, p a → ¬ p b → (∀ f : P a ⟶ P b, f = 0) ∧ ∀ f : P b ⟶ P a, f = 0) :
    (∀ j, p j) ∨ ∀ j, ¬ p j := by
  classical
  -- The projection onto the summands satisfying `p`.
  let d (j : J) : P j ⟶ P j := if p j then 𝟙 _ else 0
  let σ : ⨁ P ⟶ ⨁ P := biproduct.map d
  have hσ (ψ : ⨁ P ⟶ ⨁ P) : ψ ≫ σ = σ ≫ ψ := by
    refine biproduct.hom_ext' _ _ fun a ↦ biproduct.hom_ext _ _ fun b ↦ ?_
    simp only [σ, Category.assoc, biproduct.map_π, biproduct.ι_map_assoc, d]
    by_cases ha : p a <;> by_cases hb : p b <;>
      simp only [ha, hb, ↓reduceIte, Category.comp_id, Category.id_comp, comp_zero, zero_comp]
    · exact ((hp a b ha hb).1 _).symm
    · exact (hp b a hb ha).2 _
  have hσσ : σ ≫ σ = σ := by
    refine biproduct.hom_ext' _ _ fun a ↦ ?_
    by_cases ha : p a <;> simp [σ, d, ha]
  -- `σ` is a central idempotent of `End (⨁ P)`, hence its transport to `G` is `0` or `1`.
  have hσc : End.of σ ∈ centralIdempotents (End (⨁ P)) := mem_centralIdempotents.mpr
    ⟨End.ext (by simpa using hσσ),
      Subring.mem_center_iff.mpr fun ψ ↦ End.ext (by simpa using (hσ ψ.asHom).symm)⟩
  have hσP (j : J) : biproduct.ι P j ≫ σ ≫ biproduct.π P j = d j := by simp [σ]
  rcases hG (e.symm.endRingEquiv.map_mem_centralIdempotents hσc) with h | h
  · right
    intro j hj
    have hσ0 : σ = 0 := congrArg End.asHom ((map_eq_zero_iff _ e.symm.endRingEquiv.injective).mp h)
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [d, hj, hσ0] using (hσP j).symm
  · left
    intro j
    by_contra hj
    have hσ1 : σ = 𝟙 _ :=
      congrArg End.asHom ((map_eq_one_iff _ e.symm.endRingEquiv.injective).mp
        (Set.mem_singleton_iff.mp h))
    apply hP j
    rw [IsZero.iff_id_eq_zero]
    simpa [d, hj, hσ1] using hσP j

end TauCeti
