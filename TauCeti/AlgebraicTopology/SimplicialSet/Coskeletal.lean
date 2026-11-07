/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Horn filling in coskeletal simplicial sets

A simplicial set `X` is `k`-coskeletal (Mathlib's `SimplicialObject.IsCoskeletal X k`) when it is
the right Kan extension of its restriction to simplices of dimension at most `k`: maps into `X`
are determined by, and can be built from, their restrictions to these simplices.

A horn `Λ[m, i]` of dimension `m ≥ k + 2` contains every simplex of `Δ[m]` of dimension at most
`k`, so the restriction of its inclusion into `Δ[m]` to these dimensions is an isomorphism. Hence
every horn of dimension at least `k + 2` in a `k`-coskeletal simplicial set has a unique filler.
For instance, nerves of categories are `2`-coskeletal, so all their horns of dimension at least
`4` have unique fillers, and horn filling in a nerve reduces to horns of dimensions `2` and `3`.

## Main results

* `SSet.existsUnique_horn_extension_of_isCoskeletal`: in a `k`-coskeletal simplicial set, every
  horn `Λ[m, i]` with `k + 2 ≤ m` has a unique filler.
-/

public section

open CategoryTheory Functor Opposite Simplicial

universe u

namespace SSet

variable {X : SSet.{u}} {k : ℕ}

/-- In dimensions at most `k`, a horn `Λ[m, i]` of dimension `m ≥ k + 2` contains every simplex
of `Δ[m]`, so the restriction of its inclusion to these dimensions is an isomorphism. -/
lemma isIso_whiskerLeft_truncatedInclusion_horn_ι {m : ℕ} (hm : k + 2 ≤ m) (i : Fin (m + 1)) :
    IsIso (whiskerLeft (SimplexCategory.Truncated.inclusion k).op (horn.{u} m i).ι) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨d⟩, hd⟩
  rw [isIso_iff_bijective]
  refine ⟨fun x y h ↦ Subtype.ext h, fun x ↦ ⟨⟨x, ?_⟩, rfl⟩⟩
  -- `Λ[m, i]` contains every simplex of `Δ[m]` of dimension `d`, since `d + 1 < m`.
  dsimp
  rw [horn_obj_eq_univ i d (by simp at hd; omega)]
  exact Set.mem_univ x

/-- In a `k`-coskeletal simplicial set, every horn `Λ[m, i]` of dimension `m ≥ k + 2` has a
unique filler. -/
theorem existsUnique_horn_extension_of_isCoskeletal [X.IsCoskeletal k] {m : ℕ} (hm : k + 2 ≤ m)
    (i : Fin (m + 1)) (σ₀ : (Λ[m, i] : SSet.{u}) ⟶ X) :
    ∃! σ : Δ[m] ⟶ X, Λ[m, i].ι ≫ σ = σ₀ := by
  have := isIso_whiskerLeft_truncatedInclusion_horn_ι.{u} hm i
  let L := (SimplexCategory.Truncated.inclusion k).op
  let w := whiskerLeft L Λ[m, i].ι
  refine ⟨X.liftOfIsRightKanExtension (𝟙 (L ⋙ X)) _ (inv w ≫ whiskerLeft L σ₀), ?_, ?_⟩
  · refine X.hom_ext_of_isRightKanExtension (𝟙 (L ⋙ X)) _ _ ?_
    rw [whiskerLeft_comp, Category.assoc, liftOfIsRightKanExtension_fac, IsIso.hom_inv_id_assoc,
      Category.comp_id]
  · intro σ hσ
    refine X.hom_ext_of_isRightKanExtension (𝟙 (L ⋙ X)) _ _ ?_
    rw [liftOfIsRightKanExtension_fac, Category.comp_id, ← hσ, whiskerLeft_comp,
      IsIso.inv_hom_id_assoc]

end SSet
