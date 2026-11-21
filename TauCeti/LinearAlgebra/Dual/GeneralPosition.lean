/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import TauCeti.LinearAlgebra.LinearIndependent.GeneralPosition

import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.Basic

/-!
# Linear forms in general position

A family of linear forms `l : κ → Module.Dual F (ι → F)` on the coordinate space `F^ι` is in
**general position**, `Module.Dual.IsGeneralPosition l`, if every subfamily of at most `card ι`
members is linearly independent. Families with more than `card ι` members are the case of
interest: Vojta's form of the Subspace Theorem, with an arbitrary number of forms at each place,
assumes it. The condition "at most" rather than "exactly" `card ι` makes small families need no
separate hypothesis: a family with at most `card ι` members is in general position exactly when it
is linearly independent (`Module.Dual.isGeneralPosition_iff_linearIndependent`). A family with at
least `card ι` members is in general position exactly when the coefficient vectors of its forms are
in general position in the sense of `TauCeti.InGeneralPosition`
(`Module.Dual.isGeneralPosition_iff_inGeneralPosition`). General position of the members indexed
by a finset `B` is general position of the restricted family `fun k : B ↦ l k`, read off on the
finsets contained in `B` by `Module.Dual.isGeneralPosition_subtype_iff`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Definition 7.2.8 and
  Theorem 7.2.9.
* P. Vojta, *Diophantine approximations and value distribution theory*, Lecture Notes in Math.
  1239 (1987).
-/

public section

open Finset Function Module Set

namespace Module.Dual

variable {F ι κ : Type*} [Field F] [Fintype ι]

/-- A family of linear forms on `F^ι` is in **general position** if every subfamily with at most
`card ι` members is linearly independent. -/
def IsGeneralPosition (l : κ → Dual F (ι → F)) : Prop :=
  ∀ s : Finset κ, #s ≤ Fintype.card ι → LinearIndepOn F l (s : Set κ)

theorem isGeneralPosition_iff {l : κ → Dual F (ι → F)} :
    IsGeneralPosition l ↔ ∀ s : Finset κ, #s ≤ Fintype.card ι → LinearIndepOn F l (s : Set κ) :=
  Iff.rfl

/-- In a family in general position, every subfamily with at most `card ι` members is linearly
independent. -/
theorem IsGeneralPosition.linearIndepOn {l : κ → Dual F (ι → F)} (hl : IsGeneralPosition l)
    {s : Finset κ} (hs : #s ≤ Fintype.card ι) : LinearIndepOn F l (s : Set κ) :=
  hl s hs

/-- A family of at most `card ι` forms is in general position exactly when it is linearly
independent. -/
theorem isGeneralPosition_iff_linearIndependent [Fintype κ] {l : κ → Dual F (ι → F)}
    (h : Fintype.card κ ≤ Fintype.card ι) : IsGeneralPosition l ↔ LinearIndependent F l := by
  refine ⟨fun hl ↦ ?_, fun hl s _ ↦ hl.linearIndepOn _⟩
  have := hl.linearIndepOn (s := univ) (by rwa [card_univ])
  rwa [coe_univ, linearIndepOn_univ_iff] at this

/-- General position of the members of `l` indexed by a finset `B`: every finset of at most
`card ι` indices contained in `B` indexes linearly independent forms. -/
theorem isGeneralPosition_subtype_iff {l : κ → Dual F (ι → F)} {B : Finset κ} :
    IsGeneralPosition (fun k : B ↦ l k) ↔
      ∀ s : Finset κ, s ⊆ B → #s ≤ Fintype.card ι → LinearIndepOn F l (s : Set κ) := by
  classical
  constructor
  · intro hl s hsB hs
    have hmem : ∀ k ∈ s, k ∈ B := fun k hk ↦ hsB hk
    have h := (hl (s.subtype (· ∈ B))
      (by rwa [card_subtype, filter_true_of_mem hmem])).image_of_comp Subtype.val l
    have himage : Subtype.val '' (s.subtype (· ∈ B) : Set B) = s := by
      ext k
      constructor
      · rintro ⟨k', hk', rfl⟩
        exact mem_subtype.mp hk'
      · intro hk
        exact ⟨⟨k, hmem k hk⟩, mem_subtype.mpr hk, rfl⟩
    rwa [himage] at h
  · intro hl s hs
    have hsB : s.map (Embedding.subtype _) ⊆ B := fun k hk ↦ by
      obtain ⟨⟨k, hk'⟩, -, rfl⟩ := mem_map.mp hk
      exact hk'
    have h := hl (s.map (Embedding.subtype _)) hsB (by rwa [card_map])
    rw [coe_map] at h
    exact h.comp_of_image Subtype.val_injective.injOn

/-- A family with at least `card ι = n` members is in general position exactly when the coefficient
vectors `j ↦ l k (Pi.single (e.symm j) 1)` of its forms, read in coordinates `e : ι ≃ Fin n`, are
in general position in `F^n`. -/
theorem isGeneralPosition_iff_inGeneralPosition [DecidableEq ι] [Fintype κ] {n : ℕ} (e : ι ≃ Fin n)
    {l : κ → Dual F (ι → F)} (h : n ≤ Fintype.card κ) :
    IsGeneralPosition l ↔ TauCeti.InGeneralPosition fun k j ↦ l k (Pi.single (e.symm j) 1) := by
  -- The coefficient vector of a form, an injective linear map.
  let c : Dual F (ι → F) →ₗ[F] Fin n → F :=
    LinearMap.pi fun j ↦ Dual.eval F (ι → F) (Pi.single (e.symm j) 1)
  have hc : LinearMap.ker c = ⊥ := LinearMap.ker_eq_bot'.mpr fun f hf ↦
    (Pi.basisFun F ι).ext fun i ↦ by
      simpa [c] using congr_fun hf (e i)
  have hn : n = Fintype.card ι := by simp [Fintype.card_congr e]
  have key : ∀ σ : Fin n → κ, Injective σ →
      (LinearIndependent F (l ∘ σ) ↔ LinearIndepOn F l (range σ)) := fun σ hσ ↦ by
    rw [← image_univ, TauCeti.linearIndepOn_image_iff _ hσ.injOn, linearIndepOn_univ_iff]
  -- Independence of the coefficient vectors of `l ∘ σ` is independence of `l ∘ σ`.
  have hcoef : ∀ σ : Fin n → κ, (Matrix.of fun i j ↦ l (σ i) (Pi.single (e.symm j) 1)).det ≠ 0 ↔
      LinearIndependent F (l ∘ σ) := fun σ ↦ by
    rw [← c.linearIndependent_iff hc, ← Matrix.nonsingular_iff_det_ne_zero,
      ← Matrix.linearIndependent_row_iff]
    congr!
  rw [TauCeti.inGeneralPosition_iff_det_ne_zero]
  constructor
  · intro hl σ hσ
    rw [hcoef, key σ hσ]
    have := hl (univ.map ⟨σ, hσ⟩) (by rw [card_map, card_univ, Fintype.card_fin, hn])
    rwa [coe_map, coe_univ, image_univ] at this
  · intro hl s hs
    obtain ⟨t, hst, htn⟩ := Finset.exists_superset_card_eq (hs.trans hn.ge) h
    let σ : Fin n → κ := Subtype.val ∘ (t.equivFinOfCardEq htn).symm
    have hσ : Injective σ := Subtype.val_injective.comp (Equiv.injective _)
    have hrange : range σ = t := by
      simp [σ, range_comp]
    exact ((key σ hσ).mp ((hcoef σ).mp (hl σ hσ))).mono (hrange ▸ coe_subset.mpr hst)

end Module.Dual
