/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Bases adapted to a finite descending filtration

A finite descending filtration of a finite-dimensional vector space over a division ring admits a
basis, indexed by `Fin (finrank K V)`, with positive integer weights: its `k`-th term consists
exactly of vectors whose coordinates of weight at most `k` vanish. Equivalently, it is spanned by
the basis vectors of weight greater than `k`.

This supplies adapted bases for filtrations such as the lower central series of a nilpotent Lie
algebra. The construction splits off a complement `C` of the first positive-index term `W`
(`Submodule.exists_isCompl`) and combines an adapted basis of `W` with a basis of `C` through
`Submodule.prodEquivOfIsCompl`. Repeated terms and the zero space are allowed.
-/

public section

namespace TauCeti

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A finite descending filtration admits a basis indexed by `Fin (finrank K V)` with positive
bounded weights, in which membership in a filtration term is equivalent to the vanishing of all
lower-weight coordinates. -/
theorem exists_basis_weight_of_antitone (F : ℕ → Submodule K V) (hF : Antitone F)
    (hzero : F 0 = ⊤) (N : ℕ) (hN : F N = ⊥) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      (∀ i, 0 < w i ∧ w i ≤ N) ∧
      ∀ k x, x ∈ F k ↔ ∀ i, w i ≤ k → b.repr x i = 0 := by
  -- Build an adapted basis with an arbitrary finite index type, then reindex it by `Fin`.
  suffices ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι K V) (w : ι → ℕ),
      (∀ i, 0 < w i ∧ w i ≤ N) ∧ ∀ k x, x ∈ F k ↔ ∀ i, w i ≤ k → b.repr x i = 0 by
    obtain ⟨ι, _, b, w, hw, hmem⟩ := this
    let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
    refine ⟨b.reindex e, w ∘ e.symm, fun i ↦ hw _, fun k x ↦ ?_⟩
    simpa [hmem] using e.symm.forall_congr_right.symm
  induction N generalizing V with
  | zero =>
    have : Subsingleton V := (Submodule.subsingleton_iff K).mp
      (subsingleton_of_bot_eq_top (hN.symm.trans hzero))
    refine ⟨PEmpty, inferInstance, Basis.empty V, PEmpty.elim, fun i ↦ i.elim, fun k x ↦ ?_⟩
    simp [Subsingleton.eq_zero x]
  | succ N ih =>
    -- Split `V = W ⊕ C` with `W = F 1`, take an adapted basis of `W` for the shifted
    -- filtration, and give every vector of a basis of `C` weight `1`.
    let W := F 1
    obtain ⟨C, hC⟩ := W.exists_isCompl
    let G : ℕ → Submodule K W := fun k ↦ (F (k + 1)).comap W.subtype
    have hG : Antitone G := fun a b hab ↦ Submodule.comap_mono (hF (by omega))
    have hGzero : G 0 = ⊤ := by ext x; simp [G, W]
    have hGN : G N = ⊥ := by simp [G, hN, Submodule.ker_subtype]
    obtain ⟨ι, _, bW, wW, hweight, hmem⟩ := ih G hG hGzero hGN
    let e := W.prodEquivOfIsCompl C hC
    let b := (bW.prod (Module.finBasis K C)).map e
    let w : ι ⊕ Fin (finrank K C) → ℕ := Sum.elim (fun i ↦ wW i + 1) (fun _ ↦ 1)
    refine ⟨_, inferInstance, b, w, ?_, ?_⟩
    · rintro (i | i) <;> simp [w, hweight]
    · rintro (_ | k) x
      · -- Every weight is positive, so the zero-index condition is vacuous.
        have hw0 : ∀ i, ¬w i ≤ 0 := by rintro (_ | _) <;> simp [w]
        simp [hzero, hw0]
      · have hsymm (y : W) : e.symm y = (y, 0) := W.prodEquivOfIsCompl_symm_apply_left C hC y
        constructor
        · intro hx
          have hxW : x ∈ W := hF (by omega) hx
          rintro (i | i) hi
          · simpa [b, hsymm ⟨x, hxW⟩] using (hmem k ⟨x, hxW⟩).mp hx i (by simpa [w] using hi)
          · simp [b, hsymm ⟨x, hxW⟩]
        · intro hx
          have hxW : x ∈ W := (W.prodEquivOfIsCompl_symm_apply_snd_eq_zero C hC).mp <|
            (Module.finBasis K C).repr.injective <| Finsupp.ext fun j ↦ by
              simpa [b, e] using hx (.inr j) (by simp [w])
          refine (hmem k ⟨x, hxW⟩).mpr fun i hi ↦ ?_
          simpa [b, hsymm ⟨x, hxW⟩] using hx (.inl i) (by simpa [w] using hi)

end TauCeti
