/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Bases adapted to a finite descending filtration

A finite descending filtration of a finite-dimensional vector space admits a basis with positive
integer weights: its `k`-th term consists exactly of vectors whose coordinates of weight at most
`k` vanish. Equivalently, it is spanned by the basis vectors of weight greater than `k`.

This supplies adapted bases for filtrations such as the lower central series of a nilpotent Lie
algebra. The construction uses Mathlib's `Module.Basis.sumQuot` to combine an adapted basis of
the first positive-index term with a basis of its quotient. Repeated terms and the zero space
are allowed.
-/

public section

namespace TauCeti

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A finite descending filtration admits a finite basis with positive bounded weights, in which
membership in a filtration term is equivalent to the vanishing of all lower-weight coordinates. -/
theorem exists_basis_weight_of_antitone (F : ℕ → Submodule K V) (hF : Antitone F)
    (hzero : F 0 = ⊤) (N : ℕ) (hN : F N = ⊥) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι K V) (w : ι → ℕ),
      (∀ i, 0 < w i ∧ w i ≤ N) ∧
      ∀ k x, x ∈ F k ↔ ∀ i, w i ≤ k → b.repr x i = 0 := by
  classical
  induction N generalizing V with
  | zero =>
    have htop : (⊤ : Submodule K V) = ⊥ := hzero.symm.trans hN
    have : Subsingleton V := (Submodule.subsingleton_iff K).mp
      (subsingleton_of_bot_eq_top htop.symm)
    refine ⟨PEmpty, inferInstance, Basis.empty V, PEmpty.elim, ?_, ?_⟩
    · intro i; exact i.elim
    · intro k x
      simp [Subsingleton.eq_zero x]
  | succ N ih =>
    let W := F 1
    let G : ℕ → Submodule K W := fun k ↦ (F (k + 1)).comap W.subtype
    have hG : Antitone G := fun a b hab ↦ Submodule.comap_mono (hF (by omega))
    have hGzero : G 0 = ⊤ := by ext x; simp [G, W]
    have hGN : G N = ⊥ := by simp [G, hN, Submodule.ker_subtype]
    obtain ⟨ι, _, bW, wW, hweight, hmem⟩ := ih G hG hGzero hGN
    let bQ := Module.finBasis K (V ⧸ W)
    let b := bW.sumQuot bQ
    let w : ι ⊕ Fin (Module.finrank K (V ⧸ W)) → ℕ :=
      Sum.elim (fun i ↦ wW i + 1) (fun _ ↦ 1)
    refine ⟨_, inferInstance, b, w, ?_, ?_⟩
    · intro i
      cases i with
      | inl i => exact ⟨by simp [w], Nat.add_le_add_right (hweight i).2 1⟩
      | inr i => simp [w]
    · intro k x
      cases k with
      | zero =>
        -- Every weight is positive, so the zero-index condition is vacuous.
        have hw0 : ∀ i, ¬w i ≤ 0 := by
          intro i
          cases i <;> simp [w]
        simp [hzero, hw0]
      | succ k =>
        constructor
        · intro hx
          have hxW : x ∈ W := hF (by omega) hx
          intro i hi
          cases i with
          | inl i =>
            have hc := (hmem k ⟨x, hxW⟩).mp hx i (by simpa [w] using hi)
            simpa [b, Basis.sumQuot_repr_inl_of_mem, hxW] using hc
          | inr i => exact Basis.sumQuot_repr_inr_of_mem bW bQ x hxW i
        · intro hx
          have hquot : W.mkQ x = 0 := by
            apply bQ.repr.injective
            ext i
            have hc := hx (Sum.inr i) (by simp [w])
            simpa [b, Basis.sumQuot_repr_inr] using hc
          have hxW : x ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hquot
          apply (hmem k ⟨x, hxW⟩).mpr
          intro i hi
          have hc := hx (Sum.inl i) (by simpa [w] using hi)
          simpa [b, Basis.sumQuot_repr_inl_of_mem, hxW] using hc

end TauCeti
