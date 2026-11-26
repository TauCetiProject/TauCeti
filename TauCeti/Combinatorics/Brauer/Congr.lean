/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Diagram
-- Centralizer of `Sum.swap` in `Equiv.Perm (α ⊕ α)`, used to characterize the stabilizer of
-- `permToBrauer 1` under `PerfectMatching.congr`.
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Orbit and stabilizer of Brauer diagrams under boundary permutations

A Brauer diagram on `k` strands is a perfect matching of `Fin k ⊕ Fin k`, so the symmetric group
`Equiv.Perm (Fin k ⊕ Fin k)` of the `2 * k` boundary points acts on `BrauerDiagram k` through
`PerfectMatching.congr`, transporting each arc to the image of its two endpoints.

When a Brauer diagram acts on a tensor power through a *symmetric* bilinear form (as in
`TauCeti.BrauerDiagram.orthogonalActionMatrix`), each arc contributes symmetrically in its two
endpoints. When the form is *alternating* (as in the symplectic Brauer action
`TauCeti.BrauerDiagram.symplecticActionMatrix`), exchanging the two endpoints of an arc negates its
contribution, so defining an orientation-independent diagram matrix requires choosing an orientation
of the `k` arcs together with a compensating sign. Transporting the identity diagram
`permToBrauer 1` along a boundary permutation `φ : Equiv.Perm (Fin k ⊕ Fin k)` orients the `i`-th
arc from `φ (Sum.inl i)` to `φ (Sum.inr i)`: weighting the product of those `k` oriented arc
kernels by `Equiv.Perm.sign φ` is invariant under permuting the `k` strands (which has even sign)
and under reversing individual arcs (which negates both `sign φ` and the antisymmetric kernel).

This file supplies the orbit-stabilizer normal forms behind that construction and its loop and
reconnection evaluations:

1. **Transitivity and prescribed-arc witnesses.** Every Brauer diagram `D` on `k` strands has `k`
   arcs (`TauCeti.BrauerDiagram.card_isLowerEnd`), so sending the `k` bottom points to the lower
   ends of `D` and the `k` top points to their partners builds a boundary permutation transporting
   `permToBrauer 1` to `D` (`TauCeti.BrauerDiagram.exists_congr_permToBrauer_one`). Refining that
   witness places any one arc (`TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq`) or
   any two disjoint arcs (`TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq_of_val_eq`)
   onto dedicated strands with prescribed endpoint orientations, isolating the arcs that close a
   loop or reconnect under a cap-cup generator.
2. **Stabilizer of the identity diagram.** A boundary permutation fixes `permToBrauer 1` under
   `PerfectMatching.congr` precisely when it commutes with `Sum.swap`, so any two boundary
   permutations transporting `permToBrauer 1` to the same diagram differ on the right by a
   simultaneous strand permutation `Equiv.Perm.sumCongr π π` followed by selective swaps of the two
   endpoints of each strand
   (`TauCeti.BrauerDiagram.exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq`).

## Main results

* `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one`: every Brauer diagram is a boundary
  transport of `permToBrauer 1`.
* `TauCeti.BrauerDiagram.exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq`: two boundary
  permutations transporting `permToBrauer 1` to the same diagram differ by a strand permutation and
  endpoint swaps.
* `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq` and
  `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq_of_val_eq`: boundary transports
  placing one or two disjoint oriented arcs on dedicated strands.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace TauCeti.BrauerDiagram

variable {k : ℕ}

/-- Exchanging the two endpoints of a single strand of `permToBrauer 1` fixes the diagram. -/
private theorem congr_swap_inr_inl_permToBrauer_one (i : Fin k) :
    PerfectMatching.congr (Equiv.swap (Sum.inr i) (Sum.inl i)) (permToBrauer 1) =
      permToBrauer 1 := by
  have hval : (permToBrauer (1 : Equiv.Perm (Fin k))).val (Sum.inr i) = Sum.inl i :=
    permToBrauer_one_val_apply (Sum.inr i)
  rw [Equiv.swap_comm, ← hval, ← PerfectMatching.reconnect_def, PerfectMatching.reconnect_self]

/-- **Every Brauer diagram is a transport of the identity diagram** along a permutation of the
boundary points: sending the `k` bottom points to the lower ends of `D` and the `k` top points to
their partners matches each strand of `permToBrauer 1` with an arc of `D`. -/
theorem exists_congr_permToBrauer_one (D : BrauerDiagram k) :
    ∃ φ : Equiv.Perm (Fin k ⊕ Fin k), PerfectMatching.congr φ (permToBrauer 1) = D := by
  let e : Fin k ≃ {x // D.IsLowerEnd x} :=
    Fintype.equivOfCardEq ((Fintype.card_fin k).trans D.card_isLowerEnd.symm)
  let φ : Equiv.Perm (Fin k ⊕ Fin k) :=
    (Equiv.sumCongr e (e.trans D.notLowerEndEquiv.symm)).trans (Equiv.sumCompl D.IsLowerEnd)
  refine ⟨φ, Subtype.ext (Equiv.ext fun y => ?_)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [PerfectMatching.congr_val_apply_apply, permToBrauer_one_val_apply]
  rcases x with i | i <;> simp [φ, D.apply_apply]

/-- **Two boundary permutations transport `permToBrauer 1` to the same diagram** only when they
differ on the right by a simultaneous permutation of the strands followed by swaps of strand
endpoints. -/
theorem exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq
    {φ₁ φ₂ : Equiv.Perm (Fin k ⊕ Fin k)}
    (h : PerfectMatching.congr φ₁ (permToBrauer 1) = PerfectMatching.congr φ₂ (permToBrauer 1)) :
    ∃ (π : Equiv.Perm (Fin k)) (τ : Fin k → Equiv.Perm Bool),
      φ₂ = φ₁ * Equiv.Perm.sumCongr π π *
        (Equiv.boolProdEquivSum (Fin k)).permCongr (Equiv.prodCongrLeft τ) := by
  have hcomm (x : Fin k ⊕ Fin k) : (φ₁⁻¹ * φ₂) x.swap = ((φ₁⁻¹ * φ₂) x).swap := by
    have hx := congrArg (fun D : BrauerDiagram k => D.val (φ₂ x)) h
    simp only [PerfectMatching.congr_val_apply, permToBrauer_one_val_apply,
      Equiv.symm_apply_apply] at hx
    exact φ₁.injective (by simpa [Equiv.Perm.mul_apply, ← Equiv.Perm.inv_def] using hx.symm)
  obtain ⟨π, τ, hψ⟩ := Equiv.Perm.exists_sumCongr_mul_prodCongrLeft_of_commute_sumSwap hcomm
  refine ⟨π, τ, ?_⟩
  rw [mul_assoc, ← hψ, mul_inv_cancel_left]

/-- Given a boundary transport `φ₀` of `permToBrauer 1` to `D` and an oriented arc `D.val x = y`,
re-orient the single strand `i₀` carrying `x` so that `Sum.inl i₀ ↦ x` and `Sum.inr i₀ ↦ y`,
leaving all other strands `j ≠ i₀` unchanged. -/
private theorem exists_congr_permToBrauer_one_orient_arc {D : BrauerDiagram k}
    {φ₀ : Equiv.Perm (Fin k ⊕ Fin k)} (hφ₀ : PerfectMatching.congr φ₀ (permToBrauer 1) = D)
    {x y : Fin k ⊕ Fin k} (h : D.val x = y) :
    ∃ (φ : Equiv.Perm (Fin k ⊕ Fin k)) (i₀ : Fin k),
      PerfectMatching.congr φ (permToBrauer 1) = D ∧
        (φ₀ (Sum.inl i₀) = x ∨ φ₀ (Sum.inr i₀) = x) ∧
        φ (Sum.inl i₀) = x ∧ φ (Sum.inr i₀) = y ∧
        ∀ j ≠ i₀, φ (Sum.inl j) = φ₀ (Sum.inl j) ∧ φ (Sum.inr j) = φ₀ (Sum.inr j) := by
  have hpartner (z : Fin k ⊕ Fin k) : φ₀ z.swap = D.val (φ₀ z) := by
    rw [← hφ₀, PerfectMatching.congr_val_apply_apply, permToBrauer_one_val_apply]
  rcases hsymm : φ₀.symm x with i₀ | i₀
  · have hx : φ₀ (Sum.inl i₀) = x := by rw [← hsymm, Equiv.apply_symm_apply]
    exact ⟨φ₀, i₀, hφ₀, Or.inl hx, hx, (hpartner (Sum.inl i₀)).trans (hx ▸ h),
      fun _ _ => ⟨rfl, rfl⟩⟩
  · have hx : φ₀ (Sum.inr i₀) = x := by rw [← hsymm, Equiv.apply_symm_apply]
    let φ : Equiv.Perm (Fin k ⊕ Fin k) := φ₀ * Equiv.swap (Sum.inr i₀) (Sum.inl i₀)
    have hφ : PerfectMatching.congr φ (permToBrauer 1) = D := by
      rw [PerfectMatching.congr_mul, congr_swap_inr_inl_permToBrauer_one, hφ₀]
    refine ⟨φ, i₀, hφ, Or.inr hx, ?_, ?_, fun j hj => ⟨?_, ?_⟩⟩
    · simp [φ, Equiv.Perm.mul_apply, hx]
    · simpa [φ, Equiv.Perm.mul_apply, hx, ← h] using hpartner (Sum.inr i₀)
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hj)]
    · rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hj) Sum.inr_ne_inl]

/-- **Transporting `permToBrauer 1` to `D` with one prescribed oriented arc.** Any arc `D.val x = y`
can be placed on some strand `i₀` with `x` as the image of `Sum.inl i₀` and `y` as the image of
`Sum.inr i₀`. -/
theorem exists_congr_permToBrauer_one_of_val_eq (D : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (h : D.val x = y) :
    ∃ (φ : Equiv.Perm (Fin k ⊕ Fin k)) (i₀ : Fin k),
      PerfectMatching.congr φ (permToBrauer 1) = D ∧
        φ (Sum.inl i₀) = x ∧ φ (Sum.inr i₀) = y := by
  obtain ⟨φ₀, hφ₀⟩ := D.exists_congr_permToBrauer_one
  obtain ⟨φ, i₀, hφ, -, hx, hy, -⟩ := exists_congr_permToBrauer_one_orient_arc hφ₀ h
  exact ⟨φ, i₀, hφ, hx, hy⟩

/-- **Transporting `permToBrauer 1` to `D` with two prescribed disjoint oriented arcs.** -/
theorem exists_congr_permToBrauer_one_of_val_eq_of_val_eq (D : BrauerDiagram k)
    {x₁ y₁ x₂ y₂ : Fin k ⊕ Fin k} (h₁ : D.val x₁ = y₁) (h₂ : D.val x₂ = y₂)
    (hne : x₂ ≠ x₁) (hne' : x₂ ≠ y₁) :
    ∃ (φ : Equiv.Perm (Fin k ⊕ Fin k)) (i₁ i₂ : Fin k), i₁ ≠ i₂ ∧
      PerfectMatching.congr φ (permToBrauer 1) = D ∧
        φ (Sum.inl i₁) = x₁ ∧ φ (Sum.inr i₁) = y₁ ∧
          φ (Sum.inl i₂) = x₂ ∧ φ (Sum.inr i₂) = y₂ := by
  obtain ⟨φ₁, i₁, hφ₁, hx₁, hy₁⟩ := D.exists_congr_permToBrauer_one_of_val_eq h₁
  obtain ⟨φ, i₂, hφ, hcase, hx₂, hy₂, hkeep⟩ := exists_congr_permToBrauer_one_orient_arc hφ₁ h₂
  have hi : i₁ ≠ i₂ := by
    rintro rfl
    rcases hcase with h | h
    · exact hne (h.symm.trans hx₁)
    · exact hne' (h.symm.trans hy₁)
  obtain ⟨hkeep_inl, hkeep_inr⟩ := hkeep i₁ hi
  exact ⟨φ, i₁, i₂, hi, hφ, hkeep_inl.trans hx₁, hkeep_inr.trans hy₁, hx₂, hy₂⟩

end TauCeti.BrauerDiagram
