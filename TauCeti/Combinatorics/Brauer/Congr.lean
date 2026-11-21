/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Relabel
-- Centralizer of `Sum.swap` in `Equiv.Perm (α ⊕ α)`, used to characterize the stabilizer of
-- `permToBrauer 1` under `PerfectMatching.congr`.
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Orbit, stabilizer, and arc framings of Brauer diagrams under boundary permutations

A Brauer diagram on `k` strands is a perfect matching of `Fin k ⊕ Fin k`, so the symmetric group
`Equiv.Perm (Fin k ⊕ Fin k)` of the `2 * k` boundary points acts on `BrauerDiagram k` through
`PerfectMatching.congr`, transporting each arc to the image of its two endpoints.

When a Brauer diagram acts on a tensor power through a *symmetric* bilinear form (as in
`TauCeti.BrauerDiagram.orthogonalActionMatrix`), each arc contributes symmetrically in its two
endpoints. When the form is *alternating* (as in the symplectic Brauer action
`TauCeti.BrauerDiagram.symplecticActionMatrix`), exchanging the two endpoints of an arc negates its
contribution, so defining an orientation-independent diagram matrix requires choosing an orientation
of the `k` arcs together with a compensating sign. Transporting the identity diagram
`permToBrauer 1` along a boundary permutation `φ : Equiv.Perm (Fin k ⊕ Fin k)` — an **arc framing**
(`TauCeti.BrauerDiagram.IsFraming`) — orients the `i`-th arc from `φ (Sum.inl i)` to
`φ (Sum.inr i)`: weighting the product of those `k` oriented arc kernels by `Equiv.Perm.sign φ` is
invariant under permuting the `k` strands (which has even sign) and under reversing individual arcs
(which negates both `sign φ` and the antisymmetric kernel).

This file supplies the unweighted framing API and the orbit-stabilizer normal forms behind that
construction and its loop and reconnection evaluations:

1. **Arc framings and transport.** `TauCeti.BrauerDiagram.IsFraming` packages the condition
   `PerfectMatching.congr π (permToBrauer 1) = D`, characterized pointwise by
   `TauCeti.BrauerDiagram.isFraming_iff` and closed under boundary congruence, relabelling,
   reconnection, and arc reversal (`IsFraming.congr`, `IsFraming.relabel`, `IsFraming.reconnect`,
   `IsFraming.mul_swap_inl_inr`).
2. **Transitivity and prescribed-arc witnesses.** Every Brauer diagram `D` on `k` strands has `k`
   arcs (`TauCeti.BrauerDiagram.card_isLowerEnd`), so sending the `k` bottom points to the lower
   ends of `D` and the `k` top points to their partners constructs a canonical framing
   `TauCeti.BrauerDiagram.framing` (`TauCeti.BrauerDiagram.isFraming_framing`,
   `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one`). Refining that witness places any one arc
   (`TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq`,
   `TauCeti.BrauerDiagram.exists_isFraming_apply_eq`) or any two disjoint arcs
   (`TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq_of_val_eq`,
   `TauCeti.BrauerDiagram.exists_isFraming_apply_pair_eq`) onto dedicated strands with prescribed
   endpoint orientations, isolating the arcs that close a loop or reconnect under a cap-cup
   generator.
3. **Stabilizer of the identity diagram.** A boundary permutation fixes `permToBrauer 1` under
   `PerfectMatching.congr` precisely when it commutes with `Sum.swap`, so any two boundary
   permutations transporting `permToBrauer 1` to the same diagram differ on the right by a
   simultaneous strand permutation `Equiv.Perm.sumCongr π π` followed by selective swaps of the two
   endpoints of each strand
   (`TauCeti.BrauerDiagram.exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq`).

## Main definitions

* `TauCeti.BrauerDiagram.IsFraming`: a boundary permutation carrying `permToBrauer 1` to `D`.
* `TauCeti.BrauerDiagram.framing`: a chosen framing of a Brauer diagram.

## Main results

* `TauCeti.BrauerDiagram.isFraming_iff`: pointwise characterization of an arc framing.
* `TauCeti.BrauerDiagram.isFraming_framing`, `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one`:
  every Brauer diagram is a boundary transport of `permToBrauer 1`.
* `TauCeti.BrauerDiagram.exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq`: two boundary
  permutations transporting `permToBrauer 1` to the same diagram differ by a strand permutation and
  endpoint swaps.
* `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq`,
  `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_eq_of_val_eq`,
  `TauCeti.BrauerDiagram.exists_isFraming_apply_eq`, and
  `TauCeti.BrauerDiagram.exists_isFraming_apply_pair_eq`: boundary transports placing one or two
  disjoint oriented arcs on dedicated strands.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace TauCeti.BrauerDiagram

variable {k : ℕ}

/-! ### Arc framings of a Brauer diagram -/

/-- An **arc framing** of a Brauer diagram `D` on `k` strands is a permutation `π` of the boundary
points `Fin k ⊕ Fin k` carrying the identity diagram `permToBrauer 1` to `D`, so that the `k`
ordered pairs `(π (Sum.inl r), π (Sum.inr r))` list the `k` arcs of `D`. -/
def IsFraming (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) : Prop :=
  PerfectMatching.congr π (permToBrauer 1) = D

/-- Being a framing means transporting `permToBrauer 1` to `D`. -/
theorem isFraming_def (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) :
    D.IsFraming π ↔ PerfectMatching.congr π (permToBrauer 1) = D := Iff.rfl

/-- **Characterisation of an arc framing**: `π` frames `D` precisely when `D` matches
`π (Sum.inl r)` with `π (Sum.inr r)` for every `r : Fin k`. -/
theorem isFraming_iff (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) :
    D.IsFraming π ↔ ∀ r : Fin k, D.val (π (Sum.inl r)) = π (Sum.inr r) := by
  refine ⟨fun h r => ?_, fun h => Subtype.ext (Equiv.ext fun x => ?_)⟩
  · rw [← h, PerfectMatching.congr_val_apply_apply, permToBrauer_val_inl, Equiv.Perm.one_apply]
  · rw [PerfectMatching.congr_val_apply]
    rcases hx : π.symm x with r | r
    · rw [permToBrauer_val_inl, Equiv.Perm.one_apply, ← h r, ← hx, π.apply_symm_apply]
    · simp only [permToBrauer_val_inr, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply]
      rw [← D.apply_eq_of_apply_eq (h r), ← hx, π.apply_symm_apply]

/-- A framing sends `Sum.inl r` and `Sum.inr r` to partners under `D`. -/
theorem IsFraming.val_inl {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (r : Fin k) : D.val (π (Sum.inl r)) = π (Sum.inr r) :=
  (D.isFraming_iff π).mp hπ r

/-- A framing sends `Sum.inr r` and `Sum.inl r` to partners under `D`. -/
theorem IsFraming.val_inr {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (r : Fin k) : D.val (π (Sum.inr r)) = π (Sum.inl r) :=
  D.apply_eq_of_apply_eq (hπ.val_inl r)

/-- A framing intertwines `D.val` with `Sum.swap`. -/
theorem IsFraming.val_apply {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (x : Fin k ⊕ Fin k) : D.val (π x) = π x.swap := by
  cases x
  · exact hπ.val_inl _
  · exact hπ.val_inr _

/-- The identity permutation frames the identity diagram. -/
theorem isFraming_permToBrauer_one : (permToBrauer (1 : Equiv.Perm (Fin k))).IsFraming 1 :=
  PerfectMatching.congr_refl _

/-- `Equiv.Perm.sumCongr 1 σ` frames `permToBrauer σ`. -/
theorem isFraming_permToBrauer (σ : Equiv.Perm (Fin k)) :
    (permToBrauer σ).IsFraming (Equiv.Perm.sumCongr 1 σ) := by
  simp [IsFraming, ← relabel_def]

/-- Transporting a diagram along `ρ` multiplies its framings on the left by `ρ`. -/
theorem IsFraming.congr {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (ρ : Equiv.Perm (Fin k ⊕ Fin k)) :
    IsFraming (PerfectMatching.congr ρ D) (ρ * π) :=
  (PerfectMatching.congr_trans π ρ (permToBrauer 1)).symm.trans (congrArg _ hπ)

/-- Relabelling a diagram multiplies its framings on the left by `Equiv.Perm.sumCongr σ τ`. -/
theorem IsFraming.relabel {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (σ τ : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).IsFraming (Equiv.Perm.sumCongr σ τ * π) := by
  rw [relabel_def]
  exact hπ.congr (Equiv.Perm.sumCongr σ τ)

/-- Reconnecting two arcs multiplies framings on the left by the reconnecting transposition. -/
theorem IsFraming.reconnect {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (x y : Fin k ⊕ Fin k) :
    IsFraming (D.reconnect x y) (Equiv.swap (D.val x) y * π) := by
  have hrec : D.reconnect x y = PerfectMatching.congr (Equiv.swap (D.val x) y) D :=
    Subtype.ext ((PerfectMatching.reconnect_val D x y).trans (PerfectMatching.congr_val _ D).symm)
  rw [hrec]
  exact hπ.congr (Equiv.swap (D.val x) y)

/-- Reversing the orientation of the `r`-th arc in a framing leaves it a framing of `D`. -/
theorem IsFraming.mul_swap_inl_inr {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (r : Fin k) :
    D.IsFraming (π * Equiv.swap (Sum.inl r) (Sum.inr r)) := by
  rw [isFraming_iff]
  intro s
  rcases eq_or_ne s r with rfl | hsr
  · simp [hπ.val_inr s]
  · have h1 : Sum.inl s ≠ (Sum.inl r : Fin k ⊕ Fin k) := Sum.inl_injective.ne hsr
    have h2 : Sum.inr s ≠ (Sum.inr r : Fin k ⊕ Fin k) := Sum.inr_injective.ne hsr
    simp [Equiv.swap_apply_of_ne_of_ne, h1, h2, hπ.val_inl s]

/-! ### Existence, stabilizer, and prescribed-arc framings -/

/-- Exchanging the two endpoints of a single strand of `permToBrauer 1` fixes the diagram. -/
private theorem congr_swap_inr_inl_permToBrauer_one (i : Fin k) :
    PerfectMatching.congr (Equiv.swap (Sum.inr i) (Sum.inl i)) (permToBrauer 1) =
      permToBrauer 1 := by
  have hval : (permToBrauer (1 : Equiv.Perm (Fin k))).val (Sum.inr i) = Sum.inl i :=
    permToBrauer_one_val_apply (Sum.inr i)
  rw [Equiv.swap_comm, ← hval, ← PerfectMatching.reconnect_def, PerfectMatching.reconnect_self]

/-- **A chosen arc framing of `D`**: enumerate the `k` lower ends of `D` and send `Sum.inl r` to
the `r`-th lower end and `Sum.inr r` to its partner. -/
noncomputable def framing (D : BrauerDiagram k) : Equiv.Perm (Fin k ⊕ Fin k) :=
  let e : Fin k ≃ {x // D.IsLowerEnd x} :=
    Fintype.equivOfCardEq ((Fintype.card_fin k).trans D.card_isLowerEnd.symm)
  (Equiv.sumCongr e (e.trans D.notLowerEndEquiv.symm)).trans (Equiv.sumCompl D.IsLowerEnd)

/-- `D.framing` frames `D`. -/
theorem isFraming_framing (D : BrauerDiagram k) : D.IsFraming D.framing := by
  refine Subtype.ext (Equiv.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := D.framing.surjective y
  rw [PerfectMatching.congr_val_apply_apply, permToBrauer_one_val_apply]
  rcases x with i | i <;> simp [framing, D.apply_apply]

/-- **Every Brauer diagram is a transport of the identity diagram** along a permutation of the
boundary points: sending the `k` bottom points to the lower ends of `D` and the `k` top points to
their partners matches each strand of `permToBrauer 1` with an arc of `D`. -/
theorem exists_congr_permToBrauer_one (D : BrauerDiagram k) :
    ∃ φ : Equiv.Perm (Fin k ⊕ Fin k), PerfectMatching.congr φ (permToBrauer 1) = D :=
  ⟨D.framing, D.isFraming_framing⟩

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

/-- **Orienting one chosen arc in a framing**: for any boundary point `x`, some framing of `D`
lists the arc through `x` in the orientation `(x, D.val x)`. -/
theorem exists_isFraming_apply_eq (D : BrauerDiagram k) (x : Fin k ⊕ Fin k) :
    ∃ (π : Equiv.Perm (Fin k ⊕ Fin k)) (r : Fin k),
      D.IsFraming π ∧ π (Sum.inl r) = x ∧ π (Sum.inr r) = D.val x :=
  D.exists_congr_permToBrauer_one_of_val_eq rfl

/-- **Orienting two distinct arcs in a framing**: when `x` and `y` lie on distinct arcs of `D`,
some framing of `D` lists the arc at `x` as `(x, D.val x)` at index `r₁` and the arc at `y` as
`(D.val y, y)` at index `r₂ ≠ r₁`. -/
theorem exists_isFraming_apply_pair_eq (D : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (hxy : x ≠ y) (hDx : D.val x ≠ y) :
    ∃ (π : Equiv.Perm (Fin k ⊕ Fin k)) (r₁ r₂ : Fin k), r₁ ≠ r₂ ∧ D.IsFraming π ∧
      π (Sum.inl r₁) = x ∧ π (Sum.inr r₁) = D.val x ∧
      π (Sum.inl r₂) = D.val y ∧ π (Sum.inr r₂) = y :=
  D.exists_congr_permToBrauer_one_of_val_eq_of_val_eq rfl (D.apply_apply y)
    (fun h => hDx (D.apply_eq_of_apply_eq h)) (fun h => hxy (D.val.injective h).symm)

end TauCeti.BrauerDiagram
