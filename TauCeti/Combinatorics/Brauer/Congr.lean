/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.Combinatorics.Brauer.Flip
public import TauCeti.Combinatorics.Brauer.Generator

/-!
# Boundary permutations and cap-cup reconnections of Brauer diagrams

A Brauer diagram on `k` strands is a perfect matching of `Fin k ⊕ Fin k`. The symmetric group
`Equiv.Perm (Fin k ⊕ Fin k)` of the `2 * k` boundary points acts on `BrauerDiagram k` through
`PerfectMatching.congr`, transporting each arc to the image of its two endpoints. Several
operations on Brauer diagrams are already instances of this action: relabelling the two boundaries
(`TauCeti.BrauerDiagram.relabel`), reflecting a diagram upside down (`TauCeti.BrauerDiagram.flip`),
and bending two strands of the identity diagram into a cap and a cup (`TauCeti.capCup`).

This file proves three facts about that boundary action:

1. **Transitivity from the identity diagram.** Every Brauer diagram `D` on `k` strands has `k`
   arcs (`TauCeti.BrauerDiagram.card_isLowerEnd`), so sending the `k` bottom points to the lower
   ends of `D` and the `k` top points to their partners builds a boundary permutation transporting
   `permToBrauer 1` to `D` (`TauCeti.BrauerDiagram.exists_congr_permToBrauer_one`), with variants
   orienting one or two chosen arcs along specified strands.
2. **The stabilizer of the identity diagram.** A boundary permutation fixes `permToBrauer 1` under
   `PerfectMatching.congr` precisely when it commutes with `Sum.swap`, so any two permutations
   transporting `permToBrauer 1` to the same diagram differ on the right by a simultaneous
   permutation `Equiv.Perm.sumCongr π π` of the strands followed by a selective swap of the two
   endpoints of each strand
   (`TauCeti.BrauerDiagram.exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq`).
3. **Stacking a cap-cup generator is a reconnection.** For `a ≠ b`, stacking `capCup a b` above an
   arbitrary diagram `D` reconnects the two arcs of `D` meeting the top points `a` and `b`
   (`TauCeti.composeDiagram_capCup_left`), transporting `D` along the single boundary transposition
   `Equiv.swap (D.val (Sum.inr a)) (Sum.inr b)`. When `D` already cups `a` to `b` that
   transposition is trivial and the stack closes up one middle loop; otherwise the transposition
   moves two distinct points and no middle loop closes up (`TauCeti.middleLoopCount_capCup_left`).
   Reflection gives the mirror statements for stacking `capCup a b` underneath `D`.

## Main results

* `Equiv.Perm.exists_sumCongr_mul_prodCongrLeft_of_commute_swap`: a permutation of `α ⊕ α`
  commuting with `Sum.swap` factors into `Equiv.Perm.sumCongr π π` and a fibrewise permutation
  along `Equiv.boolProdEquivSum α`.
* `Equiv.Perm.sign_sumComm`: the sign of `Equiv.sumComm α α` is `(-1) ^ Fintype.card α`.
* `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one`: every Brauer diagram is a boundary
  transport of `permToBrauer 1`, with `exists_congr_permToBrauer_one_of_val_eq` and
  `exists_congr_permToBrauer_one_of_val_eq_of_val_eq` prescribing one or two arcs.
* `TauCeti.BrauerDiagram.exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq`: two boundary
  permutations transporting `permToBrauer 1` to the same diagram differ by a strand permutation and
  endpoint swaps.
* `TauCeti.composeDiagram_capCup_left` and `TauCeti.composeDiagram_capCup_right`: stacking
  `capCup a b` (`a ≠ b`) onto any diagram `D` reconnects its arcs at `a` and `b`.
* `TauCeti.middleLoopCount_capCup_left` and `TauCeti.middleLoopCount_capCup_right`: stacking
  `capCup a b` (`a ≠ b`) onto `D` closes one loop if `D` already joins those two boundary points,
  and none otherwise.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace Equiv.Perm

/-- **Centralizer of `Sum.swap` in `Equiv.Perm (α ⊕ α)`.** Every permutation of `α ⊕ α` commuting
with `Sum.swap` permutes the `α`-fibres by some `π : Equiv.Perm α` and, within each fibre, acts on
its two elements through `Equiv.boolProdEquivSum α`. -/
theorem exists_sumCongr_mul_prodCongrLeft_of_commute_swap {α : Type*} {ψ : Equiv.Perm (α ⊕ α)}
    (hψ : ∀ x, ψ x.swap = (ψ x).swap) :
    ∃ (π : Equiv.Perm α) (τ : α → Equiv.Perm Bool),
      ψ = Equiv.Perm.sumCongr π π *
        (Equiv.boolProdEquivSum α).permCongr (Equiv.prodCongrLeft τ) := by
  set e := Equiv.boolProdEquivSum α
  set ψ₀ : Equiv.Perm (Bool × α) := e.symm.permCongr ψ
  have he_swap (b : Bool) (i : α) : e (!b, i) = (e (b, i)).swap := by
    cases b <;> rfl
  have he_symm_swap (z : α ⊕ α) : e.symm z.swap = (!(e.symm z).1, (e.symm z).2) := by
    cases z <;> rfl
  have hψ₀ (b : Bool) (i : α) : ψ₀ (!b, i) = (!(ψ₀ (b, i)).1, (ψ₀ (b, i)).2) := by
    simp only [ψ₀, Equiv.permCongr_apply, Equiv.symm_symm, he_swap, hψ, he_symm_swap]
  have hψ₀_symm (b : Bool) (i : α) :
      ψ₀.symm (!b, i) = (!(ψ₀.symm (b, i)).1, (ψ₀.symm (b, i)).2) := by
    rcases h : ψ₀.symm (b, i) with ⟨b', j⟩
    have hbj : ψ₀ (b', j) = (b, i) := by
      rw [← h, Equiv.apply_symm_apply]
    have hneg : ψ₀ (!b', j) = (!b, i) := by
      rw [hψ₀, hbj]
    rw [← hneg, Equiv.symm_apply_apply]
  have hsnd (b : Bool) (i : α) : (ψ₀ (b, i)).2 = (ψ₀ (false, i)).2 := by
    cases b
    · rfl
    · simpa using congrArg Prod.snd (hψ₀ false i)
  have hsnd_symm (b : Bool) (i : α) : (ψ₀.symm (b, i)).2 = (ψ₀.symm (false, i)).2 := by
    cases b
    · rfl
    · simpa using congrArg Prod.snd (hψ₀_symm false i)
  let π : Equiv.Perm α :=
    { toFun := fun i => (ψ₀ (false, i)).2
      invFun := fun i => (ψ₀.symm (false, i)).2
      left_inv := fun i => by
        dsimp only
        rw [← hsnd_symm (ψ₀ (false, i)).1, Prod.eta, Equiv.symm_apply_apply]
      right_inv := fun i => by
        dsimp only
        rw [← hsnd (ψ₀.symm (false, i)).1, Prod.eta, Equiv.apply_symm_apply] }
  let τ : α → Equiv.Perm Bool := fun i =>
    if (ψ₀ (false, i)).1 then Equiv.swap false true else 1
  refine ⟨π, τ, Equiv.ext fun x => ?_⟩
  have he_symm_inl (i : α) : e.symm (Sum.inl i) = (false, i) := rfl
  have he_symm_inr (i : α) : e.symm (Sum.inr i) = (!false, i) := rfl
  have hinl (i : α) :
      (Equiv.Perm.sumCongr π π * e.permCongr (Equiv.prodCongrLeft τ)) (Sum.inl i) =
        ψ (Sum.inl i) := by
    have hτ : τ i false = (ψ₀ (false, i)).1 := by
      dsimp only [τ]
      cases (ψ₀ (false, i)).1 <;> rfl
    have hmap (b : Bool) (j : α) : Equiv.Perm.sumCongr π π (e (b, j)) = e (b, π j) := by
      cases b <;> rfl
    have hψ_inl : e (ψ₀ (false, i)) = ψ (Sum.inl i) := by
      rw [Equiv.permCongr_apply, Equiv.symm_symm, e.apply_symm_apply]
      rfl
    rw [Equiv.Perm.mul_apply, Equiv.permCongr_apply, he_symm_inl, Equiv.prodCongrLeft_apply, hτ,
      hmap]
    exact hψ_inl
  rcases x with i | i
  · exact (hinl i).symm
  · have hτ_not (b : Bool) : τ i (!b) = !(τ i b) := by
      dsimp only [τ]
      cases (ψ₀ (false, i)).1 <;> cases b <;> rfl
    have hrhs_swap :
        (Equiv.Perm.sumCongr π π * e.permCongr (Equiv.prodCongrLeft τ)) (Sum.inr i) =
          ((Equiv.Perm.sumCongr π π * e.permCongr (Equiv.prodCongrLeft τ)) (Sum.inl i)).swap := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.permCongr_apply,
        he_symm_inr, he_symm_inl, Equiv.prodCongrLeft_apply, Equiv.prodCongrLeft_apply, hτ_not,
        he_swap]
      rcases e (τ i false, i) with j | j <;> rfl
    symm
    rw [hrhs_swap, hinl, ← hψ]
    rfl

/-- **The sign of `Equiv.sumComm α α`** is `(-1) ^ Fintype.card α`, since it is the product of the
`|α|` disjoint transpositions exchanging `Sum.inl i` with `Sum.inr i`. -/
theorem sign_sumComm (α : Type*) [Fintype α] [DecidableEq α] :
    Equiv.Perm.sign (Equiv.sumComm α α) = (-1 : ℤˣ) ^ Fintype.card α := by
  have heq : Equiv.sumComm α α =
      (Equiv.boolProdEquivSum α).permCongr
        (Equiv.prodCongrLeft fun _ : α => Equiv.swap false true) := by
    ext (i | i) <;> rfl
  rw [heq, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft]
  simp [Equiv.Perm.sign_swap (by decide : false ≠ true)]

end Equiv.Perm

namespace TauCeti

/-- Reconnecting two arcs of a perfect matching is transporting it along the transposition
`Equiv.swap (D.val a) b`. -/
theorem PerfectMatching.reconnect_eq_congr {α : Type*} [DecidableEq α] (D : PerfectMatching α)
    (a b : α) : D.reconnect a b = PerfectMatching.congr (Equiv.swap (D.val a) b) D :=
  Subtype.ext ((D.reconnect_val a b).trans (PerfectMatching.congr_val _ D).symm)

variable {k : ℕ} {a b : Fin k}

namespace BrauerDiagram

/-- The underlying involution of the identity diagram is `Sum.swap`. -/
@[simp]
theorem permToBrauer_one_val_apply (x : Fin k ⊕ Fin k) :
    (permToBrauer (1 : Equiv.Perm (Fin k))).val x = x.swap := by
  cases x <;> simp [Equiv.Perm.one_def]

/-- Reflecting a Brauer diagram is transporting its underlying perfect matching along
`Equiv.sumComm`. -/
theorem flip_eq_congr (D : BrauerDiagram k) :
    D.flip = PerfectMatching.congr (Equiv.sumComm (Fin k) (Fin k)) D :=
  Subtype.ext (Equiv.ext fun x => by
    rw [flip_val, PerfectMatching.congr_val_apply]
    rfl)

end BrauerDiagram

/-- The cap-cup generator `capCup a b` is the identity diagram transported along the boundary
transposition exchanging `Sum.inr a` with `Sum.inl b`. -/
theorem capCup_eq_congr (a b : Fin k) :
    capCup a b = PerfectMatching.congr (Equiv.swap (Sum.inr a) (Sum.inl b)) (permToBrauer 1) := by
  rcases eq_or_ne a b with rfl | hab
  · rw [capCup_self]
    refine Subtype.ext (Equiv.ext fun x => ?_)
    rw [PerfectMatching.congr_val_apply, Equiv.symm_swap, BrauerDiagram.permToBrauer_one_val_apply,
      BrauerDiagram.permToBrauer_one_val_apply]
    rcases x with i | i <;> rcases eq_or_ne i a with rfl | hia
    · simp
    · simp [Equiv.swap_apply_of_ne_of_ne, hia]
    · simp
    · simp [Equiv.swap_apply_of_ne_of_ne, hia]
  · symm
    refine (eq_capCup_iff hab).mpr ⟨?_, ?_, fun i hia hib => ?_⟩
    · simp [Equiv.swap_apply_of_ne_of_ne, hab]
    · simp [Equiv.swap_apply_of_ne_of_ne, hab.symm]
    · simp [Equiv.swap_apply_of_ne_of_ne, hia, hib]

namespace BrauerDiagram

/-- **Every Brauer diagram is a transport of the identity diagram** along a permutation of the
boundary points: sending the `k` bottom points to the lower ends of `D` and the `k` top points to
their partners matches each strand of `permToBrauer 1` with an arc of `D`. -/
theorem exists_congr_permToBrauer_one (D : BrauerDiagram k) :
    ∃ φ : Equiv.Perm (Fin k ⊕ Fin k), PerfectMatching.congr φ (permToBrauer 1) = D := by
  let e : Fin k ≃ {x // D.IsLowerEnd x} :=
    Fintype.equivOfCardEq ((Fintype.card_fin k).trans D.card_isLowerEnd.symm)
  let f : Fin k ⊕ Fin k → Fin k ⊕ Fin k :=
    Sum.elim (fun i => (e i).1) (fun i => D.val (e i).1)
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (e.injective (Subtype.ext hij))
    · have hval : (e i).1 = D.val (e j).1 := hij
      exact absurd (hval ▸ (e i).2) (D.not_isLowerEnd_val (e j).2)
    · have hval : (e j).1 = D.val (e i).1 := hij.symm
      exact absurd (hval ▸ (e j).2) (D.not_isLowerEnd_val (e i).2)
    · exact congrArg Sum.inr (e.injective (Subtype.ext (D.val.injective hij)))
  let φ : Equiv.Perm (Fin k ⊕ Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  refine ⟨φ, Subtype.ext (Equiv.ext fun y => ?_)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [PerfectMatching.congr_val_apply_apply, permToBrauer_one_val_apply]
  rcases x with i | i
  · rfl
  · exact (D.apply_apply (e i).1).symm

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
  obtain ⟨π, τ, hψ⟩ := Equiv.Perm.exists_sumCongr_mul_prodCongrLeft_of_commute_swap hcomm
  refine ⟨π, τ, ?_⟩
  rw [mul_assoc, ← hψ, mul_inv_cancel_left]

/-- **Transporting `permToBrauer 1` to `D` with one prescribed oriented arc.** Any arc `D.val x = y`
can be placed on some strand `i₀` with `x` as the image of `Sum.inl i₀` and `y` as the image of
`Sum.inr i₀`. -/
theorem exists_congr_permToBrauer_one_of_val_eq (D : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (h : D.val x = y) :
    ∃ (φ : Equiv.Perm (Fin k ⊕ Fin k)) (i₀ : Fin k),
      PerfectMatching.congr φ (permToBrauer 1) = D ∧
        φ (Sum.inl i₀) = x ∧ φ (Sum.inr i₀) = y := by
  obtain ⟨φ₀, hφ₀⟩ := D.exists_congr_permToBrauer_one
  have hpartner (z : Fin k ⊕ Fin k) : φ₀ z.swap = D.val (φ₀ z) := by
    rw [← hφ₀, PerfectMatching.congr_val_apply_apply, permToBrauer_one_val_apply]
  rcases hsymm : φ₀.symm x with i₀ | i₀
  · have hx : φ₀ (Sum.inl i₀) = x := by rw [← hsymm, Equiv.apply_symm_apply]
    exact ⟨φ₀, i₀, hφ₀, hx, (hpartner (Sum.inl i₀)).trans (hx ▸ h)⟩
  · have hx : φ₀ (Sum.inr i₀) = x := by rw [← hsymm, Equiv.apply_symm_apply]
    let φ : Equiv.Perm (Fin k ⊕ Fin k) := φ₀ * Equiv.swap (Sum.inr i₀) (Sum.inl i₀)
    have hφ : PerfectMatching.congr φ (permToBrauer 1) = D := by
      have htrans : (Equiv.swap (Sum.inr i₀) (Sum.inl i₀)).trans φ₀ = φ := rfl
      rw [← htrans, ← PerfectMatching.congr_trans, ← capCup_eq_congr, capCup_self, hφ₀]
    refine ⟨φ, i₀, hφ, ?_, ?_⟩
    · simp [φ, Equiv.Perm.mul_apply, hx]
    · simpa [φ, Equiv.Perm.mul_apply, hx, ← h] using hpartner (Sum.inr i₀)

/-- **Transporting `permToBrauer 1` to `D` with two prescribed disjoint oriented arcs.** -/
theorem exists_congr_permToBrauer_one_of_val_eq_of_val_eq (D : BrauerDiagram k)
    {x₁ y₁ x₂ y₂ : Fin k ⊕ Fin k} (h₁ : D.val x₁ = y₁) (h₂ : D.val x₂ = y₂)
    (hne : x₂ ≠ x₁) (hne' : x₂ ≠ y₁) :
    ∃ (φ : Equiv.Perm (Fin k ⊕ Fin k)) (i₁ i₂ : Fin k), i₁ ≠ i₂ ∧
      PerfectMatching.congr φ (permToBrauer 1) = D ∧
        φ (Sum.inl i₁) = x₁ ∧ φ (Sum.inr i₁) = y₁ ∧
          φ (Sum.inl i₂) = x₂ ∧ φ (Sum.inr i₂) = y₂ := by
  obtain ⟨φ₁, i₁, hφ₁, hx₁, hy₁⟩ := D.exists_congr_permToBrauer_one_of_val_eq h₁
  have hpartner (z : Fin k ⊕ Fin k) : φ₁ z.swap = D.val (φ₁ z) := by
    rw [← hφ₁, PerfectMatching.congr_val_apply_apply, permToBrauer_one_val_apply]
  rcases hsymm : φ₁.symm x₂ with i₂ | i₂
  · have hx₂ : φ₁ (Sum.inl i₂) = x₂ := by rw [← hsymm, Equiv.apply_symm_apply]
    have hi : i₁ ≠ i₂ := fun hi => hne (hx₂.symm.trans (hi ▸ hx₁))
    exact ⟨φ₁, i₁, i₂, hi, hφ₁, hx₁, hy₁, hx₂, (hpartner (Sum.inl i₂)).trans (hx₂ ▸ h₂)⟩
  · have hx₂ : φ₁ (Sum.inr i₂) = x₂ := by rw [← hsymm, Equiv.apply_symm_apply]
    have hi : i₁ ≠ i₂ := fun hi => hne' (hx₂.symm.trans (hi ▸ hy₁))
    let φ : Equiv.Perm (Fin k ⊕ Fin k) := φ₁ * Equiv.swap (Sum.inr i₂) (Sum.inl i₂)
    have hφ : PerfectMatching.congr φ (permToBrauer 1) = D := by
      have htrans : (Equiv.swap (Sum.inr i₂) (Sum.inl i₂)).trans φ₁ = φ := rfl
      rw [← htrans, ← PerfectMatching.congr_trans, ← capCup_eq_congr, capCup_self, hφ₁]
    refine ⟨φ, i₁, i₂, hi, hφ, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr
        (Sum.inl_injective.ne hi), hx₁]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hi)
        Sum.inr_ne_inl, hy₁]
    · simp [φ, Equiv.Perm.mul_apply, hx₂]
    · simpa [φ, Equiv.Perm.mul_apply, hx₂, ← h₂] using hpartner (Sum.inr i₂)

/-- Reconnecting two arcs commutes with reflecting a diagram upside down, after reflecting the two
chosen endpoints. -/
@[simp]
theorem flip_reconnect (D : BrauerDiagram k) (x y : Fin k ⊕ Fin k) :
    flip (D.reconnect x y) = D.flip.reconnect x.swap y.swap := by
  have hswap : (Equiv.swap (D.val x) y).trans (Equiv.sumComm (Fin k) (Fin k)) =
      (Equiv.sumComm (Fin k) (Fin k)).trans (Equiv.swap (D.flip.val x.swap) y.swap) := by
    rw [flip_val_swap]
    ext z
    rcases eq_or_ne z (D.val x) with rfl | hzx
    · simp
    rcases eq_or_ne z y with rfl | hzy
    · simp
    have hzx' : z.swap ≠ (D.val x).swap := fun h => hzx (by simpa using congrArg Sum.swap h)
    have hzy' : z.swap ≠ y.swap := fun h => hzy (by simpa using congrArg Sum.swap h)
    simp [Equiv.swap_apply_of_ne_of_ne hzx hzy, Equiv.swap_apply_of_ne_of_ne hzx' hzy']
  rw [flip_eq_congr, PerfectMatching.reconnect_eq_congr, PerfectMatching.congr_trans, hswap,
    ← PerfectMatching.congr_trans, ← flip_eq_congr, ← PerfectMatching.reconnect_eq_congr]

end BrauerDiagram

/-! ### Stacking a cap-cup generator onto an arbitrary diagram -/

/-- Bridging the two arcs of `D` that meet the top points `c` and `d` through the cap of
`capCup c d` joins their other endpoints `D.val (Sum.inr c)` and `D.val (Sum.inr d)`. -/
private theorem composeDiagram_capCup_val_val_inr {c d : Fin k} (hcd : c ≠ d) (D : BrauerDiagram k)
    (hncup : D.val (Sum.inr c) ≠ Sum.inr d) :
    (composeDiagram (capCup c d) D).val (D.val (Sum.inr c)) = D.val (Sum.inr d) := by
  have hpc : D.val (Sum.inr c) ≠ Sum.inr c := D.apply_ne (Sum.inr c)
  have hqd : D.val (Sum.inr d) ≠ Sum.inr d := D.apply_ne (Sum.inr d)
  have hqc : D.val (Sum.inr d) ≠ Sum.inr c := fun h => hncup (D.apply_eq_of_apply_eq h)
  rcases hp : D.val (Sum.inr c) with i | j <;> rcases hq : D.val (Sum.inr d) with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_upper _ _ (D.apply_eq_of_apply_eq hp)
      (capCup_val_inl_left hcd) hq
  · have hj'c : j' ≠ c := by simpa [hq] using hqc
    have hj'd : j' ≠ d := by simpa [hq] using hqd
    exact (composeDiagram_val_eq_iff _ _).mpr <| Or.inr
      ⟨Sum.inl c, Sum.inl j', by rw [stackStart_inl, D.apply_eq_of_apply_eq hp, Sum.elim_inr],
        (Relation.ReflTransGen.single
          (by rw [stackStep_inl, capCup_val_inl_left hcd, Sum.elim_inl])).tail
          (by rw [stackStep_inr, hq, Sum.elim_inr]),
        by rw [stackStep_inl, capCup_val_inl_of_ne hj'c hj'd, Sum.elim_inr]⟩
  · have hjc : j ≠ c := by simpa [hp] using hpc
    have hjd : j ≠ d := by simpa [hp] using hncup
    exact (composeDiagram_val_eq_iff _ _).mpr <| Or.inr
      ⟨Sum.inr j, Sum.inr d, by rw [stackStart_inr, capCup_val_inr_of_ne hjc hjd, Sum.elim_inl],
        (Relation.ReflTransGen.single
          (by rw [stackStep_inr, D.apply_eq_of_apply_eq hp, Sum.elim_inr])).tail
          (by rw [stackStep_inl, capCup_val_inl_left hcd, Sum.elim_inl]),
        by rw [stackStep_inr, hq, Sum.elim_inl]⟩
  · have hjc : j ≠ c := by simpa [hp] using hpc
    have hjd : j ≠ d := by simpa [hp] using hncup
    have hj'c : j' ≠ c := by simpa [hq] using hqc
    have hj'd : j' ≠ d := by simpa [hq] using hqd
    exact (composeDiagram_val_eq_iff _ _).mpr <| Or.inr
      ⟨Sum.inr j, Sum.inl j', by rw [stackStart_inr, capCup_val_inr_of_ne hjc hjd, Sum.elim_inl],
        ((Relation.ReflTransGen.single
          (by rw [stackStep_inr, D.apply_eq_of_apply_eq hp, Sum.elim_inr])).tail
          (by rw [stackStep_inl, capCup_val_inl_left hcd, Sum.elim_inl])).tail
          (by rw [stackStep_inr, hq, Sum.elim_inr]),
        by rw [stackStep_inl, capCup_val_inl_of_ne hj'c hj'd, Sum.elim_inr]⟩

/-- Off the arcs meeting the top points `a` and `b`, stacking `capCup a b` above `D` leaves the arc
of `D` at `x` unchanged. -/
private theorem composeDiagram_capCup_val_of_ne (D : BrauerDiagram k)
    {x : Fin k ⊕ Fin k} (hxa : x ≠ Sum.inr a) (hxb : x ≠ Sum.inr b)
    (hya : D.val x ≠ Sum.inr a) (hyb : D.val x ≠ Sum.inr b) :
    (composeDiagram (capCup a b) D).val x = D.val x := by
  rcases x with i | j <;> rcases hy : D.val _ with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ hy
  · exact composeDiagram_val_inl_eq_inr_of_through _ _ hy
      (capCup_val_inl_of_ne (by simpa [hy] using hya) (by simpa [hy] using hyb))
  · exact composeDiagram_val_inr_eq_inl_of_through _ _
      (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
  · exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
      (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
      (capCup_val_inl_of_ne (by simpa [hy] using hya) (by simpa [hy] using hyb))

/-- **Stacking a cap-cup generator on top reconnects the two top endpoints.** For `a ≠ b`, placing
`capCup a b` above any diagram `D` cuts the arcs of `D` at `Sum.inr a` and `Sum.inr b`, joins
`Sum.inr a` to `Sum.inr b` by the cup of `capCup a b`, and joins their other endpoints through the
cap of `capCup a b`. -/
theorem composeDiagram_capCup_left (hab : a ≠ b) (D : BrauerDiagram k) :
    composeDiagram (capCup a b) D = D.reconnect (Sum.inr a) (Sum.inr b) := by
  have hba : (Sum.inr b : Fin k ⊕ Fin k) ≠ Sum.inr a := Sum.inr_injective.ne hab.symm
  rcases eq_or_ne (D.val (Sum.inr a)) (Sum.inr b) with hcup | hncup
  · rw [← hcup, PerfectMatching.reconnect_partner]
    refine Subtype.ext (Equiv.ext fun x => ?_)
    by_cases hxa : x = Sum.inr a
    · subst x
      rw [hcup]
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab)
    by_cases hxb : x = Sum.inr b
    · subst x
      rw [D.apply_eq_of_apply_eq hcup]
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab)
    obtain ⟨hya, hyb⟩ := (D.apply_ne_and_ne_iff hcup x).mpr ⟨hxa, hxb⟩
    exact composeDiagram_capCup_val_of_ne D hxa hxb hya hyb
  · refine Subtype.ext (Equiv.ext fun x => ?_)
    by_cases hxa : x = Sum.inr a
    · subst x
      rw [PerfectMatching.reconnect_val_self hba]
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab)
    by_cases hxb : x = Sum.inr b
    · subst x
      rw [PerfectMatching.reconnect_val_right hba]
      exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab)
    by_cases hxp : x = D.val (Sum.inr a)
    · subst x
      rw [PerfectMatching.reconnect_val_val_self hba]
      exact composeDiagram_capCup_val_val_inr hab D hncup
    by_cases hxq : x = D.val (Sum.inr b)
    · subst x
      rw [PerfectMatching.reconnect_val_val_right hba, capCup_comm]
      exact composeDiagram_capCup_val_val_inr hab.symm D fun h => hncup (D.apply_eq_of_apply_eq h)
    have hya : D.val x ≠ Sum.inr a := fun h => hxp (D.apply_eq_of_apply_eq h).symm
    have hyb : D.val x ≠ Sum.inr b := fun h => hxq (D.apply_eq_of_apply_eq h).symm
    rw [PerfectMatching.reconnect_val_of_ne hxa hxb hxp hxq]
    exact composeDiagram_capCup_val_of_ne D hxa hxb hya hyb

/-- **Stacking a cap-cup generator underneath reconnects the two bottom endpoints**, the upside-down
mirror of `TauCeti.composeDiagram_capCup_left`. -/
theorem composeDiagram_capCup_right (hab : a ≠ b) (D : BrauerDiagram k) :
    composeDiagram D (capCup a b) = D.reconnect (Sum.inl a) (Sum.inl b) := by
  apply BrauerDiagram.flip_injective
  rw [flip_composeDiagram, BrauerDiagram.flip_capCup, composeDiagram_capCup_left hab,
    BrauerDiagram.flip_reconnect]
  rfl

/-- **Middle loops when stacking a cap-cup generator on top.** For `a ≠ b`, placing `capCup a b`
above `D` closes up one loop when `D` already cups `a` to `b`, and closes up no loop otherwise. -/
theorem middleLoopCount_capCup_left (hab : a ≠ b) (D : BrauerDiagram k) :
    middleLoopCount (capCup a b) D = if D.val (Sum.inr a) = Sum.inr b then 1 else 0 := by
  split_ifs with hcup
  · have hba : D.val (Sum.inr b) = Sum.inr a := D.apply_eq_of_apply_eq hcup
    have hon {x : Fin k} : OnMiddleLoop (capCup a b) D x ↔ x = a ∨ x = b := by
      refine ⟨fun hx => (BrauerDiagram.isCap_capCup_inl_iff hab).mp
        ((isMiddleVertex_def _ _ _).mp hx.isMiddleVertex).1, ?_⟩
      rintro (rfl | rfl)
      · exact onMiddleLoop_of_val_eq (capCup_val_inl_left hab) hcup
      · exact onMiddleLoop_of_val_eq (capCup_val_inl_right hab) hba
    have hab' : Relation.ReflTransGen (MiddleAdj (capCup a b) D) a b :=
      .single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_left hab)))
    have hba' : Relation.ReflTransGen (MiddleAdj (capCup a b) D) b a :=
      .single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_right hab)))
    have hset : {x : Fin k | IsMiddleLoopMin (capCup a b) D x} = {min a b} := by
      ext x
      rw [Set.mem_ofPred_eq, isMiddleLoopMin_def, hon, Set.mem_singleton_iff]
      rcases le_total a b with hle | hle
      · rw [min_eq_left hle]
        refine ⟨?_, ?_⟩
        · rintro ⟨rfl | rfl, hmin⟩
          · rfl
          · exact le_antisymm (hmin a hba') hle
        · rintro rfl
          refine ⟨Or.inl rfl, fun y hy => ?_⟩
          rcases hon.mp ((hon.mpr (Or.inl rfl)).reflTransGen hy) with rfl | rfl
          · exact le_rfl
          · exact hle
      · rw [min_eq_right hle]
        refine ⟨?_, ?_⟩
        · rintro ⟨rfl | rfl, hmin⟩
          · exact le_antisymm (hmin b hab') hle
          · rfl
        · rintro rfl
          refine ⟨Or.inr rfl, fun y hy => ?_⟩
          rcases hon.mp ((hon.mpr (Or.inr rfl)).reflTransGen hy) with rfl | rfl
          · exact hle
          · exact le_rfl
    rw [middleLoopCount_def, hset, Set.ncard_singleton]
  · refine middleLoopCount_eq_zero_iff.mpr fun x hx => ?_
    have hon {y : Fin k} (hy : OnMiddleLoop (capCup a b) D y) : y = a ∨ y = b :=
      (BrauerDiagram.isCap_capCup_inl_iff hab).mp
        ((isMiddleVertex_def _ _ _).mp hy.isMiddleVertex).1
    have ha : OnMiddleLoop (capCup a b) D a := by
      rcases hon hx with rfl | rfl
      · exact hx
      · exact hx.reflTransGen
          (.single ((middleAdj_def _ _ _ _).mpr (Or.inl (capCup_val_inl_right hab))))
    obtain ⟨c, hc⟩ : ∃ c, D.val (Sum.inr a) = Sum.inr c :=
      Sum.isRight_iff.mp ((BrauerDiagram.isCup_def D _).mp
        ((isMiddleVertex_def _ _ _).mp ha.isMiddleVertex).2).2
    have hc_on : OnMiddleLoop (capCup a b) D c :=
      ha.reflTransGen (.single ((middleAdj_def _ _ _ _).mpr (Or.inr hc)))
    rcases hon hc_on with hca | hcb
    · exact D.apply_ne (Sum.inr a) (hca ▸ hc)
    · exact hcup (hcb ▸ hc)

/-- **Middle loops when stacking a cap-cup generator underneath**, the upside-down mirror of
`TauCeti.middleLoopCount_capCup_left`. -/
theorem middleLoopCount_capCup_right (hab : a ≠ b) (D : BrauerDiagram k) :
    middleLoopCount D (capCup a b) = if D.val (Sum.inl a) = Sum.inl b then 1 else 0 := by
  have hcond : (D.flip.val (Sum.inr a) = Sum.inr b) ↔ (D.val (Sum.inl a) = Sum.inl b) := by
    rw [BrauerDiagram.flip_val_inr]
    exact ⟨fun h => by simpa using congrArg Sum.swap h, fun h => by simp [h]⟩
  rw [← middleLoopCount_flip, BrauerDiagram.flip_capCup, middleLoopCount_capCup_left hab]
  exact if_congr hcond rfl rfl

end TauCeti
