/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# The outer automorphism group of a group

For an arbitrary group `G`, the inner automorphisms `MulAut.conj g : x ↦ g * x * g⁻¹` form a normal
subgroup of the automorphism group `MulAut G`, because `φ * conj g * φ⁻¹ = conj (φ g)`. The
quotient is the **outer automorphism group** `TauCeti.OuterAut G = Aut(G) / Inn(G)`. No finiteness
or topology is assumed: the main examples are fundamental groups of closed surfaces, which are
infinite, and whose outer automorphism groups receive the mapping class groups in the
Dehn–Nielsen–Baer theorem.

An isomorphism `e : G ≃* H` transports automorphisms by `MulAut.congr e`, which carries the inner
automorphism by `g` to the inner automorphism by `e g`, and hence induces
`TauCeti.OuterAut.congr e : OuterAut G ≃* OuterAut H`. The case used for fundamental groups is the
inversion `(MulEquiv.inv' G).symm : Gᵐᵒᵖ ≃* G`, `op g ↦ g⁻¹`, which identifies the opposite group
(the fundamental group with first-traverse concatenation as its product) with `G`; on
automorphisms it is the identification `φ ↦ MulEquiv.op φ` (`MulAut.congr_inv'`), so the two natural
ways of comparing `OuterAut Gᵐᵒᵖ` with `OuterAut G` agree.

For commutative `G` every inner automorphism is trivial, and `OuterAut G` is `MulAut G`
(`TauCeti.OuterAut.mulEquivOfIsMulCommutative`).

## Main definitions

* `TauCeti.OuterAut G`: the quotient of `MulAut G` by the range of `MulAut.conj`.
* `TauCeti.OuterAut.mk`: the quotient map `MulAut G →* OuterAut G`; it is surjective
  (`QuotientGroup.mk'_surjective`) with kernel the inner automorphisms (`QuotientGroup.ker_mk'`).
* `TauCeti.OuterAut.congr`: the isomorphism of outer automorphism groups induced by an isomorphism
  of groups.
* `TauCeti.OuterAut.mulEquivOfIsMulCommutative`: for commutative `G`, `OuterAut G ≃* MulAut G`.

## Main results

* `MulAut.mul_conj_mul_inv`: `φ * conj g * φ⁻¹ = conj (φ g)`, so the inner automorphisms form a
  normal subgroup (`MulAut.normal_range_conj`).
* `MulAut.ker_conj`: the kernel of `MulAut.conj` is the centre, and the inner automorphisms are
  all trivial exactly when `G` is commutative (`MulAut.range_conj_eq_bot_iff`).
* `MulAut.congr_conj`: transport along an isomorphism `e` sends `conj g` to `conj (e g)`, and
  `MulAut.map_congr_range_conj` identifies the inner automorphism subgroups.
* `MulAut.congr_inv'`: transport along the inversion `G ≃* Gᵐᵒᵖ` is `MulEquiv.op`.
* `TauCeti.OuterAut.mk_eq_one_iff` and `TauCeti.OuterAut.mk_eq_mk_iff`: two automorphisms have the
  same outer class exactly when they differ by an inner automorphism.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Chapter 8 (the outer automorphism group of a surface group and the Dehn–Nielsen–Baer theorem).
-/

public section

open MulOpposite

namespace MulAut

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Conjugating the inner automorphism by `g` by an automorphism `φ` gives the inner automorphism
by `φ g`. -/
theorem mul_conj_mul_inv (φ : MulAut G) (g : G) : φ * conj g * φ⁻¹ = conj (φ g) := by
  ext x
  simp

/-- The inner automorphisms form a normal subgroup of the automorphism group. -/
instance normal_range_conj : (conj : G →* MulAut G).range.Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ φ
    exact ⟨φ g, (mul_conj_mul_inv φ g).symm⟩

/-- The kernel of the conjugation homomorphism `G →* MulAut G` is the centre of `G`. -/
theorem ker_conj : (conj : G →* MulAut G).ker = Subgroup.center G := by
  ext g
  simp only [MonoidHom.mem_ker, MulEquiv.ext_iff, conj_apply, one_apply,
    Subgroup.mem_center_iff, mul_inv_eq_iff_eq_mul]
  exact forall_congr' fun _ ↦ eq_comm

/-- Every inner automorphism is trivial exactly when `G` is commutative. -/
theorem range_conj_eq_bot_iff : (conj : G →* MulAut G).range = ⊥ ↔ IsMulCommutative G := by
  rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff, ker_conj,
    Subgroup.center_eq_top_iff]

/-- Transporting the inner automorphism by `g` along an isomorphism `e` gives the inner
automorphism by `e g`. -/
theorem congr_conj (e : G ≃* H) (g : G) : congr e (conj g) = conj (e g) := by
  ext x
  simp

/-- Transport along an isomorphism `e` carries the inner automorphisms of `G` onto those of
`H`. -/
theorem map_congr_range_conj (e : G ≃* H) :
    (conj : G →* MulAut G).range.map (congr e : MulAut G →* MulAut H) =
      (conj : H →* MulAut H).range := by
  rw [MonoidHom.map_range]
  ext ψ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨e g, (congr_conj e g).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨e.symm h, (congr_conj e _).trans (by rw [MulEquiv.apply_symm_apply])⟩

@[simp]
theorem congr_refl : congr (MulEquiv.refl G) = MulEquiv.refl (MulAut G) := by
  ext φ x
  simp

@[simp]
theorem congr_symm (e : G ≃* H) : (congr e).symm = congr e.symm :=
  (rfl)

@[simp]
theorem congr_trans (e : G ≃* H) (f : H ≃* K) : congr (e.trans f) = (congr e).trans (congr f) := by
  ext φ x
  simp

/-- Transport along the inversion `g ↦ op g⁻¹` from `G` to its opposite group is the
identification `φ ↦ MulEquiv.op φ` of automorphisms: an automorphism commutes with inversion. -/
theorem congr_inv' (φ : MulAut G) : congr (MulEquiv.inv' G) φ = MulEquiv.op φ := by
  ext x
  simp

end MulAut

namespace TauCeti

/-- The **outer automorphism group** `Out(G) = Aut(G) / Inn(G)` of a group `G`: the automorphisms
of `G` modulo the inner automorphisms, the range of `MulAut.conj`. -/
abbrev OuterAut (G : Type*) [Group G] : Type _ :=
  MulAut G ⧸ (MulAut.conj : G →* MulAut G).range

namespace OuterAut

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- The quotient map from automorphisms to outer automorphisms. -/
abbrev mk : MulAut G →* OuterAut G :=
  QuotientGroup.mk' _

/-- Inner automorphisms have trivial outer class. -/
@[simp]
theorem mk_conj (g : G) : ((MulAut.conj g : MulAut G) : OuterAut G) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

/-- The outer class of an automorphism is trivial exactly when the automorphism is inner. -/
theorem mk_eq_one_iff {φ : MulAut G} : (φ : OuterAut G) = 1 ↔ ∃ g : G, MulAut.conj g = φ :=
  QuotientGroup.eq_one_iff φ

/-- Two automorphisms have the same outer class exactly when they differ by an inner
automorphism. -/
theorem mk_eq_mk_iff {φ ψ : MulAut G} :
    (φ : OuterAut G) = ψ ↔ ∃ g : G, ψ = φ * MulAut.conj g := by
  rw [QuotientGroup.eq]
  exact exists_congr fun g ↦ by rw [eq_comm, inv_mul_eq_iff_eq_mul]

/-- An isomorphism of groups induces an isomorphism of their outer automorphism groups, by
transporting automorphisms along it. -/
def congr (e : G ≃* H) : OuterAut G ≃* OuterAut H :=
  QuotientGroup.congr _ _ (MulAut.congr e) (MulAut.map_congr_range_conj e)

@[simp]
theorem congr_mk (e : G ≃* H) (φ : MulAut G) :
    congr e (φ : OuterAut G) = (MulAut.congr e φ : OuterAut H) :=
  (rfl)

@[simp]
theorem congr_refl : congr (MulEquiv.refl G) = MulEquiv.refl (OuterAut G) := by
  ext φ
  obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective φ
  simp

@[simp]
theorem congr_symm (e : G ≃* H) : (congr e).symm = congr e.symm := by
  ext φ
  obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective φ
  rw [MulEquiv.symm_apply_eq, congr_mk, congr_mk, ← MulAut.congr_symm, MulEquiv.apply_symm_apply]

@[simp]
theorem congr_trans (e : G ≃* H) (f : H ≃* K) : congr (e.trans f) = (congr e).trans (congr f) := by
  ext φ
  obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective φ
  simp

/-- Inversion `Gᵐᵒᵖ ≃* G`, `op g ↦ g⁻¹`, identifies the outer automorphism group of the opposite
group with that of `G`; it sends the class of `MulEquiv.op φ` to the class of `φ`. -/
theorem congr_symm_inv'_mk_op (φ : MulAut G) :
    congr (MulEquiv.inv' G).symm (MulEquiv.op φ : OuterAut Gᵐᵒᵖ) = (φ : OuterAut G) := by
  rw [congr_mk, ← MulAut.congr_inv', ← MulAut.congr_symm, MulEquiv.symm_apply_apply]

/-- For commutative `G` every inner automorphism is trivial, so the outer automorphism group is
the automorphism group. -/
def mulEquivOfIsMulCommutative [IsMulCommutative G] : OuterAut G ≃* MulAut G :=
  (QuotientGroup.quotientMulEquivOfEq
    (MulAut.range_conj_eq_bot_iff.mpr inferInstance)).trans QuotientGroup.quotientBot

@[simp]
theorem mulEquivOfIsMulCommutative_mk [IsMulCommutative G] (φ : MulAut G) :
    mulEquivOfIsMulCommutative (φ : OuterAut G) = φ := by
  rw [mulEquivOfIsMulCommutative, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    ← MulEquiv.eq_symm_apply, QuotientGroup.quotientBot_symm_apply]

@[simp]
theorem mulEquivOfIsMulCommutative_symm_apply [IsMulCommutative G] (φ : MulAut G) :
    mulEquivOfIsMulCommutative.symm φ = (φ : OuterAut G) := by
  rw [MulEquiv.symm_apply_eq, mulEquivOfIsMulCommutative_mk]

end OuterAut

end TauCeti
