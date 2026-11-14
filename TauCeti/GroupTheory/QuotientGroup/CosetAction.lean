/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.Algebra.Group.Subgroup.Conjugates
public import TauCeti.Algebra.GroupAction.PermutationRepresentation
public import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Permutation representations of left-coset actions

A group `G` acts on the left cosets `G ⧸ H` of a subgroup `H` by left translation, and an
enumeration `e : G ⧸ H ≃ β` turns that action into a permutation representation
`e.permutationRepresentation : G →* Equiv.Perm β`. This file classifies those representations up to
conjugacy in `Equiv.Perm β` and identifies their centralizer — the deck-transformation group of the
coset action — with the normalizer quotient `N_G(H) ⧸ H`.

* **Conjugation of subgroups and coset spaces.** Right translation by `g⁻¹` gives a `G`-equivariant
  bijection `H.quotientConjEquiv g : G ⧸ H ≃ G ⧸ (MulAut.conj g • H)`. Consequently, two coset
  actions `e₁ : G ⧸ H₁ ≃ β` and `e₂ : G ⧸ H₂ ≃ β` yield conjugate permutation representations in
  `Equiv.Perm β` if and only if `H₁` and `H₂` are conjugate in `G`
  (`Equiv.exists_conj_permutationRepresentation_quotient_iff`), and are conjugate by a permutation
  carrying the base coset `e₁ 1` to `e₂ 1` if and only if `H₁ = H₂`
  (`Equiv.exists_conj_permutationRepresentation_quotient_eq_and_apply_one_iff`).
* **Transport along homomorphisms.** The coset-space equivalences
  `TauCeti.QuotientGroup.congrComapOfSurjectiveMk` and `TauCeti.QuotientGroup.congrOfMapEq` are
  equivariant for left translation, so precomposing an enumeration with them precomposes the
  permutation representation with the group homomorphism.
* **Centralizer and normalizer quotient.** For `n ∈ N_G(H)`, right multiplication by `n⁻¹` on cosets
  commutes with left translation, inducing an isomorphism
  `Subgroup.normalizerQuotientEquivCentralizer : N_G(H) ⧸ H ≃* centralizer (range ρ)` for any
  enumeration `e : G ⧸ H ≃ β` with `ρ = e.permutationRepresentation`. Taking cardinalities recovers
  `Nat.card (centralizer (range ρ)) = H.relIndex N_G(H)` and the orbit-automorphism product formula
  `Nat.card (orbit (ConjAct G) H) * Nat.card (centralizer (range ρ)) = H.index`.
* **Fixed-index subgroups.** Conjugation preserves subgroup index, giving a `ConjAct G` action on
  `{H : Subgroup G // H.index = n}` whose orbits agree with conjugacy orbits in `Subgroup G`
  (`Subgroup.orbitConjActSubtypeIndexEquiv`), and group isomorphisms transport both fixed-index
  subgroups and their conjugacy classes (`MulEquiv.fixedIndexSubgroupEquiv`,
  `MulEquiv.fixedIndexConjClassesEquiv`).
-/

public section

open MulAction Equiv
open scoped Pointwise

section CosetEnumeration

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G) {n : ℕ}

/-- An enumeration `G ⧸ H ≃ Fin n` witnesses that `H` has index `n`. -/
theorem index_eq_of_equiv_fin (e : G ⧸ H ≃ Fin n) : H.index = n :=
  H.index_eq_card.trans ((Nat.card_congr e).trans (Nat.card_fin n))

/-- The degree of a coset enumeration `G ⧸ H ≃ Fin n` is nonzero, as `G ⧸ H` contains `1`. -/
theorem ne_zero_of_equiv_fin (e : G ⧸ H ≃ Fin n) : n ≠ 0 :=
  (e (1 : G)).pos.ne'

/-- A subgroup whose coset space admits an enumeration `G ⧸ H ≃ Fin n` has finite index. -/
theorem finiteIndex_of_equiv_fin (e : G ⧸ H ≃ Fin n) : H.FiniteIndex :=
  ⟨by rw [H.index_eq_of_equiv_fin e]; exact H.ne_zero_of_equiv_fin e⟩

/-- An enumeration of the left cosets of a subgroup of finite index `n ≠ 0`. -/
noncomputable def quotientEquivFin [NeZero n] (hH : H.index = n) : G ⧸ H ≃ Fin n :=
  have hcard : Nat.card (G ⧸ H) = n := H.index_eq_card.symm.trans hH
  have : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero (hcard ▸ NeZero.ne n)
  Finite.equivFinOfCardEq hcard

end Subgroup

end CosetEnumeration

section Transport

variable {G G' β : Type*} [Group G] [Group G']

namespace TauCeti.QuotientGroup

/-- `TauCeti.QuotientGroup.congrComapOfSurjectiveMk` intertwines left translation by `g` with left
translation by `ψ g`. -/
@[simp]
theorem congrComapOfSurjectiveMk_smul (ψ : G →* G') (B : Subgroup G')
    (hψ : Function.Surjective fun g : G ↦ (ψ g : G' ⧸ B)) (g : G) (q : G ⧸ B.comap ψ) :
    congrComapOfSurjectiveMk ψ B hψ (g • q) = ψ g • congrComapOfSurjectiveMk ψ B hψ q := by
  induction q using _root_.QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, congrComapOfSurjectiveMk_mk,
      congrComapOfSurjectiveMk_mk, map_mul, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- `TauCeti.QuotientGroup.congrOfMapEq` intertwines left translation by `g` with left translation
by `f g`. -/
@[simp]
theorem congrOfMapEq_smul (f : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : A.map (f : G →* G') = B) (g : G) (q : G ⧸ A) :
    congrOfMapEq f h (g • q) = f g • congrOfMapEq f h q := by
  induction q using _root_.QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, congrOfMapEq_mk, congrOfMapEq_mk, map_mul,
      MulAction.Quotient.smul_mk, smul_eq_mul]

end TauCeti.QuotientGroup

namespace Equiv

/-- Pulling back a coset enumeration along `ψ : G →* G'` precomposes its permutation representation
with `ψ`. -/
@[simp]
theorem permutationRepresentation_congrComapOfSurjectiveMk_trans (ψ : G →* G') (B : Subgroup G')
    (hψ : Function.Surjective fun g : G ↦ (ψ g : G' ⧸ B)) (e : G' ⧸ B ≃ β) :
    ((TauCeti.QuotientGroup.congrComapOfSurjectiveMk ψ B hψ).trans e).permutationRepresentation =
      (e.permutationRepresentation (G := G')).comp ψ :=
  permutationRepresentation_eq_of_map_smul _ fun g q ↦ by
    simp [MonoidHom.comp_apply]

/-- Pulling back a coset enumeration along a group isomorphism `f : G ≃* G'` precomposes its
permutation representation with `f`. -/
@[simp]
theorem permutationRepresentation_congrOfMapEq_trans (f : G ≃* G') {A : Subgroup G}
    {B : Subgroup G'} (h : A.map (f : G →* G') = B) (e : G' ⧸ B ≃ β) :
    ((TauCeti.QuotientGroup.congrOfMapEq f h).trans e).permutationRepresentation =
      (e.permutationRepresentation (G := G')).comp (f : G →* G') :=
  permutationRepresentation_eq_of_map_smul _ fun g q ↦ by
    simp [MonoidHom.comp_apply]

end Equiv

namespace Subgroup

/-- Inversion viewed as an isomorphism `G ≃* Gᵐᵒᵖ` maps a subgroup `H` onto `H.op`. -/
theorem map_inv'_eq_op (H : Subgroup G) :
    H.map (MulEquiv.inv' G : G →* Gᵐᵒᵖ) = H.op := by
  ext x
  obtain ⟨x, rfl⟩ := MulOpposite.op_surjective x
  simp [-MulOpposite.op_inv, inv_eq_iff_eq_inv]

/-- The bijection `gH ↦ Hg⁻¹` between left cosets `G ⧸ H` and right cosets `Gᵐᵒᵖ ⧸ H.op`,
obtained by transporting `H` along `MulEquiv.inv' G : G ≃* Gᵐᵒᵖ`. -/
def quotientEquivOp (H : Subgroup G) : G ⧸ H ≃ Gᵐᵒᵖ ⧸ H.op :=
  TauCeti.QuotientGroup.congrOfMapEq (MulEquiv.inv' G) H.map_inv'_eq_op

@[simp]
theorem quotientEquivOp_mk (H : Subgroup G) (g : G) :
    H.quotientEquivOp (g : G ⧸ H) = (MulOpposite.op g⁻¹ : Gᵐᵒᵖ ⧸ H.op) :=
  TauCeti.QuotientGroup.congrOfMapEq_mk (MulEquiv.inv' G) H.map_inv'_eq_op g

end Subgroup

namespace Equiv

/-- Under the left-to-right coset bijection `H.quotientEquivOp : G ⧸ H ≃ Gᵐᵒᵖ ⧸ H.op`
(`gH ↦ Hg⁻¹`), the left action of `g` on `G ⧸ H` is the inverse of the right action of `g` on
`Gᵐᵒᵖ ⧸ H.op`. -/
@[simp]
theorem permutationRepresentation_quotientEquivOp_trans_apply (H : Subgroup G)
    (e : Gᵐᵒᵖ ⧸ H.op ≃ β) (g : G) :
    (H.quotientEquivOp.trans e).permutationRepresentation g =
      (e.permutationRepresentation (MulOpposite.op g))⁻¹ := by
  rw [Subgroup.quotientEquivOp, permutationRepresentation_congrOfMapEq_trans]
  simp [MulOpposite.op_inv]

end Equiv

end Transport

section Conjugacy

namespace Subgroup

variable {G β : Type*} [Group G]

/-- **Right translation identifies the coset spaces of conjugate subgroups `G`-equivariantly.**
Sending `xH` to `(xg⁻¹)(gHg⁻¹)` preserves left translation by `G`, unlike left conjugation on
representatives which twists the `G`-action by `MulAut.conj g`. -/
def quotientConjEquiv (H : Subgroup G) (g : G) : G ⧸ H ≃ G ⧸ (MulAut.conj g • H) :=
  Quotient.congr (Equiv.mulRight g⁻¹) fun x y ↦ by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Equiv.coe_mulRight,
      TauCeti.mem_conj_smul]
    -- `g⁻¹ * ((x * g⁻¹)⁻¹ * (y * g⁻¹)) * g` simplifies to `x⁻¹ * y`.
    have hmul : g⁻¹ * ((x * g⁻¹)⁻¹ * (y * g⁻¹)) * g = x⁻¹ * y := by group
    rw [hmul]

@[simp]
theorem quotientConjEquiv_mk (H : Subgroup G) (g x : G) :
    H.quotientConjEquiv g (x : G ⧸ H) = ((x * g⁻¹ : G) : G ⧸ (MulAut.conj g • H)) :=
  (rfl)

@[simp]
theorem quotientConjEquiv_symm_mk (H : Subgroup G) (g y : G) :
    (H.quotientConjEquiv g).symm (y : G ⧸ (MulAut.conj g • H)) = ((y * g : G) : G ⧸ H) :=
  (H.quotientConjEquiv g).symm_apply_eq.mpr (by simp [mul_assoc])

/-- Right translation between coset spaces of conjugate subgroups commutes with left translation
by `G`. -/
@[simp]
theorem quotientConjEquiv_smul (H : Subgroup G) (g a : G) (q : G ⧸ H) :
    H.quotientConjEquiv g (a • q) = a • H.quotientConjEquiv g q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Quotient.smul_coe, smul_eq_mul, quotientConjEquiv_mk, quotientConjEquiv_mk,
      Quotient.smul_coe, smul_eq_mul, mul_assoc]

end Subgroup

namespace Equiv

variable {G β : Type*} [Group G]

/-- Precomposing an enumeration of `G ⧸ (MulAut.conj g • H)` with `H.quotientConjEquiv g` leaves
the permutation representation unchanged, since `H.quotientConjEquiv g` is `G`-equivariant. -/
@[simp]
theorem permutationRepresentation_quotientConjEquiv_trans (H : Subgroup G) (g : G)
    (e : G ⧸ (MulAut.conj g • H) ≃ β) :
    ((H.quotientConjEquiv g).trans e).permutationRepresentation (G := G) =
      e.permutationRepresentation :=
  permutationRepresentation_eq_of_map_smul _ fun a q ↦ by simp

/-- **Pointed classification of coset permutation representations.** Two coset enumerations
`e₁ : G ⧸ H₁ ≃ β` and `e₂ : G ⧸ H₂ ≃ β` have permutation representations conjugate by a
permutation carrying the base coset `e₁ 1` to `e₂ 1` if and only if `H₁ = H₂`. -/
theorem exists_conj_permutationRepresentation_quotient_eq_and_apply_one_iff
    {H₁ H₂ : Subgroup G} (e₁ : G ⧸ H₁ ≃ β) (e₂ : G ⧸ H₂ ≃ β) :
    (∃ τ : Perm β,
      (MulAut.conj τ).toMonoidHom.comp (e₁.permutationRepresentation (G := G)) =
        e₂.permutationRepresentation ∧
      τ (e₁ (1 : G)) = e₂ (1 : G)) ↔ H₁ = H₂ := by
  constructor
  · rintro ⟨τ, hρ, hτ⟩
    calc H₁ = MulAction.stabilizer G ((1 : G) : G ⧸ H₁) :=
          (MulAction.stabilizer_quotient H₁).symm
      _ = (MulAction.stabilizer (Perm β) (e₁ (1 : G))).comap e₁.permutationRepresentation :=
          (e₁.comap_stabilizer_permutationRepresentation ((1 : G) : G ⧸ H₁)).symm
      _ = (MulAction.stabilizer (Perm β) (τ • e₁ (1 : G))).comap
            ((MulAut.conj τ).toMonoidHom.comp e₁.permutationRepresentation) := by
          rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← Subgroup.comap_comap,
            Subgroup.comap_map_eq_self_of_injective (MulAut.conj τ).injective]
      _ = (MulAction.stabilizer (Perm β) (e₂ (1 : G))).comap e₂.permutationRepresentation := by
          rw [hρ, Perm.smul_def, hτ]
      _ = MulAction.stabilizer G ((1 : G) : G ⧸ H₂) :=
          e₂.comap_stabilizer_permutationRepresentation ((1 : G) : G ⧸ H₂)
      _ = H₂ := MulAction.stabilizer_quotient H₂
  · rintro rfl
    refine ⟨e₁.symm.trans e₂, MonoidHom.ext fun g ↦ ?_, by simp⟩
    simpa [MulAut.conj_apply] using (e₁.permutationRepresentation_eq_conj e₂ g).symm

/-- **Conjugacy classification of coset permutation representations.** Two coset enumerations
`e₁ : G ⧸ H₁ ≃ β` and `e₂ : G ⧸ H₂ ≃ β` have conjugate permutation representations in
`Equiv.Perm β` if and only if `H₁` and `H₂` are conjugate subgroups of `G`. -/
theorem exists_conj_permutationRepresentation_quotient_iff
    {H₁ H₂ : Subgroup G} (e₁ : G ⧸ H₁ ≃ β) (e₂ : G ⧸ H₂ ≃ β) :
    (∃ τ : Perm β,
      (MulAut.conj τ).toMonoidHom.comp (e₁.permutationRepresentation (G := G)) =
        e₂.permutationRepresentation) ↔
      ∃ c : ConjAct G, c • H₁ = H₂ := by
  constructor
  · rintro ⟨τ, hρ⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e₂.symm (τ (e₁ (1 : G))))
    have hτ : τ (e₁ (1 : G)) = e₂ (g : G ⧸ H₂) := by
      simpa using (congrArg e₂ hg).symm
    let e₂' : G ⧸ (MulAut.conj g • H₂) ≃ β :=
      (Subgroup.quotientConjEquiv H₂ g).symm.trans e₂
    have he₂' : e₂'.permutationRepresentation (G := G) = e₂.permutationRepresentation := by
      have hsymm : e₂ = (Subgroup.quotientConjEquiv H₂ g).trans e₂' := by
        ext q
        simp [e₂']
      rw [hsymm, permutationRepresentation_quotientConjEquiv_trans]
    have hbase : e₂' (1 : G) = e₂ (g : G ⧸ H₂) := by
      simp [e₂']
    have heq : H₁ = MulAut.conj g • H₂ :=
      (exists_conj_permutationRepresentation_quotient_eq_and_apply_one_iff e₁ e₂').mp
        ⟨τ, he₂' ▸ hρ, hbase ▸ hτ⟩
    refine ⟨ConjAct.toConjAct g⁻¹, ?_⟩
    rw [heq]
    ext x
    simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, mul_assoc]
  · rintro ⟨c, rfl⟩
    let g := ConjAct.ofConjAct c
    let e₁' : G ⧸ H₁ ≃ β := (H₁.quotientConjEquiv g).trans e₂
    have he₁' : e₁'.permutationRepresentation (G := G) = e₂.permutationRepresentation :=
      permutationRepresentation_quotientConjEquiv_trans H₁ g e₂
    refine ⟨e₁.symm.trans e₁', MonoidHom.ext fun a ↦ ?_⟩
    simpa [he₁', MulAut.conj_apply] using (e₁.permutationRepresentation_eq_conj e₁' a).symm

end Equiv

end Conjugacy

section Centralizer

namespace Subgroup

variable {G β : Type*} [Group G] (H : Subgroup G)

/-- Right multiplication on `G ⧸ H` by `n⁻¹` for `n ∈ N_G(H)`, as a permutation of `G ⧸ H`. -/
def normalizerCosetPerm (n : normalizer (H : Set G)) : Perm (G ⧸ H) :=
  (H.quotientConjEquiv (n : G)).trans
    (quotientEquivOfEq (mem_normalizer_iff_map_conj_eq.mp n.2))

@[simp]
theorem normalizerCosetPerm_mk (n : normalizer (H : Set G)) (x : G) :
    H.normalizerCosetPerm n (x : G ⧸ H) = ((x * (n : G)⁻¹ : G) : G ⧸ H) :=
  (rfl)

@[simp]
theorem normalizerCosetPerm_smul (n : normalizer (H : Set G)) (a : G) (q : G ⧸ H) :
    H.normalizerCosetPerm n (a • q) = a • H.normalizerCosetPerm n q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [Quotient.smul_coe, smul_eq_mul, normalizerCosetPerm_mk, normalizerCosetPerm_mk,
      Quotient.smul_coe, smul_eq_mul, mul_assoc]

/-- The homomorphism `N_G(H) →* centralizer (range (toPermHom G (G ⧸ H)))` sending `n` to right
multiplication by `n⁻¹` on left cosets. -/
def normalizerToCosetCentralizer :
    normalizer (H : Set G) →*
      centralizer ((MulAction.toPermHom G (G ⧸ H)).range : Set (Perm (G ⧸ H))) where
  toFun n :=
    ⟨H.normalizerCosetPerm n, mem_centralizer_iff.mpr fun y hy ↦ by
      obtain ⟨a, rfl⟩ := hy
      exact Perm.ext fun q ↦ (H.normalizerCosetPerm_smul n a q).symm⟩
  map_one' := Subtype.ext <| Perm.ext fun q ↦ by
    induction q using QuotientGroup.induction_on with
    | H x => simp
  map_mul' n₁ n₂ := Subtype.ext <| by
    rw [coe_mul]
    refine Perm.ext fun q ↦ ?_
    induction q using QuotientGroup.induction_on with
    | H x => simp [Perm.mul_apply, mul_assoc]

theorem coe_normalizerToCosetCentralizer_apply (n : normalizer (H : Set G)) :
    (H.normalizerToCosetCentralizer n : Perm (G ⧸ H)) = H.normalizerCosetPerm n :=
  (rfl)

/-- The kernel of `H.normalizerToCosetCentralizer` is `H` viewed inside `N_G(H)`. -/
@[simp]
theorem ker_normalizerToCosetCentralizer :
    H.normalizerToCosetCentralizer.ker = H.subgroupOf (normalizer (H : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, Subtype.ext_iff, OneMemClass.coe_one, Perm.ext_iff, mem_subgroupOf]
  constructor
  · intro hn
    have h1 := hn (1 : G)
    rw [coe_normalizerToCosetCentralizer_apply, normalizerCosetPerm_mk, one_mul, Perm.one_apply,
      QuotientGroup.eq] at h1
    simpa using h1
  · intro hn q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [coe_normalizerToCosetCentralizer_apply, normalizerCosetPerm_mk, Perm.one_apply,
        QuotientGroup.eq]
      simpa [mul_assoc] using H.inv_mem hn

/-- Every permutation of `G ⧸ H` commuting with left translation is right multiplication by `n⁻¹`
for some `n ∈ N_G(H)`. -/
theorem normalizerToCosetCentralizer_surjective :
    Function.Surjective H.normalizerToCosetCentralizer := by
  rintro ⟨σ, hσ⟩
  have hcomm : ∀ (a : G) (q : G ⧸ H), a • σ q = σ (a • q) := fun a q ↦ by
    have h := mem_centralizer_iff.mp hσ (MulAction.toPermHom G (G ⧸ H) a) ⟨a, rfl⟩
    exact congr($h q)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (σ (1 : G))
  -- Since `σ` commutes with `G`, `gH = σ(1H)` has the same stabilizer `H` as `1H`, so `g ∈ N_G(H)`.
  have hstab : MulAction.stabilizer G (g : G ⧸ H) = MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
    ext a
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, hg, hcomm, σ.injective.eq_iff]
  rw [TauCeti.stabilizer_quotientGroup_mk, MulAction.stabilizer_quotient] at hstab
  have hgN : g ∈ normalizer (H : Set G) := mem_normalizer_iff_map_conj_eq.mpr hstab
  refine ⟨⟨g⁻¹, inv_mem hgN⟩, Subtype.ext <| Perm.ext fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : (x : G ⧸ H) = x • ((1 : G) : G ⧸ H) := by rw [Quotient.smul_coe, smul_eq_mul, mul_one]
    simp only [coe_normalizerToCosetCentralizer_apply, normalizerCosetPerm_mk, inv_inv]
    rw [hx, ← hcomm, ← hg, Quotient.smul_coe, smul_eq_mul]

/-- **The deck-transformation group of a coset action.** For any subgroup `H ≤ G` and enumeration
`e : G ⧸ H ≃ β`, the centralizer in `Equiv.Perm β` of the image of `e.permutationRepresentation` is
canonically isomorphic to `N_G(H) ⧸ H`. -/
noncomputable def normalizerQuotientEquivCentralizer (e : G ⧸ H ≃ β) :
    normalizer (H : Set G) ⧸ H.subgroupOf (normalizer (H : Set G)) ≃*
      centralizer ((e.permutationRepresentation (G := G)).range : Set (Perm β)) := by
  have hrep : e.permutationRepresentation (G := G) =
      e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H)) := by
    ext a i
    simp
  have hrange :
      ((MulAction.toPermHom G (G ⧸ H)).range).map e.permCongrHom.toMonoidHom =
        (e.permutationRepresentation (G := G)).range := by
    rw [hrep, MonoidHom.range_comp]
  have hcent :
      (centralizer ((MulAction.toPermHom G (G ⧸ H)).range : Set (Perm (G ⧸ H)))).map
          (e.permCongrHom : Perm (G ⧸ H) →* Perm β) =
        centralizer ((e.permutationRepresentation (G := G)).range : Set (Perm β)) := by
    ext τ
    rw [← MulEquiv.toMonoidHom_eq_coe, mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro h y hy
      rw [← hrange] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hτ := congrArg e.permCongrHom (h x hx)
      simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply] using hτ
    · intro h x hx
      have hy : e.permCongrHom x ∈ (e.permutationRepresentation (G := G)).range := by
        rw [← hrange]
        exact ⟨x, hx, rfl⟩
      have hτ := congrArg e.permCongrHom.symm (h (e.permCongrHom x) hy)
      simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.symm_apply_apply] using hτ
  exact (QuotientGroup.quotientMulEquivOfEq H.ker_normalizerToCosetCentralizer.symm).trans <|
    (QuotientGroup.quotientKerEquivOfSurjective H.normalizerToCosetCentralizer
      H.normalizerToCosetCentralizer_surjective).trans <|
      TauCeti.Subgroup.congrOfMapEq e.permCongrHom hcent

/-- The permutation corresponding to the class of `n ∈ N_G(H)` sends `e (xH)` to `e ((xn⁻¹)H)`. -/
theorem coe_normalizerQuotientEquivCentralizer_mk_apply (e : G ⧸ H ≃ β)
    (n : normalizer (H : Set G)) (x : G) :
    (H.normalizerQuotientEquivCentralizer e (n : _ ⧸ _) : Perm β) (e (x : G ⧸ H)) =
      e ((x * (n : G)⁻¹ : G) : G ⧸ H) := by
  rw [normalizerQuotientEquivCentralizer, MulEquiv.trans_apply, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk,
    TauCeti.Subgroup.coe_congrOfMapEq_apply]
  simp only [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

/-- The centralizer of a coset permutation representation has order `[N_G(H) : H]`. -/
theorem card_centralizer_permutationRepresentation (e : G ⧸ H ≃ β) :
    Nat.card (centralizer ((e.permutationRepresentation (G := G)).range : Set (Perm β))) =
      H.relIndex (normalizer (H : Set G)) := by
  rw [← Nat.card_congr (H.normalizerQuotientEquivCentralizer e).toEquiv, relIndex, index_eq_card]

/-- **The orbit-automorphism product formula for a subgroup.** Multiplying the number of conjugates
of `H` in `G` by the order of the centralizer of its coset permutation representation gives the
index `[G : H]`. -/
theorem card_orbit_conjAct_mul_card_centralizer_permutationRepresentation (e : G ⧸ H ≃ β) :
    Nat.card (MulAction.orbit (ConjAct G) H) *
        Nat.card (centralizer ((e.permutationRepresentation (G := G)).range : Set (Perm β))) =
      H.index := by
  rw [H.card_centralizer_permutationRepresentation e, Nat.card_coe_set_eq]
  exact H.ncard_orbit_mul_relIndex_normalizer

/-- When the coset space is finite, the number of conjugates of `H` in `G` is `[G : H]` divided by
the order of the centralizer of its coset permutation representation. -/
theorem card_orbit_conjAct_eq_index_div_card_centralizer [Finite β] (e : G ⧸ H ≃ β) :
    Nat.card (MulAction.orbit (ConjAct G) H) =
      H.index /
        Nat.card (centralizer ((e.permutationRepresentation (G := G)).range : Set (Perm β))) := by
  rw [← H.card_orbit_conjAct_mul_card_centralizer_permutationRepresentation e,
    Nat.mul_div_cancel _ Nat.card_pos]

end Subgroup

end Centralizer

section FixedIndex

namespace Subgroup

variable {G : Type*} [Group G] {n : ℕ}

/-- Conjugating a subgroup preserves its index. -/
@[simp]
theorem index_conjAct_smul (c : ConjAct G) (H : Subgroup G) : (c • H).index = H.index :=
  H.index_map_equiv (MulAut.conj (ConjAct.ofConjAct c))

/-- Conjugation acts on the subgroups of `G` of fixed index `n`. -/
instance instMulActionConjActSubtypeIndexEq :
    MulAction (ConjAct G) {H : Subgroup G // H.index = n} where
  smul c H := ⟨c • H.1, (H.1.index_conjAct_smul c).trans H.2⟩
  one_smul H := Subtype.ext (one_smul _ H.1)
  mul_smul c₁ c₂ H := Subtype.ext (mul_smul c₁ c₂ H.1)

@[simp]
theorem coe_conjAct_smul_subtypeIndex (c : ConjAct G) (H : {H : Subgroup G // H.index = n}) :
    ((c • H : {H : Subgroup G // H.index = n}) : Subgroup G) = c • (H : Subgroup G) :=
  (rfl)

/-- The conjugacy orbit of `H` inside `{H : Subgroup G // H.index = n}` is in bijection with its
conjugacy orbit in `Subgroup G`, since conjugation preserves index. -/
def orbitConjActSubtypeIndexEquiv (H : {H : Subgroup G // H.index = n}) :
    MulAction.orbit (ConjAct G) H ≃ MulAction.orbit (ConjAct G) H.1 where
  toFun K := ⟨K.1.1, by
    obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp K.2
    exact MulAction.mem_orbit_iff.mpr ⟨c, congrArg Subtype.val hc⟩⟩
  invFun K := ⟨⟨K.1, by
    obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp K.2
    exact hc ▸ (H.1.index_conjAct_smul c).trans H.2⟩, by
    obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp K.2
    exact MulAction.mem_orbit_iff.mpr ⟨c, Subtype.ext hc⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Subgroup

namespace MulEquiv

variable {G G' : Type*} [Group G] [Group G']

/-- A group isomorphism transports index-`n` subgroups bijectively onto index-`n` subgroups. -/
def fixedIndexSubgroupEquiv (f : G ≃* G') (n : ℕ) :
    {H : Subgroup G // H.index = n} ≃ {H' : Subgroup G' // H'.index = n} where
  toFun H := ⟨H.1.map (f : G →* G'), (H.1.index_map_equiv f).trans H.2⟩
  invFun H' := ⟨H'.1.comap (f : G →* G'), by
    rw [Subgroup.comap_equiv_eq_map_symm]
    exact (H'.1.index_map_equiv f.symm).trans H'.2⟩
  left_inv H := Subtype.ext (H.1.comap_map_eq_self_of_injective f.injective)
  right_inv H' := Subtype.ext (H'.1.map_comap_eq_self_of_surjective f.surjective)

@[simp]
theorem coe_fixedIndexSubgroupEquiv_apply (f : G ≃* G') (n : ℕ)
    (H : {H : Subgroup G // H.index = n}) :
    (f.fixedIndexSubgroupEquiv n H : Subgroup G') = H.1.map (f : G →* G') :=
  (rfl)

@[simp]
theorem coe_fixedIndexSubgroupEquiv_symm_apply (f : G ≃* G') (n : ℕ)
    (H' : {H' : Subgroup G' // H'.index = n}) :
    ((f.fixedIndexSubgroupEquiv n).symm H' : Subgroup G) = H'.1.comap (f : G →* G') :=
  (rfl)

/-- `MulEquiv.fixedIndexSubgroupEquiv` is equivariant with respect to `ConjAct`. -/
theorem fixedIndexSubgroupEquiv_conjAct_smul (f : G ≃* G') (n : ℕ) (c : ConjAct G)
    (H : {H : Subgroup G // H.index = n}) :
    f.fixedIndexSubgroupEquiv n (c • H) =
      ConjAct.toConjAct (f (ConjAct.ofConjAct c)) • f.fixedIndexSubgroupEquiv n H := by
  ext1
  exact H.1.map_map_conj (f : G →* G') (ConjAct.ofConjAct c)

/-- A group isomorphism transports conjugacy classes of index-`n` subgroups bijectively. -/
def fixedIndexConjClassesEquiv (f : G ≃* G') (n : ℕ) :
    MulAction.orbitRel.Quotient (ConjAct G) {H : Subgroup G // H.index = n} ≃
      MulAction.orbitRel.Quotient (ConjAct G') {H' : Subgroup G' // H'.index = n} where
  toFun := Quotient.map' (f.fixedIndexSubgroupEquiv n) fun H₁ H₂ h ↦ by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨c, hc⟩ := h
    exact ⟨ConjAct.toConjAct (f (ConjAct.ofConjAct c)), by
      rw [← f.fixedIndexSubgroupEquiv_conjAct_smul, hc]⟩
  invFun := Quotient.map' (f.fixedIndexSubgroupEquiv n).symm fun H₁' H₂' h' ↦ by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h' ⊢
    obtain ⟨c', hc'⟩ := h'
    refine ⟨ConjAct.toConjAct (f.symm (ConjAct.ofConjAct c')), ?_⟩
    apply (f.fixedIndexSubgroupEquiv n).injective
    rw [f.fixedIndexSubgroupEquiv_conjAct_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      ConjAct.ofConjAct_toConjAct, f.apply_symm_apply, ConjAct.toConjAct_ofConjAct, hc']
  left_inv := Quotient.ind' fun H ↦
    congrArg Quotient.mk'' ((f.fixedIndexSubgroupEquiv n).symm_apply_apply H)
  right_inv := Quotient.ind' fun H' ↦
    congrArg Quotient.mk'' ((f.fixedIndexSubgroupEquiv n).apply_symm_apply H')

@[simp]
theorem fixedIndexConjClassesEquiv_mk (f : G ≃* G') (n : ℕ)
    (H : {H : Subgroup G // H.index = n}) :
    f.fixedIndexConjClassesEquiv n (Quotient.mk'' H) =
      Quotient.mk'' (f.fixedIndexSubgroupEquiv n H) :=
  (rfl)

@[simp]
theorem fixedIndexConjClassesEquiv_symm_mk (f : G ≃* G') (n : ℕ)
    (H' : {H' : Subgroup G' // H'.index = n}) :
    (f.fixedIndexConjClassesEquiv n).symm (Quotient.mk'' H') =
      Quotient.mk'' ((f.fixedIndexSubgroupEquiv n).symm H') :=
  (rfl)

end MulEquiv

end FixedIndex
