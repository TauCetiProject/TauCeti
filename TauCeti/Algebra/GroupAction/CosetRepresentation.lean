/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.Algebra.GroupAction.PermutationRepresentation
public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.GroupTheory.Index.Map
public import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Permutation representations on coset spaces

For a subgroup `H` of a group `G` and an enumeration `e : G ⧸ H ≃ β` of its left cosets,
`Equiv.permutationRepresentation e : G →* Equiv.Perm β` is the permutation representation of `G` on
`G ⧸ H` read through `e`. This file proves the classification and symmetry theorems for such coset
representations, without assuming `H` normal or of finite index:

* **Conjugacy (abstract Millington criterion).** Right multiplication by `g⁻¹` gives a left
  `G`-equivariant bijection `G ⧸ H₁ ≃ G ⧸ H₂` when `g H₁ g⁻¹ = H₂`
  (`Subgroup.quotientEquivOfConjAct`), so two coset representations are conjugate in `Equiv.Perm β`
  iff the subgroups are conjugate (`Equiv.exists_conj_permutationRepresentation_quotient_iff`), and
  pointed-conjugate iff `H₁ = H₂`
  (`Equiv.exists_conj_permutationRepresentation_quotient_apply_eq_iff`).
* **Transport along isomorphisms and right cosets.** Pointwise action preserves index
  (`Subgroup.index_smul` in `TauCeti.GroupTheory.Index.Map`), giving the `ConjAct G`-subaction
  `Subgroup.ofIndex` transported across `φ : G ≃* G'` by `MulEquiv.ofIndexEquiv`,
  `MulEquiv.ofIndexEquiv_conjAct_smul`, and `MulEquiv.orbitRelQuotientOfIndexEquiv`; see also
  `Equiv.permutationRepresentation_congrOfMapEq`, `Subgroup.rightCosetPerm`, and
  `Equiv.permCongr_rightCosetPerm`.
* **Normal core and centralizer.** The kernel of the coset representation is `H.normalCore`
  (`Equiv.ker_permutationRepresentation_quotient`,
  `Equiv.rangePermutationRepresentationQuotientMulEquiv`), and its centralizer in `Equiv.Perm β` is
  canonically `(H.normalizerQuotient)ᵐᵒᵖ` (`Subgroup.centralizerToPermHomQuotientMulEquiv`,
  `Equiv.centralizerPermutationRepresentationQuotientMulEquiv`), of order `[N_G(H) : H]`.

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1 (1969),
  351–357.
* J. S. Milne, *Group Theory*, Chapter 1 (transitive `G`-sets, coset spaces, and `G`-automorphisms).
-/

open scoped Pointwise

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-! ### The fiber of index-`n` subgroups -/

/-- The subgroups of `G` of index `n`, as a `ConjAct G`-invariant sub-action of `Subgroup G`.
With `Subgroup.index`'s convention, `n = 0` denotes infinite-index subgroups. -/
def ofIndex (G : Type*) [Group G] (n : ℕ) : SubMulAction (ConjAct G) (Subgroup G) where
  carrier := {H | H.index = n}
  smul_mem' g H hH := (index_smul g H).trans hH

/-- A subgroup belongs to `Subgroup.ofIndex G n` if and only if its index is `n`. -/
@[simp] theorem mem_ofIndex {n : ℕ} {H : Subgroup G} : H ∈ ofIndex G n ↔ H.index = n := Iff.rfl

/-! ### Equivariant coset bijections for conjugate subgroups -/

/-- Right multiplication by `g⁻¹` on left cosets, carrying `G ⧸ H₁` onto `G ⧸ H₂` when
`g H₁ g⁻¹ = H₂`. Unlike conjugation of representatives, right multiplication commutes with the left
translation action of `G` (`Subgroup.quotientEquivOfConjAct_smul`). -/
def quotientEquivOfConjAct {H₁ H₂ : Subgroup G} {g : G}
    (h : ConjAct.toConjAct g • H₁ = H₂) : G ⧸ H₁ ≃ G ⧸ H₂ :=
  Quotient.congr (Equiv.mulRight g⁻¹) fun a b ↦ by
    simp only [QuotientGroup.leftRel_apply, Equiv.coe_mulRight, mul_inv_rev, inv_inv, ← h,
      mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul]
    exact iff_of_eq (congrArg (· ∈ H₁) (by group))

/-- `Subgroup.quotientEquivOfConjAct` sends the left coset `x H₁` to `(x * g⁻¹) H₂`. -/
@[simp] theorem quotientEquivOfConjAct_mk {H₁ H₂ : Subgroup G} {g : G}
    (h : ConjAct.toConjAct g • H₁ = H₂) (x : G) :
    quotientEquivOfConjAct h (x : G ⧸ H₁) = ((x * g⁻¹ : G) : G ⧸ H₂) := (rfl)

/-- The inverse of `Subgroup.quotientEquivOfConjAct` sends `x H₂` to `(x * g) H₁`. -/
@[simp] theorem quotientEquivOfConjAct_symm_mk {H₁ H₂ : Subgroup G} {g : G}
    (h : ConjAct.toConjAct g • H₁ = H₂) (x : G) :
    (quotientEquivOfConjAct h).symm (x : G ⧸ H₂) = ((x * g : G) : G ⧸ H₁) :=
  (quotientEquivOfConjAct h).injective <| by
    rw [Equiv.apply_symm_apply, quotientEquivOfConjAct_mk, mul_inv_cancel_right]

/-- `Subgroup.quotientEquivOfConjAct` is equivariant for left translation by `G`. -/
theorem quotientEquivOfConjAct_smul {H₁ H₂ : Subgroup G} {g : G}
    (h : ConjAct.toConjAct g • H₁ = H₂) (k : G) (q : G ⧸ H₁) :
    quotientEquivOfConjAct h (k • q) = k • quotientEquivOfConjAct h q :=
  QuotientGroup.induction_on q fun x ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, quotientEquivOfConjAct_mk,
      quotientEquivOfConjAct_mk, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]

/-! ### Right multiplication on right cosets -/

/-- The permutation of the right coset space `Quotient (QuotientGroup.rightRel H)` induced by right
multiplication by `g`: the right coset `H x` goes to `H (x * g)`. -/
def rightCosetPerm (H : Subgroup G) (g : G) : Equiv.Perm (Quotient (QuotientGroup.rightRel H)) :=
  Quotient.congr (Equiv.mulRight g) fun a b ↦ by
    simp only [QuotientGroup.rightRel_apply, Equiv.coe_mulRight, mul_inv_rev, mul_assoc,
      mul_inv_cancel_left]

/-- `H.rightCosetPerm g` sends the right coset `H x` to `H (x * g)`. -/
@[simp] theorem rightCosetPerm_mk (H : Subgroup G) (g x : G) :
    H.rightCosetPerm g (Quotient.mk'' x) = Quotient.mk'' (x * g) := (rfl)

/-- Right multiplication by `1` induces the identity permutation on right cosets. -/
@[simp] theorem rightCosetPerm_one (H : Subgroup G) : H.rightCosetPerm 1 = 1 :=
  Equiv.ext fun q ↦ Quotient.inductionOn' q fun _ ↦ by simp

/-- Right multiplication on right cosets reverses multiplication order: applying `g₂` on the right
and then `g₁` on the right is right multiplication by `g₂ * g₁`. -/
theorem rightCosetPerm_mul (H : Subgroup G) (g₁ g₂ : G) :
    H.rightCosetPerm (g₂ * g₁) = H.rightCosetPerm g₁ * H.rightCosetPerm g₂ :=
  Equiv.ext fun q ↦ Quotient.inductionOn' q fun _ ↦ by simp [mul_assoc]

/-- Right multiplication by `g⁻¹` induces the inverse permutation on right cosets. -/
@[simp] theorem rightCosetPerm_inv (H : Subgroup G) (g : G) :
    H.rightCosetPerm g⁻¹ = (H.rightCosetPerm g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rightCosetPerm_mul, mul_inv_cancel, rightCosetPerm_one])

/-- Under `QuotientGroup.quotientRightRelEquivQuotientLeftRel H` (`H x ↦ x⁻¹ H`), right
multiplication by `g` on right cosets corresponds to left translation by `g⁻¹` on left cosets. -/
theorem quotientRightRelEquivQuotientLeftRel_rightCosetPerm (H : Subgroup G) (g : G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H (H.rightCosetPerm g q) =
      g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H q :=
  Quotient.inductionOn' q fun x ↦ by
    rw [rightCosetPerm_mk, QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk,
      QuotientGroup.quotientRightRelEquivQuotientLeftRel_mk, mul_inv_rev,
      MulAction.Quotient.smul_mk, smul_eq_mul]

/-! ### Centralizer of left translation on `G ⧸ H` -/

private theorem toPermHom_normalizer_op_mem_centralizer (H : Subgroup G)
    (u : (normalizer (H : Set G)).op) :
    MulAction.toPermHom (normalizer (H : Set G)).op (G ⧸ H) u ∈
      centralizer (Set.range (MulAction.toPermHom G (G ⧸ H))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact Equiv.ext fun q ↦ QuotientGroup.induction_on q fun x ↦ by
    simp [Equiv.Perm.mul_apply, MulAction.Quotient.smul_mk, Subgroup.smul_def,
      MulOpposite.smul_eq_mul_unop, smul_eq_mul, mul_assoc]

/-- The homomorphism `N_G(H) →* C_{Perm (G ⧸ H)}(G)ᵐᵒᵖ` sending `n` to right multiplication by `n`
on left cosets via Mathlib's `(normalizer H).op` quotient action. -/
private def normalizerToCentralizerOp (H : Subgroup G) :
    normalizer (H : Set G) →* (centralizer (Set.range (MulAction.toPermHom G (G ⧸ H))))ᵐᵒᵖ :=
  (((MulAction.toPermHom (normalizer (H : Set G)).op (G ⧸ H)).codRestrict _
    (toPermHom_normalizer_op_mem_centralizer H)).op).comp
    (normalizer (H : Set G)).mulEquivOpMop.toMonoidHom

private theorem coe_unop_normalizerToCentralizerOp_apply (H : Subgroup G)
    (n : normalizer (H : Set G)) (x : G) :
    (((normalizerToCentralizerOp H n).unop : Equiv.Perm (G ⧸ H)) (x : G ⧸ H)) =
      ((x * (n : G) : G) : G ⧸ H) := by
  simp [normalizerToCentralizerOp, MonoidHom.op, Subgroup.smul_def,
    MulOpposite.smul_eq_mul_unop]

private theorem normalizerToCentralizerOp_eq_one_iff (H : Subgroup G)
    (n : normalizer (H : Set G)) :
    normalizerToCentralizerOp H n = 1 ↔ (n : G) ∈ H := by
  rw [← MulOpposite.unop_inj, MulOpposite.unop_one, Subtype.ext_iff, OneMemClass.coe_one]
  refine ⟨fun h ↦ ?_, fun hn ↦ Equiv.ext fun q ↦ QuotientGroup.induction_on q fun x ↦ ?_⟩
  · have h1 := Equiv.congr_fun h ((1 : G) : G ⧸ H)
    rw [coe_unop_normalizerToCentralizerOp_apply, one_mul, Equiv.Perm.one_apply, QuotientGroup.eq,
      mul_one] at h1
    exact inv_mem_iff.mp h1
  · rw [coe_unop_normalizerToCentralizerOp_apply, Equiv.Perm.one_apply, QuotientGroup.eq]
    simpa [mul_assoc] using hn

private noncomputable def normalizerQuotientEquivCentralizerOp (H : Subgroup G) :
    H.normalizerQuotient ≃* (centralizer (Set.range (MulAction.toPermHom G (G ⧸ H))))ᵐᵒᵖ := by
  let ψ := H.normalizerQuotientLift (normalizerToCentralizerOp H) fun g hg ↦
    (normalizerToCentralizerOp_eq_one_iff H g).mpr hg
  refine MulEquiv.ofBijective ψ
    ⟨(H.normalizerQuotientLift_injective_iff _ _).mpr (normalizerToCentralizerOp_eq_one_iff H),
      fun y ↦ ?_⟩
  let τ := y.unop
  have hcomm (g : G) (q : G ⧸ H) : (τ : Equiv.Perm (G ⧸ H)) (g • q) =
      g • (τ : Equiv.Perm (G ⧸ H)) q :=
    (Equiv.congr_fun ((mem_centralizer_iff.mp τ.2) _ ⟨g, rfl⟩) q).symm
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective ((τ : Equiv.Perm (G ⧸ H)) ((1 : G) : G ⧸ H))
  have hτx (x : G) : (τ : Equiv.Perm (G ⧸ H)) (x : G ⧸ H) = ((x * n : G) : G ⧸ H) := by
    have hx : (x : G ⧸ H) = x • ((1 : G) : G ⧸ H) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [hx, hcomm, ← hn, MulAction.Quotient.smul_mk, smul_eq_mul]
  have hn_mem : n ∈ normalizer (H : Set G) := by
    rw [← inv_mem_iff, mem_normalizer_iff]
    intro h
    have hh : h ∈ H ↔ ((h : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      rw [QuotientGroup.eq, mul_one, inv_mem_iff]
    rw [hh, ← (τ : Equiv.Perm (G ⧸ H)).injective.eq_iff, hτx h, hτx 1, one_mul, eq_comm,
      QuotientGroup.eq]
    simp [mul_assoc]
  refine ⟨H.normalizerQuotientMk ⟨n, hn_mem⟩, ?_⟩
  rw [normalizerQuotientLift_mk, ← MulOpposite.unop_inj]
  exact Subtype.ext <| Equiv.ext fun q ↦ QuotientGroup.induction_on q fun x ↦
    (coe_unop_normalizerToCentralizerOp_apply H ⟨n, hn_mem⟩ x).trans (hτx x).symm

private theorem normalizerQuotientEquivCentralizerOp_mk (H : Subgroup G)
    (n : normalizer (H : Set G)) :
    normalizerQuotientEquivCentralizerOp H n = normalizerToCentralizerOp H n := by
  rw [← H.normalizerQuotientMk_apply]
  exact normalizerQuotientLift_mk H (normalizerToCentralizerOp H)
    (fun g hg ↦ (normalizerToCentralizerOp_eq_one_iff H g).mpr hg) n

/-- **The `G`-automorphism group of `G ⧸ H` is `(N_G(H) / H)ᵐᵒᵖ`.** Every permutation of `G ⧸ H`
centralizing left translation by `G` is right multiplication by a normalizer coset, and right
multiplications compose in the opposite order. -/
noncomputable def centralizerToPermHomQuotientMulEquiv (H : Subgroup G) :
    centralizer (Set.range (MulAction.toPermHom G (G ⧸ H))) ≃* (H.normalizerQuotient)ᵐᵒᵖ where
  toFun τ := MulOpposite.op ((normalizerQuotientEquivCentralizerOp H).symm (MulOpposite.op τ))
  invFun x := (normalizerQuotientEquivCentralizerOp H x.unop).unop
  left_inv τ := by
    dsimp only; rw [MulOpposite.unop_op, MulEquiv.apply_symm_apply, MulOpposite.unop_op]
  right_inv x := by
    dsimp only; rw [MulOpposite.op_unop, MulEquiv.symm_apply_apply, MulOpposite.op_unop]
  map_mul' τ₁ τ₂ := by rw [MulOpposite.op_mul, map_mul, ← MulOpposite.op_mul]

/-- The inverse of `Subgroup.centralizerToPermHomQuotientMulEquiv` sends the opposite of a
normalizer coset `n H` to right multiplication `x H ↦ (x * n) H`. -/
@[simp] theorem coe_centralizerToPermHomQuotientMulEquiv_symm_apply (H : Subgroup G)
    (n : normalizer (H : Set G)) (x : G) :
    (((H.centralizerToPermHomQuotientMulEquiv.symm
      (MulOpposite.op (n : H.normalizerQuotient)) : _) : Equiv.Perm (G ⧸ H)) (x : G ⧸ H)) =
        ((x * (n : G) : G) : G ⧸ H) := by
  change (((normalizerQuotientEquivCentralizerOp H n).unop :
    Equiv.Perm (G ⧸ H)) (x : G ⧸ H)) = ((x * (n : G) : G) : G ⧸ H)
  rw [normalizerQuotientEquivCentralizerOp_mk, coe_unop_normalizerToCentralizerOp_apply]

end Subgroup

namespace MulEquiv

variable {G G' : Type*} [Group G] [Group G']

/-- A group isomorphism identifies the subgroups of index `n` of `G` and `G'`. -/
def ofIndexEquiv (φ : G ≃* G') (n : ℕ) : Subgroup.ofIndex G n ≃ Subgroup.ofIndex G' n :=
  φ.mapSubgroup.subtypeEquiv fun H ↦ by simp [H.index_map_equiv φ]

/-- `φ.ofIndexEquiv` acts on subgroups as `Subgroup.map φ`. -/
@[simp] theorem coe_ofIndexEquiv_apply (φ : G ≃* G') (n : ℕ) (H : Subgroup.ofIndex G n) :
    (φ.ofIndexEquiv n H : Subgroup G') = H.1.map (φ : G →* G') := (rfl)

/-- `(φ.ofIndexEquiv n).symm` acts on subgroups as `Subgroup.comap φ`. -/
@[simp] theorem coe_ofIndexEquiv_symm_apply (φ : G ≃* G') (n : ℕ) (H : Subgroup.ofIndex G' n) :
    ((φ.ofIndexEquiv n).symm H : Subgroup G) = H.1.comap (φ : G →* G') :=
  (Subgroup.comap_equiv_eq_map_symm φ H.1).symm

/-- `φ.ofIndexEquiv` is equivariant with respect to subgroup conjugation. -/
@[simp] theorem ofIndexEquiv_conjAct_smul (φ : G ≃* G') (n : ℕ) (g : G)
    (H : Subgroup.ofIndex G n) :
    φ.ofIndexEquiv n (ConjAct.toConjAct g • H) = ConjAct.toConjAct (φ g) • φ.ofIndexEquiv n H :=
  Subtype.ext (Subgroup.map_map_conj H.1 φ.toMonoidHom g)

/-- A group isomorphism identifies the conjugacy classes of subgroups of index `n` of `G` and `G'`.
-/
def orbitRelQuotientOfIndexEquiv (φ : G ≃* G') (n : ℕ) :
    MulAction.orbitRel.Quotient (ConjAct G) (Subgroup.ofIndex G n) ≃
      MulAction.orbitRel.Quotient (ConjAct G') (Subgroup.ofIndex G' n) :=
  TauCeti.MulAction.orbitRelQuotientCongr (ConjAct.ofConjAct.trans (φ.trans ConjAct.toConjAct))
    (φ.ofIndexEquiv n) fun g H ↦ by
      simpa using φ.ofIndexEquiv_conjAct_smul n (ConjAct.ofConjAct g) H

/-- `φ.orbitRelQuotientOfIndexEquiv` maps the conjugacy class of `H` to that of
`φ.ofIndexEquiv n H`. -/
@[simp] theorem orbitRelQuotientOfIndexEquiv_mk (φ : G ≃* G') (n : ℕ) (H : Subgroup.ofIndex G n) :
    φ.orbitRelQuotientOfIndexEquiv n (Quotient.mk'' H) = Quotient.mk'' (φ.ofIndexEquiv n H) := by
  rw [orbitRelQuotientOfIndexEquiv, TauCeti.MulAction.orbitRelQuotientCongr_mk]

/-- `(φ.orbitRelQuotientOfIndexEquiv n).symm` maps the conjugacy class of `H` to that of
`φ.symm.ofIndexEquiv n H`. -/
@[simp] theorem orbitRelQuotientOfIndexEquiv_symm_mk (φ : G ≃* G') (n : ℕ)
    (H : Subgroup.ofIndex G' n) :
    (φ.orbitRelQuotientOfIndexEquiv n).symm (Quotient.mk'' H) =
      Quotient.mk'' (φ.symm.ofIndexEquiv n H) := by
  rw [orbitRelQuotientOfIndexEquiv, TauCeti.MulAction.orbitRelQuotientCongr_symm_mk]
  exact congrArg Quotient.mk'' <| Subtype.ext <|
    (φ.coe_ofIndexEquiv_symm_apply n H).trans (Subgroup.comap_equiv_eq_map_symm φ H.1)

end MulEquiv

namespace Equiv

variable {G G' β : Type*} [Group G] [Group G']

/-! ### Normal core, conjugacy, and transport of enumerated coset representations -/

/-- The kernel of the coset permutation representation of `H` read through `e : G ⧸ H ≃ β` is
`H.normalCore`. -/
theorem ker_permutationRepresentation_quotient {H : Subgroup G} (e : G ⧸ H ≃ β) :
    (e.permutationRepresentation (G := G)).ker = H.normalCore := by
  rw [ker_permutationRepresentation, Subgroup.normalCore_eq_ker]

/-- By the first isomorphism theorem, the image of the coset permutation representation of `H` is
canonically isomorphic to `G ⧸ H.normalCore`. -/
noncomputable def rangePermutationRepresentationQuotientMulEquiv {H : Subgroup G} (e : G ⧸ H ≃ β) :
    (e.permutationRepresentation (G := G)).range ≃* G ⧸ H.normalCore :=
  (QuotientGroup.quotientKerEquivRange (e.permutationRepresentation (G := G))).symm.trans <|
    QuotientGroup.quotientMulEquivOfEq e.ker_permutationRepresentation_quotient

/-- **Abstract Millington criterion.** For any two subgroups `H₁, H₂` of `G` and bijections
`e₁ : G ⧸ H₁ ≃ β` and `e₂ : G ⧸ H₂ ≃ β`, the coset permutation representations read through `e₁`
and `e₂` are conjugate in `Equiv.Perm β` if and only if `H₁` and `H₂` are conjugate in `G`. -/
theorem exists_conj_permutationRepresentation_quotient_iff {H₁ H₂ : Subgroup G}
    (e₁ : G ⧸ H₁ ≃ β) (e₂ : G ⧸ H₂ ≃ β) :
    (∃ τ : Perm β, (MulAut.conj τ).toMonoidHom.comp (e₁.permutationRepresentation (G := G)) =
      e₂.permutationRepresentation) ↔ ∃ g : ConjAct G, g • H₁ = H₂ := by
  refine ⟨fun ⟨τ, hτ⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (e₂.symm (τ (e₁ ((1 : G) : G ⧸ H₁))))
    have hstab : H₁ = ConjAct.toConjAct s • H₂ := by
      rw [← MulAction.stabilizer_quotient H₁,
        ← e₁.comap_stabilizer_permutationRepresentation ((1 : G) : G ⧸ H₁)]
      have hs' : τ (e₁ ((1 : G) : G ⧸ H₁)) = e₂ (s : G ⧸ H₂) := by rw [hs, apply_symm_apply]
      have hconj : MulAction.stabilizer (Perm β) (e₁ ((1 : G) : G ⧸ H₁)) =
          (MulAction.stabilizer (Perm β) (e₂ (s : G ⧸ H₂))).comap (MulAut.conj τ).toMonoidHom := by
        ext σ
        simp [MulAction.mem_stabilizer_iff, Perm.mul_apply, ← hs', τ.injective.eq_iff]
      rw [hconj, Subgroup.comap_comap, hτ, e₂.comap_stabilizer_permutationRepresentation,
        TauCeti.stabilizer_quotientGroup_mk]
      rfl
    exact ⟨(ConjAct.toConjAct s)⁻¹, by rw [hstab, inv_smul_smul]⟩
  · obtain ⟨c, rfl⟩ := ConjAct.toConjAct.surjective g
    let f := Subgroup.quotientEquivOfConjAct hg
    refine ⟨e₁.symm.trans (f.trans e₂), ?_⟩
    have hf : (f.trans e₂).permutationRepresentation (G := G) = e₂.permutationRepresentation :=
      (f.trans e₂).permutationRepresentation_eq_of_map_smul fun k q ↦ by
        rw [trans_apply, Subgroup.quotientEquivOfConjAct_smul, trans_apply,
          permutationRepresentation_apply, symm_apply_apply]
    ext k i
    have hc := e₁.permutationRepresentation_eq_conj (f.trans e₂) k
    rw [hf] at hc
    exact (Equiv.congr_fun hc i).symm

/-- **Pointed Millington criterion.** Two coset representations on `β` are conjugate by a
permutation carrying the base point `e₁ ⟦1⟧` to `e₂ ⟦1⟧` if and only if the subgroups are equal. -/
theorem exists_conj_permutationRepresentation_quotient_apply_eq_iff {H₁ H₂ : Subgroup G}
    (e₁ : G ⧸ H₁ ≃ β) (e₂ : G ⧸ H₂ ≃ β) :
    (∃ τ : Perm β, τ (e₁ ((1 : G) : G ⧸ H₁)) = e₂ ((1 : G) : G ⧸ H₂) ∧
      (MulAut.conj τ).toMonoidHom.comp (e₁.permutationRepresentation (G := G)) =
        e₂.permutationRepresentation) ↔ H₁ = H₂ := by
  refine ⟨fun ⟨τ, hbase, hτ⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← MulAction.stabilizer_quotient H₁, ← MulAction.stabilizer_quotient H₂,
      ← e₁.comap_stabilizer_permutationRepresentation ((1 : G) : G ⧸ H₁),
      ← e₂.comap_stabilizer_permutationRepresentation ((1 : G) : G ⧸ H₂)]
    have hconj : MulAction.stabilizer (Perm β) (e₁ ((1 : G) : G ⧸ H₁)) =
        (MulAction.stabilizer (Perm β) (e₂ ((1 : G) : G ⧸ H₂))).comap
          (MulAut.conj τ).toMonoidHom := by
      ext σ
      simp [MulAction.mem_stabilizer_iff, Perm.mul_apply, ← hbase, τ.injective.eq_iff]
    rw [hconj, Subgroup.comap_comap, hτ]
  · subst h
    refine ⟨e₁.symm.trans e₂, by simp, ?_⟩
    ext k i
    exact (Equiv.congr_fun (e₁.permutationRepresentation_eq_conj e₂ k) i).symm

/-- Transporting a coset numbering along a group isomorphism `φ : G ≃* G'` carrying `A` onto `B`
precomposes the coset permutation representation with `φ`. -/
theorem permutationRepresentation_congrOfMapEq (φ : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : A.map (φ : G →* G') = B) (e : G' ⧸ B ≃ β) :
    ((TauCeti.QuotientGroup.congrOfMapEq φ h).trans e).permutationRepresentation (G := G) =
      (e.permutationRepresentation (G := G')).comp (φ : G →* G') :=
  ((TauCeti.QuotientGroup.congrOfMapEq φ h).trans e).permutationRepresentation_eq_of_map_smul
    fun _ q ↦ QuotientGroup.induction_on q fun _ ↦ by simp [MulAction.Quotient.smul_mk, smul_eq_mul]

/-- If `r : Quotient (QuotientGroup.rightRel H) ≃ β` numbers the right cosets of `H` and
`e := (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm.trans r` is the induced numbering
of left cosets via `g H ↦ H g⁻¹`, then right multiplication by `g` on right cosets read through `r`
equals `(e.permutationRepresentation g)⁻¹`. -/
theorem permCongr_rightCosetPerm {H : Subgroup G}
    (r : Quotient (QuotientGroup.rightRel H) ≃ β) (g : G) :
    r.permCongr (H.rightCosetPerm g) =
      (((QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm.trans
        r).permutationRepresentation g)⁻¹ := by
  rw [← map_inv]
  ext i
  obtain ⟨q, rfl⟩ := r.surjective i
  rw [permCongr_apply, symm_apply_apply, permutationRepresentation_apply, trans_apply,
    symm_trans_apply, symm_apply_apply, symm_symm,
    ← Subgroup.quotientRightRelEquivQuotientLeftRel_rightCosetPerm, symm_apply_apply]

/-- The centralizer in `Equiv.Perm β` of the image of the coset representation `G →* Equiv.Perm β`
read through `e : G ⧸ H ≃ β` is canonically isomorphic to `(H.normalizerQuotient)ᵐᵒᵖ`. -/
noncomputable def centralizerPermutationRepresentationQuotientMulEquiv {H : Subgroup G}
    (e : G ⧸ H ≃ β) :
    Subgroup.centralizer (Set.range (e.permutationRepresentation (G := G))) ≃*
      (H.normalizerQuotient)ᵐᵒᵖ :=
  (TauCeti.Subgroup.congrOfMapEq e.permCongrHom.symm <| by
    ext σ
    rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap]
    simp only [MulEquiv.symm_symm, MonoidHom.coe_ofClass, Subgroup.mem_centralizer_iff,
      Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    refine forall_congr' fun g ↦ ?_
    have hg : e.permCongrHom (MulAction.toPermHom G (G ⧸ H) g) = e.permutationRepresentation g :=
      Equiv.ext fun i ↦ by simp [permCongrHom_coe, permCongr_apply]
    rw [← hg, ← map_mul, ← map_mul, e.permCongrHom.injective.eq_iff]).trans
    H.centralizerToPermHomQuotientMulEquiv

/-- The inverse of `Equiv.centralizerPermutationRepresentationQuotientMulEquiv` sends the opposite
of a normalizer coset `n H` to the conjugate by `e` of right multiplication `x H ↦ (x * n) H`. -/
@[simp] theorem coe_centralizerPermutationRepresentationQuotientMulEquiv_symm_apply
    {H : Subgroup G} (e : G ⧸ H ≃ β) (n : Subgroup.normalizer (H : Set G)) (x : G) :
    (((e.centralizerPermutationRepresentationQuotientMulEquiv.symm
      (MulOpposite.op (n : H.normalizerQuotient)) : _) : Perm β) (e (x : G ⧸ H))) =
        e ((x * (n : G) : G) : G ⧸ H) := by
  rw [centralizerPermutationRepresentationQuotientMulEquiv, MulEquiv.symm_trans_apply,
    TauCeti.Subgroup.coe_congrOfMapEq_symm_apply, MulEquiv.symm_symm, permCongrHom_coe,
    permCongr_apply, symm_apply_apply, Subgroup.coe_centralizerToPermHomQuotientMulEquiv_symm_apply]

/-- The order of the centralizer of a coset permutation representation of `H` is the relative index
`[N_G(H) : H]`. No finiteness assumption is needed (`Nat.card` is `0` when infinite). -/
theorem natCard_centralizer_permutationRepresentation_quotient {H : Subgroup G} (e : G ⧸ H ≃ β) :
    Nat.card (Subgroup.centralizer (Set.range (e.permutationRepresentation (G := G)))) =
      H.relIndex (Subgroup.normalizer (H : Set G)) := by
  rw [Nat.card_congr e.centralizerPermutationRepresentationQuotientMulEquiv.toEquiv,
    Nat.card_congr MulOpposite.opEquiv.symm]
  rfl

end Equiv
