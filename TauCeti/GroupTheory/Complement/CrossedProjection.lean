/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Basic
public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle
public import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.GroupTheory.SemidirectProduct

/-!
# Complements and normalized crossed projections

For a (not necessarily abelian) normal subgroup `N` of `G`, a complement `D` determines a
multiplicative crossed homomorphism `c : G → N` (`g ↦ n` for `g = n * d`), satisfying
`c (g * k) = g • c k * c g` (`Subgroup.IsComplement'.isMulCrossedHom_crossedProjection`) and
restricting to the identity on `N`. Conversely, the `1`-locus `hc.oneLocus` of any normalized
`TauCeti.IsMulCrossedHom` `c : G → N` is a complement of `N`, giving the bijection
`Subgroup.mulCrossedHomEquiv` (`Subgroup.exists_isComplement'_iff_isMulCrossedHom`).

The same non-abelian dictionary holds on an intermediate subgroup `H ≥ N`: the left projection
along a local complement `K` of `N` in `H` is a normalized `TauCeti.IsMulCrossedHom` `H → N`
(`Subgroup.IsLocalComplement.isMulCrossedHom_leftProjection`), mutually inverse to taking the
`1`-locus in `G` (`Subgroup.localMulCrossedHomEquiv`,
`Subgroup.exists_isLocalComplement_iff_isMulCrossedHom`). Conjugating a normalized crossed map `c`
on `H` by `g` gives the normalized crossed map `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`
(`Subgroup.smul_apply_equivSMul_symm_inclusion`), whose `1`-locus is conjugated by `g`.

Conjugating a complement by `a ∈ N` replaces its crossed projection `c` by
`x ↦ x • a * c x * a⁻¹` (`Subgroup.IsComplement'.crossedProjection_conj_coe_smul_eq`,
`Subgroup.IsComplement'.eq_conj_smul_iff_crossedProjection_eq_mul_inv`). When `N` is abelian this
simplifies to the pointwise product `c x * (x • a / a)` with the principal crossed map `δ_a`
(`Subgroup.IsComplement'.eq_conj_smul_iff_crossedProjection_eq`, and on `H ≥ N`,
`Subgroup.IsLocalComplement.eq_conj_smul_iff_leftProjection_eq`). Reading `N` as `Additive N`
identifies normalized crossed maps with normalized `groupCohomology.IsCocycle₁` maps
(`Subgroup.crossedProjectionEquiv`, `Subgroup.localCrossedProjectionEquiv`), where adding
`x ↦ x • a - a` conjugates the zero locus by `a`
(`Subgroup.map_subtype_zeroLocus_add_smul_sub`).

The conjugation action is explicit rather than a global instance. The additive
coefficient action uses `Additive.distribMulAction`, and kernels use
`TauCeti.IsMulCrossedHom.oneLocus` and the existing `groupCohomology.zeroLocus`.
The crossed projection is the first component of Mathlib's complement decomposition
(hence sends `1` to `1`, commutes with left multiplication from `N`, ignores right
multiplication from the complement, and satisfies `c g = n ↔ n⁻¹ * g ∈ D`);
its quotient-splitting formula supplies the crossed identity.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math.
  190 (1952), 93–107, §1, for normalized crossed maps in complement theory.
-/

public section

open scoped IsMulCommutative Pointwise
open groupCohomology

namespace Subgroup

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

attribute [local instance] conjugationAction

variable {N}

namespace IsComplement'

variable {D : Subgroup G} (h : N.IsComplement' D)

/-- Projection to the normal factor in Mathlib's complement decomposition.
It is generally not a homomorphism. -/
noncomputable def crossedProjection (g : G) : N :=
  (h.equiv g).1

omit [N.Normal] in
theorem crossedProjection_apply (g : G) : h.crossedProjection g = (h.equiv g).1 := (rfl)

/-- The left component of `(SemidirectProduct.mulEquivSubgroup h).symm` is `h.crossedProjection`. -/
theorem mulEquivSubgroup_symm_left_eq_crossedProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).left = h.crossedProjection g :=
  SemidirectProduct.mulEquivSubgroup_symm_apply_left h g

omit [N.Normal] in
/-- The projection of a product of the two factors is its normal component. -/
theorem crossedProjection_mul (n : N) (d : D) :
    h.crossedProjection ((n : G) * d) = n :=
  congrArg Prod.fst (h.equiv.apply_symm_apply (n, d))

omit [N.Normal] in
/-- The crossed projection restricts to the identity on the normal subgroup. -/
@[simp]
theorem crossedProjection_coe (n : N) : h.crossedProjection n = n :=
  h.equiv_fst_eq_self_of_mem_of_one_mem D.one_mem n.property

omit [N.Normal] in
/-- The crossed projection vanishes on the complementary factor. -/
@[simp]
theorem crossedProjection_coe_right (d : D) : h.crossedProjection d = 1 :=
  h.equiv_fst_eq_one_of_mem_of_one_mem N.one_mem d.property

omit [N.Normal] in
/-- The crossed projection sends `1` to `1`. -/
@[simp]
theorem crossedProjection_one : h.crossedProjection 1 = 1 :=
  congrArg Prod.fst (h.equiv_one N.one_mem D.one_mem)

omit [N.Normal] in
/-- Left multiplication by an element of `N` multiplies the crossed projection on the left. -/
@[simp]
theorem crossedProjection_mul_left (n : N) (g : G) :
    h.crossedProjection ((n : G) * g) = n * h.crossedProjection g :=
  congrArg Prod.fst (h.equiv_mul_left n g)

omit [N.Normal] in
/-- Right multiplication by an element of the complement leaves the crossed projection
unchanged. -/
@[simp]
theorem crossedProjection_mul_right (g : G) (d : D) :
    h.crossedProjection (g * d) = h.crossedProjection g :=
  (Prod.ext_iff.mp (h.equiv_mul_right g d)).1

/-- In the ambient group, the crossed projection of `g` is `g` multiplied on the right by the
inverse of its coset representative under the quotient splitting. -/
theorem coe_crossedProjection (g : G) :
    (h.crossedProjection g : G) = g * (h.quotientSplitting (g : G ⧸ N))⁻¹ := by
  obtain ⟨⟨n, d⟩, rfl⟩ := h.surjective g
  have hn : (n : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr n.property
  simp [hn]

/-- **Crossed multiplication law.** Without any commutativity assumption on `N`, the crossed
projection satisfies `c (g * k) = g • c k * c g` for ambient conjugation. -/
theorem isMulCrossedHom_crossedProjection :
    TauCeti.IsMulCrossedHom h.crossedProjection :=
  TauCeti.isMulCrossedHom_iff.mpr fun g k => by
    apply Subtype.ext
    simp only [coe_crossedProjection, coe_mul, coe_conjugationAction_smul,
      QuotientGroup.mk_mul, map_mul]
    group

/-- When `N` is abelian, the crossed projection is a multiplicative `1`-cocycle for ambient
conjugation. -/
theorem isMulCocycle₁_crossedProjection [IsMulCommutative N] :
    IsMulCocycle₁ h.crossedProjection :=
  isMulCocycle₁_iff_isMulCrossedHom.mpr h.isMulCrossedHom_crossedProjection

omit [N.Normal] in
/-- Exactly the elements of the complement have trivial crossed projection. -/
@[simp]
theorem crossedProjection_eq_one_iff (g : G) : h.crossedProjection g = 1 ↔ g ∈ D := by
  rw [← Subtype.coe_inj]
  exact h.coe_equiv_fst_eq_one_iff_mem N.one_mem

omit [N.Normal] in
/-- The crossed projection of `g` equals `n` if and only if `n⁻¹ * g` lies in the complement. -/
theorem crossedProjection_eq_iff (g : G) (n : N) :
    h.crossedProjection g = n ↔ (n : G)⁻¹ * g ∈ D := by
  rw [eq_comm, ← inv_mul_eq_one, ← h.crossedProjection_mul_left n⁻¹ g, Subgroup.coe_inv,
    h.crossedProjection_eq_one_iff]

/-- The `1`-locus of the crossed projection along `D` is `D`. -/
@[simp]
theorem oneLocus_crossedProjection :
    h.isMulCrossedHom_crossedProjection.oneLocus = D := by
  ext g
  simp

/-- **Equivariance of crossed projections.** The crossed projection along the conjugate
complement `g D g⁻¹` is `x ↦ g • c (g⁻¹ * x * g)`, where `c` is the crossed projection along
`D`. -/
theorem crossedProjection_conj_smul (g x : G) :
    (h.conj_smul g).crossedProjection x = g • h.crossedProjection (g⁻¹ * x * g) := by
  have hy : (h.crossedProjection (g⁻¹ * x * g) : G) * (h.equiv (g⁻¹ * x * g)).2 = g⁻¹ * x * g :=
    h.equiv_fst_mul_equiv_snd _
  have hd : g * (h.equiv (g⁻¹ * x * g)).2 * g⁻¹ ∈ MulAut.conj g • D := by
    rw [mem_pointwise_smul_iff_inv_smul_mem]
    convert (h.equiv (g⁻¹ * x * g)).2.property using 1
    simp [mul_assoc]
  have hx : x = ((g • h.crossedProjection (g⁻¹ * x * g) : N) : G) *
      (⟨_, hd⟩ : ↥(MulAut.conj g • D)) := by
    rw [coe_conjugationAction_smul, coe_mk, ← mul_inv_eq_iff_eq_mul.mpr hy.symm]
    group
  conv_lhs => rw [hx]
  exact (h.conj_smul g).crossedProjection_mul _ _

/-- **Non-abelian conjugation by an element of `N`.** For `a ∈ N`, the crossed projection along
`a D a⁻¹` sends `x` to `x • a * c x * a⁻¹`, without assuming `N` is abelian. -/
theorem crossedProjection_conj_coe_smul_eq (a : N) (x : G) :
    (h.conj_smul (a : G)).crossedProjection x = x • a * h.crossedProjection x * a⁻¹ := by
  have hc := h.isMulCrossedHom_crossedProjection
  rw [h.crossedProjection_conj_smul]
  simp only [hc.map_mul, crossedProjection_coe, ← coe_inv, mul_smul, smul_mul',
    conjugationAction_coe_smul_eq]
  group

/-- Two complements of a (not necessarily abelian) normal subgroup `N` are conjugate by `a ∈ N`
exactly when their crossed projections satisfy `c' x = x • a * c x * a⁻¹`. -/
theorem eq_conj_smul_iff_crossedProjection_eq_mul_inv {D' : Subgroup G} (h' : N.IsComplement' D')
    (a : N) : D' = MulAut.conj (a : G) • D ↔
      ∀ x, h'.crossedProjection x = x • a * h.crossedProjection x * a⁻¹ := by
  constructor
  · rintro rfl x
    exact h.crossedProjection_conj_coe_smul_eq a x
  · intro hD
    ext x
    rw [← h'.crossedProjection_eq_one_iff, ← (h.conj_smul (a : G)).crossedProjection_eq_one_iff,
      hD, h.crossedProjection_conj_coe_smul_eq]
end IsComplement'

/-! ### Local complements and normalized crossed homomorphisms on an intermediate subgroup -/

namespace IsLocalComplement

/-- For `H = ⊤`, the local left projection agrees with
`Subgroup.IsComplement'.crossedProjection`. -/
theorem leftProjection_top_eq_crossedProjection {D : Subgroup G}
    (h : N.IsLocalComplement D ⊤) (x : (⊤ : Subgroup G)) :
    h.leftProjection x = (isLocalComplement_top_iff.mp h).crossedProjection x :=
  h.leftProjection_top x

omit [N.Normal] in
/-- When a local complement `K` of `N` in `H` is contained in a global complement `D` of `N`, its
left projection is the restriction of the crossed projection along `D`. -/
theorem leftProjection_eq_crossedProjection {K H D : Subgroup G}
    [(N.subgroupOf H).Normal] (h : N.IsLocalComplement K H) (hD : N.IsComplement' D)
    (hKD : K ≤ D) (x : H) :
    h.leftProjection x = hD.crossedProjection x :=
  ((hD.crossedProjection_eq_iff (x : G) _).mpr (hKD ((h.leftProjection_eq_iff x _).mp rfl))).symm

variable {K H : Subgroup G} (h : N.IsLocalComplement K H)

include h

/-- **Crossed multiplication law for local complements.** Without assuming `N` is abelian, the left
projection of a local complement `K` of `N` in `H` satisfies `c (x * y) = x • c y * c x`. -/
theorem isMulCrossedHom_leftProjection : TauCeti.IsMulCrossedHom h.leftProjection :=
  TauCeti.isMulCrossedHom_iff.mpr fun x y => by
    rw [h.leftProjection_eq_iff]
    have hx := (h.leftProjection_eq_iff x _).mp rfl
    have hy := (h.leftProjection_eq_iff y _).mp rfl
    simp only [coe_mul, Subgroup.smul_def, coe_conjugationAction_smul]
    convert K.mul_mem hx hy using 1
    group

/-- The left projection of a local complement `K` of an abelian normal subgroup `N` in `H`
satisfies the `1`-cocycle identity for the conjugation action of `H` on `N`. -/
theorem isMulCocycle₁_leftProjection [IsMulCommutative N] : IsMulCocycle₁ h.leftProjection :=
  isMulCocycle₁_iff_isMulCrossedHom.mpr h.isMulCrossedHom_leftProjection

/-- The `1`-locus of the left projection of a local complement, viewed in `G`, is that local
complement. -/
@[simp]
theorem map_oneLocus_leftProjection :
    h.isMulCrossedHom_leftProjection.oneLocus.map H.subtype = K := by
  ext g
  simp only [mem_map, TauCeti.IsMulCrossedHom.mem_oneLocus, h.leftProjection_eq_one_iff,
    coe_subtype]
  exact ⟨fun ⟨_, hx, hgx⟩ => hgx ▸ hx, fun hg => ⟨⟨g, h.right_le hg⟩, hg, rfl⟩⟩

end IsLocalComplement

section LocalDictionary

variable {H : Subgroup G} (hNH : N ≤ H)

/-- For a normalized multiplicative crossed homomorphism `c` on `H`, `(c x)⁻¹ * x` lies in the
`1`-locus of `c` mapped to `G`, without assuming `N` is abelian. -/
private theorem coe_inv_mul_mem_map_oneLocus {c : H → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c (inclusion hNH n) = n) (x : H) :
    (c x : G)⁻¹ * x ∈ hc.oneLocus.map H.subtype := by
  let n : N := c x
  refine ⟨inclusion hNH n⁻¹ * x, hc.mem_oneLocus.mpr ?_, by simp [n]⟩
  rw [hc.map_mul, hn, Subgroup.smul_def, coe_inclusion, coe_inv,
    conjugationAction_inv_coe_smul_self, mul_inv_cancel]

/-- A normalized multiplicative crossed homomorphism on an intermediate subgroup `H ≥ N` has as
`1`-locus a local complement of `N` in `H`, without assuming `N` is abelian. -/
theorem isLocalComplement_map_oneLocus {c : H → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c (inclusion hNH n) = n) :
    N.IsLocalComplement (hc.oneLocus.map H.subtype) H := by
  refine ⟨?_, le_antisymm (sup_le hNH (map_subtype_le _)) fun x hx => ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hgN, x, hx, rfl⟩
    have hz : c (inclusion hNH ⟨x, hgN⟩) = 1 := hc.mem_oneLocus.mp hx
    rw [hn] at hz
    exact congrArg Subtype.val hz
  · have hk := coe_inv_mul_mem_map_oneLocus hNH hc hn ⟨x, hx⟩
    simpa using mul_mem_sup (c ⟨x, hx⟩).property hk

/-- The left projection along the `1`-locus of a normalized multiplicative crossed homomorphism is
that crossed homomorphism itself. -/
theorem leftProjection_map_oneLocus {c : H → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c (inclusion hNH n) = n) (x : H) :
    (isLocalComplement_map_oneLocus hNH hc hn).leftProjection x = c x :=
  ((isLocalComplement_map_oneLocus hNH hc hn).leftProjection_eq_iff x _).mpr
    (coe_inv_mul_mem_map_oneLocus hNH hc hn x)

variable (N H) in
/-- Local complements of a (not necessarily abelian) normal subgroup `N` in an intermediate subgroup
`H ≥ N` correspond bijectively to normalized multiplicative crossed homomorphisms `H → N`. -/
noncomputable def localMulCrossedHomEquiv :
    {K : Subgroup G // N.IsLocalComplement K H} ≃
      {c : H → N // TauCeti.IsMulCrossedHom c ∧ ∀ n : N, c (inclusion hNH n) = n} where
  toFun K := ⟨K.property.leftProjection, K.property.isMulCrossedHom_leftProjection,
    K.property.leftProjection_left⟩
  invFun c := ⟨c.property.1.oneLocus.map H.subtype,
    isLocalComplement_map_oneLocus hNH c.property.1 c.property.2⟩
  left_inv K := Subtype.ext K.property.map_oneLocus_leftProjection
  right_inv c := Subtype.ext (funext (leftProjection_map_oneLocus hNH c.property.1 c.property.2))

/-- The normalized multiplicative crossed homomorphism attached to a local complement is its left
projection. -/
@[simp]
theorem localMulCrossedHomEquiv_apply (K : {K : Subgroup G // N.IsLocalComplement K H}) (x : H) :
    (localMulCrossedHomEquiv N H hNH K).val x = K.property.leftProjection x := (rfl)

/-- The local complement attached to a normalized multiplicative crossed homomorphism on `H` is its
`1`-locus, mapped to `G`. -/
@[simp]
theorem localMulCrossedHomEquiv_symm_apply
    (c : {c : H → N // TauCeti.IsMulCrossedHom c ∧ ∀ n : N, c (inclusion hNH n) = n}) :
    ((localMulCrossedHomEquiv N H hNH).symm c).val = c.property.1.oneLocus.map H.subtype := (rfl)

/-- A normal subgroup `N` has a local complement in an intermediate subgroup `H ≥ N` if and only if
there is a multiplicative crossed homomorphism `H → N` for conjugation that restricts to the
identity on `N`. -/
theorem exists_isLocalComplement_iff_isMulCrossedHom :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      ∃ c : H → N, TauCeti.IsMulCrossedHom c ∧ ∀ n : N, c (inclusion hNH n) = n :=
  ⟨fun ⟨_, hK⟩ => ⟨hK.leftProjection, hK.isMulCrossedHom_leftProjection, hK.leftProjection_left⟩,
    fun ⟨_, hc, hn⟩ => ⟨_, isLocalComplement_map_oneLocus hNH hc hn⟩⟩

/-- Conjugating a normalized map `c : H → N` by `g` gives the map `x ↦ g • c (g⁻¹ * x * g)` on
`g H g⁻¹`, which is again the identity on `N`. By `TauCeti.IsMulCrossedHom.conj` and
`TauCeti.IsMulCrossedHom.map_subtype_oneLocus_conj`, a normalized multiplicative crossed
homomorphism conjugates to a normalized multiplicative crossed homomorphism whose `1`-locus is
conjugated by `g`. -/
theorem smul_apply_equivSMul_symm_inclusion {c : H → N}
    (hn : ∀ n : N, c (inclusion hNH n) = n) (g : G) (hN : N ≤ MulAut.conj g • H) (n : N) :
    g • c ((equivSMul (MulAut.conj g) H).symm (inclusion hN n)) = n := by
  have hx : (equivSMul (MulAut.conj g) H).symm (inclusion hN n) = inclusion hNH (g⁻¹ • n) := by
    apply Subtype.ext
    rw [equivSMul_symm_apply_coe (MulAut.conj g) H (inclusion hN n)]
    simp [coe_conjugationAction_smul]
  rw [hx, hn, smul_inv_smul]

end LocalDictionary

/-! ### Global complements and normalized multiplicative crossed homomorphisms -/

/-- A normalized multiplicative crossed homomorphism `G → N` has complementary `1`-locus, without
any commutativity assumption on `N`. -/
theorem isComplement'_oneLocus {c : G → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c n = n) : N.IsComplement' hc.oneLocus := by
  rw [← isLocalComplement_top_iff, ← map_subgroupOf_eq_of_le (le_top : hc.oneLocus ≤ ⊤),
    ← hc.oneLocus_comp_subtype]
  exact isLocalComplement_map_oneLocus le_top (hc.comp_subtype ⊤) hn

/-- Recovering the crossed projection from the `1`-locus returns the original normalized
multiplicative crossed homomorphism. -/
theorem crossedProjection_oneLocus {c : G → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c n = n) (g : G) :
    (isComplement'_oneLocus hc hn).crossedProjection g = c g := by
  have hl := isLocalComplement_map_oneLocus (le_top : N ≤ ⊤) (hc.comp_subtype ⊤) hn
  have hle : (hc.comp_subtype ⊤).oneLocus.map (⊤ : Subgroup G).subtype ≤ hc.oneLocus := by
    rw [hc.oneLocus_comp_subtype, map_subgroupOf_eq_of_le le_top]
  exact (hl.leftProjection_eq_crossedProjection (isComplement'_oneLocus hc hn) hle
    ⟨g, mem_top g⟩).symm.trans (leftProjection_map_oneLocus le_top (hc.comp_subtype ⊤) hn
      ⟨g, mem_top g⟩)

variable (N) in
/-- Complements of a (not necessarily abelian) normal subgroup `N` correspond bijectively to
normalized multiplicative crossed homomorphisms `G → N`. -/
noncomputable def mulCrossedHomEquiv :
    {D : Subgroup G // N.IsComplement' D} ≃
      {c : G → N // TauCeti.IsMulCrossedHom c ∧ ∀ n : N, c n = n} where
  toFun D := ⟨D.property.crossedProjection,
    D.property.isMulCrossedHom_crossedProjection, D.property.crossedProjection_coe⟩
  invFun c := ⟨c.property.1.oneLocus, isComplement'_oneLocus c.property.1 c.property.2⟩
  left_inv D := Subtype.ext D.property.oneLocus_crossedProjection
  right_inv c := Subtype.ext (funext (crossedProjection_oneLocus c.property.1 c.property.2))

/-- The normalized multiplicative crossed homomorphism attached to a complement is its crossed
projection. -/
@[simp]
theorem mulCrossedHomEquiv_apply (D : {D : Subgroup G // N.IsComplement' D}) (g : G) :
    (N.mulCrossedHomEquiv D).val g = D.property.crossedProjection g := (rfl)

/-- The complement attached to a normalized multiplicative crossed homomorphism is its `1`-locus. -/
@[simp]
theorem mulCrossedHomEquiv_symm_apply
    (c : {c : G → N // TauCeti.IsMulCrossedHom c ∧ ∀ n : N, c n = n}) :
    (N.mulCrossedHomEquiv.symm c).val = c.property.1.oneLocus := (rfl)

/-- A normal subgroup `N` has a complement in `G` if and only if it admits a multiplicative crossed
homomorphism `G → N` for conjugation that restricts to the identity on `N`. -/
theorem exists_isComplement'_iff_isMulCrossedHom :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      ∃ c : G → N, TauCeti.IsMulCrossedHom c ∧ ∀ n : N, c n = n :=
  ⟨fun ⟨_, hD⟩ => ⟨hD.crossedProjection, hD.isMulCrossedHom_crossedProjection,
    hD.crossedProjection_coe⟩,
    fun ⟨_, hc, hn⟩ => ⟨hc.oneLocus, isComplement'_oneLocus hc hn⟩⟩

/-! ### Abelian normal subgroups: additive cocycles -/

section Commutative

variable [IsMulCommutative N]

/-- **Conjugation by an element of `N`.** For `a ∈ N`, the left projection along the local
complement `a K a⁻¹` of `N` in `H` is the left projection along `K` times the principal crossed
map `x ↦ x • a / a`. -/
theorem IsLocalComplement.leftProjection_conj_coe_smul {K H : Subgroup G}
    (h : N.IsLocalComplement K H) (a : N) (x : H) :
    (h.conj_smul_of_mem (h.left_le a.property)).leftProjection x =
      h.leftProjection x * (x • a / a) := by
  -- `N` is abelian, so `x • a` can be moved past `c x` inside `N`
  have hN : h.leftProjection x * (x • a / a) = x • a * h.leftProjection x * a⁻¹ := by
    rw [div_eq_mul_inv, mul_left_comm, mul_assoc]
  rw [leftProjection_eq_iff, mem_pointwise_smul_iff_inv_smul_mem, hN]
  convert (h.leftProjection_eq_iff x _).mp rfl using 1
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, coe_mul, coe_inv, Subgroup.smul_def,
    coe_conjugationAction_smul]
  group

/-- Two local complements `K` and `K'` of an abelian normal subgroup `N` in `H` are conjugate by
`a ∈ N` exactly when their left projections differ by the principal crossed map
`x ↦ x • a / a`. -/
theorem IsLocalComplement.eq_conj_smul_iff_leftProjection_eq {K H : Subgroup G}
    (h : N.IsLocalComplement K H) {K' : Subgroup G} (h' : N.IsLocalComplement K' H) (a : N) :
    K' = MulAut.conj (a : G) • K ↔
      ∀ x, h'.leftProjection x = h.leftProjection x * (x • a / a) := by
  have ha := h.conj_smul_of_mem (h.left_le a.property)
  constructor
  · rintro rfl x
    exact h.leftProjection_conj_coe_smul a x
  · intro hK
    have hmem (x : H) : (x : G) ∈ K' ↔ (x : G) ∈ MulAut.conj (a : G) • K := by
      rw [← h'.leftProjection_eq_one_iff, ← ha.leftProjection_eq_one_iff, hK,
        h.leftProjection_conj_coe_smul]
    ext g
    exact ⟨fun hg => (hmem ⟨g, h'.right_le hg⟩).mp hg,
      fun hg => (hmem ⟨g, ha.right_le hg⟩).mpr hg⟩

/-- **Conjugation by an element of `N`.** For `a ∈ N`, the crossed projection along `a D a⁻¹` is
the crossed projection along `D` times the principal crossed map `x ↦ x • a / a`. This is the
case `H = ⊤` of `Subgroup.IsLocalComplement.leftProjection_conj_coe_smul`. -/
theorem IsComplement'.crossedProjection_conj_coe_smul {D : Subgroup G} (h : N.IsComplement' D)
    (a : N) (x : G) :
    (h.conj_smul a).crossedProjection x = h.crossedProjection x * (x • a / a) := by
  have hl := isLocalComplement_top_iff.mpr h
  have hx := hl.leftProjection_conj_coe_smul a ⟨x, mem_top x⟩
  rwa [hl.leftProjection_top_eq_crossedProjection,
    (hl.conj_smul_of_mem (mem_top _)).leftProjection_top_eq_crossedProjection,
    Subgroup.smul_def] at hx

/-- Two complements of an abelian normal subgroup `N` are conjugate by `a ∈ N` exactly when
their crossed projections differ by the principal crossed map `x ↦ x • a / a`. This is the case
`H = ⊤` of `Subgroup.IsLocalComplement.eq_conj_smul_iff_leftProjection_eq`. -/
theorem IsComplement'.eq_conj_smul_iff_crossedProjection_eq {D : Subgroup G}
    (h : N.IsComplement' D) {D' : Subgroup G} (h' : N.IsComplement' D') (a : N) :
    D' = MulAut.conj (a : G) • D ↔
      ∀ x, h'.crossedProjection x = h.crossedProjection x * (x • a / a) := by
  rw [(isLocalComplement_top_iff.mpr h).eq_conj_smul_iff_leftProjection_eq
    (isLocalComplement_top_iff.mpr h') a]
  simp only [IsLocalComplement.leftProjection_top_eq_crossedProjection, Subgroup.smul_def]
  exact ⟨fun hD x => hD ⟨x, mem_top x⟩, fun hD x => hD x⟩

/-- A normalized additive crossed map has complementary zero locus. This is the
kernel construction for normalized multiplicative crossed maps read on `Additive N`. -/
theorem isComplement'_zeroLocus {c : G → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c n = Additive.ofMul n) : N.IsComplement' (zeroLocus hc) := by
  rw [zeroLocus_eq_oneLocus]
  exact isComplement'_oneLocus hc.isMulCrossedHom_toMul fun n => by simp [hn]

/-- Recovering the projection from the zero locus returns the original normalized map. -/
theorem crossedProjection_zeroLocus {c : G → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c n = Additive.ofMul n) (g : G) :
    (isComplement'_zeroLocus hc hn).crossedProjection g = (c g).toMul := by
  obtain ⟨⟨n, d⟩, rfl⟩ := (isComplement'_zeroLocus hc hn).surjective g
  rw [IsComplement'.crossedProjection_mul]
  rw [hc]
  simp [(mem_zeroLocus hc).mp d.property, hn]

variable (N) in
/-- Complements correspond bijectively to normalized crossed maps, read additively. -/
noncomputable def crossedProjectionEquiv :
    {D : Subgroup G // N.IsComplement' D} ≃
      {c : G → Additive N // IsCocycle₁ c ∧ ∀ n : N, c n = Additive.ofMul n} where
  toFun D := ⟨fun g => Additive.ofMul (D.property.crossedProjection g),
    (fun g k => congrArg Additive.ofMul (D.property.isMulCocycle₁_crossedProjection g k)),
    fun n => congrArg Additive.ofMul (D.property.crossedProjection_coe n)⟩
  invFun c := ⟨zeroLocus c.property.1, isComplement'_zeroLocus c.property.1 c.property.2⟩
  left_inv D := by
    apply Subtype.ext
    ext g
    simp [IsComplement'.crossedProjection_eq_one_iff]
  right_inv c := by
    apply Subtype.ext
    funext g
    exact congrArg Additive.ofMul (crossedProjection_zeroLocus c.property.1 c.property.2 g)

@[simp]
theorem crossedProjectionEquiv_apply
    (D : {D : Subgroup G // N.IsComplement' D}) (g : G) :
    (N.crossedProjectionEquiv D).val g = Additive.ofMul (D.property.crossedProjection g) := (rfl)

@[simp]
theorem crossedProjectionEquiv_symm_apply
    (c : {c : G → Additive N // IsCocycle₁ c ∧ ∀ n : N, c n = Additive.ofMul n}) :
    (N.crossedProjectionEquiv.symm c).val = zeroLocus c.property.1 := (rfl)

section Local

variable {K H : Subgroup G} (hNH : N ≤ H)

/-- A normalized additive crossed map on an intermediate subgroup `H ≥ N` has as zero locus a
local complement of `N` in `H`. -/
theorem isLocalComplement_map_zeroLocus {c : H → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) :
    N.IsLocalComplement ((zeroLocus hc).map H.subtype) H := by
  rw [zeroLocus_eq_oneLocus]
  exact isLocalComplement_map_oneLocus hNH hc.isMulCrossedHom_toMul fun n => by simp [hn]

/-- The left projection along the zero locus of a normalized additive crossed map is the
crossed map itself. -/
theorem leftProjection_map_zeroLocus {c : H → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) (x : H) :
    (isLocalComplement_map_zeroLocus hNH hc hn).leftProjection x = (c x).toMul := by
  rw [(isLocalComplement_map_zeroLocus hNH hc hn).leftProjection_eq_iff, zeroLocus_eq_oneLocus]
  exact coe_inv_mul_mem_map_oneLocus hNH hc.isMulCrossedHom_toMul (fun n => by simp [hn]) x

/-- The left projection of a local complement, read additively, is an additive crossed map. -/
theorem IsLocalComplement.isCocycle₁_leftProjection (h : N.IsLocalComplement K H) :
    IsCocycle₁ fun x => Additive.ofMul (h.leftProjection x) :=
  fun x y => congrArg Additive.ofMul (h.isMulCocycle₁_leftProjection x y)

/-- The zero locus of the left projection of a local complement is that local complement. -/
@[simp]
theorem IsLocalComplement.map_zeroLocus_leftProjection (h : N.IsLocalComplement K H) :
    (zeroLocus h.isCocycle₁_leftProjection).map H.subtype = K := by
  rw [zeroLocus_eq_oneLocus]
  exact h.map_oneLocus_leftProjection

variable (N H) in
/-- Local complements of `N` in an intermediate subgroup `H ≥ N` correspond bijectively to
normalized crossed maps `H → N`, read additively. -/
noncomputable def localCrossedProjectionEquiv :
    {K : Subgroup G // N.IsLocalComplement K H} ≃
      {c : H → Additive N // IsCocycle₁ c ∧ ∀ n : N, c (inclusion hNH n) = Additive.ofMul n} where
  toFun K := ⟨fun x => Additive.ofMul (K.property.leftProjection x),
    K.property.isCocycle₁_leftProjection,
    fun n => congrArg Additive.ofMul (K.property.leftProjection_left n)⟩
  invFun c := ⟨(zeroLocus c.property.1).map H.subtype,
    isLocalComplement_map_zeroLocus hNH c.property.1 c.property.2⟩
  left_inv K := Subtype.ext K.property.map_zeroLocus_leftProjection
  right_inv c := by
    apply Subtype.ext
    funext x
    exact congrArg Additive.ofMul (leftProjection_map_zeroLocus hNH c.property.1 c.property.2 x)

/-- The crossed map of a local complement is its left projection, read additively. -/
@[simp]
theorem localCrossedProjectionEquiv_apply (K : {K : Subgroup G // N.IsLocalComplement K H})
    (x : H) :
    (localCrossedProjectionEquiv N H hNH K).val x =
      Additive.ofMul (K.property.leftProjection x) := (rfl)

/-- The local complement of a normalized crossed map is its zero locus, viewed in `G`. -/
@[simp]
theorem localCrossedProjectionEquiv_symm_apply
    (c : {c : H → Additive N // IsCocycle₁ c ∧ ∀ n : N, c (inclusion hNH n) = Additive.ofMul n}) :
    ((localCrossedProjectionEquiv N H hNH).symm c).val = (zeroLocus c.property.1).map H.subtype :=
  (rfl)

/-- Adding the principal crossed map `x ↦ x • a - a` of `a ∈ N` to a crossed map `H → N`, read
additively, gives a crossed map. -/
theorem isCocycle₁_add_smul_sub {c : H → Additive N} (hc : IsCocycle₁ c) (a : N) :
    IsCocycle₁ fun x => c x + (x • Additive.ofMul a - Additive.ofMul a) :=
  hc.add (IsCoboundary₁.isCocycle₁ ⟨Additive.ofMul a, fun _ => rfl⟩)

/-- Adding the principal crossed map `x ↦ x • a - a` of `a ∈ N` to a crossed map `H → N` which is
the identity on `N` gives a map which is again the identity on `N`, since `N` acts trivially on
itself. -/
theorem apply_inclusion_add_smul_sub {c : H → Additive N}
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) (a n : N) :
    c (inclusion hNH n) + (inclusion hNH n • Additive.ofMul a - Additive.ofMul a) =
      Additive.ofMul n := by
  simp [hn, Subgroup.smul_def, ← Additive.ofMul_smul, conjugationAction_coe_smul]

/-- **Principal crossed maps conjugate zero loci.** Let `c : H → N` be a crossed map on an
intermediate subgroup `H ≥ N` which is the identity on `N`, read additively, and let `a ∈ N`. The
zero locus of `c` plus the principal crossed map `x ↦ x • a - a` is the conjugate `a K a⁻¹` of the
zero locus `K` of `c`, both viewed in `G`. -/
theorem map_subtype_zeroLocus_add_smul_sub {c : H → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) (a : N) :
    (zeroLocus (isCocycle₁_add_smul_sub hc a)).map H.subtype =
      MulAut.conj (a : G) • (zeroLocus hc).map H.subtype := by
  refine ((isLocalComplement_map_zeroLocus hNH hc hn).eq_conj_smul_iff_leftProjection_eq
    (isLocalComplement_map_zeroLocus hNH (isCocycle₁_add_smul_sub hc a)
      (apply_inclusion_add_smul_sub hNH hn a)) a).mpr fun x => ?_
  rw [leftProjection_map_zeroLocus hNH hc hn,
    leftProjection_map_zeroLocus hNH _ (apply_inclusion_add_smul_sub hNH hn a), toMul_add,
    toMul_sub, Additive.toMul_smul, toMul_ofMul]
end Local

end Commutative

end Subgroup
