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
(`Subgroup.IsComplement'.eq_conj_smul_iff_crossedProjection_eq`), and reading `N` as `Additive N`
identifies normalized crossed maps with normalized `groupCohomology.IsCocycle₁` maps
(`Subgroup.crossedProjectionEquiv`, `Subgroup.localCrossedProjectionEquiv`).

The conjugation action is explicit rather than a global instance.

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
/-- The projection of a product of the two factors is its normal component. -/
@[simp]
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
  h.isMulCrossedHom_crossedProjection.map_mul

omit [N.Normal] in
/-- Exactly the elements of the complement have trivial crossed projection. -/
@[simp]
theorem crossedProjection_eq_one_iff (g : G) : h.crossedProjection g = 1 ↔ g ∈ D := by
  rw [← Subtype.coe_inj]
  exact h.coe_equiv_fst_eq_one_iff_mem N.one_mem

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
    convert (h.equiv (g⁻¹ * x * g)).2.2 using 1
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
  rw [h.crossedProjection_conj_smul, hc.map_mul, h.crossedProjection_coe, hc.map_mul,
    ← coe_inv, h.crossedProjection_coe, mul_smul, smul_mul', smul_mul', coe_inv, smul_inv_smul,
    smul_inv_smul, conjugationAction_coe_smul_eq]
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

section Commutative

variable [IsMulCommutative N]

/-- **Conjugation by an element of `N`.** For `a ∈ N` in an abelian normal subgroup `N`, the crossed
projection along `a D a⁻¹` is the crossed projection along `D` times the principal crossed map
`x ↦ x • a / a`. -/
theorem crossedProjection_conj_coe_smul (a : N) (x : G) :
    (h.conj_smul a).crossedProjection x = h.crossedProjection x * (x • a / a) := by
  rw [h.crossedProjection_conj_coe_smul_eq, div_eq_mul_inv]
  ac_rfl

/-- Two complements of an abelian normal subgroup `N` are conjugate by `a ∈ N` exactly when
their crossed projections differ by the principal crossed map `x ↦ x • a / a`. -/
theorem eq_conj_smul_iff_crossedProjection_eq {D' : Subgroup G} (h' : N.IsComplement' D')
    (a : N) : D' = MulAut.conj (a : G) • D ↔
      ∀ x, h'.crossedProjection x = h.crossedProjection x * (x • a / a) := by
  rw [h.eq_conj_smul_iff_crossedProjection_eq_mul_inv h' a]
  refine forall_congr' fun x => eq_iff_eq_cancel_left.mpr ?_
  rw [div_eq_mul_inv]
  ac_rfl

end Commutative

end IsComplement'

/-! ### Global complements and normalized multiplicative crossed homomorphisms -/

/-- A normalized multiplicative crossed homomorphism `G → N` has complementary `1`-locus, without
any commutativity assumption on `N`. -/
theorem isComplement'_oneLocus {c : G → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c n = n) : N.IsComplement' hc.oneLocus := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro g hg
    have hz : c g = 1 := hc.mem_oneLocus.mp hg.2
    rw [hn ⟨g, hg.1⟩] at hz
    exact congrArg Subtype.val hz
  · apply Set.eq_univ_iff_forall.mpr
    intro g
    let n : N := c g
    refine ⟨n, n.property, (n : G)⁻¹ * g, hc.mem_oneLocus.mpr ?_, by simp⟩
    rw [← coe_inv, hc.map_mul, hn, coe_inv, conjugationAction_inv_coe_smul_self, mul_inv_cancel]

/-- Recovering the crossed projection from the `1`-locus returns the original normalized
multiplicative crossed homomorphism. -/
theorem crossedProjection_oneLocus {c : G → N} (hc : TauCeti.IsMulCrossedHom c)
    (hn : ∀ n : N, c n = n) (g : G) :
    (isComplement'_oneLocus hc hn).crossedProjection g = c g := by
  obtain ⟨⟨n, d⟩, rfl⟩ := (isComplement'_oneLocus hc hn).surjective g
  rw [IsComplement'.crossedProjection_mul, hc.map_mul, hc.mem_oneLocus.mp d.property,
    MulDistribMulAction.smul_one, one_mul, hn]

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

/-! ### Local complements and normalized crossed homomorphisms on an intermediate subgroup -/

namespace IsLocalComplement

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
  h.isMulCrossedHom_leftProjection.map_mul

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

/-! ### Abelian normal subgroups: additive cocycles -/

section Commutative

variable [IsMulCommutative N]

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

end Local

end Commutative

end Subgroup
