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

For a normal subgroup `N` of `G` (not necessarily abelian), a complement determines a crossed map
`c : G → N`, satisfying `c (g * k) = g • c k * c g` for the ambient conjugation action, which
restricts to the identity on `N`. Conversely, the locus `groupCohomology.oneLocus` where such a map
equals `1` is a complement (`Subgroup.isComplement'_oneLocus`), and the two constructions are
mutually inverse (`Subgroup.mulCrossedProjectionEquiv`). Nothing here requires finiteness of `G` or
commutativity of `N`; the reversed factor order `c (g * k) = c g * (g • c k)` holds for every pair
of elements precisely when `N` is abelian
(`Subgroup.IsComplement'.forall_crossedProjection_mul_eq_iff_isMulCommutative`).

The same dictionary holds for an intermediate subgroup `H ≥ N`: the left projection along a local
complement of `N` in `H` is a normalized crossed map `H → N`, its `oneLocus` (or `zeroLocus` when
`N` is abelian) is a local complement, and the two constructions are mutually inverse
(`Subgroup.localMulCrossedProjectionEquiv`, `Subgroup.localCrossedProjectionEquiv`). Restricting a
normalized crossed map from `H` to an intermediate subgroup `N ≤ L ≤ H` gives a normalized crossed
map on `L` whose kernel is the intersection with `L`, matching `Subgroup.IsLocalComplement.restrict`
(`Subgroup.localCrossedProjectionEquiv_restrict`). Conjugating a normalized crossed map `c` on `H`
by `g` gives the normalized crossed map `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`
(`Subgroup.smul_apply_equivSMul_symm_inclusion`), whose kernel is conjugated by `g`.

Conjugating a global or local complement by `a ∈ N` twists its crossed projection `c` to the
normalized crossed map `x ↦ x • a * c x * a⁻¹`
(`Subgroup.IsComplement'.crossedProjection_conj_coe_smul_eq_mul`,
`Subgroup.IsLocalComplement.leftProjection_conj_coe_smul_eq_mul`), which for abelian `N` is `c`
times the principal crossed map `x ↦ x • a / a`. Adding `x ↦ x • a - a` to a normalized additive
crossed map on `G` or `H` therefore conjugates its zero locus by `a`
(`Subgroup.zeroLocus_add_smul_sub`, `Subgroup.map_subtype_zeroLocus_add_smul_sub`).

The conjugation action is explicit rather than a global instance. The additive coefficient action
uses `Additive.distribMulAction`, and kernels use `groupCohomology.oneLocus` and
`groupCohomology.zeroLocus`.

## References

* W. Gaschütz, Zur Erweiterungstheorie der endlichen Gruppen, J. reine angew. Math.
  190 (1952), 93–107, for normalized crossed maps in complement theory.
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
/-- When `d ∈ D` and `g * d⁻¹ ∈ N`, the crossed projection of `g` is `g * d⁻¹`. -/
theorem crossedProjection_eq_of_mul_inv_mem {g d : G} (hd : d ∈ D) (hn : g * d⁻¹ ∈ N) :
    (h.crossedProjection g : G) = g * d⁻¹ := by
  have hg : g = ((⟨g * d⁻¹, hn⟩ : N) : G) * (⟨d, hd⟩ : D) := (inv_mul_cancel_right g d).symm
  conv_lhs => rw [hg]
  exact congrArg Subtype.val (h.crossedProjection_mul ⟨g * d⁻¹, hn⟩ ⟨d, hd⟩)

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

theorem coe_crossedProjection (g : G) :
    (h.crossedProjection g : G) = g * (h.quotientSplitting (g : G ⧸ N))⁻¹ := by
  obtain ⟨⟨n, d⟩, rfl⟩ := h.surjective g
  have hn : (n : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr n.property
  simp [hn]

/-- **The crossed identity without commutativity.** For any normal subgroup `N`, the crossed
projection satisfies `c (g * k) = g • c k * c g`. -/
theorem crossedProjection_mul_apply (g k : G) :
    h.crossedProjection (g * k) = g • h.crossedProjection k * h.crossedProjection g := by
  apply Subtype.ext
  simp only [coe_crossedProjection, coe_mul, coe_conjugationAction_smul,
    QuotientGroup.mk_mul, map_mul]
  group

/-- The projection satisfies the crossed identity for ambient conjugation. -/
theorem isMulCocycle₁_crossedProjection [IsMulCommutative N] :
    IsMulCocycle₁ h.crossedProjection :=
  h.crossedProjection_mul_apply

omit [N.Normal] in
/-- Exactly the elements of the complement have trivial crossed projection. -/
@[simp]
theorem crossedProjection_eq_one_iff (g : G) : h.crossedProjection g = 1 ↔ g ∈ D := by
  rw [← Subtype.coe_inj]
  exact h.coe_equiv_fst_eq_one_iff_mem N.one_mem

/-- The one locus of the crossed projection along `D` is `D`. -/
@[simp]
theorem oneLocus_crossedProjection : oneLocus h.crossedProjection_mul_apply = D := by
  ext g
  rw [mem_oneLocus, h.crossedProjection_eq_one_iff]

/-- **The reversed factor order holds precisely when `N` is abelian.** For a complement `D` of a
normal subgroup `N`, the identity `c (g * k) = c g * (g • c k)` holds for all `g, k : G` if and
only if `N` is commutative. -/
theorem forall_crossedProjection_mul_eq_iff_isMulCommutative :
    (∀ g k : G, h.crossedProjection (g * k) =
        h.crossedProjection g * (g • h.crossedProjection k)) ↔
      IsMulCommutative N := by
  refine ⟨fun hrev => ⟨⟨fun n m => Subtype.ext ?_⟩⟩, fun _ g k => ?_⟩
  · have hnm := congrArg Subtype.val (hrev n m)
    rw [← coe_mul, h.crossedProjection_coe, h.crossedProjection_coe, h.crossedProjection_coe,
      coe_mul, coe_mul, coe_conjugationAction_smul] at hnm
    have hm : (m : G) = n * m * (n : G)⁻¹ := mul_left_cancel hnm
    simpa [mul_assoc] using congrArg (· * (n : G)) hm.symm
  · rw [h.crossedProjection_mul_apply, mul_comm]

omit [N.Normal] in
/-- Restricting a global complement `D` to an intermediate subgroup `H ≥ N` restricts its crossed
projection to the left projection along `D ⊓ H`. -/
@[simp]
theorem leftProjection_isLocalComplement_inf {H : Subgroup G} [(N.subgroupOf H).Normal]
    (hNH : N ≤ H) (x : H) :
    (h.isLocalComplement_inf hNH).leftProjection x = h.crossedProjection x := by
  rw [IsLocalComplement.leftProjection_eq_iff, mem_inf]
  refine ⟨?_, H.mul_mem (H.inv_mem (hNH (h.crossedProjection x).property)) x.property⟩
  have hx : (h.crossedProjection x : G)⁻¹ * x = (h.equiv x).2 :=
    (eq_inv_mul_iff_mul_eq.mpr (h.equiv_fst_mul_equiv_snd x)).symm
  rw [hx]
  exact (h.equiv x).2.property

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

/-- **Conjugation by an element of `N` without commutativity.** For `a ∈ N`, the crossed projection
along `a D a⁻¹` sends `x` to `x • a * c x * a⁻¹`. -/
theorem crossedProjection_conj_coe_smul_eq_mul (a : N) (x : G) :
    (h.conj_smul a).crossedProjection x = x • a * h.crossedProjection x * a⁻¹ := by
  rw [h.crossedProjection_conj_smul, h.crossedProjection_mul_apply, h.crossedProjection_mul_apply,
    h.crossedProjection_coe, ← coe_inv, h.crossedProjection_coe]
  apply Subtype.ext
  simp only [coe_mul, coe_conjugationAction_smul, coe_inv]
  group

/-- Two complements of a normal subgroup `N` are conjugate by `a ∈ N` exactly when their crossed
projections are related by `c' x = x • a * c x * a⁻¹`. -/
theorem eq_conj_smul_iff_crossedProjection_eq_mul {D' : Subgroup G} (h' : N.IsComplement' D')
    (a : N) : D' = MulAut.conj (a : G) • D ↔
      ∀ x, h'.crossedProjection x = x • a * h.crossedProjection x * a⁻¹ := by
  constructor
  · rintro rfl x
    exact h.crossedProjection_conj_coe_smul_eq_mul a x
  · intro hD
    ext x
    rw [← h'.crossedProjection_eq_one_iff, ← (h.conj_smul a).crossedProjection_eq_one_iff, hD,
      h.crossedProjection_conj_coe_smul_eq_mul]

variable [IsMulCommutative N]

/-- **Conjugation by an element of `N`.** For `a ∈ N`, the crossed projection along `a D a⁻¹` is
the crossed projection along `D` times the principal crossed map `x ↦ x • a / a`. -/
theorem crossedProjection_conj_coe_smul (a : N) (x : G) :
    (h.conj_smul a).crossedProjection x = h.crossedProjection x * (x • a / a) := by
  rw [h.crossedProjection_conj_coe_smul_eq_mul, div_eq_mul_inv]
  ac_rfl

/-- Two complements of an abelian normal subgroup `N` are conjugate by `a ∈ N` exactly when
their crossed projections differ by the principal crossed map `x ↦ x • a / a`. -/
theorem eq_conj_smul_iff_crossedProjection_eq {D' : Subgroup G} (h' : N.IsComplement' D')
    (a : N) : D' = MulAut.conj (a : G) • D ↔
      ∀ x, h'.crossedProjection x = h.crossedProjection x * (x • a / a) := by
  rw [h.eq_conj_smul_iff_crossedProjection_eq_mul h' a]
  refine forall_congr' fun x => eq_iff_eq_cancel_left.mpr ?_
  rw [div_eq_mul_inv]
  ac_rfl

end IsComplement'

/-! ### Global complements and normalized crossed maps without commutativity -/

/-- **A normalized crossed map has complementary one locus**, without any commutativity assumption
on `N`. -/
theorem isComplement'_oneLocus {c : G → N} (hc : ∀ g k : G, c (g * k) = g • c k * c g)
    (hn : ∀ n : N, c n = n) : N.IsComplement' (oneLocus hc) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro g hg
    have h1 : c g = 1 := (mem_oneLocus hc).mp hg.2
    rw [hn ⟨g, hg.1⟩] at h1
    exact congrArg Subtype.val h1
  · apply Set.eq_univ_iff_forall.mpr
    intro g
    let n : N := c g
    refine ⟨n, n.property, (n : G)⁻¹ * g, ?_, by simp⟩
    apply (mem_oneLocus hc).mpr
    rw [hc, ← coe_inv, hn n⁻¹, coe_inv, conjugationAction_coe_inv_smul_self]
    exact mul_inv_cancel n

/-- Recovering the crossed projection from the one locus returns the original normalized map. -/
@[simp]
theorem crossedProjection_oneLocus {c : G → N} (hc : ∀ g k : G, c (g * k) = g • c k * c g)
    (hn : ∀ n : N, c n = n) (g : G) :
    (isComplement'_oneLocus hc hn).crossedProjection g = c g := by
  obtain ⟨⟨n, d⟩, rfl⟩ := (isComplement'_oneLocus hc hn).surjective g
  rw [IsComplement'.crossedProjection_mul, hc, (mem_oneLocus hc).mp d.property, smul_one, one_mul,
    hn]

variable (N) in
/-- **Complements of a normal subgroup `N` correspond bijectively to normalized crossed maps
`G → N`**, without any commutativity assumption on `N`. -/
noncomputable def mulCrossedProjectionEquiv :
    {D : Subgroup G // N.IsComplement' D} ≃
      {c : G → N // (∀ g k : G, c (g * k) = g • c k * c g) ∧ ∀ n : N, c n = n} where
  toFun D := ⟨D.property.crossedProjection, D.property.crossedProjection_mul_apply,
    D.property.crossedProjection_coe⟩
  invFun c := ⟨oneLocus c.property.1, isComplement'_oneLocus c.property.1 c.property.2⟩
  left_inv D := Subtype.ext D.property.oneLocus_crossedProjection
  right_inv c := Subtype.ext (funext (crossedProjection_oneLocus c.property.1 c.property.2))

/-- The crossed map of a complement is its crossed projection. -/
@[simp]
theorem mulCrossedProjectionEquiv_apply (D : {D : Subgroup G // N.IsComplement' D}) (g : G) :
    (N.mulCrossedProjectionEquiv D).val g = D.property.crossedProjection g := (rfl)

/-- The complement associated to a normalized crossed map is its one locus. -/
@[simp]
theorem mulCrossedProjectionEquiv_symm_apply
    (c : {c : G → N // (∀ g k : G, c (g * k) = g • c k * c g) ∧ ∀ n : N, c n = n}) :
    (N.mulCrossedProjectionEquiv.symm c).val = oneLocus c.property.1 := (rfl)

/-- A normal subgroup `N` (not necessarily abelian) has a complement in `G` iff there is a crossed
map `G → N` for conjugation which restricts to the identity on `N`. -/
theorem exists_isComplement'_iff_crossedProjection_mul :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      ∃ c : G → N, (∀ g k : G, c (g * k) = g • c k * c g) ∧ ∀ n : N, c n = n :=
  ⟨fun ⟨_, hD⟩ => ⟨hD.crossedProjection, hD.crossedProjection_mul_apply, hD.crossedProjection_coe⟩,
    fun ⟨_, hc, hn⟩ => ⟨oneLocus hc, isComplement'_oneLocus hc hn⟩⟩

/-- Twisting a crossed map `c : G → N` by `a ∈ N` as `x ↦ x • a * c x * a⁻¹` preserves the crossed
identity, without any commutativity assumption on `N`. -/
theorem apply_mul_smul_mul_inv {c : G → N} (hc : ∀ g k : G, c (g * k) = g • c k * c g) (a : N)
    (g k : G) :
    (g * k) • a * c (g * k) * a⁻¹ = g • (k • a * c k * a⁻¹) * (g • a * c g * a⁻¹) := by
  rw [hc, smul_mul', smul_mul', mul_smul, smul_inv']
  group

/-- Twisting a map `c : G → N` by `a ∈ N` as `x ↦ x • a * c x * a⁻¹` preserves a fixed point
`c n = n` in `N`. -/
theorem smul_mul_inv_coe {c : G → N} {n : N} (hn : c n = n) (a : N) :
    (n : G) • a * c n * a⁻¹ = n := by
  apply Subtype.ext
  rw [hn, coe_mul, coe_mul, coe_conjugationAction_smul, coe_inv]
  group

/-- Twisting a normalized crossed map `c : G → N` to `x ↦ x • a * c x * a⁻¹` conjugates its one
locus by `a ∈ N`. -/
theorem oneLocus_smul_mul_inv {c : G → N} (hc : ∀ g k : G, c (g * k) = g • c k * c g)
    (hn : ∀ n : N, c n = n) (a : N) :
    oneLocus (f := fun x : G => x • a * c x * a⁻¹) (apply_mul_smul_mul_inv hc a) =
      MulAut.conj (a : G) • oneLocus hc := by
  have hD := isComplement'_oneLocus hc hn
  ext x
  rw [mem_oneLocus, ← (hD.conj_smul a).crossedProjection_eq_one_iff,
    hD.crossedProjection_conj_coe_smul_eq_mul, crossedProjection_oneLocus hc hn]

/-! ### Local crossed projections without commutativity -/

namespace IsLocalComplement

/-- **The local crossed identity without commutativity.** The left projection of a local complement
`K` of `N` in `H` satisfies `c (x * y) = x • c y * c x` for the conjugation action of `H` on `N`. -/
theorem leftProjection_mul_apply {K H : Subgroup G} (h : N.IsLocalComplement K H) (x y : H) :
    h.leftProjection (x * y) = x • h.leftProjection y * h.leftProjection x := by
  rw [h.leftProjection_eq_iff]
  have hx := (h.leftProjection_eq_iff x _).mp rfl
  have hy := (h.leftProjection_eq_iff y _).mp rfl
  simp only [coe_mul, Subgroup.smul_def, coe_conjugationAction_smul]
  convert K.mul_mem hx hy using 1
  group

/-- The left projection of a local complement `K` of `N` in `H` satisfies the crossed identity
for the conjugation action of `H` on `N`. -/
theorem isMulCocycle₁_leftProjection [IsMulCommutative N] {K H : Subgroup G}
    (h : N.IsLocalComplement K H) : IsMulCocycle₁ h.leftProjection :=
  h.leftProjection_mul_apply

/-- For a local complement `K` of a normal subgroup `N` in `H`, the reversed factor order
`c (x * y) = c x * (x • c y)` holds for all `x, y : H` if and only if `N` is commutative. -/
theorem forall_leftProjection_mul_eq_iff_isMulCommutative {K H : Subgroup G}
    (h : N.IsLocalComplement K H) :
    (∀ x y : H, h.leftProjection (x * y) = h.leftProjection x * (x • h.leftProjection y)) ↔
      IsMulCommutative N := by
  refine ⟨fun hrev => ⟨⟨fun n m => Subtype.ext ?_⟩⟩, fun _ x y => ?_⟩
  · have hnm := congrArg Subtype.val
      (hrev ⟨n, h.left_le n.property⟩ ⟨m, h.left_le m.property⟩)
    have hmul : (⟨n, h.left_le n.property⟩ : H) * ⟨m, h.left_le m.property⟩ =
        ⟨(n * m : N), h.left_le (n * m).property⟩ := Subtype.ext rfl
    rw [hmul, h.leftProjection_left, h.leftProjection_left, h.leftProjection_left,
      coe_mul, coe_mul, Subgroup.smul_def, coe_mk, coe_conjugationAction_smul] at hnm
    have hm : (m : G) = n * m * (n : G)⁻¹ := mul_left_cancel hnm
    simpa [mul_assoc] using congrArg (· * (n : G)) hm.symm
  · rw [h.leftProjection_mul_apply, mul_comm]

/-- The one locus of the left projection of a local complement, viewed in `G`, is that local
complement. -/
@[simp]
theorem map_oneLocus_leftProjection {K H : Subgroup G} (h : N.IsLocalComplement K H) :
    (oneLocus h.leftProjection_mul_apply).map H.subtype = K := by
  ext g
  simp only [mem_map, mem_oneLocus, h.leftProjection_eq_one_iff, coe_subtype]
  exact ⟨fun ⟨_, hx, hxg⟩ => hxg ▸ hx, fun hg => ⟨⟨g, h.right_le hg⟩, hg, rfl⟩⟩

/-- **Local conjugation by an element of `N` without commutativity.** For `a ∈ N`, the left
projection along `a K a⁻¹` in `H` sends `x` to `x • a * c x * a⁻¹`. -/
theorem leftProjection_conj_coe_smul_eq_mul {K H : Subgroup G} (h : N.IsLocalComplement K H)
    (a : N) (x : H) :
    (h.conj_coe_smul a).leftProjection x = x • a * h.leftProjection x * a⁻¹ := by
  rw [(h.conj_coe_smul a).leftProjection_eq_iff, mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply]
  have hx : ((h.leftProjection x : N) : G)⁻¹ * x ∈ K := (h.leftProjection_eq_iff x _).mp rfl
  convert hx using 1
  simp only [coe_mul, Subgroup.smul_def, coe_conjugationAction_smul, coe_inv]
  group

/-- Two local complements of a normal subgroup `N` in `H` are conjugate by `a ∈ N` iff their left
projections are related by `c' x = x • a * c x * a⁻¹`. -/
theorem eq_conj_coe_smul_iff_leftProjection_eq_mul {K K' H : Subgroup G}
    (h : N.IsLocalComplement K H) (h' : N.IsLocalComplement K' H) (a : N) :
    K' = MulAut.conj (a : G) • K ↔
      ∀ x : H, h'.leftProjection x = x • a * h.leftProjection x * a⁻¹ := by
  constructor
  · rintro rfl x
    exact h.leftProjection_conj_coe_smul_eq_mul a x
  · intro hK
    ext g
    constructor
    · intro hg
      have hx : (h.conj_coe_smul a).leftProjection ⟨g, h'.right_le hg⟩ = 1 := by
        rw [h.leftProjection_conj_coe_smul_eq_mul, ← hK]
        exact (h'.leftProjection_eq_one_iff ⟨g, h'.right_le hg⟩).mpr hg
      exact ((h.conj_coe_smul a).leftProjection_eq_one_iff _).mp hx
    · intro hg
      have hgH : g ∈ H := (h.conj_coe_smul a).right_le hg
      have hx : h'.leftProjection ⟨g, hgH⟩ = 1 := by
        rw [hK, ← h.leftProjection_conj_coe_smul_eq_mul]
        exact ((h.conj_coe_smul a).leftProjection_eq_one_iff ⟨g, hgH⟩).mpr hg
      exact (h'.leftProjection_eq_one_iff ⟨g, hgH⟩).mp hx

/-- **Local conjugation by an element of abelian `N`.** For `a ∈ N`, the left projection along
`a K a⁻¹` in `H` is the left projection along `K` times the principal crossed map
`x ↦ x • a / a`. -/
theorem leftProjection_conj_coe_smul [IsMulCommutative N] {K H : Subgroup G}
    (h : N.IsLocalComplement K H) (a : N) (x : H) :
    (h.conj_coe_smul a).leftProjection x = h.leftProjection x * (x • a / a) := by
  rw [h.leftProjection_conj_coe_smul_eq_mul, div_eq_mul_inv]
  ac_rfl

/-- Two local complements of an abelian normal subgroup `N` in `H` are conjugate by `a ∈ N` iff
their left projections differ by the principal crossed map `x ↦ x • a / a`. -/
theorem eq_conj_coe_smul_iff_leftProjection_eq [IsMulCommutative N] {K K' H : Subgroup G}
    (h : N.IsLocalComplement K H) (h' : N.IsLocalComplement K' H) (a : N) :
    K' = MulAut.conj (a : G) • K ↔
      ∀ x : H, h'.leftProjection x = h.leftProjection x * (x • a / a) := by
  rw [h.eq_conj_coe_smul_iff_leftProjection_eq_mul h' a]
  refine forall_congr' fun x => eq_iff_eq_cancel_left.mpr ?_
  rw [div_eq_mul_inv]
  ac_rfl

end IsLocalComplement

section LocalNoncommutative

variable {K L H : Subgroup G} (hNH : N ≤ H)

/-- For a normalized crossed map `c : H → N`, `(c x)⁻¹ * x` lies in the one locus of `c` mapped
into `G`, without any commutativity assumption on `N`. -/
private theorem coe_inv_mul_mem_map_oneLocus {c : H → N}
    (hc : ∀ x y : H, c (x * y) = x • c y * c x)
    (hn : ∀ n : N, c (inclusion hNH n) = n) (x : H) :
    (c x : G)⁻¹ * x ∈ (oneLocus hc).map H.subtype := by
  let n : N := c x
  refine ⟨inclusion hNH n⁻¹ * x, (mem_oneLocus hc).mpr ?_, by simp [n]⟩
  rw [hc, hn, Subgroup.smul_def, coe_inclusion, coe_inv, conjugationAction_coe_inv_smul_self]
  exact mul_inv_cancel n

/-- **A normalized crossed map `H → N` has as one locus a local complement of `N` in `H`**,
without any commutativity assumption on `N`. -/
theorem isLocalComplement_map_oneLocus {c : H → N}
    (hc : ∀ x y : H, c (x * y) = x • c y * c x)
    (hn : ∀ n : N, c (inclusion hNH n) = n) :
    N.IsLocalComplement ((oneLocus hc).map H.subtype) H := by
  refine ⟨?_, le_antisymm (sup_le hNH (map_subtype_le _)) fun x hx => ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hgN, x, hx, rfl⟩
    have h1 : c (inclusion hNH ⟨x, hgN⟩) = 1 := (mem_oneLocus hc).mp hx
    rw [hn] at h1
    exact congrArg Subtype.val h1
  · have hk := coe_inv_mul_mem_map_oneLocus hNH hc hn ⟨x, hx⟩
    simpa using mul_mem_sup (c ⟨x, hx⟩).property hk

/-- The left projection along the one locus of a normalized crossed map on `H` recovers that
crossed map. -/
@[simp]
theorem leftProjection_map_oneLocus {c : H → N}
    (hc : ∀ x y : H, c (x * y) = x • c y * c x)
    (hn : ∀ n : N, c (inclusion hNH n) = n) (x : H) :
    (isLocalComplement_map_oneLocus hNH hc hn).leftProjection x = c x :=
  ((isLocalComplement_map_oneLocus hNH hc hn).leftProjection_eq_iff x _).mpr
    (coe_inv_mul_mem_map_oneLocus hNH hc hn x)

variable (N H) in
/-- **Local complements of `N` in `H ≥ N` correspond bijectively to normalized crossed maps
`H → N`**, without any commutativity assumption on `N`. -/
noncomputable def localMulCrossedProjectionEquiv :
    {K : Subgroup G // N.IsLocalComplement K H} ≃
      {c : H → N // (∀ x y : H, c (x * y) = x • c y * c x) ∧
        ∀ n : N, c (inclusion hNH n) = n} where
  toFun K := ⟨K.property.leftProjection, K.property.leftProjection_mul_apply,
    K.property.leftProjection_left⟩
  invFun c := ⟨(oneLocus c.property.1).map H.subtype,
    isLocalComplement_map_oneLocus hNH c.property.1 c.property.2⟩
  left_inv K := Subtype.ext K.property.map_oneLocus_leftProjection
  right_inv c := Subtype.ext (funext (leftProjection_map_oneLocus hNH c.property.1 c.property.2))

/-- The crossed map of a local complement is its left projection. -/
@[simp]
theorem localMulCrossedProjectionEquiv_apply (K : {K : Subgroup G // N.IsLocalComplement K H})
    (x : H) :
    (localMulCrossedProjectionEquiv N H hNH K).val x = K.property.leftProjection x := (rfl)

/-- The local complement of a normalized crossed map is its one locus, viewed in `G`. -/
@[simp]
theorem localMulCrossedProjectionEquiv_symm_apply
    (c : {c : H → N // (∀ x y : H, c (x * y) = x • c y * c x) ∧
      ∀ n : N, c (inclusion hNH n) = n}) :
    ((localMulCrossedProjectionEquiv N H hNH).symm c).val =
      (oneLocus c.property.1).map H.subtype := (rfl)

/-- A normal subgroup `N` (not necessarily abelian) has a local complement in `H ≥ N` iff there is
a crossed map `H → N` for conjugation which restricts to the identity on `N`. -/
theorem exists_isLocalComplement_iff_crossedProjection_mul :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      ∃ c : H → N, (∀ x y : H, c (x * y) = x • c y * c x) ∧
        ∀ n : N, c (inclusion hNH n) = n :=
  ⟨fun ⟨_, hK⟩ => ⟨hK.leftProjection, hK.leftProjection_mul_apply, hK.leftProjection_left⟩,
    fun ⟨_, hc, hn⟩ => ⟨_, isLocalComplement_map_oneLocus hNH hc hn⟩⟩

/-- Twisting a crossed map `c : H → N` by `a ∈ N` as `x ↦ x • a * c x * a⁻¹` preserves the crossed
identity on `H`. -/
theorem local_apply_mul_smul_mul_inv {c : H → N} (hc : ∀ x y : H, c (x * y) = x • c y * c x)
    (a : N) (x y : H) :
    (x * y) • a * c (x * y) * a⁻¹ = x • (y • a * c y * a⁻¹) * (x • a * c x * a⁻¹) := by
  rw [hc, smul_mul', smul_mul', mul_smul, smul_inv']
  group

/-- Twisting a map `c : H → N` by `a ∈ N` as `x ↦ x • a * c x * a⁻¹` preserves a fixed point
`c (inclusion hNH n) = n` in `N`. -/
theorem smul_mul_inv_inclusion {c : H → N} {n : N} (hn : c (inclusion hNH n) = n) (a : N) :
    inclusion hNH n • a * c (inclusion hNH n) * a⁻¹ = n := by
  apply Subtype.ext
  rw [hn, coe_mul, coe_mul, Subgroup.smul_def, coe_inclusion, coe_conjugationAction_smul, coe_inv]
  group

/-- Twisting a normalized crossed map `c : H → N` to `x ↦ x • a * c x * a⁻¹` conjugates its one
locus in `G` by `a ∈ N`. -/
theorem map_subtype_oneLocus_smul_mul_inv {c : H → N}
    (hc : ∀ x y : H, c (x * y) = x • c y * c x)
    (hn : ∀ n : N, c (inclusion hNH n) = n) (a : N) :
    (oneLocus (f := fun x : H => x • a * c x * a⁻¹) (local_apply_mul_smul_mul_inv hc a)).map
        H.subtype =
      MulAut.conj (a : G) • (oneLocus hc).map H.subtype := by
  have hK := isLocalComplement_map_oneLocus hNH hc hn
  have heq : oneLocus (f := fun x : H => x • a * c x * a⁻¹) (local_apply_mul_smul_mul_inv hc a) =
      oneLocus (hK.conj_coe_smul a).leftProjection_mul_apply := by
    ext x
    rw [mem_oneLocus, mem_oneLocus, hK.leftProjection_conj_coe_smul_eq_mul,
      leftProjection_map_oneLocus hNH hc hn]
  rw [heq, (hK.conj_coe_smul a).map_oneLocus_leftProjection]

omit [N.Normal] in
/-- Restricting a normalized map `c` on `H` along `N ≤ L ≤ H` preserves normalization on `N`. -/
theorem comp_inclusion_inclusion {α : Type*} (hNL : N ≤ L) (hLH : L ≤ H) (c : H → α) (n : N) :
    (c ∘ inclusion hLH) (inclusion hNL n) = c (inclusion (hNL.trans hLH) n) := (rfl)

/-- Restricting a local complement along `N ≤ L ≤ H` restricts the associated non-commutative
normalized crossed map along `inclusion hLH`. -/
theorem localMulCrossedProjectionEquiv_restrict (hNL : N ≤ L) (hLH : L ≤ H)
    (K : {K : Subgroup G // N.IsLocalComplement K H}) (x : L) :
    (localMulCrossedProjectionEquiv N L hNL ⟨K.val ⊓ L, K.property.restrict hNL hLH⟩).val x =
      (localMulCrossedProjectionEquiv N H (hNL.trans hLH) K).val (inclusion hLH x) :=
  K.property.leftProjection_restrict hNL hLH x

/-- Conjugating a local complement `K` of `N` in `H` by `g` conjugates its non-commutative
normalized crossed map to `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`. -/
theorem localMulCrossedProjectionEquiv_conj_smul (g : G) (hN : N ≤ MulAut.conj g • H)
    (K : {K : Subgroup G // N.IsLocalComplement K H}) (x : ↥(MulAut.conj g • H)) :
    (localMulCrossedProjectionEquiv N (MulAut.conj g • H) hN
        ⟨MulAut.conj g • K.val, K.property.conj_smul g⟩).val x =
      g • (localMulCrossedProjectionEquiv N H hNH K).val
        ((equivSMul (MulAut.conj g) H).symm x) := by
  rw [localMulCrossedProjectionEquiv_apply, localMulCrossedProjectionEquiv_apply]
  simpa using K.property.leftProjection_conj_smul g ((equivSMul (MulAut.conj g) H).symm x)

/-- Conjugating a normalized map `c : H → N` by `g` gives `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`,
which is again the identity on `N`. -/
theorem smul_apply_equivSMul_symm_inclusion_mul {c : H → N}
    (hn : ∀ n : N, c (inclusion hNH n) = n) (g : G) (hN : N ≤ MulAut.conj g • H) (n : N) :
    g • c ((equivSMul (MulAut.conj g) H).symm (inclusion hN n)) = n := by
  have hx : (equivSMul (MulAut.conj g) H).symm (inclusion hN n) = inclusion hNH (g⁻¹ • n) := by
    apply Subtype.ext
    rw [equivSMul_symm_apply_coe (MulAut.conj g) H (inclusion hN n)]
    simp [coe_conjugationAction_smul]
  rw [hx, hn, smul_inv_smul]

/-- Conjugating a normalized map `c : H → Additive N` by `g` gives `x ↦ g • c (g⁻¹ * x * g)` on
`g H g⁻¹`, which is again the identity on `N`. By `groupCohomology.IsCocycle₁.conj` and
`groupCohomology.map_subtype_zeroLocus_conj`, a normalized crossed map conjugates to a normalized
crossed map whose zero locus is conjugated by `g`. -/
theorem smul_apply_equivSMul_symm_inclusion {c : H → Additive N}
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) (g : G)
    (hN : N ≤ MulAut.conj g • H) (n : N) :
    g • c ((equivSMul (MulAut.conj g) H).symm (inclusion hN n)) = Additive.ofMul n := by
  have hx : (equivSMul (MulAut.conj g) H).symm (inclusion hN n) = inclusion hNH (g⁻¹ • n) := by
    apply Subtype.ext
    rw [equivSMul_symm_apply_coe (MulAut.conj g) H (inclusion hN n)]
    simp [coe_conjugationAction_smul]
  rw [hx, hn, ← Additive.ofMul_smul, smul_inv_smul]

end LocalNoncommutative

/-! ### Abelian normal subgroups and additive `zeroLocus` dictionary -/

section Abelian

variable [IsMulCommutative N]

/-- A normalized additive crossed map has complementary zero locus. This is the
kernel construction for normalized multiplicative crossed maps read on `Additive N`. -/
theorem isComplement'_zeroLocus {c : G → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c n = Additive.ofMul n) : N.IsComplement' (zeroLocus hc) := by
  have hcm : ∀ g k : G, (Additive.toMul ∘ c) (g * k) =
      g • (Additive.toMul ∘ c) k * (Additive.toMul ∘ c) g :=
    fun g k => congrArg Additive.toMul (hc g k)
  have heq : zeroLocus hc = oneLocus (f := Additive.toMul ∘ c) hcm := by
    ext g
    rw [mem_zeroLocus, mem_oneLocus, Function.comp_apply, toMul_eq_one]
  rw [heq]
  exact isComplement'_oneLocus hcm fun n => congrArg Additive.toMul (hn n)

/-- Recovering the projection from the zero locus returns the original normalized map. -/
theorem crossedProjection_zeroLocus {c : G → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c n = Additive.ofMul n) (g : G) :
    (isComplement'_zeroLocus hc hn).crossedProjection g = (c g).toMul := by
  obtain ⟨⟨n, d⟩, rfl⟩ := (isComplement'_zeroLocus hc hn).surjective g
  rw [IsComplement'.crossedProjection_mul, hc]
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

/-- A normal abelian subgroup has a complement exactly when it admits a crossed
map for conjugation which is the identity on that subgroup. -/
theorem exists_complement_iff_crossedProjection :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      ∃ c : G → N, IsMulCocycle₁ c ∧ ∀ n : N, c n = n :=
  exists_isComplement'_iff_crossedProjection_mul

/-- Adding the principal crossed map `g ↦ g • a - a` of `a ∈ N` to a normalized `1`-cocycle
`c : G → Additive N` preserves normalization and conjugates its zero locus by `a`. -/
theorem zeroLocus_add_smul_sub {c : G → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c n = Additive.ofMul n) (a : N) :
    zeroLocus (hc.add (isCocycle₁_smul_sub (Additive.ofMul a))) =
      MulAut.conj (a : G) • zeroLocus hc := by
  have hD := isComplement'_zeroLocus hc hn
  ext x
  rw [mem_zeroLocus, ← toMul_eq_one, Pi.add_apply, toMul_add, toMul_sub, Additive.toMul_smul,
    toMul_ofMul, ← (hD.conj_smul a).crossedProjection_eq_one_iff,
    hD.crossedProjection_conj_coe_smul, crossedProjection_zeroLocus hc hn]

section Local

variable {K L H : Subgroup G} (hNH : N ≤ H)

/-- A normalized additive crossed map on an intermediate subgroup `H ≥ N` has as zero locus a
local complement of `N` in `H`. -/
theorem isLocalComplement_map_zeroLocus {c : H → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) :
    N.IsLocalComplement ((zeroLocus hc).map H.subtype) H := by
  have hcm : ∀ x y : H, (Additive.toMul ∘ c) (x * y) =
      x • (Additive.toMul ∘ c) y * (Additive.toMul ∘ c) x :=
    fun x y => congrArg Additive.toMul (hc x y)
  have heq : zeroLocus hc = oneLocus (f := Additive.toMul ∘ c) hcm := by
    ext x
    rw [mem_zeroLocus, mem_oneLocus, Function.comp_apply, toMul_eq_one]
  rw [heq]
  exact isLocalComplement_map_oneLocus hNH hcm fun n => congrArg Additive.toMul (hn n)

/-- The left projection along the zero locus of a normalized additive crossed map is the
crossed map itself. -/
theorem leftProjection_map_zeroLocus {c : H → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) (x : H) :
    (isLocalComplement_map_zeroLocus hNH hc hn).leftProjection x = (c x).toMul := by
  rw [(isLocalComplement_map_zeroLocus hNH hc hn).leftProjection_eq_iff]
  let n : N := (c x).toMul
  refine ⟨inclusion hNH n⁻¹ * x, (mem_zeroLocus hc).mpr ?_, by simp [n]⟩
  rw [hc, hn]
  have hs : inclusion hNH n⁻¹ • c x = c x :=
    Additive.toMul.injective (conjugationAction_coe_smul n⁻¹ (c x).toMul)
  rw [hs]
  simp [n]

/-- The left projection of a local complement, read additively, is an additive crossed map. -/
theorem IsLocalComplement.isCocycle₁_leftProjection (h : N.IsLocalComplement K H) :
    IsCocycle₁ fun x => Additive.ofMul (h.leftProjection x) :=
  fun x y => congrArg Additive.ofMul (h.isMulCocycle₁_leftProjection x y)

/-- The zero locus of the left projection of a local complement is that local complement. -/
@[simp]
theorem IsLocalComplement.map_zeroLocus_leftProjection (h : N.IsLocalComplement K H) :
    (zeroLocus h.isCocycle₁_leftProjection).map H.subtype = K := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hg
    exact ⟨⟨g, h.right_le hg⟩, by simpa using hg, rfl⟩

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

/-- An abelian normal subgroup `N` has a local complement in an intermediate subgroup `H ≥ N`
exactly when there is a crossed map `H → N` for conjugation which is the identity on `N`. -/
theorem exists_isLocalComplement_iff_crossedProjection :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      ∃ c : H → N, IsMulCocycle₁ c ∧ ∀ n : N, c (inclusion hNH n) = n :=
  exists_isLocalComplement_iff_crossedProjection_mul hNH

/-- Adding the principal crossed map `x ↦ x • a - a` of `a ∈ N` to a normalized `1`-cocycle
`c : H → Additive N` conjugates its zero locus in `G` by `a`. -/
theorem map_subtype_zeroLocus_add_smul_sub {c : H → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c (inclusion hNH n) = Additive.ofMul n) (a : N) :
    (zeroLocus (hc.add (isCocycle₁_smul_sub (G := H) (Additive.ofMul a)))).map H.subtype =
      MulAut.conj (a : G) • (zeroLocus hc).map H.subtype := by
  have hK := isLocalComplement_map_zeroLocus hNH hc hn
  have heq : zeroLocus (hc.add (isCocycle₁_smul_sub (G := H) (Additive.ofMul a))) =
      zeroLocus (hK.conj_coe_smul a).isCocycle₁_leftProjection := by
    ext x
    rw [mem_zeroLocus, mem_zeroLocus, ← toMul_eq_one, ← toMul_eq_one, Pi.add_apply, toMul_add,
      toMul_sub, Subgroup.smul_def, Additive.toMul_smul, toMul_ofMul,
      hK.leftProjection_conj_coe_smul, leftProjection_map_zeroLocus hNH hc hn, toMul_ofMul,
      Subgroup.smul_def]
  rw [heq, (hK.conj_coe_smul a).map_zeroLocus_leftProjection]

/-- Restricting a local complement along `N ≤ L ≤ H` restricts the associated normalized crossed
map along `inclusion hLH`. -/
theorem localCrossedProjectionEquiv_restrict (hNL : N ≤ L) (hLH : L ≤ H)
    (K : {K : Subgroup G // N.IsLocalComplement K H}) (x : L) :
    (localCrossedProjectionEquiv N L hNL ⟨K.val ⊓ L, K.property.restrict hNL hLH⟩).val x =
      (localCrossedProjectionEquiv N H (hNL.trans hLH) K).val (inclusion hLH x) :=
  congrArg Additive.ofMul (K.property.leftProjection_restrict hNL hLH x)

/-- Conjugating a local complement `K` of `N` in `H` by `g` conjugates its normalized crossed map
to `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`. -/
theorem localCrossedProjectionEquiv_conj_smul (g : G) (hN : N ≤ MulAut.conj g • H)
    (K : {K : Subgroup G // N.IsLocalComplement K H}) (x : ↥(MulAut.conj g • H)) :
    (localCrossedProjectionEquiv N (MulAut.conj g • H) hN
        ⟨MulAut.conj g • K.val, K.property.conj_smul g⟩).val x =
      g • (localCrossedProjectionEquiv N H hNH K).val ((equivSMul (MulAut.conj g) H).symm x) := by
  rw [localCrossedProjectionEquiv_apply, localCrossedProjectionEquiv_apply, ← Additive.ofMul_smul]
  refine congrArg Additive.ofMul ?_
  simpa using K.property.leftProjection_conj_smul g ((equivSMul (MulAut.conj g) H).symm x)

end Local

end Abelian

end Subgroup
