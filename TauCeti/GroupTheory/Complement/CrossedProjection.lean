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

For an abelian normal subgroup `N` of `G`, a complement determines a crossed map
`c : G → N` which restricts to the identity on `N`. Conversely, the locus where
such a map equals `1` is a complement. This file proves both constructions and the
existence criterion, without any finiteness assumption. The same projection for a local
complement `K` of `N` in an intermediate subgroup `H` is a crossed map on `H`.

Conjugating a complement `D` by `g` conjugates its crossed projection `c` to
`x ↦ g • c (g⁻¹ * x * g)`. For `a ∈ N` this is `c` times the principal crossed map
`x ↦ x • a / a`, so two complements are conjugate by `a` exactly when their crossed
projections differ by that principal crossed map
(`Subgroup.IsComplement'.eq_conj_smul_iff_crossedProjection_eq`).

The conjugation action is explicit rather than a global instance. The additive
coefficient action uses `Additive.distribMulAction`, and kernels use the existing
`groupCohomology.zeroLocus` rather than a second notion of cocycle kernel.
The crossed projection is the first component of Mathlib's complement decomposition;
its quotient-splitting formula supplies the crossed identity.

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

/-- The projection satisfies the crossed identity for ambient conjugation. -/
theorem isMulCocycle₁_crossedProjection [IsMulCommutative N] :
    IsMulCocycle₁ h.crossedProjection := by
  intro g k
  apply Subtype.ext
  simp only [coe_crossedProjection, coe_mul, coe_conjugationAction_smul,
    QuotientGroup.mk_mul, map_mul]
  group

omit [N.Normal] in
/-- Exactly the elements of the complement have trivial crossed projection. -/
@[simp]
theorem crossedProjection_eq_one_iff (g : G) : h.crossedProjection g = 1 ↔ g ∈ D := by
  rw [← Subtype.coe_inj]
  exact h.coe_equiv_fst_eq_one_iff_mem N.one_mem

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

variable [IsMulCommutative N]

/-- **Conjugation by an element of `N`.** For `a ∈ N`, the crossed projection along `a D a⁻¹` is
the crossed projection along `D` times the principal crossed map `x ↦ x • a / a`. -/
theorem crossedProjection_conj_coe_smul (a : N) (x : G) :
    (h.conj_smul a).crossedProjection x = h.crossedProjection x * (x • a / a) := by
  rw [h.crossedProjection_conj_smul]
  have hc (g k : G) := h.isMulCocycle₁_crossedProjection g k
  simp only [hc, ← coe_inv, crossedProjection_coe,
    mul_smul, conjugationAction_coe_smul, div_eq_mul_inv]
  ac_rfl

/-- Two complements of an abelian normal subgroup `N` are conjugate by `a ∈ N` exactly when
their crossed projections differ by the principal crossed map `x ↦ x • a / a`. -/
theorem eq_conj_smul_iff_crossedProjection_eq {D' : Subgroup G} (h' : N.IsComplement' D')
    (a : N) : D' = MulAut.conj (a : G) • D ↔
      ∀ x, h'.crossedProjection x = h.crossedProjection x * (x • a / a) := by
  constructor
  · rintro rfl x
    exact h.crossedProjection_conj_coe_smul a x
  · intro hD
    ext x
    rw [← h'.crossedProjection_eq_one_iff, ← (h.conj_smul a).crossedProjection_eq_one_iff, hD,
      h.crossedProjection_conj_coe_smul]

end IsComplement'

/-- The left projection of a local complement `K` of `N` in `H` satisfies the crossed identity
for the conjugation action of `H` on `N`. -/
theorem IsLocalComplement.isMulCocycle₁_leftProjection [IsMulCommutative N] {K H : Subgroup G}
    (h : N.IsLocalComplement K H) : IsMulCocycle₁ h.leftProjection := by
  intro x y
  rw [h.leftProjection_eq_iff]
  have hx := (h.leftProjection_eq_iff x _).mp rfl
  have hy := (h.leftProjection_eq_iff y _).mp rfl
  simp only [coe_mul, Subgroup.smul_def, coe_conjugationAction_smul]
  convert K.mul_mem hx hy using 1
  group

variable [IsMulCommutative N]

/-- A normalized additive crossed map has complementary zero locus. This is the
kernel construction for normalized multiplicative crossed maps read on `Additive N`. -/
theorem isComplement'_zeroLocus {c : G → Additive N} (hc : IsCocycle₁ c)
    (hn : ∀ n : N, c n = Additive.ofMul n) : N.IsComplement' (zeroLocus hc) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    intro g hg
    have hz : c g = 0 := (mem_zeroLocus hc).mp hg.2
    rw [hn ⟨g, hg.1⟩] at hz
    exact congrArg (fun x : Additive N => (x.toMul : G)) hz
  · apply Set.eq_univ_iff_forall.mpr
    intro g
    let n : N := (c g).toMul
    refine ⟨n, n.property, (n : G)⁻¹ * g, ?_, by simp⟩
    apply (mem_zeroLocus hc).mpr
    rw [hc]
    have hi := hn n⁻¹
    simp only [coe_inv] at hi
    rw [hi]
    have hs : ((n⁻¹ : N) : G) • c g = c g := by
      apply Additive.toMul.injective
      exact conjugationAction_coe_smul n⁻¹ (c g).toMul
    simp only [coe_inv] at hs
    rw [hs]
    simp [n]

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

/-- A normal abelian subgroup has a complement exactly when it admits a crossed
map for conjugation which is the identity on that subgroup. -/
theorem exists_complement_iff_crossedProjection :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      ∃ c : G → N, IsMulCocycle₁ c ∧ ∀ n : N, c n = n := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨hD.crossedProjection, hD.isMulCocycle₁_crossedProjection,
      hD.crossedProjection_coe⟩
  · rintro ⟨c, hc, hn⟩
    have ha : IsCocycle₁ (fun g => Additive.ofMul (c g)) :=
      fun g k => congrArg Additive.ofMul (hc g k)
    exact ⟨zeroLocus ha, isComplement'_zeroLocus ha (fun n => congrArg Additive.ofMul (hn n))⟩

end Subgroup
