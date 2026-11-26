/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.CrossedCocycle.Basic
import Mathlib.Tactic.Group

/-!
# Multiplicative crossed homomorphisms into non-abelian groups

For a multiplicative type `G` acting by scalars on a multiplicative type `M`, a function
`f : G → M` is a **multiplicative crossed homomorphism** (`TauCeti.IsMulCrossedHom`) when

  `f (g * h) = g • f h * f g`

for all `g, h : G`. This extends Mathlib's `groupCohomology.IsMulCocycle₁` (which assumes
`CommGroup M`) to possibly non-commutative coefficient groups `M`, keeping the right-to-left factor
order induced by left complement decompositions `g = n * d`. When a monoid `G` acts on a group `M`
through `α : G →* MulAut M` (`α g m = g • m`), pointwise inversion `f ↦ (g ↦ (f g)⁻¹)` identifies
`TauCeti.IsMulCrossedHom` with `TauCeti.CrossedCocycle α` (`c (g * h) = c g * α g (c h)`;
`TauCeti.mulCrossedHomEquivCrossedCocycle`, `TauCeti.isMulCrossedHom_iff_exists_crossedCocycle`).
Keeping `TauCeti.IsMulCrossedHom` unbundled in the right-to-left order matches normalized
complement projections (`c n = n`) and Mathlib's `IsMulCocycle₁`/`IsCocycle₁`, while also covering
right-cancellative `MulOneClass` targets and non-distributive `MulAction`s. In contrast to
`TauCeti.IsCrossedHom`, which twists an additive target semiring `R` by a unit-valued map
`H → Rˣ`, both domain and target here are multiplicative and no ring structure enters.

Without commutativity of `M` or distributivity of the action:

* Over a monoid `G` acting on a right-cancellative `MulOneClass` `M`, every multiplicative crossed
  homomorphism sends `1` to `1` (`TauCeti.IsMulCrossedHom.map_one`) and forces the action to fix
  `1` (`TauCeti.IsMulCrossedHom.smul_one`). When `G` is a group, the `1`-locus `{g | f g = 1}` is
  a subgroup of `G` (`TauCeti.IsMulCrossedHom.oneLocus`), compatible with restriction along
  subgroup inclusions (`TauCeti.IsMulCrossedHom.map_subtype_oneLocus_comp_inclusion`).
* Over groups `G` and `M`, `k • f (k⁻¹ * m * k) = m • f k * f m * (f k)⁻¹`
  (`TauCeti.IsMulCrossedHom.smul_apply_inv_mul_mul`) and `g • f g⁻¹ = (f g)⁻¹`
  (`TauCeti.IsMulCrossedHom.smul_map_inv`).
* When a group `G` acts on a monoid `M` by monoid endomorphisms (`MulDistribMulAction G M`),
  conjugating a multiplicative crossed homomorphism on `H ≤ G` by `g : G` produces one on `g H g⁻¹`
  (`TauCeti.IsMulCrossedHom.conj`); when `M` is right-cancellative, its `1`-locus in `G` is
  conjugated by `g` (`TauCeti.IsMulCrossedHom.map_subtype_oneLocus_conj`), extending
  `groupCohomology.zeroLocus` and `groupCohomology.IsCocycle₁.conj` from
  `TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107, §1.
* J.-P. Serre, *Galois Cohomology*, Springer, Ch. I, §5.1 (written with the opposite factor order).
-/

public section

namespace TauCeti

section Mul

variable {G M : Type*} [Mul G] [Mul M] [SMul G M]

/-- A function `f : G → M` is a **multiplicative crossed homomorphism** if
`f (g * h) = g • f h * f g` for all `g, h : G`. Unlike `groupCohomology.IsMulCocycle₁`, no
commutativity of `M` is assumed. -/
def IsMulCrossedHom (f : G → M) : Prop :=
  ∀ g h : G, f (g * h) = g • f h * f g

/-- Unfolding lemma for `IsMulCrossedHom`. -/
theorem isMulCrossedHom_iff {f : G → M} :
    IsMulCrossedHom f ↔ ∀ g h : G, f (g * h) = g • f h * f g :=
  (Iff.rfl)

/-- The crossed identity for a multiplicative crossed homomorphism. -/
theorem IsMulCrossedHom.map_mul {f : G → M} (hf : IsMulCrossedHom f) (g h : G) :
    f (g * h) = g • f h * f g :=
  hf g h

/-- Precomposing a multiplicative crossed homomorphism with a multiplicative map compatible with
the scalar actions gives a multiplicative crossed homomorphism. -/
theorem IsMulCrossedHom.comp {H : Type*} [Mul H] [SMul H M] {F : Type*} [FunLike F H G]
    [MulHomClass F H G] {f : G → M} (hf : IsMulCrossedHom f) (φ : F)
    (hφ : ∀ (x : H) (m : M), x • m = φ x • m) :
    IsMulCrossedHom (f ∘ φ) := fun x y => by
  simp only [Function.comp_apply, _root_.map_mul, hf.map_mul, hφ]

end Mul

section Monoid

variable {G M : Type*} [Monoid G] [MulOneClass M] [IsRightCancelMul M] [MulAction G M]

/-- A multiplicative crossed homomorphism into a right-cancellative `MulOneClass` sends `1` to
`1`. -/
theorem IsMulCrossedHom.map_one {f : G → M} (hf : IsMulCrossedHom f) : f 1 = 1 := by
  have h := hf.map_mul 1 1
  rw [mul_one, one_smul] at h
  exact (mul_right_cancel ((one_mul (f 1)).trans h)).symm

/-- A monoid action on a right-cancellative `MulOneClass` admitting a multiplicative crossed
homomorphism fixes `1`. -/
theorem IsMulCrossedHom.smul_one {f : G → M} (hf : IsMulCrossedHom f) (g : G) :
    g • (1 : M) = 1 := by
  have h := hf.map_mul g 1
  rw [mul_one, hf.map_one] at h
  exact mul_right_cancel (h.symm.trans (one_mul (f g)).symm)

end Monoid

section MulDistribMulAction

/-- The constant map `1` is a multiplicative crossed homomorphism for any `MulDistribMulAction`. -/
@[simp]
theorem isMulCrossedHom_const_one {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    IsMulCrossedHom (fun _ : G => (1 : M)) := fun g _ => by
  rw [MulDistribMulAction.smul_one g, mul_one]

end MulDistribMulAction

section Group

/-- Conjugating the argument of a multiplicative crossed homomorphism by `k` and acting by `k`
satisfies `k • f (k⁻¹ * m * k) = m • f k * f m * (f k)⁻¹`, for any scalar multiplication of a
group `G` on a not-necessarily-commutative group `M`. -/
theorem IsMulCrossedHom.smul_apply_inv_mul_mul {G M : Type*} [Group G] [Group M] [SMul G M]
    {f : G → M} (hf : IsMulCrossedHom f) (k m : G) :
    k • f (k⁻¹ * m * k) = m • f k * f m * (f k)⁻¹ := by
  have hmul : k * (k⁻¹ * m * k) = m * k := by group
  have h := (hf.map_mul k (k⁻¹ * m * k)).symm.trans (hmul ▸ hf.map_mul m k)
  exact eq_mul_inv_of_mul_eq h

/-- Restricting a multiplicative crossed homomorphism to a subgroup `H ≤ G` gives a multiplicative
crossed homomorphism for the restricted scalar multiplication. -/
theorem IsMulCrossedHom.comp_subtype {G M : Type*} [Group G] [Mul M] [SMul G M] {f : G → M}
    (hf : IsMulCrossedHom f) (H : Subgroup G) :
    IsMulCrossedHom (f ∘ H.subtype) :=
  hf.comp H.subtype fun _ _ => rfl

/-- Restricting a multiplicative crossed homomorphism along an inclusion `L ≤ H` of subgroups gives
a multiplicative crossed homomorphism on `L`. -/
theorem IsMulCrossedHom.comp_inclusion {G M : Type*} [Group G] [Mul M] [SMul G M]
    {L H : Subgroup G} (hLH : L ≤ H) {c : H → M} (hc : IsMulCrossedHom c) :
    IsMulCrossedHom (c ∘ Subgroup.inclusion hLH) :=
  hc.comp (Subgroup.inclusion hLH) fun _ _ => rfl

/-- The value of a multiplicative crossed homomorphism at `g⁻¹`, acted on by `g`, is `(f g)⁻¹`. -/
theorem IsMulCrossedHom.smul_map_inv {G M : Type*} [Group G] [Group M] [MulAction G M]
    {f : G → M} (hf : IsMulCrossedHom f) (g : G) :
    g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← hf.map_one, ← mul_inv_cancel g, hf.map_mul]

/-- The value of a multiplicative crossed homomorphism at `g⁻¹` is `g⁻¹ • (f g)⁻¹`. -/
theorem IsMulCrossedHom.map_inv {G M : Type*} [Group G] [Group M] [MulAction G M]
    {f : G → M} (hf : IsMulCrossedHom f) (g : G) :
    f g⁻¹ = g⁻¹ • (f g)⁻¹ := by
  rw [← hf.smul_map_inv, inv_smul_smul]

variable {G M : Type*} [Group G] [MulOneClass M] [IsRightCancelMul M] [MulAction G M]

/-- **The `1`-locus of a multiplicative crossed homomorphism**, `{g | f g = 1}`, as a subgroup of
`G`, for any group action (not necessarily distributive) on a right-cancellative `MulOneClass` `M`
(not necessarily commutative). -/
def IsMulCrossedHom.oneLocus {f : G → M} (hf : IsMulCrossedHom f) : Subgroup G where
  carrier := {g | f g = 1}
  one_mem' := hf.map_one
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hf.map_mul, hg, hh, hf.smul_one, mul_one]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := hf.map_mul g⁻¹ g
    rwa [inv_mul_cancel, hf.map_one, hg, hf.smul_one, one_mul, eq_comm] at h

/-- An element lies in the `1`-locus of a multiplicative crossed homomorphism iff the map equals
`1` there. -/
@[simp]
theorem IsMulCrossedHom.mem_oneLocus {f : G → M} (hf : IsMulCrossedHom f) {g : G} :
    g ∈ hf.oneLocus ↔ f g = 1 :=
  (Iff.rfl)

/-- The carrier of the `1`-locus of a multiplicative crossed homomorphism is the preimage of
`{1}`. -/
@[simp]
theorem IsMulCrossedHom.coe_oneLocus {f : G → M} (hf : IsMulCrossedHom f) :
    (hf.oneLocus : Set G) = f ⁻¹' {1} :=
  (rfl)

/-- The `1`-locus of the restriction of `f` to `H` is `hf.oneLocus.subgroupOf H`. -/
@[simp]
theorem IsMulCrossedHom.oneLocus_comp_subtype {f : G → M} (hf : IsMulCrossedHom f)
    (H : Subgroup G) :
    (hf.comp_subtype H).oneLocus = hf.oneLocus.subgroupOf H := by
  ext x
  rfl

/-- Restricting a multiplicative crossed homomorphism along `L ≤ H` intersects its `1`-locus in `G`
with `L`. -/
@[simp]
theorem IsMulCrossedHom.map_subtype_oneLocus_comp_inclusion {L H : Subgroup G} (hLH : L ≤ H)
    {c : H → M} (hc : IsMulCrossedHom c) :
    (hc.comp_inclusion hLH).oneLocus.map L.subtype = hc.oneLocus.map H.subtype ⊓ L := by
  ext g
  simp only [Subgroup.mem_map, mem_oneLocus, Function.comp_apply, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨Subgroup.inclusion hLH y, hy, rfl⟩, y.property⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxL⟩
    exact ⟨⟨x, hxL⟩, hx, rfl⟩

end Group

section Conj

open scoped Pointwise

variable {G M : Type*} [Group G] [Monoid M] [MulDistribMulAction G M] {H : Subgroup G}

/-- Conjugating a multiplicative crossed homomorphism `c` on `H` by `g` gives the multiplicative
crossed homomorphism `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`. -/
theorem IsMulCrossedHom.conj {c : H → M} (hc : IsMulCrossedHom c) (g : G) :
    IsMulCrossedHom fun x : ↥(MulAut.conj g • H) =>
      g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm x) :=
  isMulCrossedHom_iff.mpr fun x y => by
    have hx : (((Subgroup.equivSMul (MulAut.conj g) H).symm x : H) : G) = g⁻¹ * x * g :=
      Subgroup.equivSMul_symm_apply_coe (MulAut.conj g) H x
    simp only [_root_.map_mul, hc.map_mul, smul_mul', Subgroup.smul_def, smul_smul, hx,
      mul_assoc, mul_inv_cancel_left]

/-- The `1`-locus of the conjugate `x ↦ g • c (g⁻¹ * x * g)` of a multiplicative crossed
homomorphism on `H`, viewed in `G`, is the conjugate by `g` of the `1`-locus of `c`. -/
@[simp]
theorem IsMulCrossedHom.map_subtype_oneLocus_conj [IsRightCancelMul M] {c : H → M}
    (hc : IsMulCrossedHom c) (g : G) :
    (hc.conj g).oneLocus.map (MulAut.conj g • H).subtype =
      MulAut.conj g • hc.oneLocus.map H.subtype := by
  have hsmul (m : M) : g • m = 1 ↔ m = 1 := by
    conv_lhs => rw [← MulDistribMulAction.smul_one g]
    exact smul_left_cancel_iff g
  ext x
  simp only [Subgroup.mem_map, mem_oneLocus, hsmul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, Subgroup.equivSMul_symm_apply_coe (MulAut.conj g) H y⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨Subgroup.equivSMul (MulAut.conj g) H z, ?_, ?_⟩
    · rwa [MulEquiv.symm_apply_apply]
    · rw [Subgroup.equivSMul_apply_coe, hzx, smul_inv_smul]

end Conj

section CrossedCocycle

variable {G M : Type*} [Monoid G] [Group M] [SMul G M] {α : G →* MulAut M}
  (hα : ∀ g m, α g m = g • m)

/-- Pointwise inversion turns a multiplicative crossed homomorphism `f : G → M`
(`f (g * h) = g • f h * f g`) into a crossed cocycle `TauCeti.CrossedCocycle α`
(`c (g * h) = c g * α g (c h)`), for any action `α : G →* MulAut M` agreeing with `•`. -/
def IsMulCrossedHom.toInvCrossedCocycle {f : G → M} (hf : IsMulCrossedHom f) :
    CrossedCocycle α where
  toFun g := (f g)⁻¹
  map_mul' g h := by rw [hf.map_mul, ← hα, mul_inv_rev, _root_.map_inv]

/-- Evaluating `hf.toInvCrossedCocycle hα` at `g` gives `(f g)⁻¹`. -/
@[simp]
theorem IsMulCrossedHom.toInvCrossedCocycle_apply {f : G → M} (hf : IsMulCrossedHom f) (g : G) :
    hf.toInvCrossedCocycle hα g = (f g)⁻¹ :=
  (rfl)

/-- Two multiplicative crossed homomorphisms with the same inverted `CrossedCocycle` are equal. -/
theorem IsMulCrossedHom.toInvCrossedCocycle_injective {f f' : G → M} (hf : IsMulCrossedHom f)
    (hf' : IsMulCrossedHom f')
    (h : hf.toInvCrossedCocycle hα = hf'.toInvCrossedCocycle hα) : f = f' :=
  funext fun g => inv_injective (DFunLike.congr_fun h g)

/-- The inverted `CrossedCocycle` of the constant map `1` is `1`. -/
@[simp]
theorem IsMulCrossedHom.toInvCrossedCocycle_const_one {G M : Type*} [Monoid G] [Group M]
    [MulDistribMulAction G M] {α : G →* MulAut M} (hα : ∀ g m, α g m = g • m) :
    (isMulCrossedHom_const_one (G := G) (M := M)).toInvCrossedCocycle hα = 1 :=
  CrossedCocycle.ext fun _ => inv_one

/-- Pointwise inversion of a `TauCeti.CrossedCocycle α` is a multiplicative crossed homomorphism,
for any scalar multiplication `•` agreeing with `α`. -/
theorem CrossedCocycle.isMulCrossedHom_inv (hα : ∀ g m, α g m = g • m) (c : CrossedCocycle α) :
    IsMulCrossedHom (fun g => (c g)⁻¹) :=
  isMulCrossedHom_iff.mpr fun g h => by
    rw [c.apply_mul, mul_inv_rev, ← _root_.map_inv, hα]

/-- Applying `toInvCrossedCocycle` to the pointwise inverse of `c` recovers `c`. -/
@[simp]
theorem CrossedCocycle.toInvCrossedCocycle_isMulCrossedHom_inv (c : CrossedCocycle α) :
    (c.isMulCrossedHom_inv hα).toInvCrossedCocycle hα = c :=
  CrossedCocycle.ext fun g => inv_inv (c g)

/-- Multiplicative crossed homomorphisms `G → M` correspond bijectively to crossed cocycles
`TauCeti.CrossedCocycle α` via pointwise inversion `f ↦ (g ↦ (f g)⁻¹)`. -/
def mulCrossedHomEquivCrossedCocycle :
    {f : G → M // IsMulCrossedHom f} ≃ CrossedCocycle α where
  toFun f := f.property.toInvCrossedCocycle hα
  invFun c := ⟨fun g => (c g)⁻¹, c.isMulCrossedHom_inv hα⟩
  left_inv f := Subtype.ext (funext fun g => inv_inv (f.val g))
  right_inv := CrossedCocycle.toInvCrossedCocycle_isMulCrossedHom_inv hα

/-- `mulCrossedHomEquivCrossedCocycle` acts by pointwise inversion. -/
@[simp]
theorem mulCrossedHomEquivCrossedCocycle_apply (f : {f : G → M // IsMulCrossedHom f}) (g : G) :
    mulCrossedHomEquivCrossedCocycle hα f g = (f.val g)⁻¹ :=
  (rfl)

/-- `mulCrossedHomEquivCrossedCocycle.symm` acts by pointwise inversion. -/
@[simp]
theorem coe_mulCrossedHomEquivCrossedCocycle_symm_apply (c : CrossedCocycle α) (g : G) :
    ((mulCrossedHomEquivCrossedCocycle hα).symm c).val g = (c g)⁻¹ :=
  (rfl)

/-- A map `f : G → M` is a multiplicative crossed homomorphism if and only if it is the pointwise
inverse of a `TauCeti.CrossedCocycle α`, for an action `α : G →* MulAut M` agreeing with `•`. -/
theorem isMulCrossedHom_iff_exists_crossedCocycle (hα : ∀ g m, α g m = g • m) {f : G → M} :
    IsMulCrossedHom f ↔ ∃ c : CrossedCocycle α, ∀ g, f g = (c g)⁻¹ :=
  ⟨fun hf => ⟨hf.toInvCrossedCocycle hα, fun g => (inv_inv (f g)).symm⟩,
    fun ⟨c, hc⟩ => by
      have hfun : f = fun g => (c g)⁻¹ := funext hc
      exact hfun ▸ c.isMulCrossedHom_inv hα⟩

end CrossedCocycle

end TauCeti
