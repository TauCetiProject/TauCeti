/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.GroupTheory.GroupAction.FixedPoints
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.Topology

import Mathlib.Tactic.Abel

/-!
# The explicit low-degree complex of continuous cochains

Continuous cochain cohomology of a topological group `G` acting on a topological module `M` is
computed in low degrees by an explicit complex of *plain functions carrying continuity as a
predicate*: `C¹` is the additive subgroup of continuous elements of `G → M` and `C²` the
subgroup of continuous elements of `G × G → M`. This file builds that complex, its differentials,
its cocycles and coboundaries, and the three low-degree cohomology groups

```text
H⁰(G, M) = M^G,   H¹(G, M) = Z¹/B¹,   H²(G, M) = Z²/B².
```

## Main definitions

* `TauCeti.ContCohomology.C1`, `TauCeti.ContCohomology.C2`: the continuous cochains.
* `TauCeti.ContCohomology.d0`, `d1`, `d2`: the inhomogeneous differentials, as additive
  homomorphisms of the ambient function groups.
* `TauCeti.ContCohomology.Z1`, `Z2`: the continuous cocycles, `Cⁱ ⊓ ker dⁱ`.
* `TauCeti.ContCohomology.B1`, `B2`: the coboundaries, `range d⁰` and the image `d¹(C¹)` of the
  *continuous* `1`-cochains.
* `TauCeti.ContCohomology.H0`, `H1`, `H2`, their class maps `H1pi`, `H2pi`, and the discrete
  carriers `DiscreteH1`, `DiscreteH2` used by the comparison with canonical cohomology, together
  with their identifications `discreteH1Equiv`, `discreteH2Equiv` with `H1` and `H2`.
* `TauCeti.ContCohomology.sumCocycle`: the additive map sending a finite-group `2`-cocycle to
  the invariant obtained by summing it over its first argument.
* `TauCeti.ContCohomology.explicitMap0`: the compatible-pair pullback on the explicit degree-zero
  carrier, with `TauCeti.ContCohomology.explicitRes0` and `explicitCoeff0` its two named
  instances.

## Main statements

* `TauCeti.ContCohomology.d1_comp_d0` and `TauCeti.ContCohomology.d2_comp_d1`: `d ∘ d = 0`.
* `TauCeti.ContCohomology.B1_le_Z1` and `TauCeti.ContCohomology.B2_le_Z2`: the form of `d ∘ d = 0`
  that the two quotients need, coboundaries being continuous.
* `TauCeti.ContCohomology.subsingleton_H1_of_subsingleton` and
  `subsingleton_H2_of_subsingleton`: a trivial group has vanishing `H¹` and `H²`.
* `TauCeti.ContCohomology.subsingleton_H1_of_subsingleton_coefficients` and
  `subsingleton_H2_of_subsingleton_coefficients`: a zero coefficient group has vanishing `H¹` and
  `H²`.
* `TauCeti.ContCohomology.nsmul_H1_eq_zero` and `nsmul_H2_eq_zero`: `H¹(G, M)` and `H²(G, M)`
  are killed by whatever kills the coefficients `M`.
* `TauCeti.ContCohomology.H1EquivOfSmulEqSelf`: for a trivial action, `H¹(G, M)` is the group of
  continuous homomorphisms `G →ₜ* Multiplicative M`. This is the statement that makes `H¹` of a
  profinite group computable, and it is false without continuity.

## Implementation notes

The differentials and the cocycle identities follow the conventions of Mathlib's
`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`:

```text
(d⁰ m) g       = g • m - m,
(d¹ f) (g, h)  = g • f h - f (g * h) + f g,
(d² f) (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h).
```

The cocycle conditions are spelled by Mathlib's unbundled predicates
`groupCohomology.IsCocycle₁` and `groupCohomology.IsCocycle₂`, and
`TauCeti.ContCohomology.d1_apply_eq_zero_iff` and `d2_apply_eq_zero_iff` identify them with the
vanishing of the differentials, so that `Zⁱ = Cⁱ ⊓ ker dⁱ` — which is how `Z1` and `Z2` are
*defined*, taking their closure under the group operations from `AddMonoidHom.ker` — is stated in
that spelling by `mem_Z1_iff` and `mem_Z2_iff`.

Mathlib's bundled `groupCohomology.cocycles₁` and `cocycles₂` are *not* reused here: Mathlib's
low-degree group cohomology API states them for `Rep k G` with `k` and `G` in a single universe
(its binders are `{k G : Type u}`), and the coefficient modules of a profinite group have to be
allowed to live in the group's universe with a small coefficient ring such as `ℤ`. The unbundled
`IsCocycle₁`/`IsCocycle₂` predicates, which Mathlib provides for exactly this purpose, carry no
such constraint and are consumed directly. The cochain groups themselves are Mathlib's
`continuousAddSubgroup`.

The trivial-action results are the continuous analogues of Mathlib's
`groupCohomology.cocycles₁IsoOfIsTrivial`, `groupCohomology.coboundaries₁_eq_bot_of_isTrivial` and
`groupCohomology.H1IsoOfIsTrivial`, in the same order and with the same proof plan; they are
restated for the unbundled classes because the Mathlib versions are stated for `Rep k G`.

Cochains are not normalised. The identities at the unit, `f 1 = 0` in degree `1` and
`f (1, g) = f (1, 1)`, `f (g, 1) = g • f (1, 1)` in degree `2`, are the lemmas
`map_one_of_mem_Z1`, `map_one_fst_of_mem_Z2` and `map_one_snd_of_mem_Z2`, never definitional
conditions.

`H1` and `H2` divide `Z¹` and `Z²` by the coboundaries *viewed inside the cocycles*, in the
`AddSubgroup.addSubgroupOf` spelling, so that no proof term enters either quotient subgroup. Each
carrier retains the hypotheses of `TauCeti.ContCohomology.B1_le_Z1`, respectively
`B2_le_Z2`, through that inclusion theorem, so the subgroup divided out is always the whole of
`B¹`, respectively `B²`, and never the intersection `B ⊓ Z` that `addSubgroupOf` would cut out at a
weaker generality; `AddSubgroup.map_addSubgroupOf_eq_of_le` turns those inclusions into that
identity whenever a consumer needs it spelled out. The two carriers therefore sit in separate
sections:
`H¹` needs `G` to be a monoid acting continuously, and `H²` needs a continuous multiplication on
`G` besides, because `d¹` has to preserve continuity for `B² = d¹(C¹)` to consist of cocycles.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  cohomology of a profinite group computed by the inhomogeneous complex of continuous cochains,
  which is the complex built here in degrees `≤ 2`.
-/

public section

namespace TauCeti.ContCohomology

universe u v w

section Cochains

variable (G : Type u) [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The continuous `1`-cochains: the additive subgroup of continuous elements of `G → M`.

Continuity is a predicate on a plain function rather than a bundled `C(G, M)`, matching the shape
of Mathlib's `groupCohomology.cocycles₁ : Submodule k (G → A)`. -/
def C1 : AddSubgroup (G → M) := continuousAddSubgroup G M

/-- The continuous `2`-cochains: the continuous `1`-cochains of the domain `G × G`. -/
def C2 : AddSubgroup (G × G → M) := C1 (G × G) M

variable {G M}

/-- Membership in `C¹` is continuity. -/
@[simp]
theorem mem_C1_iff {f : G → M} : f ∈ C1 G M ↔ Continuous f := (Iff.rfl)

/-- Membership in `C²` is continuity. -/
@[simp]
theorem mem_C2_iff {f : G × G → M} : f ∈ C2 G M ↔ Continuous f := mem_C1_iff

/-- The degree-`2` cochains are the degree-`1` cochains of `G × G`. This is how `C²` is defined,
but the definition is not exposed outside this file, so the identity is recorded as a theorem for
consumers that have to move between the two spellings. -/
theorem C2_eq_C1 : C2 G M = C1 (G × G) M := (rfl)

/-- Over a discrete group every `1`-cochain is continuous. -/
@[simp]
theorem C1_eq_top [DiscreteTopology G] : C1 G M = ⊤ :=
  (AddSubgroup.eq_top_iff' _).2 fun _ => mem_C1_iff.2 continuous_of_discreteTopology

/-- Over a discrete group every `2`-cochain is continuous: `G × G` is discrete too. -/
@[simp]
theorem C2_eq_top [DiscreteTopology G] : C2 G M = ⊤ := C1_eq_top (G := G × G) (M := M)

end Cochains

section Differentials

section Degree0

/-! Degree `0` needs nothing of `G` but a distributive scalar action. -/

variable (G : Type u) (M : Type v) [AddCommGroup M] [DistribSMul G M]

/-- The degree-`0` differential `(d⁰ m) g = g • m - m`. -/
def d0 : M →+ (G → M) where
  toFun m := fun g => g • m - m
  map_zero' := by ext g; simp
  map_add' m m' := by ext g; simp only [Pi.add_apply, smul_add]; abel

/-- The `1`-coboundaries `B¹ = range d⁰`, defined as an algebraic range. Under a continuous
action, `TauCeti.ContCohomology.B1_le_C1` shows that these cochains are continuous. -/
def B1 : AddSubgroup (G → M) := (d0 G M).range

variable {G M}

/-- The defining formula for `d⁰`. -/
@[simp]
theorem d0_apply (m : M) (g : G) : d0 G M m g = g • m - m := (rfl)

/-- An equivariant additive map commutes with the degree-`0` differential. -/
theorem map_d0_apply {N : Type w} [AddCommGroup N] [DistribSMul G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (m : M) (g : G) :
    φ (d0 G M m g) = d0 G N (φ m) g := by
  simp only [d0_apply, map_sub, hφ]

/-- Membership in `B¹` is Mathlib's unbundled `1`-coboundary condition. -/
@[simp]
theorem mem_B1_iff {f : G → M} : f ∈ B1 G M ↔ groupCohomology.IsCoboundary₁ f := by
  simp only [B1, AddMonoidHom.mem_range, groupCohomology.IsCoboundary₁, funext_iff, d0_apply]

/-- The introduction rule for `B¹`: every `d⁰`-image is a `1`-coboundary.

This is deliberately not `@[simp]`: `mem_B1_iff` already rewrites the left-hand side to
`groupCohomology.IsCoboundary₁ (d0 G M m)`. -/
theorem d0_mem_B1 (m : M) : d0 G M m ∈ B1 G M :=
  AddMonoidHom.mem_range.2 ⟨m, rfl⟩

section TrivialAction

variable (htriv : ∀ (g : G) (m : M), g • m = m)
include htriv

/-- For a trivial action `d⁰` vanishes. -/
theorem d0_eq_zero_of_smul_eq_self : d0 G M = 0 :=
  AddMonoidHom.ext fun m => funext fun g => by simp [htriv g m]

/-- For a trivial action there are no nonzero `1`-coboundaries. -/
theorem B1_eq_bot_of_smul_eq_self : B1 G M = ⊥ :=
  AddMonoidHom.range_eq_bot_iff.2 (d0_eq_zero_of_smul_eq_self htriv)

end TrivialAction

end Degree0

section CocycleConditions

/-! The higher differentials and the cocycle conditions they cut out need a multiplication on `G`
and no more, which is the level at which Mathlib states `groupCohomology.IsCocycle₁` and
`IsCocycle₂`. -/

variable (G : Type u) [Mul G] (M : Type v) [AddCommGroup M] [DistribSMul G M]

/-- The degree-`1` differential `(d¹ f) (g, h) = g • f h - f (g * h) + f g`. -/
def d1 : (G → M) →+ (G × G → M) where
  toFun f := fun q => q.1 • f q.2 - f (q.1 * q.2) + f q.1
  map_zero' := by ext q; simp
  map_add' f f' := by ext q; simp only [Pi.add_apply, smul_add]; abel

/-- The degree-`2` differential
`(d² f) (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h)`. -/
def d2 : (G × G → M) →+ (G × G × G → M) where
  toFun f := fun q => q.1 • f (q.2.1, q.2.2) - f (q.1 * q.2.1, q.2.2) + f (q.1, q.2.1 * q.2.2)
    - f (q.1, q.2.1)
  map_zero' := by ext q; simp
  map_add' f f' := by ext q; simp only [Pi.add_apply, smul_add]; abel

variable {G M}

/-- The defining formula for `d¹`. -/
@[simp]
theorem d1_apply (f : G → M) (g h : G) : d1 G M f (g, h) = g • f h - f (g * h) + f g := (rfl)

/-- An equivariant additive map commutes with the degree-`1` differential. -/
theorem map_d1_apply {N : Type w} [AddCommGroup N] [DistribSMul G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (f : G → M) (g h : G) :
    φ (d1 G M f (g, h)) = d1 G N (fun x => φ (f x)) (g, h) := by
  simp only [d1_apply, map_add, map_sub, hφ]

/-- The defining formula for `d²`. -/
@[simp]
theorem d2_apply (f : G × G → M) (g h j : G) :
    d2 G M f (g, h, j) = g • f (h, j) - f (g * h, j) + f (g, h * j) - f (g, h) := (rfl)

/-- A `1`-cochain is killed by `d¹` exactly when it is a `1`-cocycle. Together with Mathlib's
`AddMonoidHom.mem_ker` this is the description of `ker d¹` that `Z¹` is built from. -/
@[simp]
theorem d1_apply_eq_zero_iff {f : G → M} :
    d1 G M f = 0 ↔ groupCohomology.IsCocycle₁ f := by
  simp only [funext_iff, Prod.forall, groupCohomology.IsCocycle₁, d1_apply, Pi.zero_apply]
  exact forall₂_congr fun g h => by rw [sub_add_eq_add_sub, sub_eq_zero, eq_comm]

/-- A `2`-cochain is killed by `d²` exactly when it is a `2`-cocycle. -/
@[simp]
theorem d2_apply_eq_zero_iff {f : G × G → M} :
    d2 G M f = 0 ↔ groupCohomology.IsCocycle₂ f := by
  simp only [funext_iff, Prod.forall, groupCohomology.IsCocycle₂, d2_apply, Pi.zero_apply]
  refine forall₃_congr fun g h j => ?_
  rw [← sub_eq_zero (a := f (g * h, j) + f (g, h)), ← neg_eq_zero]
  exact Eq.congr_left (by abel)

end CocycleConditions

section Complex

/-! `d ∘ d = 0` and degree `0` of the complex need the action to be associative and unital; only
the degree-`1` inverse formula further on needs inverses. -/

variable (G : Type u) [Monoid G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- `d¹ ∘ d⁰ = 0`. -/
theorem d1_comp_d0 : (d1 G M).comp (d0 G M) = 0 := by
  refine AddMonoidHom.ext fun m => funext fun q => ?_
  obtain ⟨g, h⟩ := q
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, d1_apply, d0_apply,
    AddMonoidHom.zero_apply, Pi.zero_apply, smul_sub, ← mul_smul]
  abel

/-- `d² ∘ d¹ = 0`. -/
theorem d2_comp_d1 : (d2 G M).comp (d1 G M) = 0 := by
  refine AddMonoidHom.ext fun f => funext fun q => ?_
  obtain ⟨g, h, j⟩ := q
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, d2_apply, d1_apply,
    AddMonoidHom.zero_apply, Pi.zero_apply, smul_sub, smul_add, ← mul_smul, mul_assoc]
  abel

/-- Degree `0` of the explicit complex: the invariants `M^G`. Unlike `H¹` and `H²` this is a
subgroup and not a quotient. It is named because the low-degree corestriction, the connecting
maps and the `(0, q)` and `(q, 0)` cup shapes all need a degree-`0` carrier to be stated
against. Membership is exposed by Mathlib's `FixedPoints.mem_addSubgroup`, which applies directly
to this abbreviation. -/
abbrev H0 : AddSubgroup M := FixedPoints.addSubgroup G M

variable {G M}

/-- `d¹ ∘ d⁰ = 0`, evaluated at a `0`-cochain. This is the form a consumer of the complex uses;
the composed form needs unfolding before it can rewrite. -/
@[simp]
theorem d1_comp_d0_apply (m : M) : d1 G M (d0 G M m) = 0 :=
  DFunLike.congr_fun (d1_comp_d0 G M) m

/-- `d² ∘ d¹ = 0`, evaluated at a `1`-cochain. -/
@[simp]
theorem d2_comp_d1_apply (f : G → M) : d2 G M (d1 G M f) = 0 :=
  DFunLike.congr_fun (d2_comp_d1 G M) f

/-- For a trivial action `H⁰(G, M) = M`. -/
theorem H0_eq_top_of_smul_eq_self (htriv : ∀ (g : G) (m : M), g • m = m) : H0 G M = ⊤ :=
  eq_top_iff.2 fun m _ => (FixedPoints.mem_addSubgroup G M m).2 fun g => htriv g m

end Complex

section CompatiblePairDegreeZero

/-! Degree zero is a subgroup of the coefficients rather than a quotient, so the pullback along a
compatible pair needs neither inverses in the acting monoids nor a topology anywhere. -/

variable (G : Type u) [Monoid G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- **The compatible-pair pullback in degree zero.** A monoid homomorphism `φ : H →* G` together
with an additive map `f : M →+ N` satisfying `f (φ h • m) = h • f m` carries the `G`-invariants of
`M` into the `H`-invariants of `N`. This is the degree-zero counterpart of
`TauCeti.ContCohomology.explicitMap1` and `explicitMap2`; unlike them it needs no topology at all,
a degree-zero cochain being a single element rather than a function. Restriction and coefficient
maps are its two named instances, by `TauCeti.ContCohomology.explicitRes0_eq_explicitMap0` and
`TauCeti.ContCohomology.explicitCoeff0_eq_explicitMap0`. -/
def explicitMap0 {H : Type*} [Monoid H] {N : Type*} [AddCommGroup N] [DistribMulAction H N]
    (φ : H →* G) (f : M →+ N) (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    H0 G M →+ H0 H N where
  toFun m := ⟨f (m : M), (FixedPoints.mem_addSubgroup H N (f (m : M))).2 fun h => by
    rw [← hequiv h (m : M), (FixedPoints.mem_addSubgroup G M (m : M)).1 m.2 (φ h)]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' _ _ := Subtype.ext (map_add f _ _)

/-- The degree-zero compatible-pair pullback applies the coefficient map. -/
@[simp]
theorem coe_explicitMap0 {H : Type*} [Monoid H] {N : Type*} [AddCommGroup N]
    [DistribMulAction H N] (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (m : H0 G M) :
    (explicitMap0 G M φ f hequiv m : N) = f (m : M) :=
  (rfl)

/-- Pullback along the identity compatible pair is the identity on degree-zero cohomology. -/
@[simp]
theorem explicitMap0_id :
    explicitMap0 G M (MonoidHom.id G) (AddMonoidHom.id M) (fun _ _ => rfl) =
      AddMonoidHom.id (H0 G M) :=
  AddMonoidHom.ext fun _ => Subtype.ext (rfl)

/-- Pullback in degree zero respects composition of compatible pairs: it is contravariant in the
group homomorphism and covariant in the coefficient map. Compatibility of the composite pair is
not a hypothesis: it is `hequiv` at `ψ k` followed by `hequivq`. -/
theorem explicitMap0_comp {H : Type*} [Monoid H] {N : Type*} [AddCommGroup N]
    [DistribMulAction H N] {K : Type*} [Monoid K] {P : Type*} [AddCommGroup P]
    [DistribMulAction K P] (φ : H →* G) (f : M →+ N)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (ψ : K →* H) (q : N →+ P)
    (hequivq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) :
    explicitMap0 G M (φ.comp ψ) (q.comp f)
        (fun k m => (congrArg (q : N → P) (hequiv (ψ k) m)).trans (hequivq k (f m))) =
      (explicitMap0 H N ψ q hequivq).comp (explicitMap0 G M φ f hequiv) :=
  AddMonoidHom.ext fun _ => Subtype.ext (rfl)

/-- A coefficient homomorphism induces an additive map on degree-zero cohomology: the
compatible-pair pullback along the identity of the acting monoid. -/
def explicitCoeff0 {N : Type*} [AddCommGroup N] [DistribMulAction G N] (f : M →+[G] N) :
    H0 G M →+ H0 G N :=
  explicitMap0 G M (MonoidHom.id G) f.toAddMonoidHom (fun g m => f.map_smul g m)

/-- The degree-zero coefficient map applies the underlying coefficient homomorphism. -/
@[simp]
theorem coe_explicitCoeff0 {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    (f : M →+[G] N) (m : H0 G M) : (explicitCoeff0 G M f m : N) = f (m : M) :=
  coe_explicitMap0 G M (MonoidHom.id G) f.toAddMonoidHom (fun g m => f.map_smul g m) m

/-- A coefficient map in degree zero is the compatible-pair pullback along the identity of the
acting monoid. -/
theorem explicitCoeff0_eq_explicitMap0 {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    (f : M →+[G] N) :
    explicitCoeff0 G M f =
      explicitMap0 G M (MonoidHom.id G) f.toAddMonoidHom (fun g m => f.map_smul g m) :=
  (rfl)

/-- The identity coefficient map induces the identity on degree-zero cohomology. -/
@[simp]
theorem explicitCoeff0_id : explicitCoeff0 G M (DistribMulActionHom.id G) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun m => Subtype.ext (coe_explicitCoeff0 G M _ m)

/-- Coefficient maps on degree-zero cohomology respect composition. -/
theorem explicitCoeff0_comp {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    {P : Type*} [AddCommGroup P] [DistribMulAction G P] (f : M →+[G] N) (q : N →+[G] P) :
    explicitCoeff0 G M (q.comp f) = (explicitCoeff0 G N q).comp (explicitCoeff0 G M f) :=
  AddMonoidHom.ext fun _ => Subtype.ext (rfl)

/-- A bijective equivariant homomorphism of coefficients induces a bijection on degree-zero
cohomology. -/
theorem explicitCoeff0_bijective {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    {f : M →+[G] N} (hf : Function.Bijective f) : Function.Bijective (explicitCoeff0 G M f) := by
  refine ⟨fun x y h => Subtype.ext (hf.1 ?_), fun y => ?_⟩
  · simpa only [coe_explicitCoeff0] using congrArg Subtype.val h
  · obtain ⟨m, hm⟩ := hf.2 (y : N)
    refine ⟨⟨m, (FixedPoints.mem_addSubgroup G M m).2 fun g => hf.1 ?_⟩, Subtype.ext ?_⟩
    · rw [map_smul f, hm]
      exact (FixedPoints.mem_addSubgroup G N (y : N)).1 y.2 g
    · simpa only [coe_explicitCoeff0] using hm

end CompatiblePairDegreeZero

section RestrictionDegreeZero

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (U : Subgroup G)

/-- **Restriction in degree zero**, the inclusion `H⁰(G, M) → H⁰(U, M)`: the compatible-pair
pullback along the inclusion of the subgroup, with the identity on the coefficients. -/
def explicitRes0 : H0 G M →+ H0 U M :=
  explicitMap0 G M U.subtype (AddMonoidHom.id M) (fun _ _ => rfl)

/-- Restriction in degree zero does not change the underlying coefficient. -/
@[simp]
theorem coe_explicitRes0 (m : H0 G M) : (explicitRes0 G M U m : M) = m :=
  coe_explicitMap0 G M U.subtype (AddMonoidHom.id M) (fun _ _ => rfl) m

/-- Restriction in degree zero is natural in equivariant coefficient homomorphisms. -/
theorem map_explicitRes0 {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    (f : M →+[G] N) (m : H0 G M) :
    fixedPointsMap f U (explicitRes0 G M U m) =
      explicitRes0 G N U (explicitCoeff0 G M f m) := by
  ext
  rw [coe_explicitRes0, coe_explicitCoeff0, ← coe_explicitRes0 G M U m]
  exact coe_fixedPointsMap f U _

/-- Restriction in degree zero is the compatible-pair pullback along the inclusion of the subgroup
with the identity on the coefficients. -/
theorem explicitRes0_eq_explicitMap0 :
    explicitRes0 G M U =
      explicitMap0 G M U.subtype (AddMonoidHom.id M) (fun _ _ => rfl) :=
  (rfl)

end RestrictionDegreeZero

end Differentials

section Cocycles

variable (G : Type u) [Mul G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M]

/-- The continuous `1`-cocycles `Z¹ = C¹ ⊓ ker d¹`; the closure of the cocycle condition under
the group operations is the one `AddMonoidHom.ker` already carries.
`TauCeti.ContCohomology.mem_Z1_iff` restates membership with the kernel spelled by Mathlib's
`groupCohomology.IsCocycle₁`. -/
def Z1 : AddSubgroup (G → M) := C1 G M ⊓ (d1 G M).ker

/-- The continuous `2`-cocycles `Z² = C² ⊓ ker d²`. -/
def Z2 : AddSubgroup (G × G → M) := C2 G M ⊓ (d2 G M).ker

/-- The `2`-coboundaries `B² = d¹(C¹)`, the image of the **continuous** `1`-cochains. The
restriction to `C¹` is what the complex asks for: `B²` has to be the image of the cochains the
complex is built from for `Z²/B²` to be the cohomology of the *continuous* complex, whereas the
image of all of `G → M` is the coboundaries of the abstract complex. -/
def B2 : AddSubgroup (G × G → M) := AddSubgroup.map (d1 G M) (C1 G M)

variable {G M}

/-- A cochain is a continuous `1`-cocycle exactly when it is continuous and satisfies the
`1`-cocycle identity. -/
@[simp]
theorem mem_Z1_iff {f : G → M} :
    f ∈ Z1 G M ↔ Continuous f ∧ groupCohomology.IsCocycle₁ f :=
  AddSubgroup.mem_inf.trans
    (and_congr mem_C1_iff (AddMonoidHom.mem_ker.trans d1_apply_eq_zero_iff))

/-- A cochain is a continuous `2`-cocycle exactly when it is continuous and satisfies the
`2`-cocycle identity. -/
@[simp]
theorem mem_Z2_iff {f : G × G → M} :
    f ∈ Z2 G M ↔ Continuous f ∧ groupCohomology.IsCocycle₂ f :=
  AddSubgroup.mem_inf.trans
    (and_congr mem_C2_iff (AddMonoidHom.mem_ker.trans d2_apply_eq_zero_iff))

/-- Membership in `B²` exhibits a *continuous* primitive. -/
@[simp]
theorem mem_B2_iff {f : G × G → M} :
    f ∈ B2 G M ↔ ∃ c : G → M, Continuous c ∧ d1 G M c = f := by
  simp only [B2, AddSubgroup.mem_map, mem_C1_iff]

/-- Membership in `B²`, with the primitive spelled out pointwise as in Mathlib's unbundled
`2`-coboundary condition. This is the degree-`2` counterpart of
`TauCeti.ContCohomology.mem_B1_iff`, which can be stated with `groupCohomology.IsCoboundary₁`
itself because `B¹` carries no continuity restriction on the primitive. -/
theorem mem_B2_iff' {f : G × G → M} :
    f ∈ B2 G M ↔ ∃ c : G → M, Continuous c ∧ ∀ g h : G, g • c h - c (g * h) + c g = f (g, h) := by
  simp only [mem_B2_iff, funext_iff, Prod.forall, d1_apply]

/-- A continuous `2`-coboundary satisfies Mathlib's unbundled `2`-coboundary condition. -/
theorem isCoboundary₂_of_mem_B2 {f : G × G → M} (hf : f ∈ B2 G M) :
    groupCohomology.IsCoboundary₂ f := by
  obtain ⟨c, -, hc⟩ := mem_B2_iff'.1 hf
  exact ⟨c, hc⟩

variable (G M)

/-- Continuous `1`-cocycles are continuous `1`-cochains. -/
theorem Z1_le_C1 : Z1 G M ≤ C1 G M := inf_le_left

/-- Continuous `2`-cocycles are continuous `2`-cochains. -/
theorem Z2_le_C2 : Z2 G M ≤ C2 G M := inf_le_left

end Cocycles

section FiniteGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [Fintype G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- The additive map sending a finite-group `2`-cocycle `f` to the invariant
`∑ x, f (x, g)` obtained by summing it over its first argument. -/
def sumCocycle (g : G) : Z2 G M →+ H0 G M where
  toFun f := ⟨∑ x : G, (f : G × G → M) (x, g), by
    rw [FixedPoints.mem_addSubgroup]
    intro y
    have hf := (mem_Z2_iff.mp f.property).2
    calc
      y • ∑ x : G, (f : G × G → M) (x, g) =
          ∑ x : G, y • (f : G × G → M) (x, g) := by rw [Finset.smul_sum]
      _ = ∑ x : G, ((f : G × G → M) (y * x, g) +
          (f : G × G → M) (y, x) - (f : G × G → M) (y, x * g)) := by
        apply Finset.sum_congr rfl
        intro x _
        have h := hf y x g
        rw [eq_sub_iff_add_eq]
        exact h.symm
      _ = (∑ x : G, (f : G × G → M) (y * x, g)) +
          ∑ x : G, (f : G × G → M) (y, x) -
            ∑ x : G, (f : G × G → M) (y, x * g) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ x : G, (f : G × G → M) (x, g) := by
        have hleft : (∑ x : G, (f : G × G → M) (y * x, g)) =
            ∑ x : G, (f : G × G → M) (x, g) :=
          Fintype.sum_bijective _ (Group.mulLeft_bijective y) _ _ (fun _ ↦ rfl)
        have hright : (∑ x : G, (f : G × G → M) (y, x * g)) =
            ∑ x : G, (f : G × G → M) (y, x) :=
          Fintype.sum_bijective _ (Group.mulRight_bijective g) _ _ (fun _ ↦ rfl)
        rw [hleft, hright, add_sub_cancel_right]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' f f' := Subtype.ext (by simp [Finset.sum_add_distrib])

/-- The value of `sumCocycle` is the sum of the cocycle over its first argument. -/
@[simp]
theorem sumCocycle_val (g : G) (f : Z2 G M) :
    (sumCocycle g f : M) = ∑ x : G, (f : G × G → M) (x, g) :=
  (rfl)

end FiniteGroup

section Normalizations

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- A continuous `1`-cocycle vanishes at `1`. This is a lemma and not part of the definition of
`Z¹`: cochains here are not normalised. -/
theorem map_one_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) : f 1 = 0 :=
  groupCohomology.map_one_of_isCocycle₁ (mem_Z1_iff.1 hf).2

/-- A continuous `2`-cocycle takes the same value at `(1, g)` as at `(1, 1)`. -/
theorem map_one_fst_of_mem_Z2 {f : G × G → M} (hf : f ∈ Z2 G M) (g : G) : f (1, g) = f (1, 1) :=
  groupCohomology.map_one_fst_of_isCocycle₂ (mem_Z2_iff.1 hf).2 g

/-- A continuous `2`-cocycle satisfies `f (g, 1) = g • f (1, 1)`. -/
theorem map_one_snd_of_mem_Z2 {f : G × G → M} (hf : f ∈ Z2 G M) (g : G) :
    f (g, 1) = g • f (1, 1) :=
  groupCohomology.map_one_snd_of_isCocycle₂ (mem_Z2_iff.1 hf).2 g

end Normalizations

section Inverse

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- The inverse formula for a continuous `1`-cocycle. -/
@[scoped simp]
theorem map_inv_of_mem_Z1 {f : G → M} (hf : f ∈ Z1 G M) (g : G) : g • f g⁻¹ = -f g :=
  groupCohomology.map_inv_of_isCocycle₁ (mem_Z1_iff.1 hf).2 g

/-- **Continuous `1`-cocycles are determined by their values on a topological generating set.**
Two continuous `1`-cocycles with values in a `T1` module that agree on a set `s` whose generated
subgroup is dense agree everywhere. -/
theorem eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top [IsTopologicalGroup G]
    [T1Space M] {c₁ c₂ : G → M} (h₁ : c₁ ∈ Z1 G M) (h₂ : c₂ ∈ Z1 G M) {s : Set G}
    (hs : (Subgroup.closure s).topologicalClosure = ⊤) (h : Set.EqOn c₁ c₂ s) : c₁ = c₂ := by
  obtain ⟨hcont, hcoc⟩ := mem_Z1_iff.1 ((Z1 G M).sub_mem h₁ h₂)
  exact sub_eq_zero.1 (groupCohomology.eq_zero_of_eqOn_zero_of_topologicalClosure_closure_eq_top
    hcoc hcont hs fun g hg ↦ sub_eq_zero.2 (h hg))

end Inverse

section Continuity

variable {G : Type u} [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DistribSMul G M] [ContinuousSMul G M]

/-- Every `1`-coboundary is continuous. -/
theorem continuous_d0_apply [ContinuousSub M] (m : M) : Continuous (d0 G M m) :=
  (continuous_id.smul continuous_const).sub continuous_const

variable [IsTopologicalAddGroup M] (G M)

/-- `1`-coboundaries are continuous `1`-cochains. -/
theorem B1_le_C1 : B1 G M ≤ C1 G M := by
  intro f hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  exact continuous_d0_apply m

end Continuity

section ContinuityMul

/-! `d¹` preserves continuity already at the level at which `d¹` itself is defined: a
multiplication on `G` and a distributive scalar action, with no unit and no associativity. -/

variable {G : Type u} [Mul G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [DistribSMul G M] [ContinuousSMul G M]

/-- `d¹` preserves continuity. -/
theorem continuous_d1_apply [ContinuousAdd M] [ContinuousSub M] {f : G → M} (hf : Continuous f) :
    Continuous (d1 G M f) :=
  ((continuous_fst.smul (hf.comp continuous_snd)).sub
    (hf.comp (continuous_fst.mul continuous_snd))).add (hf.comp continuous_fst)

variable [IsTopologicalAddGroup M] (G M)

/-- `2`-coboundaries are continuous `2`-cochains. -/
theorem B2_le_C2 : B2 G M ≤ C2 G M := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  exact continuous_d1_apply hc

end ContinuityMul

section ContinuityAction

variable (G : Type u) [Monoid G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `d ∘ d = 0` in the form the degree-`1` quotient needs. -/
theorem B1_le_Z1 : B1 G M ≤ Z1 G M := by
  intro f hf
  obtain ⟨m, rfl⟩ := AddMonoidHom.mem_range.1 hf
  exact mem_Z1_iff.2 ⟨continuous_d0_apply m, d1_apply_eq_zero_iff.1 (d1_comp_d0_apply m)⟩

end ContinuityAction

section ContinuityMulAction

variable (G : Type u) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `d ∘ d = 0` in the form the degree-`2` quotient needs. -/
theorem B2_le_Z2 : B2 G M ≤ Z2 G M := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  exact mem_Z2_iff.2 ⟨continuous_d1_apply hc, d2_apply_eq_zero_iff.1 (d2_comp_d1_apply c)⟩

end ContinuityMulAction

section CohomologyDegree1

/-! Degree `1` of the cohomology is formed exactly where `TauCeti.ContCohomology.B1_le_Z1` holds:
under a weaker action `B¹` need not consist of cocycles and the quotient below would silently be
by `B¹ ⊓ Z¹`. -/

variable (G : Type u) [Monoid G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [hcont : ContinuousSMul G M]

/-- The first continuous cohomology group `H¹(G, M) = Z¹/B¹`.

The denominator is `B¹` viewed inside `Z¹`, in Mathlib's `AddSubgroup.addSubgroupOf` spelling,
so that no proof term enters the quotient subgroup. The hypotheses in force are those of
`TauCeti.ContCohomology.B1_le_Z1`, so the subgroup divided out really is the whole of `B¹`:
`AddSubgroup.map_addSubgroupOf_eq_of_le (B1_le_Z1 G M)` says its image in `G → M` is `B¹` itself.

`H¹` is used as a bare additive group. It does inherit a quotient topology from the *pointwise*
topology on `G → M`, and that topology is not the intended one: it need not be discrete. For
trivial `ZMod 2` coefficients on a product of infinitely many copies of `C₂`, no finite set of
evaluations isolates the zero character. The comparison with canonical continuous cohomology is
therefore stated against `DiscreteH1`. -/
abbrev H1 :=
  let _h := B1_le_Z1 G M
  (Z1 G M) ⧸ ((B1 G M).addSubgroupOf (Z1 G M))

/-- The class map in degree `1`. -/
abbrev H1pi : (Z1 G M) →+ H1 G M := QuotientAddGroup.mk' _

/-- `H¹(G, M)` equipped with the discrete topology used by the comparison with canonical
continuous cohomology. -/
def DiscreteH1 : Type _ := H1 G M

/-- `DiscreteH1 G M` has the additive group structure of `H¹(G, M)`. -/
instance : AddCommGroup (DiscreteH1 G M) :=
  inferInstanceAs (AddCommGroup (H1 G M))

/-- `DiscreteH1 G M` carries the discrete topology. -/
instance : TopologicalSpace (DiscreteH1 G M) := ⊥

/-- The topology on `DiscreteH1 G M` is discrete. -/
instance : DiscreteTopology (DiscreteH1 G M) := ⟨rfl⟩

/-- The identity as an additive equivalence, so that the quotient-class computations on
representatives stay available after passing to the discrete object. -/
def discreteH1Equiv : DiscreteH1 G M ≃+ H1 G M :=
  AddEquiv.refl _

variable {G M}

omit hcont in
/-- A continuous `1`-cocycle has trivial class exactly when it is a coboundary. -/
theorem H1pi_eq_zero_iff {f : Z1 G M} :
    (f : H1 G M) = 0 ↔ (f : G → M) ∈ B1 G M := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

omit hcont in
/-- Two continuous `1`-cocycles have the same class exactly when they differ by a coboundary. -/
@[simp]
theorem H1pi_eq_iff {f f' : Z1 G M} :
    (f : H1 G M) = (f' : H1 G M) ↔ (f : G → M) - f' ∈ B1 G M := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

/-- **`H¹` inherits the exponent of its coefficients.** If `n` kills the coefficient module `M`,
then it kills every class in `H¹(G, M)`. -/
theorem nsmul_H1_eq_zero {n : ℕ} (h : ∀ m : M, n • m = 0) (x : H1 G M) : n • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    have hc : n • c = 0 := Subtype.ext (funext fun _ ↦ by simp [h])
    rw [← QuotientAddGroup.mk_nsmul, hc, QuotientAddGroup.mk_zero]

end CohomologyDegree1

section CohomologyDegree2

/-! Degree `2` needs a continuous multiplication on `G` besides, this being what makes `d¹`
preserve continuity and hence what
`TauCeti.ContCohomology.B2_le_Z2` — the inclusion the quotient below divides by — asks for. -/

variable (G : Type u) [Monoid G] [TopologicalSpace G] [hcontMul : ContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [hcontSmul : ContinuousSMul G M]

/-- The second continuous cohomology group `H²(G, M) = Z²/B²`.

As for `H¹` the denominator is `B²` viewed inside `Z²`, and the hypotheses in force are those of
`TauCeti.ContCohomology.B2_le_Z2`, so the subgroup divided out really is the whole of `B²`. The
inherited quotient topology is again not the intended one, and `H²` is used as a bare additive
group. -/
abbrev H2 :=
  let _h := B2_le_Z2 G M
  (Z2 G M) ⧸ ((B2 G M).addSubgroupOf (Z2 G M))

/-- The class map in degree `2`. -/
abbrev H2pi : (Z2 G M) →+ H2 G M := QuotientAddGroup.mk' _

/-- `H²(G, M)` equipped with the discrete topology used by the comparison with canonical
continuous cohomology. -/
def DiscreteH2 : Type _ := H2 G M

/-- `DiscreteH2 G M` has the additive group structure of `H²(G, M)`. -/
instance : AddCommGroup (DiscreteH2 G M) :=
  inferInstanceAs (AddCommGroup (H2 G M))

/-- `DiscreteH2 G M` carries the discrete topology. -/
instance : TopologicalSpace (DiscreteH2 G M) := ⊥

/-- The topology on `DiscreteH2 G M` is discrete. -/
instance : DiscreteTopology (DiscreteH2 G M) := ⟨rfl⟩

/-- The degree-`2` counterpart of `TauCeti.ContCohomology.discreteH1Equiv`. -/
def discreteH2Equiv : DiscreteH2 G M ≃+ H2 G M :=
  AddEquiv.refl _

variable {G M}

omit hcontMul hcontSmul in
/-- A continuous `2`-cocycle has trivial class exactly when it is a coboundary. -/
theorem H2pi_eq_zero_iff {f : Z2 G M} :
    (f : H2 G M) = 0 ↔ (f : G × G → M) ∈ B2 G M := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

omit hcontMul hcontSmul in
/-- Two continuous `2`-cocycles have the same class exactly when they differ by a coboundary. -/
@[simp]
theorem H2pi_eq_iff {f f' : Z2 G M} :
    (f : H2 G M) = (f' : H2 G M) ↔ (f : G × G → M) - f' ∈ B2 G M := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

/-- **`H²` inherits the exponent of its coefficients.** If `n` kills the coefficient module `M`,
then it kills every class in `H²(G, M)`. -/
theorem nsmul_H2_eq_zero {n : ℕ} (h : ∀ m : M, n • m = 0) (x : H2 G M) : n • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    have hc : n • c = 0 := Subtype.ext (funext fun _ ↦ by simp [h])
    rw [← QuotientAddGroup.mk_nsmul, hc, QuotientAddGroup.mk_zero]

end CohomologyDegree2

section TrivialGroup

variable (G : Type u) [Monoid G] [TopologicalSpace G] [Subsingleton G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **A trivial group has vanishing `H¹`.** -/
instance subsingleton_H1_of_subsingleton : Subsingleton (H1 G M) :=
  have : Subsingleton (Z1 G M) := ⟨fun f f' => Subtype.ext <| funext fun g => by
    rw [Subsingleton.elim g 1, map_one_of_mem_Z1 f.2, map_one_of_mem_Z1 f'.2]⟩
  QuotientAddGroup.mk_surjective.subsingleton

/-- **A trivial group has vanishing `H²`.** -/
instance subsingleton_H2_of_subsingleton [ContinuousMul G] : Subsingleton (H2 G M) :=
  subsingleton_of_forall_eq 0 fun x => QuotientAddGroup.induction_on x fun f =>
    H2pi_eq_zero_iff.2 <| mem_B2_iff'.2 ⟨fun _ => (f : G × G → M) (1, 1), continuous_const,
      fun g h => by rw [Subsingleton.elim g 1, Subsingleton.elim h 1, one_smul, sub_add_cancel]⟩

end TrivialGroup

section TrivialCoefficients

variable (G : Type u) [Monoid G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [Subsingleton M]

/-- **A zero coefficient group has vanishing `H¹`.** -/
instance subsingleton_H1_of_subsingleton_coefficients : Subsingleton (H1 G M) :=
  QuotientAddGroup.mk_surjective.subsingleton

/-- **A zero coefficient group has vanishing `H²`.** -/
instance subsingleton_H2_of_subsingleton_coefficients [ContinuousMul G] : Subsingleton (H2 G M) :=
  QuotientAddGroup.mk_surjective.subsingleton

end TrivialCoefficients

section TrivialAction

/-! Identifying the cocycles with homomorphisms uses only that `G` acts trivially by a
distributive scalar action; associativity of the action is needed only to form `H¹`. -/

variable {G : Type u} [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- For a trivial action a continuous `1`-cocycle is additive. -/
theorem map_mul_of_smul_eq_self_of_mem_Z1 [Mul G] {f : G → M} (hf : f ∈ Z1 G M) (a b : G) :
    f (a * b) = f a + f b := by
  have h := (mem_Z1_iff.1 hf).2 a b
  rw [htriv a (f b)] at h
  exact h.trans (add_comm _ _)

variable [Monoid G]

/-- For a trivial action the pointwise `Multiplicative.toAdd` of a continuous homomorphism
`G → Multiplicative M` is a continuous `1`-cocycle. -/
theorem mem_Z1_of_smul_eq_self_of_continuousMonoidHom
    (φ : ContinuousMonoidHom G (Multiplicative M)) :
    (fun g => Multiplicative.toAdd (φ g)) ∈ Z1 G M :=
  mem_Z1_iff.2 ⟨map_continuous φ, fun a b => by
    simp only [htriv a (Multiplicative.toAdd (φ b)), map_mul φ a b, toAdd_mul]
    exact add_comm _ _⟩

/-- For a trivial action the continuous `1`-cocycles are exactly the continuous homomorphisms
`G → Multiplicative M`. This is the continuous analogue of Mathlib's
`groupCohomology.cocycles₁IsoOfIsTrivial`. -/
def Z1EquivOfSmulEqSelf : Z1 G M ≃+ Additive (ContinuousMonoidHom G (Multiplicative M)) where
  toFun f := Additive.ofMul
    { toMonoidHom :=
        MonoidHom.mk' (fun g => Multiplicative.ofAdd ((f : G → M) g)) fun a b => by
          rw [map_mul_of_smul_eq_self_of_mem_Z1 htriv f.2 a b, ofAdd_add]
      continuous_toFun := (mem_Z1_iff.1 f.2).1 }
  invFun φ :=
    ⟨fun g => Multiplicative.toAdd ((Additive.toMul φ) g),
      mem_Z1_of_smul_eq_self_of_continuousMonoidHom htriv (Additive.toMul φ)⟩
  left_inv f := Subtype.ext rfl
  right_inv φ := Additive.toMul.injective (DFunLike.ext _ _ fun _ => rfl)
  map_add' f g := Additive.toMul.injective (DFunLike.ext _ _ fun _ => rfl)

/-- The homomorphism attached to a continuous `1`-cocycle by `Z1EquivOfSmulEqSelf` is the cocycle
itself. -/
@[simp]
theorem Z1EquivOfSmulEqSelf_apply (f : Z1 G M) (g : G) :
    Additive.toMul (Z1EquivOfSmulEqSelf htriv f) g = Multiplicative.ofAdd ((f : G → M) g) := (rfl)

/-- The continuous `1`-cocycle attached to a continuous homomorphism by `Z1EquivOfSmulEqSelf` is
the homomorphism itself. -/
@[simp]
theorem Z1EquivOfSmulEqSelf_symm_apply
    (φ : Additive (ContinuousMonoidHom G (Multiplicative M))) (g : G) :
    (((Z1EquivOfSmulEqSelf htriv).symm φ : Z1 G M) : G → M) g =
      Multiplicative.toAdd ((Additive.toMul φ) g) := (rfl)

end TrivialAction

section TrivialCohomology

variable {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- For a trivial action `H¹(G, M)` is the group of continuous homomorphisms
`G →ₜ* Multiplicative M`. This is the continuous analogue of Mathlib's
`groupCohomology.H1IsoOfIsTrivial`.

Continuity is what makes this useful rather than decorative: without it the right-hand side is the
group of abstract homomorphisms, which for a profinite group is enormous. -/
def H1EquivOfSmulEqSelf :
    H1 G M ≃+ Additive (ContinuousMonoidHom G (Multiplicative M)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (M := (B1 G M).addSubgroupOf (Z1 G M)) (N := ⊥) (by
        rw [B1_eq_bot_of_smul_eq_self htriv]
        exact AddSubgroup.bot_addSubgroupOf _)).trans
    (QuotientAddGroup.quotientBot.trans (Z1EquivOfSmulEqSelf htriv))

/-- `H1EquivOfSmulEqSelf` sends the class of a continuous `1`-cocycle to the homomorphism it
is. -/
@[simp]
theorem H1EquivOfSmulEqSelf_mk (f : Z1 G M) :
    H1EquivOfSmulEqSelf htriv (f : H1 G M) = Z1EquivOfSmulEqSelf htriv f := by
  simp only [H1EquivOfSmulEqSelf, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  rw [← QuotientAddGroup.quotientBot_symm_apply f, AddEquiv.apply_symm_apply]

/-- The class of the continuous `1`-cocycle attached to a continuous homomorphism by
`H1EquivOfSmulEqSelf`. -/
@[simp]
theorem H1EquivOfSmulEqSelf_symm_apply
    (φ : Additive (ContinuousMonoidHom G (Multiplicative M))) :
    (H1EquivOfSmulEqSelf htriv).symm φ = ((Z1EquivOfSmulEqSelf htriv).symm φ : H1 G M) :=
  (H1EquivOfSmulEqSelf htriv).symm_apply_eq.2
    (((Z1EquivOfSmulEqSelf htriv).apply_symm_apply φ).symm.trans
      (H1EquivOfSmulEqSelf_mk htriv _).symm)

/-- A compact monoid has vanishing first continuous cohomology with trivial, discrete,
torsion-free coefficients. In particular, this applies to trivial integer coefficients. -/
theorem subsingleton_H1_of_isAddTorsionFree [CompactSpace G] [DiscreteTopology M]
    [IsAddTorsionFree M] : Subsingleton (H1 G M) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ (H1EquivOfSmulEqSelf htriv).injective ?_
  apply Additive.toMul.injective
  exact (Additive.toMul ((H1EquivOfSmulEqSelf htriv) x)).eq_one_of_isMulTorsionFree

end TrivialCohomology

end TauCeti.ContCohomology
