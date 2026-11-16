/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Identities of unbundled cocycles

Facts about cocycles in the sense of Mathlib's unbundled `groupCohomology.IsCocycle₁`,
`groupCohomology.IsCocycle₂` and `groupCohomology.IsMulCocycle₁`, which need no topology and no
representation:

* `groupCohomology.smul_apply_inv_mul_mul_of_isCocycle₁`: conjugating the argument by `k` and
  then acting by `k` adds `m • f k - f k` to the value at `m`, for any scalar multiplication of
  `G` on `M`: `k • f (k⁻¹ * m * k) = m • f k - f k + f m`.
* `groupCohomology.smul_zero_of_isCocycle₁`: an action admitting a `1`-cocycle fixes `0`.
* `groupCohomology.IsCocycle₁.add`, `groupCohomology.IsMulCocycle₁.mul`,
  `groupCohomology.IsMulCocycle₁.pow`: pointwise sums, products and powers of `1`-cocycles are
  `1`-cocycles.
* `groupCohomology.isCocycle₁_smul_sub`, `groupCohomology.IsCoboundary₁.isCocycle₁`,
  `groupCohomology.isMulCocycle₁_smul_div`, `groupCohomology.IsMulCoboundary₁.isMulCocycle₁`:
  principal crossed maps (`1`-coboundaries) for distributive actions are `1`-cocycles.
* `groupCohomology.zeroLocus`: the zero locus `{g | f g = 0}` is a subgroup of `G`, for any group
  action (not necessarily distributive) admitting the cocycle. As a set it is `f ⁻¹' {0}`
  (`groupCohomology.coe_zeroLocus`). `GroupCohomology/Cocycle/Topology.lean` shows it is closed
  when `f` is continuous into a `T1` space, and deduces that such an `f` vanishing on a
  topological generating set vanishes everywhere.
* `groupCohomology.oneLocus`: the multiplicative counterpart `{g | f g = 1}` for any group action
  on a (not necessarily commutative) group `M` and any map satisfying `f (g * h) = g • f h * f g`.
* `groupCohomology.IsCocycle₁.comp_subtype`, `groupCohomology.IsCocycle₁.comp_inclusion`:
  restricting a `1`-cocycle along a subgroup inclusion gives a `1`-cocycle whose zero locus
  intersects the original zero locus with the smaller subgroup
  (`groupCohomology.map_subtype_zeroLocus_comp_subtype`,
  `groupCohomology.map_subtype_zeroLocus_comp_inclusion`), and similarly for `oneLocus`.
* `groupCohomology.IsCocycle₁.conj`: for a `G`-module `M`, a `1`-cocycle `c` on a subgroup `H`
  conjugates to the `1`-cocycle `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`, and its zero locus is
  conjugated by `g` (`groupCohomology.map_subtype_zeroLocus_conj`), with the non-commutative
  counterpart `groupCohomology.map_subtype_oneLocus_conj`.

* `TauCeti.isCocycle₁_ext_of_forall_mem_zpowers`: a one-cocycle on a cyclic group is
  determined by its value at a generator.
* `TauCeti.isCocycle₂_ext_of_forall_mem_zpowers`: a two-cocycle on a cyclic group is
  determined by its values with the generator as second argument.
* `TauCeti.sum_smul_apply_eq_zero_of_isCocycle₁`: on a finite group, the group norm kills
  every value of a one-cocycle.

Continuous cohomology uses the conjugation identity in the five-term sequence and in
transgression, and the cyclic-group facts in its first and second cohomology computations.
-/

public section

namespace groupCohomology

/-- Conjugating the argument of a `1`-cocycle by `k` and then acting by `k` adds `m • c k - c k`
to its value at `m`: `k • c (k⁻¹ * m * k) = m • c k - c k + c m`. Only a scalar multiplication
of `G` on `M` is needed, not an action. -/
theorem smul_apply_inv_mul_mul_of_isCocycle₁ {G M : Type*} [Group G] [AddCommGroup M] [SMul G M]
    {c : G → M} (hc : IsCocycle₁ c) (k m : G) :
    k • c (k⁻¹ * m * k) = m • c k - c k + c m := by
  have hmul : k * (k⁻¹ * m * k) = m * k := by group
  have h := hc k (k⁻¹ * m * k)
  rw [hmul, hc m k] at h
  rw [eq_sub_of_add_eq h.symm]
  abel

/-- A monoid action on an additive group that admits a `1`-cocycle fixes `0`. -/
theorem smul_zero_of_isCocycle₁ {G M : Type*} [Monoid G] [AddCommGroup M] [MulAction G M]
    {f : G → M} (hf : IsCocycle₁ f) (g : G) : g • (0 : M) = 0 := by
  simpa only [mul_one, map_one_of_isCocycle₁ hf, right_eq_add] using hf g 1

/-- A pointwise sum of `1`-cocycles is a `1`-cocycle. -/
theorem IsCocycle₁.add {G M : Type*} [Mul G] [AddCommGroup M] [DistribSMul G M]
    {f f' : G → M} (hf : IsCocycle₁ f) (hf' : IsCocycle₁ f') : IsCocycle₁ (f + f') :=
  fun g h => by
    simp only [Pi.add_apply, hf g h, hf' g h, smul_add]
    abel

/-- For a distributive action, the principal crossed map `g ↦ g • a - a` is a `1`-cocycle. -/
theorem isCocycle₁_smul_sub {G M : Type*} [Monoid G] [AddCommGroup M] [DistribMulAction G M]
    (a : M) : IsCocycle₁ fun g : G => g • a - a := fun g h => by
  dsimp only
  rw [smul_sub, mul_smul]
  abel

/-- Every `1`-coboundary for a distributive action is a `1`-cocycle. -/
theorem IsCoboundary₁.isCocycle₁ {G M : Type*} [Monoid G] [AddCommGroup M] [DistribMulAction G M]
    {f : G → M} (hf : IsCoboundary₁ f) : IsCocycle₁ f := by
  obtain ⟨a, ha⟩ := hf
  exact (funext fun g => (ha g).symm) ▸ isCocycle₁_smul_sub a

/-- A pointwise product of multiplicative `1`-cocycles is a multiplicative `1`-cocycle. -/
theorem IsMulCocycle₁.mul {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    {f f' : G → M} (hf : IsMulCocycle₁ f) (hf' : IsMulCocycle₁ f') : IsMulCocycle₁ (f * f') :=
  fun g h => by
    simp only [Pi.mul_apply, hf g h, hf' g h, smul_mul']
    ac_rfl

/-- A pointwise power of a multiplicative `1`-cocycle is a multiplicative `1`-cocycle. -/
theorem IsMulCocycle₁.pow {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    {f : G → M} (hf : IsMulCocycle₁ f) (n : ℕ) : IsMulCocycle₁ (f ^ n) := fun g h => by
  simp only [Pi.pow_apply, hf g h, mul_pow, smul_pow']

/-- For a multiplicative distributive action on a commutative group, the principal crossed map
`g ↦ g • a / a` is a multiplicative `1`-cocycle. -/
theorem isMulCocycle₁_smul_div {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]
    (a : M) : IsMulCocycle₁ fun g : G => g • a / a := fun g h => by
  dsimp only
  rw [smul_div', mul_smul, div_mul_div_cancel]

/-- Every multiplicative `1`-coboundary for a distributive action is a multiplicative
`1`-cocycle. -/
theorem IsMulCoboundary₁.isMulCocycle₁ {G M : Type*} [Monoid G] [CommGroup M]
    [MulDistribMulAction G M] {f : G → M} (hf : IsMulCoboundary₁ f) : IsMulCocycle₁ f := by
  obtain ⟨a, ha⟩ := hf
  exact (funext fun g => (ha g).symm) ▸ isMulCocycle₁_smul_div a

section OneLocus

/-- A map into a group satisfying the crossed identity `f (g * h) = g • f h * f g` sends `1` to
`1`, without any commutativity assumption on the target. -/
theorem map_one_of_apply_mul {G M : Type*} [Monoid G] [Group M] [MulAction G M] {f : G → M}
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) : f 1 = 1 := by
  simpa only [mul_one, one_smul, left_eq_mul] using hf 1 1

/-- A monoid action on a group that admits a map satisfying `f (g * h) = g • f h * f g` fixes
`1`. -/
theorem smul_one_of_apply_mul {G M : Type*} [Monoid G] [Group M] [MulAction G M] {f : G → M}
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) (g : G) : g • (1 : M) = 1 := by
  simpa only [mul_one, map_one_of_apply_mul hf, right_eq_mul] using hf g 1

/-- For a map into a group satisfying `f (g * h) = g • f h * f g`, `g • f g⁻¹ = (f g)⁻¹`. -/
theorem map_inv_of_apply_mul {G M : Type*} [Group G] [Group M] [MulAction G M] {f : G → M}
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) (g : G) : g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← map_one_of_apply_mul hf, ← mul_inv_cancel g, hf g g⁻¹]

/-- **The one locus of a crossed map**, `{g | f g = 1}`, as a subgroup of `G`, for any group
action on a (not necessarily commutative) group `M` and any map `f : G → M` satisfying
`f (g * h) = g • f h * f g`. When `M` is commutative, this applies directly to
`hf : IsMulCocycle₁ f`. -/
def oneLocus {G M : Type*} [Group G] [Group M] [MulAction G M] {f : G → M}
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) : Subgroup G where
  carrier := {g | f g = 1}
  one_mem' := map_one_of_apply_mul hf
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hf g h, hg, hh, smul_one_of_apply_mul hf, mul_one]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := map_inv_of_apply_mul hf g
    rwa [hg, inv_one, ← smul_one_of_apply_mul hf g, smul_left_cancel_iff] at h

/-- An element lies in the one locus of a crossed map exactly when the map takes value `1`
there. -/
@[simp]
theorem mem_oneLocus {G M : Type*} [Group G] [Group M] [MulAction G M] {f : G → M}
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) {g : G} : g ∈ oneLocus hf ↔ f g = 1 :=
  Iff.rfl

/-- The one locus of a crossed map is the preimage of `1`. -/
@[simp]
theorem coe_oneLocus {G M : Type*} [Group G] [Group M] [MulAction G M] {f : G → M}
    (hf : ∀ g h : G, f (g * h) = g • f h * f g) : (oneLocus hf : Set G) = f ⁻¹' {1} :=
  (rfl)

end OneLocus

section ZeroLocus

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- **The zero locus of a `1`-cocycle**, `{g | f g = 0}`, as a subgroup of `G`, for any group
action (not necessarily distributive). -/
def zeroLocus {f : G → M} (hf : IsCocycle₁ f) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := map_one_of_isCocycle₁ hf
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hf g h, hg, hh, smul_zero_of_isCocycle₁ hf, add_zero]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := map_inv_of_isCocycle₁ hf g
    rwa [hg, neg_zero, ← smul_zero_of_isCocycle₁ hf g, smul_left_cancel_iff] at h

/-- An element lies in the zero locus of a `1`-cocycle exactly when the cocycle vanishes there. -/
@[simp]
theorem mem_zeroLocus {f : G → M} (hf : IsCocycle₁ f) {g : G} : g ∈ zeroLocus hf ↔ f g = 0 :=
  Iff.rfl

/-- The zero locus of a `1`-cocycle is the preimage of `0`. -/
@[simp]
theorem coe_zeroLocus {f : G → M} (hf : IsCocycle₁ f) : (zeroLocus hf : Set G) = f ⁻¹' {0} :=
  (rfl)

end ZeroLocus

section Restriction

/-- Restricting a `1`-cocycle on `G` to a subgroup `H` gives a `1`-cocycle on `H`. -/
theorem IsCocycle₁.comp_subtype {G M : Type*} [Group G] [AddCommGroup M] [SMul G M]
    {f : G → M} (hf : IsCocycle₁ f) (H : Subgroup G) : IsCocycle₁ (f ∘ H.subtype) :=
  fun x y => hf x y

/-- Restricting a `1`-cocycle on `H` along an inclusion `L ≤ H` gives a `1`-cocycle on `L`. -/
theorem IsCocycle₁.comp_inclusion {G M : Type*} [Group G] [AddCommGroup M] [SMul G M]
    {L H : Subgroup G} (hLH : L ≤ H) {c : H → M} (hc : IsCocycle₁ c) :
    IsCocycle₁ (c ∘ Subgroup.inclusion hLH) :=
  fun x y => hc (Subgroup.inclusion hLH x) (Subgroup.inclusion hLH y)

/-- Restricting a multiplicative `1`-cocycle on `G` to a subgroup `H` gives a multiplicative
`1`-cocycle on `H`. -/
theorem IsMulCocycle₁.comp_subtype {G M : Type*} [Group G] [CommGroup M] [SMul G M]
    {f : G → M} (hf : IsMulCocycle₁ f) (H : Subgroup G) : IsMulCocycle₁ (f ∘ H.subtype) :=
  fun x y => hf x y

/-- Restricting a multiplicative `1`-cocycle on `H` along an inclusion `L ≤ H` gives a
multiplicative `1`-cocycle on `L`. -/
theorem IsMulCocycle₁.comp_inclusion {G M : Type*} [Group G] [CommGroup M] [SMul G M]
    {L H : Subgroup G} (hLH : L ≤ H) {c : H → M} (hc : IsMulCocycle₁ c) :
    IsMulCocycle₁ (c ∘ Subgroup.inclusion hLH) :=
  fun x y => hc (Subgroup.inclusion hLH x) (Subgroup.inclusion hLH y)

/-- Restricting a crossed map on `G` to a subgroup `H` preserves the crossed identity, without
any commutativity assumption on the target. -/
theorem apply_mul_comp_subtype {G M : Type*} [Group G] [Mul M] [SMul G M]
    {f : G → M} (hf : ∀ g h : G, f (g * h) = g • f h * f g) (H : Subgroup G) (x y : H) :
    (f ∘ H.subtype) (x * y) = x • (f ∘ H.subtype) y * (f ∘ H.subtype) x :=
  hf x y

/-- Restricting a crossed map on `H` along an inclusion `L ≤ H` preserves the crossed identity,
without any commutativity assumption on the target. -/
theorem apply_mul_comp_inclusion {G M : Type*} [Group G] [Mul M] [SMul G M]
    {L H : Subgroup G} (hLH : L ≤ H) {c : H → M} (hc : ∀ x y : H, c (x * y) = x • c y * c x)
    (x y : L) :
    (c ∘ Subgroup.inclusion hLH) (x * y) =
      x • (c ∘ Subgroup.inclusion hLH) y * (c ∘ Subgroup.inclusion hLH) x :=
  hc (Subgroup.inclusion hLH x) (Subgroup.inclusion hLH y)

/-- The zero locus of the restriction of a `1`-cocycle `f` on `G` to `H`, viewed in `G`, is the
intersection of the zero locus of `f` with `H`. -/
@[simp]
theorem map_subtype_zeroLocus_comp_subtype {G M : Type*} [Group G] [AddCommGroup M]
    [MulAction G M] {f : G → M} (hf : IsCocycle₁ f) (H : Subgroup G) :
    (zeroLocus (hf.comp_subtype H)).map H.subtype = zeroLocus hf ⊓ H := by
  ext g
  simp only [Subgroup.mem_map, mem_zeroLocus, Function.comp_apply, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  exact ⟨fun ⟨x, hx, hxg⟩ => ⟨hxg ▸ hx, hxg ▸ x.property⟩, fun ⟨hg, hgH⟩ => ⟨⟨g, hgH⟩, hg, rfl⟩⟩

/-- The zero locus of the restriction of a `1`-cocycle `c` on `H` along `L ≤ H`, viewed in `G`, is
the intersection with `L` of the zero locus of `c` viewed in `G`. -/
@[simp]
theorem map_subtype_zeroLocus_comp_inclusion {G M : Type*} [Group G] [AddCommGroup M]
    [MulAction G M] {L H : Subgroup G} (hLH : L ≤ H) {c : H → M} (hc : IsCocycle₁ c) :
    (zeroLocus (hc.comp_inclusion hLH)).map L.subtype = (zeroLocus hc).map H.subtype ⊓ L := by
  ext g
  simp only [Subgroup.mem_map, mem_zeroLocus, Function.comp_apply, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  refine ⟨fun ⟨x, hx, hxg⟩ => ⟨⟨Subgroup.inclusion hLH x, hx, hxg⟩, hxg ▸ x.property⟩, ?_⟩
  rintro ⟨⟨y, hy, rfl⟩, hyL⟩
  exact ⟨⟨y, hyL⟩, hy, rfl⟩

/-- The one locus of the restriction of a crossed map `f` on `G` to `H`, viewed in `G`, is the
intersection of the one locus of `f` with `H`. -/
@[simp]
theorem map_subtype_oneLocus_comp_subtype {G M : Type*} [Group G] [Group M] [MulAction G M]
    {f : G → M} (hf : ∀ g h : G, f (g * h) = g • f h * f g) (H : Subgroup G) :
    (oneLocus (apply_mul_comp_subtype hf H)).map H.subtype = oneLocus hf ⊓ H := by
  ext g
  simp only [Subgroup.mem_map, mem_oneLocus, Function.comp_apply, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  exact ⟨fun ⟨x, hx, hxg⟩ => ⟨hxg ▸ hx, hxg ▸ x.property⟩, fun ⟨hg, hgH⟩ => ⟨⟨g, hgH⟩, hg, rfl⟩⟩

/-- The one locus of the restriction of a crossed map `c` on `H` along `L ≤ H`, viewed in `G`, is
the intersection with `L` of the one locus of `c` viewed in `G`. -/
@[simp]
theorem map_subtype_oneLocus_comp_inclusion {G M : Type*} [Group G] [Group M] [MulAction G M]
    {L H : Subgroup G} (hLH : L ≤ H) {c : H → M} (hc : ∀ x y : H, c (x * y) = x • c y * c x) :
    (oneLocus (apply_mul_comp_inclusion hLH hc)).map L.subtype =
      (oneLocus hc).map H.subtype ⊓ L := by
  ext g
  simp only [Subgroup.mem_map, mem_oneLocus, Function.comp_apply, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  refine ⟨fun ⟨x, hx, hxg⟩ => ⟨⟨Subgroup.inclusion hLH x, hx, hxg⟩, hxg ▸ x.property⟩, ?_⟩
  rintro ⟨⟨y, hy, rfl⟩, hyL⟩
  exact ⟨⟨y, hyL⟩, hy, rfl⟩

end Restriction

section Conj

open scoped Pointwise

/-- Conjugating a `1`-cocycle `c` on a subgroup `H` by `g` gives a `1`-cocycle on `g H g⁻¹`,
namely `x ↦ g • c (g⁻¹ * x * g)`; the subgroups act on `M` by restriction. -/
theorem IsCocycle₁.conj {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    {H : Subgroup G} {c : H → M} (hc : IsCocycle₁ c) (g : G) :
    IsCocycle₁ fun x : ↥(MulAut.conj g • H) =>
      g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm x) := by
  intro x y
  dsimp only
  rw [map_mul, hc, smul_add, Subgroup.smul_def, Subgroup.smul_def, smul_smul, smul_smul,
    Subgroup.equivSMul_symm_apply_coe (MulAut.conj g) H x]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  group

/-- The zero locus of the conjugate `x ↦ g • c (g⁻¹ * x * g)` of a `1`-cocycle on `H`, viewed
in `G`, is the conjugate by `g` of the zero locus of `c`. -/
@[simp]
theorem map_subtype_zeroLocus_conj {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
    {H : Subgroup G} {c : H → M} (hc : IsCocycle₁ c) (g : G) :
    (zeroLocus (hc.conj g)).map (MulAut.conj g • H).subtype =
      MulAut.conj g • (zeroLocus hc).map H.subtype := by
  ext x
  simp only [Subgroup.mem_map, mem_zeroLocus, smul_eq_zero_iff_eq,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, Subgroup.equivSMul_symm_apply_coe (MulAut.conj g) H y⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨Subgroup.equivSMul _ H z, by simpa using hz, ?_⟩
    rw [Subgroup.equivSMul_apply_coe, hzx, smul_inv_smul]

/-- Conjugating a crossed map `c` on a subgroup `H` into a (not necessarily commutative) `G`-monoid
`M` by `g` gives the crossed map `x ↦ g • c (g⁻¹ * x * g)` on `g H g⁻¹`. -/
theorem apply_mul_conj {G M : Type*} [Group G] [Monoid M] [MulDistribMulAction G M]
    {H : Subgroup G} {c : H → M} (hc : ∀ x y : H, c (x * y) = x • c y * c x) (g : G)
    (x y : ↥(MulAut.conj g • H)) :
    g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm (x * y)) =
      x • g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm y) *
        g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm x) := by
  rw [map_mul, hc, smul_mul', Subgroup.smul_def, Subgroup.smul_def, smul_smul, smul_smul,
    Subgroup.equivSMul_symm_apply_coe (MulAut.conj g) H x]
  have hx : g * (MulAut.conj g)⁻¹ (x : G) = (x : G) * g := by
    simp [mul_assoc]
  rw [MulAut.smul_def, hx]

/-- Conjugating a multiplicative `1`-cocycle `c` on a subgroup `H` by `g` gives a multiplicative
`1`-cocycle on `g H g⁻¹`. -/
theorem IsMulCocycle₁.conj {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {H : Subgroup G} {c : H → M} (hc : IsMulCocycle₁ c) (g : G) :
    IsMulCocycle₁ fun x : ↥(MulAut.conj g • H) =>
      g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm x) :=
  apply_mul_conj hc g

/-- The one locus of the conjugate `x ↦ g • c (g⁻¹ * x * g)` of a crossed map on `H`, viewed in
`G`, is the conjugate by `g` of the one locus of `c`. -/
@[simp]
theorem map_subtype_oneLocus_conj {G M : Type*} [Group G] [Group M] [MulDistribMulAction G M]
    {H : Subgroup G} {c : H → M} (hc : ∀ x y : H, c (x * y) = x • c y * c x) (g : G) :
    (oneLocus (f := fun z : ↥(MulAut.conj g • H) =>
        g • c ((Subgroup.equivSMul (MulAut.conj g) H).symm z)) (apply_mul_conj hc g)).map
        (MulAut.conj g • H).subtype =
      MulAut.conj g • (oneLocus hc).map H.subtype := by
  ext x
  have hsmul (m : M) : g • m = 1 ↔ m = 1 :=
    ⟨fun hm => smul_left_cancel g (hm.trans (smul_one g).symm), by rintro rfl; exact smul_one g⟩
  simp only [Subgroup.mem_map, mem_oneLocus, hsmul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, Subgroup.equivSMul_symm_apply_coe (MulAut.conj g) H y⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨Subgroup.equivSMul _ H z, by simpa using hz, ?_⟩
    rw [Subgroup.equivSMul_apply_coe, hzx, smul_inv_smul]

end Conj

end groupCohomology

namespace TauCeti

open groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- Two one-cocycles on a cyclic group agree if they agree at a generator. No finiteness or
continuity hypothesis is needed, and the action need not be distributive. -/
theorem isCocycle₁_ext_of_forall_mem_zpowers {f f' : G → M} (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hf : IsCocycle₁ f) (hf' : IsCocycle₁ f')
    (h : f g = f' g) : f = f' := by
  let S : Subgroup G :=
    { carrier := {x | f x = f' x}
      one_mem' := (map_one_of_isCocycle₁ hf).trans (map_one_of_isCocycle₁ hf').symm
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [hf x y, hf' x y, hx, hy]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← smul_left_cancel_iff x]
        rw [map_inv_of_isCocycle₁ hf, map_inv_of_isCocycle₁ hf', hx] }
  have hle : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr h
  funext x
  exact hle (hg x)

/-- Two `2`-cocycles on a cyclic group agree if they agree whenever the second argument is a
generator. No finiteness or continuity hypothesis is needed, and the action need not be
distributive. -/
theorem isCocycle₂_ext_of_forall_mem_zpowers {f f' : G × G → M} (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hf : IsCocycle₂ f) (hf' : IsCocycle₂ f')
    (h : ∀ x : G, f (x, g) = f' (x, g)) : f = f' := by
  have h11 : f (1, 1) = f' (1, 1) := by
    rw [← map_one_fst_of_isCocycle₂ hf g, ← map_one_fst_of_isCocycle₂ hf' g]
    exact h 1
  have hone (x : G) : f (x, 1) = f' (x, 1) := by
    rw [map_one_snd_of_isCocycle₂ hf, map_one_snd_of_isCocycle₂ hf', h11]
  let S : Subgroup G :=
    { carrier := {y | ∀ x : G, f (x, y) = f' (x, y)}
      one_mem' := hone
      mul_mem' := by
        intro y z hy hz x
        have hmul := hf x y z
        rw [hz (x * y), hy x, hz y] at hmul
        exact add_left_cancel (hmul.symm.trans (hf' x y z))
      inv_mem' := by
        intro y hy x
        have hinv := hf x y⁻¹ y
        have hinv' := hf' x y⁻¹ y
        rw [inv_mul_cancel] at hinv hinv'
        rw [hy (x * y⁻¹), hy y⁻¹, hone x] at hinv
        exact add_left_cancel (hinv.trans hinv'.symm) }
  have hle : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr h
  funext ⟨x, y⟩
  exact hle (hg y) x

omit [MulAction G M] in
/-- The value of a one-cocycle on a finite group lies in the kernel of the group norm.
This holds at every group element, not just at a cyclic generator. Even associativity and
distributivity of the scalar multiplication are unnecessary for this identity. -/
theorem sum_smul_apply_eq_zero_of_isCocycle₁ [SMul G M] [Fintype G] {f : G → M}
    (g : G) (hf : IsCocycle₁ f) : ∑ x : G, x • f g = 0 := by
  have hsum : (∑ x : G, f x) = (∑ x : G, x • f g) + ∑ x : G, f x := by
    calc
      (∑ x : G, f x) = ∑ x : G, f (x * g) :=
        (Fintype.sum_bijective _ (Group.mulRight_bijective g) _ _ (fun _ ↦ rfl)).symm
      _ = _ := by simp only [hf _ _, Finset.sum_add_distrib]
  exact (add_right_cancel (hsum.symm.trans (zero_add _).symm))

end TauCeti
