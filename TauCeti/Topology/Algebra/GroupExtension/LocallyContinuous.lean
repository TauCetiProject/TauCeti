/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LocallyContinuous
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.Topology.Algebra.GroupExtension.FactorSet

/-!
# Locally continuous factor sets and their classes

Let `G` be a topological group acting on a commutative topological group `M`, written
multiplicatively. A factor set `α : FactorSet G M` is a normalized multiplicative `2`-cocycle; for
`M` the circle group it is the multiplier of a projective unitary representation, with
`U g * U h = α (g, h) • U (g * h)`, and with the circle acted on through a grading `G → ℤ/2` it is
the multiplier of a representation by unitary and antiunitary operators. Such multipliers can in
general only be chosen continuous near the identity. This file reads a factor set into the locally
continuous cohomology of `TauCeti/RepresentationTheory/Homological/ContCohomology/
LocallyContinuous.lean`.

A factor set is *locally continuous* (`TauCeti.FactorSet.IsLocallyContinuous`) when it is
continuous at every point of a neighbourhood of `(1, 1)` and, for every `g`, the function
`h ↦ α (g, h) / α (g * h * g⁻¹, g)` is continuous at every point of a neighbourhood of `1`. Read
additively it is then a locally continuous `2`-cocycle
(`TauCeti.FactorSet.isLocallyContinuous_iff_ofMul_mem_LCZ2`) and has a class in
`H²_lc(G, M)` (`TauCeti.FactorSet.locContCohomologyClass`). Two locally continuous factor sets have
the same class exactly when their quotient is the coboundary `(g, h) ↦ g • x h / x (g * h) * x g`
of a function `x` continuous near `1` (`TauCeti.FactorSet.locContCohomologyClass_eq_iff`), and
every class is the class of a locally continuous factor set
(`TauCeti.FactorSet.exists_locContCohomologyClass_eq`). Over a connected group the second
condition is automatic (`TauCeti.FactorSet.isLocallyContinuous_iff_of_preconnected`).

## Main definitions

* `TauCeti.FactorSet.IsLocallyContinuous`: local continuity of a factor set.
* `TauCeti.FactorSet.locContCohomologyClass`: the class of a locally continuous factor set in
  `H²_lc(G, M)`.

## References

* K.-H. Neeb, *Abelian extensions of infinite-dimensional Lie groups*, Travaux mathématiques 15
  (2004), 69–194, Section II.
-/

public section

namespace TauCeti

universe u v

open ContCohomology Filter Topology

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G] [CommGroup M]
  [TopologicalSpace M] [MulDistribMulAction G M]

namespace FactorSet

/-- A factor set is **locally continuous** when it is continuous at every point of a neighbourhood
of `(1, 1)` and, for every `g`, its conjugation function `h ↦ α (g, h) / α (g * h * g⁻¹, g)` is
continuous at every point of a neighbourhood of `1`. -/
def IsLocallyContinuous (α : FactorSet G M) : Prop :=
  (∀ᶠ p in 𝓝 1, ContinuousAt α p) ∧
    ∀ g : G, ∀ᶠ h in 𝓝 1, ContinuousAt (fun k => α (g, k) / α (g * k * g⁻¹, g)) h

/-- Continuity at a point is unchanged by reading the values additively. -/
private theorem continuousAt_ofMul_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} : ContinuousAt (fun y => Additive.ofMul (f y)) x ↔ ContinuousAt f x :=
  ⟨fun h => continuous_toMul.continuousAt.comp h, fun h => continuous_ofMul.continuousAt.comp h⟩

variable [IsTopologicalGroup M]

/-- **Local continuity of a factor set is membership of the locally continuous complex.** Read
additively, a factor set is a locally continuous `2`-cocycle in the sense of
`TauCeti.ContCohomology.LCZ2` exactly when it is locally continuous. -/
theorem isLocallyContinuous_iff_ofMul_mem_LCZ2 (α : FactorSet G M) :
    α.IsLocallyContinuous ↔
      (fun p : G × G => Additive.ofMul (α p)) ∈ LCZ2 G (Additive M) := by
  simp only [mem_LCZ2_iff, mem_LC2_iff', ← ofMul_div, continuousAt_ofMul_iff]
  exact ⟨fun h => ⟨h, fun g h j => congrArg Additive.ofMul (α.isMulCocycle₂ g h j)⟩, And.left⟩

/-- A locally continuous factor set, read additively, as a locally continuous `2`-cocycle. -/
def toLCZ2 (α : FactorSet G M) (hα : α.IsLocallyContinuous) : LCZ2 G (Additive M) :=
  ⟨fun p => Additive.ofMul (α p), (isLocallyContinuous_iff_ofMul_mem_LCZ2 α).1 hα⟩

@[simp]
theorem coe_toLCZ2 (α : FactorSet G M) (hα : α.IsLocallyContinuous) :
    (α.toLCZ2 hα : G × G → Additive M) = fun p => Additive.ofMul (α p) :=
  (rfl)

/-- A continuous factor set is locally continuous. -/
theorem IsLocallyContinuous.of_continuous [IsTopologicalGroup G] {α : FactorSet G M}
    (hα : Continuous ⇑α) : α.IsLocallyContinuous :=
  (isLocallyContinuous_iff_ofMul_mem_LCZ2 α).2
    (Z2_le_LCZ2 G (Additive M) ((ofMul_mem_Z2_iff α).2 hα))

/-- **Over a connected group a factor set is locally continuous as soon as it is continuous near
`(1, 1)`**: the conjugation condition is automatic, by
`TauCeti.ContCohomology.conjugationCochain_mem_LC1_of_preconnected`. -/
theorem isLocallyContinuous_iff_of_preconnected [IsTopologicalGroup G] [ContinuousSMul G M]
    [PreconnectedSpace G] (α : FactorSet G M) :
    α.IsLocallyContinuous ↔ ∀ᶠ p in 𝓝 1, ContinuousAt α p := by
  rw [isLocallyContinuous_iff_ofMul_mem_LCZ2, mem_LCZ2_iff_of_preconnected, mem_LC1_iff]
  simp only [continuousAt_ofMul_iff]
  exact ⟨And.left, fun h => ⟨h, fun g h j => congrArg Additive.ofMul (α.isMulCocycle₂ g h j)⟩⟩

variable [IsTopologicalGroup G] [ContinuousSMul G M]

/-- **The class of a locally continuous factor set** in the locally continuous cohomology group
`H²_lc(G, M)`. -/
def locContCohomologyClass (α : FactorSet G M) (hα : α.IsLocallyContinuous) :
    LCH2 G (Additive M) :=
  LCH2pi G (Additive M) (α.toLCZ2 hα)

theorem locContCohomologyClass_def (α : FactorSet G M) (hα : α.IsLocallyContinuous) :
    α.locContCohomologyClass hα = LCH2pi G (Additive M) (α.toLCZ2 hα) :=
  (rfl)

/-- **Two locally continuous factor sets have the same class exactly when their quotient is the
coboundary of a function continuous near `1`.** -/
theorem locContCohomologyClass_eq_iff (α β : FactorSet G M) (hα : α.IsLocallyContinuous)
    (hβ : β.IsLocallyContinuous) :
    α.locContCohomologyClass hα = β.locContCohomologyClass hβ ↔
      ∃ x : G → M, (∀ᶠ g in 𝓝 1, ContinuousAt x g) ∧
        ∀ g h : G, g • x h / x (g * h) * x g = α (g, h) / β (g, h) := by
  rw [locContCohomologyClass_def, locContCohomologyClass_def, LCH2pi_eq_iff, mem_LCB2_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun g => (c g).toMul, (mem_LC1_iff.1 hc).mono fun g hg =>
      continuous_toMul.continuousAt.comp hg, fun g k => ?_⟩
    simpa [d1_apply, toMul_add, toMul_sub] using congrArg Additive.toMul (congrFun h (g, k))
  · rintro ⟨x, hx, h⟩
    refine ⟨fun g => Additive.ofMul (x g), mem_LC1_iff.2 (hx.mono fun g hg =>
      continuous_ofMul.continuousAt.comp hg), funext fun ⟨g, k⟩ => ?_⟩
    simp only [d1_apply, coe_toLCZ2, Pi.sub_apply, ← ofMul_div, ← h g k]
    simp [ofMul_div, ofMul_mul]

/-- **Every class in `H²_lc(G, M)` is the class of a locally continuous factor set.** A locally
continuous `2`-cocycle need not be normalized; subtracting the coboundary of the constant
`1`-cochain at its value at `(1, 1)` normalizes it without moving its class. -/
theorem exists_locContCohomologyClass_eq (c : LCH2 G (Additive M)) :
    ∃ (α : FactorSet G M) (hα : α.IsLocallyContinuous), α.locContCohomologyClass hα = c := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  set b : G × G → Additive M := d1 G (Additive M) fun _ => (z : G × G → Additive M) (1, 1)
    with hb_def
  have hb : b ∈ LCB2 G (Additive M) :=
    mem_LCB2_iff.2 ⟨_, C1_le_LC1 G (Additive M) (mem_C1_iff.2 continuous_const), rfl⟩
  have hz' : (z : G × G → Additive M) - b ∈ LCZ2 G (Additive M) :=
    (LCZ2 G (Additive M)).sub_mem z.2 (LCB2_le_LCZ2 G (Additive M) hb)
  let α : FactorSet G M :=
    { toFun := fun p => ((z : G × G → Additive M) p - b p).toMul
      isMulCocycle₂' := fun g h j => congrArg Additive.toMul ((mem_LCZ2_iff.1 hz').2 g h j)
      map_one_one' := by simp [hb_def, d1_apply] }
  have hαz : (fun p => Additive.ofMul (α p)) = (z : G × G → Additive M) - b :=
    funext fun p => by simp [α]
  have hα : α.IsLocallyContinuous := (isLocallyContinuous_iff_ofMul_mem_LCZ2 α).2 (hαz ▸ hz')
  refine ⟨α, hα, ?_⟩
  rw [locContCohomologyClass_def, LCH2pi, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
    AddSubgroup.mem_addSubgroupOf]
  have hsub : (-(α.toLCZ2 hα) + z : LCZ2 G (Additive M)) = (b : G × G → Additive M) := by
    ext p
    simp [α]
  rw [hsub]
  exact hb

end FactorSet

end TauCeti
