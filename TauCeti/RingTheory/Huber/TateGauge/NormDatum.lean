/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.TateGauge.Basic

/-!
# Norm data of Tate rings

A Tate ring carries no canonical norm, but each choice of a ring of definition `A₀`, a
pseudouniformiser `ϖ ∈ A₀` and a radius `0 < r < 1` gives one: the Tate gauge
`α(x) = inf { r ^ n | n ∈ ℤ, ϖ ^ (-n) x ∈ A₀ }`, which multiplication by `ϖ` scales exactly by
`r`; in particular `ϖ` has norm `r` when `A` is Hausdorff and nonzero. This file
packages such a choice as a *norm datum* `TateNormDatum A` and its norm `tateNorm d` as an
ultrametric ring seminorm defining the topology of `A`.

Every Tate ring has a norm datum, and a topological ring with a norm datum is a Tate ring. The
norm decreases along a ring homomorphism carrying the ring of definition and the
pseudouniformiser of one datum into those of another with the same radius. The spectral seminorm
of a Tate ring is defined as the smoothing of `tateNorm d`.

The ring of definition is recorded as an open bounded subring, which is what a ring of definition
of a Tate ring is; the norm does not depend on an ideal of definition, so none is carried.

## Main definitions

* `TauCeti.Huber.TateNormDatum A`: a ring of definition, a pseudouniformiser in it and a radius.
* `TauCeti.Huber.tateNorm d`: the Tate gauge of `d`, with base `d.radius⁻¹`, as a ring seminorm.

## Main results

* `TauCeti.Huber.tateNorm_zpow_mul`: `‖ϖ ^ k * x‖ = r ^ k * ‖x‖` for `k ∈ ℤ`.
* `TauCeti.Huber.tateNorm_le_zpow_iff`: the closed ball of radius `r ^ n` is `ϖ ^ n A₀`.
* `TauCeti.Huber.tateNorm_hasBasis_nhds_zero`: the open balls about zero are a neighbourhood
  basis of zero.
* `TauCeti.Huber.tateNorm_map_le`: functoriality of the norm.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4 and Remark 2.4.4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A]

/-- A *norm datum* of a Tate ring `A`: an open bounded subring `A₀` (a ring of definition), a
topologically nilpotent unit `ϖ ∈ A₀` (a pseudouniformiser) and a radius `0 < r < 1`.
Multiplication by `ϖ` scales its norm `TauCeti.Huber.tateNorm` exactly by `r`, so `ϖ` has norm `r`
when `A` is Hausdorff and nonzero. -/
@[ext]
structure TateNormDatum where
  /-- The ring of definition `A₀`. -/
  ringOfDefinition : Subring A
  /-- The ring of definition is open. -/
  isOpen_ringOfDefinition : IsOpen (ringOfDefinition : Set A)
  /-- The ring of definition is bounded. -/
  isBounded_ringOfDefinition : IsBounded (ringOfDefinition : Set A)
  /-- The pseudouniformiser `ϖ`. -/
  pseudoUniformizer : Aˣ
  /-- The pseudouniformiser is topologically nilpotent. -/
  isTopologicallyNilpotent_pseudoUniformizer : IsTopologicallyNilpotent (pseudoUniformizer : A)
  /-- The pseudouniformiser lies in the ring of definition. -/
  pseudoUniformizer_mem : (pseudoUniformizer : A) ∈ ringOfDefinition
  /-- The radius `r`, the factor by which multiplication by the pseudouniformiser scales the norm
  (the norm of the pseudouniformiser when `A` is Hausdorff and nonzero). -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- The radius is less than one. -/
  radius_lt_one : radius < 1

namespace TateNormDatum

variable {A} (d : TateNormDatum A)

/-- The pseudouniformiser of a norm datum is a pseudouniformiser. -/
theorem isPseudoUniformizer : IsPseudoUniformizer (d.pseudoUniformizer : A) :=
  isPseudoUniformizer_iff.mpr
    ⟨d.pseudoUniformizer.isUnit, d.isTopologicallyNilpotent_pseudoUniformizer⟩

/-- The base `r⁻¹` of the Tate gauge of a norm datum is greater than one. -/
theorem one_lt_radius_inv : 1 < d.radius⁻¹ :=
  (one_lt_inv₀ d.radius_pos).2 d.radius_lt_one

variable [IsTopologicalRing A]

include d in
/-- A topological ring with a norm datum is a Tate ring. -/
theorem isTateRing : IsTateRing A :=
  IsTateRing.of_isOpen_isBounded _ d.isOpen_ringOfDefinition d.isBounded_ringOfDefinition
    d.isPseudoUniformizer

/-- The sets `ϖ ^ n A₀`, `n ≥ 0`, of a norm datum form a neighbourhood basis of zero. -/
theorem hasBasis_nhds_zero : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True)
    fun n ↦ {x | ((d.pseudoUniformizer ^ (-(n : ℤ)) : Aˣ) : A) * x ∈ d.ringOfDefinition} := by
  refine (d.isPseudoUniformizer.hasBasis_nhds_zero (PairOfDefinition.ofIsPseudoUniformizer _
    d.isOpen_ringOfDefinition d.isBounded_ringOfDefinition d.isPseudoUniformizer
    d.pseudoUniformizer_mem)).congr (fun _ ↦ Iff.rfl) fun n _ ↦ ?_
  ext x
  rw [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition, ← Units.val_pow_eq_pow_val,
    Set.mem_smul_set, Set.mem_ofPred_eq, zpow_neg, zpow_natCast]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [smul_eq_mul, Units.inv_mul_cancel_left]
  · exact fun hx ↦ ⟨_, hx, by rw [smul_eq_mul, Units.mul_inv_cancel_left]⟩

/-- Every element is moved into the ring of definition by some power of the pseudouniformiser. -/
theorem exists_zpow_mul_mem (x : A) :
    ∃ n : ℤ, ((d.pseudoUniformizer ^ n : Aˣ) : A) * x ∈ d.ringOfDefinition :=
  exists_zpow_mul_mem_of_hasBasis d.hasBasis_nhds_zero x

end TateNormDatum

/-- Every Tate ring has a norm datum. A pseudouniformiser need not lie in a given ring of
definition, but a high enough power of it does. -/
instance [IsTopologicalRing A] [IsTateRing A] : Nonempty (TateNormDatum A) := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hϖ.eventually_pow_mem_ringOfDefinition P)
  exact ⟨{ ringOfDefinition := P.ringOfDefinition
           isOpen_ringOfDefinition := P.isOpen_ringOfDefinition
           isBounded_ringOfDefinition := P.isBounded_ringOfDefinition
           pseudoUniformizer := hϖ.isUnit.unit ^ (N + 1)
           isTopologicallyNilpotent_pseudoUniformizer := by
             simpa using hϖ.isTopologicallyNilpotent.pow N.succ_ne_zero
           pseudoUniformizer_mem := by simpa using hN _ N.le_succ
           radius := 1 / 2
           radius_pos := by norm_num
           radius_lt_one := by norm_num }⟩

variable {A} [IsTopologicalRing A] (d : TateNormDatum A)

/-- The *norm* of a norm datum `d = (A₀, ϖ, r)` of a Tate ring: the Tate gauge
`x ↦ inf { r ^ n | n ∈ ℤ, ϖ ^ (-n) x ∈ A₀ }`, as an ultrametric ring seminorm. -/
noncomputable def tateNorm : RingSeminorm A :=
  tateSeminorm d.pseudoUniformizer_mem d.exists_zpow_mul_mem d.one_lt_radius_inv

/-- The norm of a norm datum is its Tate gauge with base `r⁻¹`. -/
theorem tateNorm_apply (x : A) :
    tateNorm d x = tateGauge d.ringOfDefinition d.pseudoUniformizer d.radius⁻¹ x :=
  congrFun (coe_tateSeminorm _ _ _) x

/-- The norm of a norm datum is ultrametric. -/
theorem isNonarchimedean_tateNorm : IsNonarchimedean (tateNorm d) := by
  simpa [tateNorm] using isNonarchimedean_tateGauge d.pseudoUniformizer_mem d.exists_zpow_mul_mem
    (zero_le_one.trans d.one_lt_radius_inv.le)

/-- Multiplication by `ϖ ^ k`, `k ∈ ℤ`, scales the norm of a norm datum exactly by `r ^ k`. -/
theorem tateNorm_zpow_mul (k : ℤ) (x : A) :
    tateNorm d (((d.pseudoUniformizer ^ k : Aˣ) : A) * x) = d.radius ^ k * tateNorm d x := by
  rw [tateNorm_apply, tateNorm_apply, tateGauge_zpow_mul (inv_pos.2 d.radius_pos), inv_zpow',
    neg_neg]

/-- Multiplication by the pseudouniformiser scales the norm of a norm datum exactly by the
radius. -/
@[simp]
theorem tateNorm_pseudoUniformizer_mul (x : A) :
    tateNorm d (d.pseudoUniformizer * x) = d.radius * tateNorm d x := by
  simpa using tateNorm_zpow_mul d 1 x

/-- The closed ball of radius `r ^ n` of the norm of a norm datum is `ϖ ^ n A₀`. -/
theorem tateNorm_le_zpow_iff {x : A} {n : ℤ} :
    tateNorm d x ≤ d.radius ^ n ↔
      ((d.pseudoUniformizer ^ (-n) : Aˣ) : A) * x ∈ d.ringOfDefinition := by
  rw [tateNorm_apply, ← tateGauge_le_zpow_iff d.pseudoUniformizer_mem (d.exists_zpow_mul_mem x)
    d.one_lt_radius_inv, inv_zpow', neg_neg]

/-- Elements of the ring of definition have norm at most one. -/
theorem tateNorm_le_one_of_mem {x : A} (hx : x ∈ d.ringOfDefinition) : tateNorm d x ≤ 1 :=
  (tateNorm_apply d x).trans_le <| tateGauge_le_one (zero_le_one.trans d.one_lt_radius_inv.le) hx

/-- The norm of a norm datum takes a value at most one at one. -/
theorem tateNorm_one_le : tateNorm d 1 ≤ 1 :=
  tateNorm_le_one_of_mem d d.ringOfDefinition.one_mem

/-- The open balls about zero of the norm of a norm datum are a neighbourhood basis of zero, so
the norm defines the topology of the ring. -/
theorem tateNorm_hasBasis_nhds_zero :
    (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦ {x | tateNorm d x < ε} := by
  simpa only [tateNorm_apply] using
    hasBasis_tateGauge d.hasBasis_nhds_zero d.one_lt_radius_inv d.pseudoUniformizer_mem

/-- The zero set of the norm of a norm datum is the closure of zero. -/
theorem tateNorm_eq_zero_iff {x : A} : tateNorm d x = 0 ↔ x ∈ closure ({0} : Set A) := by
  rw [tateNorm_apply]
  exact tateGauge_eq_zero_iff d.hasBasis_nhds_zero d.one_lt_radius_inv d.pseudoUniformizer_mem

/-- In a nonzero Hausdorff Tate ring the norm of a norm datum takes the value one at one. -/
@[simp]
theorem tateNorm_one [T1Space A] [Nontrivial A] : tateNorm d 1 = 1 := by
  rw [tateNorm_apply]
  exact tateGauge_one d.hasBasis_nhds_zero d.one_lt_radius_inv d.pseudoUniformizer_mem

/-- **Functoriality of the norm.** Let `φ : A →+* B` carry the ring of definition of a norm datum
`d` of `A` into that of a norm datum `d'` of `B`, and the pseudouniformiser of `d` to that of
`d'`, the two data having the same radius. Then `φ` does not increase the norm. -/
theorem tateNorm_map_le {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (d' : TateNormDatum B) (φ : A →+* B)
    (hA₀ : ∀ x ∈ d.ringOfDefinition, φ x ∈ d'.ringOfDefinition)
    (hϖ : φ d.pseudoUniformizer = d'.pseudoUniformizer) (hr : d'.radius = d.radius) (x : A) :
    tateNorm d' (φ x) ≤ tateNorm d x := by
  have hu : Units.map (φ : A →* B) d.pseudoUniformizer = d'.pseudoUniformizer := Units.ext hϖ
  have hmap (m : ℤ) :
      φ ((d.pseudoUniformizer ^ m : Aˣ) : A) = ((d'.pseudoUniformizer ^ m : Bˣ) : B) := by
    rw [← hu, ← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]
  have ha := zero_le_one.trans d.one_lt_radius_inv.le
  rw [tateNorm_apply, tateNorm_apply, hr]
  refine le_of_forall_gt fun t ht ↦ ?_
  obtain ⟨n, hn, hnt⟩ := (tateGauge_lt_iff ha (d.exists_zpow_mul_mem x)).1 ht
  refine (tateGauge_le_zpow ha ?_).trans_lt hnt
  have h := hA₀ _ hn
  rwa [map_mul, hmap] at h

end TauCeti.Huber
