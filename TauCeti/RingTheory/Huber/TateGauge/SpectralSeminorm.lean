/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SmoothingSeminorm
public import TauCeti.RingTheory.Huber.TateGauge.NormDatum

/-!
# The spectral seminorm of a Tate ring

Let `A` be a Tate ring with a norm datum `d = (A₀, ϖ, r)` and norm `α = tateNorm d`. The
*spectral seminorm* of `(A, d)` is the smoothing
`|x|_sp = lim_n α(x ^ n) ^ (1 / n) = inf_{n ≥ 1} α(x ^ n) ^ (1 / n)`
of `α`, Mathlib's `smoothingSeminorm`. It is a power-multiplicative ultrametric ring seminorm
bounded by `α`, and multiplication by `ϖ ^ k` scales it exactly by `r ^ k`.

Unlike `α`, the spectral seminorm sees the ring of definition only through the topology: it is
unchanged when `A₀` is replaced by another ring of definition containing `ϖ`, and changing the
radius `r` to `r'` raises it to the power `log r' / log r`. Its intrinsic properties are:

* `|x|_sp < 1` exactly when `x` is topologically nilpotent;
* `|x|_sp ≤ 1` when `x` is power-bounded;
* `|x|_sp = 0` exactly when every `ϖ ^ (-n) x` is topologically nilpotent; the closure of zero
  lies in this kernel;
* `|1|_sp = 1` when `A` is Hausdorff and nonzero.

Finally, a ring homomorphism compatible with norm data of the same radius does not increase the
spectral seminorm. The spectral seminorm defines the spectral topology of `A`, used to build the
uniformization of a Tate Huber pair.

## Main definitions

* `TauCeti.Huber.spectralSeminorm d`: the spectral seminorm of a norm datum `d`.

## Main results

* `TauCeti.Huber.isPowMul_spectralSeminorm`, `TauCeti.Huber.spectralSeminorm_le_tateNorm`.
* `TauCeti.Huber.spectralSeminorm_zpow_mul`: `|ϖ ^ k x|_sp = r ^ k |x|_sp` for `k ∈ ℤ`.
* `TauCeti.Huber.spectralSeminorm_eq_of_ringOfDefinition`: independence of the ring of
  definition.
* `TauCeti.Huber.spectralSeminorm_rpow`: change of radius.
* `TauCeti.Huber.spectralSeminorm_lt_one_iff`: `|x|_sp < 1` iff `x` is topologically nilpotent.
* `TauCeti.Huber.spectralSeminorm_le_one_of_isPowerBounded`.
* `TauCeti.Huber.spectralSeminorm_eq_zero_iff`: the kernel of the spectral seminorm.
* `TauCeti.Huber.spectralSeminorm_one`: `|1|_sp = 1` for a nonzero Hausdorff ring.
* `TauCeti.Huber.spectralSeminorm_map_le`: functoriality.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.1.9.
* D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*, §2, after Definition 2.10.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (d : TateNormDatum A)

/-- The *spectral seminorm* of a norm datum `d` of a Tate ring: the smoothing
`x ↦ lim_n ‖x ^ n‖ ^ (1 / n)` of the norm `tateNorm d`. -/
noncomputable def spectralSeminorm : RingSeminorm A :=
  smoothingSeminorm (tateNorm d) (tateNorm_one_le d) (isNonarchimedean_tateNorm d)

/-- The spectral seminorm is the smoothing of the norm of the datum. -/
theorem spectralSeminorm_apply (x : A) :
    spectralSeminorm d x = smoothingFun (tateNorm d) x :=
  (rfl)

/-- The spectral seminorm at `x` is the limit of `‖x ^ n‖ ^ (1 / n)`. -/
theorem tendsto_spectralSeminorm (x : A) :
    Tendsto (fun n : ℕ ↦ tateNorm d (x ^ n) ^ (1 / n : ℝ)) atTop (𝓝 (spectralSeminorm d x)) :=
  tendsto_smoothingFun_of_map_one_le_one _ (tateNorm_one_le d) x

/-- The spectral seminorm is bounded by the norm of the datum. -/
theorem spectralSeminorm_le_tateNorm (x : A) : spectralSeminorm d x ≤ tateNorm d x :=
  smoothingFun_le_self _ x

/-- The spectral seminorm is power-multiplicative. -/
theorem isPowMul_spectralSeminorm : IsPowMul (spectralSeminorm d) :=
  isPowMul_smoothingFun _ (tateNorm_one_le d)

/-- The spectral seminorm is ultrametric. -/
theorem isNonarchimedean_spectralSeminorm : IsNonarchimedean (spectralSeminorm d) :=
  isNonarchimedean_smoothingFun _ (tateNorm_one_le d) (isNonarchimedean_tateNorm d)

/-- Multiplication by `ϖ ^ k`, `k ∈ ℤ`, scales the spectral seminorm exactly by `r ^ k`. -/
theorem spectralSeminorm_zpow_mul (k : ℤ) (x : A) :
    spectralSeminorm d (((d.pseudoUniformizer ^ k : Aˣ) : A) * x) =
      d.radius ^ k * spectralSeminorm d x :=
  smoothingFun_mul_eq_mul_of_forall (tateNorm_one_le d) (zpow_nonneg d.radius_pos.le k)
    (tateNorm_zpow_mul d k) x

/-- Multiplication by the pseudouniformiser scales the spectral seminorm exactly by the radius. -/
@[simp]
theorem spectralSeminorm_pseudoUniformizer_mul (x : A) :
    spectralSeminorm d (d.pseudoUniformizer * x) = d.radius * spectralSeminorm d x := by
  simpa using spectralSeminorm_zpow_mul d 1 x

/-- **The spectral seminorm does not depend on the ring of definition.** Two norm data with the
same pseudouniformiser and radius have the same spectral seminorm, although their norms are in
general only bounded-equivalent. -/
theorem spectralSeminorm_eq_of_ringOfDefinition (d' : TateNormDatum A)
    (hϖ : d.pseudoUniformizer = d'.pseudoUniformizer) (hr : d.radius = d'.radius) :
    spectralSeminorm d = spectralSeminorm d' := by
  obtain ⟨C, -, hC⟩ := tateGauge_equiv d.hasBasis_nhds_zero (inv_pos.2 d.radius_pos)
    (hϖ ▸ d'.hasBasis_nhds_zero)
  have h₁ (y : A) : tateNorm d y ≤ C * tateNorm d' y := by
    simpa only [tateNorm_apply, ← hϖ, ← hr] using (hC y).1
  have h₂ (y : A) : tateNorm d' y ≤ C * tateNorm d y := by
    simpa only [tateNorm_apply, ← hϖ, ← hr] using (hC y).2
  ext x
  exact le_antisymm ((RingHom.id A).smoothingFun_map_le_of_le_mul (tateNorm_one_le d') h₁ x)
    ((RingHom.id A).smoothingFun_map_le_of_le_mul (tateNorm_one_le d) h₂ x)

/-- **Changing the radius.** For two norm data with the same pseudouniformiser and radii `r` and
`r'`, the spectral seminorm for `r'` is the spectral seminorm for `r` raised to the power
`log r' / log r`. -/
theorem spectralSeminorm_rpow (d' : TateNormDatum A)
    (hϖ : d.pseudoUniformizer = d'.pseudoUniformizer) (x : A) :
    spectralSeminorm d' x = spectralSeminorm d x ^ (Real.log d'.radius / Real.log d.radius) := by
  -- Replace the ring of definition of `d` by that of `d'`, keeping the radius of `d`.
  let d₁ : TateNormDatum A :=
    { d' with radius := d.radius, radius_pos := d.radius_pos, radius_lt_one := d.radius_lt_one }
  rw [spectralSeminorm_eq_of_ringOfDefinition d d₁ hϖ rfl]
  refine smoothingFun_eq_rpow_of_forall (tateNorm_one_le d₁)
    (div_pos_of_neg_of_neg (Real.log_neg d'.radius_pos d'.radius_lt_one)
      (Real.log_neg d.radius_pos d.radius_lt_one)) (fun y ↦ ?_) x
  rw [tateNorm_apply, tateNorm_apply, tateGauge_rpow d₁.one_lt_radius_inv d'.one_lt_radius_inv,
    Real.log_inv, Real.log_inv, neg_div_neg_eq]

/-- **The spectral seminorm detects topological nilpotence**: `|x|_sp < 1` exactly when the powers
of `x` tend to zero. -/
theorem spectralSeminorm_lt_one_iff {x : A} :
    spectralSeminorm d x < 1 ↔ IsTopologicallyNilpotent x := by
  have hb := (tateNorm_hasBasis_nhds_zero d).tendsto_right_iff (f := (x ^ · : ℕ → A))
    (la := atTop)
  constructor
  · -- Eventually `‖x ^ n‖ ^ (1 / n) < c` for some `c < 1`, so `‖x ^ n‖ < c ^ n → 0`.
    intro hx
    obtain ⟨c, hxc, hc⟩ := exists_between hx
    have hc₀ : 0 ≤ c := (apply_nonneg _ x).trans hxc.le
    refine hb.2 fun ε hε ↦ ?_
    filter_upwards [(tendsto_spectralSeminorm d x).eventually (gt_mem_nhds hxc),
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc₀ hc).eventually (gt_mem_nhds hε),
      eventually_ne_atTop 0] with n hn hcn hn0
    calc tateNorm d (x ^ n) = (tateNorm d (x ^ n) ^ (1 / n : ℝ)) ^ n := by
          rw [one_div, Real.rpow_inv_natCast_pow (apply_nonneg _ _) hn0]
      _ < c ^ n := pow_lt_pow_left₀ hn (by positivity) hn0
      _ < ε := hcn
  · -- Some positive power `x ^ n` has norm less than one, and `|x|_sp ^ n ≤ ‖x ^ n‖`.
    intro hx
    obtain ⟨n, hn, hn0⟩ := ((hb.1 hx 1 one_pos).and (eventually_ne_atTop 0)).exists
    rw [← pow_lt_one_iff_of_nonneg (apply_nonneg _ x) hn0,
      ← isPowMul_spectralSeminorm d x (Nat.one_le_iff_ne_zero.mpr hn0)]
    exact (spectralSeminorm_le_tateNorm d _).trans_lt hn

/-- **Power-bounded elements have spectral seminorm at most one.** -/
theorem spectralSeminorm_le_one_of_isPowerBounded {x : A} (hx : IsPowerBounded x) :
    spectralSeminorm d x ≤ 1 := by
  -- A fixed power `ϖ ^ k` moves every power of `x` into `A₀`, so `‖x ^ m‖ ≤ r ^ (-k)`.
  obtain ⟨k, hk⟩ := (isPowerBounded_iff.mp hx).exists_pow_mul_subset
    d.isTopologicallyNilpotent_pseudoUniformizer
    (d.isOpen_ringOfDefinition.mem_nhds d.ringOfDefinition.zero_mem)
  have hbound (m : ℕ) : tateNorm d (x ^ m) ≤ d.radius ^ (-(k : ℤ)) := by
    rw [tateNorm_le_zpow_iff, neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]
    exact hk (Set.mul_mem_mul rfl ⟨m, rfl⟩)
  by_contra! h
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (d.radius ^ (-(k : ℤ))) h
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (one_le_zpow_of_nonpos₀ (n := -(k : ℤ)) d.radius_pos d.radius_lt_one.le
      (by omega)).not_gt
      (by simpa using hm)
  rw [← isPowMul_spectralSeminorm d x (Nat.one_le_iff_ne_zero.mpr hm0)] at hm
  exact ((spectralSeminorm_le_tateNorm d _).trans (hbound m)).not_gt hm

/-- **The kernel of the spectral seminorm.** `|x|_sp = 0` exactly when `ϖ ^ (-n) x` is
topologically nilpotent for every `n ≥ 0`. -/
theorem spectralSeminorm_eq_zero_iff {x : A} :
    spectralSeminorm d x = 0 ↔
      ∀ n : ℕ, IsTopologicallyNilpotent (((d.pseudoUniformizer ^ (-(n : ℤ)) : Aˣ) : A) * x) := by
  simp_rw [← spectralSeminorm_lt_one_iff d, spectralSeminorm_zpow_mul, zpow_neg, zpow_natCast,
    inv_mul_lt_iff₀ (pow_pos d.radius_pos _), mul_one]
  refine ⟨fun h n ↦ h ▸ pow_pos d.radius_pos n, fun h ↦ ?_⟩
  by_contra! hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ((apply_nonneg _ x).lt_of_ne' hx) d.radius_lt_one
  exact (h n).not_gt hn

/-- Elements of the closure of zero have spectral seminorm zero. -/
theorem spectralSeminorm_eq_zero_of_mem_closure {x : A} (hx : x ∈ closure ({0} : Set A)) :
    spectralSeminorm d x = 0 :=
  le_antisymm ((spectralSeminorm_le_tateNorm d x).trans ((tateNorm_eq_zero_iff d).2 hx).le)
    (apply_nonneg _ x)

/-- In a nonzero Hausdorff Tate ring the spectral seminorm takes the value one at one. -/
@[simp]
theorem spectralSeminorm_one [T1Space A] [Nontrivial A] : spectralSeminorm d 1 = 1 := by
  rw [spectralSeminorm_apply, smoothingFun_of_powMul _ (tateNorm_one_le d) fun n _ ↦ by simp,
    tateNorm_one]

/-- **Functoriality of the spectral seminorm.** Let `φ : A →+* B` carry the ring of definition of
a norm datum `d` of `A` into that of a norm datum `d'` of `B`, and the pseudouniformiser of `d` to
that of `d'`, the two data having the same radius. Then `φ` does not increase the spectral
seminorm. -/
theorem spectralSeminorm_map_le {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] (d' : TateNormDatum B) (φ : A →+* B)
    (hA₀ : ∀ x ∈ d.ringOfDefinition, φ x ∈ d'.ringOfDefinition)
    (hϖ : φ d.pseudoUniformizer = d'.pseudoUniformizer) (hr : d'.radius = d.radius) (x : A) :
    spectralSeminorm d' (φ x) ≤ spectralSeminorm d x :=
  φ.smoothingFun_map_le_of_le_mul (tateNorm_one_le d) (C := 1)
    (fun y ↦ by simpa using tateNorm_map_le d d' φ hA₀ hϖ hr y) x

end TauCeti.Huber
