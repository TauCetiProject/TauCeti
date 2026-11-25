/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticEstimate
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Real

/-!
# Weighted Sobolev estimates for the right inverse, uniformly over windows of vortices

At a smooth plane vortex `x` with `|α| → 1`, the weak right inverse `Q` of the gauge-fixed
operator `L_x = d₀* ⊕ d₁`, with values orthogonal to the weak kernel, satisfies the weighted
Sobolev estimate

`‖exp(c ρ) Q f‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)`,  `ρ(z) = √(1 + |z|²)`, `|c| < 1/2`

(`TauCeti.Vortex.exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq`).
There the constant `K` comes from the closed graph theorem at the one vortex `x`, so nothing is
known about how it varies with `x`. This file proves the estimate with a constant that depends
only on the degree `m`, a radius `r` containing the zeros, the rate `c`, the order `k` and a bound
`B` on the derivatives of the coordinates of `x` through order `k`
(`TauCeti.Vortex.exists_forall_norm_exp_mul_smul_le_mul_norm_of_forall_mem_norm_le`), and the same
for the adjoint `Q†` on the complement of the weak kernel
(`TauCeti.Vortex.exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_norm_le`).
On a compact window of divisors the zeros lie in a fixed disc, so one constant serves every
representative over the window whose coordinates have derivatives through order `k` bounded by the
same `B`. Correcting approximate solutions glued from plane vortices uses `Q` and `Q†` on errors
decaying like `exp(-c ρ)`, with constants that must not depend on the position of the zeros.

The weighted `L²` estimate is already uniform in this sense
(`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`). The new input is
an elliptic estimate whose constant depends on the field only through bounds on its derivatives
(`TauCeti.Vortex.exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add`): for
a smooth field `x` and a matrix `A` of smooth coefficients, both with derivatives bounded by `B`
through order `k`, a weak `L²` solution `y` of `L_x y = f + A y` whose coordinates in `H^(k+1)`
are given satisfies the a priori estimate

`‖y‖_(H^(k+1)) ≤ K (‖f‖_(H^k) + ‖y‖_(L²))`

with `K` depending only on `k` and `B`. Such coordinates exist as soon as those of `f` in `H^k` do
(`TauCeti.Vortex.mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add`).
The principal part of `L_x` is that of the vacuum operator `L₀`, and `L_x - L₀` is
multiplication by a matrix whose entries are coordinates of `x - vacuumField`. So `y` is a weak
solution of `L₀ y = f + A' y`, where the derivatives of `A'` through order `k` are bounded by
`2 B + 1/2`.
The vacuum estimate `‖y‖_(H^(j+1)) ≤ K₀ (‖g‖_(H^j) + ‖y‖_(L²))` holds with `K₀` depending only on
`j`, and multiplication by a function whose derivatives through order `j` are bounded by `M`
has norm at most `C_j M` on the real elements of `H^j`
(`BesselPotentialSpace.exists_forall_exists_inclusionLp_ae_eq_mul_and_norm_le`). Applying both
with `g = f + A' y` raises the order of the bound on `y` one step at a time, from `L²` to
`H^(k+1)`. The adjoint `L_x*` is treated in the same way
(`TauCeti.Vortex.exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add`).

Sobolev norms are those of the coordinates in Mathlib's Bessel-potential spaces `H^s(ℂ)`, as in
`TauCeti.Analysis.PDE.Vortex.EllipticEstimate`.

## Main results

* `TauCeti.Vortex.exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add`,
  `TauCeti.Vortex.exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add`: the
  a priori elliptic estimates for `L_x - A` and `L_x* - A`, with constants depending only on the
  order and on a bound for the derivatives of `x` and `A`.
* `TauCeti.Vortex.exists_forall_norm_exp_mul_smul_le_mul_norm_of_forall_mem_norm_le`: the weighted
  Sobolev estimate for the right inverse, uniformly over the vortices of degree `m` with zeros in
  a fixed disc and derivatives bounded by `B`.
* `TauCeti.Vortex.exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_norm_le`:
  the same for the adjoint of the right inverse.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

open Complex MeasureTheory Filter BesselPotentialSpace
open scoped Topology RealInnerProductSpace ContDiff BesselPotentialSpace NNReal ENNReal

namespace TauCeti.Vortex

/-! ### Coordinates and matrix coefficients -/

/-- Coordinates in `H^s(ℂ)` of a field also serve, through the inclusion, at every lower order
`r`, with no larger norm. -/
private theorem norm_inclusion_le_and_ae_eq {r s : ℝ} (h : r ≤ s) (hr : 0 ≤ r)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} {u : Fin 4 → H^{s}(ℂ)}
    (hu : ∀ a, ⇑(inclusionLp (hr.trans h) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) :
    ‖fun a ↦ inclusion h (u a)‖ ≤ ‖u‖ ∧
      ∀ a, ⇑(inclusionLp hr (inclusion h (u a))) =ᵐ[volume] fun z ↦ (y z a : ℂ) :=
  ⟨(pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun a ↦
      (norm_inclusion_apply_le h _).trans (norm_le_pi_norm u a),
    fun a ↦ by rw [inclusionLp_inclusion]; exact hu a⟩

/-- Coordinates in `H^s(ℂ)` serve, through the inclusion, at an equal order `r = s`, with the same
norm. This moves coordinates between the orders `((n + 1 : ℕ) : ℝ)` and `(n : ℝ) + 1`. -/
private theorem norm_inclusion_eq_and_ae_eq {r s : ℝ} (h : r = s) (hr : 0 ≤ r)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} {u : Fin 4 → H^{s}(ℂ)}
    (hu : ∀ a, ⇑(inclusionLp (hr.trans h.le) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) :
    ‖fun a ↦ inclusion h.le (u a)‖ = ‖u‖ ∧
      ∀ a, ⇑(inclusionLp hr (inclusion h.le (u a))) =ᵐ[volume] fun z ↦ (y z a : ℂ) := by
  subst h
  exact ⟨by simp only [inclusion_self], fun a ↦ by simpa only [inclusion_self] using hu a⟩

/-- **The coordinates of `f + A y`.** For orders `j ≤ k` there is a constant `C` with the
following property. If `A` is a matrix of smooth coefficients with derivatives bounded by `B`
through order `j`, `u` are coordinates of `y` in `H^j(ℂ)` and `v` coordinates of `f` in `H^k(ℂ)`,
then `f + A y` has coordinates `W` in `H^j(ℂ)` with `‖W‖ ≤ ‖v‖ + C B ‖u‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_add_mulVec {j k : ℕ} (hjk : j ≤ k) :
    ∃ C ≥ 0, ∀ (A : Fin 4 → Fin 4 → ℂ → ℝ), (∀ i j, ContDiff ℝ ∞ (A i j)) → ∀ B : ℝ,
      (∀ i i', ∀ n ≤ j, ∀ z, ‖iteratedFDeriv ℝ n (A i i') z‖ ≤ B) →
      ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(j : ℝ)}(ℂ))
        (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg j) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      ∃ W : Fin 4 → H^{(j : ℝ)}(ℂ),
        (∀ a, ⇑(inclusionLp (Nat.cast_nonneg j) (W a)) =ᵐ[volume]
          fun z ↦ ((f z + WithLp.toLp 2 (fun i ↦ ∑ i' : Fin 4, A i i' z * y z i')) a : ℂ)) ∧
        ‖W‖ ≤ ‖v‖ + C * B * ‖u‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_mul_and_norm_le (E := ℂ) j
  refine ⟨4 * C, by positivity, fun A hA B hAb y f u v hu hv ↦ ?_⟩
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hB : 0 ≤ B := (norm_nonneg _).trans (hAb 0 0 0 (Nat.zero_le j) 0)
  -- The coordinates of the products `A a b y_b`.
  choose w hw hwn using fun a b ↦ hCb (A a b) (hA a b) B (hAb a b) (u b) (fun z ↦ y z b) (hu b)
  refine ⟨fun a ↦ inclusion hjk' (v a) + ∑ b, w a b, fun a ↦ ?_, ?_⟩
  · have hva : ⇑(inclusionLp (Nat.cast_nonneg j) (inclusion hjk' (v a))) =ᵐ[volume]
        fun z ↦ (f z a : ℂ) := by
      rw [inclusionLp_inclusion]; exact hv a
    have hsum := coeFn_inclusionLp_add_ae_eq _ hva
      (coeFn_inclusionLp_add_ae_eq _ (coeFn_inclusionLp_add_ae_eq _ (hw a 0) (hw a 1))
        (coeFn_inclusionLp_add_ae_eq _ (hw a 2) (hw a 3)))
    dsimp only
    rw [Fin.sum_univ_four, show w a 0 + w a 1 + w a 2 + w a 3 =
      (w a 0 + w a 1) + (w a 2 + w a 3) by abel]
    filter_upwards [hsum] with z hz
    rw [hz]
    simp only [PiLp.add_apply, Fin.sum_univ_four, ofReal_add]
    ring
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a ↦ ?_
    calc ‖inclusion hjk' (v a) + ∑ b, w a b‖ ≤ ‖inclusion hjk' (v a)‖ + ∑ b, ‖w a b‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ ‖v‖ + ∑ _b : Fin 4, C * B * ‖u‖ := by
          gcongr with b
          · exact (norm_inclusion_apply_le hjk' _).trans (norm_le_pi_norm v a)
          · exact (hwn a b).trans (by gcongr; exact norm_le_pi_norm u b)
      _ = ‖v‖ + 4 * C * B * ‖u‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Subtracting an entry of the zeroth-order matrix of `L_x - L₀` from a smooth coefficient with
derivatives bounded by `B` gives a smooth coefficient with derivatives bounded by
`2 B + ‖vacuumField 0‖`. -/
private theorem contDiff_and_norm_iteratedFDeriv_sub_gaugeFixedZerothOrderMatrix_le {k : ℕ}
    {B : ℝ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hxb : ∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) {g : ℂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ B) (a b : Fin 4) :
    ContDiff ℝ ∞ (fun z ↦ g z - gaugeFixedZerothOrderMatrix (x z - vacuumField z) a b) ∧
      ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z ↦ g z - gaugeFixedZerothOrderMatrix (x z - vacuumField z) a b) z‖ ≤
          2 * B + ‖vacuumField 0‖ := by
  obtain ⟨hZ, hZb⟩ := contDiff_and_norm_iteratedFDeriv_gaugeFixedZerothOrderMatrix_le hx hxb a b
  refine ⟨hg.sub hZ, fun n hn z ↦ ?_⟩
  rw [fun_iteratedFDeriv_sub_apply (hg.contDiffAt.of_le (mod_cast le_top))
      (hZ.contDiffAt.of_le (mod_cast le_top))]
  linarith [norm_sub_le (iteratedFDeriv ℝ n g z)
    (iteratedFDeriv ℝ n (fun z ↦ gaugeFixedZerothOrderMatrix (x z - vacuumField z) a b) z),
    hgb n hn z, hZb n hn z]

/-- Coefficients with derivatives bounded through order `k` multiply `L²` fields into `L²`. -/
private theorem memLp_mulVec_of_norm_iteratedFDeriv_le {k : ℕ} {Z : Fin 4 → Fin 4 → ℂ → ℝ}
    {B : ℝ} (hZ : ∀ i j, ContDiff ℝ ∞ (Z i j))
    (hZb : ∀ i j, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (Z i j) z‖ ≤ B)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) :
    MemLp (fun z ↦ WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, Z i j z * y z j)) 2 volume :=
  memLp_of_mem_sobolevFields (mulVec_mem_sobolevFields_natCast 0 hZ (fun i j ↦
    ⟨B, (norm_nonneg _).trans (hZb i j 0 (Nat.zero_le k) 0),
      fun n hn z ↦ hZb i j n (hn.trans (Nat.zero_le k)) z⟩) (by simpa using hy))

/-- **Moving the zeroth-order part to the right side.** Let `P` and `P₀` be the formal adjoints of
two operators on test fields that differ by a matrix `Z` of coefficients, in the sense that
`⟪v, P η⟫ = ⟪v, P₀ η⟫ + ⟪Z v, η⟫` pointwise. A square-integrable weak solution of
`L y = f + A y`, tested against `P`, is a weak solution of `L₀ y = f + (A - Z) y`, tested against
`P₀`, as soon as `f`, `A y` and `Z y` are square integrable. -/
private theorem integral_inner_eq_add_sub_mulVec
    {P P₀ : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)}
    {Z A : Fin 4 → Fin 4 → ℂ → ℝ}
    (hP : ∀ η z (v : EuclideanSpace ℝ (Fin 4)), ⟪v, P η z⟫ =
      ⟪v, P₀ η z⟫ + ⟪WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, Z i j z * v j), η z⟫)
    (hP₀ : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P₀ η) 2 volume)
    {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hAy : MemLp (fun z ↦ WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j)) 2 volume)
    (hZy : MemLp (fun z ↦ WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, Z i j z * y z j)) 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, P η z⟫ =
        ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪y z, P₀ η z⟫ =
      ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, (A i j z - Z i j z) * y z j), η z⟫ := by
  have hηL : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hpt (z : ℂ) :
      f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, (A i j z - Z i j z) * y z j) =
        f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j) -
          WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, Z i j z * y z j) := by
    ext i
    simp [sub_mul, Finset.sum_sub_distrib, add_sub_assoc]
  simp_rw [hpt]
  exact integral_inner_eq_integral_inner_sub_of_inner_eq_add (fun z ↦ hP η z (y z))
    (hy.integrable_inner (hP₀ η hη hηc)) ((hf.add hAy).integrable_inner hηL)
    (hZy.integrable_inner hηL) (hweak η hη hηc)

/-! ### The uniform bootstrap from the vacuum -/

section Bootstrap

variable {P : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)}

/-- One order of the uniform bootstrap, by induction on the order `j ≤ k + 1`. Here `P` is the
formal adjoint at the vacuum of the operator (`L₀` or `L₀*`), and `hest` is the elliptic estimate
for it at every order, whose constant depends only on the order. For a weak `L²` solution `y` of
`L₀ y = f + A y`, with `A` bounded by `B` through order `k`, given `H^j` coordinates of `y` are
bounded by `K (‖f‖_(H^k) + ‖y‖_(L²))`, with `K` depending only on `k`, `B` and `j`. -/
private theorem exists_norm_le_of_vacuum
    (hest : ∀ j : ℕ, ∃ K ≥ 0, ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4))
      (u : Fin 4 → H^{(j : ℝ) + 1}(ℂ)) (v : Fin 4 → H^{(j : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg j) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ = ∫ z, ⟪f z, η z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal))
    (k : ℕ) (B : ℝ) (j : ℕ) (hj : j ≤ k + 1) :
    ∃ K ≥ 0, ∀ (A : Fin 4 → Fin 4 → ℂ → ℝ), (∀ i j, ContDiff ℝ ∞ (A i j)) →
      (∀ i j, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ B) →
      ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4)) (v : Fin 4 → H^{(k : ℝ)}(ℂ)), MemLp y 2 volume →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      ∀ u : Fin 4 → H^{(j : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg j) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal) := by
  induction j with
  | zero =>
    -- In `H^0 = L²` the coordinates are bounded by the `L²` norm of the field: through the
    -- inclusions `H^0 ⊆ H^(↑0) ⊆ H^0`, the norm of `u a` is that of its `L²` function.
    refine ⟨1, zero_le_one, fun A _ _ y f v hy _ _ u hu ↦ ?_⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a ↦ ?_
    have h₀ : ((0 : ℕ) : ℝ) ≤ 0 := by simp
    have hy₀ : ‖inclusionLp (Nat.cast_nonneg 0) (u a)‖ ≤ (eLpNorm y 2 volume).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (hu a)]
      refine ENNReal.toReal_mono hy.eLpNorm_ne_top (eLpNorm_mono
        (Complex.continuous_ofReal.comp_aestronglyMeasurable
          (memLp_piLp_iff.1 hy a).aestronglyMeasurable) fun z ↦ ?_)
      rw [Complex.norm_real]
      exact PiLp.norm_apply_le (y z) a
    calc ‖u a‖ = ‖inclusion h₀ (inclusion (Nat.cast_nonneg 0) (u a))‖ := by
          rw [inclusion_inclusion, inclusion_self]
      _ ≤ ‖inclusion (Nat.cast_nonneg 0) (u a)‖ := norm_inclusion_apply_le h₀ _
      _ = ‖inclusionLp (Nat.cast_nonneg 0) (u a)‖ := by rw [← toLp_inclusion, norm_toLp_eq]
      _ ≤ 1 * (‖v‖ + (eLpNorm y 2 volume).toReal) := by linarith [norm_nonneg v]
  | succ j ih =>
    -- The right side `f + A y` is bounded in `H^j` by the bound on `y` in `H^j`, and the vacuum
    -- estimate turns this into a bound on `y` in `H^(j+1)`.
    obtain ⟨Kj, hKj, hKjb⟩ := ih (by omega)
    obtain ⟨K₀, hK₀, hK₀b⟩ := hest j
    obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_add_mulVec (j := j) (k := k)
      (by omega)
    refine ⟨K₀ * (1 + C * |B| * Kj), by positivity, fun A hA hAb y f v hy hv hweak u hu ↦ ?_⟩
    have hB : 0 ≤ B := (norm_nonneg _).trans (hAb 0 0 0 (Nat.zero_le k) 0)
    have hjs : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast j.le_succ
    -- The coordinates of `y` in `H^j`, and in `H^(j+1)` indexed by `(j : ℝ) + 1`.
    obtain ⟨-, hujy⟩ := norm_inclusion_le_and_ae_eq hjs (Nat.cast_nonneg j) hu
    obtain ⟨hu', hu'y⟩ := norm_inclusion_eq_and_ae_eq (Nat.cast_succ j).symm (by positivity) hu
    have hujb := hKjb A hA hAb y f v hy hv hweak _ hujy
    obtain ⟨W, hW, hWn⟩ := hCb A hA B (fun a b n hn ↦ hAb a b n (hn.trans (by omega))) y f _ v
      hujy hv
    calc ‖u‖ = ‖fun a ↦ inclusion (Nat.cast_succ j).symm.le (u a)‖ := hu'.symm
      _ ≤ K₀ * (‖W‖ + (eLpNorm y 2 volume).toReal) := hK₀b y _ _ W hu'y hW hweak
      _ ≤ K₀ * (‖v‖ + C * B * (Kj * (‖v‖ + (eLpNorm y 2 volume).toReal)) +
            (eLpNorm y 2 volume).toReal) := by gcongr; exact hWn.trans (by gcongr)
      _ = K₀ * (1 + C * |B| * Kj) * (‖v‖ + (eLpNorm y 2 volume).toReal) := by
          rw [abs_of_nonneg hB]; ring

/-- **The uniform bootstrap from the vacuum.** Here `hest` is the elliptic estimate for `P` with a
zeroth-order term at every order, as given at the vacuum by
`exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add` and
`exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add`. Taking no zeroth-order term
there, weak `L²` solutions of `L₀ y = f + A y` with given `H^(k+1)` coordinates, with `A` smooth
and bounded by `B` through order `k`, satisfy `‖y‖_(H^(k+1)) ≤ K (‖f‖_(H^k) + ‖y‖_(L²))` with `K`
depending only on `k` and `B`. -/
private theorem exists_norm_le_mul_add_of_vacuum
    (hest : ∀ (j : ℕ) (A : Fin 4 → Fin 4 → ℂ → ℝ), (∀ i i', ContDiff ℝ ∞ (A i i')) →
      (∀ i i', ∃ M ≥ 0, ∀ n ≤ j, ∀ z, ‖iteratedFDeriv ℝ n (A i i') z‖ ≤ M) →
      ∃ K ≥ 0, ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4))
        (u : Fin 4 → H^{(j : ℝ) + 1}(ℂ)) (v : Fin 4 → H^{(j : ℝ)}(ℂ)),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
        (∀ a, ⇑(inclusionLp (Nat.cast_nonneg j) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
        (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
          ∫ z, ⟪y z, P η z⟫ =
            ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ i' : Fin 4, A i i' z * y z i'), η z⟫) →
        ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal))
    (k : ℕ) (B : ℝ) :
    ∃ K ≥ 0, ∀ (A : Fin 4 → Fin 4 → ℂ → ℝ), (∀ i j, ContDiff ℝ ∞ (A i j)) →
      (∀ i j, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ B) →
      ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ))
        (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_le_of_vacuum (fun j ↦ (hest j (fun _ _ _ ↦ 0)
    (fun _ _ ↦ contDiff_const) fun _ _ ↦ ⟨0, le_rfl, fun n _ z ↦ by simp⟩).imp
      fun K hK ↦ ⟨hK.1, fun y f u v hu hv hweak ↦ hK.2 y f u v hu hv fun η hη hηc ↦ by
        simpa [← Pi.zero_def] using hweak η hη hηc⟩) k B (k + 1) le_rfl
  refine ⟨K, hK, fun A hA hAb y f u v hu hv hweak ↦ ?_⟩
  have hy : MemLp y 2 volume := memLp_of_forall_inclusionLp_ae_eq (by positivity) hu
  obtain ⟨hn, hu'⟩ := norm_inclusion_eq_and_ae_eq (Nat.cast_succ k) (Nat.cast_nonneg (k + 1)) hu
  exact hn.symm.trans_le (hKb A hA hAb y f v hy hv hweak _ hu')

end Bootstrap

/-! ### The elliptic estimates with constants depending on derivative bounds -/

/-- The coordinates of the vacuum, a constant field, have bounded derivatives of every order. -/
private theorem exists_norm_iteratedFDeriv_vacuumField_apply_le (i : Fin 4) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ vacuumField z i) z‖ ≤ C := by
  rw [vacuumField_eq_const]
  exact ⟨_, norm_iteratedFDeriv_const_le n (vacuumField 0 i)⟩

/-- **The elliptic estimate for `L_x - A`, uniformly in the field.** For every order `k` and bound
`B` there is a constant `K` with the following property. Let `x` be a smooth field and `A` a
`4 × 4` matrix of smooth real functions, all of whose coordinates and entries have derivatives
bounded by `B` through order `k`. A square-integrable weak solution `y` of `L_x y = f + A y`,
tested against smooth compactly supported fields, with given coordinates
`u : Fin 4 → H^(k+1)(ℂ)`, satisfies the a priori estimate

`‖y‖_(H^(k+1)) ≤ K (‖f‖_(H^k) + ‖y‖_(L²))`,

where the Sobolev norms are those of `u` and of the coordinates `v : Fin 4 → H^k(ℂ)` of `f`. Such
`u` exist as soon as `v` does, by
`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add`. For a single field
this is
`exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add`; here the constant depends on
`x` and `A` only through `B`. -/
theorem exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add (k : ℕ)
    (B : ℝ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (A : Fin 4 → Fin 4 → ℂ → ℝ),
      ContDiff ℝ ∞ x → (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ i j, ContDiff ℝ ∞ (A i j)) →
      (∀ i j, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ B) →
      ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ))
        (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal) := by
  -- The bootstrap from the vacuum estimate, whose constant depends only on the order.
  obtain ⟨K, hK, hKb⟩ := exists_norm_le_mul_add_of_vacuum (P := gaugeFixedAdjoint vacuumField)
    (fun j _ ↦ exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add j
      contDiff_vacuumField fun i n _ ↦ exists_norm_iteratedFDeriv_vacuumField_apply_le i n)
    k (2 * B + ‖vacuumField 0‖)
  refine ⟨K, hK, fun x A hx hxb hA hAb y f u v hu hv hweak ↦ ?_⟩
  -- `y` is a weak solution of `L₀ y = f + (A - Z) y`, where `Z` is the matrix of `L_x - L₀`.
  have hZ := contDiff_and_norm_iteratedFDeriv_gaugeFixedZerothOrderMatrix_le hx hxb
  have hA' (i j : Fin 4) := contDiff_and_norm_iteratedFDeriv_sub_gaugeFixedZerothOrderMatrix_le
    hx hxb (hA i j) (hAb i j) i j
  have hy : MemLp y 2 volume := memLp_of_forall_inclusionLp_ae_eq (by positivity) hu
  exact hKb _ (fun i j ↦ (hA' i j).1) (fun i j ↦ (hA' i j).2) y f u v hu hv fun η hη hηc ↦
    integral_inner_eq_add_sub_mulVec (P := gaugeFixedAdjoint x)
      (fun η z v ↦ by rw [inner_gaugeFixedAdjoint_eq_add_inner_gaugeFixedZerothOrder x
        vacuumField, gaugeFixedZerothOrder_apply])
      (fun η hη hηc ↦
        memLp_gaugeFixedAdjoint (contDiff_vacuumField (n := 0)).continuous (hη.of_le (by simp)) hηc)
      hy (memLp_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hv)
      (memLp_mulVec_of_norm_iteratedFDeriv_le hA hAb hy)
      (memLp_mulVec_of_norm_iteratedFDeriv_le (fun i j ↦ (hZ i j).1) (fun i j ↦ (hZ i j).2) hy)
      hweak hη hηc

/-- **The elliptic estimate for `L_x* - A`, uniformly in the field.** For every order `k` and
bound `B` there is a constant `K` with the following property. Let `x` be a smooth field and `A`
a `4 × 4` matrix of smooth real functions, all of whose coordinates and entries have derivatives
bounded by `B` through order `k`. A square-integrable weak solution `η` of `L_x* η = g + A η`, in
the sense that `∫ ⟪η, L_x w⟫ = ∫ ⟪g + A η, w⟫` for every smooth compactly supported field `w`,
with given coordinates `u : Fin 4 → H^(k+1)(ℂ)`, satisfies the a priori estimate

`‖η‖_(H^(k+1)) ≤ K (‖g‖_(H^k) + ‖η‖_(L²))`,

where the Sobolev norms are those of `u` and of the coordinates `v : Fin 4 → H^k(ℂ)` of `g`. Such
`u` exist as soon as `v` does, by
`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq_add`. For a single field
this is `exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add`;
here the constant depends on `x` and `A` only through `B`. -/
theorem exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add (k : ℕ)
    (B : ℝ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (A : Fin 4 → Fin 4 → ℂ → ℝ),
      ContDiff ℝ ∞ x → (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ i j, ContDiff ℝ ∞ (A i j)) →
      (∀ i j, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ B) →
      ∀ (η g : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ))
        (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (η z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (g z a : ℂ)) →
      (∀ w : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ w → HasCompactSupport w →
        ∫ z, ⟪η z, gaugeFixedOperator x w z⟫ =
          ∫ z, ⟪g z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * η z j), w z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm η 2 volume).toReal) := by
  -- The bootstrap from the vacuum estimate for the adjoint, whose constant depends only on the
  -- order.
  obtain ⟨K, hK, hKb⟩ := exists_norm_le_mul_add_of_vacuum (P := gaugeFixedOperator vacuumField)
    (fun j _ ↦ exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add j
      contDiff_vacuumField fun i n _ ↦ exists_norm_iteratedFDeriv_vacuumField_apply_le i n)
    k (2 * B + ‖vacuumField 0‖)
  refine ⟨K, hK, fun x A hx hxb hA hAb η g u v hu hv hweak ↦ ?_⟩
  -- `η` is a weak solution of `L₀* η = g + (A - Zᵀ) η`, where `Z` is the matrix of `L_x - L₀`.
  have hZ := contDiff_and_norm_iteratedFDeriv_gaugeFixedZerothOrderMatrix_le hx hxb
  have hA' (i j : Fin 4) := contDiff_and_norm_iteratedFDeriv_sub_gaugeFixedZerothOrderMatrix_le
    hx hxb (hA i j) (hAb i j) j i
  have hη : MemLp η 2 volume := memLp_of_forall_inclusionLp_ae_eq (by positivity) hu
  exact hKb _ (fun i j ↦ (hA' i j).1) (fun i j ↦ (hA' i j).2) η g u v hu hv fun w hw hwc ↦
    integral_inner_eq_add_sub_mulVec (P := gaugeFixedOperator x)
      (Z := fun i j z ↦ gaugeFixedZerothOrderMatrix (x z - vacuumField z) j i)
      (fun w z v ↦ by
        rw [inner_gaugeFixedOperator_eq_add_inner_toEuclideanLin_transpose x vacuumField,
          Matrix.toLpLin_apply, funext (Matrix.mulVec_apply_eq_sum _ _)]
        simp only [Matrix.transpose_apply])
      (fun w hw hwc ↦ (continuous_gaugeFixedOperator (contDiff_vacuumField (n := 0)).continuous
        (hw.of_le (by simp))).memLp_of_hasCompactSupport (hasCompactSupport_gaugeFixedOperator hwc))
      hη (memLp_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hv)
      (memLp_mulVec_of_norm_iteratedFDeriv_le hA hAb hη)
      (memLp_mulVec_of_norm_iteratedFDeriv_le (fun i j ↦ (hZ j i).1) (fun i j ↦ (hZ j i).2) hη)
      hweak hw hwc

/-! ### The weighted estimates over a window of divisors -/

/-- **The weighted Sobolev estimate for the right inverse, uniformly over a window of
divisors.** For every degree `m`, radius `r`, bound `B`, rate `|c| < 1/2` and order `k` there is a
constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane
vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius `r` and whose
coordinates have derivatives bounded by `B` through order `k`. Let `y` be the square-integrable
weak solution of `L_x y = f` orthogonal to the weak kernel of `L_x`, that is the value at `f` of
the weak right inverse. If the coordinates of `exp(c ρ) f` are given by `v : Fin 4 → H^k(ℂ)`, then
those of `exp(c ρ) y` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K ‖v‖`. That is,

`‖exp(c ρ) Q f‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)`,

with `K` depending only on `m`, `r`, `B`, `c` and `k`, not on the vortex or on the position of its
zeros in the disc, collisions included. For a single vortex this is
`exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq`. -/
theorem exists_forall_norm_exp_mul_smul_le_mul_norm_of_forall_mem_norm_le (m : ℕ) (r B : ℝ)
    {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ r) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) →
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪y z, w z⟫ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) a : ℂ)) ∧ ‖u‖ ≤ K * ‖v‖ := by
  -- The uniform weighted `L²` estimate bounds `exp(c ρ) y` in `L²` by `exp(c ρ) f`, and the uniform
  -- elliptic estimate for the weight commutator turns this into the Sobolev bound.
  obtain ⟨K₀, hK₀⟩ := exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le
    (μ := volume) m r hc
  obtain ⟨M, -, hM⟩ := exists_forall_norm_iteratedFDeriv_expWeightCoeff_le c k
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add k (max B M)
  exact ⟨K₁ * (1 + 4 * K₀), by positivity, fun x D hx hsol hframe hD hDr hxb f y hweak horth v hv ↦
    exists_inclusionLp_ae_eq_and_norm_le_of_eLpNorm_exp_mul_smul_le k hx
      (fun i n hn ↦ ⟨B, hxb i n hn⟩) hK₁
      (hK₁b x (expWeightCoeff c) hx (fun i n hn z ↦ (hxb i n hn z).trans (le_max_left _ _))
        (contDiff_expWeightCoeff c) fun i j n hn z ↦ (hM i j n hn z).trans (le_max_right _ _))
      hweak (hK₀ x D hx hsol hframe hD hDr f y hweak horth) hv⟩

/-- **The weighted Sobolev estimate for the adjoint of the right inverse, uniformly over a window
of divisors.** For every degree `m`, radius `r`, bound `B`, rate `|c| < 1/2` and order `k` there
is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth
plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius `r` and
whose coordinates have derivatives bounded by `B` through order `k`. Let `Q` be a bounded operator
on `L²(ℂ; ℝ⁴)` such that `Q f` is a weak solution of `L_x y = f` orthogonal to the weak kernel of
`L_x` for every `f`, and let `g ∈ L²` be orthogonal to the weak kernel of `L_x`. If the
coordinates of `exp(c ρ) g` are given by `v : Fin 4 → H^k(ℂ)`, then those of `exp(c ρ) Q† g` are
given by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K ‖v‖`. That is,

`‖exp(c ρ) Q† g‖_(H^(k+1)) ≤ K ‖exp(c ρ) g‖_(H^k)`

on the `L²`-orthogonal complement of the weak kernel, with `K` depending only on `m`, `r`, `B`,
`c` and `k`. For a single vortex this is `exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm`. -/
theorem exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_norm_le (m : ℕ)
    (r B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ r) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      ∀ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) →
      (∀ f w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q f z, w z⟫ = 0) →
      ∀ g : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪g z, w z⟫ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) a : ℂ)) ∧
        ‖u‖ ≤ K * ‖v‖ := by
  -- The uniform weighted `L²` estimate for `Q†` bounds `exp(c ρ) Q† g` in `L²` by `exp(c ρ) g`,
  -- and the uniform elliptic estimate for `L_x*` with the weight commutator turns this into the
  -- Sobolev bound.
  obtain ⟨K₀, hK₀⟩ := exists_forall_eLpNorm_exp_mul_smul_adjoint_apply_le_of_forall_mem_norm_le
    (μ := volume) m r hc
  obtain ⟨M, -, hM⟩ := exists_forall_norm_iteratedFDeriv_expWeightCoeff_le c k
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add k (max B M)
  exact ⟨K₁ * (1 + 4 * K₀), by positivity,
    fun x D hx hsol hframe hD hDr hxb Q hweak horth g hg v hv ↦
      exists_inclusionLp_ae_eq_and_norm_le_of_eLpNorm_exp_mul_smul_adjoint_apply_le k hx
        (fun i n hn ↦ ⟨B, hxb i n hn⟩) hK₁
        (hK₁b x _ hx (fun i n hn z ↦ (hxb i n hn z).trans (le_max_left _ _))
          (fun i j ↦ (contDiff_expWeightCoeff c j i).neg)
          fun i j n hn z ↦ by simpa using (hM j i n hn z).trans (le_max_right _ _))
        hweak hg (hK₀ x D hx hsol hframe hD hDr Q hweak horth g) hv⟩

end TauCeti.Vortex
