/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import TauCeti.Analysis.Pseudodifferential.LatticeDecomposition
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Composition of symbols with uniform estimates

Let `p` and `a` be symbols of orders `m'` and `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Their quantizations act on Schwartz space
(`TauCeti.Symbol.quantizeUniformCLM`), and this file shows that `Op(p) ∘ Op(a)` is again the
quantization of a symbol of order `m' + m` with estimates uniform in the position
(`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`). The composition symbol `p # a` of
`TauCeti.Symbol.sharp` is only defined when `a` has compact spatial support, since it is built
from the Fourier transforms of the position slices of `a`; a uniform symbol such as `a = 1` has
no such Fourier transforms. With this theorem the uniform symbols form an algebra under
composition; for instance `J^t ∘ Op(a)` is the quantization of a uniform symbol for every Bessel
multiplier `J^t`, which gives the Sobolev mapping of uniform symbols at every order
(`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`).

## The construction

Cut `a` into the pieces `aⱼ(x, ξ) = χ(x - j) a(x, ξ)`, `j ∈ ℤⁿ`, by the integer translates of
the bump `χ = TauCeti.latticeBump n`, a smooth partition of unity. The pieces have compact
spatial support in balls of radius `√n` about the lattice points, with symbol estimates
independent of `j`, so `p # aⱼ` is defined. Its estimates are uniform in `j`, because the Fourier
transforms of the slices of `aⱼ` are bounded by the `L¹` norms of the slices and their
derivatives, which do not depend on where the piece sits. Away from `j`, `p # aⱼ` decays faster
than every power of the distance: the commutator identity

`(x - z)ⱼ (p # b) = p # ((y - z)ⱼ b) + i (∂_{ξⱼ} p) # b`,

which comes from the commutator of `Op(p)` with a coordinate function
(`TauCeti.Symbol.coordSub_smul_coefficient_sharp`), trades a factor `(x - j)ₖ`
for a frequency derivative of `p` or a factor bounded on the support of `aⱼ`. So every mixed
derivative of `p # aⱼ` is bounded by `C ⟨x - j⟩^(-2n) ⟨ξ⟩^(m' + m - |β|)`, and these bounds are
summable over the lattice uniformly in `x`. The series `c = ∑ⱼ p # aⱼ` therefore converges, with
all its derivatives, to a symbol of order `m' + m` with uniform estimates; the derivatives of the
sum are the sums of the derivatives because the bounds are summable near each point
(`TauCeti.Symbol.exists_isUniform_hasSum_coefficient`). The pieces `aⱼ`, the uniform decay of the
Fourier transforms of their slices and the summation of the series are the lattice decomposition
of `TauCeti.Analysis.Pseudodifferential.LatticeDecomposition`.

Finally `Op(c) = Op(p) ∘ Op(a)`. On a Schwartz function `u`, `Op(p # aⱼ) u = Op(p) (χ(· - j) w)`
with `w = Op(a) u`, and the series `∑ⱼ χ(· - j) w` converges to `w` in Schwartz space
(`SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub`), on which `Op(p)` is continuous. On the other
side `∑ⱼ Op(p # aⱼ) u (x) = Op(c) u (x)` by dominated convergence in the frequency.

## Main results

* `TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`: **composition of uniform symbols**.
  The composition of the quantizations of two uniform symbols of orders `m'` and `m` is the
  quantization of a uniform symbol of order `m' + m`. The symbol is unique
  (`TauCeti.Symbol.quantizeSchwartzValue_injective`); when `a` has compact spatial support it is
  `p # a` (`TauCeti.Symbol.coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.8 (composition in the symbol classes with estimates uniform on `ℝⁿ`).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Metric
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The composition with a member of a ball family -/

section Sharp

variable {ι : Type*} {z : ι → CoordinateSpace n} {r : ℝ}

/-- **The composition symbol is bounded uniformly in the family.** If `p` is a symbol of order
`m'` with estimates uniform in the position and `c` is a ball family of order `m`, then
`‖(p # cᵢ)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)` with `C` independent of `i` and `x`. -/
private theorem IsBallFamily.exists_norm_sharp_le {p : Symbol n W U m'} (hp : p.IsUniform)
    {c : ι → Symbol n V W m} (hc : IsBallFamily z r c) :
    ∃ C, ∀ i x ξ, ‖(p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient (x, ξ)‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨Cp, hCp0, hCp⟩ := hp.exists_bound_coefficient
  obtain ⟨D, hD⟩ := hc.exists_norm_fourier_le_rpow (|m'| + n + 1)
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  set K := Cp * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * D
  refine ⟨K * I, fun i x ξ ↦ ?_⟩
  have hbound (η : CoordinateSpace n) : ‖(𝐞 ⟪η, x⟫ : ℂ) •
      (p.coefficient (x, ξ + (2 * π) • η)).comp (𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η)‖ ≤
        K * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [norm_smul, Circle.norm_coe, one_mul]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hshift :=
      one_add_norm_add_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m' ξ η
    have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + n + 1) / 2) =
        (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    calc ‖p.coefficient (x, ξ + (2 * π) • η)‖ * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖
        ≤ (Cp * (2 ^ (|m'| / 2) * (2 * π) ^ |m'| * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
            (1 + ‖η‖ ^ 2) ^ (|m'| / 2))) *
          (D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + n + 1) / 2)) := by
          gcongr
          · exact (hCp x _).trans (mul_le_mul_of_nonneg_left hshift hCp0)
          · exact hD i η ξ
      _ = K * ((1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + n + 1) / 2)) := by ring
      _ = _ := by rw [hξ, hη]
  rw [coefficient_sharp]
  refine (norm_integral_le_of_norm_le (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (K * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))) (.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul]
  ring

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]

/-- Applying the commutator with a coordinate function twice:
`(x - z)ⱼ² (p # b) = p # ((y - z)ⱼ² b) + 2i (∂_{ξⱼ} p) # ((y - z)ⱼ b) - (∂_{ξⱼ}² p) # b`, which
bounds `(x - z)ⱼ² ‖(p # b)(x, ξ)‖` by the norms of the three terms. -/
private theorem sq_coordSub_mul_norm_coefficient_sharp_le (p : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) (z : CoordinateSpace n) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    ((x - z) j) ^ 2 * ‖(p.sharp b hb).coefficient (x, ξ)‖ ≤
      ‖(p.sharp ((coordSubSymbol z j).comp ((coordSubSymbol z j).comp b))
          ((hb.comp_left _).comp_left _)).coefficient (x, ξ)‖ +
        2 * ‖((frequencyDeriv j p).sharp ((coordSubSymbol z j).comp b)
          (hb.comp_left _)).coefficient (x, ξ)‖ +
        ‖((frequencyDeriv j (frequencyDeriv j p)).sharp b hb).coefficient (x, ξ)‖ := by
  set a : ℂ := ((x - z) j : ℂ)
  have e₁ := coordSub_smul_coefficient_sharp p hb z j x ξ
  have e₂ := coordSub_smul_coefficient_sharp p (hb.comp_left (coordSubSymbol z j)) z j x ξ
  have e₃ := coordSub_smul_coefficient_sharp (frequencyDeriv j p) hb z j x ξ
  have hsq : a • a • (p.sharp b hb).coefficient (x, ξ) =
      (p.sharp ((coordSubSymbol z j).comp ((coordSubSymbol z j).comp b))
        ((hb.comp_left _).comp_left _)).coefficient (x, ξ) +
      (2 * Complex.I) • ((frequencyDeriv j p).sharp ((coordSubSymbol z j).comp b)
        (hb.comp_left _)).coefficient (x, ξ) -
      ((frequencyDeriv j (frequencyDeriv j p)).sharp b hb).coefficient (x, ξ) := by
    rw [e₁, smul_add, e₂, smul_comm a Complex.I, e₃, smul_add, smul_smul Complex.I Complex.I,
      Complex.I_mul_I, two_mul, add_smul, neg_one_smul]
    abel
  have hnorm : ‖a • a • (p.sharp b hb).coefficient (x, ξ)‖ =
      ((x - z) j) ^ 2 * ‖(p.sharp b hb).coefficient (x, ξ)‖ := by
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc, ← sq, sq_abs]
  have h2I : ‖(2 * Complex.I)‖ = 2 := by simp
  rw [← hnorm, hsq]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans_eq ?_) le_rfl)
  rw [norm_smul, h2I]

/-- **Decay away from the centres.** If `p` is a symbol of order `m'` with estimates uniform in
the position and `c` is a ball family of order `m`, then `(p # cᵢ)(x, ξ)` decays in the distance
from `x` to the centre `zᵢ` faster than every power, uniformly in `i`:
`‖x - zᵢ‖ ^ (2N) ‖(p # cᵢ)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)`. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_sharp_le (N : ℕ) :
    ∀ {m' : ℝ} {p : Symbol n W U m'}, p.IsUniform → ∀ {m : ℝ} {c : ι → Symbol n V W m}
      (hc : IsBallFamily z r c), ∃ C, 0 ≤ C ∧ ∀ i x ξ, ‖x - z i‖ ^ (2 * N) *
        ‖(p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient (x, ξ)‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  induction N with
  | zero =>
    intro m' p hp m c hc
    obtain ⟨C, hC⟩ := hc.exists_norm_sharp_le hp
    refine ⟨max C 0, le_max_right _ _, fun i x ξ ↦ ?_⟩
    rw [mul_zero, pow_zero, one_mul]
    exact (hC i x ξ).trans (by gcongr; exact le_max_left _ _)
  | succ N ih =>
    intro m' p hp m c hc
    have hc' (j : Fin n) := hc.comp_coordSubSymbol j
    have hp' (j : Fin n) := hp.frequencyDeriv j
    choose A hA0 hA using fun j ↦ ih hp ((hc' j).comp_coordSubSymbol j)
    choose B hB0 hB using fun j ↦ ih (hp' j) (hc' j)
    choose C hC0 hC using fun j ↦ ih ((hp' j).frequencyDeriv j) hc
    refine ⟨∑ j, (A j + 2 * B j + C j), Finset.sum_nonneg fun j _ ↦ by
      linarith [hA0 j, hB0 j, hC0 j], fun i x ξ ↦ ?_⟩
    set w := (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)
    have hci := hc.hasCompactSpatialSupport i
    have hj (j : Fin n) : ‖x - z i‖ ^ (2 * N) * (((x - z i) j) ^ 2 *
        ‖(p.sharp (c i) hci).coefficient (x, ξ)‖) ≤ (A j + 2 * B j + C j) * w := by
      have hA' := hA j i x ξ
      have ewA : (m' + (0 + (0 + m))) / 2 = (m' + m) / 2 := by ring
      rw [ewA] at hA'
      have hwB : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + (0 + m)) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      have hwC : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 - 1 + m) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      refine (mul_le_mul_of_nonneg_left (sq_coordSub_mul_norm_coefficient_sharp_le p hci (z i) j
        x ξ) (by positivity)).trans ?_
      rw [mul_add, mul_add, mul_left_comm _ 2]
      exact (add_le_add (add_le_add hA' (mul_le_mul_of_nonneg_left
        ((hB j i x ξ).trans (mul_le_mul_of_nonneg_left hwB (hB0 j))) zero_le_two))
        ((hC j i x ξ).trans (mul_le_mul_of_nonneg_left hwC (hC0 j)))).trans_eq (by ring)
    calc ‖x - z i‖ ^ (2 * (N + 1)) * ‖(p.sharp (c i) hci).coefficient (x, ξ)‖
        = ∑ j, ‖x - z i‖ ^ (2 * N) * (((x - z i) j) ^ 2 *
            ‖(p.sharp (c i) hci).coefficient (x, ξ)‖) :=
          norm_pow_two_mul_succ_mul_eq_sum (x - z i) N _
      _ ≤ ∑ j, (A j + 2 * B j + C j) * w := Finset.sum_le_sum fun j _ ↦ hj j
      _ = _ := by rw [Finset.sum_mul]

/-- **Decay of the derivatives away from the centres.** Every mixed derivative
`∂ₓ^α ∂_ξ^β (p # cᵢ)` satisfies `‖x - zᵢ‖ ^ (2N) ‖∂ₓ^α ∂_ξ^β (p # cᵢ)(x, ξ)‖ ≤
C ⟨ξ⟩ ^ (m' + m - |β|)`, uniformly in `i`. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le (N : ℕ)
    (α β : List (Fin n)) :
    ∀ {m' : ℝ} {p : Symbol n W U m'}, p.IsUniform → ∀ {m : ℝ} {c : ι → Symbol n V W m}
      (hc : IsBallFamily z r c), ∃ C, 0 ≤ C ∧ ∀ i x ξ, ‖x - z i‖ ^ (2 * N) *
        ‖mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by simpa [List.length_eq_zero_iff] using hD
    intro m' p hp m c hc
    simpa using IsBallFamily.exists_norm_sub_pow_mul_norm_sharp_le N hp hc
  | succ D ih =>
    intro m' p hp m c hc
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C₁, hC₁0, hC₁⟩ := ih α' [] (by simpa using hD) (hp.spatialDeriv j) hc
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih α' [] (by simpa using hD) hp (hc.map_spatialDeriv j)
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun i x ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv, spatialDeriv_sharp, coefficient_add,
          mixedDeriv_add (Symbol.contDiff_coefficient _) (Symbol.contDiff_coefficient _)]
        refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
        rw [mul_add, add_mul]
        exact add_le_add (hC₁ i x ξ) (hC₂ i x ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih α β' hlen (hp.frequencyDeriv j) hc
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih α β' hlen hp (hc.map_frequencyDeriv j)
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun i x ξ ↦ ?_⟩
      have hci := hc.hasCompactSpatialSupport i
      have hfun : (frequencyDeriv j (p.sharp (c i) hci)).coefficient =
          ((frequencyDeriv j p).sharp (c i) hci).coefficient +
            (p.sharp (frequencyDeriv j (c i)) (hci.frequencyDeriv j)).coefficient :=
        funext fun q ↦ coefficient_frequencyDeriv_sharp hci j q.1 q.2
      have e₁ : (m' - 1 + m - β'.length) / 2 = (m' + m - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have e₂ : (m' + (m - 1) - β'.length) / 2 = (m' + m - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h₁ := hC₁ i x ξ
      have h₂ := hC₂ i x ξ
      rw [e₁] at h₁
      rw [e₂] at h₂
      rw [← mixedDeriv_frequencyDeriv, hfun,
        mixedDeriv_add (Symbol.contDiff_coefficient _) (Symbol.contDiff_coefficient _)]
      refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
      rw [mul_add, add_mul]
      exact add_le_add h₁ h₂

/-- The derivative estimates of `p # cᵢ` with the weight `(1 + ‖x - zᵢ‖²) ^ (-n)` in the
position. -/
private theorem IsBallFamily.exists_norm_mixedDeriv_sharp_le {p : Symbol n W U m'}
    (hp : p.IsUniform) {c : ι → Symbol n V W m} (hc : IsBallFamily z r c)
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖mixedDeriv α β (p.sharp (c i) (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
        C * ((1 + ‖x - z i‖ ^ 2) ^ n)⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le 0 α β hp hc
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_sharp_le n α β hp hc
  refine ⟨2 ^ (n - 1) * (C₀ + C₁), by positivity, fun i x ξ ↦ ?_⟩
  have h₀ := hC₀ i x ξ
  rw [mul_zero, pow_zero, one_mul] at h₀
  exact (le_mul_one_add_norm_sq_pow_inv (norm_nonneg _) h₀ (hC₁ i x ξ)).trans_eq (by ring)

end Sharp

/-! ### The composition of two uniform symbols -/

section Composition

variable [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]

omit [CompleteSpace V] in
/-- The quantization of `p # (χ(· - j) a)` is `Op(p)` applied to `χ(· - j) Op(a) u`. -/
private theorem quantizeSchwartzValue_sharp_latticeBump_comp (p : Symbol n W U m')
    {a : Symbol n V W m} (ha : a.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) (j : Fin n → ℤ) :
    quantizeSchwartzValue (p.sharp _
      ((isBallFamily_latticeBump_comp ha).hasCompactSpatialSupport j)).coefficient u x =
      quantizeSchwartzValue p.coefficient (SchwartzMap.smulLeftCLM W
        (fun y ↦ latticeBump n (y - latticePoint j)) (quantizeUniformCLM a ha u)) x := by
  rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  congr 1
  ext y
  rw [HasCompactSupport.toSchwartzMap_toFun, quantizeSchwartzValue_ofSpatial_smul_id_comp,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_latticeBump_sub j), Complex.coe_smul,
    quantizeUniformCLM_apply]

/-- **Composition of uniform symbols.** If `p` and `a` are symbols of orders `m'` and `m` whose
estimates hold uniformly in the position, then `Op(p) ∘ Op(a)` is the quantization of a symbol of
order `m' + m` whose estimates hold uniformly in the position. No compact spatial support is
assumed for either symbol. -/
theorem IsUniform.exists_quantizeUniformCLM_comp {p : Symbol n W U m'} (hp : p.IsUniform)
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ (c : Symbol n V U (m' + m)) (hc : c.IsUniform),
      quantizeUniformCLM p hp ∘L quantizeUniformCLM a ha = quantizeUniformCLM c hc := by
  have hfam := isBallFamily_latticeBump_comp ha
  set F : (Fin n → ℤ) → Symbol n V U (m' + (0 + m)) := fun j ↦ p.sharp _
    (hfam.hasCompactSpatialSupport j)
  set w : (Fin n → ℤ) → CoordinateSpace n → ℝ := fun j x ↦
    ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹
  obtain ⟨b, hb, hbsum⟩ := exists_isUniform_hasSum_coefficient F w (fun _ _ ↦ by positivity)
    (fun x ↦ ⟨fun j ↦ 4 ^ n * w j x,
      (summable_one_add_norm_sub_latticePoint_sq_pow_inv x).mul_left _,
      fun j _ hy ↦ one_add_norm_sub_latticePoint_sq_pow_inv_le_of_dist_le_one (mem_ball.1 hy).le j⟩)
    tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le
    (hfam.exists_norm_mixedDeriv_sharp_le hp)
  have hord : m' + (0 + m) = m' + m := by ring
  refine ⟨Symbol.inclusion hord.le b, hb.inclusion hord.le, ?_⟩
  ext u x
  rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply, quantizeUniformCLM_apply,
    coefficient_inclusion]
  -- Both sides are the sum of the series `∑ⱼ Op(p # χⱼ a) u (x)`.
  obtain ⟨C, -, hC⟩ := hfam.exists_norm_mixedDeriv_sharp_le hp [] []
  simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero] at hC
  refine ((hasSum_quantizeSchwartzValue_of_hasSum_coefficient hbsum
    (summable_one_add_norm_sub_latticePoint_sq_pow_inv x) (hC · x) u).unique ?_).symm
  -- The lattice partition of unity converges in Schwartz space, on which `Op(p)` is continuous.
  simp only [F, quantizeSchwartzValue_sharp_latticeBump_comp p ha u x]
  have h := (SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub (F := W)
    (quantizeUniformCLM a ha u)).mapL ((BoundedContinuousFunction.evalCLM ℂ x) ∘L
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (CoordinateSpace n) U) ∘L
        quantizeUniformCLM p hp)
  simp only [ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    SchwartzMap.toBoundedContinuousFunctionCLM_apply, quantizeUniformCLM_apply] at h
  exact h

end Composition

end Symbol

end TauCeti
