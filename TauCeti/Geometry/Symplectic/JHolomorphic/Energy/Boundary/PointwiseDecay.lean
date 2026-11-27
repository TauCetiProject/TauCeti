/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Boundary.Decay
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.BoundaryPuncture
import TauCeti.Analysis.Calculus.FDeriv.Puncture
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Pointwise power bounds at a boundary puncture

Let `x₀` be a point of the real axis and let `u` solve `∂ₜu = J(u) ∂ₛu` on the punctured closed
half-disc `{0 ≤ im z} ∩ B_R(x₀) \ {x₀}`, with derivatives taken within the closed upper
half-plane, mapping the real axis into a subspace `L`. Suppose that `u` has finite energy and image
in a compact set `K`, near which `J` is `C²` with `J² = -1` and `J(p)` maps `L` into `Lᗮ` for
`p ∈ L`; that a constant symplectic form `ω`, compatible with the inner product through a fixed
structure `J₀`, vanishes on `L` and tames `J` along `u` with constant `c > 0`; and that
`‖J(u)‖ ≤ M`. Then the full derivative of `u` within the half-plane has a power bound

`‖du(z)‖ ≤ C |z - x₀| ^ (c / (1 + M)² - 1)`

near the puncture, with an exponent strictly greater than `-1`
(`TauCeti.SymplecticForm.exists_pos_norm_fderivWithin_le_rpow`). Consequently the speed of `u`
along every radius into the half-disc is integrable up to the puncture
(`TauCeti.SymplecticForm.exists_pos_integrableOn_deriv_radial_inter`), which supplies the
finite radial length needed to extend `u` continuously over the puncture.

The bound combines the power decay `E(r) ≤ A r^(2c / (1 + M)²)` of the energy of the half-disc
of radius `r` (`TauCeti.SymplecticForm.integral_norm_fderivWithin_one_sq_inter_ball_le_rpow`)
with the small-energy mean-value bound `d² ‖∂ₛu(z)‖² ≤ (512 / π) E(2d)` at a point `z` at distance
`d` from the puncture (`TauCeti.exists_pos_sq_norm_fderivWithin_one_le_energy`), and the
Cauchy--Riemann equation, which bounds `du` by `(1 + M) ‖∂ₛu‖`. These are the boundary
counterparts of `TauCeti.SymplecticForm.exists_pos_norm_fderiv_le_rpow` and
`TauCeti.SymplecticForm.exists_pos_integrableOn_deriv_radial` at an interior puncture, and share
with them the real-variable step `Real.exists_pos_le_sqrt_mul_rpow_sub_one_of_le_mul_rpow` and
the radial-length step `TauCeti.integrableOn_deriv_radial_of_norm_fderivWithin_le_rpow`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities, including boundary punctures with totally real boundary
  conditions).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {L : Submodule ℝ V} {x₀ : ℂ} {R c M : ℝ} {W K : Set V}

/-- Bound the energy of all small half-discs about a boundary puncture by a fixed power, using one
reference radius. -/
private theorem exists_energy_power_bound_inter_ball
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hx₀ : x₀.im = 0) (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ A ≥ 0, ∀ r ∈ Ioo 0 (R / 2),
      (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) ≤
        A * r ^ (2 * c / (1 + M) ^ 2) := by
  let b := R / 2
  let α := 2 * c / (1 + M) ^ 2
  let E := ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ b, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2
  refine ⟨E / b ^ α, by dsimp [E, b]; positivity, fun r hr ↦ ?_⟩
  have h := ω.integral_norm_fderivWithin_one_sq_inter_ball_le_rpow hg hx₀ hu hCR htame hJ hLω
    huL henergy (b := b) hr.1 hr.2.le (by dsimp [b]; linarith)
  rw [Real.div_rpow hr.1.le (half_pos hR).le] at h
  simpa only [b, α, E, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

omit [FiniteDimensional ℝ V] in
/-- The point `x₀ + R / 2` lies on the real edge of the punctured half-disc, so a bound `M` on the
norm of the target structure there is nonnegative. -/
private theorem nonneg_of_forall_norm_le (hx₀ : x₀.im = 0) (hR : 0 < R)
    (hbound : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M) : 0 ≤ M :=
  (norm_nonneg _).trans (hbound (x₀ + ((R / 2 : ℝ) : ℂ))
    ⟨by simp [hx₀], by simpa [dist_eq_norm, abs_of_pos hR] using half_lt_self hR,
      by simpa using (half_pos hR).ne'⟩)

/-- The power bound for the derivative in the real direction `∂ₛu`, from the power decay of the
energy and the small-energy mean-value inequality. -/
private theorem exists_pos_norm_fderivWithin_one_le_rpow
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫ = 0)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ ε > 0, ε < R ∧ ∃ B, ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ ε \ {x₀}),
      ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ≤ √B * ‖z - x₀‖ ^ (c / (1 + M) ^ 2 - 1) := by
  have hM : 0 ≤ M := nonneg_of_forall_norm_le hx₀ hR hbound
  -- Normalize the energy power bound, then choose a radius below the mean-value threshold.
  let β := c / (1 + M) ^ 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hα : 2 * c / (1 + M) ^ 2 = 2 * β := by dsimp [β]; ring
  obtain ⟨A, _, hpower⟩ := exists_energy_power_bound_inter_ball hg hx₀ hR
    (hu.of_le (by norm_num)) hCR htame hbound hLω huL henergy
  obtain ⟨δ, hδ, hmean⟩ := exists_pos_sq_norm_fderivWithin_one_le_energy hW hJ hK hKW hJsq
    L.isClosed_of_finiteDimensional hJL hx₀ hu hCR huL huK henergy
  obtain ⟨ε, hε, hεR, B, hB⟩ := Real.exists_pos_le_sqrt_mul_rpow_sub_one_of_le_mul_rpow
    (E := fun r ↦ ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
    (K := 512 / π) hR (by positivity) hβ hδ (by simpa only [hα] using hpower)
  refine ⟨ε, hε, by linarith, B, fun z hz ↦ ?_⟩
  have hd : 0 < ‖z - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.2.2)
  have hdε : ‖z - x₀‖ < ε := by simpa only [mem_ball, dist_eq_norm] using hz.2.1
  -- The mean-value estimate on a half-disc avoiding the puncture converts energy decay into
  -- derivative decay.
  obtain ⟨hsmallE, hreal⟩ := hB _ ⟨hd, hdε⟩
  exact hreal _ (hmean z
    ⟨hz.1, by simpa only [mem_ball, dist_eq_norm] using hdε.trans hεR, hz.2.2⟩ hsmallE)

/-- **Pointwise decay of the derivative at a boundary puncture.** The derivative within the closed
upper half-plane of a finite-energy pseudoholomorphic half-disc with Lagrangian boundary values,
as in the module docstring, has a power bound `‖du(z)‖ ≤ C |z - x₀| ^ (c / (1 + M)² - 1)` near
the puncture, with exponent strictly greater than `-1`. Both the radius and the bound are uniform
in the direction of approach. The value of the curve at the puncture is unrestricted. -/
theorem exists_pos_norm_fderivWithin_le_rpow
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫ = 0)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ ε > 0, ε < R ∧ ∃ C > 0, ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ ε \ {x₀}),
      ‖fderivWithin ℝ u {z | 0 ≤ z.im} z‖ ≤ C * ‖z - x₀‖ ^ (c / (1 + M) ^ 2 - 1) := by
  have hM : 0 ≤ M := nonneg_of_forall_norm_le hx₀ hR hbound
  obtain ⟨ε, hε, hεR, B, hB⟩ := exists_pos_norm_fderivWithin_one_le_rpow hg hc hR hW hJ hK hKW
    hJsq hJL hLω hx₀ hu hCR huL huK htame hbound henergy
  refine ⟨ε, hε, hεR, (1 + M) * (√B + 1), by positivity, fun z hz ↦ ?_⟩
  have hzR : z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}) :=
    ⟨hz.1, ball_subset_ball hεR.le hz.2.1, hz.2.2⟩
  have hd : 0 < ‖z - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.2.2)
  -- The Cauchy--Riemann equation controls the full differential by its real-direction part.
  calc
    _ ≤ (1 + M) * (√B * ‖z - x₀‖ ^ (c / (1 + M) ^ 2 - 1)) :=
      (fderivWithin ℝ u {z | 0 ≤ z.im} z).norm_le_of_apply_I_eq (hCR z hzR) (hbound z hzR) (hB z hz)
    _ ≤ (1 + M) * (√B + 1) * ‖z - x₀‖ ^ (c / (1 + M) ^ 2 - 1) := by
      nlinarith [Real.rpow_pos_of_pos hd (c / (1 + M) ^ 2 - 1)]

/-- **Finite radial length at a boundary puncture.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_pos_norm_fderivWithin_le_rpow`, a finite-energy pseudoholomorphic
half-disc with Lagrangian boundary values has integrable velocity along every radius into the
closed upper half-plane sufficiently close to the puncture, including the two radii along the real
axis. The radius is uniform over all such unit directions; no continuous extension at the missing
endpoint is assumed. -/
theorem exists_pos_integrableOn_deriv_radial_inter
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hJL : ∀ p ∈ (L : Set V) ∩ W, ∀ v ∈ L, ∀ w ∈ L, ⟪v, J p w⟫ = 0)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 3 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (huK : MapsTo u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) K)
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R)) :
    ∃ ε > 0, ε < R ∧ ∀ v : ℂ, 0 ≤ v.im → ‖v‖ = 1 →
      IntegrableOn (deriv (fun t : ℝ ↦ u (x₀ + t • v))) (Ioo 0 ε) := by
  obtain ⟨ε, hε, hεR, C, _, hC⟩ := ω.exists_pos_norm_fderivWithin_le_rpow hg hc hR hW hJ hK hKW
    hJsq hJL hLω hx₀ hu hCR huL huK htame hbound henergy
  have hM : 0 ≤ M := nonneg_of_forall_norm_le hx₀ hR hbound
  refine ⟨ε, hε, hεR, fun v hvim hv ↦ integrableOn_deriv_radial_of_norm_fderivWithin_le_rpow
    (C := C) (β := c / (1 + M) ^ 2) (by positivity) hv (fun t ht ↦ ?_) (fun z hz ↦ ?_) hC⟩
  · -- The open radius `t ↦ x₀ + t • v`, `t > 0`, stays in the closed upper half-plane.
    simpa [hx₀] using mul_nonneg ht.1.le hvim
  · have hzR : z ∈ ball x₀ R \ {x₀} := ⟨ball_subset_ball hεR.le hz.2.1, hz.2.2⟩
    exact (differentiableWithinAt_inter ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hzR)).1
      ((hu.differentiableOn (by norm_num)) z ⟨hz.1, hzR⟩)

end TauCeti.SymplecticForm
