/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.InnerProductSpace.Harmonic.BoundaryDecay
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.LevelSet
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Campanato decay of the gradient at a flat boundary

Let `H = normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, of dimension `n`,
let `x₀` be a point of its boundary hyperplane `{a} × E`, and write `B_t⁺ = ball x₀ t ∩ H` for the
half-balls centred at `x₀`. Let `u ∈ H¹(U)` on an open set `U ⊇ ball x₀ R` vanish off `H`, so that
`u` has zero boundary values on the flat part of the boundary of `U ∩ H`, and let `u` solve

`-Δu = -div G` in `U ∩ H`, that is `∫ ⟪∇u, ∇φ⟫ = ∫ ⟪G, ∇φ⟫` for every test function `φ` on `U ∩ H`,

with `G` `α`-Hölder with constant `K` on `B_R⁺`, `0 < α < 1`. This file proves the Campanato
decay of `∇u` at `x₀`
(`TauCeti.PDE.exists_setIntegral_ball_inter_normalHalfSpace_norm_gradient_sub_sq_le`): writing

`ψ(t) = ∫_{B_t⁺} ‖∇u - m_t‖²`, where `m_t = ((∇u)_{B_t⁺}.fst, 0)`,

for the square distance from `∇u` to its best constant normal to the hyperplane, there is a
constant `C`, depending only on `n` and `α`, such that for `0 < t ≤ R`

`ψ(t) ≤ C ((t / R)^(n + 2α) ψ(R) + K² t^(n + 2α))`.

This is the boundary half of Campanato's approach to the Schauder estimate for `-Δu = -div G`; the
interior half is `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`. Only constants
normal to the hyperplane are compared with `∇u`: its tangential part vanishes on the flat
boundary.

## The argument

Fix `0 < r ≤ R` and let `w` be the harmonic replacement of `u` on `B_r⁺`, so that
`u - w ∈ H¹₀(B_r⁺)` and `⟪∇w, ∇v⟫ = 0` for every `v ∈ H¹₀(B_r⁺)`
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_inner_gradient_eq_zero`). Since constants have
zero divergence, `u` solves `-Δu = -div (G - c)` against `H¹₀(B_r⁺)` for `c = G y`, `y ∈ B_r⁺`
(`TauCeti.PDE.inner_gradient_restrictL_eq_inner_toLp`), so testing with `u - w` gives

`‖∇(u - w)‖²_{L²(B_r⁺)} ≤ ‖G - c‖²_{L²(B_r⁺)} ≤ 4^α ω K² r^(n + 2α)`,

where `ω` is the volume of the unit ball. On `ball x₀ r`, the function equal to `u` minus the zero
extension of `u - w` vanishes off `H` and is weakly harmonic on `B_r⁺`, where it agrees with `w`; so
by the Schwarz reflection principle its gradient agrees on `B_r⁺` with a harmonic field `V` odd
under the reflection in the hyperplane
(`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ball_ae_eq`). The half-ball decay of such fields
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le_add`)
then gives, for `0 < t ≤ r ≤ R`,

`ψ(t) ≤ 4 D (t / r)^(n + 2) ψ(r) + (4 D + 2) 4^α ω K² r^(n + 2α)`,

with `D = 2^(3n + 8) (n + 1)²`. Since `ψ` is nondecreasing and `n + 2α < n + 2`, the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` turns this into the decay estimate.

## Main declarations

* `TauCeti.PDE.exists_setIntegral_ball_inter_normalHalfSpace_norm_gradient_sub_sq_le`: Campanato
  decay of `∇u` at a point of a flat boundary on which `u` vanishes, for `-Δu = -div G` with
  `α`-Hölder `G`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.4 (boundary regularity by Campanato's
  method).
* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Reflection of a harmonic replacement on a half-ball.** Let `x₀` lie on the hyperplane
`{a} × E`, let `u ∈ H¹(U)` vanish off `H` with `ball x₀ r ⊆ U`, and let `w` be weakly harmonic on
`Ω = B_r⁺` with the boundary values of `u`. Then there is a harmonic field `V` on `ball x₀ r`,
odd under the reflection in the hyperplane, whose square distance from `∇u` on `B_r⁺` is the
energy of `u - w`. -/
private theorem exists_harmonicOnNhd_ball_setIntegral_norm_gradient_sub_sq_eq {a : ℝ}
    {U Ω : Opens (WithLp 2 (ℝ × E))} {u : W1p volume U 2} {x₀ : WithLp 2 (ℝ × E)} {r : ℝ}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → W1p.value u x = 0)
    (hx₀ : x₀.fst = a) (hball : ball x₀ r ⊆ U)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))) = ball x₀ r ∩ normalHalfSpace (E := E) a)
    (hΩU : Ω ≤ U) {w : W1p volume Ω 2}
    (huw : W1p.restrictL hΩU u - w ∈ w1p0Submodule volume Ω 2)
    (hw : ∀ v ∈ w1p0Submodule volume Ω 2, ⟪W1p.gradient w, W1p.gradient v⟫_ℝ = 0) :
    ∃ V : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E), HarmonicOnNhd V (ball x₀ r) ∧
      (∀ x ∈ ball x₀ r, V (normalReflection E a x) = -normalLinearReflection E (V x)) ∧
      MemLp V 2 (volume.restrict (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _))) ∧
      ∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _), ‖W1p.gradient u x - V x‖ ^ 2 =
        ‖W1p.gradient (W1p.restrictL hΩU u - w)‖ ^ 2 := by
  obtain ⟨B, hB⟩ : ∃ B : Opens (WithLp 2 (ℝ × E)), (B : Set (WithLp 2 (ℝ × E))) = ball x₀ r :=
    ⟨⟨ball x₀ r, isOpen_ball⟩, rfl⟩
  have hBs : (B : Set (WithLp 2 (ℝ × E))) ⊆ U := hB ▸ hball
  have hΩBs : (Ω : Set (WithLp 2 (ℝ × E))) ⊆ B := by
    rw [hΩ, hB]
    exact inter_subset_left
  have hBU : B ≤ U := SetLike.coe_subset_coe.1 hBs
  have hΩB : Ω ≤ B := SetLike.coe_subset_coe.1 hΩBs
  have hΩeq : B ⊓ normalHalfSpace a = Ω := SetLike.coe_injective (by rw [Opens.coe_inf, hB, hΩ])
  have hΩm : MeasurableSet (Ω : Set (WithLp 2 (ℝ × E))) := Ω.isOpen.measurableSet
  -- `W = u - (u - w)₀` on `B` vanishes off `H` and restricts to `w` on `Ω`.
  obtain ⟨W, hW0, hWres⟩ := W1p.exists_restrictL_eq_of_sub_mem_w1p0Submodule hΩB hBU
    (S := normalHalfSpace (E := E) a) (hΩ ▸ inter_subset_right)
    (ae_restrict_of_ae_restrict_of_subset hBs hu0) huw
  have hG0 : ∀ᵐ x ∂volume.restrict B, x ∉ normalHalfSpace (E := E) a →
      W1p.gradient W x = 0 := by
    filter_upwards [hW0, W1p.gradient_ae_eq_zero_on_level_set (by norm_num) W 0] with x h1 h2 hx
    exact h2 (h1 hx)
  -- `w`, hence `W`, is weakly harmonic on `Ω`.
  have hwh : WeaklyHarmonicOn volume Ω (W1p.value w) :=
    W1p.weaklyHarmonicOn_value_of_forall_inner_gradient_eq_zero fun φ =>
      hw _ (W1p.ofTestFunctionₗ_mem_w1p0Submodule φ)
  have hWw : (W1p.value w : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict Ω] W1p.value W := by
    have h := W1p.value_restrictL_ae hΩB W
    rw [hWres] at h
    exact h
  -- By reflection, `∇W` agrees on `B_r⁺` with a harmonic field `V` odd under the reflection.
  obtain ⟨V, hV, hodd, hVW⟩ := WeaklyHarmonicOn.exists_harmonicOnNhd_ball_ae_eq (U := B)
    (hΩeq ▸ hwh.congr_ae hWw) (by rw [hB]; exact mapsTo_normalReflection_ball hx₀ r)
    (W1p.hasWeakFDerivOn W) hG0 hW0 hB.symm.subset
  refine ⟨V, hV, hodd, ((Lp.memLp (W1p.gradient W)).mono_measure
    (Measure.restrict_mono (hB.symm ▸ inter_subset_left) le_rfl)).ae_eq hVW.symm, ?_⟩
  -- On `B_r⁺`, `∇u - V = ∇u - ∇w`.
  rw [← hΩ] at hVW
  rw [← hΩ, ← W1p.setIntegral_norm_gradient_sub_sq_eq hΩU u w]
  refine integral_congr_ae ?_
  have hgW := W1p.gradient_restrictL_ae hΩB W
  rw [hWres] at hgW
  filter_upwards [hVW, hgW] with x h1 h2
  rw [h1, ← h2]

/-- **The `L²` oscillation of a Hölder field on a half-ball.** Let `x₀` lie on the hyperplane
`{a} × E` and let `G` be `α`-Hölder with constant `K` on `Ω = B_r⁺`, `r > 0`. Then for some point
`y`, `G - G y` is square integrable on `Ω` and `‖G - G y‖²_{L²(Ω)} ≤ 2^(2α) ω K² r^(n + 2α)`, where
`ω` is the volume of the unit ball and `n` is the dimension of `ℝ × E`. -/
private theorem exists_memLp_sub_norm_toLp_sq_le {a : ℝ}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {K α : ℝ≥0} {x₀ : WithLp 2 (ℝ × E)} {r : ℝ}
    (hα : 0 < α) (hG : HolderOnWith K α G (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)))
    (hx₀ : x₀.fst = a) (hr : 0 < r) {Ω : Opens (WithLp 2 (ℝ × E))}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))) = ball x₀ r ∩ normalHalfSpace (E := E) a) :
    ∃ y : WithLp 2 (ℝ × E), ∃ hGc : MemLp (fun x => G x - G y) 2 (volume.restrict Ω),
      ‖hGc.toLp‖ ^ 2 ≤
        2 ^ (2 * (α : ℝ)) * volume.real (ball (0 : WithLp 2 (ℝ × E)) 1) * (K : ℝ) ^ 2 *
          r ^ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) + 2 * α) := by
  -- On `Ω`, `G` stays within `K (2 r)^α` of its value at a point `y ∈ Ω`.
  set y : WithLp 2 (ℝ × E) := x₀ + WithLp.toLp 2 (r / 2, 0)
  have hyB : y ∈ ball x₀ r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs, norm_zero]
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (by linarith)]
    linarith
  have hyH : y ∈ (normalHalfSpace (E := E) a : Set _) := by
    rw [SetLike.mem_coe, mem_normalHalfSpace]
    simp [y, ← hx₀]
    linarith
  have hGbd : ∀ x ∈ (Ω : Set (WithLp 2 (ℝ × E))), ‖G x - G y‖ ≤ K * (2 * r) ^ (α : ℝ) :=
    fun x hx => by
      rw [hΩ] at hx
      rw [← dist_eq_norm]
      refine (hG.dist_le hx ⟨hyB, hyH⟩).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg ?_ α.2) K.2)
      linarith [dist_triangle_right x y x₀, mem_ball.1 hx.1, mem_ball.1 hyB]
  have hΩm : MeasurableSet (Ω : Set (WithLp 2 (ℝ × E))) := Ω.isOpen.measurableSet
  have hΩfin : volume (Ω : Set (WithLp 2 (ℝ × E))) ≠ ⊤ := by
    rw [hΩ]
    exact ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hGc : MemLp (fun x => G x - G y) 2 (volume.restrict Ω) := by
    have : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
      isFiniteMeasure_restrict.2 hΩfin
    exact MemLp.of_bound ((((hG.continuousOn hα).mono hΩ.subset).aestronglyMeasurable hΩm).sub
      aestronglyMeasurable_const) _ ((ae_restrict_iff' hΩm).2 (ae_of_all _ hGbd))
  refine ⟨y, hGc, ?_⟩
  have hGn := hGc.norm_toLp_le_measureReal_rpow_mul (by norm_num) hΩfin
    ((ae_restrict_iff' hΩm).2 (ae_of_all _ hGbd))
  rw [ENNReal.toReal_ofNat, ← one_div, ← Real.sqrt_eq_rpow] at hGn
  have hvol : volume.real (Ω : Set (WithLp 2 (ℝ × E))) ≤
      r ^ finrank ℝ (WithLp 2 (ℝ × E)) * volume.real (ball (0 : WithLp 2 (ℝ × E)) 1) := by
    rw [hΩ, ← (volume : Measure (WithLp 2 (ℝ × E))).addHaar_real_ball_of_pos x₀ hr]
    exact measureReal_mono inter_subset_left measure_ball_lt_top.ne
  have h2 : ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 =
      2 ^ (2 * (α : ℝ)) * (K : ℝ) ^ 2 * r ^ (2 * (α : ℝ)) := by
    have h : ((2 * r) ^ (α : ℝ)) ^ 2 = 2 ^ (2 * (α : ℝ)) * r ^ (2 * (α : ℝ)) := by
      rw [← Real.rpow_natCast ((2 * r) ^ (α : ℝ)) 2, ← Real.rpow_mul (by linarith),
        Real.mul_rpow (by norm_num) hr.le]
      push_cast
      ring_nf
    rw [mul_pow, h]
    ring
  have h3 : r ^ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) + 2 * α) =
      r ^ finrank ℝ (WithLp 2 (ℝ × E)) * r ^ (2 * (α : ℝ)) := by
    rw [Real.rpow_add hr, Real.rpow_natCast]
  refine (pow_le_pow_left₀ (norm_nonneg _) hGn 2).trans ?_
  rw [mul_pow, Real.sq_sqrt measureReal_nonneg, h2, h3]
  calc volume.real (Ω : Set (WithLp 2 (ℝ × E))) *
        (2 ^ (2 * (α : ℝ)) * (K : ℝ) ^ 2 * r ^ (2 * (α : ℝ)))
      ≤ r ^ finrank ℝ (WithLp 2 (ℝ × E)) * volume.real (ball (0 : WithLp 2 (ℝ × E)) 1) *
        (2 ^ (2 * (α : ℝ)) * (K : ℝ) ^ 2 * r ^ (2 * (α : ℝ))) := by gcongr
    _ = _ := by ring

/-- **One comparison step at a flat boundary.** Let `x₀` lie on the hyperplane `{a} × E`, let
`u ∈ H¹(U)` vanish off `H` and solve `-Δu = -div G` weakly on `U ∩ H`, with `G` `α`-Hölder with
constant `K` on `B_r⁺ = ball x₀ r ∩ H ⊆ U`. Then for `0 < t ≤ r` the square distance
`ψ(s) = ∫_{B_s⁺} ‖∇u - ((∇u)_{B_s⁺}.fst, 0)‖²` satisfies

`ψ(t) ≤ 4 D (t / r)^(n + 2) ψ(r) + (4 D + 2) 2^(2α) ω K² r^(n + 2α)`,

where `D = 2^(3n + 8) (n + 1)²`, `ω` is the volume of the unit ball and `n` is the dimension of
`ℝ × E`. -/
private theorem setIntegral_ball_inter_normalHalfSpace_norm_gradient_sub_sq_le_add {a : ℝ}
    {U : Opens (WithLp 2 (ℝ × E))} {u : W1p volume U 2}
    {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {K α : ℝ≥0} {x₀ : WithLp 2 (ℝ × E)} {r t : ℝ}
    (hα : 0 < α)
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → W1p.value u x = 0)
    (hu : ∀ φ : 𝓓(U ⊓ normalHalfSpace a, ℝ),
      ∫ x in (U ⊓ normalHalfSpace a : Opens (WithLp 2 (ℝ × E))),
        ⟪W1p.gradient u x, ∇ (φ : WithLp 2 (ℝ × E) → ℝ) x⟫_ℝ =
        ∫ x in (U ⊓ normalHalfSpace a : Opens (WithLp 2 (ℝ × E))),
        ⟪G x, ∇ (φ : WithLp 2 (ℝ × E) → ℝ) x⟫_ℝ)
    (hG : HolderOnWith K α G (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _)))
    (hx₀ : x₀.fst = a) (hball : ball x₀ r ⊆ U) (ht : 0 < t) (htr : t ≤ r) :
    ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _),
        ‖W1p.gradient u x - WithLp.toLp 2
          ((⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), W1p.gradient u y).fst,
            0)‖ ^ 2 ≤
      4 * (2 ^ (3 * finrank ℝ (WithLp 2 (ℝ × E)) + 8) * (finrank ℝ (WithLp 2 (ℝ × E)) + 1) ^ 2) *
          (t / r) ^ (finrank ℝ (WithLp 2 (ℝ × E)) + 2) *
          (∫ x in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _),
            ‖W1p.gradient u x - WithLp.toLp 2
              ((⨍ y in ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _), W1p.gradient u y).fst,
                0)‖ ^ 2) +
        (4 * (2 ^ (3 * finrank ℝ (WithLp 2 (ℝ × E)) + 8) *
            (finrank ℝ (WithLp 2 (ℝ × E)) + 1) ^ 2) + 2) *
          (2 ^ (2 * (α : ℝ)) * volume.real (ball (0 : WithLp 2 (ℝ × E)) 1) * (K : ℝ) ^ 2 *
            r ^ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) + 2 * α)) := by
  have hr : 0 < r := ht.trans_le htr
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Opens (WithLp 2 (ℝ × E)),
      (Ω : Set (WithLp 2 (ℝ × E))) = ball x₀ r ∩ normalHalfSpace (E := E) a :=
    ⟨⟨_, isOpen_ball.inter (normalHalfSpace a).isOpen⟩, rfl⟩
  have hΩV : Ω ≤ U ⊓ normalHalfSpace a := SetLike.coe_subset_coe.1 (by
    rw [hΩ, Opens.coe_inf]
    exact inter_subset_inter_left _ hball)
  -- The harmonic replacement `w` of `u` on `Ω` and its energy estimate.
  have hUH : U ⊓ normalHalfSpace a ≤ U := inf_le_left
  have hu₁ : ∀ φ : 𝓓(U ⊓ normalHalfSpace a, ℝ),
      ∫ x in (U ⊓ normalHalfSpace a : Opens (WithLp 2 (ℝ × E))),
        ⟪W1p.gradient (W1p.restrictL hUH u) x, ∇ (φ : WithLp 2 (ℝ × E) → ℝ) x⟫_ℝ =
        ∫ x in (U ⊓ normalHalfSpace a : Opens (WithLp 2 (ℝ × E))),
        ⟪G x, ∇ (φ : WithLp 2 (ℝ × E) → ℝ) x⟫_ℝ := fun φ => by
    rw [← hu φ]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_restrictL_ae hUH u] with x hx
    rw [hx]
  have hΩb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E))) := by
    rw [hΩ]
    exact isBounded_ball.subset inter_subset_left
  -- On `Ω`, `G` is `L²`-close to a constant.
  obtain ⟨y, hGc, hGn⟩ := exists_memLp_sub_norm_toLp_sq_le hα hG hx₀ hr hΩ
  obtain ⟨w, huw, hw, hE⟩ :=
    exists_sub_mem_w1p0Submodule_forall_inner_gradient_eq_zero hΩb (W1p.restrictL (hΩV.trans hUH) u)
  -- Constants have zero divergence, so `u` solves `-Δu = -div (G - G y)` against `H¹₀(Ω)`.
  have hE' := hE hGc.toLp fun v hv => by
    have h := inner_gradient_restrictL_eq_inner_toLp hΩV hu₁ hGc hv
    rwa [W1p.restrictL_restrictL] at h
  obtain ⟨V, hV, hodd, hVm, herr⟩ :=
    exists_harmonicOnNhd_ball_setIntegral_norm_gradient_sub_sq_eq hu0 hx₀ hball hΩ
      (hΩV.trans hUH) huw hw
  have hf : MemLp (W1p.gradient u : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)) 2
      (volume.restrict (ball x₀ r ∩ (normalHalfSpace (E := E) a : Set _))) :=
    (Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono (inter_subset_left.trans hball) le_rfl)
  have hcmp := hV.setIntegral_ball_inter_normalHalfSpace_norm_sub_sq_le_add hx₀ hodd hf hVm ht.le
    htr
  rw [herr] at hcmp
  -- The energy of `u - w` is at most `2^(2α) ω K² r^(n + 2α)`.
  have hdata : ‖W1p.gradient (W1p.restrictL (hΩV.trans hUH) u - w)‖ ^ 2 ≤
      2 ^ (2 * (α : ℝ)) * volume.real (ball (0 : WithLp 2 (ℝ × E)) 1) * (K : ℝ) ^ 2 *
        r ^ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) + 2 * α) :=
    (pow_le_pow_left₀ (norm_nonneg _) hE' 2).trans hGn
  refine hcmp.trans ?_
  gcongr

/-- **Campanato decay of the gradient at a flat boundary** for `-Δu = -div G`. Let `0 < α < 1`.
There is a constant `C`, depending only on `α` and the dimension `n` of `ℝ × E`, such that the
following holds. Let `H = {x | a < x.fst}`, let `x₀` lie on the hyperplane `{a} × E`, and write
`B_s⁺ = ball x₀ s ∩ H`. Let `u ∈ H¹(U)` on an open set `U ⊇ ball x₀ R` vanish almost everywhere
off `H`, so that `u` has zero boundary values on the flat part of the boundary of `U ∩ H`, and let
`u` solve `-Δu = -div G` weakly on `U ∩ H`: `∫ ⟪∇u, ∇φ⟫ = ∫ ⟪G, ∇φ⟫` for every test function `φ`
on `U ∩ H`. If `G` is `α`-Hölder with constant `K` on `B_R⁺`, then for `0 < t ≤ R` the square
distance `ψ(s) = ∫_{B_s⁺} ‖∇u - ((∇u)_{B_s⁺}.fst, 0)‖²` from `∇u` to its best constant normal to
the hyperplane satisfies

`ψ(t) ≤ C ((t / R)^(n + 2α) ψ(R) + K² t^(n + 2α))`.

Only normal constants are compared with `∇u`, since its tangential part vanishes on the flat
boundary. Dividing by `|B_t⁺|`, the mean square oscillation of `∇u` on `B_t⁺` is `O(t^(2α))`, the
boundary counterpart of the interior estimate behind
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`. -/
theorem exists_setIntegral_ball_inter_normalHalfSpace_norm_gradient_sub_sq_le {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} {U : Opens (WithLp 2 (ℝ × E))} {u : W1p volume U 2}
      {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {K : ℝ≥0} {x₀ : WithLp 2 (ℝ × E)} {R t : ℝ},
      (∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ normalHalfSpace a, ℝ),
        ∫ x in (U ⊓ normalHalfSpace a : Opens (WithLp 2 (ℝ × E))),
        ⟪W1p.gradient u x, ∇ (φ : WithLp 2 (ℝ × E) → ℝ) x⟫_ℝ =
          ∫ x in (U ⊓ normalHalfSpace a : Opens (WithLp 2 (ℝ × E))),
        ⟪G x, ∇ (φ : WithLp 2 (ℝ × E) → ℝ) x⟫_ℝ) →
      HolderOnWith K α G (ball x₀ R ∩ (normalHalfSpace (E := E) a : Set _)) →
      x₀.fst = a → ball x₀ R ⊆ U → 0 < t → t ≤ R →
        ∫ x in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _),
            ‖W1p.gradient u x - WithLp.toLp 2
              ((⨍ y in ball x₀ t ∩ (normalHalfSpace (E := E) a : Set _), W1p.gradient u y).fst,
                0)‖ ^ 2 ≤
          C * ((t / R) ^ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) + 2 * α) *
              (∫ x in ball x₀ R ∩ (normalHalfSpace (E := E) a : Set _),
                ‖W1p.gradient u x - WithLp.toLp 2
                  ((⨍ y in ball x₀ R ∩ (normalHalfSpace (E := E) a : Set _),
                    W1p.gradient u y).fst, 0)‖ ^ 2) +
            (K : ℝ) ^ 2 * t ^ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) + 2 * α)) := by
  set n := finrank ℝ (WithLp 2 (ℝ × E))
  set D : ℝ := 2 ^ (3 * n + 8) * (n + 1) ^ 2
  set M : ℝ := (4 * D + 2) * (2 ^ (2 * (α : ℝ)) * volume.real (ball (0 : WithLp 2 (ℝ × E)) 1))
  have hα1' : (α : ℝ) < 1 := hα1
  obtain ⟨ε₀, C₀, hε₀, hC₀, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add
    (A := 4 * D) (α := (n : ℝ) + 2) (β := (n : ℝ) + 2 * α) (γ := (n : ℝ) + 2 * α) (by positivity)
    (by linarith) (by linarith)
  refine ⟨C₀ * max 1 M, mul_nonneg hC₀.le (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro a U u G K x₀ R t hu0 hu hG hx₀ hball ht htR
  set ψ : ℝ → ℝ := fun s => ∫ x in ball x₀ s ∩ (normalHalfSpace (E := E) a : Set _),
    ‖W1p.gradient u x - WithLp.toLp 2
      ((⨍ y in ball x₀ s ∩ (normalHalfSpace (E := E) a : Set _), W1p.gradient u y).fst, 0)‖ ^ 2
    with hψ
  -- The comparison step on every half-ball `B_r⁺`, `r ≤ R`.
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
      ψ ρ ≤ 4 * D * ((ρ / r) ^ ((n : ℝ) + 2) + 0) * ψ r +
        M * (K : ℝ) ^ 2 * r ^ ((n : ℝ) + 2 * α) := by
    intro ρ r hρ hρr hrR
    have h := setIntegral_ball_inter_normalHalfSpace_norm_gradient_sub_sq_le_add hα hu0 hu
      (hG.mono (inter_subset_inter_left _ (ball_subset_ball hrR))) hx₀
      ((ball_subset_ball hrR).trans hball) hρ hρr
    have hcast : (ρ / r) ^ ((n : ℝ) + 2) = (ρ / r) ^ (n + 2) := by
      rw [← Real.rpow_natCast]
      push_cast
      rfl
    rw [add_zero, hcast]
    refine h.trans_eq ?_
    simp only [ψ, M, D, n]
    ring
  have hf : MemLp (W1p.gradient u : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)) 2
      (volume.restrict (ball x₀ R ∩ (normalHalfSpace (E := E) a : Set _))) :=
    (Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono (inter_subset_left.trans hball) le_rfl)
  have hHm : ∀ s, MeasurableSet (ball x₀ s ∩ (normalHalfSpace (E := E) a : Set _)) := fun _ =>
    measurableSet_ball.inter (normalHalfSpace a).isOpen.measurableSet
  have hM0 : 0 ≤ M := mul_nonneg (by positivity) (mul_nonneg (by positivity) measureReal_nonneg)
  have h := hit (φ := ψ) (R := R) (B := M * (K : ℝ) ^ 2) (ε := 0) (by positivity) hε₀.le
    (monotoneOn_setIntegral_ball_inter_normalHalfSpace_norm_sub_sq hf)
    (fun s _ => setIntegral_nonneg (hHm s) fun _ _ => sq_nonneg _) hstep t R ht htR le_rfl
  have hX : 0 ≤ (t / R) ^ ((n : ℝ) + 2 * α) * ψ R :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg ht.le (ht.le.trans htR)) _)
      (setIntegral_nonneg (hHm R) fun _ _ => sq_nonneg _)
  have hY : 0 ≤ (K : ℝ) ^ 2 * t ^ ((n : ℝ) + 2 * α) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.le _)
  have hM : (t / R) ^ ((n : ℝ) + 2 * α) * ψ R + M * (K : ℝ) ^ 2 * t ^ ((n : ℝ) + 2 * α) ≤
      max 1 M * ((t / R) ^ ((n : ℝ) + 2 * α) * ψ R + (K : ℝ) ^ 2 * t ^ ((n : ℝ) + 2 * α)) := by
    nlinarith [le_max_left 1 M, le_max_right 1 M]
  calc ψ t ≤ C₀ * ((t / R) ^ ((n : ℝ) + 2 * α) * ψ R + M * (K : ℝ) ^ 2 * t ^ ((n : ℝ) + 2 * α)) :=
        h
    _ ≤ C₀ * (max 1 M * ((t / R) ^ ((n : ℝ) + 2 * α) * ψ R +
          (K : ℝ) ^ 2 * t ^ ((n : ℝ) + 2 * α))) := mul_le_mul_of_nonneg_left hM hC₀.le
    _ = _ := by ring

end PDE

end TauCeti
