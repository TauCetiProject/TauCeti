/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.ConstantCoefficientDecay
import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
import TauCeti.Analysis.Sobolev.W1p.GradientMeanOscillation
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.Campanato
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Campanato's method at a flat boundary for `-Δu = -div G`

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}`, let `ρ` be the reflection in its
boundary hyperplane, and let `U` be an open set with `ρ U ⊆ U`. Let `u ∈ H¹(U)` vanish on `U ∖ H`
and solve

`-Δu = -div G` in `U ∩ H`,

that is `∫ ⟨∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ` on `U ∩ H`. So `u` has zero
boundary values on the flat part `U ∩ ∂H` of the boundary. This file proves the Schauder
estimate for the gradient up to that flat part: if `G` is `α`-Hölder with constant `K` on
`S_R ∩ H`, where `S_R` is the open `R`-thickening of a set `S` of the closed half-space and
`S_R ⊆ U`, then the precise representative of the gradient of the odd reflection
`w = u - u ∘ ρ` is `α`-Hölder on `S`, with constant `C (K + R^{-(n+1)/2-α} ‖∇w‖_{L²(U)})`:
`exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_divergence`.
The function `w` agrees with `u` on `U ∩ H`
(`TauCeti.W1p.value_sub_compHyperplaneReflectionL_ae`), so this is the `C^{1,α}` estimate for `u`
up to the flat boundary.

The datum is a vector field `G`, whose tangential part need not vanish on the hyperplane. The odd
reflection of `G` is then discontinuous across the hyperplane, so `w` does not solve an equation
with a Hölder continuous datum on `U`, and the interior estimate
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient` does not apply to `w`. Such data
arise for the tangential derivatives `∂ₑu` of a solution of `-Δu = f` vanishing on the hyperplane:
they vanish there too and solve `-Δ(∂ₑu) = -div (-f e)`, with the tangential field `-f e`.

## The argument

The proof is Campanato's, with the comparison step carried out by reflection. Fix a centre `z` in
the closed half-space and a radius `r` with `B_r = ball z r ⊆ U`.

* **Comparison** (`setIntegral_norm_gradient_sub_compHyperplaneReflectionL_sub_sq_le`).
  Let `h` be the harmonic function on `B_r` with the boundary values of `w`. On the
  reflection-invariant set `V = B_r ∪ ρ B_r`, the odd reflection `w` satisfies
  `∫_V ⟨∇w, ∇φ⟩ = ∫_{V ∩ H} ⟨G, ∇η⟩` for `φ ∈ H¹₀(V)`, where `η = (φ - φ ∘ ρ)|_{V ∩ H}` lies in
  `H¹₀(V ∩ H)` (`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL`). Since
  `η` has zero boundary values, the constant `G(y)` of any `y ∈ B_r ∩ H` may be subtracted from
  `G`, and `‖∇η‖ ≤ 2 ‖∇φ‖` (`TauCeti.PDE.abs_energyFormH1_sub_compHyperplaneReflectionL_le`).
  A point of `H` is closer to `z` than to `ρ z`
  (`TauCeti.dist_le_dist_hyperplaneReflection`), so `V ∩ H ⊆ B_r ∩ H`, and testing with
  `φ = w - h` gives `∫_{B_r} ‖∇w - ∇h‖² ≤ 4 ∫_{B_r ∩ H} ‖G - G(y)‖² ≲ K² r^{n+1+2α}`.
* **Decay**
  (`setIntegral_ball_norm_gradient_sub_compHyperplaneReflectionL_sub_setAverage_sq_le`).
  The interior Campanato decay of harmonic gradients transfers to `w`: the square mean oscillation
  `ψ(t) = ∫_{B_t} ‖∇w - (∇w)_{B_t}‖²` satisfies
  `ψ(s) ≤ A (s / r)^{n+3} ψ(r) + A ∫_{B_r ∩ H} ‖G - G(y)‖²` for `s ≤ r`, with `A` depending only
  on `n`.
* **Iteration.** The iteration lemma `TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add`
  turns this into `ψ(t) ≲ (t / R)^{n+1+2α} (‖∇w‖² + K² R^{n+1+2α})` for `t ≤ R`, and Campanato's
  theorem (`TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le`)
  gives the Hölder estimate.

Centres on the hyperplane and centres inside `H` are treated alike, so no separate combination
of interior and boundary estimates is needed. The comparison uses only that `G` is Hölder on the
part of each ball in `H`, which is where the equation holds.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Sections 5.1 and 5.4 (Schauder estimates up to a
  flat boundary by Campanato's method).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the `C^{1,α}` estimate up to the boundary).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace InnerProductSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

section Reflection

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {U H V : Opens (EuclideanSpace ℝ ι)} {ν : EuclideanSpace ℝ ι} {c₀ : ℝ}

/-- The weak equation `-Δu = -div G` on `U ∩ H`, tested against test functions, holds for the
restriction of `u` to `V ∩ H` against all of `H¹₀(V ∩ H)`, with `G` replaced by `G - c`. -/
private theorem forall_energyFormH1_restrictL_restrictL_eq_inner (hVU : V ≤ U)
    {u : W1p mu U 2} {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ mu (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu)
    {c : EuclideanSpace ℝ ι}
    (hGc : MemLp (fun x => G x - c) 2
      (mu.restrict ((V ⊓ H : Opens _) : Set (EuclideanSpace ℝ ι))))
    (v : W1p0 mu (V ⊓ H) 2) :
    energyFormH1 (fun _ => 1) 0 0
      (W1p.restrictL (inf_le_left : V ⊓ H ≤ V) (W1p.restrictL hVU u)) (v : W1p mu (V ⊓ H) 2) =
        ⟪hGc.toLp, W1p.gradient (v : W1p mu (V ⊓ H) 2)⟫_ℝ := by
  have h' := forall_energyFormH1_restrictL_eq_inner (inf_le_inf_right H hVU)
    (memLp_top_const (energyIntegrand (1 : Matrix ι ι ℝ) 0 0)) hu hGc v
  have hr : W1p.restrictL (inf_le_left : V ⊓ H ≤ V) (W1p.restrictL hVU u) =
      W1p.restrictL (inf_le_inf_right H hVU) (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) :=
    (W1p.restrictL_restrictL _ _ _).trans (W1p.restrictL_restrictL _ _ _).symm
  exact (congrArg (fun w : W1p mu (V ⊓ H) 2 =>
    energyFormH1 (fun _ => 1) 0 0 w (v : W1p mu (V ⊓ H) 2)) hr).trans h'

/-- **The energy estimate for the replacement of the odd reflection.** Let `V ⊆ U` be open with
`ρ V ⊆ V`, let `u ∈ H¹(U)` and suppose that `u|_V` vanishes on `V ∖ H` and that its restriction
to `V ∩ H` solves `-Δu = -div F` against `H¹₀(V ∩ H)`. Let `B ⊆ V` be open and let `h ∈ H¹(B)` be
harmonic with the boundary values of `w = u - u ∘ ρ` on `B`. Then
`‖∇(w|_B - h)‖_{L²(B)} ≤ 2 ‖F‖_{L²(V ∩ H)}`. -/
private theorem norm_gradient_restrictL_sub_compHyperplaneReflectionL_sub_le (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hV : MapsTo (hyperplaneReflection ν c₀) V V) (hVU : V ≤ U)
    {B : Opens (EuclideanSpace ℝ ι)} (hBV : B ≤ V) (hBU : B ≤ U) {u : W1p mu U 2}
    (hu0 : ∀ᵐ x ∂mu.restrict V, x ∉ H → W1p.value (W1p.restrictL hVU u) x = 0)
    {F : Lp (EuclideanSpace ℝ ι) 2
      (mu.restrict ((V ⊓ H : Opens _) : Set (EuclideanSpace ℝ ι)))}
    (hu : ∀ v : W1p0 mu (V ⊓ H) 2, energyFormH1 (fun _ => 1) 0 0
      (W1p.restrictL (inf_le_left : V ⊓ H ≤ V) (W1p.restrictL hVU u)) (v : W1p mu (V ⊓ H) 2) =
        ⟪F, W1p.gradient (v : W1p mu (V ⊓ H) 2)⟫_ℝ)
    {h : W1p mu B 2}
    (hh : ∀ v : W1p0 mu B 2, energyFormH1 (fun _ => 1) 0 0 h (v : W1p mu B 2) = 0)
    (hwh : W1p.restrictL hBU (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) -
      h ∈ w1p0Submodule mu B 2) :
    ‖W1p.gradient (W1p.restrictL hBU
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) - h)‖ ≤ 2 * ‖F‖ := by
  -- The energy estimate for the replacement, with the functional `v ↦ ∫_B ⟨∇w, ∇v⟩`, bounded
  -- through the reflected functional on `V`.
  have hℓ : ∀ v : W1p0 mu B 2, |energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL hBU
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)) (v : W1p mu B 2)| ≤
        2 * ‖F‖ * ‖W1p.gradient (v : W1p mu B 2)‖ := fun v =>
    (congrArg abs ((energyFormH1_one_zero_zero_restrictL_eq_restrictL hBU hBV
      ((W1p.gradient_sub_compHyperplaneReflectionL_restrictL_ae ENNReal.ofNat_ne_top hU hV hVU
        u).filter_mono
          (ae_mono (Measure.restrict_mono_set _ (SetLike.coe_subset_coe.mpr hBV)))).symm
          v).trans (energyFormH1_restrictL _ _ _ hBV _ v))).trans_le
      ((abs_energyFormH1_sub_compHyperplaneReflectionL_le hν hH hV hu0 hu _).trans_eq
        (by rw [W1p0.norm_gradient_extendByZeroL]))
  simpa using (uniformlyEllipticOn_const_one_one (n := ι) (B : Set (EuclideanSpace ℝ ι))
    ).mul_norm_gradient_sub_le_add aestronglyMeasurable_const hwh hh (G := 0)
    (ℓ := fun v => energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL hBU
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)) (v : W1p mu B 2))
    (by positivity) hℓ (fun v => by simp)

end Reflection

variable {n : ℕ} {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}

/-- The reflection-invariant neighbourhood `V = B ∪ ρ B` of a ball `B` centred in the closed
half-space: it lies in `U` when `B` does and `ρ U ⊆ U`, and its part in `H` lies in `B`. -/
private theorem exists_le_and_inf_subset_ball_inter
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : c₀ ≤ ⟪z, ν⟫_ℝ) {r : ℝ}
    {B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hBz : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z r) (hBU : B ≤ U) :
    ∃ V : Opens (EuclideanSpace ℝ (Fin (n + 1))), MapsTo (hyperplaneReflection ν c₀) V V ∧
      V ≤ U ∧ B ≤ V ∧ ((V ⊓ H : Opens _) : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
        ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hball : ball z r ⊆ U := hBz ▸ SetLike.coe_subset_coe.mpr hBU
  have hρball : ∀ {y : EuclideanSpace ℝ (Fin (n + 1))} {s : ℝ} {x}, x ∈ ball y s →
      hyperplaneReflection ν c₀ x ∈ ball (hyperplaneReflection ν c₀ y) s := fun hx => by
    rwa [mem_ball, (hyperplaneReflection ν c₀).dist_map]
  refine ⟨⟨ball z r ∪ ball (hyperplaneReflection ν c₀ z) r, isOpen_ball.union isOpen_ball⟩,
    fun x hx => ?_, fun x hx => ?_, fun x hx => Or.inl (by simpa [← hBz] using hx), ?_⟩
  · rcases hx with hx | hx
    · exact Or.inr (hρball hx)
    · exact Or.inl (by simpa using hρball hx)
  · rcases hx with hx | hx
    · exact hball hx
    · have h' := hU (hball (by simpa using hρball hx))
      rwa [hyperplaneReflection_hyperplaneReflection] at h'
  · rintro x ⟨hxV, hxH⟩
    refine ⟨?_, hxH⟩
    rcases hxV with hx | hx
    · exact hx
    · rw [mem_ball] at hx ⊢
      exact (dist_le_dist_hyperplaneReflection ((hH x).1 hxH).le hz).trans_lt hx

/-- **Comparison with a harmonic function on balls centred in the closed half-space.** Let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`, and let
`U` be open with `ρ U ⊆ U`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and solve `-Δu = -div G` weakly in
`U ∩ H`. Let `z` lie in the closed half-space, let `B = ball z r ⊆ U`, and let `c` be a constant
vector with `G - c` square integrable on `B ∩ H`. If `h ∈ H¹(B)` is harmonic
(`∫ ⟨∇h, ∇v⟩ = 0` for every `v ∈ H¹₀(B)`) with the boundary values of the odd reflection
`w = u - u ∘ ρ`, that is `w|_B - h ∈ H¹₀(B)`, then

`∫_B ‖∇w - ∇h‖² ≤ 4 ∫_{B ∩ H} ‖G - c‖²`. The ball is given as an open set `B` with
`↑B = ball z r`. -/
theorem setIntegral_norm_gradient_sub_compHyperplaneReflectionL_sub_sq_le
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : c₀ ≤ ⟪z, ν⟫_ℝ) {r : ℝ}
    {B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hBz : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z r) (hBU : B ≤ U)
    {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2
      (volume.restrict (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))))
    {h : W1p volume B 2}
    (hh : ∀ v : W1p0 volume B 2, energyFormH1 (fun _ => 1) 0 0 h (v : W1p volume B 2) = 0)
    (hwh : W1p.restrictL hBU (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) -
      h ∈ w1p0Submodule volume B 2) :
    ∫ x in B, ‖W1p.gradient
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) x -
          W1p.gradient h x‖ ^ 2 ≤
      4 * ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 := by
  obtain ⟨V, hV, hVU, hBV, hVH⟩ := exists_le_and_inf_subset_ball_inter hH hU hz hBz hBU
  have hGc' : MemLp (fun x => G x - c) 2
      (volume.restrict ((V ⊓ H : Opens _) : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    hGc.mono_measure (Measure.restrict_mono hVH le_rfl)
  -- The restriction of `u` to `V` vanishes off `H`.
  have hu0' : ∀ᵐ x ∂volume.restrict V, x ∉ H → W1p.value (W1p.restrictL hVU u) x = 0 := by
    filter_upwards [W1p.value_restrictL_ae hVU u,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hVU) hu0] with x h1 h2 hx
    rw [h1, h2 hx]
  have hest := norm_gradient_restrictL_sub_compHyperplaneReflectionL_sub_le hν hH hU hV hVU hBV hBU
    hu0' (forall_energyFormH1_restrictL_restrictL_eq_inner hVU hu hGc') hh hwh
  have hGn : ‖hGc'.toLp‖ ^ 2 = ∫ x in V ⊓ H, ‖G x - c‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hGc'.coeFn_toLp] with x hx
    rw [hx]
  refine (W1p.setIntegral_norm_gradient_sub_sq_eq hBU
    (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) h).trans_le ?_
  calc ‖W1p.gradient (W1p.restrictL hBU
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) - h)‖ ^ 2
      ≤ (2 * ‖hGc'.toLp‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hest 2
    _ = 4 * ∫ x in V ⊓ H, ‖G x - c‖ ^ 2 := by rw [mul_pow, hGn]; norm_num
    _ ≤ 4 * ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set (hGc.integrable_norm_pow two_ne_zero)
          (ae_of_all _ fun _ => by positivity) hVH.eventuallySubset) (by norm_num)

/-- The interior decay of harmonic gradients transferred to `u`, with the constant of
`setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen` for the Laplacian:
`ψ(ρ) ≤ 4 D (ρ / r)^(n + 3) ψ(r) + (4 D + 2) ∫_{B_r} ‖∇u - ∇h‖²` with `D = 2^(3n + 13) (n + 2)²`
for every harmonic `h ∈ H¹(B_r)`. -/
private theorem setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_harmonic
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r ρ : ℝ}
    {h : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hh : ∀ v : W1p0 volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      energyFormH1 (fun _ => 1) 0 0 h (v : W1p volume _ 2) = 0)
    (hball : ball z r ⊆ Omega) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball z ρ, ‖W1p.gradient u x - ⨍ y in ball z ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) * (ρ / r) ^ (n + 3) *
          (∫ x in ball z r, ‖W1p.gradient u x - ⨍ y in ball z r, W1p.gradient u y‖ ^ 2) +
        (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
          ∫ x in ball z r, ‖W1p.gradient u x - W1p.gradient h x‖ ^ 2 := by
  have hD : 2 ^ (3 * (n + 1) + 10) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * √(1 / 1) ^ (n + 1 + 2) =
      2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2 := by
    rw [div_one, Real.sqrt_one, one_pow, mul_one]
    push_cast
    ring_nf
  have h' := setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen (A := 1) (u := u)
    one_pos (fun ξ => by rw [one_mul, toQuadraticForm'_one])
    (fun ξ => by rw [one_mul, toQuadraticForm'_one]) hh hball hρ hρr
  rwa [hD] at h'

/-- A harmonic replacement of the odd reflection on a ball centred in the closed half-space,
with the energy distance of
`TauCeti.PDE.setIntegral_norm_gradient_sub_compHyperplaneReflectionL_sub_sq_le`. -/
private theorem exists_forall_energyFormH1_eq_zero_setIntegral_norm_gradient_sub_sq_le
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : c₀ ≤ ⟪z, ν⟫_ℝ) {r : ℝ} (hball : ball z r ⊆ U)
    {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2
      (volume.restrict (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))))) :
    ∃ h : W1p volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ v : W1p0 volume (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
        energyFormH1 (fun _ => 1) 0 0 h (v : W1p volume _ 2) = 0) ∧
      ∫ x in ball z r, ‖W1p.gradient
          (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) x -
            W1p.gradient h x‖ ^ 2 ≤
        4 * ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 := by
  have hB : (⟨ball z r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ U := hball
  obtain ⟨h, hwh, hh0, -⟩ := exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball
    (Omega := ⟨ball z r, isOpen_ball⟩) subset_rfl
    (W1p.restrictL hB (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))
  exact ⟨h, hh0, setIntegral_norm_gradient_sub_compHyperplaneReflectionL_sub_sq_le hν hH hU hu0 hu
    hz rfl hB hGc hh0 hwh⟩

/-- **Campanato decay at centres in the closed half-space.** Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`, and let `U` be open with `ρ U ⊆ U`. Let
`u ∈ H¹(U)` vanish on `U ∖ H` and solve `-Δu = -div G` weakly in `U ∩ H`. Let `z` lie in the
closed half-space, let `ball z r ⊆ U`, and let `c` be a constant vector with `G - c` square
integrable on `ball z r ∩ H`. Then the square mean oscillation
`ψ(t) = ∫_{B_t} ‖∇w - (∇w)_{B_t}‖²` of the gradient of the odd reflection `w = u - u ∘ ρ` on the
balls `B_t = ball z t` satisfies, for `0 < s ≤ r`,

`ψ(s) ≤ 4 D (s / r)^(n + 3) ψ(r) + 4 (4 D + 2) ∫_{B_r ∩ H} ‖G - c‖²`,

with `D = 2^(3n + 13) (n + 2)²`. -/
theorem setIntegral_ball_norm_gradient_sub_compHyperplaneReflectionL_sub_setAverage_sq_le
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : c₀ ≤ ⟪z, ν⟫_ℝ) {r s : ℝ} (hball : ball z r ⊆ U)
    {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2
      (volume.restrict (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))))
    (hs : 0 < s) (hsr : s ≤ r) :
    ∫ x in ball z s, ‖W1p.gradient
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) x -
          ⨍ y in ball z s, W1p.gradient
            (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) y‖ ^ 2 ≤
      4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) * (s / r) ^ (n + 3) *
          (∫ x in ball z r, ‖W1p.gradient
            (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) x -
              ⨍ y in ball z r, W1p.gradient
                (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) y‖ ^ 2) +
        4 * (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
          ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 := by
  obtain ⟨h, hh0, hE⟩ := exists_forall_energyFormH1_eq_zero_setIntegral_norm_gradient_sub_sq_le
    hν hH hU hu0 hu hz hball hGc
  refine (setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_harmonic hh0 hball hs hsr).trans
    (add_le_add le_rfl ?_)
  calc (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
        ∫ x in ball z r, ‖W1p.gradient
          (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) x -
            W1p.gradient h x‖ ^ 2
      ≤ (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
          (4 * ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by ring

/-- The data `G` enter the comparison through `∫_{B_r ∩ H} ‖G - c‖²`. If `G` is `α`-Hölder with
constant `K` on `T ∩ H` and `ball z r ⊆ T` with `z` in the closed half-space, then for the value
`c` of `G` at a point of `ball z r ∩ H` this is at most `K² (2r)^{2α} |B_r|`. -/
private theorem exists_memLp_setIntegral_norm_sub_sq_le {α K : ℝ≥0} (hα : 0 < α)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {T : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hG : HolderOnWith K α G (T ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))) (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : c₀ ≤ ⟪z, ν⟫_ℝ) {r : ℝ} (hr : 0 < r) (hzT : ball z r ⊆ T) :
    ∃ c : EuclideanSpace ℝ (Fin (n + 1)), MemLp (fun x => G x - c) 2
        (volume.restrict (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))) ∧
      ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 ≤
        (K : ℝ) ^ 2 * (2 * r) ^ (2 * (α : ℝ)) * volume.real (ball z r) := by
  have hνpos : 0 < ‖ν‖ := norm_pos_iff.2 hν
  -- A point `y` of `ball z r ∩ H`, at height `r / 2` above `z` along `ν`.
  set y := z + (r / 2 / ‖ν‖) • ν with hy
  have hyz : dist y z = r / 2 := by
    rw [hy, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    field_simp
  have hyH : y ∈ H := by
    rw [hH, hy, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    have : r / 2 / ‖ν‖ * ‖ν‖ ^ 2 = r / 2 * ‖ν‖ := by field_simp
    rw [this]
    nlinarith
  have hyT : y ∈ T ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    ⟨hzT (mem_ball.2 (by rw [hyz]; linarith)), hyH⟩
  have hsH : MeasurableSet (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    measurableSet_ball.inter H.isOpen.measurableSet
  have hbound : ∀ x ∈ ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ‖G x - G y‖ ≤ K * (2 * r) ^ (α : ℝ) := fun x hx => by
    have h := hG.dist_le ⟨hzT hx.1, hx.2⟩ hyT
    rw [dist_eq_norm] at h
    refine h.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg ?_ α.property) K.property)
    have := dist_triangle x z y
    rw [dist_comm z y, hyz] at this
    have hxz := mem_ball.1 hx.1
    linarith
  have : IsFiniteMeasure (volume.restrict
      (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :=
    isFiniteMeasure_restrict.2 ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hm : AEStronglyMeasurable (fun x => G x - G y)
      (volume.restrict (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :=
    (((hG.continuousOn hα).mono (inter_subset_inter_left _ hzT)).sub
      continuousOn_const).aestronglyMeasurable hsH
  refine ⟨G y, MemLp.of_bound hm _ (ae_restrict_of_forall_mem hsH hbound), ?_⟩
  calc ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - G y‖ ^ 2
      ≤ ∫ _ in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 :=
        setIntegral_mono_on ((MemLp.of_bound hm _ (ae_restrict_of_forall_mem hsH
          hbound)).integrable_norm_pow two_ne_zero) (integrable_const _) hsH
          fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hbound x hx) 2
    _ = volume.real (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) *
          ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ volume.real (ball z r) * ((K : ℝ) * (2 * r) ^ (α : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (measureReal_mono inter_subset_left measure_ball_lt_top.ne)
          (by positivity)
    _ = (K : ℝ) ^ 2 * (2 * r) ^ (2 * (α : ℝ)) * volume.real (ball z r) := by
        rw [mul_pow, ← Real.rpow_natCast ((2 * r) ^ (α : ℝ)), ← Real.rpow_mul (by positivity)]
        push_cast
        ring_nf

/-- One step of the decay at a centre in the closed half-space, with the data term
`A K² 4^α ω r^γ`, `γ = n + 1 + 2α`, from the Hölder continuity of `G` on `ball z R ∩ H`, where
`ω` is the volume of the unit ball: `ψ(ρ) ≤ A (ρ / r)^(n + 3) ψ(r) + A K² 4^α ω r^γ` for
`0 < ρ ≤ r ≤ R`, if `A` dominates the constant `4 (4 D + 2)`, and so also `4 D`, of
`setIntegral_ball_norm_gradient_sub_compHyperplaneReflectionL_sub_setAverage_sq_le`. -/
private theorem le_mul_rpow_mul_add_mul_rpow_of_holderOnWith {α : ℝ≥0} (hα : 0 < α)
    {γ ω D A : ℝ} (hγ : γ = (n : ℝ) + 1 + 2 * α)
    (hω : ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hD : D = 2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) (hAD : 4 * (4 * D + 2) ≤ A)
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {w : W1p volume U 2} (hw : w = u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hG : HolderOnWith K α G (ball z R ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hz : c₀ ≤ ⟪z, ν⟫_ℝ) (hball : ball z R ⊆ U) {ψ : ℝ → ℝ}
    (hψ : ∀ s, ψ s = ∫ x in ball z s, ‖W1p.gradient w x - ⨍ y in ball z s, W1p.gradient w y‖ ^ 2)
    (hψ0 : ∀ s, 0 ≤ ψ s) {B : ℝ} (hB : B = A * (K : ℝ) ^ 2 * 4 ^ (α : ℝ) * ω)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hrR : r ≤ R) :
    ψ ρ ≤ A * (ρ / r) ^ ((n : ℝ) + 3) * ψ r + B * r ^ γ := by
  subst hw hD
  have hD0 : (0 : ℝ) ≤ 2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2 := by positivity
  have hA0 : 0 ≤ A := by linarith
  have hr : 0 < r := hρ.trans_le hρr
  obtain ⟨c, hc, hint⟩ := exists_memLp_setIntegral_norm_sub_sq_le hα hG hν hH hz hr
    (ball_subset_ball hrR)
  have hdata : (K : ℝ) ^ 2 * (2 * r) ^ (2 * (α : ℝ)) * volume.real (ball z r) =
      (K : ℝ) ^ 2 * 4 ^ (α : ℝ) * ω * r ^ γ := by
    -- The volume of the ball is `ω r^{n+1}`.
    have hvol : volume.real (ball z r) = ω * r ^ ((n : ℝ) + 1) := by
      rw [Measure.addHaar_real_ball_of_pos _ z hr, finrank_euclideanSpace_fin, ← hω, mul_comm]
      norm_cast
    -- The powers: `(2 r)^{2α} r^{n+1} = 4^α r^γ`.
    have hpow : (2 * r) ^ (2 * (α : ℝ)) * r ^ ((n : ℝ) + 1) = 4 ^ (α : ℝ) * r ^ γ := by
      rw [Real.mul_rpow zero_le_two hr.le, Real.rpow_mul zero_le_two,
        show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num, hγ, Real.rpow_add hr ((n : ℝ) + 1)]
      ring
    rw [hvol]
    linear_combination (K : ℝ) ^ 2 * ω * hpow
  have h1 : 4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) * (ρ / r) ^ (n + 3) ≤
      A * (ρ / r) ^ ((n : ℝ) + 3) := by
    have hq : (ρ / r) ^ (n + 3) = (ρ / r) ^ ((n : ℝ) + 3) := by norm_cast
    rw [hq]
    gcongr
    linarith
  have hI0 : 0 ≤ ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have h2 : 4 * (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
      ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 ≤ B * r ^ γ :=
    calc 4 * (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
          ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2
        ≤ A * ∫ x in ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖G x - c‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hAD hI0
      _ ≤ A * ((K : ℝ) ^ 2 * 4 ^ (α : ℝ) * ω * r ^ γ) :=
          mul_le_mul_of_nonneg_left (hint.trans_eq hdata) hA0
      _ = B * r ^ γ := by rw [hB]; ring
  have hd := setIntegral_ball_norm_gradient_sub_compHyperplaneReflectionL_sub_setAverage_sq_le
    hν hH hU hu0 hu hz ((ball_subset_ball hrR).trans hball) hc hρ hρr
  rw [← hψ ρ, ← hψ r] at hd
  exact hd.trans (add_le_add (mul_le_mul_of_nonneg_right h1 (hψ0 r)) h2)

/-- **Decay at a centre in the closed half-space, given the iteration lemma.** In the setting of
`setIntegral_ball_norm_gradient_sub_compHyperplaneReflectionL_sub_setAverage_sq_le`, let
`ball z R ⊆ U` and let `G` be `α`-Hölder with constant `K` on `ball z R ∩ H`. If `A` dominates
the constants of that decay estimate and `C₁` is the constant of the iteration lemma for `A` and
the exponent `γ = n + 1 + 2α`, then the square mean oscillation `ψ(t)` of the gradient of the odd
reflection `w = u - u ∘ ρ` on `ball z t` satisfies
`ψ(t) ≤ C₁ (1 + 4^α ω A) (K² R^γ + ∫_{B_R} ‖∇w‖²) (t / R)^γ` for `0 < t ≤ R`, where `ω` is the
volume of the unit ball. -/
private theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_rpow_of_iteration
    {α : ℝ≥0} (hα : 0 < α)
    {γ ω D A : ℝ} (hγ : γ = (n : ℝ) + 1 + 2 * α)
    (hω : ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hD : D = 2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) (hAD : 4 * (4 * D + 2) ≤ A)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hit : ∀ {φ : ℝ → ℝ} {R B : ℝ}, 0 ≤ B → MonotoneOn φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, 0 ≤ φ r) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R → φ ρ ≤ A * (ρ / r) ^ ((n : ℝ) + 3) * φ r + B * r ^ γ) →
      ∀ ρ, 0 < ρ → ρ ≤ R → φ ρ ≤ C₁ * ((ρ / R) ^ γ * φ R + B * ρ ^ γ))
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {w : W1p volume U 2} (hw : w = u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hG : HolderOnWith K α G (ball z R ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hz : c₀ ≤ ⟪z, ν⟫_ℝ) (hball : ball z R ⊆ U) {ψ : ℝ → ℝ}
    (hψ : ∀ s, ψ s = ∫ x in ball z s, ‖W1p.gradient w x - ⨍ y in ball z s, W1p.gradient w y‖ ^ 2)
    {IR : ℝ} (hIR : IR = ∫ x in ball z R, ‖W1p.gradient w x‖ ^ 2) {t : ℝ} (ht : 0 < t)
    (htR : t ≤ R) :
    ψ t ≤ C₁ * (1 + A * 4 ^ (α : ℝ) * ω) * ((K : ℝ) ^ 2 * R ^ γ + IR) * (t / R) ^ γ := by
  have hR : 0 < R := ht.trans_le htR
  have hA0 : 0 ≤ A := le_trans (by rw [hD]; positivity) hAD
  have hψ0 : ∀ s, 0 ≤ ψ s := fun s => by
    rw [hψ]
    exact integral_nonneg fun _ => by positivity
  have hω0 : 0 < ω := hω ▸ measureReal_ball_pos volume _ one_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = A * (K : ℝ) ^ 2 * 4 ^ (α : ℝ) * ω := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  have hmono : MonotoneOn ψ (Ioc 0 R) := fun a ha b hb hab => by
    rw [hψ, hψ]
    exact W1p.monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq w hball ha hb hab
  have hψR : ψ R ≤ IR := by
    rw [hψ, hIR]
    exact W1p.setIntegral_norm_gradient_sub_setAverage_sq_le w hball
  have hIR0 : 0 ≤ IR := by
    rw [hIR]
    exact integral_nonneg fun _ => by positivity
  -- The iteration, then `t^γ = R^γ (t / R)^γ` and arithmetic.
  have hit' := hit hB0 hmono (fun s _ => hψ0 s) (fun ρ r hρ hρr hrR =>
    le_mul_rpow_mul_add_mul_rpow_of_holderOnWith hα hγ hω hD hAD hν hH hU hu0 hu hw hG
      hz hball hψ hψ0 hB hρ hρr hrR) t ht htR
  have htR' : t ^ γ = R ^ γ * (t / R) ^ γ := by
    rw [Real.div_rpow ht.le hR.le]
    field_simp
  have hq0 : 0 ≤ (t / R) ^ γ := by positivity
  have hc1 : 1 ≤ 1 + A * 4 ^ (α : ℝ) * ω := le_add_of_nonneg_right (by positivity)
  have e1 : (t / R) ^ γ * ψ R ≤ (1 + A * 4 ^ (α : ℝ) * ω) * ((t / R) ^ γ * IR) :=
    (mul_le_mul_of_nonneg_left hψR hq0).trans (le_mul_of_one_le_left (mul_nonneg hq0 hIR0) hc1)
  have e2 : B * t ^ γ ≤ (1 + A * 4 ^ (α : ℝ) * ω) * ((K : ℝ) ^ 2 * R ^ γ * (t / R) ^ γ) := by
    have hX : 0 ≤ (K : ℝ) ^ 2 * R ^ γ * (t / R) ^ γ := by positivity
    rw [htR', hB, show A * (K : ℝ) ^ 2 * 4 ^ (α : ℝ) * ω * (R ^ γ * (t / R) ^ γ) =
      A * 4 ^ (α : ℝ) * ω * ((K : ℝ) ^ 2 * R ^ γ * (t / R) ^ γ) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) hX
  calc ψ t ≤ C₁ * ((t / R) ^ γ * ψ R + B * t ^ γ) := hit'
    _ ≤ C₁ * ((1 + A * 4 ^ (α : ℝ) * ω) * ((t / R) ^ γ * IR) +
          (1 + A * 4 ^ (α : ℝ) * ω) * ((K : ℝ) ^ 2 * R ^ γ * (t / R) ^ γ)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC₁
    _ = _ := by ring

/-- The mean oscillation of the gradient of the odd reflection on `closedBall z t`, at a centre
`z` of the closed half-space with `ball z R ⊆ U`, is at most `M Q t^α`, where
`M = √(2 C₁ (1 + 4^α ω A) / ω)`, given the iteration lemma and any `Q ≥ 0` with
`K² R^γ ≤ (R^{(n+1)/2+α} Q)²` and `∫_{B_R} ‖∇w‖² ≤ (R^{(n+1)/2+α} Q)²`. -/
private theorem setAverage_closedBall_norm_gradient_sub_le_of_iteration {α : ℝ≥0} (hα : 0 < α)
    {γ ω D A : ℝ} (hγ : γ = (n : ℝ) + 1 + 2 * α)
    (hω : ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hD : D = 2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) (hAD : 4 * (4 * D + 2) ≤ A)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hit : ∀ {φ : ℝ → ℝ} {R B : ℝ}, 0 ≤ B → MonotoneOn φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, 0 ≤ φ r) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R → φ ρ ≤ A * (ρ / r) ^ ((n : ℝ) + 3) * φ r + B * r ^ γ) →
      ∀ ρ, 0 < ρ → ρ ≤ R → φ ρ ≤ C₁ * ((ρ / R) ^ γ * φ R + B * ρ ^ γ))
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {w : W1p volume U 2} (hw : w = u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hG : HolderOnWith K α G (ball z R ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hz : c₀ ≤ ⟪z, ν⟫_ℝ) (hR : 0 < R) (hball : ball z R ⊆ U) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hKQ : (K : ℝ) ^ 2 * R ^ γ ≤ (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2)
    (hIQ : ∫ x in ball z R, ‖W1p.gradient w x‖ ^ 2 ≤ (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2)
    {t : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    ⨍ y in closedBall z t, ‖W1p.gradient w y - ⨍ v in closedBall z t, W1p.gradient w v‖ ≤
      √(2 * C₁ * (1 + A * 4 ^ (α : ℝ) * ω) / ω) * Q * t ^ (α : ℝ) := by
  have hdec := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_rpow_of_iteration hα hγ hω hD
    hAD hC₁ hit hν hH hU hu0 hu hw hG hz hball
    (ψ := fun s => ∫ x in ball z s, ‖W1p.gradient w x - ⨍ y in ball z s, W1p.gradient w y‖ ^ 2)
    (fun _ => rfl) rfl ht htR
  have hA0 : 0 ≤ A := le_trans (by rw [hD]; positivity) hAD
  subst hω
  -- The bound in the form of `W1p.setAverage_closedBall_norm_gradient_sub_le_mul_rpow`, for an
  -- abstract value `IR` of the `L²` mass of `∇w` on `B_R`.
  have key : ∀ IR : ℝ, IR ≤ (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 →
      C₁ * (1 + A * 4 ^ (α : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) *
          ((K : ℝ) ^ 2 * R ^ γ + IR) * (t / R) ^ γ ≤
        2 * C₁ * (1 + A * 4 ^ (α : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) *
          (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 * (t / R) ^ (2 * (α : ℝ) + ((n : ℝ) + 1)) :=
    fun IR hIR => by
      rw [show (t / R) ^ (2 * (α : ℝ) + ((n : ℝ) + 1)) = (t / R) ^ γ by rw [hγ]; ring_nf]
      calc C₁ * (1 + A * 4 ^ (α : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) *
              ((K : ℝ) ^ 2 * R ^ γ + IR) * (t / R) ^ γ
          ≤ C₁ * (1 + A * 4 ^ (α : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) *
              (2 * (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2) * (t / R) ^ γ := by
            gcongr
            linarith
        _ = _ := by ring
  exact W1p.setAverage_closedBall_norm_gradient_sub_le_mul_rpow w
    ((ball_subset_ball htR).trans hball) ht hR hQ0 (hdec.trans (key _ hIQ))

/-- The Hölder estimate up to the flat boundary, given the iteration lemma, for the gradient of
the odd reflection `w = u - u ∘ ρ`: with `Q = K + R^{-(n+1)/2-α} ‖∇w‖` the constant is
`2 · 2^α (c √(2 C₁ (1 + 4^α ω A) / ω) + 1 / √ω) Q`, where `c = 2^{n+1} / (1 - 2^{-α})` is the
constant of Campanato's theorem and `ω` the volume of the unit ball. -/
private theorem holderOnWith_gradient_of_iteration {α : ℝ≥0} (hα : 0 < α)
    {γ ω D A : ℝ} (hγ : γ = (n : ℝ) + 1 + 2 * α)
    (hω : ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hD : D = 2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) (hAD : 4 * (4 * D + 2) ≤ A)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hit : ∀ {φ : ℝ → ℝ} {R B : ℝ}, 0 ≤ B → MonotoneOn φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, 0 ≤ φ r) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R → φ ρ ≤ A * (ρ / r) ^ ((n : ℝ) + 3) * φ r + B * r ^ γ) →
      ∀ ρ, 0 < ρ → ρ ≤ R → φ ρ ≤ C₁ * ((ρ / R) ^ γ * φ R + B * ρ ^ γ))
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {u : W1p volume U 2}
    (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {w : W1p volume U 2} (hw : w = u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ}
    (hG : HolderOnWith K α G (thickening R S ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hS : ∀ x ∈ S, c₀ ≤ ⟪x, ν⟫_ℝ) (hR : 0 < R) (hRS : thickening R S ⊆ U) {Q : ℝ}
    (hQ : Q = K + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient w‖) :
    HolderOnWith ((2 * 2 ^ (α : ℝ) * (2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
        (1 - 2 ^ (-(α : ℝ))) * √(2 * C₁ * (1 + A * 4 ^ (α : ℝ) * ω) / ω) + 1 / √ω)) * Q).toNNReal
      α (preciseRepresentative volume
        (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) S := by
  have hball : ∀ z ∈ S, ball z R ⊆ U := fun z hz => (ball_subset_thickening hz R).trans hRS
  have hball1 : ∀ z ∈ S, ball z (1 * R) ⊆ U := fun z hz => by rw [one_mul]; exact hball z hz
  have hQ0 : 0 ≤ Q := hQ ▸ by positivity
  -- `X = R^{(n+1)/2+α} Q` dominates both `K R^{(n+1)/2+α}` and `‖∇w‖`.
  have hXu : ‖W1p.gradient w‖ ≤ R ^ (((n : ℝ) + 1) / 2 + α) * Q := by
    rw [hQ, mul_add, ← mul_assoc _ (R ^ _), ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero,
      one_mul]
    exact le_add_of_nonneg_left (by positivity)
  have hKX : (K : ℝ) ^ 2 * R ^ γ ≤ (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 :=
    hγ ▸ Real.sq_mul_rpow_add_two_mul_le hR K.property (hQ ▸ le_add_of_nonneg_right (by positivity))
  have hIX : ∀ z ∈ S, ∫ x in ball z R, ‖W1p.gradient w x‖ ^ 2 ≤
      (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 := fun z hz =>
    (Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient w) (hball z hz)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hXu 2)
  -- The mean oscillation of `∇w` on `closedBall z t` is at most `M Q t^α`.
  have hosc : ∀ z ∈ S, ∀ t, 0 < t → t ≤ 1 * R →
      ⨍ y in closedBall z t, ‖W1p.gradient w y - ⨍ v in closedBall z t, W1p.gradient w v‖ ≤
        √(2 * C₁ * (1 + A * 4 ^ (α : ℝ) * ω) / ω) * Q * t ^ (α : ℝ) := fun z hz t ht htR =>
    setAverage_closedBall_norm_gradient_sub_le_of_iteration hα hγ hω hD hAD hC₁ hit hν hH
      hU hu0 hu hw (hG.mono (inter_subset_inter_left _ (ball_subset_thickening hz R))) (hS z hz) hR
      (hball z hz) hQ0 hKX (hIX z hz) ht (by rwa [one_mul] at htR)
  subst hω
  -- The average of `∇w` over `closedBall z R` is at most `R^α Q / √ω`.
  have hsq : (R ^ (((n : ℝ) + 1) / 2 + α) * Q) ^ 2 = R ^ (n + 1) * (R ^ (α : ℝ) * Q) ^ 2 := by
    rw [Real.rpow_div_two_add_mul_sq _ hR, Real.rpow_add_one hR.ne', Real.rpow_natCast]
    ring
  have havg : ∀ z ∈ S, ‖⨍ y in closedBall z (1 * R), W1p.gradient w y‖ ≤
      R ^ (α : ℝ) * Q /
        √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * 1 ^ (n + 1)) :=
    fun z hz =>
    W1p.norm_setAverage_closedBall_gradient_le_div w (hball1 z hz) one_pos hR hQ0
      (((Lp.setIntegral_norm_sq_le_norm_sq (W1p.gradient w) (hball1 z hz)).trans
        (pow_le_pow_left₀ (norm_nonneg _) hXu 2)).trans_eq hsq)
  have hH' := TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le hα
    (ρ := 1 * R) (by positivity) (fun z hz => W1p.integrableOn_closedBall_gradient w (hball1 z hz)
      le_rfl) hosc havg
  refine hH'.mono_const (Real.toNNReal_le_toNNReal (le_of_eq ?_))
  rw [one_mul, one_pow, mul_one, Real.rpow_neg hR.le]
  field_simp [(Real.rpow_pos_of_pos hR (α : ℝ)).ne']

/-- **Schauder estimate for the gradient up to a flat boundary for `-Δu = -div G`.** Let
`0 < α < 1`. There is a constant `C`, depending only on `n` and `α`, such that the following
holds. Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, let `ρ` be the
reflection in its boundary hyperplane, and let `U` be open with `ρ U ⊆ U`. Let `u ∈ H¹(U)` vanish
on `U ∖ H` and solve `-Δu = -div G` weakly in `U ∩ H`, that is
`∫_{U ∩ H} ⟨∇u, ∇φ⟩ = ∫_{U ∩ H} ⟨G, ∇φ⟩` for every test function `φ` on `U ∩ H`. Let `S` be a set
in the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}` whose open `R`-thickening `S_R` lies in `U`, and let
`G` be `α`-Hölder with constant `K` on `S_R ∩ H`. Then the precise representative of the gradient
of the odd reflection `w = u - u ∘ ρ` is `α`-Hölder on `S`, with constant

`C (K + R^{-(n+1)/2-α} ‖∇w‖_{L²(U)})`.

The set `S` may meet the hyperplane, where `u` vanishes, so this is the `C^{1,α}` estimate up to
the flat part of the boundary of `U ∩ H`. The function `w` agrees with `u` on `U ∩ H`
(`TauCeti.W1p.value_sub_compHyperplaneReflectionL_ae`), and the precise representative agrees
with `∇w` almost everywhere on `U` (`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`).
No condition is imposed on the tangential part of `G` on the hyperplane. -/
theorem
    exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_divergence
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ} {u : W1p volume U 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 (fun _ => 1) 0 0
        (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u) (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
          ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      HolderOnWith K α G (thickening R S ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      (∀ x ∈ S, c₀ ≤ ⟪x, ν⟫_ℝ) → 0 < R → thickening R S ⊆ U →
        HolderOnWith (C * ((K : ℝ) + R ^ (-(((n : ℝ) + 1) / 2 + α)) *
            ‖W1p.gradient (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)‖)
              ).toNNReal α
          (preciseRepresentative volume (W1p.gradient
            (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) :
              EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) S := by
  have hα' : (0 : ℝ) < α := hα
  have hα1' : (α : ℝ) < 1 := hα1
  -- The constant of the iteration lemma, for the exponent `n + 1 + 2α` and the constant `A`
  -- dominating those of the decay estimate.
  have hiter : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ {φ : ℝ → ℝ} {R B : ℝ}, 0 ≤ B → MonotoneOn φ (Ioc 0 R) →
      (∀ r ∈ Ioc 0 R, 0 ≤ φ r) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R → φ ρ ≤ 4 * (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2) *
        (ρ / r) ^ ((n : ℝ) + 3) * φ r + B * r ^ ((n : ℝ) + 1 + 2 * α)) →
      ∀ ρ, 0 < ρ → ρ ≤ R →
        φ ρ ≤ C₁ * ((ρ / R) ^ ((n : ℝ) + 1 + 2 * α) * φ R + B * ρ ^ ((n : ℝ) + 1 + 2 * α)) := by
    obtain ⟨ε₀, C₁, hε₀, hC₁, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add
      (A := 4 * (4 * (2 ^ (3 * n + 13) * ((n : ℝ) + 2) ^ 2) + 2))
      (α := (n : ℝ) + 3) (β := (n : ℝ) + 1 + 2 * α) (γ := (n : ℝ) + 1 + 2 * α) (by positivity)
      (by linarith) (by linarith)
    exact ⟨C₁, hC₁.le, fun hB hm hn hs ρ hρ hρR => hit hB hε₀.le hm hn
      (fun ρ r hρ hρr hrR => (hs ρ r hρ hρr hrR).trans_eq (by rw [add_zero])) ρ _ hρ hρR le_rfl⟩
  have hc : 0 ≤ (2 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
      (1 - 2 ^ (-(α : ℝ))) :=
    div_nonneg (by positivity) (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two
      (neg_lt_zero.2 hα'))).le
  exact hiter.elim fun C₁ hC₁ => ⟨_, mul_nonneg (by positivity)
    (add_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (by positivity)),
    fun hν hH hU hu0 hu hG hS hR hRS => holderOnWith_gradient_of_iteration hα rfl rfl rfl le_rfl
      hC₁.1 hC₁.2 hν hH hU hu0 hu rfl hG hS hR hRS rfl⟩

end PDE

end TauCeti
