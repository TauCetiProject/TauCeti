/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Schwartz
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LocalizedChangeOfVariables
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Changing the chart of a Sobolev or Besov reading of a function on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. A complex-valued smooth function `u` on `M` is read in a
chart `e` of the maximal atlas through a cutoff `τ` as the Schwartz function `τ · (u ∘ e⁻¹)` on
`ℝⁿ` (`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). This file shows that the `H^{s,p}` norm
of such a reading is controlled by the reading in any other chart: if `Ψ` is a cutoff `ψ` in a
chart `e'` read on `M`, then for every real `s` and `1 < p < ∞`

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{H^{s,p}} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^{s,p}}`

(`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`), and that
the same holds for the Besov norms `B^s_{p,q}`, `1 ≤ p, q ≤ ∞`, among them the Hölder–Zygmund norms
`𝒞^s = B^s_{∞,∞}` (`TauCeti.exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`).
The reading in `e` is `θ · (w ∘ κ)` for the reading `w` in `e'`, the transition map `κ = e' ∘ e⁻¹`
and a cutoff `θ` with compact support in the source of `κ` (`OpenPartialHomeomorph.overlapCutoff`,
`TauCeti.cutoffPushforwardSchwartz_mulLeft_ofReal_cutoffPullback_apply`). So changing the chart
of a reading is bounded in every norm in which such localized changes of variables are bounded
(`TauCeti.exists_norm_cutoffPushforwardSchwartz_mulLeft_le`), among them the norms of `H^{s,p}`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`) and of
`B^s_{p,q}` (`TauCeti.BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp`).

The readings through a fixed cutoff `φ` are all fixed in every `H^t` by multiplication by one
Schwartz function
(`TauCeti.exists_smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`). So readings
bounded in `H^s` through finitely many fixed cutoffs form a relatively compact set in `H^r` for
`r < s`, by Rellich's theorem for a common compact support
(`TauCeti.isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_of_norm_le`).

## Main results

* `TauCeti.cutoffPushforwardSchwartz_mulLeft_ofReal_cutoffPullback_apply`: the reading of `Ψ g` in
  `e` as a localized change of variables of the reading of `g` in `e'`.
* `TauCeti.exists_norm_cutoffPushforwardSchwartz_mulLeft_le`: changing the chart of a reading
  costs a constant in every norm in which localized changes of variables are bounded.
* `TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`: changing
  the chart of a reading costs a constant in the `H^{s,p}` norm.
* `TauCeti.exists_smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`: the readings
  through a cutoff are fixed in every `H^t` by multiplication by one Schwartz function.
* `TauCeti.isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_of_norm_le`:
  Rellich's theorem for chart readings, from `H^s` to `H^r` for `r < s`.
* `TauCeti.exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`: changing the chart of
  a reading costs a constant in the `B^s_{p,q}` norm.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §7.2 (Besov spaces on manifolds,
  defined through charts and a partition of unity).
-/

public section

noncomputable section

open Set TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap ENNReal Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **A reading in a second chart.** Let `ψ` be a cutoff in a chart `e'`, with `Ψ` the smooth
function `ψ ∘ e'` on `M`, extended by `0`, `τ` a cutoff in a chart `e` and `ψ₁` a cutoff in `e'`
equal to `1` near the support of `ψ`. The reading `τ · ((Ψ g) ∘ e⁻¹)` of `Ψ g` in `e` is
`θ · (w ∘ κ)` for the reading `w = ψ · (g ∘ e'⁻¹)` of `g` in `e'`, the transition map
`κ = e' ∘ e⁻¹` and the cutoff `θ = τ · (ψ₁ ∘ κ)` (`OpenPartialHomeomorph.overlapCutoff`), which has
compact support in the source of `κ`. -/
theorem cutoffPushforwardSchwartz_mulLeft_ofReal_cutoffPullback_apply
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (τ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    {ψ₁ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)} (hψ₁ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ψ₁ x = 1)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (y : CoordinateSpace n) :
    e.cutoffPushforwardSchwartz he τ
        (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g) y =
      overlapCutoff he' he τ ψ₁ y • e'.cutoffPushforwardSchwartz he' ψ g (e.symm.trans e' y) := by
  rw [cutoffPushforwardSchwartz_apply, cutoffPushforwardSchwartz_apply, coe_trans,
    Function.comp_apply]
  by_cases hy : e.symm y ∈ e'.source
  · rw [overlapCutoff_apply_of_mem he' he τ ψ₁ hy, e'.left_inv hy]
    simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      ContMDiffMap.ofReal_apply, cutoffPullback_one_apply_of_mem he' _ hy]
    by_cases hψ : ψ (e' (e.symm y)) = 0
    · simp [hψ]
    · rw [hψ₁.self_of_nhdsSet _ (subset_tsupport _ hψ), mul_one, ← Complex.real_smul]
  · rw [overlapCutoff_apply he' he, cutoffPullback_apply_of_notMem he' _ _ hy]
    simp [cutoffPullback_apply_of_notMem he' _ _ hy]

/-- **Changing the chart of a reading, in an abstract norm.** Let `L` be a map out of
`𝓢(ℝⁿ, ℂ)` into a seminormed group in whose norm every localized change of variables
`u ↦ θ · (u ∘ κ)` is bounded, `ψ` a cutoff in a chart `e'`, with `Ψ` the smooth function `ψ ∘ e'`
on `M`, extended by `0`, and `τ` a cutoff in a chart `e`. There is a constant `C` such that for
every smooth `g` on `M`, the reading `τ · ((Ψ g) ∘ e⁻¹)` of `Ψ g` in `e` satisfies

`‖L (τ · ((Ψ g) ∘ e⁻¹))‖ ≤ C ‖L (ψ · (g ∘ e'⁻¹))‖`. -/
theorem exists_norm_cutoffPushforwardSchwartz_mulLeft_le {X G : Type*} [SeminormedAddCommGroup X]
    [FunLike G 𝓢(CoordinateSpace n, ℂ) X] (L : G)
    (hL : ∀ {κ : OpenPartialHomeomorph (CoordinateSpace n) (CoordinateSpace n)},
      ContDiffOn ℝ ∞ κ κ.source → ContDiffOn ℝ ∞ κ.symm κ.target →
      ∀ {θ : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ κ.source → ∃ C, ∀ u v : 𝓢(CoordinateSpace n, ℂ),
          (∀ x, v x = θ x • u (κ x)) → ‖L v‖ ≤ C * ‖L u‖)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (τ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖L (e.cutoffPushforwardSchwartz he τ
          (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g))‖ ≤
        C * ‖L (e'.cutoffPushforwardSchwartz he' ψ g)‖ := by
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e'.target, e'.open_target⟩) (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨hθ, hθc, hθs⟩ := overlapCutoff_spec he' he τ ψ₁
  obtain ⟨C, hC⟩ := hL (contDiffOn_symm_trans_of_mem_maximalAtlas he he')
    (fun _ hz ↦ (contDiffAt_symm_trans_symm_of_mem_maximalAtlas he he' hz).contDiffWithinAt)
    hθ hθc hθs
  exact ⟨C, fun g ↦ hC _ _
    (cutoffPushforwardSchwartz_mulLeft_ofReal_cutoffPullback_apply he he' τ ψ hψ₁ g)⟩

/-- **Changing the chart of a reading.** Let `ψ` be a cutoff in a chart `e'`, with `Ψ` the smooth
function `ψ ∘ e'` on `M`, extended by `0`, and `τ` a cutoff in a chart `e`. For every real `s`
and `1 < p < ∞` there is a constant `C` such that for every smooth `g` on `M`, the reading
`τ · ((Ψ g) ∘ e⁻¹)` of `Ψ g` in `e` satisfies

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{H^{s,p}} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{H^{s,p}}`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (τ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (s : ℝ) :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesselPotentialSpaceCLM s p (e.cutoffPushforwardSchwartz he τ
          (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s p (e'.cutoffPushforwardSchwartz he' ψ g)‖ :=
  exists_norm_cutoffPushforwardSchwartz_mulLeft_le _ (fun hκ hκ' _ hθ hθc hθs ↦
    BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc
      hθs hp hp_top s) he he' τ ψ

/-- **Changing the chart of a Besov reading.** Let `ψ` be a cutoff in a chart `e'`, with `Ψ` the
smooth function `ψ ∘ e'` on `M`, extended by `0`, and `τ` a cutoff in a chart `e`. For every real
`s` and all `1 ≤ p, q ≤ ∞` there is a constant `C` such that for every smooth `g` on `M`, the
reading `τ · ((Ψ g) ∘ e⁻¹)` of `Ψ g` in `e` satisfies

`‖τ · ((Ψ g) ∘ e⁻¹)‖_{B^s_{p,q}} ≤ C ‖ψ · (g ∘ e'⁻¹)‖_{B^s_{p,q}}`. -/
theorem exists_norm_toBesovSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (τ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] :
    ∃ C, ∀ g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q (e.cutoffPushforwardSchwartz he τ
          (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e'.cutoffPullback he' ψ 1)) g))‖ ≤
        C * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q (e'.cutoffPushforwardSchwartz he' ψ g)‖ :=
  exists_norm_cutoffPushforwardSchwartz_mulLeft_le _ (fun hκ hκ' _ hθ hθc hθs ↦
    BesovSpace.exists_norm_toBesovSpaceCLM_le_of_eq_smul_comp hκ hκ' hθ hθc hθs φ s p q) he he'
    τ ψ

omit [T2Space M] in
/-- **A reading is fixed by a Schwartz cutoff.** For a cutoff `φ` in a chart `e`, there is a
Schwartz function `χ`, independent of the function `u` on `M` and of `t`, such that multiplication
by `χ` fixes the reading `φ · (u ∘ e⁻¹)` in every `H^t`. (The proof takes `χ` equal to `1` near the
support of `φ`.) -/
theorem exists_smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ χ : 𝓢(CoordinateSpace n, ℂ), ∀ (t : ℝ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯),
      BesselPotentialSpace.smulLeftCLM t χ
          (SchwartzMap.toBesselPotentialSpaceCLM t 2 (e.cutoffPushforwardSchwartz he φ u)) =
        SchwartzMap.toBesselPotentialSpaceCLM t 2 (e.cutoffPushforwardSchwartz he φ u) := by
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨χ, hχ⟩ : ∃ χ : 𝓢(CoordinateSpace n, ℂ), ∀ y, χ y = θ y :=
    ⟨(θ.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp θ.contDiff), HasCompactSupport.toSchwartzMap_toFun _ _⟩
  refine ⟨χ, fun t u ↦ BesselPotentialSpace.ext ?_⟩
  rw [BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, cutoffPushforwardSchwartz_apply,
    hχ]
  by_cases hy : y ∈ tsupport φ
  · simp [hθ.self_of_nhdsSet y hy]
  · simp [image_eq_zero_of_notMem_tsupport hy]

omit [T2Space M] in
/-- **Rellich's theorem for chart readings.** Let `φⱼ` be cutoffs in charts `eⱼ` and `gⱼ u` smooth
functions on `M` depending on a parameter `u`. If the readings `φⱼ · ((gⱼ u) ∘ eⱼ⁻¹)` in `H^s` are
bounded by `Cⱼ N(u)` for a nonnegative `N`, then for `r < s` their readings
`(φⱼ · ((gⱼ u) ∘ eⱼ⁻¹))ⱼ` in `H^r`, over the `u` with `N(u) ≤ B`, form a set with compact closure:
in each chart they are bounded in `H^s` and fixed by multiplication by one Schwartz function, so
relatively compact in `H^r`
(`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`). -/
theorem isCompact_closure_image_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_of_norm_le
    {ν X : Type*} {e : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ j, e j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : ∀ j, 𝓓(⟨(e j).target, (e j).open_target⟩, ℝ))
    (g : ν → X → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {N : X → ℝ} (hN : ∀ u, 0 ≤ N u)
    {s : ℝ} (hC : ∀ j, ∃ C, ∀ u, ‖SchwartzMap.toBesselPotentialSpaceCLM s 2
      ((e j).cutoffPushforwardSchwartz (he j) (φ j) (g j u))‖ ≤ C * N u)
    {r : ℝ} (hrs : r < s) (B : ℝ) :
    IsCompact (closure ((fun u j ↦ SchwartzMap.toBesselPotentialSpaceCLM r 2
      ((e j).cutoffPushforwardSchwartz (he j) (φ j) (g j u))) '' {u | N u ≤ B})) := by
  choose C hC using hC
  -- The readings in `H^s` in the chart `eⱼ` are bounded.
  let S (j : ν) := (fun u ↦ SchwartzMap.toBesselPotentialSpaceCLM s 2
    ((e j).cutoffPushforwardSchwartz (he j) (φ j) (g j u))) '' {u | N u ≤ B}
  have hS (j : ν) : Bornology.IsBounded (S j) := by
    refine isBounded_iff_forall_norm_le.2 ⟨|C j| * B, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (hC j u).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (hN u)).trans
      (mul_le_mul_of_nonneg_left hu (abs_nonneg _)))
  -- They are all supported in the fixed compact set `supp φⱼ`, so Rellich's theorem applies.
  choose θ hθ using fun j ↦
    exists_smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz (he j) (φ j)
  have hK (j : ν) : IsCompact (closure (BesselPotentialSpace.inclusion hrs.le '' S j)) :=
    BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq hrs (hS j)
      (φ := θ j) (by rintro _ ⟨u, -, rfl⟩; exact hθ j _ _)
  refine (isCompact_univ_pi hK).of_isClosed_subset isClosed_closure
    (closure_minimal ?_ (isClosed_set_pi fun j _ ↦ isClosed_closure))
  rintro _ ⟨u, hu, rfl⟩ j -
  exact subset_closure
    ⟨_, ⟨u, hu, rfl⟩, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM _ _⟩

end TauCeti
