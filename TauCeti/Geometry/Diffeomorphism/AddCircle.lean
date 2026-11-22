/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
public import TauCeti.Geometry.Diffeomorphism.Topology
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Prod
import TauCeti.Topology.Instances.AddCircle.Lift
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.AddCircle
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Instances.AddCircle.Lift

/-!
# Straightening circle diffeomorphisms

A `C^n` map `f` of the circle `AddCircle T` has a continuous lift `F : ℝ → ℝ`, `f x = F x`, of
some degree `d`: `F (x + T) = F x + d * T`. Interpolating the lifts
`x ↦ (1 - t) * F x + t * (F 0 + d * x)` gives the straightening `AddCircle.straighten t f`, a
homotopy of `C^n` circle maps from `f` (at `t = 0`) to the affine map `θ ↦ f 0 + d • θ` (at
`t = 1`), which fixes the affine maps throughout. It does not depend on the choice of lift.

The point of this file is that straightening is **continuous** jointly in `t` and `f` for the weak
Whitney topology (`AddCircle.continuous_straighten`), although a lift is a global object which is
not determined by `f` near any single point. Near a fixed map `f₀`, every nearby `f` is uniformly
close to `f₀`, so a lift of `f` is a lift of `f₀` corrected by the small real lift of the pointwise
difference `θ ↦ f θ - f₀ θ`. This small lift is obtained by composing with a fixed smooth local
section of `ℝ → AddCircle T` near `0`, so near `f₀` the straightening is built from pointwise
operations and composition with fixed smooth maps, which are continuous
(`ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`,
`ContMDiffMap.continuous_comp_manifoldWeakWhitney`). The section is only `C^∞`, so the regularity
is `n ≤ ∞`.

For a diffeomorphism `f`, `n ≠ 0`, the degree is `d = ±1` and the derivative of `F` has the sign of
`d`, so each interpolating lift has nonvanishing derivative of the same sign and the straightened
maps for `t ∈ [0, 1]` are diffeomorphisms (`AddCircle.straightenDiffeomorph`): an isometry
`θ ↦ f 0 + d • θ` composed with a time slice of `AddCircle.diffeotopyOfLift`. This gives a
homotopy in `Diff(AddCircle T)` from the identity to a retraction onto the isometries
`θ ↦ a ± θ`, fixing the isometries throughout (`AddCircle.straighteningHomotopy`): the
diffeomorphism group of the circle deformation retracts onto its isometry group, a copy of `O(2)`.

## Main definitions

* `AddCircle.straighten t f`: the circle map with lift `x ↦ (1 - t) * F x + t * (F 0 + d * x)`.
* `AddCircle.straightenDiffeomorph hn t f`: for `t ∈ [0, 1]`, the same map for a diffeomorphism
  `f`, as a diffeomorphism.
* `AddCircle.straighteningHomotopy hn`: the homotopy in `Diff(AddCircle T)` from the identity to
  `f ↦ straightenDiffeomorph hn 1 f`.

## Main results

* `AddCircle.straighten_apply_coe`: the straightened map, computed from any continuous lift.
* `AddCircle.straighten_zero`, `AddCircle.straighten_one_apply`,
  `AddCircle.straighten_of_forall_eq_add_zsmul`: straightening starts at `f`, ends at the affine
  map `θ ↦ f 0 + d • θ`, and fixes affine maps.
* `AddCircle.continuous_straighten`, `AddCircle.continuous_straightenDiffeomorph`: straightening
  is continuous for the weak Whitney topology.
* `AddCircle.straightenDiffeomorph_one_apply`,
  `AddCircle.straightenDiffeomorph_of_forall_eq_add_zsmul`: the homotopy ends at the isometries
  and fixes them.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.1, for lifts of circle
  maps and the straightening of circle diffeomorphisms.
* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the weak Whitney topology.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]

/-! ### A smooth local section of the quotient map near zero -/

/-- A smooth real function on the circle which is a section of the quotient map `ℝ → AddCircle T`
near `0`: the chart at `0`, cut off by a smooth bump function. -/
private def sectionNearZero : AddCircle T → ℝ :=
  fun θ ↦ Classical.arbitrary (SmoothBumpFunction 𝓘(ℝ) (0 : AddCircle T)) θ •
    chartAt ℝ (0 : AddCircle T) θ

private theorem contMDiff_sectionNearZero :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (sectionNearZero (T := T)) :=
  (Classical.arbitrary (SmoothBumpFunction 𝓘(ℝ) (0 : AddCircle T))).contMDiff_smul
    contMDiffOn_chart

private theorem eventually_coe_sectionNearZero :
    ∀ᶠ θ in 𝓝 (0 : AddCircle T), ((sectionNearZero θ : ℝ) : AddCircle T) = θ := by
  filter_upwards [(Classical.arbitrary
      (SmoothBumpFunction 𝓘(ℝ) (0 : AddCircle T))).eventuallyEq_one,
    (chartAt ℝ (0 : AddCircle T)).open_source.mem_nhds (mem_chart_source ℝ 0)] with θ h₁ h₂
  rw [sectionNearZero, h₁, Pi.one_apply, one_smul]
  exact coe_apply_of_mem_atlas (chart_mem_atlas ℝ _) h₂

/-- There is a radius `δ > 0` below which `sectionNearZero` is a section of the quotient map. -/
private theorem exists_coe_sectionNearZero :
    ∃ δ > 0, ∀ θ : AddCircle T, ‖θ‖ < δ → ((sectionNearZero θ : ℝ) : AddCircle T) = θ := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (eventually_coe_sectionNearZero (T := T))
  exact ⟨δ, hδ, fun θ hθ ↦ h (by rwa [dist_zero_right])⟩

/-! ### The deviation of a circle map from its affine part -/

variable {n : ℕ∞}

/-- A circle map has a continuous lift of some degree `d`. -/
private theorem exists_lift (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯) :
    ∃ F : ℝ → ℝ, ∃ d : ℤ, Continuous F ∧ (∀ x : ℝ, f x = F x) ∧
      ∀ x, F (x + T) = F x + d * T := by
  obtain ⟨F, hF, hf⟩ := exists_continuous_lift (map_continuous f)
  obtain ⟨d, hd⟩ := exists_int_forall_add_period_eq_of_lift hF hf
  exact ⟨F, d, hF, hf, hd⟩

omit [Fact (0 < T)] in
/-- The deviation `x ↦ F x - F 0 - d * x` of a lift of degree `d` is periodic. -/
private theorem periodic_deviation {F : ℝ → ℝ} {d : ℤ} (hd : ∀ x, F (x + T) = F x + d * T) :
    Function.Periodic (fun x ↦ F x - F 0 - d * x) T := fun x ↦ by
  dsimp only
  rw [hd]
  ring

/-- The deviation of a `C^n` circle map `f` from its affine part: for a continuous lift `F` of `f`
of degree `d`, the periodic function `x ↦ F x - F 0 - d * x`, which does not depend on the lift
(`deviation_apply_coe`). -/
private def deviation (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯) :
    C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯ :=
  have h := (exists_lift f).choose_spec.choose_spec
  ⟨(periodic_deviation h.2.2).lift, (periodic_deviation h.2.2).contMDiff_lift
    (((contDiff_of_comp_coe_eq (funext h.2.1) h.1 f.contMDiff).sub contDiff_const).sub
      (contDiff_const.mul contDiff_id))⟩

/-- The deviation of a circle map, computed from any continuous lift `F` of degree `d`. -/
private theorem deviation_apply_coe (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯)
    {F : ℝ → ℝ} (hF : Continuous F) (hf : ∀ x : ℝ, f x = F x) {d : ℤ}
    (hd : ∀ x, F (x + T) = F x + d * T) (x : ℝ) :
    deviation f x = F x - F 0 - d * x := by
  -- Compare with the lift chosen in the definition.
  suffices key : ∀ (F₀ : ℝ → ℝ) (d₀ : ℤ), Continuous F₀ → (∀ x : ℝ, f x = F₀ x) →
      (∀ x, F₀ (x + T) = F₀ x + d₀ * T) → deviation f x = F₀ x - F₀ 0 - d₀ * x →
        deviation f x = F x - F 0 - d * x by
    obtain ⟨hF₀, hf₀, hd₀⟩ := (exists_lift f).choose_spec.choose_spec
    exact key _ _ hF₀ hf₀ hd₀ (by rw [deviation, ContMDiffMap.coeFn_mk, Function.Periodic.lift_coe])
  intro F₀ d₀ hF₀ hf₀ hd₀ hdev
  obtain ⟨c, hc⟩ := exists_forall_eq_add_of_lift (T := T) hF hF₀ fun x ↦ by rw [← hf, hf₀]
  -- The two lifts differ by a constant, so they have the same degree.
  have hdd : d = d₀ := by
    have h := hd 0
    rw [hc, hc, hd₀] at h
    exact_mod_cast mul_right_cancel₀ (Fact.out : 0 < T).ne' (by linarith : (d : ℝ) * T = d₀ * T)
  rw [hdev, hc, hc, hdd]
  ring

/-! ### The straightening homotopy of circle maps -/

/-- **Straightening a circle map.** For a `C^n` map `f` of the circle with a continuous lift `F` of
degree `d`, the circle map with lift `x ↦ (1 - t) * F x + t * (F 0 + d * x)`
(`AddCircle.straighten_apply_coe`). At `t = 0` it is `f`, and at `t = 1` it is the affine map
`θ ↦ f 0 + d • θ`, read through lifts. -/
def straighten (t : ℝ) (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯) :
    C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ :=
  ⟨fun θ ↦ f θ - ((t * deviation f θ : ℝ) : AddCircle T),
    f.contMDiff.sub ((contMDiff_coe T n).comp
      ((contDiff_const.mul contDiff_id).contMDiff.comp (deviation f).contMDiff))⟩

private theorem straighten_apply (t : ℝ) (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯)
    (θ : AddCircle T) : straighten t f θ = f θ - ((t * deviation f θ : ℝ) : AddCircle T) :=
  (rfl)

/-- The straightened circle map, computed from any continuous lift `F` of degree `d`. -/
theorem straighten_apply_coe (t : ℝ) (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯)
    {F : ℝ → ℝ} (hF : Continuous F) (hf : ∀ x : ℝ, f x = F x) {d : ℤ}
    (hd : ∀ x, F (x + T) = F x + d * T) (x : ℝ) :
    straighten t f x = (((1 - t) * F x + t * (F 0 + d * x) : ℝ) : AddCircle T) := by
  rw [straighten_apply, deviation_apply_coe f hF hf hd, hf, ← coe_sub]
  congr 1
  ring

/-- Straightening for time zero does nothing. -/
@[simp]
theorem straighten_zero (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯) : straighten 0 f = f :=
  ContMDiffMap.ext fun θ ↦ by simp [straighten_apply]

/-- At time one, straightening a circle map `f` gives the affine map `θ ↦ f 0 + d • θ`, where `d`
is the degree of a continuous lift of `f`. -/
theorem straighten_one_apply (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯) {F : ℝ → ℝ}
    (hF : Continuous F) (hf : ∀ x : ℝ, f x = F x) {d : ℤ} (hd : ∀ x, F (x + T) = F x + d * T)
    (θ : AddCircle T) : straighten 1 f θ = f 0 + d • θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [straighten_apply_coe 1 f hF hf hd, show f 0 = (F 0 : AddCircle T) from hf 0, ← coe_zsmul,
      ← coe_add, zsmul_eq_mul]
    congr 1
    ring

/-- Straightening fixes the affine circle maps `θ ↦ a + d • θ` at all times. -/
theorem straighten_of_forall_eq_add_zsmul (t : ℝ)
    {f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯} {a : AddCircle T} {d : ℤ}
    (hf : ∀ θ, f θ = a + d • θ) : straighten t f = f := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective a
  -- The affine function `x ↦ b + d * x` is a lift of `f` of degree `d`.
  have hF (x : ℝ) : f x = ((b + d * x : ℝ) : AddCircle T) := by
    rw [hf, coe_add, ← zsmul_eq_mul, coe_zsmul]
  refine ContMDiffMap.ext fun θ ↦ ?_
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [straighten_apply_coe t f (by fun_prop) hF (fun x ↦ by ring), hF]
    congr 1
    ring

/-- Near `f₀`, the deviation of `f` is that of `f₀` corrected by the local lift of the pointwise
difference `f - f₀`, normalized at `0`. -/
private theorem deviation_apply_eq_of_norm_sub_lt {δ : ℝ}
    (hδ : ∀ θ : AddCircle T, ‖θ‖ < δ → ((sectionNearZero θ : ℝ) : AddCircle T) = θ)
    {f f₀ : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯} (h : ∀ θ, ‖f θ - f₀ θ‖ < δ)
    (θ : AddCircle T) :
    deviation f θ =
      deviation f₀ θ + sectionNearZero (f θ - f₀ θ) - sectionNearZero (f 0 - f₀ 0) := by
  obtain ⟨F₀, d, hF₀, hf₀, hd⟩ := exists_lift f₀
  -- Correcting a lift of `f₀` by the local lift of `f - f₀` gives a lift of `f` of the same degree.
  set G : ℝ → ℝ := fun x ↦ F₀ x + sectionNearZero (f x - f₀ x)
  have hG : Continuous G := hF₀.add (contMDiff_sectionNearZero.continuous.comp
    (((map_continuous f).sub (map_continuous f₀)).comp continuous_quotient_mk'))
  have hg (x : ℝ) : f x = G x := by
    rw [coe_add, ← hf₀, hδ _ (h x), add_sub_cancel]
  have hGd (x : ℝ) : G (x + T) = G x + d * T := by
    simp only [G, hd, coe_add_period]
    ring
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [deviation_apply_coe f hG hg hGd, deviation_apply_coe f₀ hF₀ hf₀ hd]
    simp only [G, QuotientAddGroup.mk_zero]
    ring

/-- The deviation depends continuously on the circle map. -/
private theorem continuous_deviation :
    Continuous (deviation : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ →
      C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯) := by
  obtain ⟨δ, hδ, hsec⟩ := exists_coe_sectionNearZero (T := T)
  let μ : C^n⟮𝓘(ℝ).prod 𝓘(ℝ), AddCircle T × AddCircle T; 𝓘(ℝ), AddCircle T⟯ :=
    ⟨fun p ↦ p.1 - p.2, contMDiff_fst.sub contMDiff_snd⟩
  let σ : C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯ :=
    ⟨sectionNearZero, contMDiff_sectionNearZero.of_le (by exact_mod_cast le_top)⟩
  refine continuous_iff_continuousAt.2 fun f₀ ↦ ?_
  -- Near `f₀` the deviation is given by pointwise operations, composition and evaluation.
  have hdiff : Continuous fun f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦
      σ.comp (μ.comp (f.prodMk f₀)) :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk
      (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk
        (ContMDiffMap.continuous_prodMk_manifoldWeakWhitney.comp
          (continuous_id.prodMk continuous_const)))))
  have hconst : Continuous fun f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦
      (ContMDiffMap.const (sectionNearZero (f 0 - f₀ 0)) : C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯) :=
    ContMDiffMap.continuous_const_manifoldWeakWhitney.comp
      (contMDiff_sectionNearZero.continuous.comp
        ((ContMDiffMap.continuous_eval_const_manifoldWeakWhitney 0).sub continuous_const))
  refine (((continuous_const (y := deviation f₀)).add hdiff).sub hconst).continuousAt.congr ?_
  filter_upwards [ContMDiffMap.eventually_forall_dist_lt f₀ isCompact_univ continuous_const
    fun _ _ ↦ hδ] with f hf
  refine ContMDiffMap.ext fun θ ↦ ?_
  rw [deviation_apply_eq_of_norm_sub_lt hsec (fun θ ↦ by rw [← dist_eq_norm]; exact hf θ trivial)]
  rfl

/-- **Straightening is continuous** jointly in the time and the circle map, for the weak Whitney
topology. -/
theorem continuous_straighten :
    Continuous fun p : ℝ × C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦ straighten p.1 p.2 := by
  let μ : C^n⟮𝓘(ℝ).prod 𝓘(ℝ), AddCircle T × AddCircle T; 𝓘(ℝ), AddCircle T⟯ :=
    ⟨fun p ↦ p.1 - p.2, contMDiff_fst.sub contMDiff_snd⟩
  let q : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), AddCircle T⟯ := ⟨(↑), contMDiff_coe T n⟩
  have h : Continuous fun p : ℝ × C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦
      μ.comp (p.2.prodMk (q.comp (p.1 • deviation p.2))) :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk
      (ContMDiffMap.continuous_prodMk_manifoldWeakWhitney.comp (continuous_snd.prodMk
        (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk
          (continuous_fst.smul (continuous_deviation.comp continuous_snd)))))))
  exact h.congr fun p ↦ ContMDiffMap.ext fun θ ↦ (rfl)

/-! ### Straightening circle diffeomorphisms -/

/-- The affine diffeomorphism `θ ↦ a + e • θ` of the circle, for `e = ±1`. -/
private def affineDiffeomorph (a : AddCircle T) (e : ℤ) (he : e * e = 1) :
    AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T where
  toFun θ := a + e • θ
  invFun θ := e • (θ - a)
  left_inv θ := by simp [smul_smul, he]
  right_inv θ := by simp [smul_smul, he]
  contMDiff_toFun := contMDiff_const.add (TauCeti.contMDiff_zsmul e)
  contMDiff_invFun := (TauCeti.contMDiff_zsmul e).comp (contMDiff_id.sub contMDiff_const)

private theorem affineDiffeomorph_apply (a : AddCircle T) (e : ℤ) (he : e * e = 1)
    (θ : AddCircle T) : affineDiffeomorph (n := n) a e he θ = a + e • θ :=
  (rfl)

/-- For `0 ≤ t ≤ 1`, the straightening of a circle diffeomorphism is again a diffeomorphism: it is
the affine map `θ ↦ f 0 + d • θ` composed with a time slice of the interpolating diffeotopy
`AddCircle.diffeotopyOfLift`. -/
private theorem exists_diffeomorph_coe_eq_straighten (hn : n ≠ 0)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ g : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T, ⇑g = straighten t f.toContMDiffMap := by
  have hn' : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast hn
  -- Find the time `u` at which the interpolation weight of `diffeotopyOfLift` is `1 - t`.
  obtain ⟨u, hut⟩ : ∃ u : unitInterval, Real.sin (Real.pi * u / 2) ^ 2 = 1 - t := by
    obtain ⟨u, hu, hut⟩ := intermediate_value_Icc zero_le_one
      (f := fun u : ℝ ↦ Real.sin (Real.pi * u / 2) ^ 2) (by fun_prop)
      (show 1 - t ∈ _ by
        simp only [mul_zero, zero_div, Real.sin_zero, mul_one, Real.sin_pi_div_two]
        constructor <;> norm_num <;> linarith [ht.1, ht.2])
    exact ⟨⟨u, hu⟩, hut⟩
  obtain ⟨F, hF, hf, hlift⟩ := f.exists_addCircle_lift hn'
  -- `G = d * (F - F 0)` is a lift of degree one with positive derivative.
  obtain ⟨d, hd2, hper, hpos⟩ : ∃ d : ℤ, d * d = 1 ∧ (∀ x, F (x + T) = F x + d * T) ∧
      ∀ x, 0 < deriv (fun y ↦ d * (F y - F 0)) x := by
    have hderiv (c : ℝ) (x : ℝ) : deriv (fun y ↦ c * (F y - F 0)) x = c * deriv F x := by
      rw [deriv_const_mul _ ((hF.differentiable hn').differentiableAt.sub_const _), deriv_sub_const]
    rcases hlift with ⟨hper, hpos⟩ | ⟨hper, hneg⟩
    · exact ⟨1, by norm_num, fun x ↦ by simp [hper], fun x ↦ by simpa [hderiv] using hpos x⟩
    · exact ⟨-1, by norm_num, fun x ↦ by simp [hper, sub_eq_add_neg],
        fun x ↦ by simpa [hderiv] using hneg x⟩
  have hGper (x : ℝ) : d * (F (x + T) - F 0) = d * (F x - F 0) + T := by
    rw [hper]
    linear_combination (T : ℝ) * (by exact_mod_cast hd2 : (d : ℝ) * d = 1)
  refine ⟨((diffeotopyOfLift (contDiff_const.mul (hF.sub contDiff_const)) hn' hGper hpos).timeSlice
    u).trans (affineDiffeomorph (f 0) d hd2), funext fun θ ↦ ?_⟩
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [straighten_apply_coe t f.toContMDiffMap hF.continuous hf hper]
    have hf0 : f 0 = (F 0 : AddCircle T) := hf 0
    rw [Diffeomorph.coe_trans, Function.comp_apply, TauCeti.Diffeotopy.timeSlice_apply,
      diffeotopyOfLift_apply_coe, hut, affineDiffeomorph_apply, hf0, ← coe_zsmul, ← coe_add,
      zsmul_eq_mul]
    congr 1
    linear_combination (1 - t) * (F x - F 0) * (by exact_mod_cast hd2 : (d : ℝ) * d = 1)

/-- **Straightening a circle diffeomorphism.** For a `C^n` diffeomorphism `f` of the circle,
`n ≠ 0`, and `t ∈ [0, 1]`, the diffeomorphism whose underlying map is `AddCircle.straighten t f`:
for a continuous lift `F` of `f` of degree `d = ±1`, it has the lift
`x ↦ (1 - t) * F x + t * (F 0 + d * x)` (`AddCircle.straightenDiffeomorph_apply_coe`). -/
def straightenDiffeomorph (hn : n ≠ 0) (t : unitInterval)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T :=
  (exists_diffeomorph_coe_eq_straighten hn f t.property).choose

/-- The straightened diffeomorphism is the straightened circle map. -/
@[simp]
theorem coe_straightenDiffeomorph (hn : n ≠ 0) (t : unitInterval)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) :
    ⇑(straightenDiffeomorph hn t f) = straighten t f.toContMDiffMap :=
  (exists_diffeomorph_coe_eq_straighten hn f t.property).choose_spec

/-- The straightened diffeomorphism, computed from any continuous lift `F` of degree `d`. -/
theorem straightenDiffeomorph_apply_coe (hn : n ≠ 0) (t : unitInterval)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) {F : ℝ → ℝ} (hF : Continuous F)
    (hf : ∀ x : ℝ, f x = F x) {d : ℤ} (hd : ∀ x, F (x + T) = F x + d * T) (x : ℝ) :
    straightenDiffeomorph hn t f x =
      (((1 - t) * F x + t * (F 0 + d * x) : ℝ) : AddCircle T) := by
  rw [coe_straightenDiffeomorph]
  exact straighten_apply_coe t f.toContMDiffMap hF hf hd x

/-- At time zero the straightening of a circle diffeomorphism is the diffeomorphism itself. -/
@[simp]
theorem straightenDiffeomorph_zero (hn : n ≠ 0) (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) :
    straightenDiffeomorph hn 0 f = f :=
  Diffeomorph.ext fun θ ↦ by
    rw [coe_straightenDiffeomorph, Set.Icc.coe_zero, straighten_zero]
    rfl

/-- At time one the straightening of a circle diffeomorphism `f` is the isometry
`θ ↦ f 0 + d • θ`, where `d = ±1` is the degree of a continuous lift of `f`. -/
theorem straightenDiffeomorph_one_apply (hn : n ≠ 0)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) {F : ℝ → ℝ} (hF : Continuous F)
    (hf : ∀ x : ℝ, f x = F x) {d : ℤ} (hd : ∀ x, F (x + T) = F x + d * T) (θ : AddCircle T) :
    straightenDiffeomorph hn 1 f θ = f 0 + d • θ := by
  rw [coe_straightenDiffeomorph, Set.Icc.coe_one]
  exact straighten_one_apply f.toContMDiffMap hF hf hd θ

/-- Straightening fixes the isometries `θ ↦ a + d • θ` of the circle. -/
theorem straightenDiffeomorph_of_forall_eq_add_zsmul (hn : n ≠ 0) (t : unitInterval)
    {f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T} {a : AddCircle T} {d : ℤ}
    (hf : ∀ θ, f θ = a + d • θ) : straightenDiffeomorph hn t f = f :=
  Diffeomorph.ext fun θ ↦ by
    rw [coe_straightenDiffeomorph,
      straighten_of_forall_eq_add_zsmul (f := f.toContMDiffMap) t hf]
    rfl

/-- **Straightening is continuous** on `[0, 1] × Diff(AddCircle T)`, for the weak Whitney
topology. -/
theorem continuous_straightenDiffeomorph (hn : n ≠ 0) :
    Continuous fun p : unitInterval × (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) ↦
      straightenDiffeomorph hn p.1 p.2 := by
  refine Diffeomorph.continuous_weakWhitney_iff.2 ?_
  refine (continuous_straighten.comp (continuous_subtypeVal.prodMap
    Diffeomorph.continuous_toContMDiffMap)).congr fun p ↦ ContMDiffMap.ext fun θ ↦ ?_
  exact (congrFun (coe_straightenDiffeomorph hn p.1 p.2) θ).symm

/-- **The diffeomorphism group of the circle deformation retracts onto its isometries.** The
straightening homotopy from the identity of `Diff(AddCircle T)` to the retraction
`f ↦ (θ ↦ f 0 + d • θ)` (`AddCircle.straightenDiffeomorph_one_apply`), which fixes the isometries
throughout (`AddCircle.straightenDiffeomorph_of_forall_eq_add_zsmul`). -/
def straighteningHomotopy (hn : n ≠ 0) :
    ContinuousMap.Homotopy (ContinuousMap.id (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T))
      ⟨straightenDiffeomorph hn 1, (continuous_straightenDiffeomorph hn).comp
        (continuous_const.prodMk continuous_id)⟩ where
  toFun p := straightenDiffeomorph hn p.1 p.2
  continuous_toFun := continuous_straightenDiffeomorph hn
  map_zero_left := straightenDiffeomorph_zero hn
  map_one_left _ := rfl

/-- The straightening homotopy at time `t` is the straightened diffeomorphism. -/
@[simp]
theorem straighteningHomotopy_apply (hn : n ≠ 0)
    (p : unitInterval × (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T)) :
    straighteningHomotopy hn p = straightenDiffeomorph hn p.1 p.2 :=
  (rfl)

end AddCircle
