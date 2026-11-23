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
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
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
section of `ℝ → AddCircle T` near `0` (`AddCircle.exists_contMDiff_coe_eq_of_norm_lt`), so near
`f₀` the straightening is built from pointwise operations and composition with fixed smooth maps,
which are continuous
(`ContMDiffMap.continuous_sub_manifoldWeakWhitney_of_lieAddGroup`,
`ContMDiffMap.continuous_comp_manifoldWeakWhitney`). The section is only `C^∞`, so the regularity
is `n ≤ ∞`.

For a diffeomorphism `f`, `n ≠ 0`, the degree is `d = ±1` and the derivative of `F` has the sign of
`d`, so each interpolating lift has nonvanishing derivative of the same sign and the straightened
maps for `t ∈ [0, 1]` are diffeomorphisms (`AddCircle.straightenDiffeomorph`): an isometry
`θ ↦ f 0 + d • θ` (`TauCeti.Lie.addZSMulDiffeomorph`) composed with a time slice of
`AddCircle.diffeotopyOfLift`. This gives a homotopy in `Diff(AddCircle T)` relative to the
isometries `θ ↦ a ± θ`, from the identity to a retraction onto them
(`AddCircle.straighteningRetraction`, `AddCircle.straighteningHomotopy`): the diffeomorphism group
of the circle deformation retracts onto its isometry group, a copy of `O(2)`.

## Main definitions

* `AddCircle.straighten t f`: the circle map with lift `x ↦ (1 - t) * F x + t * (F 0 + d * x)`.
* `AddCircle.straightenDiffeomorph hn t f`: for `t ∈ [0, 1]`, the same map for a diffeomorphism
  `f`, as a diffeomorphism.
* `AddCircle.isometryDiffeomorphs T n`: the isometries `θ ↦ a ± θ` among the diffeomorphisms.
* `AddCircle.straighteningRetraction hn`: the continuous retraction
  `f ↦ straightenDiffeomorph hn 1 f` of `Diff(AddCircle T)` onto the isometries.
* `AddCircle.straighteningHomotopy hn`: the homotopy in `Diff(AddCircle T)` relative to the
  isometries, from the identity to the straightening retraction.

## Main results

* `AddCircle.straighten_apply_coe`: the straightened map, computed from any continuous lift.
* `AddCircle.straighten_zero`, `AddCircle.straighten_one_apply`,
  `AddCircle.straighten_of_forall_eq_add_zsmul`: straightening starts at `f`, ends at the affine
  map `θ ↦ f 0 + d • θ`, and fixes affine maps.
* `AddCircle.continuous_straighten`, `AddCircle.continuous_straightenDiffeomorph`: straightening
  is continuous for the weak Whitney topology.
* `AddCircle.straightenDiffeomorph_one_apply`,
  `AddCircle.exists_straightenDiffeomorph_one_eq_add_zsmul`,
  `AddCircle.straightenDiffeomorph_of_forall_eq_add_zsmul`: the homotopy ends at the isometries
  and fixes them; `AddCircle.straighteningRetraction_coe`: the retraction fixes the isometries.

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

/-! ### The deviation of a circle map from its affine part -/

variable {n : ℕ∞}

/-- The deviation of a `C^n` circle map `f` from its affine part: for a continuous lift `F` of `f`
of degree `d`, the periodic function `x ↦ F x - d * x - F 0`, which does not depend on the lift
(`deviation_apply_coe`). -/
private def deviation (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯) :
    C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯ :=
  have hlift := exists_continuous_lift_add_period_eq (map_continuous f)
  have h := hlift.choose_spec.choose_spec
  have hper := (periodic_sub_int_mul_of_lift h.2.2).comp (· - hlift.choose 0)
  ⟨hper.lift, hper.contMDiff_lift
    (((contDiff_of_comp_coe_eq (funext h.2.1) h.1 f.contMDiff).sub
      (contDiff_const.mul contDiff_id)).sub contDiff_const)⟩

/-- The deviation of a circle map, computed from any continuous lift `F` of degree `d`. -/
private theorem deviation_apply_coe (f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯)
    {F : ℝ → ℝ} (hF : Continuous F) (hf : ∀ x : ℝ, f x = F x) {d : ℤ}
    (hd : ∀ x, F (x + T) = F x + d * T) (x : ℝ) :
    deviation f x = F x - d * x - F 0 := by
  obtain ⟨hF₀, hf₀, hd₀⟩ :=
    (exists_continuous_lift_add_period_eq (map_continuous f)).choose_spec.choose_spec
  -- `F` and the lift chosen in the definition have the same degree and differ by a constant.
  obtain ⟨hdd, c, hc⟩ := eq_and_exists_forall_eq_add_of_lift (Fact.out : 0 < T).ne' hF hF₀
    (fun x ↦ by rw [← hf, hf₀]) hd hd₀
  rw [deviation, ContMDiffMap.coeFn_mk, Function.Periodic.lift_coe, Function.comp_apply, hc, hc,
    hdd]
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
    have hf0 : f 0 = (F 0 : AddCircle T) := by rw [← coe_zero, hf]
    rw [straighten_apply_coe 1 f hF hf hd, hf0, ← coe_zsmul, ← coe_add, zsmul_eq_mul]
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

/-- Near `f₀`, the deviation of `f` is that of `f₀` corrected by the local lift `σ` of the
pointwise difference `f - f₀`, normalized at `0`. -/
private theorem deviation_apply_eq_of_norm_sub_lt {σ : AddCircle T → ℝ} (hσ : Continuous σ)
    {δ : ℝ} (hδ : ∀ θ : AddCircle T, ‖θ‖ < δ → ((σ θ : ℝ) : AddCircle T) = θ)
    {f f₀ : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯} (h : ∀ θ, ‖f θ - f₀ θ‖ < δ)
    (θ : AddCircle T) :
    deviation f θ = deviation f₀ θ + σ (f θ - f₀ θ) - σ (f 0 - f₀ 0) := by
  obtain ⟨F₀, d, hF₀, hf₀, hd⟩ := exists_continuous_lift_add_period_eq (map_continuous f₀)
  -- Correcting a lift of `f₀` by the local lift of `f - f₀` gives a lift of `f` of the same degree.
  set G : ℝ → ℝ := fun x ↦ F₀ x + σ (f x - f₀ x)
  have hG : Continuous G := hF₀.add (hσ.comp
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
  obtain ⟨s, hs, δ, hδ, hsec⟩ := exists_contMDiff_coe_eq_of_norm_lt (T := T)
  let σ : C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯ := ⟨s, hs.of_le (by exact_mod_cast le_top)⟩
  have hσ : ⇑σ = s := ContMDiffMap.coeFn_mk _ _
  refine continuous_iff_continuousAt.2 fun f₀ ↦ ?_
  -- Near `f₀` the deviation is given by pointwise operations, composition and evaluation.
  have hdiff : Continuous fun f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦ σ.comp (f - f₀) :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk
      (ContMDiffMap.continuous_sub_manifoldWeakWhitney_of_lieAddGroup.comp
        (continuous_id.prodMk continuous_const)))
  have hconst : Continuous fun f : C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦
      (ContMDiffMap.const (s (f 0 - f₀ 0)) : C^n⟮𝓘(ℝ), AddCircle T; ℝ⟯) :=
    ContMDiffMap.continuous_const_manifoldWeakWhitney.comp
      (hs.continuous.comp
        ((ContMDiffMap.continuous_eval_const_manifoldWeakWhitney 0).sub continuous_const))
  refine (((continuous_const (y := deviation f₀)).add hdiff).sub hconst).continuousAt.congr ?_
  filter_upwards [ContMDiffMap.eventually_forall_dist_lt f₀ isCompact_univ continuous_const
    fun _ _ ↦ hδ] with f hf
  refine ContMDiffMap.ext fun θ ↦ ?_
  rw [deviation_apply_eq_of_norm_sub_lt hs.continuous hsec
    (fun θ ↦ by rw [← dist_eq_norm]; exact hf θ trivial)]
  simp [ContMDiffMap.comp_apply, hσ]

/-- **Straightening is continuous** jointly in the time and the circle map, for the weak Whitney
topology. -/
theorem continuous_straighten :
    Continuous fun p : ℝ × C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦ straighten p.1 p.2 := by
  let q : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), AddCircle T⟯ := ⟨(↑), contMDiff_coe T n⟩
  have hq : ⇑q = ((↑) : ℝ → AddCircle T) := ContMDiffMap.coeFn_mk _ _
  have h : Continuous fun p : ℝ × C^n⟮𝓘(ℝ), AddCircle T; 𝓘(ℝ), AddCircle T⟯ ↦
      p.2 - q.comp (p.1 • deviation p.2) :=
    ContMDiffMap.continuous_sub_manifoldWeakWhitney_of_lieAddGroup.comp (continuous_snd.prodMk
      (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk
        (continuous_fst.smul (continuous_deviation.comp continuous_snd)))))
  refine h.congr fun p ↦ ContMDiffMap.ext fun θ ↦ ?_
  simp [ContMDiffMap.comp_apply, straighten_apply, hq]

/-! ### Straightening circle diffeomorphisms -/

/-- For `0 ≤ t ≤ 1`, the straightening of a circle diffeomorphism is again a diffeomorphism: it is
the affine map `θ ↦ f 0 + d • θ` composed with a time slice of the interpolating diffeotopy
`AddCircle.diffeotopyOfLift`. -/
private theorem exists_diffeomorph_coe_eq_straighten (hn : n ≠ 0)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ g : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T, ⇑g = straighten t f.toContMDiffMap := by
  have hn' : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast hn
  obtain ⟨F, hF, hf, d, hd2, hper, hsign⟩ := f.exists_addCircle_lift_degree hn'
  -- `G = d * (F - F 0)` is a lift of degree one with positive derivative.
  have hpos (x : ℝ) : 0 < deriv (fun y ↦ d * (F y - F 0)) x := by
    rw [deriv_const_mul _ ((hF.differentiable hn').differentiableAt.sub_const _),
      deriv_sub_const]
    exact hsign x
  have hGper (x : ℝ) : d * (F (x + T) - F 0) = d * (F x - F 0) + T := by
    rw [hper]
    linear_combination (T : ℝ) * (by exact_mod_cast hd2 : (d : ℝ) * d = 1)
  have hG : ContDiff ℝ n fun y ↦ d * (F y - F 0) := contDiff_const.mul (hF.sub contDiff_const)
  -- The time slice of `diffeotopyOfLift` with interpolation weight `1 - t`.
  obtain ⟨u, hu⟩ := exists_diffeotopyOfLift_apply_coe_eq hG hn' hGper hpos
    (s := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨((diffeotopyOfLift hG hn' hGper hpos).timeSlice u).trans
    (TauCeti.Lie.addZSMulDiffeomorph 𝓘(ℝ) n (f 0) d hd2), funext fun θ ↦ ?_⟩
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [straighten_apply_coe t f.toContMDiffMap hF.continuous hf hper]
    have hf0 : f 0 = (F 0 : AddCircle T) := by rw [← coe_zero, hf]
    simp only [Diffeomorph.coe_trans, Function.comp_apply, TauCeti.Diffeotopy.timeSlice_apply, hu,
      TauCeti.Lie.addZSMulDiffeomorph_apply, hf0]
    rw [← coe_zsmul, ← coe_add, zsmul_eq_mul]
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

/-- The underlying `C^n` map of the straightened diffeomorphism is the straightened circle map. -/
@[simp]
theorem toContMDiffMap_straightenDiffeomorph (hn : n ≠ 0) (t : unitInterval)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) :
    (straightenDiffeomorph hn t f).toContMDiffMap = straighten t f.toContMDiffMap :=
  ContMDiffMap.ext fun θ ↦ by
    rw [Diffeomorph.coe_toContMDiffMap, coe_straightenDiffeomorph]

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
    rw [coe_straightenDiffeomorph, Set.Icc.coe_zero, straighten_zero,
      Diffeomorph.coe_toContMDiffMap]

/-- At time one the straightening of a circle diffeomorphism `f` is the isometry
`θ ↦ f 0 + d • θ`, where `d = ±1` is the degree of a continuous lift of `f`. -/
theorem straightenDiffeomorph_one_apply (hn : n ≠ 0)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) {F : ℝ → ℝ} (hF : Continuous F)
    (hf : ∀ x : ℝ, f x = F x) {d : ℤ} (hd : ∀ x, F (x + T) = F x + d * T) (θ : AddCircle T) :
    straightenDiffeomorph hn 1 f θ = f 0 + d • θ := by
  rw [coe_straightenDiffeomorph, Set.Icc.coe_one]
  exact straighten_one_apply f.toContMDiffMap hF hf hd θ

/-- At time one the straightening of a circle diffeomorphism is an isometry `θ ↦ a + e • θ`,
`e = ±1`. -/
theorem exists_straightenDiffeomorph_one_eq_add_zsmul (hn : n ≠ 0)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) :
    ∃ (a : AddCircle T) (e : ℤ), e * e = 1 ∧ ∀ θ, straightenDiffeomorph hn 1 f θ = a + e • θ := by
  obtain ⟨F, hF, hf, d, hd2, hper, -⟩ := f.exists_addCircle_lift_degree (by exact_mod_cast hn)
  exact ⟨f 0, d, hd2, straightenDiffeomorph_one_apply hn f hF.continuous hf hper⟩

/-- Straightening fixes the isometries `θ ↦ a + d • θ` of the circle. -/
theorem straightenDiffeomorph_of_forall_eq_add_zsmul (hn : n ≠ 0) (t : unitInterval)
    {f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T} {a : AddCircle T} {d : ℤ}
    (hf : ∀ θ, f θ = a + d • θ) : straightenDiffeomorph hn t f = f :=
  Diffeomorph.ext fun θ ↦ by
    rw [coe_straightenDiffeomorph,
      straighten_of_forall_eq_add_zsmul (f := f.toContMDiffMap) t hf,
      Diffeomorph.coe_toContMDiffMap]

/-- **Straightening is continuous** on `[0, 1] × Diff(AddCircle T)`, for the weak Whitney
topology. -/
theorem continuous_straightenDiffeomorph (hn : n ≠ 0) :
    Continuous fun p : unitInterval × (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) ↦
      straightenDiffeomorph hn p.1 p.2 := by
  refine Diffeomorph.continuous_weakWhitney_iff.2 ?_
  simp only [toContMDiffMap_straightenDiffeomorph]
  exact continuous_straighten.comp
    (continuous_subtypeVal.prodMap Diffeomorph.continuous_toContMDiffMap)

variable (T n) in
/-- The isometries `θ ↦ a + e • θ`, `e = ±1`, of the circle, as a set of `C^n` diffeomorphisms. -/
def isometryDiffeomorphs : Set (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) :=
  {f | ∃ (a : AddCircle T) (e : ℤ), e * e = 1 ∧ ∀ θ, f θ = a + e • θ}

/-- A circle diffeomorphism is one of the isometries exactly when it is `θ ↦ a + e • θ` for some
`a` and some `e = ±1`. -/
@[simp]
theorem mem_isometryDiffeomorphs {f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T} :
    f ∈ isometryDiffeomorphs T n ↔
      ∃ (a : AddCircle T) (e : ℤ), e * e = 1 ∧ ∀ θ, f θ = a + e • θ :=
  Iff.rfl

/-- **The straightening retraction** of `Diff(AddCircle T)` onto its isometries: a circle
diffeomorphism `f` goes to the isometry `θ ↦ f 0 + d • θ`, where `d = ±1` is the degree of a
continuous lift of `f` (`AddCircle.straightenDiffeomorph_one_apply`). -/
def straighteningRetraction (hn : n ≠ 0) :
    C(AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T, isometryDiffeomorphs T n) where
  toFun f := ⟨straightenDiffeomorph hn 1 f,
    mem_isometryDiffeomorphs.2 (exists_straightenDiffeomorph_one_eq_add_zsmul hn f)⟩
  continuous_toFun := ((continuous_straightenDiffeomorph hn).comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

@[simp]
theorem coe_straighteningRetraction_apply (hn : n ≠ 0)
    (f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) :
    (straighteningRetraction hn f : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) =
      straightenDiffeomorph hn 1 f :=
  (rfl)

/-- The straightening retraction is a retraction: it is a left inverse of the inclusion of the
isometries. -/
@[simp]
theorem straighteningRetraction_coe (hn : n ≠ 0) (f : isometryDiffeomorphs T n) :
    straighteningRetraction hn f = f := by
  obtain ⟨_, _, _, hf⟩ := mem_isometryDiffeomorphs.1 f.property
  exact Subtype.ext (straightenDiffeomorph_of_forall_eq_add_zsmul hn 1 hf)

/-- **The diffeomorphism group of the circle deformation retracts onto its isometries.** The
straightening homotopy relative to the isometries `AddCircle.isometryDiffeomorphs`, from the
identity of `Diff(AddCircle T)` to the inclusion of the isometries composed with the
straightening retraction `AddCircle.straighteningRetraction`. -/
def straighteningHomotopy (hn : n ≠ 0) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T))
      ((ContinuousMap.subtypeVal _).comp (straighteningRetraction hn))
      (isometryDiffeomorphs T n) where
  toFun p := straightenDiffeomorph hn p.1 p.2
  continuous_toFun := continuous_straightenDiffeomorph hn
  map_zero_left := straightenDiffeomorph_zero hn
  map_one_left f := (coe_straighteningRetraction_apply hn f).symm
  prop' t f hf := by
    obtain ⟨_, _, _, hf⟩ := mem_isometryDiffeomorphs.1 hf
    exact straightenDiffeomorph_of_forall_eq_add_zsmul hn t hf

/-- The straightening homotopy at time `t` is the straightened diffeomorphism. -/
@[simp]
theorem straighteningHomotopy_apply (hn : n ≠ 0)
    (p : unitInterval × (AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T)) :
    straighteningHomotopy hn p = straightenDiffeomorph hn p.1 p.2 :=
  (rfl)

end AddCircle
