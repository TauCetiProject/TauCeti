/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.AddCircle
public import TauCeti.Geometry.Manifold.Morse.AddCircle
public import TauCeti.Geometry.Manifold.Morse.Persistence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Algebra.AddCircle

/-!
# Morse and non-Morse functions on the circle

On the circle `S¹ = AddCircle (2π)`, explicit trigonometric functions test the two halves of the
genericity of Morse functions: the Morse functions are dense, but not every function is Morse; and
they are open in the `C²` topology, but not in the `C¹` topology.

* **A degenerate function approximated by Morse functions.** For `ε : ℝ` let
  `f_ε(θ) = cos³ θ + ε cos θ` (`TauCeti.circleCubicCos`). Its derivative is
  `f_ε'(θ) = -sin θ (3 cos² θ + ε)` and its second derivative
  `f_ε''(θ) = cos θ (6 sin² θ - 3 cos² θ - ε)`. For `ε = 0` the points `θ = ±π/2`, where
  `cos θ = 0`, are critical with `f_0'' = 0`, so `f_0` is not Morse
  (`TauCeti.mem_criticalPoints_circleCubicCos_zero_and_not_isManifoldNondegenerateCriticalPoint`).
  In fact `f_ε` is Morse exactly when `ε ≠ 0` and `ε ≠ -3` (`TauCeti.isMorse_circleCubicCos_iff`);
  at `ε = -3` the point `θ = 0` degenerates. So `f_ε` is Morse for every small `ε ≠ 0`
  (`TauCeti.eventually_isMorse_circleCubicCos`), while the family depends continuously on `ε` in
  the `C^∞` topology (`TauCeti.continuous_circleCubicCos`): the degenerate function `f_0` is a
  limit of Morse functions.
* **Openness in `C²`.** The cosine `θ ↦ cos θ` (`TauCeti.circleCos`) is Morse
  (`TauCeti.isMorse_circleCos`), so by the openness theorem
  `TauCeti.eventually_forall_isManifoldNondegenerateCriticalPoint` every function `C²`-close to it
  has only nondegenerate critical points
  (`TauCeti.eventually_nhds_circleCos_forall_isManifoldNondegenerateCriticalPoint`). Explicitly,
  this holds for `cos + h` as soon as `h'² + h''² < 1` everywhere
  (`TauCeti.isManifoldNondegenerateCriticalPoint_circleCos_add_lift`): at a critical point
  `sin θ = h'(θ)`, and `cos θ = h''(θ)` would force `1 = h'² + h''²`.
* **Failure of openness in `C¹`.** The functions
  `g_N(θ) = cos θ + (1 - cos (N θ)) / N²` (`TauCeti.circleCosRipple`) satisfy
  `|g_N - cos| ≤ 2 / N²` and `|g_N' - cos'| ≤ 1 / N`, so they tend to the cosine in the `C¹`
  topology (`TauCeti.tendsto_circleCosRipple`). But `g_N'(0) = 0` and
  `g_N''(0) = -1 + 1 = 0`, so each `g_N`, `N ≠ 0`, has a degenerate critical point at `0`
  (`TauCeti.zero_mem_criticalPoints_circleCosRipple_and_not_isManifoldNondegenerateCriticalPoint`).
  Hence no `C¹` neighbourhood of the cosine consists of functions with only nondegenerate critical
  points (`TauCeti.not_eventually_nhds_circleCos_forall_isManifoldNondegenerateCriticalPoint`):
  openness of the Morse condition needs the `C^k` topology with `k ≥ 2`.

The cosine itself is the height function of the circle. Its critical points are its maximum `0`
and its minimum `π` (`TauCeti.mem_criticalPoints_circleCos_iff`), labelled as critical points by
`TauCeti.circleCosMaxCrit` and `TauCeti.circleCosMinCrit`, and a point at which it takes the value
`a ∈ [-1, 1]` is `± arccos a` (`TauCeti.eq_or_eq_neg_arccos_of_circleCos_eq`).

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 6, §1, where Morse functions are shown to form a dense open set in `C^r` for `r ≥ 2`.
-/

public section

open Real Function Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

local instance morseExamplesCircleTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-! ### The cosine -/

/-- The cosine `θ ↦ cos θ` on the circle `AddCircle (2π)`. -/
noncomputable def circleCos : AddCircle (2 * π) → ℝ :=
  cos_periodic.lift

@[simp]
theorem circleCos_coe (θ : ℝ) : circleCos θ = cos θ :=
  cos_periodic.lift_coe θ

/-- The cosine on the circle is analytic. -/
theorem contMDiff_circleCos {n : ℕ∞ω} : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n circleCos :=
  cos_periodic.contMDiff_lift contDiff_cos

/-- **The cosine is a Morse function on the circle**, with critical points `0` and `π`. -/
theorem isMorse_circleCos : IsMorse 𝓘(ℝ) circleCos := by
  rw [circleCos, cos_periodic.isMorse_lift_iff contDiff_cos]
  intro θ hθ
  rw [Real.deriv_cos, neg_eq_zero] at hθ
  rw [show iteratedDeriv 2 cos θ = -cos θ by simp, neg_ne_zero]
  intro hc
  simpa [hθ, hc] using sin_sq_add_cos_sq θ

/-! ### Values, level sets and critical points of the cosine -/

/-- A point of the circle at which the cosine takes the value `a ∈ [-1, 1]` is `± arccos a`. -/
theorem eq_or_eq_neg_arccos_of_circleCos_eq {x : AddCircle (2 * π)} {a : ℝ}
    (hx : circleCos x = a) (ha₁ : -1 ≤ a) (ha₂ : a ≤ 1) :
    x = (Real.arccos a : ℝ) ∨ x = (-Real.arccos a : ℝ) :=
  Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 (hx.trans (Real.cos_arccos ha₁ ha₂).symm)

/-- The cosine takes its maximum `1` at `0`. -/
@[simp]
theorem circleCos_zero : circleCos 0 = 1 :=
  Real.Angle.cos_zero

/-- The cosine takes its minimum `-1` at `π`. -/
theorem circleCos_pi : circleCos ((π : ℝ) : AddCircle (2 * π)) = -1 :=
  Real.Angle.cos_coe_pi

/-- **The critical points of the cosine on the circle** are its maximum `0` and its minimum `π`. -/
theorem mem_criticalPoints_circleCos_iff {x : AddCircle (2 * π)} :
    x ∈ criticalPoints 𝓘(ℝ) circleCos ↔ x = 0 ∨ x = (π : ℝ) := by
  have hlift : circleCos = Real.cos_periodic.lift := funext fun x ↦ by
    induction x using QuotientAddGroup.induction_on with | H φ =>
    rw [circleCos_coe, Real.cos_periodic.lift_coe]
  induction x using QuotientAddGroup.induction_on with | H φ =>
  rw [hlift]
  refine (Real.cos_periodic.coe_mem_criticalPoints_lift_iff φ).trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Real.deriv_cos, neg_eq_zero, Real.sin_eq_zero_iff] at h
    obtain ⟨n, rfl⟩ := h
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · exact .inl <| (AddCircle.coe_eq_coe_iff_exists_zsmul.2
        ⟨m, by push_cast; rw [zsmul_eq_mul]; ring⟩).trans
        (AddCircle.coe_zero ..)
    · exact .inr <| AddCircle.coe_eq_coe_iff_exists_zsmul.2
        ⟨m, by push_cast; rw [zsmul_eq_mul]; ring⟩
  · rw [Real.deriv_cos, neg_eq_zero]
    rcases h with h | h
    · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq_zero_iff φ |>.1 h)
      rw [← hk, zsmul_eq_mul, show (k : ℝ) * (2 * π) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring,
        Real.sin_int_mul_pi]
    · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq_iff_sub_mem.1 h)
      rw [show φ = ((2 * k + 1 : ℤ) : ℝ) * π by push_cast; rw [zsmul_eq_mul] at hk; linarith,
        Real.sin_int_mul_pi]

-- The bodies are exposed so that objects indexed by these critical points, such as spaces of
-- trajectories between them, are by definition those of the points `0` and `π` of the circle.
/-- The maximum `0` of the cosine, as a critical point. -/
@[expose] noncomputable def circleCosMaxCrit : criticalPoints 𝓘(ℝ) circleCos :=
  ⟨0, mem_criticalPoints_circleCos_iff.2 (.inl rfl)⟩

/-- The minimum `π` of the cosine, as a critical point. -/
@[expose] noncomputable def circleCosMinCrit : criticalPoints 𝓘(ℝ) circleCos :=
  ⟨(π : ℝ), mem_criticalPoints_circleCos_iff.2 (.inr rfl)⟩

@[simp]
theorem coe_circleCosMaxCrit : (circleCosMaxCrit : AddCircle (2 * π)) = 0 :=
  (rfl)

@[simp]
theorem coe_circleCosMinCrit : (circleCosMinCrit : AddCircle (2 * π)) = (π : ℝ) :=
  (rfl)

/-- The cosine has finitely many critical points, its maximum and its minimum. -/
noncomputable instance : Fintype (criticalPoints 𝓘(ℝ) circleCos) :=
  ((Set.toFinite ({0, ((π : ℝ) : AddCircle (2 * π))} : Set (AddCircle (2 * π)))).subset fun _ hx ↦
    mem_criticalPoints_circleCos_iff.1 hx).fintype

/-- The cosine has exactly two critical points, its maximum and its minimum. -/
theorem eq_circleCosMaxCrit_or_eq_circleCosMinCrit (x : criticalPoints 𝓘(ℝ) circleCos) :
    x = circleCosMaxCrit ∨ x = circleCosMinCrit :=
  (mem_criticalPoints_circleCos_iff.1 x.property).imp Subtype.ext Subtype.ext

theorem circleCosMaxCrit_ne_circleCosMinCrit : circleCosMaxCrit ≠ circleCosMinCrit :=
  fun h ↦ Real.Angle.pi_ne_zero (congrArg Subtype.val h).symm

/-! ### Stability of the cosine -/

/-- **Explicit `C²` stability of the cosine.** If `h` is a `2π`-periodic `C²` function with
`h'(θ)² + h''(θ)² < 1` for every `θ`, then every critical point of `cos + h` on the circle is
nondegenerate. -/
theorem isManifoldNondegenerateCriticalPoint_circleCos_add_lift {h : ℝ → ℝ}
    (hh : Periodic h (2 * π)) (h₂ : ContDiff ℝ 2 h)
    (hb : ∀ θ, deriv h θ ^ 2 + iteratedDeriv 2 h θ ^ 2 < 1) {x : AddCircle (2 * π)}
    (hx : x ∈ criticalPoints 𝓘(ℝ) (circleCos + hh.lift)) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) (circleCos + hh.lift) x := by
  have hper := cos_periodic.add hh
  have heq : circleCos + hh.lift = hper.lift := by
    funext y
    induction y using QuotientAddGroup.induction_on
    simp only [Pi.add_apply, circleCos_coe, hh.lift_coe, hper.lift_coe]
  have hderiv (θ : ℝ) : deriv (cos + h) θ = -sin θ + deriv h θ := by
    simpa using iteratedDeriv_add (n := 1) contDiff_cos.contDiffAt
      (h₂.of_le one_le_two).contDiffAt (x := θ)
  have hderiv₂ (θ : ℝ) : iteratedDeriv 2 (cos + h) θ = -cos θ + iteratedDeriv 2 h θ := by
    simp [iteratedDeriv_add contDiff_cos.contDiffAt h₂.contDiffAt]
  rw [heq] at hx ⊢
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hθ := (hper.coe_mem_criticalPoints_lift_iff θ).1 hx
  refine (hper.isManifoldNondegenerateCriticalPoint_lift_coe_iff
    (contDiff_cos.add h₂).contDiffAt).2 ⟨hθ, ?_⟩
  rw [hderiv] at hθ
  rw [hderiv₂]
  intro hc
  -- At a degenerate critical point `h' = sin` and `h'' = cos`, so `h'² + h''² = 1`.
  have h₁ : deriv h θ = sin θ := by linarith
  have hcos₂ : iteratedDeriv 2 h θ = cos θ := by linarith
  have := hb θ
  rw [h₁, hcos₂, sin_sq_add_cos_sq] at this
  exact lt_irrefl _ this

/-- **Openness of the Morse condition near the cosine in `C^n`, `n ≥ 2`.** Every `C^n` function
close enough to the cosine in the weak Whitney `C^n` topology has only nondegenerate critical
points. -/
theorem eventually_nhds_circleCos_forall_isManifoldNondegenerateCriticalPoint {n : ℕ∞ω}
    (hn : 2 ≤ n) :
    ∀ᶠ g : C^n⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ in 𝓝 ⟨circleCos, contMDiff_circleCos⟩,
      ∀ x ∈ criticalPoints 𝓘(ℝ) g, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) g x := by
  have h := (isMorseOn_iff_criticalPoints.1 (isMorseOn_univ.2 isMorse_circleCos)).2
  simpa using eventually_forall_isManifoldNondegenerateCriticalPoint
    (f := ⟨circleCos, contMDiff_circleCos⟩) hn isCompact_univ h

/-! ### The cubic family `cos³ θ + ε cos θ` -/

private theorem periodic_cubicCos (ε : ℝ) :
    Periodic (fun θ ↦ cos θ ^ 3 + ε * cos θ) (2 * π) :=
  fun θ ↦ by simp only [cos_add_two_pi]

/-- The function `θ ↦ cos³ θ + ε cos θ` on the circle `AddCircle (2π)`. -/
noncomputable def circleCubicCos (ε : ℝ) : AddCircle (2 * π) → ℝ :=
  (periodic_cubicCos ε).lift

@[simp]
theorem circleCubicCos_coe (ε θ : ℝ) : circleCubicCos ε θ = cos θ ^ 3 + ε * cos θ :=
  (periodic_cubicCos ε).lift_coe θ

private theorem circleCubicCos_eq (ε : ℝ) : circleCubicCos ε = (periodic_cubicCos ε).lift :=
  rfl

private theorem contDiff_cubicCos (ε : ℝ) {n : ℕ∞ω} :
    ContDiff ℝ n fun θ ↦ cos θ ^ 3 + ε * cos θ :=
  (contDiff_cos.pow 3).add (contDiff_const.mul contDiff_cos)

/-- The functions `θ ↦ cos³ θ + ε cos θ` on the circle are analytic. -/
theorem contMDiff_circleCubicCos (ε : ℝ) {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) n (circleCubicCos ε) :=
  (circleCubicCos_eq ε) ▸ (periodic_cubicCos ε).contMDiff_lift (contDiff_cubicCos ε)

private theorem deriv_cubicCos (ε : ℝ) :
    deriv (fun θ ↦ cos θ ^ 3 + ε * cos θ) = fun θ ↦ -(sin θ * (3 * cos θ ^ 2 + ε)) := by
  funext θ
  refine HasDerivAt.deriv ?_
  convert ((hasDerivAt_cos θ).fun_pow 3).fun_add ((hasDerivAt_cos θ).const_mul ε) using 1
  norm_num
  ring

private theorem iteratedDeriv_two_cubicCos (ε θ : ℝ) :
    iteratedDeriv 2 (fun θ ↦ cos θ ^ 3 + ε * cos θ) θ =
      cos θ * (6 * sin θ ^ 2 - 3 * cos θ ^ 2 - ε) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cubicCos]
  refine HasDerivAt.deriv ?_
  convert ((hasDerivAt_sin θ).fun_mul
    ((((hasDerivAt_cos θ).fun_pow 2).const_mul 3).add_const ε)).fun_neg using 1
  norm_num
  ring

/-- The class of `θ` is a critical point of `cos³ + ε cos` exactly when
`sin θ (3 cos² θ + ε) = 0`. -/
theorem coe_mem_criticalPoints_circleCubicCos_iff (ε θ : ℝ) :
    (θ : AddCircle (2 * π)) ∈ criticalPoints 𝓘(ℝ) (circleCubicCos ε) ↔
      sin θ * (3 * cos θ ^ 2 + ε) = 0 := by
  rw [circleCubicCos_eq, (periodic_cubicCos ε).coe_mem_criticalPoints_lift_iff, deriv_cubicCos,
    neg_eq_zero]

/-- The class of `θ` is a nondegenerate critical point of `cos³ + ε cos` exactly when
`sin θ (3 cos² θ + ε) = 0` and the second derivative `cos θ (6 sin² θ - 3 cos² θ - ε)` does not
vanish. -/
theorem isManifoldNondegenerateCriticalPoint_circleCubicCos_coe_iff (ε θ : ℝ) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) (circleCubicCos ε) (θ : AddCircle (2 * π)) ↔
      sin θ * (3 * cos θ ^ 2 + ε) = 0 ∧ cos θ * (6 * sin θ ^ 2 - 3 * cos θ ^ 2 - ε) ≠ 0 := by
  rw [circleCubicCos_eq, (periodic_cubicCos ε).isManifoldNondegenerateCriticalPoint_lift_coe_iff
    (contDiff_cubicCos ε).contDiffAt, deriv_cubicCos, neg_eq_zero, iteratedDeriv_two_cubicCos]

/-- **`cos³` is not a Morse function on the circle.** The points `θ` with `cos θ = 0`, namely
`θ = ±π/2`, are degenerate critical points of `θ ↦ cos³ θ`. -/
theorem mem_criticalPoints_circleCubicCos_zero_and_not_isManifoldNondegenerateCriticalPoint
    {θ : ℝ} (hθ : cos θ = 0) :
    (θ : AddCircle (2 * π)) ∈ criticalPoints 𝓘(ℝ) (circleCubicCos 0) ∧
      ¬ IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) (circleCubicCos 0) θ := by
  rw [coe_mem_criticalPoints_circleCubicCos_iff,
    isManifoldNondegenerateCriticalPoint_circleCubicCos_coe_iff]
  simp [hθ]

/-- **The Morse functions of the cubic family.** The function `θ ↦ cos³ θ + ε cos θ` on the circle
is a Morse function exactly when `ε ≠ 0` and `ε ≠ -3`. -/
theorem isMorse_circleCubicCos_iff {ε : ℝ} :
    IsMorse 𝓘(ℝ) (circleCubicCos ε) ↔ ε ≠ 0 ∧ ε ≠ -3 := by
  rw [circleCubicCos_eq, (periodic_cubicCos ε).isMorse_lift_iff (contDiff_cubicCos ε),
    deriv_cubicCos]
  simp only [neg_eq_zero, iteratedDeriv_two_cubicCos]
  refine ⟨fun H ↦ ⟨fun hε ↦ ?_, fun hε ↦ ?_⟩, fun ⟨h₀, h₃⟩ θ hθ hc ↦ ?_⟩
  · -- For `ε = 0`, the point `π / 2` is degenerate.
    exact H (π / 2) (by simp [hε]) (by simp [hε])
  · -- For `ε = -3`, the point `0` is degenerate.
    exact H 0 (by simp) (by norm_num [hε])
  · -- A degenerate critical point forces `ε = 0` or `ε = -3`.
    have hs := sin_sq_add_cos_sq θ
    rcases mul_eq_zero.1 hθ with hs₀ | hε
    · rcases mul_eq_zero.1 hc with hc₀ | hc₁
      · simp [hs₀, hc₀] at hs
      · rw [hs₀] at hc₁
        have hc₂ : cos θ ^ 2 = 1 := by nlinarith
        exact h₃ (by linarith)
    · rcases mul_eq_zero.1 hc with hc₀ | hc₁
      · exact h₀ (by rw [hc₀] at hε; linarith)
      · exact h₃ (by linarith)

/-- The function `θ ↦ cos³ θ + ε cos θ` on the circle is a Morse function for every small
`ε ≠ 0`. -/
theorem eventually_isMorse_circleCubicCos :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), IsMorse 𝓘(ℝ) (circleCubicCos ε) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds ((isOpen_ne : IsOpen {ε : ℝ | ε ≠ -3}).mem_nhds (by norm_num))]
    with ε h₀ h₃
  exact isMorse_circleCubicCos_iff.2 ⟨h₀, h₃⟩

/-- **The cubic family is continuous in `C^∞`.** The functions `θ ↦ cos³ θ + ε cos θ` depend
continuously on `ε` in the weak Whitney `C^∞` topology. In particular the degenerate function
`cos³` is the limit of the Morse functions `cos³ + ε cos`, `ε → 0`. -/
theorem continuous_circleCubicCos :
    Continuous (Y := C^∞⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯) fun ε : ℝ ↦
      ⟨circleCubicCos ε, contMDiff_circleCubicCos ε⟩ := by
  refine continuous_iff_continuousAt.2 fun ε₀ ↦
    ContMDiffMap.tendsto_addCircle_of_norm_iteratedDeriv_sub_le periodic_cubicCos
      (periodic_cubicCos ε₀) (contDiff_cubicCos ·) (contDiff_cubicCos ε₀) (b := fun _ ε ↦ |ε - ε₀|)
      (fun _ _ ↦ by simpa using (continuous_sub_right ε₀).abs.tendsto ε₀)
      fun m _ ↦ .of_forall fun ε θ ↦ ?_
  have hsub : ((fun θ ↦ cos θ ^ 3 + ε * cos θ) - fun θ ↦ cos θ ^ 3 + ε₀ * cos θ) =
      fun θ ↦ (ε - ε₀) * cos θ := by
    funext θ
    simp only [Pi.sub_apply]
    ring
  rw [hsub, iteratedDeriv_const_mul _ contDiff_cos.contDiffAt, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_iteratedDeriv_cos_le_one m θ)

/-! ### A `C¹`-small perturbation of the cosine with a degenerate critical point -/

private theorem periodic_cosRipple (N : ℕ) :
    Periodic (fun θ ↦ cos θ + (1 - cos (N * θ)) / N ^ 2) (2 * π) := fun θ ↦ by
  simp only [cos_add_two_pi, mul_add, cos_add_nat_mul_two_pi]

/-- The function `θ ↦ cos θ + (1 - cos (N θ)) / N²` on the circle `AddCircle (2π)`. For `N ≠ 0`,
it differs from the cosine by at most `2 / N²`, and its derivative from that of the cosine by at
most `1 / N`, but its second derivative at `0` vanishes. -/
noncomputable def circleCosRipple (N : ℕ) : AddCircle (2 * π) → ℝ :=
  (periodic_cosRipple N).lift

@[simp]
theorem circleCosRipple_coe (N : ℕ) (θ : ℝ) :
    circleCosRipple N θ = cos θ + (1 - cos (N * θ)) / N ^ 2 :=
  (periodic_cosRipple N).lift_coe θ

private theorem circleCosRipple_eq (N : ℕ) : circleCosRipple N = (periodic_cosRipple N).lift :=
  rfl

private theorem contDiff_cosRipple (N : ℕ) {n : ℕ∞ω} :
    ContDiff ℝ n fun θ ↦ cos θ + (1 - cos (N * θ)) / N ^ 2 :=
  contDiff_cos.add
    ((contDiff_const.sub (contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const _)

/-- The functions `θ ↦ cos θ + (1 - cos (N θ)) / N²` on the circle are analytic. -/
theorem contMDiff_circleCosRipple (N : ℕ) {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) n (circleCosRipple N) :=
  (circleCosRipple_eq N) ▸ (periodic_cosRipple N).contMDiff_lift (contDiff_cosRipple N)

private theorem hasDerivAt_rippleTerm (N : ℕ) (θ : ℝ) :
    HasDerivAt (fun θ ↦ (1 - cos (N * θ)) / N ^ 2) (N * sin (N * θ) / N ^ 2) θ := by
  convert ((((hasDerivAt_id' θ).const_mul (N : ℝ)).cos.const_sub 1).div_const
    ((N : ℝ) ^ 2)) using 1
  ring

private theorem deriv_cosRipple (N : ℕ) :
    deriv (fun θ ↦ cos θ + (1 - cos (N * θ)) / N ^ 2) =
      fun θ ↦ -sin θ + N * sin (N * θ) / N ^ 2 :=
  funext fun θ ↦ ((hasDerivAt_cos θ).add (hasDerivAt_rippleTerm N θ)).deriv

private theorem iteratedDeriv_two_cosRipple (N : ℕ) (θ : ℝ) :
    iteratedDeriv 2 (fun θ ↦ cos θ + (1 - cos (N * θ)) / N ^ 2) θ =
      -cos θ + N ^ 2 * cos (N * θ) / N ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cosRipple]
  refine HasDerivAt.deriv ?_
  convert (hasDerivAt_sin θ).fun_neg.fun_add
    (((((hasDerivAt_id' θ).const_mul (N : ℝ)).sin).const_mul (N : ℝ)).div_const ((N : ℝ) ^ 2))
    using 1
  ring

/-- **A degenerate critical point `C¹`-close to the cosine.** For `N ≠ 0`, the point `0` is a
degenerate critical point of `θ ↦ cos θ + (1 - cos (N θ)) / N²`. -/
theorem zero_mem_criticalPoints_circleCosRipple_and_not_isManifoldNondegenerateCriticalPoint
    {N : ℕ} (hN : N ≠ 0) :
    (0 : AddCircle (2 * π)) ∈ criticalPoints 𝓘(ℝ) (circleCosRipple N) ∧
      ¬ IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) (circleCosRipple N) 0 := by
  have hN' : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.2 hN)
  rw [← QuotientAddGroup.mk_zero, circleCosRipple_eq,
    (periodic_cosRipple N).coe_mem_criticalPoints_lift_iff,
    (periodic_cosRipple N).isManifoldNondegenerateCriticalPoint_lift_coe_iff
      (contDiff_cosRipple N).contDiffAt, deriv_cosRipple, iteratedDeriv_two_cosRipple]
  simp [hN']

/-- **The perturbations converge to the cosine in `C¹`.** The functions
`θ ↦ cos θ + (1 - cos (N θ)) / N²` tend to the cosine in the weak Whitney `C¹` topology as
`N → ∞`. -/
theorem tendsto_circleCosRipple :
    Tendsto (β := C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯)
      (fun N : ℕ ↦ ⟨circleCosRipple N, contMDiff_circleCosRipple N⟩)
      atTop (𝓝 ⟨circleCos, contMDiff_circleCos⟩) := by
  refine ContMDiffMap.tendsto_addCircle_of_norm_iteratedDeriv_sub_le periodic_cosRipple
    cos_periodic (contDiff_cosRipple ·) contDiff_cos (b := fun _ N ↦ 2 / N)
    (fun _ _ ↦ tendsto_const_div_atTop_nhds_zero_nat 2)
    fun m hm ↦ eventually_ne_atTop 0 |>.mono fun N hN θ ↦ ?_
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hN)
  have hsub : ((fun θ ↦ cos θ + (1 - cos (N * θ)) / N ^ 2) - cos) =
      fun θ ↦ (1 - cos (N * θ)) / N ^ 2 := by
    funext θ
    simp only [Pi.sub_apply]
    ring
  rw [hsub, Real.norm_eq_abs]
  have hm' : m ≤ 1 := by exact_mod_cast hm
  interval_cases m
  · -- The perturbation itself is at most `2 / N² ≤ 2 / N`.
    rw [iteratedDeriv_zero, abs_div, abs_of_pos (pow_pos hNpos 2), div_le_div_iff₀
      (pow_pos hNpos 2) hNpos]
    have h₁ : |1 - cos (N * θ)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [neg_one_le_cos (N * θ), cos_le_one (N * θ)]
    nlinarith
  · -- Its derivative `sin (N θ) / N` is at most `1 / N ≤ 2 / N`.
    rw [iteratedDeriv_one, (hasDerivAt_rippleTerm N θ).deriv, abs_div,
      abs_of_pos (pow_pos hNpos 2), abs_mul, abs_of_pos hNpos, div_le_div_iff₀
      (pow_pos hNpos 2) hNpos]
    have h₁ := abs_sin_le_one (N * θ)
    nlinarith

/-- **The Morse condition is not open in `C¹`.** Every neighbourhood of the cosine in the weak
Whitney `C¹` topology contains a function with a degenerate critical point. -/
theorem not_eventually_nhds_circleCos_forall_isManifoldNondegenerateCriticalPoint :
    ¬ ∀ᶠ g : C^1⟮𝓘(ℝ), AddCircle (2 * π); 𝓘(ℝ), ℝ⟯ in 𝓝 ⟨circleCos, contMDiff_circleCos⟩,
      ∀ x ∈ criticalPoints 𝓘(ℝ) g, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ) g x := by
  intro h
  obtain ⟨N, hg, hN⟩ :=
    ((tendsto_circleCosRipple.eventually h).and (eventually_ne_atTop 0)).exists
  obtain ⟨hcrit, hdeg⟩ :=
    zero_mem_criticalPoints_circleCosRipple_and_not_isManifoldNondegenerateCriticalPoint hN
  exact hdeg (hg 0 hcrit)

end TauCeti
