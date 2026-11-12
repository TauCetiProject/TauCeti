/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
import TauCeti.Geometry.Manifold.SmoothApprox

/-!
# Smooth representatives of the raw caps of a smooth loop

A raw cap of a loop `γ` based at `x` (`TauCeti.Floer.RawCap γ`) is a homotopy class of continuous
discs bounding `γ`: a path `s ↦ D_s` in the loop space from `γ` to the constant loop, up to
homotopy relative to its endpoints. The action `∫ D^* ω + ∫ H dt` of a capped orbit is an
integral over a smooth disc. This file shows that every raw cap of a smooth loop has a smooth
representative, so that such integrals can be evaluated on every raw cap.

Let `M` be a Hausdorff boundaryless manifold and `γ` the restriction to `[0, 1]` of a smooth
`1`-periodic map `g : ℝ → M`. Then every raw cap `D` of `γ` is the class of the path
`s ↦ u (s, ·)` for a smooth map `u : ℝ × ℝ → M` which is a cap of `g` in the sense of
`TauCeti.IsLoopCylinder`: `1`-periodic in `t`, equal to `g` along `s = 0` and to `x` along `s = 1`
(`TauCeti.Floer.RawCap.exists_contMDiff_isLoopCylinder`). Its seam `t = 0` stays at `x`, since
`s ↦ u (s, ·)` is a path of based loops. The target need not be compact.

The proof smooths a continuous representative relative to a closed set, by the relative Whitney
approximation theorem (`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`).
A continuous disc is not smooth anywhere a priori, so it is first precomposed with a continuous
self-map of the square, homotopic to the identity through maps preserving its boundary
conditions. This reparametrization `G` is smooth on a neighbourhood of the complement `S` of the
open square `(1/4, 3/4)²` within the strip `ℝ × [0, 1]`:

* for `s ≤ 1/3` it stays at the loop `γ`, reparametrized by the smooth maps
  `t ↦ t + c (χ(3t - 1) - t)` of `[0, 1]` fixing `0` and `1`, `χ` the smooth transition function,
  with `c` rising smoothly from `0` to `1`; so there `G (s, t) = g (…)` is a smooth function of
  `(s, t)`;
* for `c = 1` the reparametrization is locally constant near `t = 0` and `t = 1`, so the rest of
  the disc is run with its loops collapsed near the seam, where `G = x`;
* for `s ≥ 2/3` the disc has reached its centre, and `G = x`.

The approximation `u₀` agrees with `G` on `S`, and `u (s, t) = u₀ (s, fract t)` is smooth and
`1`-periodic, since near the seam lines `t ∈ ℤ` it equals the smooth periodic map `G`.

## Main results

* `TauCeti.Floer.RawCap.exists_contMDiff_isLoopCylinder`: every raw cap of a smooth loop is
  represented by a smooth periodic cap.
* `TauCeti.exists_isCap_of_homotopic`: a smooth null-homotopic loop has a smooth cap.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.26
  (relative Whitney approximation).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (capped loops and their action).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology Topology.Homotopy

namespace TauCeti.Floer.RawCap

/-! ### The reparametrization of the square -/

/-- The weight `c = χ(6 s - 1)` of the slide near `s = 0`: `0` for `s ≤ 1/6` and `1` for
`s ≥ 1/3`. -/
private def slideWeight (s : ℝ) : ℝ :=
  Real.smoothTransition (6 * s - 1)

/-- The reparametrization `t ↦ t + c (χ(3t - 1) - t)` of the unit interval. For `c = 1` it is
`0` on `[0, 1/3]` and `1` on `[2/3, 1]`. -/
private def seamCollapse (c t : ℝ) : ℝ :=
  t + c * (Real.smoothTransition (3 * t - 1) - t)

/-- The radial coordinate `s ↦ 3 s - 1`, clamped to the unit interval. -/
private def radial (s : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one (3 * s - 1)

private theorem contDiff_slideWeight : ContDiff ℝ ∞ slideWeight :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem continuous_slideWeight : Continuous slideWeight :=
  contDiff_slideWeight.continuous

private theorem continuous_seamCollapse : Continuous fun p : ℝ × ℝ ↦ seamCollapse p.1 p.2 := by
  unfold seamCollapse
  have := Real.smoothTransition.continuous
  fun_prop

private theorem contDiff_seamCollapse : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ seamCollapse p.1 p.2 :=
  contDiff_snd.add (contDiff_fst.mul ((Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_snd).sub contDiff_const)).sub contDiff_snd))

private theorem slideWeight_of_le {s : ℝ} (hs : s ≤ 1 / 6) : slideWeight s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem slideWeight_of_ge {s : ℝ} (hs : 1 / 3 ≤ s) : slideWeight s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem slideWeight_mem (s : ℝ) : slideWeight s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem radial_of_le {s : ℝ} (hs : s ≤ 1 / 3) : radial s = 0 :=
  projIcc_of_le_left _ (by linarith)

private theorem radial_of_ge {s : ℝ} (hs : 2 / 3 ≤ s) : radial s = 1 :=
  projIcc_of_right_le _ (by linarith)

private theorem seamCollapse_zero_left (t : ℝ) : seamCollapse 0 t = t := by
  simp [seamCollapse]

private theorem seamCollapse_zero_right (c : ℝ) : seamCollapse c 0 = 0 := by
  rw [seamCollapse, Real.smoothTransition.zero_of_nonpos (by norm_num)]
  ring

private theorem seamCollapse_one_right (c : ℝ) : seamCollapse c 1 = 1 := by
  rw [seamCollapse, Real.smoothTransition.one_of_one_le (by norm_num)]
  ring

/-- Near `t = 0` the reparametrization is the dilation `t ↦ (1 - c) t`. -/
private theorem seamCollapse_of_le (c : ℝ) {t : ℝ} (ht : t ≤ 1 / 3) :
    seamCollapse c t = (1 - c) * t := by
  rw [seamCollapse, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

/-- Near `t = 1` the reparametrization is the dilation `t ↦ 1 + (1 - c) (t - 1)`. -/
private theorem seamCollapse_of_ge (c : ℝ) {t : ℝ} (ht : 2 / 3 ≤ t) :
    seamCollapse c t = 1 + (1 - c) * (t - 1) := by
  rw [seamCollapse, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/-- For `0 ≤ c ≤ 1` the reparametrization maps the unit interval to itself. -/
private theorem seamCollapse_mem {c t : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    seamCollapse c t ∈ Icc (0 : ℝ) 1 := by
  have h₀ := Real.smoothTransition.nonneg (3 * t - 1)
  have h₁ := Real.smoothTransition.le_one (3 * t - 1)
  have e : seamCollapse c t = (1 - c) * t + c * Real.smoothTransition (3 * t - 1) := by
    rw [seamCollapse]
    ring
  rw [e]
  constructor <;> nlinarith [hc.1, hc.2, ht.1, ht.2]

/-! ### Loops of the disc -/

variable {M : Type*} [TopologicalSpace M] {x : M} {γ : Ω M x}

/-- Two paths of based loops from `γ` to the constant loop are homotopic if a continuous family
`Φ τ` of maps of the square joins them through maps that are `γ` along `s = 0` and `x` along the
three other sides. -/
private theorem homotopic_of_continuous {P₀ P₁ : Path γ (Path.refl x)}
    (Φ : unitInterval × unitInterval × unitInterval → M)
    (hΦ : Continuous Φ) (h₀ : ∀ s t, Φ (0, s, t) = P₀ s t) (h₁ : ∀ s t, Φ (1, s, t) = P₁ s t)
    (hl : ∀ τ t, Φ (τ, 0, t) = γ t) (hr : ∀ τ t, Φ (τ, 1, t) = x)
    (hb : ∀ τ s, Φ (τ, s, 0) = x) (ht : ∀ τ s, Φ (τ, s, 1) = x) : P₀.Homotopic P₁ := by
  refine ⟨{
    toFun := fun q ↦ (⟨⟨fun t ↦ Φ (q.1, q.2, t), by fun_prop⟩, hb q.1 q.2, ht q.1 q.2⟩ :
      Path x x)
    continuous_toFun := Path.continuous_uncurry_iff.1 (hΦ.comp (by fun_prop))
    map_zero_left := fun s ↦ Path.ext (funext fun t ↦ h₀ s t)
    map_one_left := fun s ↦ Path.ext (funext fun t ↦ h₁ s t)
    prop' := fun τ s hs ↦ ?_ }⟩
  rcases hs with rfl | hs
  · exact Path.ext (funext fun t ↦ by simpa [P₀.source] using hl τ t)
  · rw [mem_singleton_iff] at hs
    subst hs
    exact Path.ext (funext fun t ↦ by simpa [P₀.target] using hr τ t)

/-- The path of based loops `s ↦ f (s, ·)` of a continuous map `f` of the plane that is `γ` along
`s = 0` and `x` along the three other sides of the unit square. -/
private def squarePath (f : ℝ × ℝ → M) (hf : Continuous f)
    (hl : ∀ t : unitInterval, f (0, t) = γ t) (hr : ∀ t : unitInterval, f (1, t) = x)
    (hb : ∀ s : unitInterval, f (s, 0) = x) (ht : ∀ s : unitInterval, f (s, 1) = x) :
    Path γ (Path.refl x) where
  toFun s := ⟨⟨fun t ↦ f (s, t), by fun_prop⟩, hb s, ht s⟩
  continuous_toFun := Path.continuous_uncurry_iff.1 (hf.comp (by fun_prop))
  source' := Path.ext (funext fun t ↦ by simpa using hl t)
  target' := Path.ext (funext fun t ↦ by simpa using hr t)

private theorem squarePath_apply {f : ℝ × ℝ → M} {hf : Continuous f}
    {hl : ∀ t : unitInterval, f (0, t) = γ t} {hr : ∀ t : unitInterval, f (1, t) = x}
    {hb : ∀ s : unitInterval, f (s, 0) = x} {ht : ∀ s : unitInterval, f (s, 1) = x}
    (s t : unitInterval) : squarePath f hf hl hr hb ht s t = f (s, t) :=
  (rfl)

/-- The reparametrized disc of a path of loops `P`, extended `1`-periodically in `t`. -/
private def reparamDisc (P : Path γ (Path.refl x)) (z : ℝ × ℝ) : M :=
  P (radial z.1) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight z.1) (Int.fract z.2)))

private theorem reparamDisc_fract (P : Path γ (Path.refl x)) (s t : ℝ) :
    reparamDisc P (s, Int.fract t) = reparamDisc P (s, t) := by
  simp [reparamDisc, Int.fract_fract]

/-- On the strip `n ≤ t < n + 1` the reparametrized disc is given without `fract`. -/
private theorem reparamDisc_of_mem_Ico (P : Path γ (Path.refl x)) (s : ℝ) {n : ℤ} {t : ℝ}
    (ht : t ∈ Ico (n : ℝ) (n + 1)) :
    reparamDisc P (s, t) =
      P (radial s) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight s) (t - n))) := by
  rw [reparamDisc, Int.fract, Int.floor_eq_iff.2 ht]

/-- On the unit square the reparametrized disc is given without `fract`. -/
private theorem reparamDisc_of_mem_Icc (P : Path γ (Path.refl x)) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    reparamDisc P (s, t) =
      P (radial s) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight s) t)) := by
  rcases ht.2.lt_or_eq with ht' | rfl
  · simpa using reparamDisc_of_mem_Ico P s (n := 0) ⟨by simpa using ht.1, by simpa using ht'⟩
  · have h₀ : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_of_le_left _ le_rfl
    have h₁ : projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := projIcc_of_right_le _ le_rfl
    rw [reparamDisc, Int.fract_one, seamCollapse_zero_right, seamCollapse_one_right, h₀, h₁,
      (P (radial s)).source, (P (radial s)).target]

/-- The first loop of a path of loops `P` is `γ`, which at a parameter `r ∈ [0, 1]` is `g r`. -/
private theorem path_zero_projIcc {g : ℝ → M} (hγ : ∀ t : unitInterval, γ t = g t)
    (P : Path γ (Path.refl x)) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    P 0 (projIcc 0 1 zero_le_one r) = g r := by
  rw [P.source, hγ, projIcc_of_mem _ hr]

variable {g : ℝ → M}

/-- Near a seam line `t = n` the reparametrized disc is `g ((1 - c) (t - n))`, with `c` the slide
weight. This holds for every `s`: once the disc leaves `γ`, `c = 1` and both sides are `x`. -/
private theorem reparamDisc_of_abs_sub_lt (hgp : Periodic g 1)
    (hγ : ∀ t : unitInterval, γ t = g t) (P : Path γ (Path.refl x)) (s : ℝ) {n : ℤ} {t : ℝ}
    (ht : |t - n| < 1 / 3) :
    reparamDisc P (s, t) = g ((1 - slideWeight s) * (t - n)) := by
  have hg₀ : g 0 = x := by simpa using (hγ 0).symm
  have hc := slideWeight_mem s
  obtain ⟨ht₁, ht₂⟩ := abs_lt.1 ht
  rcases le_or_gt (n : ℝ) t with htn | htn
  · -- Just above the seam line, `fract t = t - n`.
    rw [reparamDisc_of_mem_Ico P s ⟨htn, by linarith⟩, seamCollapse_of_le _ (by linarith)]
    rcases le_or_gt s (1 / 3) with hs | hs
    · have h₁ := mul_nonneg hc.1 (by linarith : (0 : ℝ) ≤ t - n)
      have h₂ := mul_nonneg (sub_nonneg.2 hc.2) (by linarith : (0 : ℝ) ≤ t - n)
      rw [radial_of_le hs, path_zero_projIcc hγ P ⟨by nlinarith, by nlinarith⟩]
    · rw [slideWeight_of_ge hs.le]
      simp [hg₀]
  · -- Just below the seam line, `fract t = t - (n - 1)`.
    rw [reparamDisc_of_mem_Ico P s (n := n - 1) ⟨by push_cast; linarith, by push_cast; linarith⟩,
      seamCollapse_of_ge _ (by push_cast; linarith)]
    have e : (1 : ℝ) + (1 - slideWeight s) * (t - ↑(n - 1) - 1) =
        (1 - slideWeight s) * (t - n) + 1 := by
      push_cast
      ring
    rw [e]
    rcases le_or_gt s (1 / 3) with hs | hs
    · have h₁ := mul_nonneg hc.1 (by linarith : (0 : ℝ) ≤ n - t)
      have h₂ := mul_nonneg (sub_nonneg.2 hc.2) (by linarith : (0 : ℝ) ≤ n - t)
      rw [radial_of_le hs, path_zero_projIcc hγ P ⟨by nlinarith, by nlinarith⟩, hgp]
    · rw [slideWeight_of_ge hs.le]
      simp [hg₀]

/-- On the open strip `n < t < n + 1` the reparametrized disc is given without `fract`. -/
private theorem reparamDisc_eventuallyEq_strip (P : Path γ (Path.refl x)) {z : ℝ × ℝ} {n : ℤ}
    (hz : z.2 ∈ Ioo (n : ℝ) (n + 1)) :
    reparamDisc P =ᶠ[𝓝 z]
      fun w ↦ P (radial w.1)
        (projIcc 0 1 zero_le_one (seamCollapse (slideWeight w.1) (w.2 - n))) := by
  filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hz] with w hw
  exact reparamDisc_of_mem_Ico P w.1 (Ioo_subset_Ico_self hw)

/-- Near a seam line the reparametrized disc is `g ((1 - c) (t - n))`. -/
private theorem reparamDisc_eventuallyEq_seam (hgp : Periodic g 1)
    (hγ : ∀ t : unitInterval, γ t = g t) (P : Path γ (Path.refl x)) {z : ℝ × ℝ} {n : ℤ}
    (hz : |z.2 - n| < 1 / 3) :
    reparamDisc P =ᶠ[𝓝 z] fun w ↦ g ((1 - slideWeight w.1) * (w.2 - n)) := by
  have ho : IsOpen {w : ℝ × ℝ | |w.2 - n| < 1 / 3} :=
    isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
  filter_upwards [ho.mem_nhds hz] with w hw
  exact reparamDisc_of_abs_sub_lt hgp hγ P w.1 hw

/-- A real number is an integer or lies strictly between two consecutive integers. -/
private theorem eq_floor_or_mem_Ioo (t : ℝ) : t = ⌊t⌋ ∨ t ∈ Ioo (⌊t⌋ : ℝ) (⌊t⌋ + 1) := by
  rcases (Int.floor_le t).eq_or_lt with h | h
  · exact Or.inl h.symm
  · exact Or.inr ⟨h, Int.lt_floor_add_one t⟩

private theorem continuous_uncurry_path (P : Path γ (Path.refl x)) :
    Continuous fun p : unitInterval × unitInterval ↦ P p.1 p.2 :=
  Path.continuous_uncurry_iff.2 P.continuous

private theorem continuous_path_apply (P : Path γ (Path.refl x)) {Y : Type*} [TopologicalSpace Y]
    {a b : Y → unitInterval} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun y ↦ P (a y) (b y) :=
  (continuous_uncurry_path P).comp (ha.prodMk hb)

private theorem continuous_reparamDisc (hg : Continuous g) (hgp : Periodic g 1)
    (hγ : ∀ t : unitInterval, γ t = g t) (P : Path γ (Path.refl x)) :
    Continuous (reparamDisc P) := by
  refine continuous_iff_continuousAt.2 fun z ↦ ?_
  rcases eq_floor_or_mem_Ioo z.2 with h | h
  · refine ContinuousAt.congr ?_ (reparamDisc_eventuallyEq_seam hgp hγ P (n := ⌊z.2⌋)
      (by rw [← h, sub_self, abs_zero]; norm_num)).symm
    exact (hg.comp ((continuous_const.sub (continuous_slideWeight.comp continuous_fst)).mul
      (continuous_snd.sub continuous_const))).continuousAt
  · refine ContinuousAt.congr ?_ (reparamDisc_eventuallyEq_strip P h).symm
    exact (continuous_path_apply P
      (continuous_projIcc.comp ((continuous_const.mul continuous_fst).sub continuous_const))
      (continuous_projIcc.comp (continuous_seamCollapse.comp
        ((continuous_slideWeight.comp continuous_fst).prodMk
          (continuous_snd.sub continuous_const))))).continuousAt

/-- Along `s = 0` the reparametrized disc is the periodic loop `g`. -/
private theorem reparamDisc_zero_left (hgp : Periodic g 1) (hγ : ∀ t : unitInterval, γ t = g t)
    (P : Path γ (Path.refl x)) (t : ℝ) : reparamDisc P (0, t) = g t := by
  rw [reparamDisc, slideWeight_of_le (by norm_num), seamCollapse_zero_left,
    radial_of_le (by norm_num), path_zero_projIcc hγ P
      ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, Int.fract, ← mul_one (⌊t⌋ : ℝ),
    hgp.sub_int_mul_eq]

/-- Along `s = 1` the reparametrized disc is at the centre `x`. -/
private theorem reparamDisc_one_left (P : Path γ (Path.refl x)) (t : ℝ) :
    reparamDisc P (1, t) = x := by
  rw [reparamDisc, radial_of_ge (by norm_num), P.target, Path.refl_apply]

/-- Along the seam the reparametrized disc is at the base point `x`. -/
private theorem reparamDisc_seam (P : Path γ (Path.refl x)) (s : ℝ) {t : ℝ}
    (ht : t = 0 ∨ t = 1) : reparamDisc P (s, t) = x := by
  have h₀ : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_of_le_left _ le_rfl
  have h₁ : projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := projIcc_of_right_le _ le_rfl
  rcases ht with rfl | rfl
  · rw [reparamDisc_of_mem_Icc P s ⟨le_rfl, zero_le_one⟩, seamCollapse_zero_right, h₀,
      (P _).source]
  · rw [reparamDisc_of_mem_Icc P s ⟨zero_le_one, le_rfl⟩, seamCollapse_one_right, h₁,
      (P _).target]

/-- A path of loops is homotopic to the path of loops of its reparametrized disc. The homotopy
moves the radial coordinate linearly from `s` to `3 s - 1` and the reparametrization weight
linearly from `0` to `c`. -/
private theorem homotopic_reparamDisc (P P' : Path γ (Path.refl x))
    (hP' : ∀ s t : unitInterval, P' s t = reparamDisc P (s, t)) : P.Homotopic P' := by
  have hw : Continuous fun q : unitInterval × unitInterval × unitInterval ↦
      ((q.1 : ℝ) * slideWeight q.2.1, (q.2.2 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst |>.mul
      (continuous_slideWeight.comp (continuous_subtype_val.comp
        (continuous_fst.comp continuous_snd)))).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have h₀ : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_of_le_left _ le_rfl
  have h₁ : projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := projIcc_of_right_le _ le_rfl
  refine homotopic_of_continuous
    (fun q ↦ P (projIcc 0 1 zero_le_one ((1 - q.1) * q.2.1 + q.1 * (3 * q.2.1 - 1)))
      (projIcc 0 1 zero_le_one (seamCollapse (q.1 * slideWeight q.2.1) q.2.2)))
    (continuous_path_apply P (continuous_projIcc.comp (by fun_prop))
      (continuous_projIcc.comp (continuous_seamCollapse.comp hw))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro s t
    simp [seamCollapse_zero_left]
  · intro s t
    rw [hP', reparamDisc_of_mem_Icc P s ⟨t.2.1, t.2.2⟩]
    simp [radial]
  · intro τ t
    have hτ : projIcc (0 : ℝ) 1 zero_le_one ((1 - τ) * 0 + τ * (3 * 0 - 1)) = 0 :=
      projIcc_of_le_left _ (by nlinarith [τ.2.1])
    dsimp only
    rw [Icc.coe_zero, hτ, slideWeight_of_le (by norm_num), mul_zero, seamCollapse_zero_left,
      projIcc_val, P.source]
  · intro τ t
    have hτ : projIcc (0 : ℝ) 1 zero_le_one ((1 - τ) * 1 + τ * (3 * 1 - 1)) = 1 :=
      projIcc_of_right_le _ (by nlinarith [τ.2.1])
    dsimp only
    rw [Icc.coe_one, hτ, P.target, Path.refl_apply]
  · intro τ s
    simp only [Icc.coe_zero, seamCollapse_zero_right, h₀, Path.source]
  · intro τ s
    simp only [Icc.coe_one, seamCollapse_one_right, h₁, Path.target]

/-- The complement `S` of the open square `(1/4, 3/4)²` in the strip `ℝ × [0, 1]`: the set
relative to which the reparametrized disc is smoothed. -/
private def frame : Set (ℝ × ℝ) :=
  (univ ×ˢ Icc 0 1) \ (Ioo (1 / 4) (3 / 4) ×ˢ Ioo (1 / 4) (3 / 4))

private theorem isClosed_frame : IsClosed frame :=
  (isClosed_univ.prod isClosed_Icc).sdiff (isOpen_Ioo.prod isOpen_Ioo)

private theorem mem_frame_of_fst {s t : ℝ} (hs : s ∉ Ioo (1 / 4 : ℝ) (3 / 4))
    (ht : t ∈ Icc (0 : ℝ) 1) : (s, t) ∈ frame :=
  ⟨⟨mem_univ _, ht⟩, fun h ↦ hs h.1⟩

private theorem mem_frame_of_snd {s t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t ∉ Ioo (1 / 4 : ℝ) (3 / 4)) : (s, t) ∈ frame :=
  ⟨⟨mem_univ _, ht⟩, fun h ↦ ht' h.2⟩

/-- Points of the frame lie in the region where the reparametrized disc is smooth. -/
private theorem frame_subset :
    frame ⊆ {z | z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ ∃ n : ℤ, |z.2 - n| < 1 / 3} := by
  rintro ⟨s, t⟩ ⟨⟨-, ht₀, ht₁⟩, hz⟩
  simp only [mem_prod, mem_Ioo, not_and_or, not_lt] at hz
  simp only [mem_ofPred_eq]
  rcases le_or_gt s (1 / 4) with hs | hs
  · exact Or.inl (by linarith)
  rcases le_or_gt (3 / 4) s with hs' | hs'
  · exact Or.inr (Or.inl (by linarith))
  refine Or.inr (Or.inr ?_)
  rcases hz with ((hz | hz) | (hz | hz))
  · linarith
  · linarith
  · exact ⟨0, by rw [Int.cast_zero, sub_zero, abs_lt]; constructor <;> linarith⟩
  · exact ⟨1, by rw [Int.cast_one, abs_lt]; constructor <;> linarith⟩

/-- Near a seam line `t = n`, `(s, fract t)` lies in the frame. -/
private theorem mem_frame_fract {s t : ℝ} {n : ℤ} (ht : |t - n| < 1 / 4) :
    (s, Int.fract t) ∈ frame := by
  obtain ⟨ht₁, ht₂⟩ := abs_lt.1 ht
  refine mem_frame_of_snd ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩ fun h ↦ ?_
  rcases le_or_gt (n : ℝ) t with htn | htn
  · rw [Int.fract, Int.floor_eq_iff.2 ⟨htn, by linarith⟩] at h
    linarith [h.1]
  · rw [Int.fract, (Int.floor_eq_iff (z := n - 1)).2 ⟨by push_cast; linarith,
      by push_cast; linarith⟩] at h
    push_cast at h
    linarith [h.2]

/-- Two paths of loops whose maps of the square are homotopic relative to the frame are
homotopic. -/
private theorem homotopic_of_homotopicRel {P₀ P₁ : Path γ (Path.refl x)} {f₀ f₁ : C(ℝ × ℝ, M)}
    (h : f₀.HomotopicRel f₁ frame) (h₀ : ∀ s t : unitInterval, P₀ s t = f₀ (s, t))
    (h₁ : ∀ s t : unitInterval, P₁ s t = f₁ (s, t)) : P₀.Homotopic P₁ := by
  obtain ⟨H⟩ := h
  have hH {τ : unitInterval} {s t : unitInterval} (hz : ((s : ℝ), (t : ℝ)) ∈ frame) :
      H (τ, ((s : ℝ), (t : ℝ))) = P₀ s t := (H.eq_fst τ hz).trans (h₀ s t).symm
  have h0 : ((0 : unitInterval) : ℝ) ∉ Ioo (1 / 4 : ℝ) (3 / 4) := by norm_num
  have h1 : ((1 : unitInterval) : ℝ) ∉ Ioo (1 / 4 : ℝ) (3 / 4) := by norm_num
  refine homotopic_of_continuous (fun q ↦ H (q.1, ((q.2.1 : ℝ), (q.2.2 : ℝ))))
    (H.continuous.comp (by fun_prop)) (fun s t ↦ (H.apply_zero _).trans (h₀ s t).symm)
    (fun s t ↦ (H.apply_one _).trans (h₁ s t).symm) (fun τ t ↦ ?_) (fun τ t ↦ ?_)
    (fun τ s ↦ ?_) (fun τ s ↦ ?_)
  · rw [hH (mem_frame_of_fst h0 ⟨t.2.1, t.2.2⟩), P₀.source]
  · rw [hH (mem_frame_of_fst h1 ⟨t.2.1, t.2.2⟩), P₀.target, Path.refl_apply]
  · rw [hH (mem_frame_of_snd ⟨le_rfl, zero_le_one⟩ h0), (P₀ s).source]
  · rw [hH (mem_frame_of_snd ⟨zero_le_one, le_rfl⟩ h1), (P₀ s).target]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

/-- The reparametrized disc is smooth for `s < 1/3`, for `s > 2/3`, and near the seam lines. -/
private theorem contMDiffAt_reparamDisc (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ g) (hgp : Periodic g 1)
    (hγ : ∀ t : unitInterval, γ t = g t) (P : Path γ (Path.refl x)) {z : ℝ × ℝ}
    (hz : z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ ∃ n : ℤ, |z.2 - n| < 1 / 3) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (reparamDisc P) z := by
  -- Near a seam line, the disc is `g ((1 - c) (t - n))`.
  have hseam {n : ℤ} (hn : |z.2 - n| < 1 / 3) : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (reparamDisc P) z := by
    refine ContMDiffAt.congr_of_eventuallyEq ?_ (reparamDisc_eventuallyEq_seam hgp hγ P hn)
    exact (hg.comp ((contDiff_const.sub (contDiff_slideWeight.comp contDiff_fst)).mul
      (contDiff_snd.sub contDiff_const)).contMDiff).contMDiffAt
  rcases hz with hz | hz | ⟨n, hn⟩
  · rcases eq_floor_or_mem_Ioo z.2 with h | h
    · exact hseam (n := ⌊z.2⌋) (by rw [← h, sub_self, abs_zero]; norm_num)
    · -- For `s < 1/3` the disc is `γ`, reparametrized smoothly.
      have hev : reparamDisc P =ᶠ[𝓝 z]
          fun w ↦ g (seamCollapse (slideWeight w.1) (w.2 - ⌊z.2⌋)) := by
        filter_upwards [reparamDisc_eventuallyEq_strip P h,
          (isOpen_Iio.preimage continuous_fst).mem_nhds (show z.1 ∈ Iio (1 / 3) from hz),
          (isOpen_Ioo.preimage continuous_snd).mem_nhds h] with w hw hw₁ hw₂
        rw [hw, radial_of_le (le_of_lt hw₁)]
        exact path_zero_projIcc hγ P (seamCollapse_mem (slideWeight_mem _)
          ⟨by linarith [hw₂.1], by linarith [hw₂.2]⟩)
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
      exact (hg.comp (contDiff_seamCollapse.comp ((contDiff_slideWeight.comp contDiff_fst).prodMk
        (contDiff_snd.sub contDiff_const))).contMDiff).contMDiffAt
  · -- For `s > 2/3` the disc has reached its centre.
    have hev : reparamDisc P =ᶠ[𝓝 z] fun _ ↦ x := by
      filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds
        (show z.1 ∈ Ioi (2 / 3) from hz)] with w hw
      rw [reparamDisc, radial_of_ge (le_of_lt hw), P.target, Path.refl_apply]
    exact contMDiffAt_const.congr_of_eventuallyEq hev
  · exact hseam hn

/-- If `u₀` is smooth and agrees with the reparametrized disc on the frame, then its periodic
extension `(s, t) ↦ u₀ (s, fract t)` from the strip `ℝ × [0, 1)` is smooth: near the seam lines it
is the reparametrized disc, and between them it is a translate of `u₀`. -/
private theorem contMDiff_comp_fract (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ g) (hgp : Periodic g 1)
    (hγ : ∀ t : unitInterval, γ t = g t) (P : Path γ (Path.refl x)) {u₀ : ℝ × ℝ → M}
    (hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u₀) (hframe : ∀ z ∈ frame, u₀ z = reparamDisc P z) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ fun z : ℝ × ℝ ↦ u₀ (z.1, Int.fract z.2) := by
  intro z
  rcases eq_floor_or_mem_Ioo z.2 with h | h
  · have hz : |z.2 - ⌊z.2⌋| < 1 / 4 := by rw [← h, sub_self, abs_zero]; norm_num
    have ho : IsOpen {w : ℝ × ℝ | |w.2 - ⌊z.2⌋| < 1 / 4} :=
      isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
    have hev : (fun w : ℝ × ℝ ↦ u₀ (w.1, Int.fract w.2)) =ᶠ[𝓝 z] reparamDisc P := by
      filter_upwards [ho.mem_nhds hz] with w hw
      rw [hframe _ (mem_frame_fract hw), reparamDisc_fract]
    exact (contMDiffAt_reparamDisc hg hgp hγ P (Or.inr (Or.inr ⟨⌊z.2⌋, by linarith⟩))
      ).congr_of_eventuallyEq hev
  · have hev : (fun w : ℝ × ℝ ↦ u₀ (w.1, Int.fract w.2)) =ᶠ[𝓝 z]
        fun w ↦ u₀ (w.1, w.2 - ⌊z.2⌋) := by
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds h] with w hw
      rw [Int.fract, Int.floor_eq_iff.2 ⟨hw.1.le, hw.2⟩]
    exact (hu₀.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contMDiff
      ).contMDiffAt.congr_of_eventuallyEq hev

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth representatives of raw caps.** Let `γ` be a loop at `x` in a Hausdorff boundaryless
manifold, the restriction of a smooth `1`-periodic map `g : ℝ → M`. Every raw cap `D` of `γ` is the
class of the path of loops `s ↦ u (s, ·)` of a smooth cap `u` of `g`: a smooth map
`u : ℝ × ℝ → M`, `1`-periodic in its second coordinate, with `u (0, ·) = g` and `u (1, ·) = x`. -/
theorem exists_contMDiff_isLoopCylinder {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ g)
    (hgp : Periodic g 1) (hγ : ∀ t : unitInterval, γ t = g t) (D : RawCap γ) :
    ∃ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u ∧ IsLoopCylinder I u g (fun _ ↦ x) ∧
      ∃ P : Path γ (Path.refl x), (∀ s t : unitInterval, P s t = u (s, t)) ∧
        Path.Homotopic.Quotient.mk P = D := by
  induction D using Quotient.inductionOn with | h P => ?_
  -- Reparametrize the disc of `P`, so that it is smooth near the frame.
  let G : C(ℝ × ℝ, M) := ⟨reparamDisc P, continuous_reparamDisc hg.continuous hgp hγ P⟩
  have hU : {z : ℝ × ℝ | z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ ∃ n : ℤ, |z.2 - n| < 1 / 3} ∈ 𝓝ˢ frame := by
    have h₁ : IsOpen {z : ℝ × ℝ | z.1 < 1 / 3} := isOpen_lt continuous_fst continuous_const
    have h₂ : IsOpen {z : ℝ × ℝ | 2 / 3 < z.1} := isOpen_lt continuous_const continuous_fst
    have h₃ : IsOpen {z : ℝ × ℝ | ∃ n : ℤ, |z.2 - n| < 1 / 3} := by
      simp only [ofPred_exists]
      exact isOpen_iUnion fun n ↦ isOpen_lt (by fun_prop) continuous_const
    exact (h₁.union (h₂.union h₃)).mem_nhdsSet.2 frame_subset
  have hcpt : IsCompact (closure (range G)) := by
    have hK := isCompact_range (continuous_uncurry_path P)
    refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
    -- Each value of `G` is by definition a value of `P` on the square.
    rintro _ ⟨z, rfl⟩
    exact ⟨(_, _), rfl⟩
  -- Smooth it relative to the frame, and extend the result periodically from `ℝ × [0, 1)`.
  obtain ⟨u₀, hu₀, hGu₀⟩ := G.exists_contMDiff_homotopicRel_of_isCompact_closure_range
    (I := 𝓘(ℝ, ℝ × ℝ)) ⊤ hcpt isClosed_frame hU fun z hz ↦
      (contMDiffAt_reparamDisc hg hgp hγ P hz).contMDiffWithinAt
  have hframe (z : ℝ × ℝ) (hz : z ∈ frame) : u₀ z = reparamDisc P z :=
    (hGu₀.fst_eq_snd hz).symm
  have hfract (t : ℝ) : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hseam (s : ℝ) : u₀ (s, 0) = x := by
    rw [hframe _ (mem_frame_of_snd ⟨le_rfl, zero_le_one⟩ (by norm_num)),
      reparamDisc_seam P s (Or.inl rfl)]
  let u : ℝ × ℝ → M := fun z ↦ u₀ (z.1, Int.fract z.2)
  have hu_left (t : ℝ) : u (0, t) = g t := by
    simp only [u]
    rw [hframe _ (mem_frame_of_fst (by norm_num) (hfract t)), reparamDisc_fract,
      reparamDisc_zero_left hgp hγ]
  have hu_right (t : ℝ) : u (1, t) = x := by
    simp only [u]
    rw [hframe _ (mem_frame_of_fst (by norm_num) (hfract t)), reparamDisc_one_left]
  have hu_seam (s : ℝ) {t : ℝ} (ht : t = 0 ∨ t = 1) : u (s, t) = x := by
    rcases ht with rfl | rfl
    · simpa [u] using hseam s
    · simpa [u] using hseam s
  have hu_eq (s t : unitInterval) : u (s, t) = u₀ (s, t) := by
    rcases t.2.2.lt_or_eq with ht | ht
    · simp only [u, Int.fract_eq_self.2 ⟨t.2.1, ht⟩]
    · rw [hu_seam s (Or.inr ht), ht, hframe _ (mem_frame_of_snd ⟨zero_le_one, le_rfl⟩
        (by norm_num)), reparamDisc_seam P s (Or.inr rfl)]
  have hu := contMDiff_comp_fract hg hgp hγ P hu₀ hframe
  refine ⟨u, hu, ⟨hu.of_le (by simp), fun z ↦ by simp [u, Int.fract_add_one], hu_left,
    hu_right⟩, ?_⟩
  -- The path of loops of `u` is homotopic to that of `G` by smoothing, and so to `P`.
  let Pu := squarePath u hu.continuous (fun t ↦ by rw [hu_left, hγ])
    (fun t ↦ hu_right t) (fun s ↦ hu_seam s (Or.inl rfl)) (fun s ↦ hu_seam s (Or.inr rfl))
  let PG := squarePath G G.continuous (fun t ↦ (reparamDisc_zero_left hgp hγ P t).trans (hγ t).symm)
    (fun t ↦ reparamDisc_one_left P t) (fun s ↦ reparamDisc_seam P s (Or.inl rfl))
    (fun s ↦ reparamDisc_seam P s (Or.inr rfl))
  refine ⟨Pu, fun s t ↦ squarePath_apply s t, Quotient.sound ?_⟩
  exact ((homotopic_reparamDisc P PG fun s t ↦ squarePath_apply s t).trans
    (homotopic_of_homotopicRel hGu₀ (fun s t ↦ squarePath_apply s t)
      fun s t ↦ (squarePath_apply s t).trans (hu_eq s t))).symm

end TauCeti.Floer.RawCap

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {x : M} {γ : Ω M x}

/-- **A smooth null-homotopic loop has a smooth cap.** If the loop `γ` at `x` is the restriction of
a smooth `1`-periodic map `g : ℝ → M` and is null-homotopic, then `g` has a smooth cap in the sense
of `TauCeti.IsCap`. -/
theorem exists_isCap_of_homotopic {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ g)
    (hgp : Function.Periodic g 1) (hγ : ∀ t : unitInterval, γ t = g t)
    (h : γ.Homotopic (Path.refl x)) : ∃ u, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u ∧ IsCap I u g := by
  obtain ⟨D⟩ := Floer.RawCap.nonempty_iff.2 h
  obtain ⟨u, hu, hcyl, -⟩ := Floer.RawCap.exists_contMDiff_isLoopCylinder hg hgp hγ D
  exact ⟨u, hu, hcyl.isCap⟩

end TauCeti
