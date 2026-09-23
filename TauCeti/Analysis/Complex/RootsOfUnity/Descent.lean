/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient

/-!
# Descent of rotation-invariant functions through `u ↦ u ^ m`

The group `rootsOfUnity m ℂ` of `m`-th roots of unity acts on `ℂ` by rotations, and
`u ↦ u ^ m` is the orbit map of this action (`SubMulAction.rootsOfUnityQuotientHomeomorph`).
This file shows that the orbit map is also the quotient map holomorphically: a function invariant
under the rotations factors as `f u = g (u ^ m)`, where `g` is holomorphic, analytic, or
meromorphic whenever `f` is, and the orders of vanishing satisfy `ord₀ f = m * ord₀ g`.

This is the local model for descending invariant functions to the quotient of a Riemann surface
at a point whose stabilizer is cyclic of order `m`. In a coordinate centred at the fixed point in
which a generator acts by a primitive `m`-th root of unity, an invariant function descends to the
quotient coordinate `w = u ^ m`, and its order at the fixed point is `m` times the order of the
descended function.

The descended function `TauCeti.descendPow m f` evaluates `f` at the principal `m`-th root
`w ^ (1 / m)`. It satisfies `descendPow m f (u ^ m) = f u` at every point `u` at which `f` is
invariant under the rotations (`TauCeti.descendPow_pow`), and it undoes pulling back along
`u ↦ u ^ m` (`TauCeti.descendPow_comp_pow`), so the choice of branch is invisible in the results.

## Main declarations

* `TauCeti.descendPow`: the descent of a function through `u ↦ u ^ m`.
* `TauCeti.descendPow_pow`: `descendPow m f (u ^ m) = f u` when `f` is invariant at `u`.
* `TauCeti.eq_descendPow_iff`: the criterion for a globally invariant function to factor
  through the power map.
* `TauCeti.differentiableOn_descendPow`: the descent of a function holomorphic and invariant on
  an open set `s` is holomorphic on the open set `(· ^ m) '' s`.
* `TauCeti.analyticAt_descendPow` and `TauCeti.meromorphicAt_descendPow`: the descent of a function
  analytic, respectively meromorphic, at `0` and invariant near `0` is analytic, respectively
  meromorphic, at `0`.
* `TauCeti.analyticOrderAt_descendPow_mul` and `TauCeti.meromorphicOrderAt_descendPow_mul`: the
  order of `f` at `0` is `m` times the order of its descent at `0`.

## References

* Hershel M. Farkas and Irwin Kra, *Riemann Surfaces*, second edition, Chapter I §§4–5.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter III §3.
-/

public section

open Filter MulAction Set Topology

namespace TauCeti

variable {E : Type*} {m : ℕ}

/-- The descent of a function `f : ℂ → E` through `u ↦ u ^ m`: its value at `w` is the value of
`f` at the principal `m`-th root of `w`. When `f` is invariant under the `m`-th roots of unity on
a set `s`, this is the function on `(· ^ m) '' s` through which `f` factors on `s`
(`TauCeti.descendPow_pow`). -/
noncomputable def descendPow (m : ℕ) (f : ℂ → E) (w : ℂ) : E :=
  f (w ^ (m⁻¹ : ℂ))

theorem descendPow_apply {m : ℕ} (f : ℂ → E) (w : ℂ) :
    descendPow m f w = f (w ^ (m⁻¹ : ℂ)) :=
  (rfl)

variable [NeZero m]

/-- Descending a function pulled back along `u ↦ u ^ m` recovers the function. -/
@[simp]
theorem descendPow_comp_pow (g : ℂ → E) : descendPow m (fun u ↦ g (u ^ m)) = g := by
  funext w
  rw [descendPow_apply, Complex.cpow_nat_inv_pow w (NeZero.ne m)]

/-- Descent through `u ↦ u ^ m` is linear over functions pulled back along `u ↦ u ^ m`. -/
@[simp]
theorem descendPow_smul_comp_pow [SMul ℂ E] (φ : ℂ → ℂ) (f : ℂ → E) :
    descendPow m (fun u ↦ φ (u ^ m) • f u) = fun w ↦ φ w • descendPow m f w := by
  funext w
  rw [descendPow_apply, descendPow_apply, Complex.cpow_nat_inv_pow w (NeZero.ne m)]

/-- If `f` takes the same value at all rotations of `u` by `m`-th roots of unity, then the descent
of `f` takes that value at `u ^ m`. -/
@[simp]
theorem descendPow_pow {f : ℂ → E} {u : ℂ} (hf : ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    descendPow m f (u ^ m) = f u := by
  obtain ⟨ζ, hζ⟩ := (pow_eq_pow_iff_exists_rootsOfUnity_smul (NeZero.ne m)).mp
    (Complex.cpow_nat_inv_pow (u ^ m) (NeZero.ne m)).symm
  rw [descendPow_apply, ← hζ, hf ζ]

/-- For a globally rotation-invariant function, a function is its descent precisely when its
pullback along `u ↦ u ^ m` is the original function. -/
theorem eq_descendPow_iff {f g : ℂ → E}
    (hf : ∀ u, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    g = descendPow m f ↔ ∀ u, g (u ^ m) = f u := by
  constructor
  · rintro rfl u
    exact descendPow_pow (hf u)
  · intro h
    funext w
    obtain ⟨u, rfl⟩ := (Complex.isOpenQuotientMap_pow m).surjective w
    rw [h u, descendPow_pow (hf u)]

/-- A function invariant under the `m`-th roots of unity on a punctured neighbourhood of `0`
agrees near `0` with the pullback of its descent along `u ↦ u ^ m`. -/
theorem descendPow_pow_eventuallyEq {f : ℂ → E}
    (hf : ∀ᶠ u in 𝓝[≠] 0, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    (fun u ↦ descendPow m f (u ^ m)) =ᶠ[𝓝 0] f := by
  exact (eventually_rootsOfUnity_invariant_nhds_of_nhdsNE hf).mono fun _ hu ↦ descendPow_pow hu

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Away from `0`, the descent of a function invariant under the `m`-th roots of unity near `u` is
complex differentiable at `u ^ m` when the function is complex differentiable at `u`. -/
theorem differentiableAt_descendPow_pow {f : ℂ → E} {u : ℂ}
    (hf : ∀ᶠ v in 𝓝 u, ∀ ζ : rootsOfUnity m ℂ, f (ζ • v) = f v) (hu : u ≠ 0)
    (hfu : DifferentiableAt ℂ f u) :
    DifferentiableAt ℂ (descendPow m f) (u ^ m) := by
  have hw : u ^ m ≠ 0 := pow_ne_zero m hu
  -- A holomorphic branch `ρ` of the `m`-th root near `u ^ m`, with `ρ (u ^ m) = u`.
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ → ℂ, ρ = fun v ↦ u * (v / u ^ m) ^ (m⁻¹ : ℂ) := ⟨_, rfl⟩
  have hρw : ρ (u ^ m) = u := by simp [hρdef, div_self hw]
  have hρ : DifferentiableAt ℂ ρ (u ^ m) := by
    rw [hρdef]
    refine ((differentiableAt_id.div_const _).cpow_const ?_).const_mul u
    simp [div_self hw]
  have hρpow (v : ℂ) : ρ v ^ m = v := by
    rw [hρdef, mul_pow, Complex.cpow_nat_inv_pow _ (NeZero.ne m), mul_div_cancel₀ _ hw]
  have hρt := hρ.continuousAt.tendsto
  rw [hρw] at hρt
  have heq : descendPow m f =ᶠ[𝓝 (u ^ m)] f ∘ ρ := (hρt.eventually hf).mono fun v hv ↦ by
    rw [Function.comp_apply, ← descendPow_pow hv, hρpow]
  exact ((by rwa [hρw] : DifferentiableAt ℂ f (ρ (u ^ m))).comp _ hρ).congr_of_eventuallyEq heq

/-- The descent of a function holomorphic on an open set `s` and invariant under the `m`-th roots
of unity at every point of `s` is holomorphic on the open set `(· ^ m) '' s`. -/
theorem differentiableOn_descendPow [CompleteSpace E] {s : Set ℂ} {f : ℂ → E} (hs : IsOpen s)
    (hfd : DifferentiableOn ℂ f s) (hf : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    DifferentiableOn ℂ (descendPow m f) ((· ^ m) '' s) := by
  have hoff : DifferentiableOn ℂ (descendPow m f) ((· ^ m) '' s \ {0}) := by
    rintro _ ⟨⟨u, hu, rfl⟩, hw⟩
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hw (zero_pow (NeZero.ne m))
    exact (differentiableAt_descendPow_pow ((hs.eventually_mem hu).mono hf) hu0
      (hfd.differentiableAt (hs.mem_nhds hu))).differentiableWithinAt
  by_cases h0 : (0 : ℂ) ∈ (· ^ m) '' s
  · -- At `0`, the descent is continuous, so Riemann's removable singularity theorem applies.
    obtain ⟨u, hu, hu0⟩ := h0
    rw [(pow_eq_zero_iff (NeZero.ne m)).mp hu0] at hu
    have hroot : ContinuousAt (fun w : ℂ ↦ w ^ (m⁻¹ : ℂ)) 0 :=
      Complex.continuousAt_cpow_const_of_re_pos (by simp) (by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
        exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero m)))
    have hroot0 : (0 : ℂ) ^ (m⁻¹ : ℂ) = 0 := Complex.zero_cpow (by simp [NeZero.ne m])
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (((Complex.isOpenQuotientMap_pow m).isOpenMap _ hs).mem_nhds
        ⟨0, hu, zero_pow (NeZero.ne m)⟩)).mp ⟨hoff, ?_⟩
    exact (ContinuousAt.comp_of_eq (hfd.differentiableAt (hs.mem_nhds hu)).continuousAt hroot
      hroot0).congr (.of_forall fun w ↦ (descendPow_apply f w).symm)
  · rwa [sdiff_singleton_eq_self h0] at hoff

/-- The descent of a function analytic at `0` and invariant under the `m`-th roots of unity near
`0` is analytic at `0`. -/
theorem analyticAt_descendPow [CompleteSpace E] {f : ℂ → E} (hfa : AnalyticAt ℂ f 0)
    (hf : ∀ᶠ u in 𝓝[≠] 0, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    AnalyticAt ℂ (descendPow m f) 0 := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp
    (hfa.eventually_analyticAt.and (eventually_rootsOfUnity_invariant_nhds_of_nhdsNE hf))
  have hd := differentiableOn_descendPow Metric.isOpen_ball
    (fun u hu ↦ (h u hu).1.differentiableAt.differentiableWithinAt) fun u hu ↦ (h u hu).2
  rw [image_pow_ball hr.le] at hd
  exact hd.analyticAt (Metric.ball_mem_nhds 0 (pow_pos hr m))

/-- The descent of a function meromorphic at `0` and invariant under the `m`-th roots of unity
near `0` is meromorphic at `0`. -/
theorem meromorphicAt_descendPow [CompleteSpace E] {f : ℂ → E} (hfm : MeromorphicAt f 0)
    (hf : ∀ᶠ u in 𝓝[≠] 0, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    MeromorphicAt (descendPow m f) 0 := by
  obtain ⟨n, hn⟩ := hfm
  -- Multiplying `f` by `(u ^ m) ^ n` gives an invariant function analytic at `0`.
  have hpow : (fun u : ℂ ↦ (u ^ m) ^ n • f u) =
      fun u ↦ u ^ ((m - 1) * n) • ((u - 0) ^ n • f u) := by
    funext u
    rw [smul_smul, sub_zero, ← pow_mul, ← pow_add, Nat.sub_one_mul,
      Nat.sub_add_cancel (Nat.le_mul_of_pos_left n (Nat.pos_of_neZero m))]
  have ha : AnalyticAt ℂ (fun u : ℂ ↦ (u ^ m) ^ n • f u) 0 := by
    rw [hpow]
    exact (analyticAt_id.pow _).smul hn
  have hd := analyticAt_descendPow ha (hf.mono fun u hu ζ ↦ by rw [rootsOfUnity.smul_pow, hu ζ])
  rw [descendPow_smul_comp_pow (· ^ n) f] at hd
  exact ⟨n, by simpa using hd⟩

/-- The order of vanishing at `0` of a function analytic at `0` and invariant under the `m`-th
roots of unity near `0` is `m` times the order of vanishing of its descent. -/
theorem analyticOrderAt_descendPow_mul [CompleteSpace E] {f : ℂ → E} (hfa : AnalyticAt ℂ f 0)
    (hf : ∀ᶠ u in 𝓝[≠] 0, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    analyticOrderAt (descendPow m f) 0 * m = analyticOrderAt f 0 := by
  rw [← analyticOrderAt_comp_pow_zero (analyticAt_descendPow hfa hf) (Nat.pos_of_neZero m),
    analyticOrderAt_congr (descendPow_pow_eventuallyEq hf)]

/-- The meromorphic order at `0` of a function meromorphic at `0` and invariant under the `m`-th
roots of unity near `0` is `m` times the meromorphic order of its descent. -/
theorem meromorphicOrderAt_descendPow_mul [CompleteSpace E] {f : ℂ → E} (hfm : MeromorphicAt f 0)
    (hf : ∀ᶠ u in 𝓝[≠] 0, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = f u) :
    meromorphicOrderAt (descendPow m f) 0 * m = meromorphicOrderAt f 0 := by
  have horder : analyticOrderAt (fun u : ℂ ↦ u ^ m - (0 : ℂ) ^ m) 0 = m := by
    have h : (fun u : ℂ ↦ u ^ m - (0 : ℂ) ^ m) = (· - 0) ^ m := by
      funext u
      simp [zero_pow (NeZero.ne m)]
    rw [h, analyticOrderAt_centeredMonomial]
  have hnc : ¬EventuallyConst (fun u : ℂ ↦ u ^ m) (𝓝 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, horder]
    exact ENat.natCast_ne_top m
  have hcomp := MeromorphicAt.meromorphicOrderAt_comp (g := (· ^ m)) (x := 0)
    (by rw [zero_pow (NeZero.ne m)]; exact meromorphicAt_descendPow hfm hf) (by fun_prop) hnc
  rw [horder, zero_pow (NeZero.ne m), Function.comp_def,
    meromorphicOrderAt_congr ((descendPow_pow_eventuallyEq hf).filter_mono nhdsWithin_le_nhds)]
    at hcomp
  simpa using hcomp.symm

end TauCeti
