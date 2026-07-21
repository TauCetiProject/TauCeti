/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple

/-!
# The maximum principle for `Δ + b·∇` (a first-order drift term)

`TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple` proves the maximum
principle for the bare Laplacian `Δ` (subharmonic functions), and
`TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple` adds a
zeroth-order term `c`. This file supplies the missing first-order (transport/advection)
term: the maximum principle for the second-order elliptic operator

`L u = Δ u + ⟪b, ∇u⟫`

with a bounded drift field `b : E → E`. In Lean the directional derivative `⟪b x, ∇u x⟫`
is spelled `fderiv ℝ u x (b x)`, so the operator value at `x` is `Δ u x + fderiv ℝ u x (b x)`.

The two ingredients, both classical:

* **The strict principle needs no hypothesis on `b`.** At an interior local maximum the
  gradient vanishes (`IsLocalMax.fderiv_eq_zero`), so the drift term `fderiv ℝ u x (b x)`
  drops out and only `Δ u x ≤ 0` survives; a strict sign `0 < Δ u x + fderiv ℝ u x (b x)`
  is therefore impossible there. This is `not_isLocalMax_of_laplacian_add_fderiv_pos`.
* **The weak principle needs a bounded drift** `‖b x‖ ≤ β`. Perturbing by the barrier
  `w = exp (α ⟪u, ·⟫)` for a unit vector `u` and `α = β + 1` gives
  `Δ w + ⟪b, ∇w⟫ = α (α + ⟪u, b⟫) w > 0`, because `⟪u, b x⟫ ≥ -‖b x‖ ≥ -β`; letting the
  perturbation vanish recovers the borderline `0 ≤ Δ u + fderiv ℝ u (b)` case.

The exponential-barrier argument follows the weak maximum principle proof in
Gilbarg--Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 3.

## Main declarations

* `TauCeti.laplacian_exp_inner`: `Δ (exp (α ⟪u, ·⟫)) x = α² ‖u‖² exp (α ⟪u, x⟫)`, the
  exponential barrier's Laplacian.
* `TauCeti.fderiv_exp_inner_apply`: the directional derivative of the same barrier.
* `TauCeti.not_isLocalMax_of_laplacian_add_fderiv_pos` /
  `TauCeti.not_isLocalMin_of_laplacian_add_fderiv_neg`: a strict sign of `Δ u + ⟪b, ∇u⟫`
  forbids an interior local extremum, with no hypothesis on `b`.
* `TauCeti.exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_pos` /
  `TauCeti.exists_mem_frontier_isMinOn_of_laplacian_add_fderiv_neg`: strict boundary
  extremum principles.
* `TauCeti.le_of_laplacian_add_fderiv_nonneg_le_frontier` /
  `TauCeti.ge_of_laplacian_add_fderiv_nonpos_ge_frontier`: the **weak maximum principle**
  for `Δ + b·∇` with bounded drift, in bound form.
* `TauCeti.exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_nonneg` /
  `TauCeti.exists_mem_frontier_isMinOn_of_laplacian_add_fderiv_nonpos`: the `∃`-form of the
  weak principle.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exponential barrier `y ↦ exp (α ⟪u, y⟫)` has derivative `exp (α ⟪u, x⟫) • (α • ⟪u, ·⟫)`.
This is the shared first-derivative computation feeding both `laplacian_exp_inner` and
`fderiv_exp_inner_apply`. -/
private theorem hasFDerivAt_exp_inner (α : ℝ) (u x : E) :
    HasFDerivAt (fun y : E => Real.exp (α * ⟪u, y⟫))
      (Real.exp (α * ⟪u, x⟫) • (α • innerSL ℝ u)) x := by
  have h1 : HasFDerivAt (fun z : E => (⟪u, z⟫ : ℝ)) (innerSL ℝ u) x := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ u).hasFDerivAt
  have h2 : HasFDerivAt (fun z : E => α * ⟪u, z⟫) (α • innerSL ℝ u) x := h1.const_mul α
  exact (Real.hasDerivAt_exp (α * ⟪u, x⟫)).comp_hasFDerivAt x h2

/-- The directional derivative of the exponential barrier `y ↦ exp (α ⟪u, y⟫)`. -/
@[simp] theorem fderiv_exp_inner_apply (α : ℝ) (u x v : E) :
    fderiv ℝ (fun y : E => Real.exp (α * ⟪u, y⟫)) x v
      = Real.exp (α * ⟪u, x⟫) * (α * ⟪u, v⟫) := by
  rw [(hasFDerivAt_exp_inner α u x).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The Laplacian of the exponential barrier.** For a fixed vector `u`, the function
`y ↦ exp (α ⟪u, y⟫)` has Laplacian `α² ‖u‖² exp (α ⟪u, y⟫)`, because it is an exponential of
a linear form: the second directional derivative along an orthonormal basis vector `eᵢ`
contributes `α² ⟪u, eᵢ⟫²`, and these sum to `α² ‖u‖²`. This is the barrier for the weak
maximum principle with drift. -/
@[simp] theorem laplacian_exp_inner (α : ℝ) (u x : E) :
    Δ (fun y : E => Real.exp (α * ⟪u, y⟫)) x
      = α ^ 2 * ‖u‖ ^ 2 * Real.exp (α * ⟪u, x⟫) := by
  set w : E → ℝ := fun y => Real.exp (α * ⟪u, y⟫) with hw
  -- The first derivative of `w`, as a function of the base point.
  have hfw : fderiv ℝ w = fun y => Real.exp (α * ⟪u, y⟫) • (α • innerSL ℝ u) :=
    funext fun y => (hasFDerivAt_exp_inner α u y).fderiv
  -- The second derivative at `x`.
  have hw2 : HasFDerivAt (fun y => Real.exp (α * ⟪u, y⟫) • (α • innerSL ℝ u))
      ((Real.exp (α * ⟪u, x⟫) • (α • innerSL ℝ u)).smulRight (α • innerSL ℝ u)) x :=
    (hasFDerivAt_exp_inner α u x).smul_const (α • innerSL ℝ u)
  -- Each diagonal Hessian entry along the standard orthonormal basis.
  have hterm : ∀ i, iteratedFDeriv ℝ 2 w x
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      = α ^ 2 * ⟪u, (stdOrthonormalBasis ℝ E) i⟫ ^ 2 * Real.exp (α * ⟪u, x⟫) := by
    intro i
    rw [iteratedFDeriv_two_apply, hfw, hw2.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis w
    (stdOrthonormalBasis ℝ E)) x]
  calc ∑ i, iteratedFDeriv ℝ 2 w x
        ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      = ∑ i, α ^ 2 * ⟪u, (stdOrthonormalBasis ℝ E) i⟫ ^ 2 * Real.exp (α * ⟪u, x⟫) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = α ^ 2 * Real.exp (α * ⟪u, x⟫) * ∑ i, ⟪u, (stdOrthonormalBasis ℝ E) i⟫ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = α ^ 2 * Real.exp (α * ⟪u, x⟫) * ‖u‖ ^ 2 := by
        rw [(stdOrthonormalBasis ℝ E).sum_sq_inner_left u]
    _ = α ^ 2 * ‖u‖ ^ 2 * Real.exp (α * ⟪u, x⟫) := by ring

/-- **Strict interior obstruction.** If `0 < Δ f x + fderiv ℝ f x v` at a point where `f` is
`C²`, then `f` has no local maximum at `x`. The direction `v` is arbitrary: at a local
maximum the derivative `fderiv ℝ f x` vanishes, so the first-order term contributes nothing
and only the Laplacian's nonpositivity survives. -/
theorem not_isLocalMax_of_laplacian_add_fderiv_pos {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < Δ f x + fderiv ℝ f x v) :
    ¬ IsLocalMax f x := by
  intro hmax
  have hlap : Δ f x ≤ 0 := laplacian_nonpos_of_isLocalMax hf hmax
  rw [hmax.fderiv_eq_zero] at hpos
  simp only [zero_apply, add_zero] at hpos
  exact absurd hlap (not_le.2 hpos)

/-- **Strict interior obstruction, minimum form.** If `Δ f x + fderiv ℝ f x v < 0` at a point
where `f` is `C²`, then `f` has no local minimum at `x`. -/
theorem not_isLocalMin_of_laplacian_add_fderiv_neg {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ 2 f x) (hneg : Δ f x + fderiv ℝ f x v < 0) :
    ¬ IsLocalMin f x := by
  intro hmin
  have hlap : 0 ≤ Δ f x := laplacian_nonneg_of_isLocalMin hf hmin
  rw [hmin.fderiv_eq_zero] at hneg
  simp only [zero_apply, add_zero] at hneg
  exact absurd hlap (not_le.2 hneg)

/-- **Strict boundary maximum principle for `Δ + b·∇`.** Let `K` be compact and nonempty. If
`f` is continuous on `K`, is `C²` on `interior K`, and satisfies
`0 < Δ f x + fderiv ℝ f x (b x)` throughout `interior K`, then some maximum point of `f` on
`K` lies on `frontier K`. No hypothesis on the drift field `b` is needed. -/
theorem exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_pos {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} {b : E → E} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hpos : ∀ ⦃x⦄, x ∈ interior K → 0 < Δ f x + fderiv ℝ f x (b x)) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  exact exists_mem_frontier_isMaxOn_of_forall_mem_interior_not_isLocalMax hK hne hcont
    fun {_} hx => not_isLocalMax_of_laplacian_add_fderiv_pos (hcd hx) (hpos hx)

/-- **Strict boundary minimum principle for `Δ + b·∇`.** The dual of
`exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_pos`. -/
theorem exists_mem_frontier_isMinOn_of_laplacian_add_fderiv_neg {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} {b : E → E} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hneg : ∀ ⦃x⦄, x ∈ interior K → Δ f x + fderiv ℝ f x (b x) < 0) :
    ∃ x ∈ frontier K, IsMinOn f K x := by
  exact exists_mem_frontier_isMinOn_of_forall_mem_interior_not_isLocalMin hK hne hcont
    fun {_} hx => not_isLocalMin_of_laplacian_add_fderiv_neg (hcd hx) (hneg hx)

section Nontrivial

variable [Nontrivial E]

/-- **Weak maximum principle for `Δ + b·∇` with bounded drift.**

Let `K` be compact. If `f` is continuous on `K`, is `C²` on `interior K`, the drift field is
bounded there (`‖b x‖ ≤ β`), and `0 ≤ Δ f x + fderiv ℝ f x (b x)` (a subsolution of
`Δ + b·∇`), then any bound `m` that `f` respects on `frontier K` bounds `f` on all of `K`. -/
theorem le_of_laplacian_add_fderiv_nonneg_le_frontier {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} {b : E → E} {β m : ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ Δ f x + fderiv ℝ f x (b x))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  intro x hxK
  -- A unit vector `u` for the exponential barrier direction.
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  set u : E := (‖v₀‖⁻¹ : ℝ) • v₀ with hudef
  have hunorm : ‖u‖ = 1 := norm_smul_inv_norm hv₀
  -- The barrier `w = exp (α ⟪u, ·⟫)` with `α = β + 1`.
  set α : ℝ := β + 1 with hαdef
  set w : E → ℝ := fun y => Real.exp (α * ⟪u, y⟫) with hwdef
  have hwpos : ∀ y, 0 < w y := fun y => Real.exp_pos _
  have hwCD : ContDiff ℝ 2 w := by
    rw [hwdef]
    have hinner : ContDiff ℝ 2 (fun z : E => (⟪u, z⟫ : ℝ)) := by
      simpa only [coe_innerSL_apply] using (innerSL ℝ u).contDiff
    exact (by simpa only [smul_eq_mul] using hinner.const_smul α : ContDiff ℝ 2 _).exp
  have hwcont : Continuous w := hwCD.continuous
  have hwcd : ∀ y, ContDiffAt ℝ 2 w y := fun y => hwCD.contDiffAt
  -- `w` is bounded above by `C ≥ 0` on the compact set `K`.
  obtain ⟨C, hCub⟩ := hK.bddAbove_image (f := w) hwcont.continuousOn
  have hCnonneg : 0 ≤ C := le_trans (hwpos x).le (hCub (Set.mem_image_of_mem w hxK))
  -- Perturbation estimate: `f x ≤ m + ε C` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → f x ≤ m + ε * C := by
    intro ε hε
    set g : E → ℝ := fun y => f y + ε • w y with hgdef
    have hgcont : ContinuousOn g K := hcont.add (hwcont.continuousOn.const_smul ε)
    have hgcd : ∀ ⦃y⦄, y ∈ interior K → ContDiffAt ℝ 2 g y :=
      fun y hy => (hcd hy).add ((hwcd y).const_smul ε)
    -- The perturbed function is a strict subsolution of `Δ + b·∇`.
    have hgpos : ∀ ⦃y⦄, y ∈ interior K → 0 < Δ g y + fderiv ℝ g y (b y) := by
      intro y hy
      have hΔ : Δ g y = Δ f y + ε * Δ w y := by
        have hadd : Δ (fun z => f z + ε • w z) y = Δ f y + Δ (fun z => ε • w z) y :=
          (hcd hy).laplacian_add ((hwcd y).const_smul ε)
        have hsmul : Δ (fun z => ε • w z) y = ε • Δ w y := laplacian_smul ε (hwcd y)
        rw [hgdef, hadd, hsmul, smul_eq_mul]
      have hfd : fderiv ℝ g y (b y) = fderiv ℝ f y (b y) + ε * fderiv ℝ w y (b y) := by
        have hd : DifferentiableAt ℝ f y := (hcd hy).differentiableAt (by norm_num)
        have hdw : DifferentiableAt ℝ w y := (hwcd y).differentiableAt (by norm_num)
        have hadd : fderiv ℝ (fun z => f z + ε • w z) y
            = fderiv ℝ f y + fderiv ℝ (fun z => ε • w z) y := fderiv_add hd (hdw.const_smul ε)
        have hsmul : fderiv ℝ (fun z => ε • w z) y = ε • fderiv ℝ w y := fderiv_const_smul hdw ε
        rw [hgdef, hadd, hsmul]
        simp only [add_apply, smul_apply, smul_eq_mul]
      -- The barrier's operator value is strictly positive.
      have hbylb : -β ≤ ⟪u, b y⟫ := by
        have h := (abs_le.mp (abs_real_inner_le_norm u (b y))).1
        rw [hunorm, one_mul] at h
        exact le_trans (neg_le_neg (hb hy)) h
      have hαpos : 0 < α := by
        have := le_trans (norm_nonneg (b y)) (hb hy)
        rw [hαdef]; linarith
      have hLwpos : 0 < Δ w y + fderiv ℝ w y (b y) := by
        have hLw : Δ w y + fderiv ℝ w y (b y)
            = α * (α + ⟪u, b y⟫) * Real.exp (α * ⟪u, y⟫) := by
          have e1 : Δ w y = α ^ 2 * ‖u‖ ^ 2 * Real.exp (α * ⟪u, y⟫) := by
            rw [hwdef]; exact laplacian_exp_inner α u y
          have e2 : fderiv ℝ w y (b y) = Real.exp (α * ⟪u, y⟫) * (α * ⟪u, b y⟫) := by
            rw [hwdef]; exact fderiv_exp_inner_apply α u y (b y)
          rw [e1, e2, hunorm]; ring
        rw [hLw]
        have : 0 < α + ⟪u, b y⟫ := by rw [hαdef]; linarith
        positivity
      have hcomb : Δ g y + fderiv ℝ g y (b y)
          = (Δ f y + fderiv ℝ f y (b y)) + ε * (Δ w y + fderiv ℝ w y (b y)) := by
        rw [hΔ, hfd]; ring
      rw [hcomb]
      have := mul_pos hε hLwpos
      linarith [hlap hy]
    -- Apply the strict boundary maximum principle to the perturbed function.
    obtain ⟨z, hzfr, hzmax⟩ :=
      exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_pos hK ⟨x, hxK⟩ hgcont hgcd hgpos
    have hzK : z ∈ K := hK.isClosed.frontier_subset hzfr
    have hgx : g x = f x + ε * w x := by rw [hgdef]; simp [smul_eq_mul]
    have hgz : g z = f z + ε * w z := by rw [hgdef]; simp [smul_eq_mul]
    have hxle : f x + ε * w x ≤ f z + ε * w z := by rw [← hgx, ← hgz]; exact hzmax hxK
    have hzC : ε * w z ≤ ε * C :=
      mul_le_mul_of_nonneg_left (hCub (Set.mem_image_of_mem w hzK)) hε.le
    have hwxnn : 0 ≤ ε * w x := mul_nonneg hε.le (hwpos x).le
    linarith [hbdry hzfr]
  exact le_of_forall_pos_mul_le hCnonneg key

/-- **Weak minimum principle for `Δ + b·∇` with bounded drift.** The dual of
`le_of_laplacian_add_fderiv_nonneg_le_frontier` for supersolutions
(`Δ f x + fderiv ℝ f x (b x) ≤ 0`). -/
theorem ge_of_laplacian_add_fderiv_nonpos_ge_frontier {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} {b : E → E} {β m : ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x + fderiv ℝ f x (b x) ≤ 0)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hxK
  have hle := le_of_laplacian_add_fderiv_nonneg_le_frontier (f := -f) (b := b) (β := β) (m := -m)
    hK hcont.neg (fun y hy => (hcd hy).neg) hb
    (fun y hy => by
      have h1 : Δ (-f) y = -Δ f y := by rw [congrFun laplacian_neg y, Pi.neg_apply]
      have h2 : fderiv ℝ (-f) y (b y) = -fderiv ℝ f y (b y) := by
        rw [fderiv_neg, neg_apply]
      rw [h1, h2]; linarith [hlap hy])
    (fun y hy => neg_le_neg (hbdry hy)) hxK
  simp only [Pi.neg_apply] at hle
  linarith

/-- **Comparison principle for `Δ + b·∇`.** Two functions acted on by the same bounded drift
are ordered on a compact set if their operator values and frontier values are ordered. -/
theorem le_of_laplacian_add_fderiv_le_laplacian_add_fderiv_of_le_frontier {K : Set E}
    (hK : IsCompact K) {f g : E → ℝ} {b : E → E} {β : ℝ}
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      Δ g x + fderiv ℝ g x (b x) ≤ Δ f x + fderiv ℝ f x (b x))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hx
  have h := le_of_laplacian_add_fderiv_nonneg_le_frontier (f := f - g) (b := b) (β := β)
    (m := 0) hK (hfcont.sub hgcont) (fun y hy => (hfcd hy).sub (hgcd hy)) hb
    (fun y hy => by
      have hfd : DifferentiableAt ℝ f y := (hfcd hy).differentiableAt (by norm_num)
      have hgd : DifferentiableAt ℝ g y := (hgcd hy).differentiableAt (by norm_num)
      rw [(hfcd hy).laplacian_sub (hgcd hy), fderiv_sub hfd hgd]
      simp only [sub_apply]
      linarith [hL hy])
    (fun y hy => sub_nonpos.mpr (hbdry hy)) hx
  exact sub_nonpos.mp h

/-- **Uniqueness principle for `Δ + b·∇`.** Functions with equal operator values for the same
bounded drift and equal frontier data agree throughout the compact set. -/
theorem eqOn_of_laplacian_add_fderiv_eq_of_eqOn_frontier {K : Set E} (hK : IsCompact K)
    {f g : E → ℝ} {b : E → E} {β : ℝ} (hfcont : ContinuousOn f K)
    (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      Δ f x + fderiv ℝ f x (b x) = Δ g x + fderiv ℝ g x (b x))
    (hbdry : Set.EqOn f g (frontier K)) :
    Set.EqOn f g K := by
  intro x hx
  apply le_antisymm
  · exact le_of_laplacian_add_fderiv_le_laplacian_add_fderiv_of_le_frontier hK hfcont hgcont
      hfcd hgcd hb (fun y hy => (hL hy).ge) (fun y hy => (hbdry hy).le) hx
  · exact le_of_laplacian_add_fderiv_le_laplacian_add_fderiv_of_le_frontier hK hgcont hfcont
      hgcd hfcd hb (fun y hy => (hL hy).le) (fun y hy => (hbdry hy).ge) hx

/-- The `∃`-form of the weak maximum principle for `Δ + b·∇`: a subsolution with bounded drift
on a nonempty compact set attains a maximum on the frontier. -/
theorem exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_nonneg {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} {b : E → E} {β : ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ Δ f x + fderiv ℝ f x (b x)) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  exact exists_mem_frontier_isMaxOn_of_le_frontier hK hne hcont fun hbdry =>
    le_of_laplacian_add_fderiv_nonneg_le_frontier hK hcont hcd hb hlap hbdry

/-- The `∃`-form of the weak minimum principle for `Δ + b·∇`: a supersolution with bounded
drift on a nonempty compact set attains a minimum on the frontier. -/
theorem exists_mem_frontier_isMinOn_of_laplacian_add_fderiv_nonpos {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {f : E → ℝ} {b : E → E} {β : ℝ} (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x + fderiv ℝ f x (b x) ≤ 0) :
    ∃ x ∈ frontier K, IsMinOn f K x := by
  obtain ⟨z, hzfr, hzmax⟩ := exists_mem_frontier_isMaxOn_of_laplacian_add_fderiv_nonneg
    hK hne hcont.neg (fun y hy => (hcd hy).neg) hb (fun y hy => by
      rw [congrFun laplacian_neg y, Pi.neg_apply, fderiv_neg, neg_apply]
      linarith [hlap hy])
  refine ⟨z, hzfr, isMinOn_iff.mpr fun y hyK => ?_⟩
  simpa using neg_le_neg (isMaxOn_iff.mp hzmax y hyK)

end Nontrivial

end FiniteDimensional

end TauCeti

end
