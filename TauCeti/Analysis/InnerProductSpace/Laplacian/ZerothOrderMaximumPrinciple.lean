/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
-- Support only: the drift-free case is read off the lower-order principle.
import TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple

/-!
# The weak maximum principle for `-Δ + c` with a nonnegative zeroth-order term

`TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple` proves the weak maximum
principle for the bare Laplacian: a subharmonic (`0 ≤ Δ f`) function on a compact set is bounded on
all of `K` by any bound it satisfies on `frontier K`. This file restores the zeroth-order term, i.e.
it allows the operator `L u = -Δ u + c u` with a **nonnegative** coefficient `c`.

The sign condition `c ≥ 0` is load-bearing: it is exactly what lets the maximum principle survive
the extra term. A subsolution of `L`, `L f ≤ 0`, is a function with `c · f ≤ Δ f` on the interior,
and the conclusion is one-sided in the standard `sup u ≤ sup_{∂} u⁺` shape: a subsolution bounded
by a **nonnegative** `m` on the frontier is bounded by `m` throughout. (The nonnegativity of `m` is
needed once `c ≠ 0`; on the set where `f ≤ 0 ≤ m` the estimate is automatic, and the argument only
has to control the set where `f` is positive, where `c · f ≥ 0` makes `f` subharmonic.)

The weak maximum principle is the drift-free case (`b = 0`, `β = 0`) of
`TauCeti.le_of_mul_le_laplacian_add_fderiv_le_frontier` of
`TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple`; the remaining statements
are deduced from it.

## Main declarations

* `TauCeti.le_of_mul_le_laplacian_le_frontier`: **weak maximum principle for `-Δ + c`, `c ≥ 0`**. A
  continuous function that is `C²` on the interior with `c · f ≤ Δ f` (a subsolution of `-Δ + c`)
  and `c ≥ 0` there is bounded by any nonnegative `m` it respects on `frontier K`.
* `TauCeti.le_of_mul_le_laplacian_le_of_le_frontier`: **comparison principle for `-Δ + c`,
  `c ≥ 0`**. A subsolution `f` and a supersolution `g` ordered by `f ≤ g` on `frontier K` stay
  ordered `f ≤ g` on all of `K`.
* `TauCeti.ge_of_laplacian_le_mul_ge_frontier`: the dual weak minimum principle for supersolutions
  (`Δ f ≤ c · f`), bounded below by any nonpositive lower bound on the frontier.
* `TauCeti.abs_le_of_laplacian_eq_mul_abs_le_frontier`: a solution of `-Δ u + c u = 0`
  (`Δ f = c · f`) is bounded on `K` by any bound its absolute value respects on `frontier K`.
* `TauCeti.eqOn_of_laplacian_sub_mul_eq_of_eqOn_frontier`: **uniqueness for the Dirichlet problem
  for `-Δ + c`**. Two functions with the same `Δ · - c · ·` on the interior and the same boundary
  values agree on `K`.
* `TauCeti.nonpos_of_mul_le_laplacian_of_bddAbove`: **maximum principle on the whole space for
  `-Δ + c`, `c > 0`**. A `C²` subsolution on all of `E` that is bounded above is nonpositive.
* `TauCeti.eq_zero_of_laplacian_eq_mul_of_isBounded`: a bounded `C²` solution of `Δ f = c f` on
  all of `E`, `c > 0`, vanishes.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Nontrivial

variable [Nontrivial E]

/-- **Weak maximum principle for the operator `-Δ + c` with `c ≥ 0`.**

Let `K` be compact. If `f` is continuous on `K`, is `C²` on `interior K`, and is a subsolution of
`-Δ + c` there (`c x * f x ≤ Δ f x`) with a nonnegative coefficient (`0 ≤ c x`), then any
**nonnegative** bound `m` that `f` respects on `frontier K` bounds `f` on all of `K`.

The nonnegativity of `m` cannot be dropped once `c ≠ 0`; it encodes the `sup u ≤ sup_{∂} u⁺` shape
of the estimate. -/
theorem le_of_mul_le_laplacian_le_frontier {K : Set E} (hK : IsCompact K) {c f : E → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x) (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤ Δ f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  intro x hxK
  exact le_of_mul_le_laplacian_add_fderiv_le_frontier (b := 0) (β := 0) hK hm hcont hcd hc
    (fun _ _ => by simp) (fun y hy => by simpa using hsub hy) hbdry hxK

/-- **Comparison principle for `-Δ + c` with `c ≥ 0`.**

Let `K` be compact and let `f`, `g` be continuous on `K` and `C²` on `interior K`, with a
nonnegative coefficient `c` there. If `f` is a subsolution and `g` a supersolution of `-Δ + c`
(`c · f ≤ Δ f` and `Δ g ≤ c · g`) and `f ≤ g` on `frontier K`, then `f ≤ g` on all of `K`. This is
the two-function form of `le_of_mul_le_laplacian_le_frontier`. -/
theorem le_of_mul_le_laplacian_le_of_le_frontier {K : Set E} (hK : IsCompact K) {c f g : E → ℝ}
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤ Δ f x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K → Δ g x ≤ c x * g x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hxK
  -- Bound the difference `f - g` above by `0` via the weak maximum principle for `-Δ + c`.
  have hdiff : ∀ ⦃y⦄, y ∈ K → (f - g) y ≤ 0 :=
    le_of_mul_le_laplacian_le_frontier (c := c) hK le_rfl (hfcont.sub hgcont)
      (fun y hy => (hfcd hy).sub (hgcd hy)) hc
      (fun y hy => by
        rw [(hfcd hy).laplacian_sub (hgcd hy), Pi.sub_apply, mul_sub]
        linarith [hsub hy, hsuper hy])
      (fun y hy => by
        rw [Pi.sub_apply]
        linarith [hbdry hy])
  have := hdiff hxK
  rw [Pi.sub_apply] at this
  linarith

/-- **Weak minimum principle for supersolutions of `-Δ + c` with `c ≥ 0`.**

The dual of `le_of_mul_le_laplacian_le_frontier`: a continuous, `C²`, supersolution
(`Δ f x ≤ c x * f x`) with a nonnegative coefficient is bounded below on `K` by any **nonpositive**
lower bound it respects on `frontier K`. -/
theorem ge_of_laplacian_le_mul_ge_frontier {K : Set E} (hK : IsCompact K) {c f : E → ℝ} {m : ℝ}
    (hm : m ≤ 0) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x) (hsuper : ∀ ⦃x⦄, x ∈ interior K → Δ f x ≤ c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hxK
  have hle := le_of_mul_le_laplacian_le_frontier (c := c) (f := -f) (m := -m) hK (by linarith)
    hcont.neg (fun y hy => (hcd hy).neg) hc
    (fun y hy => by
      have h1 : Δ (-f) y = -Δ f y := by rw [congrFun laplacian_neg y, Pi.neg_apply]
      rw [h1, Pi.neg_apply, mul_neg]
      linarith [hsuper hy])
    (fun y hy => by rw [Pi.neg_apply]; linarith [hbdry hy]) hxK
  rw [Pi.neg_apply] at hle
  linarith

/-- A solution of `-Δ u + c u = 0` (`Δ f = c · f`) with `c ≥ 0`, continuous on a compact set `K` and
`C²` on its interior, is bounded on `K` by any bound `M` its absolute value respects on
`frontier K`. -/
theorem abs_le_of_laplacian_eq_mul_abs_le_frontier {K : Set E} (hK : IsCompact K) {c f : E → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hsol : ∀ ⦃x⦄, x ∈ interior K → Δ f x = c x * f x) (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) :
    ∀ ⦃x⦄, x ∈ K → |f x| ≤ M := by
  intro x hxK
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · exact ge_of_laplacian_le_mul_ge_frontier (c := c) hK (by linarith) hcont hcd hc
      (fun y hy => (hsol hy).le) (fun y hy => (abs_le.mp (hbdry hy)).1) hxK
  · exact le_of_mul_le_laplacian_le_frontier (c := c) hK hM hcont hcd hc
      (fun y hy => (hsol hy).ge) (fun y hy => (abs_le.mp (hbdry hy)).2) hxK

/-- **Uniqueness for the Dirichlet problem for `-Δ + c` with `c ≥ 0`.**

If `f` and `g` are continuous on a compact set `K`, `C²` on `interior K` with the same source term
`Δ · - c · ·` there (so both solve `-Δ u + c u = h` for one `h`), and agree on `frontier K`, then
they agree on all of `K`. -/
theorem eqOn_of_laplacian_sub_mul_eq_of_eqOn_frontier {K : Set E} (hK : IsCompact K)
    {c f g : E → ℝ} (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hlap : ∀ ⦃x⦄, x ∈ interior K → Δ f x - c x * f x = Δ g x - c x * g x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x = g x) :
    Set.EqOn f g K := by
  intro x hxK
  have habs : |(f - g) x| ≤ 0 := by
    refine abs_le_of_laplacian_eq_mul_abs_le_frontier (c := c) (f := f - g) hK le_rfl
      (hfcont.sub hgcont) (fun y hy => (hfcd hy).sub (hgcd hy)) hc (fun y hy => ?_)
      (fun y hy => ?_) hxK
    · rw [(hfcd hy).laplacian_sub (hgcd hy), Pi.sub_apply, mul_sub]
      linarith [hlap hy]
    · rw [Pi.sub_apply, hbdry hy]
      simp
  rw [Pi.sub_apply] at habs
  exact sub_eq_zero.mp (abs_nonpos_iff.mp habs)

end Nontrivial

/-! ### The whole space

On all of `E` there is no frontier. For a positive constant `c` an upper bound replaces the
boundary condition: the perturbation `f - δ ‖·‖²` attains its maximum, where the second-derivative
test bounds `c f` by `2 (dim E) δ`. -/

/-- **Maximum principle on the whole space for `-Δ + c`, `c > 0`.** A `C²` function on all of `E`
that is bounded above and a subsolution of `-Δ + c` (`c f ≤ Δ f`) for a positive constant `c` is
nonpositive. -/
theorem nonpos_of_mul_le_laplacian_of_bddAbove {c : ℝ} (hc : 0 < c) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hbdd : BddAbove (Set.range f)) (hsub : ∀ x, c * f x ≤ Δ f x) (x : E) :
    f x ≤ 0 := by
  obtain ⟨M, hM⟩ := hbdd
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  -- For every `δ > 0`, `f x ≤ δ (2 n / c + ‖x‖²)`.
  have key : ∀ δ > 0, f x ≤ δ * (2 * n / c + ‖x‖ ^ 2) := by
    intro δ hδ
    set v : E → ℝ := fun y => f y + (-δ) • ‖y‖ ^ 2
    have hv : Continuous v := hf.continuous.add (by fun_prop)
    have hlim : Filter.Tendsto v (Filter.cocompact E) Filter.atBot := by
      refine Filter.tendsto_atBot_mono (fun y => ?_ : ∀ y, v y ≤ M + -δ * ‖y‖ ^ 2) ?_
      · have := hM ⟨y, rfl⟩
        simp only [v, smul_eq_mul]
        linarith
      · exact Filter.tendsto_atBot_add_const_left _ M <| Filter.Tendsto.const_mul_atTop_of_neg
          (neg_neg_of_pos hδ) <| (Filter.tendsto_pow_atTop two_ne_zero).comp
            tendsto_norm_cocompact_atTop
    obtain ⟨x₀, hx₀⟩ := hv.exists_forall_ge hlim
    have hcd : ContDiffAt ℝ 2 f x₀ := hf.contDiffAt
    have hlap := laplacian_nonpos_of_isLocalMax
      (hcd.add ((contDiff_norm_sq ℝ).contDiffAt.const_smul (-δ)))
      (Filter.Eventually.of_forall hx₀ : IsLocalMax v x₀)
    rw [laplacian_add_const_smul_norm_sq _ hcd] at hlap
    have h₀ : f x₀ ≤ 2 * n / c * δ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith [hsub x₀]
    have hx := hx₀ x
    simp only [v, smul_eq_mul] at hx
    nlinarith [sq_nonneg ‖x₀‖]
  refine ge_of_tendsto (?_ : Filter.Tendsto (fun δ : ℝ => δ * (2 * n / c + ‖x‖ ^ 2))
    (𝓝[>] 0) (𝓝 0)) (eventually_mem_nhdsWithin.mono key)
  have hcont : Continuous fun δ : ℝ => δ * (2 * n / c + ‖x‖ ^ 2) := by fun_prop
  simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **Liouville theorem for `-Δ + c`, `c > 0`.** A bounded `C²` solution of `Δ f = c f` on all
of `E`, for a positive constant `c`, vanishes. -/
theorem eq_zero_of_laplacian_eq_mul_of_isBounded {c : ℝ} (hc : 0 < c) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hbdd : Bornology.IsBounded (Set.range f))
    (hsol : ∀ x, Δ f x = c * f x) : f = 0 := by
  rw [isBounded_iff_bddBelow_bddAbove] at hbdd
  ext x
  refine le_antisymm (nonpos_of_mul_le_laplacian_of_bddAbove hc hf hbdd.2 (fun y => (hsol y).ge) x)
    ?_
  have hneg : BddAbove (Set.range (-f)) := by
    obtain ⟨m, hm⟩ := hbdd.1
    exact ⟨-m, by rintro _ ⟨y, rfl⟩; simpa using hm ⟨y, rfl⟩⟩
  have := nonpos_of_mul_le_laplacian_of_bddAbove (f := -f) hc hf.neg hneg (fun y => ?_) x
  · simpa using this
  · rw [laplacian_neg, Pi.neg_apply, Pi.neg_apply, hsol y, mul_neg]

end TauCeti

end
