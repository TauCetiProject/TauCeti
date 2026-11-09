/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.Kernel
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# Periodization of compactly supported functions to the torus

For a compactly supported function `f : (d → ℝ) → ℂ`, the periodization
`TauCeti.UnitAddTorus.periodize f` is the function on the torus `UnitAddTorus d = (ℝ / ℤ)^d`
whose lift to `d → ℝ` is `x ↦ ∑ ℓ : d → ℤ, f (x + ℓ)` (`TauCeti.UnitAddTorus.periodize_coe`).
Near each point only finitely many translates of `f` are nonzero, so the periodization of a
smooth `f` is a smooth function on the torus (`TauCeti.UnitAddTorus.periodize_mem_smoothFunctions`).

When the support of `f` lies in a set `S` that meets none of its translates by nonzero integer
vectors, for instance a set of diameter less than one
(`TauCeti.UnitAddTorus.eq_zero_of_add_mem_of_diam_lt_one`), at most one translate is nonzero at
each point. Then the periodization agrees with `f` on `S`
(`TauCeti.UnitAddTorus.periodize_coe_of_mem`), and its `C^N` norms are those of `f`
(`TauCeti.UnitAddTorus.derivBound_periodize`). Periodization takes tensor products
`f(x) g(y)` to tensor products on the product torus (`TauCeti.UnitAddTorus.periodize_tensor`).

These are the facts that move the Fourier-series arguments on the torus, such as the Schwartz
kernel theorem of `TauCeti.Analysis.Fourier.Torus.Kernel`, to smooth functions supported in a
small compact subset of `d → ℝ`.

## Main definitions

* `TauCeti.UnitAddTorus.periodize`: the periodization of a function on `d → ℝ`.

## Main results

* `TauCeti.UnitAddTorus.periodize_coe`: the lift of the periodization is the sum of the integer
  translates.
* `TauCeti.UnitAddTorus.periodize_mem_smoothFunctions`: the periodization of a smooth compactly
  supported function is smooth.
* `TauCeti.UnitAddTorus.periodize_coe_of_mem`, `TauCeti.UnitAddTorus.derivBound_periodize`: on a
  set meeting none of its nonzero integer translates, the periodization agrees with `f`, and its
  derivatives are bounded by those of `f`.
* `TauCeti.UnitAddTorus.periodize_tensor`: periodization of tensor products.
-/

public section

noncomputable section

open Filter Function Set Topology
open scoped ContDiff

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*}

/-- The periodization of `f : (d → ℝ) → ℂ`: the function on the torus whose lift to `d → ℝ` is
`x ↦ ∑ ℓ : d → ℤ, f (x + ℓ)` (`TauCeti.UnitAddTorus.periodize_coe`). -/
def periodize (f : (d → ℝ) → ℂ) (z : UnitAddTorus d) : ℂ :=
  ∑' ℓ : d → ℤ, f ((fun i ↦ (AddCircle.equivIco 1 0 (z i) : ℝ)) + fun i ↦ (ℓ i : ℝ))

/-- The lift of the periodization to `d → ℝ` is the sum of the integer translates of `f`. -/
theorem periodize_coe (f : (d → ℝ) → ℂ) (x : d → ℝ) :
    periodize f (fun i ↦ (x i : UnitAddCircle)) = ∑' ℓ : d → ℤ, f (x + fun i ↦ (ℓ i : ℝ)) := by
  -- The chosen representative differs from `x` by an integer vector `m`.
  obtain ⟨m, hm⟩ := coe_eq_coe_iff.1 (funext fun i ↦ AddCircle.coe_equivIco (p := (1 : ℝ))
    (a := 0) (y := (x i : UnitAddCircle)))
  have hr := eq_sub_of_add_eq hm.symm
  simp only [periodize]
  rw [hr, ← (Equiv.subRight m).tsum_eq fun ℓ ↦ f (x + fun i ↦ (ℓ i : ℝ))]
  congr 1 with ℓ
  congr 1 with i
  simp only [Pi.add_apply, Equiv.subRight_apply, Pi.sub_apply, Int.cast_sub]
  ring

/-! ### Local finiteness -/

variable {f g : (d → ℝ) → ℂ}

/-- Near each point, only finitely many integer translates of a compactly supported function are
nonzero. -/
theorem _root_.HasCompactSupport.exists_finset_eventually_comp_add_eq_zero [Finite d]
    (hf : HasCompactSupport f) (x₀ : d → ℝ) :
    ∃ s : Finset (d → ℤ), ∀ᶠ x in 𝓝 x₀, ∀ ℓ ∉ s, f (x + fun i ↦ (ℓ i : ℝ)) = 0 := by
  have := Fintype.ofFinite d
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  have hfin := ((isCompact_closedBall (0 : d → ℤ) (R + ‖x₀‖ + 1)).finite_of_discrete)
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx ℓ hℓ
  refine image_eq_zero_of_notMem_tsupport fun hmem ↦ hℓ ?_
  rw [Finite.mem_toFinset, mem_closedBall_zero_iff]
  have h1 : ‖x + fun i ↦ (ℓ i : ℝ)‖ ≤ R := mem_closedBall_zero_iff.1 (hR hmem)
  have h2 : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    linarith [norm_sub_norm_le x x₀]
  have h3 : ‖fun i ↦ (ℓ i : ℝ)‖ ≤ R + ‖x₀‖ + 1 := by
    have := norm_sub_le (x + fun i ↦ (ℓ i : ℝ)) x
    rw [add_sub_cancel_left] at this
    linarith
  refine (pi_norm_le_iff_of_nonneg
    (by linarith [norm_nonneg (x + fun i ↦ (ℓ i : ℝ)), norm_nonneg x₀])).2 fun i ↦ ?_
  rw [← Int.norm_cast_real]
  exact (norm_le_pi_norm (fun i ↦ (ℓ i : ℝ)) i).trans h3

/-- The integer translates of a compactly supported function at a point are summable. -/
theorem _root_.HasCompactSupport.summable_comp_add [Finite d] (hf : HasCompactSupport f)
    (x : d → ℝ) :
    Summable fun ℓ : d → ℤ ↦ f (x + fun i ↦ (ℓ i : ℝ)) := by
  obtain ⟨s, hs⟩ := hf.exists_finset_eventually_comp_add_eq_zero x
  exact summable_of_ne_finset_zero hs.self_of_nhds

theorem periodize_add [Finite d] (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    periodize (f + g) = periodize f + periodize g := by
  ext z
  exact (hf.summable_comp_add _).tsum_add (hg.summable_comp_add _)

theorem periodize_smul (c : ℂ) (f : (d → ℝ) → ℂ) : periodize (c • f) = c • periodize f := by
  ext z
  exact tsum_mul_left

/-- On a set meeting none of its nonzero integer translates and containing the support of `f`,
the periodization of `f` agrees with `f`. -/
theorem periodize_coe_of_mem {S : Set (d → ℝ)}
    (hS : ∀ x ∈ S, ∀ ℓ : d → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ S → ℓ = 0)
    (hfS : support f ⊆ S) {x : d → ℝ} (hx : x ∈ S) :
    periodize f (fun i ↦ (x i : UnitAddCircle)) = f x := by
  rw [periodize_coe, tsum_eq_single 0 fun ℓ hℓ ↦ ?_]
  · congr 1 with i
    simp
  · exact notMem_support.1 fun h ↦ hℓ (hS x hx ℓ (hfS h))

/-! ### Smoothness and derivative bounds -/

variable [Fintype d]

/-- The sum of the integer translates of a smooth compactly supported function is smooth. -/
theorem contDiff_tsum_comp_add (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ fun x : d → ℝ ↦ ∑' ℓ : d → ℤ, f (x + fun i ↦ (ℓ i : ℝ)) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ ↦ ?_
  obtain ⟨s, hs⟩ := hc.exists_finset_eventually_comp_add_eq_zero x₀
  refine ContDiffAt.congr_of_eventuallyEq ?_ (hs.mono fun x hx ↦ tsum_eq_sum hx)
  exact (ContDiff.sum fun ℓ _ ↦ hf.comp (contDiff_id.add contDiff_const)).contDiffAt

/-- The periodization of a smooth compactly supported function is smooth. -/
theorem periodize_mem_smoothFunctions (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    periodize f ∈ smoothFunctions d := by
  rw [mem_smoothFunctions]
  simpa only [periodize_coe] using contDiff_tsum_comp_add hf hc

/-- A set of diameter less than one, in the sup norm of `d → ℝ`, meets none of its translates by
nonzero integer vectors. -/
theorem eq_zero_of_add_mem_of_diam_lt_one {S : Set (d → ℝ)} (hb : Bornology.IsBounded S)
    (hS : Metric.diam S < 1) {x : d → ℝ} (hx : x ∈ S) {ℓ : d → ℤ}
    (hxℓ : x + (fun i ↦ (ℓ i : ℝ)) ∈ S) : ℓ = 0 := by
  have h := Metric.dist_le_diam_of_mem hb hxℓ hx
  rw [dist_eq_norm, add_sub_cancel_left] at h
  ext i
  rw [Pi.zero_apply, ← Int.abs_lt_one_iff, ← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
  exact ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm (fun i ↦ (ℓ i : ℝ)) i)).trans_lt
    (h.trans_lt hS)

/-- If the support of a smooth compactly supported `f` lies in a set meeting none of its nonzero
integer translates, the derivatives of the periodization of `f` are bounded by those of `f`. -/
theorem derivBound_periodize {S : Set (d → ℝ)}
    (hS : ∀ x ∈ S, ∀ ℓ : d → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ S → ℓ = 0)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hfS : tsupport f ⊆ S) {N : ℕ} {M : ℝ}
    (hM : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M) : DerivBound N M (periodize f) := by
  rw [derivBound_iff]
  intro j hj x₀
  simp only [periodize_coe]
  obtain ⟨s, hs⟩ := hc.exists_finset_eventually_comp_add_eq_zero x₀
  have hsmooth (ℓ : d → ℤ) : ContDiff ℝ ∞ fun x ↦ f (x + fun i ↦ (ℓ i : ℝ)) :=
    hf.comp (contDiff_id.add contDiff_const)
  -- Near `x₀` the periodization is a finite sum of translates.
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (hs.mono fun x hx ↦ tsum_eq_sum hx) j).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply fun ℓ _ ↦ (hsmooth ℓ).contDiffAt.of_le (mod_cast le_top)]
  simp only [iteratedFDeriv_comp_add_right]
  have hzero (ℓ : d → ℤ) (hℓ : x₀ + (fun i ↦ (ℓ i : ℝ)) ∉ tsupport f) :
      iteratedFDeriv ℝ j f (x₀ + fun i ↦ (ℓ i : ℝ)) = 0 :=
    notMem_support.1 fun h ↦ hℓ (support_iteratedFDeriv_subset j h)
  by_cases h : ∃ ℓ ∈ s, x₀ + (fun i ↦ (ℓ i : ℝ)) ∈ tsupport f
  · -- At most one translate meets the support of `f`.
    obtain ⟨ℓ₀, hℓ₀s, hℓ₀⟩ := h
    rw [Finset.sum_eq_single_of_mem ℓ₀ hℓ₀s fun ℓ _ hℓ ↦ hzero ℓ fun hmem ↦ hℓ ?_]
    · exact hM j hj _
    · have := hS _ (hfS hℓ₀) (ℓ - ℓ₀) (by convert hfS hmem using 1; ext i; simp)
      exact sub_eq_zero.1 this
  · push Not at h
    rw [Finset.sum_eq_zero fun ℓ hℓ ↦ hzero ℓ (h ℓ hℓ), norm_zero]
    exact (norm_nonneg _).trans (hM 0 (Nat.zero_le _) x₀)

/-! ### Tensor products -/

variable {a b : Type*} [Finite a] [Finite b]

/-- The periodization of a tensor product `f(x) g(y)` of compactly supported functions is the
tensor product of their periodizations on the product torus `UnitAddTorus (a ⊕ b)`. -/
theorem periodize_tensor {f : (a → ℝ) → ℂ} {g : (b → ℝ) → ℂ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) :
    periodize (fun x : a ⊕ b → ℝ ↦ f (fun i ↦ x (.inl i)) * g (fun i ↦ x (.inr i))) =
      tensor (periodize f) (periodize g) := by
  ext z
  obtain ⟨x, rfl⟩ := surjective_coe z
  rw [periodize_coe, tensor_apply, periodize_coe (x := fun i ↦ x (.inl i)),
    periodize_coe (x := fun i ↦ x (.inr i)),
    tsum_mul_tsum_of_summable_norm (hf.summable_comp_add _).norm (hg.summable_comp_add _).norm,
    ← (Equiv.sumArrowEquivProdArrow a b ℤ).tsum_eq]
  rfl

end TauCeti.UnitAddTorus
