/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Asymptotics.Defs
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Principal parts at an isolated singularity with smooth `∂bar`

For coefficients `c : Fin n → ℂ` and a point `z`, the **principal part sum**
(`TauCeti.principalPartSum c z`) is the function

`w ↦ ∑_{j < n} c_j / (w - z)^(j + 1)`.

A function `f` **has principal part `c` at `z`** (`TauCeti.HasPrincipalPart f z c`) if
`f - principalPartSum c z` is bounded on a punctured neighbourhood of `z`. A principal part sum
that is bounded near `z` has zero coefficients (`TauCeti.eq_zero_of_isBigO_principalPartSum`), so
a function has at most one principal part of each order (`TauCeti.HasPrincipalPart.unique`), and
principal parts are additive and homogeneous. `TauCeti.principalPart f z n` selects it when it
exists, and is `0` otherwise.

The main result is a removable-singularity theorem for the inhomogeneous Cauchy–Riemann
equation. Let `η` be real differentiable on a punctured neighbourhood of `z`, with
`∂bar η = β` there for a function `β` of class `Cᵏ`, `k ≥ 1`, on a full neighbourhood of `z`,
and suppose that `(w - z)ⁿ η(w)` is bounded near `z`. Then

`η = g + principalPartSum c z`  on a punctured neighbourhood of `z`,

for some coefficients `c : Fin n → ℂ` and a function `g` of class `Cᵏ` at `z`
(`TauCeti.exists_contDiffAt_eventuallyEq_add_principalPartSum`). Indeed, subtracting a local
solution `G` of `∂bar G = β` leaves a function holomorphic on the punctured neighbourhood with a
pole of order at most `n`; its principal part is found by induction on `n`, and what remains has
a removable singularity. For `n = 0` this says that a bounded solution of `∂bar η = β` extends
across `z` with the regularity of `β`.

This is the local structure of the quotient `δα / α` of a variation of a plane vortex by its
section near a zero of the section, whose principal parts parametrize the kernel of the
linearized vortex equations.

## Main definitions

* `TauCeti.principalPartSum c z`: the function `w ↦ ∑_{j < n} c_j / (w - z)^(j + 1)`.
* `TauCeti.HasPrincipalPart f z c`: `f - principalPartSum c z` is bounded near `z`.
* `TauCeti.principalPart f z n`: the principal part of order `n` of `f` at `z`, or `0`.

## Main results

* `TauCeti.eq_zero_of_isBigO_principalPartSum`: a bounded principal part sum vanishes.
* `TauCeti.HasPrincipalPart.unique`, `TauCeti.HasPrincipalPart.add`,
  `TauCeti.HasPrincipalPart.const_mul`: uniqueness and linearity of principal parts.
* `TauCeti.hasPrincipalPart_of_eventuallyEq_add`: a principal part sum plus a function
  continuous at `z` has that principal part.
* `TauCeti.exists_contDiffAt_eventuallyEq_add_principalPartSum`: a function with `Cᵏ`
  `∂bar` near `z` and a pole of order at most `n` is a principal part sum plus a function of
  class `Cᵏ` at `z`; in particular it has a principal part of order `n` there.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I.
-/

public section

noncomputable section

open Asymptotics Complex Filter Function Set Topology

namespace TauCeti

/-! ### Principal part sums -/

section Sum

variable {n : ℕ}

/-- The **principal part sum** with coefficients `c` at `z`: the function
`w ↦ ∑_{j < n} c_j / (w - z)^(j + 1)`. -/
def principalPartSum (c : Fin n → ℂ) (z w : ℂ) : ℂ :=
  ∑ j, c j / (w - z) ^ (j.val + 1)

theorem principalPartSum_def (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum c z w = ∑ j, c j / (w - z) ^ (j.val + 1) :=
  (rfl)

/-- The principal part sum with zero coefficients vanishes. -/
@[simp]
theorem principalPartSum_zero (z : ℂ) : principalPartSum (0 : Fin n → ℂ) z = 0 := by
  funext w
  simp [principalPartSum]

theorem principalPartSum_add (c d : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (c + d) z w = principalPartSum c z w + principalPartSum d z w := by
  simp only [principalPartSum, Pi.add_apply, add_div, Finset.sum_add_distrib]

theorem principalPartSum_smul (a : ℂ) (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (a • c) z w = a * principalPartSum c z w := by
  simp only [principalPartSum, Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

theorem principalPartSum_sub (c d : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (c - d) z w = principalPartSum c z w - principalPartSum d z w := by
  simp only [principalPartSum, Pi.sub_apply, sub_div, Finset.sum_sub_distrib]

/-- Prepending a coefficient:
`principalPartSum (a, c) z w = (a + principalPartSum c z w) / (w - z)`. -/
theorem principalPartSum_cons (a : ℂ) (c : Fin n → ℂ) (z w : ℂ) :
    principalPartSum (Fin.cons a c : Fin (n + 1) → ℂ) z w =
      (a + principalPartSum c z w) / (w - z) := by
  simp only [principalPartSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, pow_zero, one_mul, add_div, Finset.sum_div, div_div, pow_succ]

/-- A principal part sum is holomorphic off its pole. -/
theorem differentiableAt_principalPartSum (c : Fin n → ℂ) {z w : ℂ} (hw : w ≠ z) :
    DifferentiableAt ℂ (principalPartSum c z) w := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
  unfold principalPartSum
  fun_prop (disch := exact pow_ne_zero _ hwz)

/-- **A bounded principal part sum vanishes.** If `∑_{j < n} c_j / (w - z)^(j + 1)` is bounded on
a punctured neighbourhood of `z`, then all the coefficients `c_j` are zero. -/
theorem eq_zero_of_isBigO_principalPartSum {c : Fin n → ℂ} {z : ℂ}
    (h : principalPartSum c z =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) : c = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    -- Multiplying by `(w - z)^(n + 1)` gives a polynomial whose value at `z` is the top
    -- coefficient; since the sum is bounded, the product also tends to zero.
    have hlast : c (Fin.last n) = 0 := by
      have h₀ : Tendsto (fun w ↦ (w - z) ^ (n + 1) * principalPartSum c z w) (𝓝[≠] z) (𝓝 0) := by
        refine Tendsto.zero_mul_isBoundedUnder_le ?_ ((isBigO_one_iff ℝ).mp h)
        have : Continuous fun w : ℂ ↦ (w - z) ^ (n + 1) := by fun_prop
        simpa using (this.tendsto z).mono_left nhdsWithin_le_nhds
      have hq : Continuous fun w : ℂ ↦ ∑ j : Fin (n + 1), c j * (w - z) ^ (n - j.val) := by
        fun_prop
      have hqz : (∑ j : Fin (n + 1), c j * (z - z) ^ (n - j.val)) = c (Fin.last n) := by
        rw [Finset.sum_eq_single (Fin.last n)]
        · simp
        · intro j _ hj
          have : j.val < n := Fin.val_lt_last hj
          simp [sub_self, zero_pow (Nat.sub_ne_zero_of_lt this)]
        · simp
      have h₁ : Tendsto (fun w ↦ (w - z) ^ (n + 1) * principalPartSum c z w) (𝓝[≠] z)
          (𝓝 (c (Fin.last n))) := by
        rw [← hqz]
        refine ((hq.tendsto z).mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
        rw [principalPartSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [show (w - z) ^ (n + 1) = (w - z) ^ (n - j.val) * (w - z) ^ (j.val + 1) by
          rw [← pow_add]; congr 1; omega]
        field_simp
      exact tendsto_nhds_unique h₁ h₀
    have hc : principalPartSum c z = principalPartSum (fun j : Fin n ↦ c j.castSucc) z := by
      funext w
      simp [principalPartSum, Fin.sum_univ_castSucc, hlast]
    have hrest := ih (hc ▸ h)
    funext j
    induction j using Fin.lastCases with
    | last => exact hlast
    | cast j => exact congrFun hrest j

end Sum

/-! ### Principal parts -/

section PrincipalPart

variable {f g : ℂ → ℂ} {z : ℂ} {n : ℕ} {c d : Fin n → ℂ}

/-- `c` is the **principal part** of order `n` of `f` at `z`: the difference
`f - principalPartSum c z` is bounded on a punctured neighbourhood of `z`. The value of `f` at
`z` plays no role. -/
def HasPrincipalPart (f : ℂ → ℂ) (z : ℂ) (c : Fin n → ℂ) : Prop :=
  (fun w ↦ f w - principalPartSum c z w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))

theorem hasPrincipalPart_iff :
    HasPrincipalPart f z c ↔
      (fun w ↦ f w - principalPartSum c z w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) :=
  Iff.rfl

/-- The principal part is zero exactly when the function is bounded near the point. -/
@[simp]
theorem hasPrincipalPart_zero_iff :
    HasPrincipalPart f z (0 : Fin n → ℂ) ↔ f =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) := by
  simp [HasPrincipalPart]

/-- **Uniqueness of principal parts.** -/
theorem HasPrincipalPart.unique (h : HasPrincipalPart f z c) (h' : HasPrincipalPart f z d) :
    c = d := by
  refine sub_eq_zero.mp (eq_zero_of_isBigO_principalPartSum (z := z) ?_)
  refine (IsBigO.sub h' h).congr_left fun w ↦ ?_
  rw [principalPartSum_sub]
  ring

theorem HasPrincipalPart.add (hf : HasPrincipalPart f z c) (hg : HasPrincipalPart g z d) :
    HasPrincipalPart (fun w ↦ f w + g w) z (c + d) := by
  refine (IsBigO.add hf hg).congr_left fun w ↦ ?_
  rw [principalPartSum_add]
  ring

theorem HasPrincipalPart.const_mul (hf : HasPrincipalPart f z c) (a : ℂ) :
    HasPrincipalPart (fun w ↦ a * f w) z (a • c) := by
  refine (IsBigO.const_mul_left hf a).congr_left fun w ↦ ?_
  rw [principalPartSum_smul]
  ring

/-- A function that is a principal part sum plus a function continuous at `z`, on a punctured
neighbourhood of `z`, has that principal part. -/
theorem hasPrincipalPart_of_eventuallyEq_add (hg : ContinuousAt g z)
    (hfg : ∀ᶠ w in 𝓝[≠] z, f w = g w + principalPartSum c z w) : HasPrincipalPart f z c :=
  IsBigO.congr' (hg.tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds)
    (hfg.mono fun w hw ↦ by simp only [hw]; ring) EventuallyEq.rfl

/-- Changing a function on a punctured neighbourhood of `z` does not change its principal
part. -/
theorem HasPrincipalPart.congr (hf : HasPrincipalPart f z c) (hfg : f =ᶠ[𝓝[≠] z] g) :
    HasPrincipalPart g z c :=
  IsBigO.congr' hf (hfg.mono fun w hw ↦ by simp only [hw]) EventuallyEq.rfl

open scoped Classical in
/-- The **principal part** of order `n` of `f` at `z`: the coefficients `c` with
`HasPrincipalPart f z c` when they exist (they are then unique), and `0` otherwise. -/
def principalPart (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : Fin n → ℂ :=
  if h : ∃ c : Fin n → ℂ, HasPrincipalPart f z c then h.choose else 0

theorem hasPrincipalPart_principalPart (h : ∃ c : Fin n → ℂ, HasPrincipalPart f z c) :
    HasPrincipalPart f z (principalPart f z n) := by
  simp only [principalPart, h, ↓reduceDIte]
  exact h.choose_spec

theorem HasPrincipalPart.principalPart_eq (h : HasPrincipalPart f z c) :
    principalPart f z n = c :=
  (hasPrincipalPart_principalPart ⟨c, h⟩).unique h

end PrincipalPart

/-! ### Existence of principal parts -/

section Existence

variable {z : ℂ}

/-- A bounded function holomorphic on a punctured neighbourhood of `z` agrees there with a
function analytic at `z`. -/
private theorem exists_analyticAt_eventuallyEq {h : ℂ → ℂ}
    (hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ h w)
    (hb : h =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧ h =ᶠ[𝓝[≠] z] H := by
  obtain ⟨C, hC⟩ := hb.bound
  have hev : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ h w ∧ ‖h w‖ ≤ C := by
    filter_upwards [hd, hC] with w hw hwC
    exact ⟨hw, by simpa using hwC⟩
  have hs := eventually_nhdsWithin_iff.mp hev
  refine ⟨update h z (limUnder (𝓝[≠] z) h),
    (Complex.differentiableOn_update_limUnder_of_bddAbove hs (fun w hw ↦ ?_) ⟨C, ?_⟩).analyticAt
      hs, ?_⟩
  · exact (hw.1 hw.2).1.differentiableWithinAt
  · rintro _ ⟨w, hw, rfl⟩
    exact (hw.1 hw.2).2
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact (update_of_ne hw _ _).symm

/-- A function holomorphic on a punctured neighbourhood of `z` with a pole of order at most `n`
has a principal part of order `n` there. -/
private theorem exists_hasPrincipalPart_of_differentiableAt :
    ∀ (n : ℕ) {h : ℂ → ℂ}, (∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ h w) →
      (fun w ↦ (w - z) ^ n * h w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) →
      ∃ c : Fin n → ℂ, HasPrincipalPart h z c
  | 0, h, _, hb => ⟨0, hasPrincipalPart_zero_iff.mpr (by simpa using hb)⟩
  | n + 1, h, hd, hb => by
    -- The principal part of `(w - z) h` has order `n`; what remains after removing it extends
    -- holomorphically across `z`, and dividing by `w - z` adds one coefficient.
    obtain ⟨c, hc⟩ := exists_hasPrincipalPart_of_differentiableAt n (h := fun w ↦ (w - z) * h w)
      (hd.mono fun w hw ↦ (differentiableAt_id.sub_const z).mul hw)
      (hb.congr_left fun w ↦ by ring)
    obtain ⟨B, hB, hbB⟩ := exists_analyticAt_eventuallyEq (h := fun w ↦ (w - z) * h w -
        principalPartSum c z w) (by
      filter_upwards [hd, self_mem_nhdsWithin] with w hw hwz
      exact ((differentiableAt_id.sub_const z).mul hw).sub
        (differentiableAt_principalPartSum c hwz)) hc
    refine ⟨Fin.cons (B z) c, ?_⟩
    obtain ⟨C, hC⟩ := hB.differentiableAt.isBigO_sub.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hbB, nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with w hw hwC hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    have heq : h w - principalPartSum (Fin.cons (B z) c) z w = (B w - B z) / (w - z) := by
      rw [principalPartSum_cons, ← hw]
      field_simp
      ring
    rw [heq, norm_div, norm_one, mul_one, div_le_iff₀ (norm_pos_iff.mpr hwz')]
    exact hwC

/-- **Principal parts at a singularity with smooth `∂bar`.** Let `η` be real differentiable on a
punctured neighbourhood of `z`, with `∂bar η = β` there, where `β` is of class `Cᵏ`, `k ≥ 1`, on a
neighbourhood of `z`. If `(w - z)ⁿ η(w)` is bounded near `z`, then on a punctured neighbourhood of
`z`, `η = g + principalPartSum c z` for some coefficients `c : Fin n → ℂ` and a function `g` of
class `Cᵏ` at `z`. -/
theorem exists_contDiffAt_eventuallyEq_add_principalPartSum {η β : ℂ → ℂ} {U : Set ℂ}
    {k : ℕ∞} {n : ℕ} (hk : 1 ≤ k) (hU : U ∈ 𝓝 z) (hβ : ContDiffOn ℝ k β U)
    (hη : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℝ η w ∧ conjWirtingerDeriv η w 1 = β w)
    (hb : (fun w ↦ (w - z) ^ n * η w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) :
    ∃ (c : Fin n → ℂ) (g : ℂ → ℂ), ContDiffAt ℝ k g z ∧
      ∀ᶠ w in 𝓝[≠] z, η w = g w + principalPartSum c z w := by
  -- Subtract a local solution `G` of `∂bar G = β`; the difference is holomorphic off `z`.
  obtain ⟨G, hG, hGβ⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq hk
    isOpen_interior (hβ.mono interior_subset) (mem_interior_iff_mem_nhds.mpr hU)
  have hGd : Differentiable ℝ G :=
    hG.differentiable (by exact_mod_cast (zero_lt_one.trans_le hk).ne')
  have hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ (η - G) w := by
    filter_upwards [hη, nhdsWithin_le_nhds hGβ] with w hw hGw
    rw [differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hw.1.sub (hGd w)),
      conjWirtingerDeriv_sub hw.1 (hGd w), sub_apply, hw.2, hGw, sub_self]
  have hbG : (fun w ↦ (w - z) ^ n * G w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ)) :=
    (((continuous_id.sub continuous_const).pow n).mul hG.continuous).continuousAt.tendsto
      |>.isBigO_one ℝ |>.mono nhdsWithin_le_nhds
  obtain ⟨c, hc⟩ := exists_hasPrincipalPart_of_differentiableAt n hd
    ((hb.sub hbG).congr_left fun w ↦ by simp only [Pi.sub_apply]; ring)
  -- What remains after removing the principal part has a removable singularity.
  obtain ⟨H, hH, hhH⟩ := exists_analyticAt_eventuallyEq (by
    filter_upwards [hd, self_mem_nhdsWithin] with w hw hwz
    exact hw.sub (differentiableAt_principalPartSum c hwz)) hc
  refine ⟨c, fun w ↦ G w + H w, hG.contDiffAt.add (hH.contDiffAt.restrict_scalars ℝ), ?_⟩
  filter_upwards [hhH] with w hw
  rw [← hw, Pi.sub_apply]
  ring

end Existence

end TauCeti
