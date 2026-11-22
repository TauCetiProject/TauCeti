/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import TauCeti.Analysis.Complex.DividedDifference.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Lagrange
import TauCeti.Analysis.Calculus.DSlope.Basic
import TauCeti.Analysis.Complex.DividedDifference.Analytic
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Coordinate polynomial degree control for `partialDslope`

The coordinate divided difference `TauCeti.partialDslope i` at `ζ` agrees with Euclidean division
by `X - C ζ` along polynomial coordinate lines in direction `i`, lowers polynomial degree in `z i`
by one, and preserves polynomial degree bounds in every other coordinate `j ≠ i` for entire
functions (by Lagrange interpolation along coordinate `j` and linearity of `dslope · ζ`). It also
commutes with `partialDeriv j` (`j ≠ i`) and lowers iterated `partialDeriv i` order by one.

## Main results

* `TauCeti.partialDslope_update_eq_eval_divByMonic`: exact polynomial division formula
  `partialDslope i f ζ (update z i w) = (P /ₘ (X - C ζ)).eval w`.
* `TauCeti.exists_natDegree_le_sub_one_and_partialDslope_eq_eval_self`: degree reduction in the
  divided coordinate.
* `TauCeti.exists_degree_lt_and_partialDslope_eq_eval`,
  `TauCeti.exists_natDegree_le_and_partialDslope_eq_eval`: coordinate polynomial degree preservation
  under `partialDslope`.
* `TauCeti.partialDeriv_partialDslope_of_ne`, `TauCeti.iterate_partialDeriv_partialDslope_of_ne`:
  `∂ⱼ` commutes with `f ↦ partialDslope i f ζ` for `j ≠ i`.
* `TauCeti.iterate_partialDeriv_partialDslope_eq_zero`: `partialDslope i f ζ` has lower
  `partialDeriv i`-order than `f`.
-/

public section

open Function Polynomial

namespace TauCeti

variable {ι : Type*} [DecidableEq ι]

/-- If `f` agrees with a polynomial `P` along the `i`-th coordinate line through `z`, then
`partialDslope i f ζ` agrees with `P /ₘ (X - C ζ)` along that line. -/
theorem partialDslope_update_eq_eval_divByMonic {f : (ι → ℂ) → ℂ} {i : ι} {ζ : ℂ}
    {z : ι → ℂ} {P : ℂ[X]} (hP : ∀ w, f (update z i w) = P.eval w) (w : ℂ) :
    partialDslope i f ζ (update z i w) = (P /ₘ (X - C ζ)).eval w := by
  have hPdiv : P = C (P.eval ζ) + (X - C ζ) * (P /ₘ (X - C ζ)) := by
    conv_lhs => rw [← modByMonic_add_div P (X - C ζ), modByMonic_X_sub_C_eq_C_eval]
  have hfun : (fun u ↦ f (update (update z i w) i u)) =
      (fun _ ↦ P.eval ζ) + ((fun u ↦ u - ζ) * fun u ↦ (P /ₘ (X - C ζ)).eval u) := by
    ext u
    simp only [update_idem, hP, Pi.add_apply, Pi.mul_apply]
    conv_lhs => rw [hPdiv]
    simp
  rw [partialDslope_apply, update_self, hfun,
    dslope_add (differentiableAt_const _) (by fun_prop), Pi.add_apply, dslope_const,
    Pi.zero_apply, zero_add, dslope_mul (by fun_prop) (by fun_prop)]
  have hderiv : dslope (fun u : ℂ ↦ u - ζ) ζ w = 1 := by
    rcases eq_or_ne w ζ with rfl | hw
    · simp
    · simp [dslope_of_ne _ hw, slope_def_field, sub_ne_zero.mpr hw]
  simp [hderiv]

/-- **Degree reduction in the divided coordinate.** If `f` is a polynomial of degree at most `e` in
`z i` along the `i`-th coordinate line through `z`, then `partialDslope i f ζ` is a polynomial of
degree at most `e - 1` along that line. -/
theorem exists_natDegree_le_sub_one_and_partialDslope_eq_eval_self {f : (ι → ℂ) → ℂ} (i : ι)
    (ζ : ℂ) {e : ℕ} {z : ι → ℂ}
    (hf : ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update z i w) = Q.eval w) :
    ∃ Q : ℂ[X], Q.natDegree ≤ e - 1 ∧ ∀ w, partialDslope i f ζ (update z i w) = Q.eval w := by
  obtain ⟨P, hPdeg, hP⟩ := hf
  refine ⟨P /ₘ (X - C ζ), ?_, partialDslope_update_eq_eval_divByMonic hP⟩
  calc (P /ₘ (X - C ζ)).natDegree
      = P.natDegree - (X - C ζ).natDegree := natDegree_divByMonic P (monic_X_sub_C ζ)
    _ ≤ e - 1 := by rw [natDegree_X_sub_C]; omega

/-- **Coordinate degree preservation under `partialDslope`.** If `f` is entire and a polynomial of
degree strictly less than `d` in coordinate `j`, then so is `partialDslope i f ζ`. -/
theorem exists_degree_lt_and_partialDslope_eq_eval [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (i j : ι) (ζ : ℂ) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialDslope i f ζ (update z j w) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨P, hPdeg, hP⟩ := hdeg z
    exact ⟨P /ₘ (X - C ζ), (degree_divByMonic_le P _).trans_lt hPdeg,
      partialDslope_update_eq_eval_divByMonic hP⟩
  cases d with
  | bot =>
    obtain ⟨Q, hQ, _⟩ := hdeg z
    exact (not_lt_bot hQ).elim
  | coe d =>
    have := Fintype.ofFinite ι
    let s : Finset ℕ := Finset.range d
    let v : ℕ → ℂ := fun m ↦ (m : ℂ)
    have hv : Set.InjOn v s := Nat.cast_injective.injOn
    refine ⟨Lagrange.interpolate s v (fun m ↦ partialDslope i f ζ (update z j (v m))), ?_,
      fun w ↦ ?_⟩
    · simpa only [s, Finset.card_range, Nat.cast_withBot] using
        Lagrange.degree_interpolate_lt (fun m ↦ partialDslope i f ζ (update z j (v m))) hv
    · have hfun : (fun u ↦ f (update (update z j w) i u)) =
          fun u ↦ ∑ m ∈ s, (Lagrange.basis s v m).eval w * f (update (update z j (v m)) i u) := by
        ext u
        obtain ⟨Qu, hQu_deg, hQu⟩ := hdeg (update z i u)
        have hQu_eq : Qu = Lagrange.interpolate s v (fun m ↦ f (update (update z i u) j (v m))) :=
          Lagrange.eq_interpolate_of_eval_eq _ hv
            (by simpa only [s, Finset.card_range, Nat.cast_withBot] using hQu_deg)
            fun m _ ↦ (hQu (v m)).symm
        rw [update_comm hij, hQu w, hQu_eq, Lagrange.interpolate_apply, eval_finsetSum]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [eval_mul, eval_C, mul_comm, update_comm (Ne.symm hij)]
      have hdiff (m : ℕ) (_ : m ∈ s) : DifferentiableAt ℂ
          (fun u ↦ (Lagrange.basis s v m).eval w * f (update (update z j (v m)) i u)) ζ :=
        ((hf _).comp ζ (hasFDerivAt_update (update z j (v m)) ζ).differentiableAt).const_mul _
      rw [partialDslope_apply, update_of_ne (Ne.symm hij), hfun,
        congrFun (dslope_sum s hdiff) (z i), Lagrange.interpolate_apply, eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [congrFun (dslope_const_mul _ _ ζ) (z i), eval_mul, eval_C, mul_comm, partialDslope_apply,
        update_of_ne (Ne.symm hij)]

/-- If `f` is entire and a polynomial of degree at most `e` in coordinate `j`, then so is
`partialDslope i f ζ`. -/
theorem exists_natDegree_le_and_partialDslope_eq_eval [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (i j : ι) (ζ : ℂ) {e : ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, partialDslope i f ζ (update z j w) = Q.eval w := by
  simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using
    exists_degree_lt_and_partialDslope_eq_eval hf i j ζ (d := Order.succ (e : WithBot ℕ))
      (fun y ↦ by simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using hdeg y) z

section PartialDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Finite ι] [CompleteSpace E]
  {f : (ι → ℂ) → E}

/-- The partial derivative `∂ⱼ` in another variable `j ≠ i` commutes with the divided difference
in the `i`-th variable. -/
theorem partialDeriv_partialDslope_of_ne (hf : Differentiable ℂ f) {i j : ι} (hji : j ≠ i)
    (ζ : ℂ) : partialDeriv j (partialDslope i f ζ) = partialDslope i (partialDeriv j f) ζ := by
  ext z
  rw [partialDeriv_eq_deriv_update (differentiable_partialDslope hf i ζ z)]
  have hupd (s : ℂ) : update z j s i = z i := update_of_ne hji.symm _ _
  by_cases h : z i = ζ
  · -- On the hyperplane `z i = ζ` the divided difference is `∂ᵢ f`, and partial derivatives
    -- commute.
    have hline : (fun s ↦ partialDslope i f ζ (update z j s)) =
        fun s ↦ partialDeriv i f (update z j s) :=
      funext fun s ↦ partialDslope_of_eq (hf _) ((hupd s).trans h)
    rw [hline, ← partialDeriv_eq_deriv_update (differentiable_partialDeriv hf i z),
      partialDslope_of_eq (differentiable_partialDeriv hf j z) h, partialDeriv_comm hf]
  · -- Off the hyperplane, differentiate the difference quotient.
    have hline : (fun s ↦ partialDslope i f ζ (update z j s)) =
        fun s ↦ (z i - ζ)⁻¹ • (f (update z j s) - f (update (update z i ζ) j s)) := by
      funext s
      rw [partialDslope_of_ne ((hupd s).trans_ne h), hupd, update_comm hji]
    have hz : update (update z i ζ) j (z j) = update z i ζ := by
      rw [← update_of_ne hji ζ z, update_eq_self]
    rw [hline, partialDslope_of_ne h]
    refine (((hasDerivAt_comp_update (hf _)).sub (hasDerivAt_comp_update (hf _))).const_smul
      (z i - ζ)⁻¹).deriv.trans ?_
    rw [update_eq_self, hz]

/-- The iterated partial derivatives `∂ⱼ^m` in another variable `j ≠ i` commute with the divided
difference in the `i`-th variable. In particular, if `f` is a polynomial of degree at most `e` in
`zⱼ`, in the sense that `∂ⱼ^(e+1) f = 0`, then so is `partialDslope i f ζ`. -/
theorem iterate_partialDeriv_partialDslope_of_ne (hf : Differentiable ℂ f) {i j : ι}
    (hji : j ≠ i) (ζ : ℂ) (m : ℕ) :
    (partialDeriv j)^[m] (partialDslope i f ζ) = partialDslope i ((partialDeriv j)^[m] f) ζ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_partialDslope_of_ne (differentiable_iterate_partialDeriv hf j m) hji]

/-- **Dividing by `zᵢ - ζ` lowers the degree in `zᵢ`.** If `f` is entire and a polynomial of
degree at most `e` in `zᵢ`, in the sense that `∂ᵢ^(e+1) f = 0`, then `partialDslope i f ζ` is a
polynomial of degree less than `e` in `zᵢ`: `∂ᵢ^e (partialDslope i f ζ) = 0`. -/
theorem iterate_partialDeriv_partialDslope_eq_zero (hf : Differentiable ℂ f) {e : ℕ}
    (he : (partialDeriv i)^[e + 1] f = 0) (ζ : ℂ) :
    (partialDeriv i)^[e] (partialDslope i f ζ) = 0 := by
  ext z
  have hline := congrFun (iteratedDeriv_comp_update (differentiable_partialDslope hf i ζ) i z e)
    (z i)
  rw [update_eq_self] at hline
  rw [Pi.zero_apply, ← hline]
  simp only [partialDslope_update]
  refine congrFun
    (Differentiable.iteratedDeriv_dslope_eq_zero (differentiable_comp_update hf z i) ?_ ζ) (z i)
  rw [iteratedDeriv_comp_update hf, he]
  funext _
  simp

end PartialDeriv

end TauCeti
