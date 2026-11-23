/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity

/-!
# The gauge-fixed vortex operator on the Sobolev scale

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴` with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a weak solution of `L_x y = f` if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for
every smooth compactly supported test field `η`; for `C¹` fields this is the same as a classical
solution (`forall_integral_inner_gaugeFixedAdjoint_eq_iff`). This file compares weak and classical
`L²` solutions and shows that, at a plane vortex lying in the affine field space `A_m^k` for every
`k`, the operator `L_x` maps `H^(k+1)` onto `H^k` in the weak sense for every `k`, with a right
inverse that is bounded on `L²` and orthogonal to the weak kernel.

* `exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq`: at a smooth field `x` whose
  coordinates have bounded derivatives of every order, a weak `L²` solution of `L_x y = f`, with
  `f` continuous and in every `H^k`, agrees almost everywhere with a smooth classical solution
  lying in every `H^k`. With `f = 0`, the weak `L²` kernel of `L_x` consists of smooth classical
  solutions of `L_x y = 0`; conversely a `C¹`, `L²` classical solution is a weak solution, so
  it is smooth (`contDiff_of_gaugeFixedOperator_eq`) and gains one Sobolev derivative over `f`
  (`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`). So the weak and
  classical `L²` kernels coincide, and lie in every `H^k`.
* `exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one`:
  at a continuous vortex lying in `A_m^k` for every `k`, the weak right inverse `Q` of `L_x` maps
  `H^k` into `H^(k+1)` for every `k`. This is the vanishing of the cokernel of `L_x` on the
  Sobolev scale.
* `exists_contDiff_gaugeFixedOperator_eq_of_forall_mem_framedFieldSpace`: at such a vortex, every
  continuous field lying in every `H^k` is `L_x y` for a smooth `y` lying in every `H^k`.

The vortex hypotheses enter only through the spectral gap of `L_x*`, which needs `|α| → 1` at
infinity, and through the elliptic bootstrap, which needs bounded derivatives of `x`. A
continuous field in every `A_m^k` is smooth with bounded derivatives
(`contDiff_of_forall_mem_framedFieldSpace`,
`exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace`), and `|α| → 1` by the end framing.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff

variable {x y f : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Regularity of weak and classical solutions -/

/-- A square-integrable weak solution of `L_x y = f`, with `f` in every `H^k`, lies in every
`H^k` when `x` is smooth with bounded derivatives: the elliptic bootstrap at every order. -/
private theorem forall_mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq
    (hx : ContDiff ℝ ∞ x) (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) (k : ℕ) :
    y ∈ sobolevFields k := by
  cases k with
  | zero => simpa using hy
  | succ k =>
    exact_mod_cast mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
      (fun i n _ ↦ hbound i n) hy (hf k) hweak

/-- **Weak `L²` solutions are smooth.** Let `x` be a smooth field whose coordinates have bounded
derivatives of every order, and let `y` be a square-integrable weak solution of `L_x y = f`, with
`f` continuous and in every `H^k`. Then `y` agrees almost everywhere with a smooth field lying in
every `H^k` and solving `L_x y = f` everywhere. For `f = 0` this identifies the weak `L²` kernel
of `L_x` with smooth classical solutions of `L_x y = 0`. -/
theorem exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k) (hfc : Continuous f)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∃ y' : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y' ∧ y =ᵐ[volume] y' ∧
      (∀ k : ℕ, y' ∈ sobolevFields k) ∧ ∀ z, gaugeFixedOperator x y' z = f z := by
  have hk := forall_mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq hx hbound hy hf hweak
  obtain ⟨y', hy', hyy'⟩ := exists_contDiff_ae_eq_of_forall_mem_sobolevFields hk
  refine ⟨y', hy', hyy', fun k ↦ mem_sobolevFields_of_ae_eq (hk k) hyy', ?_⟩
  refine (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
    (hy'.of_le (by exact_mod_cast le_top)) hfc).1 fun η hη hηc ↦ ?_
  rw [← hweak η hη hηc]
  exact integral_congr_ae (hyy'.mono fun z hz ↦ by simp only [hz])

/-- **Classical `L²` solutions are smooth.** Let `x` be a smooth field whose coordinates have
bounded derivatives of every order. A square-integrable `C¹` solution of `L_x y = f`, with `f` in
every `H^k`, is smooth. In particular every `C¹` element of the `L²` kernel of `L_x` is
smooth. -/
theorem contDiff_of_gaugeFixedOperator_eq (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : ContDiff ℝ 1 y) (hyL : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k)
    (heq : ∀ z, gaugeFixedOperator x y z = f z) : ContDiff ℝ ∞ y := by
  have hfc : Continuous f := funext heq ▸ continuous_gaugeFixedOperator hx.continuous hy
  obtain ⟨y', hy', hyy', -⟩ := exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq hx
    hbound hyL hf hfc ((forall_integral_inner_gaugeFixedAdjoint_eq_iff hx.continuous hy hfc).2 heq)
  rwa [(hy.continuous.ae_eq_iff_eq volume hy'.continuous).1 hyy']

/-! ### Surjectivity at a vortex -/

variable {ρ : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **The right inverse on the Sobolev scale.** Let `x` be a continuous solution of the plane
vortex equations lying in the affine field space `A_m^k` for every `k`. Then there is a bounded
operator `Q` on `L²(ℂ; ℝ⁴)` such that

* `Q f` is a weak solution of `L_x y = f` for every `f ∈ L²`, orthogonal to the weak kernel of
  `L_x` (`IsMinimalGaugeFixedWeakSolution`);
* `Q` maps `H^k` into `H^(k+1)` for every `k`.

In particular `L_x : H^(k+1) → H^k` is surjective in the weak sense for every `k`: the cokernel of
`L_x` vanishes on the Sobolev scale. This extends to every `k` the case `k = 0`,
`exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields`. -/
theorem exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      ∀ f, IsMinimalGaugeFixedWeakSolution volume x f (Q f) ∧
        ∀ k : ℕ, (f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k →
          (Q f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  have hlim := tendsto_normSq_of_forall_mem_framedFieldSpace hx hmem
  obtain ⟨Q, hQ⟩ := exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution
    (μ := volume) (hxs.of_le (by exact_mod_cast le_top)) hsol hlim
  refine ⟨Q, fun f ↦ ⟨hQ f, fun k hf ↦ ?_⟩⟩
  exact mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hxs
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    (Lp.memLp _) hf fun η hη hηc ↦
      (hQ f).isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by norm_cast)) hηc

/-- **Classical surjectivity at a vortex.** Let `x` be a continuous solution of the plane vortex
equations lying in the affine field space `A_m^k` for every `k`. Every continuous field `f` lying
in every `H^k` is `L_x y` for a smooth field `y` lying in every `H^k`. -/
theorem exists_contDiff_gaugeFixedOperator_eq_of_forall_mem_framedFieldSpace (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k) (hsol : ∀ z, equation x z = 0)
    (hf : ∀ k : ℕ, f ∈ sobolevFields k) (hfc : Continuous f) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ (∀ k : ℕ, y ∈ sobolevFields k) ∧
      ∀ z, gaugeFixedOperator x y z = f z := by
  obtain ⟨Q, hQ⟩ :=
    exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one
      hx hmem hsol
  have hfL : MemLp f 2 volume := by simpa using hf 0
  obtain ⟨y, hy, -, hyk, heq⟩ := exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    (Lp.memLp (Q (hfL.toLp f))) hf hfc fun η hη hηc ↦ by
      rw [(hQ _).1.isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by norm_cast)) hηc]
      exact integral_congr_ae (hfL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  exact ⟨y, hy, hyk, heq⟩

end TauCeti.Vortex
