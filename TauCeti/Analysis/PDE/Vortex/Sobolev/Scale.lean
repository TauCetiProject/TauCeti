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
inverse that is bounded on `L²` and orthogonal to the weak kernel. At a smooth vortex lying in
`A_m^s` for a single `s > 2`, the same holds for every `k ≤ s`.

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
* `exists_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one_of_mem_framedFieldSpace`:
  at a smooth vortex lying in `A_m^s` for a single `s > 2`, the weak right inverse `Q` maps `H^k`
  into `H^(k+1)` for every `k ≤ s`, by elliptic regularity at finite order
  (`mem_sobolevFields_add_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedAdjoint_eq`).
* `exists_mem_sobolevFields_contDiff_gaugeFixedOperator_ae_eq`: at such a vortex, for
  `2 ≤ k ≤ s`, every `g ∈ sobolevFields k` agrees almost everywhere with `L_x y` for a `C^(k-1)`
  field `y ∈ sobolevFields (k + 1)`. For `k ≥ 2` the field `Q g ∈ H^(k+1)` has a `C^(k-1)`
  representative, and a `C¹` weak solution solves `L_x y = g` almost everywhere
  (`gaugeFixedOperator_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq`). This is the vanishing of
  the cokernel of `L_x` at finite regularity, in the realization `H^(k+1) → H^k` of
  `gaugeFixedOperator_mem_sobolevFields`; no bundled operator on equivalence classes is
  constructed.

The vortex hypotheses enter only through the spectral gap of `L_x*`, which needs `|α| → 1` at
infinity, and through the elliptic bootstrap, which needs bounded derivatives of `x`. A
continuous field in every `A_m^k` is smooth with bounded derivatives
(`contDiff_of_forall_mem_framedFieldSpace`,
`exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace`), and `|α| → 1` by the end framing.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
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
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem i n)
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
    (exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem)
    (Lp.memLp (Q (hfL.toLp f))) hf hfc fun η hη hηc ↦ by
      rw [(hQ _).1.isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by norm_cast)) hηc]
      exact integral_congr_ae (hfL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  exact ⟨y, hy, hyk, heq⟩

/-- **The right inverse on the Sobolev scale at finite regularity.** Let `x` be a smooth vortex in
`A_m^s`, `s > 2`. There is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` such that

* `Q g` is a weak solution of `L_x y = g` for every `g ∈ L²`, orthogonal to the weak kernel of
  `L_x` (`IsMinimalGaugeFixedWeakSolution`);
* `Q` gains one derivative: it maps `H^k` into `H^(k+1)` for every `k ≤ s`.

For a vortex lying in every `A_m^j` this is
`exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one`. -/
theorem exists_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one_of_mem_framedFieldSpace
    {s : ℝ} (hs : 2 < s) (hx : x ∈ framedFieldSpace ρ m s) (hxs : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      ∀ g, IsMinimalGaugeFixedWeakSolution volume x g (Q g) ∧
        ∀ k : ℕ, k ≤ s → (g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k →
          (Q g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) := by
  obtain ⟨Q, hQ⟩ := exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution
    (μ := volume) (hxs.of_le (by simp)) hsol
    (tendsto_normSq_of_mem_framedFieldSpace (by linarith) hx hxs.continuous)
  exact ⟨Q, fun g ↦ ⟨hQ g, fun k hks hg ↦
    mem_sobolevFields_add_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedAdjoint_eq
      hs hks hx hxs (Lp.memLp _) hg
      fun η hη hηc ↦
        (hQ g).isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by simp)) hηc⟩⟩

/-- **Vanishing of the cokernel on the Sobolev scale at finite regularity.** Let `x` be a smooth
vortex in `A_m^s`, `s > 2`, and let `2 ≤ k ≤ s`. Every `g ∈ sobolevFields k` agrees almost
everywhere with `gaugeFixedOperator x y` for some `C^(k-1)` field `y ∈ sobolevFields (k + 1)`. -/
theorem exists_mem_sobolevFields_contDiff_gaugeFixedOperator_ae_eq {s : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hs : 2 < s) (hks : k ≤ s) (hx : x ∈ framedFieldSpace ρ m s) (hxs : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hg : g ∈ sobolevFields k) :
    ∃ y ∈ sobolevFields (k + 1), ContDiff ℝ (k - 1 : ℕ) y ∧
      gaugeFixedOperator x y =ᵐ[volume] g := by
  obtain ⟨Q, hQ⟩ :=
    exists_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields_add_one_of_mem_framedFieldSpace
      hs hx hxs hsol
  have hgL := memLp_of_mem_sobolevFields hg
  set u := Q (hgL.toLp g)
  have hu : (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) :=
    (hQ _).2 k hks (mem_sobolevFields_of_ae_eq hg hgL.coeFn_toLp.symm)
  -- A `C^(k-1)` representative of `u ∈ H^(k+1)`.
  obtain ⟨y, hyd, huy⟩ := exists_contDiff_ae_eq_of_mem_sobolevFields (n := k - 1)
    (by rw [Nat.cast_sub (by omega)]; push_cast; linarith) hu
  refine ⟨y, mem_sobolevFields_of_ae_eq hu huy, hyd, ?_⟩
  refine gaugeFixedOperator_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq hxs.continuous
    (hyd.of_le (by exact_mod_cast (by omega : 1 ≤ k - 1))) (hgL.locallyIntegrable (by norm_num))
    fun η hη hηc ↦ ?_
  have h := (hQ (hgL.toLp g)).1.isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by simp))
    hηc
  have h₁ : ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
    integral_congr_ae (by filter_upwards [huy] with z hz; rw [hz])
  have h₂ : ∫ z, ⟪hgL.toLp g z, η z⟫ = ∫ z, ⟪g z, η z⟫ :=
    integral_congr_ae (by filter_upwards [hgL.coeFn_toLp] with z hz; rw [hz])
  rwa [← h₁, ← h₂]

end TauCeti.Vortex
