/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Algebra.MvPolynomial.Funext

/-!
# The identity theorem across a subfield

Let `C` be a nontrivially normed field which is a normed algebra over a nontrivially normed field
`E`, so that `E` embeds isometrically in `C`. A `C`-analytic function of finitely many variables
that vanishes at the `E`-points `(algebraMap E C (x i))ᵢ` near an `E`-point vanishes near that
point in `C^ι`. Thus an analytic germ over `C` is determined by its values on the `E`-points,
as for `ℝ ⊆ ℂ` or `ℚ_p ⊆ ℂ_p`. No completeness and no characteristic hypothesis is needed.

The algebraic half is `FormalMultilinearSeries.apply_eq_zero_of_forall_algebraMap`: a homogeneous
term `p n (fun _ ↦ z)` of a power series over `C` that vanishes at every `E`-point vanishes
everywhere, for any infinite field `E` below `C`. On the `E`-points such a term is a polynomial map
whose coefficients are the multi-index coefficients `FormalMultilinearSeries.mvCoeff`, and over an
infinite field a polynomial map with vector coefficients determines them
(`TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero`).

## Main declarations

* `FormalMultilinearSeries.apply_eq_zero_of_forall_algebraMap`: a homogeneous term vanishing on
  the `E`-points vanishes.
* `AnalyticAt.eventually_eq_zero_of_eventually_algebraMap`: the identity theorem across a
  subfield.
* `AnalyticAt.eventuallyEq_of_eventually_algebraMap`: two analytic functions agreeing at the
  `E`-points near an `E`-point agree near it.

## References

* P. Schneider, *p-Adic Lie Groups*, Springer, 2011, §5, Corollary 5.8.
* S. Howe, C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Theorem 9.1.3.
-/

public section

open Filter Topology

variable {E C G ι : Type*}

namespace FormalMultilinearSeries

variable [Finite ι] [Field E] [Infinite E] [NormedField C] [Algebra E C]
  [NormedAddCommGroup G] [NormedSpace C G]

/-- **A homogeneous term vanishing at the points of an infinite subfield vanishes.** If the
degree-`n` term `p n (fun _ ↦ z)` of a power series over `C` on `ι → C` vanishes at every point
`z = (algebraMap E C (y i))ᵢ` with `y : ι → E`, for an infinite field `E` below `C`, then it
vanishes at every `z : ι → C`. -/
theorem apply_eq_zero_of_forall_algebraMap (p : FormalMultilinearSeries C (ι → C) G) {n : ℕ}
    (h : ∀ y : ι → E, p n (fun _ ↦ fun i ↦ algebraMap E C (y i)) = 0) (z : ι → C) :
    p n (fun _ ↦ z) = 0 := by
  classical
  have := Fintype.ofFinite ι
  -- view `G` as a vector space over `E` through `C`
  let : Module E G := Module.compHom G (algebraMap E C)
  have : IsScalarTower E C G := IsScalarTower.of_compHom E C G
  -- On the `E`-points the term is a polynomial map with coefficients `p.mvCoeff α` in the
  -- `E`-vector space `G`, so these coefficients vanish.
  have hcoeff (α : ι → ℕ) (hα : α ∈ Finset.univ.piAntidiag n) : p.mvCoeff α = 0 :=
    TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero (K := E) (fun y ↦ by
      simpa [apply_eq_sum_mvCoeff, ← map_pow, ← map_prod, algebraMap_smul] using h y) hα
  rw [apply_eq_sum_mvCoeff]
  exact Finset.sum_eq_zero fun α hα ↦ by rw [hcoeff α hα, smul_zero]

end FormalMultilinearSeries

namespace AnalyticAt

variable [Fintype ι] [NontriviallyNormedField E] [NontriviallyNormedField C] [NormedAlgebra E C]
  [NormedAddCommGroup G] [NormedSpace C G]

/-- **The identity theorem across a subfield.** Let `C` be a normed algebra over `E`, both
nontrivially normed fields. A `C`-analytic function of finitely many variables that vanishes at
the `E`-points near an `E`-point `a` vanishes near `a` in `C^ι`. -/
theorem eventually_eq_zero_of_eventually_algebraMap {F : (ι → C) → G} {a : ι → E}
    (hF : AnalyticAt C F (fun i ↦ algebraMap E C (a i)))
    (h : ∀ᶠ x in 𝓝 a, F (fun i ↦ algebraMap E C (x i)) = 0) :
    ∀ᶠ z in 𝓝 (fun i ↦ algebraMap E C (a i)), F z = 0 := by
  -- view `G` as a normed space over `E` through `C`, to restrict the scalars of `F` to `E`
  let : NormedSpace E G := NormedSpace.restrictScalars E C G
  have : IsScalarTower E C G := IsScalarTower.of_compHom E C G
  obtain ⟨p, r, hp⟩ := hF
  let u : (ι → E) →L[E] (ι → C) := ContinuousLinearMap.piMap fun _ ↦ algebraMapCLM E C
  have hu (x : ι → E) : u x = fun i ↦ algebraMap E C (x i) := rfl
  -- restricted to the `E`-points, the power series of `F` represents the zero function over `E`
  have h0 : HasFPowerSeriesAt 0 ((p.restrictScalars E).compContinuousLinearMap u) a :=
    (hp.hasFPowerSeriesAt.restrictScalars (𝕜 := E)).compContinuousLinearMap (u := u)
      |>.congr (h.mono fun x hx ↦ by simpa [hu] using hx)
  have hp0 (n : ℕ) (z : ι → C) : p n (fun _ ↦ z) = 0 :=
    p.apply_eq_zero_of_forall_algebraMap (fun y ↦ by
      simpa [Function.comp_def, hu] using h0.apply_eq_zero n y) z
  filter_upwards [Metric.eball_mem_nhds _ hp.r_pos] with z hz
  have hz' : z - (fun i ↦ algebraMap E C (a i)) ∈ Metric.eball 0 r := by
    rwa [Metric.mem_eball, edist_zero_right, ← eDist_eq_eNorm_sub]
  have hsum := hp.hasSum hz'
  rw [add_sub_cancel] at hsum
  simp only [hp0] at hsum
  exact hsum.unique hasSum_zero

/-- Two `C`-analytic functions of finitely many variables that agree at the `E`-points near an
`E`-point `a` agree near `a` in `C^ι`. -/
theorem eventuallyEq_of_eventually_algebraMap {F F' : (ι → C) → G} {a : ι → E}
    (hF : AnalyticAt C F (fun i ↦ algebraMap E C (a i)))
    (hF' : AnalyticAt C F' (fun i ↦ algebraMap E C (a i)))
    (h : ∀ᶠ x in 𝓝 a, F (fun i ↦ algebraMap E C (x i)) = F' fun i ↦ algebraMap E C (x i)) :
    F =ᶠ[𝓝 fun i ↦ algebraMap E C (a i)] F' := by
  filter_upwards [(hF.sub hF').eventually_eq_zero_of_eventually_algebraMap
    (h.mono fun x hx ↦ sub_eq_zero.2 hx)] with z hz using sub_eq_zero.1 hz

end AnalyticAt
