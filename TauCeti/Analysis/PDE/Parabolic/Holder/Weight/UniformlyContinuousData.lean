/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.UniformlyContinuousData
public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight.Solvability

/-!
# The weighted Cauchy problem with uniformly continuous initial data

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in `C_b^{α,α/2}`, `0 < α < 1`, with `a` uniformly elliptic, and let `w = exp ℓ` be
a positive time-independent weight whose logarithm `ℓ` is `C²` with bounded `α`-Hölder partial
derivatives `∂ᵢℓ`, `∂ᵢ∂ⱼℓ`. The logarithm itself may be unbounded, so `w` may grow or decay
exponentially at infinity. For the Cauchy problem `P u = F`, `u(·, 0) = G` with
`F / w ∈ C_b^{α,α/2}` and `G / w` bounded and uniformly continuous, this file takes as weighted
solution operator `w` times the solution operator of a conjugated problem, shows that it agrees
with the classical weighted solutions and is the unique continuous linear extension of them, and
bounds it uniformly. It does not prove that its output solves `P u = F` for general such data.

Writing `u = w v`, the conjugation identity `P (w v) = w P_w v`
(`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq`) turns the weighted
problem into a Cauchy problem for the operator `P_w`, which has the same principal coefficients
and the lower-order coefficients `b_w = euclideanWeightedFirstOrderCoeff a b dℓ` and
`c_w = euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ`, again in `C_b^{α,α/2}`. The solution
operator of `P_w` for bounded uniformly continuous initial data
(`TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC`), multiplied by `w`, is the
weighted solution operator studied here:

* on data with `G / w ∈ C_b^{2,α}` it agrees with the classical weighted solution `u = w v`
  (`exp_mul_euclideanCauchySolutionBUC_weightedCoeff_eq`), and it is the only continuous linear map
  `C_b^{α,α/2} × BUC → C_b` that sends the weighted data of every classical weighted solution
  `u = w v` to `v` (`eq_euclideanCauchySolutionBUC_weightedCoeff`);
* the weighted trace is not a result of this file but a direct reading of existing unweighted
  lemmas: since `u / w = v` and `G / w = g`, the statements that `u` takes the datum `G` at `t = 0`
  and that `sup_x |u(x, t) - G(x)| / w(x) → 0` as `t → 0⁺` are
  `TauCeti.ParabolicC2HolderSpace.euclideanCauchySolutionBUC_apply_slabMk_zero` and
  `TauCeti.ParabolicC2HolderSpace.tendstoUniformly_euclideanCauchySolutionBUC` for the coefficients
  `b_w`, `c_w`;
* `sup |u / w| ≤ C max ‖F / w‖_{α,par} (sup |G / w|)`, with `C` depending only on the dimension,
  bounds on the coefficient norms and on the norms of `∂ᵢℓ`, `∂ᵢ∂ⱼℓ`, and a bound on the horizon
  (`exists_norm_euclideanCauchySolutionBUC_weightedCoeff_le`).

On the line, the weight `1 + exp x` qualifies:
`TauCeti.contDiff_log_one_add_exp_and_exists_fderiv_eq` supplies the derivatives `dℓ`, `d2ℓ` of
`ℓ = log (1 + exp x)`, and with them the statements above cover data growing like `exp x` as
`x → ∞`, measured in the norm `sup |u / (1 + exp x)|`.

The regularity of the solution for `t > 0`, where it is classical, is not proved here; it rests on
the corresponding statement for the unweighted problem.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `exp_mul_euclideanCauchySolutionBUC_weightedCoeff_eq`: agreement with the classical weighted
  solution.
* `eq_euclideanCauchySolutionBUC_weightedCoeff`: uniqueness of the weighted solution operator.
* `exists_norm_euclideanCauchySolutionBUC_weightedCoeff_le`: the uniform bound.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the substitution
  `u = w v` by a positive weight).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (solutions with continuous initial data as limits of solutions with smooth data).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Filter ParabolicSpaceTime Real BoundedContinuousFunction
open scoped NNReal Topology

variable {α : ℝ≥0} {T : ℝ≥0}

/-! ### The weighted solution operator -/

section Solution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
  {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

/-- **Agreement with the classical weighted solution.** Let `w = exp ℓ` be a spatial weight as in
`eq_euclideanInitialDataCLE_symm_iff_exp_mul`, let `u = w v` with `v ∈ C_b^{2+α,1+α/2}` be a
classical solution of `P u = w f`, `u(·, 0) = w g` with `f ∈ C_b^{α,α/2}` and `g ∈ C_b^{2,α}`, and
let `g'` be `g` regarded as a bounded uniformly continuous function. Then `u` is `w` times the
solution with data `(f, g')` of the conjugated problem for bounded uniformly continuous initial
data. -/
theorem exp_mul_euclideanCauchySolutionBUC_weightedCoeff_eq (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s))
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ)
    (g' : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
    (hg' : ∀ x, (g' : EuclideanSpace ℝ ι →ᵇ ℝ) x = g x)
    (hP : ∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t))
    (h0 : ∀ x, u x 0 = exp (ℓ x) * g x) (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T) :
    exp (ℓ x) * euclideanCauchySolutionBUC hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
      (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha (f, g') (slabMk x t) = u x t := by
  have hv := (eq_euclideanInitialDataCLE_symm_iff_exp_mul hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ v hu f
    g).2 ⟨hP, h0⟩
  rw [euclideanCauchySolutionBUC_apply_of_ckHolderSpace hα₀ hα₁ hT ha f g' g hg', ← hv,
    valueL_apply, hu]

/-- **Uniqueness of the weighted solution operator.** Let `w = exp ℓ` be a spatial weight as in
`eq_euclideanInitialDataCLE_symm_iff_exp_mul`. A continuous linear map `L` from
`C_b^{α,α/2} × BUC` to the bounded continuous functions on the slab that recovers `v` from the
data `(f, g)` of every classical solution `u = w v` of `P u = w f`, `u(·, 0) = w g`, with
`v ∈ C_b^{2+α,1+α/2}` and `g ∈ C_b^{2,α}`, is the solution operator of the conjugated problem for
bounded uniformly continuous initial data. -/
theorem eq_euclideanCauchySolutionBUC_weightedCoeff (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (L : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ×
      uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ →L[ℝ]
        (slab (E := EuclideanSpace ℝ ι) 0 T →ᵇ ℝ))
    (hL : ∀ (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ)
      (g' : uniformContinuousSubmodule ℝ (EuclideanSpace ℝ ι) ℝ)
      (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) (u : EuclideanSpace ℝ ι → ℝ → ℝ),
      (∀ x, (g' : EuclideanSpace ℝ ι →ᵇ ℝ) x = g x) →
      (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
      (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) →
      (∀ x, u x 0 = exp (ℓ x) * g x) → L (f, g') = valueL v) :
    L = euclideanCauchySolutionBUC hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
      (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha := by
  refine eq_euclideanCauchySolutionBUC hα₀ hα₁ hT ha L fun f g' g hg' ↦ ?_
  -- The classical solution of the conjugated problem, extended in time and multiplied by the
  -- weight, is a classical solution of the weighted problem.
  set v := (euclideanInitialDataCLE hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
    (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha).symm (f, g)
  have hu (y : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) T) :
      exp (ℓ y) * timeExtension hT.le v y s = exp (ℓ y) * v (slabMk y s) := by
    rw [timeExtension_of_mem]
  obtain ⟨hP, h0⟩ := (eq_euclideanInitialDataCLE_symm_iff_exp_mul hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ
    v (u := fun y s ↦ exp (ℓ y) * timeExtension hT.le v y s) hu f g).1 rfl
  exact hL f g g' v _ hg' hu hP h0

end Solution

/-! ### The uniform bound -/

section Bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The uniform bound in the weighted uniform norm.** For `0 < α < 1`, a bound `K` on the Hölder
norms of the coefficients, a bound `L` on the Hölder norms of the derivatives `∂ᵢℓ`, `∂ᵢ∂ⱼℓ` of the
logarithm of the weight and a bound `T₀` on the horizon, the solution operators of the conjugated
problems for bounded uniformly continuous initial data on `ℝⁿ × [0, T]`, `T ≤ T₀`, are bounded
uniformly. Thus `v = euclideanCauchySolutionBUC … (f, g)` satisfies
`sup |v| ≤ C max (‖f‖_{α,par}) (sup |g|)`, that is, `sup |u / w| ≤ C max (‖f‖_{α,par}) (sup |g|)`
for `u = w v`. The constant does not depend on the ellipticity constant, and the weight itself
enters only through `L`. -/
theorem exists_norm_euclideanCauchySolutionBUC_weightedCoeff_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖euclideanCauchySolutionBUC hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
          (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha‖ ≤ C := by
  set K' : ℝ := K + Fintype.card ι * (Fintype.card ι * (K * (L + L * L))) +
    Fintype.card ι * (K * L)
  refine ⟨exp (K' * T₀) * (1 + T₀), by positivity,
    fun T hT hTT₀ a b c dℓ d2ℓ ha hak hbk hck hdℓ hd2ℓ ↦ ?_⟩
  have hc := norm_euclideanWeightedZerothOrderCoeff_le_of_le hak hbk hck hdℓ hd2ℓ
  have hTT₀' : (T : ℝ) ≤ T₀ := hTT₀
  refine (norm_euclideanCauchySolutionBUC_le hα₀ hα₁ hT ha).trans ?_
  gcongr

end Bound

end TauCeti.ParabolicC2HolderSpace
