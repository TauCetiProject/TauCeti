/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight.Backward

/-!
# The weighted Cauchy and terminal-value problems for parabolic operators with Hölder coefficients

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}`, with `0 < α < 1` and `a` uniformly elliptic,
and let `w = exp ℓ` be a positive time-independent weight whose logarithm `ℓ` is `C²` with
bounded `α`-Hölder partial derivatives `∂ᵢℓ` and `∂ᵢ∂ⱼℓ`. The logarithm itself may be unbounded,
so `w` may grow or decay exponentially at infinity, as `w(x) = 1 + exp x` does on the line. The
**weighted class** consists of the maps `u` with `u / w ∈ C_b^{2+α,1+α/2}`.

This file solves the Cauchy problem `P u = F`, `u(·, 0) = G` in the weighted class, for data with
`F / w ∈ C_b^{α,α/2}` and `G / w ∈ C_b^{2,α}`. Writing `u = w v`, the conjugation identity
`P (w v) = w P_w v` (`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq`)
turns it into the Cauchy problem `P_w v = F / w`, `v(·, 0) = G / w` for an operator of the same
type: `P_w` has the same principal coefficients `aⁱʲ` and lower-order coefficients `b_w`, `c_w`
again in `C_b^{α,α/2}`. The initial-data isomorphism of `P_w`
(`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`) is therefore the solution operator of
the weighted problem: `u = w v` solves the weighted problem exactly when `v` is the image of
`(F / w, G / w)` under its inverse. In particular the weighted problem has exactly one solution in
the weighted class.

The terminal-value problem `P_back u = F`, `u(·, T) = G` for the backward operator
`P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` is solved in the same way. The weight does not depend
on time, so `P_back (w v) = w P_back,w v` with the same conjugated coefficients
(`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanBackwardParabolicOperatorL_eq`). The
terminal-data map `v ↦ (P_back,w v, v(·, T))` of the conjugated operator is bijective
(`TauCeti.ParabolicC2HolderSpace.bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL`),
so the weighted terminal-value problem also has exactly one solution in the weighted class.

For the Cauchy problem the estimates transport in the same way. Its weighted solution satisfies
`‖u / w‖_{2+α,par} ≤ C max (‖F / w‖_{α,par}) (‖G / w‖_{2,α})`, with `C` depending only on the
dimension, `α`, the ellipticity constant, bounds on the Hölder norms of the coefficients and of
the derivatives of `ℓ`, and a bound on the horizon; and its weighted solution operator depends
Lipschitz continuously on the coefficients `a`, `b`, `c` in operator norm, for a fixed weight.
This file gives no such estimates for the terminal-value problem.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `eq_euclideanInitialDataCLE_symm_iff_exp_mul`: `u = exp ℓ * v` solves the weighted Cauchy
  problem if and only if `v` is given by the inverse initial-data isomorphism of the conjugated
  operator.
* `existsUnique_exp_mul`: the weighted Cauchy problem has exactly one solution in the weighted
  class.
* `existsUnique_one_add_exp_mul`: on the line, the Cauchy problem has exactly one solution in the
  class `u / (1 + exp x) ∈ C_b^{2+α,1+α/2}`.
* `existsUnique_exp_mul_backward`: the weighted terminal-value problem has exactly one solution in
  the weighted class.
* `existsUnique_one_add_exp_mul_backward`: on the line, the terminal-value problem has exactly one
  solution in the class `u / (1 + exp x) ∈ C_b^{2+α,1+α/2}`.
* `exists_norm_euclideanInitialDataCLE_weighted_symm_le`: the uniform bound on the weighted
  solution operators.
* `exists_norm_euclideanInitialDataCLE_weighted_symm_sub_le`: their Lipschitz dependence on the
  coefficients.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the substitution
  `u = w v` by a positive weight).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime Real
open scoped NNReal

variable {α : ℝ≥0} {T : ℝ≥0}

/-! ### The weighted solution operator -/

section Solution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}

/-- **The weighted Cauchy problem.** Let `w = exp ℓ` be a spatial weight whose logarithm `ℓ` is
`C²` with partial derivatives `∂ᵢℓ = dℓ i` and `∂ᵢ∂ⱼℓ = d2ℓ i j` bounded and `α`-Hölder; `ℓ` itself
may be unbounded. Let `v ∈ C_b^{2+α,1+α/2}` and `u = w v`, and let `f ∈ C_b^{α,α/2}` and
`g ∈ C_b^{2,α}`. Then `u` is a classical solution of the Cauchy problem `P u = w f`,
`u(·, 0) = w g` if and only if `v` is the solution of the conjugated problem `P_w v = f`,
`v(·, 0) = g`, that is, the image of `(f, g)` under the inverse of the initial-data isomorphism of
`P_w`. Hence the Cauchy problem whose data divided by `w` lie in `C_b^{α,α/2}` and `C_b^{2,α}` has
exactly one solution `u` with `u / w ∈ C_b^{2+α,1+α/2}`. -/
theorem eq_euclideanInitialDataCLE_symm_iff_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {ℓ : EuclideanSpace ℝ ι → ℝ} (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s))
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    v = (euclideanInitialDataCLE hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
        (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha).symm (f, g) ↔
      (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
        (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
          c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
        ∀ x, u x 0 = exp (ℓ x) * g x := by
  have hu₀ (x : EuclideanSpace ℝ ι) :
      u x 0 = exp (ℓ x) * v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ x := by
    rw [spatialTrace_apply]
    exact hu x ⟨0, left_mem_Icc.2 hT.le⟩
  rw [ContinuousLinearEquiv.eq_symm_apply, euclideanInitialDataCLE_apply, Prod.mk.injEq,
    euclideanParabolicOperatorL_weightedCoeff_eq_iff hα₁.le hℓ hdℓ hd2ℓ v hu]
  refine and_congr_right' ⟨fun h x ↦ by rw [hu₀, h], fun h ↦ CkHolderSpace.ext fun x ↦ ?_⟩
  exact mul_left_cancel₀ (exp_pos (ℓ x)).ne' ((hu₀ x).symm.trans (h x))

/-- **Unique solvability of the weighted Cauchy problem.** Let `w = exp ℓ` be a spatial weight as
in `eq_euclideanInitialDataCLE_symm_iff_exp_mul`. For uniformly elliptic `a` and data
`f ∈ C_b^{α,α/2}`, `g ∈ C_b^{2,α}`, there is exactly one `v ∈ C_b^{2+α,1+α/2}` such that `u = w v`
is a classical solution of `P u = w f`, `u(·, 0) = w g`. -/
theorem existsUnique_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {ℓ : EuclideanSpace ℝ ι → ℝ} (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
          ∀ x, u x 0 = exp (ℓ x) * g x := by
  have key (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
      (u : EuclideanSpace ℝ ι → ℝ → ℝ)
      (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) :=
    eq_euclideanInitialDataCLE_symm_iff_exp_mul hα₀ hα₁ hT b c ha hℓ hdℓ hd2ℓ v hu f g
  refine ⟨_, fun u hu ↦ (key _ u hu).1 rfl, fun v hv ↦ ?_⟩
  have hext (y : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) T) :
      exp (ℓ y) * timeExtension hT.le v y s = exp (ℓ y) * v (slabMk y s) := by
    rw [timeExtension_of_mem]
  exact (key v (fun y s ↦ exp (ℓ y) * timeExtension hT.le v y s) hext).2
    (hv (fun y s ↦ exp (ℓ y) * timeExtension hT.le v y s) hext)

/-- **Unique solvability of the weighted terminal-value problem.** Let `w = exp ℓ` be a spatial
weight as in `eq_euclideanInitialDataCLE_symm_iff_exp_mul`. For uniformly elliptic `a` and data
`f ∈ C_b^{α,α/2}`, `g ∈ C_b^{2,α}`, there is exactly one `v ∈ C_b^{2+α,1+α/2}` such that `u = w v`
is a classical solution of `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = w f`, `u(·, T) = w g`. -/
theorem existsUnique_exp_mul_backward (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {ℓ : EuclideanSpace ℝ ι → ℝ} (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t +
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = exp (ℓ x) * f (slabMk x t)) ∧
          ∀ x, u x T = exp (ℓ x) * g x := by
  obtain ⟨lam, hlam, ha⟩ := ha
  have key (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
      (u : EuclideanSpace ℝ ι → ℝ → ℝ)
      (hu : ∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) :=
    euclideanBackwardParabolicOperatorL_prod_spatialTraceL_weightedCoeff_eq_iff hα₁.le (a := a)
      (b := b) (c := c) hℓ hdℓ hd2ℓ v hu f g
  have hbij := bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT
    (euclideanWeightedFirstOrderCoeff a b dℓ) (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ)
    hlam ha
  obtain ⟨v, hv⟩ := hbij.2 (f, g)
  refine ⟨v, fun u hu ↦ (key v u hu).1 hv, fun v' hv' ↦ hbij.1 ?_⟩
  -- Any solution is the preimage of `(f, g)` under the injective terminal-data map.
  have hext (y : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) T) :
      exp (ℓ y) * timeExtension hT.le v' y s = exp (ℓ y) * v' (slabMk y s) := by
    rw [timeExtension_of_mem]
  exact ((key v' (fun y s ↦ exp (ℓ y) * timeExtension hT.le v' y s) hext).2
    (hv' (fun y s ↦ exp (ℓ y) * timeExtension hT.le v' y s) hext)).trans hv.symm

end Solution

/-! ### The weight `1 + exp x` on the line -/

section Line

variable {ι : Type*} [Unique ι]

/-- **The Cauchy problem on the line with the weight `1 + exp x`.** On the line
`ℝ¹ = EuclideanSpace ℝ ι`, for uniformly elliptic `a` and data `f ∈ C_b^{α,α/2}`,
`g ∈ C_b^{2,α}`, there is exactly one `v ∈ C_b^{2+α,1+α/2}` such that `u = (1 + exp x) v` is a
classical solution of `P u = (1 + exp x) f`, `u(·, 0) = (1 + exp x) g`. The solution and the data
may grow like `exp x` as `x → ∞`, and the weight has no Hölder bound itself. -/
theorem existsUnique_one_add_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = (1 + exp (y default)) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = (1 + exp (x default)) * f (slabMk x t)) ∧
          ∀ x, u x 0 = (1 + exp (x default)) * g x := by
  obtain ⟨hℓ, dℓ, d2ℓ, hdℓ, hd2ℓ⟩ :=
    contDiff_log_one_add_exp_and_exists_fderiv_eq (ι := ι) (α := α) hα₁.le
  have hw (x : EuclideanSpace ℝ ι) : exp (log (1 + exp (x default))) = 1 + exp (x default) :=
    exp_log (by positivity)
  simpa only [hw] using existsUnique_exp_mul hα₀ hα₁ hT b c ha (hℓ.of_le le_top) hdℓ hd2ℓ f g

/-- **The terminal-value problem on the line with the weight `1 + exp x`.** On the line
`ℝ¹ = EuclideanSpace ℝ ι`, for uniformly elliptic `a` and data `f ∈ C_b^{α,α/2}`,
`g ∈ C_b^{2,α}`, there is exactly one `v ∈ C_b^{2+α,1+α/2}` such that `u = (1 + exp x) v` is a
classical solution of `∂ₜu + a ∂ₓ²u + b ∂ₓu + c u = (1 + exp x) f`, `u(·, T) = (1 + exp x) g`. -/
theorem existsUnique_one_add_exp_mul_backward (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    ∃! v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ u : EuclideanSpace ℝ ι → ℝ → ℝ,
        (∀ y (s : Icc (0 : ℝ) T), u y s = (1 + exp (y default)) * v (slabMk y s)) →
        (∀ (x : EuclideanSpace ℝ ι) (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t +
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = (1 + exp (x default)) * f (slabMk x t)) ∧
          ∀ x, u x T = (1 + exp (x default)) * g x := by
  obtain ⟨hℓ, dℓ, d2ℓ, hdℓ, hd2ℓ⟩ :=
    contDiff_log_one_add_exp_and_exists_fderiv_eq (ι := ι) (α := α) hα₁.le
  have hw (x : EuclideanSpace ℝ ι) : exp (log (1 + exp (x default))) = 1 + exp (x default) :=
    exp_log (by positivity)
  simpa only [hw] using
    existsUnique_exp_mul_backward hα₀ hα₁ hT b c ha (hℓ.of_le le_top) hdℓ hd2ℓ f g

end Line

/-! ### Estimates -/

section Estimates

variable {ι : Type*} [Fintype ι]

variable (ι) in
/-- The bound `K (1 + 3 n L + n² (L + L²))` on the coefficients of the conjugated operator, where
`K` bounds the coefficients, `L` bounds the derivatives of the logarithm of the weight and `n` is
the dimension. -/
private def weightedCoeffBound (K L : ℝ≥0) : ℝ≥0 :=
  K * (1 + 3 * Fintype.card ι * L + Fintype.card ι ^ 2 * (L + L * L))

/-- The coefficients `aⁱʲ` and the weighted coefficients are bounded by `weightedCoeffBound ι K L`
when the coefficients are bounded by `K` and the derivatives of the logarithm of the weight by
`L`. -/
private theorem norm_weightedCoeff_le {t₀ t₁ : ℝ} {K L : ℝ≥0}
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
    {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
    (hak : ∀ i j, ‖a i j‖ ≤ K) (hbk : ∀ i, ‖b i‖ ≤ K) (hck : ‖c‖ ≤ K)
    (hdℓ : ∀ i, ‖dℓ i‖ ≤ L) (hd2ℓ : ∀ i j, ‖d2ℓ i j‖ ≤ L) :
    (∀ i j, ‖a i j‖ ≤ weightedCoeffBound ι K L) ∧
      (∀ i, ‖euclideanWeightedFirstOrderCoeff a b dℓ i‖ ≤ weightedCoeffBound ι K L) ∧
      ‖euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ‖ ≤ weightedCoeffBound ι K L := by
  simp only [weightedCoeffBound, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_ofNat]
  have hK : (0 : ℝ) ≤ K := K.property
  have hL : (0 : ℝ) ≤ L := L.property
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hb (i : ι) : ‖euclideanWeightedFirstOrderCoeff a b dℓ i‖ ≤
      K + Fintype.card ι * (2 * K * L) := by
    refine (norm_euclideanWeightedFirstOrderCoeff_le a b dℓ i).trans (add_le_add (hbk i) ?_)
    calc ∑ j, (‖a i j‖ + ‖a j i‖) * ‖dℓ j‖ ≤ ∑ _j : ι, 2 * (K : ℝ) * L :=
          Finset.sum_le_sum fun j _ ↦ by
            nlinarith [hak i j, hak j i, hdℓ j, norm_nonneg (dℓ j), norm_nonneg (a i j)]
      _ = _ := by simp
  have hc : ‖euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ‖ ≤
      K + Fintype.card ι ^ 2 * (K * (L + L * L)) + Fintype.card ι * (K * L) := by
    refine (norm_euclideanWeightedZerothOrderCoeff_le a b c dℓ d2ℓ).trans
      (add_le_add (add_le_add hck ?_) ?_)
    · calc ∑ i, ∑ j, ‖a i j‖ * (‖d2ℓ i j‖ + ‖dℓ i‖ * ‖dℓ j‖) ≤
            ∑ _i : ι, ∑ _j : ι, (K : ℝ) * (L + L * L) :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
              gcongr
              · exact hak i j
              · exact hd2ℓ i j
              · exact hdℓ i
              · exact hdℓ j
        _ = _ := by simp [sq]; ring
    · calc ∑ i, ‖b i‖ * ‖dℓ i‖ ≤ ∑ _i : ι, (K : ℝ) * L :=
            Finset.sum_le_sum fun i _ ↦ by gcongr; exacts [hbk i, hdℓ i]
        _ = _ := by simp
  refine ⟨fun i j ↦ (hak i j).trans (le_mul_of_one_le_right hK ?_), fun i ↦ (hb i).trans ?_,
    hc.trans ?_⟩
  · exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) (by positivity)
  all_goals nlinarith [mul_nonneg hK hL, mul_nonneg (mul_nonneg hK hL) hL,
    mul_nonneg hn (mul_nonneg hK hL),
    mul_nonneg (mul_nonneg hn hn) (mul_nonneg hK (add_nonneg hL (mul_nonneg hL hL)))]

/-- For a fixed weight whose logarithm has derivatives bounded by `L`, the differences of the
weighted coefficients of two coefficient triples are controlled by the differences of the
coefficients. -/
private theorem norm_weightedCoeff_sub_le {t₀ t₁ L : ℝ}
    {a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c c' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
    {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
    (hL : 0 ≤ L) (hdℓ : ∀ i, ‖dℓ i‖ ≤ L) (hd2ℓ : ∀ i j, ‖d2ℓ i j‖ ≤ L) :
    ∑ i, ‖euclideanWeightedFirstOrderCoeff a b dℓ i - euclideanWeightedFirstOrderCoeff a' b' dℓ i‖ ≤
        ∑ i, ‖b i - b' i‖ + 2 * L * ∑ i, ∑ j, ‖a i j - a' i j‖ ∧
      ‖euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ -
          euclideanWeightedZerothOrderCoeff a' b' c' dℓ d2ℓ‖ ≤
        ‖c - c'‖ + (L + L * L) * ∑ i, ∑ j, ‖a i j - a' i j‖ + L * ∑ i, ‖b i - b' i‖ := by
  -- The weighted coefficients are linear in `a`, `b`, `c`, so their differences are the weighted
  -- coefficients of the differences.
  refine ⟨?_, ?_⟩
  · calc _ ≤ ∑ i, (‖b i - b' i‖ + ∑ j, (‖a i j - a' i j‖ + ‖a j i - a' j i‖) * L) :=
          Finset.sum_le_sum fun i _ ↦ by
            rw [← euclideanWeightedFirstOrderCoeff_sub]
            exact (norm_euclideanWeightedFirstOrderCoeff_le _ _ _ i).trans
              (add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hdℓ j) (by positivity)))
      _ = _ := by
          have hswap : ∑ i, ∑ j, ‖a j i - a' j i‖ = ∑ i, ∑ j, ‖a i j - a' i j‖ := Finset.sum_comm
          simp only [Finset.sum_add_distrib, add_mul, ← Finset.sum_mul, hswap]
          ring
  · rw [← euclideanWeightedZerothOrderCoeff_sub]
    refine (norm_euclideanWeightedZerothOrderCoeff_le _ _ _ _ _).trans
      (add_le_add (add_le_add le_rfl ?_) ?_)
    · calc _ ≤ ∑ i, ∑ j, ‖a i j - a' i j‖ * (L + L * L) :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (add_le_add (hd2ℓ i j)
                (mul_le_mul (hdℓ i) (hdℓ j) (norm_nonneg _) hL)) (norm_nonneg _)
        _ = _ := by simp only [← Finset.sum_mul]; ring
    · calc _ ≤ ∑ i, ‖b i - b' i‖ * L :=
            Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hdℓ i) (norm_nonneg _)
        _ = _ := by simp only [← Finset.sum_mul]; ring

variable [DecidableEq ι]

/-- **The Schauder estimate for the weighted Cauchy problem.** For `0 < α < 1`, an ellipticity
constant `λ > 0`, a bound `K` on the Hölder norms of the coefficients, a bound `L` on the Hölder
norms of the derivatives `∂ᵢℓ`, `∂ᵢ∂ⱼℓ` of the logarithm of the weight and a bound `T₀` on the
horizon, the weighted solution operators on `ℝⁿ × [0, T]`, `T ≤ T₀`, are bounded uniformly: the
solution `u = exp ℓ * v` of `P u = exp ℓ * f`, `u(·, 0) = exp ℓ * g`
(`eq_euclideanInitialDataCLE_symm_iff_exp_mul`) satisfies
`‖v‖_{2+α,par} ≤ C max (‖f‖_{α,par}) (‖g‖_{2,α})`. The weight itself enters only through `L`. -/
theorem exists_norm_euclideanInitialDataCLE_weighted_symm_le (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖(euclideanInitialDataCLE hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
          (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ)
            ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanInitialDataCLE_symm_le (ι := ι) hα₀ hα₁ hlam (weightedCoeffBound ι K L) T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c dℓ d2ℓ ha hak hbk hck hdℓ hd2ℓ ↦ ?_⟩
  obtain ⟨ha', hb, hc⟩ := norm_weightedCoeff_le hak hbk hck hdℓ hd2ℓ
  exact hest T hT hTT₀ a _ _ ha ha' hb hc

/-- **Lipschitz dependence of the weighted solution operator on the coefficients.** Under the
bounds of `exists_norm_euclideanInitialDataCLE_weighted_symm_le`, for a fixed weight the weighted
solution operators of two Cauchy problems differ in operator norm by at most
`C (∑ᵢⱼ ‖aⁱʲ - a'ⁱʲ‖ + ∑ᵢ ‖bⁱ - b'ⁱ‖ + ‖c - c'‖)`. -/
theorem exists_norm_euclideanInitialDataCLE_weighted_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c c' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
        (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ),
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        (∀ i j, ‖a' i j‖ ≤ K) → (∀ i, ‖b' i‖ ≤ K) → ‖c'‖ ≤ K →
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
        ‖(euclideanInitialDataCLE hα₀ hα₁ hT a (euclideanWeightedFirstOrderCoeff a b dℓ)
            (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ)
              ⟨lam, hlam, ha⟩).symm.toContinuousLinearMap -
          (euclideanInitialDataCLE hα₀ hα₁ hT a' (euclideanWeightedFirstOrderCoeff a' b' dℓ)
            (euclideanWeightedZerothOrderCoeff a' b' c' dℓ d2ℓ)
              ⟨lam, hlam, ha'⟩).symm.toContinuousLinearMap‖ ≤
          C * (∑ i, ∑ j, ‖a i j - a' i j‖ + ∑ i, ‖b i - b' i‖ + ‖c - c'‖) := by
  obtain ⟨C, hC, hest⟩ := exists_norm_euclideanInitialDataCLE_symm_sub_le (ι := ι) hα₀ hα₁ hlam
    (weightedCoeffBound ι K L) T₀
  refine ⟨C * (1 + 3 * L + L * L), by positivity, fun T hT hTT₀ a a' b b' c c' dℓ d2ℓ ha ha'
    hak hbk hck hak' hbk' hck' hdℓ hd2ℓ ↦ ?_⟩
  obtain ⟨hak₁, hb, hc⟩ := norm_weightedCoeff_le hak hbk hck hdℓ hd2ℓ
  obtain ⟨hak₁', hb', hc'⟩ := norm_weightedCoeff_le hak' hbk' hck' hdℓ hd2ℓ
  obtain ⟨hbw, hcw⟩ := norm_weightedCoeff_sub_le (a := a) (a' := a') (b := b) (b' := b') (c := c)
    (c' := c') L.property hdℓ hd2ℓ
  refine (hest T hT hTT₀ a a' _ _ _ _ ha ha' hak₁ hb hc hak₁' hb' hc').trans ?_
  set A := ∑ i, ∑ j, ‖a i j - a' i j‖
  set B := ∑ i, ‖b i - b' i‖
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  have hL : (0 : ℝ) ≤ L := L.property
  have hc0 : 0 ≤ ‖c - c'‖ := norm_nonneg _
  have h : A + (B + 2 * L * A) + (‖c - c'‖ + (L + L * L) * A + L * B) ≤
      (1 + 3 * L + L * L) * (A + B + ‖c - c'‖) := by
    nlinarith [mul_nonneg hL hA, mul_nonneg hL hB, mul_nonneg (mul_nonneg hL hL) hA,
      mul_nonneg hL hc0, mul_nonneg (mul_nonneg hL hL) hB, mul_nonneg (mul_nonneg hL hL) hc0]
  exact (mul_le_mul_of_nonneg_left ((add_le_add (add_le_add le_rfl hbw) hcw).trans h) hC).trans_eq
    (by ring)

end Estimates

end TauCeti.ParabolicC2HolderSpace
