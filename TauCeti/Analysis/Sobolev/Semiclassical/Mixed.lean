/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Mixed
public import TauCeti.Analysis.Sobolev.Semiclassical.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Mixed semiclassical Sobolev norms in a tube

Let `E` be a finite-dimensional real inner product space and `V` a subspace of `E`. Near a
submanifold of a manifold, after choosing a tube, `V` plays the role of the normal directions and
its orthogonal complement `Vᗮ` that of the tangent, or horizontal, directions. Fields that
concentrate at the scale `h` around the submanifold vary on the scale `h` in the normal directions
but only on a scale of order one along it, as the rescaled Seiberg–Witten fields near a
pseudoholomorphic curve in Taubes's large-parameter analysis do, at the scale `h = (2r)^(-1/2)`.
The natural norms for them weight the normal derivatives by powers of `h`, leave the horizontal
derivatives unscaled, and normalize the volume by the normal volume `h^(dim V)` of the tube.

**Mixed derivatives.** The mixed derivative `∂^{a, n - a} f x` of order `(a, n - a)`
(`Submodule.mixedIteratedFDeriv`) is the `n`-th derivative `Dⁿ f x` with its first `a` arguments
projected to the horizontal subspace `Vᗮ` and the other `n - a` to the normal subspace `V`. It is
defined in `TauCeti.Analysis.Calculus.IteratedFDeriv.Mixed`, together with its pointwise calculus,
and the **normal dilation** `Submodule.normalDilation V t`, which fixes `Vᗮ` and multiplies `V` by
`t`, in `TauCeti.Analysis.InnerProductSpace.Projection.NormalDilation`. This file turns the
pointwise bounds into `Lᵖ` bounds (`Submodule.memLp_iteratedFDeriv_and_lpNorm_le`,
`Submodule.lpNorm_mixedIteratedFDeriv_fderiv_apply_le_of_mem`,
`Submodule.lpNorm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal`) and builds the `L²` norms
from them.

**The mixed norm.** The mixed semiclassical Sobolev norm of order `j` at scale `h` is

`‖f‖_{j,h,V} = h^(-dim V / 2) ∑_{n ≤ j} ∑_{a ≤ n} h^(n - a) ‖∂^{a, n - a} f‖₂`

(`Submodule.mixedSemiclassicalSobolevNorm`): each normal derivative costs a factor `h`, each
horizontal one none. At scales `h ≥ 0` it is a seminorm on fields of class `Cʲ` with
square-integrable mixed derivatives (`Submodule.mixedSemiclassicalSobolevNorm_neg`,
`Submodule.mixedSemiclassicalSobolevNorm_const_smul`,
`Submodule.mixedSemiclassicalSobolevNorm_add_le`,
`Submodule.mixedSemiclassicalSobolevNorm_sum_le`). The normal dilation by `h` reads a field in
the rescaled normal coordinate `w = y / h`, `y ∈ V`: for `h > 0`, the mixed norm at scale `h` is
the mixed norm at scale one of the dilated field `f ∘ normalDilation V h`, that is, the
unweighted mixed norm `∑_{a + b ≤ j} ‖∇^a ∂_w^b v‖₂` of the rescaled field `v` against `dvol dw`
(`Submodule.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation`).

At scale one the mixed norm is equivalent to the ordinary Sobolev norm
`∑_{n ≤ j} ‖Dⁿ f‖₂`, with constants depending only on `j`
(`Submodule.memLp_iteratedFDeriv_and_semiclassicalSobolevNorm_one_le`,
`Submodule.mixedSemiclassicalSobolevNorm_one_le_mul_semiclassicalSobolevNorm_one`). Together with
the dilation identity this gives the **Sobolev embedding uniformly in the scale**: if `2j > dim E`,
then `|f(x)| ≤ C ‖f‖_{j,h,V}` for every real-valued `f` of class `Cʲ` whose mixed derivatives
through total order `j` are square integrable, and every `h > 0`, with `C` independent of `h`
(`Submodule.exists_norm_le_mul_mixedSemiclassicalSobolevNorm`). This is the pointwise control
of real-valued functions in the tube norms; the volume normalization `h^(-dim V / 2)` is the one
that makes it uniform.

**Derivatives.** A horizontal derivative is bounded from order `j + 1` to order `j` with no loss
in `h`, `‖∂_e f‖_{j,h,V} ≤ ‖e‖ ‖f‖_{j+1,h,V}` for `e ∈ Vᗮ`
(`Submodule.mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem_orthogonal`), while a normal
derivative costs one factor of the scale, `h ‖∂_v f‖_{j,h,V} ≤ ‖v‖ ‖f‖_{j+1,h,V}` for `v ∈ V`
(`Submodule.mul_mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem`). These are the graph
derivatives `(h ∂_ν, ∇)` of the tube spaces; on the isotropic semiclassical norms of
`TauCeti.semiclassicalSobolevNorm` every derivative costs a factor `h`.

**Products and multipliers.** Since the product of two normally dilated fields is the dilation of
their product, the estimates for products at scale one carry over to every scale through the
dilation identity, with constants independent of `h`. If `2j > dim E`, the mixed norms of
real-valued functions satisfy the algebra estimate `‖f g‖_{j,h,V} ≤ C ‖f‖_{j,h,V} ‖g‖_{j,h,V}`
(`Submodule.exists_mixedSemiclassicalSobolevNorm_mul_le`). In every dimension and at every order,
a multiplier `g` whose mixed derivatives satisfy `h^(n - a) ‖∂^{a, n - a} g‖ ≤ B` for `a ≤ n ≤ j`
is bounded on the mixed norm of order `j`, `‖g • f‖_{j,h,V} ≤ (j + 1)² 8ʲ B ‖f‖_{j,h,V}`
(`Submodule.mixedSemiclassicalSobolevNorm_smul_le_of_le_left`); so is an operator-valued
multiplier `A`, acting by `y ↦ A y (f y)`
(`Submodule.mixedSemiclassicalSobolevNorm_clm_apply_le_of_le_left`). These bounds are the ones
satisfied by cutoffs, gauge transformations and changes of frame that vary on the scale `h` in the
normal directions and on a scale of order one along the tube, such as functions of the rescaled
normal coordinate `y / h`. Read through the dilation, such a multiplier has derivatives at scale one
bounded by `2ʲ B` (`Submodule.norm_iteratedFDeriv_comp_normalDilation_le`).

The norms assume that `E` is finite-dimensional and `V` has an orthogonal projection. A product
tube model `base × fibre` is the case `E = WithLp 2 (base × fibre)` with `V` the fibre; the inner
product space is needed for the Sobolev embedding, which the sup norm of a plain product does not
carry.

## Main definitions

* `Submodule.mixedSemiclassicalSobolevNorm V j h f`: the mixed norm `‖f‖_{j,h,V}`.

## Main results

* `Submodule.lpNorm_comp_normalDilation`: the change of variables under the normal dilation.
* `Submodule.mixedSemiclassicalSobolevNorm_add_le`: the triangle inequality for the mixed norm.
* `Submodule.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation`: the mixed norm at scale `h` is
  the unscaled mixed norm of the normally dilated field.
* `Submodule.exists_norm_le_mul_mixedSemiclassicalSobolevNorm`: the Sobolev embedding, uniformly in
  `h`.
* `Submodule.mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem_orthogonal`,
  `Submodule.mul_mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem`: horizontal derivatives are
  unscaled, normal derivatives cost a factor `h`.
* `Submodule.exists_mixedSemiclassicalSobolevNorm_mul_le`: the algebra estimate, uniformly in `h`.
* `Submodule.mixedSemiclassicalSobolevNorm_smul_le_of_le_left`,
  `Submodule.mixedSemiclassicalSobolevNorm_smul_le_of_le_right`,
  `Submodule.mixedSemiclassicalSobolevNorm_clm_apply_le_of_le_left`: multipliers with mixed `Cʲ`
  bounds are bounded on the mixed norms, uniformly in `h`.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Seiberg–Witten and Gromov invariants for symplectic 4-manifolds*, First
  International Press Lecture Series 2 (2000).
-/

public section

noncomputable section

namespace Submodule

open MeasureTheory Module Finset
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (V : Submodule ℝ E)
  [V.HasOrthogonalProjection]

/-! ### `Lᵖ` bounds on mixed derivatives -/

variable [MeasurableSpace E] {p : ℝ≥0∞} {μ : Measure E}

/-- If the `n`-th derivative of `f` is in `Lᵖ`, so is every mixed derivative of total order `n`. -/
theorem memLp_mixedIteratedFDeriv {n : ℕ} {f : E → F} (hD : MemLp (iteratedFDeriv ℝ n f) p μ)
    (a : ℕ) : MemLp (V.mixedIteratedFDeriv n a f) p μ :=
  hD.of_le (((ContinuousMultilinearMap.compContinuousLinearMapL fun i : Fin n ↦
      if (i : ℕ) < a then Vᗮ.starProjection else V.starProjection).continuous
        |>.comp_aestronglyMeasurable hD.aestronglyMeasurable).congr <| .of_forall fun x ↦ by
      simp only [ContinuousMultilinearMap.compContinuousLinearMapL_apply, mixedIteratedFDeriv_def])
    (.of_forall fun x ↦ V.norm_mixedIteratedFDeriv_le n a f x)

/-- The `Lᵖ` norms of the mixed derivatives of a normal derivative:
`‖∂^{a, n - a} (∂_v f)‖_p ≤ ‖v‖ ‖∂^{a, n + 1 - a} f‖_p` for `a ≤ n`, `f` of class `Cⁿ⁺¹` and
`v ∈ V`. -/
theorem lpNorm_mixedIteratedFDeriv_fderiv_apply_le_of_mem {n a : ℕ} (ha : a ≤ n) {f : E → F}
    (hf : ContDiff ℝ (n + 1) f) (hm : MemLp (V.mixedIteratedFDeriv (n + 1) a f) p μ) {v : E}
    (hv : v ∈ V) :
    lpNorm (V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v)) p μ ≤
      ‖v‖ * lpNorm (V.mixedIteratedFDeriv (n + 1) a f) p μ := by
  refine (lpNorm_mono_real (hm.norm.const_smul ‖v‖) fun x ↦
    V.norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem ha hf.contDiffAt hv).trans_eq ?_
  rw [lpNorm_const_smul_of_nonneg (norm_nonneg v), lpNorm_norm hm.aestronglyMeasurable]

/-- The `Lᵖ` norms of the mixed derivatives of a horizontal derivative:
`‖∂^{a, n - a} (∂_e f)‖_p ≤ ‖e‖ ‖∂^{a + 1, n - a} f‖_p` for `a ≤ n`, `f` of class `Cⁿ⁺¹` and
`e ∈ Vᗮ`. -/
theorem lpNorm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal {n a : ℕ} (ha : a ≤ n)
    {f : E → F} (hf : ContDiff ℝ (n + 1) f)
    (hm : MemLp (V.mixedIteratedFDeriv (n + 1) (a + 1) f) p μ) {e : E} (he : e ∈ Vᗮ) :
    lpNorm (V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e)) p μ ≤
      ‖e‖ * lpNorm (V.mixedIteratedFDeriv (n + 1) (a + 1) f) p μ := by
  refine (lpNorm_mono_real (hm.norm.const_smul ‖e‖) fun x ↦
    V.norm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal ha hf.contDiffAt he).trans_eq ?_
  rw [lpNorm_const_smul_of_nonneg (norm_nonneg e), lpNorm_norm hm.aestronglyMeasurable]

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- **The `Lᵖ` norm of the full derivative is bounded by those of the mixed derivatives.** For
`1 ≤ p` and `f` of class `Cⁿ` whose mixed derivatives of total order `n` are in `Lᵖ`, `Dⁿ f` is in
`Lᵖ` and `‖Dⁿ f‖_p ≤ ∑_{a ≤ n} (n choose a) ‖∂^{a, n - a} f‖_p`. -/
theorem memLp_iteratedFDeriv_and_lpNorm_le (hp : 1 ≤ p) {n : ℕ} {f : E → F}
    (hf : ContDiff ℝ n f) (hm : ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) p μ) :
    MemLp (iteratedFDeriv ℝ n f) p μ ∧ lpNorm (iteratedFDeriv ℝ n f) p μ ≤
      ∑ a ∈ range (n + 1), (n.choose a : ℝ) * lpNorm (V.mixedIteratedFDeriv n a f) p μ := by
  have hm' (a : ℕ) (ha : a ∈ range (n + 1)) : MemLp (V.mixedIteratedFDeriv n a f) p μ :=
    hm a (Nat.lt_succ_iff.1 (mem_range.1 ha))
  set Ψ : E → ℝ := ∑ a ∈ range (n + 1), (n.choose a : ℝ) • fun x ↦ ‖V.mixedIteratedFDeriv n a f x‖
  have hΨm : MemLp Ψ p μ := memLp_finsetSum' _ fun a ha ↦ (hm' a ha).norm.const_smul _
  have hle (x : E) : ‖iteratedFDeriv ℝ n f x‖ ≤ Ψ x := by
    simpa [Ψ, Finset.sum_apply] using
      V.norm_iteratedFDeriv_le_sum_choose_mul_norm_mixedIteratedFDeriv hf.contDiffAt
  refine ⟨hΨm.of_le (hf.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (.of_forall fun x ↦ (hle x).trans (le_abs_self _)), (lpNorm_mono_real hΨm hle).trans ?_⟩
  refine (lpNorm_sum_le (fun a ha ↦ (hm' a ha).norm.const_smul _) hp).trans_eq
    (sum_congr rfl fun a ha ↦ ?_)
  rw [lpNorm_const_smul_of_nonneg (Nat.cast_nonneg _), lpNorm_norm (hm' a ha).aestronglyMeasurable]

/-! ### The mixed norm -/

/-- The **mixed semiclassical Sobolev norm** of order `j` at scale `h` along the normal subspace
`V`,

`‖f‖_{j,h,V} = h^(-dim V / 2) ∑_{n ≤ j} ∑_{a ≤ n} h^(n - a) ‖∂^{a, n - a} f‖₂`:

the `L²` norms of the mixed derivatives through total order `j`, each normal derivative weighted
by `h` and each horizontal one unweighted, against the volume normalized by the normal volume
`h^(dim V)`. For `h > 0` it is the unweighted mixed norm of the normally
dilated field `f ∘ normalDilation V h`
(`Submodule.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation`).

The value is meaningful only when the mixed derivatives are in `L²`: `lpNorm` is `0` on a function
outside `L²`. -/
def mixedSemiclassicalSobolevNorm (j : ℕ) (h : ℝ) (f : E → F) : ℝ :=
  h ^ (-(finrank ℝ V : ℝ) / 2) * ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
    h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume

/-- The defining formula of the mixed norm, valid at every scale `h`. -/
theorem mixedSemiclassicalSobolevNorm_def (j : ℕ) (h : ℝ) (f : E → F) :
    V.mixedSemiclassicalSobolevNorm j h f =
      h ^ (-(finrank ℝ V : ℝ) / 2) * ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
        h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume :=
  (rfl)

/-- At scale one the mixed norm is the sum of the `L²` norms of the mixed derivatives through
total order `j`. -/
@[simp]
theorem mixedSemiclassicalSobolevNorm_one (j : ℕ) (f : E → F) :
    V.mixedSemiclassicalSobolevNorm j 1 f = ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
      lpNorm (V.mixedIteratedFDeriv n a f) 2 volume := by
  simp [mixedSemiclassicalSobolevNorm]

@[simp]
theorem mixedSemiclassicalSobolevNorm_zero (j : ℕ) (h : ℝ) :
    V.mixedSemiclassicalSobolevNorm j h (0 : E → F) = 0 := by
  simp [mixedSemiclassicalSobolevNorm]

theorem mixedSemiclassicalSobolevNorm_nonneg (j : ℕ) {h : ℝ} (hh : 0 ≤ h) (f : E → F) :
    0 ≤ V.mixedSemiclassicalSobolevNorm j h f :=
  mul_nonneg (Real.rpow_nonneg hh _) (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
    mul_nonneg (pow_nonneg hh _) lpNorm_nonneg)

/-- The mixed norm is invariant under negation. -/
@[simp]
theorem mixedSemiclassicalSobolevNorm_neg (j : ℕ) (h : ℝ) (f : E → F) :
    V.mixedSemiclassicalSobolevNorm j h (-f) = V.mixedSemiclassicalSobolevNorm j h f := by
  simp [mixedSemiclassicalSobolevNorm]

/-- **Homogeneity of the mixed norm.** `‖c f‖_{j,h,V} = |c| ‖f‖_{j,h,V}`. -/
theorem mixedSemiclassicalSobolevNorm_const_smul (j : ℕ) (h c : ℝ) (f : E → F) :
    V.mixedSemiclassicalSobolevNorm j h (c • f) =
      |c| * V.mixedSemiclassicalSobolevNorm j h f := by
  simp only [mixedSemiclassicalSobolevNorm, mixedIteratedFDeriv_const_smul, lpNorm_const_smul,
    coe_nnNorm, Real.norm_eq_abs, mul_sum]
  exact sum_congr rfl fun n _ ↦ sum_congr rfl fun a _ ↦ by ring

/-- **The triangle inequality for the mixed norm.** For `f`, `g` of class `Cʲ`, the mixed
derivatives of `f` through total order `j` square integrable, and `h ≥ 0`,
`‖f + g‖_{j,h,V} ≤ ‖f‖_{j,h,V} + ‖g‖_{j,h,V}`. -/
theorem mixedSemiclassicalSobolevNorm_add_le {j : ℕ} {f g : E → F} (hf : ContDiff ℝ j f)
    (hg : ContDiff ℝ j g) (hfm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2)
    {h : ℝ} (hh : 0 ≤ h) :
    V.mixedSemiclassicalSobolevNorm j h (f + g) ≤
      V.mixedSemiclassicalSobolevNorm j h f + V.mixedSemiclassicalSobolevNorm j h g := by
  rw [mixedSemiclassicalSobolevNorm, mixedSemiclassicalSobolevNorm, mixedSemiclassicalSobolevNorm,
    ← mul_add, ← sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun n hn ↦ ?_) (Real.rpow_nonneg hh _)
  have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
  rw [← sum_add_distrib]
  refine sum_le_sum fun a ha ↦ ?_
  rw [← mul_add, V.mixedIteratedFDeriv_add (hf.of_le (by exact_mod_cast hn))
    (hg.of_le (by exact_mod_cast hn))]
  exact mul_le_mul_of_nonneg_left
    (lpNorm_add_le (hfm n hn a (Nat.lt_succ_iff.1 (mem_range.1 ha))) one_le_two) (pow_nonneg hh _)

/-- **The triangle inequality for finite sums.** For functions `f i` of class `Cʲ` whose mixed
derivatives through total order `j` are square integrable, and `h ≥ 0`,
`‖∑ i ∈ s, f i‖_{j,h,V} ≤ ∑ i ∈ s, ‖f i‖_{j,h,V}`. -/
theorem mixedSemiclassicalSobolevNorm_sum_le {ι : Type*} (s : Finset ι) {j : ℕ} {f : ι → E → F}
    (hf : ∀ i ∈ s, ContDiff ℝ j (f i))
    (hfm : ∀ i ∈ s, ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a (f i)) 2) {h : ℝ}
    (hh : 0 ≤ h) :
    V.mixedSemiclassicalSobolevNorm j h (fun x ↦ ∑ i ∈ s, f i x) ≤
      ∑ i ∈ s, V.mixedSemiclassicalSobolevNorm j h (f i) := by
  simp only [mixedSemiclassicalSobolevNorm, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh _)
  rw [sum_comm]
  refine sum_le_sum fun n hn ↦ ?_
  have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
  rw [sum_comm]
  refine sum_le_sum fun a ha ↦ ?_
  rw [← mul_sum, V.mixedIteratedFDeriv_sum s fun i hi ↦ (hf i hi).of_le (by exact_mod_cast hn)]
  exact mul_le_mul_of_nonneg_left
    (lpNorm_sum_le (fun i hi ↦ hfm i hi n hn a (Nat.lt_succ_iff.1 (mem_range.1 ha))) one_le_two)
    (pow_nonneg hh _)

/-- **Translation invariance of the mixed norm.** `‖f (· - c)‖_{j,h,V} = ‖f‖_{j,h,V}`. -/
@[simp]
theorem mixedSemiclassicalSobolevNorm_comp_sub (j : ℕ) (h : ℝ) (f : E → F) (c : E) :
    V.mixedSemiclassicalSobolevNorm j h (fun x ↦ f (x - c)) =
      V.mixedSemiclassicalSobolevNorm j h f := by
  simp only [mixedSemiclassicalSobolevNorm, mixedIteratedFDeriv_comp_sub, lpNorm_comp_sub_right]

/-- **Change of variables under the normal dilation.** Composing with the normal dilation by
`h > 0` multiplies `Lᵖ` norms against an additive Haar measure by `h^(-dim V / p)`. The exponent
is `-dim V / p.toReal`, which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem lpNorm_comp_normalDilation {G : Type*} [NormedAddCommGroup G] [μ.IsAddHaarMeasure]
    (u : E → G) {h : ℝ} (hh : 0 < h) :
    lpNorm (u ∘ V.normalDilation h) p μ =
      h ^ (-(finrank ℝ V : ℝ) / p.toReal) * lpNorm u p μ := by
  have hc := Measure.eLpNorm_comp_continuousLinearEquiv μ u (V.normalDilationEquiv hh.ne') p
  have hdet : LinearMap.det ((V.normalDilationEquiv hh.ne' : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) =
      h ^ finrank ℝ V := by
    rw [← V.det_normalDilation h]
    congr 1
    ext x
    simp
  have hval : |(h ^ finrank ℝ V)⁻¹| ^ (1 / p).toReal = h ^ (-(finrank ℝ V : ℝ) / p.toReal) := by
    rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hh.le,
      ← Real.rpow_mul hh.le, one_div, ENNReal.toReal_inv, div_eq_mul_inv]
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  rw [hdet] at hc
  rw [← V.coeFn_normalDilationEquiv hh.ne', hc,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _), hval]


/-- **The mixed norm is the unscaled mixed norm of the normally dilated field.** For `h > 0`,
`‖f‖_{j,h,V} = ‖f ∘ normalDilation V h‖_{j,1,V}`: in the normal coordinate rescaled by `h`, each
normal derivative gains the factor `h` of its weight and the change of variables gains the volume
normalization `h^(-dim V / 2)`. No smoothness of `f` is needed. -/
theorem mixedSemiclassicalSobolevNorm_eq_comp_normalDilation (j : ℕ) (f : E → F) {h : ℝ}
    (hh : 0 < h) :
    V.mixedSemiclassicalSobolevNorm j h f =
      V.mixedSemiclassicalSobolevNorm j 1 (f ∘ V.normalDilation h) := by
  rw [mixedSemiclassicalSobolevNorm_one, mixedSemiclassicalSobolevNorm, mul_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [V.mixedIteratedFDeriv_comp_normalDilation_of_ne_zero n a f hh.ne',
    lpNorm_const_smul_of_nonneg (pow_nonneg hh.le _), V.lpNorm_comp_normalDilation _ hh,
    ENNReal.toReal_ofNat]
  ring

/-- **Comparison of scales.** For `0 < h ≤ 1`, multiplying the mixed norm at scale `h` by
`h^(dim V / 2)` gives at most the unscaled mixed norm and at least `hʲ` times it:
`hʲ ‖f‖_{j,1,V} ≤ h^(dim V / 2) ‖f‖_{j,h,V} ≤ ‖f‖_{j,1,V}`. -/
theorem pow_mul_mixedSemiclassicalSobolevNorm_one_le_and_le (j : ℕ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (f : E → F) :
    h ^ j * V.mixedSemiclassicalSobolevNorm j 1 f ≤
        h ^ ((finrank ℝ V : ℝ) / 2) * V.mixedSemiclassicalSobolevNorm j h f ∧
      h ^ ((finrank ℝ V : ℝ) / 2) * V.mixedSemiclassicalSobolevNorm j h f ≤
        V.mixedSemiclassicalSobolevNorm j 1 f := by
  have hnorm : h ^ ((finrank ℝ V : ℝ) / 2) * V.mixedSemiclassicalSobolevNorm j h f =
      ∑ n ∈ range (j + 1), ∑ a ∈ range (n + 1),
        h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a f) 2 volume := by
    rw [mixedSemiclassicalSobolevNorm, ← mul_assoc, ← Real.rpow_add hh, neg_div, add_neg_cancel,
      Real.rpow_zero, one_mul]
  rw [hnorm, mixedSemiclassicalSobolevNorm_one, mul_sum]
  refine ⟨sum_le_sum fun n hn ↦ ?_, sum_le_sum fun n _ ↦ sum_le_sum fun a _ ↦
    mul_le_of_le_one_left lpNorm_nonneg (pow_le_one₀ hh.le hh1)⟩
  rw [mul_sum]
  refine sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one hh.le hh1 ?_) lpNorm_nonneg
  have := Nat.lt_succ_iff.1 (mem_range.1 hn)
  omega

/-- **At scale one the mixed norm controls the Sobolev norm.** For `f` of class `Cʲ` whose mixed
derivatives through total order `j` are square integrable, the derivatives of `f` through order
`j` are square integrable and `∑_{n ≤ j} ‖Dⁿ f‖₂ ≤ 2ʲ ‖f‖_{j,1,V}`. -/
theorem memLp_iteratedFDeriv_and_semiclassicalSobolevNorm_one_le {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ j f) (hm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) :
    (∀ n ≤ j, MemLp (iteratedFDeriv ℝ n f) 2) ∧
      TauCeti.semiclassicalSobolevNorm j 1 f ≤
        2 ^ j * V.mixedSemiclassicalSobolevNorm j 1 f := by
  have key (n : ℕ) (hn : n ≤ j) := V.memLp_iteratedFDeriv_and_lpNorm_le one_le_two
    (hf.of_le (by exact_mod_cast hn)) (hm n hn)
  refine ⟨fun n hn ↦ (key n hn).1, ?_⟩
  rw [TauCeti.semiclassicalSobolevNorm_one, mixedSemiclassicalSobolevNorm_one, mul_sum]
  refine sum_le_sum fun n hn ↦ (key n (Nat.lt_succ_iff.1 (mem_range.1 hn))).2.trans ?_
  rw [mul_sum]
  refine sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right ?_ lpNorm_nonneg
  calc (n.choose a : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n a
    _ ≤ 2 ^ j := pow_le_pow_right₀ one_le_two (Nat.lt_succ_iff.1 (mem_range.1 hn))

/-- **At scale one the Sobolev norm controls the mixed norm.** For `f` whose derivatives through
order `j` are square integrable, `‖f‖_{j,1,V} ≤ (j + 1) ∑_{n ≤ j} ‖Dⁿ f‖₂`. -/
theorem mixedSemiclassicalSobolevNorm_one_le_mul_semiclassicalSobolevNorm_one {j : ℕ} {f : E → F}
    (hm : ∀ n ≤ j, MemLp (iteratedFDeriv ℝ n f) 2) :
    V.mixedSemiclassicalSobolevNorm j 1 f ≤
      (j + 1) * TauCeti.semiclassicalSobolevNorm j 1 f := by
  rw [TauCeti.semiclassicalSobolevNorm_one, mixedSemiclassicalSobolevNorm_one, mul_sum]
  refine sum_le_sum fun n hn ↦ ?_
  have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
  calc ∑ a ∈ range (n + 1), lpNorm (V.mixedIteratedFDeriv n a f) 2 volume
      ≤ ∑ _a ∈ range (n + 1), lpNorm (iteratedFDeriv ℝ n f) 2 volume :=
        sum_le_sum fun a _ ↦ (lpNorm_mono_real (hm n hn).norm
          fun x ↦ V.norm_mixedIteratedFDeriv_le n a f x).trans_eq
            (lpNorm_norm (hm n hn).aestronglyMeasurable 2)
    _ ≤ (j + 1) * lpNorm (iteratedFDeriv ℝ n f) 2 volume := by
        rw [sum_const, card_range, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ lpNorm_nonneg
        exact_mod_cast Nat.succ_le_succ hn

/-! ### Transfer to the unit scale

The mixed norm at scale `h` is the unscaled mixed norm of the field read in the normal coordinate
rescaled by `h`, which at scale one is equivalent to the Sobolev norm. The two private lemmas below
carry fields and bounds across this identification in both directions; every estimate of the
mixed norms uniform in the scale is then an estimate of the Sobolev norm at scale one. -/

/-- Read in the normal coordinate rescaled by `h > 0`, a field of class `Cʲ` with
square-integrable mixed derivatives through total order `j` has square-integrable derivatives
through order `j`, and its Sobolev norm at scale one is at most `2ʲ` times its mixed norm at
scale `h`. -/
private theorem contDiff_comp_normalDilation_and_semiclassicalSobolevNorm_one_le {j : ℕ}
    {f : E → F} (hf : ContDiff ℝ j f)
    (hm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ j (f ∘ V.normalDilation h) ∧
      (∀ n ≤ j, MemLp (iteratedFDeriv ℝ n (f ∘ V.normalDilation h)) 2) ∧
        TauCeti.semiclassicalSobolevNorm j 1 (f ∘ V.normalDilation h) ≤
          2 ^ j * V.mixedSemiclassicalSobolevNorm j h f := by
  have hg : ContDiff ℝ j (f ∘ V.normalDilation h) := hf.comp (V.normalDilation h).contDiff
  have hgm (n : ℕ) (hn : n ≤ j) (a : ℕ) (ha : a ≤ n) :
      MemLp (V.mixedIteratedFDeriv n a (f ∘ V.normalDilation h)) 2 := by
    rw [V.mixedIteratedFDeriv_comp_normalDilation_of_ne_zero n a f hh.ne',
      ← V.coeFn_normalDilationEquiv hh.ne']
    exact ((hm n hn a ha).comp_continuousLinearEquiv _).const_smul _
  obtain ⟨hDg, hle⟩ := V.memLp_iteratedFDeriv_and_semiclassicalSobolevNorm_one_le hg hgm
  refine ⟨hg, hDg, ?_⟩
  rwa [V.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation j f hh]

/-- Conversely, if a field read in the normal coordinate rescaled by `h > 0` has
square-integrable derivatives through order `j` and Sobolev norm at most `M` at scale one, then
its mixed derivatives through total order `j` are square integrable and its mixed norm at scale
`h` is at most `(j + 1) M`. -/
private theorem memLp_and_mixedSemiclassicalSobolevNorm_le_of_comp_normalDilation {j : ℕ}
    {φ : E → F} {h M : ℝ} (hh : 0 < h)
    (hm : ∀ n ≤ j, MemLp (iteratedFDeriv ℝ n (φ ∘ V.normalDilation h)) 2)
    (hle : TauCeti.semiclassicalSobolevNorm j 1 (φ ∘ V.normalDilation h) ≤ M) :
    (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a φ) 2) ∧
      V.mixedSemiclassicalSobolevNorm j h φ ≤ (j + 1) * M := by
  refine ⟨fun n hn a _ ↦ ?_, ?_⟩
  · -- `φ` is the dilated field read back through the dilation by `h⁻¹`.
    have hφ : φ = (φ ∘ V.normalDilation h) ∘ V.normalDilation h⁻¹ := by
      ext x
      rw [Function.comp_apply, Function.comp_apply, ← normalDilationEquiv_apply _ hh.ne',
        ← normalDilationEquiv_apply _ (inv_ne_zero hh.ne'), ← normalDilationEquiv_symm _ hh.ne',
        ContinuousLinearEquiv.apply_symm_apply]
    rw [hφ, V.mixedIteratedFDeriv_comp_normalDilation_of_ne_zero n a _ (inv_ne_zero hh.ne'),
      ← V.coeFn_normalDilationEquiv (inv_ne_zero hh.ne')]
    exact ((V.memLp_mixedIteratedFDeriv (hm n hn) a).comp_continuousLinearEquiv _).const_smul _
  · rw [V.mixedSemiclassicalSobolevNorm_eq_comp_normalDilation j φ hh]
    exact (V.mixedSemiclassicalSobolevNorm_one_le_mul_semiclassicalSobolevNorm_one hm).trans
      (mul_le_mul_of_nonneg_left hle (by positivity))

/-- **The Sobolev embedding for the mixed norms, uniformly in the scale.** If `2j > dim E`, there
is a constant `C ≥ 0` such that for every `h > 0` and every real-valued function `f` of class
`Cʲ` whose mixed derivatives through total order `j` are square integrable,
`|f(x)| ≤ C ‖f‖_{j,h,V}` at every point. -/
theorem exists_norm_le_mul_mixedSemiclassicalSobolevNorm {j : ℕ} (hj : finrank ℝ E < 2 * j) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f : E → ℝ, ContDiff ℝ j f →
      (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) →
        ∀ x, ‖f x‖ ≤ C * V.mixedSemiclassicalSobolevNorm j h f := by
  obtain ⟨C, hC, hCf⟩ := TauCeti.exists_norm_le_mul_semiclassicalSobolevNorm (E := E) hj
  refine ⟨C * 2 ^ j, by positivity, fun h hh f hf hm x ↦ ?_⟩
  -- Read `f` in the normal coordinate rescaled by `h`.
  obtain ⟨hg, hDg, hle⟩ :=
    contDiff_comp_normalDilation_and_semiclassicalSobolevNorm_one_le V hf hm hh
  have hx : (f ∘ V.normalDilation h) ((V.normalDilationEquiv hh.ne').symm x) = f x := by
    rw [Function.comp_apply, ← normalDilationEquiv_apply _ hh.ne',
      ContinuousLinearEquiv.apply_symm_apply]
  rw [← hx, mul_assoc]
  exact (hCf 1 one_pos _ hg hDg _).trans (mul_le_mul_of_nonneg_left hle hC)

/-- **A horizontal derivative is bounded on the mixed norms, without loss in the scale.** For `f`
of class `Cʲ⁺¹` whose mixed derivatives through total order `j + 1` are square integrable, a
horizontal vector `e ∈ Vᗮ` and `h ≥ 0`, `‖∂_e f‖_{j,h,V} ≤ ‖e‖ ‖f‖_{j+1,h,V}`: horizontal
derivatives are unscaled in the mixed norms. -/
theorem mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem_orthogonal {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ (j + 1) f)
    (hm : ∀ n ≤ j + 1, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) {h : ℝ} (hh : 0 ≤ h)
    {e : E} (he : e ∈ Vᗮ) :
    V.mixedSemiclassicalSobolevNorm j h (fun y ↦ fderiv ℝ f y e) ≤
      ‖e‖ * V.mixedSemiclassicalSobolevNorm (j + 1) h f := by
  -- Each term of order `(a, n - a)` on the left is bounded by `‖e‖` times the term of order
  -- `(a + 1, n - a)` on the right, which carries the same weight `h ^ (n - a)`.
  have hterm (n : ℕ) (hn : n ∈ range (j + 1)) (a : ℕ) (ha : a ∈ range (n + 1)) :
      h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y e)) 2 volume ≤
        ‖e‖ * (h ^ (n + 1 - (a + 1)) *
          lpNorm (V.mixedIteratedFDeriv (n + 1) (a + 1) f) 2 volume) := by
    have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have ha : a ≤ n := Nat.lt_succ_iff.1 (mem_range.1 ha)
    rw [Nat.add_sub_add_right, mul_left_comm]
    exact mul_le_mul_of_nonneg_left
      (V.lpNorm_mixedIteratedFDeriv_fderiv_apply_le_of_mem_orthogonal ha
        (hf.of_le (by exact_mod_cast Nat.succ_le_succ hn))
        (hm (n + 1) (by omega) (a + 1) (by omega)) he) (pow_nonneg hh _)
  rw [mixedSemiclassicalSobolevNorm, mixedSemiclassicalSobolevNorm, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh _)
  conv_rhs => rw [sum_range_succ', mul_add, mul_sum]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (mul_nonneg (norm_nonneg e) (sum_nonneg fun _ _ ↦ mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))
  conv_rhs => rw [sum_range_succ', mul_add, mul_sum]
  exact le_add_of_le_of_nonneg (sum_le_sum fun a ha ↦ hterm n hn a ha)
    (mul_nonneg (norm_nonneg e) (mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))

/-- **A normal derivative costs one factor of the scale.** For `f` of class `Cʲ⁺¹` whose mixed
derivatives through total order `j + 1` are square integrable, a normal vector `v ∈ V` and
`h ≥ 0`, `h ‖∂_v f‖_{j,h,V} ≤ ‖v‖ ‖f‖_{j+1,h,V}`: the operator `h ∂_v` is bounded from order
`j + 1` to order `j`, uniformly in `h`. -/
theorem mul_mixedSemiclassicalSobolevNorm_fderiv_apply_le_of_mem {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ (j + 1) f)
    (hm : ∀ n ≤ j + 1, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) {h : ℝ} (hh : 0 ≤ h)
    {v : E} (hv : v ∈ V) :
    h * V.mixedSemiclassicalSobolevNorm j h (fun y ↦ fderiv ℝ f y v) ≤
      ‖v‖ * V.mixedSemiclassicalSobolevNorm (j + 1) h f := by
  -- Each term of order `(a, n - a)` on the left, times `h`, is bounded by `‖v‖` times the term of
  -- order `(a, n + 1 - a)` on the right, which carries the weight `h ^ (n + 1 - a)`.
  have hterm (n : ℕ) (hn : n ∈ range (j + 1)) (a : ℕ) (ha : a ∈ range (n + 1)) :
      h * (h ^ (n - a) * lpNorm (V.mixedIteratedFDeriv n a (fun y ↦ fderiv ℝ f y v)) 2 volume) ≤
        ‖v‖ * (h ^ (n + 1 - a) * lpNorm (V.mixedIteratedFDeriv (n + 1) a f) 2 volume) := by
    have hn : n ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have ha : a ≤ n := Nat.lt_succ_iff.1 (mem_range.1 ha)
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_comm ha, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (V.lpNorm_mixedIteratedFDeriv_fderiv_apply_le_of_mem ha
      (hf.of_le (by exact_mod_cast Nat.succ_le_succ hn)) (hm (n + 1) (by omega) a (by omega)) hv)
      (pow_nonneg hh _)
  rw [mixedSemiclassicalSobolevNorm, mixedSemiclassicalSobolevNorm, mul_left_comm,
    mul_left_comm ‖v‖]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh _)
  rw [mul_sum]
  conv_rhs => rw [sum_range_succ', mul_add, mul_sum]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (mul_nonneg (norm_nonneg v) (sum_nonneg fun _ _ ↦ mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))
  rw [mul_sum]
  conv_rhs => rw [sum_range_succ _ (n + 1), mul_add, mul_sum]
  exact le_add_of_le_of_nonneg (sum_le_sum fun a ha ↦ hterm n hn a ha)
    (mul_nonneg (norm_nonneg v) (mul_nonneg (pow_nonneg hh _) lpNorm_nonneg))

/-! ### Products and multipliers -/

/-- **The algebra estimate for the mixed norms, uniformly in the scale.** If `2j > dim E`, there
is a constant `C ≥ 0` such that for every `h > 0` and all real-valued functions `f` and `g` of
class `Cʲ` whose mixed derivatives through total order `j` are square integrable, the mixed
derivatives of `f g` through total order `j` are square integrable and
`‖f g‖_{j,h,V} ≤ C ‖f‖_{j,h,V} ‖g‖_{j,h,V}`. -/
theorem exists_mixedSemiclassicalSobolevNorm_mul_le {j : ℕ} (hj : finrank ℝ E < 2 * j) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f g : E → ℝ, ContDiff ℝ j f → ContDiff ℝ j g →
      (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) →
      (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a g) 2) →
      (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a (f * g)) 2) ∧
        V.mixedSemiclassicalSobolevNorm j h (f * g) ≤
          C * V.mixedSemiclassicalSobolevNorm j h f * V.mixedSemiclassicalSobolevNorm j h g := by
  obtain ⟨C, hC, hCfg⟩ := TauCeti.exists_semiclassicalSobolevNorm_mul_le (E := E) hj
  refine ⟨(j + 1) * C * 4 ^ j, by positivity, fun h hh f g hf hg hfm hgm ↦ ?_⟩
  -- Read `f` and `g` in the normal coordinate rescaled by `h`, where the product of the dilated
  -- fields is the dilated product.
  obtain ⟨hf', hfm', hfle⟩ :=
    contDiff_comp_normalDilation_and_semiclassicalSobolevNorm_one_le V hf hfm hh
  obtain ⟨hg', hgm', hgle⟩ :=
    contDiff_comp_normalDilation_and_semiclassicalSobolevNorm_one_le V hg hgm hh
  obtain ⟨hm, hle⟩ := hCfg 1 one_pos _ _ hf' hg' hfm' hgm'
  rw [← Pi.mul_comp] at hm hle
  have hM : TauCeti.semiclassicalSobolevNorm j 1 ((f * g) ∘ V.normalDilation h) ≤
      C * (2 ^ j * V.mixedSemiclassicalSobolevNorm j h f) *
        (2 ^ j * V.mixedSemiclassicalSobolevNorm j h g) :=
    hle.trans (mul_le_mul (mul_le_mul_of_nonneg_left hfle hC) hgle
      (TauCeti.semiclassicalSobolevNorm_nonneg j zero_le_one _)
      (mul_nonneg hC
        (mul_nonneg (by positivity) (V.mixedSemiclassicalSobolevNorm_nonneg j hh.le f))))
  obtain ⟨hm', hle'⟩ :=
    memLp_and_mixedSemiclassicalSobolevNorm_le_of_comp_normalDilation V hh hm hM
  refine ⟨hm', hle'.trans_eq ?_⟩
  rw [show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
  ring

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A bound `B` on the scaled mixed derivatives of a field, as in the multiplier hypotheses below,
is nonnegative. -/
private theorem nonneg_of_pow_mul_norm_mixedIteratedFDeriv_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {j : ℕ} {g : E → G} {h B : ℝ}
    (hB : ∀ n ≤ j, ∀ a ≤ n, ∀ x, h ^ (n - a) * ‖V.mixedIteratedFDeriv n a g x‖ ≤ B) : 0 ≤ B :=
  le_trans (by simp) (hB 0 (Nat.zero_le j) 0 le_rfl 0)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A field whose mixed derivatives satisfy `h^(n - a) ‖∂^{a, n - a} g‖ ≤ B` for `a ≤ n ≤ j` has,
read in the normal coordinate rescaled by `h > 0`, all its derivatives through order `j` bounded
by `2ʲ B`, in the form of the multiplier bounds at scale one. -/
private theorem pow_mul_norm_iteratedFDeriv_comp_normalDilation_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {j : ℕ} {g : E → G} (hg : ContDiff ℝ j g) {h B : ℝ}
    (hh : 0 < h)
    (hB : ∀ n ≤ j, ∀ a ≤ n, ∀ x, h ^ (n - a) * ‖V.mixedIteratedFDeriv n a g x‖ ≤ B) :
    ∀ n ≤ j, ∀ x, (1 : ℝ) ^ n * ‖iteratedFDeriv ℝ n (g ∘ V.normalDilation h) x‖ ≤ 2 ^ j * B := by
  have hB0 : 0 ≤ B := nonneg_of_pow_mul_norm_mixedIteratedFDeriv_le V hB
  intro n hn x
  rw [one_pow, one_mul]
  exact (V.norm_iteratedFDeriv_comp_normalDilation_le (hg.of_le (by exact_mod_cast hn)) hh.le
    fun a ha ↦ hB n hn a ha _).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hn) hB0)

/-- The common step of the multiplier estimates: a bound at scale one of the kind given by
`TauCeti.semiclassicalSobolevNorm_smul_le_of_le_left`, for the fields `u` and `φ` read in the
normal coordinate rescaled by `h` and with the multiplier bound `2ʲ B` of
`pow_mul_norm_iteratedFDeriv_comp_normalDilation_le`, gives the corresponding bound for the mixed
norms at scale `h`. -/
private theorem memLp_and_mixedSemiclassicalSobolevNorm_le_of_unit_scale {G G' : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G'] {j : ℕ}
    {h B : ℝ} {u : E → G'} {φ : E → G}
    (hu : ContDiff ℝ j u) (hum : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a u) 2)
    (hh : 0 < h) (hB0 : 0 ≤ B)
    (hunit : ContDiff ℝ j (u ∘ V.normalDilation h) →
      (∀ n ≤ j, MemLp (iteratedFDeriv ℝ n (u ∘ V.normalDilation h)) 2) →
      (∀ n ≤ j, MemLp (iteratedFDeriv ℝ n (φ ∘ V.normalDilation h)) 2) ∧
        TauCeti.semiclassicalSobolevNorm j 1 (φ ∘ V.normalDilation h) ≤
          (j + 1) * 2 ^ j * (2 ^ j * B) *
            TauCeti.semiclassicalSobolevNorm j 1 (u ∘ V.normalDilation h)) :
    (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a φ) 2) ∧
      V.mixedSemiclassicalSobolevNorm j h φ ≤
        (j + 1) ^ 2 * 8 ^ j * B * V.mixedSemiclassicalSobolevNorm j h u := by
  obtain ⟨hu', hum', hule⟩ :=
    contDiff_comp_normalDilation_and_semiclassicalSobolevNorm_one_le V hu hum hh
  -- At the call sites below, `hunit` comes from a unit-scale lemma about the pointwise product
  -- `y ↦ (g ∘ δ) y • (u ∘ δ) y` of the dilated factors, which is `φ ∘ δ` by the definition of
  -- composition, for `φ = fun y ↦ g y • u y` and `δ = normalDilation V h`.
  obtain ⟨hm, hle⟩ := hunit hu' hum'
  obtain ⟨hm', hle'⟩ := memLp_and_mixedSemiclassicalSobolevNorm_le_of_comp_normalDilation V hh hm
    (hle.trans (mul_le_mul_of_nonneg_left hule (by positivity)))
  refine ⟨hm', hle'.trans_eq ?_⟩
  rw [show (8 : ℝ) ^ j = 2 ^ j * 2 ^ j * 2 ^ j by rw [← mul_pow, ← mul_pow]; norm_num]
  ring

section Multiplier

variable {j : ℕ} {h B : ℝ} {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F]
  [IsScalarTower ℝ 𝕜 F] {g : E → 𝕜} {f : E → F}

/-- **Multipliers with mixed `Cʲ` bounds, uniformly in the scale.** Let `g` be a scalar function
of class `Cʲ` whose mixed derivatives satisfy `h^(n - a) ‖∂^{a, n - a} g‖ ≤ B` everywhere for
`a ≤ n ≤ j`: normal derivatives cost a factor `h`, horizontal ones none, as for a cutoff or a gauge
transformation varying on the scale `h` in the normal directions and on a scale of order one along
the tube. For `h > 0` and `f` of class `Cʲ` whose mixed derivatives through total order `j` are
square integrable, the mixed derivatives of `g • f` through total order `j` are square integrable
and

`‖g • f‖_{j,h,V} ≤ (j + 1)² 8ʲ B ‖f‖_{j,h,V}`.

The constant depends only on `j` and `B`, not on `h`, `V`, the dimension or the target. -/
theorem mixedSemiclassicalSobolevNorm_smul_le_of_le_left (hg : ContDiff ℝ j g)
    (hf : ContDiff ℝ j f) (hfm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2)
    (hh : 0 < h) (hB : ∀ n ≤ j, ∀ a ≤ n, ∀ x, h ^ (n - a) * ‖V.mixedIteratedFDeriv n a g x‖ ≤ B) :
    (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a fun y ↦ g y • f y) 2) ∧
      V.mixedSemiclassicalSobolevNorm j h (fun y ↦ g y • f y) ≤
        (j + 1) ^ 2 * 8 ^ j * B * V.mixedSemiclassicalSobolevNorm j h f :=
  memLp_and_mixedSemiclassicalSobolevNorm_le_of_unit_scale V hf hfm hh
    (nonneg_of_pow_mul_norm_mixedIteratedFDeriv_le V hB) fun hf' hfm' ↦
      TauCeti.semiclassicalSobolevNorm_smul_le_of_le_left (hg.comp (V.normalDilation h).contDiff)
        hf' hfm' one_pos (pow_mul_norm_iteratedFDeriv_comp_normalDilation_le V hg hh hB)

/-- **Multiplication by a function with mixed `Cʲ` bounds, uniformly in the scale.** Let `f` be of
class `Cʲ` with `h^(n - a) ‖∂^{a, n - a} f‖ ≤ B` everywhere for `a ≤ n ≤ j`. For `h > 0` and a
scalar function `g` of class `Cʲ` whose mixed derivatives through total order `j` are square
integrable, the mixed derivatives of `g • f` through total order `j` are square integrable and
`‖g • f‖_{j,h,V} ≤ (j + 1)² 8ʲ B ‖g‖_{j,h,V}`. -/
theorem mixedSemiclassicalSobolevNorm_smul_le_of_le_right (hg : ContDiff ℝ j g)
    (hf : ContDiff ℝ j f) (hgm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a g) 2)
    (hh : 0 < h) (hB : ∀ n ≤ j, ∀ a ≤ n, ∀ x, h ^ (n - a) * ‖V.mixedIteratedFDeriv n a f x‖ ≤ B) :
    (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a fun y ↦ g y • f y) 2) ∧
      V.mixedSemiclassicalSobolevNorm j h (fun y ↦ g y • f y) ≤
        (j + 1) ^ 2 * 8 ^ j * B * V.mixedSemiclassicalSobolevNorm j h g :=
  memLp_and_mixedSemiclassicalSobolevNorm_le_of_unit_scale V hg hgm hh
    (nonneg_of_pow_mul_norm_mixedIteratedFDeriv_le V hB) fun hg' hgm' ↦
      TauCeti.semiclassicalSobolevNorm_smul_le_of_le_right hg'
        (hf.comp (V.normalDilation h).contDiff) hgm' one_pos
        (pow_mul_norm_iteratedFDeriv_comp_normalDilation_le V hf hh hB)

/-- **Operator-valued multipliers with mixed `Cʲ` bounds, uniformly in the scale.** Let
`A : E → F →L[ℝ] G` be of class `Cʲ` with `h^(n - a) ‖∂^{a, n - a} A‖ ≤ B` everywhere for
`a ≤ n ≤ j`, such as a change of frame of a vector bundle over the tube. For `h > 0` and `f` of
class `Cʲ` whose mixed derivatives through total order `j` are square integrable, the mixed
derivatives of `y ↦ A y (f y)` through total order `j` are square integrable and
`‖A f‖_{j,h,V} ≤ (j + 1)² 8ʲ B ‖f‖_{j,h,V}`. -/
theorem mixedSemiclassicalSobolevNorm_clm_apply_le_of_le_left {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {A : E → F →L[ℝ] G} (hA : ContDiff ℝ j A) (hf : ContDiff ℝ j f)
    (hfm : ∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a f) 2) (hh : 0 < h)
    (hB : ∀ n ≤ j, ∀ a ≤ n, ∀ x, h ^ (n - a) * ‖V.mixedIteratedFDeriv n a A x‖ ≤ B) :
    (∀ n ≤ j, ∀ a ≤ n, MemLp (V.mixedIteratedFDeriv n a fun y ↦ A y (f y)) 2) ∧
      V.mixedSemiclassicalSobolevNorm j h (fun y ↦ A y (f y)) ≤
        (j + 1) ^ 2 * 8 ^ j * B * V.mixedSemiclassicalSobolevNorm j h f :=
  memLp_and_mixedSemiclassicalSobolevNorm_le_of_unit_scale V hf hfm hh
    (nonneg_of_pow_mul_norm_mixedIteratedFDeriv_le V hB) fun hf' hfm' ↦
      TauCeti.semiclassicalSobolevNorm_clm_apply_le_of_le_left
        (hA.comp (V.normalDilation h).contDiff) hf' hfm' one_pos
        (pow_mul_norm_iteratedFDeriv_comp_normalDilation_le V hA hh hB)

end Multiplier

end Submodule
