/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.Mixed
public import TauCeti.Analysis.Sobolev.Semiclassical.UniformlyLocal
public import TauCeti.Analysis.Sobolev.Trace.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.BumpFunction.Translates
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp

/-!
# Traces of semiclassical Sobolev norms on hyperplanes

Let `E` be a finite-dimensional real inner product space of dimension `n`, so that `ℝ × E`, with
the Euclidean norm of `WithLp 2 (ℝ × E)`, has dimension `n + 1`, and let `h > 0` be a length scale.
Restricting a function `u` on `ℝ × E` to the hyperplane `{a} × E` loses one derivative and no
power of `h` in the semiclassical Sobolev norms `‖·‖_{k,h}`
(`TauCeti.semiclassicalSobolevNorm`): for `u` compactly supported of class `Cᵏ⁺¹`,

`‖u(a, ·)‖_{k,h} ≤ 2 ‖u‖_{k+1,h}`

(`TauCeti.semiclassicalSobolevNorm_hyperplane_le`), where the left side is the norm on `E`, against
the volume normalized by `h⁻ⁿ`, and the right side the norm on `ℝ × E`, against the volume
normalized by `h⁻⁽ⁿ⁺¹⁾`. The constant is independent of `h`, `a` and `u`.

The unscaled estimate at `h = 1` is the sum over the orders `i ≤ k` of the flat trace inequalities
`‖Dⁱ(u(a, ·))‖₂ ≤ ‖Dⁱ u‖₂ + ‖Dⁱ⁺¹ u‖₂` (`TauCeti.lpNorm_iteratedFDeriv_hyperplane_le`); each order
of `u` through `k + 1` occurs at most twice. The semiclassical norm at scale `h` is the unscaled
norm of the dilation `u (h • ·)` (`TauCeti.semiclassicalSobolevNorm_eq_comp_smul`), and the
restriction of `u` to `{a} × E`, dilated by `h`, is the restriction of `u (h • ·)` to
`{a / h} × E`. The two normalizations `h⁻ⁿ` and `h⁻⁽ⁿ⁺¹⁾` of the volume are exactly what makes
the estimate uniform: a function concentrated at scale `h` near the hyperplane has comparable
norms on both sides.

The same holds for the uniformly local norms `‖·‖_{k,h,η}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm`), with the cutoff `η` restricted to `{0} × E`.
Localizing the trace about a centre `x ∈ E` is tracing the localization of `u` about `(a, x)`,
because `h⁻¹ • ((a, y) - (a, x)) = (0, h⁻¹ • (y - x))`
(`TauCeti.semiclassicalSobolevNorm_localization_hyperplane_le`). Hence, when the localizations of
`f` at order `k + 1` are bounded, so are those of its trace at order `k`
(`TauCeti.bddAbove_semiclassicalSobolevNorm_localization_hyperplane`), and

`‖f(a, ·)‖_{k,h,η(0, ·)} ≤ 2 ‖f‖_{k+1,h,η}`

(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_hyperplane_le`), with no compact support needed
for `f`.

The mixed norms `‖·‖_{j,h,V}` of a tube (`Submodule.mixedSemiclassicalSobolevNorm`), which weight
derivatives along a normal subspace `V` by `h` and leave the horizontal ones unscaled, have the same
trace estimate. Take a subspace `p` of `ℝ`, so that the normal subspace of the tube `ℝ × E` is the
product `p × V`, the subspace `(p.prod V).comap (WithLp.linearEquiv 2 ℝ (ℝ × E)).toLinearMap`
of `WithLp 2 (ℝ × E)`: the coordinate cut by the hyperplane `{a} × E` is normal
for `p = ⊤` and horizontal for `p = ⊥`. For `u` compactly supported of class `Cʲ⁺¹`,

`‖u(a, ·)‖_{j,h,V} ≤ (j + 1) 2ʲ⁺² ‖u‖_{j+1,h,p×V}`

(`Submodule.mixedSemiclassicalSobolevNorm_hyperplane_le`), uniformly in `h`. The normal dilation
along `p × V` dilates each factor (`Submodule.normalDilation_comap_prod`), so dilating the
restriction normally along `V` restricts the normally dilated `u` to the hyperplane
`{b} × E` with `a = normalDilation p h b`. The mixed norm at scale `h` is equivalent to the
unscaled Sobolev norm of the normally dilated field, and the trace estimate at scale one applies to
that field.

These are the trace estimates for the semiclassical, uniformly local and mixed norms in which
Taubes measures the fields near a pseudoholomorphic curve, at the scale `h = (2r)^(-1/2)`.

## Main results

* `TauCeti.semiclassicalSobolevNorm_hyperplane_le`: the trace estimate for the semiclassical norms,
  uniformly in `h`.
* `TauCeti.semiclassicalSobolevNorm_localization_hyperplane_le`: centre by centre, the localization
  of the trace about `x` is bounded by twice the `(k + 1)`-norm of the localization of `f` about
  `(a, x)`.
* `TauCeti.uniformlyLocalSemiclassicalSobolevNorm_hyperplane_le`: the trace estimate for the
  uniformly local norms.
* `Submodule.mixedSemiclassicalSobolevNorm_hyperplane_le`: the trace estimate for the mixed norms of
  a tube, uniformly in `h`, across a normal or a horizontal coordinate.

## References

* M. Zworski, *Semiclassical Analysis*, Graduate Studies in Mathematics 138, American
  Mathematical Society, 2012 (semiclassical Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5 (traces).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

namespace TauCeti

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {h : ℝ}

/-- The trace estimate at scale one: for `u` compactly supported of class `Cᵏ⁺¹` on `ℝ × E`,
`‖u(a, ·)‖_{k,1} ≤ 2 ‖u‖_{k+1,1}`. -/
private theorem semiclassicalSobolevNorm_one_hyperplane_le {u : WithLp 2 (ℝ × E) → F}
    (hu : ContDiff ℝ (k + 1) u) (hsupp : HasCompactSupport u) (a : ℝ) :
    semiclassicalSobolevNorm k 1 (fun y : E ↦ u (WithLp.toLp 2 (a, y))) ≤
      2 * semiclassicalSobolevNorm (k + 1) 1 u := by
  simp only [semiclassicalSobolevNorm_one]
  refine (Finset.sum_le_sum fun i hi ↦ lpNorm_iteratedFDeriv_hyperplane_le
    (hu.of_le (by norm_cast; simpa using Finset.mem_range.1 hi)) hsupp a).trans ?_
  -- Each order through `k + 1` occurs at most twice in the sum of the trace inequalities.
  rw [Finset.sum_add_distrib, two_mul]
  refine add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _))
    fun _ _ _ ↦ lpNorm_nonneg) ?_
  rw [Finset.sum_range_succ' (fun i ↦ lpNorm (iteratedFDeriv ℝ i u) 2 volume)]
  exact le_add_of_nonneg_right lpNorm_nonneg

/-- **The trace estimate for the semiclassical norms, uniformly in the scale.** For `h > 0` and
`u` compactly supported of class `Cᵏ⁺¹` on `ℝ × E`, the restriction of `u` to the hyperplane
`{a} × E` satisfies `‖u(a, ·)‖_{k,h} ≤ 2 ‖u‖_{k+1,h}`. -/
theorem semiclassicalSobolevNorm_hyperplane_le {u : WithLp 2 (ℝ × E) → F}
    (hu : ContDiff ℝ (k + 1) u) (hsupp : HasCompactSupport u) (hh : 0 < h) (a : ℝ) :
    semiclassicalSobolevNorm k h (fun y : E ↦ u (WithLp.toLp 2 (a, y))) ≤
      2 * semiclassicalSobolevNorm (k + 1) h u := by
  have hres : ContDiff ℝ k fun y : E ↦ u (WithLp.toLp 2 (a, y)) :=
    (hu.of_le (by norm_cast; omega)).comp
      (WithLp.contDiff_toLp.comp (contDiff_const.prodMk contDiff_id))
  -- Dilating the restriction to `{a} × E` by `h` restricts the dilation to `{a / h} × E`.
  have hdil : (fun y : E ↦ u (WithLp.toLp 2 (a, h • y))) =
      fun y ↦ u (h • WithLp.toLp 2 (a / h, y)) := by
    ext y
    rw [← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, mul_div_cancel₀ a hh.ne']
  rw [semiclassicalSobolevNorm_eq_comp_smul hres hh, semiclassicalSobolevNorm_eq_comp_smul hu hh,
    hdil]
  exact semiclassicalSobolevNorm_one_hyperplane_le (hu.comp (contDiff_const_smul h))
    (hsupp.comp_smul hh.ne') (a / h)

variable {η : WithLp 2 (ℝ × E) → ℝ} {f : WithLp 2 (ℝ × E) → F}

/-- **The trace of a localization.** For `h > 0` and `η`, `f` of class `Cᵏ⁺¹` on `ℝ × E` with `η`
compactly supported, the localization about `x ∈ E` of the restriction of `f` to `{a} × E`, by the
cutoff `η` restricted to `{0} × E`, is the restriction of the localization of `f` about `(a, x)`.
Its norm `‖·‖_{k,h}` is therefore at most twice the norm `‖·‖_{k+1,h}` of that localization. -/
theorem semiclassicalSobolevNorm_localization_hyperplane_le (hη : ContDiff ℝ (k + 1) η)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ (k + 1) f) (hh : 0 < h) (a : ℝ) (x : E) :
    semiclassicalSobolevNorm k h
        (fun y : E ↦ η (WithLp.toLp 2 (0, h⁻¹ • (y - x))) • f (WithLp.toLp 2 (a, y))) ≤
      2 * semiclassicalSobolevNorm (k + 1) h
        fun z ↦ η (h⁻¹ • (z - WithLp.toLp 2 (a, x))) • f z := by
  have hloc : (fun y : E ↦ η (WithLp.toLp 2 (0, h⁻¹ • (y - x))) • f (WithLp.toLp 2 (a, y))) =
      fun y ↦
        η (h⁻¹ • (WithLp.toLp 2 (a, y) - WithLp.toLp 2 (a, x))) • f (WithLp.toLp 2 (a, y)) := by
    ext y
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero]
  rw [hloc]
  exact semiclassicalSobolevNorm_hyperplane_le ((hη.comp_inv_smul_sub h _).smul hf)
    (hηc.comp_inv_smul_sub hh.ne' _).smul_right hh a

/-- When the localizations of `f` at order `k + 1` are bounded above, so are the localizations at
order `k` of its restriction to the hyperplane `{a} × E`, by the cutoff `η` restricted to
`{0} × E`. -/
theorem bddAbove_semiclassicalSobolevNorm_localization_hyperplane (hη : ContDiff ℝ (k + 1) η)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ (k + 1) f) (hh : 0 < h)
    (hb : BddAbove (range fun x ↦
      semiclassicalSobolevNorm (k + 1) h fun y ↦ η (h⁻¹ • (y - x)) • f y)) (a : ℝ) :
    BddAbove (range fun x : E ↦ semiclassicalSobolevNorm k h
      fun y ↦ η (WithLp.toLp 2 (0, h⁻¹ • (y - x))) • f (WithLp.toLp 2 (a, y))) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨2 * M, forall_mem_range.2 fun x ↦ ?_⟩
  exact (semiclassicalSobolevNorm_localization_hyperplane_le hη hηc hf hh a x).trans
    (mul_le_mul_of_nonneg_left (hM (mem_range_self _)) zero_le_two)

/-- **The trace estimate for the uniformly local norms, uniformly in the scale.** For `h > 0`, a
compactly supported cutoff `η` of class `Cᵏ⁺¹` on `ℝ × E` and `f` of class `Cᵏ⁺¹` whose
localizations at order `k + 1` are bounded above, the restriction of `f` to the hyperplane
`{a} × E` satisfies `‖f(a, ·)‖_{k,h,η(0, ·)} ≤ 2 ‖f‖_{k+1,h,η}`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_hyperplane_le (hη : ContDiff ℝ (k + 1) η)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ (k + 1) f) (hh : 0 < h)
    (hb : BddAbove (range fun x ↦
      semiclassicalSobolevNorm (k + 1) h fun y ↦ η (h⁻¹ • (y - x)) • f y)) (a : ℝ) :
    uniformlyLocalSemiclassicalSobolevNorm k h (fun y : E ↦ η (WithLp.toLp 2 (0, y)))
        (fun y ↦ f (WithLp.toLp 2 (a, y))) ≤
      2 * uniformlyLocalSemiclassicalSobolevNorm (k + 1) h η f :=
  uniformlyLocalSemiclassicalSobolevNorm_le fun x ↦
    (semiclassicalSobolevNorm_localization_hyperplane_le hη hηc hf hh a x).trans
      (mul_le_mul_of_nonneg_left
        (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hb _) zero_le_two)

end TauCeti

/-! ### Traces of the mixed norms -/

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : Submodule ℝ E) (p : Submodule ℝ ℝ) {j : ℕ} {h : ℝ} {u : WithLp 2 (ℝ × E) → F}

/-- **The trace estimate for the mixed norms, uniformly in the scale.** Let `V` be a subspace of
`E` and `p` a subspace of `ℝ`, so that `p × V` is the normal subspace of the tube `ℝ × E`: the
coordinate cut by the hyperplane is normal for `p = ⊤` and horizontal for `p = ⊥`. For `h > 0`
and `u` compactly supported of class `Cʲ⁺¹` on `ℝ × E`, the restriction of `u` to the hyperplane
`{a} × E` satisfies `‖u(a, ·)‖_{j,h,V} ≤ (j + 1) 2ʲ⁺² ‖u‖_{j+1,h,p×V}`. -/
theorem mixedSemiclassicalSobolevNorm_hyperplane_le (hu : ContDiff ℝ (j + 1) u)
    (hsupp : HasCompactSupport u) (hh : 0 < h) (a : ℝ) :
    V.mixedSemiclassicalSobolevNorm j h (fun y : E ↦ u (WithLp.toLp 2 (a, y))) ≤
      (j + 1) * 2 ^ (j + 2) *
        mixedSemiclassicalSobolevNorm
          ((p.prod V).comap (WithLp.linearEquiv 2 ℝ (ℝ × E)).toLinearMap) (j + 1) h u := by
  set W := (p.prod V).comap (WithLp.linearEquiv 2 ℝ (ℝ × E)).toLinearMap
  set U := u ∘ W.normalDilation h
  set b := p.normalDilation h⁻¹ a
  have hU : ContDiff ℝ (j + 1) U := hu.comp (W.normalDilation h).contDiff
  have hUc : HasCompactSupport U := by
    have he := (W.normalDilationEquiv hh.ne').toHomeomorph.isClosedEmbedding
    rw [ContinuousLinearEquiv.coe_toHomeomorph, coeFn_normalDilationEquiv] at he
    exact hsupp.comp_isClosedEmbedding he
  have hb : p.normalDilation h b = a := p.normalDilation_normalDilation_inv hh.ne' a
  -- Dilating the restriction normally along `V` restricts the dilation of `u` to `{b} × E`.
  have hdil : (fun y : E ↦ u (WithLp.toLp 2 (a, y))) ∘ V.normalDilation h =
      fun y ↦ U (WithLp.toLp 2 (b, y)) := by
    ext y
    simp only [Function.comp_apply, U, W, normalDilation_comap_prod, WithLp.toLp_fst,
      WithLp.toLp_snd, hb]
  have hres : ContDiff ℝ j fun y : E ↦ U (WithLp.toLp 2 (b, y)) :=
    (hU.of_le (by norm_cast; omega)).comp
      (WithLp.contDiff_toLp.comp (contDiff_const.prodMk contDiff_id))
  have hresc : HasCompactSupport fun y : E ↦ U (WithLp.toLp 2 (b, y)) :=
    hUc.comp_isClosedEmbedding (WithLp.isClosedEmbedding_toLp_prodMk_left 2 b)
  have hle :=
    (V.memLp_mixedIteratedFDeriv_and_mixedSemiclassicalSobolevNorm_le_of_comp_normalDilation hh
      (j := j) (by
        rw [hdil]
        exact fun n hn ↦ hres.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hn)
          hresc)).2
  rw [hdil] at hle
  have hmix := (W.memLp_iteratedFDeriv_comp_normalDilation_and_semiclassicalSobolevNorm_le hu
    (fun n hn _ _ ↦ W.memLp_mixedIteratedFDeriv
      (hu.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hn) hsupp) _) hh).2
  calc V.mixedSemiclassicalSobolevNorm j h (fun y : E ↦ u (WithLp.toLp 2 (a, y)))
      ≤ (j + 1) * TauCeti.semiclassicalSobolevNorm j 1 fun y : E ↦ U (WithLp.toLp 2 (b, y)) := hle
    _ ≤ (j + 1) * (2 * (2 ^ (j + 1) * W.mixedSemiclassicalSobolevNorm (j + 1) h u)) := by
        gcongr
        exact (TauCeti.semiclassicalSobolevNorm_hyperplane_le hU hUc one_pos b).trans
          (mul_le_mul_of_nonneg_left hmix zero_le_two)
    _ = (j + 1) * 2 ^ (j + 2) * W.mixedSemiclassicalSobolevNorm (j + 1) h u := by ring

end Submodule
