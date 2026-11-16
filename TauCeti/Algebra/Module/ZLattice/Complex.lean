/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Algebra.Module.ZLattice.Scaling
public import TauCeti.Algebra.Module.ZLattice.ShortestPair
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Module.ZLattice.Covolume

/-!
# Lattices in the complex plane

A lattice `L` in `ℂ` is a discrete `ℤ`-submodule spanning `ℂ` over `ℝ`, such as the period lattice
of an elliptic function or the lattice of parabolic translations of a cusp of a hyperbolic
`3`-manifold. For `ℂ` with its Lebesgue measure, the covolume of `L` is computed from any of its
`ℤ`-bases `a, b` as `|Im (conj a * b)|`, the area of the parallelogram they span
(`ZLattice.covolume_eq_abs_im`); in particular it is computed from any shortest pair of `L`
(`ZLattice.IsShortestPair.covolume_eq`), all of which are `ℤ`-bases since the norm of `ℂ` is
strictly convex.

Multiplying a lattice by a nonzero complex number `c`, a rotation followed by a homothety, changes
the normalization of a cusp but not the cusp: it carries the shortest pairs of `L` onto those of
`c • L` (`ZLattice.isShortestPair_complex_smul_iff`), so lengths scale by `‖c‖`, and it multiplies
the covolume by `‖c‖ ^ 2` (`ZLattice.covolume_complex_smul`). The rescaled lattice is again a
discrete lattice by the scaling instances of `TauCeti.Algebra.Module.ZLattice.Scaling`.

## Main results

* `ZLattice.covolume_eq_abs_im`: the covolume of a lattice in `ℂ` with `ℤ`-basis `a, b` is
  `|Im (conj a * b)|`.
* `ZLattice.IsShortestPair.covolume_eq`: the same for the vectors of a shortest pair.
* `ZLattice.isShortestPair_complex_smul_iff`: shortest pairs are invariant under complex
  rescaling.
* `ZLattice.covolume_complex_smul`: complex rescaling by `c` multiplies the covolume by
  `‖c‖ ^ 2`.

## References

* C. Adams, M. Hildebrand and J. Weeks, *Hyperbolic invariants of knots and links*, Trans. Amer.
  Math. Soc. 326 (1991), §2 (cusp lattices, their shortest translations and cusp volumes).
-/

public section

open Module Submodule ComplexConjugate
open scoped Pointwise

namespace ZLattice

/-- **The covolume of a lattice in `ℂ`.** For a `ℤ`-basis `a, b` of a lattice `L` in `ℂ`, the
covolume of `L` for the Lebesgue measure is `|Im (conj a * b)|`, the area of the parallelogram
spanned by `a` and `b`. -/
theorem covolume_eq_abs_im (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L) : covolume L = |(conj (b 0 : ℂ) * b 1).im| := by
  -- The Gram determinant of `a, b` is `‖a‖² ‖b‖² - (Re (conj a * b))² = (Im (conj a * b))²`.
  have hgram : (Matrix.gram ℝ fun i ↦ (b i : ℂ)).det = (conj (b 0 : ℂ) * b 1).im ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram, Matrix.of_apply, Complex.inner, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [← Real.sqrt_sq_eq_abs, ← hgram, ← covolume_sq_eq_det_gram L b,
    Real.sqrt_sq (covolume_pos L _).le]

variable {L : Submodule ℤ ℂ} {v w : ℂ}

/-- The covolume of a lattice in `ℂ` is `|Im (conj v * w)|` for every shortest pair `v, w`. -/
theorem IsShortestPair.covolume_eq [DiscreteTopology L] [IsZLattice ℝ L]
    (h : IsShortestPair L v w) : covolume L = |(conj v * w).im| := by
  simpa using covolume_eq_abs_im L (h.basis Complex.finrank_real_complex)

/-- **Shortest pairs are invariant under complex rescaling.** For `c ≠ 0`, the shortest pairs of
`c • L` are the pairs `c * v, c * w` for the shortest pairs `v, w` of `L`. -/
theorem isShortestPair_complex_smul_iff {c : ℂ} (hc : c ≠ 0) :
    IsShortestPair (c • L) (c * v) (c * w) ↔ IsShortestPair L v w := by
  -- `c • L` is the image of `L` under `z ↦ c * z` (`Submodule.pointwise_smul_def`).
  rw [pointwise_smul_def]
  exact isShortestPair_map_iff (f := LinearMap.mulLeft ℝ c) (norm_pos_iff.2 hc) fun x ↦ norm_mul c x

/-- **Complex rescaling multiplies the covolume by `‖c‖ ^ 2`.** -/
theorem covolume_complex_smul [DiscreteTopology L] [IsZLattice ℝ L] (c : ℂ) [NeZero c] :
    covolume (c • L) = ‖c‖ ^ 2 * covolume L := by
  obtain ⟨v, w, h⟩ := exists_isShortestPair L (by simp [Complex.finrank_real_complex])
  have hc : conj (c * v) * (c * w) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (conj v * w) := by
    rw [map_mul, Complex.ofReal_pow, ← Complex.conj_mul']
    ring
  rw [((isShortestPair_complex_smul_iff (NeZero.ne c)).2 h).covolume_eq, h.covolume_eq, hc,
    Complex.im_ofReal_mul, abs_mul, abs_of_nonneg (by positivity)]

end ZLattice
