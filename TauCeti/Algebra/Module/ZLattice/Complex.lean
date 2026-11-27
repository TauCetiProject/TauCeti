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

For lattices `L`, `L'` and `a ∈ ℂ`, multiplication by `a` is an **isogeny of degree `N`** from `L`
to `L'` (`ZLattice.IsIsogeny`) if `a L ⊆ L'` and `|a|² covolume (L) = N covolume (L')`. Every
nonzero `a` with `a L ⊆ L'` is an isogeny, of degree the index `[L' : a L]`
(`ZLattice.isIsogeny_relIndex`, `ZLattice.IsIsogeny.degree_eq_relIndex`), and degrees multiply
under composition (`ZLattice.IsIsogeny.mul`).

## Main results

* `ZLattice.covolume_eq_abs_im`: the covolume of a lattice in `ℂ` with `ℤ`-basis `a, b` is
  `|Im (conj a * b)|`.
* `ZLattice.IsShortestPair.covolume_eq`: the same for the vectors of a shortest pair.
* `ZLattice.isShortestPair_complex_smul_iff`: shortest pairs are invariant under complex
  rescaling.
* `ZLattice.covolume_complex_smul`: complex rescaling by `c` multiplies the covolume by
  `‖c‖ ^ 2`.
* `ZLattice.IsIsogeny`: multiplication by `a` is an isogeny of degree `N`.
* `ZLattice.isIsogeny_relIndex`, `ZLattice.IsIsogeny.degree_eq_relIndex`: the degree of an
  isogeny by `a ≠ 0` is the index `[L' : a L]`.

## Provenance

`ZLattice.IsIsogeny` and `ZLattice.exists_isIsogeny` are adapted from `PeriodPair.IsIsogeny` and
`New.exists_isIsogeny_of_mul_mem_lattice` (file `src/Lib/CM/Sigma/Basic.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic,
PBC). There they are attached to period pairs, with the area `|Im (conj(ω₁) ω₂)|`; here they are
attached to lattices, with the area their covolume. The identification of the degree of an
isogeny with an index, and the composition of isogenies, are new here.

## References

* C. Adams, M. Hildebrand and J. Weeks, *Hyperbolic invariants of knots and links*, Trans. Amer.
  Math. Soc. 326 (1991), §2 (cusp lattices, their shortest translations and cusp volumes).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer,
  1994, II.1 (isogenies of complex tori).
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

/-! ### Isogenies -/

/-- Multiplication by `a ∈ ℂ` is an **isogeny of degree `N`** from the lattice `L` to the lattice
`L'` if `a L ⊆ L'` and `|a|² covolume (L) = N covolume (L')`. For `a ≠ 0` the degree is the index
`[L' : a L]` (`ZLattice.IsIsogeny.degree_eq_relIndex`). -/
structure IsIsogeny (L L' : Submodule ℤ ℂ) (a : ℂ) (N : ℕ) : Prop where
  /-- Multiplication by `a` maps `L` into `L'`. -/
  smul_le : a • L ≤ L'
  /-- The covolumes are related by `|a|² covolume (L) = N covolume (L')`. -/
  norm_sq_mul_covolume : ‖a‖ ^ 2 * covolume L = N * covolume L'

variable {L' L'' : Submodule ℤ ℂ} {a b : ℂ} {N N' : ℕ}

/-- Unbundled form of `ZLattice.IsIsogeny`. -/
theorem isIsogeny_iff :
    IsIsogeny L L' a N ↔ a • L ≤ L' ∧ ‖a‖ ^ 2 * covolume L = N * covolume L' :=
  ⟨fun h ↦ ⟨h.smul_le, h.norm_sq_mul_covolume⟩, fun h ↦ ⟨h.1, h.2⟩⟩

variable [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology L'] [IsZLattice ℝ L']

variable (L) in
/-- **A nonzero multiplier into a lattice is an isogeny of degree the index**: if `a ≠ 0` and
`a L ⊆ L'`, then `|a|² covolume (L) = [L' : a L] covolume (L')`. -/
theorem isIsogeny_relIndex (ha : a ≠ 0) (h : a • L ≤ L') :
    IsIsogeny L L' a ((a • L).toAddSubgroup.relIndex L'.toAddSubgroup) := by
  have : NeZero a := ⟨ha⟩
  refine ⟨h, ?_⟩
  rw [← covolume_complex_smul, ← covolume_div_covolume_eq_relIndex' _ _ h]
  exact (div_mul_cancel₀ _ (covolume_pos L').ne').symm

variable (L) in
/-- If multiplication by `a` maps `L` into `L'`, it is an isogeny of some degree. -/
theorem exists_isIsogeny (h : a • L ≤ L') : ∃ N : ℕ, IsIsogeny L L' a N := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, h, by simp⟩
  · exact ⟨_, isIsogeny_relIndex L ha h⟩

/-- The degree of an isogeny by `a ≠ 0` is the index `[L' : a L]`. -/
theorem IsIsogeny.degree_eq_relIndex (hN : IsIsogeny L L' a N) (ha : a ≠ 0) :
    N = (a • L).toAddSubgroup.relIndex L'.toAddSubgroup := by
  have h₂ := (isIsogeny_relIndex L ha hN.smul_le).norm_sq_mul_covolume
  rw [hN.norm_sq_mul_covolume] at h₂
  exact Nat.cast_injective (R := ℝ) (mul_right_cancel₀ (covolume_pos L').ne' h₂)

variable (L) in
omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Multiplication by `1` is an isogeny of degree `1` from a lattice to itself. -/
theorem isIsogeny_one : IsIsogeny L L 1 1 := ⟨by simp, by simp⟩

omit [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology L'] [IsZLattice ℝ L'] in
/-- **Composition of isogenies**: degrees multiply. -/
theorem IsIsogeny.mul (h₁ : IsIsogeny L L' a N) (h₂ : IsIsogeny L' L'' b N') :
    IsIsogeny L L'' (b * a) (N' * N) := by
  refine ⟨?_, ?_⟩
  · rw [mul_smul]
    refine le_trans ?_ h₂.smul_le
    rw [pointwise_smul_def, pointwise_smul_def]
    exact map_mono h₁.smul_le
  · rw [norm_mul, mul_pow, mul_assoc, h₁.norm_sq_mul_covolume, mul_left_comm,
      h₂.norm_sq_mul_covolume]
    push_cast
    ring

end ZLattice
