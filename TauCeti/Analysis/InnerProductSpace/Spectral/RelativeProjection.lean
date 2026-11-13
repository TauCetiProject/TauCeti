/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Smooth
public import TauCeti.Analysis.InnerProductSpace.Spectral.Projection
public import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.LinearAlgebra.QuadraticForm.Signature
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Negative spectral projections of a form relative to a metric

Let `q` be a symmetric bilinear form on a finite-dimensional real inner product space `E` and let
`h` be a second inner product on `E`, given as a positive definite bilinear form. The operator
`h⁻¹ q`, defined by `h (h⁻¹ q u) v = q u v`, is self-adjoint for `h`, so `E` splits
`h`-orthogonally into its negative and nonnegative spectral subspaces. When `q` is nondegenerate
this is a splitting `E = E⁻ ⊕ E⁺` which is orthogonal both for `h` and for `q`, with `q` negative
definite on `E⁻` and positive definite on `E⁺`. The dimension of `E⁻` is then the negative index
of inertia of `q`, and that of `E⁺` the positive one.

The projection onto `E⁻` along `E⁺` is `q.negativeSpectralProjection h`. It is constructed with
the metric change transport `T = H ^ (-(1 / 2))` of `h`, where `H` is the Riesz operator of `h`
(`ContinuousLinearMap.metricChangeTransport`): `T` is an isometry from the inner product of `E`
to `h`, so it carries the orthogonal spectral splitting of the pulled-back form `q (T ·) (T ·)`
to the `h`-orthogonal spectral splitting of `q`. Conjugating the orthogonal spectral projection
of the pulled-back form by `T` gives the projection. The inner product of `E` only serves as a
reference: the projection is characterized by `q` and `h` alone
(`ContinuousLinearMap.eq_negativeSpectralProjection_iff`).

Every step of the construction depends smoothly, even real analytically, on the pair `(q, h)`:
the transport and its inverse through the functional calculus of positive operators, and the
spectral projection through `ContDiffOn.starProjection_pointSpectralSubspace_Iio_zero`. Hence
smooth families of nondegenerate forms and of metrics have smooth families of negative spectral
projections (`ContDiffOn.negativeSpectralProjection`), without choosing eigenbases. These are
the local projections onto the negative subbundle of a nondegenerate family of forms on a
vector bundle with a fibre metric, such as the normal Hessian of a Morse–Bott function.

## Main declarations

* `ContinuousLinearMap.negativeSpectralProjection q h`: the projection onto the negative spectral
  subspace of `q` relative to `h`, along the positive one.
* `ContinuousLinearMap.isIdempotentElem_negativeSpectralProjection`: it is a projection.
* `ContinuousLinearMap.metric_apply_negativeSpectralProjection_apply_sub_eq_zero` and
  `ContinuousLinearMap.apply_negativeSpectralProjection_apply_sub_eq_zero`: its range and kernel
  are orthogonal for `h` and for `q`.
* `ContinuousLinearMap.apply_negativeSpectralProjection_apply_self_lt_zero` and
  `ContinuousLinearMap.apply_sub_negativeSpectralProjection_apply_self_pos`: `q` is negative
  definite on its range and positive definite on its kernel.
* `ContinuousLinearMap.apply_sub_negativeSpectralProjection_apply_self_nonneg`: even for
  degenerate `q`, it is positive semidefinite on the kernel.
* `ContinuousLinearMap.eq_negativeSpectralProjection_iff`: these properties characterize it.
* `ContinuousLinearMap.range_negativeSpectralProjection` and
  `ContinuousLinearMap.ker_negativeSpectralProjection`: its range and kernel are the negative and
  positive relative spectral subspaces of `q` with respect to `h`
  (`LinearMap.BilinForm.relativeSpectralSubspace`); the range needs no nondegeneracy.
* `ContinuousLinearMap.negativeSpectralProjection_eq_projection`: for nondegenerate `q`, it is the
  projection onto the negative relative spectral subspace along the positive one.
* `ContinuousLinearMap.finrank_range_negativeSpectralProjection` and
  `ContinuousLinearMap.finrank_ker_negativeSpectralProjection`: the rank is the negative index of
  inertia of `q` and the nullity is the positive one.
* `ContinuousLinearMap.contDiffOn_negativeSpectralProjection` and
  `ContDiffOn.negativeSpectralProjection`: the projection depends smoothly on `(q, h)`.
* `TauCeti.exists_contDiffOn_range_eq_relativeSpectralSubspace`: on a finite-dimensional normed
  space without a chosen inner product, there is still a real-analytic family of projections onto
  the negative relative spectral subspaces along the positive ones.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2.
-/

public section

noncomputable section

open InnerProductSpace Set
open scoped InnerProductSpace ContDiff

/-! ### The negative spectral projection -/

/-- The Riesz operator of a real bilinear form, written as Mathlib's `InnerProductSpace.Dual`
writes it. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **negative spectral projection** of a bilinear form `q` relative to a second inner
product `h`: when `q` is symmetric and nondegenerate and `h` is positive definite, the projection
onto the negative spectral subspace of `h⁻¹ q` along its positive spectral subspace. These two
subspaces are orthogonal for both `h` and `q`, with `q` negative definite on the first and positive
definite on the second.

It is the orthogonal spectral projection of the pulled-back form `q (T ·) (T ·)`, conjugated by
the metric change transport `T` of `h`. -/
def negativeSpectralProjection (q h : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  h.metricChangeTransport *
    (Module.End.pointSpectralSubspace
      (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯.toLinearMap
        (Iio 0)).starProjection *
    CFC.sqrt h♯

theorem negativeSpectralProjection_def (q h : E →L[ℝ] E →L[ℝ] ℝ) :
    q.negativeSpectralProjection h =
      h.metricChangeTransport *
        (Module.End.pointSpectralSubspace
          (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯.toLinearMap
            (Iio 0)).starProjection *
        CFC.sqrt h♯ :=
  (rfl)

variable {q h : E →L[ℝ] E →L[ℝ] ℝ}

/-- The Riesz operator of the pullback of `q` along the transport of `h` represents
`q (T u) (T v)`. -/
private theorem inner_continuousLinearMapOfBilin_bilinearComp_apply (u v : E) :
    ⟪(q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ u, v⟫_ℝ =
      q (h.metricChangeTransport u) (h.metricChangeTransport v) := by
  rw [continuousLinearMapOfBilin_apply, bilinearComp_apply]

/-- The pullback of a symmetric form along the transport of `h` has a symmetric Riesz
operator. -/
private theorem isSymmetric_continuousLinearMapOfBilin_bilinearComp (hq : ∀ u v, q u v = q v u) :
    ((q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ :
      E →ₗ[ℝ] E).IsSymmetric :=
  isSymmetric_continuousLinearMapOfBilin fun _ _ ↦ hq _ _

/-- The pullback of a nondegenerate form along the transport of a positive definite `h` has an
injective Riesz operator. -/
private theorem ker_continuousLinearMapOfBilin_bilinearComp (hh : IsStrictlyPositive h♯)
    (hq : Function.Injective q) :
    LinearMap.ker
      ((q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯ : E →ₗ[ℝ] E) = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun u hu ↦ ?_
  -- `q (T u)` vanishes on every `T v`, and `T` is surjective.
  have hTu : q (h.metricChangeTransport u) = 0 := by
    ext w
    have := congr(⟪$hu, CFC.sqrt h♯ w⟫_ℝ)
    rwa [coe_coe, inner_continuousLinearMapOfBilin_bilinearComp_apply, inner_zero_left,
      metricChangeTransport_apply_sqrt_apply hh] at this
  have h0 : h.metricChangeTransport u = 0 := hq (by rw [hTu, map_zero])
  simpa [sqrt_apply_metricChangeTransport_apply hh] using
    congr(CFC.sqrt h♯ $h0)

/-- The negative spectral projection relative to a positive definite metric is a projection. -/
theorem isIdempotentElem_negativeSpectralProjection (hh : IsStrictlyPositive h♯) :
    IsIdempotentElem (q.negativeSpectralProjection h) := by
  ext u
  simp only [negativeSpectralProjection, mul_apply_eq_comp, sqrt_apply_metricChangeTransport_apply
    hh, Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- The complement `v - P v` of the negative spectral projection `P` is the transport of the
component of `CFC.sqrt h♯ v` orthogonal to the negative spectral subspace. -/
private theorem sub_negativeSpectralProjection_apply (hh : IsStrictlyPositive h♯) (v : E) :
    v - q.negativeSpectralProjection h v =
      h.metricChangeTransport (CFC.sqrt h♯ v -
        (Module.End.pointSpectralSubspace
          (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯.toLinearMap
            (Iio 0)).starProjection (CFC.sqrt h♯ v)) := by
  rw [map_sub, metricChangeTransport_apply_sqrt_apply hh]
  simp only [negativeSpectralProjection, mul_apply_eq_comp]

/-- **The negative spectral projection is `h`-orthogonal.** Its range and its kernel are
orthogonal for the metric `h`. -/
theorem metric_apply_negativeSpectralProjection_apply_sub_eq_zero (hh : IsStrictlyPositive h♯)
    (u v : E) :
    h (q.negativeSpectralProjection h u) (v - q.negativeSpectralProjection h v) = 0 := by
  rw [sub_negativeSpectralProjection_apply hh]
  simp only [negativeSpectralProjection, mul_apply_eq_comp]
  rw [apply_metricChangeTransport_metricChangeTransport hh]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _)
    (Submodule.sub_starProjection_mem_orthogonal _)

/-- **The negative spectral projection is `q`-orthogonal.** Its range and its kernel are
orthogonal for the form `q`. -/
theorem apply_negativeSpectralProjection_apply_sub_eq_zero (hh : IsStrictlyPositive h♯)
    (u v : E) :
    q (q.negativeSpectralProjection h u) (v - q.negativeSpectralProjection h v) = 0 := by
  set A := (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  rw [sub_negativeSpectralProjection_apply hh]
  simp only [negativeSpectralProjection, mul_apply_eq_comp]
  rw [← inner_continuousLinearMapOfBilin_bilinearComp_apply]
  -- The negative spectral subspace is invariant, and orthogonal to the complement.
  have hmem : A (W.starProjection (CFC.sqrt h♯ u)) ∈ W :=
    Module.End.map_pointSpectralSubspace_le ⟨_, W.starProjection_apply_mem _, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hmem (Submodule.sub_starProjection_mem_orthogonal _)

/-- **`q` is negative definite on the range of its negative spectral projection.** -/
theorem apply_negativeSpectralProjection_apply_self_lt_zero
    (hq : ∀ u v, q u v = q v u) {u : E} (hu : q.negativeSpectralProjection h u ≠ 0) :
    q (q.negativeSpectralProjection h u) (q.negativeSpectralProjection h u) < 0 := by
  set A := (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  simp only [negativeSpectralProjection, mul_apply_eq_comp] at hu ⊢
  rw [← inner_continuousLinearMapOfBilin_bilinearComp_apply]
  have hne : W.starProjection (CFC.sqrt h♯ u) ≠ 0 := fun h0 ↦ hu (by rw [h0, map_zero])
  have hA := isSymmetric_continuousLinearMapOfBilin_bilinearComp (h := h) hq
  simpa using hA.re_inner_apply_self_lt_zero_of_mem_pointSpectralSubspace subset_rfl
    (W.starProjection_apply_mem _) hne

/-- **`q` is positive semidefinite on the kernel of its negative spectral projection**, which
consists of the vectors `u - P u`. No nondegeneracy of `q` is needed. -/
theorem apply_sub_negativeSpectralProjection_apply_self_nonneg (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (u : E) :
    0 ≤ q (u - q.negativeSpectralProjection h u) (u - q.negativeSpectralProjection h u) := by
  set A := (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  have hA := isSymmetric_continuousLinearMapOfBilin_bilinearComp (h := h) hq
  rw [sub_negativeSpectralProjection_apply hh,
    ← inner_continuousLinearMapOfBilin_bilinearComp_apply]
  -- The orthogonal complement of the negative spectral subspace is the nonnegative one.
  have hmem : CFC.sqrt h♯ u - W.starProjection (CFC.sqrt h♯ u) ∈
      Module.End.pointSpectralSubspace A.toLinearMap (Ici 0) := by
    rw [← compl_Iio, ← hA.orthogonal_pointSpectralSubspace]
    exact W.sub_starProjection_mem_orthogonal _
  simpa using hA.re_inner_apply_self_nonneg_of_mem_pointSpectralSubspace subset_rfl hmem

/-- **A nondegenerate `q` is positive definite on the kernel of its negative spectral
projection**, which consists of the vectors `u - P u`. -/
theorem apply_sub_negativeSpectralProjection_apply_self_pos (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {u : E}
    (hu : u - q.negativeSpectralProjection h u ≠ 0) :
    0 < q (u - q.negativeSpectralProjection h u) (u - q.negativeSpectralProjection h u) := by
  set A := (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  have hA := isSymmetric_continuousLinearMapOfBilin_bilinearComp (h := h) hq
  rw [sub_negativeSpectralProjection_apply hh] at hu ⊢
  rw [← inner_continuousLinearMapOfBilin_bilinearComp_apply]
  set w := CFC.sqrt h♯ u - W.starProjection (CFC.sqrt h♯ u)
  have hne : w ≠ 0 := fun h0 ↦ hu (by rw [h0, map_zero])
  -- For an injective operator, the orthogonal complement of the negative spectral subspace is the
  -- positive one.
  have hmem : w ∈ Module.End.pointSpectralSubspace A.toLinearMap (Ioi 0) := by
    rw [← hA.orthogonal_pointSpectralSubspace_Iio_zero
      (ker_continuousLinearMapOfBilin_bilinearComp hh hq')]
    exact W.sub_starProjection_mem_orthogonal _
  simpa using hA.re_inner_apply_self_pos_of_mem_pointSpectralSubspace subset_rfl hmem hne

/-- **Characterization of the negative spectral projection.** For a symmetric nondegenerate form
`q` and a positive definite `h`, an operator `p` is the negative spectral projection of `q`
relative to `h` exactly when it is a projection whose range and kernel are orthogonal both for `h`
and for `q`, with `q` negative definite on the range and positive definite on the kernel. In
particular the negative spectral projection does not depend on the inner product of `E`. -/
theorem eq_negativeSpectralProjection_iff (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) {p : E →L[ℝ] E} :
    p = q.negativeSpectralProjection h ↔
      IsIdempotentElem p ∧ (∀ u v, h (p u) (v - p v) = 0) ∧ (∀ u v, q (p u) (v - p v) = 0) ∧
        (∀ u, p u ≠ 0 → q (p u) (p u) < 0) ∧ ∀ u, u - p u ≠ 0 → 0 < q (u - p u) (u - p u) := by
  constructor
  · rintro rfl
    exact ⟨isIdempotentElem_negativeSpectralProjection hh,
      metric_apply_negativeSpectralProjection_apply_sub_eq_zero hh,
      apply_negativeSpectralProjection_apply_sub_eq_zero hh,
      fun u hu ↦ apply_negativeSpectralProjection_apply_self_lt_zero hq hu,
      fun u hu ↦ apply_sub_negativeSpectralProjection_apply_self_pos hh hq hq' hu⟩
  rintro ⟨hp, hph, hpq, hneg, hpos⟩
  set T := h.metricChangeTransport
  set R := CFC.sqrt h♯
  set A := (q.bilinearComp T T)♯
  set W := Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)
  have hA := isSymmetric_continuousLinearMapOfBilin_bilinearComp (h := h) hq
  have hTR (x : E) : T (R x) = x := metricChangeTransport_apply_sqrt_apply hh x
  have hRT (x : E) : R (T x) = x := sqrt_apply_metricChangeTransport_apply hh x
  have hT0 {x : E} (hx : T x = 0) : x = 0 := by rw [← hRT x, hx, map_zero]
  -- Read `p` through the transport `T`, an isometry from the inner product of `E` to `h`; the
  -- result `p'` is an orthogonal projection whose range and kernel are invariant under `A`.
  set p' : E →L[ℝ] E := R * p * T
  have hTp' (x : E) : T (p' x) = p (T x) := by simp [p', hTR]
  have hp'idem (x : E) : p' (p' x) = p' x := by
    simp only [p', mul_apply_eq_comp, hTR]
    rw [← mul_apply_eq_comp p p, hp.eq]
  have hinner (x y : E) : ⟪p' x, y - p' y⟫_ℝ = 0 := by
    rw [← apply_metricChangeTransport_metricChangeTransport hh, map_sub, hTp', hTp']
    exact hph _ _
  have hinnerA (x y : E) : ⟪A (p' x), y - p' y⟫_ℝ = 0 := by
    rw [inner_continuousLinearMapOfBilin_bilinearComp_apply, map_sub, hTp', hTp']
    exact hpq _ _
  have hcomm : Commute (A : E →ₗ[ℝ] E) (p' : E →ₗ[ℝ] E) :=
    (hA.commute_of_isIdempotentElem (LinearMap.ext hp'idem) hinner hinnerA).symm
  -- Through `T`, `q` is negative definite on the range of `p'` and positive definite on its
  -- kernel, so `p'` is the orthogonal projection onto `W`.
  have hp'W := hA.eq_starProjection_pointSpectralSubspace_Iio_zero
    (ker_continuousLinearMapOfBilin_bilinearComp hh hq') (LinearMap.ext hp'idem) hcomm
    (fun x hx ↦ by
      simp only [coe_coe] at hx ⊢
      have := hneg (T x) (by rw [← hTp']; exact fun h0 ↦ hx (hT0 h0))
      rwa [← hTp', ← inner_continuousLinearMapOfBilin_bilinearComp_apply] at this)
    (fun x hx hx0 ↦ by
      simp only [coe_coe] at hx
      have hTx : T x - p (T x) = T x := by rw [← hTp', hx, map_zero, sub_zero]
      have := hpos (T x) (by rw [hTx]; exact fun h0 ↦ hx0 (hT0 h0))
      rwa [hTx, ← inner_continuousLinearMapOfBilin_bilinearComp_apply] at this)
  -- Hence `p` is the conjugate by `T` of the orthogonal projection onto `W`.
  ext u
  have hsplit : p' (R u) = W.starProjection (R u) := LinearMap.congr_fun hp'W (R u)
  simp only [negativeSpectralProjection, mul_apply_eq_comp]
  rw [← hsplit, hTp', hTR]

/-- The range and the kernel of the negative spectral projection are complementary, with `q`
negative definite on the range and positive semidefinite on the kernel. -/
private theorem isCompl_range_ker_negativeSpectralProjection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) :
    IsCompl ((q.negativeSpectralProjection h).range)
        ((q.negativeSpectralProjection h).ker) ∧
      (∀ x ∈ (q.negativeSpectralProjection h).range, x ≠ 0 → q x x < 0) ∧
      ∀ x ∈ (q.negativeSpectralProjection h).ker, 0 ≤ q x x := by
  have hP := isIdempotentElem_negativeSpectralProjection (q := q) hh
  have hP' : IsIdempotentElem (q.negativeSpectralProjection h : E →ₗ[ℝ] E) :=
    congr(($hP : E →ₗ[ℝ] E))
  refine ⟨LinearMap.IsIdempotentElem.isCompl hP', fun x hx hx0 ↦ ?_, fun x hx ↦ ?_⟩
  · have hxP : q.negativeSpectralProjection h x = x :=
      (LinearMap.IsIdempotentElem.mem_range_iff hP').mp hx
    rw [← hxP] at hx0 ⊢
    exact apply_negativeSpectralProjection_apply_self_lt_zero hq hx0
  · have hx' : q.negativeSpectralProjection h x = 0 := LinearMap.mem_ker.mp hx
    have hxP : x - q.negativeSpectralProjection h x = x := by
      rw [hx', sub_zero]
    rw [← hxP]
    exact apply_sub_negativeSpectralProjection_apply_self_nonneg hh hq x

/-- **The rank of the negative spectral projection is the negative index of inertia of `q`.** -/
theorem finrank_range_negativeSpectralProjection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) :
    Module.finrank ℝ ((q.negativeSpectralProjection h).range) =
      sigNeg q.toBilinForm.toQuadraticMap := by
  obtain ⟨hcompl, hneg, hpos⟩ := isCompl_range_ker_negativeSpectralProjection hh hq
  refine (QuadraticForm.sigNeg_eq_finrank_of_isCompl_of_negDef _ hcompl
    (fun x hx0 ↦ ?_) fun x hx ↦ by simpa using hpos x hx).symm
  have := hneg x x.2 (by simpa using hx0)
  simpa [QuadraticMap.restrict_apply] using this

/-- **The nullity of the negative spectral projection is the positive index of inertia of a
nondegenerate `q`.** -/
theorem finrank_ker_negativeSpectralProjection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    Module.finrank ℝ ((q.negativeSpectralProjection h).ker) =
      sigPos q.toBilinForm.toQuadraticMap := by
  obtain ⟨hcompl, hneg, -⟩ := isCompl_range_ker_negativeSpectralProjection hh hq
  refine (QuadraticForm.sigPos_eq_finrank_of_isCompl_of_posDef _ hcompl.symm
    (fun x hx0 ↦ ?_) fun x hx ↦ ?_).symm
  · -- A vector `x` of the kernel is its own complement `x - P x`.
    have hxP : (x : E) - q.negativeSpectralProjection h x = x := by
      rw [show q.negativeSpectralProjection h x = 0 from LinearMap.mem_ker.mp x.2, sub_zero]
    have := apply_sub_negativeSpectralProjection_apply_self_pos hh hq hq' (u := x)
      (by rw [hxP]; simpa using hx0)
    rw [hxP] at this
    simpa [QuadraticMap.restrict_apply] using this
  · by_cases hx0 : x = 0
    · simp [hx0]
    · simpa using (hneg x hx hx0).le

/-- **The range of the negative spectral projection is the negative relative spectral subspace**:
the span of the vectors `v` with `q v = μ h v` for some `μ < 0`. -/
theorem range_negativeSpectralProjection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) :
    (q.negativeSpectralProjection h).range =
      h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) := by
  obtain ⟨hhs, hhpos⟩ := isStrictlyPositive_continuousLinearMapOfBilin_iff.mp hh
  set W := Module.End.pointSpectralSubspace
    (q.bilinearComp h.metricChangeTransport h.metricChangeTransport)♯.toLinearMap (Iio 0)
  refine (Submodule.eq_of_le_of_finrank_eq
    (LinearMap.BilinForm.relativeSpectralSubspace_le_iff.mpr fun μ hμ v hv ↦
      LinearMap.mem_range.mpr ⟨v, ?_⟩) ?_).symm
  · -- For a relative eigenvector `v`, the vector `CFC.sqrt h♯ v` is an eigenvector of the
    -- operator representing the pulled-back form, with the same eigenvalue.
    have hx : CFC.sqrt h♯ v ∈ W := by
      refine Module.End.eigenspace_le_pointSpectralSubspace hμ
        (Module.End.mem_eigenspace_iff.mpr (ext_inner_right ℝ fun y ↦ ?_))
      rw [coe_coe, inner_continuousLinearMapOfBilin_bilinearComp_apply,
        metricChangeTransport_apply_sqrt_apply hh, RCLike.ofReal_real_eq_id, id_eq,
        real_inner_smul_left, ← apply_metricChangeTransport_metricChangeTransport hh,
        metricChangeTransport_apply_sqrt_apply hh]
      simpa using (LinearMap.BilinForm.mem_relativeEigenspace_iff.mp hv) _
    simp only [negativeSpectralProjection, coe_coe, mul_apply_eq_comp]
    rw [Submodule.starProjection_eq_self_iff.mpr hx, metricChangeTransport_apply_sqrt_apply hh]
  · rw [finrank_range_negativeSpectralProjection hh hq,
      LinearMap.BilinForm.finrank_relativeSpectralSubspace_Iio (isSymm_toBilinForm_iff.mpr hhs)
        (fun v hv ↦ hhpos v hv) (isSymm_toBilinForm_iff.mpr hq)]

/-- **The negative spectral projection of a nondegenerate form is the projection onto its negative
relative spectral subspace along the positive one.** These subspaces are complementary by
`LinearMap.BilinForm.isCompl_relativeSpectralSubspace_Iio_Ioi`. -/
theorem negativeSpectralProjection_eq_projection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q)
    (hc : IsCompl (h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0))
      (h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0))) :
    q.negativeSpectralProjection h =
      LinearMap.toContinuousLinearMap
        ((h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0)).projection
          (h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0)) hc) := by
  obtain ⟨hhs, hhpos⟩ := isStrictlyPositive_continuousLinearMapOfBilin_iff.mp hh
  have hhs' : h.toBilinForm.IsSymm := isSymm_toBilinForm_iff.mpr hhs
  have hhpos' (v : E) (hv : v ≠ 0) : 0 < h.toBilinForm v v := hhpos v hv
  have hqs : q.toBilinForm.IsSymm := isSymm_toBilinForm_iff.mpr hq
  set N := h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0)
  set P := h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0)
  -- The vector `v - π v` is the component of `v` in `P`.
  have hsub (v : E) : v - N.projection P hc v ∈ P := by
    rw [← Submodule.projection_eq_self_sub_projection hc]
    exact Submodule.projection_apply_mem hc.symm v
  refine ((eq_negativeSpectralProjection_iff hh hq hq').mpr ⟨?_, fun u v ↦ ?_, fun u v ↦ ?_,
    fun u hu ↦ ?_, fun u hu ↦ ?_⟩).symm
  · ext u
    exact congr($(Submodule.isIdempotentElem_projection hc) u)
  · exact (LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace hhs' hqs
      Iio_disjoint_Ioi_same (Submodule.projection_apply_mem hc u) (hsub v)).1
  · exact (LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace hhs' hqs
      Iio_disjoint_Ioi_same (Submodule.projection_apply_mem hc u) (hsub v)).2
  · exact LinearMap.BilinForm.apply_self_neg_of_mem_relativeSpectralSubspace_Iio hhs' hhpos' hqs
      (Submodule.projection_apply_mem hc u) hu
  · exact LinearMap.BilinForm.apply_self_pos_of_mem_relativeSpectralSubspace_Ioi hhs' hhpos' hqs
      (hsub u) hu

/-- **The kernel of the negative spectral projection is the positive relative spectral subspace**
of a nondegenerate `q`: the span of the vectors `v` with `q v = μ h v` for some `μ > 0`. -/
theorem ker_negativeSpectralProjection (hh : IsStrictlyPositive h♯)
    (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q) :
    (q.negativeSpectralProjection h).ker =
      h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) := by
  obtain ⟨hhs, hhpos⟩ := isStrictlyPositive_continuousLinearMapOfBilin_iff.mp hh
  rw [negativeSpectralProjection_eq_projection hh hq hq'
    (LinearMap.BilinForm.isCompl_relativeSpectralSubspace_Iio_Ioi (isSymm_toBilinForm_iff.mpr hhs)
      (fun v hv ↦ hhpos v hv) (isSymm_toBilinForm_iff.mpr hq)
      (by rw [ker_toBilinForm, LinearMap.ker_eq_bot.mpr hq'])),
    LinearMap.coe_toContinuousLinearMap, Submodule.ker_projection]

/-! ### Smooth dependence -/

/-- **The negative spectral projection depends smoothly on the form and the metric**, including
real analytically, as long as the form stays symmetric and nondegenerate and the metric positive
definite. Smoothness is within this set of pairs, not on an open subset of all pairs of forms. -/
theorem contDiffOn_negativeSpectralProjection {n : ℕ∞ω} :
    ContDiffOn ℝ n
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1.negativeSpectralProjection p.2)
      {p | (∀ u v, p.1 u v = p.1 v u) ∧ Function.Injective p.1 ∧ IsStrictlyPositive p.2♯} := by
  set U := {p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) |
    (∀ u v, p.1 u v = p.1 v u) ∧ Function.Injective p.1 ∧ IsStrictlyPositive p.2♯}
  have hT : ContDiffOn ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      p.2.metricChangeTransport) U :=
    contDiff_snd.contDiffOn.metricChangeTransport fun p hp ↦ hp.2.2
  have hS : ContDiffOn ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      CFC.sqrt p.2♯) U :=
    contDiff_snd.contDiffOn.sqrt_continuousLinearMapOfBilin fun p hp ↦ hp.2.2
  -- The Riesz operator of the pulled-back form is smooth in the pair.
  have hA : ContDiffOn ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      (p.1.bilinearComp p.2.metricChangeTransport p.2.metricChangeTransport)♯) U :=
    contDiff_continuousLinearMapOfBilin.comp_contDiffOn
      (contDiff_fst.contDiffOn.clm_bilinearComp hT hT)
  have hP := hA.starProjection_pointSpectralSubspace_Iio_zero
    (fun p hp ↦ isSelfAdjoint_iff_isSymmetric.mpr
      (isSymmetric_continuousLinearMapOfBilin_bilinearComp hp.1))
    (fun p hp ↦ isUnit_iff_isUnit_toLinearMap.mpr ((LinearMap.isUnit_iff_ker_eq_bot _).mpr
      (ker_continuousLinearMapOfBilin_bilinearComp hp.2.2 hp.2.1)))
  exact (hT.mul hP).mul hS

/-- **A smooth family of nondegenerate forms and positive definite metrics has a smooth family
of negative spectral projections.** -/
theorem _root_.ContDiffOn.negativeSpectralProjection {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ∞ω} {s : Set F} {q h : F → E →L[ℝ] E →L[ℝ] ℝ}
    (hqd : ContDiffOn ℝ n q s) (hhd : ContDiffOn ℝ n h s) (hq : ∀ x ∈ s, ∀ u v, q x u v = q x v u)
    (hq' : ∀ x ∈ s, Function.Injective (q x)) (hh : ∀ x ∈ s, IsStrictlyPositive (h x)♯) :
    ContDiffOn ℝ n (fun x ↦ (q x).negativeSpectralProjection (h x)) s :=
  contDiffOn_negativeSpectralProjection.comp (hqd.prodMk hhd) fun x hx ↦
    ⟨hq x hx, hq' x hx, hh x hx⟩

end ContinuousLinearMap

/-! ### Finite-dimensional normed spaces -/

namespace TauCeti

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Smooth negative relative spectral projections on a finite-dimensional normed space.** There
is a family `Φ` of projections of `P`, indexed by the pairs `(q, h)` of a symmetric nondegenerate
bilinear form `q` and a positive definite symmetric bilinear form `h`, which depends real
analytically on the pair, and whose range is the negative relative spectral subspace of `q` with
respect to `h` (spanned by the vectors `v` with `q v = μ h v` for some `μ < 0`) and whose kernel is
the positive one. No inner product on `P` is needed. -/
theorem exists_contDiffOn_range_eq_relativeSpectralSubspace :
    ∃ Φ : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) → P →L[ℝ] P,
      ContDiffOn ℝ ω Φ {x | (∀ u v, x.1 u v = x.1 v u) ∧ Function.Injective x.1 ∧
        (∀ u v, x.2 u v = x.2 v u) ∧ ∀ u, u ≠ 0 → 0 < x.2 u u} ∧
      ∀ q h : P →L[ℝ] P →L[ℝ] ℝ, (∀ u v, q u v = q v u) → Function.Injective q →
        (∀ u v, h u v = h v u) → (∀ u, u ≠ 0 → 0 < h u u) →
        IsIdempotentElem (Φ (q, h)) ∧
        (Φ (q, h)).range = h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Iio 0) ∧
        (Φ (q, h)).ker = h.toBilinForm.relativeSpectralSubspace q.toBilinForm (Ioi 0) := by
  set W := EuclideanSpace ℝ (Fin (Module.finrank ℝ P))
  let T : P ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq (by simp [W])
  set Ts : W →L[ℝ] P := (T.symm : W →L[ℝ] P)
  -- Pulled back to `W`, a nondegenerate form and a metric on `P` stay so.
  have hpull {q h : P →L[ℝ] P →L[ℝ] ℝ} (hq : ∀ u v, q u v = q v u) (hq' : Function.Injective q)
      (hh : ∀ u v, h u v = h v u) (hh' : ∀ u, u ≠ 0 → 0 < h u u) :
      (∀ u v, q.bilinearComp Ts Ts u v = q.bilinearComp Ts Ts v u) ∧
        Function.Injective (q.bilinearComp Ts Ts) ∧
        IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (h.bilinearComp Ts Ts)) :=
    ⟨fun u v ↦ hq _ _, ContinuousLinearMap.injective_bilinearComp hq' T.symm.bijective,
      isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr ⟨fun u v ↦ hh _ _,
        fun u hu ↦ hh' _ ((map_ne_zero_iff _ T.symm.injective).mpr hu)⟩⟩
  refine ⟨fun x ↦ Ts ∘L (x.1.bilinearComp Ts Ts).negativeSpectralProjection
    (x.2.bilinearComp Ts Ts) ∘L (T : P →L[ℝ] W), ?_, fun q h hq hq' hh hh' ↦ ?_⟩
  · have hc : ContDiff ℝ ω fun x : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) ↦
        (x.1.bilinearComp Ts Ts, x.2.bilinearComp Ts Ts) :=
      contDiffOn_univ.mp ((contDiff_fst.contDiffOn.clm_bilinearComp contDiffOn_const
        contDiffOn_const).prodMk (contDiff_snd.contDiffOn.clm_bilinearComp contDiffOn_const
        contDiffOn_const))
    exact contDiffOn_const.clm_comp
      ((ContinuousLinearMap.contDiffOn_negativeSpectralProjection.comp hc.contDiffOn
        fun x (hx : x ∈ {x : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) |
          (∀ u v, x.1 u v = x.1 v u) ∧ Function.Injective x.1 ∧ (∀ u v, x.2 u v = x.2 v u) ∧
            ∀ u, u ≠ 0 → 0 < x.2 u u}) ↦
          hpull hx.1 hx.2.1 hx.2.2.1 hx.2.2.2).clm_comp contDiffOn_const)
  obtain ⟨hqs, hqi, hhp⟩ := hpull hq hq' hh hh'
  set N := (q.bilinearComp Ts Ts).negativeSpectralProjection (h.bilinearComp Ts Ts)
  -- The relative spectral subspaces of the pulled-back forms are carried to those of `q` and `h`.
  have hmap (Ω : Set ℝ) : ((h.bilinearComp Ts Ts).toBilinForm.relativeSpectralSubspace
      (q.bilinearComp Ts Ts).toBilinForm Ω).map (Ts : W →ₗ[ℝ] P) =
      h.toBilinForm.relativeSpectralSubspace q.toBilinForm Ω := by
    have hc (B : P →L[ℝ] P →L[ℝ] ℝ) : (B.bilinearComp Ts Ts).toBilinForm =
        B.toBilinForm.compl₁₂ (Ts : W →ₗ[ℝ] P) (Ts : W →ₗ[ℝ] P) := by
      ext u v
      simp
    rw [hc, hc]
    exact LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂ T.symm.toLinearEquiv
  have hT : LinearMap.range ((T : P →L[ℝ] W) : P →ₗ[ℝ] W) = ⊤ :=
    LinearMap.range_eq_top.mpr T.surjective
  have hTs : LinearMap.ker (Ts : W →ₗ[ℝ] P) = ⊥ := LinearMap.ker_eq_bot.mpr T.symm.injective
  refine ⟨?_, ?_, ?_⟩
  · -- Conjugating the projection `N` by `T` gives a projection.
    have hN := ContinuousLinearMap.isIdempotentElem_negativeSpectralProjection
      (q := q.bilinearComp Ts Ts) hhp
    ext u
    simpa [Ts] using congr(Ts ($hN.eq (T u)))
  · rw [← hmap, ← ContinuousLinearMap.range_negativeSpectralProjection hhp hqs,
      ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hT]
  · rw [← hmap, ← ContinuousLinearMap.ker_negativeSpectralProjection hhp hqs hqi,
      ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.ker_comp_of_ker_eq_bot _ hTs, LinearMap.ker_comp]
    exact Submodule.comap_equiv_eq_map_symm T.toLinearEquiv N.ker

end TauCeti
