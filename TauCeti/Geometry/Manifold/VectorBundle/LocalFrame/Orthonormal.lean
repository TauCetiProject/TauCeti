/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Orthonormal local frames

Let `V → M` be a vector bundle whose fibres carry inner products.

* `IsLocalFrameOn.coeff_eq_inner`: the coefficient functionals of an orthonormal local frame are
  its metric duals. This lets local-frame connection and curvature coefficients be read as inner
  products.
* `IsLocalFrameOn.sum_inner_smul_eq` and `IsLocalFrameOn.sum_sq_norm_inner`: every fibre vector
  is the sum of these inner products times the frame vectors, and its squared norm is the sum of
  the squared norms of these inner products.
* `IsLocalFrameOn.of_orthonormal`: a `C^n` family of `finrank 𝕜 F` pointwise orthonormal sections
  of a finite-rank bundle on `u` forms a `C^n` local frame on `u`.
* `IsLocalFrameOn.toOrthonormalBasisAt`: at each point `x ∈ u`, an orthonormal local frame gives
  an `OrthonormalBasis ι 𝕜 (V x)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace IsLocalFrameOn

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace 𝕜 (V x)]
  [FiberBundle F V]
  {ι : Type*}

section

variable [Finite ι] {n : ℕ∞ω} {s : ι → Π x, V x} {u : Set M}
  (hs : IsLocalFrameOn I F n s u) {x : M}

/-- The coefficients of an orthonormal local frame are its metric duals. Only orthonormality
at the point is needed. -/
theorem coeff_eq_inner (hx : x ∈ u) (ho : Orthonormal 𝕜 (fun i ↦ s i x))
    (i : ι) (v : V x) : hs.coeff i x v = inner 𝕜 (s i x) v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hexp : v = ∑ j, hs.coeff j x v • s j x := by
    simpa only [FiberBundle.extend_apply_self] using
      hs.coeff_sum_eq (FiberBundle.extend F v) hx
  have h := ho.inner_right_fintype (fun j ↦ hs.coeff j x v) i
  rw [← hexp] at h
  exact h.symm

include hs

/-- A frame orthonormal at a point reconstructs every fibre vector from its inner products. -/
theorem sum_inner_smul_eq [Fintype ι] (hx : x ∈ u)
    (ho : Orthonormal 𝕜 (fun i ↦ s i x)) (v : V x) :
    ∑ i, inner 𝕜 (s i x) v • s i x = v := by
  simpa only [FiberBundle.extend_apply_self, hs.coeff_eq_inner hx ho] using
    (hs.coeff_sum_eq (FiberBundle.extend F v) hx).symm

/-- Parseval's identity for a local frame orthonormal at the point of evaluation. -/
theorem sum_sq_norm_inner [Fintype ι] (hx : x ∈ u)
    (ho : Orthonormal 𝕜 (fun i ↦ s i x)) (v : V x) :
    ∑ i, ‖inner 𝕜 (s i x) v‖ ^ 2 = ‖v‖ ^ 2 := by
  symm
  rw [@norm_sq_eq_re_inner 𝕜]
  nth_rw 1 [← hs.sum_inner_smul_eq hx ho v]
  simp only [sum_inner, inner_smul_left, map_sum, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

end

variable {n : ℕ∞ω} {s : ι → Π x, V x} {u : Set M}

/-- A `C^n` family of `finrank 𝕜 F` pointwise orthonormal sections on `u` forms a `C^n` local
frame on `u`. -/
theorem of_orthonormal [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F] [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank 𝕜 F)
    (ho : ∀ x ∈ u, Orthonormal 𝕜 fun i ↦ s i x)
    (hs : ∀ i, CMDiff[u] n (T% (s i))) :
    IsLocalFrameOn I F n s u :=
  of_linearIndependent hcard (fun x hx ↦ (ho x hx).linearIndependent) hs

/-- Given an orthonormal local frame `{s i}` on `u ∋ x`, returns the orthonormal basis
`{s i x}` of the fibre `V x`. -/
noncomputable def toOrthonormalBasisAt [Fintype ι] (hs : IsLocalFrameOn I F n s u) {x : M}
    (hx : x ∈ u) (ho : Orthonormal 𝕜 fun i ↦ s i x) :
    OrthonormalBasis ι 𝕜 (V x) :=
  OrthonormalBasis.mk ho (hs.generating hx)

@[simp]
theorem coe_toOrthonormalBasisAt [Fintype ι] (hs : IsLocalFrameOn I F n s u) {x : M}
    (hx : x ∈ u) (ho : Orthonormal 𝕜 fun i ↦ s i x) :
    ⇑(hs.toOrthonormalBasisAt hx ho) = fun i ↦ s i x :=
  OrthonormalBasis.coe_mk ho (hs.generating hx)

end IsLocalFrameOn
