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
  {ι : Type*} {n : ℕ∞ω} {s : ι → Π x, V x} {u : Set M}

/-- The coefficients of an orthonormal local frame are its metric duals. Only orthonormality
at the point is needed. -/
theorem coeff_eq_inner [Finite ι] (hs : IsLocalFrameOn I F n s u) {x : M} (hx : x ∈ u)
    (ho : Orthonormal 𝕜 (fun i ↦ s i x)) (i : ι) (v : V x) :
    hs.coeff i x v = inner 𝕜 (s i x) v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hexp : v = ∑ j, hs.coeff j x v • s j x := by
    simpa only [FiberBundle.extend_apply_self] using
      hs.coeff_sum_eq (FiberBundle.extend F v) hx
  have h := ho.inner_right_fintype (fun j ↦ hs.coeff j x v) i
  rw [← hexp] at h
  exact h.symm

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
