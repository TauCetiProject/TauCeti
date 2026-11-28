/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Projection.Nearby
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence

/-!
# Nearby and homotopic projections

Re-exports `TauCeti.Analysis.CStarAlgebra.Projection.Nearby` (Kato's overlap-polar unitary
`IsStarProjection.nearbyUnitary`, `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`, and
`Continuous.exists_joined_one_mul_mul_star_eq`) and derives the non-unital and matrix-level
consequences:

* `IsStarProjection.exists_star_mul_self_eq_of_norm_sub_lt_one`: in a C⋆-algebra, possibly
  without unit, projections with `‖p - q‖ < 1` are Murray–von Neumann equivalent.
* `Continuous.exists_star_mul_self_eq`: the values of a continuous family of projections over a
  preconnected space are Murray–von Neumann equivalent.
* `Continuous.isMurrayVonNeumannEquivalent`: the values of a continuous family of matrix
  projections over a C⋆-algebra are Murray–von Neumann equivalent matrix projections.
* `Matrix.IsMurrayVonNeumannEquivalent.exists_path_fromBlocks`: over a unital C⋆-algebra,
  equivalent matrix projections `p` and `q` are joined by a path of projections from `p ⊕ 0` to
  `0 ⊕ q`.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Section 2.2.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Section 4.6.
-/

public section

namespace IsStarProjection

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q : A}

/-- **Nearby projections are Murray–von Neumann equivalent.** Star projections `p` and `q` of a
C⋆-algebra, possibly without unit, with `‖p - q‖ < 1` satisfy `star v * v = p` and
`v * star v = q` for some `v`. -/
theorem exists_star_mul_self_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  obtain ⟨u, hupq, -, -⟩ := hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq hpq
  exact hp.exists_star_mul_self_eq_of_mem_unitary_unitization u.property hupq

end NonUnital

end IsStarProjection

section Continuous

/-! The statements below write `Star.star`: in a declaration named `Continuous.foo`, plain `star`
resolves to `Continuous.star`. -/

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

/-- **Homotopic projections are Murray–von Neumann equivalent.** For a continuous family `f` of
star projections of a C⋆-algebra, possibly without unit, over a preconnected space, any two values
satisfy `star v * v = f x` and `v * star v = f y` for some `v`. -/
theorem Continuous.exists_star_mul_self_eq {A : Type*} [NonUnitalCStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ v : A, Star.star v * v = f x ∧ v * Star.star v = f y := by
  have hfp' (x : X) : IsStarProjection ((f x : A) : Unitization ℂ A) := by
    simpa using (hfp x).map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  obtain ⟨u, -, hu⟩ :=
    ((Unitization.continuous_inr (𝕜 := ℂ)).comp hf).exists_joined_one_mul_mul_star_eq hfp' x y
  exact (hfp x).exists_star_mul_self_eq_of_mem_unitary_unitization u.property hu

/-- **Homotopic matrix projections are Murray–von Neumann equivalent.** For a continuous family `f`
of matrix projections over a C⋆-algebra, possibly without unit, over a preconnected space, any two
values `f x` and `f y` are Murray–von Neumann equivalent. The topology on matrices is the entrywise
one, which is the norm topology of `CStarMatrix n n A`. -/
theorem Continuous.isMurrayVonNeumannEquivalent {A : Type*} [NonUnitalCStarAlgebra A]
    {n : Type*} [Fintype n] {f : X → Matrix n n A} (hf : Continuous f)
    (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    Matrix.IsMurrayVonNeumannEquivalent (f x) (f y) := by
  -- `CStarMatrix n n A` is a C⋆-algebra for the spectral order on `A`.
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  have hfp' (x : X) : IsStarProjection (CStarMatrix.ofMatrix (f x)) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 (hfp x)
  have hg : Continuous fun x ↦ CStarMatrix.ofMatrix (f x) := by
    rw [CStarMatrix.ofMatrix_eq_ofMatrixL]
    exact CStarMatrix.ofMatrixL.continuous.comp hf
  obtain ⟨v, hv₁, hv₂⟩ := hg.exists_star_mul_self_eq hfp' x y
  simpa using CStarMatrix.isMurrayVonNeumannEquivalent_of_star_mul_self_eq (hfp' x) (hfp' y) hv₁ hv₂

end Continuous

/-- **Equivalent projections are homotopic after stabilization.** Murray–von Neumann equivalent
matrix projections `p` and `q` over a unital C⋆-algebra are joined by a continuous path of
projections from `p ⊕ 0` to `0 ⊕ q`. -/
theorem Matrix.IsMurrayVonNeumannEquivalent.exists_path_fromBlocks {A : Type*} [CStarAlgebra A]
    {m n : Type*} [Fintype m] [Fintype n] {p : Matrix m m A} {q : Matrix n n A}
    (h : Matrix.IsMurrayVonNeumannEquivalent p q) :
    ∃ γ : Path (Matrix.fromBlocks p 0 0 0) (Matrix.fromBlocks 0 0 0 q),
      ∀ t, IsStarProjection (γ t) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  have h' : CStarMatrix.MurrayVonNeumannEquiv
      (CStarMatrix.ofMatrix p) (CStarMatrix.ofMatrix q) :=
    CStarMatrix.murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mpr
      (by simpa only [Equiv.symm_apply_apply] using h)
  obtain ⟨γ, hγ⟩ := h'.exists_path_isStarProjection_fromBlocks_zero₂₂_fromBlocks_zero₁₁
  refine ⟨(γ.map CStarMatrix.ofMatrixL.symm.continuous).cast ?_ ?_, fun t ↦ ?_⟩
  · simp [CStarMatrix.ofMatrix_symm_fromBlocks, CStarMatrix.ofMatrix_symm_zero]
  · simp [CStarMatrix.ofMatrix_symm_fromBlocks, CStarMatrix.ofMatrix_symm_zero]
  · simpa using CStarMatrix.isStarProjection_ofMatrix_symm_iff.mpr (hγ t)
