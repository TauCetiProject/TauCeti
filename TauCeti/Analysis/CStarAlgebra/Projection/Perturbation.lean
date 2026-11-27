/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import Mathlib.Topology.Connected.Clopen
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.Projection.Conjugacy
import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence
import TauCeti.Analysis.CStarAlgebra.Unitary.Connected

/-!
# Nearby and homotopic projections

Two star projections `p` and `q` in a unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a
unitary `u` with `‖u - 1‖ ≤ √2 * ‖p - q‖`. The unitary is the unitary part of the polar
decomposition of the intertwiner `z = q * p + (1 - q) * (1 - p)`: since
`star z * z = z * star z = 1 - (p - q) ^ 2` commutes with `p` and `q`, the element
`u = z * (1 - (p - q) ^ 2) ^ (-1 / 2)` is a unitary with `u * p * star u = q`, and its real part
`(1 - (p - q) ^ 2) ^ (1 / 2)` gives the norm estimate. Since `‖u - 1‖ < 2`, the unitary lies in
the path component of the identity of the unitary group.

Consequently the values of a norm-continuous family of projections over a preconnected space are
mutually unitarily equivalent, through unitaries joined to `1`. In a C⋆-algebra without unit,
applying this in the unitization shows that nearby projections, and the values of a continuous
family of projections, are Murray–von Neumann equivalent. For matrices over a C⋆-algebra this says
that matrix projections joined by a path of matrix projections are Murray–von Neumann equivalent,
so they have the same class in the projection monoid `V(A)`. Conversely, over a unital C⋆-algebra,
equivalent matrix projections `p` and `q` are joined by a path of projections after
stabilization, from `p ⊕ 0` to `0 ⊕ q`.

## Main statements

* `IsStarProjection.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one`: projections `p` and
  `q` of a unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a unitary `u` with
  `‖u - 1‖ ≤ √2 * ‖p - q‖`.
* `IsStarProjection.exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one`: the conjugating
  unitary can be chosen in the path component of `1`.
* `IsStarProjection.exists_star_mul_self_eq_of_norm_sub_lt_one`: in a C⋆-algebra, possibly
  without unit, projections with `‖p - q‖ < 1` are Murray–von Neumann equivalent.
* `Continuous.exists_joined_one_mul_mul_star_eq`: the values of a continuous family of projections
  of a unital C⋆-algebra over a preconnected space are conjugate by unitaries joined to `1`.
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

section Unital

variable {A : Type*} [CStarAlgebra A] {p q : A}

/-- **Nearby projections are unitarily equivalent.** Star projections `p` and `q` of a unital
C⋆-algebra with `‖p - q‖ < 1` are conjugate, `u * p * star u = q`, by a unitary `u` with
`‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u ∈ unitary A, u * p * star u = q ∧ ‖u - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨_, (hp.projectionConjugacyUnitary hq hpq).property,
    hp.conjugate_projectionConjugacyUnitary hq hpq,
    hp.norm_projectionConjugacyUnitary_sub_one_le hq hpq⟩

/-- **Nearby projections are homotopic through unitaries.** Star projections `p` and `q` of a
unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a unitary in the path component of `1`. -/
theorem exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q :=
  ⟨_, hp.joined_one_projectionConjugacyUnitary hq hpq,
    hp.conjugate_projectionConjugacyUnitary hq hpq⟩

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q : A}

/-- **Nearby projections are Murray–von Neumann equivalent.** Star projections `p` and `q` of a
C⋆-algebra, possibly without unit, with `‖p - q‖ < 1` satisfy `star v * v = p` and
`v * star v = q` for some `v`. -/
theorem exists_star_mul_self_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hp' := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hq' := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  rw [Unitization.inrNonUnitalStarAlgHom_apply] at hp' hq'
  obtain ⟨u, hu, hupq, -⟩ := hp'.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one hq'
    (by rwa [← Unitization.inr_sub, Unitization.norm_inr])
  exact hp.exists_star_mul_self_eq_of_mem_unitary_unitization hu hupq

end NonUnital

end IsStarProjection

section Continuous

/-! The statements below write `Star.star`: in a declaration named `Continuous.foo`, plain `star`
resolves to `Continuous.star`. -/

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

/-- **Homotopic projections are unitarily equivalent.** For a continuous family `f` of star
projections of a unital C⋆-algebra over a preconnected space, any two values `f x` and `f y` are
conjugate by a unitary in the path component of `1`. For a path of projections this compares its
endpoints. -/
theorem Continuous.exists_joined_one_mul_mul_star_eq {A : Type*} [CStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y := by
  refine PreconnectedSpace.induction₂'
    (fun x y ↦ ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y)
    (fun x ↦ ?_) ⟨fun a b c ⟨u, hu, hab⟩ ⟨v, hv, hbc⟩ ↦ ⟨v * u, ?_, ?_⟩⟩ x y
  · filter_upwards [hf.continuousAt.eventually (Metric.ball_mem_nhds (f x) one_pos)] with y hy
    rw [dist_eq_norm] at hy
    exact ⟨(hfp x).exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one (hfp y)
      (by rwa [norm_sub_rev]), (hfp y).exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one
      (hfp x) hy⟩
  · simpa using hv.mul hu
  · rw [Submonoid.coe_mul, star_mul, ← hbc, ← hab]
    simp only [mul_assoc]

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
  refine ⟨hfp x, hfp y, CStarMatrix.ofMatrix.symm v, ?_, ?_⟩
  · rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, hv₁,
      Equiv.symm_apply_apply]
  · rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, hv₂,
      Equiv.symm_apply_apply]

end Continuous

/-- **Equivalent projections are homotopic after stabilization.** Murray–von Neumann equivalent
matrix projections `p` and `q` over a unital C⋆-algebra are joined by a continuous path of
projections from `p ⊕ 0` to `0 ⊕ q`. -/
theorem Matrix.IsMurrayVonNeumannEquivalent.exists_path_fromBlocks {A : Type*} [CStarAlgebra A]
    {m n : Type*} [Fintype m] [Fintype n] {p : Matrix m m A} {q : Matrix n n A}
    (h : Matrix.IsMurrayVonNeumannEquivalent p q) :
    ∃ γ : Path (Matrix.fromBlocks p 0 0 0) (Matrix.fromBlocks 0 0 0 q),
      ∀ t, IsStarProjection (γ t) := by
  classical
  -- `CStarMatrix (m ⊕ n) (m ⊕ n) A` is a C⋆-algebra for the spectral order on `A`.
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  -- The path conjugates `p ⊕ 0` by a path of unitaries from `1` to a self-adjoint unitary `w`
  -- carrying `p ⊕ 0` to `0 ⊕ q`.
  obtain ⟨w, hw, hwu, hwpq⟩ := h.exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star
  set P := Matrix.fromBlocks p 0 0 (0 : Matrix n n A)
  have hP : IsStarProjection P := h.isStarProjection_left.fromBlocks_zero₁₂_zero₂₁ (.zero _)
  -- The unitary `w`, read in the C⋆-algebra `CStarMatrix (m ⊕ n) (m ⊕ n) A`.
  have hW : CStarMatrix.ofMatrix w ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
    CStarMatrix.ofMatrix_mem_unitary_iff.2 hwu
  have hWsa : IsSelfAdjoint (CStarMatrix.ofMatrix w) := CStarMatrix.isSelfAdjoint_ofMatrix_iff.2 hw
  let γ := (Unitary.joined_one_of_isSelfAdjoint ⟨_, hW⟩ hWsa).somePath
  -- Conjugation of `P` by a unitary, read back as an ordinary matrix.
  let f : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) → Matrix (m ⊕ n) (m ⊕ n) A := fun u ↦
    CStarMatrix.ofMatrix.symm
      ((u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * CStarMatrix.ofMatrix P * star (u : CStarMatrix _ _ A))
  have hf : Continuous f := by
    have : Continuous (CStarMatrix.ofMatrix.symm : CStarMatrix (m ⊕ n) (m ⊕ n) A → _) :=
      CStarMatrix.ofMatrixL.symm.continuous
    exact this.comp (by fun_prop)
  have hf₁ (u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) : f u =
      CStarMatrix.ofMatrix.symm (u : CStarMatrix _ _ A) * P *
        CStarMatrix.ofMatrix.symm (star (u : CStarMatrix _ _ A)) := by
    simp only [f, CStarMatrix.ofMatrix_symm_mul, Equiv.symm_apply_apply]
  refine ⟨(γ.map hf).cast ?_ ?_, fun t ↦ ?_⟩
  · simp [hf₁]
  · rw [hf₁, CStarMatrix.ofMatrix_symm_star]
    simpa [Matrix.star_eq_conjTranspose] using hwpq.symm
  · have hP' : IsStarProjection (CStarMatrix.ofMatrix P) :=
      CStarMatrix.isStarProjection_ofMatrix_iff.2 hP
    exact CStarMatrix.isStarProjection_ofMatrix_symm_iff.2
      (CStarMatrix.murrayVonNeumannEquiv_unitary_conj hP' (γ t)).isStarProjection_right
