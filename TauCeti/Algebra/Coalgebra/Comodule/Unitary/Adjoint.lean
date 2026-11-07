/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoints of intertwiners of unitary comodules

The Hilbert adjoint of a morphism between finite-dimensional unitary native comodules is
again colinear. Thus their intertwiner spaces have an involutive, conjugate-linear dagger
reversing composition. Only a star algebra with a coalgebra structure is needed: no antipode,
positivity or norm on the coefficient algebra is assumed.

The proof uses coefficient matrices in orthonormal bases: taking conjugate transposes of
`V T = T U` and multiplying by the unitary matrices gives `U T* = T* V`.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.3, for unitary corepresentations and their intertwiners.
-/

public section

open Module
open scoped Matrix

namespace TauCeti.Comodule.Hom

variable {𝕜 A M N P : Type*} [RCLike 𝕜] [Semiring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A] [Coalgebra 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [FiniteDimensional 𝕜 N]
  [NormedAddCommGroup P] [InnerProductSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [Comodule 𝕜 A M] [Comodule 𝕜 A N] [Comodule 𝕜 A P]

/-- The Hilbert adjoint of an intertwiner between finite unitary comodules, as a native
comodule morphism. -/
noncomputable def adjoint (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) : Hom 𝕜 A N M where
  toLinearMap := f.toLinearMap.adjoint
  map_coact := by
    classical
    let b := stdOrthonormalBasis 𝕜 M
    let c := stdOrthonormalBasis 𝕜 N
    rw [c.toBasis.map_coact_iff_coefficientMatrix b.toBasis,
      LinearMap.toMatrix_adjoint b c]
    have h := congrArg Matrix.conjTranspose (f.coefficientMatrix_mul_toMatrix b.toBasis c.toBasis)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      ← Matrix.conjTranspose_map _ algebraMap_star_comm] at h
    have hb := hM.coefficientMatrix_mem_unitary b
    have hc := hN.coefficientMatrix_mem_unitary c
    have heq := congrArg (fun X => coefficientMatrix (C := A) b.toBasis * X *
      coefficientMatrix (C := A) c.toBasis) h
    simp only [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, hc.1,
      Matrix.mul_one] at heq
    simpa only [← Matrix.mul_assoc, hb.2, Matrix.one_mul] using heq

/-- Forgetting colinearity gives the ordinary Hilbert adjoint. -/
@[simp]
theorem adjoint_toLinearMap (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) :
    (f.adjoint hM hN).toLinearMap = f.toLinearMap.adjoint := (rfl)

/-- The comodule adjoint acts as the ordinary Hilbert adjoint. -/
@[simp]
theorem coe_adjoint (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) :
    ⇑(f.adjoint hM hN) = LinearMap.adjoint f.toLinearMap := (rfl)

/-- The defining inner-product identity for the comodule adjoint in the left slot. -/
theorem adjoint_inner_left (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) (x : M) (y : N) :
    inner 𝕜 (f.adjoint hM hN y) x = inner 𝕜 y (f x) := by
  simpa only [coe_adjoint, coe_toLinearMap] using
    LinearMap.adjoint_inner_left f.toLinearMap x y

/-- The defining inner-product identity for the comodule adjoint in the right slot. -/
theorem adjoint_inner_right (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) (x : M) (y : N) :
    inner 𝕜 x (f.adjoint hM hN y) = inner 𝕜 (f x) y := by
  simpa only [coe_adjoint, coe_toLinearMap] using
    LinearMap.adjoint_inner_right f.toLinearMap x y

/-- A comodule morphism is the adjoint of another exactly when it satisfies the
adjoint inner-product identity. -/
theorem eq_adjoint_iff (f : Hom 𝕜 A M N) (g : Hom 𝕜 A N M)
    (hM : IsUnitary 𝕜 A M) (hN : IsUnitary 𝕜 A N) :
    f = g.adjoint hN hM ↔ ∀ x y, inner 𝕜 (f x) y = inner 𝕜 x (g y) := by
  rw [← toLinearMap_injective.eq_iff, adjoint_toLinearMap]
  simpa only [coe_toLinearMap] using LinearMap.eq_adjoint_iff f.toLinearMap g.toLinearMap

/-- Taking the comodule adjoint twice returns the original intertwiner. -/
@[simp]
theorem adjoint_adjoint (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) : (f.adjoint hM hN).adjoint hN hM = f := by
  apply toLinearMap_injective
  simp

/-- The comodule adjoint reverses composition. -/
@[simp]
theorem adjoint_comp (g : Hom 𝕜 A N P) (f : Hom 𝕜 A M N)
    (hM : IsUnitary 𝕜 A M) (hN : IsUnitary 𝕜 A N) (hP : IsUnitary 𝕜 A P) :
    (g.comp f).adjoint hM hP = (f.adjoint hM hN).comp (g.adjoint hN hP) := by
  apply toLinearMap_injective
  simp [LinearMap.adjoint_comp]

/-- The comodule adjoint preserves the identity. -/
-- Use `rw`: the categorical API simplifies `Hom.id` before this rule could match.
theorem adjoint_id (hM : IsUnitary 𝕜 A M) : (id 𝕜 A M).adjoint hM hM = id 𝕜 A M := by
  apply toLinearMap_injective
  simp

/-- The comodule adjoint preserves zero. -/
@[simp]
theorem adjoint_zero (hM : IsUnitary 𝕜 A M) (hN : IsUnitary 𝕜 A N) :
    (0 : Hom 𝕜 A M N).adjoint hM hN = 0 := by
  apply toLinearMap_injective
  simp

/-- The comodule adjoint is additive. -/
@[simp]
theorem adjoint_add (f g : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) :
    (f + g).adjoint hM hN = f.adjoint hM hN + g.adjoint hM hN := by
  apply toLinearMap_injective
  simp

/-- The comodule adjoint is conjugate-linear in the intertwiner. -/
@[simp]
theorem adjoint_smul (r : 𝕜) (f : Hom 𝕜 A M N) (hM : IsUnitary 𝕜 A M)
    (hN : IsUnitary 𝕜 A N) :
    (r • f).adjoint hM hN = star r • f.adjoint hM hN := by
  apply toLinearMap_injective
  simp [map_smulₛₗ]

end TauCeti.Comodule.Hom
