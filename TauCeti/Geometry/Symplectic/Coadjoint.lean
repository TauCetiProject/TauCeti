/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Coadjoint tangent spaces are symplectic

For a real Lie algebra `L` and `ν ∈ L*`, the Kirillov–Kostant–Souriau form
`ω_ν([ξ], [η]) = ν ⁅ξ, η⁆` on the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit through
`ν` (`Module.Dual.kksForm`) is alternating and nondegenerate. This file packages it as a linear
`TauCeti.SymplecticForm` (`Module.Dual.kksSymplecticForm ν`). When `L` is the Lie algebra of a Lie
group whose coadjoint orbit through `ν` is a smooth homogeneous space, this is the pointwise value
at `ν` of the symplectic form of the orbit. When `L ⧸ L_ν` is finite-dimensional, its dimension is
even (`Module.Dual.even_finrank_quotient_lieAnnihilator`).

The algebraic naturality of the KKS form becomes a statement about symplectomorphisms: along a
surjective Lie algebra map `f : L → L'` with `ν = ν' ∘ f`, the equivalence `[ξ] ↦ [f ξ]` is a
symplectomorphism from `ω_ν` to `ω_ν'`
(`Module.Dual.isSymplectomorphism_quotientLieAnnihilatorEquiv`), and for a product functional
`(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂` on `L₁ × L₂` the equivalence `[(ξ₁, ξ₂)] ↦ ([ξ₁], [ξ₂])` is a
symplectomorphism onto the direct sum of `ω_ν₁` and `ω_ν₂`
(`Module.Dual.isSymplectomorphism_quotientLieAnnihilatorProdEquiv`).

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open Module TauCeti

namespace Module.Dual

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (ν : Dual ℝ L)

/-- The Kirillov–Kostant–Souriau form `ω_ν([ξ], [η]) = ν ⁅ξ, η⁆` on the algebraic tangent model
`L ⧸ L_ν` of the coadjoint orbit through `ν`, as a linear symplectic form. -/
noncomputable def kksSymplecticForm : SymplecticForm (L ⧸ (lieAnnihilator ℝ L ν).toSubmodule) where
  toBilinForm := ν.kksForm
  isAlt := ν.isAlt_kksForm
  nondegenerate := ν.kksForm_nondegenerate

@[simp]
theorem kksSymplecticForm_toBilinForm : ν.kksSymplecticForm.toBilinForm = ν.kksForm :=
  (rfl)

/-- The algebraic tangent model `L ⧸ L_ν` of a coadjoint orbit of a real Lie algebra, when
finite-dimensional, has even dimension, since it carries the symplectic form `ω_ν`. -/
theorem even_finrank_quotient_lieAnnihilator
    [FiniteDimensional ℝ (L ⧸ (lieAnnihilator ℝ L ν).toSubmodule)] :
    Even (finrank ℝ (L ⧸ (lieAnnihilator ℝ L ν).toSubmodule)) :=
  ν.kksSymplecticForm.even_finrank

/-! ### Naturality and products -/

section Map

variable {L' : Type*} [LieRing L'] [LieAlgebra ℝ L'] {ν} (ν' : Dual ℝ L') {f : L →ₗ⁅ℝ⁆ L'}
  (hf : Function.Surjective f) (hν : ν'.comp (f : L →ₗ[ℝ] L') = ν)

/-- **Naturality of the Kirillov–Kostant–Souriau symplectic form.** Along a surjective Lie algebra
map `f : L → L'` with `ν = ν' ∘ f`, the equivalence `[ξ] ↦ [f ξ]` of algebraic tangent models is a
symplectomorphism from `ω_ν` to `ω_ν'`. -/
theorem isSymplectomorphism_quotientLieAnnihilatorEquiv :
    SymplecticForm.IsSymplectomorphism ν.kksSymplecticForm ν'.kksSymplecticForm
      (quotientLieAnnihilatorEquiv ν' hf hν) :=
  SymplecticForm.isSymplectomorphism_iff.mpr (kksForm_quotientLieAnnihilatorEquiv ν' hf hν)

end Map

section Prod

variable {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℝ L₁] [LieRing L₂] [LieAlgebra ℝ L₂]
  (ν₁ : Dual ℝ L₁) (ν₂ : Dual ℝ L₂)

/-- **The Kirillov–Kostant–Souriau symplectic form of a product.** The equivalence
`[(ξ₁, ξ₂)] ↦ ([ξ₁], [ξ₂])` is a symplectomorphism from the KKS form of
`(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂` on `L₁ × L₂` to the direct sum of `ω_ν₁` and `ω_ν₂`. -/
theorem isSymplectomorphism_quotientLieAnnihilatorProdEquiv :
    SymplecticForm.IsSymplectomorphism (kksSymplecticForm (ν₁.coprod ν₂))
      (ν₁.kksSymplecticForm.prod ν₂.kksSymplecticForm) (ν₁.quotientLieAnnihilatorProdEquiv ν₂) :=
  SymplecticForm.isSymplectomorphism_iff.mpr fun x y ↦ (kksForm_coprod ν₁ ν₂ x y).symm

end Prod

end Module.Dual
