/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.Presentation.Basic
public import TauCeti.LinearAlgebra.Dual.FiniteProjective
public import TauCeti.LinearAlgebra.Dual.Opposite
public import TauCeti.Algebra.Module.AuslanderReiten.Morphism
public import Mathlib.Algebra.Exact.Basic

/-!
# Dual right presentations

Dualizing a finite projective right presentation with values in the regular module `A`
gives a finite projective left presentation of its cokernel. The cokernel is finitely
presented over an arbitrary ring.

The `A`-valued dual makes the inverse Auslander–Bridger transpose an actual left `A`-module,
without transporting a module over the double opposite. `rightTransposePresentation` retains
the presenting projectives and maps so that the canonical recovery is available to the stable
equivalence. `rightTransposeEquiv` compares the two codomain conventions semilinearly along
the canonical equivalence from `A` to its double opposite.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

universe u v

variable {A : Type u} [Ring A]

namespace FiniteProjectivePresentation

open CategoryTheory

variable {N : ModuleCat.{v} Aᵐᵒᵖ}

/-- The transpose of a right presentation, with duals valued in `A` so that the result is
an actual left `A`-module rather than a module over the double opposite. -/
noncomputable abbrev rightTranspose (Q : FiniteProjectivePresentation N) : ModuleCat.{max u v} A :=
  ModuleCat.of A ((Q.P₁ →ₗ[Aᵐᵒᵖ] A) ⧸ LinearMap.range (Q.p.lcomp A A))

/-- Changing functional values from `A` to `Aᵐᵒᵖ` identifies the right transpose with the
ordinary transpose over `Aᵐᵒᵖ`, with scalars transported to the double opposite. -/
noncomputable def rightTransposeEquiv (Q : FiniteProjectivePresentation N) :
    ((Q.P₁ →ₗ[Aᵐᵒᵖ] A) ⧸ LinearMap.range (Q.p.lcomp A A))
      ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A)]
      AuslanderReitenTranspose Q.p :=
  (AuslanderReitenTranspose.quotientEquiv Q.p _ (opDualCodomainEquiv A Q.P₁).symm
    ((Submodule.map_symm_eq_iff (opDualCodomainEquiv A Q.P₁)).mpr
      (map_range_opDualCodomainEquiv A Q.p))).symm

/-- Right-transpose transport applies `op` to the values of a functional representative. -/
@[simp]
theorem rightTransposeEquiv_mk (Q : FiniteProjectivePresentation N)
    (φ : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquiv (Submodule.Quotient.mk φ) =
      AuslanderReitenTranspose.mk Q.p (opDualCodomainEquiv A Q.P₁ φ) := by
  apply Q.rightTransposeEquiv.symm.injective
  simp [rightTransposeEquiv]

/-- Inverse right-transpose transport removes the opposite from functional values. -/
@[simp]
theorem rightTransposeEquiv_symm_mk (Q : FiniteProjectivePresentation N)
    (φ : Module.Dual Aᵐᵒᵖ Q.P₁) :
    Q.rightTransposeEquiv.symm (AuslanderReitenTranspose.mk Q.p φ) =
      Submodule.Quotient.mk ((opDualCodomainEquiv A Q.P₁).symm φ) := by
  simp [rightTransposeEquiv]

variable {N' : ModuleCat.{v} Aᵐᵒᵖ}

/-- A morphism of right presentations induces a map of transposes in the reverse direction. -/
noncomputable def rightTransposeMap (Q : FiniteProjectivePresentation N)
    (P : FiniteProjectivePresentation N') (φ : Q.shortComplex ⟶ P.shortComplex) :
    P.rightTranspose →ₗ[A] Q.rightTranspose :=
  Q.rightTransposeEquiv.symm.toLinearMap ∘ₛₗ
    AuslanderReitenTranspose.map φ.τ₂.hom φ.τ₁.hom
      (congrArg ModuleCat.Hom.hom φ.comm₁₂.symm) ∘ₛₗ P.rightTransposeEquiv.toLinearMap

/-- On a functional, the induced transpose map is precomposition on the relation modules. -/
@[simp↓]
theorem rightTransposeMap_mk (Q : FiniteProjectivePresentation N)
    (P : FiniteProjectivePresentation N') (φ : Q.shortComplex ⟶ P.shortComplex)
    (g : P.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeMap P φ (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (g ∘ₗ φ.τ₁.hom) := by
  simp only [rightTransposeMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [rightTransposeEquiv_mk, AuslanderReitenTranspose.map_mk (p := Q.p) (q := P.p),
    rightTransposeEquiv_symm_mk]
  congr 1
  ext x
  simp

/-- The identity presentation morphism induces the identity on the right transpose. -/
@[simp]
theorem rightTransposeMap_id (Q : FiniteProjectivePresentation N) :
    Q.rightTransposeMap Q (𝟙 Q.shortComplex) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [rightTransposeMap_mk]
  simp

/-- Right-transpose maps reverse composition of presentation morphisms. -/
@[simp]
theorem rightTransposeMap_comp {N'' : ModuleCat.{v} Aᵐᵒᵖ}
    (Q : FiniteProjectivePresentation N) (P : FiniteProjectivePresentation N')
    (P' : FiniteProjectivePresentation N'') (φ : Q.shortComplex ⟶ P.shortComplex)
    (ψ : P.shortComplex ⟶ P'.shortComplex) :
    Q.rightTransposeMap P' (φ ≫ ψ) =
      (Q.rightTransposeMap P φ).comp (P.rightTransposeMap P' ψ) := by
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [LinearMap.comp_apply]
  rw [rightTransposeMap_mk, rightTransposeMap_mk, rightTransposeMap_mk]
  simp [LinearMap.comp_assoc]

/-- The finite projective presentation of a right transpose obtained by dualizing its
right presentation. The abbreviation keeps the dual modules and their maps definitionally
identifiable for double-transpose recovery. -/
noncomputable abbrev rightTransposePresentation (Q : FiniteProjectivePresentation N) :
    FiniteProjectivePresentation Q.rightTranspose := by
  let : Module.Finite A (Q.P₀ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Finite.of_surjective (opDualCodomainEquiv A Q.P₀).symm.toLinearMap
      (opDualCodomainEquiv A Q.P₀).symm.surjective
  let : Module.Finite A (Q.P₁ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Finite.of_surjective (opDualCodomainEquiv A Q.P₁).symm.toLinearMap
      (opDualCodomainEquiv A Q.P₁).symm.surjective
  let : Module.Projective A (Q.P₀ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Projective.of_equiv (opDualCodomainEquiv A Q.P₀).symm
  let : Module.Projective A (Q.P₁ →ₗ[Aᵐᵒᵖ] A) :=
    Module.Projective.of_equiv (opDualCodomainEquiv A Q.P₁).symm
  exact
    { P₀ := ModuleCat.of A (Q.P₁ →ₗ[Aᵐᵒᵖ] A)
      P₁ := ModuleCat.of A (Q.P₀ →ₗ[Aᵐᵒᵖ] A)
      p := Q.p.lcomp A A
      π := (LinearMap.range (Q.p.lcomp A A)).mkQ
      exact := LinearMap.exact_map_mkQ_range _
      surjective := Submodule.mkQ_surjective _ }

/-- A right transpose is finitely presented over an arbitrary ring. -/
instance (Q : FiniteProjectivePresentation N) : Module.FinitePresentation A Q.rightTranspose := by
  let P := Q.rightTransposePresentation
  let := P.finite₀
  let := P.finite₁
  let := P.projective₀
  let : Module.FinitePresentation A P.P₀ := Module.finitePresentation_of_projective _ _
  exact Module.finitePresentation_of_surjective P.π P.surjective
    (P.exact.linearMap_ker_eq.symm ▸ Submodule.fg_range P.p)

end FiniteProjectivePresentation

end TauCeti
