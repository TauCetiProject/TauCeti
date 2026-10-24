/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Factors
public import TauCeti.RingTheory.Idempotents.Projective

/-!
# Right-projective terms of the zigzag braid complexes

For a vertex `i`, the underlying right module of the vertex bimodule is
`e_i Z ⊗[k] Z e_i`. The right ideal `e_i Z` is projective over `Zᵐᵒᵖ`, and `Z e_i` is
a direct summand of the free `k`-module `Z`. Mathlib's projectivity of tensor products,
transported through the existing factor identification, therefore makes the vertex
bimodule projective as a right `Z`-module.

The regular bimodule is a free right module, and internal shifts preserve its carrier
and scalar actions. The canonical term isomorphisms of the two braid complexes then
give right projectivity in every cohomological degree, with the remaining terms zero.
These statements hold over every commutative coefficient ring and include isolated
vertices of the componentwise algebra.

Each assertion uses the canonical restricted action of `Zᵐᵒᵖ`, obtained from the second
factor of the enveloping algebra. These are the module-theoretic inputs for studying
the tensor action on acyclic complexes.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "U" => zigzagGradedBraidBimodule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)

private def rightFactorsLinearEquiv (i : V) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
    U i ≃ₗ[Zᵐᵒᵖ] R i ⊗[k] L i := by
  letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
  exact
    { (zigzagBraidBimoduleRightFactorsEquiv k G i).toAddEquiv with
      map_smul' := fun a m ↦ by
        change zigzagBraidBimoduleRightFactorsEquiv k G i (a • m) =
          a • zigzagBraidBimoduleRightFactorsEquiv k G i m
        simpa only [op_unop] using
          zigzagBraidBimoduleRightFactorsEquiv_op_smul k G i (unop a) m }

/-- The vertex bimodule is projective for its restricted right action of the zigzag algebra. -/
theorem projective_zigzagGradedBraidBimodule_right (i : V) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
    Module.Projective Zᵐᵒᵖ (U i) := by
  let := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) (U i)
  have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
  let : Module.Projective k Z := Module.Projective.of_basis (zigzagAlgebraBasis k G)
  let : Module.Projective k (L i) := by
    apply Module.Projective.of_split ((L i).subtype.restrictScalars k)
      ((LinearMap.toSpanSingleton Z (L i) (spanSingletonGenerator (e i))).restrictScalars k)
    apply LinearMap.ext
    intro x
    exact smul_spanSingletonGenerator he x
  let : Module.Projective Zᵐᵒᵖ (R i) :=
    (show IsIdempotentElem (op (e i)) from by
      rw [IsIdempotentElem, ← op_mul, he.eq]).projective_span_singleton
  exact Module.Projective.of_equiv' (rightFactorsLinearEquiv k G i).symm

private def regularRightLinearEquiv :
    letI := TauCeti.Algebra.TensorProduct.moduleRight
      (k := k) (A := Z) (B := Zᵐᵒᵖ) (zigzagGradedBimodule k G)
    zigzagGradedBimodule k G ≃ₗ[Zᵐᵒᵖ] Zᵐᵒᵖ := by
  letI := TauCeti.Algebra.TensorProduct.moduleRight
    (k := k) (A := Z) (B := Zᵐᵒᵖ) (zigzagGradedBimodule k G)
  change Bimodule (AlgHom.id k Z) ≃ₗ[Zᵐᵒᵖ] Zᵐᵒᵖ
  exact
    { toFun := fun m ↦ op ((Bimodule.of (AlgHom.id k Z)).symm m)
      invFun := fun a ↦ Bimodule.of (AlgHom.id k Z) (unop a)
      left_inv := fun m ↦ by simp
      right_inv := fun a ↦ by simp
      map_add' := fun m n ↦ by simp only [map_add, MulOpposite.op_add]
      map_smul' := fun a m ↦ by
        change op ((Bimodule.of (AlgHom.id k Z)).symm (((1 : Z) ⊗ₜ[k] a) • m)) =
          a * op ((Bimodule.of (AlgHom.id k Z)).symm m)
        rw [Bimodule.symm_smul]
        simp only [AlgHom.id_apply, one_mul, op_mul, op_unop] }

private theorem regular_projective_right :
    letI := TauCeti.Algebra.TensorProduct.moduleRight
      (k := k) (A := Z) (B := Zᵐᵒᵖ) (zigzagGradedBimodule k G)
    Module.Projective Zᵐᵒᵖ (zigzagGradedBimodule k G) := by
  let := TauCeti.Algebra.TensorProduct.moduleRight
    (k := k) (A := Z) (B := Zᵐᵒᵖ) (zigzagGradedBimodule k G)
  exact Module.Projective.of_equiv' (regularRightLinearEquiv k G).symm

private theorem projective_of_graded_iso
    {M N : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece} (f : M ≅ N)
    (hN : letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) N
      Module.Projective Zᵐᵒᵖ N) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) M
    Module.Projective Zᵐᵒᵖ M := by
  let := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) M
  let := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) N
  let : Module.Projective Zᵐᵒᵖ N := hN
  let g := (GradedModuleCat.toModuleCat.mapIso f).toLinearEquiv
  let g' : M ≃ₗ[Zᵐᵒᵖ] N :=
    { g.toAddEquiv with
      map_smul' := fun a m ↦ by
        change g (((1 : Z) ⊗ₜ[k] a) • m) = ((1 : Z) ⊗ₜ[k] a) • g m
        exact g.map_smul _ _ }
  exact Module.Projective.of_equiv' g'.symm

private theorem projective_of_graded_isZero
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    (hM : Limits.IsZero M) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) M
    Module.Projective Zᵐᵒᵖ M := by
  let := TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) M
  let : Subsingleton M :=
    ModuleCat.subsingleton_of_isZero (GradedModuleCat.toModuleCat.map_isZero hM)
  infer_instance

/-- Every term of the braid complex is projective for the restricted right action. -/
theorem projective_zigzagBraidComplex_X_right (i : V) (n : ℤ) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight
      (k := k) (A := Z) (B := Zᵐᵒᵖ) ((zigzagBraidComplex k G i).X n)
    Module.Projective Zᵐᵒᵖ ((zigzagBraidComplex k G i).X n) := by
  by_cases h₀ : n = -1
  · subst n
    exact projective_of_graded_iso k G (zigzagBraidComplexXIso₀ k G i)
      (projective_zigzagGradedBraidBimodule_right k G i)
  by_cases h₁ : n = 0
  · subst n
    exact projective_of_graded_iso k G (zigzagBraidComplexXIso₁ k G i)
      (regular_projective_right k G)
  exact projective_of_graded_isZero k G _
    (isZero_zigzagBraidComplex_X (k := k) (G := G) i h₀ h₁)

/-- Every term of the inverse braid complex is projective for the restricted right action. -/
theorem projective_zigzagBraidInverseComplex_X_right (i : V) (n : ℤ) :
    letI := TauCeti.Algebra.TensorProduct.moduleRight
      (k := k) (A := Z) (B := Zᵐᵒᵖ) ((zigzagBraidInverseComplex k G i).X n)
    Module.Projective Zᵐᵒᵖ ((zigzagBraidInverseComplex k G i).X n) := by
  by_cases h₀ : n = 0
  · subst n
    exact projective_of_graded_iso k G (zigzagBraidInverseComplexXIso₀ k G i)
      (regular_projective_right k G)
  by_cases h₁ : n = 1
  · subst n
    apply projective_of_graded_iso k G (zigzagBraidInverseComplexXIso₁ k G i)
    -- An internal shift preserves the carrier and its restricted right action.
    simpa only [GradedModuleCat.shiftFunctor_obj] using
      projective_zigzagGradedBraidBimodule_right k G i
  exact projective_of_graded_isZero k G _
    (isZero_zigzagBraidInverseComplex_X (k := k) (G := G) i h₀ h₁)

end TauCeti
