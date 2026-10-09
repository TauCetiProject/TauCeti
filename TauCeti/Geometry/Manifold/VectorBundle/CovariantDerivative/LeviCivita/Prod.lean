/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The Levi-Civita connection of a product metric

Give `M × N` the product of Riemannian metrics on `M` and `N`. Its Levi-Civita connection
differentiates a product vector field `(Y₁, Y₂)` factor by factor:

`∇_(u, v) (Y₁, Y₂) = (∇_u Y₁, ∇_v Y₂)`.

This is the input for the curvature of a product, which is the product of the curvatures of the
factors (`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod`).

The proof goes through the Koszul formula: on product fields the Koszul expression of the product
metric is the sum of the Koszul expressions of the factors
(`TauCeti.Manifold.koszul_prodVectorField`), because the inner product of product fields is a sum of
functions of one factor each and the Lie bracket of product fields is computed factor by factor
(`TauCeti.Manifold.mlieBracket_prodVectorField`). Every tangent vector of `M × N` is the value of a
product field, so the Koszul formula determines the connection.

## Main results

* `TauCeti.Manifold.koszul_prodVectorField`: the Koszul expression of the product metric on product
  fields.
* `TauCeti.Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField`: the Levi-Civita
  connection of the product metric on product fields, in any direction.
* `TauCeti.Manifold.leviCivitaConnection_prodVectorField`: the same along a product field, as an
  identity of product fields.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5
  (the Koszul formula, Theorem 5.10).
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7 (the connection of a
  warped product, of which a product metric is the case of a constant warping function).
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold TauCeti

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {X₁ Y₁ Z₁ : Π x : M, TangentSpace I x} {X₂ Y₂ Z₂ : Π y : N, TangentSpace J y} {p : M × N}

omit [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [IsManifold J 2 N] [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- The inner product of two product fields is the sum of a function of the first factor and a
function of the second. -/
private theorem inner_prodVectorField_eq (Y₁ Z₁ : Π x : M, TangentSpace I x)
    (Y₂ Z₂ : Π y : N, TangentSpace J y) :
    (fun q : M × N ↦ inner ℝ (prodVectorField Y₁ Y₂ q) (prodVectorField Z₁ Z₂ q)) =
      (fun x ↦ inner ℝ (Y₁ x) (Z₁ x)) ∘ Prod.fst + (fun y ↦ inner ℝ (Y₂ y) (Z₂ y)) ∘ Prod.snd :=
  funext fun q ↦ by
    rw [inner_tangentSpace_prod, tangentSpaceProdEquiv_prodVectorField,
      tangentSpaceProdEquiv_prodVectorField, Pi.add_apply, Function.comp_apply,
      Function.comp_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The derivative of the inner product of two product fields along a third. -/
private theorem mvfderiv_inner_prodVectorField (hY₁ : MDiffAt (T% Y₁) p.1)
    (hZ₁ : MDiffAt (T% Z₁) p.1) (hY₂ : MDiffAt (T% Y₂) p.2) (hZ₂ : MDiffAt (T% Z₂) p.2) :
    mvfderiv (I.prod J) (fun q ↦ inner ℝ (prodVectorField Y₁ Y₂ q) (prodVectorField Z₁ Z₂ q)) p
        (prodVectorField X₁ X₂ p) =
      mvfderiv I (fun x ↦ inner ℝ (Y₁ x) (Z₁ x)) p.1 (X₁ p.1) +
        mvfderiv J (fun y ↦ inner ℝ (Y₂ y) (Z₂ y)) p.2 (X₂ p.2) := by
  have h₁ : MDifferentiableAt (I.prod J) 𝓘(ℝ) ((fun x ↦ inner ℝ (Y₁ x) (Z₁ x)) ∘ Prod.fst) p :=
    (mdifferentiableAt_inner hY₁ hZ₁).comp p mdifferentiableAt_fst
  have h₂ : MDifferentiableAt (I.prod J) 𝓘(ℝ) ((fun y ↦ inner ℝ (Y₂ y) (Z₂ y)) ∘ Prod.snd) p :=
    (mdifferentiableAt_inner hY₂ hZ₂).comp p mdifferentiableAt_snd
  rw [inner_prodVectorField_eq, mvfderiv_add h₁ h₂, add_apply, mvfderiv_comp_fst_apply,
    mvfderiv_comp_snd_apply, prodVectorField_fst, prodVectorField_snd]

/-- On product fields, the Koszul expression of the product metric is the sum of the Koszul
expressions of the factors. -/
theorem koszul_prodVectorField (hX₁ : MDiffAt (T% X₁) p.1) (hY₁ : MDiffAt (T% Y₁) p.1)
    (hZ₁ : MDiffAt (T% Z₁) p.1) (hX₂ : MDiffAt (T% X₂) p.2) (hY₂ : MDiffAt (T% Y₂) p.2)
    (hZ₂ : MDiffAt (T% Z₂) p.2) :
    koszul (I.prod J) (prodVectorField X₁ X₂) (prodVectorField Y₁ Y₂) (prodVectorField Z₁ Z₂) p =
      koszul I X₁ Y₁ Z₁ p.1 + koszul J X₂ Y₂ Z₂ p.2 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have : IsManifold J (minSmoothness ℝ 2) N := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  rw [koszul_apply, koszul_apply, koszul_apply, mvfderiv_inner_prodVectorField hY₁ hZ₁ hY₂ hZ₂,
    mvfderiv_inner_prodVectorField hZ₁ hX₁ hZ₂ hX₂, mvfderiv_inner_prodVectorField hX₁ hY₁ hX₂ hY₂,
    mlieBracket_prodVectorField hX₁ hY₁ hX₂ hY₂, mlieBracket_prodVectorField hX₁ hZ₁ hX₂ hZ₂,
    mlieBracket_prodVectorField hY₁ hZ₁ hY₂ hZ₂]
  simp only [inner_tangentSpace_prod, tangentSpaceProdEquiv_prodVectorField]
  ring

/-- **The Levi-Civita connection of a product metric** differentiates a product field factor by
factor: `∇_(u, v) (Y₁, Y₂) = (∇_u Y₁, ∇_v Y₂)`. -/
theorem tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (hY₁ : MDiffAt (T% Y₁) p.1)
    (hY₂ : MDiffAt (T% Y₂) p.2) (v : TangentSpace (I.prod J) p) :
    tangentSpaceProdEquiv p (leviCivitaConnection (I.prod J) (M × N) (prodVectorField Y₁ Y₂) p v) =
      (leviCivitaConnection I M Y₁ p.1 (tangentSpaceProdEquiv p v).1,
        leviCivitaConnection J N Y₂ p.2 (tangentSpaceProdEquiv p v).2) := by
  set e := tangentSpaceProdEquiv (I := I) (J := J) p
  -- Realise `v` and a test vector `w` as values at `p` of differentiable product fields.
  have hX₁ := mdifferentiableAt_extend I E (V := TangentSpace I) (e v).1
  have hX₂ := mdifferentiableAt_extend J F (V := TangentSpace J) (e v).2
  have hXp : prodVectorField (extend E (e v).1 : Π x : M, TangentSpace I x)
      (extend F (e v).2 : Π y : N, TangentSpace J y) p = v := by
    apply e.injective
    rw [tangentSpaceProdEquiv_prodVectorField, extend_apply_self, extend_apply_self]
  apply e.symm.injective
  apply ext_inner_right ℝ
  intro w
  have hZ₁ := mdifferentiableAt_extend I E (V := TangentSpace I) (e w).1
  have hZ₂ := mdifferentiableAt_extend J F (V := TangentSpace J) (e w).2
  have hZp : prodVectorField (extend E (e w).1 : Π x : M, TangentSpace I x)
      (extend F (e w).2 : Π y : N, TangentSpace J y) p = w := by
    apply e.injective
    rw [tangentSpaceProdEquiv_prodVectorField, extend_apply_self, extend_apply_self]
  -- Compare the Koszul formulas of the product and of the factors on these fields.
  have hkoszul := two_inner_leviCivitaConnection_eq_koszul (I := I.prod J) (M := M × N)
    (mdifferentiableAt_prodVectorField hX₁ hX₂) (mdifferentiableAt_prodVectorField hY₁ hY₂)
    (mdifferentiableAt_prodVectorField hZ₁ hZ₂)
  rw [koszul_prodVectorField hX₁ hY₁ hZ₁ hX₂ hY₂ hZ₂,
    ← two_inner_leviCivitaConnection_eq_koszul hX₁ hY₁ hZ₁,
    ← two_inner_leviCivitaConnection_eq_koszul hX₂ hY₂ hZ₂, hXp, hZp, extend_apply_self,
    extend_apply_self, extend_apply_self, extend_apply_self] at hkoszul
  rw [e.symm_apply_apply, inner_tangentSpace_prod (v := e.symm _), e.apply_symm_apply]
  linarith

/-- The Levi-Civita connection of a product metric, differentiating a product field along another:
`∇_(X₁, X₂) (Y₁, Y₂) = (∇_X₁ Y₁, ∇_X₂ Y₂)`. -/
theorem leviCivitaConnection_prodVectorField (hY₁ : MDiffAt (T% Y₁) p.1)
    (hY₂ : MDiffAt (T% Y₂) p.2) :
    leviCivitaConnection (I.prod J) (M × N) (prodVectorField Y₁ Y₂) p (prodVectorField X₁ X₂ p) =
      prodVectorField (fun x ↦ leviCivitaConnection I M Y₁ x (X₁ x))
        (fun y ↦ leviCivitaConnection J N Y₂ y (X₂ y)) p := by
  apply (tangentSpaceProdEquiv p).injective
  rw [tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ hY₂,
    tangentSpaceProdEquiv_prodVectorField, tangentSpaceProdEquiv_prodVectorField]

end TauCeti.Manifold
