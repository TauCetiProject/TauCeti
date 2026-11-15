/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The Levi-Civita connection of a warped product

Let `M × N` carry the warped product `⟪(u₁, u₂), (v₁, v₂)⟫ = ⟪u₁, v₁⟫ + f(x)² ⟪u₂, v₂⟫` of the
Riemannian metrics of `M` and `N` (`TauCeti.Manifold.IsWarpedProduct`). Its Levi-Civita connection
on a product vector field `(Y₁, Y₂)`, in the direction `(u₁, u₂)` at `(x, y)`, is

`∇_(u₁, u₂) (Y₁, Y₂) = (∇_u₁ Y₁ - f ⟪u₂, Y₂⟫ grad f, ∇_u₂ Y₂ + (df(u₁) / f) Y₂ + (df(Y₁) / f) u₂)`,

where `f`, `df` and `grad f` are evaluated at `x`, and `⟪u₂, Y₂⟫` is the inner product of `N`.
Splitting into horizontal fields `X, Y` (tangent to `M`) and vertical fields `V, W` (tangent to
`N`), this is the classical description of Bishop and O'Neill:

* `∇_X Y` is the horizontal lift of the Levi-Civita connection of `M`;
* `∇_X V = ∇_V X = (X f / f) V`;
* `∇_V W` is the Levi-Civita connection of `N` minus `(⟪V, W⟫_warped / f) grad f`.

Read off from these formulas, the slices `M × {y}` are totally geodesic, while the fibres
`{x} × N` are totally umbilic, with second fundamental form `-(⟪V, W⟫_warped / f) grad f`; these
consequences are not stated separately here. For `f = 1` the formula is the Levi-Civita
connection of the product metric (`TauCeti.Manifold.leviCivitaConnection_prodVectorField`).

As for products, the proof evaluates the Koszul formula on product fields. The inner product of
two product fields is now `a(x) + f(x)² b(y)`, whose derivative contributes the extra terms
`2 f df(·) b`.

The formula needs no nonvanishing hypothesis on `f` at the point considered: where `f(x) = 0`
the warped metric can only be nondegenerate if `N` is zero-dimensional, and the correction terms
with `1 / f` vanish with the convention `a / 0 = 0`.

## Main results

* `TauCeti.Manifold.IsWarpedProduct.koszul_prodVectorField`: the Koszul expression of a warped
  product on product fields.
* `TauCeti.Manifold.IsWarpedProduct.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField`:
  the Levi-Civita connection of a warped product on product fields, in any direction.
* `TauCeti.Manifold.IsWarpedProduct.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField_zero`
  : its restriction to horizontal fields.

## References

* R. L. Bishop and B. O'Neill, *Manifolds of negative curvature*, Trans. Amer. Math. Soc. 145
  (1969), 1–49, Section 7.
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Proposition 35.
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold

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
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  {f : M → ℝ} {X₁ Y₁ Z₁ : Π x : M, TangentSpace I x} {X₂ Y₂ Z₂ : Π y : N, TangentSpace J y}
  {p : M × N}

omit [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [IsManifold J 2 N] [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)] in
/-- In a warped product, the inner product of two product fields is `a(x) + f(x)² b(y)`. -/
private theorem IsWarpedProduct.inner_prodVectorField_eq (h : IsWarpedProduct I J N f)
    (Y₁ Z₁ : Π x : M, TangentSpace I x) (Y₂ Z₂ : Π y : N, TangentSpace J y) :
    (fun q : M × N ↦ inner ℝ (prodVectorField Y₁ Y₂ q) (prodVectorField Z₁ Z₂ q)) =
      (fun x ↦ inner ℝ (Y₁ x) (Z₁ x)) ∘ Prod.fst +
        ((fun x ↦ f x ^ 2) ∘ Prod.fst) * ((fun y ↦ inner ℝ (Y₂ y) (Z₂ y)) ∘ Prod.snd) :=
  funext fun q ↦ by
    rw [h.inner_eq, tangentSpaceProdEquiv_prodVectorField, tangentSpaceProdEquiv_prodVectorField,
      Pi.add_apply, Pi.mul_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- In a warped product, the derivative of the inner product of two product fields along a third. -/
private theorem IsWarpedProduct.mvfderiv_inner_prodVectorField (h : IsWarpedProduct I J N f)
    (hf : MDiffAt f p.1) (hY₁ : MDiffAt (T% Y₁) p.1) (hZ₁ : MDiffAt (T% Z₁) p.1)
    (hY₂ : MDiffAt (T% Y₂) p.2) (hZ₂ : MDiffAt (T% Z₂) p.2) :
    mvfderiv (I.prod J) (fun q ↦ inner ℝ (prodVectorField Y₁ Y₂ q) (prodVectorField Z₁ Z₂ q)) p
        (prodVectorField X₁ X₂ p) =
      mvfderiv I (fun x ↦ inner ℝ (Y₁ x) (Z₁ x)) p.1 (X₁ p.1) +
        2 * f p.1 * mvfderiv I f p.1 (X₁ p.1) * inner ℝ (Y₂ p.2) (Z₂ p.2) +
        f p.1 ^ 2 * mvfderiv J (fun y ↦ inner ℝ (Y₂ y) (Z₂ y)) p.2 (X₂ p.2) := by
  have h₁ : MDifferentiableAt (I.prod J) 𝓘(ℝ) ((fun x ↦ inner ℝ (Y₁ x) (Z₁ x)) ∘ Prod.fst) p :=
    (mdifferentiableAt_inner hY₁ hZ₁).comp p mdifferentiableAt_fst
  have hf₂ : MDifferentiableAt (I.prod J) 𝓘(ℝ) ((fun x ↦ f x ^ 2) ∘ Prod.fst) p :=
    (hf.pow 2).comp p mdifferentiableAt_fst
  have h₂ : MDifferentiableAt (I.prod J) 𝓘(ℝ) ((fun y ↦ inner ℝ (Y₂ y) (Z₂ y)) ∘ Prod.snd) p :=
    (mdifferentiableAt_inner hY₂ hZ₂).comp p mdifferentiableAt_snd
  have hsq : mvfderiv I (fun x ↦ f x ^ 2) p.1 (X₁ p.1) = 2 * f p.1 * mvfderiv I f p.1 (X₁ p.1) := by
    simp only [pow_two, mvfderiv_fun_mul hf hf, add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [h.inner_prodVectorField_eq, mvfderiv_add h₁ (hf₂.mul h₂), mvfderiv_mul hf₂ h₂]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mvfderiv_comp_fst_apply,
    mvfderiv_comp_snd_apply, prodVectorField_fst, prodVectorField_snd, Function.comp_apply, hsq]
  ring

/-- On product fields, the Koszul expression of a warped product with warping function `f` is
`K₁ + f² K₂ + 2 f (df(X₁) ⟪Y₂, Z₂⟫ + df(Y₁) ⟪Z₂, X₂⟫ - df(Z₁) ⟪X₂, Y₂⟫)`, where `K₁` and `K₂` are
the Koszul expressions of the factors. -/
theorem IsWarpedProduct.koszul_prodVectorField (h : IsWarpedProduct I J N f)
    (hf : MDiffAt f p.1) (hX₁ : MDiffAt (T% X₁) p.1) (hY₁ : MDiffAt (T% Y₁) p.1)
    (hZ₁ : MDiffAt (T% Z₁) p.1) (hX₂ : MDiffAt (T% X₂) p.2) (hY₂ : MDiffAt (T% Y₂) p.2)
    (hZ₂ : MDiffAt (T% Z₂) p.2) :
    koszul (I.prod J) (prodVectorField X₁ X₂) (prodVectorField Y₁ Y₂) (prodVectorField Z₁ Z₂) p =
      koszul I X₁ Y₁ Z₁ p.1 + f p.1 ^ 2 * koszul J X₂ Y₂ Z₂ p.2 +
        2 * f p.1 * (mvfderiv I f p.1 (X₁ p.1) * inner ℝ (Y₂ p.2) (Z₂ p.2) +
          mvfderiv I f p.1 (Y₁ p.1) * inner ℝ (Z₂ p.2) (X₂ p.2) -
          mvfderiv I f p.1 (Z₁ p.1) * inner ℝ (X₂ p.2) (Y₂ p.2)) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have : IsManifold J (minSmoothness ℝ 2) N := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  rw [koszul_apply, koszul_apply, koszul_apply,
    h.mvfderiv_inner_prodVectorField hf hY₁ hZ₁ hY₂ hZ₂,
    h.mvfderiv_inner_prodVectorField hf hZ₁ hX₁ hZ₂ hX₂,
    h.mvfderiv_inner_prodVectorField hf hX₁ hY₁ hX₂ hY₂,
    mlieBracket_prodVectorField hX₁ hY₁ hX₂ hY₂, mlieBracket_prodVectorField hX₁ hZ₁ hX₂ hZ₂,
    mlieBracket_prodVectorField hY₁ hZ₁ hY₂ hZ₂]
  simp only [h.inner_eq, tangentSpaceProdEquiv_prodVectorField]
  ring

/-- **The Levi-Civita connection of a warped product** with warping function `f`, on a product
field `(Y₁, Y₂)` in the direction `v = (u₁, u₂)` at `p = (x, y)`:

`∇_v (Y₁, Y₂) = (∇_u₁ Y₁ - f(x) ⟪u₂, Y₂ y⟫ grad f(x),`
`  ∇_u₂ Y₂ + (df_x(u₁) / f(x)) Y₂ y + (df_x(Y₁ x) / f(x)) u₂)`. -/
theorem IsWarpedProduct.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField
    [IsContMDiffRiemannianBundle (I.prod J) 1 (E × F) (fun p : M × N ↦ TangentSpace (I.prod J) p)]
    (h : IsWarpedProduct I J N f) (hf : MDiffAt f p.1) (hY₁ : MDiffAt (T% Y₁) p.1)
    (hY₂ : MDiffAt (T% Y₂) p.2) (v : TangentSpace (I.prod J) p) :
    tangentSpaceProdEquiv p (leviCivitaConnection (I.prod J) (M × N) (prodVectorField Y₁ Y₂) p v) =
      (leviCivitaConnection I M Y₁ p.1 (tangentSpaceProdEquiv p v).1 -
          (f p.1 * inner ℝ (tangentSpaceProdEquiv p v).2 (Y₂ p.2)) • mgradient I f p.1,
        leviCivitaConnection J N Y₂ p.2 (tangentSpaceProdEquiv p v).2 +
          (mvfderiv I f p.1 (tangentSpaceProdEquiv p v).1 / f p.1) • Y₂ p.2 +
          (mvfderiv I f p.1 (Y₁ p.1) / f p.1) • (tangentSpaceProdEquiv p v).2) := by
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
  -- The Koszul formula determines the connection, and on these product fields the Koszul
  -- expression of the warped product is that of the factors plus the derivatives of `f`.
  have hkoszul := two_inner_leviCivitaConnection_eq_koszul (I := I.prod J) (M := M × N)
    (mdifferentiableAt_prodVectorField hX₁ hX₂) (mdifferentiableAt_prodVectorField hY₁ hY₂)
    (mdifferentiableAt_prodVectorField hZ₁ hZ₂)
  rw [h.koszul_prodVectorField hf hX₁ hY₁ hZ₁ hX₂ hY₂ hZ₂,
    ← two_inner_leviCivitaConnection_eq_koszul hX₁ hY₁ hZ₁,
    ← two_inner_leviCivitaConnection_eq_koszul hX₂ hY₂ hZ₂, hXp, hZp, extend_apply_self,
    extend_apply_self, extend_apply_self, extend_apply_self] at hkoszul
  rw [e.symm_apply_apply, h.inner_eq p (e.symm _) w, e.apply_symm_apply]
  simp only [inner_sub_left, inner_add_left, inner_smul_left, inner_mgradient,
    RCLike.conj_to_real] at hkoszul ⊢
  -- `f² ((a / f) b) = f a b` holds for every real `f`, including `f = 0`.
  have hdiv (a b : ℝ) : f p.1 ^ 2 * (a / f p.1 * b) = f p.1 * a * b := by
    rcases eq_or_ne (f p.1) 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [real_inner_comm (e v).2 (e w).2] at hkoszul
  simp only [mul_add, hdiv]
  linear_combination hkoszul / 2

/-- On a horizontal section `W`, the Levi-Civita connection of the warped product differs from
the base connection only by the factor `W f / f` on the vertical component. -/
theorem IsWarpedProduct.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField_zero
    [IsContMDiffRiemannianBundle (I.prod J) 1 (E × F) (fun p : M × N ↦ TangentSpace (I.prod J) p)]
    (h : IsWarpedProduct I J N f) {W : Π x : M, TangentSpace I x}
    (hf : MDiffAt f p.1) (hW : MDiffAt (T% W) p.1) (u : TangentSpace (I.prod J) p) :
    tangentSpaceProdEquiv p
        ((leviCivitaConnection (I.prod J) (M × N)) (prodVectorField W 0) p u) =
      (leviCivitaConnection I M W p.1 (tangentSpaceProdEquiv p u).1,
        (mvfderiv I f p.1 (W p.1) / f p.1) • (tangentSpaceProdEquiv p u).2) := by
  have h0N : MDiffAt (T% (0 : Π y : N, TangentSpace J y)) p.2 :=
    (contMDiff_zeroSection ℝ (TangentSpace J)).mdifferentiableAt one_ne_zero
  simpa [(leviCivitaConnection J N).isCovariantDerivativeOnUniv.zero] using
    h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hf hW h0N u

end TauCeti.Manifold
