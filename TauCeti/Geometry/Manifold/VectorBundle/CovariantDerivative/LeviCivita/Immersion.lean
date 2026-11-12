/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Levi-Civita connection of an isometric immersion

Let `f : M → F` be a `C²` map from a Riemannian manifold to a real inner product space whose
differential preserves inner products, `⟪v, w⟫ = ⟪df v, df w⟫`. For a vector field `Y` on `M`,
`df Y : y ↦ df_y (Y y)` is an `F`-valued function on `M`, and `D_X (df Y)` denotes its derivative
along a vector field `X`. The **Gauss formula** says that the Levi-Civita connection of `M` is the
tangential part of this ambient derivative:

`⟪∇_X Y, w⟫ = ⟪D_X (df Y), df w⟫` for every tangent vector `w`.

Equivalently, `df (∇_X Y)` is the orthogonal projection of `D_X (df Y)` onto the image of `df`.
This computes the connection of a submanifold of Euclidean space, such as the round sphere, from
ordinary derivatives in the ambient space.

The proof evaluates the Koszul formula: the derivative of `⟪Y, Z⟫ = ⟪df Y, df Z⟫` follows the
product rule `TauCeti.mvfderiv_inner_apply`, and `df [X, Y] = D_X (df Y) - D_Y (df X)` by
`mvfderiv_mlieBracket`.

## Main result

* `CovariantDerivative.IsLeviCivitaConnection.inner_apply_eq_inner_mvfderiv`: the Gauss formula.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 8.2 (the Gauss formula) and Theorem 5.10 (the Koszul formula).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 6, §2.
-/

public section

open Bundle FiberBundle Manifold VectorField
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : M → F} {x : M}

/-- **The Gauss formula.** If `f : M → F` is a `C²` map into a real inner product space whose
differential preserves inner products, then `⟪∇_X Y, w⟫ = ⟪D_X (df Y), df w⟫` for a Levi-Civita
connection `∇`: it is the tangential part of the ambient derivative of `df Y : y ↦ df_y (Y y)`. -/
theorem IsLeviCivitaConnection.inner_apply_eq_inner_mvfderiv (h : cov.IsLeviCivitaConnection)
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hg : ∀ y (v w : TangentSpace I y),
      inner ℝ v w = inner ℝ (mvfderiv I f y v) (mvfderiv I f y w))
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (w : TangentSpace I x) :
    inner ℝ (cov Y x (X x)) w =
      inner ℝ (mvfderiv I (fun y ↦ mvfderiv I f y (Y y)) x (X x)) (mvfderiv I f x w) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hn : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp [minSmoothness_of_isRCLikeNormedField]
  let Z : Π y : M, TangentSpace I y := extend E w
  have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend I E w
  -- `D U V` is the ambient derivative of `df V` along `U`, and `A U V W` the Koszul building block.
  let D : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) → F :=
    fun U V ↦ mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (U x)
  let A : (Π y : M, TangentSpace I y) → (Π y : M, TangentSpace I y) →
      (Π y : M, TangentSpace I y) → ℝ :=
    fun U V W ↦ inner ℝ (D U V) (mvfderiv I f x (W x))
  -- The product rule for the induced inner product of two fields.
  have hdiff {U V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
      (hW : MDiffAt (T% W) x) :
      mvfderiv I (fun y ↦ inner ℝ (V y) (W y)) x (U x) = A U V W + A U W V := by
    have heq : (fun y ↦ inner ℝ (V y) (W y)) =
        fun y ↦ inner ℝ (mvfderiv I f y (V y)) (mvfderiv I f y (W y)) :=
      funext fun y ↦ hg y (V y) (W y)
    rw [heq, TauCeti.mvfderiv_inner_apply (TauCeti.mdifferentiableAt_mvfderiv_apply hf hn hV)
      (TauCeti.mdifferentiableAt_mvfderiv_apply hf hn hW), real_inner_comm _ (mvfderiv I f x (V x))]
  -- The differential of the immersion carries brackets to commutators of ambient derivatives.
  have hbracket {U V W : Π y : M, TangentSpace I y} (hU : MDiffAt (T% U) x)
      (hV : MDiffAt (T% V) x) :
      inner ℝ (mlieBracket I U V x) (W x) = A U V W - A V U W := by
    rw [hg, mvfderiv_mlieBracket hf hn hU hV, inner_sub_left]
  have hk := h.two_inner_eq_koszul hX hY hZ
  rw [TauCeti.Manifold.koszul_apply, hdiff hY hZ, hdiff hZ hX, hdiff hX hY,
    hbracket hX hY, hbracket hX hZ, hbracket hY hZ] at hk
  have hw : Z x = w := by simp [Z]
  simp only [A, D, hw] at hk
  linarith

end CovariantDerivative
