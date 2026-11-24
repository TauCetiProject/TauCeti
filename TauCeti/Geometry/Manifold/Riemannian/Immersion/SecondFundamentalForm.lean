/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.NormalBundle
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Torsion

/-!
# The second fundamental form of an immersion into a Riemannian manifold

Let `f : M → N` be a map into a manifold whose tangent spaces carry a Riemannian metric, and let
`∇` be a covariant derivative on the tangent bundle of `N`. For vector fields `X` and `Y` on `M`,
`df Y : x ↦ df_x (Y x)` is a tangent field along `f`, and `∇_X (df Y)` denotes its covariant
derivative along `f` (`CovariantDerivative.alongMap`). The tangent space `T_{f x} N` splits
orthogonally into the range of `df_x` and the normal space `ν_x = (range df_x)ᗮ`
(`TauCeti.orthogonalNormalSpace`).

* The **second fundamental form** `TauCeti.immersionSecondFundamentalForm` is the normal part
  `B(X, Y) = (∇_X (df Y))^⊥`.
* The **shape operator** `TauCeti.immersionShapeOperator` of a field `ν` along `f` is the
  tangential part `S_ν X = -(∇_X ν)^⊤`, a vector of `range df_x ⊆ T_{f x} N`.
* The **normal connection** `TauCeti.immersionNormalConnection` is the normal part
  `∇^⊥_X ν = (∇_X ν)^⊥`.

These are the ambient-valued forms used for embedded submanifolds: the tangent part of a vector
of `T_{f x} N` is kept in `range df_x` rather than pulled back to `T_x M`. All three are defined
for every map `f`; the theorems carry the hypotheses they need.

The Gauss formula `∇_X (df Y) = (∇_X (df Y))^⊤ + B(X, Y)` is the orthogonal decomposition
(`TauCeti.starProjection_range_add_immersionSecondFundamentalForm`). The second fundamental form
is additive in `Y` and `C^∞(M)`-linear in it: the Leibniz term `(X g) df Y` is tangent, so the
normal projection removes it (`TauCeti.immersionSecondFundamentalForm_smul_right`). The normal
connection is additive in `ν` and satisfies the Leibniz rule on normal fields
(`TauCeti.immersionNormalConnection_smul`), and the shape operator is additive in `ν` and
`C^∞(M)`-linear on normal fields (`TauCeti.immersionShapeOperator_smul`). Both are
`C^∞(M)`-linear in `X`.

For a torsion-free `∇` and a `C²` map `f`, the second fundamental form is symmetric
(`TauCeti.immersionSecondFundamentalForm_comm`). This rests on the pulled-back torsion identity
`∇_X (df Y) - ∇_Y (df X) = df [X, Y]`
(`CovariantDerivative.alongMap_mfderiv_sub_alongMap_mfderiv`), which is tangent.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 7–8
  (curvature and submanifolds), the convention reference of the RiemannianGeometry roadmap.
-/

public section

open Bundle Manifold Module Set Filter VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J 2 N]
  (cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)) (f : M → N)

section Definitions

/-- The **second fundamental form** `B(X, Y) = (∇_X (df Y))^⊥` of a map `f : M → N` at `x`: the
normal part of the covariant derivative along `f`, in the direction `X x`, of the tangent field
`df Y : y ↦ df_y (Y y)` along `f`. -/
noncomputable def immersionSecondFundamentalForm (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace J (f x) :=
  (orthogonalNormalSpace I J f x).starProjection
    (cov.alongMap I f (fun y ↦ mfderiv I J f y (Y y)) x (X x))

/-- The **shape operator** `S_ν X = -(∇_X ν)^⊤` of a map `f : M → N` at `x`, for a tangent field
`ν` along `f`: minus the tangential part, in `range df_x`, of the covariant derivative of `ν` along
`f` in the direction `X x`. -/
noncomputable def immersionShapeOperator (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) : TangentSpace J (f x) :=
  -(LinearMap.range (mfderiv I J f x).toLinearMap).starProjection (cov.alongMap I f ν x (X x))

/-- The **normal connection** `∇^⊥_X ν = (∇_X ν)^⊥` of a map `f : M → N` at `x`: the normal part
of the covariant derivative of a field `ν` along `f` in the direction `X x`. -/
noncomputable def immersionNormalConnection (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) : TangentSpace J (f x) :=
  (orthogonalNormalSpace I J f x).starProjection (cov.alongMap I f ν x (X x))

/-- The second fundamental form is the normal part of the covariant derivative of `df Y`. -/
theorem immersionSecondFundamentalForm_def (X Y : Π x : M, TangentSpace I x) (x : M) :
    immersionSecondFundamentalForm cov f X Y x =
      (orthogonalNormalSpace I J f x).starProjection
        (cov.alongMap I f (fun y ↦ mfderiv I J f y (Y y)) x (X x)) :=
  (rfl)

/-- The shape operator is minus the tangential part of the covariant derivative of `ν`. -/
theorem immersionShapeOperator_def (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) :
    immersionShapeOperator cov f ν X x =
      -(LinearMap.range (mfderiv I J f x).toLinearMap).starProjection
        (cov.alongMap I f ν x (X x)) :=
  (rfl)

/-- The normal connection is the normal part of the covariant derivative of `ν`. -/
theorem immersionNormalConnection_def (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) :
    immersionNormalConnection cov f ν X x =
      (orthogonalNormalSpace I J f x).starProjection (cov.alongMap I f ν x (X x)) :=
  (rfl)

end Definitions

section Basic

variable {cov f}

/-- The second fundamental form takes values in the normal space. -/
theorem immersionSecondFundamentalForm_mem (X Y : Π x : M, TangentSpace I x) (x : M) :
    immersionSecondFundamentalForm cov f X Y x ∈ orthogonalNormalSpace I J f x :=
  Submodule.starProjection_apply_mem _ _

/-- **The Gauss formula.** The covariant derivative of `df Y` along `f` is the sum of its
tangential part and the second fundamental form. -/
theorem starProjection_range_add_immersionSecondFundamentalForm
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    (LinearMap.range (mfderiv I J f x).toLinearMap).starProjection
        (cov.alongMap I f (fun y ↦ mfderiv I J f y (Y y)) x (X x)) +
      immersionSecondFundamentalForm cov f X Y x =
        cov.alongMap I f (fun y ↦ mfderiv I J f y (Y y)) x (X x) := by
  rw [immersionSecondFundamentalForm_def, starProjection_orthogonalNormalSpace]
  exact Submodule.starProjection_add_starProjection_orthogonal _

/-- The second fundamental form pairs with a normal vector like the covariant derivative of
`df Y`. -/
theorem inner_immersionSecondFundamentalForm_of_mem (X Y : Π x : M, TangentSpace I x) {x : M}
    {w : TangentSpace J (f x)} (hw : w ∈ orthogonalNormalSpace I J f x) :
    inner ℝ (immersionSecondFundamentalForm cov f X Y x) w =
      inner ℝ (cov.alongMap I f (fun y ↦ mfderiv I J f y (Y y)) x (X x)) w := by
  rw [immersionSecondFundamentalForm_def, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 hw]

/-- The second fundamental form is linear in its first argument, which enters only through its
value at the point. -/
@[simp]
theorem immersionSecondFundamentalForm_add_left (X X' Y : Π x : M, TangentSpace I x) (x : M) :
    immersionSecondFundamentalForm cov f (X + X') Y x =
      immersionSecondFundamentalForm cov f X Y x +
        immersionSecondFundamentalForm cov f X' Y x := by
  simp only [immersionSecondFundamentalForm_def, Pi.add_apply, map_add]

/-- The second fundamental form is `C^∞(M)`-linear in its first argument. -/
@[simp]
theorem immersionSecondFundamentalForm_smul_left (g : M → ℝ) (X Y : Π x : M, TangentSpace I x)
    (x : M) :
    immersionSecondFundamentalForm cov f (g • X) Y x =
      g x • immersionSecondFundamentalForm cov f X Y x := by
  simp only [immersionSecondFundamentalForm_def, Pi.smul_apply', map_smul]

/-- The second fundamental form is additive in its second argument, for fields whose images
under `df` are differentiable in the chart at `f x`. -/
theorem immersionSecondFundamentalForm_add_right (X Y Y' : Π x : M, TangentSpace I x) {x : M}
    (hY : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (Y y)) (f x)) x)
    (hY' : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (Y' y)) (f x)) x) :
    immersionSecondFundamentalForm cov f X (Y + Y') x =
      immersionSecondFundamentalForm cov f X Y x +
        immersionSecondFundamentalForm cov f X Y' x := by
  have h : (fun y ↦ mfderiv I J f y ((Y + Y') y)) =
      (fun y ↦ mfderiv I J f y (Y y)) + fun y ↦ mfderiv I J f y (Y' y) :=
    funext fun y ↦ map_add _ _ _
  simp only [immersionSecondFundamentalForm_def, h, cov.alongMap_add f _ _ hY hY',
    add_apply, map_add]

/-- **The second fundamental form is `C^∞(M)`-linear in its second argument.** The Leibniz term
`(X g) df Y` of `∇_X (df (g Y))` is tangent, so the normal projection removes it. -/
theorem immersionSecondFundamentalForm_smul_right (X Y : Π x : M, TangentSpace I x) {x : M}
    (g : M → ℝ) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x)
    (hY : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (Y y)) (f x)) x) :
    immersionSecondFundamentalForm cov f X (g • Y) x =
      g x • immersionSecondFundamentalForm cov f X Y x := by
  have h : (fun y ↦ mfderiv I J f y ((g • Y) y)) = g • fun y ↦ mfderiv I J f y (Y y) :=
    funext fun y ↦ map_smul _ _ _
  simp only [immersionSecondFundamentalForm_def, h, cov.alongMap_smul f _ g hg hY,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    starProjection_orthogonalNormalSpace_mfderiv, smul_zero, add_zero]

/-- The normal connection takes values in the normal space. -/
theorem immersionNormalConnection_mem (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) :
    immersionNormalConnection cov f ν X x ∈ orthogonalNormalSpace I J f x :=
  Submodule.starProjection_apply_mem _ _

/-- The shape operator takes values in the range of the differential. -/
theorem immersionShapeOperator_mem (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) :
    immersionShapeOperator cov f ν X x ∈ LinearMap.range (mfderiv I J f x).toLinearMap :=
  Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ _)

/-- **The Weingarten decomposition.** The covariant derivative of a field `ν` along `f` is the sum
of minus the shape operator and the normal connection. -/
theorem neg_immersionShapeOperator_add_immersionNormalConnection (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) (x : M) :
    -immersionShapeOperator cov f ν X x + immersionNormalConnection cov f ν X x =
      cov.alongMap I f ν x (X x) := by
  rw [immersionShapeOperator_def, neg_neg, immersionNormalConnection_def,
    starProjection_orthogonalNormalSpace]
  exact Submodule.starProjection_add_starProjection_orthogonal _

/-- The shape operator is additive in its direction argument, which enters only through its value
at the point. -/
@[simp]
theorem immersionShapeOperator_add_right (ν : Π x : M, TangentSpace J (f x))
    (X X' : Π x : M, TangentSpace I x) (x : M) :
    immersionShapeOperator cov f ν (X + X') x =
      immersionShapeOperator cov f ν X x + immersionShapeOperator cov f ν X' x := by
  simp only [immersionShapeOperator_def, Pi.add_apply, map_add, neg_add]

/-- The shape operator is `C^∞(M)`-linear in its direction argument. -/
@[simp]
theorem immersionShapeOperator_smul_right (ν : Π x : M, TangentSpace J (f x)) (g : M → ℝ)
    (X : Π x : M, TangentSpace I x) (x : M) :
    immersionShapeOperator cov f ν (g • X) x = g x • immersionShapeOperator cov f ν X x := by
  simp only [immersionShapeOperator_def, Pi.smul_apply', map_smul, smul_neg]

/-- The normal connection is additive in its direction argument, which enters only through its
value at the point. -/
@[simp]
theorem immersionNormalConnection_add_right (ν : Π x : M, TangentSpace J (f x))
    (X X' : Π x : M, TangentSpace I x) (x : M) :
    immersionNormalConnection cov f ν (X + X') x =
      immersionNormalConnection cov f ν X x + immersionNormalConnection cov f ν X' x := by
  simp only [immersionNormalConnection_def, Pi.add_apply, map_add]

/-- The normal connection is `C^∞(M)`-linear in its direction argument. -/
@[simp]
theorem immersionNormalConnection_smul_right (ν : Π x : M, TangentSpace J (f x)) (g : M → ℝ)
    (X : Π x : M, TangentSpace I x) (x : M) :
    immersionNormalConnection cov f ν (g • X) x = g x • immersionNormalConnection cov f ν X x := by
  simp only [immersionNormalConnection_def, Pi.smul_apply', map_smul]

/-- The shape operator is additive in fields along `f` with differentiable readings in the chart
at `f x`. -/
theorem immersionShapeOperator_add (ν ν' : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) {x : M}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hν' : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν' (f x)) x) :
    immersionShapeOperator cov f (ν + ν') X x =
      immersionShapeOperator cov f ν X x + immersionShapeOperator cov f ν' X x := by
  simp only [immersionShapeOperator_def, cov.alongMap_add f _ _ hν hν', add_apply, map_add,
    neg_add]

/-- The normal connection is additive in fields along `f` with differentiable readings in the
chart at `f x`. -/
theorem immersionNormalConnection_add (ν ν' : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) {x : M}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hν' : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν' (f x)) x) :
    immersionNormalConnection cov f (ν + ν') X x =
      immersionNormalConnection cov f ν X x + immersionNormalConnection cov f ν' X x := by
  simp only [immersionNormalConnection_def, cov.alongMap_add f _ _ hν hν', add_apply, map_add]

/-- **The Leibniz rule for the normal connection.** For a normal field `ν` at `x`,
`∇^⊥_X (g ν) = g ∇^⊥_X ν + (X g) ν`. -/
theorem immersionNormalConnection_smul (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) {x : M} (g : M → ℝ) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x)
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνx : ν x ∈ orthogonalNormalSpace I J f x) :
    immersionNormalConnection cov f (g • ν) X x =
      g x • immersionNormalConnection cov f ν X x + mvfderiv I g x (X x) • ν x := by
  simp only [immersionNormalConnection_def, cov.alongMap_smul f ν g hg hν, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    Submodule.starProjection_eq_self_iff.2 hνx]

/-- **The shape operator is `C^∞(M)`-linear on normal fields.** For a normal field `ν` at `x`,
`S_{g ν} X = g S_ν X`: the Leibniz term `(X g) ν` is normal, so the tangential projection removes
it. -/
theorem immersionShapeOperator_smul (ν : Π x : M, TangentSpace J (f x))
    (X : Π x : M, TangentSpace I x) {x : M} (g : M → ℝ) (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x)
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνx : ν x ∈ orthogonalNormalSpace I J f x) :
    immersionShapeOperator cov f (g • ν) X x = g x • immersionShapeOperator cov f ν X x := by
  have h0 : (LinearMap.range (mfderiv I J f x).toLinearMap).starProjection (ν x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2 (by rwa [orthogonalNormalSpace_def] at hνx)
  simp only [immersionShapeOperator_def, cov.alongMap_smul f ν g hg hν,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, h0, smul_zero, add_zero, smul_neg]

end Basic

section Symmetry

variable {cov f}

/-- **The second fundamental form of a torsion-free connection is symmetric.** For a map `f`
which is `C²` at `x` and vector fields `X`, `Y` differentiable at `x`, `B(X, Y) = B(Y, X)` at `x`:
the difference `∇_X (df Y) - ∇_Y (df X) = df [X, Y]` is tangent. This applies to the Levi-Civita
connection of `N`. -/
theorem immersionSecondFundamentalForm_comm [CompleteSpace E] [IsManifold I 2 M]
    (ht : cov.IsTorsionFree) {x : M} (hf : ContMDiffAt I J 2 f x) {X Y : Π x : M, TangentSpace I x}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x) :
    immersionSecondFundamentalForm cov f X Y x = immersionSecondFundamentalForm cov f Y X x := by
  rw [← sub_eq_zero, immersionSecondFundamentalForm_def, immersionSecondFundamentalForm_def,
    ← map_sub, cov.alongMap_mfderiv_sub_alongMap_mfderiv ht hf hX hY,
    starProjection_orthogonalNormalSpace_mfderiv]

end Symmetry

end TauCeti
