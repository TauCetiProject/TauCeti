/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic

/-!
# The Levi-Civita connection under Riemannian isometries

A smooth Riemannian isometry `Φ : M → N` transports the Levi-Civita connection of `N` to that of
`M`: for a vector field `Y` on `N`, differentiable at `Φ x`, and a tangent vector `v` at `x`,

`dΦ_x (∇ᴹ_v (Φ^* Y)) = ∇ᴺ_{dΦ_x v} Y`,

where `Φ^* Y = VectorField.mpullback I J Φ Y` is the pullback vector field
`x ↦ (dΦ_x)⁻¹ (Y (Φ x))`. Equivalently, the connection on `M` obtained by transporting `∇ᴺ`
along `Φ` agrees with `∇ᴹ` on differentiable vector fields.

This is the connection-level input for transporting geodesics, their maximal intervals, and
exponential maps along Riemannian isometries.

## Main results

In the namespace `TauCeti.RiemannianIsometry`:

* `inner_mpullback`: pulling back along a Riemannian isometry preserves pointwise inner products
  of vector fields.
* `koszul_mpullback`: the Koszul expression is natural under Riemannian isometries.
* `mfderiv_apply_mpullback_of_isLeviCivitaConnection`: **naturality of Levi-Civita
  connections** under Riemannian isometries.
* `mfderiv_leviCivitaConnection_mpullback`: the same statement for Mathlib's
  `CovariantDerivative.leviCivitaConnection`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Prop. 5.13.
-/

public section

open Bundle FiberBundle Manifold VectorField CovariantDerivative
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- Pulling back vector fields along a Riemannian isometry preserves their pointwise inner
products. -/
@[simp]
theorem inner_mpullback (Φ : RiemannianIsometry I J M N) (Y Z : Π y : N, TangentSpace J y)
    (x : M) :
    inner ℝ (mpullback I J Φ Y x) (mpullback I J Φ Z x) = inner ℝ (Y (Φ x)) (Z (Φ x)) := by
  rw [← Φ.inner_mfderiv x]
  -- `⇑Φ.toDiffeomorph` is `⇑Φ` by definition (`coe_toDiffeomorph` is `rfl`).
  exact congrArg₂ (inner ℝ) (Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Y x)
    (Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Z x)

variable [IsManifold I 2 M] [IsManifold J 2 N] [CompleteSpace E]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- **Naturality of the Koszul expression.** The Koszul expression of the pullbacks of three
vector fields along a Riemannian isometry `Φ` is the Koszul expression of the fields themselves,
evaluated at the image point. -/
@[simp]
theorem koszul_mpullback (Φ : RiemannianIsometry I J M N) {X Y Z : Π y : N, TangentSpace J y}
    {x : M} (hX : MDiffAt (T% X) (Φ x)) (hY : MDiffAt (T% Y) (Φ x))
    (hZ : MDiffAt (T% Z) (Φ x)) :
    koszul I (mpullback I J Φ X) (mpullback I J Φ Y) (mpullback I J Φ Z) x =
      koszul J X Y Z (Φ x) := by
  -- Directional derivatives of inner products: the chain rule through `Φ`.
  have hd : ∀ {V W : Π y : N, TangentSpace J y} (U : Π y : N, TangentSpace J y),
      MDiffAt (T% V) (Φ x) → MDiffAt (T% W) (Φ x) →
      mvfderiv I (fun y ↦ inner ℝ (mpullback I J Φ V y) (mpullback I J Φ W y)) x
          (mpullback I J Φ U x) =
        mvfderiv J (fun y ↦ inner ℝ (V y) (W y)) (Φ x) (U (Φ x)) := by
    intro V W U hV hW
    have hcomp : (fun y ↦ inner ℝ (mpullback I J Φ V y) (mpullback I J Φ W y)) =
        (fun y ↦ inner ℝ (V y) (W y)) ∘ Φ := funext fun y ↦ Φ.inner_mpullback V W y
    rw [hcomp, mvfderiv_comp_apply x (mdifferentiableAt_inner hV hW) (Φ.mdifferentiableAt x)]
    exact congrArg _ (Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) U x)
  -- Lie brackets: Mathlib's naturality of the Lie bracket under pullback.
  have hb : ∀ {V W : Π y : N, TangentSpace J y}, MDiffAt (T% V) (Φ x) →
      MDiffAt (T% W) (Φ x) →
      mlieBracket I (mpullback I J Φ V) (mpullback I J Φ W) x =
        mpullback I J Φ (mlieBracket J V W) x := fun hV hW ↦ by
    let _ : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    let _ : IsManifold J (minSmoothness ℝ 2) N := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    exact (mpullback_mlieBracket hV hW (Φ.toDiffeomorph.contMDiff.contMDiffAt) (by simp)).symm
  rw [koszul_apply, koszul_apply, hd X hY hZ, hd Y hZ hX, hd Z hX hY, hb hX hY, hb hX hZ,
    hb hY hZ, inner_mpullback, inner_mpullback, inner_mpullback]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Naturality of Levi-Civita connections under Riemannian isometries.** If `∇ᴹ` and `∇ᴺ` are
Levi-Civita connections of `M` and `N` and `Φ : M → N` is a smooth Riemannian isometry, then
`dΦ_x (∇ᴹ_v (Φ^* Y)) = ∇ᴺ_{dΦ_x v} Y` for every vector field `Y` on `N` differentiable at
`Φ x`. -/
theorem mfderiv_apply_mpullback_of_isLeviCivitaConnection (Φ : RiemannianIsometry I J M N)
    {covM : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    {covN : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
    (hM : covM.IsLeviCivitaConnection) (hN : covN.IsLeviCivitaConnection)
    {Y : Π y : N, TangentSpace J y} {x : M} (hY : MDiffAt (T% Y) (Φ x)) (v : TangentSpace I x) :
    mfderiv I J Φ x (covM (mpullback I J Φ Y) x v) = covN Y (Φ x) (mfderiv I J Φ x v) := by
  have hpull : ∀ {V : Π y : N, TangentSpace J y}, MDiffAt (T% V) (Φ x) →
      MDiffAt (T% (mpullback I J Φ V)) x := fun hV ↦
    hV.mpullback_vectorField (Φ.toDiffeomorph.contMDiff.contMDiffAt)
      (Φ.toDiffeomorph.isInvertible_mfderiv (by simp)) (by simp)
  -- Realize the direction `dΦ_x v` by a vector field on `N` whose pullback takes the value `v`.
  obtain ⟨X, hX, hXv⟩ : ∃ X : Π y : N, TangentSpace J y,
      MDiffAt (T% X) (Φ x) ∧ X (Φ x) = mfderiv I J Φ x v :=
    ⟨extend F _, mdifferentiableAt_extend J F _, extend_apply_self F _⟩
  have hXx : mpullback I J Φ X x = v := by
    rw [mpullback_apply, hXv]
    exact (Φ.toDiffeomorph.isInvertible_mfderiv (by simp)).inverse_apply_self v
  refine TauCeti.eq_of_forall_inner_section_eq (I := J) (V := fun y : N ↦ TangentSpace J y) F
    fun Z hZ ↦ ?_
  have hMk := hM.two_inner_eq_koszul (hpull hX) (hpull hY) (hpull hZ)
  have hNk := hN.two_inner_eq_koszul hX hY hZ
  rw [Φ.koszul_mpullback hX hY hZ, hXx] at hMk
  rw [hXv] at hNk
  have hinner : inner ℝ (mfderiv I J Φ x (covM (mpullback I J Φ Y) x v)) (Z (Φ x)) =
      inner ℝ (covM (mpullback I J Φ Y) x v) (mpullback I J Φ Z x) := by
    rw [← Φ.inner_mfderiv x]
    exact congrArg _ (Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Z x).symm
  linarith

/-- **Naturality of the Levi-Civita connection under Riemannian isometries**, for Mathlib's
`CovariantDerivative.leviCivitaConnection`:
`dΦ_x (∇ᴹ_v (Φ^* Y)) = ∇ᴺ_{dΦ_x v} Y` for every vector field `Y` on `N` differentiable at
`Φ x`. -/
@[simp]
theorem mfderiv_leviCivitaConnection_mpullback (Φ : RiemannianIsometry I J M N)
    {Y : Π y : N, TangentSpace J y} {x : M} (hY : MDiffAt (T% Y) (Φ x)) (v : TangentSpace I x) :
    mfderiv I J Φ x (leviCivitaConnection I M (mpullback I J Φ Y) x v) =
      leviCivitaConnection J N Y (Φ x) (mfderiv I J Φ x v) :=
  Φ.mfderiv_apply_mpullback_of_isLeviCivitaConnection
    (isLeviCivitaConnection_leviCivitaConnection I) (isLeviCivitaConnection_leviCivitaConnection J)
    hY v

end TauCeti.RiemannianIsometry

end
