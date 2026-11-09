/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Lie.Tangent.LieEquiv
public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Manifold.Algebra.Monoid
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Monoid
import TauCeti.Geometry.Manifold.VectorField.Related

/-!
# The Lie functor on smooth homomorphisms

The differential at the identity of a smooth Lie-group homomorphism induces a Lie-algebra
homomorphism between left-invariant derivations. Smooth homomorphisms carry their differentiability
proof in `ContMDiffMonoidMorphism`; identity and composition complete that bundled morphism API.
The resulting Lie map preserves identities and composition and is natural with respect to the
Lie-group exponential.

## References

* The exponential-naturality proof generalizes the integral-curve argument in
  `TauCeti.Lie.conj_mulInvariantIntegralCurve` and `TauCeti.Lie.conj_mulInvariantExp`.

## Main results

* `lieMap`: the Lie-algebra homomorphism induced by a smooth monoid morphism.
* `ContMDiffMonoidMorphism.groupLieAlgebraMap_lie`: the differential at the identity of a smooth
  homomorphism preserves the Lie bracket.
* `lieMap_id`, `lieMap_comp`: the identity and composition laws.
* `map_lieExp`: naturality with respect to the Lie-group exponential.
* `continuous_lieMap`: the Lie map is continuous.
* `ContMDiffMonoidMorphism.isLocalDiffeomorph_iff_lieMap_bijective` and
  `ContMDiffMonoidMorphism.isLocalDiffeomorph_of_lieMap_bijective`: the local-diffeomorphism
  criterion at every point.
* `ContMDiffMonoidMorphism.lieMap_injective_of_mfderiv_injective`: injectivity of the identity
  differential implies injectivity of the Lie map.
* `TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt`: the Lie-algebra equivalence induced by a smooth
  homomorphism that is a local diffeomorphism at the identity.
* `ContMDiffMonoidMorphism.lieMap_bijective_of_isLocalDiffeomorphAt`: the Lie map of a
  homomorphism that is a local diffeomorphism at the identity is bijective.
* `ContMDiffMonoidMorphism.isLocalDiffeomorphAt_of_lieMap_bijective`: a smooth homomorphism with
  bijective Lie map is a local diffeomorphism at the identity.
* `ContMDiffMonoidMorphism.isLocalDiffeomorphAt_iff_lieMap_bijective`: the corresponding
  characterization.
-/

public section

noncomputable section

open Function Manifold VectorField
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable [LieGroup I ∞ G] [LieGroup I' ∞ G']

private theorem mfderiv_monoidHom_mulInvariantVectorField
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G)
    (X : GroupLieAlgebra I G) :
    mfderiv I I' φ g (mulInvariantVectorField X g) =
      mulInvariantVectorField (φ.toMonoidHom.groupLieAlgebraMap I I' X) (φ g) := by
  simp only [mulInvariantVectorField]
  have hfun : (φ : G → G') ∘ (fun y : G ↦ g * y) =
      (fun z : G' ↦ φ g * z) ∘ φ := by
    funext y
    simp
  have h := congrArg (fun L : E →L[ℝ] E' ↦ L X)
    (mfderiv_congr (I := I) (I' := I') (x := (1 : G)) hfun)
  have hleft := mfderiv_comp (I := I) (I' := I) (I'' := I') (x := (1 : G))
    (g := (φ : G → G')) (f := fun y : G ↦ g * y)
    (φ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
    (mdifferentiableAt_mul_left (a := g))
  have hright := mfderiv_comp (I := I) (I' := I') (I'' := I') (x := (1 : G))
    (g := fun z : G' ↦ φ g * z) (f := (φ : G → G'))
    (mdifferentiableAt_mul_left (a := φ g))
    (φ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
  rw [hleft, hright] at h
  rw [mul_one, map_one] at h
  rw [φ.toMonoidHom.groupLieAlgebraMap_apply I X]
  exact h

/-- The differential at the identity of a smooth homomorphism preserves the Lie bracket of the
tangent Lie algebras. -/
theorem ContMDiffMonoidMorphism.groupLieAlgebraMap_lie
    [CompleteSpace E] [CompleteSpace E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (X Y : GroupLieAlgebra I G) :
    φ.toMonoidHom.groupLieAlgebraMap I I' ⁅X, Y⁆ =
      ⁅φ.toMonoidHom.groupLieAlgebraMap I I' X, φ.toMonoidHom.groupLieAlgebraMap I I' Y⁆ := by
  have h := TauCeti.mfderiv_mlieBracket_of_eventually_related (I := I') (J := I) (n := ∞)
    (f := ⇑φ) (y := (1 : G)) φ.contMDiff_toFun.contMDiffAt (by simp)
    (mdifferentiableAt_mulInvariantVectorField X) (mdifferentiableAt_mulInvariantVectorField Y)
    (mdifferentiableAt_mulInvariantVectorField (φ.toMonoidHom.groupLieAlgebraMap I I' X))
    (mdifferentiableAt_mulInvariantVectorField (φ.toMonoidHom.groupLieAlgebraMap I I' Y))
    (Filter.Eventually.of_forall fun g => mfderiv_monoidHom_mulInvariantVectorField φ g X)
    (Filter.Eventually.of_forall fun g => mfderiv_monoidHom_mulInvariantVectorField φ g Y)
  rw [φ.toMonoidHom.groupLieAlgebraMap_apply I, GroupLieAlgebra.bracket_def X Y,
    GroupLieAlgebra.bracket_def]
  rw [map_one] at h
  exact h

/-- The Lie functor on morphisms: the differential at the identity of a smooth homomorphism. -/
noncomputable def lieMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') :
    LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G' :=
  let tangentMap : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I' G' :=
    { toLinearMap := φ.toMonoidHom.groupLieAlgebraMap I I'
      map_lie' := by
        intro X Y
        exact φ.groupLieAlgebraMap_lie X Y }
  (leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := I') (G := G') (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)).symm.toLieHom.comp
    (tangentMap.comp
      (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)).toLieHom)

/-- Under evaluation at the identity, `lieMap` is the manifold differential of the homomorphism. -/
@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra
        (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
        (lieMap φ D) =
      mfderiv I I' φ 1
        (leftInvariantDerivationLieEquivGroupLieAlgebra
          (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) D) := by
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let hG' := ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra hG'
  -- Unfold the transported `LieHom` application once to expose the two canonical Lie
  -- equivalences; their inverse law then characterizes `lieMap` without exposing its body publicly.
  change e' (e'.symm (φ.toMonoidHom.groupLieAlgebraMap I I' (e D))) = _
  rw [e'.apply_symm_apply]
  exact φ.toMonoidHom.groupLieAlgebraMap_apply I (e D)

/-- The Lie map of the identity homomorphism is the identity Lie-algebra homomorphism. -/
@[simp]
theorem lieMap_id [FiniteDimensional ℝ E] :
    lieMap (ContMDiffMonoidMorphism.id (I := I) (G := G)) = 1 := by
  apply LieHom.ext
  intro D
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  apply e.injective
  rw [one_apply_eq_self]
  -- Expose the transported `LieHom` application so the coordinate theorem matches the target.
  change e (lieMap (ContMDiffMonoidMorphism.id (I := I) (G := G)) D) = e D
  rw [leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap]
  rw [ContMDiffMonoidMorphism.coe_id]
  simp
  rfl

/-- The Lie map of a composite is the composite of the two Lie maps. -/
@[simp]
theorem lieMap_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [LieGroup I'' ∞ G''] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [FiniteDimensional ℝ E'']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (ψ : ContMDiffMonoidMorphism I' I'' ∞ G' G'') :
    lieMap (ψ.comp φ) = (lieMap ψ).comp (lieMap φ) := by
  apply LieHom.ext
  intro D
  let hG := ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)
  let hG' := ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')
  let hG'' := ContMDiffMul.isInteriorPoint (I := I'') (n := ∞) (by simp) (1 : G'')
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra hG
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra hG'
  let e'' := leftInvariantDerivationLieEquivGroupLieAlgebra hG''
  apply e''.injective
  have hleft : e'' (lieMap (ψ.comp φ) D) =
      mfderiv I I'' (ψ.comp φ) 1 (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _
  have hφD : e' (lieMap φ D) = mfderiv I I' φ 1 (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _
  have hψD : e'' (lieMap ψ (lieMap φ D)) =
      mfderiv I' I'' ψ 1 (e' (lieMap φ D)) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap _ _
  have hchain' : mfderiv I I'' (ψ.comp φ) 1 (e D) =
      mfderiv I' I'' ψ 1 (mfderiv I I' φ 1 (e D)) := by
    rw [ContMDiffMonoidMorphism.coe_comp]
    exact mfderiv_comp_apply_of_eq 1 (ψ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
      (φ.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt (map_one φ) (e D)
  have hright : mfderiv I' I'' ψ 1 (mfderiv I I' φ 1 (e D)) =
      e'' (lieMap ψ (lieMap φ D)) := by
    rw [← hφD, ← hψD]
  rw [LieHom.comp_apply]
  exact hleft.trans (hchain'.trans hright)

private theorem monoidHom_mulInvariantExp
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (X : GroupLieAlgebra I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
    φ (mulInvariantExp (I := I) (G := G) X) =
      mulInvariantExp (I := I') (G := G')
        (φ.toMonoidHom.groupLieAlgebraMap I I' X) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
  dsimp only
  let Y := φ.toMonoidHom.groupLieAlgebraMap I I' X
  let γ := mulInvariantIntegralCurve (I := I) (G := G) X 1
  have hcurve : IsMIntegralCurve (φ ∘ γ)
      (mulInvariantVectorField (I := I') (G := G') Y) := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn]
    exact IsMIntegralCurveOn.map_of_mfderiv_eq (I := I) (I' := I')
      (M := G) (M' := G') (f := (φ : G → G'))
      (V := mulInvariantVectorField (I := I) (G := G) X)
      (W := mulInvariantVectorField (I := I') (G := G') Y)
      (γ := γ) (s := Set.univ)
      (fun t _ => φ.contMDiff_toFun.mdifferentiable (by simp) (γ t))
      (fun t _ => mfderiv_monoidHom_mulInvariantVectorField (I := I) (I' := I') φ (γ t) X)
      ((isMIntegralCurve_mulInvariantIntegralCurve
        (I := I) (G := G) X 1).isMIntegralCurveOn Set.univ)
  have hzero : (φ ∘ γ) 0 = (1 : G') := by simp [γ]
  have heq : φ ∘ γ =
      mulInvariantIntegralCurve (I := I') (G := G') Y 1 :=
    eq_mulInvariantIntegralCurve (I := I') (G := G') Y 1 hzero hcurve
  rw [mulInvariantExp_eq_mulInvariantIntegralCurve]
  rw [mulInvariantExp_eq_mulInvariantIntegralCurve]
  exact congrFun heq 1

/-- A smooth group homomorphism intertwines the Lie-group exponentials through its Lie map. -/
@[simp]
theorem map_lieExp [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
    φ (lieExp X) = lieExp (lieMap φ X) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : T2Space G' := I'.t2Space_of_lieGroup ∞
  dsimp only
  rw [lieExp_eq_mulInvariantExp, lieExp_eq_mulInvariantExp]
  rw [monoidHom_mulInvariantExp (I := I) (I' := I') φ]
  congr 1
  rw [← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply, MonoidHom.groupLieAlgebraMap_apply]
  exact (leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap
    (I := I) (I' := I') φ X).symm

/-- The Lie map of a smooth homomorphism is continuous, being a linear map between
finite-dimensional real normed spaces. -/
theorem continuous_lieMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [T2Space G]
    [T2Space G'] (φ : ContMDiffMonoidMorphism I I' ∞ G G') : Continuous (lieMap φ) := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  exact (lieMap φ).toLinearMap.continuous_of_finiteDimensional

namespace ContMDiffMonoidMorphism

/-- A smooth homomorphism whose differential at the identity is injective induces an injective
Lie-algebra homomorphism. -/
theorem lieMap_injective_of_mfderiv_injective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (hφ : Function.Injective (mfderiv I I' φ 1)) :
    Function.Injective (lieMap φ) := by
  intro X Y hXY
  let sourceEquiv := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let targetEquiv := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
  have h := congrArg targetEquiv hXY
  rw [leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap,
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap] at h
  exact sourceEquiv.injective (hφ h)

/-- The Lie map of a smooth homomorphism that is a local diffeomorphism at the identity is
bijective: under evaluation at the identity it is the differential there, a linear equivalence. -/
theorem lieMap_bijective_of_isLocalDiffeomorphAt [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : IsLocalDiffeomorphAt I I' ∞ φ 1) :
    Bijective (lieMap φ) := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
  let L := hφ.mfderivToContinuousLinearEquiv (by simp)
  have h (D : LeftInvariantDerivation I G) : e' (lieMap φ D) = L (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ D
  refine ⟨fun D₁ D₂ hD ↦ e.injective (L.injective ((h D₁).symm.trans ((congrArg e' hD).trans
    (h D₂)))), fun D' ↦ ⟨e.symm (L.symm (e' D')), e'.injective ((h _).trans
      (by simp only [LieEquiv.apply_symm_apply]; exact L.apply_symm_apply _))⟩⟩

/-- A smooth homomorphism with bijective Lie map is a local diffeomorphism at the identity. -/
theorem isLocalDiffeomorphAt_of_lieMap_bijective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : Bijective (lieMap φ)) :
    IsLocalDiffeomorphAt I I' ∞ φ 1 := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
  let L : LieEquiv ℝ (LeftInvariantDerivation I G) (LeftInvariantDerivation I' G') :=
    LieEquiv.ofBijective (lieMap φ) hφ
  let T : TangentSpace I (1 : G) ≃ₗ[ℝ] TangentSpace I' (φ 1) := by
    rw [map_one]
    exact e.symm.toLinearEquiv.trans (L.toLinearEquiv.trans e'.toLinearEquiv)
  apply TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq
      (s := Set.univ) (e := T.toContinuousLinearEquiv)
      φ.contMDiff_toFun.contMDiffOn isOpen_univ (Set.mem_univ 1)
      BoundarylessManifold.isInteriorPoint (by simp)
  apply ContinuousLinearMap.ext
  intro X
  let D := e.symm X
  have h := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ D
  -- Normalize the tangent equivalences in `T` to the evaluation-at-one coordinates of `h`.
  change e' (lieMap φ (e.symm X)) = mfderiv I I' φ 1 X
  simpa only [D, e, e', LieEquiv.apply_symm_apply] using h

/-- A smooth homomorphism of finite-dimensional Lie groups is a local diffeomorphism at the
identity if and only if its Lie map is bijective. -/
theorem isLocalDiffeomorphAt_iff_lieMap_bijective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') :
  IsLocalDiffeomorphAt I I' ∞ φ 1 ↔ Bijective (lieMap φ) :=
  ⟨lieMap_bijective_of_isLocalDiffeomorphAt φ,
    isLocalDiffeomorphAt_of_lieMap_bijective φ⟩

/-- A smooth homomorphism of finite-dimensional Lie groups is a local diffeomorphism
if and only if its Lie map is bijective. -/
theorem isLocalDiffeomorph_iff_lieMap_bijective [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (f : ContMDiffMonoidMorphism I I' ∞ G G') :
    IsLocalDiffeomorph I I' ∞ f ↔ Bijective (lieMap f) :=
  (f.toMonoidHom.isLocalDiffeomorph_iff_isLocalDiffeomorphAt 1).trans
    f.isLocalDiffeomorphAt_iff_lieMap_bijective

/-- A smooth homomorphism with bijective Lie map is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_lieMap_bijective [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (f : ContMDiffMonoidMorphism I I' ∞ G G')
    (hf : Bijective (lieMap f)) : IsLocalDiffeomorph I I' ∞ f :=
  f.isLocalDiffeomorph_iff_lieMap_bijective.mpr hf

end ContMDiffMonoidMorphism

namespace TauCeti.Lie

/-- A smooth homomorphism that is a local diffeomorphism at the identity induces an equivalence of
Lie algebras. -/
noncomputable def lieEquivOfIsLocalDiffeomorphAt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : IsLocalDiffeomorphAt I I' ∞ φ 1) :
    LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I' G' :=
  LieEquiv.ofBijective (lieMap φ)
    (ContMDiffMonoidMorphism.lieMap_bijective_of_isLocalDiffeomorphAt φ hφ)

/-- The Lie-algebra equivalence induced by a local diffeomorphism acts by the Lie functor. -/
@[simp]
theorem lieEquivOfIsLocalDiffeomorphAt_apply
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : IsLocalDiffeomorphAt I I' ∞ φ 1)
    (X : LeftInvariantDerivation I G) :
    lieEquivOfIsLocalDiffeomorphAt φ hφ X = lieMap φ X := by
  simp [lieEquivOfIsLocalDiffeomorphAt]

/-- The Lie homomorphism underlying the equivalence induced by a local diffeomorphism is its Lie
map. -/
@[simp]
theorem lieEquivOfIsLocalDiffeomorphAt_toLieHom
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : IsLocalDiffeomorphAt I I' ∞ φ 1) :
    (lieEquivOfIsLocalDiffeomorphAt φ hφ).toLieHom = lieMap φ := by
  apply LieHom.ext
  intro X
  exact lieEquivOfIsLocalDiffeomorphAt_apply φ hφ X

/-- The inverse Lie-algebra equivalence of a local diffeomorphism sends the Lie map of a derivation
back to that derivation. -/
@[simp]
theorem lieEquivOfIsLocalDiffeomorphAt_symm_apply_lieMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : IsLocalDiffeomorphAt I I' ∞ φ 1)
    (X : LeftInvariantDerivation I G) :
    (lieEquivOfIsLocalDiffeomorphAt φ hφ).symm (lieMap φ X) = X := by
  rw [← lieEquivOfIsLocalDiffeomorphAt_apply φ hφ]
  exact (lieEquivOfIsLocalDiffeomorphAt φ hφ).symm_apply_apply X

/-- The Lie map of a local diffeomorphism sends the inverse Lie-algebra equivalence of a derivation
back to that derivation. -/
@[simp]
theorem lieMap_lieEquivOfIsLocalDiffeomorphAt_symm_apply
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (hφ : IsLocalDiffeomorphAt I I' ∞ φ 1)
    (Y : LeftInvariantDerivation I' G') :
    lieMap φ ((lieEquivOfIsLocalDiffeomorphAt φ hφ).symm Y) = Y := by
  rw [← lieEquivOfIsLocalDiffeomorphAt_apply φ hφ]
  exact (lieEquivOfIsLocalDiffeomorphAt φ hφ).apply_symm_apply Y

end TauCeti.Lie
