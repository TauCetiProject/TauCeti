/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.Analysis.Complex.Basic

/-!
# Coefficient maps and coefficient scalars of differential forms

A continuous real-linear map `L : F →L[ℝ] G` of coefficient spaces sends an `F`-valued
differential form to the `G`-valued form `RoughForm.mapCoeff L φ`, obtained by applying `L` to
each value. This preserves regularity, commutes with pullback, and commutes with the exterior
derivative of differentiable forms. On smooth forms it is the real-linear map
`SmoothForm.mapCoeff L`.

Scalars acting on the coefficients act on smooth forms through the coefficient map given by
multiplication by the scalar. When `F` is a complex vector space, this makes
`SmoothForm I M F k` a complex vector space whose complex scalars restrict to its existing real
scalars, as needed for complex-valued forms on complex manifolds, and the exterior derivative
and pullback are complex-linear. The scalar action is defined on underlying forms pointwise,
so for real scalars it agrees with the submodule action on `SmoothForm I M F k` up to reducible
unfolding of instances. Coefficient conjugation of complex-valued forms is conjugate-linear.

The paired wedge is natural for coefficient maps intertwining two pairings. A pairing that turns
multiplication by one scalar into multiplication by another makes the wedge of smooth forms
semilinear in the same way; in particular, the wedge for a complex-bilinear pairing of complex
coefficient spaces is complex-linear in each form. Coefficient conjugation is multiplicative for
the wedge of complex-valued forms given by complex multiplication.

## Main declarations

* `TauCeti.RoughForm.mapCoeff`, `TauCeti.SmoothForm.mapCoeff`: coefficient maps of forms.
* `TauCeti.IsSmoothForm.mapCoeff`: coefficient maps preserve regularity.
* `TauCeti.mextDerivWithin_mapCoeff`, `TauCeti.mextDeriv_mapCoeff`: naturality of the exterior
  derivative in the coefficient space.
* `TauCeti.mpullbackWithin_mapCoeff`, `TauCeti.mpullback_mapCoeff`: coefficient maps commute
  with pullback.
* `TauCeti.SmoothForm.instModule`: the action of scalars on the coefficients, for instance
  complex scalars on complex-valued forms, with `TauCeti.SmoothForm.smul_toRoughForm` and
  `TauCeti.SmoothForm.smul_eq_mapCoeff`.
* `TauCeti.SmoothForm.mextDerivₗ_smul`, `TauCeti.SmoothForm.mpullback_smul`: the exterior
  derivative and pullback are linear for these scalars.
* `TauCeti.SmoothForm.mapCoeff_conj_smul`: coefficient conjugation is conjugate-linear.
* `TauCeti.RoughForm.mapCoeff_wedgeWith`, `TauCeti.SmoothForm.mapCoeff_wedgeWith`: naturality of
  the paired wedge in the coefficients.
* `TauCeti.SmoothForm.wedgeWith_smul_left_of_map_smul`,
  `TauCeti.SmoothForm.wedgeWith_smul_right_of_map_smul`: the paired wedge is linear, or
  semilinear, for scalars acting on the coefficients compatibly with the pairing.
* `TauCeti.SmoothForm.mapCoeff_conj_wedgeWith_mul`: coefficient conjugation of the wedge of
  complex-valued forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

variable {E H M E' H' M' F G G' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']
  {k : ℕ}

/-! ### Coefficient maps of rough forms -/

namespace RoughForm

/-- The form obtained by applying a fixed continuous linear map of coefficient spaces to the
values of a form. -/
def mapCoeff (L : F →L[ℝ] G) (φ : RoughForm I M F k) : RoughForm I M G k :=
  fun x ↦ L.compContinuousAlternatingMap (φ x)

@[simp]
theorem mapCoeff_apply (L : F →L[ℝ] G) (φ : RoughForm I M F k) (x : M)
    (v : Fin k → TangentSpace I x) : mapCoeff L φ x v = L (φ x v) :=
  (rfl)

@[simp]
theorem mapCoeff_zero (L : F →L[ℝ] G) : mapCoeff L (0 : RoughForm I M F k) = 0 := by
  ext x v
  simp

@[simp]
theorem mapCoeff_add (L : F →L[ℝ] G) (φ ψ : RoughForm I M F k) :
    mapCoeff L (φ + ψ) = mapCoeff L φ + mapCoeff L ψ := by
  ext x v
  simp

@[simp]
theorem mapCoeff_smul (L : F →L[ℝ] G) (c : ℝ) (φ : RoughForm I M F k) :
    mapCoeff L (c • φ) = c • mapCoeff L φ := by
  ext x v
  simp

@[simp]
theorem mapCoeff_id (φ : RoughForm I M F k) : mapCoeff (ContinuousLinearMap.id ℝ F) φ = φ :=
  (rfl)

@[simp]
theorem mapCoeff_mapCoeff (L' : G →L[ℝ] G') (L : F →L[ℝ] G) (φ : RoughForm I M F k) :
    mapCoeff L' (mapCoeff L φ) = mapCoeff (L'.comp L) φ :=
  (rfl)

/-- Scalar multiplication of the coefficients is the coefficient map given by multiplication by
the scalar. -/
theorem smul_eq_mapCoeff {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (c : S) (φ : RoughForm I M F k) :
    c • φ = mapCoeff (c • ContinuousLinearMap.id ℝ F) φ := by
  ext x v
  simp

/-- A coefficient map that is semilinear for scalars `c ↦ d` turns multiplication by `c` into
multiplication by `d`. -/
theorem mapCoeff_smul_of_map_smul {S S' : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] [Monoid S'] [DistribMulAction S' G]
    [ContinuousConstSMul S' G] [SMulCommClass ℝ S' G] (L : F →L[ℝ] G) {c : S} {d : S'}
    (hL : ∀ v, L (c • v) = d • L v) (φ : RoughForm I M F k) :
    mapCoeff L (c • φ) = d • mapCoeff L φ := by
  ext x v
  simp [hL]

/-- In every chart, the coordinate expression of a coefficient map of a form is the coefficient
map of its coordinate expression. -/
theorem inChartAt_mapCoeff (L : F →L[ℝ] G) (φ : RoughForm I M F k) (x₀ : M) :
    (mapCoeff L φ).inChartAt x₀ = fun z ↦ L.compContinuousAlternatingMap (φ.inChartAt x₀ z) := by
  ext z v
  simp only [inChartAt_apply, mapCoeff_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
    Function.comp_apply]

end RoughForm

/-- A coefficient map preserves the regularity of a form. -/
theorem IsSmoothForm.mapCoeff [IsManifold I 1 M] {n : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) (L : F →L[ℝ] G) : IsSmoothForm I n (RoughForm.mapCoeff L φ) :=
  IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun x ↦ by
    rw [RoughForm.inChartAt_mapCoeff]
    exact (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E F G (Fin k) L).contDiff
      |>.comp_contDiffWithinAt (hφ.contDiffWithinAt_inChartAt_self x)

/-- The exterior derivative is natural in the coefficient space, at a point where the
coordinate expression of the form is differentiable within the set. -/
theorem mextDerivWithin_mapCoeff (L : F →L[ℝ] G) {φ : RoughForm I M F k} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x)) :
    mextDerivWithin (RoughForm.mapCoeff L φ) s x =
      L.compContinuousAlternatingMap (mextDerivWithin φ s x) := by
  rw [mextDerivWithin_def, mextDerivWithin_def, RoughForm.inChartAt_mapCoeff]
  exact L.extDerivWithin_compContinuousAlternatingMap hs hφ

/-- The exterior derivative of a `C¹` form is natural in the coefficient space. -/
theorem mextDeriv_mapCoeff [IsManifold I 1 M] (L : F →L[ℝ] G) {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I 1 φ) :
    mextDeriv (RoughForm.mapCoeff L φ) = RoughForm.mapCoeff L (mextDeriv φ) := by
  funext x
  simp only [← mextDerivWithin_univ]
  exact mextDerivWithin_mapCoeff L (uniqueMDiffWithinAt_univ I) (by
    simpa using (hφ.contDiffWithinAt_inChartAt_self x).differentiableWithinAt one_ne_zero)

/-- Coefficient maps commute with within-set pullback. -/
@[simp]
theorem mpullbackWithin_mapCoeff (L : F →L[ℝ] G) (f : M → M') (s : Set M)
    (η : RoughForm I' M' F k) :
    mpullbackWithin I I' f s (RoughForm.mapCoeff L η) =
      RoughForm.mapCoeff L (mpullbackWithin I I' f s η) := by
  ext x v
  simp

/-- Coefficient maps commute with pullback. -/
@[simp]
theorem mpullback_mapCoeff (L : F →L[ℝ] G) (f : M → M') (η : RoughForm I' M' F k) :
    mpullback I I' f (RoughForm.mapCoeff L η) = RoughForm.mapCoeff L (mpullback I I' f η) := by
  ext x v
  simp

/-! ### Coefficient maps of smooth forms -/

namespace SmoothForm

variable [IsManifold I 1 M]

/-- A continuous linear map of coefficient spaces, as a linear map on smooth forms. -/
def mapCoeff (L : F →L[ℝ] G) : SmoothForm I M F k →ₗ[ℝ] SmoothForm I M G k where
  toFun φ := ⟨RoughForm.mapCoeff L φ.1, (φ.isSmoothForm.mapCoeff L).mem_smoothForms⟩
  map_add' φ ψ := Subtype.ext (RoughForm.mapCoeff_add L φ.1 ψ.1)
  map_smul' c φ := Subtype.ext (RoughForm.mapCoeff_smul L c φ.1)

/-- The underlying rough form of a coefficient map of a smooth form. -/
@[simp]
theorem coe_mapCoeff (L : F →L[ℝ] G) (φ : SmoothForm I M F k) :
    (mapCoeff L φ).1 = RoughForm.mapCoeff L φ.1 :=
  (rfl)

@[simp]
theorem mapCoeff_id : mapCoeff (I := I) (M := M) (k := k) (ContinuousLinearMap.id ℝ F) =
    LinearMap.id :=
  (rfl)

theorem mapCoeff_comp (L' : G →L[ℝ] G') (L : F →L[ℝ] G) :
    mapCoeff (I := I) (M := M) (k := k) (L'.comp L) = (mapCoeff L').comp (mapCoeff L) :=
  (rfl)

/-- The exterior derivative of smooth forms is natural in the coefficient space. -/
@[simp]
theorem mextDerivₗ_mapCoeff [IsManifold I 2 M] (L : F →L[ℝ] G) (φ : SmoothForm I M F k) :
    mextDerivₗ I k (mapCoeff L φ) = mapCoeff L (mextDerivₗ I k φ) :=
  Subtype.ext <| by
    simpa only [mextDerivₗ_apply, coe_mapCoeff] using
      mextDeriv_mapCoeff L (φ.isSmoothForm.of_le (by simp))

variable [IsManifold I' 1 M']

/-- Coefficient maps commute with pullback of smooth forms. -/
@[simp]
theorem mpullback_mapCoeff (L : F →L[ℝ] G) (f : M → M') (hf : ContMDiff I I' ∞ f)
    (φ : SmoothForm I' M' F k) :
    mpullback f hf (mapCoeff L φ) = mapCoeff L (mpullback f hf φ) :=
  Subtype.ext <| by simp only [coe_mpullback, coe_mapCoeff, TauCeti.mpullback_mapCoeff]

/-! ### Scalars acting on the coefficients -/

section Scalars

variable {S : Type*}

/-- Scalars acting on the coefficients act on smooth forms pointwise. -/
instance instSMul [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] : SMul S (SmoothForm I M F k) where
  smul c φ := ⟨c • φ.1, by
    rw [RoughForm.smul_eq_mapCoeff]
    exact (φ.isSmoothForm.mapCoeff _).mem_smoothForms⟩

/-- The rough form underlying a scalar multiple of a smooth form is the scalar multiple of its
rough form. -/
@[simp]
theorem smul_toRoughForm [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] (c : S) (φ : SmoothForm I M F k) : (c • φ).1 = c • φ.1 :=
  (rfl)

/-- Scalar multiplication of a smooth form is the coefficient map given by multiplication by the
scalar. -/
theorem smul_eq_mapCoeff [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] (c : S) (φ : SmoothForm I M F k) :
    c • φ = mapCoeff (c • ContinuousLinearMap.id ℝ F) φ :=
  Subtype.ext (RoughForm.smul_eq_mapCoeff c φ.1)

/-- Scalars acting on the coefficients act on smooth forms, making them a module. For complex
coefficients this is the complex vector space of complex-valued smooth forms. -/
instance instModule [Semiring S] [Module S F] [ContinuousConstSMul S F] [SMulCommClass ℝ S F] :
    Module S (SmoothForm I M F k) :=
  Function.Injective.module S (smoothForms I M F k).subtype.toAddMonoidHom
    Subtype.val_injective fun _ _ ↦ (rfl)

/-- When the coefficient scalars restrict to real scalars, so do their actions on smooth forms;
for complex coefficients, `RCLike.real_smul_eq_coe_smul` then identifies the real action on
smooth forms with the action of real numbers viewed as complex numbers. -/
instance [SMul ℝ S] [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] [IsScalarTower ℝ S F] : IsScalarTower ℝ S (SmoothForm I M F k) where
  smul_assoc r c φ := Subtype.ext (smul_assoc r c φ.1)

instance [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F] [SMulCommClass ℝ S F] :
    SMulCommClass ℝ S (SmoothForm I M F k) where
  smul_comm r c φ := Subtype.ext (smul_comm r c φ.1)

instance [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F] [SMulCommClass ℝ S F] :
    SMulCommClass S ℝ (SmoothForm I M F k) :=
  .symm _ _ _

/-- A coefficient map that is semilinear for scalars `c ↦ d` turns multiplication of smooth
forms by `c` into multiplication by `d`. -/
theorem mapCoeff_smul_of_map_smul {S' : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] [Monoid S'] [DistribMulAction S' G]
    [ContinuousConstSMul S' G] [SMulCommClass ℝ S' G] (L : F →L[ℝ] G) {c : S} {d : S'}
    (hL : ∀ v, L (c • v) = d • L v) (φ : SmoothForm I M F k) :
    mapCoeff L (c • φ) = d • mapCoeff L φ :=
  Subtype.ext (RoughForm.mapCoeff_smul_of_map_smul L hL φ.1)

/-- The exterior derivative of smooth forms is linear for scalars acting on the coefficients,
such as complex scalars on complex-valued forms. -/
@[simp]
theorem mextDerivₗ_smul [IsManifold I 2 M] [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass ℝ S F] (c : S) (φ : SmoothForm I M F k) :
    mextDerivₗ I k (c • φ) = c • mextDerivₗ I k φ := by
  rw [smul_eq_mapCoeff, smul_eq_mapCoeff, mextDerivₗ_mapCoeff]

/-- Pullback of smooth forms is linear for scalars acting on the coefficients. -/
@[simp]
theorem mpullback_smul [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] (f : M → M') (hf : ContMDiff I I' ∞ f) (c : S)
    (φ : SmoothForm I' M' F k) :
    mpullback f hf (c • φ) = c • mpullback f hf φ :=
  Subtype.ext <| by simp only [coe_mpullback, smul_toRoughForm, TauCeti.mpullback_smul]

end Scalars

/-- Complex conjugation of the coefficients of complex-valued smooth forms is
conjugate-linear. -/
theorem mapCoeff_conj_smul (c : ℂ) (φ : SmoothForm I M ℂ k) :
    mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) (c • φ) =
      conj c • mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) φ :=
  mapCoeff_smul_of_map_smul _ (fun v ↦ by simp) φ

end SmoothForm

/-! ### Coefficient maps and scalars of wedge products -/

section Wedge

variable {F₁ F₂ F₃ G₁ G₂ G₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [NormedAddCommGroup G₃] [NormedSpace ℝ G₃]
  {l : ℕ}

/-- The paired rough-form wedge is natural in the coefficients: if coefficient maps `L₁`, `L₂`,
`L` intertwine the pairings `μ` and `μ'`, then the coefficient map `L` of the wedge of `φ` and `ψ`
is the wedge of their coefficient maps. -/
theorem RoughForm.mapCoeff_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (μ' : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (L₁ : F₁ →L[ℝ] G₁) (L₂ : F₂ →L[ℝ] G₂) (L : F₃ →L[ℝ] G₃)
    (hL : ∀ a b, L (μ a b) = μ' (L₁ a) (L₂ b)) (φ : RoughForm I M F₁ k)
    (ψ : RoughForm I M F₂ l) :
    mapCoeff L (φ.wedgeWith μ ψ) = (mapCoeff L₁ φ).wedgeWith μ' (mapCoeff L₂ ψ) := by
  funext x
  simp only [mapCoeff, wedgeWith_apply']
  exact ContinuousAlternatingMap.compContinuousAlternatingMap_pairedWedge μ μ.continuous₂ μ'
    μ'.continuous₂ L₁ L₂ L hL (φ x) (ψ x)

namespace SmoothForm

variable [IsManifold I 1 M]

/-- The paired wedge of smooth forms is natural in the coefficients: if coefficient maps `L₁`,
`L₂`, `L` intertwine the pairings `μ` and `μ'`, then the coefficient map `L` of the wedge of `φ`
and `ψ` is the wedge of their coefficient maps. -/
theorem mapCoeff_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (μ' : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (L₁ : F₁ →L[ℝ] G₁) (L₂ : F₂ →L[ℝ] G₂) (L : F₃ →L[ℝ] G₃)
    (hL : ∀ a b, L (μ a b) = μ' (L₁ a) (L₂ b)) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    mapCoeff L (wedgeWith μ φ ψ) = wedgeWith μ' (mapCoeff L₁ φ) (mapCoeff L₂ ψ) :=
  Subtype.ext <| by
    simpa only [coe_mapCoeff, coe_wedgeWith] using
      RoughForm.mapCoeff_wedgeWith μ μ' L₁ L₂ L hL φ.1 ψ.1

section Scalars

variable {S S' : Type*} [Monoid S'] [DistribMulAction S' F₃] [ContinuousConstSMul S' F₃]
  [SMulCommClass ℝ S' F₃]

/-- If the pairing turns multiplication by `c` in its first argument into multiplication by `d`,
then so does the paired wedge of smooth forms in its first form. For a complex-bilinear pairing
of complex coefficient spaces this is complex-linearity in the first form; it also covers
pairings that are conjugate-linear in the first argument. -/
theorem wedgeWith_smul_left_of_map_smul [Monoid S] [DistribMulAction S F₁]
    [ContinuousConstSMul S F₁] [SMulCommClass ℝ S F₁] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {c : S} {d : S'}
    (hcd : ∀ a b, μ (c • a) b = d • μ a b) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    wedgeWith μ (c • φ) ψ = d • wedgeWith μ φ ψ :=
  Subtype.ext <| by
    simpa only [coe_wedgeWith, smul_toRoughForm] using
      RoughForm.wedgeWith_smul_left_of_map_smul μ hcd φ.1 ψ.1

/-- If the pairing turns multiplication by `c` in its second argument into multiplication by
`d`, then so does the paired wedge of smooth forms in its second form. For a complex-bilinear
pairing of complex coefficient spaces this is complex-linearity in the second form. -/
theorem wedgeWith_smul_right_of_map_smul [Monoid S] [DistribMulAction S F₂]
    [ContinuousConstSMul S F₂] [SMulCommClass ℝ S F₂] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {c : S} {d : S'}
    (hcd : ∀ a b, μ a (c • b) = d • μ a b) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    wedgeWith μ φ (c • ψ) = d • wedgeWith μ φ ψ :=
  Subtype.ext <| by
    simpa only [coe_wedgeWith, smul_toRoughForm] using
      RoughForm.wedgeWith_smul_right_of_map_smul μ hcd φ.1 ψ.1

end Scalars

/-- Complex conjugation of the coefficients of complex-valued smooth forms is multiplicative for
the wedge product given by complex multiplication. -/
theorem mapCoeff_conj_wedgeWith_mul (φ : SmoothForm I M ℂ k) (ψ : SmoothForm I M ℂ l) :
    mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) (wedgeWith (ContinuousLinearMap.mul ℝ ℂ) φ ψ) =
      wedgeWith (ContinuousLinearMap.mul ℝ ℂ) (mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) φ)
        (mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) ψ) :=
  mapCoeff_wedgeWith _ _ _ _ _ (fun a b ↦ by simp) φ ψ

end SmoothForm

end Wedge

end TauCeti
