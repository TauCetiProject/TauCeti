/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.EndLie
public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.RepresentationTheory.GKModule.Basic

/-!
# Compatible `(𝔤, K)`-modules

Let `K` be a Lie group modelled on `I` over `ℝ`, let `𝔤` be a Lie algebra over a normed field
extension `k` of `ℝ` (in the analytic theory `k = ℂ` and `𝔤` is a complexified Lie algebra) and let
`ι : Lie K → 𝔤` be the differentiated inclusion: for a Lie group `G` containing `K` through
`j : K →* G`, this is `c ∘ₗ (j.groupLieAlgebraMap I I').toLinearMap`, the differential
`MonoidHom.groupLieAlgebraMap` of `j` at `1` followed by a linear map `c : Lie G → 𝔤` (in the
analytic theory, the inclusion of `Lie G` into its complexification). A `(𝔤, K)`-module `M` in the
sense of harmonic analysis is a `TauCeti.GKModule` whose `K`-action is smooth on each
finite-dimensional `K`-stable subspace, with differential the action of `Lie K` through `ι`.

Every vector lies in the finite-dimensional `K`-stable span of its orbit, and a map into a
finite-dimensional space is smooth exactly when its coordinates are, with derivative computed
coordinatewise. So the condition is stated on matrix coefficients: for every linear functional `f`
and vector `v`, the function `g ↦ f (ρ g v)` is smooth, and its differential at `1` sends
`X ∈ Lie K` to `f ⁅ι X, v⁆`. No topology on `V` is needed.

Admissibility and the Harish-Chandra condition of `TauCeti.GKModule` are properties of the
underlying algebraic module and use no compatibility: a Harish-Chandra module in the sense of
harmonic analysis is a `TauCeti.GKModule` `M` with `M.IsCompatible ι` and
`M.IsHarishChandraModule`.

## Main definitions

* `TauCeti.GKModule.IsCompatible M ι`: the `K`-action of `M` is smooth on finite-dimensional
  `K`-stable subspaces, with differential the action of `Lie K` through `ι`.
* `TauCeti.GKModule.glStd V`: for a finite-dimensional real normed space `V`, the defining
  representation of `GL(V)` on `V` as a `(𝔤𝔩(V), GL(V))`-module, with `GL(V)` acting on `𝔤𝔩(V)` by
  conjugation (`TauCeti.GKModule.glConj`).

## Main statements

* `TauCeti.GKModule.isCompatible_glStd`: `glStd V` is compatible with the differentiated inclusion
  of `GL(V)` in itself.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), §3.3.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.GKModule

variable {k 𝔤 : Type*} [NontriviallyNormedField k] [NormedAlgebra ℝ k] [LieRing 𝔤]
  [LieAlgebra k 𝔤] [Module ℝ 𝔤] [IsScalarTower ℝ k 𝔤]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {K : Type*} [TopologicalSpace K] [ChartedSpace H K] [Group K]
  {Ad : Representation k K 𝔤} [IsLieAction Ad] {V : Type*} [AddCommGroup V] [Module k V]
  [LieRingModule 𝔤 V] [LieModule k 𝔤 V]

/-- A `(𝔤, K)`-module `M` is **compatible** with a map `ι : Lie K → 𝔤` when its `K`-action is
smooth on every finite-dimensional `K`-stable subspace with differential the action of `Lie K`
through `ι`. This is stated on matrix coefficients: each `g ↦ f (M.ρ g v)` is smooth, with
differential at `1` sending `X` to `f ⁅ι X, v⁆`. -/
structure IsCompatible (M : GKModule Ad V) (ι : GroupLieAlgebra I K →ₗ[ℝ] 𝔤) : Prop where
  /-- Every matrix coefficient of the `K`-action is smooth. -/
  contMDiff (f : Module.Dual k V) (v : V) : ContMDiff I 𝓘(ℝ, k) ∞ fun g ↦ f (M.ρ g v)
  /-- The differential of the `K`-action at `1` is the action of `Lie K` through `ι`. -/
  mfderiv_apply (f : Module.Dual k V) (v : V) (X : GroupLieAlgebra I K) :
    mfderiv I 𝓘(ℝ, k) (fun g ↦ f (M.ρ g v)) 1 X = f ⁅ι X, v⁆

section GeneralLinear

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A continuous endomorphism of `V` as an element of `𝔤𝔩(V)`. -/
noncomputable def toEndLie : (V →L[ℝ] V) →ₐ[ℝ] EndLie ℝ V :=
  (EndLie.equiv ℝ V).symm.toAlgHom.comp
    { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ ↦ rfl }

variable {V}

/-- A continuous endomorphism, as an element of `𝔤𝔩(V)`, corresponds to its underlying linear
map. -/
@[simp]
theorem toEndLie_apply (A : V →L[ℝ] V) :
    toEndLie V A = (EndLie.equiv ℝ V).symm (A : Module.End ℝ V) :=
  (rfl)

variable (V)

/-- The action of `GL(V)` on `𝔤𝔩(V)` by conjugation, `g • X = g X g⁻¹`. -/
noncomputable def glConj : Representation ℝ (V →L[ℝ] V)ˣ (EndLie ℝ V) where
  toFun g := LinearMap.mulLeft ℝ (toEndLie V g) ∘ₗ LinearMap.mulRight ℝ (toEndLie V ↑g⁻¹)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

variable {V}

/-- Conjugation by `g` sends `X` to `g X g⁻¹`. -/
@[simp]
theorem glConj_apply (g : (V →L[ℝ] V)ˣ) (X : EndLie ℝ V) :
    glConj V g X = toEndLie V g * X * toEndLie V ↑g⁻¹ := by
  simp only [glConj, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]

variable (V)

-- `LinearEquiv.lieConj` and `AlgEquiv.toLieEquiv` use the commutator Lie algebra structure on
-- `Module.End ℝ V`, which Mathlib provides only as a local instance.
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- Conjugation acts on `𝔤𝔩(V)` by Lie algebra endomorphisms: transported along
`TauCeti.EndLie.equiv`, it is Mathlib's conjugation `LinearEquiv.lieConj`. -/
instance instIsLieActionGlConj : IsLieAction (glConj V) :=
  .of_lieEquiv (fun g ↦ (EndLie.equiv ℝ V).toLieEquiv.trans
      ((ContinuousLinearEquiv.unitsEquiv ℝ V g).toLinearEquiv.lieConj.trans
        (EndLie.equiv ℝ V).toLieEquiv.symm)) fun g X ↦ (EndLie.equiv ℝ V).injective <| by
    ext v
    simp only [LieEquiv.trans_apply, AlgEquiv.toLieEquiv_apply, AlgEquiv.toLieEquiv_symm_apply,
      AlgEquiv.apply_symm_apply, LinearEquiv.lieConj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_apply, glConj_apply, map_mul, toEndLie_apply, mul_apply_eq_comp,
      ContinuousLinearMap.coe_coe]
    -- Mathlib has no lemma for the inverse of `ContinuousLinearEquiv.unitsEquiv ℝ V g`, which is
    -- `g⁻¹` by definition.
    rfl

variable [FiniteDimensional ℝ V]

/-- The defining representation of `GL(V)` on `V`, as a `(𝔤𝔩(V), GL(V))`-module. -/
noncomputable def glStd : GKModule (glConj V) V where
  ρ := (ContinuousLinearMap.toLinearMapRingHom : (V →L[ℝ] V) →+* Module.End ℝ V).toMonoidHom.comp
    (Units.coeHom _)
  map_lie g X v := by
    have hv : (↑g⁻¹ : V →L[ℝ] V) ((g : V →L[ℝ] V) v) = v := by
      rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
    simp [hv]
  isGFinite v := .of_finiteDimensional v

variable {V} in
/-- `GL(V)` acts on `V` by evaluation. -/
@[simp]
theorem glStd_ρ_apply (g : (V →L[ℝ] V)ˣ) (v : V) : (glStd V).ρ g v = (g : V →L[ℝ] V) v :=
  (rfl)

/-- The defining representation of `GL(V)` is compatible with the differentiated inclusion of
`GL(V)` in itself: its matrix coefficients `g ↦ f (g v)` are smooth, with differential
`X ↦ f (X v)` at `1`. -/
theorem isCompatible_glStd : (glStd V).IsCompatible
    ((toEndLie V).toLinearMap ∘ₗ ((MonoidHom.id (V →L[ℝ] V)ˣ).groupLieAlgebraMap
      𝓘(ℝ, V →L[ℝ] V) 𝓘(ℝ, V →L[ℝ] V)).toLinearMap) := by
  have key (f : Module.Dual ℝ V) (v : V) : (fun g : (V →L[ℝ] V)ˣ ↦ f ((glStd V).ρ g v)) =
      (LinearMap.toContinuousLinearMap f ∘L ContinuousLinearMap.apply ℝ V v) ∘ Units.val := by
    funext g
    simp
  refine ⟨fun f v ↦ ?_, fun f v X ↦ ?_⟩
  · rw [key]
    exact (ContinuousLinearMap.contMDiff _).comp Units.contMDiff_val
  · rw [key, ((ContinuousLinearMap.hasMFDerivAt _).comp 1 (Units.hasMFDerivAt_val 1)).mfderiv,
      MonoidHom.groupLieAlgebraMap_id]
    -- `GroupLieAlgebra 𝓘(ℝ, V →L[ℝ] V) (V →L[ℝ] V)ˣ` is `V →L[ℝ] V` only by definition, so
    -- `simp` cannot apply `LinearMap.comp_id` or `toEndLie_apply` across it; both sides are
    -- `f (X v)` by definition.
    rfl

end GeneralLinear

end TauCeti.GKModule
