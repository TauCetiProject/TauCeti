/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.RepresentationTheory.GKModule.Basic

/-!
# Compatible `(𝔤, K)`-modules

Let `K` be a Lie group modelled on `I` over `ℝ`, let `𝔤` be a Lie algebra over a normed field
extension `k` of `ℝ` (in the analytic theory `k = ℂ` and `𝔤` is a complexified Lie algebra) and let
`ι : Lie K → 𝔤` be the differentiated inclusion: for a Lie group `G` containing `K` through
`j : K →* G`, this is `TauCeti.GKModule.lieInclusion j c`, the differential of `j` at `1` followed
by a linear map `c : Lie G → 𝔤` (in the analytic theory, the inclusion of `Lie G` into its
complexification). A `(𝔤, K)`-module `M` in the sense of harmonic
analysis is a `TauCeti.GKModule` whose `K`-action is smooth on each finite-dimensional `K`-stable
subspace, with differential the action of `Lie K` through `ι`.

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

* `TauCeti.GKModule.lieInclusion j c`: the differentiated inclusion `Lie K → 𝔤` of a Lie group
  homomorphism `j : K →* G`, followed by `c : Lie G → 𝔤`.
* `TauCeti.GKModule.IsCompatible M ι`: the `K`-action of `M` is smooth on finite-dimensional
  `K`-stable subspaces, with differential the action of `Lie K` through `ι`.
* `TauCeti.GKModule.EndLie V`: `End(V)` as the Lie algebra `𝔤𝔩(V)` acting on `V`.
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

section LieInclusion

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {G : Type*} [TopologicalSpace G] [ChartedSpace H' G] [Group G]

/-- The **differentiated inclusion** `Lie K → 𝔤` of a Lie group pair: the differential at `1` of
a homomorphism `j : K →* G` (the inclusion of `K` in the Lie group `G`), followed by a linear map
`c : Lie G → 𝔤`, such as the inclusion of `Lie G` into its complexification. A `(𝔤, K)`-module in
the sense of harmonic analysis for the pair `(G, K)` is one with
`M.IsCompatible (lieInclusion j c)`. -/
noncomputable def lieInclusion (j : K →* G) (c : GroupLieAlgebra I' G →ₗ[ℝ] 𝔤) :
    GroupLieAlgebra I K →ₗ[ℝ] 𝔤 :=
  c ∘ₗ (show E →L[ℝ] E' from mfderiv I I' j 1).toLinearMap

theorem lieInclusion_apply (j : K →* G) (c : GroupLieAlgebra I' G →ₗ[ℝ] 𝔤)
    (X : GroupLieAlgebra I K) : lieInclusion j c X = c (mfderiv I I' j 1 X) :=
  (rfl)

end LieInclusion

section GeneralLinear

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `End(V)` as the Lie algebra `𝔤𝔩(V)`, with the commutator bracket, acting on `V`. -/
-- The body is exposed so that the algebraic structure of `Module.End ℝ V` and its action on `V`
-- transfer to the synonym.
@[expose] def EndLie : Type _ := Module.End ℝ V

noncomputable instance instRingEndLie : Ring (EndLie V) := inferInstanceAs (Ring (Module.End ℝ V))
noncomputable instance instAlgebraEndLie : Algebra ℝ (EndLie V) :=
  inferInstanceAs (Algebra ℝ (Module.End ℝ V))
noncomputable instance instLieRingEndLie : LieRing (EndLie V) := LieRing.ofAssociativeRing
noncomputable instance instLieAlgebraEndLie : LieAlgebra ℝ (EndLie V) :=
  LieAlgebra.ofAssociativeAlgebra
noncomputable instance instLieRingModuleEndLie : LieRingModule (EndLie V) V :=
  Module.End.instLieRingModule
noncomputable instance instLieModuleEndLie : LieModule ℝ (EndLie V) V :=
  Module.End.instLieModule

/-- A continuous endomorphism of `V` as an element of `𝔤𝔩(V)`. -/
noncomputable def toEndLie : (V →L[ℝ] V) →ₐ[ℝ] EndLie V :=
  { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ ↦ rfl }

variable {V} in
/-- An element of `𝔤𝔩(V)` acts on `V` by evaluation. -/
@[simp]
theorem EndLie.lie_apply (X : EndLie V) (v : V) :
    ⁅X, v⁆ = (show Module.End ℝ V from X) v := (rfl)

/-- The action of `GL(V)` on `𝔤𝔩(V)` by conjugation, `g • X = g X g⁻¹`. -/
noncomputable def glConj : Representation ℝ (V →L[ℝ] V)ˣ (EndLie V) where
  toFun g := LinearMap.mulLeft ℝ (toEndLie V g) ∘ₗ LinearMap.mulRight ℝ (toEndLie V ↑g⁻¹)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

/-- Conjugation by `g` sends `X` to `g X g⁻¹`. -/
theorem glConj_apply (g : (V →L[ℝ] V)ˣ) (X : EndLie V) :
    glConj V g X = toEndLie V g * X * toEndLie V ↑g⁻¹ := by
  simp [glConj, mul_assoc]

/-- Conjugation acts on `𝔤𝔩(V)` by Lie algebra endomorphisms. -/
instance instIsLieActionGlConj : IsLieAction (glConj V) where
  map_lie g X Y := by
    have h : toEndLie V ↑g⁻¹ * toEndLie V g = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    simp only [glConj_apply, LieRing.of_associative_ring_bracket, mul_sub, sub_mul, mul_assoc]
    simp only [← mul_assoc (toEndLie V ↑g⁻¹) (toEndLie V g), h, one_mul]

variable [FiniteDimensional ℝ V]

/-- The defining representation of `GL(V)` on `V`, as a `(𝔤𝔩(V), GL(V))`-module. -/
noncomputable def glStd : GKModule (glConj V) V where
  ρ := (ContinuousLinearMap.toLinearMapRingHom : (V →L[ℝ] V) →+* Module.End ℝ V).toMonoidHom.comp
    (Units.coeHom _)
  map_lie g X v := by
    have hv : (↑g⁻¹ : V →L[ℝ] V) ((g : V →L[ℝ] V) v) = v := congrArg (· v) (Units.inv_mul g)
    exact congrArg (fun w ↦ (g : V →L[ℝ] V) ((show Module.End ℝ V from X) w)) hv.symm
  isGFinite v := .of_finiteDimensional v

/-- The defining representation of `GL(V)` is compatible with the differentiated inclusion of
`GL(V)` in itself: its matrix coefficients `g ↦ f (g v)` are smooth, with differential
`X ↦ f (X v)` at `1`. -/
theorem isCompatible_glStd : (glStd V).IsCompatible (I := 𝓘(ℝ, V →L[ℝ] V))
    (lieInclusion (I' := 𝓘(ℝ, V →L[ℝ] V)) (MonoidHom.id _) (toEndLie V).toLinearMap) := by
  have key (f : Module.Dual ℝ V) (v : V) : (fun g : (V →L[ℝ] V)ˣ ↦ f ((glStd V).ρ g v)) =
      (LinearMap.toContinuousLinearMap f ∘L ContinuousLinearMap.apply ℝ V v) ∘ Units.val :=
    rfl
  have hval : HasMFDerivAt 𝓘(ℝ, V →L[ℝ] V) 𝓘(ℝ, V →L[ℝ] V) (Units.val : (V →L[ℝ] V)ˣ → _) 1
      (ContinuousLinearMap.id ℝ _) := by
    refine ⟨Units.continuous_val.continuousAt, ?_⟩
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, modelWithCornersSelf_coe,
      Set.range_id, hasFDerivWithinAt_univ]
    refine (hasFDerivAt_id _).congr_of_eventuallyEq ?_
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨1, rfl⟩] with _ ⟨u, hu⟩
    subst hu
    exact congrArg Units.val ((extChartAt 𝓘(ℝ, V →L[ℝ] V) (1 : (V →L[ℝ] V)ˣ)).left_inv
      (by simp))
  refine ⟨fun f v ↦ ?_, fun f v X ↦ ?_⟩
  · rw [key]
    exact (ContinuousLinearMap.contMDiff _).comp Units.contMDiff_val
  · rw [key, ((ContinuousLinearMap.hasMFDerivAt _).comp 1 hval).mfderiv]
    have hid : mfderiv 𝓘(ℝ, V →L[ℝ] V) 𝓘(ℝ, V →L[ℝ] V) (MonoidHom.id (V →L[ℝ] V)ˣ) 1 =
        ContinuousLinearMap.id ℝ _ := by
      rw [MonoidHom.coe_id]
      exact mfderiv_id
    refine Eq.trans ?_ (congrArg (fun Y ↦ f ⁅Y, v⁆) (lieInclusion_apply _ _ X)).symm
    exact congrArg (fun A ↦ f ⁅(toEndLie V).toLinearMap A, v⁆) (congrArg (· X) hid).symm

end GeneralLinear

end TauCeti.GKModule
