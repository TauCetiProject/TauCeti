/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# The almost complex structure of a complex manifold

A complex manifold `M` modelled on `𝓘(ℂ, E)` is, with the same charts, a real manifold modelled on
`𝓘(ℝ, E)` (`TauCeti.ComplexManifold.isManifold_real`). Its tangent spaces are the complex vector
space `E`, and multiplication by `i` on them is a smooth almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M` of the underlying real manifold: in
the tangent coordinates of any two holomorphic charts it is multiplication by `i` again, because
the derivatives of holomorphic coordinate changes are complex linear.

This is the almost complex structure through which the type decomposition of complex-valued forms
and the operators `∂` and `∂bar` of `TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic`
apply to complex manifolds. Two properties tie it to the complex structure:

* a map between complex manifolds is pseudoholomorphic for these structures exactly when it is
  holomorphic, within a set at a point, at a point, on a set, or everywhere; that is, a map is
  holomorphic exactly when its real differential is complex linear;
* the structure is integrable: its Nijenhuis tensor vanishes. In a holomorphic chart it is the
  constant structure given by multiplication by `i`, and the Nijenhuis expression of a constant
  structure on a vector space vanishes identically.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`: the almost complex structure of a
  complex manifold.
* `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold_apply`: it acts on each tangent space as
  multiplication by `i`.
* `TauCeti.isPseudoholomorphicAt_ofComplexManifold_iff` and its variants within a set, on a set
  and everywhere: pseudoholomorphic maps between complex manifolds are the holomorphic maps.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_ofComplexManifold`: the almost complex structure
  of a complex manifold is integrable.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume II,
  Chapter IX, Section 2.
-/

public section

open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

namespace SmoothAlmostComplexStructure

variable (E M) in
/-- The almost complex structure of a complex manifold `M` modelled on `𝓘(ℂ, E)`, as a smooth
almost complex structure of the underlying real manifold modelled on `𝓘(ℝ, E)`: on every tangent
space, which is `E`, it is multiplication by `i` (`ofComplexManifold_apply`). -/
def ofComplexManifold : SmoothAlmostComplexStructure 𝓘(ℝ, E) M where
  toEndomorphism :=
    ⟨fun _ ↦ Complex.I • ContinuousLinearMap.id ℝ E, fun x₀ ↦ by
      -- In the tangent coordinates at `x₀`, the section is constantly multiplication by `I` near
      -- `x₀`, since the real coordinate changes are complex linear.
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, (contMDiffAt_const (c := Complex.I • ContinuousLinearMap.id ℝ E))
        |>.congr_of_eventuallyEq ?_⟩
      filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with x hx
      refine (inTangentCoordinates_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) id id
        (fun x : M ↦ (Complex.I • ContinuousLinearMap.id ℝ E :
          TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x)) hx hx).trans
        (ContinuousLinearMap.ext fun v ↦ ?_)
      have hx' : x ∈ (extChartAt 𝓘(ℝ, E) x₀).source ∩ (extChartAt 𝓘(ℝ, E) x).source ∩
          (extChartAt 𝓘(ℝ, E) x₀).source := by
        simp [hx]
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
      exact (tangentCoordChange_smul ℝ (𝕜' := ℂ) ⟨mem_chart_source E x, hx⟩ _ _).trans
        (congrArg (Complex.I • ·)
          ((tangentCoordChange_comp hx').trans (tangentCoordChange_self (by simp [hx]))))⟩
  square_neg x := ContinuousLinearMap.ext fun v ↦ by
    simp only [ContinuousLinearMap.comp_apply]
    -- The tangent space at `x` is the model space `E`, where `I • I • w = -w`.
    have h (w : E) : Complex.I • Complex.I • w = -w := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    exact h v

/-- The almost complex structure of a complex manifold is multiplication by `i` on every tangent
space. -/
@[simp]
theorem ofComplexManifold_apply (x : M) (v : E) : ofComplexManifold E M x v = Complex.I • v :=
  (rfl)

end SmoothAlmostComplexStructure

open SmoothAlmostComplexStructure

/-! ### Pseudoholomorphic maps are holomorphic maps -/

section Pseudoholomorphic

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] [IsManifold 𝓘(ℂ, E') ∞ N]
  {f : M → N} {s : Set M} {x : M}

/-- A map between complex manifolds is pseudoholomorphic within a set at a point, for their
almost complex structures, exactly when it is holomorphic within that set at that point. -/
@[simp]
theorem isPseudoholomorphicWithinAt_ofComplexManifold_iff :
    IsPseudoholomorphicWithinAt (ofComplexManifold E M) (ofComplexManifold E' N) f s x ↔
      MDifferentiableWithinAt 𝓘(ℂ, E) 𝓘(ℂ, E') f s x := by
  rw [isPseudoholomorphicWithinAt_iff_isComplexLinearMap]
  constructor
  · rintro ⟨u, hu, hJ⟩
    have hJ' (w : TangentSpace 𝓘(ℝ, E) x) :
        u (ofComplexManifold E M x w) = ofComplexManifold E' N (f x) (u w) := by
      have h := (isComplexLinearMap_iff_apply _ _ _).mp hJ w
      rwa [almostComplexStructureAt_apply, almostComplexStructureAt_apply] at h
    -- Read the real derivative between the model spaces, where multiplication by `I` acts; there
    -- it commutes with `I`, so it is complex linear.
    let u₀ : E →L[ℝ] E' := u
    -- By `ofComplexManifold_apply`, both structures act on `E` and `E'` as multiplication by `I`.
    have hI (w : E) : u₀ (Complex.I • w) = Complex.I • u₀ w := by
      have h := hJ' w
      rwa [ofComplexManifold_apply (E := E) x w,
        ofComplexManifold_apply (E := E') (f x) (u w)] at h
    -- Read in the model spaces, `complexOfMapISmul` with scalars restricted to `ℝ` is `u₀`.
    exact (hu.of_restrictScalars ℝ (f' := u₀.complexOfMapISmul hI)
      (by ext w; exact congrFun (u₀.coe_complexOfMapISmul hI) w)).mdifferentiableWithinAt
  · intro h
    -- The complex derivative, regarded as a real linear map between the real tangent spaces.
    let u : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E') (f x) :=
      (mfderivWithin 𝓘(ℂ, E) 𝓘(ℂ, E') f s x).restrictScalars ℝ
    refine ⟨u, h.hasMFDerivWithinAt.restrictScalars ℝ rfl,
      (isComplexLinearMap_iff_apply _ _ _).mpr fun w ↦ ?_⟩
    rw [almostComplexStructureAt_apply, almostComplexStructureAt_apply]
    exact (congrArg u (ofComplexManifold_apply (E := E) x w)).trans
      (((mfderivWithin 𝓘(ℂ, E) 𝓘(ℂ, E') f s x).map_smul Complex.I w).trans
        (ofComplexManifold_apply (E := E') (f x) (u w)).symm)

/-- A map between complex manifolds is pseudoholomorphic at a point, for their almost complex
structures, exactly when it is holomorphic at that point. -/
@[simp]
theorem isPseudoholomorphicAt_ofComplexManifold_iff :
    IsPseudoholomorphicAt (ofComplexManifold E M) (ofComplexManifold E' N) f x ↔
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E') f x := by
  rw [← isPseudoholomorphicWithinAt_univ, isPseudoholomorphicWithinAt_ofComplexManifold_iff,
    mdifferentiableWithinAt_univ]

/-- A map between complex manifolds is pseudoholomorphic on a set, for their almost complex
structures, exactly when it is holomorphic on that set. -/
@[simp]
theorem isPseudoholomorphicOn_ofComplexManifold_iff :
    IsPseudoholomorphicOn (ofComplexManifold E M) (ofComplexManifold E' N) f s ↔
      MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, E') f s :=
  isPseudoholomorphicOn_iff.trans
    (forall₂_congr fun _ _ ↦ isPseudoholomorphicWithinAt_ofComplexManifold_iff)

/-- A map between complex manifolds is pseudoholomorphic, for their almost complex structures,
exactly when it is holomorphic. -/
@[simp]
theorem isPseudoholomorphic_ofComplexManifold_iff :
    IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' N) f ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E') f :=
  isPseudoholomorphic_iff.trans (forall_congr' fun _ ↦ isPseudoholomorphicAt_ofComplexManifold_iff)

end Pseudoholomorphic

/-! ### Integrability -/

namespace SmoothAlmostComplexStructure

/-- In the chart at `x`, the coordinate expression of the vector field `J V` is `I` times that of
`V`, since the real tangent coordinate changes are complex linear. -/
private lemma mpullbackWithin_ofComplexManifold_eventuallyEq
    (V : Π x : M, TangentSpace 𝓘(ℝ, E) x) (x : M) :
    mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x).symm
        (fun y ↦ ofComplexManifold E M y (V y)) (range 𝓘(ℝ, E)) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, E) x x)]
      fun z ↦ (Complex.I • ContinuousLinearMap.id ℝ E)
        (mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x).symm V (range 𝓘(ℝ, E)) z) := by
  filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) x] with z hz
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ (extChartAt 𝓘(ℝ, E) x).source, extChartAt 𝓘(ℝ, E) x y = z :=
    ⟨_, (extChartAt _ x).map_target hz, (extChartAt _ x).right_inv hz⟩
  rw [mpullbackWithin_extChartAt_symm_apply _ hy, mpullbackWithin_extChartAt_symm_apply _ hy,
    TangentBundle.trivializationAt_apply_tangentCoordChange,
    TangentBundle.trivializationAt_apply_tangentCoordChange]
  have h : y ∈ (chartAt E y).source ∩ (chartAt E x).source := by
    simpa using hy
  rw [smul_apply, ContinuousLinearMap.id_apply]
  exact (congrArg (tangentCoordChange 𝓘(ℝ, E) y x y)
    (ofComplexManifold_apply (E := E) y (V y))).trans (tangentCoordChange_smul ℝ (𝕜' := ℂ) h _ _)

variable [FiniteDimensional ℂ E]

/-- **The almost complex structure of a complex manifold is integrable**: its Nijenhuis tensor
vanishes. -/
@[simp]
theorem nijenhuis_ofComplexManifold : (ofComplexManifold E M).nijenhuis = 0 := by
  rw [nijenhuis_eq_zero_iff]
  intro X Y x hX hY
  -- Compute the four Lie brackets at `x` in the chart at `x`, where `J` is the constant
  -- structure `L` given by multiplication by `I`.
  let pb : (Π y : M, TangentSpace 𝓘(ℝ, E) y) → E → E := fun V ↦
    mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x).symm V (range 𝓘(ℝ, E))
  let z₀ := extChartAt 𝓘(ℝ, E) x x
  let L : E →L[ℝ] E := Complex.I • ContinuousLinearMap.id ℝ E
  have hbr (V W : Π y : M, TangentSpace 𝓘(ℝ, E) y) :
      mlieBracket 𝓘(ℝ, E) V W x = lieBracketWithin ℝ (pb V) (pb W) (range 𝓘(ℝ, E)) z₀ := by
    have h := lieBracketWithin_mpullbackWithin_extChartAt_symm (𝕜 := ℝ) V W univ x
    rw [preimage_univ, univ_inter, mlieBracketWithin_univ] at h
    exact h.symm
  have hd {V : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hV : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun y ↦ (V y : TangentBundle 𝓘(ℝ, E) M)) x) :
      DifferentiableWithinAt ℝ (pb V) (range 𝓘(ℝ, E)) z₀ := by
    simpa only [preimage_univ, univ_inter] using
      (hV.mdifferentiableWithinAt (s := univ)).differentiableWithinAt_mpullbackWithin_vectorField
  have hJ (V : Π y : M, TangentSpace 𝓘(ℝ, E) y) :
      pb (fun y ↦ ofComplexManifold E M y (V y)) =ᶠ[𝓝 z₀] fun z ↦ L (pb V z) :=
    mpullbackWithin_ofComplexManifold_eventuallyEq V x
  have hL {V : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hV : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun y ↦ (V y : TangentBundle 𝓘(ℝ, E) M)) x) :
      fderivWithin ℝ (fun z ↦ L (pb V z)) (range 𝓘(ℝ, E)) z₀ =
        L.comp (fderivWithin ℝ (pb V) (range 𝓘(ℝ, E)) z₀) :=
    (L.hasFDerivAt.comp_hasFDerivWithinAt z₀ (hd hV).hasFDerivWithinAt).fderivWithin
      (𝓘(ℝ, E).uniqueDiffOn _ (mem_range_self _))
  rw [hbr, hbr, hbr, hbr, (hJ X).lieBracketWithin_vectorField_eq_nhds (hJ Y),
    (hJ X).lieBracketWithin_vectorField_eq_nhds EventuallyEq.rfl,
    EventuallyEq.rfl.lieBracketWithin_vectorField_eq_nhds (hJ Y)]
  simp only [lieBracketWithin_eq, hL hX, hL hY]
  -- What remains is linear algebra for the real-linear derivatives `DA`, `DB` of the coordinate
  -- expressions of `X` and `Y` and the constant structure `L`, using only `L ∘ L = -1`.
  have key (DA DB : E →L[ℝ] E) (a b : E) :
      L (DB (L a)) - L (DA (L b)) =
        DB a - DA b + L (DB (L a) - L (DA b)) + L (L (DB a) - DA (L b)) := by
    simp only [L, smul_apply, ContinuousLinearMap.id_apply, smul_sub,
      smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  exact key _ _ _ _

end SmoothAlmostComplexStructure

end TauCeti
