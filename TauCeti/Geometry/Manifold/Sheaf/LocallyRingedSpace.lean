/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Morphisms between manifolds as locally ringed spaces

Mathlib views a smooth manifold `M` over a field `𝕜` as a locally ringed space
`ChartedSpace.locallyRingedSpace IM M`, whose structure sheaf is the sheaf of smooth functions
`M → 𝕜`, and a smooth map `f : M → N` as the morphism `ChartedSpace.locallyRingedSpaceMap f hf`,
which pulls back functions along `f`. This file proves the converse when `N` is
finite-dimensional and `𝕜` is complete: every morphism of locally ringed spaces
`φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N` which preserves values at points comes
from a unique smooth map, namely its underlying continuous map.

Preserving values (`ChartedSpace.PreservesValues`) means
`φ.stalkMap x ≫ evalHom x = evalHom (φ.base x)` for every `x`: the induced map of residue fields
`𝕜 → 𝕜` is the identity. This is the condition of a morphism of
locally `𝕜`-ringed spaces, and it is not automatic: on a one-point complex manifold, whose
structure sheaf is `ℂ`, complex conjugation is an endomorphism of the locally ringed space
which is not induced by any map. By the usual residue-field argument, it suffices to check the
condition on constant functions (`ChartedSpace.stalkMap_evalHom_of_forall_C`).

Given this condition, a section `g` of the structure sheaf of `N` is sent to `g ∘ φ.base`
(`ChartedSpace.locallyRingedSpace_c_app_apply`): the germ of `φ.c.app (op V) g` at `x` is the
image of the germ of `g` under the stalk map, so they have the same value. Applied to the chart
coordinates `ℓ ∘ extChartAt IN y` for continuous linear functionals `ℓ`, this shows that the
coordinates of `φ.base` in a chart are smooth, so `φ.base` is smooth
(`ChartedSpace.contMDiff_base`). Since both morphisms act on sections by composition, `φ` is the
morphism induced by `φ.base` (`ChartedSpace.eq_locallyRingedSpaceMap`).

## Main declarations

* `ChartedSpace.PreservesValues`: the morphisms inducing the identity on residue fields; this
  holds for identities, compositions and `locallyRingedSpaceMap`.
* `ChartedSpace.contMDiff_base`: the underlying map of a value-preserving morphism is smooth.
* `ChartedSpace.eq_locallyRingedSpaceMap`: such a morphism is induced by its underlying map.
* `ChartedSpace.locallyRingedSpaceMapEquiv`: smooth maps `M → N` correspond bijectively to
  value-preserving morphisms of locally ringed spaces, compatibly with identities and
  composition.

For `𝕜 = ℂ` the smooth functions and maps are the holomorphic ones;
`TauCeti.holomorphicMapLocalRingedEquiv` restates the correspondence for holomorphic maps.

## References

* The locally ringed spaces and their morphisms are those of
  `Mathlib/Geometry/Manifold/Sheaf/LocallyRingedSpace.lean`, by Heather Macbeth, whose TODO list
  asks for this converse.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Chapter 1, for `ℂ`-ringed spaces and
  the description of their morphisms between manifolds by pullback of functions.
-/

public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners 𝕜 EN HN}
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type u} [TopologicalSpace P] [ChartedSpace HP P]

namespace ChartedSpace

/-- A morphism of locally ringed spaces between manifolds *preserves values* if at every point `x`
its stalk map followed by evaluation at `x` is evaluation at the image of `x`, that is, it induces
the identity on the residue fields `𝕜`. These are the morphisms of locally `𝕜`-ringed spaces. -/
def PreservesValues (φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N) : Prop :=
  ∀ x : M, φ.stalkMap x ≫ smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
    smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (φ.base x)

/-- Unfolding `PreservesValues` into its pointwise condition. -/
theorem preservesValues_iff (φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N) :
    PreservesValues φ ↔ ∀ x : M, φ.stalkMap x ≫ smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (φ.base x) :=
  Iff.rfl

/-- The morphism induced by a smooth map preserves values. -/
theorem preservesValues_locallyRingedSpaceMap (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    PreservesValues (locallyRingedSpaceMap f hf) :=
  stalkMap_locallyRingedSpaceMap_evalHom f hf

/-- The identity morphism preserves values. -/
theorem preservesValues_id : PreservesValues (𝟙 (locallyRingedSpace IM M)) :=
  locallyRingedSpace_id IM M ▸ preservesValues_locallyRingedSpaceMap id contMDiff_id

/-- A composition of value-preserving morphisms preserves values. -/
theorem PreservesValues.comp {φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N}
    {ψ : locallyRingedSpace IN N ⟶ locallyRingedSpace IP P} (hφ : PreservesValues φ)
    (hψ : PreservesValues ψ) : PreservesValues (φ ≫ ψ) := fun x ↦ by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (ψ.stalkMap (φ.base x) ≫ ·) (hφ x)).trans (hψ (φ.base x)))


/-- A morphism of locally ringed spaces between manifolds that preserves values at points acts on
sections by composition with its underlying map. -/
theorem locallyRingedSpace_c_app_apply
    (φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N)
    (hφ : PreservesValues φ)
    {V : Opens N} (g : (smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.obj (op V))
    {x : M} (hx : φ.base x ∈ V) :
    (φ.c.app (op V) g).1 ⟨x, hx⟩ = g ⟨φ.base x, hx⟩ := by
  have h := congr($(hφ x) ((locallyRingedSpace IN N).presheaf.germ V (φ.base x) hx g))
  rw [CommRingCat.comp_apply, LocallyRingedSpace.stalkMap_germ_apply] at h
  exact (smoothSheafCommRing.evalHom_germ IM 𝓘(𝕜) M 𝕜 _ x hx _).symm.trans
    (h.trans (smoothSheafCommRing.evalHom_germ IN 𝓘(𝕜) N 𝕜 V _ hx g))

/-- The chart coordinate `ℓ ∘ extChartAt IN y`, as a smooth function on the chart domain. -/
private def chartCoordinateSection [IsManifold IN ∞ N] (y : N) (ℓ : EN →L[𝕜] 𝕜) :
    (smoothSheafCommRing IN 𝓘(𝕜) N 𝕜).presheaf.obj (op ⟨(chartAt HN y).source,
      (chartAt HN y).open_source⟩) :=
  ⟨fun z ↦ ℓ (extChartAt IN y z), fun z ↦ contMDiffAt_subtype_iff.mpr <|
    ℓ.contMDiffAt.comp _ ((contMDiffOn_extChartAt (n := ∞)).contMDiffAt
      ((chartAt HN y).open_source.mem_nhds z.2))⟩

/-- The underlying map of a morphism of locally ringed spaces between manifolds that preserves
values at points is smooth, when the target is finite-dimensional. -/
theorem contMDiff_base [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EN] [IsManifold IN ∞ N]
    (φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N)
    (hφ : PreservesValues φ) :
    ContMDiff (M := M) (M' := N) IM IN ∞ φ.base := by
  intro x
  -- Name the underlying map with its manifold types, so that the charted-space instances apply.
  obtain ⟨f, hf⟩ : ∃ f : M → N, ⇑φ.base = f := ⟨_, rfl⟩
  rw [hf, contMDiffAt_iff_target]
  refine ⟨hf ▸ φ.base.hom.continuous.continuousAt, ?_⟩
  have hx : φ.base x ∈ (⟨(chartAt HN (f x)).source, (chartAt HN (f x)).open_source⟩ : Opens N) :=
    hf ▸ mem_chart_source HN (f x)
  have key (ℓ : EN →L[𝕜] 𝕜) :
      ContMDiffAt IM 𝓘(𝕜) ∞ (fun z ↦ ℓ (extChartAt IN (f x) (f z))) x := by
    have h : ContMDiffAt IM 𝓘(𝕜) ∞ (φ.c.app _ (chartCoordinateSection (f x) ℓ)).1 ⟨x, hx⟩ :=
      (φ.c.app _ (chartCoordinateSection (f x) ℓ)).2 ⟨x, hx⟩
    refine contMDiffAt_subtype_iff.mp (h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_))
    intro z
    refine ((locallyRingedSpace_c_app_apply φ hφ _ z.2).trans ?_).symm
    simp [chartCoordinateSection, hf]
  let b := Module.finBasis 𝕜 EN
  have hpi : ContMDiffAt IM 𝓘(𝕜, Fin (Module.finrank 𝕜 EN) → 𝕜) ∞
      (fun z ↦ b.equivFunL (extChartAt IN (f x) (f z))) x :=
    contMDiffAt_pi_module_iff.mpr fun i ↦
      key ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  convert (b.equivFunL.symm.toContinuousLinearMap.contMDiffAt).comp x hpi using 1
  ext z
  simp

/-- A morphism of locally ringed spaces between manifolds that preserves values at points is the
morphism induced by its underlying smooth map, when the target is finite-dimensional. -/
theorem eq_locallyRingedSpaceMap [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EN] [IsManifold IN ∞ N]
    (φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N)
    (hφ : PreservesValues φ) :
    φ = locallyRingedSpaceMap (M := M) (N := N) φ.base (contMDiff_base φ hφ) := by
  -- The two base maps agree definitionally, so the transport between them is the identity and
  -- the sheaf maps can be compared section by section.
  refine LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ rfl ?_)
  ext V g
  refine Subtype.ext (funext fun z ↦ ?_)
  exact locallyRingedSpace_c_app_apply φ hφ g z.2

/-- A morphism of locally ringed spaces between manifolds preserves values at a point `x` as soon
as it preserves the values of the germs of constant functions at `x`. -/
theorem stalkMap_evalHom_of_forall_C
    (φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N) (x : M)
    (h : ∀ c : 𝕜, smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x (φ.stalkMap x
      ((locallyRingedSpace IN N).presheaf.germ ⊤ (φ.base x) trivial
        (ContMDiffMap.C c : C^∞⟮IN, (⊤ : Opens N); 𝕜⟯))) = c) :
    φ.stalkMap x ≫ smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (φ.base x) := by
  ext s
  -- `smoothSheafCommRing.eval` is by definition the ring map underlying `evalHom`, and is the
  -- form used by `smoothSheafCommRing.isUnit_stalk_iff`.
  change smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x (φ.stalkMap x s) =
    smoothSheafCommRing.eval IN 𝓘(𝕜) N 𝕜 (φ.base x) s
  set k := (locallyRingedSpace IN N).presheaf.germ ⊤ (φ.base x) trivial
    (ContMDiffMap.C (smoothSheafCommRing.eval IN 𝓘(𝕜) N 𝕜 (φ.base x) s) :
      C^∞⟮IN, (⊤ : Opens N); 𝕜⟯)
  have hk : smoothSheafCommRing.eval IN 𝓘(𝕜) N 𝕜 (φ.base x) k =
      smoothSheafCommRing.eval IN 𝓘(𝕜) N 𝕜 (φ.base x) s :=
    smoothSheafCommRing.eval_germ (IM := IN) (I := 𝓘(𝕜)) (M := N) ⊤ (φ.base x) trivial _
  have hs : ¬IsUnit (s - k) := by
    rw [smoothSheafCommRing.isUnit_stalk_iff, not_not, RingHom.mem_ker, map_sub, hk, sub_self]
  have hφs : ¬IsUnit (φ.stalkMap x (s - k)) := fun hu ↦ hs (isUnit_of_map_unit _ _ hu)
  rw [smoothSheafCommRing.isUnit_stalk_iff, not_not, RingHom.mem_ker, map_sub, map_sub,
    sub_eq_zero] at hφs
  exact hφs.trans (h _)

/-- Smooth maps `M → N` into a finite-dimensional manifold are the morphisms of locally ringed
spaces `locallyRingedSpace IM M ⟶ locallyRingedSpace IN N` which preserve values at points: a
smooth map gives `locallyRingedSpaceMap`, and a morphism gives its underlying map. -/
def locallyRingedSpaceMapEquiv [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EN] [IsManifold IN ∞ N] :
    C^∞⟮IM, M; IN, N⟯ ≃
      {φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N // PreservesValues φ} where
  toFun f := ⟨locallyRingedSpaceMap f f.contMDiff, preservesValues_locallyRingedSpaceMap f _⟩
  invFun φ := ⟨φ.1.base, contMDiff_base φ.1 φ.2⟩
  left_inv _ := rfl
  right_inv φ := Subtype.ext (eq_locallyRingedSpaceMap φ.1 φ.2).symm

/-- The morphism of locally ringed spaces attached to a smooth map is `locallyRingedSpaceMap`. -/
@[simp]
theorem locallyRingedSpaceMapEquiv_apply_coe [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EN]
    [IsManifold IN ∞ N] (f : C^∞⟮IM, M; IN, N⟯) :
    (locallyRingedSpaceMapEquiv f).1 = locallyRingedSpaceMap f f.contMDiff := (rfl)

/-- The smooth map attached to a value-preserving morphism is its underlying map. -/
@[simp]
theorem coe_locallyRingedSpaceMapEquiv_symm_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EN]
    [IsManifold IN ∞ N]
    (φ : {φ : locallyRingedSpace IM M ⟶ locallyRingedSpace IN N // PreservesValues φ}) :
    ⇑(locallyRingedSpaceMapEquiv.symm φ) = φ.1.base := (rfl)

/-- The identity map corresponds to the identity morphism. -/
theorem locallyRingedSpaceMapEquiv_id [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EM]
    [IsManifold IM ∞ M] :
    (locallyRingedSpaceMapEquiv (ContMDiffMap.id : C^∞⟮IM, M; IM, M⟯)).1 =
      𝟙 (locallyRingedSpace IM M) :=
  locallyRingedSpace_id IM M

/-- A composition of smooth maps corresponds to the composition of morphisms. -/
theorem locallyRingedSpaceMapEquiv_comp [CompleteSpace 𝕜] [FiniteDimensional 𝕜 EN]
    [IsManifold IN ∞ N] [FiniteDimensional 𝕜 EP] [IsManifold IP ∞ P]
    (g : C^∞⟮IN, N; IP, P⟯) (f : C^∞⟮IM, M; IN, N⟯) :
    (locallyRingedSpaceMapEquiv (g.comp f)).1 =
      (locallyRingedSpaceMapEquiv f).1 ≫ (locallyRingedSpaceMapEquiv g).1 :=
  locallyRingedSpace_comp IP f.contMDiff g.contMDiff

end ChartedSpace
