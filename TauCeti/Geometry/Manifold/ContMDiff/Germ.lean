/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Germ
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Analytic germs under changes of charts

The scalar analytic germ rings in two analytic charts at the same manifold point are
canonically isomorphic. `ModelWithCorners.analyticGermsEquiv` is pullback by the analytic
change of extended charts. It has an explicit representative formula, reverses when the
charts are exchanged, and satisfies the identity and cocycle laws. Thus local analytic
functions can be transported without retaining a particular chart or neighborhood.

For a scalar analytic function on the manifold,
`analyticGermsEquiv_ofAnalyticAt_comp_extend_symm_of_contMDiffAt` identifies its two chart
representatives. In particular, equality of the local functions can be tested
in either chart.

The model is boundaryless so that the transition domains are neighborhoods in the full
normed model space. No finite-dimensionality or countability assumption is needed.
The construction uses `TauCeti.analyticGerms.pullback` and its local-inverse equivalence;
complexification compatibility is consequently given by
`TauCeti.analyticGerms.complexify_pullback` for real finite-coordinate models.

We also define `TauCeti.AnalyticMapGerm I J x y`, the type of germs along `𝓝 x` of maps `X → Y`
analytic near `x` and sending `x` to `y` (requiring neither boundarylessness nor any manifold
assumption), together with its constructor `AnalyticMapGerm.mk`, representative extraction
`AnalyticMapGerm.exists_mk`, convergence `AnalyticMapGerm.tendsto`, identity `AnalyticMapGerm.id`,
and composition `AnalyticMapGerm.comp`.
-/

public section

open Filter Function IsManifold Topology
open scoped ContDiff Manifold

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {e e' e'' : OpenPartialHomeomorph M H} {x : M}

/-- Pullback by a change of analytic charts identifies the analytic germ rings at the two
coordinates of the same point. The direction is from the second chart to the first. -/
def analyticGermsEquiv (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    TauCeti.analyticGerms 𝕜 (I (e' x)) ≃+* TauCeti.analyticGerms 𝕜 (I (e x)) :=
  TauCeti.analyticGerms.equivOfInverse (I.extendCoordChange e e') (I.extendCoordChange e' e)
    (I.analyticAt_extendCoordChange he he' hx hx')
    (I.analyticAt_extendCoordChange he' he hx' hx)
    (I.extendCoordChange_apply hx)
    (by
      filter_upwards [I.extendCoordChange_source_mem_nhds hx hx'] with y hy
      exact (I.extendCoordChange e e').left_inv hy)
    (by
      filter_upwards [I.extendCoordChange_source_mem_nhds hx' hx] with y hy
      exact (I.extendCoordChange e' e).left_inv hy)

/-- Chart transport acts by analytic pullback along the transition map. -/
@[simp]
theorem analyticGermsEquiv_apply (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (φ : TauCeti.analyticGerms 𝕜 (I (e' x))) :
    I.analyticGermsEquiv he he' hx hx' φ =
      TauCeti.analyticGerms.pullback (I.extendCoordChange e e')
        (I.analyticAt_extendCoordChange he he' hx hx')
        (I.extendCoordChange_apply hx) φ := by
  unfold analyticGermsEquiv
  exact TauCeti.analyticGerms.equivOfInverse_apply _ _ _ _ _ _ _ φ

/-- Exchanging the two charts gives the inverse germ equivalence. -/
@[simp]
theorem analyticGermsEquiv_symm (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (I.analyticGermsEquiv he he' hx hx').symm = I.analyticGermsEquiv he' he hx' hx := by
  apply RingEquiv.ext
  intro φ
  unfold analyticGermsEquiv
  exact (TauCeti.analyticGerms.equivOfInverse_symm_apply _ _ _ _ _ _ _ φ).trans
    (TauCeti.analyticGerms.equivOfInverse_apply _ _ _ _ _ _ _ φ).symm

/-- Transport from a chart to itself fixes every analytic germ. -/
@[simp 1100]
theorem analyticGermsEquiv_self_apply (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source)
    (φ : TauCeti.analyticGerms 𝕜 (I (e x))) :
    I.analyticGermsEquiv he he hx hx φ = φ := by
  obtain ⟨f, hf, rfl⟩ := TauCeti.analyticGerms.exists_ofAnalyticAt φ
  rw [analyticGermsEquiv_apply, TauCeti.analyticGerms.pullback_ofAnalyticAt]
  apply TauCeti.analyticGerms.ofAnalyticAt_congr
  filter_upwards [I.extendCoordChange_source_mem_nhds hx hx] with y hy
  exact congrArg f ((e.extend I).right_inv hy.1)

/-- Transport identifies any two analytic chart representatives of the same scalar function. -/
theorem analyticGermsEquiv_ofAnalyticAt_comp_extend_symm
    (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (f : M → 𝕜)
    (hf' : AnalyticAt 𝕜 (f ∘ (e'.extend I).symm) (I (e' x)))
    (hf : AnalyticAt 𝕜 (f ∘ (e.extend I).symm) (I (e x))) :
    I.analyticGermsEquiv he he' hx hx'
        (TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e'.extend I).symm) hf') =
      TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e.extend I).symm) hf := by
  rw [analyticGermsEquiv_apply, TauCeti.analyticGerms.pullback_ofAnalyticAt]
  exact TauCeti.analyticGerms.ofAnalyticAt_congr
    ((I.extend_symm_comp_extendCoordChange_eventuallyEq hx hx').fun_comp f)

/-- The cocycle law for chart transport: passing through an intermediate chart does not change
the resulting germ. -/
@[simp]
theorem analyticGermsEquiv_trans (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (he'' : e'' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hx'' : x ∈ e''.source) :
    (I.analyticGermsEquiv he' he'' hx' hx'').trans (I.analyticGermsEquiv he he' hx hx') =
      I.analyticGermsEquiv he he'' hx hx'' := by
  apply RingEquiv.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := TauCeti.analyticGerms.exists_ofAnalyticAt φ
  rw [RingEquiv.trans_apply, I.analyticGermsEquiv_apply he' he'',
    TauCeti.analyticGerms.pullback_ofAnalyticAt, I.analyticGermsEquiv_apply he he'',
    TauCeti.analyticGerms.pullback_ofAnalyticAt]
  -- A transition representative is the representative of the function read in the final chart.
  exact I.analyticGermsEquiv_ofAnalyticAt_comp_extend_symm he he' hx hx' (f ∘ e''.extend I)
    (hf.comp_of_eq (I.analyticAt_extendCoordChange he' he'' hx' hx'')
      (I.extendCoordChange_apply hx'))
    (hf.comp_of_eq (I.analyticAt_extendCoordChange he he'' hx hx'')
      (I.extendCoordChange_apply hx))

/-- The chart representatives of an analytic scalar function correspond under chart transport.
Thus the represented local analytic function does not depend on the choice of chart. -/
theorem analyticGermsEquiv_ofAnalyticAt_comp_extend_symm_of_contMDiffAt {f : M → 𝕜}
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) ω f x) (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    I.analyticGermsEquiv he he' hx hx'
        (TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e'.extend I).symm)
          (hf.analyticAt_comp_extend_symm he' hx')) =
      TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e.extend I).symm)
        (hf.analyticAt_comp_extend_symm he hx) :=
  I.analyticGermsEquiv_ofAnalyticAt_comp_extend_symm he he' hx hx' f
    (hf.analyticAt_comp_extend_symm he' hx') (hf.analyticAt_comp_extend_symm he hx)

end ModelWithCorners

namespace TauCeti

section AnalyticMapGerm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- The type of germs along `𝓝 x` of maps `X → Y` that are analytic near `x` and send `x` to `y`. -/
abbrev AnalyticMapGerm (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (x : X) (y : Y) :=
  {F : Germ (𝓝 x) Y //
    ∃ f : X → Y, (f : Germ (𝓝 x) Y) = F ∧ f x = y ∧ ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w}

-- Exposed so `.val` reduces definitionally across module boundaries.
/-- Construct an `AnalyticMapGerm` from a map `f : X → Y` analytic near `x` with `f x = y`. -/
@[expose]
def AnalyticMapGerm.mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) : AnalyticMapGerm I J x y :=
  ⟨(f : Germ (𝓝 x) Y), ⟨f, rfl, hfx, hf⟩⟩

/-- The underlying `Germ (𝓝 x) Y` of `AnalyticMapGerm.mk f hf hfx` is `(f : Germ (𝓝 x) Y)`. -/
@[simp]
theorem AnalyticMapGerm.val_mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (AnalyticMapGerm.mk f hf hfx).val = (f : Germ (𝓝 x) Y) := (rfl)

/-- Two `AnalyticMapGerm.mk` germs are equal if and only if their representatives agree near `x`. -/
@[simp]
theorem AnalyticMapGerm.mk_eq_mk {x : X} {y : Y} {f₁ f₂ : X → Y}
    (hf₁ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₁ w) (hfx₁ : f₁ x = y)
    (hf₂ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₂ w) (hfx₂ : f₂ x = y) :
    AnalyticMapGerm.mk f₁ hf₁ hfx₁ = AnalyticMapGerm.mk f₂ hf₂ hfx₂ ↔ f₁ =ᶠ[𝓝 x] f₂ := by
  rw [Subtype.ext_iff, AnalyticMapGerm.val_mk, AnalyticMapGerm.val_mk, Germ.coe_eq]

/-- Every `AnalyticMapGerm` is represented by `AnalyticMapGerm.mk` of a locally analytic map. -/
theorem AnalyticMapGerm.exists_mk {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    ∃ (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y),
      AnalyticMapGerm.mk f hf hfx = F :=
  let ⟨f, hF, hfx, hf⟩ := F.property; ⟨f, hf, hfx, Subtype.ext hF⟩

/-- Every analytic map germ `(X, x) → (Y, y)` tends to `𝓝 y` along `𝓝 x`. -/
theorem AnalyticMapGerm.tendsto {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    F.val.Tendsto (𝓝 y) := by
  obtain ⟨f, hF, hfx, hf⟩ := F.property
  exact hF ▸ Germ.coe_tendsto.2 (hfx ▸ hf.self_of_nhds.continuousAt.tendsto)

-- Exposed so `AnalyticMapGerm.id` reduces to `AnalyticMapGerm.mk _root_.id ...` across modules.
/-- The identity analytic map germ at `x`. -/
@[expose]
def AnalyticMapGerm.id (I : ModelWithCorners 𝕜 E H) (x : X) : AnalyticMapGerm I I x x :=
  AnalyticMapGerm.mk _root_.id (Eventually.of_forall fun _ ↦ contMDiffAt_id) rfl

/-- The underlying `Germ (𝓝 x) X` of `AnalyticMapGerm.id I x` is the germ of `id`. -/
@[simp]
theorem AnalyticMapGerm.val_id (I : ModelWithCorners 𝕜 E H) (x : X) :
    (AnalyticMapGerm.id I x).val = ((_root_.id : X → X) : Germ (𝓝 x) X) := (rfl)

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H'' Z]

-- Exposed so `.val` reduces definitionally across module boundaries.
/-- Composition of analytic map germs `(X, x) → (Y, y)` and `(Y, y) → (Z, z)`. -/
@[expose]
def AnalyticMapGerm.comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) : AnalyticMapGerm I K x z :=
  ⟨G.val.compTendsto' F.val F.tendsto, by
    obtain ⟨g, hG, hgy, hg⟩ := G.property; obtain ⟨f, hF, hfx, hf⟩ := F.property
    exact ⟨g ∘ f, by simp [← hG, ← hF], (congrArg g hfx).trans hgy,
      eventually_contMDiffAt_comp hg hf hfx⟩⟩

/-- The underlying filter germ of `G.comp F` is `G.val.compTendsto' F.val F.tendsto`. -/
@[simp]
theorem AnalyticMapGerm.val_comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    (G.comp F).val = G.val.compTendsto' F.val F.tendsto := (rfl)

/-- Composing `AnalyticMapGerm.mk` representatives produces `AnalyticMapGerm.mk (g ∘ f) _ _`. -/
@[simp]
theorem AnalyticMapGerm.comp_mk {x : X} {y : Y} {z : Z}
    (g : Y → Z) (hg : ∀ᶠ v in 𝓝 y, ContMDiffAt J K ω g v) (hgy : g y = z)
    (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (AnalyticMapGerm.mk g hg hgy).comp (AnalyticMapGerm.mk f hf hfx) =
      AnalyticMapGerm.mk (g ∘ f) (eventually_contMDiffAt_comp hg hf hfx)
        ((congrArg g hfx).trans hgy) :=
  Subtype.ext rfl

/-- Left composition with `AnalyticMapGerm.id` is the identity. -/
@[simp]
theorem AnalyticMapGerm.id_comp {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    (AnalyticMapGerm.id J y).comp F = F := by obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk; rfl

/-- Right composition with `AnalyticMapGerm.id` is the identity. -/
@[simp]
theorem AnalyticMapGerm.comp_id {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    F.comp (AnalyticMapGerm.id I x) = F := by obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk; rfl

/-- Composition of analytic map germs is associative. -/
theorem AnalyticMapGerm.comp_assoc {E''' : Type*} [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
    {H''' : Type*} [TopologicalSpace H'''] {L : ModelWithCorners 𝕜 E''' H'''}
    {W : Type*} [TopologicalSpace W] [ChartedSpace H''' W] {x : X} {y : Y} {z : Z} {w : W}
    (H : AnalyticMapGerm K L z w) (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    (H.comp G).comp F = H.comp (G.comp F) := by
  obtain ⟨h, hh, hhz, rfl⟩ := H.exists_mk; obtain ⟨g, hg, hgy, rfl⟩ := G.exists_mk
  obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk; rfl

end AnalyticMapGerm

end TauCeti
