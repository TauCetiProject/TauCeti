/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Analysis.Analytic.Complexification.Germ
public import TauCeti.Analysis.Analytic.Germ
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic
public import TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Order.Filter.Germ

/-!
# Analytic germs on a manifold and under changes of charts

The scalar analytic germ rings in two analytic charts at the same manifold point are
canonically isomorphic. `ModelWithCorners.analyticGermsEquiv` is pullback by the analytic
change of extended charts. It has an explicit representative formula, reverses when the
charts are exchanged, and satisfies the identity and cocycle laws. Thus local analytic
functions can be transported without retaining a particular chart or neighborhood.

For a scalar analytic function on the manifold,
`analyticGermsEquiv_ofAnalyticAt_comp_extend_symm_of_contMDiffAt` identifies its two chart
representatives. In particular, equality of the local functions can be tested
in either chart.

The ring of analytic germs of the manifold itself, `ModelWithCorners.analyticGerms I x`, is the
subring of germs at `x` of scalar functions on `M` that are `C^ω` at `x`; it needs no chart to
define. A `C^ω` map of manifolds pulls germs back (`ModelWithCorners.analyticGerms.pullback`),
functorially, and locally inverse `C^ω` maps give ring isomorphisms
(`ModelWithCorners.analyticGerms.equivOfInverse`). For a chart `e` of the maximal `C^ω` atlas at
`x`, taking chart representatives is a ring isomorphism
`ModelWithCorners.analyticGermsChartEquiv` onto `TauCeti.analyticGerms 𝕜 (I (e x))`. The
isomorphisms of two charts differ by `analyticGermsEquiv`, and they turn pullback along a map into
pullback along its coordinate expression. On a normed space with its trivial model the ring is
`TauCeti.analyticGerms` (`ModelWithCorners.analyticGerms_modelWithCornersSelf`).

For a model `ι → ℝ`, `ModelWithCorners.analyticGermsComplexify` complexifies a germ through a
chart by `TauCeti.analyticGerms.complexify`. It is injective, its image consists of the
holomorphic germs commuting with complex conjugation, and the complexifications through two charts
correspond under pullback along a holomorphic extension of the change of coordinates. This is the
local compatibility needed to glue chartwise complexifications of a real-analytic manifold.

The germ ring of the manifold, its pullback and `ModelWithCorners.analyticGerms.equivOfInverse`
need no assumption on the model. The chart material (`analyticGermsEquiv`,
`analyticGermsChartEquiv` and its consequences) assumes a boundaryless model, so that the
transition domains are neighborhoods in the full normed model space. Complexification assumes a
finite-coordinate model `ι → ℝ` with `[Fintype ι]`; otherwise no finite-dimensionality or
countability assumption is needed.
The construction uses `TauCeti.analyticGerms.pullback` and its local-inverse equivalence;
complexification compatibility comes from `TauCeti.analyticGerms.complexify_pullback`.
For complex manifolds, `TauCeti.holomorphicStructureSheaf` describes holomorphic germs as
categorical stalks, compared with function germs by
`TauCeti.holomorphicStructureSheaf.toFilterGerm`; the rings here are subrings of function germs,
over any nontrivially normed field.

## References

* H. Whitney and F. Bruhat, *Quelques propriétés fondamentales des ensembles analytiques-réels*,
  Comment. Math. Helv. 33 (1959), §1.
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

/-! ### Analytic germs on a manifold -/

section ManifoldGerms

open Germ

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {x : M} {y : M'} {z : M''}

namespace ModelWithCorners

/-- The ring of analytic germs of `M` at `x`: the germs at `x` of the scalar functions on `M`
that are `C^ω` at `x`, inside the ring of all function germs at `x`. -/
def analyticGerms (x : M) : Subring (Germ (𝓝 x) 𝕜) where
  carrier := {φ | ∃ f : M → 𝕜, ContMDiffAt I 𝓘(𝕜) ω f x ∧ (f : Germ (𝓝 x) 𝕜) = φ}
  zero_mem' := ⟨0, contMDiffAt_const, rfl⟩
  one_mem' := ⟨1, contMDiffAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

variable {I}

/-- Membership in the analytic germ ring of `M` means having a representative that is `C^ω` at the
base point. -/
theorem mem_analyticGerms_iff {φ : Germ (𝓝 x) 𝕜} :
    φ ∈ I.analyticGerms x ↔ ∃ f : M → 𝕜, ContMDiffAt I 𝓘(𝕜) ω f x ∧ (f : Germ (𝓝 x) 𝕜) = φ :=
  Iff.rfl

/-- A function has an analytic germ on `M` exactly when it is `C^ω` at the base point. -/
@[simp]
theorem coe_mem_analyticGerms {f : M → 𝕜} :
    (f : Germ (𝓝 x) 𝕜) ∈ I.analyticGerms x ↔ ContMDiffAt I 𝓘(𝕜) ω f x :=
  ⟨fun ⟨_, hg, hgf⟩ ↦ hg.congr_of_eventuallyEq (coe_eq.1 hgf).symm, fun hf ↦ ⟨f, hf, rfl⟩⟩

/-- On a normed space with its trivial model, the analytic germs of the manifold are the germs of
analytic functions. -/
theorem analyticGerms_modelWithCornersSelf [CompleteSpace 𝕜] (a : E) :
    𝓘(𝕜, E).analyticGerms a = TauCeti.analyticGerms 𝕜 a := by
  ext φ
  induction φ using Germ.inductionOn with
  | h f =>
    rw [coe_mem_analyticGerms, TauCeti.coe_mem_analyticGerms,
      TauCeti.contMDiffAt_modelSpace_omega_iff_analyticAt]

namespace analyticGerms

/-- The germ of a function that is `C^ω` at the base point. -/
def ofContMDiffAt (f : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x) : I.analyticGerms x :=
  ⟨f, coe_mem_analyticGerms.2 hf⟩

@[simp]
theorem coe_ofContMDiffAt (f : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x) :
    ((ofContMDiffAt f hf : I.analyticGerms x) : Germ (𝓝 x) 𝕜) = f := (rfl)

/-- The zero function represents the zero analytic germ. -/
@[simp]
theorem ofContMDiffAt_zero :
    ofContMDiffAt (0 : M → 𝕜) (x := x) (I := I) contMDiffAt_const = 0 := (rfl)

/-- The constant one function represents the unit analytic germ. -/
@[simp]
theorem ofContMDiffAt_one :
    ofContMDiffAt (1 : M → 𝕜) (x := x) (I := I) contMDiffAt_const = 1 := (rfl)

/-- Taking analytic germs preserves addition. -/
@[simp]
theorem ofContMDiffAt_add (f g : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x)
    (hg : ContMDiffAt I 𝓘(𝕜) ω g x) :
    ofContMDiffAt (f + g) (hf.add hg) = ofContMDiffAt f hf + ofContMDiffAt g hg := (rfl)

/-- Taking analytic germs preserves multiplication. -/
@[simp]
theorem ofContMDiffAt_mul (f g : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x)
    (hg : ContMDiffAt I 𝓘(𝕜) ω g x) :
    ofContMDiffAt (f * g) (hf.mul hg) = ofContMDiffAt f hf * ofContMDiffAt g hg := (rfl)

/-- Taking analytic germs preserves negation. -/
@[simp]
theorem ofContMDiffAt_neg (f : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x) :
    ofContMDiffAt (-f) hf.neg = -ofContMDiffAt f hf := (rfl)

/-- Taking analytic germs preserves subtraction. -/
@[simp]
theorem ofContMDiffAt_sub (f g : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x)
    (hg : ContMDiffAt I 𝓘(𝕜) ω g x) :
    ofContMDiffAt (f - g) (hf.sub hg) = ofContMDiffAt f hf - ofContMDiffAt g hg := (rfl)

/-- Two `C^ω` representatives define the same germ exactly when they agree near the base point. -/
@[simp]
theorem ofContMDiffAt_eq_ofContMDiffAt_iff {f g : M → 𝕜} {hf : ContMDiffAt I 𝓘(𝕜) ω f x}
    {hg : ContMDiffAt I 𝓘(𝕜) ω g x} :
    ofContMDiffAt f hf = ofContMDiffAt g hg ↔ f =ᶠ[𝓝 x] g := by
  rw [Subtype.ext_iff, coe_ofContMDiffAt, coe_ofContMDiffAt, coe_eq]

/-- Eventually equal `C^ω` functions represent the same analytic germ. -/
theorem ofContMDiffAt_congr {f g : M → 𝕜} {hf : ContMDiffAt I 𝓘(𝕜) ω f x}
    {hg : ContMDiffAt I 𝓘(𝕜) ω g x} (h : f =ᶠ[𝓝 x] g) :
    ofContMDiffAt f hf = ofContMDiffAt g hg :=
  ofContMDiffAt_eq_ofContMDiffAt_iff.2 h

/-- Every analytic germ of `M` is the germ of a function that is `C^ω` at the base point. -/
theorem exists_ofContMDiffAt (φ : I.analyticGerms x) :
    ∃ (f : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x), ofContMDiffAt f hf = φ := by
  obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.property
  exact ⟨f, hf, Subtype.ext hφ⟩

/-! #### Pullback along analytic maps -/

/-- Pullback of analytic germs along a map of manifolds that is `C^ω` at the base point. -/
def pullback (g : M → M') (hg : ContMDiffAt I I' ω g x) (hgx : g x = y) :
    I'.analyticGerms y →+* I.analyticGerms x :=
  (compTendstoRingHom g (hgx ▸ hg.continuousAt.tendsto)).restrict _ _ fun φ hφ ↦ by
    obtain ⟨f, hf, rfl⟩ := hφ
    rw [compTendstoRingHom_apply, coe_compTendsto, coe_mem_analyticGerms]
    exact hf.comp_of_eq hg hgx

@[simp]
theorem coe_pullback (g : M → M') (hg : ContMDiffAt I I' ω g x) (hgx : g x = y)
    (φ : I'.analyticGerms y) :
    ((pullback g hg hgx φ : I.analyticGerms x) : Germ (𝓝 x) 𝕜) =
      (φ : Germ (𝓝 y) 𝕜).compTendsto g (hgx ▸ hg.continuousAt.tendsto) :=
  (RingHom.coe_restrict_apply _ _ _ _ φ).trans (compTendstoRingHom_apply _ _ _)

/-- Pullback sends the germ of `f` to the germ of its composition. -/
@[simp]
theorem pullback_ofContMDiffAt (g : M → M') (hg : ContMDiffAt I I' ω g x) (hgx : g x = y)
    (f : M' → 𝕜) (hf : ContMDiffAt I' 𝓘(𝕜) ω f y) :
    pullback g hg hgx (ofContMDiffAt f hf) = ofContMDiffAt (f ∘ g) (hf.comp_of_eq hg hgx) :=
  Subtype.ext ((coe_pullback g hg hgx _).trans (coe_compTendsto _ _))

/-- Pullback along the identity fixes each analytic germ. -/
@[simp]
theorem pullback_id (φ : I.analyticGerms x) : pullback (y := x) id contMDiffAt_id rfl φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofContMDiffAt φ
  rw [pullback_ofContMDiffAt]
  rfl

/-- Pullback depends only on the germ of the analytic map. -/
theorem pullback_congr {g g' : M → M'} (hg : ContMDiffAt I I' ω g x)
    (hg' : ContMDiffAt I I' ω g' x) (hgx : g x = y) (hg'x : g' x = y) (h : g =ᶠ[𝓝 x] g') :
    pullback g hg hgx = pullback g' hg' hg'x := by
  refine RingHom.ext fun φ ↦ ?_
  obtain ⟨f, hf, rfl⟩ := exists_ofContMDiffAt φ
  rw [pullback_ofContMDiffAt, pullback_ofContMDiffAt]
  exact ofContMDiffAt_congr (h.fun_comp f)

/-- Pullbacks compose in the opposite order to the maps. -/
@[simp]
theorem pullback_pullback (g : M → M') (hg : ContMDiffAt I I' ω g x) (hgx : g x = y)
    (h : M' → M'') (hh : ContMDiffAt I' I'' ω h y) (hhy : h y = z) (φ : I''.analyticGerms z) :
    pullback g hg hgx (pullback h hh hhy φ) =
      pullback (h ∘ g) (hh.comp_of_eq hg hgx) (by rw [Function.comp_apply, hgx, hhy]) φ := by
  obtain ⟨f, hf, rfl⟩ := exists_ofContMDiffAt φ
  rw [pullback_ofContMDiffAt, pullback_ofContMDiffAt, pullback_ofContMDiffAt]
  rfl

/-- Locally inverse analytic maps of manifolds identify the analytic germ rings at corresponding
points, contravariantly. Only inverse identities near the two base points are required. -/
def equivOfInverse (g : M → M') (h : M' → M) (hg : ContMDiffAt I I' ω g x)
    (hh : ContMDiffAt I' I ω h y) (hgx : g x = y) (hleft : h ∘ g =ᶠ[𝓝 x] id)
    (hright : g ∘ h =ᶠ[𝓝 y] id) : I'.analyticGerms y ≃+* I.analyticGerms x :=
  RingEquiv.ofRingHom (pullback g hg hgx) (pullback h hh (hgx ▸ hleft.self_of_nhds))
    (RingHom.ext fun φ ↦ by
      obtain ⟨f, hf, rfl⟩ := exists_ofContMDiffAt φ
      rw [RingHom.comp_apply, pullback_ofContMDiffAt, pullback_ofContMDiffAt, RingHom.id_apply]
      exact ofContMDiffAt_congr (hleft.fun_comp f))
    (RingHom.ext fun φ ↦ by
      obtain ⟨f, hf, rfl⟩ := exists_ofContMDiffAt φ
      rw [RingHom.comp_apply, pullback_ofContMDiffAt, pullback_ofContMDiffAt, RingHom.id_apply]
      exact ofContMDiffAt_congr (hright.fun_comp f))

/-- Transport by locally inverse analytic maps is pullback. -/
@[simp]
theorem equivOfInverse_apply (g : M → M') (h : M' → M) (hg : ContMDiffAt I I' ω g x)
    (hh : ContMDiffAt I' I ω h y) (hgx : g x = y) (hleft : h ∘ g =ᶠ[𝓝 x] id)
    (hright : g ∘ h =ᶠ[𝓝 y] id) (φ : I'.analyticGerms y) :
    equivOfInverse g h hg hh hgx hleft hright φ = pullback g hg hgx φ := (rfl)

/-- Inverse transport is pullback by the local inverse. -/
@[simp]
theorem equivOfInverse_symm_apply (g : M → M') (h : M' → M) (hg : ContMDiffAt I I' ω g x)
    (hh : ContMDiffAt I' I ω h y) (hgx : g x = y) (hleft : h ∘ g =ᶠ[𝓝 x] id)
    (hright : g ∘ h =ᶠ[𝓝 y] id) (φ : I.analyticGerms x) :
    (equivOfInverse g h hg hh hgx hleft hright).symm φ =
      pullback h hh (hgx ▸ hleft.self_of_nhds) φ := (rfl)

end analyticGerms

/-! #### Chart representatives -/

section Chart

variable [I.Boundaryless] [CompleteSpace 𝕜] {e e' : OpenPartialHomeomorph M H}

variable (I) in
/-- For a chart `e` of the maximal `C^ω` atlas at `x`, taking chart representatives identifies the
analytic germs of `M` at `x` with the analytic germs of the model at the coordinate of `x`: it is
pullback along the inverse of the extended chart, whose inverse is pullback along the extended
chart. -/
def analyticGermsChartEquiv (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) :
    I.analyticGerms x ≃+* TauCeti.analyticGerms 𝕜 (I (e x)) :=
  have hleft : e.extend I ∘ (e.extend I).symm =ᶠ[𝓝 (I (e x))] id :=
    eventually_of_mem (e.extend_target_mem_nhds hx) fun _ hz ↦ (e.extend I).right_inv hz
  have hright : (e.extend I).symm ∘ e.extend I =ᶠ[𝓝 x] id :=
    eventually_of_mem (e.extend_source_mem_nhds hx) fun _ hz ↦ (e.extend I).left_inv hz
  (analyticGerms.equivOfInverse (e.extend I).symm (e.extend I) (e.contMDiffAt_extend_symm he hx)
    (e.contMDiffAt_extend he hx) (e.extend_symm_apply_of_mem_source hx) hleft hright).trans
    (RingEquiv.subringCongr (analyticGerms_modelWithCornersSelf (I (e x))))

/-- The chart representative of an analytic germ of `M` is its pullback along the inverse of the
extended chart. -/
@[simp]
theorem coe_analyticGermsChartEquiv (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source)
    (φ : I.analyticGerms x) :
    ((I.analyticGermsChartEquiv he hx φ : TauCeti.analyticGerms 𝕜 (I (e x))) :
        Germ (𝓝 (I (e x))) 𝕜) =
      (φ : Germ (𝓝 x) 𝕜).compTendsto (e.extend I).symm
        ((e.continuousAt_extend_symm' (e.mem_extend_target hx)).tendsto.mono_right
          (congrArg 𝓝 (e.extend_symm_apply_of_mem_source hx)).le) := by
  unfold analyticGermsChartEquiv
  rw [RingEquiv.trans_apply, RingEquiv.coe_subringCongr_apply]
  exact (congrArg Subtype.val (analyticGerms.equivOfInverse_apply _ _ _ _ _ _ _ φ)).trans
    (analyticGerms.coe_pullback _ _ _ φ)

/-- The chart representative of the germ of a `C^ω` function is the germ of its coordinate
expression. -/
@[simp]
theorem analyticGermsChartEquiv_ofContMDiffAt (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source)
    (f : M → 𝕜) (hf : ContMDiffAt I 𝓘(𝕜) ω f x) :
    I.analyticGermsChartEquiv he hx (analyticGerms.ofContMDiffAt f hf) =
      TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e.extend I).symm)
        (hf.analyticAt_comp_extend_symm he hx) := by
  rw [Subtype.ext_iff, coe_analyticGermsChartEquiv, analyticGerms.coe_ofContMDiffAt,
    coe_compTendsto, TauCeti.analyticGerms.coe_ofAnalyticAt]

/-- The germ on `M` corresponding to an analytic germ of the model is the germ of its composition
with the extended chart. -/
@[simp]
theorem analyticGermsChartEquiv_symm_ofAnalyticAt (he : e ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (f : E → 𝕜) (hf : AnalyticAt 𝕜 f (I (e x))) :
    (I.analyticGermsChartEquiv he hx).symm (TauCeti.analyticGerms.ofAnalyticAt f hf) =
      analyticGerms.ofContMDiffAt (f ∘ e.extend I)
        (hf.contDiffAt.contMDiffAt.comp_of_eq (e.contMDiffAt_extend he hx)
          (congrFun e.extend_coe x)) := by
  rw [RingEquiv.symm_apply_eq, analyticGermsChartEquiv_ofContMDiffAt]
  refine TauCeti.analyticGerms.ofAnalyticAt_congr (eventually_of_mem
    (e.extend_target_mem_nhds hx) fun z hz ↦ ?_)
  exact (congrArg f ((e.extend I).right_inv hz)).symm

/-- Chart representatives in two charts correspond under the chart transport
`ModelWithCorners.analyticGermsEquiv`, which is pullback by the change of coordinates. -/
@[simp]
theorem analyticGermsChartEquiv_trans_analyticGermsEquiv (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (I.analyticGermsChartEquiv he' hx').trans (I.analyticGermsEquiv he he' hx hx') =
      I.analyticGermsChartEquiv he hx := by
  refine RingEquiv.ext fun φ ↦ ?_
  obtain ⟨f, hf, rfl⟩ := analyticGerms.exists_ofContMDiffAt φ
  rw [RingEquiv.trans_apply, analyticGermsChartEquiv_ofContMDiffAt,
    analyticGermsChartEquiv_ofContMDiffAt]
  exact I.analyticGermsEquiv_ofAnalyticAt_comp_extend_symm_of_contMDiffAt hf he he' hx hx'

/-- In charts `e` at `x` and `e'` at `y = g x`, pullback of analytic germs along a `C^ω` map `g`
of manifolds is pullback along its coordinate expression `e' ∘ g ∘ e⁻¹`. -/
theorem analyticGermsChartEquiv_pullback [I'.Boundaryless] {e' : OpenPartialHomeomorph M' H'}
    (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I' ω M') (hx : x ∈ e.source)
    (hy : y ∈ e'.source) (g : M → M') (hg : ContMDiffAt I I' ω g x) (hgx : g x = y)
    (φ : I'.analyticGerms y) :
    I.analyticGermsChartEquiv he hx (analyticGerms.pullback g hg hgx φ) =
      TauCeti.analyticGerms.pullback (e'.extend I' ∘ g ∘ (e.extend I).symm)
        (by simpa only [e.extend_coe, Function.comp_apply] using
          hg.analyticAt_extend_comp_extend_symm he he' hx (hgx ▸ hy))
        (by rw [Function.comp_apply, Function.comp_apply, e.extend_symm_apply_of_mem_source hx,
          hgx, e'.extend_coe, Function.comp_apply])
        (I'.analyticGermsChartEquiv he' hy φ) := by
  obtain ⟨f, hf, rfl⟩ := analyticGerms.exists_ofContMDiffAt φ
  rw [analyticGerms.pullback_ofContMDiffAt, analyticGermsChartEquiv_ofContMDiffAt,
    analyticGermsChartEquiv_ofContMDiffAt, TauCeti.analyticGerms.pullback_ofAnalyticAt]
  apply TauCeti.analyticGerms.ofAnalyticAt_congr
  have hcont : ContinuousAt (g ∘ (e.extend I).symm) (I (e x)) :=
    hg.continuousAt.comp_of_eq (e.continuousAt_extend_symm' (e.mem_extend_target hx))
      (e.extend_symm_apply_of_mem_source hx)
  have hmem : e'.source ∈ 𝓝 ((g ∘ (e.extend I).symm) (I (e x))) := by
    rw [Function.comp_apply, e.extend_symm_apply_of_mem_source hx, hgx]
    exact e'.open_source.mem_nhds hy
  filter_upwards [hcont.preimage_mem_nhds hmem] with w hw
  exact congrArg f (e'.extend_left_inv hw).symm

end Chart

end ModelWithCorners

end ManifoldGerms

/-! ### Complexification through a chart -/

section Complexification

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (ι → ℝ) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {e e' : OpenPartialHomeomorph M H} {x : M}

namespace ModelWithCorners

variable (I) in
/-- The complexification of the analytic germs of `M` at `x` through a chart `e` of the maximal
`C^ω` atlas: the complexification of the chart representative, a holomorphic germ at the
complexified coordinate of `x`. -/
noncomputable def analyticGermsComplexify (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) :
    I.analyticGerms x →+* TauCeti.analyticGerms ℂ (fun i ↦ (I (e x) i : ℂ)) :=
  (TauCeti.analyticGerms.complexify (I (e x))).comp (I.analyticGermsChartEquiv he hx).toRingHom

/-- Complexification through a chart complexifies the chart representative. -/
theorem analyticGermsComplexify_apply (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source)
    (φ : I.analyticGerms x) :
    I.analyticGermsComplexify he hx φ =
      TauCeti.analyticGerms.complexify (I (e x)) (I.analyticGermsChartEquiv he hx φ) := (rfl)

/-- A holomorphic function represents the complexification through `e` of the germ of a `C^ω`
function exactly when, near the coordinate of `x`, its values at real points are those of the
coordinate expression of the function. -/
theorem analyticGermsComplexify_ofContMDiffAt_eq_iff (he : e ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (f : M → ℝ) (hf : ContMDiffAt I 𝓘(ℝ) ω f x) (F : (ι → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F (fun i ↦ (I (e x) i : ℂ))) :
    I.analyticGermsComplexify he hx (analyticGerms.ofContMDiffAt f hf) =
        TauCeti.analyticGerms.ofAnalyticAt F hF ↔
      ∀ᶠ z in 𝓝 (I (e x)), F (fun i ↦ (z i : ℂ)) = (f ((e.extend I).symm z) : ℂ) := by
  rw [analyticGermsComplexify_apply, analyticGermsChartEquiv_ofContMDiffAt,
    TauCeti.analyticGerms.complexify_ofAnalyticAt_eq_iff]
  rfl

/-- Complexification through a chart does not identify distinct analytic germs. -/
theorem analyticGermsComplexify_injective (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) :
    Function.Injective (I.analyticGermsComplexify he hx) :=
  (TauCeti.analyticGerms.complexify_injective _).comp (I.analyticGermsChartEquiv he hx).injective

/-- **Change of charts.** The complexifications of an analytic germ of `M` through two charts
correspond under pullback along any holomorphic extension `G` of the change of coordinates. -/
theorem analyticGermsComplexify_eq_pullback (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (G : (ι → ℂ) → ι → ℂ) (hG : AnalyticAt ℂ G (fun i ↦ (I (e x) i : ℂ)))
    (hGr : ∀ᶠ z in 𝓝 (I (e x)),
      G (fun i ↦ (z i : ℂ)) = fun j ↦ (I.extendCoordChange e e' z j : ℂ))
    (φ : I.analyticGerms x) :
    I.analyticGermsComplexify he hx φ =
      TauCeti.analyticGerms.pullback G hG (hGr.self_of_nhds.trans
        (congrArg (fun w : ι → ℝ ↦ fun j ↦ (w j : ℂ)) (I.extendCoordChange_apply hx)))
        (I.analyticGermsComplexify he' hx' φ) := by
  rw [analyticGermsComplexify_apply, analyticGermsComplexify_apply,
    ← analyticGermsChartEquiv_trans_analyticGermsEquiv he he' hx hx', RingEquiv.trans_apply,
    analyticGermsEquiv_apply]
  exact TauCeti.analyticGerms.complexify_pullback _ _ _ G hG hGr _

/-- **Change of charts.** The change of coordinates between two charts has a holomorphic
extension near the complexified coordinate of `x`, and pullback along it carries the
complexifications through the second chart to those through the first. -/
theorem exists_analyticGermsComplexify_eq_pullback (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ (G : (ι → ℂ) → ι → ℂ) (hG : AnalyticAt ℂ G (fun i ↦ (I (e x) i : ℂ)))
      (hGx : G (fun i ↦ (I (e x) i : ℂ)) = fun i ↦ (I (e' x) i : ℂ)),
      (∀ᶠ z in 𝓝 (I (e x)),
        G (fun i ↦ (z i : ℂ)) = fun j ↦ (I.extendCoordChange e e' z j : ℂ)) ∧
      ∀ φ, I.analyticGermsComplexify he hx φ =
        TauCeti.analyticGerms.pullback G hG hGx (I.analyticGermsComplexify he' hx' φ) := by
  obtain ⟨r, hr, G, hG, hGr, -⟩ :=
    (I.analyticAt_extendCoordChange he he' hx hx').exists_complexification_pi
  have hGr' : ∀ᶠ z in 𝓝 (I (e x)),
      G (fun i ↦ (z i : ℂ)) = fun j ↦ (I.extendCoordChange e e' z j : ℂ) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) hGr
  exact ⟨G, hG _ (Metric.mem_ball_self hr), _, hGr',
    analyticGermsComplexify_eq_pullback he he' hx hx' G _ hGr'⟩

/-- The complexifications through a chart are exactly the holomorphic germs at the complexified
coordinate of `x` that commute with complex conjugation. -/
theorem exists_analyticGermsComplexify_eq_iff_eventually_apply_star
    (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source) {F : (ι → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun i ↦ (I (e x) i : ℂ))) :
    (∃ φ, I.analyticGermsComplexify he hx φ = TauCeti.analyticGerms.ofAnalyticAt F hF) ↔
      ∀ᶠ z in 𝓝 (fun i ↦ (I (e x) i : ℂ)), F (star z) = star (F z) := by
  simp only [analyticGermsComplexify_apply]
  exact (I.analyticGermsChartEquiv he hx).surjective.exists.symm.trans
    (TauCeti.analyticGerms.exists_complexify_eq_iff_eventually_apply_star hF)

end ModelWithCorners

end Complexification
