/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.IneffectiveKernel
public import TauCeti.Geometry.Manifold.Etale.Linearization
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Principal

import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth structure and local geometry of the effective quotient

For an étale groupoid `C` whose objects carry a `C^n` manifold structure, the effective quotient
`TauCeti.EffectiveQuotient C` inherits canonical `C^n` manifold structures on both objects and
total arrows:
* the object charts are pulled back along `(EffectiveQuotient.objHomeomorph C).symm`, making
  `(toEffectiveQuotient C).obj` a `C^n` diffeomorphism (`EffectiveQuotient.objDiffeomorph`);
* the total-arrow charts are pulled back from the objects along the source local homeomorphism
  (`EffectiveQuotient.chartedSpaceArrows`), making the source map a `C^n` local diffeomorphism and
  characterising `C^n` maps into the effective arrows by continuity together with smoothness of
  their sources (`EffectiveQuotient.contMDiff_arrows_iff`).

When the original source map is a `C^n` local diffeomorphism (possibly for a distinct arrow model
`J`), the arrow projection `(toEffectiveQuotient C).toPrefunctor.mapTotal` is a surjective `C^n`
local diffeomorphism (`EffectiveQuotient.isLocalDiffeomorph_mapTotal`), so smoothness of maps out
of the effective arrow space is detected after precomposing with `mapTotal`
(`EffectiveQuotient.contMDiff_comp_mapTotal_iff`). When the original target map is `C^n`, the
effective target map and arrow inversion become `C^n` local diffeomorphisms and diffeomorphisms
respectively.

For a `C^n` (`1 ≤ n`) proper étale groupoid with Hausdorff arrow space over a boundaryless
complete `RCLike` model, `ineffectiveArrows C` is closed, so the effective arrow space is
Hausdorff (`EffectiveQuotient.t2Space_arrows`). Together with the topological results in
`TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology` and `Principal`, the effective
quotient is a Hausdorff, second-countable (when `C` is), `C^n` proper étale groupoid with trivial
ineffective kernel and open dense principal locus.

Finally, this file gives two local descriptions of `ineffectiveKernel` and the principal locus:
* on any preconnected smooth isotropy chart `V`, `ineffectiveKernel` at the centre equals the
  global action kernel `(MulAction.toPermHom (Aut x) V).ker`, and every point of a `C^n` (`1 ≤ n`)
  proper étale groupoid admits such a preconnected smooth isotropy chart
  (`exists_preconnected_contMDiff_isotropy_action_of_proper_source_target`);
* in any linear isotropy chart `B : Opens E` governed by a continuous representation `σ`,
  `ineffectiveKernel` equals `σ.toMonoidHom.ker`, and the principal locus in `B` is the complement
  of the proper fixed linear subspaces `LinearMap.eqLocus (σ g) id` for `g ∉ ineffectiveKernel`.

## Main declarations

* `TauCeti.EffectiveQuotient.instChartedSpaceObjects`,
  `TauCeti.EffectiveQuotient.instIsManifoldObjects`, `TauCeti.EffectiveQuotient.objDiffeomorph`:
  the `C^n` manifold structure on objects of `EffectiveQuotient C`.
* `TauCeti.EffectiveQuotient.chartedSpaceArrows`, `TauCeti.EffectiveQuotient.isManifold_arrows`,
  `TauCeti.EffectiveQuotient.compatible_chartedSpaceArrows`: the `C^n` manifold structure on total
  arrows of `EffectiveQuotient C` and its uniqueness up to atlas equivalence.
* `TauCeti.EffectiveQuotient.isLocalDiffeomorph_mapTotal`,
  `TauCeti.EffectiveQuotient.contMDiff_comp_mapTotal_iff`: smooth descent along the arrow quotient.
* `TauCeti.EffectiveQuotient.isLocalDiffeomorph_source`,
  `TauCeti.EffectiveQuotient.isLocalDiffeomorph_target`,
  `TauCeti.EffectiveQuotient.contMDiff_unit`, `TauCeti.EffectiveQuotient.inverseDiffeomorph`,
  `TauCeti.EffectiveQuotient.contMDiff_comp`: the `C^n` étale groupoid structure of
  `EffectiveQuotient C`.
* `TauCeti.EffectiveQuotient.t2Space_arrows`: Hausdorffness of `Quiver.Total (EffectiveQuotient C)`
  for `C^n` (`1 ≤ n`) proper étale groupoids over boundaryless complete `RCLike` models.
* `ContRepresentation.germKernel_opens_eq_ker`,
  `ContRepresentation.setOf_stabilizer_opens_eq_ker`: germ kernel and principal locus of a linear
  representation restricted to an open subset.
* `TauCeti.exists_preconnected_contMDiff_isotropy_action_of_proper_source_target`: preconnected
  smooth isotropy charts identifying `ineffectiveKernel` with the chart action kernel.
* `TauCeti.ineffectiveKernel_eq_ker_of_linear_isotropy_chart`,
  `TauCeti.preimage_setOf_ineffectiveKernel_eq_top_of_linear_isotropy_chart`: linear fixed-subspace
  description of `ineffectiveKernel` and the principal locus.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public noncomputable section

open CategoryTheory MulAction Set Topology
open scoped Manifold ContDiff

namespace ContRepresentation

variable {𝕜 G E : Type*} [NontriviallyNormedField 𝕜] [Group G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (σ : ContRepresentation 𝕜 G E) (B : TopologicalSpace.Opens E)

/-- For any action of `G` on an open subset `B` of `E` given by a continuous linear representation
`σ`, the germ kernel at every point `v : B` is `σ.toMonoidHom.ker`: a linear map equal to the
identity on a nonempty open set is the identity everywhere. -/
theorem germKernel_opens_eq_ker [MulAction G B]
    (hval : ∀ g : G, ∀ v : B, (g • v : B).val = σ g v) (v : B) :
    TauCeti.MulAction.germKernel G v = σ.toMonoidHom.ker := by
  refine le_antisymm (fun g hg ↦ ?_) (fun g hg ↦ ?_)
  · rw [TauCeti.MulAction.mem_germKernel_iff_mem_interior_fixedBy] at hg
    have hopen : IsOpen ((Subtype.val : B → E) '' interior (fixedBy B g)) :=
      B.isOpen.isOpenMap_subtype_val _ isOpen_interior
    have hne : ((Subtype.val : B → E) '' interior (fixedBy B g)).Nonempty :=
      ⟨v, v, hg, rfl⟩
    have hsub : (Subtype.val : B → E) '' interior (fixedBy B g) ⊆
        LinearMap.eqLocus ((σ g : E →L[𝕜] E) : E →ₗ[𝕜] E) LinearMap.id := by
      rintro _ ⟨w, hw, rfl⟩
      have hgw : g • w = w := mem_fixedBy.mp (interior_subset hw)
      simp [LinearMap.mem_eqLocus, ← hval g w, hgw]
    have htop := Submodule.eq_top_of_nonempty_interior' _
      (hne.mono (interior_maximal hsub hopen))
    exact MonoidHom.mem_ker.mpr
      (ContinuousLinearMap.coe_injective (LinearMap.eqLocus_eq_top.mp htop))
  · rw [MonoidHom.mem_ker, ContRepresentation.toMonoidHom_apply] at hg
    exact TauCeti.MulAction.mem_germKernel.mpr (Filter.Eventually.of_forall fun w ↦
      Subtype.ext (by simp [hval g w, hg]))

/-- For `ContRepresentation.mulActionOpens`, the germ kernel at every point of `B` equals
`σ.toMonoidHom.ker`. -/
theorem germKernel_mulActionOpens_eq_ker (hB : ∀ g : G, ∀ v ∈ B, σ g v ∈ B) (v : B) :
    letI := σ.mulActionOpens B hB
    TauCeti.MulAction.germKernel G v = σ.toMonoidHom.ker :=
  letI := σ.mulActionOpens B hB
  σ.germKernel_opens_eq_ker B (σ.val_mulActionOpens_smul B hB) v

/-- On a nonempty open subset `B` of `E`, the permutation kernel of an action given by `σ` equals
`σ.toMonoidHom.ker`. -/
theorem ker_toPermHom_opens_eq_ker [MulAction G B] [Nonempty B]
    (hval : ∀ g : G, ∀ v : B, (g • v : B).val = σ g v) :
    (toPermHom G B).ker = σ.toMonoidHom.ker := by
  obtain ⟨v⟩ := ‹Nonempty B›
  refine le_antisymm ?_ (fun g hg ↦ ?_)
  · rw [← σ.germKernel_opens_eq_ker B hval v]
    exact TauCeti.MulAction.ker_toPermHom_le_germKernel v
  · rw [MonoidHom.mem_ker, ContRepresentation.toMonoidHom_apply] at hg
    exact MonoidHom.mem_ker.mpr (Equiv.Perm.ext fun w ↦ Subtype.ext (by simp [hval g w, hg]))

/-- On a nonempty invariant open subset `B` of `E`, the permutation kernel of
`σ.mulActionOpens B hB` equals `σ.toMonoidHom.ker`. -/
theorem ker_toPermHom_mulActionOpens [Nonempty B] (hB : ∀ g : G, ∀ v ∈ B, σ g v ∈ B) :
    letI := σ.mulActionOpens B hB
    (toPermHom G B).ker = σ.toMonoidHom.ker :=
  letI := σ.mulActionOpens B hB
  σ.ker_toPermHom_opens_eq_ker B (σ.val_mulActionOpens_smul B hB)

/-- An element `g : G` fixes `v : B` if and only if `(v : E)` lies in the fixed linear subspace
`LinearMap.eqLocus (σ g) id`. -/
theorem mem_stabilizer_opens_iff [MulAction G B]
    (hval : ∀ g : G, ∀ v : B, (g • v : B).val = σ g v) {v : B} {g : G} :
    g ∈ stabilizer G v ↔
      (v : E) ∈ LinearMap.eqLocus ((σ g : E →L[𝕜] E) : E →ₗ[𝕜] E) LinearMap.id := by
  rw [mem_stabilizer_iff, Subtype.ext_iff, hval g v, LinearMap.mem_eqLocus,
    ContinuousLinearMap.coe_coe, LinearMap.id_coe, id_eq]

/-- A point `v : B` has stabilizer equal to `σ.toMonoidHom.ker` if and only if `(v : E)` avoids the
fixed linear subspace `LinearMap.eqLocus (σ g) id` for every `g ∉ σ.toMonoidHom.ker`. -/
theorem stabilizer_opens_eq_ker_iff [MulAction G B]
    (hval : ∀ g : G, ∀ v : B, (g • v : B).val = σ g v) (v : B) :
    stabilizer G v = σ.toMonoidHom.ker ↔
      ∀ g : G, g ∉ σ.toMonoidHom.ker →
        (v : E) ∉ LinearMap.eqLocus ((σ g : E →L[𝕜] E) : E →ₗ[𝕜] E) LinearMap.id := by
  have hle : σ.toMonoidHom.ker ≤ stabilizer G v := by
    rw [← σ.germKernel_opens_eq_ker B hval v]
    exact TauCeti.MulAction.germKernel_le_stabilizer v
  refine ⟨fun h g hg hv ↦ hg (h ▸ (σ.mem_stabilizer_opens_iff B hval).mpr hv),
    fun h ↦ le_antisymm (fun g hg ↦ by_contra fun hgn ↦
      h g hgn ((σ.mem_stabilizer_opens_iff B hval).mp hg)) hle⟩

/-- In a linear representation chart `B : Opens E`, the principal locus where the stabilizer equals
`σ.toMonoidHom.ker` is the complement in `B` of the proper fixed linear subspaces
`LinearMap.eqLocus (σ g) id` for `g ∉ σ.toMonoidHom.ker`. -/
theorem setOf_stabilizer_opens_eq_ker [MulAction G B]
    (hval : ∀ g : G, ∀ v : B, (g • v : B).val = σ g v) :
    {v : B | stabilizer G v = σ.toMonoidHom.ker} =
      (⋃ g ∈ (σ.toMonoidHom.ker : Set G)ᶜ,
        (Subtype.val : B → E) ⁻¹'
          (LinearMap.eqLocus ((σ g : E →L[𝕜] E) : E →ₗ[𝕜] E) LinearMap.id : Set E))ᶜ := by
  ext v
  simp [σ.stabilizer_opens_eq_ker_iff B hval v]

end ContRepresentation

namespace TauCeti

namespace EffectiveQuotient

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)]

/-- The object charts of `EffectiveQuotient C`, pulled back from `C` along the inverse of the
object homeomorphism. -/
instance instChartedSpaceObjects : ChartedSpace H (EffectiveQuotient C) :=
  (objHomeomorph C).symm.pullbackChartedSpace

/-- Objects of `EffectiveQuotient C` form a `C^n` manifold whenever `C` does. -/
instance instIsManifoldObjects [IsManifold I n C] : IsManifold I n (EffectiveQuotient C) :=
  Homeomorph.pullback_isManifold I n (objHomeomorph C).symm

variable (C) in
/-- The projection from `C` to `EffectiveQuotient C` on objects, bundled as a `C^n`
diffeomorphism. -/
def objDiffeomorph : C ≃ₘ^n⟮I, I⟯ EffectiveQuotient C :=
  ((objHomeomorph C).symm.pullbackDiffeomorph I n).symm

/-- `objDiffeomorph` agrees on objects with `(toEffectiveQuotient C).obj`. -/
@[simp]
theorem objDiffeomorph_apply (x : C) :
    objDiffeomorph I n C x = (toEffectiveQuotient C).obj x := by
  simp [objDiffeomorph]

/-- The inverse of `objDiffeomorph` agrees with `(objEquiv C).symm`. -/
@[simp]
theorem objDiffeomorph_symm_apply (q : EffectiveQuotient C) :
    (objDiffeomorph I n C).symm q = (objEquiv C).symm q := by
  change ((objHomeomorph C).symm.pullbackDiffeomorph I n) q = (objEquiv C).symm q
  simp

/-- The object component of `toEffectiveQuotient C` is `C^n`. -/
theorem contMDiff_toEffectiveQuotient_obj :
    ContMDiff I I n (toEffectiveQuotient C).obj :=
  (objDiffeomorph I n C).contMDiff.congr fun x ↦ (objDiffeomorph_apply I n x).symm

/-- The object component of `toEffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_toEffectiveQuotient_obj :
    IsLocalDiffeomorph I I n (toEffectiveQuotient C).obj := by
  simpa only [funext (objDiffeomorph_apply I n)] using (objDiffeomorph I n C).isLocalDiffeomorph

/-- A map into `EffectiveQuotient C` is `C^n` if and only if its lift to `C` along `objEquiv.symm`
is `C^n`. -/
theorem contMDiff_objects_iff {f : N → EffectiveQuotient C} :
    ContMDiff K I n f ↔ ContMDiff K I n fun z ↦ (objEquiv C).symm (f z) := by
  simp [← (objDiffeomorph I n C).symm.contMDiff_diffeomorph_comp_iff le_rfl, Function.comp_def]

section EtaleTopology

variable [IsTopologicalGroupoid C]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- The total-arrow charts of `EffectiveQuotient C`, pulled back from its object manifold along the
source local homeomorphism. -/
@[instance_reducible]
def chartedSpaceArrows : ChartedSpace H (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).chartedSpaceComap

/-- For an étale topological groupoid whose objects form a `C^n` manifold, the total arrows of
`EffectiveQuotient C` form a `C^n` manifold. -/
theorem isManifold_arrows [IsManifold I n C] :
    letI := chartedSpaceArrows (H := H) hs
    IsManifold I n (Quiver.Total (EffectiveQuotient C)) :=
  (isLocalHomeomorph_source hs).isManifold_chartedSpaceComap

/-- The source map of `EffectiveQuotient C` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source :
    letI := chartedSpaceArrows (H := H) hs
    IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  (isLocalHomeomorph_source hs).isLocalDiffeomorph_chartedSpaceComap

/-- A map into the total arrows of `EffectiveQuotient C` is `C^n` if and only if it is continuous
and its composite with the source map is `C^n`. -/
theorem contMDiff_arrows_iff {f : N → Quiver.Total (EffectiveQuotient C)} :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff K I n f ↔ Continuous f ∧ ContMDiff K I n fun z ↦ (f z).left :=
  (isLocalHomeomorph_source hs).contMDiff_chartedSpaceComap_iff

/-- Any `C^n` manifold structure on `Quiver.Total (EffectiveQuotient C)` for which the source map
is a `C^n` local diffeomorphism is compatible with `chartedSpaceArrows hs`. -/
theorem compatible_chartedSpaceArrows [IsManifold I n C]
    [c : ChartedSpace H (Quiver.Total (EffectiveQuotient C))]
    [IsManifold I n (Quiver.Total (EffectiveQuotient C))]
    (hsrc : IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C)) :
    ∀ e ∈ c.atlas, ∀ e' ∈ (chartedSpaceArrows (H := H) hs).atlas,
      e.symm.trans e' ∈ contDiffGroupoid n I :=
  (isLocalHomeomorph_source hs).compatible_chartedSpaceComap hsrc

/-- The unit section of `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_unit :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff I I n fun x : EffectiveQuotient C ↦
      (⟨x, x, 𝟙 x⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := isTopologicalGroupoid hs
  let := chartedSpaceArrows (H := H) hs
  exact (contMDiff_arrows_iff I n hs).2 ⟨IsTopologicalGroupoid.continuous_unit, contMDiff_id⟩

/-- Composing two `C^n` families of composable arrows in `EffectiveQuotient C` produces a `C^n`
family of arrows. -/
theorem contMDiff_comp {a b : N → Quiver.Total (EffectiveQuotient C)}
    (ha : letI := chartedSpaceArrows (H := H) hs; ContMDiff K I n a)
    (hb : letI := chartedSpaceArrows (H := H) hs; ContMDiff K I n b)
    (h : ∀ z, (a z).right = (b z).left) :
    letI := chartedSpaceArrows (H := H) hs
    ContMDiff K I n fun z ↦ (a z).comp (b z) (h z) := by
  let := isTopologicalGroupoid hs
  let := chartedSpaceArrows (H := H) hs
  have hsource : ContMDiff K I n fun z ↦ ((a z).comp (b z) (h z)).left := by
    simpa only [Quiver.Total.comp_left, Function.comp_def] using
      (isLocalDiffeomorph_source I n hs).contMDiff.comp ha
  exact (contMDiff_arrows_iff I n hs).2
    ⟨IsTopologicalGroupoid.continuous_comp.comp
      ((ha.continuous.prodMk hb.continuous).subtype_mk h), hsource⟩

end EtaleTopology

section SmoothArrows

variable [ChartedSpace H' (Quiver.Total C)] [IsTopologicalGroupoid C]
  (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))

/-- When the original source map is a `C^n` local diffeomorphism, the arrow quotient map
`(toEffectiveQuotient C).toPrefunctor.mapTotal` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_mapTotal :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph J I n (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro a
  have hcomp : IsLocalDiffeomorphAt J I n
      (Quiver.Total.left ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) a := by
    have heq : (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) ∘
        (toEffectiveQuotient C).toPrefunctor.mapTotal =
        objDiffeomorph I n C ∘ Quiver.Total.left := by
      funext b
      simp [Prefunctor.mapTotal_left]
    rw [heq]
    exact (hs a).comp (hg := (objDiffeomorph I n C).isLocalDiffeomorph a.left)
  exact hcomp.of_comp_left
    (isLocalDiffeomorph_source I n hs.isLocalHomeomorph _)
    isQuotientMap_mapTotal.continuous.continuousAt

/-- The arrow quotient map `(toEffectiveQuotient C).toPrefunctor.mapTotal` is `C^n`. -/
theorem contMDiff_mapTotal :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff J I n (toEffectiveQuotient C).toPrefunctor.mapTotal :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  (isLocalDiffeomorph_mapTotal I n hs).contMDiff

/-- **Smooth descent along the effective arrow quotient.** For `m ≤ n`, a map out of
`Quiver.Total (EffectiveQuotient C)` is `C^m` if and only if its composite with `mapTotal` is
`C^m`. -/
theorem contMDiff_comp_mapTotal_iff {m : ℕ∞ω} (hm : m ≤ n)
    {g : Quiver.Total (EffectiveQuotient C) → N} :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff J K m (g ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) ↔
      ContMDiff I K m g :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  (isLocalDiffeomorph_mapTotal I n hs).contMDiff_comp_iff mapTotal_surjective hm

/-- When the source map of `C` is a `C^n` local diffeomorphism and the target map of `C` is `C^n`,
the target map of `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_target
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  refine (contMDiff_comp_mapTotal_iff I n hs le_rfl).mp ?_
  have heq : (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) ∘
      (toEffectiveQuotient C).toPrefunctor.mapTotal =
      (toEffectiveQuotient C).obj ∘ Quiver.Total.right := by
    funext b
    rfl
  rw [heq]
  exact (contMDiff_toEffectiveQuotient_obj I n).comp ht

/-- Inversion of arrows in `EffectiveQuotient C` is `C^n`. -/
theorem contMDiff_inverse
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    ContMDiff I I n fun a : Quiver.Total (EffectiveQuotient C) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (EffectiveQuotient C)) := by
  let := isTopologicalGroupoid hs.isLocalHomeomorph
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  exact (contMDiff_arrows_iff I n hs.isLocalHomeomorph).2
    ⟨IsTopologicalGroupoid.continuous_inverse, contMDiff_target I n hs ht⟩

/-- Arrow inversion as an involutive `C^n` diffeomorphism of
`Quiver.Total (EffectiveQuotient C)`. -/
def inverseDiffeomorph
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    Quiver.Total (EffectiveQuotient C) ≃ₘ^n⟮I, I⟯ Quiver.Total (EffectiveQuotient C) :=
  letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  { toFun a := ⟨a.right, a.left, inv a.hom⟩
    invFun a := ⟨a.right, a.left, inv a.hom⟩
    left_inv a := by simp
    right_inv a := by simp
    contMDiff_toFun := contMDiff_inverse I n hs ht
    contMDiff_invFun := contMDiff_inverse I n hs ht }

/-- `inverseDiffeomorph` reverses an arrow of `EffectiveQuotient C`. -/
@[simp]
theorem inverseDiffeomorph_apply
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C))
    (a : Quiver.Total (EffectiveQuotient C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    inverseDiffeomorph I n hs ht a = ⟨a.right, a.left, inv a.hom⟩ :=
  (rfl)

/-- `inverseDiffeomorph` is its own inverse. -/
@[simp]
theorem inverseDiffeomorph_symm
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    (inverseDiffeomorph I n hs ht).symm = inverseDiffeomorph I n hs ht :=
  (rfl)

/-- The target map of `EffectiveQuotient C` is a `C^n` local diffeomorphism whenever the source map
of `C` is a `C^n` local diffeomorphism and the target map of `C` is `C^n`. -/
theorem isLocalDiffeomorph_target
    (ht : ContMDiff J I n (Quiver.Total.right : Quiver.Total C → C)) :
    letI := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
    IsLocalDiffeomorph I I n
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  let := chartedSpaceArrows (H := H) hs.isLocalHomeomorph
  intro a
  exact ((inverseDiffeomorph I n hs ht).isLocalDiffeomorph a).comp
    (hg := isLocalDiffeomorph_source I n hs.isLocalHomeomorph _)

end SmoothArrows

end Smooth

section Hausdorff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)] {n : ℕ∞ω}

/-- In a `C^n` (`1 ≤ n`) proper étale groupoid with Hausdorff arrow space over a boundaryless
complete `RCLike` model, the total arrow space of `EffectiveQuotient C` is Hausdorff. -/
theorem t2Space_arrows
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) (hn : 1 ≤ n) :
    T2Space (Quiver.Total (EffectiveQuotient C)) := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  exact t2Space_arrows_of_isClosed_ineffectiveArrows hs.isLocalHomeomorph
    (isClosed_ineffectiveArrows hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp hn)

end Hausdorff

end EffectiveQuotient

section PreconnectedChart

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {n : ℕ∞ω} {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)]

/-- **Ineffective kernel on a preconnected smooth isotropy chart.** On any preconnected open
isotropy chart `V` of a Hausdorff boundaryless manifold where `Aut x` is finite and acts by `C^n`
(`1 ≤ n`) maps, `ineffectiveKernel hs x` is the global kernel of the `Aut x`-action on `V`. -/
theorem ineffectiveKernel_eq_ker_of_preconnected_isotropy_chart
    [IsTopologicalGroupoid C] [T2Space C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} [Finite (Aut x)] {V : TopologicalSpace.Opens C} (hxV : x ∈ V)
    [PreconnectedSpace V] [MulAction (Aut x) V] [ContMDiffConstSMul I n (Aut x) V] (hn : 1 ≤ n)
    {F : ActionCategory (Aut x) V ⥤ C} (hobj : ∀ a, F.obj a = (a.back : C))
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun z : V ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, z)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, ⟨x, hxV⟩)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩) :
    ineffectiveKernel hs x = (toPermHom (Aut x) V).ker := by
  rw [ineffectiveKernel_eq_germKernel_of_isotropy_chart hs Subtype.val_injective
    (z := (⟨x, hxV⟩ : V)) hobj hσ hcentre]
  exact germKernel_eq_ker (I := I)
    (fun g ↦ (ContMDiffConstSMul.contMDiff_const_smul (I := I) (n := n) g).of_le hn)
    (fun _ ↦ isMulTorsion_of_finite) (⟨x, hxV⟩ : V)

/-- On a preconnected smooth isotropy chart `V` (`1 ≤ n`), an object `y : V` belongs to the
principal locus of `C` if and only if its `Aut x`-stabilizer equals the kernel of the `Aut x`-action
on `V`. -/
theorem ineffectiveKernel_eq_top_iff_stabilizer_eq_ker_of_preconnected_isotropy_chart
    [IsTopologicalGroupoid C] [T2Space C]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {x : C} [Finite (Aut x)] {V : TopologicalSpace.Opens C} [PreconnectedSpace V]
    [MulAction (Aut x) V] [ContMDiffConstSMul I n (Aut x) V] (hn : 1 ≤ n)
    {F : ActionCategory (Aut x) V ⥤ C} [F.Full] [F.Faithful]
    (hobj : ∀ a, F.obj a = (a.back : C))
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun z : V ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, z)).hom⟩ : Quiver.Total C))
    (y : V) :
    ineffectiveKernel hs (y : C) = ⊤ ↔ stabilizer (Aut x) y = (toPermHom (Aut x) V).ker := by
  rw [ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs Subtype.val_injective hobj hσ y,
    germKernel_eq_ker (I := I)
      (fun g ↦ (ContMDiffConstSMul.contMDiff_const_smul (I := I) (n := n) g).of_le hn)
      (fun _ ↦ isMulTorsion_of_finite) y]

/-- **Preconnected smooth isotropy charts.** Every object `x` of a `C^n` (`1 ≤ n`) proper étale
groupoid with Hausdorff arrow space over a boundaryless complete `RCLike` model admits a
preconnected open isotropy chart `V : Opens C` on which `Aut x` acts by `C^n` maps fixing `x`,
with fully faithful inclusion functor `F : Aut x ⋉ V ⥤ C` and
`ineffectiveKernel hs.isLocalHomeomorph x = (MulAction.toPermHom (Aut x) V).ker`. -/
theorem exists_preconnected_contMDiff_isotropy_action_of_proper_source_target
    [ChartedSpace H' (Quiver.Total C)] [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hn : 1 ≤ n) (x : C) :
    ∃ (V : TopologicalSpace.Opens C) (hxV : x ∈ V) (_ : PreconnectedSpace V)
      (_ : MulAction (Aut x) V) (F : ActionCategory (Aut x) V ⥤ C),
      ContMDiffConstSMul I n (Aut x) V ∧
      (∀ g : Aut x, g • (⟨x, hxV⟩ : V) = ⟨x, hxV⟩) ∧
      (∀ a, F.obj a = (a.back : C)) ∧ F.Full ∧ F.Faithful ∧
      (∀ g : Aut x, IsOpenEmbedding fun y : V ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, y)).hom⟩ :
          Quiver.Total C)) ∧
      (∀ g : Aut x, IsLocalDiffeomorph I J n fun y : V ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, y)).hom⟩ :
          Quiver.Total C)) ∧
      (∀ g : Aut x,
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, ⟨x, hxV⟩)).hom⟩ :
          Quiver.Total C) = ⟨x, x, g.asIso.hom⟩) ∧
      ineffectiveKernel hs.isLocalHomeomorph x = (toPermHom (Aut x) V).ker := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  have := finite_aut_of_proper_source_target hp hs.isLocalHomeomorph x
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace C := ChartedSpace.locallyConnectedSpace H C
  obtain ⟨U, hxU, actU, F₀, hsmulU, hfixU, hobj₀, hfull₀, hfaith₀, hopen₀, harrow₀, -, -,
      hcentre₀⟩ :=
    exists_contMDiff_isotropy_action_of_proper_source_target hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let : MulAction (Aut x) U := actU
  have : F₀.Full := hfull₀
  have : F₀.Faithful := hfaith₀
  have : LocallyConnectedSpace U := U.isOpen.locallyConnectedSpace
  let x₀ : U := ⟨x, hxU⟩
  let W : Set U := connectedComponent x₀
  have hWopen : IsOpen W := isOpen_connectedComponent
  let V : TopologicalSpace.Opens C :=
    ⟨(Subtype.val : U → C) '' W, U.isOpen.isOpenMap_subtype_val W hWopen⟩
  have hVU : (V : Set C) ⊆ U := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hmemW {y : C} (hy : y ∈ V) : (⟨y, hVU hy⟩ : U) ∈ W := by
    rcases hy with ⟨u, huW, rfl⟩
    exact huW
  have hpresW (g : Aut x) {u : U} (hu : u ∈ W) : g • u ∈ W :=
    (isPreconnected_connectedComponent.image (g • ·)
      (hsmulU.contMDiff_const_smul g).continuous.continuousOn).subset_connectedComponent
      ⟨x₀, mem_connectedComponent, hfixU g⟩ (mem_image_of_mem (g • ·) hu)
  let actV : MulAction (Aut x) V :=
    { smul g y := ⟨(g • (⟨y.1, hVU y.2⟩ : U) : U).1,
        ⟨g • ⟨y.1, hVU y.2⟩, hpresW g (hmemW y.2), rfl⟩⟩
      one_smul y := Subtype.ext (congrArg (Subtype.val : U → C)
        (one_smul (Aut x) (⟨y.1, hVU y.2⟩ : U)))
      mul_smul g h y := Subtype.ext (congrArg (Subtype.val : U → C)
        (mul_smul g h (⟨y.1, hVU y.2⟩ : U))) }
  let : MulAction (Aut x) V := actV
  let ι : V →[Aut x] U :=
    { toFun y := ⟨y.1, hVU y.2⟩
      map_smul' _ _ := rfl }
  have hι_inj : Function.Injective ι :=
    fun a b hab ↦ Subtype.ext (congrArg (Subtype.val : U → C) hab)
  have hι_open : IsOpenEmbedding ι := by
    refine .of_continuous_injective_isOpenMap
      (continuous_subtype_val.subtype_mk fun y ↦ hVU y.2) hι_inj fun S hS ↦ ?_
    have himg : (ι '' S : Set U) = (Subtype.val : U → C) ⁻¹' ((Subtype.val : V → C) '' S) := by
      ext u
      refine ⟨?_, fun hu ↦ ?_⟩
      · rintro ⟨y, hyS, rfl⟩
        exact ⟨y, hyS, rfl⟩
      · rcases hu with ⟨y, hyS, hyu⟩
        refine ⟨y, hyS, Subtype.ext hyu⟩
    rw [himg]
    exact (V.isOpen.isOpenMap_subtype_val S hS).preimage continuous_subtype_val
  have hι_diff : IsLocalDiffeomorph I I n ι := fun y ↦ by
    have hcomp : IsLocalDiffeomorphAt I I n ((Subtype.val : U → C) ∘ ι) y :=
      isLocalDiffeomorph_subtype_val y
    exact hcomp.of_comp_left (isLocalDiffeomorph_subtype_val (ι y)) hι_open.continuous.continuousAt
  have hsmulV : ContMDiffConstSMul I n (Aut x) V :=
    ⟨fun g ↦ (ContMDiff.subtypeVal_comp_iff V _).mp
      ((contMDiff_subtype_val : ContMDiff I I n (Subtype.val : U → C)).comp
        ((hsmulU.contMDiff_const_smul g).comp hι_diff.contMDiff))⟩
  have hxV : x ∈ V := ⟨x₀, mem_connectedComponent, rfl⟩
  have hconnV : PreconnectedSpace V :=
    Subtype.preconnectedSpace
      (isPreconnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn)
  have : PreconnectedSpace V := hconnV
  have : ContMDiffConstSMul I n (Aut x) V := hsmulV
  let A := ActionCategory.map (MonoidHom.id (Aut x)) ι
  have : A.Full := ActionCategory.full_map_of_injective ι hι_inj
  have : A.Faithful := ActionCategory.faithful_map _ _ Function.injective_id
  let F := A ⋙ F₀
  have hlabel (g : Aut x) (y : V) :
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, y)).hom⟩ :
        Quiver.Total C) =
      ⟨_, _, F₀.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, ι y)).hom⟩ :=
    congrArg F₀.toPrefunctor.mapTotal
      (ActionCategory.mapTotal_totalEquiv_symm (MonoidHom.id (Aut x)) ι g y)
  have hobj (a : ActionCategory (Aut x) V) : F.obj a = (a.back : C) :=
    (hobj₀ (A.obj a)).trans
      (congrArg (Subtype.val : U → C) (ActionCategory.back_map_obj (MonoidHom.id (Aut x)) ι a))
  have hopen (g : Aut x) : IsOpenEmbedding fun y : V ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, y)).hom⟩ :
        Quiver.Total C) := by
    simp only [hlabel]
    exact (hopen₀ g).comp hι_open
  have harrow (g : Aut x) : IsLocalDiffeomorph I J n fun y : V ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, y)).hom⟩ :
        Quiver.Total C) := by
    simp only [hlabel]
    exact fun y ↦ (hι_diff y).comp (hg := harrow₀ g (ι y))
  have hcentre (g : Aut x) :
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) V).symm (g, ⟨x, hxV⟩)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩ := by
    rw [hlabel]
    exact hcentre₀ g
  refine ⟨V, hxV, hconnV, actV, F, hsmulV,
    fun g ↦ Subtype.ext (congrArg (Subtype.val : U → C) (hfixU g)),
    hobj, inferInstance, inferInstance, hopen, harrow, hcentre, ?_⟩
  exact ineffectiveKernel_eq_ker_of_preconnected_isotropy_chart (I := I) hs.isLocalHomeomorph
    hxV hn hobj hopen hcentre

end PreconnectedChart

section LinearChart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- **Ineffective kernel in a linear isotropy chart.** In any local isotropy chart `B : Opens E`
at `x` governed by a continuous linear representation `σ : ContRepresentation 𝕜 (Aut x) E`, the
ineffective kernel at `x` equals `σ.toMonoidHom.ker`. This applies directly to the linear-ball
charts supplied by `TauCeti.exists_linear_ball_isotropy_chart`. -/
theorem ineffectiveKernel_eq_ker_of_linear_isotropy_chart
    {x : C} {σ : ContRepresentation 𝕜 (Aut x) E} {B : TopologicalSpace.Opens E}
    [MulAction (Aut x) B] (hval : ∀ g : Aut x, ∀ v : B, (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f) {z : B}
    {F : ActionCategory (Aut x) B ⥤ C} (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩) :
    ineffectiveKernel hs x = σ.toMonoidHom.ker :=
  (ineffectiveKernel_eq_germKernel_of_isotropy_chart hs hf hobj hσ hcentre).trans
    (σ.germKernel_opens_eq_ker B hval z)

/-- In a linear isotropy chart `B : Opens E` at `x`, `ineffectiveKernel hs x` equals the kernel of
the `Aut x`-action on `B`. -/
theorem ineffectiveKernel_eq_ker_toPermHom_of_linear_isotropy_chart
    {x : C} {σ : ContRepresentation 𝕜 (Aut x) E} {B : TopologicalSpace.Opens E}
    [MulAction (Aut x) B] (hval : ∀ g : Aut x, ∀ v : B, (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f) {z : B}
    {F : ActionCategory (Aut x) B ⥤ C} (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩) :
    ineffectiveKernel hs x = (toPermHom (Aut x) B).ker := by
  have : Nonempty B := ⟨z⟩
  exact (ineffectiveKernel_eq_ker_of_linear_isotropy_chart hs hval hf hobj hσ hcentre).trans
    (σ.ker_toPermHom_opens_eq_ker B hval).symm

/-- **Pointwise linear description of the principal locus.** In a linear isotropy chart
`B : Opens E` at `x`, an object `f v` belongs to the principal locus of `C` if and only if
`(v : E)` avoids the fixed linear subspace `LinearMap.eqLocus (σ g) id` for every
`g ∉ ineffectiveKernel hs x`. -/
theorem ineffectiveKernel_eq_top_iff_of_linear_isotropy_chart
    {x : C} {σ : ContRepresentation 𝕜 (Aut x) E} {B : TopologicalSpace.Opens E}
    [MulAction (Aut x) B] (hval : ∀ g : Aut x, ∀ v : B, (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f) {z : B}
    {F : ActionCategory (Aut x) B ⥤ C} [F.Full] [F.Faithful] (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩)
    (v : B) :
    ineffectiveKernel hs (f v) = ⊤ ↔
      ∀ g : Aut x, g ∉ ineffectiveKernel hs x →
        (v : E) ∉ LinearMap.eqLocus ((σ g : E →L[𝕜] E) : E →ₗ[𝕜] E) LinearMap.id := by
  rw [ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs hf hobj hσ v,
    σ.germKernel_opens_eq_ker B hval v,
    ineffectiveKernel_eq_ker_of_linear_isotropy_chart hs hval hf hobj hσ hcentre,
    σ.stabilizer_opens_eq_ker_iff B hval v]

/-- **Set-level linear description of the principal locus.** In a linear isotropy chart
`B : Opens E` at `x`, the preimage of the principal locus `{y : C | ineffectiveKernel hs y = ⊤}` is
the complement in `B` of the proper fixed linear subspaces `LinearMap.eqLocus (σ g) id` for
`g ∉ ineffectiveKernel hs x`. -/
theorem preimage_setOf_ineffectiveKernel_eq_top_of_linear_isotropy_chart
    {x : C} {σ : ContRepresentation 𝕜 (Aut x) E} {B : TopologicalSpace.Opens E}
    [MulAction (Aut x) B] (hval : ∀ g : Aut x, ∀ v : B, (g • v : B).val = σ g v)
    {f : B → C} (hf : Function.Injective f) {z : B}
    {F : ActionCategory (Aut x) B ⥤ C} [F.Full] [F.Faithful] (hobj : ∀ a, F.obj a = f a.back)
    (hσ : ∀ g : Aut x, IsOpenEmbedding fun v : B ↦
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ : Quiver.Total C))
    (hcentre : ∀ g : Aut x,
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ :
        Quiver.Total C) = ⟨x, x, g.asIso.hom⟩) :
    f ⁻¹' {y : C | ineffectiveKernel hs y = ⊤} =
      (⋃ g ∈ (ineffectiveKernel hs x : Set (Aut x))ᶜ,
        (Subtype.val : B → E) ⁻¹'
          (LinearMap.eqLocus ((σ g : E →L[𝕜] E) : E →ₗ[𝕜] E) LinearMap.id : Set E))ᶜ := by
  ext v
  simp [ineffectiveKernel_eq_top_iff_of_linear_isotropy_chart hs hval hf hobj hσ hcentre v]

end LinearChart

end TauCeti
