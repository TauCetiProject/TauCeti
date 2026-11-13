/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.Orientation

/-!
# Embedded pseudoholomorphic curves and their homology classes

Let `(M, J)` be an almost complex manifold with a two-form `σ` taming `J`, for instance a
symplectic manifold with a compatible almost complex structure. This file builds the carrier of
the embedded curves counted in Taubes's Gromov invariant: closed connected embedded
`J`-holomorphic curves, considered as subsets of `M`, with their integral homology classes, and
finite configurations of disjoint such curves with positive multiplicities.

**Orientation.** If `u : (S, j) → (M, J)` is pseudoholomorphic with injective derivatives, then
`u^* σ` tames `j` (`TauCeti.SmoothTwoForm.Tames.mpullback_of_isPseudoholomorphic`), so it is
nondegenerate and `S` carries its symplectic orientation. In it the `j`-adapted bases
`(e₁, j e₁, …, eₙ, j eₙ)` are positive
(`TauCeti.CompactConnectedPseudoholomorphicEmbedding.orientation_reindex_eq_orientationAt`), and
forms taming the same `j` give the same orientation
(`TauCeti.SmoothTwoForm.IsNondegenerate.orientation_eq_of_tames`). So this is the complex
orientation of `(S, j)`, and it does not depend on `σ`.

**Parametrized curves.** A `TauCeti.CompactConnectedPseudoholomorphicEmbedding J F` bundles a
compact connected Hausdorff manifold `S` without boundary modelled on the real normed space `F`, an
almost complex structure `j` on `S` and a smooth pseudoholomorphic embedding `u : S → M`. If `u₁`
and `u₂` have the same image, then `φ = u₂⁻¹ ∘ u₁` is a pseudoholomorphic diffeomorphism, smooth
in both directions because `u₁` and `u₂` are immersions
(`TauCeti.CompactConnectedPseudoholomorphicEmbedding.reparam`). For `F` a finite-dimensional real
inner product space and with the complex orientation of `S`, `u` pushes the fundamental class of
`S` forward to `u_*[S]` (`TauCeti.CompactConnectedPseudoholomorphicEmbedding.homologyClass`). This
class depends only on the image of `u`
(`TauCeti.CompactConnectedPseudoholomorphicEmbedding.homologyClass_eq_of_range_eq`):
`φ^* (u₂^* σ) = u₁^* σ`, so `φ` preserves the complex orientations. Its degree is therefore the
local index `1` at the single preimage of a point, and `u₁ = u₂ ∘ φ` gives
`u₁_*[S₁] = deg φ • u₂_*[S₂] = u₂_*[S₂]`.

**Curves and configurations.** For `F = ℂ` the images are the closed connected embedded
`J`-holomorphic curves (`TauCeti.IsClosedConnectedEmbeddedPseudoholomorphicCurve`). Each has a
homology class (`TauCeti.IsClosedConnectedEmbeddedPseudoholomorphicCurve.homologyClass`) equal to
`u_*[S]` for every parametrization. A `TauCeti.EmbeddedCurveConfiguration J` is a finitely
supported multiplicity function on subsets of `M` whose support consists of pairwise disjoint such
curves. Distinct curves are distinct subsets, so a configuration forgets parametrizations but
keeps the images and their multiplicities. Its class is the linear combination `∑ m_C [C]` of the
curve classes, extended by `0` to all subsets of `M`
(`TauCeti.EmbeddedCurveConfiguration.curveHomologyClass`). So the configurations of class `A` are
exactly the compatible configurations `TauCeti.compatibleConfigurations` of the closed connected
embedded curves, for disjointness as compatibility
(`TauCeti.EmbeddedCurveConfiguration.mem_compatibleConfigurations_iff`), and the weighted counts
of `TauCeti.configurationCount` apply to them.

## Main definitions

* `TauCeti.CompactConnectedPseudoholomorphicEmbedding J F`: a smooth pseudoholomorphic embedding
  of a compact connected manifold without boundary modelled on `F`.
* `TauCeti.CompactConnectedPseudoholomorphicEmbedding.reparam`: the diffeomorphism `u₂⁻¹ ∘ u₁`
  between the sources of two pseudoholomorphic embeddings with the same image.
* `TauCeti.CompactConnectedPseudoholomorphicEmbedding.homologyClass`: its class `u_*[S]` for the
  complex orientation of `S`.
* `TauCeti.IsClosedConnectedEmbeddedPseudoholomorphicCurve J C`: `C` is the image of a smooth
  pseudoholomorphic embedding of a compact connected surface.
* `TauCeti.IsClosedConnectedEmbeddedPseudoholomorphicCurve.homologyClass`: the homology class of
  such a curve.
* `TauCeti.EmbeddedCurveConfiguration J`: a finite configuration of disjoint closed connected
  embedded `J`-holomorphic curves with positive multiplicities, and its class
  `TauCeti.EmbeddedCurveConfiguration.homologyClass`.

## Main results

* `TauCeti.CompactConnectedPseudoholomorphicEmbedding.homologyClass_eq_of_range_eq`:
  pseudoholomorphic embeddings with the same image carry the same class.
* `TauCeti.CompactConnectedPseudoholomorphicEmbedding.homologyClass_eq_of_tames`: the class does
  not depend on the taming form.
* `TauCeti.CompactConnectedPseudoholomorphicEmbedding.homologyClass_id`: the identity of a compact
  connected almost complex manifold carries its fundamental class.
* `TauCeti.EmbeddedCurveConfiguration.mem_compatibleConfigurations_iff`: the configurations of
  class `A` are the compatible configurations of closed connected embedded curves in class `A`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893, Section 2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.6 (simple and embedded curves).
-/

public section

noncomputable section

open Module Set
open Manifold (IsSmoothEmbedding)
open scoped Manifold ContDiff

namespace TauCeti

section Tames

variable {E H M E' H' S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold I' ∞ S]
  {J : SmoothAlmostComplexStructure I M} {j : SmoothAlmostComplexStructure I' S}
  {σ : SmoothTwoForm I M} {u : S → M}

/-- **Taming pulls back along pseudoholomorphic immersions.** If `σ` tames `J` and `u : S → M`
is a smooth pseudoholomorphic map with injective derivatives, then `u^* σ` tames `j`:
`(u^* σ)(e, j e) = σ(du e, J (du e)) > 0` for `e ≠ 0`. -/
theorem SmoothTwoForm.Tames.mpullback_of_isPseudoholomorphic (hσ : σ.Tames J)
    (hu : ContMDiff I' I ∞ u) (hhol : IsPseudoholomorphic j J u)
    (hinj : ∀ x, Function.Injective (mfderiv I' I u x)) :
    SmoothTwoForm.Tames (SmoothForm.mpullback u hu σ) j := by
  rw [SmoothTwoForm.tames_iff]
  intro x v hv
  rw [SmoothForm.eval₂_mpullback, (hhol.isPseudoholomorphicAt x).mfderiv_apply_commute]
  exact SmoothTwoForm.tames_iff.1 hσ (u x) _ fun h ↦ hv (hinj x (h.trans (map_zero _).symm))

end Tames

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {J : SmoothAlmostComplexStructure I M} {σ : SmoothTwoForm I M}

variable (J) in
/-- A **pseudoholomorphic embedding of a compact connected manifold** into `(M, J)`: the source
`S`, a compact connected Hausdorff manifold without boundary modelled on `F`, an almost complex
structure `j` on it, and a smooth embedding `u : S → M` which is `(j, J)`-holomorphic. For `F = ℂ`
these parametrize the closed connected embedded `J`-holomorphic curves in `M`. -/
structure CompactConnectedPseudoholomorphicEmbedding (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] where
  /-- The source manifold. -/
  Source : Type
  /-- The topology of the source. -/
  [instTopologicalSpace : TopologicalSpace Source]
  /-- The source is Hausdorff. -/
  [instT2Space : T2Space Source]
  /-- The source is compact. -/
  [instCompactSpace : CompactSpace Source]
  /-- The source is connected. -/
  [instConnectedSpace : ConnectedSpace Source]
  /-- The charts of the source, modelled on `F`. -/
  [instChartedSpace : ChartedSpace F Source]
  /-- The smooth structure of the source. -/
  [instIsManifold : IsManifold 𝓘(ℝ, F) ∞ Source]
  /-- The almost complex structure of the source. -/
  j : SmoothAlmostComplexStructure 𝓘(ℝ, F) Source
  /-- The embedding. -/
  toFun : Source → M
  /-- The map is a smooth embedding: an immersion which is a homeomorphism onto its image. -/
  isSmoothEmbedding : IsSmoothEmbedding 𝓘(ℝ, F) I ∞ toFun
  /-- The map is `(j, J)`-holomorphic. -/
  isPseudoholomorphic : IsPseudoholomorphic j J toFun

namespace CompactConnectedPseudoholomorphicEmbedding

attribute [instance] instTopologicalSpace instT2Space instCompactSpace instConnectedSpace
  instChartedSpace instIsManifold

variable {F F' F'' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [NormedAddCommGroup F''] [NormedSpace ℝ F'']

instance : CoeFun (CompactConnectedPseudoholomorphicEmbedding J F) fun p ↦ p.Source → M :=
  ⟨toFun⟩

variable (p : CompactConnectedPseudoholomorphicEmbedding J F)
  (q : CompactConnectedPseudoholomorphicEmbedding J F')

/-- A pseudoholomorphic embedding is smooth. -/
theorem contMDiff : ContMDiff 𝓘(ℝ, F) I ∞ p :=
  p.isSmoothEmbedding.contMDiff

/-- A pseudoholomorphic embedding is continuous. -/
theorem continuous : Continuous p :=
  p.contMDiff.continuous

/-- A pseudoholomorphic embedding is injective. -/
theorem injective : Function.Injective p :=
  p.isSmoothEmbedding.isEmbedding.injective

/-- A pseudoholomorphic embedding has injective derivatives. -/
theorem mfderiv_injective (x : p.Source) : Function.Injective (mfderiv 𝓘(ℝ, F) I p x) :=
  p.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) x

/-- The embedding as a continuous map. -/
def toContinuousMap : C(p.Source, M) :=
  ⟨p, p.continuous⟩

@[simp]
theorem coe_toContinuousMap : ⇑p.toContinuousMap = p :=
  (rfl)

/-- The pullback `u^* σ` of a form taming `J` tames the almost complex structure of the source. -/
theorem tames_mpullback (hσ : σ.Tames J) :
    SmoothTwoForm.Tames (SmoothForm.mpullback p p.contMDiff σ) p.j :=
  hσ.mpullback_of_isPseudoholomorphic p.contMDiff p.isPseudoholomorphic p.mfderiv_injective

/-- The **reparametrization** between two pseudoholomorphic embeddings with the same image: the
diffeomorphism `u₂⁻¹ ∘ u₁` from the source of `p` to the source of `q`. It is smooth in both
directions because `u₁` and `u₂` are immersions. -/
def reparam (h : range p = range q) : p.Source ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, F')⟯ q.Source :=
  Homeomorph.diffeomorphOfImmersions
    (p.isSmoothEmbedding.isEmbedding.toHomeomorph.trans
      ((Homeomorph.setCongr h).trans q.isSmoothEmbedding.isEmbedding.toHomeomorph.symm))
    p.isSmoothEmbedding.isImmersion q.isSmoothEmbedding.isImmersion <|
      funext fun _ ↦ (q.isSmoothEmbedding.isEmbedding.toHomeomorph_apply_coe _).symm.trans
        (congrArg Subtype.val (Homeomorph.apply_symm_apply _ _))

/-- The reparametrization `u₂⁻¹ ∘ u₁` followed by `u₂` is `u₁`. -/
@[simp]
theorem apply_reparam (h : range p = range q) (x : p.Source) : q (p.reparam q h x) = p x := by
  rw [reparam, Homeomorph.diffeomorphOfImmersions_apply]
  exact (q.isSmoothEmbedding.isEmbedding.toHomeomorph_apply_coe _).symm.trans
    (congrArg Subtype.val (Homeomorph.apply_symm_apply _ _))

/-- `u₂ ∘ (u₂⁻¹ ∘ u₁) = u₁`. -/
theorem comp_reparam (h : range p = range q) : q ∘ p.reparam q h = p :=
  funext (p.apply_reparam q h)

/-- The reparametrization of `p` to itself is the identity. -/
@[simp]
theorem reparam_self (h : range p = range p) :
    p.reparam p h = Diffeomorph.refl 𝓘(ℝ, F) p.Source ∞ :=
  Diffeomorph.ext fun x ↦ p.injective (p.apply_reparam p h x)

/-- Reparametrizing from `p` to `q` and then from `q` to `r` reparametrizes from `p` to `r`. -/
@[simp]
theorem reparam_apply_reparam (r : CompactConnectedPseudoholomorphicEmbedding J F'')
    (h₁ : range p = range q) (h₂ : range q = range r) (x : p.Source) :
    q.reparam r h₂ (p.reparam q h₁ x) = p.reparam r (h₁.trans h₂) x :=
  r.injective (by rw [apply_reparam, apply_reparam, apply_reparam])

/-- The composite of the reparametrizations from `p` to `q` and from `q` to `r` is the
reparametrization from `p` to `r`. -/
@[simp]
theorem reparam_trans_reparam (r : CompactConnectedPseudoholomorphicEmbedding J F'')
    (h₁ : range p = range q) (h₂ : range q = range r) :
    (p.reparam q h₁).trans (q.reparam r h₂) = p.reparam r (h₁.trans h₂) :=
  Diffeomorph.ext (p.reparam_apply_reparam q r h₁ h₂)

/-- The inverse of the reparametrization from `p` to `q` is the reparametrization from `q`
to `p`. -/
@[simp]
theorem symm_reparam (h : range p = range q) : (p.reparam q h).symm = q.reparam p h.symm :=
  Diffeomorph.ext fun y ↦ p.injective <| by
    rw [apply_reparam, ← p.apply_reparam q h, Diffeomorph.apply_symm_apply]

/-- The reparametrization is `(j₁, j₂)`-holomorphic, since `u₂` is a pseudoholomorphic immersion
and `u₂ ∘ reparam = u₁` is pseudoholomorphic. -/
theorem isPseudoholomorphic_reparam (h : range p = range q) :
    IsPseudoholomorphic p.j q.j (p.reparam q h) := isPseudoholomorphic_iff.2 fun x ↦
  IsPseudoholomorphicAt.of_comp
    (by rw [p.comp_reparam q h]; exact p.isPseudoholomorphic.isPseudoholomorphicAt x)
    (q.isPseudoholomorphic.isPseudoholomorphicAt _) (q.mfderiv_injective _)
    ((p.reparam q h).contMDiff.mdifferentiableAt (by simp))

/-- The reparametrization pulls `u₂^* σ` back to `u₁^* σ`. -/
theorem mpullback_reparam (h : range p = range q) :
    SmoothForm.mpullback (p.reparam q h) (p.reparam q h).contMDiff
        (SmoothForm.mpullback q q.contMDiff σ) =
      SmoothForm.mpullback p p.contMDiff σ := by
  rw [SmoothForm.mpullback_mpullback]
  apply Subtype.ext
  simp only [SmoothForm.coe_mpullback, p.comp_reparam q h]

variable (F) in
/-- The identity of a compact connected almost complex manifold `(S, j)` modelled on `F`, as a
pseudoholomorphic embedding into itself. -/
@[expose] protected def id (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ConnectedSpace S] [ChartedSpace F S] [IsManifold 𝓘(ℝ, F) ∞ S]
    (j : SmoothAlmostComplexStructure 𝓘(ℝ, F) S) :
    CompactConnectedPseudoholomorphicEmbedding j F where
  Source := S
  j := j
  toFun := _root_.id
  isSmoothEmbedding := IsSmoothEmbedding.id
  isPseudoholomorphic := isPseudoholomorphic_id j

section Id

variable {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
  [ChartedSpace F S] [IsManifold 𝓘(ℝ, F) ∞ S] (j : SmoothAlmostComplexStructure 𝓘(ℝ, F) S)

@[simp]
theorem coe_id : ⇑(CompactConnectedPseudoholomorphicEmbedding.id F S j) = _root_.id :=
  (rfl)

@[simp]
theorem id_j : (CompactConnectedPseudoholomorphicEmbedding.id F S j).j = j :=
  (rfl)

@[simp]
theorem toContinuousMap_id : (CompactConnectedPseudoholomorphicEmbedding.id F S j).toContinuousMap =
    ContinuousMap.id S :=
  (rfl)

end Id

section Orientation

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] {n : ℕ} (hF : finrank ℝ F = n + 1)
  (hF' : finrank ℝ F' = n + 1)

/-- The **complex orientation** of the source of `p`, computed as the symplectic orientation of
`u^* σ` for a form `σ` taming `J`. By `orientation_eq_of_tames` it does not depend on `σ`. -/
def orientation (hσ : σ.Tames J) : Manifold.Orientation 𝓘(ℝ, F) p.Source (Fin (n + 1)) :=
  (p.tames_mpullback hσ).isNondegenerate.orientation hF

theorem orientation_def (hσ : σ.Tames J) :
    p.orientation hF hσ = (p.tames_mpullback hσ).isNondegenerate.orientation hF :=
  (rfl)

/-- The tangent orientation of the complex orientation at `x` is the symplectic orientation of
`(u^* σ)_x`. -/
@[simp]
theorem orientationAt_orientation (hσ : σ.Tames J) (x : p.Source) :
    (p.orientation hF hσ).orientationAt x =
      ((p.tames_mpullback hσ).isNondegenerate.symplecticFormAt x).orientation hF :=
  SmoothTwoForm.IsNondegenerate.orientationAt_orientation _ hF x

/-- **`j`-adapted bases are positive for the complex orientation.** Every `j`-adapted basis
`(e₁, j e₁, …, eₘ, j eₘ)` of the tangent space at `x`, listed in this interleaved order, is
positive. -/
theorem orientation_reindex_eq_orientationAt (hσ : σ.Tames J) {x : p.Source} {m : ℕ}
    {b : Basis (Fin m × Fin 2) ℝ (TangentSpace 𝓘(ℝ, F) x)}
    (hb : ∀ i, b (i, 1) = p.j x (b (i, 0))) (h : m * 2 = n + 1) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation =
      (p.orientation hF hσ).orientationAt x := by
  rw [orientation_def]
  exact SmoothTwoForm.IsNondegenerate.orientation_reindex_eq_orientationAt_of_tames _ hF
    (p.tames_mpullback hσ) hb h

/-- **`j`-adapted frames of a surface are positive for the complex orientation.** If `S` is a
surface, every basis `(e, j e)` of the tangent space at `x` is positive. -/
theorem orientation_eq_orientationAt (hF₂ : finrank ℝ F = 2) (hσ : σ.Tames J) {x : p.Source}
    {b : Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, F) x)} (hb : b 1 = p.j x (b 0)) :
    b.orientation = (p.orientation (n := 1) hF₂ hσ).orientationAt x := by
  rw [orientation_def]
  exact SmoothTwoForm.IsNondegenerate.orientation_eq_orientationAt_of_tames _
    (p.tames_mpullback hσ) hF₂ hb

/-- The complex orientation does not depend on the taming form. -/
theorem orientation_eq_of_tames {σ' : SmoothTwoForm I M} (hσ : σ.Tames J) (hσ' : σ'.Tames J) :
    p.orientation hF hσ = p.orientation hF hσ' :=
  SmoothTwoForm.IsNondegenerate.orientation_eq_of_tames _ hF _ (p.tames_mpullback hσ)
    (p.tames_mpullback hσ')

/-- The complex orientation of the identity of `(S, j)` is the symplectic orientation of any form
`τ` taming `j`. -/
@[simp]
theorem orientation_id {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ConnectedSpace S] [ChartedSpace F S] [IsManifold 𝓘(ℝ, F) ∞ S]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, F) S} {τ : SmoothTwoForm 𝓘(ℝ, F) S}
    (hτ : τ.Tames j) :
    (CompactConnectedPseudoholomorphicEmbedding.id F S j).orientation hF hτ =
      hτ.isNondegenerate.orientation hF :=
  SmoothTwoForm.IsNondegenerate.orientation_eq_of_tames _ hF _
    ((CompactConnectedPseudoholomorphicEmbedding.id F S j).tames_mpullback hτ) hτ

/-- The reparametrization preserves the complex orientations. -/
theorem isOrientationPreservingAt_reparam (hσ : σ.Tames J) (h : range p = range q)
    (x : p.Source) :
    Manifold.Orientation.IsOrientationPreservingAt (p.orientation hF hσ) (q.orientation hF' hσ)
      (p.reparam q h) x :=
  SmoothTwoForm.IsNondegenerate.isOrientationPreservingAt_orientation _ hF
    (q.tames_mpullback hσ).isNondegenerate hF' (p.reparam q h).contMDiff
    (p.mpullback_reparam q h) x

end Orientation

end CompactConnectedPseudoholomorphicEmbedding

namespace CompactConnectedPseudoholomorphicEmbedding

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (p q : CompactConnectedPseudoholomorphicEmbedding J F) {n : ℕ} (hF : finrank ℝ F = n + 1)

/-- The **homology class** `u_*[S] ∈ Hₙ₊₁(M; ℤ)` carried by a pseudoholomorphic embedding
`u : S → M`, for the complex orientation of `S`. -/
def homologyClass (hσ : σ.Tames J) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  ((p.orientation hF hσ).toHomologicalOrientation hF).mapFundamentalClass hF p.toContinuousMap

theorem homologyClass_def (hσ : σ.Tames J) :
    p.homologyClass hF hσ =
      ((p.orientation hF hσ).toHomologicalOrientation hF).mapFundamentalClass hF
        p.toContinuousMap :=
  (rfl)

/-- The class `u_*[S]` does not depend on the form taming `J` used to orient `S`. -/
theorem homologyClass_eq_of_tames {σ' : SmoothTwoForm I M} (hσ : σ.Tames J)
    (hσ' : σ'.Tames J) : p.homologyClass hF hσ = p.homologyClass hF hσ' := by
  rw [homologyClass_def, homologyClass_def, p.orientation_eq_of_tames hF hσ hσ']

/-- The reparametrization has degree one. -/
theorem degree_reparam (hσ : σ.Tames J) (h : range p = range q) :
    ((p.orientation hF hσ).toHomologicalOrientation hF).degree
      ((q.orientation hF hσ).toHomologicalOrientation hF) hF
        ((p.reparam q h).toHomeomorph : C(p.Source, q.Source)) = 1 := by
  set φ := ((p.reparam q h).toHomeomorph : C(p.Source, q.Source))
  obtain ⟨x⟩ := (inferInstance : Nonempty p.Source)
  have hfib : φ ⁻¹' {φ x} = {x} := by
    ext y
    exact (p.reparam q h).injective.eq_iff
  have hpres := p.isOrientationPreservingAt_reparam q hF hF hσ h x
  rw [← HomologicalOrientation.localDegree_eq_degree _ _ hF hF φ.continuous.isProperMap (φ x),
    HomologicalOrientation.localDegree_eq_localIndex _ _ hF hF φ hfib,
    Manifold.Orientation.localIndex_toHomologicalOrientation hF _ _ φ hpres.isInvertible_mfderiv]
  exact Manifold.Orientation.orientationSign_of_isOrientationPreservingAt hpres

/-- **The class of a pseudoholomorphic embedding depends only on its image.** If two smooth
pseudoholomorphic embeddings of compact connected manifolds have the same image, then they carry
the same class `u₁_*[S₁] = u₂_*[S₂]` for the complex orientations. -/
theorem homologyClass_eq_of_range_eq (hσ : σ.Tames J) (h : range p = range q) :
    p.homologyClass hF hσ = q.homologyClass hF hσ := by
  have hcomp : q.toContinuousMap.comp ((p.reparam q h).toHomeomorph : C(p.Source, q.Source)) =
      p.toContinuousMap :=
    ContinuousMap.ext (p.apply_reparam q h)
  rw [homologyClass_def, homologyClass_def, ← hcomp,
    HomologicalOrientation.mapFundamentalClass_comp_eq_degree_smul _ _ hF hF,
    p.degree_reparam q hF hσ h, one_smul]

/-- The identity of a compact connected almost complex manifold `(S, j)` carries the fundamental
class of `S` for its complex orientation, the symplectic orientation of any form taming `j`. -/
@[simp]
theorem homologyClass_id {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ConnectedSpace S] [ChartedSpace F S] [IsManifold 𝓘(ℝ, F) ∞ S]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, F) S} {τ : SmoothTwoForm 𝓘(ℝ, F) S}
    (hτ : τ.Tames j) :
    (CompactConnectedPseudoholomorphicEmbedding.id F S j).homologyClass hF hτ =
      ((hτ.isNondegenerate.orientation hF).toHomologicalOrientation hF).fundamentalClass hF := by
  rw [homologyClass_def, orientation_id, toContinuousMap_id]
  exact HomologicalOrientation.mapFundamentalClass_id _ hF

end CompactConnectedPseudoholomorphicEmbedding

variable (J) in
/-- A subset `C ⊆ M` is a **closed connected embedded `J`-holomorphic curve** when it is the image
of a smooth pseudoholomorphic embedding of a compact connected surface without boundary, a
manifold modelled on `ℂ`. -/
def IsClosedConnectedEmbeddedPseudoholomorphicCurve (C : Set M) : Prop :=
  ∃ p : CompactConnectedPseudoholomorphicEmbedding J ℂ, range p = C

theorem isClosedConnectedEmbeddedPseudoholomorphicCurve_iff {C : Set M} :
    IsClosedConnectedEmbeddedPseudoholomorphicCurve J C ↔
      ∃ p : CompactConnectedPseudoholomorphicEmbedding J ℂ, range p = C :=
  Iff.rfl

namespace CompactConnectedPseudoholomorphicEmbedding

/-- The image of a pseudoholomorphic embedding of a compact connected surface is a closed
connected embedded `J`-holomorphic curve. -/
@[simp]
theorem isClosedConnectedEmbeddedPseudoholomorphicCurve_range
    (p : CompactConnectedPseudoholomorphicEmbedding J ℂ) :
    IsClosedConnectedEmbeddedPseudoholomorphicCurve J (range p) :=
  ⟨p, rfl⟩

end CompactConnectedPseudoholomorphicEmbedding

namespace IsClosedConnectedEmbeddedPseudoholomorphicCurve

variable {C : Set M}

/-- A closed connected embedded `J`-holomorphic curve is compact. -/
theorem isCompact (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) : IsCompact C := by
  obtain ⟨p, rfl⟩ := hC
  exact isCompact_range p.continuous

/-- A closed connected embedded `J`-holomorphic curve is connected, and in particular nonempty. -/
theorem isConnected (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) :
    IsConnected C := by
  obtain ⟨p, rfl⟩ := hC
  exact isConnected_range p.continuous

/-- A closed connected embedded `J`-holomorphic curve is nonempty. -/
theorem nonempty (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) : C.Nonempty :=
  hC.isConnected.nonempty

end IsClosedConnectedEmbeddedPseudoholomorphicCurve

/-- The empty set is not a closed connected embedded `J`-holomorphic curve. -/
@[simp]
theorem not_isClosedConnectedEmbeddedPseudoholomorphicCurve_empty :
    ¬ IsClosedConnectedEmbeddedPseudoholomorphicCurve J (∅ : Set M) :=
  fun h ↦ Set.not_nonempty_empty h.nonempty

namespace IsClosedConnectedEmbeddedPseudoholomorphicCurve

variable {C : Set M}

/-- The **homology class** `[C] ∈ H₂(M; ℤ)` of a closed connected embedded `J`-holomorphic curve
`C`: the class `u_*[S]` of any parametrization `u : S → M` of `C`, with the complex orientation of
`S` (`TauCeti.IsClosedConnectedEmbeddedPseudoholomorphicCurve.homologyClass_eq`). -/
def homologyClass (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) (hσ : σ.Tames J) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  hC.choose.homologyClass Complex.finrank_real_complex hσ

/-- The class of a closed connected embedded `J`-holomorphic curve is the class carried by any of
its parametrizations. -/
theorem homologyClass_eq (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C)
    (hσ : σ.Tames J) (p : CompactConnectedPseudoholomorphicEmbedding J ℂ) (hp : range p = C) :
    hC.homologyClass hσ = p.homologyClass Complex.finrank_real_complex hσ :=
  hC.choose.homologyClass_eq_of_range_eq p _ hσ (hC.choose_spec.trans hp.symm)

/-- The class of the image of `p` is the class carried by `p`. -/
@[simp]
theorem homologyClass_range (p : CompactConnectedPseudoholomorphicEmbedding J ℂ)
    (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J (range p)) (hσ : σ.Tames J) :
    hC.homologyClass hσ = p.homologyClass Complex.finrank_real_complex hσ :=
  hC.homologyClass_eq hσ p rfl

/-- The class of a closed connected embedded `J`-holomorphic curve does not depend on the form
taming `J`. -/
theorem homologyClass_eq_of_tames (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C)
    {σ' : SmoothTwoForm I M} (hσ : σ.Tames J) (hσ' : σ'.Tames J) :
    hC.homologyClass hσ = hC.homologyClass hσ' :=
  hC.choose.homologyClass_eq_of_tames _ hσ hσ'

end IsClosedConnectedEmbeddedPseudoholomorphicCurve

variable (J) in
/-- A **configuration of embedded `J`-holomorphic curves**: a finitely supported multiplicity
function `m` on subsets of `M` whose support consists of pairwise disjoint closed connected
embedded `J`-holomorphic curves `C`, each counted with the positive multiplicity `m C`. -/
@[ext]
structure EmbeddedCurveConfiguration where
  /-- The multiplicity of each curve; its support is the set of curves of the configuration. -/
  mult : Set M →₀ ℕ
  /-- Every curve of the configuration is a closed connected embedded `J`-holomorphic curve. -/
  isClosedConnectedEmbeddedPseudoholomorphicCurve :
    ∀ C ∈ mult.support, IsClosedConnectedEmbeddedPseudoholomorphicCurve J C
  /-- Distinct curves of the configuration are disjoint. -/
  pairwiseDisjoint : (mult.support : Set (Set M)).PairwiseDisjoint id

namespace EmbeddedCurveConfiguration

open Classical in
/-- The **homology class of a curve** as a function on all subsets of `M`: the class
`[C] ∈ H₂(M; ℤ)` of a closed connected embedded `J`-holomorphic curve `C`, extended by `0` to
the other subsets. A configuration has the class `∑ m_C [C]` of this function. -/
def curveHomologyClass (hσ : σ.Tames J) (C : Set M) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  if hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C then hC.homologyClass hσ else 0

/-- On a closed connected embedded `J`-holomorphic curve, `curveHomologyClass` is its class. -/
@[simp]
theorem curveHomologyClass_eq (hσ : σ.Tames J) {C : Set M}
    (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) :
    curveHomologyClass hσ C = hC.homologyClass hσ :=
  dite_eq_left hC

/-- Off the closed connected embedded `J`-holomorphic curves, `curveHomologyClass` is `0`. -/
@[simp]
theorem curveHomologyClass_eq_zero (hσ : σ.Tames J) {C : Set M}
    (hC : ¬ IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) :
    curveHomologyClass hσ C = 0 :=
  dite_eq_right hC

/-- The curve classes do not depend on the form taming `J`. -/
theorem curveHomologyClass_eq_of_tames {σ' : SmoothTwoForm I M} (hσ : σ.Tames J)
    (hσ' : σ'.Tames J) : curveHomologyClass hσ = curveHomologyClass hσ' := by
  funext C
  by_cases hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C
  · rw [curveHomologyClass_eq hσ hC, curveHomologyClass_eq hσ' hC,
      hC.homologyClass_eq_of_tames hσ hσ']
  · rw [curveHomologyClass_eq_zero hσ hC, curveHomologyClass_eq_zero hσ' hC]

/-- The **homology class** `∑ m_C [C] ∈ H₂(M; ℤ)` of a configuration of embedded `J`-holomorphic
curves. -/
def homologyClass (c : EmbeddedCurveConfiguration J) (hσ : σ.Tames J) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M) :=
  Finsupp.linearCombination ℕ (curveHomologyClass hσ) c.mult

theorem homologyClass_def (c : EmbeddedCurveConfiguration J) (hσ : σ.Tames J) :
    c.homologyClass hσ = Finsupp.linearCombination ℕ (curveHomologyClass hσ) c.mult :=
  (rfl)

/-- The class of a configuration computed from any parametrizations `p C` of its curves. -/
theorem homologyClass_eq_sum (c : EmbeddedCurveConfiguration J) (hσ : σ.Tames J)
    (p : ∀ C ∈ c.mult.support, CompactConnectedPseudoholomorphicEmbedding J ℂ)
    (hp : ∀ C (hC : C ∈ c.mult.support), range (p C hC) = C) :
    c.homologyClass hσ = ∑ C ∈ c.mult.support.attach,
      c.mult C • (p C C.2).homologyClass Complex.finrank_real_complex hσ := by
  rw [homologyClass_def, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [curveHomologyClass_eq hσ (c.isClosedConnectedEmbeddedPseudoholomorphicCurve C C.2),
    IsClosedConnectedEmbeddedPseudoholomorphicCurve.homologyClass_eq _ hσ _ (hp C C.2)]

/-- The class of a configuration does not depend on the form taming `J`. -/
theorem homologyClass_eq_of_tames (c : EmbeddedCurveConfiguration J) {σ' : SmoothTwoForm I M}
    (hσ : σ.Tames J) (hσ' : σ'.Tames J) : c.homologyClass hσ = c.homologyClass hσ' := by
  rw [homologyClass_def, homologyClass_def, curveHomologyClass_eq_of_tames hσ hσ']

/-- **Configurations are the compatible configurations of embedded curves.** A finitely
supported multiplicity function `l` on subsets of `M` lies in `TauCeti.compatibleConfigurations`
for disjointness as compatibility, the curve classes `curveHomologyClass hσ`, the closed connected
embedded `J`-holomorphic curves as candidates and the class `A` exactly when it is the
multiplicity function of a configuration of class `A`. -/
theorem mem_compatibleConfigurations_iff (hσ : σ.Tames J) {l : Set M →₀ ℕ}
    {A : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of M)} :
    l ∈ compatibleConfigurations Disjoint (curveHomologyClass hσ)
        {C | IsClosedConnectedEmbeddedPseudoholomorphicCurve J C} A ↔
      ∃ c : EmbeddedCurveConfiguration J, c.mult = l ∧ c.homologyClass hσ = A := by
  rw [mem_compatibleConfigurations]
  constructor
  · rintro ⟨hs, hd, hA⟩
    exact ⟨⟨l, fun C hC ↦ hs hC, hd⟩, rfl, hA⟩
  · rintro ⟨c, rfl, rfl⟩
    exact ⟨fun C hC ↦ c.isClosedConnectedEmbeddedPseudoholomorphicCurve C hC,
      c.pairwiseDisjoint, rfl⟩

/-- The multiplicity function of a configuration is a compatible configuration of embedded curves
in the class of the configuration. -/
theorem mult_mem_compatibleConfigurations (c : EmbeddedCurveConfiguration J) (hσ : σ.Tames J) :
    c.mult ∈ compatibleConfigurations Disjoint (curveHomologyClass hσ)
      {C | IsClosedConnectedEmbeddedPseudoholomorphicCurve J C} (c.homologyClass hσ) :=
  (mem_compatibleConfigurations_iff hσ).2 ⟨c, rfl, rfl⟩

/-- The empty configuration, with no curves. -/
instance : Zero (EmbeddedCurveConfiguration J) :=
  ⟨⟨0, by simp, by simp⟩⟩

@[simp]
theorem mult_zero : (0 : EmbeddedCurveConfiguration J).mult = 0 :=
  (rfl)

/-- A configuration is empty exactly when all its multiplicities vanish. -/
@[simp]
theorem mult_eq_zero {c : EmbeddedCurveConfiguration J} : c.mult = 0 ↔ c = 0 := by
  rw [EmbeddedCurveConfiguration.ext_iff, mult_zero]

/-- The empty configuration has class zero. -/
@[simp]
theorem homologyClass_zero (hσ : σ.Tames J) :
    (0 : EmbeddedCurveConfiguration J).homologyClass hσ = 0 := by
  rw [homologyClass_def, mult_zero, map_zero]

/-- The configuration consisting of one closed connected embedded `J`-holomorphic curve `C` with
multiplicity `m`; for `m = 0` this is the empty configuration. -/
def single {C : Set M} (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) (m : ℕ) :
    EmbeddedCurveConfiguration J where
  mult := Finsupp.single C m
  isClosedConnectedEmbeddedPseudoholomorphicCurve D hD := by
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hD)
    exact hC
  pairwiseDisjoint := (Set.pairwiseDisjoint_singleton C id).subset <| by
    rw [← Finset.coe_singleton, Finset.coe_subset]
    exact Finsupp.support_single_subset

@[simp]
theorem mult_single {C : Set M} (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C)
    (m : ℕ) : (single hC m).mult = Finsupp.single C m :=
  (rfl)

/-- The configuration of one curve with multiplicity `m` is empty exactly when `m = 0`. -/
@[simp]
theorem single_eq_zero {C : Set M} (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C)
    {m : ℕ} : single hC m = 0 ↔ m = 0 := by
  rw [← mult_eq_zero, mult_single, Finsupp.single_eq_zero]

theorem single_zero {C : Set M} (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C) :
    single hC 0 = (0 : EmbeddedCurveConfiguration J) :=
  (single_eq_zero hC).2 rfl

/-- The configuration of one curve `C` with multiplicity `m` has class `m • [C]`. -/
@[simp]
theorem homologyClass_single {C : Set M} (hC : IsClosedConnectedEmbeddedPseudoholomorphicCurve J C)
    (m : ℕ) (hσ : σ.Tames J) : (single hC m).homologyClass hσ = m • hC.homologyClass hσ := by
  rw [homologyClass_def, mult_single, Finsupp.linearCombination_single,
    curveHomologyClass_eq hσ hC]

/-- The **sum** of two configurations whose distinct curves are disjoint: a curve of either
configuration is counted with the sum of its multiplicities in the two. -/
def add (c₁ c₂ : EmbeddedCurveConfiguration J)
    (h : ∀ C ∈ c₁.mult.support, ∀ D ∈ c₂.mult.support, C ≠ D → Disjoint C D) :
    EmbeddedCurveConfiguration J where
  mult := c₁.mult + c₂.mult
  isClosedConnectedEmbeddedPseudoholomorphicCurve C hC := by
    classical
    exact (Finset.mem_union.1 (Finsupp.support_add hC)).elim
      (c₁.isClosedConnectedEmbeddedPseudoholomorphicCurve C)
      (c₂.isClosedConnectedEmbeddedPseudoholomorphicCurve C)
  pairwiseDisjoint := by
    classical
    refine (Set.pairwiseDisjoint_union.2 ⟨c₁.pairwiseDisjoint, c₂.pairwiseDisjoint,
      fun C hC D hD ↦ h C hC D hD⟩).subset ?_
    rw [← Finset.coe_union, Finset.coe_subset]
    exact Finsupp.support_add

@[simp]
theorem mult_add (c₁ c₂ : EmbeddedCurveConfiguration J)
    (h : ∀ C ∈ c₁.mult.support, ∀ D ∈ c₂.mult.support, C ≠ D → Disjoint C D) :
    (c₁.add c₂ h).mult = c₁.mult + c₂.mult :=
  (rfl)

/-- The class of the sum of two configurations is the sum of their classes. -/
@[simp]
theorem homologyClass_add (c₁ c₂ : EmbeddedCurveConfiguration J)
    (h : ∀ C ∈ c₁.mult.support, ∀ D ∈ c₂.mult.support, C ≠ D → Disjoint C D) (hσ : σ.Tames J) :
    (c₁.add c₂ h).homologyClass hσ = c₁.homologyClass hσ + c₂.homologyClass hσ := by
  rw [homologyClass_def, homologyClass_def, homologyClass_def, mult_add, map_add]

end EmbeddedCurveConfiguration

end TauCeti
