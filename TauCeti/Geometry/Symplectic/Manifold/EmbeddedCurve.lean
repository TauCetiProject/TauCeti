/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.AlgebraicTopology.Singular.MinimalGenus
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Embedded pseudoholomorphic curves, their classes and their configurations

Taubes's count of pseudoholomorphic curves in a symplectic four-manifold `X` with a compatible
almost complex structure `J` runs over *configurations*: finite unordered families `{(C_a, m_a)}`
of distinct, mutually disjoint, connected, closed, embedded `J`-holomorphic images `C_a` with
positive integer multiplicities `m_a`, whose total class `∑ m_a [C_a]` is a given integral class
`A ∈ H₂(X; ℤ)`. A configuration records images, not parametrizations, so the class `[C_a]` of an
image has to be read off any of its parametrizations. This file constructs these objects for an
almost complex manifold `(X, J)` modelled on a real normed space.

* An **embedded pseudoholomorphic curve** (`TauCeti.EmbeddedPseudoholomorphicCurve J`) is a
  compact connected Riemann surface `Σ` with an injective `C¹` immersion `u : Σ → X` which is
  `J`-holomorphic. Since `Σ` is compact, `u` is a `C¹` embedding as soon as `X` is Hausdorff
  (`TauCeti.EmbeddedPseudoholomorphicCurve.isSmoothEmbedding`). Its class is
  `u_*[Σ] ∈ H₂(X; ℤ)` (`TauCeti.EmbeddedPseudoholomorphicCurve.homologyClass`), the image of the
  fundamental class of `Σ` for its complex orientation (`TauCeti.complexFundamentalClass`).
* **Two parametrizations of one image differ by a biholomorphism.** If `u : Σ → X` and
  `u' : Σ' → X` are embedded pseudoholomorphic curves with the same image, then `e = u'⁻¹ ∘ u` is
  a homeomorphism; it is `C¹` because `u'` is an immersion (`ContMDiff.iff_comp_isImmersion`),
  and its derivative is complex linear because `du' ∘ de = du` intertwines the complex structures
  of `Σ` and `Σ'` with `J` and `du'` is injective (`TauCeti.IsPseudoholomorphicAt.of_comp`). So
  `e` is a biholomorphism `Σ ≃ Σ'` with `u' ∘ e = u`
  (`TauCeti.EmbeddedPseudoholomorphicCurve.reparam`). Biholomorphisms preserve the complex
  orientation, hence the fundamental class, so **the class depends only on the image**:
  `u_*[Σ] = u'_*[Σ']` (`TauCeti.EmbeddedPseudoholomorphicCurve.homologyClass_eq_of_range_eq`).
  Here the `J`-holomorphicity of both maps matters: it makes the reparametrization holomorphic,
  hence orientation preserving, and not merely a diffeomorphism.
* An **embedded pseudoholomorphic image** (`TauCeti.IsEmbeddedPseudoholomorphicImage J S`) is a
  subset `S ⊆ X` which is the image of an embedded pseudoholomorphic curve. It is nonempty,
  compact and connected, and closed when `X` is Hausdorff. Its class
  `TauCeti.embeddedCurveClass J S` is the class of any of its parametrizations
  (`TauCeti.embeddedCurveClass_range`).
* The **configurations** in class `A` (`TauCeti.embeddedCurveConfigurations J A`) are the
  multiplicity functions `l : Set X →₀ ℕ` whose support consists of pairwise disjoint embedded
  pseudoholomorphic images with `∑ l S • [S] = A`
  (`TauCeti.mem_embeddedCurveConfigurations`). This is the set
  `TauCeti.compatibleConfigurations` of the abstract weighted count
  (`TauCeti.configurationCount`), with the images as candidates, their classes and disjointness
  as compatibility. An image `S` taken with multiplicity `m` is a configuration in class
  `m • [S]` (`TauCeti.single_mem_embeddedCurveConfigurations_iff`); it is a different
  configuration from a single embedded image whose class is the divisible class `m • [S]`.

Every compact connected Riemann surface is an embedded pseudoholomorphic curve in itself, through
the identity, with class its fundamental class
(`TauCeti.EmbeddedPseudoholomorphicCurve.homologyClass_id`).

The intersection forms on `H₂(X; ℤ)` that pair these classes are the `ℤ`-bilinear forms
`TauCeti.IntersectionForm X` for the `ℤ`-module structure `AddCommGroup.toIntModule`, the one the
abstract counts and cycles over an additive group use, with symmetry
`TauCeti.IntersectionForm.IsSymm`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893, §1.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), §2.1.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

/-- The `ℤ`-bilinear forms on `H₂(X; ℤ)`, such as the intersection form of a closed oriented
four-manifold `X`. They are bilinear for the `ℤ`-module structure `AddCommGroup.toIntModule`, the
one the abstract counts and cycles over an additive group use, rather than for the `ModuleCat ℤ`
structure of `secondHomology X`, which agrees with it only propositionally. -/
abbrev IntersectionForm (X : Type) [TopologicalSpace X] : Type :=
  @LinearMap.BilinForm ℤ _ (secondHomology X) _ (AddCommGroup.toIntModule _)

/-- An intersection form `B : TauCeti.IntersectionForm X` is **symmetric**,
`LinearMap.BilinForm.IsSymm` for the `ℤ`-module structure `AddCommGroup.toIntModule`. -/
abbrev IntersectionForm.IsSymm {X : Type} [TopologicalSpace X] (B : IntersectionForm X) : Prop :=
  @LinearMap.BilinForm.IsSymm ℤ (secondHomology X) _ _ (AddCommGroup.toIntModule _) B

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]

variable (J : SmoothAlmostComplexStructure I X)

/-- An **embedded closed pseudoholomorphic curve** in an almost complex manifold `(X, J)`: a
compact connected Riemann surface `Σ` with an injective immersion `u : Σ → X` which is
`J`-holomorphic for the complex structure of `Σ`. -/
structure EmbeddedPseudoholomorphicCurve where
  /-- The parametrizing Riemann surface. -/
  carrier : Type
  /-- The topology of the Riemann surface. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The Riemann surface is Hausdorff. -/
  [t2Space : T2Space carrier]
  /-- The holomorphic charts of the Riemann surface. -/
  [chartedSpace : ChartedSpace ℂ carrier]
  /-- The charts form a complex manifold. -/
  [isManifold : IsManifold 𝓘(ℂ) ∞ carrier]
  /-- The Riemann surface is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The Riemann surface is connected. -/
  [connectedSpace : ConnectedSpace carrier]
  /-- The parametrization. -/
  toFun : carrier → X
  /-- The parametrization is a `C¹` immersion of the underlying real surface. -/
  isImmersion : Manifold.IsImmersion 𝓘(ℝ, ℂ) I 1 toFun
  /-- The parametrization is injective. -/
  injective : Function.Injective toFun
  /-- The parametrization is `J`-holomorphic. -/
  isPseudoholomorphic : IsPseudoholomorphic (ofComplexManifold ℂ carrier) J toFun

namespace EmbeddedPseudoholomorphicCurve

attribute [instance] topologicalSpace t2Space chartedSpace isManifold compactSpace connectedSpace

variable {J} (C C' : EmbeddedPseudoholomorphicCurve J)

/-- The parametrization of an embedded pseudoholomorphic curve is continuous. -/
theorem continuous : Continuous C.toFun :=
  C.isImmersion.contMDiff.continuous

/-- The parametrization as a continuous map. -/
def toContinuousMap : C(C.carrier, X) :=
  ⟨C.toFun, C.continuous⟩

@[simp]
theorem coe_toContinuousMap : ⇑C.toContinuousMap = C.toFun :=
  (rfl)

/-- The **homology class** `u_*[Σ] ∈ H₂(X; ℤ)` of an embedded pseudoholomorphic curve: the image
of the fundamental class of the parametrizing Riemann surface, for its complex orientation. -/
def homologyClass : secondHomology X :=
  (complexHomologicalOrientation C.carrier).mapFundamentalClass Complex.finrank_real_complex
    C.toContinuousMap

theorem homologyClass_def :
    C.homologyClass = (complexHomologicalOrientation C.carrier).mapFundamentalClass
      Complex.finrank_real_complex C.toContinuousMap :=
  (rfl)

/-- A map `e` between the parametrizing surfaces of two embedded pseudoholomorphic curves with
`u' ∘ e = u` is holomorphic, as soon as it is continuous: the immersion `u'` makes `e` a `C¹` map,
and the Cauchy–Riemann equations of `u` and `u'` together with the injectivity of `du'` make its
derivative complex linear. -/
theorem mdifferentiable_of_toFun_comp_eq {e : C.carrier → C'.carrier} (he : Continuous e)
    (hcomp : C'.toFun ∘ e = C.toFun) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e := fun x ↦ by
  refine isPseudoholomorphicAt_ofComplexManifold_iff.1 ?_
  refine IsPseudoholomorphicAt.of_comp (v := C'.toFun) ?_
    (isPseudoholomorphic_iff.1 C'.isPseudoholomorphic (e x))
    (C'.isImmersion.mfderiv_injective one_ne_zero (e x))
    (((ContMDiff.iff_comp_isImmersion C'.isImmersion).2
      ⟨he, hcomp.symm ▸ C.isImmersion.contMDiff⟩).mdifferentiable one_ne_zero x)
  rw [hcomp]
  exact isPseudoholomorphic_iff.1 C.isPseudoholomorphic x

variable [T2Space X]

/-- The parametrization of an embedded pseudoholomorphic curve is a `C¹` embedding: an injective
continuous map from a compact space to a Hausdorff one is a topological embedding. -/
theorem isSmoothEmbedding : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℂ) I 1 C.toFun :=
  ⟨C.isImmersion, (C.continuous.isClosedEmbedding C.injective).isEmbedding⟩

/-- The reparametrization between two embedded pseudoholomorphic curves with the same image, as a
homeomorphism of the parametrizing surfaces. -/
private def reparamHomeomorph (h : range C.toFun = range C'.toFun) : C.carrier ≃ₜ C'.carrier :=
  ((C.continuous.isClosedEmbedding C.injective).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr h)).trans
    (C'.continuous.isClosedEmbedding C'.injective).isEmbedding.toHomeomorph.symm

private theorem toFun_reparamHomeomorph (h : range C.toFun = range C'.toFun) (x : C.carrier) :
    C'.toFun (reparamHomeomorph C C' h x) = C.toFun x :=
  congrArg Subtype.val
    ((C'.continuous.isClosedEmbedding C'.injective).isEmbedding.toHomeomorph.apply_symm_apply
      ⟨C.toFun x, h ▸ mem_range_self x⟩)

/-- **Parametrizations of an embedded image differ by a biholomorphism.** Two embedded
pseudoholomorphic curves `u : Σ → X` and `u' : Σ' → X` with the same image are related by the
biholomorphism `u'⁻¹ ∘ u : Σ ≃ Σ'` (`TauCeti.EmbeddedPseudoholomorphicCurve.toFun_reparam`). -/
def reparam (h : range C.toFun = range C'.toFun) :
    C.carrier ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ C'.carrier where
  toEquiv := (reparamHomeomorph C C' h).toEquiv
  contMDiff_toFun := (mdifferentiable_of_toFun_comp_eq C C' (reparamHomeomorph C C' h).continuous
    (funext (toFun_reparamHomeomorph C C' h))).contMDiff
  contMDiff_invFun := by
    refine (mdifferentiable_of_toFun_comp_eq C' C (reparamHomeomorph C C' h).symm.continuous ?_
      ).contMDiff
    funext y
    rw [Function.comp_apply, ← toFun_reparamHomeomorph C C' h, Homeomorph.apply_symm_apply]

/-- The reparametrization `e : Σ ≃ Σ'` between two parametrizations of one image satisfies
`u' ∘ e = u`. -/
@[simp]
theorem toFun_reparam (h : range C.toFun = range C'.toFun) (x : C.carrier) :
    C'.toFun (reparam C C' h x) = C.toFun x :=
  toFun_reparamHomeomorph C C' h x

/-- The inverse of the reparametrization `e : Σ ≃ Σ'` satisfies `u ∘ e⁻¹ = u'`. -/
@[simp]
theorem toFun_reparam_symm (h : range C.toFun = range C'.toFun) (y : C'.carrier) :
    C.toFun ((reparam C C' h).symm y) = C'.toFun y := by
  rw [← toFun_reparam C C' h, Diffeomorph.apply_symm_apply]

/-- **The class of an embedded curve depends only on its image.** Two embedded pseudoholomorphic
curves with the same image have the same homology class. -/
theorem homologyClass_eq_of_range_eq (h : range C.toFun = range C'.toFun) :
    C.homologyClass = C'.homologyClass := by
  have hcomp :
      C'.toContinuousMap.comp ((reparam C C' h).toHomeomorph : C(C.carrier, C'.carrier)) =
        C.toContinuousMap := by
    ext x
    exact toFun_reparam C C' h x
  rw [homologyClass_def, homologyClass_def, ← hcomp]
  exact (reparam C C' h).mapFundamentalClass_complexHomologicalOrientation_comp
    C'.toContinuousMap

/-- **A compact connected Riemann surface in itself.** The identity of a compact connected Riemann
surface `Σ` is an embedded pseudoholomorphic curve for the almost complex structure of `Σ`. -/
protected def id (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ∞ S] [CompactSpace S] [ConnectedSpace S] :
    EmbeddedPseudoholomorphicCurve (ofComplexManifold ℂ S) where
  carrier := S
  toFun := _root_.id
  isImmersion := Manifold.IsImmersion.id
  injective := Function.injective_id
  isPseudoholomorphic := isPseudoholomorphic_ofComplexManifold_iff.2 mdifferentiable_id

/-- The class of a compact connected Riemann surface in itself is its fundamental class. -/
@[simp]
theorem homologyClass_id (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ∞ S] [CompactSpace S] [ConnectedSpace S] :
    (EmbeddedPseudoholomorphicCurve.id S).homologyClass = complexFundamentalClass S := by
  rw [complexFundamentalClass_def,
    ← (complexHomologicalOrientation S).mapFundamentalClass_id Complex.finrank_real_complex]
  -- The parametrizing surface of `EmbeddedPseudoholomorphicCurve.id S` is `S`, and its
  -- parametrization is the identity.
  rfl

end EmbeddedPseudoholomorphicCurve

/-! ### Embedded pseudoholomorphic images -/

/-- A subset `S` of `X` is an **embedded pseudoholomorphic image** when it is the image of an
embedded pseudoholomorphic curve: a connected closed embedded `J`-holomorphic curve, with its
parametrization forgotten. -/
def IsEmbeddedPseudoholomorphicImage (S : Set X) : Prop :=
  ∃ C : EmbeddedPseudoholomorphicCurve J, range C.toFun = S

/-- The **class** `[S] ∈ H₂(X; ℤ)` of an embedded pseudoholomorphic image `S`: the class `u_*[Σ]`
of any embedded pseudoholomorphic curve `u : Σ → X` with image `S` when `X` is Hausdorff
(`TauCeti.embeddedCurveClass_range`). It is `0` for a subset which is not such an image. -/
def embeddedCurveClass (S : Set X) : secondHomology X :=
  open Classical in
  if h : IsEmbeddedPseudoholomorphicImage J S then h.choose.homologyClass else 0

/-- The **configurations of embedded pseudoholomorphic curves** in class `A ∈ H₂(X; ℤ)`: the finite
unordered families `{(C_a, m_a)}` of distinct, mutually disjoint embedded pseudoholomorphic
images `C_a` with positive multiplicities `m_a` and `∑ m_a [C_a] = A`. A configuration is recorded
as its multiplicity function `Set X →₀ ℕ`, which forgets the parametrizations of the images. -/
def embeddedCurveConfigurations (A : secondHomology X) : Set (Set X →₀ ℕ) :=
  compatibleConfigurations Disjoint (embeddedCurveClass J)
    {S | IsEmbeddedPseudoholomorphicImage J S} A

variable {J}

/-- A subset is an embedded pseudoholomorphic image exactly when it is the image of an embedded
pseudoholomorphic curve. -/
theorem isEmbeddedPseudoholomorphicImage_iff {S : Set X} :
    IsEmbeddedPseudoholomorphicImage J S ↔
      ∃ C : EmbeddedPseudoholomorphicCurve J, range C.toFun = S :=
  Iff.rfl

/-- The configurations of embedded pseudoholomorphic curves are the compatible configurations of
pairwise disjoint embedded pseudoholomorphic images. -/
theorem embeddedCurveConfigurations_def (A : secondHomology X) :
    embeddedCurveConfigurations J A =
      compatibleConfigurations Disjoint (embeddedCurveClass J)
        {S | IsEmbeddedPseudoholomorphicImage J S} A :=
  (rfl)

/-- The image of an embedded pseudoholomorphic curve is an embedded pseudoholomorphic image. -/
theorem EmbeddedPseudoholomorphicCurve.isEmbeddedPseudoholomorphicImage
    (C : EmbeddedPseudoholomorphicCurve J) : IsEmbeddedPseudoholomorphicImage J (range C.toFun) :=
  ⟨C, rfl⟩

namespace IsEmbeddedPseudoholomorphicImage

variable {S : Set X}

/-- An embedded pseudoholomorphic image is compact. -/
theorem isCompact (hS : IsEmbeddedPseudoholomorphicImage J S) : IsCompact S := by
  obtain ⟨C, rfl⟩ := hS
  exact isCompact_range C.continuous

/-- An embedded pseudoholomorphic image is connected, in particular nonempty. -/
theorem isConnected (hS : IsEmbeddedPseudoholomorphicImage J S) : IsConnected S := by
  obtain ⟨C, rfl⟩ := hS
  exact isConnected_range C.continuous

/-- An embedded pseudoholomorphic image is nonempty. -/
theorem nonempty (hS : IsEmbeddedPseudoholomorphicImage J S) : S.Nonempty :=
  hS.isConnected.nonempty

/-- An embedded pseudoholomorphic image in a Hausdorff manifold is closed. -/
theorem isClosed [T2Space X] (hS : IsEmbeddedPseudoholomorphicImage J S) : IsClosed S :=
  hS.isCompact.isClosed

end IsEmbeddedPseudoholomorphicImage

theorem embeddedCurveClass_of_not {S : Set X} (hS : ¬IsEmbeddedPseudoholomorphicImage J S) :
    embeddedCurveClass J S = 0 :=
  dite_eq_right hS

variable {A : secondHomology X} {l : Set X →₀ ℕ}

/-- A configuration in class `A` is a finitely supported multiplicity function on pairwise
disjoint embedded pseudoholomorphic images, the sum of whose classes with these multiplicities
is `A`. -/
@[simp]
theorem mem_embeddedCurveConfigurations :
    l ∈ embeddedCurveConfigurations J A ↔
      (∀ S ∈ l.support, IsEmbeddedPseudoholomorphicImage J S) ∧
        (l.support : Set (Set X)).Pairwise Disjoint ∧
          ∑ S ∈ l.support, l S • embeddedCurveClass J S = A := by
  simp only [embeddedCurveConfigurations, mem_compatibleConfigurations, Set.subset_def,
    Finset.mem_coe, Set.mem_ofPred_eq, Finsupp.linearCombination_apply, Finsupp.sum]

/-- The empty configuration is a configuration exactly in class `0`. -/
theorem zero_mem_embeddedCurveConfigurations_iff : 0 ∈ embeddedCurveConfigurations J A ↔ A = 0 :=
  zero_mem_compatibleConfigurations_iff

/-- A single image `S` taken with multiplicity `m ≠ 0` is a configuration exactly in the class
`m • [S]`. -/
theorem single_mem_embeddedCurveConfigurations_iff {S : Set X} {m : ℕ} (hm : m ≠ 0) :
    Finsupp.single S m ∈ embeddedCurveConfigurations J A ↔
      IsEmbeddedPseudoholomorphicImage J S ∧ m • embeddedCurveClass J S = A := by
  simp [mem_embeddedCurveConfigurations, Finsupp.support_single _ hm]

variable [T2Space X]

/-- The class of the image of an embedded pseudoholomorphic curve is the class of the curve. -/
@[simp]
theorem embeddedCurveClass_range (C : EmbeddedPseudoholomorphicCurve J) :
    embeddedCurveClass J (range C.toFun) = C.homologyClass := by
  rw [embeddedCurveClass, dite_eq_left C.isEmbeddedPseudoholomorphicImage]
  exact C.isEmbeddedPseudoholomorphicImage.choose.homologyClass_eq_of_range_eq C
    C.isEmbeddedPseudoholomorphicImage.choose_spec

end TauCeti
