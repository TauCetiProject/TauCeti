/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The fundamental class of a compact manifold relative to its collared boundary

Let `X` be a compact Hausdorff space, and let `ι : M → X` be an open embedding of a Hausdorff
space `M` modelled on a real normed space `E` of finite dimension `n`, a topological `n`-manifold
without boundary. Suppose that the complement of `ι(M)` is the image of a collared map
`f : N → X` (`TauCeti.IsCollared`): there is an open embedding `c : N × [0, 1) → X` with
`c (y, 0) = f y`. This is the situation of a compact topological manifold `X` with boundary
`∂X = f(N)` and interior `M`. For a compact manifold with boundary the half-space charts collar the
boundary locally (`TauCeti.isLocallyCollared_subtypeVal_boundary`,
`TauCeti.isCollared_subtypeVal_boundary`), and for a compact manifold with corners the quadrant
charts do
(`TauCeti.isLocallyCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant`,
`TauCeti.isCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant`). In both cases Brown's
collaring theorem (`TauCeti.IsLocallyCollared.isCollared`) assembles local collars of a compact
boundary into a global one, and the interior is a manifold without boundary
(`ModelWithCorners.instChartedSpaceInterior`, `ModelWithCorners.range_subtypeVal_interior`).

Let `R` be a module over a ring `Λ`. A family of local classes `α x ∈ Hₙ(M, M ∖ {x}; R)` invariant
under transport along paths is the family of interior local images of exactly one class of
`Hₙ(X, ∂X; R)` (`TauCeti.existsUnique_localHomologyRestriction_range_eq_of_invariant`): its image in
`Hₙ(X, X ∖ {ι x}; R) ≅ Hₙ(M, M ∖ {x}; R)` is `α x` at every point `x` of the interior. The class
is written in the local homology `Hₙ(X, X ∖ ι(M); R)` of `X` along `ι(M)`, since `X ∖ ι(M) = ∂X`.
Two families give the *fundamental class of `X` relative to its boundary*:

* with integral coefficients, the local orientations `o x` of an orientation `o` of `M` give the
  class `o.fundamentalClassRel hn hι hιf hf` of `Hₙ(X, ∂X; ℤ)`. Its image in
  `Hₙ(X, X ∖ ι(K); ℤ) ≅ Hₙ(M, M ∖ K; ℤ)` is the fundamental class of `M` along `K` for every
  compact `K ⊆ M`, and reversing the orientation negates it;
* with coefficients in a ring `K` whose only unit is `1`, such as `ZMod 2`, the local homology
  `Hₙ(M, M ∖ {x}; K) ≅ K` has a single generator, and transport preserves it. So `Hₙ(X, ∂X; K)`
  has exactly one class generating the local homology at every interior point
  (`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`), with no orientation of `M`:
  the mod `2` fundamental class relative to the boundary.

The proof follows Hatcher. For `0 < t`, let `Cₜ = c(N × [0, t))` be the collar of depth less than
`t` and `Kₜ = X ∖ Cₜ`. Then `Kₜ` is a compact subset of `ι(M)`, and the restriction
`Hₙ(X, ∂X) ⟶ Hₙ(X, X ∖ Kₜ) = Hₙ(X, Cₜ)` is an isomorphism, by the long exact sequence of the
triple `(X, Cₜ, ∂X)`: the collar coordinates deform `Cₜ` onto `∂X` relative to `∂X`
(`TauCeti.IsCollar.collarDeformation`), so `H_*(Cₜ, ∂X)` vanishes. By excision,
`Hₙ(X, X ∖ Kₜ) ≅ Hₙ(M, M ∖ ι⁻¹(Kₜ))`, in which the family `α` glues to a single class over the
compact set `ι⁻¹(Kₜ)` (`TauCeti.existsUnique_localHomologyRestriction_eq_of_invariant`), and a
class there is determined by its local images (`TauCeti.localHomology_ext_of_isCompact`). Every
interior point lies in `Kₜ` for `t` small enough, and these classes are compatible as `t`
decreases.

The relative cycles representing these classes are the fundamental chains of `X` relative to its
boundary. Through the cubical–singular comparison,
`TopPair.exists_boundary_eq_of_singularHomologyδ_eq` lifts a relative class to a normalized
cubical chain of `X` whose boundary is any prescribed cycle of `∂X` representing its image under
the connecting morphism.

## Main definitions

* `TauCeti.HomologicalOrientation.fundamentalClassRel`: the fundamental class
  `[X, ∂X] ∈ Hₙ(X, ∂X; ℤ)` of a compact manifold `X` relative to its collared boundary.

## Main results

* `TauCeti.existsUnique_localHomologyRestriction_range_eq_of_invariant`: a transport-invariant
  family of local classes of the interior, with coefficients in any module, is the family of
  interior local images of exactly one class of `Hₙ(X, ∂X)`.
* `TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`: when `1` is the only unit of
  the coefficients, exactly one class of `Hₙ(X, ∂X)` generates the local homology at every
  interior point.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_fundamentalClassRel`: the image of the
  integral relative fundamental class in the local homology at every interior point is the local
  orientation there.
* `TauCeti.HomologicalOrientation.isLocalOrientation_localHomologyRestriction_fundamentalClassRel`:
  so it restricts to a local orientation at every interior point.
* `TauCeti.HomologicalOrientation.eq_fundamentalClassRel`: it is the only class with this
  property.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_fundamentalClassRel_image`: its image
  along `ι(K)`, for compact `K ⊆ M`, is the fundamental class of `M` along `K`.
* `TauCeti.HomologicalOrientation.fundamentalClassRel_neg`: reversing the orientation negates it.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the fundamental
  class of a compact manifold with boundary through a collar (Lefschetz duality, Theorem 3.43), and
  the `R`-orientations and mod `2` fundamental classes (Theorem 3.26).
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Lemma 2.2 and Appendix A, where fundamental chains relative to the
  boundary of the compactified trajectory spaces, with coefficients in `ℤ/2`, form the representing
  chain systems.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Module

universe w

namespace TauCeti

section Coefficients

variable {X M : Type w} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {ι : M → X}
  {f : N → X} {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ)

section Collar

variable {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c) (hιf : range ι = (range f)ᶜ)
include hc hιf

private lemma compl_collarPart_subset_range {t : ℝ} (ht : 0 < t) :
    (collarPart c t)ᶜ ⊆ range ι := by
  rw [hιf]
  exact compl_subset_compl.2 (hc.range_subset_collarPart ht)

omit hιf in
/-- The relative homology of a pair `(B, A)` with `A = ∂X = f(N)` and `B` the collar `Cₜ` of
positive depth vanishes: the collar coordinates deform `Cₜ` onto `∂X` relative to `∂X`. -/
private lemma isZero_singularHomology_of_eq_collarPart {A B : Set X} (hAB : A ⊆ B)
    (hA : A = range f) {t : ℝ} (ht : 0 < t) (hB : B = collarPart c t) (k : ℕ) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of X) hAB).singularHomology R k) := by
  subst hA hB
  exact TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel _ _
    (hc.collarDeformation ht) _ k

/-- **Restriction to the complement of a collar is an isomorphism.** For `0 < t`, the restriction
`Hₖ(X, ∂X) ⟶ Hₖ(X, Cₜ)` from the local homology along `ι(M)` to the local homology along
`Kₜ = X ∖ Cₜ` is an isomorphism, by the long exact sequence of the triple `(X, Cₜ, ∂X)`. -/
private lemma isIso_localHomologyRestriction_compl_collarPart {t : ℝ} (ht : 0 < t) (k : ℕ) :
    IsIso (localHomologyRestriction R (compl_collarPart_subset_range hc hιf ht) k) := by
  have hsub : (range ι)ᶜ ⊆ (collarPart c t)ᶜᶜ := by
    rw [compl_compl, hιf, compl_compl]
    exact hc.range_subset_collarPart ht
  have hz (m : ℕ) := isZero_singularHomology_of_eq_collarPart R hc hsub
    (by rw [hιf, compl_compl]) ht (compl_compl _) m
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := TopCat.of X) hsub) R k (hz k) fun m _ ↦ hz m
  rw [TopTriple.totalToOuter_app_ofSubset] at this
  rw [localHomologyRestriction_def]
  exact this

end Collar

variable [TopologicalSpace M]

section CollarInterior

variable (hι : IsOpenEmbedding ι) {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c)
  (hιf : range ι = (range f)ᶜ)
include hι hc hιf

private lemma isCompact_preimage_compl_collarPart [CompactSpace X] {t : ℝ} (ht : 0 < t) :
    IsCompact (ι ⁻¹' (collarPart c t)ᶜ) :=
  hι.isInducing.isCompact_preimage' (hc.isOpen_collarPart t).isClosed_compl.isCompact
    (compl_collarPart_subset_range hc hιf ht)

end CollarInterior

variable [T1Space X] [CompactSpace X] [T2Space M] {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)
  (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ)

include hn hι hιf in
/-- For `0 < t`, a transport-invariant family `α` of local classes glues over the compact set
`ι⁻¹(Kₜ)`, `Kₜ = X ∖ Cₜ`, to a class of `Hₙ(M, M ∖ ι⁻¹(Kₜ))`, which excision carries to a class of
`Hₙ(X, X ∖ Kₜ)` with local image the image of `α x` at every point `ι x` of `Kₜ`. -/
private lemma exists_localHomologyRestriction_compl_collarPart_eq {c : N × Ico (0 : ℝ) 1 → X}
    (hc : IsCollar f c) (α : ∀ x : M, (localHomology R {x} n : ModuleCat.{w} Λ))
    (hα : ∀ {x y : FundamentalGroupoid M} (g : x ⟶ y),
      localHomologyTransport R M E n g (α x.as) = α y.as) {t : ℝ} (ht : 0 < t) :
    ∃ β : (localHomology R (collarPart c t)ᶜ n : ModuleCat.{w} Λ),
      ∀ x (hx : ι x ∈ (collarPart c t)ᶜ), localHomologyRestriction R (singleton_subset_iff.2 hx) n
        β = (localHomologyIsoOfIsOpenEmbedding R hι x n).hom (α x) := by
  obtain ⟨δ, hδ, -⟩ := existsUnique_localHomologyRestriction_eq_of_invariant R hn
    (isCompact_preimage_compl_collarPart hι hc hιf ht) α hα
  refine ⟨localHomologyMap R ⟨ι, hι.continuous⟩ (subset_refl _) n δ, fun x hx ↦ ?_⟩
  rw [← ConcreteCategory.comp_apply,
    localHomologyMap_comp_localHomologyRestriction_singleton _ hι _ hx,
    ConcreteCategory.comp_apply, hδ x hx]

include hn hιf in
/-- **Relative classes with prescribed interior local classes.** Let `ι : M → X` be an open
embedding of an `n`-manifold `M` into a compact `T₁` space `X`, such as a compact Hausdorff space,
whose complement
`∂X = X ∖ ι(M)` is the image of a collared map `f : N → X`, and let `R` be a module over a ring
`Λ`. A family `α` of local classes `α x ∈ Hₙ(M, M ∖ {x}; R)` invariant under transport along paths
is the family of interior local images of exactly one class of `Hₙ(X, ∂X; R)`, written as the
local homology `Hₙ(X, X ∖ ι(M); R)` along `ι(M)`.

For integral coefficients and the local orientations of an orientation this is the fundamental
class relative to the boundary, `TauCeti.HomologicalOrientation.fundamentalClassRel`; with
coefficients in a ring whose only unit is `1` the generators of the local homology form such a
family without any orientation
(`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`). -/
theorem existsUnique_localHomologyRestriction_range_eq_of_invariant (hf : IsCollared f)
    (α : ∀ x : M, (localHomology R {x} n : ModuleCat.{w} Λ))
    (hα : ∀ {x y : FundamentalGroupoid M} (g : x ⟶ y),
      localHomologyTransport R M E n g (α x.as) = α y.as) :
    ∃! γ : (localHomology R (range ι) n : ModuleCat.{w} Λ), ∀ x : M,
      localHomologyRestriction R (singleton_subset_iff.2 (mem_range_self x)) n γ =
        (localHomologyIsoOfIsOpenEmbedding R hι x n).hom (α x) := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  have hglue {t : ℝ} (ht : 0 < t) := exists_localHomologyRestriction_compl_collarPart_eq R hn hι
    hιf hc α hα ht
  -- Two classes of `Hₙ(X, X ∖ Kₜ)` with the same local images along `Kₜ` are equal.
  have hext {t : ℝ} (ht : 0 < t) {γ γ' : (localHomology R (collarPart c t)ᶜ n : ModuleCat.{w} Λ)}
      (h : ∀ x (hx : ι x ∈ (collarPart c t)ᶜ),
        localHomologyRestriction R (singleton_subset_iff.2 hx) n γ =
          localHomologyRestriction R (singleton_subset_iff.2 hx) n γ') : γ = γ' :=
    localHomology_ext_of_isOpenEmbedding R hn hι (hc.isOpen_collarPart t).isClosed_compl
      (compl_collarPart_subset_range hc hιf ht) (isCompact_preimage_compl_collarPart hι hc hιf ht) h
  -- Work at depth `1 / 2`, where `r : Hₙ(X, ∂X) ⟶ Hₙ(X, X ∖ K₁/₂)` is an isomorphism.
  have h₂ : (0 : ℝ) < 1 / 2 := by norm_num
  set r := localHomologyRestriction R (compl_collarPart_subset_range hc hιf h₂) n
  have := isIso_localHomologyRestriction_compl_collarPart R hc hιf h₂ n
  obtain ⟨β, hβ⟩ := hglue h₂
  refine ⟨inv r β, fun x ↦ ?_, fun γ hγ ↦ ?_⟩
  · -- The point `ι x` lies in `Kₛ` for some `s ≤ 1 / 2`.
    obtain ⟨t, ht, hxt⟩ := hc.exists_notMem_collarPart (x := ι x)
      (by rw [← mem_compl_iff, ← hιf]; exact mem_range_self x)
    have hs : 0 < min t (1 / 2) := lt_min ht h₂
    have hxs : ι x ∈ (collarPart c (min t (1 / 2)))ᶜ :=
      fun h ↦ hxt (collarPart_mono (min_le_left _ _) h)
    have hK : (collarPart c (1 / 2))ᶜ ⊆ (collarPart c (min t (1 / 2)))ᶜ :=
      compl_subset_compl.2 (collarPart_mono (min_le_right _ _))
    obtain ⟨β', hβ'⟩ := hglue hs
    -- The restriction `Hₙ(X, X ∖ Kₛ) ⟶ Hₙ(X, X ∖ K₁/₂)` is an isomorphism, since both restrictions
    -- from `Hₙ(X, ∂X)` are, and it carries both `β'` and the image of `inv r β` to `β`.
    have hρ := localHomologyRestriction_comp R hK (compl_collarPart_subset_range hc hιf hs) n
    have := isIso_localHomologyRestriction_compl_collarPart R hc hιf hs n
    have := IsIso.of_isIso_fac_left hρ
    have key : localHomologyRestriction R (compl_collarPart_subset_range hc hιf hs) n (inv r β) =
        β' := by
      refine ConcreteCategory.injective_of_mono_of_preservesPullback
        (localHomologyRestriction R hK n) ?_
      rw [← ConcreteCategory.comp_apply, hρ, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
        ModuleCat.id_apply]
      exact hext h₂ fun y hy ↦ by rw [hβ y hy, localHomologyRestriction_comp_apply, hβ' y (hK hy)]
    rw [← hβ' x hxs, ← key, localHomologyRestriction_comp_apply]
  · -- The image of `γ` in `Hₙ(X, X ∖ K₁/₂)` has the local images of `β` along `K₁/₂`.
    have : r γ = β := hext h₂ fun y hy ↦ by
      rw [hβ y hy, localHomologyRestriction_comp_apply, hγ y]
    rw [← this, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply]

section SubsingletonUnits

variable (K : Type w) [Ring K] [IsDedekindFiniteMonoid K] [Subsingleton Kˣ]

include hn hι hιf in
/-- **The fundamental class relative to the boundary when `1` is the only unit of the
coefficients.** Let `ι : M → X` be an open embedding of an `n`-manifold `M` into a compact `T₁`
space `X`, such as a compact Hausdorff space, whose complement `∂X = X ∖ ι(M)` is collared, as for
a compact topological manifold with boundary or with corners. With coefficients in a ring `K`
whose only unit is `1`, such as `ZMod 2`, and in which one-sided inverses are inverses, exactly one
class of `Hₙ(X, ∂X; K)` generates the local homology `Hₙ(X, X ∖ {ι x}; K) ≅ K` at every interior
point. No orientation of `M` is needed: the local homology of `M` at each point has a single
generator, and these generators form a family invariant under transport. For `K = ZMod 2` this is
the mod `2` fundamental class of `X` relative to its boundary (Hatcher, Section 3.3). -/
theorem existsUnique_span_localHomologyRestriction_range_eq_top (hf : IsCollared f) :
    ∃! γ : (localHomology (ModuleCat.of K K) (range ι) n : ModuleCat.{w} K), ∀ x : M,
      Submodule.span K
        {localHomologyRestriction (ModuleCat.of K K) (singleton_subset_iff.2 (mem_range_self x)) n
          γ} = ⊤ := by
  -- The generator of the local homology of `M` at `x`, the class corresponding to `1`.
  let g (x : M) := (localHomologySingletonLinearEquiv (ModuleCat.of K K) hn
    (LinearEquiv.refl K K) x).symm 1
  have hg (x : M) : Submodule.span K {g x} = ⊤ :=
    LinearEquiv.span_singleton_apply_eq_top_iff _ |>.2 Ideal.span_singleton_one
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_localHomologyRestriction_range_eq_of_invariant
    (ModuleCat.of K K) hn hι hιf hf g fun h ↦ localHomologyTransport_eq_of_span_eq_top K hn h
      (hg _) (hg _)
  refine ⟨γ, fun x ↦ ?_, fun γ' hγ' ↦ huniq γ' fun x ↦ ?_⟩
  · rw [hγ x, ModuleCat.span_singleton_apply_eq_top_iff]
    exact hg x
  · -- The preimage of the local image of `γ'` in the local homology of `M` is a generator.
    set e := localHomologyIsoOfIsOpenEmbedding (ModuleCat.of K K) hι x n
    have := eq_of_span_localHomology_eq_top K hn (x := x)
      ((ModuleCat.span_singleton_apply_eq_top_iff e.inv).2 (hγ' x)) (hg x)
    rw [← this, ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

end SubsingletonUnits

end Coefficients

namespace HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {ι : M → X}
  {f : N → X} [TopologicalSpace M] [T2Space X] [CompactSpace X] [T2Space M] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ)

include hn hι hιf in
private theorem existsUnique_fundamentalClassRel (hf : IsCollared f) :
    ∃! γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range ι) n,
      ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (mem_range_self x)) n γ =
          (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x n).hom
            (o x).val :=
  existsUnique_localHomologyRestriction_range_eq_of_invariant _ hn hι hιf hf (fun x ↦ (o x).val)
    fun g ↦ by rw [← coe_localOrientationTransport, localOrientationTransport_apply]

variable (hf : IsCollared f)

/-- **The fundamental class of a compact manifold relative to its collared boundary.** Let
`ι : M → X` be an open embedding of an oriented `n`-manifold `M` into a compact Hausdorff space
`X` whose complement `∂X = X ∖ ι(M)` is the image of a collared map `f : N → X`. This is the unique
class of `Hₙ(X, ∂X; ℤ)`, written as the local homology `Hₙ(X, X ∖ ι(M); ℤ)` along `ι(M)`, whose
image in the local homology `Hₙ(X, X ∖ {ι x}; ℤ) ≅ Hₙ(M, M ∖ {x}; ℤ)` is the local orientation
`o x` at every `x : M`. -/
def fundamentalClassRel :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range ι) n :=
  (o.existsUnique_fundamentalClassRel hn hι hιf hf).exists.choose

/-- The relative fundamental class restricts to the local orientation at every interior point. -/
@[simp]
theorem localHomologyRestriction_fundamentalClassRel (x : M) :
    localHomologyRestriction (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (mem_range_self x)) n (o.fundamentalClassRel hn hι hιf hf) =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x n).hom (o x).val :=
  (o.existsUnique_fundamentalClassRel hn hι hιf hf).exists.choose_spec x

/-- The relative fundamental class restricts to a local orientation at every interior point. -/
theorem isLocalOrientation_localHomologyRestriction_fundamentalClassRel {p : X}
    (hp : p ∈ range ι) :
    IsLocalOrientation p n (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 hp) n (o.fundamentalClassRel hn hι hιf hf)) := by
  obtain ⟨x, rfl⟩ := hp
  rw [o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf x]
  exact (o x).property.map _

/-- **Uniqueness of the relative fundamental class**: a class of `Hₙ(X, ∂X; ℤ)` restricting to the
local orientation at every interior point is the relative fundamental class. -/
theorem eq_fundamentalClassRel
    {γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range ι) n}
    (hγ : ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 (mem_range_self x)) n γ =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x n).hom (o x).val) :
    γ = o.fundamentalClassRel hn hι hιf hf :=
  (o.existsUnique_fundamentalClassRel hn hι hιf hf).unique hγ
    (o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf)

/-- **The relative fundamental class along a compact set.** For compact `K ⊆ M`, the image of the
relative fundamental class in `Hₙ(X, X ∖ ι(K); ℤ)` is the image under `ι` of the fundamental class
of `M` along `K`. -/
@[simp]
theorem localHomologyRestriction_fundamentalClassRel_image {K : Set M} (hK : IsCompact K) :
    localHomologyRestriction (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
        (image_subset_range ι K) n (o.fundamentalClassRel hn hι hιf hf) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨ι, hι.continuous⟩
        (hι.injective.preimage_image K).subset n (o.fundamentalClassOn hn hK) := by
  refine o.eq_localHomologyMap_fundamentalClassOn hn hι hK (hι.injective.preimage_image K)
    (hK.image hι.continuous).isClosed (image_subset_range ι K) fun x hx ↦ ?_
  rw [← ConcreteCategory.comp_apply, localHomologyRestriction_comp]
  exact o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf x

/-- Reversing the orientation negates the relative fundamental class. -/
@[simp]
theorem fundamentalClassRel_neg :
    (-o).fundamentalClassRel hn hι hιf hf = -o.fundamentalClassRel hn hι hιf hf := by
  refine ((-o).eq_fundamentalClassRel hn hι hιf hf fun x ↦ ?_).symm
  rw [map_neg, o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf x, neg_apply,
    LocalOrientation.coe_neg, map_neg]

end HomologicalOrientation

end TauCeti
