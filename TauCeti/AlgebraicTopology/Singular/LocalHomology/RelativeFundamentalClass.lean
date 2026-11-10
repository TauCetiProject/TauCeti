/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The fundamental class of a compact manifold relative to its collared boundary

Let `X` be a compact Hausdorff space, and let `ι : M → X` be an open embedding of a Hausdorff
space `M` modelled on a real normed space `E` of finite dimension `n`, a topological `n`-manifold
without boundary, oriented by `o`. Suppose that the complement of `ι(M)` is the image of a
collared map `f : N → X` (`TauCeti.IsCollared`): there is an open embedding
`c : N × [0, 1) → X` with `c (y, 0) = f y`. This is the situation of a compact topological
manifold `X` with boundary `∂X = f(N)` and interior `M`, for instance a compact manifold with
corners: the half-space charts collar the boundary locally, and Brown's collaring theorem
(`TauCeti.IsLocallyCollared.isCollared`) assembles local collars of a compact boundary into a
global one.

Then there is a unique class `o.fundamentalClassRel hn hι hιf hf` of `Hₙ(X, ∂X; ℤ)`, the
*fundamental class of `X` relative to its boundary*, whose image in the local homology
`Hₙ(X, X ∖ {ι x}; ℤ) ≅ Hₙ(M, M ∖ {x}; ℤ)` is the local orientation `o x` at every point `x` of the
interior. It is written in the local homology `Hₙ(X, X ∖ ι(M); ℤ)` of `X` along `ι(M)`, since
`X ∖ ι(M) = ∂X`. Its image in `Hₙ(X, X ∖ ι(K); ℤ) ≅ Hₙ(M, M ∖ K; ℤ)` is the fundamental class of
`M` along `K` for every compact `K ⊆ M`, and reversing the orientation negates it.

The proof follows Hatcher. For `0 < t`, let `Cₜ = c(N × [0, t))` be the collar of depth less than
`t` and `Kₜ = X ∖ Cₜ`. Then `Kₜ` is a compact subset of `ι(M)`, and the restriction
`Hₙ(X, ∂X) ⟶ Hₙ(X, X ∖ Kₜ) = Hₙ(X, Cₜ)` is an isomorphism, by the long exact sequence of the
triple `(X, Cₜ, ∂X)`: the collar coordinates deform `Cₜ` onto `∂X` relative to `∂X`, so
`H_*(Cₜ, ∂X)` vanishes. By excision, `Hₙ(X, X ∖ Kₜ) ≅ Hₙ(M, M ∖ ι⁻¹(Kₜ))`, which carries the
fundamental class of `M` along the compact set `ι⁻¹(Kₜ)`. Every interior point lies in `Kₜ` for
`t` small enough, and these classes are compatible as `t` decreases.

The relative cycles representing this class are the fundamental chains of `X` relative to its
boundary. Through the cubical–singular comparison,
`TopPair.exists_boundary_eq_of_singularHomologyδ_eq` lifts a relative class to a normalized
cubical chain of `X` whose boundary is any prescribed cycle of `∂X` representing its image under
the connecting morphism.

## Main definitions

* `TauCeti.HomologicalOrientation.fundamentalClassRel`: the fundamental class
  `[X, ∂X] ∈ Hₙ(X, ∂X; ℤ)` of a compact manifold `X` relative to its collared boundary.

## Main results

* `TauCeti.HomologicalOrientation.localHomologyRestriction_fundamentalClassRel`: its image in the
  local homology at every interior point is the local orientation there.
* `TauCeti.HomologicalOrientation.eq_fundamentalClassRel`: it is the only class with this
  property.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_fundamentalClassRel_image`: its image
  along `ι(K)`, for compact `K ⊆ M`, is the fundamental class of `M` along `K`.
* `TauCeti.HomologicalOrientation.fundamentalClassRel_neg`: reversing the orientation negates it.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the fundamental
  class of a compact manifold with boundary through a collar (Lefschetz duality, Theorem 3.43).
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, where fundamental chains relative to the boundary of the
  compactified trajectory spaces form the representing chain systems.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Module

namespace TauCeti

namespace HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {ι : M → X}
  {f : N → X}

section Collar

/-! ### The collar of depth less than `t` -/

variable {c : N × Ico (0 : ℝ) 1 → X}

/-- The part `c(N × [0, t))` of the collar `c` of depth less than `t`. -/
private def collarPart (c : N × Ico (0 : ℝ) 1 → X) (t : ℝ) : Set X :=
  c '' {p | (p.2 : ℝ) < t}

variable (hc : IsCollar f c)
include hc

private lemma isOpen_collarPart (t : ℝ) : IsOpen (collarPart c t) :=
  hc.isOpenEmbedding.isOpenMap _ (isOpen_lt (by fun_prop) continuous_const)

private lemma range_subset_collarPart {t : ℝ} (ht : 0 < t) : range f ⊆ collarPart c t := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(y, ⟨0, by norm_num⟩), ht, hc.apply_zero y⟩

omit [TopologicalSpace X] [TopologicalSpace N] hc in
private lemma collarPart_mono {s t : ℝ} (h : s ≤ t) : collarPart c s ⊆ collarPart c t :=
  image_mono fun _ hp ↦ lt_of_lt_of_le hp h

variable (hιf : range ι = (range f)ᶜ)
include hιf

private lemma compl_collarPart_subset_range {t : ℝ} (ht : 0 < t) :
    (collarPart c t)ᶜ ⊆ range ι := by
  rw [hιf]
  exact compl_subset_compl.2 (range_subset_collarPart hc ht)

/-- Every interior point lies outside the collar of some depth `t ≤ 1 / 2`. -/
private lemma exists_notMem_collarPart (x : X) (hx : x ∈ range ι) :
    ∃ t, 0 < t ∧ t ≤ 1 / 2 ∧ x ∉ collarPart c t := by
  by_cases hxc : x ∈ range c
  · obtain ⟨q, rfl⟩ := hxc
    -- The depth of `x = c q` is positive, since the zero slice of the collar is the boundary.
    have hq : 0 < (q.2 : ℝ) := by
      refine lt_of_le_of_ne q.2.2.1 fun h ↦ ?_
      have h₀ : q = (q.1, ⟨0, by norm_num⟩) := Prod.ext rfl (Subtype.ext h.symm)
      rw [hιf, h₀, hc.apply_zero] at hx
      exact hx (mem_range_self _)
    refine ⟨min (q.2 : ℝ) (1 / 2), lt_min hq (by norm_num), min_le_right _ _, ?_⟩
    rintro ⟨p, hp, hpq⟩
    rw [hc.isOpenEmbedding.injective hpq] at hp
    exact (min_le_left (q.2 : ℝ) (1 / 2)).not_gt hp
  · exact ⟨1 / 2, by norm_num, le_rfl, fun ⟨p, _, hp⟩ ↦ hxc ⟨p, hp⟩⟩

/-! ### The collar deforms onto the boundary -/

/-- The collar coordinates of a point of the collar of depth less than `t`. -/
private def collarCoord {t : ℝ} :
    C(((collarPart c t)ᶜᶜ : Set X), N × Ico (0 : ℝ) 1) :=
  ⟨fun x ↦ hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm
      ⟨x, image_subset_range _ _ (of_not_not x.2 : (x : X) ∈ collarPart c t)⟩,
    hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)⟩

omit hιf in
private lemma apply_collarCoord {t : ℝ} (x : ((collarPart c t)ᶜᶜ : Set X)) :
    c (collarCoord hc x) = x :=
  congrArg Subtype.val (hc.isOpenEmbedding.isEmbedding.toHomeomorph.apply_symm_apply
    ⟨x, image_subset_range _ _ (of_not_not x.2 : (x : X) ∈ collarPart c t)⟩)

omit hιf in
private lemma collarCoord_apply {t : ℝ} (x : ((collarPart c t)ᶜᶜ : Set X))
    (p : N × Ico (0 : ℝ) 1) (hp : c p = x) : collarCoord hc x = p :=
  hc.isOpenEmbedding.injective ((apply_collarCoord hc x).trans hp.symm)

omit hιf in
private lemma collarCoord_lt {t : ℝ} (x : ((collarPart c t)ᶜᶜ : Set X)) :
    ((collarCoord hc x).2 : ℝ) < t := by
  obtain ⟨p, hp, hpx⟩ := (of_not_not x.2 : (x : X) ∈ collarPart c t)
  rw [collarCoord_apply hc x p hpx]
  exact hp

/-- The point at the same base and at depth `τ` times the depth of `x`. -/
private def collarScale {t : ℝ} (τ : unitInterval) (x : ((collarPart c t)ᶜᶜ : Set X)) : X :=
  c ((collarCoord hc x).1, ⟨τ * (collarCoord hc x).2, mul_nonneg τ.2.1 (collarCoord hc x).2.2.1,
    (mul_le_of_le_one_left (collarCoord hc x).2.2.1 τ.2.2).trans_lt (collarCoord hc x).2.2.2⟩)

omit hιf in
private lemma collarScale_mem {t : ℝ} (τ : unitInterval) (x : ((collarPart c t)ᶜᶜ : Set X)) :
    collarScale hc τ x ∈ (collarPart c t)ᶜᶜ := by
  rw [compl_compl]
  exact ⟨_, (mul_le_of_le_one_left (collarCoord hc x).2.2.1 τ.2.2).trans_lt
    (collarCoord_lt hc x), rfl⟩

omit hιf in
private lemma continuous_collarScale {t : ℝ} :
    Continuous fun q : unitInterval × ((collarPart c t)ᶜᶜ : Set X) ↦ collarScale hc q.1 q.2 := by
  have h : Continuous fun q : unitInterval × ((collarPart c t)ᶜᶜ : Set X) ↦ collarCoord hc q.2 :=
    (map_continuous _).comp continuous_snd
  exact hc.isOpenEmbedding.continuous.comp (h.fst.prodMk (((continuous_subtype_val.comp
    continuous_fst).mul (continuous_subtype_val.comp h.snd)).subtype_mk _))

omit hιf in
private lemma collarScale_zero {t : ℝ} (x : ((collarPart c t)ᶜᶜ : Set X)) :
    collarScale hc 0 x = f (collarCoord hc x).1 := by
  rw [collarScale, ← hc.apply_zero]
  exact congrArg c (Prod.ext rfl (Subtype.ext (zero_mul _)))

omit hιf in
private lemma collarScale_one {t : ℝ} (x : ((collarPart c t)ᶜᶜ : Set X)) :
    collarScale hc 1 x = x := by
  refine Eq.trans ?_ (apply_collarCoord hc x)
  rw [collarScale]
  exact congrArg c (Prod.ext rfl (Subtype.ext (one_mul _)))

omit hιf in
/-- The deformation fixes the boundary, whose points have depth `0`. -/
private lemma collarScale_of_mem_range {t : ℝ} (τ : unitInterval)
    (x : ((collarPart c t)ᶜᶜ : Set X)) (hx : (x : X) ∈ range f) :
    collarScale hc τ x = f (collarCoord hc x).1 := by
  obtain ⟨y, hy⟩ := hx
  have h₀ : ((collarCoord hc x).2 : ℝ) = 0 := by
    rw [collarCoord_apply hc x _ ((hc.apply_zero y).trans hy)]
  rw [collarScale, ← hc.apply_zero]
  exact congrArg c (Prod.ext rfl (Subtype.ext ((congrArg ((τ : ℝ) * ·) h₀).trans (mul_zero _))))

/-- The relative homology of the collar `Cₜ` of positive depth modulo the boundary vanishes: the
collar coordinates deform `Cₜ` onto `∂X = f(N)` relative to `∂X`. -/
private lemma isZero_singularHomology_collarPart {t : ℝ}
    (hsub : (range ι)ᶜ ⊆ (collarPart c t)ᶜᶜ) (k : ℕ) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of X) hsub).singularHomology
      (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) k) := by
  have hf (y : N) : f y ∈ (range ι)ᶜ := by
    rw [hιf, compl_compl]
    exact mem_range_self y
  let r : C(((collarPart c t)ᶜᶜ : Set X), ((range ι)ᶜ : Set X)) :=
    ⟨fun x ↦ ⟨f (collarCoord hc x).1, hf _⟩,
      (hc.continuous.comp (map_continuous (collarCoord hc)).fst).subtype_mk _⟩
  refine TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel hsub r
    { toFun := fun q ↦ ⟨collarScale hc q.1 q.2, collarScale_mem hc q.1 q.2⟩
      continuous_toFun := (continuous_collarScale (t := t) hc).subtype_mk _
      map_zero_left := fun x ↦ Subtype.ext (collarScale_zero hc x)
      map_one_left := fun x ↦ Subtype.ext (collarScale_one hc x)
      prop' := fun τ x hx ↦ Subtype.ext (collarScale_of_mem_range hc τ x
        (by rw [← compl_compl (range f), ← hιf]; exact hx)) } _ k

/-- **Restriction to the complement of a collar is an isomorphism.** For `0 < t`, the restriction
`Hₖ(X, ∂X) ⟶ Hₖ(X, Cₜ)` from the local homology along `ι(M)` to the local homology along
`Kₜ = X ∖ Cₜ` is an isomorphism, by the long exact sequence of the triple `(X, Cₜ, ∂X)`. -/
private lemma isIso_localHomologyRestriction_compl_collarPart {t : ℝ} (ht : 0 < t) (k : ℕ) :
    IsIso (localHomologyRestriction (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (compl_collarPart_subset_range hc hιf ht) k) := by
  have hsub : (range ι)ᶜ ⊆ (collarPart c t)ᶜᶜ := by
    rw [compl_compl, hιf, compl_compl]
    exact range_subset_collarPart hc ht
  have hz (m : ℕ) := isZero_singularHomology_collarPart hc hιf hsub m
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := TopCat.of X) hsub) (ModuleCat.of ℤ (ULift.{0} ℤ)) k (hz k)
    fun m _ ↦ hz m
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
  hι.isInducing.isCompact_preimage' (isOpen_collarPart hc t).isClosed_compl.isCompact
    (compl_collarPart_subset_range hc hιf ht)

/-- **Excision onto the interior.** For `0 < t`, the open embedding `ι` induces an isomorphism
`Hₖ(M, M ∖ ι⁻¹(Kₜ)) ≅ Hₖ(X, X ∖ Kₜ)`. -/
private lemma isIso_localHomologyMap_compl_collarPart {t : ℝ} (ht : 0 < t) (k : ℕ) :
    IsIso (localHomologyMap (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      ⟨ι, hι.continuous⟩ (subset_refl (ι ⁻¹' (collarPart c t)ᶜ)) k) :=
  isIso_localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) _ hι rfl
    (isOpen_collarPart hc t).isClosed_compl (compl_collarPart_subset_range hc hιf ht) k

end CollarInterior

variable [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (hι : IsOpenEmbedding ι)

variable (hιf : range ι = (range f)ᶜ)

/-! ### The fundamental class of the interior along the complement of a collar -/

section Depth

variable {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c)

/-- For `0 < t`, the image in `Hₙ(X, X ∖ Kₜ; ℤ)`, `Kₜ = X ∖ Cₜ`, of the fundamental class of `M`
along the compact set `ι⁻¹(Kₜ)`. -/
private def collarFundamentalClass {t : ℝ} (ht : 0 < t) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (collarPart c t)ᶜ n :=
  localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨ι, hι.continuous⟩
    (subset_refl (ι ⁻¹' (collarPart c t)ᶜ)) n
    (o.fundamentalClassOn hn (isCompact_preimage_compl_collarPart hι hc hιf ht))

/-- A class of `Hₙ(X, ∂X; ℤ)` whose image in `Hₙ(X, X ∖ Kₜ; ℤ)` is `collarFundamentalClass`
restricts to the local orientation at every interior point of `Kₜ`. -/
private lemma localHomologyRestriction_singleton_of_eq_collarFundamentalClass {t : ℝ}
    (ht : 0 < t) {γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (range ι) n}
    (hγ : localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (compl_collarPart_subset_range hc hιf ht) n γ = o.collarFundamentalClass hn hι hιf hc ht)
    {x : M} (hx : ι x ∈ (collarPart c t)ᶜ) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (mem_range_self x)) n γ =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x n).hom (o x).val := by
  rw [collarFundamentalClass] at hγ
  rw [← o.localHomologyRestriction_fundamentalClassOn hn
      (isCompact_preimage_compl_collarPart hι hc hιf ht) (x := x) hx,
    ← ConcreteCategory.comp_apply,
    ← localHomologyMap_comp_localHomologyRestriction_singleton _ hι
      (subset_refl (ι ⁻¹' (collarPart c t)ᶜ)) (mem_preimage.2 hx) hx,
    ConcreteCategory.comp_apply, ← hγ, ← ConcreteCategory.comp_apply,
    localHomologyRestriction_comp]

omit [T2Space X] in
/-- The condition that a class of `Hₙ(X, ∂X; ℤ)` restricts to `collarFundamentalClass` passes from
depth `t` to every smaller positive depth `s`: the restriction `Hₙ(X, X ∖ Kₛ) ⟶ Hₙ(X, X ∖ Kₜ)` is
an isomorphism, since both restrictions from `Hₙ(X, ∂X)` are, and it carries the fundamental class
along `ι⁻¹(Kₛ)` to the one along `ι⁻¹(Kₜ)`. -/
private lemma localHomologyRestriction_eq_collarFundamentalClass_of_le {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) {γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (range ι) n}
    (hγ : localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (compl_collarPart_subset_range hc hιf (hs.trans_le hst)) n γ =
        o.collarFundamentalClass hn hι hιf hc (hs.trans_le hst)) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (compl_collarPart_subset_range hc hιf hs) n γ = o.collarFundamentalClass hn hι hιf hc hs := by
  have ht := hs.trans_le hst
  have hK : (collarPart c t)ᶜ ⊆ (collarPart c s)ᶜ := compl_subset_compl.2 (collarPart_mono hst)
  have hρ := localHomologyRestriction_comp (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
    hK (compl_collarPart_subset_range hc hιf hs) n
  have := isIso_localHomologyRestriction_compl_collarPart hc hιf hs n
  have := isIso_localHomologyRestriction_compl_collarPart hc hιf ht n
  have := IsIso.of_isIso_fac_left hρ
  refine ConcreteCategory.injective_of_mono_of_preservesPullback
    (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) hK n) ?_
  rw [← ConcreteCategory.comp_apply, hρ, hγ, collarFundamentalClass, collarFundamentalClass,
    ← ConcreteCategory.comp_apply, localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_fundamentalClassOn_of_subset o hn
      (isCompact_preimage_compl_collarPart hι hc hιf hs)
      (isCompact_preimage_compl_collarPart hι hc hιf ht) (preimage_mono hK),
    ← ConcreteCategory.comp_apply, localHomologyRestriction_comp_localHomologyMap]

end Depth

/-! ### The relative fundamental class -/

include hn hι hιf in
private theorem existsUnique_fundamentalClassRel (hf : IsCollared f) :
    ∃! γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range ι) n,
      ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (mem_range_self x)) n γ =
          (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x n).hom
            (o x).val := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  -- Work at depth `1 / 2`, where `r : Hₙ(X, ∂X) ⟶ Hₙ(X, X ∖ K₁/₂)` is an isomorphism.
  have h₂ : (0 : ℝ) < 1 / 2 := by norm_num
  set r := localHomologyRestriction (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
    (compl_collarPart_subset_range hc hιf h₂) n
  have := isIso_localHomologyRestriction_compl_collarPart hc hιf h₂ n
  refine ⟨inv r (o.collarFundamentalClass hn hι hιf hc h₂), fun x ↦ ?_, fun γ hγ ↦ ?_⟩
  · -- The point `ι x` lies in `Kₜ` for some `t ≤ 1 / 2`.
    obtain ⟨t, ht, ht₂, hxt⟩ := exists_notMem_collarPart hc hιf (ι x) (mem_range_self x)
    refine o.localHomologyRestriction_singleton_of_eq_collarFundamentalClass hn hι hιf hc ht
      (o.localHomologyRestriction_eq_collarFundamentalClass_of_le hn hι hιf hc ht ht₂ ?_) hxt
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]
  · -- The image of `γ` in `Hₙ(X, X ∖ K₁/₂)` restricts to the local orientations along `K₁/₂`.
    have hγ' : r γ = o.collarFundamentalClass hn hι hιf hc h₂ := by
      refine o.eq_localHomologyMap_fundamentalClassOn hn hι _ rfl
        (isOpen_collarPart hc _).isClosed_compl (compl_collarPart_subset_range hc hιf h₂)
        fun x hx ↦ ?_
      rw [← ConcreteCategory.comp_apply, localHomologyRestriction_comp]
      exact hγ x
    rw [← hγ', ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ModuleCat.id_apply]

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
theorem localHomologyRestriction_fundamentalClassRel (x : M) :
    localHomologyRestriction (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (mem_range_self x)) n (o.fundamentalClassRel hn hι hιf hf) =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x n).hom (o x).val :=
  (o.existsUnique_fundamentalClassRel hn hι hιf hf).exists.choose_spec x

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
