/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Collar
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass

/-!
# The boundary of the relative fundamental class

Let `X` be a compact Hausdorff space and `ι : M → X` an open embedding of an oriented
`(m + 1)`-manifold `M`, whose complement `∂X = X ∖ ι(M)` is the image of a collared map
`f : N → X` from an `m`-manifold `N`. This is the situation of a compact topological manifold `X`
with boundary `∂X`, for instance a compact manifold with corners. The relative fundamental class
`[X, ∂X] ∈ H_{m+1}(X, ∂X; ℤ)` (`TauCeti.HomologicalOrientation.fundamentalClassRel`) is the class
restricting to the orientation at every interior point.

This file proves that the connecting morphism `H_{m+1}(X, ∂X; ℤ) ⟶ H_m(∂X; ℤ)` sends `[X, ∂X]` to a
fundamental class of the boundary
(`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`): its
image in the local homology `H_m(∂X, ∂X ∖ {z}; ℤ)` generates that group at every boundary point
`z`. This is the homological fact through which fundamental chains relative to the boundary are
chosen compatibly with their boundaries: a relative cycle representing `[X, ∂X]` has as boundary a
cycle representing a fundamental class of `∂X`.

The proof is local at `z = f y`. Let `ι x = c (y, 1 / 2)` be the interior point above `z` in a
collar `c`, and `Q = c({y} × [0, 1 / 2])` the segment joining them. Removing `Q` does not change
homology (`TauCeti.IsCollar.isZero_singularHomology_compl_image_prod`), so the connecting morphism
of the triple `(X, X ∖ {ι x}, X ∖ Q)` is an isomorphism
`H_{m+1}(X, X ∖ {ι x}) ≅ H_m(X ∖ {ι x}, X ∖ Q)`.
The inclusion of triples `(X, ∂X, ∂X ∖ {z}) ⟶ (X, X ∖ {ι x}, X ∖ Q)` and the naturality of
connecting morphisms show that the map `H_m(∂X, ∂X ∖ {z}) ⟶ H_m(X ∖ {ι x}, X ∖ Q)` carries the
local image of `δ[X, ∂X]` at `z` to the image of the local orientation at `ι x`, a generator of
infinite order. Since the local homology of `∂X ≅ N` at `z` is cyclic, the local image at `z` is
then a generator itself.

## Main results

* `TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`: the
  connecting morphism sends the relative fundamental class to a fundamental class of the boundary.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the
  fundamental class of a compact manifold with boundary and Lefschetz duality (Theorem 3.43).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, where fundamental chains relative to the boundary, with
  boundaries the fundamental chains of the boundary, form the representing chain systems.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Module

namespace TauCeti

namespace HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {m : ℕ} (o : HomologicalOrientation M E (m + 1))
  (hn : finrank ℝ E = m + 1) {ι : M → X} (hι : IsOpenEmbedding ι) {f : N → X}
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

include hn in
/-- The restriction of the relative fundamental class to an interior point `ι x` is a generator
of infinite order of the local homology there. -/
private lemma localHomologyRestriction_fundamentalClassRel_generator (x : M) :
    let ρ := localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 (mem_range_self x)) (m + 1) (o.fundamentalClassRel hn hι hιf hf)
    IsLocalOrientation (ι x) (m + 1) ρ ∧ ∀ a : ℤ, a • ρ = 0 → a = 0 := by
  intro ρ
  set e := localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hι x (m + 1)
  have hρ : ρ = e.hom (o x).val := o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf x
  refine ⟨hρ ▸ (o x).2.map e, fun a ha ↦ zsmul_left_injective hn o x ?_⟩
  rw [hρ, ← map_zsmul] at ha
  simpa using congrArg e.inv ha

omit [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N] [T2Space M] in
include hιf in
/-- A point outside the interior `ι(M)` lies on the boundary `f(N)`. -/
private lemma mem_range_of_mem_compl_range {z : X} (hz : z ∈ (range ι)ᶜ) : z ∈ range f := by
  simpa [hιf] using hz

omit [TopologicalSpace M] [T2Space M] [T2Space X] [CompactSpace X] in
include hιf hf in
/-- Every boundary point lies in the source of a chart of the boundary, read through `f` from a
chart of `N`. -/
private lemma exists_mem_source {E' : Type} [NormedAddCommGroup E'] [ChartedSpace E' N]
    (z : ((range ι)ᶜ : Set X)) :
    ∃ χ : OpenPartialHomeomorph ((range ι)ᶜ : Set X) E', z ∈ χ.source := by
  obtain ⟨y, hy⟩ := mem_range_of_mem_compl_range hιf z.2
  let h : ((range ι)ᶜ : Set X) ≃ₜ N :=
    (Homeomorph.setCongr (by rw [hιf, compl_compl])).trans hf.isEmbedding.toHomeomorph.symm
  have hhz : h z = y := hf.isEmbedding.toHomeomorph.symm_apply_eq.2 (Subtype.ext hy.symm)
  exact ⟨h.toOpenPartialHomeomorph.trans (chartAt E' y), by simp [hhz, mem_chart_source]⟩

omit [TopologicalSpace M] [T2Space M] [T2Space X] [CompactSpace X] in
include hιf in
/-- A boundary point in the column `c({y} × S)` of a collar is `f y`. -/
private lemma eq_of_mem_image_singleton_prod {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c)
    {y : N} {S : Set (Ico (0 : ℝ) 1)} {w : ((range ι)ᶜ : Set X)}
    (hw : (w : X) ∈ c '' ({y} ×ˢ S)) : (w : X) = f y := by
  obtain ⟨q, ⟨hq₁, -⟩, hqw⟩ := hw
  obtain ⟨y', hy'⟩ := mem_range_of_mem_compl_range hιf w.2
  have hq := hc.isOpenEmbedding.injective (hqw.trans (hy'.symm.trans (hc.apply_zero y').symm))
  have hyy : y' = y := (congrArg Prod.fst hq).symm.trans (mem_singleton_iff.1 hq₁)
  rw [← hy', hyy]

/-- **Comparing the boundary with the interior.** Let `z = f y` be a boundary point and
`ι x = c (y, 1 / 2)` the interior point above it in a collar `c`. Some homomorphism out of the
local homology of `∂X` at `z` carries the local image of `δ[X, ∂X]` at `z` to the image of the
restriction of `[X, ∂X]` to `ι x` under an isomorphism. The homomorphism is induced by the map of
pairs `(∂X, ∂X ∖ {z}) ⟶ (X ∖ {ι x}, X ∖ Q)` for the segment `Q = c({y} × [0, 1 / 2])`, and the
isomorphism is the connecting morphism of the triple `(X, X ∖ {ι x}, X ∖ Q)`. -/
private lemma exists_localHomology_map_eq {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c)
    {z : ((range ι)ᶜ : Set X)} {y : N} (hy : f y = z) {x : M}
    (hx : ι x = c (y, ⟨1 / 2, by norm_num, by norm_num⟩)) :
    ∃ (G : ModuleCat.{0} ℤ)
      (J : localHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ({z} : Set ((range ι)ᶜ : Set X)) m ⟶ G)
      (δ : localHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) {ι x} (m + 1) ≅ G),
      J (singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) z m
          (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) m) (o.fundamentalClassRel hn hι hιf hf))) =
        δ.hom (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
          (singleton_subset_iff.2 (mem_range_self x)) (m + 1) (o.fundamentalClassRel hn hι hιf hf))
    := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  set P := TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))
  set μ := o.fundamentalClassRel hn hι hιf hf
  -- Removing the segment `Q` does not change homology, so the connecting morphism of the triple
  -- `T = (X, X ∖ {ι x}, X ∖ Q)` is an isomorphism.
  set Q := c '' ({y} ×ˢ (Subtype.val ⁻¹' Icc 0 (1 / 2)))
  have hQ (k : ℕ) := hc.isZero_singularHomology_compl_image_prod (isCompact_singleton (x := y))
    (s := 1 / 2) (by norm_num) R k
  have hpQ : (Qᶜ : Set (TopCat.of X)) ⊆ {ι x}ᶜ :=
    compl_subset_compl.2 (singleton_subset_iff.2
      (hx ▸ ⟨(y, ⟨1 / 2, by norm_num, by norm_num⟩), ⟨rfl, by norm_num, le_rfl⟩, rfl⟩))
  let T := TopTriple.ofSubset (X := TopCat.of X) hpQ
  have := T.isIso_singularHomologyδ_of_isZero R (m + 1) m (hQ _) (hQ _) rfl
  -- The maps of pairs `φ : (X, ∂X) ⟶ (X, X ∖ {ι x})`, `r : (∂X, ∅) ⟶ (∂X, ∂X ∖ {z})` and
  -- `J : (∂X, ∂X ∖ {z}) ⟶ (X ∖ {ι x}, X ∖ Q)`; `r ≫ J` and `φ` agree on `∂X`.
  have hA : ((range ι)ᶜ : Set (TopCat.of X)) ⊆ {ι x}ᶜ :=
    compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self x))
  let φ : P ⟶ TopPair.ofSubset ({ι x}ᶜ : Set (TopCat.of X)) := TopPair.ofSubsetMap (𝟙 _) hA
  let J : TopPair.ofSubset ({z}ᶜ : Set (TopCat.of ((range ι)ᶜ : Set X))) ⟶
      TopTriple.innerPair.obj T :=
    TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion hA))
      (TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, fun hw ↦ w.2 (Subtype.ext
        ((eq_of_mem_image_singleton_prod hιf hc hw).trans hy))⟩, by fun_prop⟩) (by ext; rfl)
  let r := TopPair.ofSubsetMap (𝟙 (TopCat.of ((range ι)ᶜ : Set X)))
    (compl_subset_compl.2 (subset_univ {z}))
  have hφ : TopPair.Hom.snd φ = TopCat.ofHom (ContinuousMap.inclusion hA) := by
    ext w
    exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ w)
  have hfst : TopPair.Hom.fst (r ≫ J) = TopPair.Hom.snd φ := by
    rw [hφ]
    ext w
    exact congrArg (ContinuousMap.inclusion hA) (TopPair.ofSubsetMap_fst_apply _ _ w)
  -- Naturality of the connecting morphisms along `φ`, and of `Hₘ(∂X) ⟶ Hₘ(∂X, ∂X ∖ {z})`
  -- along `r ≫ J`, make the square from `H_{m+1}(X, ∂X)` to `Hₘ(X ∖ {ι x}, X ∖ Q)` commute.
  let δ := asIso (T.singularHomologyδ R (m + 1) m rfl)
  have key : P.singularHomologyδ R (m + 1) m rfl ≫
      (TopPair.ofSubset ((univ : Set (TopCat.of ((range ι)ᶜ : Set X)))ᶜ)).singularHomologyπ R m ≫
      TopPair.singularHomologyMap r R m ≫ TopPair.singularHomologyMap J R m =
        TopPair.singularHomologyMap φ R (m + 1) ≫ δ.hom := by
    rw [← TopPair.singularHomologyMap_comp]
    refine (P.singularHomologyδ R (m + 1) m rfl ≫=
      (TopPair.singularHomologyπ_naturality (f := r ≫ J) (R := R) m).symm).trans ?_
    rw [hfst]
    exact (TopPair.singularHomologyδ_naturality_assoc R φ (m + 1) m rfl _).trans
      (TopPair.singularHomologyMap φ R (m + 1) ≫=
        (T.singularHomologyδ_eq_comp_singularHomologyπ R (m + 1) m rfl).symm)
  refine ⟨_, TopPair.singularHomologyMap J R m, δ, ?_⟩
  refine (congrArg _ (singularHomologyToLocalHomology_apply R z
    (P.singularHomologyδ R (m + 1) m rfl μ))).trans ?_
  rw [localHomologyRestriction_def, localHomologyRestriction_def]
  exact congrArg (fun F ↦ F μ) key

/-- **The boundary of the relative fundamental class is a fundamental class.** Let `X` be a
compact Hausdorff space and `ι : M → X` an open embedding of an `(m + 1)`-manifold `M` oriented by
`o`, whose complement `∂X = X ∖ ι(M)` is the image of a collared map `f : N → X` from a manifold
`N`. Then the connecting morphism `H_{m+1}(X, ∂X; ℤ) ⟶ H_m(∂X; ℤ)` sends the relative fundamental
class `[X, ∂X]` to a fundamental class of `∂X`: its image in the local homology of `∂X` at every
point generates it. -/
theorem isFundamentalClass_singularHomologyδ_fundamentalClassRel {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' N] :
    IsFundamentalClass (M := ((range ι)ᶜ : Set X))
      (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) m) (o.fundamentalClassRel hn hι hιf hf)) := by
  refine (isFundamentalClass_iff_forall_isLocalOrientation _).2 fun z ↦ ?_
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  -- The boundary point `z` is `f y`, and `ι x = c (y, 1 / 2)` is an interior point above it.
  obtain ⟨y, hy⟩ := mem_range_of_mem_compl_range hιf z.2
  obtain ⟨x, hx⟩ : c (y, ⟨1 / 2, by norm_num, by norm_num⟩) ∈ range ι := by
    rw [hιf]
    rintro ⟨y', hy'⟩
    have h := congrArg (fun q : N × Ico (0 : ℝ) 1 ↦ (q.2 : ℝ))
      (hc.isOpenEmbedding.injective ((hc.apply_zero y').trans hy'))
    norm_num at h
  obtain ⟨G, J, δ, hJ⟩ := o.exists_localHomology_map_eq hn hι hιf hf hc hy hx
  -- The local homology of `∂X ≅ N` at `z` is a copy of `ℤ`, or zero in the wrong degree.
  obtain ⟨χ, hzχ⟩ := exists_mem_source (E' := E') hιf hf z
  by_cases hm : finrank ℝ E' = m
  · subst hm
    obtain ⟨hρ, hρ₀⟩ := o.localHomologyRestriction_fundamentalClassRel_generator hn hι hιf hf x
    exact IsLocalOrientation.of_addMonoidHom_eq (isLocalOrientation_inv_one
      (singularHomologyComplSingletonFinrankIso (ModuleCat.of ℤ (ULift.{0} ℤ)) χ hzχ))
      J.hom.toAddMonoidHom δ.toLinearEquiv.toAddEquiv ((isLocalOrientation_iff _ _ _).1 hρ) hρ₀ hJ
  · have := ModuleCat.subsingleton_of_isZero (isZero_singularHomology_complSingleton_of_ne
      (ModuleCat.of ℤ (ULift.{0} ℤ)) χ hzχ rfl (Ne.symm hm))
    exact (isLocalOrientation_iff _ _ _).2 fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end HomologicalOrientation

end TauCeti
