/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Blowup
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Sections
import TauCeti.AlgebraicGeometry.Blowup.Separation
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Separating extended markings by blowing up a model

Let `M` be a proper model over a discrete valuation ring `R` of a scheme `C` over the fraction
field `K`. Every `K`-rational point `p` of `C` extends uniquely to a section `σ_p` of `M`
(`TauCeti.Model.extendSection`). Distinct rational points have distinct generic values, but their
extensions can meet in the special fibre. This file shows that blowing up centres in the special
fibre makes the extensions of finitely many distinct rational points pairwise disjoint, without
changing the generic fibre or its identification with `C`.

For two distinct rational points `p ≠ q`, the intersection of the images of `σ_p` and `σ_q` is the
support of the ideal sheaf `ker σ_p ⊔ ker σ_q`. It misses the generic fibre, so the blowup of `M`
along this ideal sheaf is again a proper model of `C` (`TauCeti.Model.blowup`). On that blowup the
extensions of `p` and `q` are disjoint. The extension of `p` is contained in the closure of its
generic value, which lies off the centre, so it lies in the strict transform of the image of
`σ_p`, and similarly for `q`. Blowing up `I ⊔ J` separates the strict transforms of `V(I)` and
`V(J)` (`AlgebraicGeometry.Scheme.IdealSheafData.disjoint_closure_preimage_support_sdiff_blowup`).

A morphism of proper models carries extended sections to extended sections
(`TauCeti.Model.extendSection_hom`), so extensions that are disjoint on a model stay disjoint on
every proper model mapping to it. Blowing up once for each pair of points therefore separates the
extensions of finitely many distinct rational points at once.

The extensions on the resulting model need not pass through the smooth locus of its structure
morphism.

## Main results

* `TauCeti.Model.disjoint_range_genericι_support_ker_sup_ker`: the extensions of two distinct
  rational points meet only in the special fibre.
* `TauCeti.Model.range_extendSection_blowup_subset`: on a blowup of `M` in a centre of the special
  fibre, an extended section lies in the strict transform of the extended section on `M`.
* `TauCeti.Model.disjoint_range_extendSection_blowup`: on the blowup of their intersection, the
  extensions of two distinct rational points are disjoint.
* `TauCeti.Model.disjoint_range_extendSection_of_hom`: disjointness of extensions pulls back along
  morphisms of proper models.
* `TauCeti.Model.exists_hom_pairwise_disjoint_range_extendSection`: finitely many distinct
  rational points have pairwise disjoint extensions on some proper model mapping to `M`.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.1
  (blowing up) and Chapter 10 (models of curves).
* [The Stacks Project, Section 31.32, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF),
  *Blowing up*.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- **Disjointness of extended sections pulls back along morphisms of proper models.** A morphism
`f : M ⟶ N` of proper models carries the extension of each rational point on `M` to its extension
on `N`, so rational points with disjoint extensions on `N` have disjoint extensions on `M`. -/
theorem disjoint_range_extendSection_of_hom {M N : Model R K C toK} [M.IsProper] [N.IsProper]
    (f : M ⟶ N) {p q : Spec (.of K) ⟶ C} (hp : p ≫ toK = 𝟙 _) (hq : q ≫ toK = 𝟙 _)
    (h : Disjoint (Set.range (N.extendSection p hp)) (Set.range (N.extendSection q hq))) :
    Disjoint (Set.range (M.extendSection p hp)) (Set.range (M.extendSection q hq)) := by
  have hsub (r : Spec (.of K) ⟶ C) (hr : r ≫ toK = 𝟙 _) :
      Set.range (M.extendSection r hr) ⊆ f.hom ⁻¹' Set.range (N.extendSection r hr) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by rw [← extendSection_hom f r hr, Scheme.Hom.comp_apply]⟩
  exact (h.preimage _).mono (hsub p hp) (hsub q hq)

/-- The extension of a rational point takes its generic value on the generic fibre. -/
private lemma extendSection_specMap_apply (M : Model R K C toK) [M.IsProper]
    {p : Spec (.of K) ⟶ C} (hp : p ≫ toK = 𝟙 _) (x : Spec (.of K)) :
    M.extendSection p hp (Spec.map (CommRingCat.ofHom (algebraMap R K)) x) = M.genericι (p x) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun φ : Spec (.of K) ⟶ M.total ↦ φ x) (M.specMap_extendSection p hp)

/-- **The extensions of two distinct rational points meet only in the special fibre.** The
intersection of the images of the extensions, the support of `ker σ_p ⊔ ker σ_q`, does not meet the
generic fibre. This is the hypothesis under which blowing up this intersection gives a model of
`C` (`TauCeti.Model.blowup`). -/
theorem disjoint_range_genericι_support_ker_sup_ker (M : Model R K C toK) [M.IsProper]
    {p q : Spec (.of K) ⟶ C} (hp : p ≫ toK = 𝟙 _) (hq : q ≫ toK = 𝟙 _) (hpq : p ≠ q) :
    Disjoint (Set.range M.genericι)
      (((M.extendSection p hp).ker ⊔ (M.extendSection q hq).ker).support : Set M.total) := by
  have := M.isOpenImmersion_genericι
  have : IsClosedImmersion (M.extendSection p hp) :=
    (M.extendSection p hp).isClosedImmersion_of_comp_eq_id (M.extendSection_toBase p hp)
  have : IsClosedImmersion (M.extendSection q hq) :=
    (M.extendSection q hq).isClosedImmersion_of_comp_eq_id (M.extendSection_toBase q hq)
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨c, rfl⟩ hc
  rw [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf, Scheme.Hom.support_ker,
    Scheme.Hom.support_ker, (M.extendSection p hp).isClosedEmbedding.isClosed_range.closure_eq,
    (M.extendSection q hq).isClosedEmbedding.isClosed_range.closure_eq] at hc
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  -- A point of `Spec R` on which an extension takes a value in the generic fibre lies under
  -- that generic fibre.
  have hbase (r : Spec (.of K) ⟶ C) (hr : r ≫ toK = 𝟙 _) (y : Spec (.of R))
      (hy : M.extendSection r hr y = M.genericι c) : y = t (toK c) := by
    rw [← AlgebraicGeometry.section_apply (M.extendSection_toBase r hr) y, hy,
      ← Scheme.Hom.comp_apply, M.isPullback_genericι.w, Scheme.Hom.comp_apply]
  obtain rfl := hbase p hp a ha
  obtain rfl := hbase q hq b hb
  have h := (AlgebraicGeometry.comp_eq_comp_iff_of_section (M.extendSection_toBase p hp)
    (M.extendSection_toBase q hq) t (toK c)).mpr (ha.trans hb.symm)
  rw [specMap_extendSection, specMap_extendSection, cancel_mono] at h
  exact hpq h

/-- **Extended sections of a blowup lie in strict transforms.** On the blowup of `M` along an ideal
sheaf `I` whose support misses the generic fibre, the extension of a rational point lies in the
strict transform of its extension on `M`: the closure of the inverse image of the part of the
image of that extension off the centre. -/
theorem range_extendSection_blowup_subset (M : Model R K C toK) [M.IsProper]
    (I : M.total.IdealSheafData) (hC : Disjoint (Set.range M.genericι) (I.support : Set M.total))
    {r : Spec (.of K) ⟶ C} (hr : r ≫ toK = 𝟙 _) :
    Set.range ((M.blowup I hC).extendSection r hr) ⊆
      closure (I.blowupToBase ⁻¹'
        (((M.extendSection r hr).ker.support : Set M.total) \ I.support)) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsDominant t := ⟨RingHom.denseRange_comap_of_injective _ (IsFractionRing.injective R K)⟩
  refine (((M.blowup I hC).extendSection r hr).continuous.range_subset_closure_image_dense
    t.denseRange).trans (closure_mono ?_)
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  -- The blowup morphism carries the generic value of the extension on the blowup to the generic
  -- value of the extension on `M`, which lies on the generic fibre.
  have hx : I.blowupToBase ((M.blowup I hC).extendSection r hr (t x)) =
      M.extendSection r hr (t x) := by
    rw [← Scheme.Hom.comp_apply, ← blowupHom_hom M I hC, extendSection_hom]
  rw [Set.mem_preimage, hx]
  refine ⟨(M.extendSection r hr).range_subset_ker_support ⟨t x, rfl⟩, ?_⟩
  rw [extendSection_specMap_apply]
  exact Set.disjoint_left.mp hC ⟨r x, rfl⟩

/-- **Blowing up the intersection separates the extensions of two distinct rational points.** On
the blowup of a proper model along `ker σ_p ⊔ ker σ_q`, the extensions of the distinct rational
points `p` and `q` are disjoint. -/
theorem disjoint_range_extendSection_blowup (M : Model R K C toK) [M.IsProper]
    {p q : Spec (.of K) ⟶ C} (hp : p ≫ toK = 𝟙 _) (hq : q ≫ toK = 𝟙 _) (hpq : p ≠ q) :
    Disjoint
      (Set.range ((M.blowup _
        (M.disjoint_range_genericι_support_ker_sup_ker hp hq hpq)).extendSection p hp))
      (Set.range ((M.blowup _
        (M.disjoint_range_genericι_support_ker_sup_ker hp hq hpq)).extendSection q hq)) := by
  have hsep := Scheme.IdealSheafData.disjoint_closure_preimage_support_sdiff_blowup
    (M.extendSection p hp).ker (M.extendSection q hq).ker
  exact hsep.mono (range_extendSection_blowup_subset M _ _ hp)
    (range_extendSection_blowup_subset M _ _ hq)

/-- Separate the extensions of the pairs in a finite set of index pairs, one blowup at a time. -/
private lemma exists_hom_forall_mem_disjoint_range_extendSection (M : Model R K C toK)
    [M.IsProper] {ι : Type*} (p : ι → (Spec (.of K) ⟶ C)) (hp : ∀ i, p i ≫ toK = 𝟙 _)
    (s : Finset (ι × ι)) (hs : ∀ ij ∈ s, p ij.1 ≠ p ij.2) :
    ∃ (N : Model R K C toK) (_ : N.IsProper) (_ : N ⟶ M), ∀ ij ∈ s,
      Disjoint (Set.range (N.extendSection (p ij.1) (hp ij.1)))
        (Set.range (N.extendSection (p ij.2) (hp ij.2))) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨M, inferInstance, 𝟙 M, by simp⟩
  | insert ij s _ ih =>
    obtain ⟨N, _, f, hN⟩ := ih fun kl hkl ↦ hs kl (Finset.mem_insert_of_mem hkl)
    have hC := N.disjoint_range_genericι_support_ker_sup_ker (hp ij.1) (hp ij.2)
      (hs ij (Finset.mem_insert_self ij s))
    refine ⟨N.blowup _ hC, inferInstance, N.blowupHom _ hC ≫ f, fun kl hkl ↦ ?_⟩
    obtain rfl | hkl := Finset.mem_insert.mp hkl
    · exact N.disjoint_range_extendSection_blowup _ _ (hs _ (Finset.mem_insert_self _ s))
    · exact disjoint_range_extendSection_of_hom (N.blowupHom _ hC) _ _ (hN kl hkl)

/-- **Separating finitely many extended markings.** For finitely many distinct rational points
`p i` of `C`, there is a proper model `N` of `C` with a morphism of models `N ⟶ M` on which the
extensions of the `p i` have pairwise disjoint images. -/
theorem exists_hom_pairwise_disjoint_range_extendSection (M : Model R K C toK) [M.IsProper]
    {ι : Type*} [Finite ι] (p : ι → (Spec (.of K) ⟶ C)) (hp : ∀ i, p i ≫ toK = 𝟙 _)
    (hinj : Function.Injective p) :
    ∃ (N : Model R K C toK) (_ : N.IsProper) (_ : N ⟶ M),
      Pairwise fun i j ↦ Disjoint (Set.range (N.extendSection (p i) (hp i)))
        (Set.range (N.extendSection (p j) (hp j))) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨N, _, f, hN⟩ := M.exists_hom_forall_mem_disjoint_range_extendSection p hp
    (Finset.univ.filter fun ij : ι × ι ↦ ij.1 ≠ ij.2) (by simpa using fun i j ↦ hinj.ne)
  exact ⟨N, inferInstance, f, fun i j hij ↦ hN (i, j) (by simpa using hij)⟩

end TauCeti.Model
