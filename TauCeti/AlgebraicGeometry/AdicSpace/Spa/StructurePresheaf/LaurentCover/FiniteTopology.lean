/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Topology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Sheaf
public import TauCeti.Topology.Category.TopCommRingCat.Sheaf

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor

/-!
# Continuous gluing for finite Laurent covers

Sections on a rational open carry the topology induced by restriction to the sieve of a finite
Laurent cover, as soon as they carry the topology induced by restriction to every two-piece
Laurent cover `W ∩ {|f| ≤ 1}`, `W ∩ {|f| ≥ 1}` of a rational subset `W`
(`isInducing_presentationLimitPresheafMap_laurentSieve_of_isInducing`). This is the induction of
Wedhorn's Lemma 8.34(i), run on topologies instead of on sections.

The rest of Wedhorn's proof of Lemma 8.34 passes to rational localisations, so its topological
form applies to any class of Tate rings that is stable under rational localisation and satisfies
both the algebraic and the topological halves of Lemma 8.33 on rational subsets.
`ContinuousLaurentGluing` packages these hypotheses on a predicate on Tate rings, extending
`LaurentGluing` by the topological half. Over a Tate ring satisfying such a predicate, Laurent
gluing is valid for continuous ring homomorphisms, not just for elements: compatible continuous
homomorphisms into the rings of sections glue to a unique continuous homomorphism
(`isSheafFor_laurentSieve_topCommRingCat`). Strong noetherianness satisfies
`ContinuousLaurentGluing` (`continuousLaurentGluing_isStronglyNoetherian`).

Neither completeness nor Hausdorffness of the original ring is required; the rings of sections
are complete and separated by construction.

## Main definitions

* `TauCeti.ValuationSpectrum.ContinuousLaurentGluing` : the hypotheses on a predicate on Tate
  rings under which the topological form of Wedhorn's reduction of Lemma 8.34 runs.

## Main results

* `TauCeti.ValuationSpectrum.isInducing_presentationLimitPresheafMap_laurentSieve_of_isInducing` :
  if restriction to every two-piece Laurent cover of a rational subset is inducing, so is
  restriction to every finite Laurent sieve of a rational subset.
* `TauCeti.ValuationSpectrum.isSheafFor_laurentSieve_topCommRingCat` : the presentation-limit
  presheaf of topological rings satisfies the sheaf condition for every finite Laurent cover of a
  rational subset.
* `TauCeti.ValuationSpectrum.continuousLaurentGluing_isStronglyNoetherian` : strong
  noetherianness satisfies `ContinuousLaurentGluing`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.33, Lemma 8.34(i) and
  Remark 8.20.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §8.2.2, Lemma 2.
-/

public section

open CategoryTheory TopologicalSpace Topology Opposite TauCeti.Huber

universe v

namespace TauCeti.ValuationSpectrum

/-! ### The induction over the generators -/

section Induction

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (P : PairOfDefinition A) {Aplus : Subring A}

omit [IsHuberRing A] in
/-- Restriction from `W` to its two Laurent pieces, read on the presheaf rather than on the
presentation limits, is inducing when it is inducing on the presentation limits. -/
private theorem isInducing_presheafMap_inf_laurentCoverOpen {W : Opens ↥(spa Aplus)} (f : A)
    (hind : IsInducing fun x : presentationLimit (P := P) Aplus W ↦
      ((presentationLimitMap (P := P)
          (inf_le_left : W ⊓ laurentCoverOpen Aplus f true ≤ W)).hom.1 x,
        (presentationLimitMap (P := P)
          (inf_le_left : W ⊓ laurentCoverOpen Aplus f false ≤ W)).hom.1 x)) :
    IsInducing fun x : (presentationLimitPresheaf P Aplus).obj (op W) ↦
      (((presentationLimitPresheaf P Aplus).map
          (homOfLE (inf_le_left : W ⊓ laurentCoverOpen Aplus f true ≤ W)).op).hom.1 x,
        ((presentationLimitPresheaf P Aplus).map
          (homOfLE (inf_le_left : W ⊓ laurentCoverOpen Aplus f false ≤ W)).op).hom.1 x) := by
  let G := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ _root_.TopCommRingCat TopCat
  let e (V : Opens ↥(spa Aplus)) : (presentationLimitPresheaf P Aplus).obj (op V) ≃ₜ
      presentationLimit (P := P) Aplus V := TopCat.homeoOfIso
    (G.mapIso (eqToIso (presentationLimitPresheaf_obj P Aplus (op V))))
  have h := hind.comp (e W).isInducing
  apply ((e (W ⊓ laurentCoverOpen Aplus f true)).prodCongr
    (e (W ⊓ laurentCoverOpen Aplus f false))).isInducing.of_comp_iff.mp
  convert h using 1
  funext x
  apply Prod.ext
  all_goals
    exact eqToHom_apply_presentationLimitPresheaf_map_apply P _ x

/-- **The topological induction of Wedhorn's Lemma 8.34(i).** Suppose that, for every rational
subset `W` of `Spa(A, A⁺)` and every `f ∈ A`, sections on `W` carry the topology induced by
restriction to the two Laurent pieces `W ∩ {|f| ≤ 1}` and `W ∩ {|f| ≥ 1}`. Then sections on a
rational subset carry the topology induced by restriction to the sieve of any finite Laurent
cover. -/
theorem isInducing_presentationLimitPresheafMap_laurentSieve_of_isInducing
    (hind : ∀ {W : Opens ↥(spa Aplus)}, W ∈ spaRationalOpens Aplus → ∀ f : A,
      IsInducing fun x : presentationLimit (P := P) Aplus W ↦
        ((presentationLimitMap (P := P)
            (inf_le_left : W ⊓ laurentCoverOpen Aplus f true ≤ W)).hom.1 x,
          (presentationLimitMap (P := P)
            (inf_le_left : W ⊓ laurentCoverOpen Aplus f false ≤ W)).hom.1 x))
    (T : Finset A) {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus) :
    IsInducing fun (x : (presentationLimitPresheaf P Aplus).obj (op W))
      (g : (V : Opens ↥(spa Aplus)) × { f : V ⟶ W // laurentSieve Aplus T W f }) ↦
        ((presentationLimitPresheaf P Aplus).map g.2.1.op).hom.1 x := by
  classical
  let F := presentationLimitPresheaf P Aplus
  have hc {V : Opens ↥(spa Aplus)} (S : Sieve V) : Continuous
      (fun (x : F.obj (op V)) (g : (U : Opens ↥(spa Aplus)) × { f : U ⟶ V // S f }) ↦
        (F.map g.2.1.op).hom.1 x) :=
    continuous_pi fun g ↦ (F.map g.2.1.op).hom.2
  induction T using Finset.induction_on generalizing W with
  | empty =>
    let g : (V : Opens ↥(spa Aplus)) × { f : V ⟶ W // laurentSieve Aplus ∅ W f } :=
      ⟨W, 𝟙 W, by simp⟩
    apply IsInducing.of_comp (hc _) (continuous_apply g)
    convert (IsInducing.id : IsInducing (id : F.obj (op W) → F.obj (op W))) using 1
    funext x
    exact ConcreteCategory.congr_hom (F.map_id (op W)) x
  | insert a T _ ih =>
    let Y (b : Bool) := W ⊓ laurentCoverOpen Aplus a b
    have hY (b : Bool) : Y b ∈ spaRationalOpens Aplus :=
      inf_mem_spaRationalOpens hW (laurentCoverOpen_mem_spaRationalOpens Aplus a b)
    -- On either half, the remaining Laurent cover is the cover generated by T. Its arrows
    -- compose with Y b → W to give arrows of the full cover generated by insert a T.
    let j (b : Bool)
        (g : (V : Opens ↥(spa Aplus)) × { f : V ⟶ Y b // laurentSieve Aplus T (Y b) f }) :
        (V : Opens ↥(spa Aplus)) × { f : V ⟶ W // laurentSieve Aplus (insert a T) W f } :=
      ⟨g.1, g.2.1 ≫ homOfLE inf_le_left, by
        rw [laurentSieve_apply]
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ⟨b, g.2.1.le.trans inf_le_right⟩
        · exact (laurentSieve_apply g.2.1).mp g.2.2 t ht⟩
    let q (b : Bool) := fun z :
        (g : (V : Opens ↥(spa Aplus)) ×
          { f : V ⟶ W // laurentSieve Aplus (insert a T) W f }) → F.obj (op g.1) ↦
      fun g ↦ z (j b g)
    have hq (b : Bool) : Continuous (q b) := continuous_pi fun g ↦ continuous_apply (j b g)
    have h := ((ih (hY true)).prodMap (ih (hY false))).comp
      (isInducing_presheafMap_inf_laurentCoverOpen P a (hind hW a))
    apply IsInducing.of_comp (hc _) ((hq true).prodMk (hq false))
    convert h using 1
    funext x
    apply Prod.ext <;> funext g
    all_goals
      simp only [Function.comp_apply, Prod.map_apply, q, j, Functor.map_comp,
        op_comp, ObjectProperty.FullSubcategory.comp_hom]
      -- Evaluate composition in TopCommRingCat, whose morphisms are continuous ring homs.
      rfl

end Induction

/-! ### Predicates on Tate rings admitting continuous Laurent gluing -/

/-- **The hypotheses of the topological form of Wedhorn's reduction to Laurent covers**, on a
predicate `C` on Tate rings. In addition to the hypotheses of `LaurentGluing`:

* on every Tate ring `A` satisfying `C`, and for every subring `A⁺` of power-bounded elements,
  sections of the presentation-limit presheaf of `Spa(A, A⁺)` on a rational subset `W` carry the
  topology induced by restriction to the two pieces `W ∩ {|f| ≤ 1}`, `W ∩ {|f| ≥ 1}`, for every
  `f ∈ A`. This is the topological half of Wedhorn's Lemma 8.33 on rational subsets.

For such a `C`, over a Tate ring satisfying `C`, compatible continuous ring homomorphisms into the
sections on any cover of a rational subset by rational subsets glue continuously
(`isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_topCommRingCat`), so the structure presheaf is a
sheaf of complete separated topological rings
(`isSheaf_presentationLimitPresheaf_of_continuousLaurentGluing`). Strong noetherianness and stable
uniformity are examples (`continuousLaurentGluing_isStronglyNoetherian`,
`continuousLaurentGluing_isStablyUniform`). -/
structure ContinuousLaurentGluing
    (C : ∀ (A : Type v) [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A],
      Prop) : Prop extends LaurentGluing C where
  /-- Over a Tate ring satisfying `C`, sections on a rational subset carry the topology induced by
  restriction to its two Laurent pieces. -/
  isInducing_inf_laurentCoverOpen {A : Type v} [CommRing A] [UniformSpace A]
    [IsTopologicalRing A] [IsTateRing A] (P : PairOfDefinition A) {Aplus : Subring A} : C A →
    (∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) → ∀ {W : Opens ↥(spa Aplus)},
    W ∈ spaRationalOpens Aplus → ∀ f : A,
    IsInducing fun x : presentationLimit (P := P) Aplus W ↦
      ((presentationLimitMap (P := P)
          (inf_le_left : W ⊓ laurentCoverOpen Aplus f true ≤ W)).hom.1 x,
        (presentationLimitMap (P := P)
          (inf_le_left : W ⊓ laurentCoverOpen Aplus f false ≤ W)).hom.1 x)

section ContinuousLaurentGluing

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  (P : PairOfDefinition A) {Aplus : Subring A}
  {C : ∀ (A : Type v) [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A], Prop}

/-- **Continuous gluing for finite Laurent covers.** Let `C` be a predicate on Tate rings
satisfying `ContinuousLaurentGluing`, and `A` a Tate ring satisfying `C`. The presentation-limit
presheaf, viewed as a presheaf of topological commutative rings, satisfies the sheaf condition for
every finite Laurent cover of a rational open. Equivalently, compatible continuous ring
homomorphisms from any topological commutative ring into the sections on the cover glue to a
unique continuous ring homomorphism into sections on the original open. -/
theorem isSheafFor_laurentSieve_topCommRingCat
    (hC : ContinuousLaurentGluing C) (hA : C A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (T : Finset A) {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus)
    (E : _root_.TopCommRingCat.{v}) :
    (laurentSieve Aplus T W).arrows.IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        coyoneda.obj (op E)) :=
  TopCommRingCat.isSheafFor_of_isSheafFor_forget
    (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι)
    (laurentSieve Aplus T W)
    (isSheafFor_laurentSieve_of_isSheafFor
      (hC.isSheafFor_ofArrows_inf_laurentCoverOpen P hA hAplus) T hW)
    (isInducing_presentationLimitPresheafMap_laurentSieve_of_isInducing P
      (hC.isInducing_inf_laurentCoverOpen P hA hAplus) T hW) E

end ContinuousLaurentGluing

/-- **Strong noetherianness admits continuous Laurent gluing.** It admits Laurent gluing
(`laurentGluing_isStronglyNoetherian`), and over a strongly noetherian Tate ring restriction from a
rational subset to its two Laurent pieces is a closed embedding
(`isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen`). -/
theorem continuousLaurentGluing_isStronglyNoetherian :
    ContinuousLaurentGluing.{v} fun A _ _ _ _ ↦ IsStronglyNoetherian A where
  toLaurentGluing := laurentGluing_isStronglyNoetherian
  isInducing_inf_laurentCoverOpen P _ hA hAplus _ hW f :=
    have := hA
    (isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen P hAplus hW f).isInducing

end TauCeti.ValuationSpectrum
