/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.EtaleEquivRel
public import TauCeti.AlgebraicGeometry.Cover.Open
public import TauCeti.RingTheory.Localization.Away.NegX
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic

/-!
# Examples of étale equivalence relations

This file collects examples and non-examples of étale equivalence relations on schemes (Stacks,
Definition 39.3.1 (022P) and Spaces, Definition 65.9.2 (02WS)): the relation `Δ ⊔ Γ` given by the
diagonal together with the graph of a fixed-point-free involution, in particular the relation on
the affine line of Stacks, Example 65.14.1 (02Z1); the kernel pair of a fold map; and
`𝔸¹_k ×_k 𝔸¹_k`, an equivalence relation whose projections are not étale.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.coprodDesc`: for an étale monomorphism
  `ι : V ⟶ U` and an involution `τ` of `V` without fixed points (no nonempty `f : T ⟶ V` has
  `f ≫ τ = f`), the relation `Δ ⊔ Γ` on `U`, with total space `U ⨿ V`, target
  `coprod.desc (𝟙 U) ι` and source `coprod.desc (𝟙 U) (τ ≫ ι)`, is an étale equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.not_mono_coprodDesc`: when `V` is nonempty, its projections
  are not monomorphisms, in particular not isomorphisms.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.kernelPair_codiag`: the kernel pair of the fold
  map `U ⨿ U ⟶ U` is an étale equivalence relation on `U ⨿ U`.
* `TauCeti.AlgebraicGeometry.Spaces.not_jointlyMono₂_codiag`: for nonempty `U`, the pair
  `(𝟙 ⊔ 𝟙, 𝟙 ⊔ 𝟙) : U ⨿ U ⟶ U × U` is not jointly monic, so it is not an equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.coprodDesc_gmToAffineLine`: over a ring `k` in
  which `2` is a unit, `Δ ⊔ Γ` on `𝔸¹_k = Spec k[X]`, with `Γ = {(x, -x) : x ≠ 0}` the graph of
  `x ↦ -x` on `Spec k[X, X⁻¹]`, is an étale equivalence relation, and
  `TauCeti.AlgebraicGeometry.Spaces.not_isIso_coprodDesc_gmToAffineLine`,
  `TauCeti.AlgebraicGeometry.Spaces.not_isIso_coprodDesc_gmNeg_comp_gmToAffineLine`: for
  nontrivial `k` its projections are not isomorphisms.
* `TauCeti.AlgebraicGeometry.Spaces.isEquivalenceRelation_pullback_affineLine`,
  `TauCeti.AlgebraicGeometry.Spaces.not_etale_pullback_fst_affineLine`, `..._snd_...`:
  `𝔸¹_k ×_k 𝔸¹_k` is an equivalence relation on `𝔸¹_k` (the kernel pair of the structure
  morphism) whose projections are not étale for nontrivial `k`.

## References

* [Stacks Project, Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Example 65.14.1](https://stacks.math.columbia.edu/tag/02Z1)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry TauCeti.CategoryTheory TauCeti.Localization

universe u

section DeltaGamma

variable {U V : Scheme.{u}} (ι : V ⟶ U) (τ : V ⟶ V)

/-- The pair `t = 𝟙 ⊔ ι`, `s = 𝟙 ⊔ (τ ≫ ι)` on `U ⨿ V` is jointly monic when `ι` is a monomorphism
and `τ` has no fixed points. -/
private lemma jointlyMono₂_coprodDesc [Mono ι]
    (hτ : ∀ {T : Scheme.{u}} (f : T ⟶ V), f ≫ τ = f → IsEmpty T) :
    JointlyMono₂ (coprod.desc (𝟙 U) ι) (coprod.desc (𝟙 U) (τ ≫ ι)) := by
  -- On a piece where one morphism goes through `U` and the other through `V`, the latter is
  -- fixed by `τ`, so the piece is empty.
  have empty {T : Scheme.{u}} (x : T ⟶ U) (y : T ⟶ V) (ht : x = y ≫ ι)
      (hs : x = y ≫ τ ≫ ι) : IsEmpty T :=
    hτ y (by rw [← cancel_mono ι, Category.assoc, ← hs, ht])
  refine ⟨fun T f g ht hs ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := f.exists_openCover_coprod
  refine 𝒰.hom_ext _ _ fun i ↦ ?_
  obtain ⟨𝒱, h𝒱⟩ := (𝒰.f i ≫ g).exists_openCover_coprod
  refine 𝒱.hom_ext _ _ fun j ↦ ?_
  have ht' := congr(𝒱.f j ≫ 𝒰.f i ≫ $ht)
  have hs' := congr(𝒱.f j ≫ 𝒰.f i ≫ $hs)
  rcases h𝒰 i with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases h𝒱 j with ⟨b, hb⟩ | ⟨b, hb⟩ <;>
    simp only [reassoc_of% ha, reassoc_of% hb, coprod.inl_desc, coprod.inr_desc,
      Category.comp_id] at ht' hs' <;> rw [hb, ha]
  · simp [← ht']
  · have := empty (𝒱.f j ≫ a) b (by simpa using ht') (by simpa using hs')
    exact isInitialOfIsEmpty.hom_ext _ _
  · have := empty b (𝒱.f j ≫ a) (by simpa using ht'.symm) (by simpa using hs'.symm)
    exact isInitialOfIsEmpty.hom_ext _ _
  · have e : 𝒱.f j ≫ a = b := (cancel_mono ι).1 (by simpa using ht')
    simp [← e]

/-- **`Δ ⊔ Γ`.** For an étale monomorphism `ι : V ⟶ U` and an involution `τ` of `V` without fixed
points (every `f : T ⟶ V` with `f ≫ τ = f` has empty source), the relation on `U` with total space
`U ⨿ V`, target `coprod.desc (𝟙 U) ι` and source `coprod.desc (𝟙 U) (τ ≫ ι)` is an étale
equivalence relation: the diagonal together with the graph of `τ` on `V`. -/
theorem EtaleEquivRel.coprodDesc [Etale ι] [Mono ι] (hττ : τ ≫ τ = 𝟙 V)
    (hτ : ∀ {T : Scheme.{u}} (f : T ⟶ V), f ≫ τ = f → IsEmpty T) :
    EtaleEquivRel (coprod.desc (𝟙 U) (τ ≫ ι)) (coprod.desc (𝟙 U) ι) := by
  have : IsIso τ := ⟨τ, hττ, hττ⟩
  have := jointlyMono₂_coprodDesc ι τ hτ
  refine ⟨(isEquivalenceRelation_iff).2 ⟨this, fun T ↦ ⟨fun a ↦ ?_, fun hr ↦ ?_,
      fun hr₁ hr₂ ↦ ?_⟩⟩, ?_, ?_⟩
  · exact Rel.ofPairHom_iff.2 ⟨a ≫ coprod.inl, by simp, by simp⟩
  · obtain ⟨r, h₁, h₂⟩ := Rel.ofPairHom_iff.1 hr
    refine Rel.ofPairHom_iff.2 ?_
    subst h₁ h₂
    refine ⟨r ≫ coprod.map (𝟙 U) τ, ?_, ?_⟩ <;> rw [Category.assoc] <;> congr 1 <;> ext <;>
      simp [reassoc_of% hττ]
  · -- Split `T` along `r₁`, then along `r₂`.
    obtain ⟨r₁, h₁, h₂⟩ := Rel.ofPairHom_iff.1 hr₁
    obtain ⟨r₂, h₁', h₂'⟩ := Rel.ofPairHom_iff.1 hr₂
    refine Rel.ofPairHom_iff.2 ?_
    subst h₁ h₂'
    obtain ⟨𝒰, h𝒰⟩ := r₁.exists_openCover_coprod
    refine 𝒰.exists_lift_of_jointlyMono₂ fun i ↦ ?_
    rcases h𝒰 i with ⟨x, hx⟩ | ⟨x, hx⟩
    · refine ⟨𝒰.f i ≫ r₂, ?_, rfl⟩
      rw [Category.assoc, h₁', ← h₂, reassoc_of% hx, reassoc_of% hx]
      simp
    obtain ⟨𝒱, h𝒱⟩ := (𝒰.f i ≫ r₂).exists_openCover_coprod
    refine 𝒱.exists_lift_of_jointlyMono₂ fun j ↦ ?_
    have hb := congr(𝒱.f j ≫ 𝒰.f i ≫ $(h₂.trans h₁'.symm))
    rcases h𝒱 j with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine ⟨𝒱.f j ≫ 𝒰.f i ≫ r₁, rfl, ?_⟩
      simp only [reassoc_of% hx, reassoc_of% hy, coprod.inl_desc, coprod.inr_desc,
        Category.comp_id, Category.assoc] at hb ⊢
      rw [hb]
    · simp only [reassoc_of% hx, reassoc_of% hy, coprod.inr_desc] at hb
      have e : 𝒱.f j ≫ x ≫ τ = y := (cancel_mono ι).1 (by simpa using hb)
      refine ⟨𝒱.f j ≫ 𝒰.f i ≫ r₁ ≫ coprod.desc (𝟙 U) ι ≫ coprod.inl, by simp, ?_⟩
      simp [reassoc_of% hx, reassoc_of% hy, ← e, reassoc_of% hττ]
  · infer_instance
  · infer_instance

/-- If `V` is nonempty, no morphism `coprod.desc (𝟙 U) g : U ⨿ V ⟶ U` is a monomorphism: it
identifies `coprod.inr` with `g ≫ coprod.inl`. In particular neither projection of `Δ ⊔ Γ` is an
isomorphism. -/
theorem not_mono_coprodDesc [Nonempty V] (g : V ⟶ U) :
    ¬ Mono (coprod.desc (𝟙 U) g) := by
  intro h
  have : (coprod.inr : V ⟶ U ⨿ V) = g ≫ coprod.inl := by
    rw [← cancel_mono (coprod.desc (𝟙 U) g)]
    simp
  obtain ⟨x⟩ := ‹Nonempty V›
  exact inl_ne_inr U V (g x) x (by rw [this, Scheme.Hom.comp_apply])

end DeltaGamma

section Fold

variable (U : Scheme.{u})

/-- The kernel pair of the fold map `codiag U : U ⨿ U ⟶ U` is an étale equivalence relation on
`U ⨿ U`. -/
theorem EtaleEquivRel.kernelPair_codiag :
    EtaleEquivRel (pullback.snd (Limits.codiag U) (Limits.codiag U))
      (pullback.fst (Limits.codiag U) (Limits.codiag U)) :=
  of_isKernelPair (IsPullback.of_hasPullback (Limits.codiag U) (Limits.codiag U))

/-- For nonempty `U`, the pair `(𝟙 ⊔ 𝟙, 𝟙 ⊔ 𝟙) : U ⨿ U ⟶ U × U` is not jointly monic: `coprod.inl`
and `coprod.inr` have the same composites. So it is not an equivalence relation. -/
theorem not_jointlyMono₂_codiag [Nonempty U] : ¬ JointlyMono₂ (codiag U) (codiag U) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty U›
  have := h.right_cancellation coprod.inl coprod.inr (by simp) (by simp)
  exact inl_ne_inr U U x x (by rw [this])

end Fold

section AffineLine

open Polynomial TensorProduct

variable (k : Type u) [CommRing k]

/-- The open immersion `𝔾_m = Spec k[X, X⁻¹] ⟶ 𝔸¹_k = Spec k[X]`. -/
noncomputable abbrev gmToAffineLine :
    Spec (.of (Localization.Away (X : k[X]))) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X]))))

/-- The involution `x ↦ -x` of `Spec k[X, X⁻¹]`. -/
noncomputable abbrev gmNeg :
    Spec (.of (Localization.Away (X : k[X]))) ⟶ Spec (.of (Localization.Away (X : k[X]))) :=
  Spec.map (CommRingCat.ofHom (negAwayX k).toRingHom)

/-- `x ↦ -x` is an involution of `Spec k[X, X⁻¹]`. -/
@[reassoc (attr := simp)]
theorem gmNeg_comp_gmNeg : gmNeg k ≫ gmNeg k = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

variable {k} in
/-- When `2` is a unit in `k`, the involution `x ↦ -x` of `Spec k[X, X⁻¹]` has no fixed points:
every morphism `f : T ⟶ Spec k[X, X⁻¹]` with `f ≫ gmNeg k = f` has empty source. -/
theorem isEmpty_of_comp_gmNeg (h2 : IsUnit (2 : k)) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of (Localization.Away (X : k[X])))) (hf : f ≫ gmNeg k = f) :
    IsEmpty T := by
  let φ := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have hφ : CommRingCat.ofHom (negAwayX k).toRingHom ≫ φ = φ := by
    have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (negAwayX k).toRingHom)
    rw [← Iso.eq_comp_inv, Category.assoc] at this
    simp only [φ]
    conv_rhs => rw [← hf, Scheme.Hom.comp_appTop, this]
    simp
  set b := algebraMap k[X] (Localization.Away (X : k[X])) X
  have hb : φ.hom (-b) = φ.hom b := by
    simpa [b] using congr($hφ b)
  have h0 : (2 : Γ(T, ⊤)) * φ.hom b = 0 := by
    rw [two_mul]
    nth_rw 1 [← hb]
    rw [map_neg, neg_add_cancel]
  have h2' : IsUnit (2 : Γ(T, ⊤)) := by
    have := h2.map (φ.hom.comp ((algebraMap k[X] _).comp C))
    rwa [map_ofNat] at this
  have : Subsingleton Γ(T, ⊤) := subsingleton_of_zero_eq_one <| isUnit_zero_iff.mp <|
    h0 ▸ h2'.mul ((IsLocalization.Away.algebraMap_isUnit (X : k[X])).map φ.hom)
  refine ⟨fun x ↦ ?_⟩
  have : Nonempty (⊤ : T.Opens) := ⟨⟨x, trivial⟩⟩
  exact not_subsingleton Γ(T, ⊤) ‹_›

variable {k} in
/-- **`Δ ⊔ Γ` on the affine line.** When `2` is a unit in `k`, the relation on `𝔸¹_k = Spec k[X]`
with total space `𝔸¹_k ⨿ 𝔾_m`, the diagonal on `𝔸¹_k` together with the graph
`Γ = {(x, -x) : x ≠ 0}` of `x ↦ -x` on `𝔾_m = Spec k[X, X⁻¹]`, is an étale equivalence relation
(Stacks, Example 65.14.1 (02Z1)). -/
theorem EtaleEquivRel.coprodDesc_gmToAffineLine (h2 : IsUnit (2 : k)) :
    EtaleEquivRel (coprod.desc (𝟙 _) (gmNeg k ≫ gmToAffineLine k))
      (coprod.desc (𝟙 _) (gmToAffineLine k)) :=
  coprodDesc _ _ (gmNeg_comp_gmNeg k) (isEmpty_of_comp_gmNeg h2)

/-- The target projection of `Δ ⊔ Γ` on `𝔸¹_k` is not an isomorphism. -/
theorem not_isIso_coprodDesc_gmToAffineLine [Nontrivial k] :
    ¬ IsIso (coprod.desc (𝟙 _) (gmToAffineLine k)) :=
  fun _ ↦ not_mono_coprodDesc (gmToAffineLine k) inferInstance

/-- The source projection of `Δ ⊔ Γ` on `𝔸¹_k` is not an isomorphism. -/
theorem not_isIso_coprodDesc_gmNeg_comp_gmToAffineLine [Nontrivial k] :
    ¬ IsIso (coprod.desc (𝟙 _) (gmNeg k ≫ gmToAffineLine k)) :=
  fun _ ↦ not_mono_coprodDesc (gmNeg k ≫ gmToAffineLine k) inferInstance

/-- The structure morphism `𝔸¹_k = Spec k[X] ⟶ Spec k`. -/
noncomputable abbrev affineLineToSpec : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))

/-- `𝔸¹_k ×_k 𝔸¹_k` is an equivalence relation on `𝔸¹_k`: it is the kernel pair of the structure
morphism. -/
theorem isEquivalenceRelation_pullback_affineLine :
    IsEquivalenceRelation (pullback.fst (affineLineToSpec k) (affineLineToSpec k))
      (pullback.snd (affineLineToSpec k) (affineLineToSpec k)) :=
  IsKernelPair.isEquivalenceRelation (f := affineLineToSpec k) (IsPullback.of_hasPullback _ _)

/-- For nontrivial `k`, the first projection `𝔸¹_k ×_k 𝔸¹_k ⟶ 𝔸¹_k` is not étale: as a
`k[X]`-algebra, `k[X] ⊗_k k[X] ≅ k[X][Y]` has nonzero Kähler differentials. -/
theorem not_etale_pullback_fst_affineLine [Nontrivial k] :
    ¬ Etale (pullback.fst (affineLineToSpec k) (affineLineToSpec k)) := by
  intro h
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap k[X] (k[X] ⊗[k] k[X])))) := by
    rw [← pullbackSpecIso_inv_fst']
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
    RingHom.etale_algebraMap] at this
  have := Algebra.Etale.of_equiv (polyEquivTensor' k k[X]).symm
  exact not_subsingleton k[X][X]
    ((KaehlerDifferential.polynomialEquiv k[X]).toEquiv.subsingleton_congr.mp inferInstance)

/-- For nontrivial `k`, the second projection `𝔸¹_k ×_k 𝔸¹_k ⟶ 𝔸¹_k` is not étale. -/
theorem not_etale_pullback_snd_affineLine [Nontrivial k] :
    ¬ Etale (pullback.snd (affineLineToSpec k) (affineLineToSpec k)) := by
  intro h
  refine not_etale_pullback_fst_affineLine k ?_
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

end AffineLine

end TauCeti.AlgebraicGeometry.Spaces
