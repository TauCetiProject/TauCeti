/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.EtaleEquivRel

/-!
# Examples of étale equivalence relations

This file records the Checks of the roadmap section on étale equivalence relations (Stacks,
Definition 39.3.1 (022P) and Spaces, Definition 65.9.2 (02WS)).

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.coprod_desc`: for an étale monomorphism
  `ι : V ⟶ U` and an involution `τ` of `V` without fixed points (no nonempty `f : T ⟶ V` has
  `f ≫ τ = f`), the relation `Δ ⊔ Γ` on `U`, with total space `U ⨿ V`, target
  `coprod.desc (𝟙 U) ι` and source `coprod.desc (𝟙 U) (τ ≫ ι)`, is an étale equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.not_mono_coprod_desc`: when `V` is nonempty, its
  projections are not monomorphisms, in particular not isomorphisms.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.codiag`: the kernel pair of the fold map
  `U ⨿ U ⟶ U` is an étale equivalence relation on `U ⨿ U`.
* `TauCeti.AlgebraicGeometry.Spaces.not_jointlyMono₂_codiag`: for nonempty `U`, the pair
  `(𝟙 ⊔ 𝟙, 𝟙 ⊔ 𝟙) : U ⨿ U ⟶ U × U` is not jointly monic, so it is not an equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.affineLineNeg`: over a ring `k` in which `2` is
  a unit, `Δ ⊔ Γ` on `𝔸¹_k = Spec k[X]`, with `Γ = {(x, -x) : x ≠ 0}` the graph of `x ↦ -x` on
  `Spec k[X, X⁻¹]`, is an étale equivalence relation, and
  `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.not_isIso_affineLineNeg_t`, `..._s`: for
  nontrivial `k` its projections are not isomorphisms.
* `TauCeti.AlgebraicGeometry.Spaces.isEquivalenceRelation_pullback_affineLine`,
  `TauCeti.AlgebraicGeometry.Spaces.not_etale_pullback_fst_affineLine`, `..._snd_...`:
  `𝔸¹_k ×_k 𝔸¹_k` is an equivalence relation on `𝔸¹_k` (the kernel pair of the structure
  morphism) whose projections are not étale for nontrivial `k`.

## References

* [Stacks Project, Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry TauCeti.CategoryTheory

universe u

section Coprod

variable {T A B : Scheme.{u}}

/-- Every morphism `r : T ⟶ A ⨿ B` restricts, on the members of an open cover of `T`, to a
morphism through `A` or through `B`. -/
private lemma exists_cover_coprod (r : T ⟶ A ⨿ B) :
    ∃ 𝒰 : T.OpenCover.{u}, ∀ i, (∃ a, 𝒰.f i ≫ r = a ≫ coprod.inl) ∨
      ∃ b, 𝒰.f i ≫ r = b ≫ coprod.inr :=
  ⟨(coprodOpenCover.{u, u} A B).pullback₁ r, fun i ↦ by
    rcases i with ⟨⟩ | ⟨⟩
    · exact .inl ⟨pullback.snd _ _, pullback.condition⟩
    · exact .inr ⟨pullback.snd _ _, pullback.condition⟩⟩

/-- For a jointly monic pair `t, s : R ⟶ U`, the pair `(a, c)` of morphisms `T ⟶ U` lifts to `R`
as soon as it does on the members of an open cover of `T`. -/
private lemma exists_lift_of_cover {R U : Scheme.{u}} {t s : R ⟶ U} [JointlyMono₂ t s]
    {a c : T ⟶ U} (𝒰 : T.OpenCover.{u})
    (h : ∀ i, ∃ r : 𝒰.X i ⟶ R, r ≫ t = 𝒰.f i ≫ a ∧ r ≫ s = 𝒰.f i ≫ c) :
    ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = c := by
  choose r ht hs using h
  have hr : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ r i = pullback.snd _ _ ≫ r j := fun i j ↦
    JointlyMono₂.right_cancellation (p₁ := t) (p₂ := s) _ _
      (by simp [ht, pullback.condition_assoc])
      (by simp [hs, pullback.condition_assoc])
  exact ⟨𝒰.glueMorphisms r hr, 𝒰.hom_ext _ _ fun i ↦ by simp [ht],
    𝒰.hom_ext _ _ fun i ↦ by simp [hs]⟩

/-- A morphism out of `A ⨿ B` is étale when its restrictions to `A` and to `B` are. -/
private lemma etale_coprod_desc {X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) [Etale f] [Etale g] :
    Etale (coprod.desc f g) :=
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{u, u} A B) fun i ↦ by
    rcases i with ⟨⟩ | ⟨⟩ <;> simp only [coprodOpenCover] <;> simpa using ‹_›

end Coprod

section DeltaGamma

variable {U V : Scheme.{u}} (ι : V ⟶ U) (τ : V ⟶ V)

/-- The pair `t = 𝟙 ⊔ ι`, `s = 𝟙 ⊔ (τ ≫ ι)` on `U ⨿ V` is jointly monic when `ι` is a monomorphism
and `τ` has no fixed points. -/
private lemma jointlyMono₂_coprod_desc [Mono ι]
    (hτ : ∀ {T : Scheme.{u}} (f : T ⟶ V), f ≫ τ = f → IsEmpty T) :
    JointlyMono₂ (coprod.desc (𝟙 U) ι) (coprod.desc (𝟙 U) (τ ≫ ι)) := by
  -- On a piece where one morphism goes through `U` and the other through `V`, the latter is
  -- fixed by `τ`, so the piece is empty.
  have empty {T : Scheme.{u}} (x : T ⟶ U) (y : T ⟶ V) (ht : x = y ≫ ι)
      (hs : x = y ≫ τ ≫ ι) : IsEmpty T :=
    hτ y (by rw [← cancel_mono ι, Category.assoc, ← hs, ht])
  refine ⟨fun T f g ht hs ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := exists_cover_coprod f
  refine 𝒰.hom_ext _ _ fun i ↦ ?_
  obtain ⟨𝒱, h𝒱⟩ := exists_cover_coprod (𝒰.f i ≫ g)
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
theorem EtaleEquivRel.coprod_desc [Etale ι] [Mono ι] (hττ : τ ≫ τ = 𝟙 V)
    (hτ : ∀ {T : Scheme.{u}} (f : T ⟶ V), f ≫ τ = f → IsEmpty T) :
    EtaleEquivRel (coprod.desc (𝟙 U) (τ ≫ ι)) (coprod.desc (𝟙 U) ι) := by
  have : IsIso τ := ⟨τ, hττ, hττ⟩
  have := jointlyMono₂_coprod_desc ι τ hτ
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
    obtain ⟨𝒰, h𝒰⟩ := exists_cover_coprod r₁
    refine exists_lift_of_cover 𝒰 fun i ↦ ?_
    rcases h𝒰 i with ⟨x, hx⟩ | ⟨x, hx⟩
    · refine ⟨𝒰.f i ≫ r₂, ?_, rfl⟩
      rw [Category.assoc, h₁', ← h₂, reassoc_of% hx, reassoc_of% hx]
      simp
    obtain ⟨𝒱, h𝒱⟩ := exists_cover_coprod (𝒰.f i ≫ r₂)
    refine exists_lift_of_cover 𝒱 fun j ↦ ?_
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
  · exact etale_coprod_desc _ _
  · exact etale_coprod_desc _ _

/-- If `V` is nonempty, no morphism `coprod.desc (𝟙 U) g : U ⨿ V ⟶ U` is a monomorphism: it
identifies `coprod.inr` with `g ≫ coprod.inl`. In particular neither projection of `Δ ⊔ Γ` is an
isomorphism. -/
theorem not_mono_coprod_desc [Nonempty V] (g : V ⟶ U) :
    ¬ Mono (coprod.desc (𝟙 U) g) := by
  intro h
  have : (coprod.inr : V ⟶ U ⨿ V) = g ≫ coprod.inl := by
    rw [← cancel_mono (coprod.desc (𝟙 U) g)]
    simp
  obtain ⟨x⟩ := ‹Nonempty V›
  exact inl_ne_inr U V (g x) x (by rw [this]; rfl)

end DeltaGamma

section Fold

variable (U : Scheme.{u})

/-- The kernel pair of the fold map `codiag U : U ⨿ U ⟶ U` is an étale equivalence relation on
`U ⨿ U`. -/
theorem EtaleEquivRel.kernelPair_codiag :
    EtaleEquivRel (pullback.snd (Limits.codiag U) (Limits.codiag U))
      (pullback.fst (Limits.codiag U) (Limits.codiag U)) :=
  have : Etale (Limits.codiag U) := etale_coprod_desc _ _
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

/-- The automorphism `X ↦ -X` of `k[X, X⁻¹]`, the localization of `k[X]` away from `X`. -/
noncomputable def negAwayX : Localization.Away (X : k[X]) →+* Localization.Away (X : k[X]) :=
  IsLocalization.Away.lift X (g := (algebraMap k[X] (Localization.Away (X : k[X]))).comp
    (aeval (R := k) (-X : k[X])).toRingHom) (by
      simpa using (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (X : k[X]))
        (X : k[X])).neg)

/-- `negAwayX k` substitutes `-X` for `X` in polynomials. -/
@[simp]
theorem negAwayX_algebraMap (p : k[X]) :
    negAwayX k (algebraMap k[X] (Localization.Away (X : k[X])) p) =
      algebraMap k[X] (Localization.Away (X : k[X])) (aeval (-X) p) := by
  rw [negAwayX, IsLocalization.Away.lift_eq]
  rfl

/-- `negAwayX k` is an involution. -/
@[simp]
theorem negAwayX_negAwayX (x : Localization.Away (X : k[X])) :
    negAwayX k (negAwayX k x) = x := by
  suffices (negAwayX k).comp (negAwayX k) = RingHom.id _ from congr($this x)
  refine IsLocalization.ringHom_ext (.powers (X : k[X])) ?_
  ext p <;> simp

/-- The graph `Γ` of `x ↦ -x` on `𝔾_m`: the open immersion `Spec k[X, X⁻¹] ⟶ Spec k[X]`. -/
noncomputable abbrev gmToAffineLine :
    Spec (.of (Localization.Away (X : k[X]))) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X]))))

/-- The involution `x ↦ -x` of `Spec k[X, X⁻¹]`. -/
noncomputable abbrev gmNeg :
    Spec (.of (Localization.Away (X : k[X]))) ⟶ Spec (.of (Localization.Away (X : k[X]))) :=
  Spec.map (CommRingCat.ofHom (negAwayX k))

/-- `x ↦ -x` is an involution of `Spec k[X, X⁻¹]`. -/
theorem gmNeg_comp_gmNeg : gmNeg k ≫ gmNeg k = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

variable {k} in
/-- When `2` is a unit in `k`, the involution `x ↦ -x` of `Spec k[X, X⁻¹]` has no fixed points:
a morphism `f : T ⟶ Spec k[X, X⁻¹]` with `f ≫ τ = f` sends the unit `X` to an element `a` of
`Γ(T, ⊤)` with `a = -a`, so `Γ(T, ⊤)` is the zero ring. -/
theorem isEmpty_of_comp_gmNeg (h2 : IsUnit (2 : k)) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of (Localization.Away (X : k[X])))) (hf : f ≫ gmNeg k = f) :
    IsEmpty T := by
  let φ := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have hφ : CommRingCat.ofHom (negAwayX k) ≫ φ = φ := by
    have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (negAwayX k))
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
  rcases isEmpty_or_nonempty T with hT | hT
  · exact hT
  · have : Nonempty (⊤ : T.Opens) := ⟨⟨hT.some, trivial⟩⟩
    exact absurd this (fun _ ↦ not_subsingleton Γ(T, ⊤) ‹_›)

variable {k} in
/-- **`Δ ⊔ Γ` on the affine line.** When `2` is a unit in `k`, the relation on `𝔸¹_k = Spec k[X]`
with total space `𝔸¹_k ⨿ 𝔾_m`, the diagonal on `𝔸¹_k` together with the graph
`Γ = {(x, -x) : x ≠ 0}` of `x ↦ -x` on `𝔾_m = Spec k[X, X⁻¹]`, is an étale equivalence relation. -/
theorem EtaleEquivRel.affineLineNeg (h2 : IsUnit (2 : k)) :
    EtaleEquivRel (coprod.desc (𝟙 _) (gmNeg k ≫ gmToAffineLine k))
      (coprod.desc (𝟙 _) (gmToAffineLine k)) :=
  coprod_desc _ _ (gmNeg_comp_gmNeg k) (isEmpty_of_comp_gmNeg h2)

/-- `𝔾_m` over a nontrivial ring is nonempty. -/
instance nonempty_spec_localizationAwayX [Nontrivial k] :
    Nonempty (Spec (.of (Localization.Away (X : k[X])))) :=
  have : Nontrivial (Localization.Away (X : k[X])) :=
    (IsLocalization.Away.lift (X : k[X]) (g := evalRingHom 1) (by simp)).domain_nontrivial
  inferInstanceAs (Nonempty (PrimeSpectrum _))

/-- The target projection of `Δ ⊔ Γ` on `𝔸¹_k` is not an isomorphism. -/
theorem not_isIso_affineLineNeg_t [Nontrivial k] :
    ¬ IsIso (coprod.desc (𝟙 _) (gmToAffineLine k)) :=
  fun _ ↦ not_mono_coprod_desc (gmToAffineLine k) inferInstance

/-- The source projection of `Δ ⊔ Γ` on `𝔸¹_k` is not an isomorphism. -/
theorem not_isIso_affineLineNeg_s [Nontrivial k] :
    ¬ IsIso (coprod.desc (𝟙 _) (gmNeg k ≫ gmToAffineLine k)) :=
  fun _ ↦ not_mono_coprod_desc (gmNeg k ≫ gmToAffineLine k) inferInstance

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
