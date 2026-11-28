/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveMap.Immersion
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveMap.AffineGenerators
public import TauCeti.AlgebraicGeometry.LineBundle.Power
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Projective immersions from affine nonvanishing covers

A finite affine cover by nonvanishing loci of sections of a line bundle gives a projective
immersion after taking a common positive tensor power and adding affine algebra generators.
For a proper scheme, an arbitrary affine nonvanishing cover proves projectivity.

## Main results

* `exists_isImmersion_of_isAffineOpen`: a finite affine nonvanishing cover produces an immersion
  into polynomial projective space using sections of one positive tensor power.
* `isProjectiveOver_of_isAffineOpen`: a proper scheme with an arbitrary affine nonvanishing cover
  is projective over its base ring.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 7.2 and the proof of
  Proposition 7.6.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The powered original sections augmented by prescribed global extensions. -/
@[expose, reducible]
def augmentedTensorPowSections {X : Scheme.{u}} (L : InvertibleSheaf X) {I : Type u}
    (s : I → Γ(L.obj, ⊤)) {K : I → Type u} (N : ℕ)
    (t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤)) :
    (I ⊕ Σ i, K i) → Γ((L.monoidalTensorPow N).obj, ⊤) :=
  Sum.elim (fun i ↦ Scheme.Modules.tensorPowSection (s i) N) (fun p ↦ t p.1 p.2)

/-- An original coordinate is the prescribed section raised to the chosen tensor power. -/
@[simp]
theorem augmentedTensorPowSections_inl {X : Scheme.{u}} (L : InvertibleSheaf X) {I : Type u}
    (s : I → Γ(L.obj, ⊤)) {K : I → Type u} (N : ℕ)
    (t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤)) (i : I) :
    L.augmentedTensorPowSections s N t (Sum.inl i) =
      Scheme.Modules.tensorPowSection (s i) N := rfl

/-- An added coordinate is its prescribed global extension. -/
@[simp]
theorem augmentedTensorPowSections_inr {X : Scheme.{u}} (L : InvertibleSheaf X) {I : Type u}
    (s : I → Γ(L.obj, ⊤)) {K : I → Type u} (N : ℕ)
    (t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤)) (i : I) (k : K i) :
    L.augmentedTensorPowSections s N t (Sum.inr ⟨i, k⟩) = t i k := rfl

variable {X : Scheme.{u}} (L : InvertibleSheaf X) {I R : Type u} [CommRing R]
  [Finite I] (s : I → Γ(L.obj, ⊤)) (c : R →+* Γ(X, ⊤))

omit [Finite I] in
/-- Extending algebra generators in one positive tensor degree makes the map defined by the
powered original sections and those extensions an immersion over the coefficient ring. -/
theorem exists_isImmersion_of_tensorPow_extensions
    (ha : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (s i)))
    (hcover : ⨆ i, L.obj.nonvanishingLocus (s i) = ⊤)
    {K : I → Type u}
    (f : ∀ i, K i → Γ(X, L.obj.nonvanishingLocus (s i)))
    (hf : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE le_top).op).hom.comp c) (f i)))
    {N : ℕ} (hN : 0 < N) (t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤))
    (ht : L.IsTensorPowExtension s f N t) :
    ∃ (hu : ⨆ j, (L.monoidalTensorPow N).obj.nonvanishingLocus
        (L.augmentedTensorPowSections s N t j) = ⊤),
      IsImmersion ((L.monoidalTensorPow N).projectiveMap
        (L.augmentedTensorPowSections s N t) c hu) := by
  let M : InvertibleSheaf X := L.monoidalTensorPow N
  have : SheafOfModules.isInvertible X M.obj := M.property
  let u : (I ⊕ Σ i, K i) → Γ(M.obj, ⊤) := L.augmentedTensorPowSections s N t
  let V (j : I ⊕ Σ i, K i) : X.Opens := @Scheme.Modules.nonvanishingLocus X M.obj M.property ⊤ (u j)
  have hU (i : I) : V (Sum.inl i) =
      L.obj.nonvanishingLocus (s i) :=
    Scheme.Modules.nonvanishingLocus_tensorPowSection (s i) hN
  have hu : ⨆ j, V j = ⊤ := by
    apply top_unique
    rw [← hcover]
    exact iSup_le fun i ↦ (hU i).symm.le.trans (le_iSup _ (Sum.inl i))
  have hratio (i : I) (k : K i) :
      X.presheaf.map (homOfLE (hU i).ge).op
          (M.sectionRatio u (Sum.inl i) (Sum.inr ⟨i, k⟩)) = f i k := by
    have hgen : L.obj.nonvanishingLocus (s i) ≤
        @Scheme.Modules.nonvanishingLocus X M.obj M.property (L.obj.nonvanishingLocus (s i))
        (M.obj.presheaf.map (homOfLE le_top).op (u (Sum.inl i))) := by
      rw [@Scheme.Modules.nonvanishingLocus_map X M.obj M.property ⊤
        (L.obj.nonvanishingLocus (s i)) (homOfLE le_top) (u (Sum.inl i))]
      -- The augmented coordinate is the original section raised to the chosen positive power.
      change L.obj.nonvanishingLocus (s i) ≤ L.obj.nonvanishingLocus (s i) ⊓ V (Sum.inl i)
      rw [hU]
      exact le_inf le_rfl le_rfl
    apply @Scheme.Modules.injective_smul_of_le_nonvanishingLocus X M.obj M.property
      (L.obj.nonvanishingLocus (s i)) _ hgen
    beta_reduce
    calc
      _ = M.obj.presheaf.map (homOfLE le_top).op (u (Sum.inr ⟨i, k⟩)) := by
        simpa only [Subsingleton.elim
          (L.obj.nonvanishingLocus (s i)).leTop
          (homOfLE (le_top : L.obj.nonvanishingLocus (s i) ≤ ⊤))] using
            M.map_sectionRatio_smul u (Sum.inl i) (Sum.inr ⟨i, k⟩) (hU i).ge
      _ = _ := (IsTensorPowExtension.map_eq L ht i k).trans (by
        dsimp only [M, u, augmentedTensorPowSections, Sum.elim_inl]
        rw [Scheme.Modules.map_tensorPowSection])
  have hsurj (i : I) : Function.Surjective (M.coordinateRingHom u c (Sum.inl i)) :=
    M.surjective_coordinateRingHom_of_generators u c (Sum.inl i) (hU i).symm
      (f i) (hf i) (fun k ↦ Sum.inr ⟨i, k⟩) (hratio i)
  have : IsImmersion (M.projectiveMap u c hu) :=
    M.isImmersion_projectiveMap_of_surjective u c hu Sum.inl
      -- These opens are the nonvanishing loci of the powered original sections.
      (by change ⨆ i, V (Sum.inl i) = ⊤; simpa only [hU] using hcover)
      (fun i ↦ by change IsAffineOpen (V (Sum.inl i)); rw [hU]; exact ha i) hsurj
  exact ⟨hu, inferInstance⟩

/-- A finite affine nonvanishing cover gives a positive degree and global sections augmenting
the powered original sections whose projective map is an immersion. Its twisting-sheaf pullback
recovers that tensor power by `projectiveMapPullbackTwistingSheafIso`. -/
theorem exists_isImmersion_of_isAffineOpen
    [LocallyOfFiniteType (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c))]
    (ha : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (s i)))
    (hcover : ⨆ i, L.obj.nonvanishingLocus (s i) = ⊤) :
    ∃ (N : ℕ) (_ : 0 < N) (K : I → Type u) (_ : ∀ i, Finite (K i))
      (t : ∀ i, K i → Γ(TauCeti.tensorPow L.obj N, ⊤)),
      ∃ (hu : ⨆ j, (L.monoidalTensorPow N).obj.nonvanishingLocus
          (L.augmentedTensorPowSections s N t j) = ⊤),
        IsImmersion ((L.monoidalTensorPow N).projectiveMap
          (L.augmentedTensorPowSections s N t) c hu) := by
  obtain ⟨K, hK, f, hf, N, hN, t, ht⟩ :=
    L.exists_affine_generators_common_tensorPow s c ha hcover
  let _ (i : I) : Finite (K i) := hK i
  exact ⟨N, hN, K, hK, t,
    L.exists_isImmersion_of_tensorPow_extensions s c ha hcover f hf hN t ht⟩

omit [Finite I] in
/-- A proper scheme over a ring is projective if one line bundle admits an affine
nonvanishing cover. -/
theorem isProjectiveOver_of_isAffineOpen [X.Over (Spec (.of R))]
    [IsProper (X ↘ Spec (.of R))]
    (ha : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (s i)))
    (hcover : ⨆ i, L.obj.nonvanishingLocus (s i) = ⊤) : X.IsProjectiveOver R := by
  let f := X ↘ Spec (.of R)
  let c : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom
  have hc : X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c) = f := by
    -- The coefficient ring map is the global-sections map of the structure morphism.
    change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c)) := hc ▸ inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ (L.obj.nonvanishingLocus (s i) : Set X))
    (fun i ↦ (L.obj.nonvanishingLocus (s i)).isOpen) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hcov : ⨆ i : T, L.obj.nonvanishingLocus (s i) = ⊤ := top_unique fun x _ ↦ by
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩
  obtain ⟨N, _, K, hK, t, hu, hg⟩ :=
    L.exists_isImmersion_of_isAffineOpen (fun i : T ↦ s i) c (fun i ↦ ha i) hcov
  let _ (i : T) : Finite (K i) := hK i
  have := hg
  have := (L.monoidalTensorPow N).isClosedImmersion_projectiveMap
    (L.augmentedTensorPowSections (fun i : T ↦ s i) N t) c hu
  have : ((L.monoidalTensorPow N).projectiveMap
      (L.augmentedTensorPowSections (fun i : T ↦ s i) N t) c hu).IsOver (Spec (.of R)) :=
    ⟨((L.monoidalTensorPow N).projectiveMap_toSpecCoeff _ c hu).trans hc⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion R
    ((L.monoidalTensorPow N).projectiveMap _ c hu)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
