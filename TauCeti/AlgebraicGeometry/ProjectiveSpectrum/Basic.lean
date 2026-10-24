/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Points of `Proj` through standard charts, and compatibilities of `Proj.map`

For a graded ring `A`, a ring homomorphism `φ : A →+* R` and a homogeneous element `f` of positive
degree with `φ f` a unit, the composite

`Spec R ⟶ Spec A_{(f)} ⟶ Proj A`

of `Spec` of `HomogeneousLocalization.Away.lift φ` with the standard chart `Proj.awayι` is the
`R`-point of `Proj A` with "homogeneous coordinates" `φ`. This file proves that it does not
depend on the chart: any other homogeneous `g` of positive degree with `φ g` a unit gives the same
morphism. It also proves that `Proj.map` of a graded ring homomorphism lies over the induced map on
`Spec` of the degree-zero parts, and packages `Proj.map` of a graded ring isomorphism as an
isomorphism of schemes. It computes the locus where a function `g / fⁿ` on a standard
chart `D₊(f)` is invertible: it is `D₊(fg)`, so the restriction of sections from `D₊(f)` to
`D₊(fg)` is a localization at `g / fⁿ`. Finally, it identifies the inverse image under
`Proj A ⟶ Spec A₀` of the basic open of a degree-zero element `r` with the standard open `D₊(r)`,
so that the structure map to `Spec A₀` can be studied through homogeneous prime ideals, and shows
that on `D₊(f)` the functions pulled back from `Spec A₀` are the fractions `a / 1`.

## Main definitions

* `AlgebraicGeometry.Proj.mapIso`: the isomorphism `Proj ℬ ≅ Proj 𝒜` induced by mutually inverse
  graded ring homomorphisms.

## Main results

* `AlgebraicGeometry.Proj.map_congr`: `Proj.map f` depends only on `f`.
* `AlgebraicGeometry.Proj.SpecMap_awayLift_awayι_eq`: the point of `Proj A` defined by `φ` on the
  chart `D₊(f)` agrees with the one defined on the chart `D₊(g)`.
* `AlgebraicGeometry.Proj.map_toSpecZero`: `Proj.map f` lies over `Spec` of the degree-zero part
  of `f`.
* `AlgebraicGeometry.Proj.basicOpen_awayToSection_mk`: on the chart `D₊(f)`, the function `g / fⁿ`
  is invertible exactly on `D₊(fg)`.
* `AlgebraicGeometry.Proj.toSpecZero_preimage_basicOpen`: the inverse image of the basic open
  `D(r)` of a degree-zero element under `Proj A ⟶ Spec A₀` is the standard open `D₊(r)`.
* `AlgebraicGeometry.Proj.toSpecZero_appLE_basicOpen`: on `D₊(f)`, the functions pulled back
  along `Proj A ⟶ Spec A₀` are the fractions `a / 1`.
* `ProjectiveSpectrum.ext_of_mem_pos`: positive-degree homogeneous elements determine a
  projective point, allowing comparison through its positive-degree coordinate opens.
-/

public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The `R`-point of `Proj A` with homogeneous coordinates `φ : A →+* R`, read on the standard
chart `D₊(f)`, does not depend on the homogeneous element `f` of positive degree with `φ f` a
unit: both charts give the point read on `D₊(fg)`. -/
theorem SpecMap_awayLift_awayι_eq {R : Type u} [CommRing R] (φ : A →+* R) {f g : A} {m m' : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') (hf : IsUnit (φ f))
    (hg : IsUnit (φ g)) :
    Spec.map (CommRingCat.ofHom (Away.lift 𝒜 φ hf)) ≫ awayι 𝒜 f f_deg hm =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 φ hg)) ≫ awayι 𝒜 g g_deg hm' := by
  have hfg : IsUnit (φ (f * g)) := by rw [map_mul]; exact hf.mul hg
  rw [← Away.lift_comp_awayMap φ g_deg rfl hfg hf,
    ← Away.lift_comp_awayMap φ f_deg (mul_comm f g) hfg hg, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    SpecMap_awayMap_awayι, SpecMap_awayMap_awayι]
  -- the two charts `D₊(fg)` differ only in the order of the degree `m + m'` of `fg`
  congr 2
  exact add_comm m m'

/-- `Proj.map f` lies over `Spec` of the ring homomorphism `𝒜 0 →+* ℬ 0` induced by `f` on the
degree-zero parts. -/
@[reassoc (attr := simp)]
theorem map_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤
    (HomogeneousIdeal.irrelevant 𝒜).map f) :
    map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun ⟨i, x, hx⟩ ↦ ?_
  -- the chart of `mapAffineOpenCover` at `⟨i, x⟩` is `awayι ℬ (f x)`, by definition
  have hpos : 0 < (i : ℕ) := i.2
  have key : awayι ℬ (f x) (f.2 hx) hpos ≫ map f hf ≫ toSpecZero 𝒜 =
      awayι ℬ (f x) (f.2 hx) hpos ≫ toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
    rw [awayι_comp_map_assoc f hf hpos x hx, awayι_toSpecZero, awayι_toSpecZero_assoc,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    have h𝒜 : fromZeroRingHom 𝒜 (.powers x) a = Away.mk 𝒜 hx 0 a (by simp) := by
      ext
      exact (Localization.mk_eq_mk_iff.mpr (by simp [Localization.r_iff_exists])).symm
    rw [h𝒜, Away.map_mk]
    exact Localization.mk_eq_mk_iff.mpr (by simp [Localization.r_iff_exists])
  exact key

/-- `Proj.map f` depends only on the graded ring homomorphism `f`, and not on the proof that the
irrelevant ideal of the target is contained in the ideal generated by the image of the irrelevant
ideal of the source. -/
theorem map_congr {f g : 𝒜 →+*ᵍ ℬ} (hfg : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    map f hf = map g hg := by
  subst hfg
  rfl

/-- Mutually inverse graded ring homomorphisms `f : 𝒜 →+*ᵍ ℬ` and `g : ℬ →+*ᵍ 𝒜` induce mutually
inverse morphisms `Proj.map f` and `Proj.map g`. -/
noncomputable def mapIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : Function.RightInverse g f)
    (hgf : Function.LeftInverse g f) : Proj ℬ ≅ Proj 𝒜 where
  hom := map f (HomogeneousIdeal.irrelevant_le_map_of_surjective f hfg.surjective)
  inv := map g (HomogeneousIdeal.irrelevant_le_map_of_surjective g hgf.surjective)
  hom_inv_id := by
    rw [← map_comp]
    convert map_id (𝒜 := ℬ)
    exact GradedRingHom.ext hfg
  inv_hom_id := by
    rw [← map_comp]
    convert map_id (𝒜 := 𝒜)
    exact GradedRingHom.ext hgf

@[simp]
theorem mapIso_hom (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : Function.RightInverse g f)
    (hgf : Function.LeftInverse g f) :
    (mapIso f g hfg hgf).hom =
      map f (HomogeneousIdeal.irrelevant_le_map_of_surjective f hfg.surjective) :=
  (rfl)

@[simp]
theorem mapIso_inv (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : Function.RightInverse g f)
    (hgf : Function.LeftInverse g f) :
    (mapIso f g hfg hgf).inv =
      map g (HomogeneousIdeal.irrelevant_le_map_of_surjective g hgf.surjective) :=
  (rfl)

/-- On the standard chart `D₊(f)`, the function `g / fⁿ` is invertible exactly on `D₊(fg)`. -/
theorem basicOpen_awayToSection_mk {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (g : A)
    (hg : g ∈ 𝒜 (n • d)) :
    (Proj 𝒜).basicOpen (awayToSection 𝒜 f (Away.mk 𝒜 hf n g hg)) = basicOpen 𝒜 (f * g) := by
  ext p
  rw [SetLike.mem_coe, SetLike.mem_coe, basicOpen_mul, TopologicalSpace.Opens.mem_inf]
  by_cases hp : p ∈ basicOpen 𝒜 f
  · -- the germ of `g / fⁿ` at `p` is `g / fⁿ` in the homogeneous localization at `p`
    rw [Scheme.mem_basicOpen _ _ _ hp]
    have h := ConcreteCategory.congr_hom (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f p hp)
      (Away.mk 𝒜 hf n g hg)
    -- `erw`: the germ map of the scheme `Proj 𝒜` is that of its structure sheaf only up to
    -- unfolding the scheme structure
    erw [h]
    refine (MulEquiv.isUnit_map (Proj.stalkIso' 𝒜 p).symm.toMulEquiv
      (x := mapId 𝒜 (Submonoid.powers_le.mpr hp) (Away.mk 𝒜 hf n g hg))).trans ?_
    rw [← isUnit_iff_isUnit_val]
    -- `erw`: the homogeneous prime of `p` is read through the same identification
    erw [Away.mk, map_mk, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact ⟨fun h ↦ ⟨hp, h⟩, And.right⟩
  · simp only [hp, false_and, iff_false]
    exact fun h ↦ hp ((Proj 𝒜).basicOpen_le _ h)

variable (𝒜) in
/-- **Degree-zero basic opens.** The inverse image under `Proj A ⟶ Spec A₀` of the basic open
`D(r)` of a degree-zero element `r` is the standard open `D₊(r)` of `Proj A`: the points `x` with
`r ∉ x`. -/
@[simp]
theorem toSpecZero_preimage_basicOpen (r : 𝒜 0) :
    toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen r = basicOpen 𝒜 (r : A) := by
  ext x
  -- `x` lies in some standard chart `D₊(f)` with `f` homogeneous of positive degree.
  obtain ⟨i, hi, f, f_deg, hfx⟩ : ∃ i > 0, ∃ f ∈ 𝒜 i, f ∉ x.asHomogeneousIdeal := by
    by_contra! h
    exact x.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp
      ((HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr h))
  obtain ⟨z, rfl⟩ : x ∈ (awayι 𝒜 f f_deg hi).opensRange := by rwa [opensRange_awayι]
  have h₁ : awayι 𝒜 f f_deg hi z ∈ toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen r ↔
      z ∈ (PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 _ r) : (Spec (.of (Away 𝒜 f))).Opens) := by
    have h := Scheme.Hom.comp_preimage (awayι 𝒜 f f_deg hi) (toSpecZero 𝒜)
      (PrimeSpectrum.basicOpen r)
    rw [awayι_toSpecZero, SpecMap_preimage_basicOpen] at h
    rw [← Scheme.Hom.mem_preimage, ← h, CommRingCat.ofHom_apply]
    -- the sides differ only in typing `D(r / 1)` as an open of `Spec` or of the prime spectrum
    rfl
  -- On `D₊(f)`, the standard open `D₊(r) = D₊(r f)` is cut out by `(r f)ⁱ / fⁱ = (r / 1)ⁱ`.
  have hrf : (r : A) * f ∈ 𝒜 i := by simpa using SetLike.mul_mem_graded r.2 f_deg
  have helem : Away.isLocalizationElem f_deg hrf = fromZeroRingHom 𝒜 _ r ^ i := by
    apply val_injective
    -- `fromZeroRingHom` sends `r` to the fraction `r / 1`
    have hr : (fromZeroRingHom 𝒜 (Submonoid.powers f) r).val = Localization.mk (r : A) 1 := by
      simp only [fromZeroRingHom]
      exact val_mk _
    rw [Away.val_mk, val_pow, hr, Localization.mk_pow, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp [mul_pow, mul_comm]⟩
  have h₂ : awayι 𝒜 f f_deg hi z ∈ basicOpen 𝒜 (r : A) ↔
      z ∈ (PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 _ r) : (Spec (.of (Away 𝒜 f))).Opens) := by
    have hzf : awayι 𝒜 f f_deg hi z ∈ basicOpen 𝒜 f := opensRange_awayι 𝒜 f f_deg hi ▸ ⟨z, rfl⟩
    rw [← PrimeSpectrum.basicOpen_pow _ i hi, ← helem,
      ← awayι_preimage_basicOpen 𝒜 f_deg hi hrf hi]
    exact ⟨fun h ↦ (basicOpen_mul 𝒜 _ _).ge ⟨h, hzf⟩, fun h ↦ ((basicOpen_mul 𝒜 _ _).le h).1⟩
  exact h₁.trans h₂.symm

variable (𝒜) in
/-- **Constants on a standard chart.** On the chart `D₊(f)`, for `f` homogeneous of positive degree,
the functions pulled back from `Spec A₀` along `Proj A ⟶ Spec A₀` are the fractions `a / 1` of
degree-zero elements `a`. -/
theorem toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (toSpecZero 𝒜).appLE ⊤ (basicOpen 𝒜 f) le_top =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (fromZeroRingHom 𝒜 _) ≫ awayToSection 𝒜 f := by
  -- compose with the isomorphism `Γ(Proj A, D₊(f)) ≅ Γ(D₊(f), ⊤)` given by the inclusion
  rw [← cancel_mono ((basicOpen 𝒜 f).ι.appLE (basicOpen 𝒜 f) ⊤ (basicOpen 𝒜 f).ι_preimage_self.ge)]
  refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
  -- on `D₊(f) ≅ Spec A_(f)`, the structure map is `Spec` of `A₀ → A_(f)`
  have hι : (basicOpen 𝒜 f).ι ≫ toSpecZero 𝒜 = (basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
    rw [← awayι_toSpecZero 𝒜 f f_deg hm, ← basicOpenIsoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  -- The first `show` reads `appLE ⊤ ⊤` as `appTop` through `appLE_eq_app`, relying on the
  -- definitional equality `f ⁻¹ᵁ ⊤ = ⊤` (`Scheme.Hom.preimage_top`, proved by `rfl`), which `rw`
  -- cannot match; the second reads `basicOpenToSpec_app_top`, stated for `app ⊤`, through the
  -- abbreviation `appTop`.
  rw [show ((basicOpen 𝒜 f).ι ≫ toSpecZero 𝒜).appLE ⊤ ⊤ _ =
      ((basicOpen 𝒜 f).ι ≫ toSpecZero 𝒜).appTop from Scheme.Hom.appLE_eq_app _, hι,
    Scheme.Hom.comp_appTop, basicOpenIsoSpec_hom,
    show (basicOpenToSpec 𝒜 f).appTop = _ from basicOpenToSpec_app_top 𝒜 f, ← Category.assoc,
    Scheme.ΓSpecIso_naturality]
  simp only [Category.assoc, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
  -- both sides restrict along the inclusion `D₊(f) ≤ ι '' ⊤`, and inclusions of opens are unique
  rfl

end AlgebraicGeometry.Proj

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Relevant homogeneous prime ideals are determined by their positive-degree elements. -/
theorem ext_of_mem_pos {x y : ProjectiveSpectrum 𝒜}
    (h : ∀ n > 0, ∀ s ∈ 𝒜 n,
      s ∈ x.asHomogeneousIdeal ↔ s ∈ y.asHomogeneousIdeal) : x = y := by
  have hex : ∃ n > 0, ∃ t ∈ 𝒜 n, t ∉ x.asHomogeneousIdeal := by
    by_contra! ht
    exact x.not_irrelevant_le ((toIdeal_le_toIdeal_iff).mp
      ((HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr ht))
  obtain ⟨n, hn, t, ht, htx⟩ := hex
  have hty : t ∉ y.asHomogeneousIdeal := fun hy ↦ htx ((h n hn t ht).mpr hy)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro i s hs
  rcases i with _ | i
  · have hst : s * t ∈ 𝒜 n := by
      simpa using SetLike.mul_mem_graded hs ht
    have heq := h n hn (s * t) hst
    have htx' : t ∉ x.asHomogeneousIdeal.toIdeal := HomogeneousIdeal.mem_iff.not.mpr htx
    have hty' : t ∉ y.asHomogeneousIdeal.toIdeal := HomogeneousIdeal.mem_iff.not.mpr hty
    simpa only [← HomogeneousIdeal.mem_iff, x.isPrime.mul_mem_iff_mem_or_mem,
      y.isPrime.mul_mem_iff_mem_or_mem, htx', hty', or_false] using heq
  · exact h (i + 1) (Nat.succ_pos i) s hs

end ProjectiveSpectrum
