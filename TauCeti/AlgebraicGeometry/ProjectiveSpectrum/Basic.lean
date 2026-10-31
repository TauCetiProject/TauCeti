/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
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
that on `D₊(f)` the functions pulled back from `Spec A₀` are the fractions `a / 1`. It also
proves the homogeneous Nullstellensatz for elements of the irrelevant ideal, with two consequences
used to compute the sections of the twisting sheaves over standard opens: a homogeneous element
vanishing in the localizations at all points of `D₊(g)` is killed by a power of `g`, and compatible
homogeneous fractions covering `D₊(f)` glue to a single fraction over a power of `f`. These two
are graded versions of the injectivity and gluing steps of Mathlib's computation of the sections
of the structure sheaf of `Spec` over basic opens
(`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_injective` and
`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_surjective` in
`Mathlib/AlgebraicGeometry/StructureSheaf.lean`), whose arguments they adapt.

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
  is invertible exactly on `D₊(fg)`; its values in the localizations are given by
  `AlgebraicGeometry.Proj.val_awayToSection_mk_apply`.
* `AlgebraicGeometry.Proj.toSpecZero_preimage_basicOpen`: the inverse image of the basic open
  `D(r)` of a degree-zero element under `Proj A ⟶ Spec A₀` is the standard open `D₊(r)`.
* `AlgebraicGeometry.Proj.toSpecZero_appLE_basicOpen`: on `D₊(f)`, the functions pulled back
  along `Proj A ⟶ Spec A₀` are the fractions `a / 1`.
* `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top`: if `A` is generated in degree
  one over `A₀`, the standard opens of degree-one elements cover `Proj A`.
* `ProjectiveSpectrum.exists_le_mem_notMem`: a projective point misses homogeneous elements of
  arbitrarily large degree.
* `ProjectiveSpectrum.ext_of_mem_pos`: positive-degree homogeneous elements determine a
  projective point, allowing comparison through its positive-degree coordinate opens.
* `ProjectiveSpectrum.mem_radical_of_zeroLocus_subset`: the homogeneous Nullstellensatz, for
  elements of the irrelevant ideal.
* `ProjectiveSpectrum.exists_pow_mul_eq_zero`: a homogeneous element which is locally zero on
  `D₊(g)` is killed by a power of `g`.
* `ProjectiveSpectrum.exists_mul_eq_pow_mul`: compatible homogeneous fractions whose standard opens
  cover `D₊(f)` glue to a single fraction with a power of `f` as denominator.
* `ProjectiveSpectrum.comap_extendOfIsLocalization` and
  `ProjectiveSpectrum.extendOfIsLocalization_comap`: if a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`
  exhibits `B` as a localization of `A` at `M`, the points of `Proj ℬ` are, through `f⁻¹`, the
  points of `Proj 𝒜` disjoint from `M`; the point over `x` is the extension of the homogeneous
  prime ideal of `x` (`ProjectiveSpectrum.extendOfIsLocalization`).
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
  -- The proof of `⊤ ≤ ⊤` carried by the restriction map has type `⊤ ≤ f ⁻¹ᵁ ⊤` only up to
  -- unfolding `Scheme.Hom.preimage`, so `Scheme.Hom.appLE_eq_app` is applied by unification
  -- rather than by `rw`; the middle term is fixed to `appTop`, whose codomain is `Γ(_, ⊤)`
  -- rather than `Γ(_, f ⁻¹ᵁ ⊤)`.
  refine Eq.trans (b := Scheme.Hom.appTop _) (Scheme.Hom.appLE_eq_app _) ?_
  -- The `show` reads `basicOpenToSpec_app_top`, stated for `app ⊤`, through the abbreviation
  -- `appTop`.
  rw [hι, Scheme.Hom.comp_appTop, basicOpenIsoSpec_hom,
    show (basicOpenToSpec 𝒜 f).appTop = _ from basicOpenToSpec_app_top 𝒜 f, ← Category.assoc,
    Scheme.ΓSpecIso_naturality]
  simp only [Category.assoc, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
  -- both sides restrict along the inclusion `D₊(f) ≤ ι '' ⊤`, and inclusions of opens are unique
  rfl

variable (𝒜) in
/-- **Generation in degree one.** If `A` is generated by `A₁` as an `A₀`-algebra, the standard
opens `D₊(f)` of the elements `f ∈ A₁` cover `Proj A`. -/
theorem iSup_basicOpen_eq_top_of_adjoin_eq_top (h : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) :
    ⨆ f : 𝒜 1, basicOpen 𝒜 (f : A) = ⊤ :=
  iSup_basicOpen_eq_top' 𝒜 _ (fun f ↦ ⟨1, f.2⟩) (by rwa [Subtype.range_coe_subtype])

section

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- On the standard chart `D₊(f)`, the function `g / fⁿ` takes the value `g / fⁿ` in the
localization at each point. -/
theorem val_awayToSection_mk_apply {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (g : A)
    (hg : g ∈ 𝒜 (n • d)) (x : basicOpen 𝒜 f) :
    ((awayToSection 𝒜 f (Away.mk 𝒜 hf n g hg)).1 x).val =
      Localization.mk g ⟨f ^ n, fun h ↦ x.2 (x.1.isPrime.mem_of_pow_mem n h)⟩ :=
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

end

end AlgebraicGeometry.Proj

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A relevant homogeneous prime ideal misses homogeneous elements of arbitrarily large degree: it
misses a homogeneous element of positive degree, and hence all of its powers. -/
theorem exists_le_mem_notMem (x : ProjectiveSpectrum 𝒜) (N : ℕ) :
    ∃ i, N ≤ i ∧ ∃ s ∈ 𝒜 i, s ∉ x.asHomogeneousIdeal := by
  obtain ⟨d, hd, f, hf, hfx⟩ : ∃ d > 0, ∃ f ∈ 𝒜 d, f ∉ x.asHomogeneousIdeal := by
    by_contra! h
    exact x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr h)
  exact ⟨N * d, Nat.le_mul_of_pos_right N hd, f ^ N, by simpa using SetLike.pow_mem_graded N hf,
    fun h ↦ hfx (x.isPrime.mem_of_pow_mem N h)⟩

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

/-- **Homogeneous Nullstellensatz on `Proj`.** If an element `f` of the irrelevant ideal lies in
every point of `Proj A` containing a homogeneous ideal `I`, then `f` lies in the radical of `I`. -/
theorem mem_radical_of_zeroLocus_subset {I : Ideal A} (hI : I.IsHomogeneous 𝒜) {f : A}
    (hf : f ∈ HomogeneousIdeal.irrelevant 𝒜) (h : zeroLocus 𝒜 I ⊆ zeroLocus 𝒜 {f}) :
    f ∈ I.radical := by
  rw [Ideal.IsHomogeneous.radical_eq hI, Submodule.mem_sInf]
  rintro J ⟨hJ, hIJ, hJp⟩
  by_contra hfJ
  -- otherwise `J` is a relevant homogeneous prime containing `I` but not `f`
  have hx : (⟨⟨J, hJ⟩, hJp, fun hle ↦ hfJ (hle hf)⟩ : ProjectiveSpectrum 𝒜) ∈ zeroLocus 𝒜 {f} :=
    h hIJ
  exact hfJ (hx (Set.mem_singleton f))

/-- Let `g` be an element of the irrelevant ideal, for instance homogeneous of positive degree,
and `a` homogeneous. If at every point `x` of `D₊(g)` the element `a` is annihilated by some element
outside `x`, then `a` is annihilated by a power of `g`. -/
theorem exists_pow_mul_eq_zero {g a : A} {k : ℕ} (hg : g ∈ HomogeneousIdeal.irrelevant 𝒜)
    (ha : a ∈ 𝒜 k)
    (h : ∀ x : ProjectiveSpectrum 𝒜, g ∉ x.asHomogeneousIdeal →
      ∃ c ∉ x.asHomogeneousIdeal, c * a = 0) :
    ∃ N, g ^ N * a = 0 := by
  classical
  -- the homogeneous core `I` of the annihilator of `a` is a homogeneous ideal annihilating `a`
  let I := (Submodule.span A {a}).annihilator.homogeneousCore 𝒜
  suffices g ∈ I.toIdeal.radical from this.imp fun N hN ↦
    (Submodule.mem_annihilator_span_singleton _ _).1 (Ideal.toIdeal_homogeneousCore_le 𝒜 _ hN)
  refine mem_radical_of_zeroLocus_subset I.isHomogeneous hg fun x hx ↦ ?_
  rw [mem_zeroLocus, Set.singleton_subset_iff]
  by_contra hgx
  obtain ⟨c, hcx, hc⟩ := h x hgx
  -- some homogeneous component `cᵢ` of `c` lies outside `x`, and `cᵢ * a = 0` lies in `I`
  obtain ⟨i, hi⟩ : ∃ i, (DirectSum.decompose 𝒜 c i : A) ∉ x.asHomogeneousIdeal := by
    by_contra! H
    exact hcx ((x.asHomogeneousIdeal.isHomogeneous.mem_iff 𝒜).2 H)
  refine hi (hx (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨i, SetLike.coe_mem _⟩
    ((Submodule.mem_annihilator_span_singleton _ _).2 ?_)))
  simpa [hc] using (DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := i) ha).symm

/-- **Gluing homogeneous fractions.** Let `f` be homogeneous of positive degree `d`, and let
`r x / g x` be finitely many fractions of homogeneous elements of degrees `deg r x = deg g x + n`
whose standard opens `D₊(g x)` cover `D₊(f)`, and which are compatible in the strong sense
`g x * r z = g z * r x`. Then there is a single fraction `R / fᵏ`, with `R` homogeneous of degree
`k * d + n`, such that `g x * R = fᵏ * r x` for every `x`. -/
theorem exists_mul_eq_pow_mul {n : ℤ} {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {ι : Type*}
    [Finite ι] {i j : ι → ℕ} (h : ∀ x, (j x : ℤ) = i x + n) {r g : ι → A}
    (hr : ∀ x, r x ∈ 𝒜 (j x)) (hg : ∀ x, g x ∈ 𝒜 (i x))
    (hcover : ∀ y : ProjectiveSpectrum 𝒜, f ∉ y.asHomogeneousIdeal →
      ∃ x, g x ∉ y.asHomogeneousIdeal)
    (hcompat : ∀ x z, g x * r z = g z * r x) :
    ∃ (k J : ℕ) (_ : (J : ℤ) = (k * d : ℕ) + n) (R : A), R ∈ 𝒜 J ∧ ∀ x, g x * R = f ^ k * r x := by
  classical
  have := Fintype.ofFinite ι
  -- `f` lies in the radical of the ideal generated by the `g x`
  obtain ⟨K, hK⟩ : f ∈ (Ideal.span (Set.range g)).radical := by
    refine mem_radical_of_zeroLocus_subset (Ideal.homogeneous_span _ _ ?_)
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hf) fun y hy ↦ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, hg x⟩
    rw [mem_zeroLocus, Set.singleton_subset_iff]
    by_contra hfy
    obtain ⟨x, hx⟩ := hcover y hfy
    exact hx (hy (Ideal.subset_span ⟨x, rfl⟩))
  -- raise the exponent so that the numerator has nonnegative degree `k * d + n`
  set k := K + n.natAbs
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1
    (show f ^ k ∈ _ from pow_add f K n.natAbs ▸ Ideal.mul_mem_right _ _ hK)
  have hkd : k ≤ k * d := Nat.le_mul_of_pos_right k hd
  set J := ((k * d : ℕ) + n).toNat
  have hJ : (J : ℤ) = (k * d : ℕ) + n := by omega
  -- the numerator is the degree-`J` part of `∑ x, c x * r x`
  refine ⟨k, J, hJ, _, SetLike.coe_mem (DirectSum.decompose 𝒜 (∑ x, c x * r x) J), fun x ↦ ?_⟩
  have hmem : f ^ k * r x ∈ 𝒜 (J + i x) := by
    convert SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) (hr x) using 2
    have := h x
    simp only [smul_eq_mul]
    omega
  have hsum : (∑ z, c z * r z) * g x = f ^ k * r x := by
    rw [Finset.sum_mul, ← hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by
      rw [mul_assoc, mul_comm (r z), hcompat x z, ← mul_assoc]
  rw [mul_comm (g x), ← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (hg x), hsum,
    DirectSum.decompose_of_mem_same 𝒜 hmem]

section Localization

open HomogeneousIdeal

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {f : 𝒜 →+*ᵍ ℬ} {M : Submonoid A} (hloc : letI := f.toRingHom.toAlgebra; IsLocalization M B)

/-- For `f : 𝒜 →+*ᵍ ℬ` exhibiting `B` as a localization of `A` at `M`, the point of `Proj ℬ`
over a point `x` of `Proj 𝒜` disjoint from `M`: its homogeneous prime ideal is the extension of
that of `x`. -/
def extendOfIsLocalization (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) : ProjectiveSpectrum ℬ where
  asHomogeneousIdeal := x.asHomogeneousIdeal.map f
  isPrime :=
    letI := f.toRingHom.toAlgebra
    IsLocalization.isPrime_of_isPrime_disjoint M B _ x.isPrime hx
  not_irrelevant_le h := by
    let := f.toRingHom.toAlgebra
    obtain ⟨i, hi, s, hs, hsx⟩ := x.exists_le_mem_notMem 1
    refine hsx ?_
    rw [← HomogeneousIdeal.mem_iff,
      ← IsLocalization.under_map_of_isPrime_disjoint M B x.isPrime hx]
    exact h (mem_irrelevant_of_mem ℬ (by omega : 0 < i) (Graded.map_mem f hs))

/-- The homogeneous prime ideal of the point over `x` is the extension of that of `x`. -/
theorem extendOfIsLocalization_asHomogeneousIdeal (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) :
    (x.extendOfIsLocalization hloc hx).asHomogeneousIdeal = x.asHomogeneousIdeal.map f :=
  (rfl)

include hloc in
/-- The point of `Proj ℬ` over `x` contains `f a` exactly when `x` contains `a`. -/
@[simp]
theorem map_mem_extendOfIsLocalization_iff (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) (a : A) :
    f a ∈ (x.extendOfIsLocalization hloc hx).asHomogeneousIdeal ↔ a ∈ x.asHomogeneousIdeal := by
  let := f.toRingHom.toAlgebra
  -- `f a ∈ x B` says that `a` lies in the contraction of the extension `x B`, which is `x`
  exact Iff.of_eq
    (congrArg (a ∈ ·) (IsLocalization.under_map_of_isPrime_disjoint M B x.isPrime hx))

variable (hf : ℬ₊ ≤ 𝒜₊.map f)
include hloc

/-- The point of `Proj ℬ` over `x` lies over `x`. -/
@[simp]
theorem comap_extendOfIsLocalization (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) :
    AlgebraicGeometry.ProjectiveSpectrum.comap f hf (x.extendOfIsLocalization hloc hx) = x :=
  ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
    (Ideal.ext (map_mem_extendOfIsLocalization_iff hloc x hx)))

/-- The points of `Proj 𝒜` under points of `Proj ℬ` are disjoint from `M`, whose image consists of
units. -/
theorem disjoint_comap_of_isLocalization (y : ProjectiveSpectrum ℬ) :
    Disjoint (M : Set A)
      (AlgebraicGeometry.ProjectiveSpectrum.comap f hf y).asHomogeneousIdeal.toIdeal := by
  let := f.toRingHom.toAlgebra
  exact Set.disjoint_left.mpr fun m hm hmy ↦
    y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmy (IsLocalization.map_units B ⟨m, hm⟩))

/-- Every point of `Proj ℬ` is the point over its image in `Proj 𝒜`. -/
@[simp]
theorem extendOfIsLocalization_comap (y : ProjectiveSpectrum ℬ) :
    (AlgebraicGeometry.ProjectiveSpectrum.comap f hf y).extendOfIsLocalization hloc
      (ProjectiveSpectrum.disjoint_comap_of_isLocalization hloc hf y) = y := by
  let := f.toRingHom.toAlgebra
  exact ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
    (IsLocalization.map_under M B y.asHomogeneousIdeal.toIdeal))

end Localization

end ProjectiveSpectrum
