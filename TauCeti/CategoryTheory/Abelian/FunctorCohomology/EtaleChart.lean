/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.OpenSubfunctor
public import TauCeti.CategoryTheory.ObjectProperty.Extensions

/-!
# Étale charts, atlases and charting subfunctors

Let `X` be a functor on commutative algebras over a ring `k`. This file gives `X` coordinates in
the sense of smooth schemes, through charts étale over affine space.

* `CategoryTheory.Functor.EtaleChart X d`: an *étale chart of dimension `d`* of `X` is a
  `k`-algebra `R` with elements `x₁, …, x_d` such that `k[X₁, …, X_d] → R`, `Xᵢ ↦ xᵢ`, is étale,
  together with a point `y ∈ X(R)` such that `φ ↦ X(φ)(y)` is injective on `R ⟶ A` for every `A`
  and has an open image (`CategoryTheory.Subfunctor.IsOpen`), the *locus* of the chart. The locus
  is corepresented by `R` (`CategoryTheory.Functor.EtaleChart.locusCorepresentableBy`).
* `CategoryTheory.Functor.HasAtlas X d`: `X` has an *atlas of dimension `d`* if it is separated
  and the loci of finitely many étale charts of dimension `d` contain every point of `X` with
  values in a field. The union of these loci is then Zariski-locally everything
  (`CategoryTheory.Functor.HasAtlas.exists_isZariskiLocallyTop`).
* `CategoryTheory.Subfunctor.IsCharting V`: a subfunctor `V` of `X` is *charting* if it is
  Zariski-locally everything and the free abelian functor `ℤ[V]` lies in every closed class of
  functors to abelian groups (`CategoryTheory.ObjectProperty.IsClosedClass`) that contains
  `ℤ[h_R]` for the algebra `R` of every étale chart of `X` whose coordinates are units, that is,
  of every chart étale over a torus.

The notions are modelled on the functor of points of a quasi-compact scheme smooth of relative
dimension `d` over `k`, whose affine opens étale over affine space give charts; that example is
not treated in this file.

## Main results

* `CategoryTheory.Functor.EtaleChart.away`: the restriction of a chart to the basic open subset
  of its algebra where an element `r` is a unit, a chart on `R[1/r]`; its locus consists of the
  points coming from maps that send `r` to a unit. Openness of this locus is the transitivity of
  openness (`CategoryTheory.Subfunctor.IsOpen.image_ι`). Restricting to the locus where all
  coordinates are units gives a chart étale over a torus
  (`CategoryTheory.Functor.EtaleChart.awayProd`).
* `CategoryTheory.Functor.CorepresentableBy.etaleChart`: a functor corepresented by an algebra `R`
  étale over affine space has the chart on `R` itself, whose locus is everything; and
  `CategoryTheory.Functor.CorepresentableBy.etaleChartAway`: for `r ∈ R`, a localization `R[1/r]`
  étale over affine space gives a chart whose locus is the basic open subfunctor `D(r)`.
* `CategoryTheory.Functor.CorepresentableBy.hasAtlas_of_span_eq_top`: a functor corepresented by
  `R` has an atlas of dimension `d` once elements generating the unit ideal of `R` have
  localizations étale over affine space of dimension `d`; for instance affine space itself
  (`CategoryTheory.Functor.CorepresentableBy.hasAtlas_mvPolynomial`).
* `CategoryTheory.Functor.EtaleChart.isCharting_locus`: the locus of a chart étale over a torus
  is charting if it is Zariski-locally everything; hence the functor corepresented by an algebra
  étale over a torus is charting in itself, for instance the torus
  (`CategoryTheory.Functor.CorepresentableBy.isCharting_top_away_prod_X`).

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*, Quatrième partie,
  Publ. Math. IHÉS 32, 1967, Corollaire 17.11.4 (a smooth morphism is étale over affine space
  locally on the source).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/General/Geometry/EtaleCharts.lean` (declarations `New.Variety.EtaleChart`,
  `New.Variety.HasAtlas`, `New.Variety.IsCharting`); Apache 2.0, Copyright 2026 Anthropic, PBC.
  The definitions are adapted from these declarations.
-/

public section

open CategoryTheory Opposite

universe w u' u

namespace CategoryTheory

section General

variable {k : Type u'} [CommRing k]

namespace Functor

section Away

variable {X : CommAlgCat.{u} k ⥤ Type w} {R : CommAlgCat.{u} k} (y : X.obj R) (r : R)

/-- The points of `X` that come from the image of `y ∈ X(R)` in `X(R[1/r])` are those that come
from `y` along maps `R ⟶ A` sending `r` to a unit. -/
private lemma mem_ofElement_map_away_iff {A : CommAlgCat.{u} k} {x : X.obj A} :
    x ∈ (Subfunctor.ofElement (X.map (CommAlgCat.ofHom
      (IsScalarTower.toAlgHom k R (Localization.Away r))) y)).obj A ↔
      ∃ φ : R ⟶ A, IsUnit (φ r) ∧ X.map φ y = x := by
  rw [Subfunctor.mem_ofElement_obj_iff]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨_ ≫ ψ, (IsLocalization.Away.algebraMap_isUnit r).map ψ.hom,
      Functor.map_comp_apply X _ ψ y⟩
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (f := φ.hom) r hφ), ?_⟩
    have : CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r)) ≫
        CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom (f := φ.hom) r hφ) = φ := by
      ext a
      exact IsLocalization.Away.lift_eq r hφ a
    rw [← Functor.map_comp_apply, this]

/-- If distinct maps out of `R` carry `y` to distinct points, then distinct maps out of `R[1/r]`
carry the image of `y` in `X(R[1/r])` to distinct points: maps out of a localization are
determined on `R`. -/
private lemma injective_map_away (hy : ∀ {A : CommAlgCat.{u} k},
      Function.Injective fun φ : R ⟶ A ↦ X.map φ y) {A : CommAlgCat.{u} k} :
    Function.Injective fun φ : CommAlgCat.of k (Localization.Away r) ⟶ A ↦
      X.map φ (X.map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r))) y) := by
  intro φ ψ h
  simp only [← Functor.map_comp_apply] at h
  ext1
  exact IsLocalization.algHom_ext (Submonoid.powers r) congr(($(hy h)).hom)

end Away

/-- An *étale chart of dimension `d`* of a functor `X` on commutative `k`-algebras: a `k`-algebra
`R` with elements `x₁, …, x_d` such that `k[X₁, …, X_d] → R`, `Xᵢ ↦ xᵢ`, is étale, and a point
`y ∈ X(R)` such that `φ ↦ X(φ)(y)` is injective on the maps `R ⟶ A` for every `A` and has an open
subfunctor of `X` as its image, the *locus* of the chart. -/
structure EtaleChart (X : CommAlgCat.{u} k ⥤ Type w) (d : ℕ) where
  /-- The `k`-algebra of the chart. -/
  R : CommAlgCat.{u} k
  /-- The coordinates of the chart. -/
  coord : Fin d → R
  /-- The coordinates make `R` étale over the polynomial ring in `d` variables. -/
  etale_aeval : (MvPolynomial.aeval (R := k) coord).toRingHom.Etale
  /-- The point of `X` with values in `R`. -/
  pt : X.obj R
  /-- Distinct maps out of `R` carry `pt` to distinct points. -/
  injective {A : CommAlgCat.{u} k} : Function.Injective fun φ : R ⟶ A ↦ X.map φ pt
  /-- The points of `X` that come from `pt` form an open subfunctor. -/
  isOpen_ofElement : (Subfunctor.ofElement pt).IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u})

namespace EtaleChart

variable {X : CommAlgCat.{u} k ⥤ Type w} {d : ℕ} (c : X.EtaleChart d)

/-- The *locus* of an étale chart: the open subfunctor of `X` of the points `X(φ)(y)` that come
from the point `y` of the chart. -/
def locus : Subfunctor X :=
  Subfunctor.ofElement c.pt

/-- A point lies in the locus of a chart exactly when it comes from the point of the chart. -/
@[simp]
lemma mem_locus_obj_iff {A : CommAlgCat.{u} k} {x : X.obj A} :
    x ∈ c.locus.obj A ↔ ∃ φ : c.R ⟶ A, X.map φ c.pt = x :=
  Subfunctor.mem_ofElement_obj_iff c.pt

/-- The point of a chart lies in its locus. -/
lemma pt_mem_locus : c.pt ∈ c.locus.obj c.R :=
  Subfunctor.mem_ofElement_obj c.pt

/-- The locus of a chart is an open subfunctor. -/
lemma isOpen_locus : c.locus.IsOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) :=
  c.isOpen_ofElement

/-- The locus of an étale chart is corepresented by the algebra of the chart: a map `φ : R ⟶ A`
corresponds to the point `X(φ)(y)`. -/
noncomputable def locusCorepresentableBy : c.locus.toFunctor.CorepresentableBy c.R where
  homEquiv := Equiv.ofBijective (fun φ ↦ ⟨X.map φ c.pt, c.mem_locus_obj_iff.2 ⟨φ, rfl⟩⟩)
    ⟨fun _ _ h ↦ c.injective (congrArg Subtype.val h), fun x ↦
      have ⟨φ, hφ⟩ := c.mem_locus_obj_iff.1 x.property
      ⟨φ, Subtype.ext hφ⟩⟩
  homEquiv_comp g f := Subtype.ext (by
    simp only [Subfunctor.toFunctor_map]
    exact Functor.map_comp_apply X f g c.pt)

/-- The point of the locus corresponding to `φ : R ⟶ A` is `X(φ)(y)`. Not a `simp` lemma: its
left-hand side is not in simp normal form, since `simp` rewrites the type of the point through
`CategoryTheory.Subfunctor.toFunctor_obj`. -/
lemma coe_locusCorepresentableBy_homEquiv {A : CommAlgCat.{u} k} (φ : c.R ⟶ A) :
    (c.locusCorepresentableBy.homEquiv φ : X.obj A) = X.map φ c.pt :=
  (rfl)

/-! #### Restricting a chart to a basic open subset -/

/-- The coordinates of an étale chart, read in a localization `R[1/r]` of its algebra, make it
étale over the polynomial ring. -/
lemma etale_aeval_away (r : c.R) : (MvPolynomial.aeval (R := k)
    fun i ↦ algebraMap c.R (Localization.Away r) (c.coord i)).toRingHom.Etale := by
  have : (MvPolynomial.aeval (R := k)
      fun i ↦ algebraMap c.R (Localization.Away r) (c.coord i)).toRingHom =
      (algebraMap c.R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) c.coord).toRingHom := by
    ext <;> simp [← IsScalarTower.algebraMap_apply]
  rw [this]
  -- `RingHom.Etale.stableUnderComposition` needs all rings in one universe; compose the
  -- unramified and smooth parts instead.
  have hf := (RingHom.etale_iff_formallyUnramified_and_smooth _).1 c.etale_aeval
  have hg := (RingHom.etale_iff_formallyUnramified_and_smooth _).1
    (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway (A := Localization.Away r) r))
  rw [RingHom.etale_iff_formallyUnramified_and_smooth]
  exact ⟨hf.1.comp hg.1, hf.2.comp hg.2⟩

/-- The points of `X` that come from the image of the point of a chart in `X(R[1/r])` form the
image in `X` of the basic open subfunctor `D(r)` of the locus, which is corepresented by `R`. -/
private lemma ofElement_map_away (r : c.R) :
    Subfunctor.ofElement (X.map (CommAlgCat.ofHom
      (IsScalarTower.toAlgHom k c.R (Localization.Away r))) c.pt) =
      (c.locusCorepresentableBy.basicOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) r).image
        c.locus.ι := by
  ext A x
  rw [mem_ofElement_map_away_iff, Subfunctor.mem_image_ι_obj_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨c.mem_locus_obj_iff.2 ⟨φ, rfl⟩, ?_⟩
    have : c.locusCorepresentableBy.homEquiv.symm
        ⟨X.map φ c.pt, c.mem_locus_obj_iff.2 ⟨φ, rfl⟩⟩ = φ :=
      c.locusCorepresentableBy.homEquiv.symm_apply_eq.2
        (Subtype.ext (c.coe_locusCorepresentableBy_homEquiv φ).symm)
    rw [CorepresentableBy.mem_basicOpen_obj_iff, this]
    simpa using hφ
  · rintro ⟨hx, hu⟩
    rw [CorepresentableBy.mem_basicOpen_obj_iff] at hu
    refine ⟨c.locusCorepresentableBy.homEquiv.symm ⟨x, hx⟩, by simpa using hu, ?_⟩
    have := c.coe_locusCorepresentableBy_homEquiv (c.locusCorepresentableBy.homEquiv.symm ⟨x, hx⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

/-- The restriction of an étale chart `(R, x, y)` to the basic open subset where `r ∈ R` is a
unit: for coordinates `z` making the localization `R[1/r]` étale over the polynomial ring in `d`
variables (for instance the images of `x`, `CategoryTheory.Functor.EtaleChart.etale_aeval_away`),
the chart on `R[1/r]` given by `z` and the image of `y`. Its locus is open because openness is
transitive (`CategoryTheory.Subfunctor.IsOpen.image_ι`). -/
noncomputable def away (r : c.R) (z : Fin d → Localization.Away r)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) : X.EtaleChart d where
  R := CommAlgCat.of k (Localization.Away r)
  coord := z
  etale_aeval := hz
  pt := X.map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k c.R (Localization.Away r))) c.pt
  injective {_} _ _ h := injective_map_away c.pt r (fun h ↦ c.injective h) h
  isOpen_ofElement := by
    rw [ofElement_map_away]
    exact c.isOpen_locus.image_ι
      (c.locusCorepresentableBy.isOpen_basicOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) r)

/-- A point lies in the locus of the restriction of a chart to `D(r)` exactly when it comes from
a map `φ : R ⟶ A` out of the algebra of the chart that sends `r` to a unit. -/
lemma mem_locus_away_obj_iff (r : c.R) (z : Fin d → Localization.Away r)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) {A : CommAlgCat.{u} k} {x : X.obj A} :
    x ∈ (c.away r z hz).locus.obj A ↔ ∃ φ : c.R ⟶ A, IsUnit (φ r) ∧ X.map φ c.pt = x := by
  unfold locus away
  exact mem_ofElement_map_away_iff c.pt r

/-- The restriction of an étale chart to the locus where all its coordinates are units, with the
images of the coordinates: a chart étale over a torus
(`CategoryTheory.Functor.EtaleChart.isUnit_awayProd_coord`). -/
noncomputable def awayProd : X.EtaleChart d :=
  c.away (∏ i, c.coord i) (fun i ↦ algebraMap c.R _ (c.coord i)) (c.etale_aeval_away _)

/-- The coordinates of `c.awayProd` are units. -/
lemma isUnit_awayProd_coord (i : Fin d) : IsUnit (c.awayProd.coord i) := by
  have : IsUnit (algebraMap c.R (Localization.Away (∏ i, c.coord i)) (c.coord i)) :=
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit _)
  -- the coordinates of `c.awayProd` are, by definition, the images of those of `c`
  exact this

/-- A point lies in the locus of `c.awayProd` exactly when it comes from a map out of the algebra
of the chart that sends every coordinate to a unit. -/
lemma mem_locus_awayProd_obj_iff {A : CommAlgCat.{u} k} {x : X.obj A} :
    x ∈ c.awayProd.locus.obj A ↔
      ∃ φ : c.R ⟶ A, (∀ i, IsUnit (φ (c.coord i))) ∧ X.map φ c.pt = x := by
  rw [awayProd, mem_locus_away_obj_iff]
  simp [map_prod]

end EtaleChart

/-- A functor `X` on commutative `k`-algebras has an *atlas of dimension `d`* if it is separated
and finitely many étale charts of dimension `d` have loci that together contain every point of `X`
with values in a field. -/
structure HasAtlas (X : CommAlgCat.{u} k ⥤ Type w) (d : ℕ) : Prop where
  /-- `X` is separated. -/
  isSeparated : X.IsSeparated (forget₂ (CommAlgCat.{u} k) CommRingCat.{u})
  /-- Finitely many charts contain all points with values in fields. -/
  exists_finite_charts : ∃ S : Set (X.EtaleChart d), S.Finite ∧
    ∀ K : CommAlgCat.{u} k, IsField K → ∀ x : X.obj K, ∃ c ∈ S, x ∈ c.locus.obj K

/-- The loci of the charts of an atlas have a Zariski-locally everything union: they are open and
contain all points with values in fields. -/
theorem HasAtlas.exists_isZariskiLocallyTop {X : CommAlgCat.{u} k ⥤ Type w} {d : ℕ}
    (h : X.HasAtlas d) : ∃ S : Set (X.EtaleChart d), S.Finite ∧
      (⨆ c ∈ S, c.locus).IsZariskiLocallyTop (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) := by
  obtain ⟨S, hS, hcov⟩ := h.exists_finite_charts
  refine ⟨S, hS, ?_⟩
  rw [iSup_subtype']
  refine Subfunctor.isZariskiLocallyTop_iSup_of_isOpen_of_isField (fun c ↦ c.val.isOpen_locus)
    fun K hK x ↦ ?_
  obtain ⟨c, hc, hx⟩ := hcov K hK x
  exact ⟨⟨c, hc⟩, hx⟩

end Functor

/-- A subfunctor `V` of a functor `X` on commutative `k`-algebras is *charting* if it is
Zariski-locally everything and `ℤ[V]` lies in every closed class of functors from commutative
`k`-algebras to abelian groups that contains `ℤ[H]`, for every functor `H` corepresented by the
algebra of an étale chart of `X` (of any dimension) whose coordinates are units, that is, of a
chart étale over a torus. -/
structure Subfunctor.IsCharting {X : CommAlgCat.{u} k ⥤ Type w} (V : Subfunctor X) : Prop where
  /-- `V` is Zariski-locally everything. -/
  isZariskiLocallyTop : V.IsZariskiLocallyTop (forget₂ (CommAlgCat.{u} k) CommRingCat.{u})
  /-- `ℤ[V]` lies in every closed class containing the free functors on the charts étale over
  tori. -/
  prop_free : ∀ (P : ObjectProperty (CommAlgCat.{u} k ⥤ AddCommGrpCat.{w})) [P.IsClosedClass],
    (∀ (n : ℕ) (c : X.EtaleChart n), (∀ i, IsUnit (c.coord i)) →
      ∀ (H : CommAlgCat.{u} k ⥤ Type w), H.CorepresentableBy c.R →
        P (H ⋙ AddCommGrpCat.free)) →
    P (V.toFunctor ⋙ AddCommGrpCat.free)

namespace Functor

variable {X : CommAlgCat.{u} k ⥤ Type w} {d : ℕ}

/-- The locus of an étale chart whose coordinates are units is charting as soon as it is
Zariski-locally everything: `ℤ` of the locus is `ℤ[h_R]` for the algebra `R` of the chart. -/
theorem EtaleChart.isCharting_locus (c : X.EtaleChart d) (hc : ∀ i, IsUnit (c.coord i))
    (h : c.locus.IsZariskiLocallyTop (forget₂ (CommAlgCat.{u} k) CommRingCat.{u})) :
    c.locus.IsCharting :=
  ⟨h, fun _ _ hP ↦ hP d c hc _ c.locusCorepresentableBy⟩

/-! ### Charts of corepresentable functors -/

namespace CorepresentableBy

variable {R : CommAlgCat.{u} k} (e : X.CorepresentableBy R)

/-- Distinct maps out of `R` carry the universal point of a functor corepresented by `R` to
distinct points. -/
private lemma etaleChart_injective {A : CommAlgCat.{u} k} :
    Function.Injective fun φ : R ⟶ A ↦ X.map φ (e.homEquiv (𝟙 R)) := by
  intro φ ψ h
  simpa [← e.homEquiv_comp] using h

/-- A functor corepresented by `R`, with coordinates `x` making `R` étale over the polynomial ring
in `d` variables, has the étale chart on `R` given by `x` and the universal point. Its locus is
the whole functor. -/
def etaleChart (x : Fin d → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    X.EtaleChart d where
  R := R
  coord := x
  etale_aeval := hx
  pt := e.homEquiv (𝟙 R)
  injective {_} _ _ h := e.etaleChart_injective h
  isOpen_ofElement := by
    rw [Subfunctor.ofElement_homEquiv_id]
    exact Subfunctor.isOpen_top

/-- The chart of a corepresentable functor on its corepresenting algebra covers the whole
functor. -/
@[simp]
lemma locus_etaleChart (x : Fin d → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    (e.etaleChart x hx).locus = ⊤ :=
  Subfunctor.ofElement_homEquiv_id e

/-- The points of a functor corepresented by `R` that come from the image of the universal point
in `X(R[1/r])` are those of the basic open subfunctor `D(r)`. -/
private lemma ofElement_map_away (r : R) :
    Subfunctor.ofElement (X.map (CommAlgCat.ofHom
      (IsScalarTower.toAlgHom k R (Localization.Away r))) (e.homEquiv (𝟙 R))) =
      e.basicOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) r := by
  ext A x
  rw [mem_ofElement_map_away_iff, mem_basicOpen_obj_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rwa [← e.homEquiv_comp, Category.id_comp, Equiv.symm_apply_apply]
  · intro hx
    refine ⟨e.homEquiv.symm x, hx, ?_⟩
    rw [← e.homEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- For `r ∈ R` and coordinates `y` making the localization `R[1/r]` étale over the polynomial
ring in `d` variables, a functor corepresented by `R` has the étale chart on `R[1/r]` given by `y`
and the image of the universal point under `R ⟶ R[1/r]`. Its locus is the basic open subfunctor
`D(r)`. -/
noncomputable def etaleChartAway (r : R) (y : Fin d → Localization.Away r)
    (hy : (MvPolynomial.aeval (R := k) y).toRingHom.Etale) : X.EtaleChart d where
  R := CommAlgCat.of k (Localization.Away r)
  coord := y
  etale_aeval := hy
  pt := X.map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r)))
    (e.homEquiv (𝟙 R))
  injective {_} _ _ h := injective_map_away _ r (fun h ↦ e.etaleChart_injective h) h
  isOpen_ofElement := by
    rw [ofElement_map_away]
    exact e.isOpen_basicOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) r

/-- The locus of the chart of a corepresentable functor on `R[1/r]` is the basic open subfunctor
`D(r)`. -/
@[simp]
lemma locus_etaleChartAway (r : R) (y : Fin d → Localization.Away r)
    (hy : (MvPolynomial.aeval (R := k) y).toRingHom.Etale) :
    (e.etaleChartAway r y hy).locus = e.basicOpen (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) r :=
  e.ofElement_map_away r

include e in
/-- A functor corepresented by `R` has an atlas of dimension `d` if elements of `R` that generate
the unit ideal have localizations étale over the polynomial ring in `d` variables: finitely many
of them generate the unit ideal, and a point with values in a field sends one of those to a unit. -/
theorem hasAtlas_of_span_eq_top {s : Set R} (hspan : Ideal.span s = ⊤)
    (y : ∀ r : s, Fin d → Localization.Away (r : R))
    (hy : ∀ r, (MvPolynomial.aeval (R := k) (y r)).toRingHom.Etale) : X.HasAtlas d where
  isSeparated := e.isSeparated
  exists_finite_charts := by
    -- finitely many elements of `s` already generate the unit ideal
    obtain ⟨t, hts, ht⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 hspan)
    let incl (r : (t : Set R)) : s := ⟨r, hts r.property⟩
    refine ⟨Set.range fun r : (t : Set R) ↦ e.etaleChartAway _ (y (incl r)) (hy (incl r)),
      Set.finite_range _, fun K hK z ↦ ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : (t : Set R), IsUnit ((e.homEquiv.symm z).hom r) := by
      by_contra! H
      have h₀ : (1 : R) ∈ RingHom.ker (e.homEquiv.symm z).hom := by
        refine Ideal.span_le.2 (fun r hr ↦ ?_) ht
        by_contra h
        obtain ⟨b, hb⟩ := hK.mul_inv_cancel h
        exact H ⟨r, hr⟩ (IsUnit.of_mul_eq_one b hb)
      have := hK.nontrivial
      simp at h₀
    exact ⟨_, ⟨r, rfl⟩, by simpa using hr⟩

include e in
/-- A functor corepresented by an algebra `R` étale over the polynomial ring in `d` variables has
an atlas of dimension `d`, formed by the chart on `R` itself. -/
theorem hasAtlas (x : Fin d → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    X.HasAtlas d where
  isSeparated := e.isSeparated
  exists_finite_charts := ⟨{e.etaleChart x hx}, Set.finite_singleton _, fun K _ z ↦
    ⟨_, rfl, by simp⟩⟩

include e in
/-- A functor corepresented by an algebra `R` étale over the polynomial ring in `d` variables
through coordinates that are units of `R` (étale over a torus) is charting in itself. -/
theorem isCharting_top (x : Fin d → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hu : ∀ i, IsUnit (x i)) : (⊤ : Subfunctor X).IsCharting := by
  have := (e.etaleChart x hx).isCharting_locus hu
    (by rw [locus_etaleChart]; exact Subfunctor.isZariskiLocallyTop_top)
  rwa [locus_etaleChart] at this

end CorepresentableBy

end Functor

end General

/-! ### Affine space and the torus -/

section Examples

variable {k : Type u} [CommRing k] {X : CommAlgCat.{u} k ⥤ Type w} {d : ℕ}

namespace Functor.CorepresentableBy

/-- A functor corepresented by the polynomial ring in `d` variables, affine `d`-space, has an
atlas of dimension `d`. -/
theorem hasAtlas_mvPolynomial (e : X.CorepresentableBy (CommAlgCat.of k (MvPolynomial (Fin d) k))) :
    X.HasAtlas d :=
  e.hasAtlas MvPolynomial.X (by
    rw [MvPolynomial.aeval_X_left]
    exact RingHom.Etale.of_bijective Function.bijective_id)

/-- The functor corepresented by the ring of Laurent polynomials `k[X₁, …, X_d][1/(X₁ ⋯ X_d)]`,
the torus of dimension `d`, is charting in itself. -/
theorem isCharting_top_away_prod_X (e : X.CorepresentableBy (CommAlgCat.of k
    (Localization.Away (∏ i, MvPolynomial.X i : MvPolynomial (Fin d) k)))) :
    (⊤ : Subfunctor X).IsCharting := by
  let p : MvPolynomial (Fin d) k := ∏ i, MvPolynomial.X i
  let L := Localization.Away p
  refine e.isCharting_top (fun i ↦ algebraMap (MvPolynomial (Fin d) k) L (MvPolynomial.X i)) ?_
    fun i ↦ ?_
  · have : MvPolynomial.aeval (R := k)
        (fun i ↦ algebraMap (MvPolynomial (Fin d) k) L (MvPolynomial.X i)) =
        IsScalarTower.toAlgHom k (MvPolynomial (Fin d) k) L :=
      MvPolynomial.algHom_ext fun i ↦ by simp
    rw [this]
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway p)
  · exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit p)

end Functor.CorepresentableBy

end Examples

end CategoryTheory
