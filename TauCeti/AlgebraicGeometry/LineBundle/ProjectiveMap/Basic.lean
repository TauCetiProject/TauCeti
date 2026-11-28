/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import Mathlib.AlgebraicGeometry.Gluing
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Morphisms to projective space defined by sections of a line bundle

A family of global sections whose nonvanishing loci cover a scheme defines a morphism to
polynomial projective space. On the nonvanishing locus of one section, the coordinates are
the ratios of the other sections to that section.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Theorem 7.1.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} (L : InvertibleSheaf X) {I : Type u}
  (s : I → Γ(L.obj, ⊤))

/-- The restriction of a global section to the locus where `s i` generates. -/
def sectionOnNonvanishing (i j : I) : Γ(L.obj, L.obj.nonvanishingLocus (s i)) :=
  L.obj.presheaf.map (homOfLE le_top).op (s j)

private theorem le_nonvanishing_sectionOnNonvanishing (i : I) :
    L.obj.nonvanishingLocus (s i) ≤
      L.obj.nonvanishingLocus (L.sectionOnNonvanishing s i i) := by
  rw [sectionOnNonvanishing, Scheme.Modules.nonvanishingLocus_map]
  exact le_inf le_rfl le_rfl

/-- The coefficient of `s j` in the basis `s i` over its nonvanishing locus. -/
def sectionRatio (i j : I) : Γ(X, L.obj.nonvanishingLocus (s i)) :=
  Classical.choose (Scheme.Modules.surjective_smul_of_le_nonvanishingLocus
    (L.le_nonvanishing_sectionOnNonvanishing s i) (L.sectionOnNonvanishing s i j))

/-- Multiplication by the coefficient recovers the restricted section. -/
theorem sectionRatio_smul (i j : I) :
    L.sectionRatio s i j • L.sectionOnNonvanishing s i i = L.sectionOnNonvanishing s i j :=
  Classical.choose_spec (Scheme.Modules.surjective_smul_of_le_nonvanishingLocus
    (L.le_nonvanishing_sectionOnNonvanishing s i) (L.sectionOnNonvanishing s i j))

/-- A section has coefficient one in its own basis. -/
@[simp]
theorem sectionRatio_self (i : I) : L.sectionRatio s i i = 1 := by
  apply Scheme.Modules.injective_smul_of_le_nonvanishingLocus
    (L.le_nonvanishing_sectionOnNonvanishing s i)
  beta_reduce
  rw [L.sectionRatio_smul, one_smul]

/-- The coefficient equation commutes with restriction. -/
theorem map_sectionRatio_smul {U : X.Opens} (i j : I)
    (hU : U ≤ L.obj.nonvanishingLocus (s i)) :
    X.presheaf.map (homOfLE hU).op (L.sectionRatio s i j) •
        L.obj.presheaf.map U.leTop.op (s i) =
      L.obj.presheaf.map U.leTop.op (s j) := by
  have h := congrArg (L.obj.presheaf.map (homOfLE hU).op) (L.sectionRatio_smul s i j)
  simpa only [sectionOnNonvanishing, Scheme.Modules.map_smul,
    ← Functor.map_comp_apply, ← op_comp, Subsingleton.elim
      (homOfLE hU ≫ homOfLE (le_top : L.obj.nonvanishingLocus (s i) ≤ ⊤)) U.leTop] using h

/-- Coordinate ratios satisfy their multiplicative cocycle equation wherever both bases exist. -/
theorem sectionRatio_mul {U : X.Opens} (i j k : I)
    (hi : U ≤ L.obj.nonvanishingLocus (s i))
    (hj : U ≤ L.obj.nonvanishingLocus (s j)) :
    X.presheaf.map (homOfLE hj).op (L.sectionRatio s j i) *
        X.presheaf.map (homOfLE hi).op (L.sectionRatio s i k) =
      X.presheaf.map (homOfLE hj).op (L.sectionRatio s j k) := by
  have hU : U ≤ L.obj.nonvanishingLocus (L.obj.presheaf.map U.leTop.op (s j)) := by
    rw [Scheme.Modules.nonvanishingLocus_map]
    exact le_inf le_rfl hj
  apply Scheme.Modules.injective_smul_of_le_nonvanishingLocus hU
  beta_reduce
  rw [mul_comm, mul_smul, L.map_sectionRatio_smul s j i hj,
    L.map_sectionRatio_smul s i k hi, L.map_sectionRatio_smul s j k hj]

/-- The basic open of a coordinate ratio is the intersection of the two nonvanishing loci. -/
theorem basicOpen_sectionRatio (i j : I) :
    X.basicOpen (L.sectionRatio s i j) =
      L.obj.nonvanishingLocus (s i) ⊓ L.obj.nonvanishingLocus (s j) := by
  have h := congrArg L.obj.nonvanishingLocus (L.sectionRatio_smul s i j)
  rw [Scheme.Modules.nonvanishingLocus_smul, sectionOnNonvanishing,
    Scheme.Modules.nonvanishingLocus_map, sectionOnNonvanishing,
    Scheme.Modules.nonvanishingLocus_map] at h
  have hle := X.basicOpen_le (L.sectionRatio s i j)
  simpa only [inf_idem, inf_eq_left.mpr hle] using h

section Morphism

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))

/-- Evaluation at the ratios in a nonvanishing chart, with coefficients pulled back from `R`. -/
def coordinateRingHom (i : I) :
    MvPolynomial I R →+* Γ((L.obj.nonvanishingLocus (s i)).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom
    ((L.obj.nonvanishingLocus (s i)).topIso.inv.hom.comp
      ((X.presheaf.map (homOfLE le_top).op).hom.comp c))
    (fun j ↦ (L.obj.nonvanishingLocus (s i)).topIso.inv (L.sectionRatio s i j))

/-- A coordinate evaluates to its section ratio. -/
@[simp]
theorem coordinateRingHom_X (i j : I) :
    L.coordinateRingHom s c i (MvPolynomial.X j) =
      (L.obj.nonvanishingLocus (s i)).topIso.inv (L.sectionRatio s i j) := by
  simp [coordinateRingHom]

/-- A constant evaluates to the restricted coefficient. -/
@[simp]
theorem coordinateRingHom_C (i : I) (r : R) :
    L.coordinateRingHom s c i (MvPolynomial.C r) =
      (L.obj.nonvanishingLocus (s i)).topIso.inv
        (X.presheaf.map (homOfLE le_top).op (c r)) := by
  simp [coordinateRingHom]

/-- The irrelevant ideal generates the unit ideal under evaluation at the section ratios,
so the coordinates have no common zero on the chart. -/
theorem map_irrelevant_coordinateRingHom (i : I) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule I R)).toIdeal.map
        (L.coordinateRingHom s c i) = ⊤ := by
  rw [MvPolynomial.irrelevant_eq_span_X, Ideal.map_span, ← Set.range_comp]
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) ?_
  simp [coordinateRingHom]

/-- The morphism to projective space on a chart is defined by its ratios. -/
def localProjectiveMap (i : I) :
    (L.obj.nonvanishingLocus (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule I R) :=
  Proj.fromOfGlobalSections _ (L.coordinateRingHom s c i)
    (L.map_irrelevant_coordinateRingHom s c i)

/-- In a nonvanishing chart the projective map factors through the normalized affine chart. -/
theorem localProjectiveMap_eq (i : I) :
    L.localProjectiveMap s c i =
      (L.obj.nonvanishingLocus (s i)).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.lift (MvPolynomial.homogeneousSubmodule I R)
            (L.coordinateRingHom s c i) (by simp [coordinateRingHom]))) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.isHomogeneous_X R i)) one_pos :=
  Proj.fromOfGlobalSections_eq_toSpecΓ_awayLift _ _ _ _ _

/-- Pullback of a fraction in the normalized chart is evaluation at the section ratios. -/
theorem localProjectiveMap_appLE_awayToSection (i : I)
    (h : ⊤ ≤ L.localProjectiveMap s c i ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i))
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I R)
      (MvPolynomial.X i)) :
    (L.localProjectiveMap s c i).appLE
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i)) ⊤ h
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i) a) =
      HomogeneousLocalization.Away.lift (MvPolynomial.homogeneousSubmodule I R)
        (L.coordinateRingHom s c i) (by simp [coordinateRingHom]) a := by
  let e := (L.localProjectiveMap_eq s c i).trans (Category.assoc _ _ _).symm
  rw [Scheme.Hom.congr_appLE _ e _ _ h (e ▸ h),
    Proj.comp_awayι_appLE_awayToSection]
  let φ := CommRingCat.ofHom (HomogeneousLocalization.Away.lift
    (MvPolynomial.homogeneousSubmodule I R) (L.coordinateRingHom s c i)
      (f := MvPolynomial.X i) (by simp [coordinateRingHom]))
  have hφ : (Scheme.ΓSpecIso _).inv ≫
      ((L.obj.nonvanishingLocus (s i)).toScheme.toSpecΓ ≫ Spec.map φ).appTop = φ := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congrArg (fun f : CommRingCat.of
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I R)
        (MvPolynomial.X i)) ⟶ Γ((L.obj.nonvanishingLocus (s i)).toScheme, ⊤) ↦ f a) hφ

/-- Restricting a chart's coordinate homomorphism evaluates at the restricted section ratios. -/
theorem coordinateRingHom_restrict {U : X.Opens} (i : I)
    (hU : U ≤ L.obj.nonvanishingLocus (s i)) :
    (X.homOfLE hU).appTop.hom.comp (L.coordinateRingHom s c i) =
      MvPolynomial.eval₂Hom
        (U.topIso.inv.hom.comp ((X.presheaf.map U.leTop.op).hom.comp c))
        (fun k ↦ U.topIso.inv (X.presheaf.map (homOfLE hU).op (L.sectionRatio s i k))) := by
  ext k
  · simp only [RingHom.comp_apply, coordinateRingHom, MvPolynomial.eval₂Hom_C]
    rw [Scheme.homOfLE_appTop_topIso_inv]
    simp only [← Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim
        (homOfLE hU ≫ homOfLE (le_top : L.obj.nonvanishingLocus (s i) ≤ ⊤)) U.leTop]
  · simp only [RingHom.comp_apply, coordinateRingHom, MvPolynomial.eval₂Hom_X']
    exact Scheme.homOfLE_appTop_topIso_inv _ _

/-- Projective maps defined in two nonvanishing charts agree on their overlap. -/
theorem localProjectiveMap_compat (i j : I) :
    X.homOfLE (inf_le_left : L.obj.nonvanishingLocus (s i) ⊓
        L.obj.nonvanishingLocus (s j) ≤ L.obj.nonvanishingLocus (s i)) ≫
        L.localProjectiveMap s c i =
      X.homOfLE (inf_le_right : L.obj.nonvanishingLocus (s i) ⊓
        L.obj.nonvanishingLocus (s j) ≤ L.obj.nonvanishingLocus (s j)) ≫
        L.localProjectiveMap s c j := by
  let U := L.obj.nonvanishingLocus (s i) ⊓ L.obj.nonvanishingLocus (s j)
  let p : U.toScheme ⟶ (L.obj.nonvanishingLocus (s i)).toScheme := X.homOfLE inf_le_left
  let q : U.toScheme ⟶ (L.obj.nonvanishingLocus (s j)).toScheme := X.homOfLE inf_le_right
  let a : I → Γ(U.toScheme, ⊤) := fun k ↦
    U.topIso.inv (X.presheaf.map (homOfLE inf_le_left).op (L.sectionRatio s i k))
  let b : I → Γ(U.toScheme, ⊤) := fun k ↦
    U.topIso.inv (X.presheaf.map (homOfLE inf_le_right).op (L.sectionRatio s j k))
  have hratio (k : I) : b i * a k = b k := by
    dsimp only [a, b]
    rw [← map_mul, L.sectionRatio_mul s i j k inf_le_left inf_le_right]
  have hu : IsUnit (b i) := IsUnit.of_mul_eq_one (a j) (by
    rw [hratio]
    simp [b])
  let d : R →+* Γ(U.toScheme, ⊤) :=
    U.topIso.inv.hom.comp ((X.presheaf.map U.leTop.op).hom.comp c)
  have hp : p.appTop.hom.comp (L.coordinateRingHom s c i) = MvPolynomial.eval₂Hom d a :=
    L.coordinateRingHom_restrict s c i inf_le_left
  have hq : q.appTop.hom.comp (L.coordinateRingHom s c j) = MvPolynomial.eval₂Hom d b :=
    L.coordinateRingHom_restrict s c j inf_le_right
  rw [localProjectiveMap, localProjectiveMap,
    Proj.fromOfGlobalSections_naturality, Proj.fromOfGlobalSections_naturality]
  have heval (n : ℕ) (f : MvPolynomial I R)
      (hf : f ∈ MvPolynomial.homogeneousSubmodule I R n) :
      MvPolynomial.eval₂Hom d b f = hu.unit ^ n * MvPolynomial.eval₂Hom d a f := by
    have hb : b = fun k ↦ (hu.unit : Γ(U.toScheme, ⊤)) * a k := by
      funext k
      rw [IsUnit.unit_spec]
      exact (hratio k).symm
    calc
      MvPolynomial.eval₂Hom d b f =
          MvPolynomial.eval₂Hom d (fun k ↦ (hu.unit : Γ(U.toScheme, ⊤)) * a k) f :=
        congrArg (fun v ↦ MvPolynomial.eval₂Hom d v f) hb
      _ = _ := (show f.IsHomogeneous n from hf).eval₂_const_mul d a _
  symm
  exact TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling
    (MvPolynomial.homogeneousSubmodule I R) _ _ hu.unit
    (fun n f hf ↦ by rw [hp, hq]; exact heval n f hf) _

variable (hcover : ⨆ i, L.obj.nonvanishingLocus (s i) = ⊤)

/-- A family of sections generating a line bundle defines a morphism to projective space. -/
def projectiveMap : X ⟶ Proj (MvPolynomial.homogeneousSubmodule I R) :=
  (X.openCoverOfIsOpenCover _ (IsOpenCover.mk hcover)).glueMorphisms
    (L.localProjectiveMap s c) (by
      -- The cover's overlap maps are the two pullback projections.
      change ∀ i j : I, Limits.pullback.fst (L.obj.nonvanishingLocus (s i)).ι
          (L.obj.nonvanishingLocus (s j)).ι ≫ L.localProjectiveMap s c i =
        Limits.pullback.snd (L.obj.nonvanishingLocus (s i)).ι
          (L.obj.nonvanishingLocus (s j)).ι ≫ L.localProjectiveMap s c j
      intro i j
      rw [← cancel_epi (isPullback_opens_inf _ _).isoPullback.hom,
        IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
      exact L.localProjectiveMap_compat s c i j)

/-- The morphism to projective space restricts to the map defined by ratios in each chart. -/
@[reassoc (attr := simp)]
theorem ι_projectiveMap (i : I) :
    (L.obj.nonvanishingLocus (s i)).ι ≫ L.projectiveMap s c hcover =
      L.localProjectiveMap s c i :=
  Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover _ (IsOpenCover.mk hcover)) _ _ i

/-- The inverse image of a coordinate open is the nonvanishing locus of that section. -/
@[simp]
theorem projectiveMap_preimage_basicOpen (j : I) :
    L.projectiveMap s c hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X j) =
      L.obj.nonvanishingLocus (s j) := by
  have hlocal (i : I) : L.obj.nonvanishingLocus (s i) ⊓
        (L.projectiveMap s c hcover ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X j)) =
      L.obj.nonvanishingLocus (s i) ⊓ L.obj.nonvanishingLocus (s j) := by
    rw [← Scheme.Opens.opensRange_ι (L.obj.nonvanishingLocus (s i)),
      ← Scheme.Hom.image_preimage_eq_opensRange_inf,
      ← Scheme.Hom.comp_preimage, L.ι_projectiveMap, localProjectiveMap,
      Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R j))]
    simp only [coordinateRingHom, MvPolynomial.eval₂Hom_X']
    rw [Scheme.Opens.ι_image_basicOpen_topIso_inv, L.basicOpen_sectionRatio]
    rw [Scheme.Opens.opensRange_ι]
  ext x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top x))
  have h := congrArg (fun U : X.Opens ↦ x ∈ U) (hlocal i)
  -- Express the extensionality goal in open-set membership before cancelling the chart.
  change x ∈ (L.projectiveMap s c hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X j)) ↔
    x ∈ L.obj.nonvanishingLocus (s j)
  simpa only [Opens.mem_inf, hi, true_and] using Iff.of_eq h

/-- On each nonvanishing locus, pullback evaluates a localized projective coordinate at
the ratios defining the map. -/
theorem projectiveMap_appLE_awayToSection (i : I)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I R)
      (MvPolynomial.X i)) :
    (L.projectiveMap s c hcover).appLE
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i))
        (L.obj.nonvanishingLocus (s i)) (L.projectiveMap_preimage_basicOpen s c hcover i).ge
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i) a) =
      (L.obj.nonvanishingLocus (s i)).topIso.hom
        (HomogeneousLocalization.Away.lift (MvPolynomial.homogeneousSubmodule I R)
          (L.coordinateRingHom s c i) (by simp [coordinateRingHom]) a) := by
  let U := L.obj.nonvanishingLocus (s i)
  have hU : ⊤ ≤ U.ι ⁻¹ᵁ U := by simp
  have hcomp := Scheme.Hom.appLE_comp_appLE U.ι (L.projectiveMap s c hcover)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i))
    U ⊤ (L.projectiveMap_preimage_basicOpen s c hcover i).ge hU
  have hι : U.ι.appLE U ⊤ hU = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [hι] at hcomp
  apply (ConcreteCategory.bijective_of_isIso U.topIso.inv).injective
  rw [Iso.hom_inv_id_apply]
  -- The affine chart comparison identifies ambient sections with sections on the open subscheme.
  change ((L.projectiveMap s c hcover).appLE _ U _ ≫ U.topIso.inv)
      (Proj.awayToSection _ _ a) = _
  have hlocal : ⊤ ≤ L.localProjectiveMap s c i ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i) := by
    rw [← L.ι_projectiveMap s c hcover i, Scheme.Hom.comp_preimage,
      L.projectiveMap_preimage_basicOpen]
    simp
  rw [hcomp, Scheme.Hom.congr_appLE _ (L.ι_projectiveMap s c hcover i) _ _ _ hlocal,
    L.localProjectiveMap_appLE_awayToSection]

/-- Pulling back the ratio `Xⱼ / Xᵢ` recovers the ratio of the corresponding sections. -/
@[simp]
theorem projectiveMap_appLE_awayXRatio (i j : I) :
    (L.projectiveMap s c hcover).appLE
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i))
        (L.obj.nonvanishingLocus (s i)) (L.projectiveMap_preimage_basicOpen s c hcover i).ge
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i)
          (TauCeti.MvPolynomial.awayXRatio i j)) = L.sectionRatio s i j := by
  rw [L.projectiveMap_appLE_awayToSection, TauCeti.MvPolynomial.awayXRatio_def,
    HomogeneousLocalization.Away.lift_mk]
  have hunit : (by simp [coordinateRingHom] : IsUnit
      (L.coordinateRingHom s c i (MvPolynomial.X i))).unit = 1 := by
    apply Units.ext
    simp [coordinateRingHom]
  rw [hunit]
  simp only [one_pow, inv_one, Units.val_one, mul_one,
    coordinateRingHom, MvPolynomial.eval₂Hom_X', Iso.inv_hom_id_apply]

/-- A pulled back homogeneous coordinate ratio converts its denominator section into its
numerator section. -/
theorem projectiveMap_app_awayToSection_smul (i j : I) :
    (L.projectiveMap s c hcover).app
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i))
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i)
          (TauCeti.MvPolynomial.awayXRatio i j)) •
        L.obj.presheaf.map (homOfLE (le_top :
          L.projectiveMap s c hcover ⁻¹ᵁ Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i) ≤ ⊤)).op (s i) =
      L.obj.presheaf.map (homOfLE (le_top :
        L.projectiveMap s c hcover ⁻¹ᵁ Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i) ≤ ⊤)).op (s j) := by
  let e := L.projectiveMap_preimage_basicOpen s c hcover i
  apply (ConcreteCategory.bijective_of_isIso (L.obj.presheaf.map (eqToHom e.symm).op)).injective
  rw [Scheme.Modules.map_smul]
  have hscalar := L.projectiveMap_appLE_awayXRatio s c hcover i j
  -- Restriction along the equality of opens is the map used by `appLE`.
  change X.presheaf.map (eqToHom e.symm).op
      ((L.projectiveMap s c hcover).app _ (Proj.awayToSection _ _
        (TauCeti.MvPolynomial.awayXRatio i j))) = _ at hscalar
  rw [hscalar]
  simpa only [sectionOnNonvanishing, ← Functor.map_comp_apply, ← op_comp, Subsingleton.elim
      (eqToHom e.symm ≫ homOfLE le_top)
      (homOfLE (le_top : L.obj.nonvanishingLocus (s i) ≤ ⊤))] using
    L.sectionRatio_smul s i j

/-- The projective map has the supplied coefficient morphism as its structure morphism. -/
@[reassoc (attr := simp)]
theorem projectiveMap_toSpecCoeff :
    L.projectiveMap s c hcover ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule I R) =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c) := by
  refine (X.openCoverOfIsOpenCover _ (IsOpenCover.mk hcover)).hom_ext _ _ ?_
  -- The cover inclusions are the inclusions of the nonvanishing loci.
  change ∀ i : I, (L.obj.nonvanishingLocus (s i)).ι ≫ _ =
    (L.obj.nonvanishingLocus (s i)).ι ≫ _
  intro i
  rw [L.ι_projectiveMap_assoc, localProjectiveMap, Proj.fromOfGlobalSections_toSpecCoeff,
    Scheme.toSpecΓ_naturality_assoc]
  simp only [← Spec.map_comp, coordinateRingHom, MvPolynomial.algebraMap_eq]
  congr 2
  ext r
  simp only [RingHom.comp_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    MvPolynomial.eval₂Hom_C]
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  -- Identify chart sections with ambient sections before composing their restrictions.
  change X.presheaf.map _ (X.presheaf.map _ (c r)) = X.presheaf.map _ (c r)
  calc
    _ = X.presheaf.map (_ ≫ _) (c r) := (Functor.map_comp_apply _ _ _ (c r)).symm
    _ = _ := congrArg (fun f : _ ⟶ _ ↦ X.presheaf.map f (c r))
      (Subsingleton.elim _ _)

end Morphism

end TauCeti.AlgebraicGeometry.InvertibleSheaf
