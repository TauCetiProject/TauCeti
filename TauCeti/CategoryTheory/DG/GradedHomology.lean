/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.Functor.Basic

/-!
# Graded cohomology composition in a differential graded category

For objects `X`, `Y`, `Z` of a differential graded category `C` over a commutative ring `R`, the
graded Leibniz rule ensures that homogeneous DG composition sends cocycles of degrees `p` and `q`
to cocycles of degree `p + q` and descends to canonical cohomology `(dgHomComplex R X Y).homology p`
as an associative, unital bilinear map `TauCeti.dgHomologyComp` extending `TauCeti.dgHomotopyComp`
and preserved by enriched DG functors (`CategoryTheory.EnrichedFunctor.homologyMap_dgHomologyComp`).

## References

* B. Keller, *Deriving DG categories*, Section 1.2.
-/

public section
noncomputable section

open CategoryTheory HomologicalComplex

namespace TauCeti

universe v u u'

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

private def dgGradedHomologyIso (n : ℤ) (X Y : C) :
    (dgHomComplex R X Y).homology n ≅
      ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.H :=
  (dgHomComplex R X Y).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatHomologyIso

/-- The linear quotient map from degree-`n` cocycles to canonical degree-`n` cohomology. -/
def dgHomologyClassLinearMap (n : ℤ) (X Y : C) :
    LinearMap.ker (dgDifferential R (X := X) (Y := Y) n) →ₗ[R] (dgHomComplex R X Y).homology n :=
  (dgGradedHomologyIso R n X Y).inv.hom.comp
    ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.π.hom

/-- The canonical degree-`n` cohomology class of a closed morphism `f : DGHom R n X Y`. -/
def dgHomologyClass {n : ℤ} {X Y : C} (f : DGHom R n X Y) (hf : dgDifferential R n f = 0) :
    (dgHomComplex R X Y).homology n :=
  dgHomologyClassLinearMap R n X Y ⟨f, hf⟩

private theorem dgHomologyClass_hom {n : ℤ} {X Y : C}
    (f : DGHom R n X Y) (hf : dgDifferential R n f = 0) :
    (dgGradedHomologyIso R n X Y).hom.hom (dgHomologyClass R f hf) =
      Submodule.Quotient.mk (p := LinearMap.range
        ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatToCycles) ⟨f, hf⟩ := by
  let e := dgGradedHomologyIso R n X Y
  change e.hom (e.inv _) = _; exact e.inv_hom_id_apply _

/-- Zero represents the zero cohomology class in every degree. -/
@[simp]
theorem dgHomologyClass_zero (n : ℤ) (X Y : C) :
    dgHomologyClass R (0 : DGHom R n X Y) (map_zero _) = 0 :=
  (dgHomologyClassLinearMap R n X Y).map_zero

/-- `TauCeti.dgHomologyClass` preserves addition of cocycles. -/
@[simp]
theorem dgHomologyClass_add {n : ℤ} {X Y : C} (f g : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) :
    dgHomologyClass R (f + g) (by rw [map_add, hf, hg, add_zero]) =
      dgHomologyClass R f hf + dgHomologyClass R g hg :=
  (dgHomologyClassLinearMap R n X Y).map_add ⟨f, hf⟩ ⟨g, hg⟩

/-- `TauCeti.dgHomologyClass` preserves scalar multiplication of cocycles. -/
@[simp]
theorem dgHomologyClass_smul {n : ℤ} {X Y : C} (r : R) (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R (r • f) (by rw [map_smul, hf, smul_zero]) = r • dgHomologyClass R f hf :=
  (dgHomologyClassLinearMap R n X Y).map_smul r ⟨f, hf⟩

/-- `TauCeti.dgHomologyClass` preserves negation of cocycles. -/
@[simp]
theorem dgHomologyClass_neg {n : ℤ} {X Y : C} (f : DGHom R n X Y) (hf : dgDifferential R n f = 0) :
    dgHomologyClass R (-f) (by rw [map_neg, hf, neg_zero]) = -dgHomologyClass R f hf :=
  (dgHomologyClassLinearMap R n X Y).map_neg ⟨f, hf⟩

/-- Every degree-`n` cohomology class has a closed degree-`n` representative. -/
theorem exists_dgHomologyClass_eq {n : ℤ} {X Y : C} (c : (dgHomComplex R X Y).homology n) :
    ∃ (f : DGHom R n X Y) (hf : dgDifferential R n f = 0), dgHomologyClass R f hf = c := by
  let e := dgGradedHomologyIso R n X Y
  obtain ⟨f, hf⟩ : ∃ f, Submodule.Quotient.mk f = e.hom.hom c := by
    induction e.hom.hom c using Submodule.Quotient.induction_on with | H f => exact ⟨f, rfl⟩
  refine ⟨f.1, f.2, e.toLinearEquiv.injective ?_⟩
  change e.hom.hom (dgHomologyClass R f.1 f.2) = e.hom.hom c
  exact (dgHomologyClass_hom R f.1 f.2).trans hf

/-- Two closed degree-`n` morphisms represent the same cohomology class iff their difference is a
coboundary. -/
theorem dgHomologyClass_eq_iff {n : ℤ} {X Y : C} {f g : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) :
    dgHomologyClass R f hf = dgHomologyClass R g hg ↔
      ∃ h : DGHom R (n - 1) X Y, ((dgHomComplex R X Y).d (n - 1) n).hom h = f - g := by
  let e := dgGradedHomologyIso R n X Y
  let S := (dgHomComplex R X Y).sc' (n - 1) n (n + 1)
  refine ⟨fun heq ↦ ?_, fun ⟨h, hh⟩ ↦ e.toLinearEquiv.injective ?_⟩
  · have h' := congrArg e.hom.hom heq
    rw [dgHomologyClass_hom, dgHomologyClass_hom] at h'
    obtain ⟨h, hh⟩ := (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mp h'
    exact ⟨h, congrArg Subtype.val hh⟩
  · change e.hom.hom (dgHomologyClass R f hf) = e.hom.hom (dgHomologyClass R g hg)
    rw [dgHomologyClass_hom, dgHomologyClass_hom]
    exact (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mpr ⟨h, Subtype.ext hh⟩

/-- A closed degree-`n` morphism represents zero in cohomology iff it is a coboundary. -/
theorem dgHomologyClass_eq_zero_iff {n : ℤ} {X Y : C} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R f hf = 0 ↔
      ∃ h : DGHom R (n - 1) X Y, ((dgHomComplex R X Y).d (n - 1) n).hom h = f := by
  rw [← dgHomologyClass_zero R n X Y, dgHomologyClass_eq_iff, sub_zero]

/-- Exact coboundaries `dgDifferential R m h` vanish in degree-`m + 1` cohomology. -/
@[simp]
theorem dgHomologyClass_dgDifferential {m : ℤ} {X Y : C} (h : DGHom R m X Y) :
    dgHomologyClass R (dgDifferential R m h) (dgDifferential_dgDifferential R h) = 0 := by
  rw [dgHomologyClass_eq_zero_iff]
  exact ⟨castDeg R (by omega : m = m + 1 - 1) h, by
    simpa only [castDeg_self] using d_castDeg R (by omega : m = m + 1 - 1) rfl h⟩

private theorem exists_iCycles_and_dgHomologyClass {n : ℤ} {X Y : C} (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    ∃ x : (dgHomComplex R X Y).cycles n, ((dgHomComplex R X Y).iCycles n).hom x = f ∧
      dgHomologyClass R f hf = ((dgHomComplex R X Y).homologyπ n).hom x := by
  let K := dgHomComplex R X Y; let S := K.sc' (n - 1) n (n + 1)
  let e := K.cyclesIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let eH := K.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let c : S.moduleCatLeftHomologyData.K := ⟨f, hf⟩
  refine ⟨(S.moduleCatCyclesIso.inv ≫ e.inv).hom c, ?_, ?_⟩
  · have h : (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.iCycles n = S.moduleCatLeftHomologyData.i := by
      rw [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
      exact S.moduleCatCyclesIso_inv_iCycles
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c
  · have h : S.moduleCatLeftHomologyData.π ≫ (S.moduleCatHomologyIso.inv ≫ eH.inv) =
        (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.homologyπ n := by
      rw [← Category.assoc, ← S.moduleCatCyclesIso_inv_π, Category.assoc, Category.assoc,
        HomologicalComplex.π_homologyIsoSc'_inv]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c

/-- `TauCeti.dgHomologyClass` agrees with `HomologicalComplex.homologyπ` on any lifting cycle. -/
theorem dgHomologyClass_eq_homologyπ {n : ℤ} {X Y : C} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (x : (dgHomComplex R X Y).cycles n)
    (hx : ((dgHomComplex R X Y).iCycles n).hom x = f) :
    dgHomologyClass R f hf = ((dgHomComplex R X Y).homologyπ n).hom x := by
  obtain ⟨y, hy, hclass⟩ := exists_iCycles_and_dgHomologyClass R f hf
  rw [hclass, (ModuleCat.mono_iff_injective ((dgHomComplex R X Y).iCycles n)).1 inferInstance
    (hy.trans hx.symm)]

/-- In degree zero, `TauCeti.dgHomologyClass` agrees with `TauCeti.dgHomotopyClass`. -/
theorem dgHomologyClass_zero_eq_dgHomotopyClass {X Y : C} (f : DGHom R 0 X Y)
    (hf : dgDifferential R 0 f = 0) :
    dgHomologyClass R f hf = dgHomotopyClass R f ((mem_dgCycles R).mpr hf) := by
  obtain ⟨x, hx, hclass⟩ := exists_iCycles_and_dgHomologyClass R f hf
  exact hclass.trans (dgHomotopyClass_eq_homologyπ R ((mem_dgCycles R).mpr hf) x hx).symm

/-- Every cycle `x` of `dgHomComplex R X Y` has `dgDifferential` zero on `iCycles x`. -/
theorem dgDifferential_iCycles {n : ℤ} {X Y : C} (x : (dgHomComplex R X Y).cycles n) :
    dgDifferential R n (((dgHomComplex R X Y).iCycles n).hom x) = 0 :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((dgHomComplex R X Y).iCycles_d n (n + 1))) x

/-- `HomologicalComplex.homologyπ` evaluates a cycle `x` to `dgHomologyClass` of `iCycles x`. -/
@[simp]
theorem homologyπ_eq_dgHomologyClass {n : ℤ} {X Y : C} (x : (dgHomComplex R X Y).cycles n) :
    ((dgHomComplex R X Y).homologyπ n).hom x =
      dgHomologyClass R (((dgHomComplex R X Y).iCycles n).hom x) (dgDifferential_iCycles R x) :=
  (dgHomologyClass_eq_homologyπ R (dgDifferential_iCycles R x) x rfl).symm

/-- A chain map between Hom complexes preserves closedness of homogeneous morphisms. -/
theorem map_dgDifferential_eq_zero {C' : Type u'} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {n : ℤ} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) : dgDifferential R n ((φ.f n).hom f) = 0 := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, dgDifferential, hf, map_zero] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.comm n (n + 1))) f

/-- `HomologicalComplex.homologyMap` acts on `dgHomologyClass` through representatives. -/
@[simp]
theorem homologyMap_dgHomologyClass {C' : Type u'} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {n : ℤ} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) :
    (HomologicalComplex.homologyMap φ n).hom (dgHomologyClass R f hf) =
      dgHomologyClass R ((φ.f n).hom f) (map_dgDifferential_eq_zero R φ hf) := by
  obtain ⟨x, hx, hclass⟩ := exists_iCycles_and_dgHomologyClass R f hf
  rw [hclass, dgHomologyClass_eq_homologyπ R _ ((HomologicalComplex.cyclesMap φ n).hom x)]
  · exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.homologyπ_naturality φ n)) x
  · rw [← hx]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (HomologicalComplex.cyclesMap_i φ n)) x

/-! ### Graded cohomology composition and identity -/

/-- The canonical degree-zero cohomology class of the DG identity of `X`. -/
def dgHomologyId (X : C) : (dgHomComplex R X X).homology 0 :=
  dgHomologyClass R (dgId R X) (dgDifferential_dgId R X)

/-- `TauCeti.dgHomologyId` is the degree-zero class of `dgId R X`. -/
theorem dgHomologyId_def (X : C) :
    dgHomologyId R X = dgHomologyClass R (dgId R X) (dgDifferential_dgId R X) := (rfl)

/-- Composing closed morphisms of degrees `p` and `q` gives a closed morphism of degree `p + q`. -/
theorem dgDifferential_dgComp_eq_zero {X Y Z : C} {p q n : ℤ} {f : DGHom R p X Y}
    {g : DGHom R q Y Z} (hf : dgDifferential R p f = 0) (hg : dgDifferential R q g = 0)
    (h : p + q = n) : dgDifferential R n (dgComp R f g h) = 0 := by
  rw [dgDifferential_dgComp, hf, hg, zero_dgComp, dgComp_zero, smul_zero, add_zero]

private def dgConcreteGradedComp (X Y Z : C) {p q n : ℤ} (h : p + q = n) :
    ((dgHomComplex R X Y).sc' (p - 1) p (p + 1)).moduleCatLeftHomologyData.H →ₗ[R]
      ((dgHomComplex R Y Z).sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData.H →ₗ[R]
        ((dgHomComplex R X Z).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.H :=
  let SXY := (dgHomComplex R X Y).sc' (p - 1) p (p + 1)
  let SYZ := (dgHomComplex R Y Z).sc' (q - 1) q (q + 1)
  let SXZ := (dgHomComplex R X Z).sc' (n - 1) n (n + 1)
  (LinearMap.mk₂ R
    (fun f g ↦ Submodule.Quotient.mk (p := LinearMap.range SXZ.moduleCatToCycles)
      ⟨dgComp R f.1 g.1 h, dgDifferential_dgComp_eq_zero R f.2 g.2 h⟩)
    (fun f f' g ↦ by
      rw [← Submodule.Quotient.mk_add]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (add_dgComp R f.1 f'.1 g.1 h)))
    (fun r f g ↦ by
      rw [← Submodule.Quotient.mk_smul]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (smul_dgComp R r f.1 g.1 h)))
    (fun f g g' ↦ by
      rw [← Submodule.Quotient.mk_add]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (dgComp_add R f.1 g.1 g'.1 h)))
    (fun r f g ↦ by
      rw [← Submodule.Quotient.mk_smul]
      exact congrArg Submodule.Quotient.mk (Subtype.ext (dgComp_smul R r f.1 g.1 h)))).liftQ₂
    (LinearMap.range SXY.moduleCatToCycles) (LinearMap.range SYZ.moduleCatToCycles)
    (by
      rintro _ ⟨f₀, rfl⟩; ext g
      have hk : ((dgHomComplex R X Z).d (n - 1) n).hom (dgComp R f₀ g.1 (by omega)) =
          dgComp R (((dgHomComplex R X Y).d (p - 1) p).hom f₀) g.1 h := by
        have hg0 : dgDifferential R q g.1 = 0 := g.2
        rw [dgHomComplex_d_dgComp R (by omega : p - 1 + 1 = p) rfl (by omega : n - 1 + 1 = n)
          f₀ g.1 (by omega), hg0, dgComp_zero, smul_zero, add_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, Subtype.ext hk⟩)
    (by
      rintro _ ⟨g₀, rfl⟩; ext f
      have hk : ((dgHomComplex R X Z).d (n - 1) n).hom
          (p.negOnePow • dgComp R f.1 g₀ (by omega)) =
          dgComp R f.1 (((dgHomComplex R Y Z).d (q - 1) q).hom g₀) h := by
        have hf0 : dgDifferential R p f.1 = 0 := f.2
        rw [Units.smul_def, map_zsmul, ← Units.smul_def,
          dgHomComplex_d_dgComp R rfl (by omega : q - 1 + 1 = q) (by omega : n - 1 + 1 = n)
            f.1 g₀ (by omega), hf0, zero_dgComp, zero_add, smul_smul, Int.units_mul_self, one_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, Subtype.ext hk⟩)

/-- Bilinear graded composition on canonical cohomology of DG Hom complexes, in Mathlib's enriched
factor order (`dgHomologyComp R X Y Z h [f] [g] = [dgComp R f g h]`). -/
def dgHomologyComp (X Y Z : C) {p q n : ℤ} (h : p + q = n) :
    (dgHomComplex R X Y).homology p →ₗ[R]
      (dgHomComplex R Y Z).homology q →ₗ[R] (dgHomComplex R X Z).homology n :=
  ((dgConcreteGradedComp R X Y Z h).compl₁₂
    (dgGradedHomologyIso R p X Y).hom.hom (dgGradedHomologyIso R q Y Z).hom.hom).compr₂
    (dgGradedHomologyIso R n X Z).inv.hom

/-- `TauCeti.dgHomologyComp` evaluates on cohomology classes to the class of their DG composite. -/
@[simp]
theorem dgHomologyComp_dgHomologyClass {X Y Z : C} {p q n : ℤ} (h : p + q = n)
    (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (hf : dgDifferential R p f = 0) (hg : dgDifferential R q g = 0) :
    dgHomologyComp R X Y Z h (dgHomologyClass R f hf) (dgHomologyClass R g hg) =
      dgHomologyClass R (dgComp R f g h) (dgDifferential_dgComp_eq_zero R hf hg h) := by
  let eXZ := dgGradedHomologyIso R n X Z
  apply eXZ.toLinearEquiv.injective
  dsimp only [dgHomologyComp, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  change eXZ.hom.hom (eXZ.inv.hom _) = eXZ.hom.hom _
  rw [show eXZ.hom.hom (eXZ.inv.hom _) = _ from eXZ.inv_hom_id_apply _,
    dgHomologyClass_hom, dgHomologyClass_hom, dgHomologyClass_hom]
  rfl

/-- Graded cohomology composition is associative. -/
theorem dgHomologyComp_assoc {W X Y Z : C} {p q r pq qr n : ℤ}
    (hpq : p + q = pq) (hqr : q + r = qr) (hn₁ : pq + r = n) (hn₂ : p + qr = n)
    (a : (dgHomComplex R W X).homology p) (b : (dgHomComplex R X Y).homology q)
    (c : (dgHomComplex R Y Z).homology r) :
    dgHomologyComp R W Y Z hn₁ (dgHomologyComp R W X Y hpq a b) c =
      dgHomologyComp R W X Z hn₂ a (dgHomologyComp R X Y Z hqr b c) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomologyClass_eq R b
  obtain ⟨k, hk, rfl⟩ := exists_dgHomologyClass_eq R c
  simp only [dgHomologyComp_dgHomologyClass]
  exact congrArg (dgHomologyClassLinearMap R n W Z)
    (Subtype.ext (dgComp_assoc R f g k hpq hqr (by omega)))

/-- Left composition with `dgHomologyId` is the identity on graded cohomology in every degree. -/
@[simp]
theorem dgHomologyId_dgHomologyComp {X Y : C} {n : ℤ} (a : (dgHomComplex R X Y).homology n) :
    dgHomologyComp R X X Y (zero_add n) (dgHomologyId R X) a = a := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  rw [dgHomologyId_def, dgHomologyComp_dgHomologyClass]
  exact congrArg (dgHomologyClassLinearMap R n X Y) (Subtype.ext (dgId_dgComp R f))

/-- Right composition with `dgHomologyId` is the identity on graded cohomology in every degree. -/
@[simp]
theorem dgHomologyComp_dgHomologyId {X Y : C} {n : ℤ} (a : (dgHomComplex R X Y).homology n) :
    dgHomologyComp R X Y Y (add_zero n) a (dgHomologyId R Y) = a := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  rw [dgHomologyId_def, dgHomologyComp_dgHomologyClass]
  exact congrArg (dgHomologyClassLinearMap R n X Y) (Subtype.ext (dgComp_dgId R f))

/-- In degree zero, `TauCeti.dgHomologyComp` agrees with `TauCeti.dgHomotopyComp`. -/
theorem dgHomologyComp_zero_eq_dgHomotopyComp (X Y Z : C) :
    dgHomologyComp R X Y Z (zero_add 0) = dgHomotopyComp R X Y Z := by
  ext a b
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomologyClass_eq R b
  rw [dgHomologyComp_dgHomologyClass, dgHomologyClass_zero_eq_dgHomotopyClass,
    dgHomologyClass_zero_eq_dgHomotopyClass, dgHomologyClass_zero_eq_dgHomotopyClass,
    dgHomotopyComp_dgHomotopyClass, dgHomotopyClass_eq_iff, dgCompZero_def, sub_self]
  exact (dgBoundaries R X Z).zero_mem

end TauCeti

namespace CategoryTheory.EnrichedFunctor

open TauCeti HomologicalComplex

universe v u u'

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u'} [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- Every DG functor preserves `TauCeti.dgHomologyId`. -/
@[simp]
theorem homologyMap_dgHomologyId (X : C) :
    (homologyMap (F.map X X) 0).hom (dgHomologyId R X) = dgHomologyId R (F.obj X) := by
  rw [dgHomologyId_def, dgHomologyId_def, homologyMap_dgHomologyClass]
  exact congrArg (dgHomologyClassLinearMap R 0 (F.obj X) (F.obj X))
    (Subtype.ext ((F.dgMap_apply (dgId R X)).symm.trans (F.dgMap_dgId X)))

/-- Every DG functor commutes with `TauCeti.dgHomologyComp` in all degrees. -/
theorem homologyMap_dgHomologyComp {X Y Z : C} {p q n : ℤ} (h : p + q = n)
    (a : (dgHomComplex R X Y).homology p) (b : (dgHomComplex R Y Z).homology q) :
    (homologyMap (F.map X Z) n).hom (dgHomologyComp R X Y Z h a b) =
      dgHomologyComp R (F.obj X) (F.obj Y) (F.obj Z) h
        ((homologyMap (F.map X Y) p).hom a) ((homologyMap (F.map Y Z) q).hom b) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomologyClass_eq R b
  simp only [dgHomologyComp_dgHomologyClass, homologyMap_dgHomologyClass]
  exact congrArg (dgHomologyClassLinearMap R n (F.obj X) (F.obj Z)) <| Subtype.ext <|
    ((F.dgMap_apply (dgComp R f g h)).symm.trans (F.dgMap_dgComp f g h)).trans
      (by rw [F.dgMap_apply, F.dgMap_apply])

end CategoryTheory.EnrichedFunctor
