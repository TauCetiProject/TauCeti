/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.CategoryTheory.DG.Basic

/-!
# Graded cohomology composition in a differential graded category

For objects `X`, `Y`, `Z` of a differential graded category `C` over a commutative ring `R`, the
graded Leibniz rule ensures that homogeneous DG composition sends cocycles of degrees `p` and `q`
to cocycles of degree `p + q` and descends to canonical cohomology `(dgHomComplex R X Y).homology p`
as an associative, unital bilinear map `TauCeti.dgHomologyComp` with unit `TauCeti.dgHomologyId`.
Degree equalities give linear equivalences `TauCeti.dgHomologyCastEquiv`, and mutually inverse
graded cohomology classes induce left and right composition equivalences
`TauCeti.dgHomologyCompLeftEquiv` and `TauCeti.dgHomologyCompRightEquiv`.

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

/-- `TauCeti.dgHomologyClassLinearMap` evaluates a cocycle subtype to `TauCeti.dgHomologyClass`. -/
@[simp] theorem dgHomologyClassLinearMap_apply (n : ℤ) (X Y : C)
    (f : LinearMap.ker (dgDifferential R (X := X) (Y := Y) n)) :
    dgHomologyClassLinearMap R n X Y f = dgHomologyClass R f.val f.property := (rfl)

/-- Equal closed degree-`n` morphisms represent the same cohomology class, regardless of the
closedness proofs. -/
theorem dgHomologyClass_congr {n : ℤ} {X Y : C} {f g : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) (h : f = g) :
    dgHomologyClass R f hf = dgHomologyClass R g hg := by
  cases h; rfl

private theorem dgHomologyClass_toLinearEquiv {n : ℤ} {X Y : C}
    (f : DGHom R n X Y) (hf : dgDifferential R n f = 0) :
    (dgGradedHomologyIso R n X Y).toLinearEquiv (dgHomologyClass R f hf) =
      Submodule.Quotient.mk (p := LinearMap.range
        ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatToCycles) ⟨f, hf⟩ := by
  rw [dgHomologyClass, dgHomologyClassLinearMap, LinearMap.comp_apply,
    ShortComplex.moduleCatLeftHomologyData_π_hom, Submodule.mkQ_apply]
  exact (dgGradedHomologyIso R n X Y).inv_hom_id_apply _

/-- Zero represents the zero cohomology class in every degree. -/
@[simp] theorem dgHomologyClass_zero (n : ℤ) (X Y : C) :
    dgHomologyClass R (0 : DGHom R n X Y) (map_zero _) = 0 :=
  (dgHomologyClassLinearMap R n X Y).map_zero

/-- `TauCeti.dgHomologyClass` preserves addition of cocycles. -/
@[simp] theorem dgHomologyClass_add {n : ℤ} {X Y : C} (f g : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) :
    dgHomologyClass R (f + g) (by rw [map_add, hf, hg, add_zero]) =
      dgHomologyClass R f hf + dgHomologyClass R g hg :=
  (dgHomologyClassLinearMap R n X Y).map_add ⟨f, hf⟩ ⟨g, hg⟩

/-- `TauCeti.dgHomologyClass` preserves scalar multiplication of cocycles. -/
@[simp] theorem dgHomologyClass_smul {n : ℤ} {X Y : C} (r : R) (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R (r • f) (by rw [map_smul, hf, smul_zero]) = r • dgHomologyClass R f hf :=
  (dgHomologyClassLinearMap R n X Y).map_smul r ⟨f, hf⟩

/-- `TauCeti.dgHomologyClass` preserves negation of cocycles. -/
@[simp] theorem dgHomologyClass_neg {n : ℤ} {X Y : C} (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R (-f) (by rw [map_neg, hf, neg_zero]) = -dgHomologyClass R f hf :=
  (dgHomologyClassLinearMap R n X Y).map_neg ⟨f, hf⟩

/-- Every degree-`n` cohomology class has a closed degree-`n` representative. -/
theorem exists_dgHomologyClass_eq {n : ℤ} {X Y : C} (c : (dgHomComplex R X Y).homology n) :
    ∃ (f : DGHom R n X Y) (hf : dgDifferential R n f = 0), dgHomologyClass R f hf = c := by
  obtain ⟨f, hf⟩ : ∃ f, Submodule.Quotient.mk f =
      (dgGradedHomologyIso R n X Y).toLinearEquiv c := by
    induction (dgGradedHomologyIso R n X Y).toLinearEquiv c using Submodule.Quotient.induction_on
    with | H f => exact ⟨f, rfl⟩
  have hf0 : dgDifferential R n f.val = 0 := f.property
  refine ⟨f.val, hf0, (dgGradedHomologyIso R n X Y).toLinearEquiv.injective ?_⟩
  rw [dgHomologyClass_toLinearEquiv, hf]

/-- Two closed degree-`n` morphisms represent the same cohomology class iff their difference is a
coboundary. -/
theorem dgHomologyClass_eq_iff {n : ℤ} {X Y : C} {f g : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) :
    dgHomologyClass R f hf = dgHomologyClass R g hg ↔
      ∃ h : DGHom R (n - 1) X Y, ((dgHomComplex R X Y).d (n - 1) n).hom h = f - g := by
  let S := (dgHomComplex R X Y).sc' (n - 1) n (n + 1)
  refine ⟨fun heq ↦ ?_, fun ⟨h, hh⟩ ↦ (dgGradedHomologyIso R n X Y).toLinearEquiv.injective ?_⟩
  · have h' := congrArg (dgGradedHomologyIso R n X Y).toLinearEquiv heq
    rw [dgHomologyClass_toLinearEquiv, dgHomologyClass_toLinearEquiv] at h'
    obtain ⟨h, hh⟩ := (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mp h'
    exact ⟨h, congrArg Subtype.val hh⟩
  · rw [dgHomologyClass_toLinearEquiv, dgHomologyClass_toLinearEquiv]
    exact (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mpr ⟨h, Subtype.ext hh⟩

/-- A closed degree-`n` morphism represents zero in cohomology iff it is a coboundary. -/
theorem dgHomologyClass_eq_zero_iff {n : ℤ} {X Y : C} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R f hf = 0 ↔
      ∃ h : DGHom R (n - 1) X Y, ((dgHomComplex R X Y).d (n - 1) n).hom h = f := by
  rw [← dgHomologyClass_zero R n X Y, dgHomologyClass_eq_iff, sub_zero]

/-- Exact coboundaries `dgDifferential R m h` vanish in degree-`m + 1` cohomology. -/
@[simp] theorem dgHomologyClass_dgDifferential {m : ℤ} {X Y : C} (h : DGHom R m X Y) :
    dgHomologyClass R (dgDifferential R m h) (dgDifferential_dgDifferential R h) = 0 := by
  rw [dgHomologyClass_eq_zero_iff]
  exact ⟨castDeg R (by omega : m = m + 1 - 1) h, by
    simpa only [castDeg_self] using d_castDeg R (by omega : m = m + 1 - 1) rfl h⟩

/-- Every closed degree-`n` morphism lifts to a cycle in `(dgHomComplex R X Y).cycles n` whose
image under `HomologicalComplex.homologyπ` is `TauCeti.dgHomologyClass`. -/
theorem exists_iCycles_and_dgHomologyClass {n : ℤ} {X Y : C} (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    ∃ x : (dgHomComplex R X Y).cycles n, ((dgHomComplex R X Y).iCycles n).hom x = f ∧
      dgHomologyClass R f hf = ((dgHomComplex R X Y).homologyπ n).hom x := by
  let K := dgHomComplex R X Y; let S := K.sc' (n - 1) n (n + 1)
  let e := K.cyclesIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let c : S.moduleCatLeftHomologyData.K := ⟨f, hf⟩
  have h₁ : (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.iCycles n = S.moduleCatLeftHomologyData.i := by
    simp [S, e]
  have h₂ : S.moduleCatLeftHomologyData.π ≫ (dgGradedHomologyIso R n X Y).inv =
      (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.homologyπ n := by
    rw [dgGradedHomologyIso, Iso.trans_inv, ← S.moduleCatCyclesIso_inv_π_assoc,
      HomologicalComplex.π_homologyIsoSc'_inv, Category.assoc]
  exact ⟨(S.moduleCatCyclesIso.inv ≫ e.inv).hom c,
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h₁) c,
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h₂) c⟩

/-- `TauCeti.dgHomologyClass` agrees with `HomologicalComplex.homologyπ` on any lifting cycle. -/
theorem dgHomologyClass_eq_homologyπ {n : ℤ} {X Y : C} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (x : (dgHomComplex R X Y).cycles n)
    (hx : ((dgHomComplex R X Y).iCycles n).hom x = f) :
    dgHomologyClass R f hf = ((dgHomComplex R X Y).homologyπ n).hom x := by
  obtain ⟨y, hy, hclass⟩ := exists_iCycles_and_dgHomologyClass R f hf
  rw [hclass, (ModuleCat.mono_iff_injective ((dgHomComplex R X Y).iCycles n)).mp inferInstance
    (hy.trans hx.symm)]

/-- Every cycle `x` of `dgHomComplex R X Y` has `dgDifferential` zero on `iCycles x`. -/
theorem dgDifferential_iCycles {n : ℤ} {X Y : C} (x : (dgHomComplex R X Y).cycles n) :
    dgDifferential R n (((dgHomComplex R X Y).iCycles n).hom x) = 0 :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((dgHomComplex R X Y).iCycles_d n (n + 1))) x

/-- `HomologicalComplex.homologyπ` evaluates a cycle `x` to `dgHomologyClass` of `iCycles x`. -/
theorem homologyπ_eq_dgHomologyClass {n : ℤ} {X Y : C}
    (x : (dgHomComplex R X Y).cycles n) :
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
@[simp] theorem homologyMap_dgHomologyClass {C' : Type u'} [DGCategory R C'] {X Y : C} {X' Y' : C'}
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
      ⟨dgComp R f.val g.val h, LinearMap.mem_ker.mpr (dgDifferential_dgComp_eq_zero R
        (LinearMap.mem_ker.mp f.property) (LinearMap.mem_ker.mp g.property) h)⟩)
    (fun f f' g ↦ by
      rw [← Submodule.Quotient.mk_add]
      exact congrArg _ (Subtype.ext (add_dgComp R f.val f'.val g.val h)))
    (fun r f g ↦ by
      rw [← Submodule.Quotient.mk_smul]
      exact congrArg _ (Subtype.ext (smul_dgComp R r f.val g.val h)))
    (fun f g g' ↦ by
      rw [← Submodule.Quotient.mk_add]
      exact congrArg _ (Subtype.ext (dgComp_add R f.val g.val g'.val h)))
    (fun r f g ↦ by
      rw [← Submodule.Quotient.mk_smul]
      exact congrArg _ (Subtype.ext (dgComp_smul R r f.val g.val h)))).liftQ₂
    (LinearMap.range SXY.moduleCatToCycles) (LinearMap.range SYZ.moduleCatToCycles)
    (by
      rintro _ ⟨f₀, rfl⟩; ext g
      have hg0 : dgDifferential R q g.val = 0 := LinearMap.mem_ker.mp g.property
      refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨dgComp R f₀ g.val (by omega), Subtype.ext ?_⟩
      simp only [LinearMap.codRestrict_apply, SXZ, SXY, shortComplexFunctor'_obj_f]
      rw [dgHomComplex_d_dgComp R (by omega : p - 1 + 1 = p) rfl (by omega : n - 1 + 1 = n)
        f₀ g.val (by omega), hg0, dgComp_zero, smul_zero, add_zero])
    (by
      rintro _ ⟨g₀, rfl⟩; ext f
      have hf0 : dgDifferential R p f.val = 0 := LinearMap.mem_ker.mp f.property
      refine (Submodule.Quotient.mk_eq_zero _).mpr
        ⟨p.negOnePow • dgComp R f.val g₀ (by omega), Subtype.ext ?_⟩
      simp only [LinearMap.codRestrict_apply, SXZ, SYZ, shortComplexFunctor'_obj_f]
      rw [Units.smul_def, map_zsmul, ← Units.smul_def,
        dgHomComplex_d_dgComp R rfl (by omega : q - 1 + 1 = q) (by omega : n - 1 + 1 = n)
          f.val g₀ (by omega), hf0, zero_dgComp, zero_add, smul_smul, Int.units_mul_self,
          one_smul])

/-- Bilinear graded composition on canonical cohomology of DG Hom complexes, in Mathlib's enriched
factor order (`dgHomologyComp R X Y Z h [f] [g] = [dgComp R f g h]`). -/
def dgHomologyComp (X Y Z : C) {p q n : ℤ} (h : p + q = n) :
    (dgHomComplex R X Y).homology p →ₗ[R]
      (dgHomComplex R Y Z).homology q →ₗ[R] (dgHomComplex R X Z).homology n :=
  ((dgConcreteGradedComp R X Y Z h).compl₁₂
    (dgGradedHomologyIso R p X Y).toLinearEquiv.toLinearMap
    (dgGradedHomologyIso R q Y Z).toLinearEquiv.toLinearMap).compr₂
    (dgGradedHomologyIso R n X Z).toLinearEquiv.symm.toLinearMap

/-- `TauCeti.dgHomologyComp` evaluates on cohomology classes to the class of their DG composite. -/
@[simp] theorem dgHomologyComp_dgHomologyClass {X Y Z : C} {p q n : ℤ} (h : p + q = n)
    (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (hf : dgDifferential R p f = 0) (hg : dgDifferential R q g = 0) :
    dgHomologyComp R X Y Z h (dgHomologyClass R f hf) (dgHomologyClass R g hg) =
      dgHomologyClass R (dgComp R f g h) (dgDifferential_dgComp_eq_zero R hf hg h) := by
  apply (dgGradedHomologyIso R n X Z).toLinearEquiv.injective
  rw [dgHomologyComp, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    dgHomologyClass_toLinearEquiv, dgHomologyClass_toLinearEquiv, dgHomologyClass_toLinearEquiv,
    dgConcreteGradedComp, LinearMap.liftQ₂_mk, LinearMap.mk₂_apply]

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
  exact dgHomologyClass_congr R _ _ (dgComp_assoc R f g k hpq hqr (by omega))

/-- Left composition with `dgHomologyId` is the identity on graded cohomology in every degree. -/
@[simp] theorem dgHomologyId_dgHomologyComp {X Y : C} {n : ℤ}
    (a : (dgHomComplex R X Y).homology n) :
    dgHomologyComp R X X Y (zero_add n) (dgHomologyId R X) a = a := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  rw [dgHomologyId_def, dgHomologyComp_dgHomologyClass]
  exact dgHomologyClass_congr R _ _ (dgId_dgComp R f)

/-- Right composition with `dgHomologyId` is the identity on graded cohomology in every degree. -/
@[simp] theorem dgHomologyComp_dgHomologyId {X Y : C} {n : ℤ}
    (a : (dgHomComplex R X Y).homology n) :
    dgHomologyComp R X Y Y (add_zero n) a (dgHomologyId R Y) = a := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  rw [dgHomologyId_def, dgHomologyComp_dgHomologyClass]
  exact dgHomologyClass_congr R _ _ (dgComp_dgId R f)

/-! ### Degree transport and composition equivalences on graded cohomology -/

/-- Transport graded cohomology of a DG Hom complex along an equality of degrees. -/
def dgHomologyCastEquiv (X Y : C) {a b : ℤ} (hab : a = b) :
    (dgHomComplex R X Y).homology a ≃ₗ[R] (dgHomComplex R X Y).homology b :=
  (eqToIso (congrArg (fun d ↦ (dgHomComplex R X Y).homology d) hab)).toLinearEquiv

/-- `TauCeti.dgHomologyCastEquiv` is induced by `CategoryTheory.eqToIso` on cohomology. -/
theorem dgHomologyCastEquiv_def (X Y : C) {a b : ℤ} (hab : a = b) :
    dgHomologyCastEquiv R X Y hab =
      (eqToIso (congrArg (fun d ↦ (dgHomComplex R X Y).homology d) hab)).toLinearEquiv := (rfl)

/-- Transport along a reflexive degree equality is the identity linear equivalence. -/
@[simp] theorem dgHomologyCastEquiv_rfl (X Y : C) (a : ℤ) :
    dgHomologyCastEquiv R X Y (rfl : a = a) = LinearEquiv.refl R _ := by
  ext; simp [dgHomologyCastEquiv]

/-- Inverting `TauCeti.dgHomologyCastEquiv` reverses the degree equality. -/
@[simp] theorem dgHomologyCastEquiv_symm (X Y : C) {a b : ℤ} (hab : a = b) :
    (dgHomologyCastEquiv R X Y hab).symm = dgHomologyCastEquiv R X Y hab.symm := by
  subst hab; ext; rfl

/-- Two successive cohomology degree transports compose to transport along transitivity. -/
@[simp] theorem dgHomologyCastEquiv_trans (X Y : C) {a b c : ℤ} (hab : a = b) (hbc : b = c) :
    (dgHomologyCastEquiv R X Y hab).trans (dgHomologyCastEquiv R X Y hbc) =
      dgHomologyCastEquiv R X Y (hab.trans hbc) := by
  subst hab hbc; ext; simp

/-- `TauCeti.dgHomologyCastEquiv` transports `TauCeti.dgHomologyClass` via `TauCeti.castDeg`. -/
@[simp] theorem dgHomologyCastEquiv_dgHomologyClass {X Y : C} {a b : ℤ} (hab : a = b)
    (f : DGHom R a X Y) (hf : dgDifferential R a f = 0) :
    dgHomologyCastEquiv R X Y hab (dgHomologyClass R f hf) =
      dgHomologyClass R (castDeg R hab f) (by subst hab; simpa using hf) := by
  subst hab; simp [dgHomologyCastEquiv]

/-- `TauCeti.dgHomologyCastEquiv` commutes with `TauCeti.dgHomologyComp`. -/
theorem dgHomologyCastEquiv_dgHomologyComp {X Y Z : C} {p₁ p₂ q₁ q₂ n₁ n₂ : ℤ}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (hn : n₁ = n₂) (h₁ : p₁ + q₁ = n₁) (h₂ : p₂ + q₂ = n₂)
    (a : (dgHomComplex R X Y).homology p₁) (b : (dgHomComplex R Y Z).homology q₁) :
    dgHomologyCastEquiv R X Z hn (dgHomologyComp R X Y Z h₁ a b) =
      dgHomologyComp R X Y Z h₂ (dgHomologyCastEquiv R X Y hp a)
        (dgHomologyCastEquiv R Y Z hq b) := by
  subst hp hq hn; rfl

/-- Left composition with a graded cohomology class `u ∈ Hom^p(X, Y)` having two-sided inverse
`v ∈ Hom^q(Y, X)` is a linear equivalence `Hom^{d₁}(Y, Z) ≃ₗ[R] Hom^{d₂}(X, Z)`. -/
def dgHomologyCompLeftEquiv (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hd₁ : p + d₁ = d₂)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y ((add_comm q p).trans hpq) v u = dgHomologyId R Y) :
    (dgHomComplex R Y Z).homology d₁ ≃ₗ[R] (dgHomComplex R X Z).homology d₂ where
  toFun := dgHomologyComp R X Y Z hd₁ u
  invFun := dgHomologyComp R Y X Z (by omega : q + d₂ = d₁) v
  left_inv _ := by
    rw [← dgHomologyComp_assoc R ((add_comm q p).trans hpq) hd₁ (zero_add d₁) (by omega), hvu,
      dgHomologyId_dgHomologyComp]
  right_inv _ := by
    rw [← dgHomologyComp_assoc R hpq (by omega) (zero_add d₂) hd₁, huv,
      dgHomologyId_dgHomologyComp]
  map_add' := map_add _
  map_smul' := map_smul _

/-- `TauCeti.dgHomologyCompLeftEquiv` composes on the left with `u`. -/
@[simp] theorem dgHomologyCompLeftEquiv_apply (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hd₁ : p + d₁ = d₂)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y ((add_comm q p).trans hpq) v u = dgHomologyId R Y)
    (x : (dgHomComplex R Y Z).homology d₁) :
    dgHomologyCompLeftEquiv R Z hpq hd₁ u v huv hvu x = dgHomologyComp R X Y Z hd₁ u x :=
  (rfl)

/-- `(TauCeti.dgHomologyCompLeftEquiv …).symm` composes on the left with `v`. -/
@[simp] theorem dgHomologyCompLeftEquiv_symm_apply (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hd₁ : p + d₁ = d₂)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y ((add_comm q p).trans hpq) v u = dgHomologyId R Y)
    (y : (dgHomComplex R X Z).homology d₂) :
    (dgHomologyCompLeftEquiv R Z hpq hd₁ u v huv hvu).symm y =
      dgHomologyComp R Y X Z (by omega : q + d₂ = d₁) v y :=
  (rfl)

/-- Right composition with a graded cohomology class `u ∈ Hom^p(X, Y)` having two-sided inverse
`v ∈ Hom^q(Y, X)` is a linear equivalence `Hom^{d₁}(Z, X) ≃ₗ[R] Hom^{d₂}(Z, Y)`. -/
def dgHomologyCompRightEquiv (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hd₁ : d₁ + p = d₂)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y ((add_comm q p).trans hpq) v u = dgHomologyId R Y) :
    (dgHomComplex R Z X).homology d₁ ≃ₗ[R] (dgHomComplex R Z Y).homology d₂ where
  toFun := (dgHomologyComp R Z X Y hd₁).flip u
  invFun := (dgHomologyComp R Z Y X (by omega : d₂ + q = d₁)).flip v
  left_inv _ := by
    rw [LinearMap.flip_apply, LinearMap.flip_apply,
      dgHomologyComp_assoc R hd₁ hpq (by omega) (add_zero d₁), huv, dgHomologyComp_dgHomologyId]
  right_inv _ := by
    rw [LinearMap.flip_apply, LinearMap.flip_apply,
      dgHomologyComp_assoc R (by omega) ((add_comm q p).trans hpq) hd₁ (add_zero d₂), hvu,
      dgHomologyComp_dgHomologyId]
  map_add' := map_add _
  map_smul' := map_smul _

/-- `TauCeti.dgHomologyCompRightEquiv` composes on the right with `u`. -/
@[simp] theorem dgHomologyCompRightEquiv_apply (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hd₁ : d₁ + p = d₂)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y ((add_comm q p).trans hpq) v u = dgHomologyId R Y)
    (x : (dgHomComplex R Z X).homology d₁) :
    dgHomologyCompRightEquiv R Z hpq hd₁ u v huv hvu x = dgHomologyComp R Z X Y hd₁ x u :=
  (rfl)

/-- `(TauCeti.dgHomologyCompRightEquiv …).symm` composes on the right with `v`. -/
@[simp] theorem dgHomologyCompRightEquiv_symm_apply (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hd₁ : d₁ + p = d₂)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y ((add_comm q p).trans hpq) v u = dgHomologyId R Y)
    (y : (dgHomComplex R Z Y).homology d₂) :
    (dgHomologyCompRightEquiv R Z hpq hd₁ u v huv hvu).symm y =
      dgHomologyComp R Z Y X (by omega : d₂ + q = d₁) y v :=
  (rfl)

end TauCeti
