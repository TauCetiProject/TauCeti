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
graded Leibniz rule `d(dgComp f g) = dgComp (d f) g + (-1)^p • dgComp f (d g)` ensures that
homogeneous DG composition sends cocycles of degrees `p` and `q` to a cocycle of degree `p + q`
and sends coboundaries paired with cocycles on either side to coboundaries. Descending to Mathlib's
canonical cohomology objects `(dgHomComplex R X Y).homology p` produces a bilinear graded
composition `TauCeti.dgHomologyComp` extending the degree-zero composition `TauCeti.dgHomotopyComp`
of `DGHomotopyCategory`.

## Main definitions and results

* `TauCeti.dgHomologyClass`: the canonical degree-`n` cohomology class of a closed morphism
  `f : DGHom R n X Y`, with `TauCeti.exists_dgHomologyClass_eq`,
  `TauCeti.dgHomologyClass_eq_zero_iff`, and comparison `TauCeti.dgHomologyClass_eq_homologyπ` with
  `HomologicalComplex.homologyπ`.
* `TauCeti.dgHomologyId`: the degree-zero identity class `[dgId R X]`.
* `TauCeti.dgHomologyComp`: bilinear composition
  `Hom^p(X, Y) →ₗ[R] Hom^q(Y, Z) →ₗ[R] Hom^n(X, Z)` for `p + q = n`, associative
  (`TauCeti.dgHomologyComp_assoc`), unital (`TauCeti.dgHomologyId_dgHomologyComp`,
  `TauCeti.dgHomologyComp_dgHomologyId`), agreeing with `TauCeti.dgHomotopyComp` in degree zero,
  and preserved by every DG functor (`CategoryTheory.EnrichedFunctor.homologyMap_dgHomologyComp`).

## References

* B. Keller, *Deriving DG categories*, Section 1.2, for the graded homotopy category `H*(C)`.
-/

public section
noncomputable section

open CategoryTheory HomologicalComplex

namespace TauCeti

universe v u u'

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

private def dgGradedCyclesEquiv (n : ℤ) (X Y : C) :
    LinearMap.ker (dgDifferential R (X := X) (Y := Y) n) ≃ₗ[R]
      ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.K :=
  LinearEquiv.refl R _

private def dgGradedHomologyIso (n : ℤ) (X Y : C) :
    (dgHomComplex R X Y).homology n ≅
      ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.H :=
  (dgHomComplex R X Y).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    ((dgHomComplex R X Y).sc' (n - 1) n (n + 1)).moduleCatHomologyIso

/-- The linear quotient map from degree-`n` cocycles to canonical degree-`n` cohomology. -/
def dgHomologyClassLinearMap (n : ℤ) (X Y : C) :
    LinearMap.ker (dgDifferential R (X := X) (Y := Y) n) →ₗ[R]
      (dgHomComplex R X Y).homology n :=
  let S := (dgHomComplex R X Y).sc' (n - 1) n (n + 1)
  (dgGradedHomologyIso R n X Y).inv.hom.comp
    (S.moduleCatLeftHomologyData.π.hom.comp (dgGradedCyclesEquiv R n X Y).toLinearMap)

/-- The canonical degree-`n` cohomology class of a closed morphism `f : DGHom R n X Y`. -/
def dgHomologyClass {n : ℤ} {X Y : C} (f : DGHom R n X Y) (hf : dgDifferential R n f = 0) :
    (dgHomComplex R X Y).homology n :=
  dgHomologyClassLinearMap R n X Y ⟨f, hf⟩

private theorem dgHomologyClass_hom {n : ℤ} {X Y : C}
    (f : DGHom R n X Y) (hf : dgDifferential R n f = 0) :
    (dgGradedHomologyIso R n X Y).hom.hom (dgHomologyClass R f hf) =
      Submodule.Quotient.mk (dgGradedCyclesEquiv R n X Y ⟨f, hf⟩) := by
  let e := dgGradedHomologyIso R n X Y
  -- Unfolding `dgHomologyClassLinearMap` exposes transport by `e.inv`, cancelled by `e.hom`.
  change e.hom (e.inv _) = _
  exact e.inv_hom_id_apply _

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
    dgHomologyClass R (r • f) (by rw [map_smul, hf, smul_zero]) =
      r • dgHomologyClass R f hf :=
  (dgHomologyClassLinearMap R n X Y).map_smul r ⟨f, hf⟩

/-- `TauCeti.dgHomologyClass` preserves negation of cocycles. -/
@[simp]
theorem dgHomologyClass_neg {n : ℤ} {X Y : C} (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R (-f) (by rw [map_neg, hf, neg_zero]) = -dgHomologyClass R f hf :=
  (dgHomologyClassLinearMap R n X Y).map_neg ⟨f, hf⟩

/-- Every degree-`n` cohomology class has a closed degree-`n` representative. -/
theorem exists_dgHomologyClass_eq {n : ℤ} {X Y : C}
    (c : (dgHomComplex R X Y).homology n) :
    ∃ (f : DGHom R n X Y) (hf : dgDifferential R n f = 0), dgHomologyClass R f hf = c := by
  let e := dgGradedHomologyIso R n X Y
  obtain ⟨f, hf⟩ : ∃ f, Submodule.Quotient.mk f = e.hom.hom c := by
    induction e.hom.hom c using Submodule.Quotient.induction_on with
    | H f => exact ⟨f, rfl⟩
  have hf' : dgDifferential R n f.1 = 0 := by
    simpa only [HomologicalComplex.shortComplexFunctor'_obj_g, LinearMap.mem_ker] using f.2
  refine ⟨f.1, hf', ?_⟩
  apply e.toLinearEquiv.injective
  -- `e.toLinearEquiv` acts by `e.hom.hom`, matching `dgHomologyClass_hom`.
  change e.hom.hom (dgHomologyClass R f.1 hf') = e.hom.hom c
  exact (dgHomologyClass_hom R f.1 hf').trans hf

/-- Two closed degree-`n` morphisms represent the same cohomology class if and only if their
difference lies in the image of the incoming differential. -/
theorem dgHomologyClass_eq_iff {n : ℤ} {X Y : C} {f g : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) :
    dgHomologyClass R f hf = dgHomologyClass R g hg ↔
      ∃ h : DGHom R (n - 1) X Y, ((dgHomComplex R X Y).d (n - 1) n).hom h = f - g := by
  let e := dgGradedHomologyIso R n X Y
  let S := (dgHomComplex R X Y).sc' (n - 1) n (n + 1)
  constructor
  · intro heq
    have h' : e.hom.hom (dgHomologyClass R f hf) = e.hom.hom (dgHomologyClass R g hg) :=
      congrArg e.hom.hom heq
    rw [dgHomologyClass_hom, dgHomologyClass_hom] at h'
    obtain ⟨h, hh⟩ := (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mp h'
    exact ⟨h, congrArg Subtype.val hh⟩
  · rintro ⟨h, hh⟩
    apply e.toLinearEquiv.injective
    -- Expose `e.hom.hom` so `dgHomologyClass_hom` rewrites both sides to quotient classes.
    change e.hom.hom (dgHomologyClass R f hf) = e.hom.hom (dgHomologyClass R g hg)
    rw [dgHomologyClass_hom, dgHomologyClass_hom]
    exact (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mpr ⟨h, Subtype.ext hh⟩

/-- A closed degree-`n` morphism represents zero in cohomology if and only if it is in the image of
the incoming differential. -/
theorem dgHomologyClass_eq_zero_iff {n : ℤ} {X Y : C} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) :
    dgHomologyClass R f hf = 0 ↔
      ∃ h : DGHom R (n - 1) X Y, ((dgHomComplex R X Y).d (n - 1) n).hom h = f := by
  rw [← dgHomologyClass_zero R n X Y, dgHomologyClass_eq_iff]
  simp only [sub_zero]

/-- Exact coboundaries `dgDifferential R m h` vanish in degree-`m + 1` cohomology. -/
@[simp]
theorem dgHomologyClass_dgDifferential {m : ℤ} {X Y : C} (h : DGHom R m X Y) :
    dgHomologyClass R (dgDifferential R m h) (dgDifferential_dgDifferential R h) = 0 := by
  rw [dgHomologyClass_eq_zero_iff]
  refine ⟨castDeg R (by omega : m = m + 1 - 1) h, ?_⟩
  simpa only [castDeg_self] using
    d_castDeg R (by omega : m = m + 1 - 1) (rfl : m + 1 = m + 1) h

private theorem exists_iCycles_and_dgHomologyClass {n : ℤ} {X Y : C} (f : DGHom R n X Y)
    (hf : dgDifferential R n f = 0) :
    ∃ x : (dgHomComplex R X Y).cycles n, ((dgHomComplex R X Y).iCycles n).hom x = f ∧
      dgHomologyClass R f hf = ((dgHomComplex R X Y).homologyπ n).hom x := by
  let K := dgHomComplex R X Y
  let S := K.sc' (n - 1) n (n + 1)
  let e := K.cyclesIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let eH := K.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)
  let c : S.moduleCatLeftHomologyData.K := ⟨f, hf⟩
  refine ⟨(S.moduleCatCyclesIso.inv ≫ e.inv).hom c, ?_, ?_⟩
  · have h : (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.iCycles n =
        S.moduleCatLeftHomologyData.i := by
      rw [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
      exact S.moduleCatCyclesIso_inv_iCycles
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c
  · have h : S.moduleCatLeftHomologyData.π ≫ (S.moduleCatHomologyIso.inv ≫ eH.inv) =
        (S.moduleCatCyclesIso.inv ≫ e.inv) ≫ K.homologyπ n := by
      rw [← Category.assoc, ← S.moduleCatCyclesIso_inv_π, Category.assoc, Category.assoc,
        HomologicalComplex.π_homologyIsoSc'_inv]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c

/-- `TauCeti.dgHomologyClass` agrees with Mathlib's `HomologicalComplex.homologyπ` on any cycle
lifting `f`. -/
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
    (hf : dgDifferential R n f = 0) :
    dgDifferential R n ((φ.f n).hom f) = 0 := by
  have hcomm := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.comm n (n + 1))) f
  -- `φ.comm n (n + 1)` says `φ.f n ≫ d = d ≫ φ.f (n + 1)`, so `d (φ.f n f) = φ.f (n + 1) (d f)`.
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, dgDifferential, hf, map_zero] using hcomm

/-- `HomologicalComplex.homologyMap` acts on `TauCeti.dgHomologyClass` by applying the chain map to
its representative. -/
@[simp]
theorem homologyMap_dgHomologyClass {C' : Type u'} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {n : ℤ} {f : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) :
    (HomologicalComplex.homologyMap φ n).hom (dgHomologyClass R f hf) =
      dgHomologyClass R ((φ.f n).hom f) (map_dgDifferential_eq_zero R φ hf) := by
  obtain ⟨x, hx, hclass⟩ := exists_iCycles_and_dgHomologyClass R f hf
  rw [hclass, dgHomologyClass_eq_homologyπ R _ ((HomologicalComplex.cyclesMap φ n).hom x)]
  · simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.homologyπ_naturality φ n)) x
  · rw [← hx]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.cyclesMap_i φ n)) x

/-! ### Graded cohomology composition and identity -/

/-- The canonical degree-zero cohomology class of the DG identity of `X`. -/
def dgHomologyId (X : C) : (dgHomComplex R X X).homology 0 :=
  dgHomologyClass R (dgId R X) (dgDifferential_dgId R X)

/-- `TauCeti.dgHomologyId` is the degree-zero class of `dgId R X`. -/
theorem dgHomologyId_def (X : C) :
    dgHomologyId R X = dgHomologyClass R (dgId R X) (dgDifferential_dgId R X) :=
  (rfl)

/-- Composing closed homogeneous morphisms of degrees `p` and `q` gives a closed morphism of
degree `p + q`. -/
theorem dgDifferential_dgComp_eq_zero {X Y Z : C} {p q n : ℤ} {f : DGHom R p X Y}
    {g : DGHom R q Y Z} (hf : dgDifferential R p f = 0) (hg : dgDifferential R q g = 0)
    (h : p + q = n) :
    dgDifferential R n (dgComp R f g h) = 0 := by
  rw [dgDifferential_dgComp, hf, hg, zero_dgComp, dgComp_zero, smul_zero, add_zero]

private theorem exists_d_eq_dgComp_of_left {X Y Z : C} {p q n : ℤ}
    (f₀ : DGHom R (p - 1) X Y) {g : DGHom R q Y Z} (hg : dgDifferential R q g = 0)
    (h : p + q = n) :
    ∃ k : DGHom R (n - 1) X Z,
      ((dgHomComplex R X Z).d (n - 1) n).hom k =
        dgComp R (((dgHomComplex R X Y).d (p - 1) p).hom f₀) g h := by
  refine ⟨dgComp R f₀ g (by omega), ?_⟩
  rw [dgHomComplex_d_dgComp R (by omega : p - 1 + 1 = p) (rfl : q + 1 = q + 1)
    (by omega : n - 1 + 1 = n) f₀ g (by omega), hg, dgComp_zero, smul_zero, add_zero]

private theorem exists_d_eq_dgComp_of_right {X Y Z : C} {p q n : ℤ}
    {f : DGHom R p X Y} (hf : dgDifferential R p f = 0) (g₀ : DGHom R (q - 1) Y Z)
    (h : p + q = n) :
    ∃ k : DGHom R (n - 1) X Z,
      ((dgHomComplex R X Z).d (n - 1) n).hom k =
        dgComp R f (((dgHomComplex R Y Z).d (q - 1) q).hom g₀) h := by
  refine ⟨p.negOnePow • dgComp R f g₀ (by omega), ?_⟩
  rw [Units.smul_def, map_zsmul, ← Units.smul_def,
    dgHomComplex_d_dgComp R (rfl : p + 1 = p + 1) (by omega : q - 1 + 1 = q)
      (by omega : n - 1 + 1 = n) f g₀ (by omega),
    hf, zero_dgComp, zero_add, smul_smul, Int.units_mul_self, one_smul]

private def dgConcreteGradedComp (X Y Z : C) {p q n : ℤ} (h : p + q = n) :
    ((dgHomComplex R X Y).sc' (p - 1) p (p + 1)).moduleCatLeftHomologyData.H →ₗ[R]
      ((dgHomComplex R Y Z).sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData.H →ₗ[R]
        ((dgHomComplex R X Z).sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.H :=
  let SXY := (dgHomComplex R X Y).sc' (p - 1) p (p + 1)
  let SYZ := (dgHomComplex R Y Z).sc' (q - 1) q (q + 1)
  let SXZ := (dgHomComplex R X Z).sc' (n - 1) n (n + 1)
  let raw : SXY.moduleCatLeftHomologyData.K →ₗ[R] SYZ.moduleCatLeftHomologyData.K →ₗ[R]
      SXZ.moduleCatLeftHomologyData.H :=
    LinearMap.mk₂ R
      (fun f g ↦ Submodule.Quotient.mk
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
        exact congrArg Submodule.Quotient.mk (Subtype.ext (dgComp_smul R r f.1 g.1 h)))
  raw.liftQ₂ (LinearMap.range SXY.moduleCatToCycles) (LinearMap.range SYZ.moduleCatToCycles)
    (by
      rintro _ ⟨f₀, rfl⟩
      apply LinearMap.ext fun g ↦ ?_
      obtain ⟨k, hk⟩ := exists_d_eq_dgComp_of_left R f₀ g.2 h
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨k, Subtype.ext hk⟩)
    (by
      rintro _ ⟨g₀, rfl⟩
      apply LinearMap.ext fun f ↦ ?_
      obtain ⟨k, hk⟩ := exists_d_eq_dgComp_of_right R f.2 g₀ h
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨k, Subtype.ext hk⟩)

/-- Bilinear graded composition on canonical cohomology of DG Hom complexes, in Mathlib's enriched
factor order (`dgHomologyComp R X Y Z h [f] [g] = [dgComp R f g h]`). -/
def dgHomologyComp (X Y Z : C) {p q n : ℤ} (h : p + q = n) :
    (dgHomComplex R X Y).homology p →ₗ[R]
      (dgHomComplex R Y Z).homology q →ₗ[R]
        (dgHomComplex R X Z).homology n :=
  LinearMap.mk₂ R
    (fun a b ↦ (dgGradedHomologyIso R n X Z).inv.hom
      (dgConcreteGradedComp R X Y Z h
        ((dgGradedHomologyIso R p X Y).hom.hom a)
        ((dgGradedHomologyIso R q Y Z).hom.hom b)))
    (fun _ _ _ ↦ by simp only [map_add, LinearMap.add_apply])
    (fun _ _ _ ↦ by simp only [map_smul, LinearMap.smul_apply])
    (fun _ _ _ ↦ by simp only [map_add])
    (fun _ _ _ ↦ by simp only [map_smul])

/-- `TauCeti.dgHomologyComp` evaluates on cohomology classes of closed morphisms to the class of
their DG composite. -/
@[simp]
theorem dgHomologyComp_dgHomologyClass {X Y Z : C} {p q n : ℤ} (h : p + q = n)
    (f : DGHom R p X Y) (g : DGHom R q Y Z)
    (hf : dgDifferential R p f = 0) (hg : dgDifferential R q g = 0) :
    dgHomologyComp R X Y Z h (dgHomologyClass R f hf) (dgHomologyClass R g hg) =
      dgHomologyClass R (dgComp R f g h) (dgDifferential_dgComp_eq_zero R hf hg h) := by
  let eXZ := dgGradedHomologyIso R n X Z
  apply eXZ.toLinearEquiv.injective
  -- Expose `eXZ.hom.hom` so `eXZ.inv_hom_id_apply` and `dgHomologyClass_hom` simplify both sides.
  change eXZ.hom.hom (eXZ.inv.hom _) = eXZ.hom.hom _
  rw [show eXZ.hom.hom (eXZ.inv.hom _) = _ from eXZ.inv_hom_id_apply _,
    dgHomologyClass_hom, dgHomologyClass_hom, dgHomologyClass_hom]
  rfl

/-- Graded cohomology composition is associative. -/
theorem dgHomologyComp_assoc {W X Y Z : C} {p q r pq qr n : ℤ}
    (hpq : p + q = pq) (hqr : q + r = qr) (hn₁ : pq + r = n) (hn₂ : p + qr = n)
    (a : (dgHomComplex R W X).homology p)
    (b : (dgHomComplex R X Y).homology q)
    (c : (dgHomComplex R Y Z).homology r) :
    dgHomologyComp R W Y Z hn₁ (dgHomologyComp R W X Y hpq a b) c =
      dgHomologyComp R W X Z hn₂ a (dgHomologyComp R X Y Z hqr b c) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomologyClass_eq R b
  obtain ⟨k, hk, rfl⟩ := exists_dgHomologyClass_eq R c
  simp only [dgHomologyComp_dgHomologyClass]
  apply congrArg (dgHomologyClassLinearMap R n W Z)
  exact Subtype.ext (dgComp_assoc R f g k hpq hqr (by omega))

/-- Left composition with `dgHomologyId` is the identity on graded cohomology in every degree. -/
@[simp]
theorem dgHomologyId_dgHomologyComp {X Y : C} {n : ℤ} (a : (dgHomComplex R X Y).homology n) :
    dgHomologyComp R X X Y (zero_add n) (dgHomologyId R X) a = a := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  rw [dgHomologyId_def, dgHomologyComp_dgHomologyClass]
  apply congrArg (dgHomologyClassLinearMap R n X Y)
  exact Subtype.ext (dgId_dgComp R f)

/-- Right composition with `dgHomologyId` is the identity on graded cohomology in every degree. -/
@[simp]
theorem dgHomologyComp_dgHomologyId {X Y : C} {n : ℤ} (a : (dgHomComplex R X Y).homology n) :
    dgHomologyComp R X Y Y (add_zero n) a (dgHomologyId R Y) = a := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  rw [dgHomologyId_def, dgHomologyComp_dgHomologyClass]
  apply congrArg (dgHomologyClassLinearMap R n X Y)
  exact Subtype.ext (dgComp_dgId R f)

/-- In degree zero, `TauCeti.dgHomologyComp` agrees with `TauCeti.dgHomotopyComp`. -/
theorem dgHomologyComp_zero_eq_dgHomotopyComp (X Y Z : C) :
    dgHomologyComp R X Y Z (zero_add 0) = dgHomotopyComp R X Y Z := by
  apply LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
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

variable {R : Type v} [CommRing R] {C : Type u} {D : Type u'}
  [DGCategory R C] [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

/-- Every DG functor preserves `TauCeti.dgHomologyId`. -/
@[simp]
theorem homologyMap_dgHomologyId (X : C) :
    (homologyMap (F.map X X) 0).hom (dgHomologyId R X) = dgHomologyId R (F.obj X) := by
  rw [dgHomologyId_def, dgHomologyId_def, homologyMap_dgHomologyClass]
  apply congrArg (dgHomologyClassLinearMap R 0 (F.obj X) (F.obj X))
  exact Subtype.ext ((F.dgMap_apply (dgId R X)).symm.trans (F.dgMap_dgId X))

/-- Every DG functor commutes with `TauCeti.dgHomologyComp` in all degrees. -/
theorem homologyMap_dgHomologyComp {X Y Z : C} {p q n : ℤ} (h : p + q = n)
    (a : (dgHomComplex R X Y).homology p) (b : (dgHomComplex R Y Z).homology q) :
    (homologyMap (F.map X Z) n).hom (dgHomologyComp R X Y Z h a b) =
      dgHomologyComp R (F.obj X) (F.obj Y) (F.obj Z) h
        ((homologyMap (F.map X Y) p).hom a) ((homologyMap (F.map Y Z) q).hom b) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq R a
  obtain ⟨g, hg, rfl⟩ := exists_dgHomologyClass_eq R b
  simp only [dgHomologyComp_dgHomologyClass, homologyMap_dgHomologyClass]
  apply congrArg (dgHomologyClassLinearMap R n (F.obj X) (F.obj Z))
  exact Subtype.ext
    (((F.dgMap_apply (dgComp R f g h)).symm.trans (F.dgMap_dgComp f g h)).trans
      (by rw [F.dgMap_apply, F.dgMap_apply]))

end CategoryTheory.EnrichedFunctor
