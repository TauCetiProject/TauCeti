/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.Algebra.Homology.ModuleCat.Shift.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Mapping cones of complexes of modules

Let `φ : K ⟶ L` be a morphism of homological complexes of modules over a ring. In a degree `i`
with `c.Rel i j`, the term of the mapping cone `homotopyCofiber φ` is `K.X j ⊞ L.X i`; composing
Mathlib's `HomologicalComplex.homotopyCofiber.XIsoBiprod` with `ModuleCat.biprodIsoProd` gives the
linear equivalence `HomologicalComplex.homotopyCofiber.XEquiv` with `L.X i × K.X j`, whose
coordinates are the projections `sndX` and `fstX`. For chain complexes indexed by `ℤ`, bases of
`K` and `L` give the mapping cone the basis `HomologicalComplex.homotopyCofiber.basis`: the basis
of `L.X i` followed by that of `K.X (i - 1)`.

The mapping cone of `K ⟶ 0` is `K` shifted by one degree: its terms are identified with those of
`K` by `HomologicalComplex.homotopyCofiber.zeroEquiv`, under which its differentials become the
negatives of those of `K` (`HomologicalComplex.homotopyCofiber.zeroEquiv_d`), its homology is
identified with that of `K` one degree down
(`HomologicalComplex.homotopyCofiber.zeroHomologyEquiv`), and the connecting map of
`coneShortComplex φ` is `homologyMap φ` composed with that identification
(`HomologicalComplex.homotopyCofiber.coneShortComplex_δ_eq`).
-/

public section

noncomputable section

open CategoryTheory Limits ZeroObject Module

namespace HomologicalComplex.homotopyCofiber

variable {R : Type*} [Ring R]

section XEquiv

variable {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
  {K L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L)

/-- The decomposition `(homotopyCofiber φ).X i ≃ L.X i × K.X j` of the term of the mapping cone in
a degree `i` with `c.Rel i j`. -/
def XEquiv {i j : ι} (hij : c.Rel i j) : (X φ i : ModuleCat R) ≃ₗ[R] L.X i × K.X j :=
  (XIsoBiprod φ i j hij ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.trans
    (LinearEquiv.prodComm R _ _)

/-- The coordinates of `XEquiv` are the projections `sndX` and `fstX`. -/
@[simp]
theorem XEquiv_apply {i j : ι} (hij : c.Rel i j) (x : (X φ i : ModuleCat R)) :
    XEquiv φ hij x = ((sndX φ i).hom x, (fstX φ i j hij).hom x) := by
  simp only [XEquiv, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply]
  exact Prod.ext congr(($(XIsoBiprod_hom_snd φ i j hij)).hom x) rfl

/-- The inverse of `XEquiv` is the sum of the inclusions `inrX` and `inlX`. -/
@[simp]
theorem XEquiv_symm_apply {i j : ι} (hij : c.Rel i j) (y : L.X i × K.X j) :
    (XEquiv φ hij).symm y = (inrX φ i).hom y.1 + (inlX φ j i hij).hom y.2 := by
  rw [LinearEquiv.symm_apply_eq, XEquiv_apply, map_add, map_add]
  have h₁ := congr(($(inrX_sndX φ i)).hom y.1)
  have h₂ := congr(($(inrX_fstX φ i j hij)).hom y.1)
  have h₃ := congr(($(inlX_sndX φ j i hij)).hom y.2)
  have h₄ := congr(($(inlX_fstX φ j i hij)).hom y.2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

variable (K) in
/-- The projection `fstX` identifies the term of the mapping cone of `K ⟶ 0` in a degree `i` with
`c.Rel i j` with `K.X j`. -/
def zeroEquiv {i j : ι} (hij : c.Rel i j) :
    (X (0 : K ⟶ 0) i : ModuleCat R) ≃ₗ[R] K.X j :=
  LinearEquiv.ofLinearMap (fstX (0 : K ⟶ 0) i j hij).hom (inlX (0 : K ⟶ 0) j i hij).hom
    (by ext x; exact congr(($(inlX_fstX (0 : K ⟶ 0) j i hij)).hom x))
    (by ext x; exact congr(($(fstX_inlX_zero (F := K) i j hij)).hom x))

variable (K) in
/-- The isomorphism `zeroEquiv` is the projection `fstX`. -/
@[simp]
theorem zeroEquiv_apply {i j : ι} (hij : c.Rel i j) (x : (X (0 : K ⟶ 0) i : ModuleCat R)) :
    zeroEquiv K hij x = (fstX (0 : K ⟶ 0) i j hij).hom x :=
  (rfl)

variable (K) in
/-- The inverse of `zeroEquiv` is the inclusion `inlX`. -/
@[simp]
theorem zeroEquiv_symm_apply {i j : ι} (hij : c.Rel i j) (x : K.X j) :
    (zeroEquiv K hij).symm x = (inlX (0 : K ⟶ 0) j i hij).hom x :=
  (rfl)

variable (K) in
/-- The differentials of the mapping cone of `K ⟶ 0` correspond under `zeroEquiv` to the negated
differentials of `K`. -/
theorem zeroEquiv_d {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k)
    (x : (homotopyCofiber (0 : K ⟶ 0)).X i) :
    zeroEquiv K hjk (((homotopyCofiber (0 : K ⟶ 0)).d i j).hom x) =
      -(K.d j k).hom (zeroEquiv K hij x) :=
  congr(($(d_fstX (0 : K ⟶ 0) i j k hij hjk)).hom x)

end XEquiv

section Basis

variable {K L : ChainComplex (ModuleCat R) ℤ} (φ : K ⟶ L)
  {nK nL : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) R (K.X i))
  (cL : ∀ i, Basis (Fin (nL i)) R (L.X i))

/-- The basis of the term `(homotopyCofiber φ).X i = K.X (i - 1) ⊞ L.X i` of the mapping cone of a
chain map `φ : K ⟶ L` of based complexes: the basis `cL i` of `L.X i`, included by `inrX`, followed
by the basis `cK (i - 1)` of `K.X (i - 1)`, included by `inlX`. -/
def basis (i : ℤ) : Basis (Fin (nL i + nK (i - 1))) R (X φ i : ModuleCat R) :=
  (((cL i).prod (cK (i - 1))).map
    (XEquiv φ (by simp : (ComplexShape.down ℤ).Rel i (i - 1))).symm).reindex finSumFinEquiv

/-- The first `nL i` vectors of the basis of the mapping cone in degree `i` are the images of the
basis of `L.X i`. -/
@[simp]
theorem basis_castAdd (i : ℤ) (k : Fin (nL i)) :
    basis φ cK cL i (Fin.castAdd (nK (i - 1)) k) = (inrX φ i).hom (cL i k) := by
  simp [basis]

/-- The last `nK (i - 1)` vectors of the basis of the mapping cone in degree `i` are the images of
the basis of `K.X (i - 1)`. -/
@[simp]
theorem basis_natAdd (i : ℤ) (k : Fin (nK (i - 1))) :
    basis φ cK cL i (Fin.natAdd (nL i) k) = (inlX φ (i - 1) i (by simp)).hom (cK (i - 1) k) := by
  simp [basis]

/-- The basis of the term of the mapping cone of `K ⟶ 0` in degree `i` corresponding to the basis
`cK (i - 1)` of `K.X (i - 1)`. -/
def zeroBasis (i : ℤ) : Basis (Fin (nK (i - 1))) R (X (0 : K ⟶ 0) i : ModuleCat R) :=
  (cK (i - 1)).map (zeroEquiv K (by simp : (ComplexShape.down ℤ).Rel i (i - 1))).symm

/-- The basis of the term of the mapping cone of `K ⟶ 0` in degree `i` is the image of the basis
`cK (i - 1)` under the inclusion `inlX`. -/
@[simp]
theorem zeroBasis_apply (i : ℤ) (k : Fin (nK (i - 1))) :
    zeroBasis cK i k = (inlX (0 : K ⟶ 0) (i - 1) i (by simp)).hom (cK (i - 1) k) :=
  zeroEquiv_symm_apply K _ _

/-- The isomorphism `zeroEquiv` sends the basis of the term of the mapping cone of `K ⟶ 0` in
degree `i + 1` to the basis `cK i`, up to the identification of `i + 1 - 1` with `i`. -/
theorem zeroEquiv_zeroBasis (i : ℤ) (k : Fin (nK (i + 1 - 1))) :
    zeroEquiv K (by simp : (ComplexShape.down ℤ).Rel (i + 1) i) (zeroBasis cK (i + 1) k) =
      cK i (Fin.cast (by simp) k) := by
  -- The indices `i + 1 - 1` and `i` are only propositionally equal.
  have key : ∀ a (ha : a = i) (k : Fin (nK a)) (h₁ : (ComplexShape.down ℤ).Rel (i + 1) a),
      (fstX (0 : K ⟶ 0) (i + 1) i (by simp)).hom ((inlX (0 : K ⟶ 0) a (i + 1) h₁).hom (cK a k)) =
        cK i (Fin.cast (by rw [ha]) k) := by
    rintro a rfl k h₁
    exact congr(($(inlX_fstX (0 : K ⟶ 0) _ _ h₁)).hom (cK a k))
  exact key _ (by simp) k _

end Basis

section Homology

variable {K L : ChainComplex (ModuleCat R) ℤ} (φ : K ⟶ L)

variable (K) in
/-- The isomorphism `(homotopyCofiber (0 : K ⟶ 0)).homology (i + 1) ≃ₗ[R] K.homology i` induced by
`zeroEquiv`. -/
def zeroHomologyEquiv (i : ℤ) :
    (homotopyCofiber (0 : K ⟶ 0)).homology (i + 1) ≃ₗ[R] K.homology i :=
  homologyEquivOfShift (fun j ↦ zeroEquiv K (by simp))
    (fun j ↦ zeroEquiv_d K (i := j + 1 + 1) (j := j + 1) (k := j) (by simp) (by simp)) i

variable (K) in
/-- `zeroHomologyEquiv K` is `homologyEquivOfShift` for `zeroEquiv K`. -/
theorem zeroHomologyEquiv_eq (i : ℤ) :
    zeroHomologyEquiv K i = homologyEquivOfShift (fun j ↦ zeroEquiv K (by simp))
      (fun j ↦ zeroEquiv_d K (i := j + 1 + 1) (j := j + 1) (k := j) (by simp) (by simp)) i := by
  rfl

/-- The connecting map of `coneShortComplex φ` in degree `i + 1` is `homologyMap φ i` composed with
`zeroHomologyEquiv K i`. -/
theorem coneShortComplex_δ_eq (hc : ∀ j : ℤ, ∃ i, (ComplexShape.down ℤ).Rel i j) (i : ℤ) :
    ((coneShortComplex_shortExact φ hc).δ (i + 1) i rfl).hom =
      (homologyMap φ i).hom ∘ₗ (zeroHomologyEquiv K i).toLinearMap := by
  ext x
  obtain ⟨z, rfl⟩ := (homotopyCofiber (0 : K ⟶ 0)).moduleCat_homologyπ_surjective (i + 1) x
  set zK : K.cycles i :=
    cyclesEquivOfShift (fun j ↦ zeroEquiv K (by simp))
      (fun j ↦ zeroEquiv_d K (i := j + 1 + 1) (j := j + 1) (k := j) (by simp) (by simp)) i z
  let x₂ : (homotopyCofiber φ).X (i + 1) := (inlX φ i (i + 1) (by simp)).hom ((K.iCycles i).hom zK)
  have hx₂ : ((coneShortComplex φ hc).g.f (i + 1)).hom x₂ =
      ((homotopyCofiber (0 : K ⟶ 0)).iCycles (i + 1)).hom z := by
    have hzero : (inlX (0 : K ⟶ 0) i (i + 1) (by simp)).hom ((K.iCycles i).hom zK) =
        ((homotopyCofiber (0 : K ⟶ 0)).iCycles (i + 1)).hom z := by
      apply (zeroEquiv K (by simp : (ComplexShape.down ℤ).Rel (i + 1) i)).injective
      simpa [zK] using (LinearEquiv.apply_symm_apply
        (zeroEquiv K (by simp : (ComplexShape.down ℤ).Rel (i + 1) i)) ((K.iCycles i).hom zK))
    dsimp [coneShortComplex, x₂]
    exact congr(($(inlX_mapArrowHom_f φ (0 : K ⟶ 0) hc (Arrow.homMk (𝟙 K) 0) i (i + 1)
      (by simp))).hom ((K.iCycles i).hom zK)).trans (by simpa using hzero)
  have hzL : ((coneShortComplex φ hc).f.f i).hom ((L.iCycles i).hom ((cyclesMap φ i).hom zK)) =
      ((homotopyCofiber φ).d (i + 1) i).hom x₂ := by
    have hd := congr(($(inlX_d φ (i + 1) i (i - 1) (by simp) (by simp))).hom ((K.iCycles i).hom zK))
    have hdzK : (K.d i (i - 1)).hom ((K.iCycles i).hom zK) = 0 :=
      K.moduleCat_d_iCycles_apply i (i - 1) zK
    have hcyc := congr(($(cyclesMap_i φ i)).hom zK)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.hom_neg, LinearMap.neg_apply, hdzK, map_zero, neg_zero, zero_add] at hd hcyc
    simpa [coneShortComplex, x₂, hcyc] using hd.symm
  have hδ := (coneShortComplex_shortExact φ hc).moduleCat_δ_homologyπ (i + 1) i rfl z x₂ hx₂
    ((cyclesMap φ i).hom zK) hzL
  have hnat := congr(($(homologyπ_naturality φ i)).hom zK)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, zeroHomologyEquiv,
    homologyEquivOfShift_homologyπ]
  exact hδ.trans hnat.symm

end Homology

end HomologicalComplex.homotopyCofiber
