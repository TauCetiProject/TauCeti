/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Determinant
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Mapping cones of complexes of modules

Let `φ : K ⟶ L` be a morphism of homological complexes of modules over a ring. In a degree `i`
with `c.Rel i j`, the term of the mapping cone `homotopyCofiber φ` is `K.X j ⊞ L.X i`; composing
Mathlib's `HomologicalComplex.homotopyCofiber.XIsoBiprod` with `ModuleCat.biprodIsoProd` gives the
linear equivalence `HomologicalComplex.homotopyCofiber.XEquiv` with `L.X i × K.X j`, whose
coordinates are the projections `sndX` and `fstX`. On elements, these projections are left
inverses of the inclusions `inrX` and `inlX` and vanish on the other inclusion
(`HomologicalComplex.homotopyCofiber.inrX_sndX_apply`,
`HomologicalComplex.homotopyCofiber.inlX_fstX_apply`), so `inrX` is injective, and the
differential of the cone is `d (inrX x) = inrX (d x)` and `d (inlX x) = -inlX (d x) + inrX (φ x)`
(`HomologicalComplex.homotopyCofiber.inrX_d_apply`,
`HomologicalComplex.homotopyCofiber.inlX_d_apply`); where the differential of `K` vanishes, the
latter is `d (inlX x) = inrX (φ x)`
(`HomologicalComplex.homotopyCofiber.inlX_d_apply_of_d_eq_zero`).

For chain complexes indexed by `ℤ`, bases of `K` and `L` give the mapping cone the basis
`HomologicalComplex.homotopyCofiber.basis`: the basis of `L.X i` followed by that of
`K.X (i - 1)`. The determinant in this basis of a family made of vectors of `L.X i` followed by
vectors of `K.X (i - 1)` is the product of the determinants of the two blocks
(`HomologicalComplex.homotopyCofiber.basis_det_eq_mul`).

The mapping cone of `K ⟶ 0` is `K` shifted by one degree: its terms are identified with those of
`K` by `HomologicalComplex.homotopyCofiber.zeroEquiv`, under which its differentials become the
negatives of those of `K` (`HomologicalComplex.homotopyCofiber.zeroEquiv_d`).
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

/-- The projection `sndX` is a left inverse of the inclusion `inrX`. -/
@[simp]
theorem inrX_sndX_apply (i : ι) (x : L.X i) : (sndX φ i).hom ((inrX φ i).hom x) = x :=
  congr(($(inrX_sndX φ i)).hom x)

/-- The projection `fstX` vanishes on the image of the inclusion `inrX`. -/
@[simp]
theorem inrX_fstX_apply {i j : ι} (hij : c.Rel i j) (x : L.X i) :
    (fstX φ i j hij).hom ((inrX φ i).hom x) = 0 :=
  congr(($(inrX_fstX φ i j hij)).hom x)

/-- The projection `fstX` is a left inverse of the inclusion `inlX`. -/
@[simp]
theorem inlX_fstX_apply {i j : ι} (hij : c.Rel i j) (x : K.X j) :
    (fstX φ i j hij).hom ((inlX φ j i hij).hom x) = x :=
  congr(($(inlX_fstX φ j i hij)).hom x)

/-- The projection `sndX` vanishes on the image of the inclusion `inlX`. -/
@[simp]
theorem inlX_sndX_apply {i j : ι} (hij : c.Rel i j) (x : K.X j) :
    (sndX φ i).hom ((inlX φ j i hij).hom x) = 0 :=
  congr(($(inlX_sndX φ j i hij)).hom x)

/-- The inverse of `XEquiv` is the sum of the inclusions `inrX` and `inlX`. -/
@[simp]
theorem XEquiv_symm_apply {i j : ι} (hij : c.Rel i j) (y : L.X i × K.X j) :
    (XEquiv φ hij).symm y = (inrX φ i).hom y.1 + (inlX φ j i hij).hom y.2 := by
  rw [LinearEquiv.symm_apply_eq]
  simp

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

/-- The inclusion `inrX` of `L.X i` into the mapping cone is injective. -/
theorem inrX_hom_injective (i : ι) : Function.Injective (inrX φ i).hom :=
  Function.LeftInverse.injective (inrX_sndX_apply φ i)

/-- The differential of the mapping cone on an element of `L`. -/
@[simp]
theorem inrX_d_apply (i j : ι) (x : L.X i) :
    (d φ i j).hom ((inrX φ i).hom x) = (inrX φ j).hom ((L.d i j).hom x) :=
  congr(($(inrX_d φ i j)).hom x)

/-- The differential of the mapping cone on an element of `K`. -/
theorem inlX_d_apply {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) (x : K.X j) :
    (d φ i j).hom ((inlX φ j i hij).hom x) =
      -(inlX φ k j hjk).hom ((K.d j k).hom x) + (inrX φ j).hom ((φ.f j).hom x) :=
  congr(($(inlX_d φ i j k hij hjk)).hom x)

/-- The differential of the mapping cone on an element of `K` in a degree where the differential
of `K` vanishes: it is `φ` followed by the inclusion of `L`. -/
theorem inlX_d_apply_of_d_eq_zero {i j : ι} (hij : c.Rel i j) (hK : K.d j (c.next j) = 0)
    (x : K.X j) : (d φ i j).hom ((inlX φ j i hij).hom x) = (inrX φ j).hom ((φ.f j).hom x) := by
  by_cases hj : c.Rel j (c.next j)
  · rw [inlX_d_apply φ hij hj, hK]
    simp
  · exact congr(($(inlX_d' φ i j hij hj)).hom x)

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

section Det

variable {S : Type*} [CommRing S] {K L : ChainComplex (ModuleCat S) ℤ} (φ : K ⟶ L)
  {nK nL : ℤ → ℕ} (cK : ∀ i, Basis (Fin (nK i)) S (K.X i))
  (cL : ∀ i, Basis (Fin (nL i)) S (L.X i))

/-- The determinant, in the basis `homotopyCofiber.basis` of the mapping cone, of a family whose
first `nL i` members come from `L.X i` and whose last `nK (i - 1)` members come from
`K.X (i - 1)` is the product of the determinants of the two blocks. -/
theorem basis_det_eq_mul (i : ℤ) (w : Fin (nL i + nK (i - 1)) → (homotopyCofiber φ).X i)
    (u : Fin (nL i) → L.X i) (v : Fin (nK (i - 1)) → K.X (i - 1))
    (hu : ∀ k, w (Fin.castAdd _ k) = (inrX φ i).hom (u k))
    (hv : ∀ k, w (Fin.natAdd _ k) = (inlX φ (i - 1) i (by simp)).hom (v k)) :
    (basis φ cK cL i).det w = (cL i).det u * (cK (i - 1)).det v := by
  rw [basis, Basis.det_reindex, Basis.det_map, ← Basis.prod_det_sumElim]
  congr 1
  ext (k | k) <;> simp [hu, hv]

end Det

end HomologicalComplex.homotopyCofiber
