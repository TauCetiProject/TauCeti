/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Tensor products of regular-form classes

The tensor product of diagonal forms is diagonal: if `p` has weights `a i` and `q` has weights
`b j`, their tensor product has weights `a i * b j`. This file packages that operation on
`TauCeti.RegularFormPresentation`, proves that it presents Mathlib's
`QuadraticForm.tmul`, and descends it to isometry classes.

Tensor product makes `TauCeti.RegularFormClass K` a commutative monoid. Together with the
orthogonal-sum structure from `TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic`, this
is the multiplicative half of the semiring whose additive group completion underlies the
Witt--Grothendieck ring.

## Main definitions

* `TauCeti.RegularFormPresentation.tmul`: the diagonal presentation of a tensor product.
* `TauCeti.presentedFormTensorIsometryEquiv`: its comparison with `QuadraticForm.tmul`.

## Main results

* `TauCeti.RegularFormClass.mk_mul_mk`: multiplication computes by tensoring presentations.
* `TauCeti.formClass_tmul`: the class of a tensor product is the product of the classes.
* `TauCeti.RegularFormClass.rank_mul`: rank is multiplicative.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §1.
-/

public section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {K : Type u} [Field K]

/-! ### Tensor products of presentations -/

/-- The diagonal presentation of the tensor product of two presented forms. Its weights are all
pairwise products of a weight from each factor. -/
def RegularFormPresentation.tmul (p q : RegularFormPresentation K) :
    RegularFormPresentation K :=
  ⟨p.1 * q.1, fun k => p.2 (finProdFinEquiv.symm k).1 * q.2 (finProdFinEquiv.symm k).2⟩

/-- Tensor product multiplies the ranks of presentations. -/
@[simp]
theorem RegularFormPresentation.fst_tmul (p q : RegularFormPresentation K) :
    (p.tmul q).1 = p.1 * q.1 := (rfl)

/-- A tensor-product weight is the product of the corresponding weights of its factors. -/
@[simp]
theorem RegularFormPresentation.tmul_apply (p q : RegularFormPresentation K)
    (i : Fin p.1) (j : Fin q.1) :
    (p.tmul q).2
      (Fin.cast (RegularFormPresentation.fst_tmul p q).symm (finProdFinEquiv (i, j))) =
        p.2 i * q.2 j := by
  simp [RegularFormPresentation.tmul]

variable [Invertible (2 : K)]

private theorem associated_presentedForm_basisFun (p : RegularFormPresentation K)
    (i j : Fin p.1) :
    associated (R := K) (presentedForm p) (Pi.basisFun K (Fin p.1) i)
        (Pi.basisFun K (Fin p.1) j) = if i = j then (p.2 i : K) else 0 := by
  classical
  by_cases h : i = j
  · subst j
    rw [QuadraticMap.associated_eq_self_apply]
    rw [presentedForm_apply, Finset.sum_eq_single i]
    · simp [Pi.basisFun_apply]
    · intro j _ hji
      simp [Pi.basisFun_apply, hji]
    · simp
  · have hsum :
        (∑ x, (p.2 x : K) *
          ((Pi.basisFun K (Fin p.1) i x + Pi.basisFun K (Fin p.1) j x) *
            (Pi.basisFun K (Fin p.1) i x + Pi.basisFun K (Fin p.1) j x))) -
            (∑ x, (p.2 x : K) *
              (Pi.basisFun K (Fin p.1) i x * Pi.basisFun K (Fin p.1) i x)) -
            (∑ x, (p.2 x : K) *
              (Pi.basisFun K (Fin p.1) j x * Pi.basisFun K (Fin p.1) j x)) = 0 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : k = i
      · subst k
        simp [Pi.basisFun_apply, h]
      · by_cases hkj : k = j
        · subst k
          simp [Pi.basisFun_apply, hki]
        · simp [Pi.basisFun_apply, hki, hkj]
    rw [QuadraticMap.associated_apply]
    simp only [Module.End.smul_def, presentedForm_apply]
    have hsum' :
        (∑ x, (p.2 x : K) *
          ((Pi.basisFun K (Fin p.1) i + Pi.basisFun K (Fin p.1) j) x *
            (Pi.basisFun K (Fin p.1) i + Pi.basisFun K (Fin p.1) j) x)) -
            (∑ x, (p.2 x : K) *
              (Pi.basisFun K (Fin p.1) i x * Pi.basisFun K (Fin p.1) i x)) -
            (∑ x, (p.2 x : K) *
              (Pi.basisFun K (Fin p.1) j x * Pi.basisFun K (Fin p.1) j x)) = 0 := by
      simpa only [Pi.add_apply] using hsum
    rw [hsum']
    simp [h]

private theorem presentedForm_basisFun (p : RegularFormPresentation K) (i : Fin p.1) :
    presentedForm p (Pi.basisFun K (Fin p.1) i) = (p.2 i : K) := by
  rw [← QuadraticMap.associated_eq_self_apply (S := K),
    associated_presentedForm_basisFun]
  simp

/-- The product indexing of tensor weights, transported to the first projection of the sigma
presentation. -/
private def presentedFormTensorIndexEquiv (p q : RegularFormPresentation K) :
    Fin p.1 × Fin q.1 ≃ Fin (p.tmul q).1 :=
  finProdFinEquiv.trans (finCongr (RegularFormPresentation.fst_tmul p q).symm)

/-- The tensor-product basis of the coordinate spaces, indexed by the tensor presentation. -/
private noncomputable def presentedFormTensorBasis (p q : RegularFormPresentation K) :
    Module.Basis (Fin (p.tmul q).1) K ((Fin p.1 → K) ⊗[K] (Fin q.1 → K)) :=
  ((Pi.basisFun K (Fin p.1)).tensorProduct (Pi.basisFun K (Fin q.1))).reindex
    (presentedFormTensorIndexEquiv p q)

private theorem presentedFormTensorBasis_isOrtho (p q : RegularFormPresentation K) :
    (associated (R := K) ((presentedForm p).tmul (presentedForm q))).IsOrthoᵢ
      (presentedFormTensorBasis p q) := by
  intro i j hij
  simp only [Function.onFun, QuadraticForm.associated_tmul, presentedFormTensorBasis,
    Module.Basis.reindex_apply]
  rw [Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply',
    LinearMap.BilinForm.tensorDistrib_tmul]
  rw [associated_presentedForm_basisFun, associated_presentedForm_basisFun]
  split_ifs with h₁ h₂
  · exfalso
    apply hij
    apply (presentedFormTensorIndexEquiv p q).symm.injective
    exact Prod.ext h₂ h₁
  all_goals simp

/-- Tensoring two diagonal presentations presents the tensor product of their quadratic forms. -/
noncomputable def presentedFormTensorIsometryEquiv (p q : RegularFormPresentation K) :
    ((presentedForm p).tmul (presentedForm q)).IsometryEquiv (presentedForm (p.tmul q)) := by
  let b := presentedFormTensorBasis (K := K) p q
  let e := ((presentedForm p).tmul (presentedForm q)).isometryEquivBasisRepr b
  have hb := presentedFormTensorBasis_isOrtho p q
  have hform : ((presentedForm p).tmul (presentedForm q)).basisRepr b =
      presentedForm (p.tmul q) := by
    rw [QuadraticMap.basisRepr_eq_of_iIsOrtho _ _ hb]
    apply QuadraticMap.ext
    intro x
    rw [weightedSumSquares_apply, presentedForm_apply]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    let e := presentedFormTensorIndexEquiv p q
    have hk' : k = e (e.symm k) := (e.apply_symm_apply k).symm
    rw [hk']
    rcases e.symm k with ⟨i, j⟩
    simp only [presentedFormTensorBasis, Module.Basis.reindex_apply,
      Module.Basis.tensorProduct_apply',
      QuadraticForm.tensorDistrib_tmul]
    rw [presentedForm_basisFun, presentedForm_basisFun]
    simp [e, presentedFormTensorIndexEquiv, RegularFormPresentation.tmul_apply,
      smul_eq_mul, mul_comm]
  exact ⟨e.toLinearEquiv, fun x => hform ▸ e.map_app x⟩

/-- The comparison isometry sends a pure tensor to the corresponding products of coordinates. -/
@[simp]
theorem presentedFormTensorIsometryEquiv_tmul_apply (p q : RegularFormPresentation K)
    (x : Fin p.1 → K) (y : Fin q.1 → K) (i : Fin p.1) (j : Fin q.1) :
    presentedFormTensorIsometryEquiv p q (x ⊗ₜ[K] y)
      (Fin.cast (RegularFormPresentation.fst_tmul p q).symm (finProdFinEquiv (i, j))) =
        x i * y j := by
  change (presentedFormTensorBasis p q).repr (x ⊗ₜ[K] y)
    (Fin.cast (RegularFormPresentation.fst_tmul p q).symm (finProdFinEquiv (i, j))) = _
  simp [presentedFormTensorBasis, presentedFormTensorIndexEquiv, smul_eq_mul, mul_comm]

/-! ### Multiplication of isometry classes -/

/-- The form presented by tensoring two presentations is isometric to the tensor product of the
forms they present. -/
theorem equivalent_presentedForm_tmul (p q : RegularFormPresentation K) :
    (presentedForm (p.tmul q)).Equivalent ((presentedForm p).tmul (presentedForm q)) :=
  ⟨(presentedFormTensorIsometryEquiv p q).symm⟩

/-- Tensoring presentations respects isometry in each argument. -/
theorem presentedForm_tmul_congr {p p' q q' : RegularFormPresentation K}
    (hp : (presentedForm p).Equivalent (presentedForm p'))
    (hq : (presentedForm q).Equivalent (presentedForm q')) :
    (presentedForm (p.tmul q)).Equivalent (presentedForm (p'.tmul q')) :=
  (equivalent_presentedForm_tmul p q).trans
    ((hp.tmul hq).trans (equivalent_presentedForm_tmul p' q').symm)

/-- Tensoring presentations is commutative up to isometry. -/
theorem presentedForm_tmul_comm (p q : RegularFormPresentation K) :
    (presentedForm (p.tmul q)).Equivalent (presentedForm (q.tmul p)) := by
  have hcomm : ((presentedForm p).tmul (presentedForm q)).Equivalent
      ((presentedForm q).tmul (presentedForm p)) :=
    ⟨QuadraticForm.tensorComm (presentedForm p) (presentedForm q)⟩
  exact (equivalent_presentedForm_tmul p q).trans
    (hcomm.trans (equivalent_presentedForm_tmul q p).symm)

/-- Tensoring presentations is associative up to isometry. -/
theorem presentedForm_tmul_assoc (p q r : RegularFormPresentation K) :
    (presentedForm ((p.tmul q).tmul r)).Equivalent
      (presentedForm (p.tmul (q.tmul r))) := by
  have hassoc : (((presentedForm p).tmul (presentedForm q)).tmul
      (presentedForm r)).Equivalent
        ((presentedForm p).tmul ((presentedForm q).tmul (presentedForm r))) :=
    ⟨QuadraticForm.tensorAssoc (presentedForm p) (presentedForm q) (presentedForm r)⟩
  exact (equivalent_presentedForm_tmul (p.tmul q) r).trans
    (((equivalent_presentedForm_tmul p q).tmul (QuadraticMap.Equivalent.refl _)).trans
      (hassoc.trans
        (((QuadraticMap.Equivalent.refl _).tmul
            (equivalent_presentedForm_tmul q r).symm).trans
          (equivalent_presentedForm_tmul p (q.tmul r)).symm)))

/-- The rank-one presentation with weight one. -/
def RegularFormPresentation.one : RegularFormPresentation K := ⟨1, fun _ => 1⟩

omit [Invertible (2 : K)] in
/-- The unit presentation has rank one. -/
@[simp]
theorem RegularFormPresentation.fst_one :
    (RegularFormPresentation.one (K := K)).1 = 1 := (rfl)

omit [Invertible (2 : K)] in
/-- The sole weight of the unit presentation is one. -/
@[simp]
theorem RegularFormPresentation.one_apply
    (i : Fin (RegularFormPresentation.one (K := K)).1) :
    (RegularFormPresentation.one (K := K)).2 i = 1 := (rfl)

/-- The rank-one presentation with weight one presents the square form. -/
noncomputable def presentedFormOneIsometryEquiv :
    (presentedForm (RegularFormPresentation.one (K := K))).IsometryEquiv
      (QuadraticMap.sq (R := K)) where
  toLinearEquiv := LinearEquiv.funUnique (Fin 1) K K
  map_app' x := by
    unfold RegularFormPresentation.one at x ⊢
    rw [presentedForm_apply, QuadraticMap.sq_apply]
    convert (Fin.sum_univ_one fun i : Fin 1 => x i * x i).symm using 1 <;> simp

omit [Invertible (2 : K)] in
/-- The comparison from the unit presentation to the square form evaluates its sole coordinate. -/
@[simp]
theorem presentedFormOneIsometryEquiv_apply
    (x : Fin (RegularFormPresentation.one (K := K)).1 → K) :
    presentedFormOneIsometryEquiv x =
      x (Fin.cast RegularFormPresentation.fst_one.symm 0) := (rfl)

/-- Tensoring a presentation on the right with the rank-one presentation preserves its form up
to isometry. -/
theorem presentedForm_tmul_one (p : RegularFormPresentation K) :
    (presentedForm (p.tmul (RegularFormPresentation.one (K := K)))).Equivalent
      (presentedForm p) :=
  (equivalent_presentedForm_tmul p RegularFormPresentation.one).trans
    ((((QuadraticMap.Equivalent.refl _).tmul ⟨presentedFormOneIsometryEquiv⟩).trans
      ⟨QuadraticForm.tensorRId (presentedForm p)⟩))

/-- Tensor product of isometry classes. -/
instance : Mul (RegularFormClass K) :=
  ⟨Quotient.map₂ RegularFormPresentation.tmul fun _ _ hp _ _ hq =>
    presentedForm_tmul_congr hp hq⟩

/-- The class of the rank-one form with coefficient one. -/
instance : One (RegularFormClass K) :=
  ⟨Quotient.mk _ (RegularFormPresentation.one (K := K))⟩

/-- The product of two classes is represented by pairwise products of their weights. -/
@[simp]
theorem RegularFormClass.mk_mul_mk (p q : RegularFormPresentation K) :
    Quotient.mk (regularFormSetoid K) p * Quotient.mk (regularFormSetoid K) q =
      Quotient.mk (regularFormSetoid K) (p.tmul q) := rfl

omit [Invertible (2 : K)] in
/-- The multiplicative unit is represented by the rank-one presentation with weight one. -/
theorem RegularFormClass.one_def :
    (1 : RegularFormClass K) =
      Quotient.mk (regularFormSetoid K) (RegularFormPresentation.one (K := K)) := rfl

/-- Tensor product makes regular-form classes a commutative monoid. -/
instance : CommMonoid (RegularFormClass K) where
  mul_assoc x y z := by
    refine Quotient.inductionOn₃ x y z fun p q r => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr (presentedForm_tmul_assoc p q r)
  one_mul x := by
    refine Quotient.inductionOn x fun p => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr
      ((presentedForm_tmul_comm RegularFormPresentation.one p).trans
        (presentedForm_tmul_one p))
  mul_one x := by
    refine Quotient.inductionOn x fun p => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr (presentedForm_tmul_one p)
  mul_comm x y := by
    refine Quotient.inductionOn₂ x y fun p q => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr (presentedForm_tmul_comm p q)

/-- Rank is multiplicative on tensor products of classes. -/
@[simp]
theorem RegularFormClass.rank_mul (x y : RegularFormClass K) :
    RegularFormClass.rank (x * y) = RegularFormClass.rank x * RegularFormClass.rank y := by
  refine Quotient.inductionOn₂ x y fun p q => ?_
  rw [RegularFormClass.mk_mul_mk, RegularFormClass.rank_mk, RegularFormClass.rank_mk,
    RegularFormClass.rank_mk, RegularFormPresentation.fst_tmul]

omit [Invertible (2 : K)] in
/-- The multiplicative unit has rank one. -/
@[simp]
theorem RegularFormClass.rank_one : RegularFormClass.rank (1 : RegularFormClass K) = 1 := by
  rw [RegularFormClass.one_def, RegularFormClass.rank_mk]
  rfl

/-! ### The class of a tensor product -/

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The tensor product of two regular finite-dimensional quadratic forms is regular. -/
theorem _root_.QuadraticMap.Nondegenerate.tmul {Q : QuadraticForm K V}
    {R : QuadraticForm K W} (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    (Q.tmul R).Nondegenerate := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  obtain ⟨q, hq⟩ := exists_presentedForm_equivalent R hR
  have h : (Q.tmul R).Equivalent (presentedForm (p.tmul q)) :=
    (hp.tmul hq).trans (equivalent_presentedForm_tmul p q).symm
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero,
    h.rank_radical_eq, Submodule.finrank_eq_zero]
  exact (nondegenerate_presentedForm (p.tmul q)).radical_eq_bot

/-- The class of a tensor product is the product of the classes of its factors. -/
@[simp]
theorem formClass_tmul (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (R : QuadraticForm K W) (hR : R.Nondegenerate) :
    formClass (Q.tmul R) (hQ.tmul hR) = formClass Q hQ * formClass R hR := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  obtain ⟨q, hq⟩ := exists_presentedForm_equivalent R hR
  rw [formClass_mk Q hQ p hp, formClass_mk R hR q hq,
    RegularFormClass.mk_mul_mk,
    formClass_mk _ _ (p.tmul q)
      ((hp.tmul hq).trans (equivalent_presentedForm_tmul p q).symm)]

end TauCeti
