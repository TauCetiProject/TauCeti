/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange

/-!
# Transport of regular-form isometry classes along field isomorphisms

A ring isomorphism `e : K ≃+* L` of fields, in any two universes, maps a diagonal presentation
over `K` to the presentation over `L` of the same rank whose weights are the images of the
original weights under `e`, with inverse given by `e.symm`. When `2` is invertible in both fields,
scalar extension along `e` and along `e.symm` are mutually inverse semiring homomorphisms on
isometry classes, packaged as `TauCeti.RegularFormClass.mapRingEquiv e`.

Unlike `TauCeti.RegularFormClass.baseChange`, this equivalence takes the isomorphism explicitly and
needs no ambient `Algebra K L` instance, which makes it usable directly along completion
isomorphisms such as `adicCompletionCongr`. When an `Algebra K L` structure is present and
`algebraMap K L` is surjective (hence bijective), `RegularFormClass.baseChange L` agrees with
`mapRingEquiv` for `RingEquiv.ofBijective (algebraMap K L)` and is therefore bijective.

## Main definitions

* `TauCeti.RegularFormPresentation.equivOfRingEquiv`: the equivalence of diagonal presentations
  induced by a ring isomorphism of fields.
* `TauCeti.RegularFormClass.mapRingEquiv`: the semiring isomorphism of regular-form isometry
  classes induced by a ring isomorphism of fields in which `2` is invertible.

## Main results

* `TauCeti.RegularFormPresentation.equivOfRingEquiv_refl`,
  `TauCeti.RegularFormPresentation.equivOfRingEquiv_symm`,
  `TauCeti.RegularFormPresentation.equivOfRingEquiv_trans`: identity, inverse, and composition
  laws on presentations.
* `TauCeti.RegularFormPresentation.equivOfRingEquiv_baseChange`: naturality with respect to
  scalar extension in a commutative square of field homomorphisms.
* `TauCeti.RegularFormClass.mapRingEquiv_refl`, `TauCeti.RegularFormClass.mapRingEquiv_symm`,
  `TauCeti.RegularFormClass.mapRingEquiv_trans`: identity, inverse, and composition laws on
  classes.
* `TauCeti.RegularFormClass.baseChange_bijective_of_surjective`,
  `TauCeti.RegularFormClass.baseChange_injective_of_surjective`,
  `TauCeti.RegularFormClass.baseChange_inj_of_surjective`: scalar extension along a surjective field
  homomorphism is bijective on regular-form classes.
* `TauCeti.RegularFormClass.rank_mapRingEquiv`,
  `TauCeti.RegularFormClass.mapRingEquiv_hyperbolicClass`,
  `TauCeti.RegularFormClass.discr_mapRingEquiv`,
  `TauCeti.RegularFormClass.signedDiscr_mapRingEquiv`: behaviour of rank, the hyperbolic plane,
  and the plain and signed discriminants under transport.
* `TauCeti.RegularFormClass.mapRingEquiv_baseChange`: naturality of class transport with respect to
  scalar extension in a commutative square of field homomorphisms.
* `TauCeti.formClass_eq_mapRingEquiv_of_semilinearEquiv`,
  `TauCeti.discr_formClass_of_semilinearEquiv`,
  `TauCeti.signedDiscr_formClass_of_semilinearEquiv`: the isometry class and discriminants of a
  regular form transported along a semilinear equivalence over a field isomorphism.
-/

public section
noncomputable section

namespace TauCeti

universe u v w

/-! ### Transport of diagonal presentations -/

section Presentation

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Field M]

/-- The equivalence of diagonal presentations induced by a ring isomorphism `e : K ≃+* L`, mapping
every weight by `Units.map e` and preserving the rank. -/
def RegularFormPresentation.equivOfRingEquiv (e : K ≃+* L) :
    RegularFormPresentation K ≃ RegularFormPresentation L where
  toFun :=
    letI : Algebra K L := e.toRingHom.toAlgebra
    RegularFormPresentation.baseChange L
  invFun :=
    letI : Algebra L K := e.symm.toRingHom.toAlgebra
    RegularFormPresentation.baseChange K
  left_inv p := by
    let _ : Algebra K L := e.toRingHom.toAlgebra
    let _ : Algebra L K := e.symm.toRingHom.toAlgebra
    have : IsScalarTower K L K := IsScalarTower.of_algebraMap_eq fun x ↦ by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.algebraMap_toAlgebra,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using (e.symm_apply_apply x).symm
    exact (RegularFormPresentation.baseChange_baseChange L K p).trans
      (RegularFormPresentation.baseChange_self p)
  right_inv q := by
    let _ : Algebra K L := e.toRingHom.toAlgebra
    let _ : Algebra L K := e.symm.toRingHom.toAlgebra
    have : IsScalarTower L K L := IsScalarTower.of_algebraMap_eq fun y ↦ by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.algebraMap_toAlgebra,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using (e.apply_symm_apply y).symm
    exact (RegularFormPresentation.baseChange_baseChange K L q).trans
      (RegularFormPresentation.baseChange_self q)

private theorem RegularFormPresentation.equivOfRingEquiv_eq_toAlgebra_baseChange (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    RegularFormPresentation.equivOfRingEquiv e p = RegularFormPresentation.baseChange L p :=
  (rfl)

/-- Transporting a presentation along `e` keeps its rank and maps its weights by `Units.map e`. -/
theorem RegularFormPresentation.equivOfRingEquiv_def (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e p =
      ⟨p.1, fun i ↦ Units.map (e : K →* L) (p.2 i)⟩ := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormPresentation.equivOfRingEquiv_eq_toAlgebra_baseChange,
    RegularFormPresentation.baseChange_def]
  rfl

/-- Transporting a presentation along `e` leaves its rank unchanged. -/
@[simp]
theorem RegularFormPresentation.fst_equivOfRingEquiv (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    (RegularFormPresentation.equivOfRingEquiv e p).1 = p.1 := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact RegularFormPresentation.fst_baseChange L p

/-- Each weight of the transported presentation is the image under `e` of the weight of `p` at the
same index, read through `TauCeti.RegularFormPresentation.fst_equivOfRingEquiv`. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_apply (e : K ≃+* L)
    (p : RegularFormPresentation K)
    (i : Fin (RegularFormPresentation.equivOfRingEquiv e p).1) :
    (RegularFormPresentation.equivOfRingEquiv e p).2 i =
      Units.map (e : K →* L)
        (p.2 (Fin.cast (RegularFormPresentation.fst_equivOfRingEquiv e p) i)) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact RegularFormPresentation.baseChange_apply L p i

/-- When an `Algebra K L` structure agrees with `e`, presentation transport agrees with
`RegularFormPresentation.baseChange`. -/
theorem RegularFormPresentation.equivOfRingEquiv_eq_baseChange [Algebra K L] (e : K ≃+* L)
    (he : ∀ x, algebraMap K L x = e x) (p : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e p = RegularFormPresentation.baseChange L p := by
  refine RegularFormPresentation.ext (by simp) fun i ↦ Units.ext ?_
  rw [RegularFormPresentation.baseChange_apply, RegularFormPresentation.equivOfRingEquiv_apply]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, he]
  exact congrArg (fun j : Fin p.1 ↦ e (p.2 j : K)) (Fin.ext (by simp))

-- Not `@[simp]`: `RegularFormPresentation.equivOfRingEquiv_apply` rewrites inside the product, so
-- the left-hand side is not in `simp`-normal form.
/-- The weight product of a transported presentation is the image of the original weight product. -/
theorem RegularFormPresentation.prod_equivOfRingEquiv (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    (∏ i, (RegularFormPresentation.equivOfRingEquiv e p).2 i) =
      Units.map (e : K →* L) (∏ i, p.2 i) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact RegularFormPresentation.prod_baseChange L p

/-- Transporting presentations along the identity ring isomorphism is the identity equivalence. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_refl :
    RegularFormPresentation.equivOfRingEquiv (RingEquiv.refl K) = Equiv.refl _ := by
  ext1 p
  exact RegularFormPresentation.equivOfRingEquiv_eq_baseChange (RingEquiv.refl K) (fun _ ↦ rfl) p
    |>.trans (RegularFormPresentation.baseChange_self p)

/-- Inverting presentation transport corresponds to inverting the field isomorphism. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_symm (e : K ≃+* L) :
    (RegularFormPresentation.equivOfRingEquiv e).symm =
      RegularFormPresentation.equivOfRingEquiv e.symm :=
  Equiv.ext fun _ ↦ rfl

/-- Transporting presentations along two field isomorphisms in succession agrees with transport
along their composite. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    (RegularFormPresentation.equivOfRingEquiv e).trans
        (RegularFormPresentation.equivOfRingEquiv f) =
      RegularFormPresentation.equivOfRingEquiv (e.trans f) := by
  ext1 p
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let _ : Algebra L M := f.toRingHom.toAlgebra
  let _ : Algebra K M := (e.trans f).toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  exact RegularFormPresentation.baseChange_baseChange L M p

/-- Applying successive presentation transports computes transport along the composite
isomorphism. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_trans_apply (e : K ≃+* L) (f : L ≃+* M)
    (p : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv f (RegularFormPresentation.equivOfRingEquiv e p) =
      RegularFormPresentation.equivOfRingEquiv (e.trans f) p := by
  rw [← Equiv.trans_apply, RegularFormPresentation.equivOfRingEquiv_trans]

/-- Presentation transport fixes the rank-one presentation with weight one. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_one (e : K ≃+* L) :
    RegularFormPresentation.equivOfRingEquiv e (RegularFormPresentation.one (K := K)) =
      RegularFormPresentation.one := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact RegularFormPresentation.baseChange_one L

/-- Presentation transport commutes with concatenation of presentations. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_append (e : K ≃+* L)
    (p q : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e (p.append q) =
      (RegularFormPresentation.equivOfRingEquiv e p).append
        (RegularFormPresentation.equivOfRingEquiv e q) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact RegularFormPresentation.baseChange_append L p q

/-- Presentation transport commutes with the tensor product of presentations. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_tmul (e : K ≃+* L)
    (p q : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e (p.tmul q) =
      (RegularFormPresentation.equivOfRingEquiv e p).tmul
        (RegularFormPresentation.equivOfRingEquiv e q) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  exact RegularFormPresentation.baseChange_tmul L p q

/-- In a commutative square of field homomorphisms with horizontal isomorphisms `e` and `e'`,
presentation transport commutes with scalar extension. -/
theorem RegularFormPresentation.equivOfRingEquiv_baseChange
    {K' L' : Type*} [Field K'] [Field L'] [Algebra K K'] [Algebra L L']
    (e : K ≃+* L) (e' : K' ≃+* L')
    (hcomm : ∀ a : K, e' (algebraMap K K' a) = algebraMap L L' (e a))
    (p : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e' (RegularFormPresentation.baseChange K' p) =
      RegularFormPresentation.baseChange L' (RegularFormPresentation.equivOfRingEquiv e p) := by
  refine RegularFormPresentation.ext (by simp) fun i ↦ Units.ext ?_
  rw [RegularFormPresentation.baseChange_apply, RegularFormPresentation.equivOfRingEquiv_apply,
    RegularFormPresentation.equivOfRingEquiv_apply, RegularFormPresentation.baseChange_apply]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hcomm]
  exact congrArg (fun j : Fin p.1 ↦ algebraMap L L' (e (p.2 j : K))) (Fin.ext (by simp))

end Presentation

/-! ### Transport of isometry classes -/

section Class

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Field M]
variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- **Transport of regular-form isometry classes along a ring isomorphism of fields**, as an
isomorphism of commutative semirings. -/
def RegularFormClass.mapRingEquiv (e : K ≃+* L) :
    RegularFormClass K ≃+* RegularFormClass L :=
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Algebra L K := e.symm.toRingHom.toAlgebra
  { RegularFormClass.baseChangeHom (K := K) (L := L) with
    invFun := RegularFormClass.baseChange K
    left_inv := fun x ↦ by
      have : IsScalarTower K L K := IsScalarTower.of_algebraMap_eq fun a ↦ by
        simpa only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.algebraMap_toAlgebra,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using (e.symm_apply_apply a).symm
      rw [RingHom.toFun_eq_coe, RegularFormClass.baseChangeHom_apply]
      exact (RegularFormClass.baseChange_baseChange L K x).trans
        (RegularFormClass.baseChange_self x)
    right_inv := fun y ↦ by
      have : IsScalarTower L K L := IsScalarTower.of_algebraMap_eq fun b ↦ by
        simpa only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.algebraMap_toAlgebra,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using (e.apply_symm_apply b).symm
      rw [RingHom.toFun_eq_coe, RegularFormClass.baseChangeHom_apply]
      exact (RegularFormClass.baseChange_baseChange K L y).trans
        (RegularFormClass.baseChange_self y) }

private theorem RegularFormClass.mapRingEquiv_eq_toAlgebra_baseChange (e : K ≃+* L)
    (x : RegularFormClass K) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    RegularFormClass.mapRingEquiv e x = RegularFormClass.baseChange L x := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv]
  exact RegularFormClass.baseChangeHom_apply x

/-- Class transport is computed on diagonal presentations by
`TauCeti.RegularFormPresentation.equivOfRingEquiv`. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_mk (e : K ≃+* L) (p : RegularFormPresentation K) :
    RegularFormClass.mapRingEquiv e (Quotient.mk (regularFormSetoid K) p) =
      Quotient.mk (regularFormSetoid L) (RegularFormPresentation.equivOfRingEquiv e p) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_toAlgebra_baseChange, RegularFormClass.baseChange_mk,
    RegularFormPresentation.equivOfRingEquiv_eq_toAlgebra_baseChange]

/-- When an `Algebra K L` structure agrees with `e`, `RegularFormClass.mapRingEquiv e` agrees with
`RegularFormClass.baseChange L`. -/
theorem RegularFormClass.mapRingEquiv_eq_baseChange [Algebra K L] (e : K ≃+* L)
    (he : ∀ x, algebraMap K L x = e x) (x : RegularFormClass K) :
    RegularFormClass.mapRingEquiv e x = RegularFormClass.baseChange L x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.mapRingEquiv_mk, RegularFormClass.baseChange_mk,
    RegularFormPresentation.equivOfRingEquiv_eq_baseChange e he]

/-- Scalar extension of regular-form classes along a surjective `algebraMap K L` is transport along
`RingEquiv.ofBijective (algebraMap K L)`. -/
theorem RegularFormClass.baseChange_eq_mapRingEquiv_of_surjective [Algebra K L]
    (h : Function.Surjective (algebraMap K L)) (x : RegularFormClass K) :
    RegularFormClass.baseChange L x =
      RegularFormClass.mapRingEquiv
        (RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, h⟩) x :=
  (RegularFormClass.mapRingEquiv_eq_baseChange
    (RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, h⟩) (fun _ ↦ rfl) x).symm

omit [Invertible (2 : L)] in
/-- Scalar extension of regular-form classes along a surjective field homomorphism is bijective. -/
theorem RegularFormClass.baseChange_bijective_of_surjective [Algebra K L]
    (h : Function.Surjective (algebraMap K L)) :
    Function.Bijective (RegularFormClass.baseChange (K := K) L) := by
  let _ : Invertible (2 : L) :=
    invertibleOfNonzero (by
      rw [← map_ofNat (algebraMap K L) 2, map_ne_zero]
      exact Invertible.ne_zero (2 : K))
  have heq : RegularFormClass.baseChange (K := K) L =
      RegularFormClass.mapRingEquiv
        (RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, h⟩) :=
    funext (RegularFormClass.baseChange_eq_mapRingEquiv_of_surjective h)
  rw [heq]
  exact (RegularFormClass.mapRingEquiv
    (RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, h⟩)).bijective

omit [Invertible (2 : L)] in
/-- Scalar extension of regular-form classes along a surjective field homomorphism is injective. -/
theorem RegularFormClass.baseChange_injective_of_surjective [Algebra K L]
    (h : Function.Surjective (algebraMap K L)) :
    Function.Injective (RegularFormClass.baseChange (K := K) L) :=
  (RegularFormClass.baseChange_bijective_of_surjective h).injective

omit [Invertible (2 : L)] in
/-- Scalar extension along a surjective field homomorphism reflects equality of regular-form
classes. -/
theorem RegularFormClass.baseChange_inj_of_surjective [Algebra K L]
    (h : Function.Surjective (algebraMap K L)) {x y : RegularFormClass K} :
    RegularFormClass.baseChange L x = RegularFormClass.baseChange L y ↔ x = y :=
  (RegularFormClass.baseChange_injective_of_surjective h).eq_iff

/-- Transporting regular-form classes along the identity field isomorphism is the identity
semiring isomorphism. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_refl :
    RegularFormClass.mapRingEquiv (RingEquiv.refl K) = RingEquiv.refl (RegularFormClass K) := by
  ext x
  exact (RegularFormClass.mapRingEquiv_eq_baseChange (RingEquiv.refl K) (fun _ ↦ rfl) x).trans
    (RegularFormClass.baseChange_self x)

/-- Inverting class transport corresponds to inverting the field isomorphism. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_symm (e : K ≃+* L) :
    (RegularFormClass.mapRingEquiv e).symm = RegularFormClass.mapRingEquiv e.symm := by
  ext y
  refine Quotient.inductionOn y fun q ↦ ?_
  rw [RingEquiv.symm_apply_eq, RegularFormClass.mapRingEquiv_mk, RegularFormClass.mapRingEquiv_mk,
    RegularFormPresentation.equivOfRingEquiv_trans_apply]
  simp

/-- Transporting regular-form classes along two field isomorphisms in succession agrees with
transport along their composite. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_trans [Invertible (2 : M)] (e : K ≃+* L) (f : L ≃+* M) :
    (RegularFormClass.mapRingEquiv e).trans (RegularFormClass.mapRingEquiv f) =
      RegularFormClass.mapRingEquiv (e.trans f) := by
  ext x
  refine Quotient.inductionOn x fun p ↦ ?_
  simp

/-- Applying successive class transports computes transport along the composite isomorphism. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_trans_apply [Invertible (2 : M)] (e : K ≃+* L) (f : L ≃+* M)
    (x : RegularFormClass K) :
    RegularFormClass.mapRingEquiv f (RegularFormClass.mapRingEquiv e x) =
      RegularFormClass.mapRingEquiv (e.trans f) x := by
  rw [← RingEquiv.trans_apply, RegularFormClass.mapRingEquiv_trans]

/-- Transport along a field isomorphism preserves the rank of a class. -/
@[simp]
theorem RegularFormClass.rank_mapRingEquiv (e : K ≃+* L) (x : RegularFormClass K) :
    (RegularFormClass.mapRingEquiv e x).rank = x.rank := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_toAlgebra_baseChange]
  exact RegularFormClass.rank_baseChange L x

/-- Transport along a field isomorphism preserves the hyperbolic class. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_hyperbolicClass (e : K ≃+* L) :
    RegularFormClass.mapRingEquiv e (hyperbolicClass K) = hyperbolicClass L := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_toAlgebra_baseChange]
  exact RegularFormClass.baseChange_hyperbolicClass

/-- **The discriminant commutes with transport along a field isomorphism**: transporting a class
along `e` pushes its discriminant forward along `(e : K →+* L).squareClassMap`. -/
@[simp]
theorem RegularFormClass.discr_mapRingEquiv (e : K ≃+* L) (x : RegularFormClass K) :
    RegularFormClass.discr (RegularFormClass.mapRingEquiv e x) =
      (e : K →+* L).squareClassMap (RegularFormClass.discr x) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_toAlgebra_baseChange]
  exact RegularFormClass.discr_baseChange x

/-- **The signed discriminant commutes with transport along a field isomorphism**: transporting a
class along `e` pushes its signed discriminant forward along `(e : K →+* L).squareClassMap`. -/
@[simp]
theorem RegularFormClass.signedDiscr_mapRingEquiv (e : K ≃+* L) (x : RegularFormClass K) :
    RegularFormClass.signedDiscr (RegularFormClass.mapRingEquiv e x) =
      (e : K →+* L).squareClassMap (RegularFormClass.signedDiscr x) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_toAlgebra_baseChange]
  exact RegularFormClass.signedDiscr_baseChange x

/-- In a commutative square of field homomorphisms with horizontal isomorphisms `e : K ≃+* L` and
`e' : K' ≃+* L'`, class transport commutes with scalar extension. -/
theorem RegularFormClass.mapRingEquiv_baseChange
    {K' L' : Type*} [Field K'] [Field L'] [Algebra K K'] [Algebra L L']
    [Invertible (2 : K')] [Invertible (2 : L')]
    (e : K ≃+* L) (e' : K' ≃+* L')
    (hcomm : ∀ a : K, e' (algebraMap K K' a) = algebraMap L L' (e a))
    (x : RegularFormClass K) :
    RegularFormClass.mapRingEquiv e' (RegularFormClass.baseChange K' x) =
      RegularFormClass.baseChange L' (RegularFormClass.mapRingEquiv e x) := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.baseChange_mk, RegularFormClass.mapRingEquiv_mk,
    RegularFormClass.mapRingEquiv_mk, RegularFormClass.baseChange_mk,
    RegularFormPresentation.equivOfRingEquiv_baseChange e e' hcomm]

end Class

/-! ### Semilinearly transported regular forms -/

section FormClass

variable {K : Type u} {L : Type v} [Field K] [Field L]
variable {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable [Invertible (2 : K)] [Invertible (2 : L)]
variable {V : Type*} {W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module L W] [FiniteDimensional L W]

/-- If `f : V ≃ₛₗ[σ] W` intertwines two regular quadratic forms `Q` and `Q'` via
`Q' (f v) = σ (Q v)`, then the isometry class of `Q'` is the transport along
`RingHomInvPair.toRingEquiv σ σ'` of the isometry class of `Q`. -/
theorem formClass_eq_mapRingEquiv_of_semilinearEquiv
    {Q : QuadraticForm K V} {Q' : QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ v, Q' (f v) = σ (Q v)) :
    formClass Q' hQ' =
      RegularFormClass.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ') (formClass Q hQ) := by
  let e : K ≃+* L := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨p, ⟨g⟩⟩ := exists_presentedForm_equivalent Q hQ
  have hcast := RegularFormPresentation.fst_equivOfRingEquiv e p
  let hL : W ≃ₗ[L] (Fin (RegularFormPresentation.equivOfRingEquiv e p).1 → L) :=
    { toFun := fun w i ↦ σ (g (f.symm w) (Fin.cast hcast i))
      map_add' := fun w₁ w₂ ↦ by
        ext i
        simp
      map_smul' := fun c w ↦ by
        ext i
        have hsymm : f.symm (c • w) = σ' c • f.symm w := f.symm.map_smulₛₗ c w
        simp [hsymm]
      invFun := fun y ↦ f (g.symm fun j ↦ σ' (y (Fin.cast hcast.symm j)))
      left_inv := fun w ↦ by
        dsimp only
        have hg : (fun j ↦ σ' (σ (g (f.symm w) (Fin.cast hcast (Fin.cast hcast.symm j))))) =
            g (f.symm w) := by
          ext j
          simp
        rw [hg, g.symm_apply_apply, f.apply_symm_apply]
      right_inv := fun y ↦ by
        ext i
        have hf_symm : f.symm (f (g.symm fun j ↦ σ' (y (Fin.cast hcast.symm j)))) =
            g.symm fun j ↦ σ' (y (Fin.cast hcast.symm j)) :=
          f.symm_apply_apply _
        simp [hf_symm] }
  have hEquiv : Q'.Equivalent (presentedForm (RegularFormPresentation.equivOfRingEquiv e p)) := by
    refine ⟨{ toLinearEquiv := hL, map_app' := fun w ↦ ?_ }⟩
    obtain ⟨v, rfl⟩ := f.surjective w
    have hfv : f.symm (f v) = v := f.symm_apply_apply v
    have hsum :
        presentedForm (RegularFormPresentation.equivOfRingEquiv e p) (hL (f v)) =
          σ (presentedForm p (g v)) := by
      simp only [presentedForm_eq_weightedSumSquares, QuadraticMap.weightedSumSquares_apply,
        Units.smul_def, smul_eq_mul, map_sum, map_mul]
      refine Fintype.sum_equiv (finCongr hcast) _ _ fun i ↦ ?_
      simp [e, hL, hfv]
    change presentedForm (RegularFormPresentation.equivOfRingEquiv e p) (hL (f v)) = Q' (f v)
    rw [hsum, g.map_app v, hf v]
  rw [formClass_mk Q hQ p ⟨g⟩, RegularFormClass.mapRingEquiv_mk, formClass_mk Q' hQ' _ hEquiv]

/-- If `f : V ≃ₛₗ[σ] W` intertwines two regular quadratic forms `Q` and `Q'` via
`Q' (f v) = σ (Q v)`, then the discriminant of `Q'` is the image under `σ` of the discriminant of
`Q`. -/
theorem discr_formClass_of_semilinearEquiv
    {Q : QuadraticForm K V} {Q' : QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ v, Q' (f v) = σ (Q v)) :
    RegularFormClass.discr (formClass Q' hQ') =
      σ.squareClassMap (RegularFormClass.discr (formClass Q hQ)) := by
  rw [formClass_eq_mapRingEquiv_of_semilinearEquiv hQ hQ' f hf, RegularFormClass.discr_mapRingEquiv]
  -- Coercing `RingHomInvPair.toRingEquiv σ σ'` to `K →+* L` reduces definitionally to `σ`.
  rfl

/-- If `f : V ≃ₛₗ[σ] W` intertwines two regular quadratic forms `Q` and `Q'` via
`Q' (f v) = σ (Q v)`, then the signed discriminant of `Q'` is the image under `σ` of the signed
discriminant of `Q`. -/
theorem signedDiscr_formClass_of_semilinearEquiv
    {Q : QuadraticForm K V} {Q' : QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ v, Q' (f v) = σ (Q v)) :
    RegularFormClass.signedDiscr (formClass Q' hQ') =
      σ.squareClassMap (RegularFormClass.signedDiscr (formClass Q hQ)) := by
  rw [formClass_eq_mapRingEquiv_of_semilinearEquiv hQ hQ' f hf,
    RegularFormClass.signedDiscr_mapRingEquiv]
  -- Coercing `RingHomInvPair.toRingEquiv σ σ'` to `K →+* L` reduces definitionally to `σ`.
  rfl

end FormClass

end TauCeti
