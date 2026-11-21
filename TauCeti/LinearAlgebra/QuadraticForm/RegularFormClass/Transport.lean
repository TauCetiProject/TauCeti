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

* `TauCeti.presentedForm_equivOfRingEquiv`: evaluation of a transported presented form on
  coordinatewise images under `e`.
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
  `TauCeti.discr_formClass_eq_squareClassMap_of_semilinearEquiv`,
  `TauCeti.signedDiscr_formClass_eq_squareClassMap_of_semilinearEquiv`: the isometry class and
  discriminants of a regular form transported along a semilinear equivalence over a field
  isomorphism.
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
    RegularFormPresentation K ≃ RegularFormPresentation L :=
  Equiv.sigmaCongrRight fun _ ↦ Equiv.piCongrRight fun _ ↦ (Units.mapEquiv e.toMulEquiv).toEquiv

/-- Transporting a presentation along `e` keeps its rank and maps its weights by `Units.map e`. -/
theorem RegularFormPresentation.equivOfRingEquiv_def (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e p =
      ⟨p.1, fun i ↦ Units.map (e : K →* L) (p.2 i)⟩ := by
  rcases p with ⟨n, w⟩
  rw [RegularFormPresentation.equivOfRingEquiv, Equiv.sigmaCongrRight_apply]
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  apply Units.ext
  simp

/-- Transporting a presentation along `e` leaves its rank unchanged. -/
@[simp]
theorem RegularFormPresentation.fst_equivOfRingEquiv (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    (RegularFormPresentation.equivOfRingEquiv e p).1 = p.1 := by
  simp [RegularFormPresentation.equivOfRingEquiv]

/-- Each weight of the transported presentation is the image under `e` of the weight of `p` at the
same index, read through `TauCeti.RegularFormPresentation.fst_equivOfRingEquiv`. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_apply (e : K ≃+* L)
    (p : RegularFormPresentation K)
    (i : Fin (RegularFormPresentation.equivOfRingEquiv e p).1) :
    (RegularFormPresentation.equivOfRingEquiv e p).2 i =
      Units.map (e : K →* L)
        (p.2 (Fin.cast (RegularFormPresentation.fst_equivOfRingEquiv e p) i)) := by
  have h : ∀ (q : RegularFormPresentation L)
      (hq : q = ⟨p.1, fun j ↦ Units.map (e : K →* L) (p.2 j)⟩) (j : Fin q.1),
      q.2 j = Units.map (e : K →* L)
        (p.2 (Fin.cast (congrArg (fun r : RegularFormPresentation L ↦ r.1) hq) j)) := by
    rintro _ rfl j
    simp
  exact h _ (RegularFormPresentation.equivOfRingEquiv_def e p) i

/-- Evaluating the form presented by `RegularFormPresentation.equivOfRingEquiv e p` on
coordinatewise `e`-images of `x` gives `e (presentedForm p x)`. -/
theorem presentedForm_equivOfRingEquiv (p : RegularFormPresentation K) (e : K ≃+* L)
    (x : Fin p.1 → K) :
    presentedForm (RegularFormPresentation.equivOfRingEquiv e p)
        (fun i ↦ e (x (Fin.cast (RegularFormPresentation.fst_equivOfRingEquiv e p) i))) =
      e (presentedForm p x) := by
  rw [presentedForm_apply, presentedForm_apply, map_sum]
  refine Fintype.sum_equiv (finCongr (RegularFormPresentation.fst_equivOfRingEquiv e p)) _ _
    fun i ↦ ?_
  simp [RegularFormPresentation.equivOfRingEquiv_apply]

/-- When an `Algebra K L` structure agrees with `e`, presentation transport agrees with
`RegularFormPresentation.baseChange`. -/
theorem RegularFormPresentation.equivOfRingEquiv_eq_baseChange [Algebra K L] (e : K ≃+* L)
    (he : ∀ x, algebraMap K L x = e x) (p : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e p = RegularFormPresentation.baseChange L p := by
  refine RegularFormPresentation.ext (by simp) fun i ↦ Units.ext ?_
  rw [RegularFormPresentation.baseChange_apply, RegularFormPresentation.equivOfRingEquiv_apply]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, he]
  exact congrArg (fun j : Fin p.1 ↦ e (p.2 j : K)) (Fin.ext (by simp))

/-- The weight product of a transported presentation is the image of the original weight product. -/
@[simp↓]
theorem RegularFormPresentation.prod_equivOfRingEquiv (e : K ≃+* L)
    (p : RegularFormPresentation K) :
    (∏ i, (RegularFormPresentation.equivOfRingEquiv e p).2 i) =
      Units.map ((e : K →+* L) : K →* L) (∏ i, p.2 i) := by
  rw [RegularFormPresentation.equivOfRingEquiv_def, map_prod]
  exact Units.ext (by simp)

/-- Transporting presentations along the identity ring isomorphism is the identity equivalence. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_refl :
    RegularFormPresentation.equivOfRingEquiv (RingEquiv.refl K) = Equiv.refl _ := by
  ext1 p
  rw [RegularFormPresentation.equivOfRingEquiv_def]
  refine RegularFormPresentation.ext rfl fun i ↦ Units.ext ?_
  simp

/-- Inverting presentation transport corresponds to inverting the field isomorphism. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_symm (e : K ≃+* L) :
    (RegularFormPresentation.equivOfRingEquiv e).symm =
      RegularFormPresentation.equivOfRingEquiv e.symm := by
  ext1 q
  rw [Equiv.symm_apply_eq, RegularFormPresentation.equivOfRingEquiv_def,
    RegularFormPresentation.equivOfRingEquiv_def]
  refine RegularFormPresentation.ext rfl fun i ↦ Units.ext ?_
  simp

/-- Transporting presentations along two field isomorphisms in succession agrees with transport
along their composite. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    (RegularFormPresentation.equivOfRingEquiv e).trans
        (RegularFormPresentation.equivOfRingEquiv f) =
      RegularFormPresentation.equivOfRingEquiv (e.trans f) := by
  ext1 p
  rw [Equiv.trans_apply, RegularFormPresentation.equivOfRingEquiv_def,
    RegularFormPresentation.equivOfRingEquiv_def,
    RegularFormPresentation.equivOfRingEquiv_def]
  refine RegularFormPresentation.ext rfl fun i ↦ Units.ext ?_
  simp

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
  rw [RegularFormPresentation.equivOfRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra])]
  exact RegularFormPresentation.baseChange_one L

/-- Presentation transport commutes with concatenation of presentations. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_append (e : K ≃+* L)
    (p q : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e (p.append q) =
      (RegularFormPresentation.equivOfRingEquiv e p).append
        (RegularFormPresentation.equivOfRingEquiv e q) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  simp_rw [RegularFormPresentation.equivOfRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra])]
  exact RegularFormPresentation.baseChange_append L p q

/-- Presentation transport commutes with the tensor product of presentations. -/
@[simp]
theorem RegularFormPresentation.equivOfRingEquiv_tmul (e : K ≃+* L)
    (p q : RegularFormPresentation K) :
    RegularFormPresentation.equivOfRingEquiv e (p.tmul q) =
      (RegularFormPresentation.equivOfRingEquiv e p).tmul
        (RegularFormPresentation.equivOfRingEquiv e q) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  simp_rw [RegularFormPresentation.equivOfRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra])]
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
  haveI : IsScalarTower K L K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower L K L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  RingEquiv.ofRingHom (RegularFormClass.baseChangeHom (K := K) (L := L))
    (RegularFormClass.baseChangeHom (K := L) (L := K))
    (by rw [RegularFormClass.baseChangeHom_comp, RegularFormClass.baseChangeHom_self])
    (by rw [RegularFormClass.baseChangeHom_comp, RegularFormClass.baseChangeHom_self])

/-- Class transport is computed on diagonal presentations by
`TauCeti.RegularFormPresentation.equivOfRingEquiv`. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_mk (e : K ≃+* L) (p : RegularFormPresentation K) :
    RegularFormClass.mapRingEquiv e (Quotient.mk (regularFormSetoid K) p) =
      Quotient.mk (regularFormSetoid L) (RegularFormPresentation.equivOfRingEquiv e p) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv, RingEquiv.ofRingHom_apply,
    RegularFormClass.baseChangeHom_apply, RegularFormClass.baseChange_mk,
    ← RegularFormPresentation.equivOfRingEquiv_eq_baseChange e
      (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra])]

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
    (RingEquiv.ofBijective (algebraMap K L) ⟨(algebraMap K L).injective, h⟩)
    (fun a ↦ (RingEquiv.ofBijective_apply _ _ a).symm) x).symm

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
  exact (RegularFormClass.mapRingEquiv_eq_baseChange (RingEquiv.refl K) (fun _ ↦ by simp) x).trans
    (RegularFormClass.baseChange_self x)

/-- Inverting class transport corresponds to inverting the field isomorphism. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_symm (e : K ≃+* L) :
    (RegularFormClass.mapRingEquiv e).symm = RegularFormClass.mapRingEquiv e.symm := by
  ext y
  rw [RegularFormClass.mapRingEquiv, RegularFormClass.mapRingEquiv, RingEquiv.ofRingHom_symm,
    RingEquiv.ofRingHom_apply, RingEquiv.ofRingHom_apply]

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
  rw [RegularFormClass.mapRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra])]
  exact RegularFormClass.rank_baseChange L x

/-- Transport along a field isomorphism preserves the hyperbolic class. -/
@[simp]
theorem RegularFormClass.mapRingEquiv_hyperbolicClass (e : K ≃+* L) :
    RegularFormClass.mapRingEquiv e (hyperbolicClass K) = hyperbolicClass L := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra])]
  exact RegularFormClass.baseChange_hyperbolicClass

/-- **The discriminant commutes with transport along a field isomorphism**: transporting a class
along `e` pushes its discriminant forward along `(e : K →+* L).squareClassMap`. -/
@[simp]
theorem RegularFormClass.discr_mapRingEquiv (e : K ≃+* L) (x : RegularFormClass K) :
    RegularFormClass.discr (RegularFormClass.mapRingEquiv e x) =
      (e : K →+* L).squareClassMap (RegularFormClass.discr x) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]),
    RegularFormClass.discr_baseChange, RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe]

/-- **The signed discriminant commutes with transport along a field isomorphism**: transporting a
class along `e` pushes its signed discriminant forward along `(e : K →+* L).squareClassMap`. -/
@[simp]
theorem RegularFormClass.signedDiscr_mapRingEquiv (e : K ≃+* L) (x : RegularFormClass K) :
    RegularFormClass.signedDiscr (RegularFormClass.mapRingEquiv e x) =
      (e : K →+* L).squareClassMap (RegularFormClass.signedDiscr x) := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  rw [RegularFormClass.mapRingEquiv_eq_baseChange e
    (fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]),
    RegularFormClass.signedDiscr_baseChange, RingHom.algebraMap_toAlgebra,
    RingEquiv.toRingHom_eq_coe]

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
  let hAdd : W ≃+ (Fin p.1 → L) :=
    (f.symm.toAddEquiv.trans g.toLinearEquiv.toAddEquiv).trans
      (AddEquiv.piCongrRight fun _ ↦ e.toAddEquiv)
  let hL : W ≃ₗ[L] (Fin (RegularFormPresentation.equivOfRingEquiv e p).1 → L) :=
    ({ hAdd with
      map_smul' := fun c w ↦ by
        ext i
        have hsymm : f.symm (c • w) = σ' c • f.symm w := f.symm.map_smulₛₗ c w
        simp [hAdd, e, hsymm] } : W ≃ₗ[L] (Fin p.1 → L)).trans
      (LinearEquiv.funCongrLeft L L (finCongr (RegularFormPresentation.fst_equivOfRingEquiv e p)))
  have hEquiv : Q'.Equivalent
      (presentedForm (RegularFormPresentation.equivOfRingEquiv e p)) := by
    refine ⟨{ toLinearEquiv := hL, map_app' := fun w ↦ ?_ }⟩
    obtain ⟨v, rfl⟩ := f.surjective w
    have hfv : f.symm (f v) = v := f.symm_apply_apply v
    have hcoord : hL (f v) =
        fun i ↦ e (g v (Fin.cast (RegularFormPresentation.fst_equivOfRingEquiv e p) i)) := by
      ext i
      simp [hL, hAdd, hfv]
    rw [LinearEquiv.toFun_eq_coe, hcoord, presentedForm_equivOfRingEquiv p e (g v),
      g.map_app v, RingHomInvPair.toRingEquiv_apply, hf v]
  rw [formClass_mk Q hQ p ⟨g⟩, RegularFormClass.mapRingEquiv_mk,
    formClass_mk Q' hQ' _ hEquiv]

/-- If `f : V ≃ₛₗ[σ] W` intertwines two regular quadratic forms `Q` and `Q'` via
`Q' (f v) = σ (Q v)`, then the discriminant of `Q'` is the image under `σ` of the discriminant of
`Q`. -/
theorem discr_formClass_eq_squareClassMap_of_semilinearEquiv
    {Q : QuadraticForm K V} {Q' : QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ v, Q' (f v) = σ (Q v)) :
    RegularFormClass.discr (formClass Q' hQ') =
      σ.squareClassMap (RegularFormClass.discr (formClass Q hQ)) := by
  rw [formClass_eq_mapRingEquiv_of_semilinearEquiv hQ hQ' f hf, RegularFormClass.discr_mapRingEquiv,
    RingHomInvPair.toRingEquiv, RingEquiv.toRingHom_ofRingHom]

/-- If `f : V ≃ₛₗ[σ] W` intertwines two regular quadratic forms `Q` and `Q'` via
`Q' (f v) = σ (Q v)`, then the signed discriminant of `Q'` is the image under `σ` of the signed
discriminant of `Q`. -/
theorem signedDiscr_formClass_eq_squareClassMap_of_semilinearEquiv
    {Q : QuadraticForm K V} {Q' : QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ v, Q' (f v) = σ (Q v)) :
    RegularFormClass.signedDiscr (formClass Q' hQ') =
      σ.squareClassMap (RegularFormClass.signedDiscr (formClass Q hQ)) := by
  rw [formClass_eq_mapRingEquiv_of_semilinearEquiv hQ hQ' f hf,
    RegularFormClass.signedDiscr_mapRingEquiv, RingHomInvPair.toRingEquiv,
    RingEquiv.toRingHom_ofRingHom]

end FormClass

end TauCeti
