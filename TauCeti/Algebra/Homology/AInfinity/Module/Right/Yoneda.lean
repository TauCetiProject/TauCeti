/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Free
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Complex
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Concat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Yoneda lemma for right A-infinity modules

Let `A` be an `A∞` algebra with a strict unit `e`, and let `M` be a right `A∞` module over `A` on
which `e` is a right unit for the binary operation, `m₂(x, e) = x`.  The free module of rank one
`A` represents the underlying complex of `M`: evaluation at `e` is a homotopy equivalence from the
morphism complex `Hom(A, M)` to the underlying complex `(M, m₁)` of `M`.  This is the `A∞`
counterpart of the differential graded Yoneda lemma, where the corresponding map is an isomorphism;
for `A∞` modules only a homotopy equivalence survives, because a morphism out of `A` has higher
components which are not determined by its value at `e`.

All constructions are made on the cofree bar comodules `sA ⊗ Tᶜ(sA)` and `sM ⊗ Tᶜ(sA)`, through
`TauCeti.TensorWords.tmulConcat`, which sends `y ⊗ w` to `x ⊗ y w`.

* Evaluation at `e`, `TauCeti.AInfinityRightModule.evalUnit`, applies the Taylor map of a cochain
  to the one-letter word `e`.  It commutes with the differentials as soon as `m₁(e) = 0`.
* The Yoneda cochain `TauCeti.AInfinityRightModule.yonedaCochain` of `x` has Taylor map
  `y ⊗ w ↦ b^M(x ⊗ y w)`, that is `(a₁, …, aₙ) ↦ m_{n+1}(x, a₁, …, aₙ)` up to the suspension
  signs.  By the module Stasheff identities, the assignment `x ↦ yonedaCochain x` commutes with
  the differentials, which makes it the map of complexes `TauCeti.AInfinityRightModule.yoneda`;
  evaluating the Yoneda cochain of `x` at `e` returns `m₂(x, e) = x`.
* Prepending `e` is a contracting homotopy of the bar complex of the free module of rank one
  (`TauCeti.AInfinityAlgebra.barDifferential_toRightModule_comp_tmulConcat_add`), because `e` is a
  strict unit.  Precomposing with it gives the homotopy
  `TauCeti.AInfinityRightModule.yonedaHomotopy` between the identity of `Hom(A, M)` and the
  composite of evaluation with the Yoneda cochains.

## Main definitions

* `TauCeti.AInfinityRightModule.yonedaEval`: evaluation at a degree-zero cycle, such as the unit,
  as a map of cochain complexes.
* `TauCeti.AInfinityRightModule.yoneda`: the Yoneda cochains, a map of cochain complexes.
* `TauCeti.AInfinityRightModule.homotopyYonedaEvalCompYoneda`: the homotopy from the identity of
  the morphism complex to evaluation followed by the Yoneda cochains.
* `TauCeti.AInfinityRightModule.yonedaHomotopyEquiv`: the Yoneda lemma, a homotopy equivalence.

## Main results

* `TauCeti.AInfinityRightModule.evalUnit_homDifferential`,
  `TauCeti.AInfinityRightModule.homDifferential_yonedaCochains`: both maps commute with the
  differentials.
* `TauCeti.AInfinityRightModule.evalUnit_yonedaCochain`: evaluating the Yoneda cochain of `x` at
  `e` gives `m₂(x, e)`, so evaluation is a left inverse of the Yoneda cochains.
* `TauCeti.AInfinityRightModule.homDifferential_yonedaHomotopy_add`: the homotopy identity
  `δ K F + K δ F = F - Y (F e)`.
* `TauCeti.AInfinityRightModule.quasiIso_yonedaEval`: evaluation at the unit is a
  quasi-isomorphism.

## Implementation notes

The cochain-level constructions allow the ground ring, the algebra and the module to live in
different universes.  The complex-level statements compare the morphism complex, whose terms live
in the universe of linear maps between the bar comodules, with the underlying complex of the
module; they put all three in one universe `u`, as the differential graded category of right
`A∞` modules does.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Chapter I (the Yoneda embedding).
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u uR uA uM

attribute [local instance] Comodule.cofree

section Cochains

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

open TensorWords

namespace AInfinityRightModule

variable {AA : AInfinityAlgebra R A} {M : Type uM} [AddCommGroup M] [Module R M]
  (MM : AInfinityRightModule AA M)

/-- The bar differential of a module after concatenation behind `x`: the cut before the first
letter applies the differential to `x`, the other cuts give the cofree lift of the Taylor map, and
the algebra bar differential acts on the concatenated word with the Koszul sign of `x`. -/
theorem barDifferential_comp_tmulConcat (x : M) :
    MM.barDifferential ∘ₗ tmulConcat R A M x =
      tmulConcat R A M (MM.differential x) +
        (Comodule.Hom.cofreeLift (C := TensorWords R A)
          (MM.taylor ∘ₗ tmulConcat R A M x)).toLinearMap +
        tmulConcat R A M ((MM.grading.shift 1).koszulTwist 1 x) ∘ₗ
          AA.toRightModule.barDifferential := by
  have hL : MM.taylor.rTensor (TensorWords R A) ∘ₗ
      (TensorProduct.assoc R M (TensorWords R A) (TensorWords R A)).symm.toLinearMap ∘ₗ
        (deconcatenation R A).lTensor M =
      (Comodule.Hom.cofreeLift (C := TensorWords R A) MM.taylor).toLinearMap := by
    rw [Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact, comul_eq_deconcatenation]
  have hb := AInfinityAlgebra.lift_prepend_comp_barDifferential_toRightModule AA
  rw [barDifferential_eq, gradedCoderiv_def, hL, LinearMap.add_comp, cofreeLift_comp_tmulConcat]
  congr 1
  · rw [differential_apply, ← taylor_tmul_one]
  refine TensorProduct.ext' fun y w ↦ ?_
  have hbw := LinearMap.congr_fun hb (y ⊗ₜ[R] w)
  have hι := LinearMap.congr_fun AA.coaugmentedBarDifferential_comp_reducedInclusion
    (TensorProduct.lift (prepend R A) (y ⊗ₜ[R] w))
  simp only [LinearMap.comp_apply] at hbw hι
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    tmulConcat_apply, hbw]
  rw [hι]

end AInfinityRightModule

namespace AInfinityAlgebra

variable {AA : AInfinityAlgebra R A} {e : A}

/-- Prepending a strict unit to a nonempty word and applying the Taylor map of the free module of
rank one returns the first letter on one-letter words and vanishes on longer words. -/
theorem taylor_toRightModule_comp_tmulConcat (he : AA.StrictUnit e) :
    AA.toRightModule.taylor ∘ₗ tmulConcat R A A e =
      (TensorProduct.rid R A).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor A := by
  have hte (q : ℤ) : AA.grading.koszulTwist q e = e :=
    AA.grading.koszulTwist_apply_of_mem_zero he.degree_zero q
  refine TensorProduct.ext (LinearMap.ext fun y ↦ TensorWords.linearMap_ext R A fun n a ↦ ?_)
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
    tmulConcat_tmul, toRightModule_taylor_tmul, prepend_of_tprod, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  rw [reducedInclusion_of, prepend_of_tprod, taylor_of_tprod]
  rcases n with _ | n
  · have ha : TensorWords.of R A 0 (PiTensorProduct.tprod R a) = 1 := by
      rw [one_eq_of_zero]
      exact of_tprod_congr R A fun i ↦ i.elim0
    rw [ha, counit_eq_counit, counit_one, one_smul]
    have hx : (fun i : Fin 2 ↦ AA.grading.koszulTwist ((2 : ℕ) - 1 - i)
        ((Fin.cons e (Fin.cons y a) : Fin 2 → A) i)) = ![e, y] := by
      funext i
      fin_cases i
      · simp [hte]
      · simp
    exact (congrArg (AA.m 2) hx).trans (he.binary_left y)
  · rw [counit_eq_counit, counit_of_of_ne_zero R A (Nat.succ_ne_zero n), zero_smul]
    exact he.higher _ (by simp) _ ⟨0, by simp [hte]⟩

/-- Prepending a strict unit is a contracting homotopy of the cofree bar comodule of the free
module of rank one: `b ∘ h + h ∘ b = 1` for `h (y ⊗ w) = e ⊗ y w`. -/
theorem barDifferential_toRightModule_comp_tmulConcat_add (he : AA.StrictUnit e) :
    AA.toRightModule.barDifferential ∘ₗ tmulConcat R A A e +
      tmulConcat R A A e ∘ₗ AA.toRightModule.barDifferential = LinearMap.id := by
  have hid := Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp
    (Comodule.Hom.id R (TensorWords R A) (A ⊗[R] TensorWords R A))
  have hτ : (AA.toRightModule.grading.shift 1).koszulTwist 1 e = -e := by
    rw [toRightModule_grading, InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply,
      AA.grading.koszulTwist_apply_of_mem_zero he.degree_zero]
  rw [AInfinityRightModule.barDifferential_comp_tmulConcat, differential_toRightModule,
    differential_apply, he.unary_eq_zero, map_zero, zero_add,
    taylor_toRightModule_comp_tmulConcat he, hτ, map_neg, LinearMap.neg_comp]
  rw [show (Comodule.Hom.cofreeLift (C := TensorWords R A) ((TensorProduct.rid R A).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor A)).toLinearMap = LinearMap.id
    from congrArg Comodule.Hom.toLinearMap hid]
  abel

end AInfinityAlgebra

namespace AInfinityRightModule

variable {AA : AInfinityAlgebra R A} {M : Type uM} [AddCommGroup M] [Module R M]
  (MM : AInfinityRightModule AA M) {e : A}

/-- Concatenation behind a module element of degree `p` has degree `p - 1` between the cofree bar
comodules of the free module of rank one and of `MM`. -/
private theorem isHomogeneous_tmulConcat_barGrading {p : ℤ} {x : M} (hx : x ∈ MM.grading.piece p) :
    LinearMap.IsHomogeneous (tmulConcat R A M x)
      (barGrading AA AA.toRightModule.grading).piece (barGrading AA MM.grading).piece (p - 1) := by
  have hx' : x ∈ (MM.grading.shift 1).piece (p - 1) := by
    rwa [InternalGrading.shift_piece, sub_add_cancel]
  have hG (G : InternalGrading R M) : (barGrading AA G).piece =
      ((G.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1))).piece :=
    funext (barGrading_piece AA G)
  have hA : (barGrading AA AA.toRightModule.grading).piece =
      ((AA.grading.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1))).piece := by
    rw [AInfinityAlgebra.toRightModule_grading]
    exact funext (barGrading_piece AA AA.grading)
  rw [hA, hG]
  exact TensorWords.isHomogeneous_tmulConcat (AA.grading.shift 1) (MM.grading.shift 1) hx'

/-- The Yoneda cochain of `x`: the cochain out of the free module of rank one whose Taylor map
sends `y ⊗ w` to the module Taylor map of `x ⊗ y w`, after the degree-one Koszul twist of `x`.
On unsuspended operations it is `(a₁, …, aₙ) ↦ m_{n+1}(x, a₁, …, aₙ)` up to the suspension
signs. -/
noncomputable def yonedaCochain :
    M →ₗ[R] A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A where
  toFun x := (Comodule.Hom.cofreeLift (C := TensorWords R A)
    (MM.taylor ∘ₗ tmulConcat R A M (MM.grading.koszulTwist 1 x))).toLinearMap
  map_add' _ _ := by
    simp only [map_add, LinearMap.comp_add, Comodule.Hom.cofreeLift_toLinearMap,
      LinearMap.rTensor_add, LinearMap.add_comp]
  map_smul' _ _ := by
    simp only [map_smul, LinearMap.comp_smul, Comodule.Hom.cofreeLift_toLinearMap,
      LinearMap.rTensor_smul, LinearMap.smul_comp, RingHom.id_apply]

/-- The Yoneda cochain of `x` is the cofree lift of the module Taylor map after concatenation
behind the Koszul twist of `x`. -/
theorem yonedaCochain_apply (x : M) :
    MM.yonedaCochain x = (Comodule.Hom.cofreeLift (C := TensorWords R A)
      (MM.taylor ∘ₗ tmulConcat R A M (MM.grading.koszulTwist 1 x))).toLinearMap :=
  (rfl)

/-- The Yoneda cochain of an element of degree `p` is a cochain of degree `p`. -/
theorem yonedaCochain_mem_homCochains {p : ℤ} {x : M} (hx : x ∈ MM.grading.piece p) :
    MM.yonedaCochain x ∈ homCochains AA.toRightModule MM p := by
  refine cofreeLift_mem_homCochains ?_
  have h := MM.isHomogeneous_taylor.comp
    (MM.isHomogeneous_tmulConcat_barGrading (MM.grading.koszulTwist_mem_piece hx 1))
  rwa [sub_add_cancel] at h

/-- The Yoneda cochains of the elements of degree `p`. -/
noncomputable def yonedaCochains (p : ℤ) :
    MM.grading.piece p →ₗ[R] homCochains AA.toRightModule MM p where
  toFun x := ⟨MM.yonedaCochain x, MM.yonedaCochain_mem_homCochains x.2⟩
  map_add' _ _ := Subtype.ext (map_add MM.yonedaCochain _ _)
  map_smul' r _ := Subtype.ext (map_smul MM.yonedaCochain r _)

/-- The degreewise Yoneda cochains are the Yoneda cochains. -/
@[simp]
theorem coe_yonedaCochains {p : ℤ} (x : MM.grading.piece p) :
    (MM.yonedaCochains p x : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) =
      MM.yonedaCochain x :=
  (rfl)

variable {MM} in
/-- Evaluation of a cochain at the unit: the Taylor map of the cochain at the one-letter word
`e`. -/
noncomputable def evalUnit (e : A) :
    (A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) →ₗ[R] M :=
  ((TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M) ∘ₗ
      LinearMap.applyₗ (e ⊗ₜ[R] (1 : TensorWords R A))

/-- Evaluation at `e` applies the cochain to `e ⊗ 1` and then the counit. -/
theorem evalUnit_apply (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) :
    evalUnit e F = TensorProduct.rid R M
      ((Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M (F (e ⊗ₜ[R] 1))) :=
  (rfl)

/-- A cochain out of the free module of rank one sends `e ⊗ 1` to its value at the unit, followed
by the empty word. -/
theorem homCochains.apply_tmul_one {p : ℤ} (F : homCochains AA.toRightModule MM p) :
    (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) (e ⊗ₜ[R] 1) =
      evalUnit e (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) ⊗ₜ[R] 1 := by
  conv_lhs => rw [homCochains.eq_cofreeLift F]
  rw [Comodule.Hom.cofreeLift_toLinearMap, LinearMap.comp_apply, Comodule.cofree_coact_tmul,
    comul_eq_deconcatenation, deconcatenation_one, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul, evalUnit_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

/-- Evaluation at a unit of degree zero sends cochains of degree `p` to elements of degree `p`. -/
theorem evalUnit_mem_piece (he : e ∈ AA.grading.piece 0) {p : ℤ}
    {F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A}
    (hF : F ∈ homCochains AA.toRightModule MM p) : evalUnit e F ∈ MM.grading.piece p := by
  have he' : e ⊗ₜ[R] (1 : TensorWords R A) ∈
      (barGrading AA AA.toRightModule.grading).piece (-1) := by
    rw [barGrading_piece, AInfinityAlgebra.toRightModule_grading, ← add_zero (-1 : ℤ)]
    refine InternalGrading.tmul_mem_tensorProduct _ _ ?_
      (by rw [grading_piece]; exact one_mem_gradedPiece _)
    rwa [InternalGrading.shift_piece, neg_add_cancel]
  have hFe := (mem_homCochains_iff.1 hF).2.map_mem he'
  rw [barGrading_piece] at hFe
  have h := (TensorWords.isHomogeneous_rid_comp_lTensor_counit (MM.grading.shift 1)
    (AA.grading.shift 1)).map_mem hFe
  rw [add_zero, InternalGrading.shift_piece, neg_add_cancel_comm] at h
  exact h

/-- Evaluation at a cycle `e` commutes with the differentials: the module bar differential of
`F (e ⊗ 1)` is its unary part, and the bar differential of the free module kills `e ⊗ 1`. -/
theorem evalUnit_homDifferential (he : AA.differential e = 0) {p : ℤ}
    (F : homCochains AA.toRightModule MM p) :
    evalUnit e (homDifferential AA.toRightModule MM p F :
        A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) =
      MM.differential (evalUnit e (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A)) := by
  have hb : AA.toRightModule.barDifferential (e ⊗ₜ[R] (1 : TensorWords R A)) = 0 := by
    rw [barDifferential_tmul_one, taylor_tmul_one_eq_differential,
      AInfinityAlgebra.differential_toRightModule, he, TensorProduct.zero_tmul]
  rw [coe_homDifferential, map_sub, Units.smul_def, map_zsmul, evalUnit_apply, evalUnit_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, hb, map_zero, homCochains.apply_tmul_one,
    barDifferential_tmul_one, taylor_tmul_one_eq_differential]
  simp

/-- Evaluating the Yoneda cochain of `x` at `e` gives the binary module operation `m₂(x, e)`. -/
theorem evalUnit_yonedaCochain (x : M) : evalUnit e (MM.yonedaCochain x) = MM.m 2 x ![e] := by
  have h := LinearMap.congr_fun (Comodule.Hom.rid_comp_lTensor_counit_comp_cofreeLift
    (C := TensorWords R A) (MM.taylor ∘ₗ tmulConcat R A M (MM.grading.koszulTwist 1 x)))
    (e ⊗ₜ[R] 1)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [evalUnit_apply, yonedaCochain_apply, h, LinearMap.comp_apply, tmulConcat_tmul, prepend_one,
    ReducedTensorWords.ofLetter_eq_of_tprod, reducedInclusion_of, taylor_tmul_of_tprod]
  congr 2
  · simp
  · funext i
    rw [Fin.fin_one_eq_zero i]
    simp

/-- For `z` of degree `p`, the cofree lift of the Taylor map after concatenation behind `z` is the
graded commutator of concatenation behind `z` with the bar differentials, corrected by
concatenation behind `d z`. -/
private theorem cofreeLift_taylor_comp_tmulConcat_eq {p : ℤ} {z : M}
    (hz : z ∈ MM.grading.piece p) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A)
        (MM.taylor ∘ₗ tmulConcat R A M z)).toLinearMap =
      MM.barDifferential ∘ₗ tmulConcat R A M z - tmulConcat R A M (MM.differential z) +
        ((p.negOnePow : ℤ) : R) • (tmulConcat R A M z ∘ₗ AA.toRightModule.barDifferential) := by
  have hτ : (MM.grading.shift 1).koszulTwist 1 z = -(((p.negOnePow : ℤ) : R) • z) := by
    rw [InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply,
      MM.grading.koszulTwist_one_apply_of_mem hz]
  rw [barDifferential_comp_tmulConcat, hτ, map_neg, map_smul, LinearMap.neg_comp,
    LinearMap.smul_comp]
  abel

/-- On an element of degree `q`, the Koszul twist in the Yoneda cochain is the sign `(-1)^q`. -/
private theorem yonedaCochain_eq_smul {q : ℤ} {y : M} (hy : y ∈ MM.grading.piece q) :
    MM.yonedaCochain y = ((q.negOnePow : ℤ) : R) • (Comodule.Hom.cofreeLift (C := TensorWords R A)
      (MM.taylor ∘ₗ tmulConcat R A M y)).toLinearMap := by
  rw [yonedaCochain_apply, MM.grading.koszulTwist_one_apply_of_mem hy, map_smul,
    LinearMap.comp_smul, Comodule.Hom.cofreeLift_toLinearMap, Comodule.Hom.cofreeLift_toLinearMap,
    LinearMap.rTensor_smul, LinearMap.smul_comp]

/-- The Yoneda cochains form a chain map: the differential of the Yoneda cochain of `x` is the
Yoneda cochain of the differential of `x`. -/
theorem homDifferential_yonedaCochains {p : ℤ} (x : MM.grading.piece p) :
    homDifferential AA.toRightModule MM p (MM.yonedaCochains p x) =
      MM.yonedaCochains (p + 1) ⟨MM.differential x, MM.differential_mem_piece x.2⟩ := by
  obtain ⟨x, hx⟩ := x
  have hdx := MM.differential_mem_piece hx
  have hdd : MM.differential (MM.differential x) = 0 :=
    LinearMap.congr_fun MM.differential_comp_self_eq_zero x
  have hb := AA.toRightModule.barDifferential_sq
  have hbM (f : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) :
      MM.barDifferential ∘ₗ MM.barDifferential ∘ₗ f = 0 := by
    rw [← LinearMap.comp_assoc, MM.barDifferential_sq, LinearMap.zero_comp]
  have hs : ((p.negOnePow : ℤ) : R) * ((p.negOnePow : ℤ) : R) = 1 := by
    norm_cast
    simp
  apply Subtype.ext
  rw [coe_homDifferential, coe_yonedaCochains, coe_yonedaCochains, yonedaCochain_eq_smul MM hx,
    yonedaCochain_eq_smul MM hdx, cofreeLift_taylor_comp_tmulConcat_eq MM hx,
    cofreeLift_taylor_comp_tmulConcat_eq MM hdx, hdd, map_zero, Units.smul_def,
    ← Int.cast_smul_eq_zsmul R, Int.negOnePow_succ]
  simp only [LinearMap.comp_sub, LinearMap.comp_add, LinearMap.comp_smul, LinearMap.sub_comp,
    LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_assoc, hb, hbM, LinearMap.comp_zero,
    smul_zero, smul_add, smul_sub, smul_smul, Units.val_neg, Int.cast_neg, neg_smul, sub_zero,
    add_zero, zero_sub, neg_mul_neg, hs, one_smul]
  abel

variable {MM} in
/-- Evaluation at a unit of degree zero on the cochains of degree `p`. -/
noncomputable def evalUnitCochains (he : e ∈ AA.grading.piece 0) (p : ℤ) :
    homCochains AA.toRightModule MM p →ₗ[R] MM.grading.piece p where
  toFun F := ⟨evalUnit e (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A),
    evalUnit_mem_piece MM he F.2⟩
  map_add' _ _ := Subtype.ext (map_add (evalUnit e) _ _)
  map_smul' r _ := Subtype.ext (map_smul (evalUnit e) r _)

/-- Degreewise evaluation at the unit is evaluation at the unit. -/
@[simp]
theorem coe_evalUnitCochains (he : e ∈ AA.grading.piece 0) {p : ℤ}
    (F : homCochains AA.toRightModule MM p) :
    (evalUnitCochains he p F : M) =
      evalUnit e (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) :=
  (rfl)

/-- A cochain out of the free module of rank one after prepending `e`: the cut before the
first letter gives concatenation behind the value of the cochain at `e`, and the other cuts give
the cofree lift of the Taylor map after prepending `e`. -/
private theorem homCochains.comp_tmulConcat {p : ℤ} (F : homCochains AA.toRightModule MM p) :
    (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) ∘ₗ tmulConcat R A A e =
      tmulConcat R A M (evalUnit e (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A)) +
        (Comodule.Hom.cofreeLift (C := TensorWords R A)
          (((TensorProduct.rid R M).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ
              (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A)) ∘ₗ
            tmulConcat R A A e)).toLinearMap := by
  conv_lhs => rw [homCochains.eq_cofreeLift F]
  rw [cofreeLift_comp_tmulConcat, evalUnit_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

variable {MM} in
/-- The contracting homotopy of the Yoneda lemma, from cochains of degree `p` to cochains of degree
`q = p - 1`: up to the sign `(-1)^p`, the cofree lift of the Taylor map of a cochain after
prepending the unit `e`. -/
noncomputable def yonedaHomotopy (he : e ∈ AA.grading.piece 0) {p q : ℤ} (hpq : q + 1 = p) :
    homCochains AA.toRightModule MM p →ₗ[R] homCochains AA.toRightModule MM q where
  toFun F := ⟨((p.negOnePow : ℤ) : R) • (Comodule.Hom.cofreeLift (C := TensorWords R A)
      (((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ
          (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A)) ∘ₗ
        tmulConcat R A A e)).toLinearMap, by
    refine Submodule.smul_mem _ _ (cofreeLift_mem_homCochains ?_)
    have hF := homCochains.isHomogeneous F
    have hG : (barGrading AA MM.grading).piece =
        ((MM.grading.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1))).piece :=
      funext (barGrading_piece AA MM.grading)
    rw [hG] at hF
    have ht := ((TensorWords.isHomogeneous_rid_comp_lTensor_counit (MM.grading.shift 1)
      (AA.grading.shift 1)).comp hF).comp (AA.toRightModule.isHomogeneous_tmulConcat_barGrading
        (p := 0) (by rwa [AInfinityAlgebra.toRightModule_grading]))
    rw [show (0 : ℤ) - 1 + (p + 0) = q by omega, LinearMap.comp_assoc] at ht
    exact ht⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, LinearMap.comp_add, LinearMap.add_comp,
      Comodule.Hom.cofreeLift_toLinearMap, LinearMap.rTensor_add, smul_add]
  map_smul' r _ := by
    apply Subtype.ext
    simp only [SetLike.val_smul, LinearMap.comp_smul, LinearMap.smul_comp,
      Comodule.Hom.cofreeLift_toLinearMap, LinearMap.rTensor_smul, RingHom.id_apply,
      smul_comm r]

/-- The homotopy is `(-1)^p` times the cofree lift of the Taylor map after prepending `e`. -/
theorem coe_yonedaHomotopy (he : e ∈ AA.grading.piece 0) {p q : ℤ} (hpq : q + 1 = p)
    (F : homCochains AA.toRightModule MM p) :
    (yonedaHomotopy he hpq F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) =
      ((p.negOnePow : ℤ) : R) • (Comodule.Hom.cofreeLift (C := TensorWords R A)
        (((TensorProduct.rid R M).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ
            (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A)) ∘ₗ
          tmulConcat R A A e)).toLinearMap :=
  (rfl)

/-- **The homotopy of the Yoneda lemma.**  For a strict unit `e`, the composite of evaluation at
`e` with the Yoneda cochains is homotopic to the identity of the morphism complex out of the free
module of rank one: `δ K F + K δ F = F - Y (F e)`. -/
theorem homDifferential_yonedaHomotopy_add (he : AA.StrictUnit e) {p q : ℤ} (hpq : q + 1 = p)
    (F : homCochains AA.toRightModule MM p) :
    (homDifferential AA.toRightModule MM q (yonedaHomotopy he.degree_zero hpq F) :
        A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) +
      (yonedaHomotopy he.degree_zero rfl (homDifferential AA.toRightModule MM p F) :
        A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) =
      (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) -
        MM.yonedaCochain
          (evalUnit e (F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A)) := by
  subst hpq
  have hdF := evalUnit_homDifferential MM he.differential_eq_zero F
  have hxp := evalUnit_mem_piece MM he.degree_zero F.2
  have hK := homCochains.comp_tmulConcat MM (e := e) F
  have hKδ := homCochains.comp_tmulConcat MM (e := e)
    (homDifferential AA.toRightModule MM (q + 1) F)
  have hD := congrArg ((F : A ⊗[R] TensorWords R A →ₗ[R] M ⊗[R] TensorWords R A) ∘ₗ ·)
    (AInfinityAlgebra.barDifferential_toRightModule_comp_tmulConcat_add he)
  simp only [LinearMap.comp_add, LinearMap.comp_id] at hD
  have hY := yonedaCochain_eq_smul MM hxp
  rw [cofreeLift_taylor_comp_tmulConcat_eq MM hxp] at hY
  rw [coe_homDifferential, coe_yonedaHomotopy, coe_yonedaHomotopy, ← sub_eq_of_eq_add' hK,
    ← sub_eq_of_eq_add' hKδ, hdF, coe_homDifferential, hY]
  have hs : ((q.negOnePow : ℤ) : R) * ((q.negOnePow : ℤ) : R) = 1 := by
    norm_cast
    simp
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, Int.negOnePow_succ, Units.val_neg,
    Int.cast_neg, neg_neg, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, LinearMap.comp_assoc, smul_sub, smul_add, smul_smul, neg_mul, mul_neg,
    hs, neg_smul, one_smul, LinearMap.comp_neg, LinearMap.neg_comp, smul_neg] at hD ⊢
  linear_combination (norm := module) hD

end AInfinityRightModule

end Cochains

section Complex

namespace AInfinityRightModule

open CategoryTheory

variable {R A M : Type u} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
  {AA : AInfinityAlgebra R A}
  (MM : AInfinityRightModule AA M) {e : A}

/-- Evaluation at a cycle `e` of degree zero, as a map of cochain complexes from the morphism
complex out of the free module of rank one to the underlying complex of the module. -/
noncomputable def yonedaEval (he : e ∈ AA.grading.piece 0) (hde : AA.differential e = 0) :
    homComplex AA.toRightModule MM ⟶ MM.cochainComplex where
  f p := ConcreteCategory.ofHom (C := ModuleCat R)
    ((gradedCochainComplexXEquiv p).symm.toLinearMap ∘ₗ evalUnitCochains he p ∘ₗ
      (homComplexXEquiv AA.toRightModule MM p).toLinearMap)
  comm' := by
    rintro i j (rfl : i + 1 = j)
    refine ModuleCat.hom_ext (LinearMap.ext fun F ↦ (gradedCochainComplexXEquiv (i + 1)).injective
      (Subtype.ext ?_))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      gradedCochainComplexXEquiv_d]
    simp only [ConcreteCategory.hom_ofHom, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, coe_evalUnitCochains, homComplexXEquiv_d]
    exact (evalUnit_homDifferential MM hde _).symm

/-- In degree `p`, the evaluation map of complexes is evaluation at the unit. -/
@[simp]
theorem gradedCochainComplexXEquiv_yonedaEval_f (he : e ∈ AA.grading.piece 0)
    (hde : AA.differential e = 0) (p : ℤ) (F : (homComplex AA.toRightModule MM).X p) :
    gradedCochainComplexXEquiv p ((MM.yonedaEval he hde).f p F) =
      evalUnitCochains he p (homComplexXEquiv AA.toRightModule MM p F) := by
  simp [yonedaEval]

/-- The Yoneda cochains, as a map of cochain complexes from the underlying complex of the module to
the morphism complex out of the free module of rank one. -/
noncomputable def yoneda : MM.cochainComplex ⟶ homComplex AA.toRightModule MM where
  f p := ConcreteCategory.ofHom (C := ModuleCat R)
    ((homComplexXEquiv AA.toRightModule MM p).symm.toLinearMap ∘ₗ MM.yonedaCochains p ∘ₗ
      (gradedCochainComplexXEquiv p).toLinearMap)
  comm' := by
    rintro i j (rfl : i + 1 = j)
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦
      (homComplexXEquiv AA.toRightModule MM (i + 1)).injective ?_)
    have hd : gradedCochainComplexXEquiv (i + 1) ((MM.cochainComplex.d i (i + 1)).hom x) =
        ⟨MM.differential (gradedCochainComplexXEquiv i x),
          MM.differential_mem_piece (gradedCochainComplexXEquiv i x).2⟩ :=
      Subtype.ext (gradedCochainComplexXEquiv_d i x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, homComplexXEquiv_d, hd]
    exact homDifferential_yonedaCochains MM _

/-- In degree `p`, the Yoneda map of complexes is the degree-`p` Yoneda cochains. -/
@[simp]
theorem homComplexXEquiv_yoneda_f (p : ℤ) (x : MM.cochainComplex.X p) :
    homComplexXEquiv AA.toRightModule MM p (MM.yoneda.f p x) =
      MM.yonedaCochains p (gradedCochainComplexXEquiv p x) := by
  simp [yoneda]

/-- If a degree-zero cycle `e` is a right unit for the binary module operation, evaluation at `e`
is a left inverse of the Yoneda cochains. -/
theorem yoneda_comp_yonedaEval (he : e ∈ AA.grading.piece 0) (hde : AA.differential e = 0)
    (hM : ∀ x, MM.m 2 x ![e] = x) : MM.yoneda ≫ MM.yonedaEval he hde = 𝟙 MM.cochainComplex := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ (gradedCochainComplexXEquiv p).injective
    (Subtype.ext ?_))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    gradedCochainComplexXEquiv_yonedaEval_f, homComplexXEquiv_yoneda_f, coe_evalUnitCochains,
    coe_yonedaCochains, evalUnit_yonedaCochain, hM, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]

/-- The contracting homotopy of the Yoneda lemma, as a homotopy from the identity of the morphism
complex out of the free module of rank one to evaluation at the unit followed by the Yoneda
cochains. -/
noncomputable def homotopyYonedaEvalCompYoneda (he : AA.StrictUnit e) :
    Homotopy (𝟙 (homComplex AA.toRightModule MM))
      (MM.yonedaEval he.degree_zero he.differential_eq_zero ≫ MM.yoneda) where
  hom i j := if h : j + 1 = i then ConcreteCategory.ofHom (C := ModuleCat R)
      ((homComplexXEquiv AA.toRightModule MM j).symm.toLinearMap ∘ₗ
        yonedaHomotopy he.degree_zero h ∘ₗ
        (homComplexXEquiv AA.toRightModule MM i).toLinearMap) else 0
  zero i j hij := dite_eq_right hij
  comm i := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by ring⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl), dite_eq_left rfl,
      dite_eq_left rfl]
    refine ModuleCat.hom_ext (LinearMap.ext fun F ↦
      (homComplexXEquiv AA.toRightModule MM (j + 1)).injective (Subtype.ext ?_))
    have h := homDifferential_yonedaHomotopy_add MM he rfl
      (homComplexXEquiv AA.toRightModule MM (j + 1) F)
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_add,
      ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply, HomologicalComplex.comp_f,
      homComplexXEquiv_yoneda_f, gradedCochainComplexXEquiv_yonedaEval_f,
      ConcreteCategory.hom_ofHom, LinearEquiv.coe_coe, map_add, LinearEquiv.apply_symm_apply,
      homComplexXEquiv_d, Submodule.coe_add, coe_yonedaCochains, coe_evalUnitCochains]
    rw [eq_sub_iff_add_eq] at h
    exact h.symm.trans (by abel)

/-- **The Yoneda lemma for right `A∞` modules.**  Over an `A∞` algebra with a strict unit `e`,
for a module on which `e` is a right unit for the binary operation, evaluation at `e` is a
homotopy equivalence from the morphism complex out of the free module of rank one to the
underlying complex of the module, with homotopy inverse the Yoneda cochains. -/
noncomputable def yonedaHomotopyEquiv (he : AA.StrictUnit e) (hM : ∀ x, MM.m 2 x ![e] = x) :
    HomotopyEquiv (homComplex AA.toRightModule MM) MM.cochainComplex where
  hom := MM.yonedaEval he.degree_zero he.differential_eq_zero
  inv := MM.yoneda
  homotopyHomInvId := (MM.homotopyYonedaEvalCompYoneda he).symm
  homotopyInvHomId :=
    Homotopy.ofEq (MM.yoneda_comp_yonedaEval he.degree_zero he.differential_eq_zero hM)

/-- Evaluation at a strict unit `e` is a quasi-isomorphism from the morphism complex out of the
free module of rank one to the underlying complex of a module on which `e` is a right unit for the
binary operation. -/
theorem quasiIso_yonedaEval (he : AA.StrictUnit e) (hM : ∀ x, MM.m 2 x ![e] = x) :
    QuasiIso (MM.yonedaEval he.degree_zero he.differential_eq_zero) :=
  (MM.yonedaHomotopyEquiv he hM).quasiIso_hom

end AInfinityRightModule

end Complex

end TauCeti
