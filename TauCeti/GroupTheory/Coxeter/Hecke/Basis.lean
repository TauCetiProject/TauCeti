/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.GroupTheory.Coxeter.Hecke.Basic
public import TauCeti.GroupTheory.Coxeter.Hecke.Operator

/-!
# The basis theorem for the Iwahori–Hecke algebra of a Coxeter system

Let `cs : CoxeterSystem M W` be a Coxeter system. The elements `T_w`, `w : W`, of the Hecke algebra
`M.HeckeAlgebra c` (`CoxeterMatrix.HeckeAlgebra.Tw`) span it; this file proves that they are
linearly independent over every commutative semiring `R` and for every parameter `c : R`, so that
they form a basis `CoxeterMatrix.HeckeAlgebra.basisTw`.

The proof is Iwahori's. The left regular operators `CoxeterSystem.heckeLeftMul` on the free module
`W →₀ R` satisfy the quadratic and braid relations, which gives the **regular representation**
`CoxeterMatrix.HeckeAlgebra.regularRep`. It sends `T_w` to an operator taking the basis vector of
`1` to that of `w`, so evaluating at the basis vector of `1` is a linear map sending the family
`T_w` to the standard basis of `W →₀ R`. That evaluation is then the coordinate map of the basis
(`CoxeterMatrix.HeckeAlgebra.basisTw_repr_apply`), and the regular representation is faithful.

Applied to the Coxeter system `M.toCoxeterSystem` of the Coxeter group `M.Group`, this shows that
`M.HeckeAlgebra c` is a free `R`-module; for a finite Coxeter group its rank is the order of the
group (`CoxeterMatrix.HeckeAlgebra.finrank_eq_natCard`).

## Main definitions

* `CoxeterMatrix.HeckeAlgebra.regularRep`: the regular representation on `W →₀ R`.
* `CoxeterMatrix.HeckeAlgebra.basisTw`: the basis `T_w` indexed by `W`.

## Main results

* `CoxeterMatrix.HeckeAlgebra.regularRep_Tw_apply_single_one`: `T_w` takes the basis vector of
  `1` to that of `w`.
* `CoxeterMatrix.HeckeAlgebra.linearIndependent_Tw`: the elements `T_w` are linearly independent.
* `CoxeterMatrix.HeckeAlgebra.basisTw_repr_apply`: the coordinates in the basis `T_w` are read off
  from the regular representation.
* `CoxeterMatrix.HeckeAlgebra.basisTw_repr_T_mul` and
  `CoxeterMatrix.HeckeAlgebra.basisTw_repr_mul_T`: the coordinates of a product with a generator.
* `CoxeterMatrix.HeckeAlgebra.regularRep_injective`: the regular representation is faithful.
* `CoxeterMatrix.HeckeAlgebra.finrank_eq_natCard`: the rank is the order of `W`.

## References

* N. Iwahori, *On the structure of a Hecke ring of a Chevalley group over a finite field*,
  J. Fac. Sci. Univ. Tokyo Sect. I 10 (1964), 215–236.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 7.3.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4.
* The type-A basis theorem in `TauCeti.Algebra.TypeAHeckeAlgebra.Basis` is obtained from this one
  by transport.
-/

public section

open CoxeterSystem Finsupp

namespace CoxeterMatrix

namespace HeckeAlgebra

variable {B : Type*} {M : CoxeterMatrix B} {R : Type*} [CommSemiring R] (c : R)
variable {W : Type*} [Group W] (cs : CoxeterSystem M W)

/-- The **regular representation** of the Hecke algebra on the free module `W →₀ R`: the
generator `T i` acts by the left regular operator `CoxeterSystem.heckeLeftMul`, sending the basis
vector of `w` to that of `s i * w` when `i` is not a left descent of `w`, and to `c` times itself
plus that of `s i * w` when it is. -/
noncomputable def regularRep : M.HeckeAlgebra c →ₐ[R] Module.End R (W →₀ R) :=
  lift (cs.heckeLeftMul c) (cs.heckeLeftMul_mul_self c) (cs.prod_map_heckeLeftMul_braidWord c)

/-- The regular representation takes the generator `T i` to the left regular operator of the
simple reflection `s i`. -/
@[simp]
theorem regularRep_T (i : B) : regularRep c cs (T M c i) = cs.heckeLeftMul c i :=
  lift_T _ _ _ i

/-- The regular representation commutes with every right regular Hecke operator. -/
theorem commute_regularRep_heckeRightMul (x : M.HeckeAlgebra c) (i : B) :
    Commute (regularRep c cs x) (cs.heckeRightMul c i) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T M c)) := by
    rw [adjoin_range_T]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem _ hx =>
    obtain ⟨j, rfl⟩ := hx
    simpa using cs.commute_heckeLeftMul_heckeRightMul c j i
  | algebraMap r => simp only [AlgHom.commutes]; exact Algebra.commutes _ _
  | add a b _ _ ha hb => simpa only [map_add] using ha.add_left hb
  | mul a b _ _ ha hb => simpa only [map_mul] using ha.mul_left hb

/-- In the regular representation, `T_w` takes the basis vector of `1` to that of `w`. -/
@[simp]
theorem regularRep_Tw_apply_single_one (w : W) :
    regularRep c cs (Tw c cs w) (single 1 1) = single w (1 : R) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hT : ⇑(regularRep c cs) ∘ T M c = cs.heckeLeftMul c := funext (regularRep_T c cs)
  rw [Tw_wordProd hω, map_list_prod, List.map_map, hT,
    cs.prod_map_heckeLeftMul_apply_single_one c hω]

/-- Evaluation of the regular representation at the basis vector of `1`. -/
private noncomputable def evalOne : M.HeckeAlgebra c →ₗ[R] W →₀ R :=
  LinearMap.applyₗ (single 1 1) ∘ₗ (regularRep c cs).toLinearMap

private theorem evalOne_apply (x : M.HeckeAlgebra c) :
    evalOne c cs x = regularRep c cs x (single 1 1) :=
  (rfl)

/-- **The elements `T_w` are linearly independent** over every commutative semiring and for every
parameter. -/
theorem linearIndependent_Tw : LinearIndependent R (Tw c cs) := by
  refine LinearIndependent.of_comp (evalOne c cs) ?_
  have h : ⇑(evalOne c cs) ∘ Tw c cs = ⇑(Finsupp.basisSingleOne : Module.Basis W R (W →₀ R)) := by
    funext w
    simp [evalOne_apply]
  rw [h]
  exact Finsupp.basisSingleOne.linearIndependent

/-- **The basis theorem**: the elements `T_w`, `w : W`, form a basis of the Hecke algebra over
every commutative semiring and for every parameter. -/
noncomputable def basisTw : Module.Basis W R (M.HeckeAlgebra c) :=
  .mk (linearIndependent_Tw c cs) (span_range_Tw c cs).ge

/-- The basis vectors of `CoxeterMatrix.HeckeAlgebra.basisTw` are the elements `T_w`. -/
@[simp]
theorem coe_basisTw : ⇑(basisTw c cs) = Tw c cs :=
  Module.Basis.coe_mk _ _

/-- The coordinates of `x` in the basis `T_w` are the image under the regular representation of
`x` of the basis vector of `1`. -/
theorem basisTw_repr_apply (x : M.HeckeAlgebra c) :
    (basisTw c cs).repr x = regularRep c cs x (single 1 1) := by
  have h : ((basisTw c cs).repr : M.HeckeAlgebra c →ₗ[R] W →₀ R) = evalOne c cs :=
    (basisTw c cs).ext fun w ↦ by
      rw [LinearEquiv.coe_coe, Module.Basis.repr_self, evalOne_apply, coe_basisTw,
        regularRep_Tw_apply_single_one]
  exact (LinearMap.congr_fun h x).trans (evalOne_apply c cs x)

open scoped Classical in
/-- The coefficient of `T_w` after left multiplication by a generator. -/
theorem basisTw_repr_T_mul (i : B) (x : M.HeckeAlgebra c) (w : W) :
    (basisTw c cs).repr (T M c i * x) w =
      (if cs.IsLeftDescent w i then c * (basisTw c cs).repr x w else 0) +
        (basisTw c cs).repr x (cs.simple i * w) := by
  let b := basisTw c cs
  have h : (b.coord w).comp (LinearMap.mulLeft R (T M c i)) =
      (if cs.IsLeftDescent w i then c • b.coord w else 0) + b.coord (cs.simple i * w) := by
    apply b.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, b, coe_basisTw]
    by_cases hv : cs.IsLeftDescent v i <;>
      simp only [hv, not_false_eq_true, T_mul_Tw_of_isLeftDescent,
        T_mul_Tw_of_not_isLeftDescent] <;>
      by_cases hw : cs.IsLeftDescent w i <;>
      simp [hw, ← coe_basisTw, Finsupp.single_apply, ← eq_inv_mul_iff_mul_eq] <;>
      split_ifs <;> simp_all
  by_cases hw : cs.IsLeftDescent w i <;>
    simpa [b, hw] using LinearMap.congr_fun h x

open scoped Classical in
/-- The coefficient of `T_w` after right multiplication by a generator. -/
theorem basisTw_repr_mul_T (x : M.HeckeAlgebra c) (i : B) (w : W) :
    (basisTw c cs).repr (x * T M c i) w =
      (if cs.IsRightDescent w i then c * (basisTw c cs).repr x w else 0) +
        (basisTw c cs).repr x (w * cs.simple i) := by
  let b := basisTw c cs
  have h : (b.coord w).comp (LinearMap.mulRight R (T M c i)) =
      (if cs.IsRightDescent w i then c • b.coord w else 0) + b.coord (w * cs.simple i) := by
    apply b.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, b, coe_basisTw]
    by_cases hv : cs.IsRightDescent v i <;>
      simp only [hv, not_false_eq_true, Tw_mul_T_of_isRightDescent,
        Tw_mul_T_of_not_isRightDescent] <;>
      by_cases hw : cs.IsRightDescent w i <;>
      simp [hw, ← coe_basisTw, Finsupp.single_apply, ← eq_mul_inv_iff_mul_eq] <;>
      split_ifs <;> simp_all
  by_cases hw : cs.IsRightDescent w i <;>
    simpa [b, hw] using LinearMap.congr_fun h x

/-- **The regular representation is faithful.** -/
theorem regularRep_injective : Function.Injective (regularRep c cs) :=
  fun x y h ↦ (basisTw c cs).repr.injective <| by
    rw [basisTw_repr_apply, basisTw_repr_apply, h]

/-- The Hecke algebra is a free module, with basis the elements `T_w` of the Coxeter group
`M.Group`. -/
instance : Module.Free R (M.HeckeAlgebra c) :=
  .of_basis (basisTw c M.toCoxeterSystem)

include cs in
/-- Over a commutative semiring with the strong rank condition, for instance a nontrivial
commutative ring, the rank of the Hecke algebra is the order of the Coxeter group `W`. (When `W` is
infinite, both sides are `0` by convention.) -/
theorem finrank_eq_natCard [StrongRankCondition R] :
    Module.finrank R (M.HeckeAlgebra c) = Nat.card W :=
  Module.finrank_eq_nat_card_basis (basisTw c cs)

end HeckeAlgebra

end CoxeterMatrix
