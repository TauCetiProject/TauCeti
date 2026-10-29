/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord
public import TauCeti.GroupTheory.Coxeter.HeckeOperator
public import TauCeti.GroupTheory.Coxeter.Matrix

/-!
# The basis theorem for the type-A Hecke algebra

Let `cs` be a Coxeter system of type `A_(n-1)` on a group `W`. The elements `T_w`, `w : W`, of the
Hecke algebra `TypeAHeckeAlgebra R q n` (`TauCeti.TypeAHeckeAlgebra.Tw`) span it; this file proves
that they are linearly independent over every commutative ring `R` and every unit `q`, so that they
form a basis `TauCeti.TypeAHeckeAlgebra.basisTw`.

The proof is Iwahori's. The left regular operators `CoxeterSystem.heckeLeftMul` on the free module
`W →₀ R`, with quadratic coefficient `q - q⁻¹`, satisfy the defining relations of the Hecke algebra,
which gives the **regular representation** `TauCeti.TypeAHeckeAlgebra.regularRep`. It sends `T_w`
to an operator taking the basis vector of `1` to that of `w`, so evaluating at the basis vector of
`1` is a linear map sending the family `T_w` to the standard basis of `W →₀ R`. That evaluation is
then the coordinate map of the basis (`TauCeti.TypeAHeckeAlgebra.basisTw_repr_apply`), and the
regular representation is faithful.

The Coxeter system is an arbitrary one of type `A_(n-1)`. For the abstract Coxeter group
`(CoxeterMatrix.A (n - 1)).Group` this shows that the Hecke algebra is a free module; for a
concrete finite model of the Coxeter group, such as the symmetric group on `n` letters, the rank
is the order of that group (`TauCeti.TypeAHeckeAlgebra.finrank_eq_natCard`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.regularRep`: the regular representation on `W →₀ R`.
* `TauCeti.TypeAHeckeAlgebra.basisTw`: the basis `T_w` indexed by `W`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.regularRep_Tw_apply_single_one`: `T_w` takes the basis vector of `1`
  to that of `w`.
* `TauCeti.TypeAHeckeAlgebra.linearIndependent_Tw`: the elements `T_w` are linearly independent.
* `TauCeti.TypeAHeckeAlgebra.basisTw_repr_apply`: the coordinates in the basis `T_w` are read off
  from the regular representation.
* `TauCeti.TypeAHeckeAlgebra.regularRep_injective`: the regular representation is faithful.
* `TauCeti.TypeAHeckeAlgebra.finrank_eq_natCard`: the rank is the order of `W`.

## References

* N. Iwahori, *On the structure of a Hecke ring of a Chevalley group over a finite field*,
  J. Fac. Sci. Univ. Tokyo Sect. I 10 (1964), 215–236.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Chapter 7.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4.
-/

public section

namespace TauCeti

namespace TypeAHeckeAlgebra

open CoxeterSystem Finsupp

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}
variable {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

variable (q) in
/-- The **regular representation** of the type-A Hecke algebra on the free module `W →₀ R`: the
generator `T i` acts by the left regular operator `CoxeterSystem.heckeLeftMul` with quadratic
coefficient `q - q⁻¹`, sending the basis vector of `w` to that of `s i * w` when `i` is not a left
descent of `w`, and to `(q - q⁻¹)` times itself plus that of `s i * w` when it is. -/
noncomputable def regularRep : TypeAHeckeAlgebra R q n →ₐ[R] Module.End R (W →₀ R) :=
  lift (fun i ↦ cs.heckeLeftMul ((q : R) - ↑q⁻¹) i) (fun i ↦ cs.heckeLeftMul_mul_self _ i)
    (fun {i j} h ↦ by
      have hb := cs.prod_map_heckeLeftMul_braidWord ((q : R) - ↑q⁻¹) i j
      rw [braidWord, coxeterMatrixA_eq_three (.inl h), braidWord,
        coxeterMatrixA_eq_three (.inr h), prod_map_alternatingWord_three,
        prod_map_alternatingWord_three] at hb
      exact hb.symm)
    (fun {i j} h ↦ by
      have hb := cs.prod_map_heckeLeftMul_braidWord ((q : R) - ↑q⁻¹) i j
      rw [braidWord, coxeterMatrixA_eq_two (.inl h), braidWord,
        coxeterMatrixA_eq_two (.inr h), prod_map_alternatingWord_two,
        prod_map_alternatingWord_two] at hb
      exact hb)

/-- The regular representation takes the generator `T i` to the left regular operator of the
simple reflection `s i`. -/
@[simp]
theorem regularRep_T (i : Fin (n - 1)) :
    regularRep q cs (T q i) = cs.heckeLeftMul ((q : R) - ↑q⁻¹) i :=
  lift_T _ _ _ _ i

/-- In the regular representation, `T_w` takes the basis vector of `1` to that of `w`. -/
@[simp]
theorem regularRep_Tw_apply_single_one (w : W) :
    regularRep q cs (Tw q cs w) (single 1 1) = single w (1 : R) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hT : ⇑(regularRep q cs) ∘ T q = cs.heckeLeftMul ((q : R) - ↑q⁻¹) :=
    funext (regularRep_T cs)
  rw [Tw_wordProd cs hω, map_list_prod, List.map_map, hT,
    cs.prod_map_heckeLeftMul_apply_single_one _ hω]

/-- Evaluation of the regular representation at the basis vector of `1`. -/
private noncomputable def evalOne : TypeAHeckeAlgebra R q n →ₗ[R] W →₀ R :=
  LinearMap.applyₗ (single 1 1) ∘ₗ (regularRep q cs).toLinearMap

private theorem evalOne_apply (x : TypeAHeckeAlgebra R q n) :
    evalOne cs x = regularRep q cs x (single 1 1) :=
  (rfl)

/-- **The elements `T_w` are linearly independent** over every commutative ring and for every unit
parameter. -/
theorem linearIndependent_Tw : LinearIndependent R (Tw q cs : W → TypeAHeckeAlgebra R q n) := by
  refine LinearIndependent.of_comp (evalOne cs) ?_
  have h : ⇑(evalOne cs) ∘ Tw q cs = ⇑(Finsupp.basisSingleOne : Module.Basis W R (W →₀ R)) := by
    funext w
    simp [evalOne_apply]
  rw [h]
  exact Finsupp.basisSingleOne.linearIndependent

variable (q) in
/-- **The basis theorem**: the elements `T_w`, `w : W`, form a basis of the type-A Hecke algebra
over every commutative ring and for every unit parameter. -/
noncomputable def basisTw : Module.Basis W R (TypeAHeckeAlgebra R q n) :=
  .mk (linearIndependent_Tw cs) (span_range_Tw cs).ge

/-- The basis vectors of `TauCeti.TypeAHeckeAlgebra.basisTw` are the elements `T_w`. -/
@[simp]
theorem coe_basisTw : ⇑(basisTw q cs) = (Tw q cs : W → TypeAHeckeAlgebra R q n) :=
  Module.Basis.coe_mk _ _

/-- The coordinates of `x` in the basis `T_w` are the image under the regular representation of
`x` of the basis vector of `1`. -/
theorem basisTw_repr_apply (x : TypeAHeckeAlgebra R q n) :
    (basisTw q cs).repr x = regularRep q cs x (single 1 1) := by
  have h : ((basisTw q cs).repr : TypeAHeckeAlgebra R q n →ₗ[R] W →₀ R) = evalOne cs :=
    (basisTw q cs).ext fun w ↦ by
      rw [LinearEquiv.coe_coe, Module.Basis.repr_self, evalOne_apply, coe_basisTw,
        regularRep_Tw_apply_single_one]
  exact (LinearMap.congr_fun h x).trans (evalOne_apply cs x)

/-- **The regular representation is faithful.** -/
theorem regularRep_injective :
    Function.Injective (regularRep q cs : TypeAHeckeAlgebra R q n → Module.End R (W →₀ R)) :=
  fun x y h ↦ (basisTw q cs).repr.injective <| by
    rw [basisTw_repr_apply, basisTw_repr_apply, h]

/-- The type-A Hecke algebra is a free module, with basis the elements `T_w` of the abstract
Coxeter group of type `A_(n-1)`. -/
instance : Module.Free R (TypeAHeckeAlgebra R q n) :=
  .of_basis (basisTw q (CoxeterMatrix.A (n - 1)).toCoxeterSystem)

include cs in
/-- Over a nontrivial commutative ring, the rank of the type-A Hecke algebra is the order of the
Coxeter group `W` of type `A_(n-1)`. (When `W` is infinite, both sides are `0` by convention.) -/
theorem finrank_eq_natCard [Nontrivial R] :
    Module.finrank R (TypeAHeckeAlgebra R q n) = Nat.card W :=
  Module.finrank_eq_nat_card_basis (basisTw q cs)

end TypeAHeckeAlgebra

end TauCeti
