/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Product
public import Mathlib.LinearAlgebra.Trace

/-!
# Characters and characteristic polynomials of comodules

Let `M` be a comodule over `H`, finite free as a `k`-module; when `H` is a commutative Hopf
algebra, `M` is a finite-dimensional representation of the affine group scheme `G = Spec H`. Its
**character** `TauCeti.Comodule.character k H M ∈ H` is the regular function `g ↦ tr(g | M)`, and
its **characteristic polynomial** `TauCeti.Comodule.charpoly k H M ∈ H[X]` is the polynomial
`g ↦ det(X - g | M)` with coefficients in `H`. Both are defined through the universal point
`AlgHom.id k H`, whose action on `H ⊗[k] M` is the coaction read as an `H`-linear endomorphism;
in a basis, they are the trace and the characteristic polynomial of the coefficient matrix.
Evaluating them at any point `g : H →ₐ[k] A` gives the trace and characteristic polynomial of
the action of `g` on `A ⊗[k] M`.

The character is functorial in the coalgebra (`TauCeti.Comodule.character_corestrict`),
invariant under comodule isomorphism (`TauCeti.Comodule.character_eq_of_bijective`), additive on
products (`TauCeti.Comodule.character_prod`) and multiplicative on tensor products
(`TauCeti.Comodule.character_tensor`); a group-like comodule, in particular the trivial one, has a
multiple of its group-like element as character. The characteristic polynomial is monic of degree
the rank, multiplicative on products, functorial and isomorphism invariant, and determines the
character.

Over a Hopf algebra, the trace and the characteristic polynomial of a point action are unchanged
by conjugating the point (`TauCeti.Comodule.trace_endOfPoint_mul_mul_inv`,
`TauCeti.Comodule.charpoly_endOfPoint_mul_mul_inv`). This is what makes the character and the
coefficients of the characteristic polynomial regular class functions, in
`TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Character`.

## Main declarations

* `TauCeti.Comodule.character`: the character of a comodule, an element of `H`.
* `TauCeti.Comodule.apply_character`: its value at a point is the trace of the point action.
* `TauCeti.Comodule.charpoly`: the characteristic polynomial of a comodule, in `H[X]`.
* `TauCeti.Comodule.map_charpoly`: its image under a point is the characteristic polynomial of
  the point action.
* `TauCeti.Comodule.trace_endOfPoint_mul_mul_inv` and
  `TauCeti.Comodule.charpoly_endOfPoint_mul_mul_inv`: conjugate points act with equal traces and
  characteristic polynomials.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  §6.
-/
public section

open Module Polynomial TensorProduct WithConv

namespace TauCeti

namespace Comodule

universe u v w x

noncomputable section

section Coalgebra

variable (k : Type u) (H : Type v) (M : Type w)
variable [CommSemiring k] [CommSemiring H] [Algebra k H] [Coalgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- The **character** of a comodule `M` over `H`: the trace of the action of the universal point
`AlgHom.id k H` on `H ⊗[k] M`, that is of the coaction read as an `H`-linear endomorphism. For
`M` finite free over `k` its value at every point `g` is the trace of the action of `g`
(`TauCeti.Comodule.apply_character`), and in a basis it is the trace of the coefficient matrix
(`TauCeti.Comodule.character_eq_trace_coefficientMatrix`). -/
def character : H :=
  LinearMap.trace H (H ⊗[k] M) (endOfPoint M (AlgHom.id k H))

variable {k H M}

theorem character_def :
    character k H M = LinearMap.trace H (H ⊗[k] M) (endOfPoint M (AlgHom.id k H)) :=
  (rfl)

/-- In any finite basis, the character of a comodule is the trace of its coefficient matrix: the
sum of the diagonal matrix coefficients. -/
theorem character_eq_trace_coefficientMatrix {ι : Type x} [Fintype ι] (b : Basis ι k M) :
    character k H M = (coefficientMatrix (C := H) b).trace := by
  classical
  rw [character_def, LinearMap.trace_eq_matrix_trace H (b.baseChange H), toMatrix_endOfPoint,
    AlgHom.coe_id, Matrix.map_id]

variable [Module.Free k M] [Module.Finite k M]

/-- **The character computes traces.** The value of the character at a point `g` is the trace of
the action of `g` on the scalar extension. -/
@[simp]
theorem apply_character {A : Type*} [CommSemiring A] [Algebra k A] (g : H →ₐ[k] A) :
    g (character k H M) = LinearMap.trace A (A ⊗[k] M) (endOfPoint M g) := by
  classical
  let b := Free.chooseBasis k M
  rw [character_eq_trace_coefficientMatrix b, AddMonoidHom.map_trace,
    LinearMap.trace_eq_matrix_trace A (b.baseChange A), toMatrix_endOfPoint]

/-- Corestricting a comodule along a coalgebra morphism maps its character along that morphism. -/
theorem character_corestrict {H' : Type*} [CommSemiring H'] [Algebra k H'] [Coalgebra k H']
    (f : H →ₗc[k] H') :
    letI : Comodule k H' M := Corestrict f
    character k H' M = f (character k H M) := by
  classical
  let _ : Comodule k H' M := Corestrict f
  let b := Free.chooseBasis k M
  rw [character_eq_trace_coefficientMatrix b, character_eq_trace_coefficientMatrix b,
    coefficientMatrix_corestrict, AddMonoidHom.map_trace]

attribute [local instance] Prod in
/-- **Characters are additive.** The character of the product of two comodules is the sum of their
characters. -/
@[simp]
theorem character_prod {N : Type*} [AddCommMonoid N] [Module k N] [Comodule k H N]
    [Module.Free k N] [Module.Finite k N] :
    character k H (M × N) = character k H M + character k H N := by
  let b := Free.chooseBasis k M
  let c := Free.chooseBasis k N
  rw [character_eq_trace_coefficientMatrix (b.prod c), coefficientMatrix_prod,
    Matrix.trace_fromBlocks, ← character_eq_trace_coefficientMatrix,
    ← character_eq_trace_coefficientMatrix]

end Coalgebra

section GroupLike

variable {k : Type u} {H : Type v} {M : Type w}
variable [CommSemiring k] [AddCommMonoid M] [Module k M] [Module.Free k M] [Module.Finite k M]

/-- The character of a group-like comodule is its rank times the group-like element. -/
theorem character_groupLike [CommSemiring H] [Algebra k H] [Coalgebra k H] [StrongRankCondition k]
    (x : GroupLike k H) :
    letI : Comodule k H M := groupLike (R := k) (C := H) (M := M) x
    character k H M = finrank k M • (x : H) := by
  classical
  let _ : Comodule k H M := groupLike (R := k) (C := H) (M := M) x
  let b := Free.chooseBasis k M
  rw [character_eq_trace_coefficientMatrix b, finrank_eq_card_chooseBasisIndex, Matrix.trace]
  simp [coefficientMatrix_apply, matrixCoefficient_groupLike]

attribute [local instance] trivial in
/-- The character of a trivial comodule is its rank. -/
@[simp]
theorem character_trivial [CommSemiring H] [Bialgebra k H] [StrongRankCondition k] :
    character k H M = (finrank k M : H) := by
  rw [character_groupLike, GroupLike.val_one, nsmul_eq_mul, mul_one]

end GroupLike

section HopfAlgebra

variable {k : Type u} {H : Type v} {M : Type w}
variable [CommSemiring k] [Semiring H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- **Traces of point actions are conjugation invariant.** Conjugate points act on a comodule with
equal traces. -/
theorem trace_endOfPoint_mul_mul_inv {A : Type*} [CommSemiring A] [Algebra k A]
    (g x : WithConv (H →ₐ[k] A)) :
    LinearMap.trace A (A ⊗[k] M) (endOfPoint M (g * x * g⁻¹).ofConv) =
      LinearMap.trace A (A ⊗[k] M) (endOfPoint M x.ofConv) := by
  rw [endOfPoint_convMul, endOfPoint_convMul, ← Module.End.mul_eq_comp,
    LinearMap.trace_mul_comm, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
    endOfPoint_inv_comp, LinearMap.id_comp]

/-- Conjugate points act on a finite free comodule with equal characteristic polynomials. -/
theorem charpoly_endOfPoint_mul_mul_inv [Module.Free k M] [Module.Finite k M]
    {A : Type*} [CommRing A] [Algebra k A] (g x : WithConv (H →ₐ[k] A)) :
    (endOfPoint M (g * x * g⁻¹).ofConv).charpoly = (endOfPoint M x.ofConv).charpoly := by
  have h : endOfPoint M (g * x * g⁻¹).ofConv = (pointsAction M g).conj (endOfPoint M x.ofConv) := by
    rw [LinearEquiv.conj_apply, endOfPoint_convMul, endOfPoint_convMul, pointsAction_toLinearMap,
      ← pointsAction_toLinearMap M g⁻¹, map_inv]
    -- The inverse in the automorphism group `(A ⊗[k] M) ≃ₗ[A] (A ⊗[k] M)` is `symm` by
    -- definition; Mathlib states this only for the underlying function (`LinearEquiv.coe_inv`).
    rfl
  rw [h, LinearEquiv.charpoly_conj]

end HopfAlgebra

section Isomorphism

variable {k : Type u} {H : Type v} {M : Type w}
variable [CommSemiring k] [Semiring H] [Algebra k H] [Coalgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- A comodule isomorphism conjugates the point actions: after scalar extension along any point,
the action on the target is the conjugate of the action on the source. -/
theorem endOfPoint_eq_conj_of_bijective {N : Type*} [AddCommMonoid N] [Module k N]
    [Comodule k H N] (f : Hom k H M N) (hf : Function.Bijective f) {A : Type*} [CommSemiring A]
    [Algebra k A] (g : H →ₐ[k] A) :
    endOfPoint N g =
      ((LinearEquiv.ofBijective f.toLinearMap hf).baseChange k A M N).conj (endOfPoint M g) := by
  rw [LinearEquiv.conj_apply, LinearEquiv.eq_comp_toLinearMap_symm]
  exact (baseChange_comp_endOfPoint f g).symm

end Isomorphism

section RingCoalgebra

variable {k : Type u} {H : Type v} {M : Type w}
variable [CommSemiring k] [CommRing H] [Algebra k H] [Coalgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- The character of a comodule is unchanged under an isomorphism of comodules. -/
theorem character_eq_of_bijective {N : Type*} [AddCommMonoid N] [Module k N] [Comodule k H N]
    (f : Hom k H M N) (hf : Function.Bijective f) :
    character k H N = character k H M := by
  rw [character_def, character_def, endOfPoint_eq_conj_of_bijective f hf,
    LinearMap.trace_conj']

variable [Module.Free k M] [Module.Finite k M]

variable (k H M) in
/-- The **characteristic polynomial** of a comodule `M` over `H`: the characteristic polynomial,
with coefficients in `H`, of the action of the universal point `AlgHom.id k H` on `H ⊗[k] M`. For
`M` finite free over `k` its image under every point `g` is the characteristic polynomial of the
action of `g` (`TauCeti.Comodule.map_charpoly`). -/
def charpoly : H[X] :=
  (endOfPoint M (AlgHom.id k H)).charpoly

theorem charpoly_def : charpoly k H M = (endOfPoint M (AlgHom.id k H)).charpoly :=
  (rfl)

/-- In any finite basis, the characteristic polynomial of a comodule is the characteristic
polynomial of its coefficient matrix. -/
theorem charpoly_eq_charpoly_coefficientMatrix {ι : Type x} [Fintype ι] [DecidableEq ι]
    (b : Basis ι k M) :
    charpoly k H M = (coefficientMatrix (C := H) b).charpoly := by
  rw [charpoly_def, ← LinearMap.charpoly_toMatrix _ (b.baseChange H), toMatrix_endOfPoint,
    AlgHom.coe_id, Matrix.map_id]

/-- **The characteristic polynomial computes characteristic polynomials.** The image of the
characteristic polynomial of a comodule under a point `g` is the characteristic polynomial of the
action of `g` on the scalar extension. -/
@[simp]
theorem map_charpoly {A : Type*} [CommRing A] [Algebra k A] (g : H →ₐ[k] A) :
    (charpoly k H M).map (g : H →+* A) = (endOfPoint M g).charpoly := by
  rw [charpoly_def, ← charpoly_endOfPoint_comp, AlgHom.comp_id]

/-- The coefficient of the characteristic polynomial of a comodule, evaluated at a point, is the
corresponding coefficient of the characteristic polynomial of the point action. -/
@[simp]
theorem apply_coeff_charpoly {A : Type*} [CommRing A] [Algebra k A] (g : H →ₐ[k] A) (n : ℕ) :
    g ((charpoly k H M).coeff n) = (endOfPoint M g).charpoly.coeff n := by
  rw [← map_charpoly, coeff_map, AlgHom.coe_toRingHom]

/-- The characteristic polynomial of a comodule is monic. -/
theorem charpoly_monic : (charpoly k H M).Monic :=
  LinearMap.charpoly_monic _

/-- The degree of the characteristic polynomial of a comodule is its rank. -/
@[simp]
theorem natDegree_charpoly [StrongRankCondition k] :
    (charpoly k H M).natDegree = finrank k M := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · -- Over the zero coalgebra the coaction vanishes, so the comodule does.
    have : Subsingleton M := coact_eq_zero_iff (R := k) (C := H).mp (Subsingleton.elim _ _)
    rw [finrank_zero_of_subsingleton, Polynomial.natDegree_of_subsingleton]
  · rw [charpoly_def, LinearMap.charpoly_natDegree, finrank_baseChange]

/-- The character is the negative of the subleading coefficient of the characteristic
polynomial. -/
theorem character_eq_neg_coeff_charpoly [StrongRankCondition k] (h : 0 < finrank k M) :
    character k H M = -(charpoly k H M).coeff (finrank k M - 1) := by
  classical
  let b := Free.chooseBasis k M
  have : Nonempty (Free.ChooseBasisIndex k M) := by
    rw [← Fintype.card_pos_iff, ← finrank_eq_card_chooseBasisIndex]
    exact h
  rw [character_eq_trace_coefficientMatrix b, charpoly_eq_charpoly_coefficientMatrix b,
    Matrix.trace_eq_neg_charpoly_coeff, finrank_eq_card_chooseBasisIndex]

attribute [local instance] Prod in
/-- The characteristic polynomial of the product of two comodules is the product of their
characteristic polynomials. -/
@[simp]
theorem charpoly_prod {N : Type*} [AddCommMonoid N] [Module k N] [Comodule k H N]
    [Module.Free k N] [Module.Finite k N] :
    charpoly k H (M × N) = charpoly k H M * charpoly k H N := by
  classical
  let b := Free.chooseBasis k M
  let c := Free.chooseBasis k N
  rw [charpoly_eq_charpoly_coefficientMatrix (b.prod c), coefficientMatrix_prod,
    Matrix.charpoly_fromBlocks_zero₁₂, ← charpoly_eq_charpoly_coefficientMatrix,
    ← charpoly_eq_charpoly_coefficientMatrix]

/-- The characteristic polynomial of a comodule is unchanged under an isomorphism of
comodules. -/
theorem charpoly_eq_of_bijective {N : Type*} [AddCommMonoid N] [Module k N] [Comodule k H N]
    [Module.Free k N] [Module.Finite k N] (f : Hom k H M N) (hf : Function.Bijective f) :
    charpoly k H N = charpoly k H M := by
  rw [charpoly_def, charpoly_def, endOfPoint_eq_conj_of_bijective f hf,
    LinearEquiv.charpoly_conj]

end RingCoalgebra

section RingBialgebra

variable {k : Type u} {H : Type v} {M : Type w}
variable [CommSemiring k] [CommRing H] [Bialgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M] [Module.Free k M] [Module.Finite k M]

attribute [local instance] tensor in
/-- **Characters are multiplicative.** The character of the diagonal tensor product of two
comodules is the product of their characters. -/
@[simp]
theorem character_tensor {N : Type*} [AddCommMonoid N] [Module k N] [Comodule k H N]
    [Module.Free k N] [Module.Finite k N] :
    character k H (M ⊗[k] N) = character k H M * character k H N := by
  let e := TensorProduct.AlgebraTensorModule.distribBaseChange k H M N
  have he : endOfPoint (M ⊗[k] N) (AlgHom.id k H) =
      e.symm.conj (TensorProduct.map (endOfPoint M (AlgHom.id k H))
        (endOfPoint N (AlgHom.id k H))) := by
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm, endOfPoint_tensor, LinearMap.comp_assoc,
      ← LinearEquiv.coe_trans, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.comp_id]
  rw [character_def, character_def, character_def, he]
  exact (LinearMap.trace_conj' _ _).trans (LinearMap.trace_tensorProduct' _ _)

/-- Corestricting a comodule along a bialgebra morphism maps its characteristic polynomial along
that morphism. -/
theorem charpoly_corestrict {H' : Type*} [CommRing H'] [Bialgebra k H'] (φ : H →ₐc[k] H') :
    letI : Comodule k H' M := Corestrict φ.toCoalgHom
    charpoly k H' M = (charpoly k H M).map (φ : H →+* H') := by
  classical
  let _ : Comodule k H' M := Corestrict φ.toCoalgHom
  let b := Free.chooseBasis k M
  rw [charpoly_eq_charpoly_coefficientMatrix b, charpoly_eq_charpoly_coefficientMatrix b,
    coefficientMatrix_corestrict, ← Matrix.charpoly_map, RingHom.coe_coe]
  exact congrArg (fun F ↦ ((coefficientMatrix b).map F).charpoly) (funext φ.toCoalgHom_apply)

end RingBialgebra

end

end Comodule

end TauCeti
