/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action
-- Non-public: double-update sums and `SymplecticGroup.mem_iff` evaluate the cap-cup matrix product.
import TauCeti.Data.Fintype.BigOperators
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymplectic` of the Brauer algebra `B_k(-2n)` on the tensor power
`(R^{2n})^{⊗k}` commutes with the diagonal action `g ↦ g^{⊗k}` of every matrix `g` preserving the
standard alternating form `Matrix.J (Fin n) R`, that is, with `gᵀ * J * g = J`. Equivalently, the
image of `B_k(-2n)` lies in the commutant of the symplectic group `Sp(2n)` acting diagonally on the
tensor power (`TauCeti.range_brauerActionSymplectic_le_centralizer`). This is the easy inclusion of
Brauer's Schur–Weyl duality for the symplectic group; the reverse inclusion requires hypotheses on
the base ring and is not part of this file.

In the monomial basis `TauCeti.symplecticTensorPowerBasis`, an operator `A^{⊗k}` acts by the
Kronecker power `A.kroneckerPower (Fin k)`:

* for a permutation diagram `permToBrauer σ`, its matrix commutes with `A.kroneckerPower (Fin k)`
  for *every* matrix `A`, by reindexing the `k`-fold product along `σ`
  (`TauCeti.BrauerDiagram.commute_symplecticActionMatrix_permToBrauer_kroneckerPower`);
* for a cap-cup diagram `capCup a b` (`a ≠ b`), multiplying on the right by `A^{⊗k}` contracts the
  two input slots through `Aᵀ * J * A = J`, while multiplying on the left contracts the two output
  slots through `A * J * Aᵀ = J`;
* induction along `TauCeti.BrauerDiagram.capCup_induction_on` together with the loop rule
  `TauCeti.BrauerDiagram.symplecticActionMatrix_mul` then extends commutation to every Brauer
  diagram (`TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`).

## Main results

* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_permToBrauer_kroneckerPower`: the symplectic
  matrix of a permutation diagram commutes with the Kronecker power of *any* matrix.
* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`: the symplectic matrix of
  any Brauer diagram commutes with the Kronecker power of a matrix satisfying `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymplectic_piTensorProductMap`: every element of `B_k(-2n)` acts by
  an operator commuting with `A^{⊗k}` when `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymplectic_tensorPower` and
  `TauCeti.range_brauerActionSymplectic_le_centralizer`: the image of `B_k(-2n)` commutes with the
  diagonal action of `Matrix.symplecticGroup (Fin n) R`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Dipper, S. Doty and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur–Weyl
  duality*, Trans. Amer. Math. Soc. 360 (2008), 189-213, §1.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

namespace BrauerDiagram

variable {k : ℕ} {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The symplectic matrix of a permutation diagram commutes with every Kronecker power**: the sign
factor commutes with scalars and `σ` reindexes the `k`-fold product of entries of `A`. -/
theorem commute_symplecticActionMatrix_permToBrauer_kroneckerPower (σ : Equiv.Perm (Fin k))
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    Commute ((permToBrauer σ).symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  ext v u
  have hcond (m : Fin k → ι ⊕ ι) : (m = v ∘ σ) ↔ m = fun i => v (σ i) := Iff.rfl
  have hcond' (m : Fin k → ι ⊕ ι) : (u = m ∘ σ) ↔ m = fun i => u (σ.symm i) := by
    refine ⟨fun h => funext fun i => by simpa using (congrFun h (σ.symm i)).symm, fun h => ?_⟩
    funext i
    simp [h]
  simp only [Matrix.mul_apply, symplecticActionMatrix_permToBrauer, kroneckerPower_apply,
    hcond, hcond', ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  rw [mul_comm]
  congr 1
  exact Fintype.prod_equiv σ _ _ fun _ => by simp

/-- For `a ≠ b` and `Aᵀ * J * A = J`, the symplectic matrix of `capCup a b` commutes with
`A.kroneckerPower (Fin k)`. -/
private theorem commute_symplecticActionMatrix_capCup_kroneckerPower {a b : Fin k} (hab : a ≠ b)
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (hA : Aᵀ * Matrix.J ι R * A = Matrix.J ι R) :
    Commute ((capCup a b).symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  have hA' : A * Matrix.J ι R * Aᵀ = Matrix.J ι R :=
    SymplecticGroup.mem_iff.mp (SymplecticGroup.mem_iff'.mpr hA)
  ext v u
  let P : R := ∏ t ∈ (Finset.univ.erase a).erase b, A (v t) (u t)
  have hprod (w : Fin k → ι ⊕ ι) (F : (ι ⊕ ι) → Fin k → R)
      (hP : ∏ t ∈ (Finset.univ.erase a).erase b, F (w t) t = P) (x y : ι ⊕ ι) :
      (∏ t : Fin k, F (Function.update (Function.update w a x) b y t) t) =
        F x a * F y b * P := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase (Finset.univ.erase a) _
        (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩), mul_assoc, ← hP]
    refine congrArg₂ (· * ·) (by simp [Function.update_of_ne hab])
      (congrArg₂ (· * ·) (by simp) (Finset.prod_congr rfl fun t ht => ?_))
    have htb : t ≠ b := (Finset.mem_erase.mp ht).1
    have hta : t ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    rw [Function.update_of_ne htb, Function.update_of_ne hta]
  have hcap_sum :
      (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, A x (u a) * Matrix.J ι R x y * A y (u b)) =
        Matrix.J ι R (u a) (u b) := by
    have h := congrFun (congrFun hA (u a)) (u b)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul] at h
    rwa [Finset.sum_comm]
  have hcup_sum :
      (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, A (v a) x * Matrix.J ι R x y * A (v b) y) =
        Matrix.J ι R (v a) (v b) := by
    have h := congrFun (congrFun hA' (v a)) (v b)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul] at h
    rwa [Finset.sum_comm]
  have hcond (f m : Fin k → ι ⊕ ι) :
      (∀ t, t ≠ a → t ≠ b → m t = f t) ↔
        m = Function.update (Function.update f a (m a)) b (m b) := by
    simp only [Function.eq_update_iff, true_and]
    refine ⟨fun h t htb => ?_, fun h t hta htb => (h t htb).trans (by simp [hta])⟩
    rcases eq_or_ne t a with rfl | hta <;> simp [*]
  have hsymm (m : Fin k → ι ⊕ ι) :
      (∀ t, t ≠ a → t ≠ b → v t = m t) ↔ ∀ t, t ≠ a → t ≠ b → m t = v t :=
    ⟨fun h t hta htb => (h t hta htb).symm, fun h t hta htb => (h t hta htb).symm⟩
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [symplecticActionMatrix_capCup R ι hab, kroneckerPower_apply, ite_mul, zero_mul,
    mul_ite, mul_zero]
  simp_rw [hsymm, hcond]
  refine (Fintype.sum_ite_eq_update_update (M := R) v hab _).trans
    (Eq.trans ?_ (Fintype.sum_ite_eq_update_update (M := R) u hab _).symm)
  simp only [Function.update_of_ne hab, Function.update_self,
    hprod v (fun z t => A z (u t)) rfl, hprod u (fun z t => A (v t) z) rfl]
  have hL :
      (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        -(Matrix.J ι R x y * Matrix.J ι R (v a) (v b)) * (A x (u a) * A y (u b) * P)) =
      (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, A x (u a) * Matrix.J ι R x y * A y (u b)) *
        (-(Matrix.J ι R (v a) (v b) * P)) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hR :
      (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        (A (v a) x * A (v b) y * P) * -(Matrix.J ι R (u a) (u b) * Matrix.J ι R x y)) =
      (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, A (v a) x * Matrix.J ι R x y * A (v b) y) *
        (-(Matrix.J ι R (u a) (u b) * P)) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hL, hR, hcap_sum, hcup_sum]
  ring

/-- **The symplectic matrix of any Brauer diagram commutes with symplectic matrices.** For every
matrix `A` with `Aᵀ * J * A = J`, `TauCeti.BrauerDiagram.symplecticActionMatrix` commutes with the
Kronecker power `A.kroneckerPower (Fin k)`. -/
theorem commute_symplecticActionMatrix_kroneckerPower (D : BrauerDiagram k)
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (hA : Aᵀ * Matrix.J ι R * A = Matrix.J ι R) :
    Commute (D.symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  induction D using BrauerDiagram.capCup_induction_on with
  | permToBrauer σ =>
    exact commute_symplecticActionMatrix_permToBrauer_kroneckerPower σ A
  | capCup_compose a b X hab hloop ih =>
    have hmul :
        (composeDiagram (capCup a b) X).symplecticActionMatrix R ι =
          (capCup a b).symplecticActionMatrix R ι * X.symplecticActionMatrix R ι := by
      rw [symplecticActionMatrix_mul R ι (capCup a b) X, hloop, pow_zero, one_smul]
    rw [hmul]
    exact (commute_symplecticActionMatrix_capCup_kroneckerPower hab hA).mul_left ih

end BrauerDiagram

/-! ### Equivariance of the Brauer algebra action -/

section Equivariance

variable (R : Type u) [CommRing R] (n k : ℕ)

/-- **The Brauer algebra `B_k(-2n)` commutes with symplectic matrices.** Every element of
`BrauerAlgebra R (-(2 * n : R)) k` acts on `(R^{2n})^{⊗k}` by an operator commuting with the
diagonal action of each matrix `A` satisfying `Aᵀ * J * A = J`. -/
theorem commute_brauerActionSymplectic_piTensorProductMap (x : BrauerAlgebra R (-(2 * n : R)) k)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : Aᵀ * Matrix.J (Fin n) R * A = Matrix.J (Fin n) R) :
    Commute (brauerActionSymplectic R n k x)
      (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  set T := PiTensorProduct.map fun _ : Fin k => A.mulVecLin
  have hT : T = Matrix.toLin (symplecticTensorPowerBasis R n k) (symplecticTensorPowerBasis R n k)
      (A.kroneckerPower (Fin k)) := by
    rw [← A.toMatrix_piTensorProductMap_symplecticTensorPowerBasis, Matrix.toLin_toMatrix]
  -- Both products are linear in `x`, so it suffices to compare them on the diagram basis.
  have hlin : (LinearMap.mulRight R T).comp (brauerActionSymplectic R n k).toLinearMap =
      (LinearMap.mulLeft R T).comp (brauerActionSymplectic R n k).toLinearMap :=
    (BrauerAlgebra.basis R (-(2 * n : R)) k).ext fun D => by
      simp only [LinearMap.comp_apply, BrauerAlgebra.basis_apply, AlgHom.toLinearMap_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply, brauerActionSymplectic_of, hT]
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
        (D.commute_symplecticActionMatrix_kroneckerPower hA).eq]
  exact LinearMap.congr_fun hlin x

/-- **The Brauer algebra acts by intertwiners of the symplectic group.** Every element of `B_k(-2n)`
acts on `(R^{2n})^{⊗k}` by an operator commuting with the tensor power of the standard
representation of `Matrix.symplecticGroup (Fin n) R`. -/
theorem commute_brauerActionSymplectic_tensorPower (x : BrauerAlgebra R (-(2 * n : R)) k)
    (g : Matrix.symplecticGroup (Fin n) R) :
    Commute (brauerActionSymplectic R n k x) ((stdSymplecticRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymplectic_piTensorProductMap R n k x
      (SymplecticGroup.mem_iff'.mp g.prop)

/-- **The image of `B_k(-2n)` lies in the commutant of the symplectic group** acting diagonally on
the tensor power `(R^{2n})^{⊗k}`. -/
theorem range_brauerActionSymplectic_le_centralizer :
    (brauerActionSymplectic R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdSymplecticRep R n).tensorPower k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymplectic_tensorPower R n k x g).symm.eq

end Equivariance

end TauCeti
