/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Kronecker.Power
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action
-- Non-public: `SymplecticGroup.mem_iff` converts `Aᵀ * J * A = J` into `A * J * Aᵀ = J`, and
-- `Symplectic.TwoStrands` supplies the two-strand commutant span.
import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TwoStrands

/-!
# The Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymp` of the Brauer algebra `B_k(-2n)` on the tensor power
`((Fin n ⊕ Fin n) → R)^{⊗k}` commutes with the diagonal action `g ↦ g^{⊗k}` of every matrix `g`
preserving the standard alternating form `Matrix.J (Fin n) R`, that is, satisfying
`gᵀ * J * g = J`. Equivalently, the image of `B_k(-2n)` lies in the commutant of the symplectic
group acting on the tensor power (`TauCeti.range_brauerActionSymp_le_centralizer`). On two strands,
combining `TauCeti.range_brauerActionSymp_two` with
`TauCeti.adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer` upgrades this inclusion to an
equality (`TauCeti.range_brauerActionSymp_two_eq_centralizer`).

At the matrix level, every Brauer diagram `D` is obtained by stacking distinct-strand cap-cup
generators onto a permutation diagram without creating middle loops
(`TauCeti.BrauerDiagram.capCup_induction_on`). Because the loop count is zero at each step, the
loop rule `TauCeti.BrauerDiagram.symplecticActionMatrix_mul` expresses `M(D)` as a product of
matrices of permutation diagrams and cap-cup diagrams over any commutative ring `R` and finite
coordinate type `ι`, without dividing by the loop parameter. A permutation diagram commutes with
every Kronecker power `A^{⊗k}` by reindexing the product, while on `capCup a b` left-multiplying
`A^{⊗k}` contracts two columns of `A` through `Aᵀ * J * A = J` (the cap) and right-multiplying
`A^{⊗k}` expands two rows of `A` through `A * J * Aᵀ = J` (the cup).

## Main results

* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_permToBrauer_kroneckerPower`: the matrix of
  a permutation diagram commutes with the Kronecker power of any matrix.
* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`: the symplectic matrix of
  any Brauer diagram commutes with the Kronecker power of a matrix satisfying `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_piTensorProductMap`: every element of `B_k(-2n)` acts by an
  operator commuting with `A^{⊗k}` when `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_tensorPower` and
  `TauCeti.range_brauerActionSymp_le_centralizer`: equivariance under the tensor power of
  `TauCeti.stdSymplecticRep`, packaged as an inclusion into the commutant.
* `TauCeti.range_brauerActionSymp_two_eq_centralizer` and
  `TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`: **Brauer duality on two strands**
  for the symplectic group, identifying `(brauerActionSymp K n 2).range` with the full commutant.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Dipper, S. Doty, and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl
  duality*, Transactions of the American Mathematical Society 360 (2008), 189-213, §1.
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

/-- **The matrix of a permutation diagram commutes with every Kronecker power**, since reindexing
the factors of `∏ i, A (v i) (u i)` along `σ` leaves the product unchanged. -/
theorem commute_symplecticActionMatrix_permToBrauer_kroneckerPower
    (σ : Equiv.Perm (Fin k)) (A : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    Commute ((permToBrauer σ).symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  rw [Commute, SemiconjBy]
  ext v u
  have hcond (m : Fin k → ι ⊕ ι) : (v = fun j => m (σ.symm j)) ↔ m = v ∘ σ := by
    refine ⟨fun h => funext fun i => ?_, fun h => funext fun j => by simp [h]⟩
    simpa using (congrFun h (σ i)).symm
  have hlhs : ((permToBrauer σ).symplecticActionMatrix R ι * A.kroneckerPower (Fin k)) v u =
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : Fin k, A (v (σ i)) (u i) := by
    rw [Matrix.mul_apply]
    simp only [symplecticActionMatrix_permToBrauer, Matrix.kroneckerPower_apply, hcond, ite_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply]
  have hrhs : (A.kroneckerPower (Fin k) * (permToBrauer σ).symplecticActionMatrix R ι) v u =
      (∏ j : Fin k, A (v j) (u (σ.symm j))) * ((Equiv.Perm.sign σ : ℤ) : R) := by
    rw [Matrix.mul_apply]
    simp only [symplecticActionMatrix_permToBrauer, Matrix.kroneckerPower_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hprod : (∏ i : Fin k, A (v (σ i)) (u i)) = ∏ j : Fin k, A (v j) (u (σ.symm j)) :=
    (Finset.prod_congr (g := fun i => A (v (σ i)) (u (σ.symm (σ i)))) rfl
      fun i _ => by simp).trans (Equiv.prod_comp σ fun j => A (v j) (u (σ.symm j)))
  exact hlhs.trans ((congrArg (((Equiv.Perm.sign σ : ℤ) : R) * ·) hprod).trans
    ((mul_comm _ _).trans hrhs.symm))

/-- On a cap-cup generator `capCup a b` (`a ≠ b`), left-multiplying `A^{⊗k}` contracts columns
`u a` and `u b` through `Aᵀ * J * A = J`, while right-multiplying `A^{⊗k}` expands rows `v a` and
`v b` through `A * J * Aᵀ = J`. -/
private theorem commute_symplecticActionMatrix_capCup_kroneckerPower {a b : Fin k} (hab : a ≠ b)
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (hA : Aᵀ * Matrix.J ι R * A = Matrix.J ι R) :
    Commute ((capCup a b).symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  have hAcup : A * Matrix.J ι R * Aᵀ = Matrix.J ι R :=
    SymplecticGroup.mem_iff.mp (SymplecticGroup.mem_iff'.mpr hA)
  rw [Commute, SemiconjBy]
  ext v u
  let R₀ : R := ∏ t ∈ (Finset.univ.erase a).erase b, A (v t) (u t)
  have hK_left (x y : ι ⊕ ι) :
      A.kroneckerPower (Fin k) (Function.update (Function.update v a x) b y) u =
        A x (u a) * (A y (u b) * R₀) := by
    rw [Matrix.kroneckerPower_apply,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase (Finset.univ.erase a) _
        (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
    refine congrArg₂ (· * ·) (by simp [hab]) (congrArg₂ (· * ·) (by simp) ?_)
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at ht
    simp [ht.1, ht.2.1]
  have hK_right (x y : ι ⊕ ι) :
      A.kroneckerPower (Fin k) v (Function.update (Function.update u a x) b y) =
        A (v a) x * (A (v b) y * R₀) := by
    rw [Matrix.kroneckerPower_apply,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase (Finset.univ.erase a) _
        (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
    refine congrArg₂ (· * ·) (by simp [hab]) (congrArg₂ (· * ·) (by simp) ?_)
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at ht
    simp [ht.1, ht.2.1]
  have hcap_sum : ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        A x (u a) * Matrix.J ι R x y * A y (u b) =
      Matrix.J ι R (u a) (u b) := by
    have hm := congrFun (congrFun hA (u a)) (u b)
    rw [Matrix.mul_apply] at hm
    rw [← hm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [Matrix.transpose_apply]
  have hcup_sum : ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        A (v a) x * Matrix.J ι R x y * A (v b) y =
      Matrix.J ι R (v a) (v b) := by
    have hm := congrFun (congrFun hAcup (v a)) (v b)
    rw [Matrix.mul_apply] at hm
    rw [← hm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  have hcalc₁ (f : (ι ⊕ ι) → (ι ⊕ ι) → R) (g₁ g₂ : (ι ⊕ ι) → R) (c r : R) :
      ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, -(f x y * c) * (g₁ x * (g₂ y * r)) =
        -((∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, g₁ x * f x y * g₂ y) * (c * r)) := by
    have h1 (x y : ι ⊕ ι) : -(f x y * c) * (g₁ x * (g₂ y * r)) =
        -(g₁ x * f x y * g₂ y * (c * r)) := by ring
    simp only [h1, Finset.sum_neg_distrib, ← Finset.sum_mul]
  have hcalc₂ (f : (ι ⊕ ι) → (ι ⊕ ι) → R) (g₁ g₂ : (ι ⊕ ι) → R) (c r : R) :
      ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, (g₁ x * (g₂ y * r)) * -(c * f x y) =
        -(c * ((∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι, g₁ x * f x y * g₂ y) * r)) := by
    have h1 (x y : ι ⊕ ι) : (g₁ x * (g₂ y * r)) * -(c * f x y) =
        -(c * (g₁ x * f x y * g₂ y * r)) := by ring
    simp only [h1, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hlhs : ((capCup a b).symplecticActionMatrix R ι * A.kroneckerPower (Fin k)) v u =
      -(Matrix.J ι R (u a) (u b) * (Matrix.J ι R (v a) (v b) * R₀)) := by
    rw [symplecticActionMatrix_capCup_mul_apply R ι hab]
    simp only [hK_left]
    refine (hcalc₁ (Matrix.J ι R) (fun x => A x (u a)) (fun y => A y (u b)) _ _).trans ?_
    refine (congrArg (fun z => -(z * (Matrix.J ι R (v a) (v b) * R₀))) hcap_sum).trans ?_
    ring
  have hrhs : (A.kroneckerPower (Fin k) * (capCup a b).symplecticActionMatrix R ι) v u =
      -(Matrix.J ι R (u a) (u b) * (Matrix.J ι R (v a) (v b) * R₀)) := by
    rw [mul_symplecticActionMatrix_capCup_apply R ι hab]
    simp only [hK_right]
    refine (hcalc₂ (Matrix.J ι R) (fun x => A (v a) x) (fun y => A (v b) y) _ _).trans ?_
    exact congrArg (fun z => -(Matrix.J ι R (u a) (u b) * (z * R₀))) hcup_sum
  exact hlhs.trans hrhs.symm

/-- **The symplectic matrix of a Brauer diagram commutes with symplectic matrices.** For any matrix
`A` with `Aᵀ * Matrix.J ι R * A = Matrix.J ι R`, `TauCeti.BrauerDiagram.symplecticActionMatrix`
commutes with the Kronecker power `A.kroneckerPower (Fin k)`. -/
theorem commute_symplecticActionMatrix_kroneckerPower (D : BrauerDiagram k)
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (hA : Aᵀ * Matrix.J ι R * A = Matrix.J ι R) :
    Commute (D.symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  induction D using capCup_induction_on with
  | permToBrauer σ =>
    exact commute_symplecticActionMatrix_permToBrauer_kroneckerPower σ A
  | capCup_compose a b X hab hloop ih =>
    have hmul : (composeDiagram (capCup a b) X).symplecticActionMatrix R ι =
        (capCup a b).symplecticActionMatrix R ι * X.symplecticActionMatrix R ι := by
      rw [symplecticActionMatrix_mul, hloop, pow_zero, one_smul]
    rw [hmul]
    exact (commute_symplecticActionMatrix_capCup_kroneckerPower hab hA).mul_left ih

end BrauerDiagram

section CommRing

variable (R : Type u) [CommRing R] (n k : ℕ)

/-- **The symplectic Brauer action commutes with symplectic matrices.** Every element of `B_k(-2n)`
acts on `((Fin n ⊕ Fin n) → R)^{⊗k}` by an operator commuting with the diagonal action of each
matrix `A` preserving `Matrix.J (Fin n) R`. -/
theorem commute_brauerActionSymp_piTensorProductMap (x : BrauerAlgebra R (-(2 * n : R)) k)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : Aᵀ * Matrix.J (Fin n) R * A = Matrix.J (Fin n) R) :
    Commute (brauerActionSymp R n k x)
      (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  set B := Basis.piTensorProduct fun _ : Fin k => Pi.basisFun R (Fin n ⊕ Fin n)
  set T := PiTensorProduct.map fun _ : Fin k => A.mulVecLin
  have hT : T = Matrix.toLin B B (A.kroneckerPower (Fin k)) := by
    rw [← A.toMatrix_piTensorProductMap_mulVecLin (κ := Fin k), Matrix.toLin_toMatrix]
  have hlin : (LinearMap.mulRight R T).comp (brauerActionSymp R n k).toLinearMap =
      (LinearMap.mulLeft R T).comp (brauerActionSymp R n k).toLinearMap :=
    (BrauerAlgebra.basis R (-(2 * n : R)) k).ext fun D => by
      simp only [LinearMap.comp_apply, BrauerAlgebra.basis_apply, AlgHom.toLinearMap_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply, brauerActionSymp_of, hT, B]
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
        (D.commute_symplecticActionMatrix_kroneckerPower hA).eq]
  exact LinearMap.congr_fun hlin x

/-- **The Brauer algebra acts by intertwiners of the symplectic group.** Every element of `B_k(-2n)`
acts on `((Fin n ⊕ Fin n) → R)^{⊗k}` by an operator commuting with the tensor power of the standard
symplectic representation `TauCeti.stdSymplecticRep`. -/
theorem commute_brauerActionSymp_tensorPower (x : BrauerAlgebra R (-(2 * n : R)) k)
    (g : Matrix.symplecticGroup (Fin n) R) :
    Commute (brauerActionSymp R n k x) ((stdSymplecticRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymp_piTensorProductMap R n k x
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := R)).mp g.prop)

/-- **The image of `B_k(-2n)` lies in the commutant of the symplectic group** acting on
`((Fin n ⊕ Fin n) → R)^{⊗k}`. -/
theorem range_brauerActionSymp_le_centralizer :
    (brauerActionSymp R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdSymplecticRep R n).tensorPower k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymp_tensorPower R n k x g).symm.eq

end CommRing

section TwoStrands

/-- **Brauer duality for the symplectic group on two strands.** Over an integral domain containing a
unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`, the image of `B₂(-2n)` under `TauCeti.brauerActionSymp`
is the full commutant of the symplectic group on `K^{2n} ⊗ K^{2n}`. -/
theorem range_brauerActionSymp_two_eq_centralizer (K : Type u) [CommRing K] [IsDomain K] (n : ℕ)
    (ht : ∃ t : Kˣ, ∀ m : ℕ, 0 < m → m ≤ 4 → t ^ m ≠ 1) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) :=
  (range_brauerActionSymp_two K n).trans
    (adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer ht)

/-- **Brauer duality for the symplectic group on two strands in characteristic zero**: over any
field of characteristic zero, `(brauerActionSymp K n 2).range` equals the commutant of `Sp(2n, K)`
on `K^{2n} ⊗ K^{2n}`. -/
theorem range_brauerActionSymp_two_eq_centralizer_of_charZero (K : Type u) [Field K] [CharZero K]
    (n : ℕ) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) :=
  (range_brauerActionSymp_two K n).trans
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer_of_charZero

end TwoStrands

end TauCeti
