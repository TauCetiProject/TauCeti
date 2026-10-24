/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Action

/-!
# The Brauer algebra acts by intertwiners of the orthogonal group

The action `TauCeti.brauerActionOrth` of the Brauer algebra `B_k(n)` on the tensor power
`(Rⁿ)^{⊗k}` commutes with the diagonal action `g ↦ g^{⊗k}` of every matrix `g` preserving the
standard symmetric form, that is, with `gᵀ * g = 1`. Equivalently, the image of the Brauer algebra
lies in the commutant of the orthogonal group acting on the tensor power
(`TauCeti.range_brauerActionOrth_le_centralizer`). This is the easy half of Brauer's
Schur-Weyl duality for the orthogonal group; the converse inclusion, the first fundamental theorem
of invariant theory for `O(n)`, needs more hypotheses on `R` and is not part of this file.

The proof works one diagram at a time and does not use generators of the Brauer algebra. In the
monomial basis a diagram `D` acts by the matrix `M` whose `(v, u)` entry is `1` when the labelling
`Sum.elim u v` of the `2 * k` boundary points is constant on the arcs of `D`, and `g^{⊗k}` acts by
the Kronecker power `K = Matrix.kroneckerPower (Fin k) g` with `(v, u)` entry `∏ i, g (v i) (u i)`.
Conjugating `M` by `K` sums, over the labellings `m` constant on the arcs of `D`, the product of the
entries `g (ℓ x) (m x)` at all boundary points `x`, where `ℓ` is the outer labelling. Such an `m` is
the same as a free choice of one label per arc (`TauCeti.BrauerDiagram.isConstantOnArcsEquiv`), so
the sum factors as a product over the arcs, and the factor of an arc with endpoints `x` and `y` is
`∑ c, g (ℓ x) c * g (ℓ y) c = (g * gᵀ) (ℓ x) (ℓ y)`, which is `1` when `ℓ x = ℓ y` and `0` otherwise
(`TauCeti.BrauerDiagram.sum_isConstantOnArcs_prod_apply`). So `K * M * Kᵀ = M`, and since also
`Kᵀ * K = 1` the matrices `M` and `K` commute.

## Main results

* `TauCeti.BrauerDiagram.sum_isConstantOnArcs_prod_apply`: the invariance of the arc tensor of a
  Brauer diagram under a matrix with `A * Aᵀ = 1`.
* `TauCeti.BrauerDiagram.commute_orthogonalActionMatrix_kroneckerPower`: the matrix of a Brauer
  diagram commutes with the Kronecker power of a matrix with `Aᵀ * A = 1`.
* `TauCeti.commute_brauerActionOrth_piTensorProductMap`: every element of the Brauer algebra acts by
  an operator commuting with `A^{⊗k}` when `Aᵀ * A = 1`.
* `TauCeti.commute_brauerActionOrth_tensorPower` and
  `TauCeti.range_brauerActionOrth_le_centralizer`: the same for the tensor power of the standard
  representation of the orthogonal group, packaged as an inclusion of the image of the Brauer
  algebra in the commutant of the group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open Matrix

namespace TauCeti

universe u

namespace BrauerDiagram

variable {k : ℕ}

variable {R : Type u} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The arc tensor of a Brauer diagram is invariant.** For a matrix `A` with `A * Aᵀ = 1`,
summing the products `∏ x, A (ℓ x) (m x)` over the labellings `m` of the boundary points constant
on the arcs of `D` gives `1` when the labelling `ℓ` is itself constant on the arcs of `D`, and `0`
otherwise. In other words, the tensor `∑ m, e_m` over those labellings, the product over the arcs
of the copairing `∑ c, e_c ⊗ e_c`, is fixed by `A` acting on every boundary point. -/
theorem sum_isConstantOnArcs_prod_apply (D : BrauerDiagram k) {A : Matrix ι ι R}
    (hA : A * Aᵀ = 1) (ℓ : Fin k ⊕ Fin k → ι) :
    ∑ m with D.IsConstantOnArcs m, ∏ x, A (ℓ x) (m x) =
      if D.IsConstantOnArcs ℓ then 1 else 0 := by
  -- The factor of an arc is an entry of `A * Aᵀ = 1`.
  have harc : ∀ x, ∑ c, A (ℓ x) c * A (ℓ (D.val x)) c =
      if ℓ (D.val x) = ℓ x then 1 else 0 := fun x => by
    have h := congrFun (congrFun hA (ℓ x)) (ℓ (D.val x))
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    rw [h]
    exact if_congr eq_comm rfl rfl
  rw [Finset.sum_subtype (p := D.IsConstantOnArcs) _ (fun m => by simp),
    ← (D.isConstantOnArcsEquiv (ι := ι)).symm.sum_comp]
  calc ∑ g : {x // D.IsLowerEnd x} → ι, ∏ x, A (ℓ x) ((D.isConstantOnArcsEquiv.symm g).1 x)
      = ∑ g : {x // D.IsLowerEnd x} → ι, ∏ x : {x // D.IsLowerEnd x},
          A (ℓ x) (g x) * A (ℓ (D.val x)) (g x) := by
        refine Fintype.sum_congr _ _ fun g => ?_
        rw [prod_eq_prod_isLowerEnd D]
        refine Fintype.prod_congr _ _ fun x => ?_
        simp [isConstantOnArcsEquiv_symm_apply, x.2, D.not_isLowerEnd_val x.2, D.apply_apply]
    _ = ∏ x : {x // D.IsLowerEnd x}, if ℓ (D.val x) = ℓ x then 1 else 0 := by
        exact (Fintype.prod_sum fun (x : {x // D.IsLowerEnd x}) c =>
          A (ℓ x) c * A (ℓ (D.val x)) c).symm.trans (Fintype.prod_congr _ _ fun x => harc x)
    _ = if D.IsConstantOnArcs ℓ then 1 else 0 := by
        -- Equality across every arc, read at the lower ends, is constancy on the arcs.
        refine Fintype.prod_boole.trans (if_congr ⟨fun h => (D.isConstantOnArcs_def ℓ).mpr
          fun x => ?_, fun hℓ x => (D.isConstantOnArcs_def ℓ).mp hℓ x⟩ rfl rfl)
        by_cases hlx : D.IsLowerEnd x
        · exact h ⟨x, hlx⟩
        · have hx := h ⟨D.val x, D.isLowerEnd_val_of_not_isLowerEnd hlx⟩
          rw [D.apply_apply] at hx
          exact hx.symm

/-- **The matrix of a Brauer diagram commutes with orthogonal matrices.** For a matrix `A` with
`Aᵀ * A = 1`, the matrix `TauCeti.BrauerDiagram.orthogonalActionMatrix` of `D` commutes with the
Kronecker power of `A`, the matrix of `A` acting diagonally on the `k`-th tensor power. -/
theorem commute_orthogonalActionMatrix_kroneckerPower (D : BrauerDiagram k)
    {A : Matrix ι ι R} (hA : Aᵀ * A = 1) :
    Commute (D.orthogonalActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  set K := A.kroneckerPower (Fin k)
  set M := D.orthogonalActionMatrix R ι
  -- Conjugating `M` by `K` is the sum of `sum_isConstantOnArcs_prod_apply` at `Sum.elim u v`.
  have hconj : K * M * Kᵀ = M := by
    ext v u
    have hprod : ∀ m : Fin k ⊕ Fin k → ι, ∏ x, A (Sum.elim u v x) (m x) =
        (∏ i, A (v i) (m (Sum.inr i))) * ∏ j, A (u j) (m (Sum.inl j)) := fun m => by
      rw [Fintype.prod_sum_type, mul_comm]
      simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Matrix.mul_apply]
    simp only [K, M, Matrix.mul_apply, Matrix.transpose_apply, kroneckerPower_apply,
      orthogonalActionMatrix_apply, mul_ite, mul_one, mul_zero, Finset.sum_mul, ite_mul, zero_mul]
    rw [← D.sum_isConstantOnArcs_prod_apply (mul_eq_one_comm.mp hA)
      (Sum.elim u v), Finset.sum_filter,
      ← (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) ι).symm.sum_comp, Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun w' => Fintype.sum_congr _ _ fun w => ?_
    have hsymm : (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) ι).symm (w', w) = Sum.elim w' w :=
      funext fun x => by cases x <;> simp
    rw [hsymm, hprod]
    simp
  calc M * K = K * M * Kᵀ * K := by rw [hconj]
    _ = K * M := by rw [Matrix.mul_assoc, transpose_kroneckerPower_mul_self hA, Matrix.mul_one]

end BrauerDiagram

variable (R : Type u) (n k : ℕ)

section CommSemiring

variable [CommSemiring R]

/-- **The Brauer algebra commutes with orthogonal matrices.** Every element of the Brauer algebra
`B_k(n)` acts on `(Rⁿ)^{⊗k}` by an operator commuting with the diagonal action of each matrix `A`
with `Aᵀ * A = 1`. -/
theorem commute_brauerActionOrth_piTensorProductMap (x : BrauerAlgebra R (n : R) k)
    {A : Matrix (Fin n) (Fin n) R} (hA : Aᵀ * A = 1) :
    Commute (brauerActionOrth R n k x) (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  set T := PiTensorProduct.map fun _ : Fin k => A.mulVecLin
  have hT : T = Matrix.toLin (tensorPowerBasis R n k) (tensorPowerBasis R n k)
      (A.kroneckerPower (Fin k)) := by
    rw [← A.toMatrix_piTensorProductMap_tensorPowerBasis, Matrix.toLin_toMatrix]
  -- Both products are linear in `x`, so it suffices to compare them on the diagram basis.
  have hlin : (LinearMap.mulRight R T).comp (brauerActionOrth R n k).toLinearMap =
      (LinearMap.mulLeft R T).comp (brauerActionOrth R n k).toLinearMap :=
    (BrauerAlgebra.basis R (n : R) k).ext fun D => by
      simp only [LinearMap.comp_apply, BrauerAlgebra.basis_apply, AlgHom.toLinearMap_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply, brauerActionOrth_of, hT]
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
        (D.commute_orthogonalActionMatrix_kroneckerPower hA).eq]
  exact LinearMap.congr_fun hlin x

end CommSemiring

section CommRing

variable [CommRing R]

/-- **The Brauer algebra acts by intertwiners of the orthogonal group.** Every element of the
Brauer algebra `B_k(n)` acts on `(Rⁿ)^{⊗k}` by an operator commuting with the tensor power of the
standard representation of the orthogonal group. -/
theorem commute_brauerActionOrth_tensorPower (x : BrauerAlgebra R (n : R) k)
    (g : Matrix.orthogonalGroup (Fin n) R) :
    Commute (brauerActionOrth R n k x) ((stdOrthogonalRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    commute_brauerActionOrth_piTensorProductMap R n k x
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) R).mp g.prop)

/-- **The image of the Brauer algebra lies in the commutant of the orthogonal group** acting on the
tensor power `(Rⁿ)^{⊗k}`. -/
theorem range_brauerActionOrth_le_centralizer :
    (brauerActionOrth R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionOrth_tensorPower R n k x g).symm.eq

end CommRing

end TauCeti
