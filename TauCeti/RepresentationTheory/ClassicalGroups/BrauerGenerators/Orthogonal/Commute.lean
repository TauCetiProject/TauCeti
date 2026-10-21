/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Action

/-!
# The Brauer action commutes with the orthogonal group

The Brauer algebra `B_k(n)` acts on the tensor power `V^{⊗k}` of `V = Rⁿ` through the standard
symmetric form (`TauCeti.brauerActionOrth`), and the orthogonal group of that form acts on
`V^{⊗k}` diagonally. This file proves, over every commutative ring, that the two actions commute,
so that the image of the Brauer algebra lies in the commutant of the orthogonal group. This is
one inclusion of Brauer's orthogonal Schur-Weyl duality. Over `ℂ` the image is the whole
commutant, which is the first fundamental theorem of invariant theory for the orthogonal group;
that is not part of this file.

The commutation is proved for every Brauer diagram at once, rather than generator by generator.
Read the matrix of a diagram `D` in the monomial basis as a function of the labellings
`x : Fin k ⊕ Fin k → ι` of its `2k` boundary points: it is the indicator of the labellings
constant on the arcs of `D`, a product over the arcs of `D` of copies of the copairing
`∑ c, e_c ⊗ e_c`. A matrix `A` with `A * Aᵀ = 1` fixes the copairing, so applying `A` at every
boundary point fixes this indicator (`TauCeti.BrauerDiagram.sum_prod_mul_ite_isConstantOnArcs`).
Splitting the boundary into its bottom and top halves, this says `T * M * Tᵀ = M` for the matrix
`M` of `D` and the matrix `T` of the diagonal action of `A`, and `Tᵀ * T = 1` turns it into
`T * M = M * T`.

## Main results

* `TauCeti.BrauerDiagram.sum_prod_mul_ite_isConstantOnArcs`: the indicator of the labellings
  constant on the arcs of a Brauer diagram is invariant under a matrix `A` with `A * Aᵀ = 1`
  applied at every boundary point.
* `TauCeti.commute_brauerActionOrth_piTensorProductMap`: every element of the Brauer algebra acts
  on `(Rⁿ)^{⊗k}` commuting with the diagonal action of a matrix `A` with `Aᵀ * A = 1`.
* `TauCeti.commute_brauerActionOrth_tensorPower`: the Brauer action commutes with the diagonal
  action of the orthogonal group.
* `TauCeti.range_brauerActionOrth_le_centralizer`: the image of the Brauer algebra lies in the
  centralizer of the image of the orthogonal group.

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

variable {R : Type u} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- **The arc indicator of a Brauer diagram is orthogonally invariant.** Applying a matrix `A`
with `A * Aᵀ = 1` at every boundary point of `D` fixes the indicator of the labellings constant
on the arcs of `D`. Read as a tensor on the `2k` boundary points, the indicator is a product over
the arcs of copies of the copairing `∑ c, e_c ⊗ e_c`, which `A ⊗ A` fixes. -/
theorem sum_prod_mul_ite_isConstantOnArcs (D : BrauerDiagram k) {A : Matrix ι ι R}
    (hA : A * Aᵀ = 1) (x : Fin k ⊕ Fin k → ι) :
    ∑ y : Fin k ⊕ Fin k → ι, (∏ p, A (x p) (y p)) * (if D.IsConstantOnArcs y then 1 else 0) =
      if D.IsConstantOnArcs x then 1 else 0 := by
  -- A labelling constant on arcs is a free labelling of the arc transversal `S`, and along it the
  -- product over the boundary is a product over the arcs. The sum over labellings of `S` then
  -- factors over the arcs, each factor being an entry of `A * Aᵀ = 1`, and the product of these
  -- entries is the arc indicator of `x`.
  classical
  set S := D.arcTransversal
  set e := D.isConstantOnArcsEquiv (ι := ι)
  -- Along such a labelling, the product over the boundary is a product over the arcs.
  have hprod : ∀ z : S → ι, ∏ p, A (x p) ((e.symm z).1 p) =
      ∏ s : S, (A (x s) (z s) * A (x (D.val s)) (z s)) := by
    intro z
    rw [← D.isInvolutionTransversal_arcTransversal.prod_mul_prod_comp _
        (fun p _ => Finset.mem_univ _) (fun p _ => D.apply_apply p),
      ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun s _ => by
      rw [isConstantOnArcsEquiv_symm_apply_coe, isConstantOnArcsEquiv_symm_apply_val]
  -- Summing over the label of one arc meets the identity `A * Aᵀ = 1`.
  have hpair : ∀ s : S, ∑ c, A (x s) c * A (x (D.val s)) c =
      if x (D.val s) = x s then 1 else 0 := by
    intro s
    have := congrFun (congrFun hA (x s)) (x (D.val s))
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    rw [this]
    exact if_congr eq_comm rfl rfl
  calc ∑ y, (∏ p, A (x p) (y p)) * (if D.IsConstantOnArcs y then 1 else 0)
      = ∑ y : {y // D.IsConstantOnArcs y}, ∏ p, A (x p) (y.1 p) := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter, Finset.sum_subtype (p := D.IsConstantOnArcs) _ fun _ => by simp]
    _ = ∑ z : S → ι, ∏ s : S, (A (x s) (z s) * A (x (D.val s)) (z s)) := by
        rw [← e.symm.sum_comp]
        exact Finset.sum_congr rfl fun z _ => hprod z
    _ = ∏ s : S, ∑ c, A (x s) c * A (x (D.val s)) c :=
        (Fintype.prod_sum fun (s : S) c => A (x s) c * A (x (D.val s)) c).symm
    _ = ∏ s : S, if x (D.val s) = x s then 1 else 0 := Finset.prod_congr rfl fun s _ => hpair s
    _ = if D.IsConstantOnArcs x then 1 else 0 := by
        rw [Fintype.prod_boole]
        refine if_congr ?_ rfl rfl
        rw [D.isConstantOnArcs_iff_forall_mem_arcTransversal, Subtype.forall]

end BrauerDiagram

section CommSemiring

variable {R : Type u} [CommSemiring R] {n k : ℕ}

/-- **The Brauer action commutes with the diagonal action of an orthogonal matrix.** Every element
of the Brauer algebra `B_k(n)` acts on `(Rⁿ)^{⊗k}` commuting with `A ⊗ ⋯ ⊗ A` for every matrix `A`
with `Aᵀ * A = 1`. -/
theorem commute_brauerActionOrth_piTensorProductMap {A : Matrix (Fin n) (Fin n) R}
    (hA : Aᵀ * A = 1) (b : BrauerAlgebra R (n : R) k) :
    Commute (brauerActionOrth R n k b)
      (PiTensorProduct.map fun _ : Fin k => Matrix.mulVecLin A) := by
  rw [← (BrauerAlgebra.basis R (n : R) k).sum_repr b]
  simp only [map_sum, map_smul, BrauerAlgebra.basis_apply]
  refine Commute.sum_left _ _ _ fun D _ => Commute.smul_left ?_ _
  set T : Matrix (Fin k → Fin n) (Fin k → Fin n) R := Matrix.of fun v u => ∏ i, A (v i) (u i)
  set M := D.orthogonalActionMatrix R (Fin n)
  have hconj : T * M * Tᵀ = M := by
    ext v u
    have key := D.sum_prod_mul_ite_isConstantOnArcs (mul_eq_one_comm.mp hA) (Sum.elim u v)
    -- Split a labelling of the boundary into its bottom and top labellings.
    have helim : ∀ w w' : Fin k → Fin n,
        (Equiv.sumArrowEquivProdArrow _ _ _).symm (w, w') = Sum.elim w w' := fun w w' => by
      funext p
      rcases p with i | i <;> simp
    rw [← (Equiv.sumArrowEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type] at key
    simp only [helim, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at key
    simp only [T, M, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
      BrauerDiagram.orthogonalActionMatrix_apply, Finset.sum_mul]
    rw [← key]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
  have horth : Tᵀ * T = 1 := by
    -- `Tᵀ` is the matrix of `Aᵀ ⊗ ⋯ ⊗ Aᵀ`, so this is the functoriality of `PiTensorProduct.map`.
    have hTt : Tᵀ = Matrix.of fun v u => ∏ i, Aᵀ (v i) (u i) := by
      ext v u
      simp [T]
    rw [hTt, ← toMatrix_piTensorProductMap,
      show T = _ from (toMatrix_piTensorProductMap R n k A).symm, ← LinearMap.toMatrix_comp,
      ← PiTensorProduct.map_comp, ← Matrix.mulVecLin_mul, hA, Matrix.mulVecLin_one,
      PiTensorProduct.map_id, LinearMap.toMatrix_id]
  have hcomm : M * T = T * M := by
    calc M * T = T * M * Tᵀ * T := by rw [hconj]
      _ = T * M := by rw [Matrix.mul_assoc (T * M), horth, Matrix.mul_one]
  apply (LinearMap.toMatrix (tensorPowerBasis R n k) (tensorPowerBasis R n k)).injective
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, brauerActionOrth_of,
    LinearMap.toMatrix_toLin, toMatrix_piTensorProductMap]
  exact hcomm

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {n k : ℕ}

/-- **The Brauer action commutes with the orthogonal group.** Every element of the Brauer algebra
`B_k(n)` acts on `(Rⁿ)^{⊗k}` by an endomorphism commuting with the diagonal action of every element
of the orthogonal group of the standard symmetric form. -/
theorem commute_brauerActionOrth_tensorPower (g : Matrix.orthogonalGroup (Fin n) R)
    (b : BrauerAlgebra R (n : R) k) :
    Commute (brauerActionOrth R n k b) ((stdOrthogonalRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    commute_brauerActionOrth_piTensorProductMap
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) R).mp g.prop) b

/-- **The image of the Brauer algebra centralizes the orthogonal group**: it lies in the
centralizer of the image of the orthogonal group in the endomorphisms of `(Rⁿ)^{⊗k}`. -/
theorem range_brauerActionOrth_le_centralizer :
    (brauerActionOrth R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)) := by
  rintro _ ⟨b, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionOrth_tensorPower g b).symm.eq

end CommRing

end TauCeti
