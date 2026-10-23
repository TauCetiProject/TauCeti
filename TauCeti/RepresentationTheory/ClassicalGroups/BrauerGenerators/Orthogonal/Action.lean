/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerAlgebra.Basic
public import TauCeti.Combinatorics.Brauer.Labelling
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.TensorPower

/-!
# The Brauer algebra acting on a tensor power of `Rⁿ`

Equip `V = Rⁿ` with its standard symmetric bilinear form, the coordinate dot product, whose
copairing is `∑ c, e_c ⊗ e_c`. A Brauer diagram `D` on `k` strands acts on the tensor power
`V^{⊗k}`: its through strands carry tensor slots from the bottom to the top, its caps contract two
input slots against the form, and its cups insert the copairing into two output slots. In the
monomial basis `TauCeti.tensorPowerBasis` the coefficient of the output basis tensor `e_v` in the
image of the input basis tensor `e_u` is `1` when the labelling `Sum.elim u v` of the boundary
points of `D` is constant on its arcs, and `0` otherwise
(`TauCeti.BrauerDiagram.orthogonalActionMatrix`).

These operators multiply by the loop rule of the Brauer algebra at the loop value `δ = n`, a closed
loop evaluating to the trace `n` of the form
(`TauCeti.BrauerDiagram.orthogonalActionMatrix_mul`, which rests on the count
`TauCeti.BrauerDiagram.natCard_middleLabelling`), so they assemble into an algebra map
`TauCeti.brauerActionOrth` from the Brauer algebra `B_k(n)` to the endomorphisms of
`V^{⊗k}`. It extends the two families of generators already available: on a permutation diagram
it is the permutation action `TauCeti.permTensorAction` of `Sₖ` on the tensor factors, so it
restricts along `TauCeti.BrauerAlgebra.ofPerm` to the group-algebra action
`TauCeti.permTensorActionAlgHom`; and on the cap-cup diagram on two distinct strands it is the
single-arc generator `TauCeti.orthogonalCupCapAt`.

This is the action through which the Brauer algebra is the partner of the orthogonal group in
Schur-Weyl duality: over `ℂ` (more generally, over an algebraically closed field of characteristic
zero), its image is the commutant of the diagonal action of the form-orthogonal group of `V`
(Brauer's theorem). That theorem does not hold over an arbitrary commutative semiring, and it is
not part of this file.

## Main definitions

* `TauCeti.BrauerDiagram.orthogonalActionMatrix`: the matrix of a Brauer diagram acting on the
  tensor power of `ι → R`, indexed by the labellings of the strands.
* `TauCeti.brauerActionOrth`: the action of the Brauer algebra `B_k(n)` on `(Rⁿ)^{⊗k}`.

## Main results

* `TauCeti.BrauerDiagram.orthogonalActionMatrix_mul`: **the loop rule for the matrices**,
  `M(D₁) * M(D₂) = |ι| ^ c • M(D₁ ∘ D₂)` with `c` the number of closed middle loops.
* `TauCeti.brauerActionOrth_of_tensorPowerBasis`: a diagram sends a monomial basis tensor to the
  sum of the basis tensors whose labels, together with those of the input, are constant on its
  arcs.
* `TauCeti.brauerActionOrth_of_permToBrauer` and `TauCeti.brauerActionOrth_comp_ofPerm`: on the
  permutation diagrams the action is the permutation action of the symmetric group.
* `TauCeti.brauerActionOrth_of_capCup`: on a cap-cup diagram the action is the single-arc
  generator `TauCeti.orthogonalCupCapAt`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

namespace BrauerDiagram

variable (R : Type u) [CommSemiring R] (ι : Type*) [DecidableEq ι] {k : ℕ}

/-- **The matrix of a Brauer diagram** acting on the `k`-th tensor power of `ι → R` with its
standard symmetric form, in the monomial basis indexed by the labellings `Fin k → ι` of the strands:
the entry in the row of the output labelling `v` and the column of the input labelling `u` is `1`
when `Sum.elim u v` is constant on the arcs of `D`, and `0` otherwise. -/
def orthogonalActionMatrix (D : BrauerDiagram k) : Matrix (Fin k → ι) (Fin k → ι) R :=
  Matrix.of fun v u => if D.IsConstantOnArcs (Sum.elim u v) then 1 else 0

@[simp]
theorem orthogonalActionMatrix_apply (D : BrauerDiagram k) (v u : Fin k → ι) :
    D.orthogonalActionMatrix R ι v u = if D.IsConstantOnArcs (Sum.elim u v) then 1 else 0 :=
  (rfl)

/-- The identity diagram has the identity matrix. -/
@[simp]
theorem orthogonalActionMatrix_permToBrauer_one :
    (permToBrauer 1).orthogonalActionMatrix R ι = (1 : Matrix (Fin k → ι) (Fin k → ι) R) := by
  ext v u
  simp [isConstantOnArcs_permToBrauer_iff, Matrix.one_apply, ← funext_iff]

/-- **The loop rule for the matrices of Brauer diagrams.** The matrix of `D₁` times the matrix of
`D₂` is the matrix of the composite `TauCeti.composeDiagram D₁ D₂`, scaled by `|ι|` to the number of
closed middle loops: summing over the labellings of the middle boundary counts the free labels of
those loops. -/
theorem orthogonalActionMatrix_mul [Fintype ι] (D₁ D₂ : BrauerDiagram k) :
    D₁.orthogonalActionMatrix R ι * D₂.orthogonalActionMatrix R ι =
      (Fintype.card ι : R) ^ middleLoopCount D₁ D₂ •
        (composeDiagram D₁ D₂).orthogonalActionMatrix R ι := by
  ext v u
  have hsum : (D₁.orthogonalActionMatrix R ι * D₂.orthogonalActionMatrix R ι) v u =
      (Nat.card {m : Fin k → ι // D₁.IsConstantOnArcs (Sum.elim m v) ∧
        D₂.IsConstantOnArcs (Sum.elim u m)} : R) := by
    simp only [Matrix.mul_apply, orthogonalActionMatrix_apply, ite_zero_mul_ite_zero, mul_one]
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsum, Matrix.smul_apply, orthogonalActionMatrix_apply, smul_eq_mul]
  split_ifs with hC
  · rw [natCard_middleLabelling hC, Nat.card_eq_fintype_card, mul_one, Nat.cast_pow]
  · have : IsEmpty {m : Fin k → ι // D₁.IsConstantOnArcs (Sum.elim m v) ∧
        D₂.IsConstantOnArcs (Sum.elim u m)} := ⟨fun m => hC (m.2.1.composeDiagram m.2.2)⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero, mul_zero]

end BrauerDiagram

variable (R : Type u) [CommSemiring R] (n k : ℕ)

/-- **The Brauer algebra acting on a tensor power of `Rⁿ`.** The Brauer algebra `B_k(n)` at the
loop value `n = dim Rⁿ` acts on `(Rⁿ)^{⊗k}` through the standard symmetric form: a diagram acts
by the matrix `TauCeti.BrauerDiagram.orthogonalActionMatrix` in the monomial basis, and these
matrices obey the loop rule (`TauCeti.BrauerDiagram.orthogonalActionMatrix_mul`). -/
noncomputable def brauerActionOrth :
    BrauerAlgebra R (n : R) k →ₐ[R] Module.End R (⨂[R] _ : Fin k, Fin n → R) :=
  BrauerAlgebra.lift
    (fun D => Matrix.toLin (tensorPowerBasis R n k) (tensorPowerBasis R n k)
      (D.orthogonalActionMatrix R (Fin n)))
    (by
      rw [BrauerDiagram.orthogonalActionMatrix_permToBrauer_one, Matrix.toLin_one,
        Module.End.one_eq_id])
    fun D₁ D₂ => by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin_mul, BrauerDiagram.orthogonalActionMatrix_mul,
        Fintype.card_fin, map_smul]

/-- A Brauer diagram acts by its matrix in the monomial basis. -/
theorem brauerActionOrth_of (D : BrauerDiagram k) :
    brauerActionOrth R n k (BrauerAlgebra.of D) =
      Matrix.toLin (tensorPowerBasis R n k) (tensorPowerBasis R n k)
        (D.orthogonalActionMatrix R (Fin n)) :=
  BrauerAlgebra.lift_of ..

/-- **A Brauer diagram on a monomial basis tensor.** The diagram `D` sends the basis tensor `e_u`
to the sum of the basis tensors `e_v` for which the labelling `Sum.elim u v` is constant on the
arcs of `D`. -/
theorem brauerActionOrth_of_tensorPowerBasis (D : BrauerDiagram k) (u : Fin k → Fin n) :
    brauerActionOrth R n k (BrauerAlgebra.of D) (tensorPowerBasis R n k u) =
      ∑ v with D.IsConstantOnArcs (Sum.elim u v), tensorPowerBasis R n k v := by
  rw [brauerActionOrth_of, Matrix.toLin_self, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [BrauerDiagram.orthogonalActionMatrix_apply]
  split_ifs <;> simp

/-- **Permutation diagrams act by permuting the tensor factors.** The diagram of `σ` acts on
`(Rⁿ)^{⊗k}` as `σ` does in the permutation action `TauCeti.permTensorAction`. -/
@[simp]
theorem brauerActionOrth_of_permToBrauer (σ : Equiv.Perm (Fin k)) :
    brauerActionOrth R n k (BrauerAlgebra.of (permToBrauer σ)) = permTensorAction R n k σ := by
  refine (tensorPowerBasis R n k).ext fun u => ?_
  rw [brauerActionOrth_of_tensorPowerBasis, permTensorAction_tensorPowerBasis]
  have hfilter : Finset.univ.filter (fun v => (permToBrauer σ).IsConstantOnArcs (Sum.elim u v)) =
      {fun i => u (σ.symm i)} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      BrauerDiagram.isConstantOnArcs_permToBrauer_iff]
    refine ⟨fun h => funext fun j => by simpa using h (σ.symm j), ?_⟩
    rintro rfl i
    simp
  rw [hfilter, Finset.sum_singleton]

/-- **The action restricts to the symmetric group.** Along the embedding
`TauCeti.BrauerAlgebra.ofPerm` of the group algebra of `Sₖ`, the action of the Brauer algebra is
the action `TauCeti.permTensorActionAlgHom` of the group algebra by permutations of the tensor
factors. -/
theorem brauerActionOrth_comp_ofPerm :
    (brauerActionOrth R n k).comp (BrauerAlgebra.ofPerm R (n : R) k) =
      permTensorActionAlgHom R n k := by
  refine MonoidAlgebra.algHom_ext (fun σ => ?_) (by ext)
  rw [AlgHom.comp_apply, BrauerAlgebra.ofPerm_single, map_smul, one_smul,
    brauerActionOrth_of_permToBrauer, ← permTensorActionAlgHom_of, MonoidAlgebra.of_apply]

/-- **Cap-cup diagrams act by the single-arc generators.** On two distinct strands `a` and `b`,
the cap-cup diagram acts on `(Rⁿ)^{⊗k}` as the generator `TauCeti.orthogonalCupCapAt`, contracting
the two slots against the dot product and re-expanding them through its copairing. -/
@[simp]
theorem brauerActionOrth_of_capCup {a b : Fin k} (hab : a ≠ b) :
    brauerActionOrth R n k (BrauerAlgebra.of (capCup a b)) = orthogonalCupCapAt R n k a b := by
  refine (tensorPowerBasis R n k).ext fun u => ?_
  rw [brauerActionOrth_of_tensorPowerBasis, orthogonalCupCapAt_tensorPowerBasis hab]
  split_ifs with hu
  · have hfilter : Finset.univ.filter (fun v => (capCup a b).IsConstantOnArcs (Sum.elim u v)) =
        Finset.univ.image fun c : Fin n => Function.update (Function.update u a c) b c := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        BrauerDiagram.isConstantOnArcs_capCup_iff hab]
      refine ⟨fun ⟨_, hv, h⟩ => ⟨v a, funext fun i => ?_⟩, ?_⟩
      · rcases eq_or_ne i b with rfl | hib
        · simp [hv]
        rcases eq_or_ne i a with rfl | hia
        · simp [hib]
        · simp [hia, hib, h i hia hib]
      · rintro ⟨c, rfl⟩
        refine ⟨hu, by simp [hab], fun i hia hib => by simp [hia, hib]⟩
    rw [hfilter, Finset.sum_image fun c _ c' _ h => by simpa using congrFun h b]
  · exact Finset.sum_eq_zero fun v hv => absurd
      ((BrauerDiagram.isConstantOnArcs_capCup_iff hab u v).mp (Finset.mem_filter.mp hv).2).1 hu

end TauCeti
