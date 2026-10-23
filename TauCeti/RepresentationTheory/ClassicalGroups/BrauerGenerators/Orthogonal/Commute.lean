/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Matrix
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Action

/-!
# The Brauer action commutes with the orthogonal group

The Brauer algebra `B_k(n)` acts on the tensor power `(Rⁿ)^{⊗k}` through the coordinate dot
product (`TauCeti.brauerActionOrth`), and the orthogonal group `O(n, R)` acts on the same tensor
power diagonally. This file proves that the two actions commute, so that every operator by which
the Brauer algebra acts lies in the commutant of the orthogonal group. This is the easy half of
Brauer's orthogonal Schur-Weyl duality; the converse, that over `ℂ` the image of the Brauer algebra
is the whole commutant (the first fundamental theorem of invariant theory for `O(n)`), is not
proved here.

The proof is uniform in the diagram rather than reduced to generators of the Brauer algebra (the
single-arc generators commute with the orthogonal group by
`TauCeti.commute_orthogonalCupCapAt_tensorPower`). In the monomial basis a diagram `D` acts by the
matrix whose entry at the pair of labellings `(v, u)` is `1` when the labelling `Sum.elim u v` of
the boundary points is constant on the arcs of `D`, and `0` otherwise. Read as a tensor on the
`2k` boundary slots, that matrix is a product over the arcs of copies of the copairing
`∑ c, e_c ⊗ e_c`, and a matrix `A` acting on both ends of one copy turns it into
`∑ c, A e_c ⊗ A e_c`, whose coefficients are the entries of `A * Aᵀ`
(`TauCeti.BrauerDiagram.sum_isConstantOnArcs_prod_eq`). For `A * Aᵀ = 1` the arc tensor is
therefore invariant, which says that conjugating the action of `D` by the diagonal action of `A`
gives it back.

## Main results

* `TauCeti.BrauerDiagram.sum_isConstantOnArcs_prod_eq`: the arc tensor of a Brauer diagram is
  invariant under every matrix `A` with `A * Aᵀ = 1` acting on all boundary slots.
* `TauCeti.commute_brauerActionOrth_piTensorProductMap`: the action of the Brauer algebra commutes
  with the diagonal action of every matrix `A` with `Aᵀ * A = 1`, over a commutative semiring.
* `TauCeti.commute_brauerActionOrth_tensorPower`: the action of the Brauer algebra commutes with
  the diagonal action of the orthogonal group.
* `TauCeti.range_brauerActionOrth_le_centralizer`: the image of the Brauer algebra lies in the
  centralizer of the image of the orthogonal group.

## Implementation notes

To split a sum over the labellings constant on the arcs into a product over the arcs, each arc is
represented by its endpoint that comes first in the lexicographic order of `Fin k ⊕ Fin k`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped Matrix

namespace TauCeti

universe u

namespace BrauerDiagram

variable {k : ℕ} (D : BrauerDiagram k)

/-- The boundary points of `D` that come first on their arc in the lexicographic order of
`Fin k ⊕ Fin k`: one chosen endpoint of each arc. -/
private abbrev LowerEnd : Type := {x : Fin k ⊕ Fin k // toLex x < toLex (D.val x)}

/-- The boundary points are enumerated by the first endpoints of the arcs together with a flag
choosing that endpoint (`false`) or its partner (`true`). -/
private noncomputable def lowerEndEquiv : D.LowerEnd × Bool ≃ Fin k ⊕ Fin k :=
  Equiv.ofBijective (fun p => if p.2 then D.val p.1 else p.1) <| by
    refine ⟨?_, fun x => ?_⟩
    · rintro ⟨⟨x, hx⟩, _ | _⟩ ⟨⟨y, hy⟩, _ | _⟩ h <;>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
      · subst h; rfl
      · subst h
        rw [D.apply_apply] at hx
        exact absurd (hx.trans hy) (lt_irrefl _)
      · subst h
        rw [D.apply_apply] at hy
        exact absurd (hx.trans hy) (lt_irrefl _)
      · obtain rfl : x = y := D.val.injective h
        rfl
    · rcases lt_or_gt_of_ne (toLex.injective.ne (D.apply_ne x).symm) with h | h
      · exact ⟨(⟨x, h⟩, false), rfl⟩
      · exact ⟨(⟨D.val x, by rwa [D.apply_apply]⟩, true), D.apply_apply x⟩

private theorem lowerEndEquiv_false (s : D.LowerEnd) : D.lowerEndEquiv (s, false) = s := (rfl)

private theorem lowerEndEquiv_true (s : D.LowerEnd) : D.lowerEndEquiv (s, true) = D.val s := (rfl)

/-- The first endpoint of the arc through a boundary point. -/
private noncomputable def lowerEnd (x : Fin k ⊕ Fin k) : D.LowerEnd := (D.lowerEndEquiv.symm x).1

private theorem lowerEnd_coe (s : D.LowerEnd) : D.lowerEnd s = s := by
  rw [lowerEnd, ← D.lowerEndEquiv_false, Equiv.symm_apply_apply]

private theorem lowerEnd_val (x : Fin k ⊕ Fin k) : D.lowerEnd (D.val x) = D.lowerEnd x := by
  obtain ⟨⟨s, _ | _⟩, rfl⟩ := D.lowerEndEquiv.surjective x
  · rw [lowerEndEquiv_false, lowerEnd_coe, lowerEnd, ← D.lowerEndEquiv_true,
      Equiv.symm_apply_apply]
  · rw [lowerEndEquiv_true, D.apply_apply, lowerEnd_coe, lowerEnd, ← D.lowerEndEquiv_true,
      Equiv.symm_apply_apply]

private theorem eq_or_eq_val_lowerEnd (x : Fin k ⊕ Fin k) :
    x = D.lowerEnd x ∨ x = D.val (D.lowerEnd x) := by
  obtain ⟨⟨s, _ | _⟩, rfl⟩ := D.lowerEndEquiv.surjective x
  · exact .inl (by rw [lowerEndEquiv_false, lowerEnd_coe])
  · exact .inr (by rw [lowerEndEquiv_true, lowerEnd_val, lowerEnd_coe])

/-- A labelling is constant on the arcs as soon as it agrees at the two ends of every arc read
from its first endpoint. -/
private theorem isConstantOnArcs_iff_forall_lowerEnd {ι : Type*} (ℓ : Fin k ⊕ Fin k → ι) :
    D.IsConstantOnArcs ℓ ↔ ∀ s : D.LowerEnd, ℓ s = ℓ (D.val s) := by
  refine ⟨fun h s => ((D.isConstantOnArcs_def ℓ).mp h s).symm,
    fun h => (D.isConstantOnArcs_def ℓ).mpr fun x => ?_⟩
  rcases D.eq_or_eq_val_lowerEnd x with hx | hx
  · rw [hx]
    exact (h _).symm
  · rw [hx, D.apply_apply]
    exact h _

/-- A labelling constant on the arcs is the same as a labelling of the first endpoints. -/
private noncomputable def isConstantOnArcsEquiv (ι : Type*) :
    {ℓ : Fin k ⊕ Fin k → ι // D.IsConstantOnArcs ℓ} ≃ (D.LowerEnd → ι) where
  toFun ℓ s := ℓ.1 s
  invFun c := ⟨fun x => c (D.lowerEnd x), (D.isConstantOnArcs_def _).mpr fun x => by
    rw [lowerEnd_val]⟩
  left_inv ℓ := Subtype.ext <| funext fun x => by
    dsimp only
    rcases D.eq_or_eq_val_lowerEnd x with hx | hx
    · exact congrArg ℓ.1 hx.symm
    · exact ((D.isConstantOnArcs_def _).mp ℓ.2 _).symm.trans (congrArg ℓ.1 hx.symm)
  right_inv c := funext fun s => by
    dsimp only
    rw [lowerEnd_coe]

variable {R : Type u} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The arc tensor of a Brauer diagram is orthogonally invariant.** Read the diagram `D` as the
tensor `∑ ℓ e_ℓ` over the labellings `ℓ` of its boundary points constant on its arcs. Applying a
matrix `A` with `A * Aᵀ = 1` to every one of the `2k` boundary slots leaves that tensor unchanged:
its coefficient at the labelling `m` is again `1` or `0` according as `m` is constant on the arcs.
Each arc contributes the entry `(A * Aᵀ) (m x) (m y)` at its two endpoints `x` and `y`. -/
theorem sum_isConstantOnArcs_prod_eq {A : Matrix ι ι R} (hA : A * Aᵀ = 1)
    (m : Fin k ⊕ Fin k → ι) :
    ∑ ℓ with D.IsConstantOnArcs ℓ, ∏ x, A (m x) (ℓ x) =
      if D.IsConstantOnArcs m then 1 else 0 := by
  have hsplit (f : Fin k ⊕ Fin k → R) : ∏ x, f x = ∏ s : D.LowerEnd, f s * f (D.val s) := by
    rw [← D.lowerEndEquiv.prod_comp, Fintype.prod_prod_type]
    simp only [Fintype.prod_bool, lowerEndEquiv_true, lowerEndEquiv_false, mul_comm]
  have harc (s : D.LowerEnd) :
      ∑ a, A (m s) a * A (m (D.val s)) a = if m s = m (D.val s) then 1 else 0 := by
    rw [← Matrix.one_apply, ← hA, Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
  rw [Finset.sum_subtype _ (fun ℓ => by simp) (p := D.IsConstantOnArcs),
    ← (D.isConstantOnArcsEquiv ι).symm.sum_comp]
  simp only [isConstantOnArcsEquiv, Equiv.coe_fn_symm_mk, hsplit, lowerEnd_coe, lowerEnd_val]
  refine (Fintype.prod_sum fun (s : D.LowerEnd) a => A (m s) a * A (m (D.val s)) a).symm.trans ?_
  simp only [harc, Fintype.prod_boole, isConstantOnArcs_iff_forall_lowerEnd]

end BrauerDiagram

section CommSemiring

variable {R : Type u} [CommSemiring R] {n k : ℕ}

/-- Conjugating the action of a Brauer diagram by the diagonal action of a matrix `A` with
`A * Aᵀ = 1` gives it back: this is `TauCeti.BrauerDiagram.sum_isConstantOnArcs_prod_eq` read in
the monomial basis. -/
private theorem piTensorProductMap_mul_brauerActionOrth_mul {A : Matrix (Fin n) (Fin n) R}
    (hA : A * Aᵀ = 1) (D : BrauerDiagram k) :
    PiTensorProduct.map (fun _ : Fin k => A.mulVecLin) *
        brauerActionOrth R n k (BrauerAlgebra.of D) *
        PiTensorProduct.map (fun _ : Fin k => Aᵀ.mulVecLin) =
      brauerActionOrth R n k (BrauerAlgebra.of D) := by
  apply (LinearMap.toMatrix (tensorPowerBasis R n k) (tensorPowerBasis R n k)).injective
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, brauerActionOrth_of,
    LinearMap.toMatrix_toLin, tensorPowerBasis_def, PiTensorProduct.toMatrix_map,
    PiTensorProduct.toMatrix_map]
  ext w u
  -- Split a labelling of the `2k` boundary points into its bottom and top halves.
  have helim (a b : Fin k → Fin n) :
      (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (Fin n)).symm (a, b) = Sum.elim a b := (rfl)
  rw [BrauerDiagram.orthogonalActionMatrix_apply,
    ← D.sum_isConstantOnArcs_prod_eq hA (Sum.elim u w), Finset.sum_filter,
    ← (Equiv.sumArrowEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.of_apply, BrauerDiagram.orthogonalActionMatrix_apply,
    LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin', Matrix.transpose_apply, Finset.sum_mul, helim,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [mul_comm]

/-- **The Brauer action commutes with every matrix preserving the dot product.** The action of
every element of the Brauer algebra `B_k(n)` on `(Rⁿ)^{⊗k}` commutes with the diagonal action of a
matrix `A` with `Aᵀ * A = 1`. -/
theorem commute_brauerActionOrth_piTensorProductMap {A : Matrix (Fin n) (Fin n) R}
    (hA : Aᵀ * A = 1) (x : BrauerAlgebra R (n : R) k) :
    Commute (brauerActionOrth R n k x) (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  have hinv : PiTensorProduct.map (fun _ : Fin k => Aᵀ.mulVecLin) *
      PiTensorProduct.map (fun _ : Fin k => A.mulVecLin) = 1 := by
    rw [← PiTensorProduct.map_mul]
    simp only [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hA, Matrix.mulVecLin_one]
    exact PiTensorProduct.map_id
  rw [← (BrauerAlgebra.basis R (n : R) k).sum_repr x, map_sum]
  refine Commute.sum_left _ _ _ fun D _ => ?_
  rw [map_smul, BrauerAlgebra.basis_apply]
  refine Commute.smul_left ?_ _
  calc brauerActionOrth R n k (BrauerAlgebra.of D) * PiTensorProduct.map (fun _ => A.mulVecLin)
      = PiTensorProduct.map (fun _ => A.mulVecLin) *
          brauerActionOrth R n k (BrauerAlgebra.of D) *
          (PiTensorProduct.map (fun _ => Aᵀ.mulVecLin) *
            PiTensorProduct.map (fun _ => A.mulVecLin)) := by
        rw [← mul_assoc, piTensorProductMap_mul_brauerActionOrth_mul (mul_eq_one_comm.mp hA)]
    _ = _ := by rw [hinv, mul_one]

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {n k : ℕ}

/-- **The Brauer action commutes with the orthogonal group.** The action of every element of the
Brauer algebra `B_k(n)` on `(Rⁿ)^{⊗k}` commutes with the diagonal action of every element of the
orthogonal group `O(n, R)`. -/
theorem commute_brauerActionOrth_tensorPower (g : Matrix.orthogonalGroup (Fin n) R)
    (x : BrauerAlgebra R (n : R) k) :
    Commute (brauerActionOrth R n k x) ((stdOrthogonalRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    commute_brauerActionOrth_piTensorProductMap
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) R).mp g.prop) x

variable (R n k) in
/-- **The image of the Brauer algebra lies in the commutant of the orthogonal group**: every
operator by which `B_k(n)` acts on `(Rⁿ)^{⊗k}` commutes with the whole diagonal action of
`O(n, R)`. -/
theorem range_brauerActionOrth_le_centralizer :
    (brauerActionOrth R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)) := by
  intro T hT
  obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).mp hT
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionOrth_tensorPower g x).symm.eq

end CommRing

end TauCeti
