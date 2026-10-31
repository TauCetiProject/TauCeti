/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Folding
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# The folded Cartan matrix of a diagram automorphism is of finite type

Let `B : Matrix I I ℤ` be positive definite with diagonal entries `2` and nonpositive off-diagonal
entries, the Cartan matrix of a simply laced Dynkin diagram, possibly disconnected, and let
`σ : Equiv.Perm I` be a diagram automorphism, `B.reindex σ σ = B`. The folded Cartan matrix
`C = Matrix.foldedCartanMatrix B σ`, indexed by the `σ`-orbits of vertices with `H` rows and `E`
columns, is `C_{O,P} = c_O ∑_{i ∈ O} B i j` for `j ∈ P`, where `c_O = 2 / d_O` is the folding scale
and `d_O` the column sum of `B` over `O`. It is the Cartan matrix of the Lie algebra fixed by the
pinned action of `σ`.

This file shows that `C` is of finite type in the sense of `TauCeti.IsFiniteType`
(`Matrix.isFiniteType_foldedCartanMatrix`), so that the classification of finite-type Cartan
matrices applies to it. The symmetrization is explicit. Reading a vertex `i` as the simple root
`αᵢ`, the folded simple root of an orbit `O` is the mean of the simple roots in it,

`β_O = |O|⁻¹ ∑_{i ∈ O} αᵢ`  (`Equiv.Perm.orbitMean`),

and the folded Gram matrix `G_{O,P} = ⟪β_O, β_P⟫` (`Matrix.foldedGramMatrix`) is the Gram matrix
of these vectors for the form of `B`. Since the orbits are disjoint and nonempty, the `β_O` are
linearly independent (`Equiv.Perm.linearIndependent_orbitMean`), so `G` is positive definite
(`Matrix.posDef_foldedGramMatrix`). Since the column sums of `B` over an orbit are constant along
the orbits, `G_{O,P} = |O|⁻¹ ∑_{i ∈ O} B i j` for `j ∈ P`
(`Matrix.foldedGramMatrix_apply_eq_sum_div_card`), and multiplying row `O` of `C` by the positive
rational

`δ_O = (c_O |O|)⁻¹ = d_O / (2 |O|)`  (`Matrix.foldingSymmetrizer`)

gives `G` (`Matrix.foldingSymmetrizer_mul_foldedCartanMatrix`). In particular
`C_{O,P} = 2 ⟪β_O, β_P⟫ / ⟪β_O, β_O⟫` (`Matrix.foldedCartanMatrix_apply_eq_two_mul_div`), the usual
formula for the Cartan integers of a root system with simple roots `β_O`.

For instance, for the reversal of `A₃` the orbits `O = {1, 3}` and `P = {2}` both have column sum
`d = 2`, so `c_O = c_P = 1`, and `C` has rows `(2, -2)` and `(-1, 2)`, a rank-two Cartan matrix with
a double edge. The folded simple roots `β_O = (α₁ + α₃) / 2` and `β_P = α₂` have
`⟪β_O, β_O⟫ = 1`, `⟪β_O, β_P⟫ = -1` and `⟪β_P, β_P⟫ = 2`, and the symmetrizer `(1/2, 1)` carries
`C` to this Gram matrix.

## Main definitions

* `Equiv.Perm.orbitMean σ O`: the folded simple root `β_O = |O|⁻¹ ∑_{i ∈ O} αᵢ`.
* `Matrix.foldedGramMatrix B σ`: the Gram matrix `⟪β_O, β_P⟫` of the folded simple roots.
* `Matrix.foldingSymmetrizer B σ`: the symmetrizer `δ_O = (c_O |O|)⁻¹`.

## Main results

* `Equiv.Perm.linearIndependent_orbitMean`: the folded simple roots are linearly independent.
* `Matrix.posDef_foldedGramMatrix`: the folded Gram matrix of a positive definite `B` is positive
  definite.
* `Matrix.foldedGramMatrix_apply_eq_sum_div_card`: `⟪β_O, β_P⟫ = |O|⁻¹ ∑_{i ∈ O} B i j` for `j ∈ P`.
* `Matrix.foldingSymmetrizer_mul_foldedCartanMatrix`: `δ_O C_{O,P} = ⟪β_O, β_P⟫`.
* `Matrix.foldedCartanMatrix_apply_eq_two_mul_div`: `C_{O,P} = 2 ⟪β_O, β_P⟫ / ⟪β_O, β_O⟫`.
* `Matrix.isFiniteType_foldedCartanMatrix`: the folded Cartan matrix is of finite type.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.9, for the fixed points of a diagram automorphism and the folded Cartan matrix.
-/

public section

open Finset Matrix

namespace Equiv.Perm

variable {I : Type*} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I)

/-- The folded simple root `β_O = |O|⁻¹ ∑_{i ∈ O} αᵢ` of a `σ`-orbit `O` of vertices: the mean of
the coordinate vectors of the vertices in `O`, as a vector of coordinates in the basis `αᵢ`. -/
noncomputable def orbitMean (O : Quotient (SameCycle.setoid σ)) : I → ℚ :=
  fun i ↦ if σ.SameCycle i O.out then (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ else 0

theorem orbitMean_apply (O : Quotient (SameCycle.setoid σ)) (i : I) :
    σ.orbitMean O i = if σ.SameCycle i O.out then (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ else 0 :=
  (rfl)

/-- The dot product with a folded simple root is the mean over the orbit. -/
theorem orbitMean_dotProduct (O : Quotient (SameCycle.setoid σ)) (v : I → ℚ) :
    σ.orbitMean O ⬝ᵥ v =
      (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ * ∑ i with σ.SameCycle i O.out, v i := by
  simp [dotProduct, orbitMean_apply, ite_mul, sum_filter, mul_sum]

/-- The dot product with a folded simple root is the mean over the orbit. -/
theorem dotProduct_orbitMean (O : Quotient (SameCycle.setoid σ)) (v : I → ℚ) :
    v ⬝ᵥ σ.orbitMean O =
      (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ * ∑ i with σ.SameCycle i O.out, v i := by
  rw [dotProduct_comm, orbitMean_dotProduct]

/-- A combination of folded simple roots, evaluated at the representative of an orbit `O`, only
sees the coefficient of `β_O`. -/
private theorem vecMul_of_orbitMean_apply_out [Fintype (Quotient (SameCycle.setoid σ))]
    (x : Quotient (SameCycle.setoid σ) → ℚ) (O : Quotient (SameCycle.setoid σ)) :
    (x ᵥ* Matrix.of σ.orbitMean) O.out = x O * (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ := by
  rw [vecMul, dotProduct, Fintype.sum_eq_single O fun P hP ↦ ?_]
  · simp [orbitMean_apply, SameCycle.refl]
  · have : ¬σ.SameCycle O.out P.out := fun h ↦
      ne_of_sameCycle_out (SameCycle.refl σ O.out) h (Ne.symm hP) rfl
    simp [orbitMean_apply, this]

/-- **The folded simple roots are linearly independent**: the orbits are disjoint and nonempty. -/
theorem linearIndependent_orbitMean : LinearIndependent ℚ σ.orbitMean := by
  classical
  have hinj : Function.Injective (Matrix.of σ.orbitMean).vecMul := fun x y h ↦ funext fun O ↦ by
    have hO : (x ᵥ* Matrix.of σ.orbitMean) O.out = (y ᵥ* Matrix.of σ.orbitMean) O.out :=
      congr_fun h O.out
    rw [vecMul_of_orbitMean_apply_out, vecMul_of_orbitMean_apply_out] at hO
    have hcard : (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ ≠ 0 := by
      have : 0 < #{j | σ.SameCycle j O.out} := card_pos.2 ⟨O.out, by simp [SameCycle.refl]⟩
      positivity
    exact mul_right_cancel₀ hcard hO
  exact Matrix.vecMul_injective_iff.mp hinj

end Equiv.Perm

namespace Matrix

variable {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I ℤ) (σ : Equiv.Perm I)

/-- The folded Gram matrix `G_{O,P} = ⟪β_O, β_P⟫` of a permutation `σ` of the vertices: the Gram
matrix, for the form `⟪a, b⟫ = a ⬝ᵥ B *ᵥ b` read over `ℚ`, of the folded simple roots
`β_O = Equiv.Perm.orbitMean σ O`. -/
noncomputable def foldedGramMatrix :
    Matrix (Quotient (Equiv.Perm.SameCycle.setoid σ)) (Quotient (Equiv.Perm.SameCycle.setoid σ))
      ℚ :=
  Matrix.of fun O P ↦ σ.orbitMean O ⬝ᵥ B.map (Int.cast : ℤ → ℚ) *ᵥ σ.orbitMean P

theorem foldedGramMatrix_apply (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldedGramMatrix σ O P = σ.orbitMean O ⬝ᵥ B.map (Int.cast : ℤ → ℚ) *ᵥ σ.orbitMean P :=
  (rfl)

/-- The folded Gram matrix is the congruence of `B` by the matrix whose rows are the folded simple
roots. -/
theorem foldedGramMatrix_eq_mul_mul_transpose :
    B.foldedGramMatrix σ =
      Matrix.of σ.orbitMean * B.map (Int.cast : ℤ → ℚ) * (Matrix.of σ.orbitMean)ᵀ := by
  ext O P
  rw [foldedGramMatrix_apply, dotProduct_mulVec, mul_apply]
  simp [vecMul, dotProduct, mul_apply]

variable {B} in
/-- **The folded Gram matrix of a positive definite `B` is positive definite**, since the folded
simple roots are linearly independent. No invariance of `B` under `σ` is needed. -/
theorem posDef_foldedGramMatrix (hB : B.PosDef) : (B.foldedGramMatrix σ).PosDef := by
  classical
  rw [foldedGramMatrix_eq_mul_mul_transpose, ← conjTranspose_eq_transpose_of_trivial]
  exact (TauCeti.Matrix.posDef_map_intCast hB).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff.mpr σ.linearIndependent_orbitMean)

variable {B σ}

/-- For a `σ`-invariant `B`, the folded Gram matrix is the column sum of `B` over `O` at any
vertex `j` of `P`, divided by `|O|`: `⟪β_O, β_P⟫ = |O|⁻¹ ∑_{i ∈ O} B i j`. In particular
`⟪β_O, β_O⟫ = d_O / |O|`. -/
theorem foldedGramMatrix_apply_eq_sum_div_card (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) {P : Quotient (Equiv.Perm.SameCycle.setoid σ)}
    {j : I} (hj : σ.SameCycle j P.out) :
    B.foldedGramMatrix σ O P =
      ((∑ i with σ.SameCycle i O.out, B i j : ℤ) : ℚ) / #{i | σ.SameCycle i O.out} := by
  have hP : (#{j | σ.SameCycle j P.out} : ℚ) ≠ 0 := by
    have : 0 < #{j | σ.SameCycle j P.out} :=
      card_pos.2 ⟨P.out, by simp [Equiv.Perm.SameCycle.refl]⟩
    positivity
  -- Each column sum over `O` at a vertex of `P` is the one at `j`.
  have hcol : ∀ j' ∈ ({j' | σ.SameCycle j' P.out} : Finset I),
      ∑ i with σ.SameCycle i O.out, (B i j' : ℚ) =
        ((∑ i with σ.SameCycle i O.out, B i j : ℤ) : ℚ) :=
    fun j' hj' ↦ by
      rw [sum_apply_eq_of_sameCycle hσ O (hj.trans (mem_filter.mp hj').2.symm), Int.cast_sum]
  simp_rw [foldedGramMatrix_apply, Equiv.Perm.orbitMean_dotProduct, mulVec,
    Equiv.Perm.dotProduct_orbitMean, ← mul_sum, map_apply]
  rw [sum_comm, sum_congr rfl hcol, sum_const, nsmul_eq_mul]
  field_simp

variable (B σ) in
/-- The folding symmetrizer `δ_O = (c_O |O|)⁻¹` of a `σ`-orbit `O`, where `c_O` is the folding
scale `Matrix.foldingScale B σ O`. Since `c_O d_O = 2` for the column sum `d_O` of `B` over `O`,
it is `d_O / (2 |O|)`. -/
noncomputable def foldingSymmetrizer (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : ℚ :=
  ((B.foldingScale σ O : ℚ) * #{i | σ.SameCycle i O.out})⁻¹

theorem foldingSymmetrizer_def (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingSymmetrizer σ O = ((B.foldingScale σ O : ℚ) * #{i | σ.SameCycle i O.out})⁻¹ :=
  (rfl)

/-- The folding symmetrizer is positive. -/
theorem foldingSymmetrizer_pos (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : 0 < B.foldingSymmetrizer σ O := by
  have hc : (0 : ℚ) < B.foldingScale σ O := by exact_mod_cast foldingScale_pos hB hdiag hoff hσ O
  have hO : 0 < #{i | σ.SameCycle i O.out} :=
    card_pos.2 ⟨O.out, by simp [Equiv.Perm.SameCycle.refl]⟩
  rw [foldingSymmetrizer_def]
  positivity

/-- **The folding symmetrizer symmetrizes the folded Cartan matrix**: multiplying row `O` of the
folded Cartan matrix by `δ_O` gives the folded Gram matrix, `δ_O C_{O,P} = ⟪β_O, β_P⟫`. -/
theorem foldingSymmetrizer_mul_foldedCartanMatrix (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingSymmetrizer σ O * B.foldedCartanMatrix σ O P = B.foldedGramMatrix σ O P := by
  have hc : (B.foldingScale σ O : ℚ) ≠ 0 := by
    exact_mod_cast (foldingScale_pos hB hdiag hoff hσ O).ne'
  have hO : (#{i | σ.SameCycle i O.out} : ℚ) ≠ 0 := by
    have : 0 < #{i | σ.SameCycle i O.out} :=
      card_pos.2 ⟨O.out, by simp [Equiv.Perm.SameCycle.refl]⟩
    positivity
  rw [foldedGramMatrix_apply_eq_sum_div_card hσ O (Equiv.Perm.SameCycle.refl σ P.out),
    foldedCartanMatrix_apply, foldingSymmetrizer_def]
  push_cast
  field_simp

/-- **The Cartan integers of the folded simple roots.** The folded Cartan matrix is
`C_{O,P} = 2 ⟪β_O, β_P⟫ / ⟪β_O, β_O⟫`, the Cartan matrix, with `H` rows, of the vectors `β_O` for
the form of `B`. -/
theorem foldedCartanMatrix_apply_eq_two_mul_div (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)
    (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (B.foldedCartanMatrix σ O P : ℚ) =
      2 * B.foldedGramMatrix σ O P / B.foldedGramMatrix σ O O := by
  have hδ := (foldingSymmetrizer_pos hB hdiag hoff hσ O).ne'
  rw [← foldingSymmetrizer_mul_foldedCartanMatrix hB hdiag hoff hσ,
    ← foldingSymmetrizer_mul_foldedCartanMatrix hB hdiag hoff hσ,
    foldedCartanMatrix_apply_self hB hdiag hoff hσ]
  field_simp
  ring

/-- **The folded Cartan matrix is of finite type.** For a positive definite `σ`-invariant `B` with
diagonal entries `2` and nonpositive off-diagonal entries, the folded Cartan matrix is a
generalized Cartan matrix with positive symmetrizer `δ_O = Matrix.foldingSymmetrizer B σ O`, whose
symmetrization is the positive definite folded Gram matrix. -/
theorem isFiniteType_foldedCartanMatrix (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B) :
    TauCeti.IsFiniteType (B.foldedCartanMatrix σ) := by
  refine TauCeti.isFiniteType_of (foldedCartanMatrix_apply_self hB hdiag hoff hσ)
    (fun _ _ ↦ foldedCartanMatrix_nonpos hB hdiag hoff hσ)
    (foldingSymmetrizer_pos hB hdiag hoff hσ) ?_
  convert posDef_foldedGramMatrix σ hB using 1
  ext O P
  exact foldingSymmetrizer_mul_foldedCartanMatrix hB hdiag hoff hσ O P

end Matrix
