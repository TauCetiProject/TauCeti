/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Equivariance
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import TauCeti.LinearAlgebra.Matrix.KroneckerPower.OrthogonalCommutant
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.PlaneRotation
import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Faithful

/-!
# Brauer duality for the orthogonal group on two strands

Let `V = Rⁿ` carry its standard symmetric form. The Brauer algebra `B₂(n)` on two strands acts on
`V ⊗ V` (`TauCeti.brauerActionOrth`) through its three diagrams: the identity, the crossing,
which flips the two tensor factors, and the cap-cup diagram, which acts by the contraction-expansion
`x ⊗ y ↦ (x ⬝ᵥ y) • ∑ᵢ eᵢ ⊗ eᵢ`. These operators commute with the diagonal action of the orthogonal
group (`TauCeti.range_brauerActionOrth_le_centralizer`). This file proves the converse on two
strands: every operator on `V ⊗ V` commuting with the orthogonal group is a combination of them,
so the image of `B₂(n)` is the whole commutant
(`TauCeti.range_brauerActionOrth_two_eq_centralizer_of_noZeroDivisors`). This is the two-strand
case of Brauer's theorem that the image of `B_k(n)` is the commutant of the orthogonal group on
`V^{⊗k}`.

The theorem holds over a commutative ring without zero divisors in which `2 ≠ 0` and which
contains a point `(c, s)` of the unit circle with `c * s ≠ 0`, for instance over any field of
characteristic zero, with `(3 / 5, 4 / 5)`
(`TauCeti.range_brauerActionOrth_two_eq_centralizer` in
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Commutant`). Some such
point is needed: over `ZMod 3` the orthogonal group of the plane consists of the signed
permutation matrices, and these commute with the projection onto the span of `e₀ ⊗ e₀` and
`e₁ ⊗ e₁`, which is not in the image.

## The argument

In the monomial basis an operator on `V ⊗ V` is a matrix `M` whose rows and columns are indexed by
pairs of labels, and commuting with `g ⊗ g` is commuting with the Kronecker square of `g`.

* **Signed permutations.** The diagonal sign matrix negating one label is orthogonal, so an entry
  of `M` vanishes as soon as some label occurs an odd number of times among its four indices
  (`Matrix.apply_eq_zero_of_commute_kroneckerPower`). Permutation matrices are orthogonal, so an
  entry depends only on the pattern of equalities among its indices
  (`Matrix.apply_comp_comp_of_commute_kroneckerPower`). The surviving patterns are those of the
  identity, the crossing and the cap-cup diagram, together with the pattern in which all four
  indices agree. So `M` is a combination of the three diagram matrices and of the projection `D`
  onto the span of the tensors `e_a ⊗ e_a`.
* **A rotation.** The diagram matrices commute with every orthogonal matrix, but `D` does not
  commute with the plane rotation `A` through `(c, s)`
  (`TauCeti.exists_orthogonal_apply_mul_apply_ne_zero`): the two products with its Kronecker
  square differ at the entry `(e_a ⊗ e_a, e_a ⊗ e_b)` by `A a a * A a b = -c * s ≠ 0`. So the
  coefficient of `D` vanishes.

In dimension at most one the tensor square has rank at most one, and every operator is a scalar.
In dimension at least two the action of `B₂(n)` is faithful
(`TauCeti.brauerActionOrth_injective`), so the commutant has rank three
(`TauCeti.finrank_centralizer_stdOrthogonalRep_tensorPower_two`).

## Main results

* `TauCeti.range_brauerActionOrth_two_eq_centralizer_of_noZeroDivisors`: **Brauer duality on two
  strands**, the image of `B₂(n)` is the commutant of the orthogonal group on `Rⁿ ⊗ Rⁿ`.
* `TauCeti.finrank_centralizer_stdOrthogonalRep_tensorPower_two`: the commutant has rank three
  once `n ≥ 2`.

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

/-! ### The matrices commuting with the orthogonal group on two strands -/

section TwoStrands

variable {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Matrix (Fin 2 → ι) (Fin 2 → ι) R}

variable (R ι) in
/-- The combination `x • 1 + y • s + z • e` of the matrices of the identity, the crossing and the
cap-cup diagram on two strands. -/
private def diagramCombination (x y z : R) : Matrix (Fin 2 → ι) (Fin 2 → ι) R :=
  x • (permToBrauer 1).orthogonalActionMatrix R ι +
    y • (permToBrauer (Equiv.swap 0 1)).orthogonalActionMatrix R ι +
    z • (capCup 0 1).orthogonalActionMatrix R ι

variable (R ι) in
/-- The matrix of the projection of the tensor square onto the span of the tensors `e_a ⊗ e_a`.
It commutes with the signed permutation matrices but not with a rotation. -/
private def diagonalTensorMatrix : Matrix (Fin 2 → ι) (Fin 2 → ι) R :=
  Matrix.of fun v u => if v = u ∧ v 0 = v 1 then 1 else 0

/-- **Relabelling.** A matrix commuting with the orthogonal group on two strands has the same
entry at two index patterns that differ by a permutation of the labels. -/
private theorem apply_perm_pattern
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower (Fin 2)))
    (σ : Equiv.Perm ι) (x₀ x₁ y₀ y₁ : ι) :
    M ![σ x₀, σ x₁] ![σ y₀, σ y₁] = M ![x₀, x₁] ![y₀, y₁] := by
  have hc : ∀ a b : ι, ![σ a, σ b] = σ ∘ ![a, b] := fun a b => by
    ext i; fin_cases i <;> rfl
  rw [hc, hc]
  exact apply_comp_comp_of_commute_kroneckerPower hM σ _ _

/-- **Parity.** A matrix commuting with the orthogonal group on two strands has a vanishing entry
at a pair of index patterns in which some label `a` occurs an odd number of times in total. -/
private theorem apply_eq_zero_of_not_iff [NoZeroDivisors R]
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower (Fin 2)))
    (h2 : (2 : R) ≠ 0) {a : ι} {v u : Fin 2 → ι}
    (h : ¬((v 0 = a ↔ v 1 = a) ↔ (u 0 = a ↔ u 1 = a))) : M v u = 0 := by
  have hpar (w : Fin 2 → ι) :
      Even (Finset.univ.filter fun i => w i = a).card ↔ (w 0 = a ↔ w 1 = a) := by
    rw [Finset.card_filter, Fin.sum_univ_two]
    by_cases h0 : w 0 = a <;> by_cases h1 : w 1 = a <;> simp [h0, h1]
  exact apply_eq_zero_of_commute_kroneckerPower hM h2 a (by rwa [hpar, hpar])

/-- **The entries of a matrix commuting with the orthogonal group on two strands.** Such a matrix
is determined by its entries at the four patterns of equality among its indices, so it is a
combination of the three diagram matrices and of `TauCeti.diagonalTensorMatrix`. -/
private theorem eq_diagramCombination_add_smul [NoZeroDivisors R]
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower (Fin 2)))
    (h2 : (2 : R) ≠ 0) {a₀ a₁ : ι} (h01 : a₀ ≠ a₁) :
    M = diagramCombination R ι (M ![a₀, a₁] ![a₀, a₁]) (M ![a₀, a₁] ![a₁, a₀])
        (M ![a₀, a₀] ![a₁, a₁]) +
      (M ![a₀, a₀] ![a₀, a₀] -
        (M ![a₀, a₁] ![a₀, a₁] + M ![a₀, a₁] ![a₁, a₀] + M ![a₀, a₀] ![a₁, a₁])) •
        diagonalTensorMatrix R ι := by
  -- Relabelling moves each pattern to a normal form at the labels `a₀` and `a₁`.
  have hσ := apply_perm_pattern hM
  have hτ (a : ι) : M ![a, a] ![a, a] = M ![a₀, a₀] ![a₀, a₀] := by
    simpa using (hσ (Equiv.swap a a₀) a a a a).symm
  have hpair {a b : ι} (hab : a ≠ b) : ∃ σ : Equiv.Perm ι, σ a = a₀ ∧ σ b = a₁ := by
    simpa only [Equiv.Perm.smul_def] using
      MulAction.is_two_pretransitive_iff.mp (Equiv.Perm.isMultiplyPretransitive ι 2) hab h01
  have hβ {a b : ι} (hab : a ≠ b) : M ![a, b] ![a, b] = M ![a₀, a₁] ![a₀, a₁] := by
    obtain ⟨σ, ha, hb⟩ := hpair hab
    rw [← hσ σ, ha, hb]
  have hγ {a b : ι} (hab : a ≠ b) : M ![a, b] ![b, a] = M ![a₀, a₁] ![a₁, a₀] := by
    obtain ⟨σ, ha, hb⟩ := hpair hab
    rw [← hσ σ, ha, hb]
  have hα {a b : ι} (hab : a ≠ b) : M ![a, a] ![b, b] = M ![a₀, a₀] ![a₁, a₁] := by
    obtain ⟨σ, ha, hb⟩ := hpair hab
    rw [← hσ σ, ha, hb]
  have hz {a : ι} {v u : Fin 2 → ι} (h : ¬((v 0 = a ↔ v 1 = a) ↔ (u 0 = a ↔ u 1 = a))) :
      M v u = 0 := apply_eq_zero_of_not_iff hM h2 h
  ext v u
  obtain ⟨x₀, x₁, rfl⟩ : ∃ x₀ x₁ : ι, v = ![x₀, x₁] := ⟨v 0, v 1, by ext i; fin_cases i <;> rfl⟩
  obtain ⟨y₀, y₁, rfl⟩ : ∃ y₀ y₁ : ι, u = ![y₀, y₁] := ⟨u 0, u 1, by ext i; fin_cases i <;> rfl⟩
  simp only [diagramCombination, diagonalTensorMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, BrauerDiagram.orthogonalActionMatrix_apply,
    BrauerDiagram.isConstantOnArcs_permToBrauer_iff,
    BrauerDiagram.isConstantOnArcs_capCup_iff (by decide : (0 : Fin 2) ≠ 1), Fin.forall_fin_two,
    funext_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Equiv.Perm.coe_one, id_eq,
    Equiv.swap_apply_left, Equiv.swap_apply_right, smul_eq_mul, ne_eq, not_true_eq_false,
    false_implies]
  rcases eq_or_ne x₀ x₁ with rfl | hx
  · rcases eq_or_ne y₀ y₁ with rfl | hy
    · rcases eq_or_ne x₀ y₀ with rfl | hxy
      · rw [hτ]; grind
      · rw [hα hxy]; grind
    · rw [hz (a := y₀) (by simpa using hy.symm)]; grind
  · rcases eq_or_ne y₀ y₁ with rfl | hy
    · rw [hz (a := x₀) (by simpa using hx.symm)]; grind
    · by_cases h00 : x₀ = y₀
      · subst h00
        by_cases h11 : x₁ = y₁
        · subst h11; rw [hβ hx]; grind
        · rw [hz (a := x₁) (by simp; grind)]; grind
      · by_cases h01 : x₀ = y₁
        · subst h01
          by_cases h10 : x₁ = y₀
          · subst h10; rw [hγ hx]; grind
          · rw [hz (a := x₁) (by simp; grind)]; grind
        · rw [hz (a := x₀) (by simp; grind)]; grind

/-- **The rotation step.** A multiple `t • D` of `TauCeti.diagonalTensorMatrix` commuting with the
Kronecker square of a matrix `A` with `A a a * A a b ≠ 0` for labels `a ≠ b` vanishes: the two
products differ at the entry `(e_a ⊗ e_a, e_a ⊗ e_b)` by `t * (A a a * A a b)`. -/
private theorem eq_zero_of_commute_smul_diagonalTensorMatrix [NoZeroDivisors R] {t : R}
    {A : Matrix ι ι R} (hA : Commute (t • diagonalTensorMatrix R ι) (A.kroneckerPower (Fin 2)))
    {a b : ι} (hab : a ≠ b) (hAab : A a a * A a b ≠ 0) : t = 0 := by
  have hent := congrFun (congrFun hA.eq ![a, a]) ![a, b]
  simp only [diagonalTensorMatrix, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, kroneckerPower_apply, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, hab, ite_false] at hent
  exact (mul_eq_zero.mp hent).resolve_right hAab

/-- **The matrices commuting with the orthogonal group on two strands.** Let `M` commute with the
Kronecker square of every orthogonal matrix, where some orthogonal matrix `A` has
`A a a * A a b ≠ 0` for labels `a ≠ b`. Then `M` is the combination of the matrices of the three
Brauer diagrams on two strands whose coefficients are the entries of `M` at a pair `a₀ ≠ a₁` of
labels. -/
private theorem eq_diagramCombination [NoZeroDivisors R]
    (hM : ∀ A : Matrix ι ι R, Aᵀ * A = 1 → Commute M (A.kroneckerPower (Fin 2)))
    (h2 : (2 : R) ≠ 0) {a₀ a₁ : ι} (h01 : a₀ ≠ a₁)
    (hrot : ∃ A : Matrix ι ι R, Aᵀ * A = 1 ∧ ∃ a b, a ≠ b ∧ A a a * A a b ≠ 0) :
    M = diagramCombination R ι (M ![a₀, a₁] ![a₀, a₁]) (M ![a₀, a₁] ![a₁, a₀])
      (M ![a₀, a₀] ![a₁, a₁]) := by
  obtain ⟨A, hA, a, b, hab, hAab⟩ := hrot
  have hMN := eq_diagramCombination_add_smul hM h2 h01
  -- The diagram matrices commute with every orthogonal Kronecker square, hence so does the
  -- remaining multiple of `TauCeti.diagonalTensorMatrix`.
  have hN (x y z : R) : Commute (diagramCombination R ι x y z) (A.kroneckerPower (Fin 2)) := by
    rw [diagramCombination]
    refine ((Commute.smul_left ?_ _).add_left (Commute.smul_left ?_ _)).add_left
      (Commute.smul_left ?_ _) <;>
    exact BrauerDiagram.commute_orthogonalActionMatrix_kroneckerPower _ hA
  rw [← sub_eq_iff_eq_add'] at hMN
  have ht := eq_zero_of_commute_smul_diagonalTensorMatrix (hMN ▸ (hM A hA).sub_left (hN _ _ _))
    hab hAab
  rw [← sub_eq_zero, hMN, ht, zero_smul]

end TwoStrands

/-! ### Brauer duality on two strands -/

section Duality

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **Brauer duality for the orthogonal group on two strands.** Over a commutative ring without
zero divisors in which `2 ≠ 0` and which contains a point `(c, s)` of the unit circle with
`c * s ≠ 0`, the operators on `Rⁿ ⊗ Rⁿ` commuting with the diagonal action of the orthogonal
group are exactly the image of the Brauer algebra `B₂(n)`: the combinations of the identity, the
flip of the two factors, and the contraction-expansion `x ⊗ y ↦ (x ⬝ᵥ y) • ∑ᵢ eᵢ ⊗ eᵢ`.

Some point of the circle with `c * s ≠ 0` is needed when `n = 2`: over `ZMod 3` the orthogonal
group of the plane consists of the signed permutation matrices, which commute with the projection
onto the span of `e₀ ⊗ e₀` and `e₁ ⊗ e₁`, and that projection is not in the image. -/
theorem range_brauerActionOrth_two_eq_centralizer_of_noZeroDivisors [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (hrot : ∃ c s : R, c ^ 2 + s ^ 2 = 1 ∧ c * s ≠ 0) :
    (brauerActionOrth R n 2).range =
      Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower 2)) := by
  refine le_antisymm (range_brauerActionOrth_le_centralizer R n 2) fun T hT => ?_
  set b := tensorPowerBasis R n 2 with hb
  set M := LinearMap.toMatrix b b T
  -- The matrix of `T` commutes with the Kronecker square of every orthogonal matrix.
  have hM : ∀ A : Matrix (Fin n) (Fin n) R, Aᵀ * A = 1 → Commute M (A.kroneckerPower (Fin 2)) := by
    intro A hA
    have h := (Subalgebra.mem_centralizer_iff R).mp hT _
      ⟨⟨A, (Matrix.mem_orthogonalGroup_iff' (Fin n) R).mpr hA⟩, rfl⟩
    rw [Representation.tensorPower_apply, stdOrthogonalRep_apply] at h
    have h' := congrArg (LinearMap.toMatrix b b) h
    rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
      Matrix.toMatrix_piTensorProductMap_tensorPowerBasis] at h'
    exact h'.symm
  obtain ⟨x, hx⟩ : ∃ x : BrauerAlgebra R (n : R) 2,
      LinearMap.toMatrix b b (brauerActionOrth R n 2 x) = M := by
    rcases lt_or_ge n 2 with hn | hn
    · -- With at most one label there is at most one basis tensor, so `M` is a scalar.
      have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
      refine ⟨M.trace • 1, ?_⟩
      ext v u
      obtain rfl := Subsingleton.elim v u
      simp [Matrix.trace, Fintype.sum_subsingleton _ v]
    · set a₀ : Fin n := ⟨0, by omega⟩
      set a₁ : Fin n := ⟨1, by omega⟩
      have h01 : a₀ ≠ a₁ := by simp [a₀, a₁, Fin.ext_iff]
      refine ⟨M ![a₀, a₁] ![a₀, a₁] • .of (permToBrauer 1) +
        M ![a₀, a₁] ![a₁, a₀] • .of (permToBrauer (Equiv.swap 0 1)) +
        M ![a₀, a₀] ![a₁, a₁] • .of (capCup 0 1), ?_⟩
      simp only [map_add, map_smul, brauerActionOrth_of, ← hb, LinearMap.toMatrix_toLin]
      exact (eq_diagramCombination hM h2 h01
        (exists_orthogonal_apply_mul_apply_ne_zero hn hrot)).symm
  exact ⟨x, (LinearMap.toMatrix b b).injective hx⟩

/-- **The commutant of the orthogonal group on `Rⁿ ⊗ Rⁿ` has rank three** when `n ≥ 2`, under the
hypotheses of `TauCeti.range_brauerActionOrth_two_eq_centralizer_of_noZeroDivisors`: it is the
image of the Brauer algebra `B₂(n)`, on which the action is faithful, and `B₂(n)` is free on its
three diagrams. -/
theorem finrank_centralizer_stdOrthogonalRep_tensorPower_two [IsDomain R] {n : ℕ} (hn : 2 ≤ n)
    (h2 : (2 : R) ≠ 0) (hrot : ∃ c s : R, c ^ 2 + s ^ 2 = 1 ∧ c * s ≠ 0) :
    Module.finrank R
      (Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower 2))) = 3 := by
  rw [← range_brauerActionOrth_two_eq_centralizer_of_noZeroDivisors R n h2 hrot,
    ← (AlgEquiv.ofInjective _ (brauerActionOrth_injective R n 2 hn)).toLinearEquiv.finrank_eq,
    BrauerAlgebra.finrank_eq_doubleFactorial]
  rfl

end Duality

end TauCeti
