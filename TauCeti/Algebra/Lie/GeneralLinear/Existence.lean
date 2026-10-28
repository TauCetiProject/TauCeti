/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.Sl2.Basic
import Mathlib.Algebra.Lie.Weights.Linear

/-!
# Highest weight vectors for `gl n`-modules with triangularizable diagonal action

Let `K` be a field of characteristic zero and let `M` be a nonzero finite-dimensional module over
`gl n K = Matrix n n K`. If the diagonal Cartan action is triangularizable, as it is over an
algebraically closed field, then `M` carries a highest weight vector for the matrix unit positive
system. The weight of any highest weight vector is dominant integral. For irreducible `M`, these
results give the existence half of the classification of finite-dimensional irreducible
`gl n`-modules.

Dominance holds more generally for Noetherian torsion-free modules over any domain of
characteristic zero.

## The argument

The diagonal Cartan subalgebra is abelian, hence nilpotent. Mathlib's
`LieModule.exists_nontrivial_weightSpace_of_isNilpotent` produces a nonzero simultaneous
eigenvector of the diagonal matrix units when their action is triangularizable. This step works
in every characteristic. Over `ℝ` a simultaneous eigenvector need not exist without the splitting
hypothesis. The whole Cartan action need not be semisimple: for instance, `gl 1` can act on `K²`
by a nilpotent Jordan block.

Such an eigenvector need not be annihilated by the raising matrix units, and the second half of
the argument moves it up until it is. Bracketing with `Eₚq` sends an eigenvector of weight `μ` to
an eigenvector of weight `μ + εₚ - ε_q`, so, writing `ht μ` for the value of `μ` on the fixed
diagonal operator `TauCeti.glHeightMatrix`, one raising step with `p < q` increases `ht` by the
positive integer `d p - d q`, where `d = TauCeti.glHeightLabel n` strictly decreases along the
ordered indices. All the vectors so produced are eigenvectors of a *single* operator, the
action of that fixed diagonal matrix, with pairwise distinct eigenvalues, so there are only
finitely many of them: the set of integers `m` for which an eigenvector of `ht`-value `ht μ₀ + m`
exists is finite. A vector realizing its greatest element is moved by no raising operator, which
is exactly a highest weight vector.

Dominance is the rank-one reduction. For `p < q` the matrix units `Eₚq`, `E_qp` and their
commutator `Eₚₚ - E_qq` form an `sl₂` triple, and a highest weight vector is a primitive vector
for it with eigenvalue `μ p - μ q`; Mathlib's `IsSl2Triple.HasPrimitiveVectorWith.exists_nat` then
makes that eigenvalue a natural number. This needs only a Noetherian torsion-free module over a
domain of characteristic zero, with no irreducibility or algebraic closure assumption.

## Main results

* `TauCeti.exists_isGlHighestWeightVector`: a nonzero finite-dimensional module over `gl n K`, for
  `K` of characteristic zero with triangularizable diagonal action, has a highest weight vector.
* `TauCeti.IsGlHighestWeightVector.isGlDominantIntegral`: the weight of a highest weight vector in
  a Noetherian torsion-free `gl n R`-module over a domain of characteristic zero is dominant
  integral.
* `TauCeti.exists_ne_zero_forall_lie_single_self_eq_smul`: triangularizable diagonal action gives
  a nonzero simultaneous eigenvector, in every characteristic.
* `TauCeti.exists_isGlHighestWeightVector_and_isGlDominantIntegral`: the two main results
  together.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §15.
* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255 (2009),
  Chapter 5.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

/-! ### Simultaneous eigenvectors of the diagonal -/

section Eigenvector

variable {K : Type u} [Field K] {n : Type v} [Fintype n] [DecidableEq n]
variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule (Matrix n n K) M]
  [LieModule K (Matrix n n K) M]

/-- A nonzero finite-dimensional `gl n`-module has a nonzero simultaneous eigenvector of the
diagonal matrix units when the diagonal action is triangularizable. This holds in particular over
an algebraically closed field, in any characteristic.

The eigenvector need not be annihilated by the raising matrix units; that is what
`TauCeti.exists_isGlHighestWeightVector` adds in characteristic zero. -/
theorem exists_ne_zero_forall_lie_single_self_eq_smul [FiniteDimensional K M] [Nontrivial M]
    [LieModule.IsTriangularizable K (diagonalCartan K n) M] :
    ∃ (mu : n → K) (v : M), v ≠ 0 ∧ ∀ i : n, ⁅(single i i 1 : Matrix n n K), v⁆ = mu i • v := by
  obtain ⟨chi, hchi⟩ :=
    LieModule.exists_nontrivial_weightSpace_of_isNilpotent K (diagonalCartan K n) M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace M chi)
  refine ⟨(glWeightEquiv K n).symm chi, v, ?_, ?_⟩
  · simpa [Submodule.mk_eq_zero] using hv0
  · exact (mem_weightSpace_glWeightEquiv_iff _ _).mp (by simpa using hv)

end Eigenvector

/-! ### Existence of a highest weight vector -/

section Existence

variable {K : Type u} [Field K] {n : Type v} [Fintype n] [DecidableEq n] [LinearOrder n]
variable {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix n n K) M] [LieModule K (Matrix n n K) M]

/-- A nonzero finite-dimensional `gl n`-module over a field of characteristic zero has a highest
weight vector when the diagonal Cartan action is triangularizable. The matrix indices may be any
finite linearly ordered type. The splitting hypothesis holds in particular over an algebraically
closed field.

Neither irreducibility nor a choice of generator is assumed; for irreducible `M` this is the
existence half of the classification of the finite-dimensional irreducibles of `gl n`. -/
theorem exists_isGlHighestWeightVector [CharZero K] [FiniteDimensional K M] [Nontrivial M]
    [LieModule.IsTriangularizable K (diagonalCartan K n) M] :
    ∃ (mu : n → K) (v : M), IsGlHighestWeightVector mu v := by
  classical
  obtain ⟨mu₀, v₀, hv₀, hmu₀⟩ :=
    exists_ne_zero_forall_lie_single_self_eq_smul (K := K) (n := n) (M := M)
  -- The integer height differences from the starting weight vector.
  set S : Set ℤ := {m | ∃ (mu : n → K) (v : M), v ≠ 0 ∧
    (∀ i : n, ⁅(single i i 1 : Matrix n n K), v⁆ = mu i • v) ∧
    glHeight K n mu = glHeight K n mu₀ + m}
  have hmem : ∀ m : S, ∃ (mu : n → K) (v : M), v ≠ 0 ∧
      (∀ i : n, ⁅(single i i 1 : Matrix n n K), v⁆ = mu i • v) ∧
      glHeight K n mu = glHeight K n mu₀ + ((m : ℤ) : K) := fun m => m.2
  choose weight vec hvec0 hveceig hvecht using hmem
  -- Those vectors are eigenvectors of one operator, with pairwise distinct eigenvalues.
  set T := LieModule.toEnd K (Matrix n n K) M (glHeightMatrix K n) with hT
  have hinj : Function.Injective fun m : S => glHeight K n mu₀ + ((m : ℤ) : K) := by
    intro a b hab
    exact Subtype.ext (by exact_mod_cast add_right_injective (glHeight K n mu₀) hab)
  have heig : ∀ m : S, T.HasEigenvector (glHeight K n mu₀ + ((m : ℤ) : K)) (vec m) :=
    fun m => ⟨Module.End.mem_eigenspace_iff.2
      (by simpa [hT, ← hvecht m] using lie_glHeightMatrix_eq_smul (hveceig m)), hvec0 m⟩
  have _i : Finite S := (T.eigenvectors_linearIndependent' _ hinj _ heig).finite
  -- So `S` has a greatest element, and its weight vector cannot be raised.
  have hne : S.Nonempty := ⟨0, mu₀, v₀, hv₀, hmu₀, by simp⟩
  obtain ⟨m, hmS, hmmax⟩ := (Set.toFinite S).exists_maximal hne
  refine ⟨weight ⟨_, hmS⟩, vec ⟨_, hmS⟩, isGlHighestWeightVector_iff.mpr
    ⟨hvec0 ⟨_, hmS⟩, hveceig ⟨_, hmS⟩, fun p q hpq => ?_⟩⟩
  by_contra hraise
  have hpos : 0 < glHeightLabel n p - glHeightLabel n q :=
    sub_pos.mpr (strictAnti_glHeightLabel hpq)
  have hstep : m + (glHeightLabel n p - glHeightLabel n q) ∈ S :=
    ⟨weight ⟨_, hmS⟩ + (Pi.single p 1 - Pi.single q 1), _, hraise,
      fun i => lie_single_self_lie_single_eq_smul (hveceig ⟨_, hmS⟩) p q i, by
        simp only [map_add, map_sub, glHeight_single, one_mul, hvecht ⟨_, hmS⟩,
          Int.cast_add, Int.cast_sub]
        ring⟩
  have := hmmax hstep (by omega)
  omega

end Existence

/-! ### Dominance of the highest weight -/

section Dominant

variable {K : Type u} [CommRing K] [IsDomain K] [CharZero K] {N : ℕ}
variable {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M] [LieModule K (Matrix (Fin N) (Fin N) K) M]
variable {mu : Fin N → K} {v : M}

/-- **The weight of a highest weight vector is dominant integral.** Restricting to the `sl₂` triple
of a pair `p < q` makes the highest weight vector a primitive vector of eigenvalue `μ p - μ q`, and
the eigenvalue of a primitive vector in a Noetherian torsion-free module is a natural number.

The scalars may be any domain of characteristic zero; neither irreducibility of `M` nor algebraic
closure of the scalars is used. -/
theorem IsGlHighestWeightVector.isGlDominantIntegral [IsNoetherian K M] [Module.IsTorsionFree K M]
    (hv : IsGlHighestWeightVector mu v) : IsGlDominantIntegral mu := by
  rw [isGlDominantIntegral_iff_forall_le]
  intro p q hpq
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact ⟨0, by simp⟩
  have hprim : (isSl2Triple_matrix_single (S := K) p q hlt.ne).HasPrimitiveVectorWith v
      (mu p - mu q) := by
    refine ⟨hv.ne_zero, ?_, hv.lie_single_eq_zero hlt⟩
    rw [sub_lie, hv.lie_single_self_eq_smul, hv.lie_single_self_eq_smul, sub_smul]
  exact hprim.exists_nat

end Dominant

section DominantExistence

variable {K : Type u} [Field K] [CharZero K] {N : ℕ}
variable {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M] [LieModule K (Matrix (Fin N) (Fin N) K) M]

/-- A nonzero finite-dimensional `gl N`-module over a field of characteristic zero with
triangularizable diagonal action has a dominant highest weight vector.

For an irreducible `M` this is the statement that a finite-dimensional irreducible `gl N`-module
has a dominant highest weight, the first half of the classification of the irreducibles of
`gl N`. -/
theorem exists_isGlHighestWeightVector_and_isGlDominantIntegral [FiniteDimensional K M]
    [Nontrivial M] [LieModule.IsTriangularizable K (diagonalCartan K (Fin N)) M] :
    ∃ (mu : Fin N → K) (v : M), IsGlHighestWeightVector mu v ∧ IsGlDominantIntegral mu := by
  obtain ⟨mu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (n := Fin N) (M := M)
  exact ⟨mu, v, hv, hv.isGlDominantIntegral⟩

end DominantExistence

end TauCeti
