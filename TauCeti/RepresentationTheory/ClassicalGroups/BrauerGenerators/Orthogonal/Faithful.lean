/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Action
public import TauCeti.RingTheory.Jacobson.FiniteOverArtinian

/-!
# The orthogonal Brauer action is faithful in large dimension, and `B_k(n)` is semisimple

The Brauer algebra `B_k(n)` acts on the tensor power `(Rⁿ)^{⊗k}` through the standard symmetric
form (`TauCeti.brauerActionOrth`), a diagram `D` acting by the matrix `M(D)` whose entry at a
labelling `Sum.elim u v` of the boundary points is `1` when the labelling is constant on the arcs
of `D`, and `0` otherwise. In small dimension this action is not faithful. Once `k ≤ n`, however,
it is: the `k` arcs of a diagram `D` can be given pairwise distinct labels, and the resulting
labelling is constant on the arcs of `D` and of no other diagram
(`TauCeti.BrauerDiagram.exists_forall_isConstantOnArcs_iff_eq`). So the entry of
`∑ D, c_D • M(D)` at that labelling is the single coefficient `c_D`, the matrices of the diagrams
are linearly independent (`TauCeti.BrauerDiagram.linearIndependent_orthogonalActionMatrix`), and
the action is injective over every commutative semiring (`TauCeti.brauerActionOrth_injective`).

Over a star-ordered field `K`, such as `ℚ`, `ℝ` or `ℂ`, faithfulness makes the Brauer algebra
`B_k(n)` semisimple for `k ≤ n` (`TauCeti.BrauerAlgebra.isSemisimpleRing_of_le`). The matrices
of the diagrams have entries `0` and `1`, and the transpose of `M(D)` is the matrix of the
reflected diagram `D.flip`, so the image of the action is closed under conjugate transposition.
If `x` lies in the Jacobson radical, which is a nilpotent ideal, then so does `y * x` for the
element `y = ∑ D, star c_D • D.flip` acting by the conjugate transpose of the matrix `A` of `x`;
hence `Aᴴ * A` is a nilpotent self-adjoint matrix, so it vanishes, so `A = 0`, and `x = 0` by
faithfulness. The radical is zero, and a finite-dimensional algebra with zero radical is
semisimple.

The loop value here is the dimension `n` itself, at least the number `k` of strands. The Brauer
algebra is also semisimple at generic loop values, and at the symplectic value `-2l` when `k` is
small relative to `l`, which this argument does not reach.

## Main results

* `TauCeti.BrauerDiagram.linearIndependent_orthogonalActionMatrix`: with at least `k` labels, the
  matrices of the Brauer diagrams on `k` strands are linearly independent.
* `TauCeti.brauerActionOrth_injective`: **the action of `B_k(n)` on `(Rⁿ)^{⊗k}` is faithful** when
  `k ≤ n`.
* `TauCeti.BrauerAlgebra.isSemisimpleRing_of_le`: **the Brauer algebra `B_k(n)` is semisimple**
  over a star-ordered field when `k ≤ n`.

## References

* R. Brauer, *On algebras which are connected with the semisimple continuous groups*, Annals of
  Mathematics 38 (1937), 857-872.
* W. P. Brown, *An algebra related to the orthogonal group*, Michigan Mathematical Journal 3
  (1955), 1-22.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped Matrix

namespace TauCeti

universe u

namespace BrauerDiagram

variable (R : Type u) [CommSemiring R] (ι : Type*) [DecidableEq ι] [Fintype ι] {k : ℕ}

/-- **The matrices of the Brauer diagrams are linearly independent** as soon as there are at least
as many labels as strands. -/
theorem linearIndependent_orthogonalActionMatrix (hk : k ≤ Fintype.card ι) :
    LinearIndependent R fun D : BrauerDiagram k => D.orthogonalActionMatrix R ι := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  intro f g hfg
  ext D
  obtain ⟨ℓ, hℓ⟩ := exists_forall_isConstantOnArcs_iff_eq hk D
  have hcoeff (f : BrauerDiagram k →₀ R) :
      Finsupp.linearCombination R (fun D : BrauerDiagram k => D.orthogonalActionMatrix R ι) f
        (ℓ ∘ Sum.inr) (ℓ ∘ Sum.inl) = f D := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply, hℓ]
  rw [← hcoeff f, ← hcoeff g, hfg]

end BrauerDiagram

variable (R : Type u) [CommSemiring R] (n k : ℕ)

/-- **The orthogonal Brauer action is faithful in large dimension**: when the number `k` of
strands is at most the dimension `n`, distinct elements of `B_k(n)` act differently on
`(Rⁿ)^{⊗k}`. -/
theorem brauerActionOrth_injective (hk : k ≤ n) : Function.Injective (brauerActionOrth R n k) := by
  intro x y h
  have hmat := congrArg (LinearMap.toMatrix (tensorPowerBasis R n k) (tensorPowerBasis R n k)) h
  rw [toMatrix_brauerActionOrth, toMatrix_brauerActionOrth] at hmat
  exact BrauerAlgebra.ext ((BrauerDiagram.linearIndependent_orthogonalActionMatrix R (Fin n)
    (by simpa using hk)).finsuppLinearCombination_injective hmat)

variable {n k}

/-- **The Brauer algebra `B_k(n)` is semisimple** over a star-ordered field, such as `ℚ`, `ℝ` or
`ℂ` (with `ComplexOrder`), when the loop value `n` is a natural number at least the number `k` of
strands. -/
theorem BrauerAlgebra.isSemisimpleRing_of_le {K : Type*} [Field K] [PartialOrder K] [StarRing K]
    [StarOrderedRing K] (hk : k ≤ n) : IsSemisimpleRing (BrauerAlgebra K (n : K) k) := by
  -- the matrix of the action, an injective algebra map
  let Φ : BrauerAlgebra K (n : K) k →ₐ[K] Matrix (Fin k → Fin n) (Fin k → Fin n) K :=
    (LinearMap.toMatrixAlgEquiv (tensorPowerBasis K n k)).toAlgHom.comp (brauerActionOrth K n k)
  have hΦ (x : BrauerAlgebra K (n : K) k) : Φ x = Finsupp.linearCombination K
      (fun D : BrauerDiagram k => D.orthogonalActionMatrix K (Fin n)) x.coeff := by
    rw [← toMatrix_brauerActionOrth]
    ext i j
    simp [Φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hinj : Function.Injective Φ :=
    (LinearMap.toMatrixAlgEquiv _).injective.comp (brauerActionOrth_injective K n k hk)
  rw [isSemisimpleRing_iff_jacobson_eq_bot (K := K)]
  obtain ⟨m, hm⟩ := isNilpotent_jacobson (K := K) (A := BrauerAlgebra K (n : K) k)
  refine eq_bot_iff.mpr fun x hx => ?_
  -- the reflected diagrams with conjugate coefficients act by the conjugate transpose of `Φ x`
  let y : BrauerAlgebra K (n : K) k :=
    ∑ D ∈ x.coeff.support, star (x.coeff D) • BrauerAlgebra.of D.flip
  have hof (D : BrauerDiagram k) : Φ (BrauerAlgebra.of D) = D.orthogonalActionMatrix K (Fin n) := by
    simp [hΦ]
  have hy : Φ y = (Φ x)ᴴ := by
    rw [hΦ x]
    simp [y, hof, Finsupp.linearCombination_apply, Finsupp.sum, Matrix.conjTranspose_sum]
  -- `y * x` lies in the nilpotent radical, so `(Φ x)ᴴ * Φ x` is a nilpotent self-adjoint matrix
  have hnil : IsNilpotent ((Φ x)ᴴ * Φ x) := by
    refine ⟨m, ?_⟩
    have hpow := Ideal.pow_mem_pow ((Ring.jacobson _).smul_mem y hx) m
    rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot, smul_eq_mul] at hpow
    rw [← hy, ← map_mul, ← map_pow, hpow, map_zero]
  have h0 := (IsSelfAdjoint.star_mul_self (Φ x)).eq_zero_of_isNilpotent hnil
  rw [star_mul_self_eq_zero, ← map_zero Φ] at h0
  exact (Submodule.mem_bot _).mpr (hinj h0)

end TauCeti
