/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.RaisesDegree
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL
public import TauCeti.RingTheory.Valuation.Pair
import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Valuation.Pair

/-!
# Triangular decomposition of matrices over the finite adeles

Let `R` be a Dedekind domain with fraction field `K`, `𝔸_f` its finite adeles and `Ô = ∏_v 𝒪_v`
the integral finite adeles. Although `Ô` is far from a valuation ring (it has many idempotents),
it is a *valuation pair* inside `𝔸_f` (`Subring.IsValuationPair`): any two finite adeles are
`Ô`-multiples of a single one, obtained by choosing place by place the one of larger absolute
value. Indeed `Ô` is the pullback, along the injection of `𝔸_f` into the full product `∏_v K_v`,
of the product `∏_v 𝒪_v` of the valuation subrings, which is a valuation pair
(`Subring.IsValuationPair.pi`, `Subring.IsValuationPair.comap`).

Row reduction over a valuation pair (`Subring.IsValuationPair.exists_mul_blockTriangular`) then
gives the Iwasawa decomposition of matrices over `𝔸_f` along any flag of coordinate subspaces:
for an integer grading `deg` of the index set, every square matrix `Z` over `𝔸_f` becomes, after
multiplication on the right by a matrix of `GL_n(Ô)`, a matrix `b` such that `b` and `b⁻¹` have
degree `≥ 0`, that is, are block triangular for the blocks of equal degree
(`Matrix.raisesDegree_zero_iff_blockTriangular`). For `Z` invertible, `b = Z k` is a basis of the
`Ô`-lattice `Z Ôⁿ` adapted to the flag of the grades.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.isValuationPair_integralAdeles`: `Ô` is a valuation pair in
  `𝔸_f`.
* `IsDedekindDomain.FiniteAdeleRing.exists_raisesDegree_mul_integralGL`: for every square matrix
  `Z` over `𝔸_f` there is `k ∈ GL_n(Ô)` such that `Z k` and `(Z k)⁻¹` have degree `≥ 0`.

## References

* J. Tits, *Reductive groups over local fields*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33 (1979), §3.3.2, for the Iwasawa decomposition.
* N. Bourbaki, *Commutative Algebra*, Chapter VI (valuation rings and finitely generated ideals).

The statement `IsDedekindDomain.FiniteAdeleRing.exists_raisesDegree_mul_integralGL` corresponds to
`New.Grading.exists_basis_hasDegreeGe` in `src/Lib/Weil/Periods/GradedLattice.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0), stated there for the grade of a graded
hermitian space. The proof here is independent: it goes through valuation pairs.
-/

public section

open Matrix

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (R K) in
/-- The integral finite adeles `Ô` form a valuation pair inside the finite adeles: for any two
finite adeles `a` and `b` there is an idempotent `e ∈ Ô` such that `a` and `b` are `Ô`-multiples
of `a - e (a - b)`. -/
theorem isValuationPair_integralAdeles : (integralAdeles R K).toSubring.IsValuationPair := by
  -- the injection of `𝔸_f` into the full product of the completions
  let f : FiniteAdeleRing R K →+* ∀ v : HeightOneSpectrum R, v.adicCompletion K :=
    RingHom.pi fun v ↦ (proj K v : FiniteAdeleRing R K →+* v.adicCompletion K)
  have hf (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) : f a v = a v := by
    simp [f]
  let O : Subring (∀ v : HeightOneSpectrum R, v.adicCompletion K) :=
    ⨅ v : HeightOneSpectrum R, (v.adicCompletionIntegers K).toSubring.comap (Pi.evalRingHom _ v)
  have hO (x : ∀ v : HeightOneSpectrum R, v.adicCompletion K) :
      x ∈ O ↔ ∀ v, x v ∈ v.adicCompletionIntegers K := by
    simp [O, Subring.mem_iInf]
  have hOf : O ≤ f.range := fun x hx ↦
    ⟨integralEmbedding fun v ↦ ⟨x v, (hO x).1 hx v⟩, funext fun v ↦ by simp [hf]⟩
  have hcomap : (integralAdeles R K).toSubring = O.comap f := by
    ext a
    simp [hO, hf]
  rw [hcomap]
  exact (Subring.IsValuationPair.pi fun v ↦
    (v.adicCompletionIntegers K).isValuationPair_toSubring).comap
      (fun a b h ↦ DFunLike.ext _ _ fun v ↦ by simpa [hf] using congrFun h v) hOf

variable (K) in
/-- **Iwasawa decomposition over the finite adeles.** For an integer grading `deg` of a finite
index type `ι` and a square matrix `Z` over `𝔸_f`, some `k ∈ GL_ι(Ô)` makes both `b = Z k` and
`b⁻¹` of degree `≥ 0`: their entry in row `r` and column `s` vanishes whenever
`deg r < deg s`. -/
theorem exists_raisesDegree_mul_integralGL {ι : Type*} [Fintype ι] [DecidableEq ι] (deg : ι → ℤ)
    (Z : Matrix ι ι (FiniteAdeleRing R K)) :
    ∃ k : GL ι (integralAdeles R K),
      (Z * (integralGL K ι k).val).RaisesDegree deg 0 ∧
        (Z * (integralGL K ι k).val)⁻¹.RaisesDegree deg 0 := by
  obtain ⟨k, hk⟩ :=
    (isValuationPair_integralAdeles R K).exists_mul_blockTriangular (OrderDual.toDual ∘ deg) Z
  -- `k` lives in `GL ι` of the subring `(integralAdeles R K).toSubring`, whose underlying subtype
  -- is that of `integralAdeles R K`; `Subalgebra.toSubring_subtype` identifies the inclusions.
  rw [Subalgebra.toSubring_subtype] at hk
  have hb : (Z * (integralGL K ι k).val).RaisesDegree deg 0 := by
    rw [integralGL_def, raisesDegree_zero_iff_blockTriangular]
    exact hk
  exact ⟨k, hb, hb.inv⟩

end IsDedekindDomain.FiniteAdeleRing
