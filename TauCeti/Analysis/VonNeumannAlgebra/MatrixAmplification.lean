/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import TauCeti.Analysis.InnerProductSpace.Amplification

/-!
# Matrix amplifications of star algebras of operators

For a star subalgebra `S` of the bounded operators on a Hilbert space `H` and a finite index type
`ι`, the matrix amplification `Mᵢ(S)` is the star subalgebra `StarSubalgebra.piLpMatrix ι S` of
operators on the Hilbert sum `PiLp 2 (fun _ : ι => H)` all of whose matrix entries
(`ContinuousLinearMap.piLpEntry`) lie in `S`.

Taking double commutants commutes with matrix amplification: an operator on the Hilbert sum lies
in the double commutant of `Mᵢ(S)` exactly when all its matrix entries lie in the double commutant
of `S` (`StarSubalgebra.mem_centralizer_centralizer_piLpMatrix_iff`). The commutant of `Mᵢ(S)`
consists of the block-diagonal operators with constant diagonal entry in the commutant of `S`
(`StarSubalgebra.mem_centralizer_piLpMatrix_iff`): an operator commuting with the matrix units is
diagonal with equal diagonal entries, and commuting with the diagonal copies of `S` puts that entry
in the commutant of `S`.

This is how statements about the double commutant of `S`, such as the Kaplansky density theorem,
pass to its matrix amplifications; the `2 × 2` case turns the self-adjoint form of the Kaplansky
density theorem into the general one.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, the proof of
Theorem 5.3.5.
-/

public section

namespace StarSubalgebra

open ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The matrix amplification `Mᵢ(S)` of a star subalgebra `S` of operators on `H`: the operators on
the Hilbert sum `PiLp 2 (fun _ : ι => H)` all of whose matrix entries lie in `S`. -/
def piLpMatrix (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    StarSubalgebra 𝕜 (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  carrier := {T | ∀ i j, T.piLpEntry i j ∈ S}
  mul_mem' {T U} hT hU i k := by
    rw [piLpEntry_mul]
    exact sum_mem fun j _ => mul_mem (hT i j) (hU j k)
  add_mem' {T U} hT hU i j := by
    rw [piLpEntry_add]
    exact add_mem (hT i j) (hU i j)
  algebraMap_mem' c i j := by
    rw [← AlgHomClass.commutes (PiLp.diagStarAlgHom 𝕜 H ι) c, piLpEntry_diagStarAlgHom]
    split_ifs
    exacts [S.algebraMap_mem c, zero_mem S]
  star_mem' {T} hT i j := by
    rw [piLpEntry_star]
    exact star_mem (hT j i)

@[simp]
theorem mem_piLpMatrix {S : StarSubalgebra 𝕜 (H →L[𝕜] H)}
    {T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    T ∈ S.piLpMatrix ι ↔ ∀ i j, T.piLpEntry i j ∈ S :=
  Iff.rfl

/-- Placing an element of `S` in a single `(i, j)` block belongs to `S.piLpMatrix ι`, and
conversely. -/
theorem singleEntryCLM_mem_piLpMatrix {S : StarSubalgebra 𝕜 (H →L[𝕜] H)} {i j : ι}
    {s : H →L[𝕜] H} :
    PiLp.singleEntryCLM i j s ∈ S.piLpMatrix ι ↔ s ∈ S := by
  refine ⟨fun h => by simpa using h i j, fun hs k l => ?_⟩
  rw [piLpEntry_singleEntryCLM]
  split_ifs
  exacts [hs, zero_mem S]

/-- The diagonal amplification of an element of `S` lies in the matrix amplification of `S`. -/
theorem diagStarAlgHom_mem_piLpMatrix {S : StarSubalgebra 𝕜 (H →L[𝕜] H)} {s : H →L[𝕜] H}
    (hs : s ∈ S) : PiLp.diagStarAlgHom 𝕜 H ι s ∈ S.piLpMatrix ι := fun i j => by
  rw [piLpEntry_diagStarAlgHom]
  split_ifs
  exacts [hs, zero_mem S]

/-- The commutant of the matrix amplification `Mᵢ(S)` consists of the block-diagonal operators
with constant diagonal entry in `S'`. -/
theorem mem_centralizer_piLpMatrix_iff (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    {R : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    R ∈ (S.piLpMatrix ι : Set _).centralizer ↔
      (∀ i j, i ≠ j → R.piLpEntry i j = 0) ∧
        (∀ i j, R.piLpEntry i i = R.piLpEntry j j) ∧
        ∀ i, R.piLpEntry i i ∈ (S : Set (H →L[𝕜] H)).centralizer := by
  refine ⟨fun hR => ?_, fun ⟨hoff, hdiag, hcomm⟩ A hA => ext_piLpEntry fun i j => ?_⟩
  · -- `R` commutes with each matrix unit `E a b`, whose only nonzero entry is `1` at `(a, b)`;
    -- comparing the `(k, l)` entries of `E a b * R` and `R * E a b` gives `hE`.
    have hE (a b k l : ι) :
        (if k = a then R.piLpEntry b l else 0) = if l = b then R.piLpEntry k a else 0 := by
      have h := congrArg (fun T => piLpEntry T k l)
        (hR (PiLp.singleEntryCLM a b 1) (singleEntryCLM_mem_piLpMatrix.2 (one_mem S)))
      simpa using h
    refine ⟨fun i j hij => ?_, fun i j => ?_, fun i s hs => ?_⟩
    · simpa [hij.symm] using hE i i i j
    · simpa using (hE i j i j).symm
    · -- `R` commutes with the diagonal amplification of `s ∈ S`.
      simpa using congrArg (fun T => piLpEntry T i i) (hR _ (diagStarAlgHom_mem_piLpMatrix hs))
  · rw [piLpEntry_mul_of_offDiag_zero_right hoff,
      piLpEntry_mul_of_offDiag_zero_left hoff, hdiag i j]
    exact hcomm j (A.piLpEntry i j) (hA i j)

/-- **Double commutants of matrix amplifications.** An operator on the Hilbert sum lies in the
double commutant of the matrix amplification `Mᵢ(S)` exactly when all its matrix entries lie in
the double commutant of `S`. -/
theorem mem_centralizer_centralizer_piLpMatrix_iff (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    {T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    T ∈ (S.piLpMatrix ι : Set _).centralizer.centralizer ↔
      ∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer := by
  refine ⟨fun hT i j r hr => ?_, fun hT R hR => ext_piLpEntry fun i k => ?_⟩
  · -- The diagonal amplification of `r ∈ S'` commutes with `Mᵢ(S)`.
    have hdiag : PiLp.diagStarAlgHom 𝕜 H ι r ∈ (S.piLpMatrix ι : Set _).centralizer :=
      fun U hU => ext_piLpEntry fun i j => by simpa using hr _ (hU i j)
    simpa using congrArg (fun T => piLpEntry T i j) (hT _ hdiag)
  · -- `R` is the diagonal amplification of its entry `R k k`, which lies in `S'`.
    obtain ⟨hoff, hdiag, hcomm⟩ := (mem_centralizer_piLpMatrix_iff S).mp hR
    rw [piLpEntry_mul_of_offDiag_zero_right hoff,
      piLpEntry_mul_of_offDiag_zero_left hoff, hdiag i k]
    exact hT i k _ (hcomm k)

end StarSubalgebra
