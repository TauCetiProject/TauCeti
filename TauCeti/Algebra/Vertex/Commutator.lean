/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.ResidueProduct

/-!
# The commutator formula in a formal vertex algebra

Let `V` be a formal vertex algebra (`TauCeti.FormalVertexAxioms`) whose underlying additive group
is torsion-free, for instance a vector space over a field of characteristic zero. For `n ≥ 0`
the field of the state `a₍ₙ₎ b` is the residue product of the fields of `a` and `b`:

`Y(a₍ₙ₎ b, w) = Res_z (z - w)ⁿ [Y(a,z), Y(b,w)]`

(`TauCeti.FormalVertexAxioms.field_ncoeff_apply`). Combined with the delta expansion of a local
commutator, this gives the **commutator formula**

`[a₍ₘ₎, b₍ₙ₎] = ∑_{j ≥ 0} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`

for all integers `m` and `n`, a finite sum because `a₍ⱼ₎ b = 0` for large `j`
(`TauCeti.FormalVertexAxioms.lie_ncoeff_field_eq_sum`). Its case `m = 0` says that each `a₍₀₎`
acts as a derivation of all products: `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`.

The proof follows Kac. By Dong's lemma (`VertexOperator.isLocalOfOrder_nonnegResidueProduct`)
the residue product is local with every field, and it is translation covariant
(`VertexOperator.lie_ncoeff_nonnegResidueProduct`). A covariant field local with every field and
with no negative powers of `z` on the vacuum is the field of `B₍₋₁₎|0⟩`
(`TauCeti.FormalVertexAxioms.eq_field_of_lie_translation`, in `TauCeti.Algebra.Vertex.Axioms`).

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: `Y(a₍ₙ₎ b) = Y(a)₍ₙ₎ Y(b)` for `n ≥ 0`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field_eq_sum`: the commutator formula.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_zero_field`: `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Chapter 3 (Dong's lemma) and Chapter 4
  (the `n`-th product identity, from the uniqueness theorem, and the commutator formula).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., Chapter 3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- The **`n`-th product identity** for `n ≥ 0`: the field of `a₍ₙ₎ b` is the residue product
`Res_z (z - w)ⁿ [Y(a,z), Y(b,w)]` of the fields of `a` and `b`. -/
theorem field_ncoeff_apply [IsAddTorsionFree V] (a b : V) (n : ℕ) :
    A.field (((A.field a)[[n]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  set P := nonnegResidueProduct n (A.field a) (A.field b)
  have hvac (k : ℤ) : (P[[k]]) A.vacuum =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((A.field a)[[(ij.1 : ℤ)]]) (((A.field b)[[k + ij.2]]) A.vacuum) := by
    rw [ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    refine sum_congr rfl fun ij _ ↦ ?_
    simp [A.ncoeff_field_apply_vacuum_of_nonneg a ij.1 (by positivity), -zsmul_eq_mul,
      -nsmul_eq_mul]
  -- A summand of `hvac` vanishes once `b₍ₖ₊ⱼ₎|0⟩ = 0`, that is, when `k + j ≥ 0`.
  have hterm (k : ℤ) (ij : ℕ × ℕ) (hk : 0 ≤ k + ij.2) : n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
      ((A.field a)[[(ij.1 : ℤ)]]) (((A.field b)[[k + ij.2]]) A.vacuum) = 0 := by
    simp [A.ncoeff_field_apply_vacuum_of_nonneg _ _ hk]
  have hP : P = A.field ((P[[-1]]) A.vacuum) := by
    refine A.eq_field_of_lie_translation (fun c ↦ ?_)
      (lie_ncoeff_nonnegResidueProduct (A.lie_translation_ncoeff a)
        (A.lie_translation_ncoeff b) n) fun k hk ↦ ?_
    · obtain ⟨N₁, h₁⟩ := A.exists_isLocalOfOrder a b
      obtain ⟨N₂, h₂⟩ := A.exists_isLocalOfOrder a c
      obtain ⟨N₃, h₃⟩ := A.exists_isLocalOfOrder b c
      exact ⟨_, isLocalOfOrder_nonnegResidueProduct h₁ h₂ h₃ n⟩
    · rw [hvac]
      exact sum_eq_zero fun ij _ ↦ hterm k ij (by omega)
  have hP₁ : (P[[-1]]) A.vacuum = ((A.field a)[[n]]) b := by
    rw [hvac, sum_eq_single (n, 0)]
    · simp
    · intro ij hij hne
      have hj : ij.2 ≠ 0 := fun hj ↦ hne (Prod.ext (by simpa [hj] using mem_antidiagonal.1 hij) hj)
      exact hterm (-1) ij (by omega)
    · simp
  rw [hP, hP₁]

/-- **The commutator formula** `[a₍ₘ₎, b₍ₙ₎] = ∑_{j < N} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`, for any
`N` such that `a₍ⱼ₎ b = 0` for all `j ≥ N`. -/
theorem lie_ncoeff_field_eq_sum [IsAddTorsionFree V] (a b : V) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → ((A.field a)[[j]]) b = 0) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (A.field (((A.field a)[[j]]) b))[[m + n - j]] := by
  obtain ⟨N', h⟩ := A.exists_isLocalOfOrder a b
  rw [h.lie_ncoeff_eq_sum]
  simp_rw [← A.field_ncoeff_apply]
  -- Both sums agree with the sum up to `max N N'`: the extra terms vanish.
  have hzero (M : ℕ) (hle : M ≤ max N N') (hM : ∀ j : ℕ, M ≤ j → ((A.field a)[[j]]) b = 0) :
      ∑ j ∈ range M, Ring.choose m j • (A.field (((A.field a)[[j]]) b))[[m + n - j]] =
        ∑ j ∈ range (max N N'), Ring.choose m j •
          (A.field (((A.field a)[[j]]) b))[[m + n - j]] := by
    refine sum_subset (range_subset_range.2 hle) fun j _ hjM ↦ ?_
    rw [hM j (by simpa using hjM), map_zero, map_zero, Pi.zero_apply, smul_zero]
  have hN' (j : ℕ) (hj : N' ≤ j) : ((A.field a)[[j]]) b = 0 :=
    A.field_injective (by rw [A.field_ncoeff_apply, map_zero,
      h.nonnegResidueProduct_eq_zero hj])
  rw [hzero N' (le_max_right N N') hN', hzero N (le_max_left N N') hN]

/-- The zero mode `a₍₀₎` is a derivation of all products: `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`. -/
theorem lie_ncoeff_zero_field [IsAddTorsionFree V] (a b : V) (n : ℤ) :
    ⁅(A.field a)[[0]], (A.field b)[[n]]⁆ = (A.field (((A.field a)[[0]]) b))[[n]] := by
  obtain ⟨N, hN⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  rw [A.lie_ncoeff_field_eq_sum a b (N := N + 1) (fun j hj ↦ hN j (by omega)), sum_range_succ']
  simp [Ring.choose_zero_succ]

end FormalVertexAxioms

end TauCeti
