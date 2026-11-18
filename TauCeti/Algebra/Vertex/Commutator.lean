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
(`VertexOperator.lie_ncoeff_nonnegResidueProduct`). A covariant field local with every field is
the field of its value on the vacuum (`TauCeti.FormalVertexAxioms.eq_field_of_lie_translation`);
here torsion-freeness recovers its creation series from the recursion
`T (B₍ₖ₎|0⟩) = -k B₍ₖ₋₁₎|0⟩`.

## Main results

* `TauCeti.FormalVertexAxioms.eq_field_of_lie_translation`: a translation covariant field local
  with every `Y(a,z)` and with no negative powers on the vacuum is `Y(B₍₋₁₎|0⟩, z)`.
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

/-- A translation covariant field `B` that is local with every field `Y(a,z)` and has no
negative powers of `z` on the vacuum is the field of the state `B₍₋₁₎|0⟩`. -/
theorem eq_field_of_lie_translation [IsAddTorsionFree V] {B : VertexOperator R V}
    (hB : ∀ a, ∃ N, B.IsLocalOfOrder (A.field a) N)
    (hT : ∀ n : ℤ, ⁅A.translation, B[[n]]⁆ = (derivative B)[[n]])
    (hvac : ∀ n : ℤ, 0 ≤ n → (B[[n]]) A.vacuum = 0) :
    B = A.field ((B[[-1]]) A.vacuum) := by
  set b := (B[[-1]]) A.vacuum
  refine A.eq_field_of_ncoeff_apply_vacuum_eq hB ?_
  -- Both creation series satisfy `T x₍ₖ₎ = -k x₍ₖ₋₁₎` and agree in degrees `k ≥ -1`.
  have hrec (n : ℤ) : A.translation ((B[[n]]) A.vacuum) = (-n) • (B[[n - 1]]) A.vacuum := by
    have h := LinearMap.congr_fun (hT n) A.vacuum
    rwa [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      A.translation_vacuum, map_zero, sub_zero, ncoeff_derivative, LinearMap.smul_apply] at h
  have hneg (l : ℕ) : (B[[-l - 1]]) A.vacuum = ((A.field b)[[-l - 1]]) A.vacuum := by
    induction l with
    | zero => simp [b]
    | succ l ih =>
      have h₁ := hrec (-l - 1)
      have h₂ := A.translation_ncoeff_apply_vacuum b (-l - 1)
      rw [ih, h₂, show -(-(l : ℤ) - 1) = ((l + 1 : ℕ) : ℤ) by push_cast; ring, natCast_zsmul,
        natCast_zsmul] at h₁
      rw [show -((l + 1 : ℕ) : ℤ) - 1 = -l - 1 - 1 by push_cast; ring]
      exact (eq_of_nsmul_eq_nsmul_of_addCommute (Nat.succ_ne_zero l) (.all _ _) h₁).symm
  intro n
  obtain ⟨k, rfl⟩ | ⟨l, rfl⟩ : (∃ k : ℕ, n = k) ∨ ∃ l : ℕ, n = -l - 1 := by
    rcases le_or_gt 0 n with h | h
    · exact .inl ⟨n.toNat, by omega⟩
    · exact .inr ⟨(-n - 1).toNat, by omega⟩
  · rw [hvac _ (by positivity), A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by positivity)]
  · exact hneg l

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
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
      mul_apply_eq_comp, A.ncoeff_field_apply_vacuum_of_nonneg a ij.1 (by positivity), map_zero,
      sub_zero]
  have hP : P = A.field ((P[[-1]]) A.vacuum) := by
    refine A.eq_field_of_lie_translation (fun c ↦ ?_)
      (lie_ncoeff_nonnegResidueProduct (A.lie_translation_ncoeff a)
        (A.lie_translation_ncoeff b) n) fun k hk ↦ ?_
    · obtain ⟨N₁, h₁⟩ := A.exists_isLocalOfOrder a b
      obtain ⟨N₂, h₂⟩ := A.exists_isLocalOfOrder a c
      obtain ⟨N₃, h₃⟩ := A.exists_isLocalOfOrder b c
      exact ⟨_, isLocalOfOrder_nonnegResidueProduct h₁ h₂ h₃ n⟩
    · rw [hvac]
      refine sum_eq_zero fun ij _ ↦ ?_
      rw [A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by omega), map_zero, smul_zero, smul_zero]
  have hP₁ : (P[[-1]]) A.vacuum = ((A.field a)[[n]]) b := by
    rw [hvac, sum_eq_single (n, 0)]
    · simp
    · intro ij hij hne
      have hj : ij.2 ≠ 0 := fun hj ↦ hne (Prod.ext (by simpa [hj] using mem_antidiagonal.1 hij) hj)
      rw [A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by omega), map_zero, smul_zero, smul_zero]
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
