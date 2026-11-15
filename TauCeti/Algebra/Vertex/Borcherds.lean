/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.Dong
import Mathlib.Algebra.Module.Rat

/-!
# The Borcherds identity and consequences for formal vertex algebras

We prove the **Borcherds (Jacobi–Cauchy) identity** first at the pure field level for any pair of
mutually local fields `A, B : VertexOperator R V` over an arbitrary commutative ring `R` (with no
torsion or characteristic hypotheses), and then deduce the fundamental structural identities of a
formal vertex algebra (`TauCeti.FormalVertexAxioms R V`):

* **State–field correspondence for all `n`-th products** (`FormalVertexAxioms.field_ncoeff_apply`):
  under `[IsAddTorsionFree V]`, `Y(a₍ₙ₎ b, z) = A₍ₙ₎ B` for all `n : ℤ`, specializing to residue
  products for `n ≥ 0`, normal ordering `:Y(a, z) Y(b, z):` for `n = -1`, and Hasse-differentiated
  normal ordering `:(∂_z^{(k)} Y(a, z)) Y(b, z):` for `n = -k - 1`.
* **The Borcherds identity** (`IsLocalOfOrder.borcherds`, `FormalVertexAxioms.borcherds`):
  for all `m, n, r : ℤ`,
  `∑ⱼ (m choose j) (a₍ₙ₊ⱼ₎ b)₍ₘ₊ᵣ₋ⱼ₎ c = ∑ᵢ (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ b₍ᵣ₊ᵢ₎ c -
    (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ a₍ₘ₊ᵢ₎ c)`.
* **Borcherds commutator formula** (`FormalVertexAxioms.lie_ncoeff_field_apply`,
  `FormalVertexAxioms.lie_ncoeff_field_of_isLocalOfOrder`,
  `FormalVertexAxioms.lie_ncoeff_zero_field`) at `n = 0`.
* **Borcherds iterate / associativity formula** (`FormalVertexAxioms.ncoeff_field_ncoeff_apply`)
  at `m = 0`.
* **Skew-symmetry** (`FormalVertexAxioms.ncoeff_field_apply_eq_finsum_vacuum` over any
  `[IsAddTorsionFree V]`, and `FormalVertexAxioms.ncoeff_field_apply_eq_finsum_translation` over
  `[Module ℚ V]`).

## References

* R. E. Borcherds, *Vertex algebras, Kac–Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.2, §4.5, §4.6, §4.8.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 2.2.4 and Theorem 2.3.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.1–§3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti VertexOperator

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### Action of translation-covariant fields on a translation-invariant vector -/

/-- If `T vac = 0` and `[IsAddTorsionFree V]`, any translation-covariant field `G` automatically
has no singular part on `vac`: `(G[[n]]) vac = 0` for all `n ≥ 0`. -/
theorem ncoeff_apply_eq_zero_of_nonneg_of_lie_derivative [IsAddTorsionFree V]
    {T : Module.End R V} {vac : V} (hT : T vac = 0) {G : VertexOperator R V}
    (hG : ∀ m : ℤ, ⁅T, G[[m]]⁆ = (derivative G)[[m]]) {n : ℤ} (hn : 0 ≤ n) :
    (G[[n]]) vac = 0 := by
  obtain ⟨N, hN⟩ := G.exists_forall_ncoeff_apply_eq_zero vac
  have hstep : ∀ d k : ℕ, N - k ≤ d → (G[[(k : ℤ)]]) vac = 0 := by
    intro d
    induction d with
    | zero =>
      intro k hk
      exact hN k (by omega)
    | succ d ih =>
      intro k hk
      rcases le_or_gt N k with hge | hlt
      · exact hN k (by omega)
      · have hnext : (G[[((k + 1 : ℕ) : ℤ)]]) vac = 0 := ih (k + 1) (by omega)
        have hcov := LinearMap.congr_fun (hG ((k + 1 : ℕ) : ℤ)) vac
        rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hnext, hT,
          map_zero, map_zero, sub_self, ncoeff_derivative, LinearMap.smul_apply,
          show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega] at hcov
        exact (IsAddTorsionFree.zsmul_eq_zero_iff_right (by omega)).1 hcov.symm
  lift n to ℕ using hn
  exact hstep (N - n) n le_rfl

/-- If `T vac = 0` and `[IsAddTorsionFree V]`, a translation-covariant field `G` with
`(G[[-1]]) vac = 0` annihilates `vac` in every mode. -/
theorem ncoeff_apply_eq_zero_of_lie_derivative [IsAddTorsionFree V]
    {T : Module.End R V} {vac : V} (hT : T vac = 0) {G : VertexOperator R V}
    (hG : ∀ m : ℤ, ⁅T, G[[m]]⁆ = (derivative G)[[m]]) (h_neg_one : (G[[-1]]) vac = 0) (m : ℤ) :
    (G[[m]]) vac = 0 := by
  rcases le_or_gt 0 m with hm | hm
  · exact ncoeff_apply_eq_zero_of_nonneg_of_lie_derivative hT hG hm
  · have hneg : ∀ k : ℕ, (G[[-(k : ℤ) - 1]]) vac = 0 := by
      intro k
      induction k with
      | zero => simpa using h_neg_one
      | succ k ih =>
        have hcov := LinearMap.congr_fun (hG (-(k : ℤ) - 1)) vac
        rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, ih, hT,
          map_zero, map_zero, sub_self, ncoeff_derivative, LinearMap.smul_apply,
          show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring] at hcov
        exact (IsAddTorsionFree.zsmul_eq_zero_iff_right (by omega)).1 hcov.symm
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
    exact hneg k

/-- Two translation-covariant fields whose `-1`-modes agree on `vac` (where `T vac = 0` and
`[IsAddTorsionFree V]`) agree on `vac` in every mode. -/
theorem ncoeff_apply_eq_of_lie_derivative [IsAddTorsionFree V]
    {T : Module.End R V} {vac : V} (hT : T vac = 0) {G H : VertexOperator R V}
    (hG : ∀ m : ℤ, ⁅T, G[[m]]⁆ = (derivative G)[[m]])
    (hH : ∀ m : ℤ, ⁅T, H[[m]]⁆ = (derivative H)[[m]])
    (h_neg_one : (G[[-1]]) vac = (H[[-1]]) vac) (m : ℤ) :
    (G[[m]]) vac = (H[[m]]) vac := by
  have hsub : ∀ k : ℤ, ⁅T, (G - H)[[k]]⁆ = (derivative (G - H))[[k]] := fun k ↦ by
    rw [map_sub, Pi.sub_apply, Ring.lie_def, mul_sub, sub_mul, sub_sub_sub_comm, ← Ring.lie_def,
      ← Ring.lie_def, hG, hH, map_sub, map_sub, Pi.sub_apply]
  have h0 := ncoeff_apply_eq_zero_of_lie_derivative hT hsub
    (by simp [map_sub, h_neg_one]) m
  rwa [map_sub, Pi.sub_apply, LinearMap.sub_apply, sub_eq_zero] at h0

/-! ### Field-level Borcherds identity -/

section BorcherdsField

private def borcherdsLHS (A B : VertexOperator R V) (m n r : ℤ) (c : V) : V :=
  ∑ᶠ j : ℕ, Ring.choose m j • ((nthProduct (n + j) A B)[[m + r - j]]) c

private def borcherdsRHS₁ (A B : VertexOperator R V) (m n r : ℤ) (c : V) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + i]]) c)

private def borcherdsRHS₂ (A B : VertexOperator R V) (m n r : ℤ) (c : V) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
    (B[[n + r - i]]) ((A[[m + i]]) c)

private theorem borcherds_zero_left (A B : VertexOperator R V) (n r : ℤ) (c : V) :
    borcherdsLHS A B 0 n r c = borcherdsRHS₁ A B 0 n r c - borcherdsRHS₂ A B 0 n r c := by
  have hlhs : borcherdsLHS A B 0 n r c = ((nthProduct n A B)[[r]]) c := by
    rw [borcherdsLHS, finsum_eq_single _ 0]
    · simp
    · intro j hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      simp
  have hrhs₁ : borcherdsRHS₁ A B 0 n r c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[n - i]]) ((B[[r + i]]) c) := by
    simp [borcherdsRHS₁]
  have hrhs₂ : borcherdsRHS₂ A B 0 n r c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
        (B[[n + r - i]]) ((A[[(i : ℤ)]]) c) := by
    simp [borcherdsRHS₂]
  rw [hlhs, hrhs₁, hrhs₂, ncoeff_nthProduct_apply]

private theorem borcherds_of_ge {A B : VertexOperator R V} {N : ℕ}
    (hAB : A.IsLocalOfOrder B N) (m : ℤ) {n : ℤ} (hn : (N : ℤ) ≤ n) (r : ℤ) (c : V) :
    borcherdsLHS A B m n r c = borcherdsRHS₁ A B m n r c - borcherdsRHS₂ A B m n r c := by
  have hn0 : 0 ≤ n := le_trans (Nat.cast_nonneg N) hn
  lift n to ℕ using hn0
  have hlhs : borcherdsLHS A B m (n : ℤ) r c = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_
    rw [show (n : ℤ) + (j : ℤ) = ((n + j : ℕ) : ℤ) by push_cast; rfl,
      hAB.nthProduct_eq_zero (by omega), map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have hloc := LinearMap.congr_fun (isLocalOfOrder_iff.1 (hAB.mono (Nat.cast_le.1 hn)) m r) c
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
    LinearMap.zero_apply] at hloc
  rw [hlhs, borcherdsRHS₁, borcherdsRHS₂,
    ← sum_antidiagonal_commutator_eq_sub_finsum n m r A B c, hloc]

private theorem support_borcherdsLHS_subset {A B : VertexOperator R V} {N : ℕ}
    (hAB : A.IsLocalOfOrder B N) (m n r : ℤ) (c : V) (K : ℕ) (hK : N ≤ n + K) :
    (Function.support fun j : ℕ ↦
      Ring.choose m j • ((nthProduct (n + j) A B)[[m + r - j]]) c) ⊆ range K := by
  intro j hj
  simp only [mem_coe, mem_range]
  by_contra! h
  apply hj
  dsimp only
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n + j = k := ⟨(n + j).toNat, by omega⟩
  rw [hk, hAB.nthProduct_eq_zero (by omega), map_zero, Pi.zero_apply, LinearMap.zero_apply,
    smul_zero]

private theorem borcherdsLHS_add_one {A B : VertexOperator R V} {N : ℕ}
    (hAB : A.IsLocalOfOrder B N) (m n r : ℤ) (c : V) :
    borcherdsLHS A B (m + 1) n r c =
      borcherdsLHS A B m n (r + 1) c + borcherdsLHS A B m (n + 1) r c := by
  let K : ℕ := (N - n).toNat + 1
  rw [borcherdsLHS, borcherdsLHS, borcherdsLHS,
    finsum_eq_sum_of_support_subset _
      (support_borcherdsLHS_subset hAB (m + 1) n r c (K + 1) (by omega)),
    finsum_eq_sum_of_support_subset _
      (support_borcherdsLHS_subset hAB m n (r + 1) c (K + 1) (by omega)),
    finsum_eq_sum_of_support_subset _
      (support_borcherdsLHS_subset hAB m (n + 1) r c K (by omega)),
    sum_range_succ' _ K, sum_range_succ' _ K]
  have hhead : Ring.choose (m + 1) 0 • ((nthProduct (n + (0 : ℕ)) A B)[[m + 1 + r - (0 : ℕ)]]) c =
      Ring.choose m 0 • ((nthProduct (n + (0 : ℕ)) A B)[[m + (r + 1) - (0 : ℕ)]]) c := by
    simp [show m + 1 + r = m + (r + 1) by omega]
  have htail : (∑ j ∈ range K,
      Ring.choose (m + 1) (j + 1) •
        ((nthProduct (n + ((j + 1 : ℕ) : ℤ)) A B)[[m + 1 + r - ((j + 1 : ℕ) : ℤ)]]) c) =
      (∑ j ∈ range K,
        Ring.choose m (j + 1) •
          ((nthProduct (n + ((j + 1 : ℕ) : ℤ)) A B)[[m + (r + 1) - ((j + 1 : ℕ) : ℤ)]]) c) +
      ∑ j ∈ range K,
        Ring.choose m j • ((nthProduct (n + 1 + j) A B)[[m + r - j]]) c := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [Ring.choose_succ_succ, add_smul,
      show n + ((j + 1 : ℕ) : ℤ) = n + 1 + j by push_cast; ring,
      show m + 1 + r - ((j + 1 : ℕ) : ℤ) = m + r - j by push_cast; ring,
      show m + (r + 1) - ((j + 1 : ℕ) : ℤ) = m + r - j by push_cast; ring, add_comm]
  rw [hhead, htail]
  abel

private theorem borcherdsRHS₁_add_one (A B : VertexOperator R V) (m n r : ℤ) (c : V) :
    borcherdsRHS₁ A B (m + 1) n r c =
      borcherdsRHS₁ A B m n (r + 1) c + borcherdsRHS₁ A B m (n + 1) r c := by
  obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero c
  let M : ℕ := P + r.natAbs + 2
  have hsub₁ (m' n' : ℤ) : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n' i) • (A[[m' + n' - i]]) ((B[[r + i]]) c)) ⊆
      range (M + 1) :=
    support_nthProduct_left_subset A B m' n' r c fun i hi ↦ hP _ (by omega)
  have hsub₂ : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + 1 + i]]) c)) ⊆
      range M :=
    support_nthProduct_left_subset A B m n (r + 1) c fun i hi ↦ hP _ (by omega)
  rw [borcherdsRHS₁, borcherdsRHS₁, borcherdsRHS₁,
    finsum_eq_sum_of_support_subset _ (hsub₁ (m + 1) n),
    finsum_eq_sum_of_support_subset _ hsub₂,
    finsum_eq_sum_of_support_subset _ (hsub₁ m (n + 1)),
    sum_range_succ' _ M, sum_range_succ' _ M]
  have hhead : ((-1 : ℤ) ^ 0 * Ring.choose n 0) •
        (A[[m + 1 + n - (0 : ℕ)]]) ((B[[r + (0 : ℕ)]]) c) =
      ((-1 : ℤ) ^ 0 * Ring.choose (n + 1) 0) •
        (A[[m + (n + 1) - (0 : ℕ)]]) ((B[[r + (0 : ℕ)]]) c) := by
    simp [show m + 1 + n = m + (n + 1) by omega]
  have htail : (∑ i ∈ range M,
      ((-1 : ℤ) ^ (i + 1) * Ring.choose n (i + 1)) •
        (A[[m + 1 + n - ((i + 1 : ℕ) : ℤ)]]) ((B[[r + ((i + 1 : ℕ) : ℤ)]]) c)) =
      (∑ i ∈ range M,
        ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + 1 + i]]) c)) +
      ∑ i ∈ range M,
        ((-1 : ℤ) ^ (i + 1) * Ring.choose (n + 1) (i + 1)) •
          (A[[m + (n + 1) - ((i + 1 : ℕ) : ℤ)]]) ((B[[r + ((i + 1 : ℕ) : ℤ)]]) c) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Ring.choose_succ_succ,
      show m + 1 + n - ((i + 1 : ℕ) : ℤ) = m + n - i by push_cast; ring,
      show m + (n + 1) - ((i + 1 : ℕ) : ℤ) = m + n - i by push_cast; ring,
      show r + ((i + 1 : ℕ) : ℤ) = r + 1 + i by push_cast; ring,
      ← add_smul]
    congr 1
    rw [pow_succ]
    ring
  rw [hhead, htail]
  abel

private theorem borcherdsRHS₂_add_one (A B : VertexOperator R V) (m n r : ℤ) (c : V) :
    borcherdsRHS₂ A B (m + 1) n r c =
      borcherdsRHS₂ A B m n (r + 1) c + borcherdsRHS₂ A B m (n + 1) r c := by
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero c
  let M : ℕ := Q + m.natAbs + 2
  have hsub_lhs : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
        (B[[n + r - i]]) ((A[[m + 1 + i]]) c)) ⊆ range M :=
    support_nthProduct_right_subset A B (m + 1) n r c fun i hi ↦ hQ _ (by omega)
  have hsub_rhs (n' r' : ℤ) : (Function.support fun i : ℕ ↦
      ((-1 : ℤ) ^ i * Ring.choose n' i * (n'.negOnePow : ℤ)) •
        (B[[n' + r' - i]]) ((A[[m + i]]) c)) ⊆ range (M + 1) :=
    support_nthProduct_right_subset A B m n' r' c fun i hi ↦ hQ _ (by omega)
  rw [borcherdsRHS₂, borcherdsRHS₂, borcherdsRHS₂,
    finsum_eq_sum_of_support_subset _ hsub_lhs,
    finsum_eq_sum_of_support_subset _ (hsub_rhs n (r + 1)),
    finsum_eq_sum_of_support_subset _ (hsub_rhs (n + 1) r),
    sum_range_succ' _ M, sum_range_succ' _ M]
  have hsign : ((n + 1).negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
    rw [Int.negOnePow_succ, Units.val_neg]
  have hhead : ((-1 : ℤ) ^ 0 * Ring.choose n 0 * (n.negOnePow : ℤ)) •
        (B[[n + (r + 1) - (0 : ℕ)]]) ((A[[m + (0 : ℕ)]]) c) +
      ((-1 : ℤ) ^ 0 * Ring.choose (n + 1) 0 * ((n + 1).negOnePow : ℤ)) •
        (B[[n + 1 + r - (0 : ℕ)]]) ((A[[m + (0 : ℕ)]]) c) = 0 := by
    simp only [pow_zero, Ring.choose_zero_right, one_mul, Nat.cast_zero, sub_zero, add_zero, hsign,
      neg_zsmul, show n + (r + 1) = n + 1 + r by omega, add_neg_cancel]
  have htail : (∑ i ∈ range M,
      ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
        (B[[n + r - i]]) ((A[[m + 1 + i]]) c)) =
      (∑ i ∈ range M,
        ((-1 : ℤ) ^ (i + 1) * Ring.choose n (i + 1) * (n.negOnePow : ℤ)) •
          (B[[n + (r + 1) - ((i + 1 : ℕ) : ℤ)]]) ((A[[m + ((i + 1 : ℕ) : ℤ)]]) c)) +
      ∑ i ∈ range M,
        ((-1 : ℤ) ^ (i + 1) * Ring.choose (n + 1) (i + 1) * ((n + 1).negOnePow : ℤ)) •
          (B[[n + 1 + r - ((i + 1 : ℕ) : ℤ)]]) ((A[[m + ((i + 1 : ℕ) : ℤ)]]) c) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Ring.choose_succ_succ, hsign,
      show n + (r + 1) - ((i + 1 : ℕ) : ℤ) = n + r - i by push_cast; ring,
      show n + 1 + r - ((i + 1 : ℕ) : ℤ) = n + r - i by push_cast; ring,
      show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by push_cast; ring,
      ← add_smul]
    congr 1
    rw [pow_succ]
    ring
  calc ∑ i ∈ range M,
        ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
          (B[[n + r - i]]) ((A[[m + 1 + i]]) c)
      = (∑ i ∈ range M,
          ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
            (B[[n + r - i]]) ((A[[m + 1 + i]]) c)) + 0 := (add_zero _).symm
    _ = _ := by rw [← hhead, htail]; abel

end BorcherdsField

/-- **The Borcherds identity for mutually local fields.** Over any commutative ring `R`, if
`A.IsLocalOfOrder B N`, then for all `m, n, r : ℤ` and `c : V`,
`∑ᶠ j : ℕ, (m choose j) • ((A₍ₙ₊ⱼ₎ B)₍ₘ₊ᵣ₋ⱼ₎) c =
  (∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • A₍ₘ₊ₙ₋ᵢ₎ (B₍ᵣ₊ᵢ₎ c)) -
    ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (-1)ⁿ • B₍ₙ₊ᵣ₋ᵢ₎ (A₍ₘ₊ᵢ₎ c)`. -/
theorem IsLocalOfOrder.borcherds {A B : VertexOperator R V} {N : ℕ}
    (hAB : A.IsLocalOfOrder B N) (m n r : ℤ) (c : V) :
    ∑ᶠ j : ℕ, Ring.choose m j • ((nthProduct (n + j) A B)[[m + r - j]]) c =
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) • (A[[m + n - i]]) ((B[[r + i]]) c)) -
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
          (B[[n + r - i]]) ((A[[m + i]]) c) := by
  let Δ : ℤ → ℤ → ℤ → V := fun m' n' r' ↦
    borcherdsLHS A B m' n' r' c - (borcherdsRHS₁ A B m' n' r' c - borcherdsRHS₂ A B m' n' r' c)
  have h0 : ∀ n' r' : ℤ, Δ 0 n' r' = 0 := fun n' r' ↦
    sub_eq_zero.2 (borcherds_zero_left A B n' r' c)
  have hge : ∀ m' n' r' : ℤ, (N : ℤ) ≤ n' → Δ m' n' r' = 0 := fun m' n' r' hn' ↦
    sub_eq_zero.2 (borcherds_of_ge hAB m' hn' r' c)
  have hstep : ∀ m' n' r' : ℤ, Δ (m' + 1) n' r' = Δ m' n' (r' + 1) + Δ m' (n' + 1) r' := by
    intro m' n' r'
    simp only [Δ, borcherdsLHS_add_one hAB, borcherdsRHS₁_add_one, borcherdsRHS₂_add_one]
    abel
  have hpos : ∀ (k : ℕ) (n' r' : ℤ), Δ k n' r' = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro n' r'
      rw [Nat.cast_add, Nat.cast_one, hstep, ih, ih, add_zero]
  have hneg : ∀ (k d : ℕ) (n' r' : ℤ), (N - n').toNat ≤ d → Δ (-(k : ℤ)) n' r' = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ n' r' _
      simpa using h0 n' r'
    | succ k ihk =>
      intro d
      induction d with
      | zero =>
        intro n' r' hd
        exact hge _ n' r' (by omega)
      | succ d ihd =>
        intro n' r' hd
        rcases le_or_gt (N : ℤ) n' with hge' | _
        · exact hge _ n' r' hge'
        · have h₁ : Δ (-(k : ℤ)) n' (r' - 1) = 0 := ihk (N - n').toNat n' (r' - 1) le_rfl
          have h₂ : Δ (-((k + 1 : ℕ) : ℤ)) (n' + 1) (r' - 1) = 0 :=
            ihd (n' + 1) (r' - 1) (by omega)
          have hs := hstep (-((k + 1 : ℕ) : ℤ)) n' (r' - 1)
          rw [show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by push_cast; ring,
            show r' - 1 + 1 = r' by omega, h₁, h₂, add_zero] at hs
          exact hs.symm
  have hall : Δ m n r = 0 := by
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm
      exact hpos m n r
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
      exact hneg k (N - n).toNat n r le_rfl
  exact sub_eq_zero.1 hall

end VertexOperator

namespace TauCeti.FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The field attached to the vacuum vector is `VertexOperator.identity`. -/
@[simp]
theorem field_vacuum (A : FormalVertexAxioms R V) :
    A.field A.vacuum = VertexOperator.identity := by
  refine ext_ncoeff fun n ↦ ?_
  rw [A.ncoeff_field_vacuum, ncoeff_identity]

section TorsionFree

variable [IsAddTorsionFree V] (A : FormalVertexAxioms R V)

/-- **State–field correspondence for all `n`-th products.** For any `a, b : V` and `n : ℤ`,
`Y(a₍ₙ₎ b, z) = nthProduct n (Y(a, z)) (Y(b, z))`. -/
theorem field_ncoeff_apply (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = VertexOperator.nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_ncoeff_apply_vacuum_eq (fun c ↦ ?_) (fun m ↦ ?_)
  · obtain ⟨r₁, hr₁⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨r₂, hr₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨r₃, hr₃⟩ := A.exists_isLocalOfOrder b c
    exact ⟨_, hr₁.nthProduct_left hr₂ hr₃ n⟩
  · refine ncoeff_apply_eq_of_lie_derivative A.translation_vacuum
      (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n)
      (A.lie_translation_ncoeff _) ?_ m
    rw [ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
      (A.ncoeff_field_apply_vacuum_of_nonneg b) n,
      A.ncoeff_neg_one_field_apply_vacuum, A.ncoeff_neg_one_field_apply_vacuum]

/-- For `n : ℕ`, `Y(a₍ₙ₎ b, z)` is the `n`-th nonnegative residue product of `Y(a, z)` and
`Y(b, z)`. -/
theorem field_ncoeff_natCast_apply (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) =
      VertexOperator.nonnegResidueProduct n (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- For `n = -1`, `Y(a₍₋₁₎ b, z)` is the normal-ordered product `:Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply (a b : V) :
    A.field (((A.field a)[[-1]]) b) = VertexOperator.normalOrder (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_one]

/-- For `k : ℕ`, `Y(a₍₋ₖ₋₁₎ b, z)` is `:(∂_z^{(k)} Y(a, z)) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      VertexOperator.normalOrder (VertexOperator.hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_succ]

/-- Divided-power translation covariance: `Y(a₍₋ₖ₋₁₎ |0⟩, z) = ∂_z^{(k)} Y(a, z)`. -/
theorem field_ncoeff_apply_vacuum_neg_succ (a : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) A.vacuum) =
      VertexOperator.hasseDeriv k (A.field a) := by
  rw [A.field_ncoeff_neg_succ_apply, A.field_vacuum, normalOrder_identity_right]

/-- **The Borcherds identity** in a formal vertex algebra (`[IsAddTorsionFree V]`):
for all `a, b, c : V` and `m, n, r : ℤ`,
`∑ᶠ j : ℕ, (m choose j) • ((a₍ₙ₊ⱼ₎ b)₍ₘ₊ᵣ₋ⱼ₎) c =
  (∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c)) -
    ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (-1)ⁿ • b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c)`. -/
theorem borcherds (a b c : V) (m n r : ℤ) :
    ∑ᶠ j : ℕ, Ring.choose m j •
        ((A.field (((A.field a)[[n + j]]) b))[[m + r - j]]) c =
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
          ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c)) -
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
          ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c) := by
  obtain ⟨N, hN⟩ := A.exists_isLocalOfOrder a b
  have hlhs : (fun j : ℕ ↦ Ring.choose m j •
      ((A.field (((A.field a)[[n + j]]) b))[[m + r - j]]) c) =
      fun j : ℕ ↦ Ring.choose m j • ((nthProduct (n + j) (A.field a) (A.field b))[[m + r - j]]) c :=
    funext fun j ↦ by rw [A.field_ncoeff_apply]
  rw [hlhs, hN.borcherds]

/-- **Borcherds commutator formula** (`n = 0` specialization of the Borcherds identity), evaluated
on a state `c : V`. -/
theorem lie_ncoeff_field_apply (a b c : V) (m r : ℤ) :
    (⁅(A.field a)[[m]], (A.field b)[[r]]⁆) c =
      ∑ᶠ j : ℕ, Ring.choose m j •
        ((A.field (((A.field a)[[(j : ℤ)]]) b))[[m + r - j]]) c := by
  have hb := A.borcherds a b c m 0 r
  have hr₁ : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose 0 i) •
      ((A.field a)[[m + 0 - i]]) (((A.field b)[[r + i]]) c)) =
      ((A.field a)[[m]]) (((A.field b)[[r]]) c) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro i hi
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      simp
  have hr₂ : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose 0 i * ((0 : ℤ).negOnePow : ℤ)) •
      ((A.field b)[[0 + r - i]]) (((A.field a)[[m + i]]) c)) =
      ((A.field b)[[r]]) (((A.field a)[[m]]) c) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro i hi
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      simp
  rw [hr₁, hr₂] at hb
  simp only [zero_add] at hb
  simpa [Ring.lie_def, mul_apply_eq_comp] using hb.symm

/-- **Operator-level Borcherds commutator formula** for fields local of order `N`:
`⁅a₍ₘ₎, b₍ᵣ₎⁆ = ∑ j ∈ range N, (m choose j) • (a₍ⱼ₎ b)₍ₘ₊ᵣ₋ⱼ₎`. -/
theorem lie_ncoeff_field_of_isLocalOfOrder {a b : V} {N : ℕ}
    (hAB : (A.field a).IsLocalOfOrder (A.field b) N) (m r : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[r]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (A.field (((A.field a)[[(j : ℤ)]]) b))[[m + r - j]] := by
  ext c
  rw [A.lie_ncoeff_field_apply, LinearMap.sum_apply]
  have hsub : (Function.support fun j : ℕ ↦
      Ring.choose m j • ((A.field (((A.field a)[[(j : ℤ)]]) b))[[m + r - j]]) c) ⊆ range N := by
    intro j hj
    simp only [mem_coe, mem_range]
    by_contra! h
    apply hj
    dsimp only
    rw [A.field_ncoeff_apply, hAB.nthProduct_eq_zero (Nat.cast_le.2 h), map_zero, Pi.zero_apply,
      LinearMap.zero_apply, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  simp only [LinearMap.smul_apply]

/-- Zero-mode derivation property: `⁅a₍₀₎, b₍ᵣ₎⁆ = (a₍₀₎ b)₍ᵣ₎`. -/
@[simp]
theorem lie_ncoeff_zero_field (a b : V) (r : ℤ) :
    ⁅(A.field a)[[0]], (A.field b)[[r]]⁆ = (A.field (((A.field a)[[0]]) b))[[r]] := by
  obtain ⟨N, hN⟩ := A.exists_isLocalOfOrder a b
  rw [A.lie_ncoeff_field_of_isLocalOfOrder (hN.mono (Nat.le_add_right N 1)), sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp
  · simp

/-- **Borcherds iterate (associativity) formula** (`m = 0` specialization of the Borcherds
identity): for all `a, b, c : V` and `n, r : ℤ`,
`((a₍ₙ₎ b)₍ᵣ₎) c = (∑ᶠ i : ℕ, (-1)ⁱ (n choose i) • a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c)) -
  ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (-1)ⁿ • b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c)`. -/
theorem ncoeff_field_ncoeff_apply (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
          ((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c)) -
        ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
          ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct_apply]

/-- **Division-free skew-symmetry** in a formal vertex algebra (`[IsAddTorsionFree V]`):
`a₍ₙ₎ b = ∑ᶠ j : ℕ, -((-1)ʲ (-1)ⁿ) • (b₍ₙ₊ⱼ₎ a)₍₋ⱼ₋₁₎ |0⟩`. -/
theorem ncoeff_field_apply_eq_finsum_vacuum (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ j : ℕ, (-((-1 : ℤ) ^ j * (n.negOnePow : ℤ))) •
        ((A.field (((A.field b)[[n + j]]) a))[[-j - 1]]) A.vacuum := by
  have hb := A.borcherds b a A.vacuum (-1) n 0
  have hr₁ : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
      ((A.field b)[[-1 + n - i]]) (((A.field a)[[0 + i]]) A.vacuum)) = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun i ↦ by
      rw [A.ncoeff_field_apply_vacuum_of_nonneg a _ (by omega), map_zero, smul_zero]
  have hr₂ : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i * (n.negOnePow : ℤ)) •
      ((A.field a)[[n + 0 - i]]) (((A.field b)[[-1 + i]]) A.vacuum)) =
      (n.negOnePow : ℤ) • ((A.field a)[[n]]) b := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro i hi
      rw [A.ncoeff_field_apply_vacuum_of_nonneg b _ (by omega), map_zero, smul_zero]
  rw [hr₁, hr₂, zero_sub] at hb
  obtain ⟨M, hM⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  have hfin : (Function.support fun j : ℕ ↦
      Ring.choose (-1) j •
        ((A.field (((A.field b)[[n + j]]) a))[[-1 + 0 - j]]) A.vacuum).Finite := by
    refine (finite_toSet (range (M + n.natAbs))).subset fun j hj ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    apply hj
    dsimp only
    rw [hM _ (by omega), map_zero, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have hmul := congrArg (fun v : V ↦ (-(n.negOnePow : ℤ)) • v) hb.symm
  have hunit : (-(n.negOnePow : ℤ)) * -(n.negOnePow : ℤ) = 1 := by
    rw [neg_mul_neg, ← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hmap : (-(n.negOnePow : ℤ)) • (∑ᶠ j : ℕ, Ring.choose (-1) j •
        ((A.field (((A.field b)[[n + j]]) a))[[-1 + 0 - j]]) A.vacuum) =
      ∑ᶠ j : ℕ, (-(n.negOnePow : ℤ)) • (Ring.choose (-1) j •
        ((A.field (((A.field b)[[n + j]]) a))[[-1 + 0 - j]]) A.vacuum) :=
    (DistribSMul.toAddMonoidHom V (-(n.negOnePow : ℤ))).map_finsum hfin
  rw [← neg_zsmul, smul_smul, hunit, one_smul, hmap] at hmul
  rw [hmul]
  refine finsum_congr fun j ↦ ?_
  have hchoose : Ring.choose (-1 : ℤ) j = (-1 : ℤ) ^ j := by
    rw [Ring.choose_neg, show (1 : ℤ) + j - 1 = (j : ℤ) by omega, Ring.choose_natCast,
      Nat.choose_self, Nat.cast_one, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
      mul_one]
  rw [hchoose, show (-1 : ℤ) + 0 - j = -(j : ℤ) - 1 by omega, smul_smul]
  congr 1
  ring

end TorsionFree

/-- **Skew-symmetry** in a formal vertex algebra over a `ℚ`-module:
`a₍ₙ₎ b = ∑ᶠ j : ℕ, (-((-1)ʲ (-1)ⁿ) / j!) • Tʲ (b₍ₙ₊ⱼ₎ a)`. -/
theorem ncoeff_field_apply_eq_finsum_translation [Module ℚ V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ j : ℕ, ((-(((-1 : ℚ) ^ j) * (n.negOnePow : ℤ))) / j.factorial) •
        (A.translation ^ j) (((A.field b)[[n + j]]) a) := by
  have : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
  rw [A.ncoeff_field_apply_eq_finsum_vacuum a b n]
  refine finsum_congr fun j ↦ ?_
  rw [A.ncoeff_field_apply_vacuum_neg _ j, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, div_eq_mul_inv]
  congr 1
  push_cast
  ring

end TauCeti.FormalVertexAxioms
