/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.NthProduct
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.RingTheory.Binomial
import Mathlib.Tactic.Abel

/-!
# The Borcherds identity, state–field `n`-th products, and skew-symmetry

Over any commutative ring `R`, mutually local fields satisfy the field-level Borcherds identity.
For `A : TauCeti.FormalVertexAxioms R V` under `HasUniqueDiv V`, the state–field map intertwines
all integer `n`-th products, yielding the state-level commutator, iterate, Borcherds, and
skew-symmetry identities (both division-free and in `(i!)⁻¹ Tⁱ` form over any `ℚ`-algebra).

## Main results

* `VertexOperator.IsLocalOfOrder.borcherds_finsum`, `borcherds`: field-level Borcherds identity.
* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: `Y(a₍ₙ₎ b, z) = Y(a, z)_{(n)} Y(b, z)`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field`, `lie_ncoeff_field_finsum`: mode commutator formula.
* `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply`: mode iterate formula (`m = 0` case).
* `TauCeti.FormalVertexAxioms.borcherds_finsum`, `borcherds`: full Borcherds identity.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry_vacuum`,
  `ncoeff_field_apply_skewSymmetry`: division-free and `ℚ`-algebra skew-symmetry of vertex modes.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.2, §4.5, §4.6 and §4.8.
* R. E. Borcherds, *Vertex algebras, Kac–Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.2–3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

/-! ### Field-level Borcherds identity over a commutative ring -/

namespace VertexOperator

section BorcherdsField

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private def borcherdsLHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v

private def borcherdsRHS (A B : VertexOperator R V) (v : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    ((A[[m + n - i]]) ((B[[r + i]]) v) -
      (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v))

private theorem borcherdsLHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hM : ∀ i : ℕ, M ≤ i → nthProduct (n + i) A B = 0) :
    borcherdsLHS A B v m n r =
      ∑ i ∈ range M, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v :=
  TauCeti.finsum_eq_sum_range_of_zero fun i hi ↦ by simp [hM i hi]

private theorem borcherdsRHS_eq_sum {A B : VertexOperator R V} {v : V} {m n r : ℤ} {M : ℕ}
    (hB : ∀ i : ℕ, M ≤ i → (B[[r + i]]) v = 0) (hA : ∀ i : ℕ, M ≤ i → (A[[m + i]]) v = 0) :
    borcherdsRHS A B v m n r =
      ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[m + n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) :=
  TauCeti.finsum_eq_sum_range_of_zero fun i hi ↦ by simp [hB i hi, hA i hi]

private theorem borcherdsLHS_add_one {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    borcherdsLHS A B v (m + 1) n r =
      borcherdsLHS A B v m n (r + 1) + borcherdsLHS A B v m (n + 1) r := by
  let M := ((N : ℤ) - n).toNat
  have hcut (q : ℤ) (hq : n ≤ q) (K : ℕ) (hK : M ≤ K) :
      ∀ i : ℕ, K ≤ i → nthProduct (q + i) A B = 0 := fun i hi ↦ by
    rw [nthProduct_of_nonneg (by omega)]; exact h.nonnegResidueProduct_eq_zero (by omega)
  rw [borcherdsLHS_eq_sum (M := M + 1) (hcut n le_rfl (M + 1) (by omega)),
    borcherdsLHS_eq_sum (M := M + 1) (hcut n le_rfl (M + 1) (by omega)),
    borcherdsLHS_eq_sum (M := M) (hcut (n + 1) (by omega) M le_rfl),
    TauCeti.Ring.sum_range_choose_add_one_smul (R := ℤ) M m
      (fun i ↦ ((nthProduct (n + i) A B)[[m + 1 + r - i]]) v)]
  congr 1
  · exact sum_congr rfl fun i _ ↦ by rw [show m + 1 + r - (i : ℤ) = m + (r + 1) - i by omega]
  · exact sum_congr rfl fun i _ ↦ by
      rw [show n + ((i + 1 : ℕ) : ℤ) = n + 1 + i by omega,
        show m + 1 + r - ((i + 1 : ℕ) : ℤ) = m + r - i by omega]

private theorem borcherdsRHS_add_one (A B : VertexOperator R V) (v : V) (m n r : ℤ) :
    borcherdsRHS A B v (m + 1) n r =
      borcherdsRHS A B v m n (r + 1) + borcherdsRHS A B v m (n + 1) r := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M := max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat
  rw [borcherdsRHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega)),
    borcherdsRHS_eq_sum (M := M) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega)),
    borcherdsRHS_eq_sum (M := M + 1) (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  simp only [smul_sub, sum_sub_distrib]; rw [← add_sub_add_comm]; congr 1
  · rw [TauCeti.Ring.sum_range_neg_one_pow_mul_choose_smul (R := ℤ) M n
      (fun i ↦ (A[[m + 1 + n - i]]) ((B[[r + i]]) v))]
    congr 1
    · exact sum_congr rfl fun i _ ↦ by
        rw [show m + 1 + n - ((i + 1 : ℕ) : ℤ) = m + n - i by omega,
          show r + ((i + 1 : ℕ) : ℤ) = r + 1 + i by omega]
    · exact sum_congr rfl fun i _ ↦ by rw [show m + 1 + n - (i : ℤ) = m + (n + 1) - i by omega]
  · have h₂ := eq_sub_of_add_eq (TauCeti.Ring.sum_range_neg_one_pow_mul_choose_smul (R := ℤ) M n
      (fun i ↦ (n.negOnePow : ℤ) • (B[[n + (r + 1) - i]]) ((A[[m + i]]) v))).symm
    rw [sum_range_succ _ M, hN₃ (m + M) (by omega), map_zero, smul_zero, smul_zero, add_zero] at h₂
    rw [sum_range_succ _ M, hN₃ (m + 1 + M) (by omega), map_zero, smul_zero, smul_zero, add_zero,
      sum_congr rfl fun i _ ↦ show _ = ((-1 : ℤ) ^ i * Ring.choose n i) • (n.negOnePow : ℤ) •
          (B[[n + (r + 1) - ((i + 1 : ℕ) : ℤ)]]) ((A[[m + ((i + 1 : ℕ) : ℤ)]]) v) by
        rw [show n + (r + 1) - ((i + 1 : ℕ) : ℤ) = n + r - i by omega,
          show m + ((i + 1 : ℕ) : ℤ) = m + 1 + i by omega],
      h₂, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1; exact sum_congr rfl fun i _ ↦ by
      simp only [Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg,
        show n + 1 + r - (i : ℤ) = n + (r + 1) - i by omega]

private theorem borcherds_eq_of_zero {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) {v : V}
    (h0n : ∀ q s : ℤ, borcherdsLHS A B v 0 q s = borcherdsRHS A B v 0 q s)
    (hm0 : ∀ p s : ℤ, borcherdsLHS A B v p 0 s = borcherdsRHS A B v p 0 s)
    (m n r : ℤ) : borcherdsLHS A B v m n r = borcherdsRHS A B v m n r := by
  let D (p q s : ℤ) := borcherdsLHS A B v p q s - borcherdsRHS A B v p q s
  have hrec (p q s : ℤ) : D (p + 1) q s = D p q (s + 1) + D p (q + 1) s := by
    simp only [D, borcherdsLHS_add_one h, borcherdsRHS_add_one]; abel
  have hm0' (k : ℕ) : ∀ q s : ℤ, D k q s = 0 := by
    induction k with
    | zero => exact fun q s ↦ sub_eq_zero.mpr (h0n q s)
    | succ k ih => exact fun q s ↦ by rw [Nat.cast_succ, hrec, ih, ih, add_zero]
  have hn0' (l : ℕ) : ∀ p s : ℤ, D p l s = 0 := by
    induction l with
    | zero => exact fun p s ↦ sub_eq_zero.mpr (hm0 p s)
    | succ l ih =>
      intro p s
      have h' := hrec p l s; rw [ih (p + 1) s, ih p (s + 1), zero_add, eq_comm] at h'
      simpa [Nat.cast_succ] using h'
  have hneg (k : ℕ) : ∀ (l : ℕ) (s : ℤ), D (-(k : ℤ)) (-(l : ℤ)) s = 0 := by
    induction k with
    | zero => exact fun l s ↦ by simpa [D] using sub_eq_zero.mpr (h0n _ s)
    | succ k ihk =>
      intro l; induction l with
      | zero => exact fun s ↦ by simpa [D] using sub_eq_zero.mpr (hm0 _ s)
      | succ l ihl =>
        intro s
        have h' := hrec (-((k + 1 : ℕ) : ℤ)) (-((l + 1 : ℕ) : ℤ)) (s - 1)
        rw [show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by omega,
          show -((l + 1 : ℕ) : ℤ) + 1 = -(l : ℤ) by omega, sub_add_cancel,
          ihk (l + 1) (s - 1), ihl (s - 1), add_zero] at h'; exact h'.symm
  suffices hD : D m n r = 0 from sub_eq_zero.mp hD
  rcases le_or_gt 0 m with hm | hm; · lift m to ℕ using hm; exact hm0' m n r
  rcases le_or_gt 0 n with hn | hn; · lift n to ℕ using hn; exact hn0' n m r
  simpa only [show -((-m).toNat : ℤ) = m by omega, show -((-n).toNat : ℤ) = n by omega] using
    hneg (-m).toNat (-n).toNat r

/-- **Field-level Borcherds identity** in `finsum` form, over any commutative ring: for mutually
local fields `A, B` (local of order `N`), any `v : V`, and all integers `m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) ((A_{(n+i)} B)_{(m+r-i)}) v =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (A₍ₘ₊ₙ₋ᵢ₎ (B₍ᵣ₊ᵢ₎ v) - (-1)ⁿ B₍ₙ₊ᵣ₋ᵢ₎ (A₍ₘ₊ᵢ₎ v))`. -/
theorem IsLocalOfOrder.borcherds_finsum {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A[[m + n - i]]) ((B[[r + i]]) v) -
          (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  refine borcherds_eq_of_zero h (fun q s ↦ ?_) (fun p s ↦ ?_) m n r
  · rw [borcherdsLHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    simpa [borcherdsRHS] using ncoeff_nthProduct_apply A B q s v
  · rw [borcherdsRHS, finsum_eq_single _ 0 (fun i hi ↦ by
      simp [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)])]
    have hL : borcherdsLHS A B v p 0 s = (⁅A[[p]], B[[s]]⁆) v := by
      rw [h.lie_ncoeff p s, LinearMap.sum_apply,
        borcherdsLHS_eq_sum (M := N) fun i hi ↦ by simpa using h.nonnegResidueProduct_eq_zero hi]
      exact sum_congr rfl fun i _ ↦ by
        simp only [zero_add, nthProduct_natCast, LinearMap.smul_apply]
    simpa [Ring.lie_def, mul_apply_eq_comp] using hL

/-- **Field-level Borcherds identity** with explicit finite cutoff `M`, over any commutative ring:
all three mode expressions vanish for `i ≥ M`, and the finite sums over `Finset.range M` agree. -/
theorem IsLocalOfOrder.borcherds {A B : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder B N) (v : V) (m n r : ℤ) :
    ∃ M : ℕ,
      (∀ i : ℕ, M ≤ i → ((nthProduct (n + i) A B)[[m + r - i]]) v = 0) ∧
      (∀ i : ℕ, M ≤ i →
        (A[[m + n - i]]) ((B[[r + i]]) v) = 0 ∧ (B[[n + r - i]]) ((A[[m + i]]) v) = 0) ∧
      (∑ i ∈ range M, Ring.choose m i • ((nthProduct (n + i) A B)[[m + r - i]]) v) =
        ∑ i ∈ range M, ((-1 : ℤ) ^ i * Ring.choose n i) •
          ((A[[m + n - i]]) ((B[[r + i]]) v) -
            (n.negOnePow : ℤ) • (B[[n + r - i]]) ((A[[m + i]]) v)) := by
  obtain ⟨N₂, hN₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨N₃, hN₃⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M := max ((N : ℤ) - n).toNat (max ((N₂ : ℤ) - r).toNat ((N₃ : ℤ) - m).toNat)
  have hcut (i : ℕ) (hi : M ≤ i) : nthProduct (n + i) A B = 0 := by
    rw [nthProduct_of_nonneg (by omega)]; exact h.nonnegResidueProduct_eq_zero (by omega)
  refine ⟨M, fun i hi ↦ by simp [hcut i hi],
    fun i hi ↦ ⟨by simp [hN₂ (r + i) (by omega)], by simp [hN₃ (m + i) (by omega)]⟩, ?_⟩
  rw [← borcherdsLHS_eq_sum hcut,
    ← borcherdsRHS_eq_sum (fun _ _ ↦ hN₂ _ (by omega)) (fun _ _ ↦ hN₃ _ (by omega))]
  exact h.borcherds_finsum v m n r

end BorcherdsField

end VertexOperator

/-! ### State–field `n`-th products, Borcherds identity, and skew-symmetry -/

namespace TauCeti.FormalVertexAxioms

open VertexOperator

section UniqueDiv

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [HasUniqueDiv V]
variable (A : FormalVertexAxioms R V)

/-- **State–field `n`-th product identity.** On a module with unique division by positive integers,
the field of `a₍ₙ₎ b` is the `n`-th field product `Y(a, z)_{(n)} Y(b, z)` for every integer `n`. -/
theorem field_ncoeff_apply (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_lie_translation_ncoeff (fun c ↦ ?_)
    (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n) ?_
  · obtain ⟨_, h₁⟩ := A.exists_isLocalOfOrder a b; obtain ⟨_, h₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨_, h₃⟩ := A.exists_isLocalOfOrder b c; exact ⟨_, h₁.nthProduct_left h₃ h₂ n⟩
  · rw [ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
      (A.ncoeff_field_apply_vacuum_of_nonneg b) n, A.ncoeff_neg_one_field_apply_vacuum]

/-- For `k : ℕ`, `Y(a₍ₖ₎ b, z)` is the `k`-th nonnegative residue product of `Y(a, z)` and
`Y(b, z)`. -/
theorem field_ncoeff_natCast_apply (a b : V) (k : ℕ) :
    A.field (((A.field a)[[(k : ℤ)]]) b) = nonnegResidueProduct k (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- `Y(a₍₋₁₎ b, z)` is the normal-ordered product `:Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_one]

/-- For `k : ℕ`, `Y(a₍₋ₖ₋₁₎ b, z)` is `:(∂_z^{(k)} Y(a, z)) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_succ]

/-- **Borcherds commutator formula** for fields local of order `N`:
`[a₍ₘ₎, b₍ₙ₎] = ∑_{i < N} (m choose i) (a₍ᵢ₎ b)₍ₘ₊ₙ₋ᵢ₎`. -/
theorem lie_ncoeff_field {a b : V} {N : ℕ}
    (h : (A.field a).IsLocalOfOrder (A.field b) N) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ i ∈ range N, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  rw [h.lie_ncoeff]; exact sum_congr rfl fun i _ ↦ by rw [A.field_ncoeff_natCast_apply]

/-- **Borcherds commutator formula** in `finsum` form, independent of a chosen locality bound. -/
theorem lie_ncoeff_field_finsum (a b : V) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ᶠ i : ℕ, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  obtain ⟨N, h⟩ := A.exists_isLocalOfOrder a b; rw [A.lie_ncoeff_field h m n, eq_comm]
  exact TauCeti.finsum_eq_sum_range_of_zero fun i hi ↦ by
    simp [A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder h hi]

/-- **Mode iterate / associativity formula** (`m = 0` case of the Borcherds identity):
`((a₍ₙ₎ b)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c))`
for all `a, b, c : V` and all integers `n, r : ℤ`. -/
theorem ncoeff_field_ncoeff_apply (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct_apply]

/-- **The Borcherds identity** in `finsum` form: for all states `a, b, c : V` and `m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) (a₍ₙ₊ᵢ₎ b)₍ₘ₊ᵣ₋ᵢ₎ c =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c))`. -/
theorem borcherds_finsum (a b c : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) :=
  let ⟨_, h⟩ := A.exists_isLocalOfOrder a b
  by simpa only [A.field_ncoeff_apply] using h.borcherds_finsum c m n r

/-- **The Borcherds identity** with explicit finite cutoff `N`: all three mode expressions vanish
for `i ≥ N`, and the finite sums over `Finset.range N` agree. -/
theorem borcherds (a b c : V) (m n r : ℤ) :
    ∃ N : ℕ,
      (∀ i : ℕ, N ≤ i → ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c = 0) ∧
      (∀ i : ℕ, N ≤ i →
        ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) = 0 ∧
        ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c) = 0) ∧
      (∑ i ∈ range N, Ring.choose m i •
          ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
        ∑ i ∈ range N, ((-1 : ℤ) ^ i * Ring.choose n i) •
          (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
            (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) :=
  let ⟨_, h⟩ := A.exists_isLocalOfOrder a b
  by simpa only [A.field_ncoeff_apply] using h.borcherds c m n r

/-- **Division-free skew-symmetry of formal vertex algebra modes**: on any module with unique
division by positive integers,
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (b₍ₙ₊ᵢ₎ a)₍₋ᵢ₋₁₎ |0⟩` for all `a, b : V` and `n : ℤ`. -/
theorem ncoeff_field_apply_skewSymmetry_vacuum (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        ((A.field (((A.field b)[[n + i]]) a))[[-(i : ℤ) - 1]]) A.vacuum := by
  have hbor := A.borcherds_finsum b a A.vacuum (-1) n 0
  obtain ⟨N₀, hN₀⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let M := ((N₀ : ℤ) - n).toNat
  rw [TauCeti.finsum_eq_sum_range_of_zero (N := M) (fun i hi ↦ by simp [hN₀ (n + i) (by omega)]),
    finsum_eq_single _ 0 (fun i hi ↦ by
      simp [A.ncoeff_field_apply_vacuum_of_nonneg b (-1 + i) (by omega)])] at hbor
  simp only [Nat.cast_zero, pow_zero, Ring.choose_zero_right, mul_one, one_smul, add_zero,
    sub_zero, A.ncoeff_field_apply_vacuum_of_nonneg a 0 le_rfl, map_zero, zero_sub,
    A.ncoeff_neg_one_field_apply_vacuum] at hbor
  rw [TauCeti.finsum_eq_sum_range_of_zero (N := M) (fun i _ ↦ by simp [hN₀ (n + i) (by omega)])]
  have hmul := congrArg ((-(n.negOnePow : ℤ)) • ·) hbor.symm
  rw [smul_neg, ← neg_smul, neg_neg, smul_smul, Int.units_coe_mul_self n.negOnePow, one_smul,
    smul_sum] at hmul
  rw [hmul]; exact sum_congr rfl fun i _ ↦ by
    rw [TauCeti.Ring.choose_neg_one (R := ℤ) i, show -1 - (i : ℤ) = -(i : ℤ) - 1 by omega,
      smul_smul, Int.negOnePow_add, Units.val_mul, Int.coe_negOnePow_natCast, neg_mul]

end UniqueDiv

section RatAlgebra

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- **Skew-symmetry of formal vertex algebra modes** over a `ℚ`-algebra `R`:
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)` for all `a, b : V` and `n : ℤ`. -/
theorem ncoeff_field_apply_skewSymmetry (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        (algebraMap ℚ R (i.factorial : ℚ)⁻¹ • (A.translation ^ i) (((A.field b)[[n + i]]) a)) := by
  let : Module ℚ V := Module.compHom V (algebraMap ℚ R)
  have : HasUniqueDiv V := .of_module_rat V
  rw [A.ncoeff_field_apply_skewSymmetry_vacuum a b n]
  exact finsum_congr fun i ↦ by rw [A.ncoeff_field_neg_succ_apply_vacuum]

end RatAlgebra

end TauCeti.FormalVertexAxioms
