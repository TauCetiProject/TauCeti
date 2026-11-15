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
# State–field duality, skew-symmetry, and the Borcherds identity

In a formal vertex algebra `A : TauCeti.FormalVertexAxioms R V` whose underlying additive group `V`
is torsion-free (`[IsAddTorsionFree V]`), Dong's lemma and Goddard's uniqueness theorem identify the
field of every `n`-th product `a₍ₙ₎ b` with the field-level `n`-th product `Y(a, z)₍ₙ₎ Y(b, z)`
(`VertexOperator.nthProduct n`). From this state–field duality and the formal delta expansion of
local commutators we deduce:

* the **mode commutator formula**
  `[a₍ₘ₎, b₍ₙ₎] = ∑_{j = 0}^{N - 1} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`, and in particular the derivation
  property `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`;
* the **Borcherds identity** (also called the Jacobi identity for vertex algebras) for all
  `a, b, c : V` and `m, n, r : ℤ`:
  `∑ᵢ (m choose i) (a₍ₙ₊ᵢ₎ b)₍ₘ₊ᵣ₋ᵢ₎ c =`
  `∑ᵢ (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c))`;
* the **iterate (associativity) formula** (`m = 0` of Borcherds), expressing `(a₍ₙ₎ b)₍ᵣ₎ c` in
  terms of modes of `a` and `b`;
* **skew-symmetry**, expressing `a₍ₙ₎ b` as
  `∑ᵢ (-1)^{n + i + 1} (b₍ₙ₊ᵢ₎ a)₍₋ᵢ₋₁₎ |0⟩`, and over a `ℚ`-module as
  `∑ᵢ (-1)^{n + i + 1} (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)`.

The hypothesis `[IsAddTorsionFree V]` is satisfied automatically whenever `V` is a `ℚ`-module (via
`HasUniqueDiv.of_module_rat V`), and cannot be omitted: over `𝔽₂`, a nonzero square-zero formal
`z²`-perturbation of a commutative algebra satisfies `TauCeti.FormalVertexAxioms` while violating
state–field `n`-th product duality, skew-symmetry, and the Borcherds identity.

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: `Y(a₍ₙ₎ b, z) = nthProduct n Y(a, z) Y(b, z)`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field_of_isLocalOfOrder`,
  `TauCeti.FormalVertexAxioms.lie_ncoeff_field_eq_finsum`,
  `TauCeti.FormalVertexAxioms.lie_ncoeff_zero_field`: the Borcherds commutator formulas.
* `TauCeti.FormalVertexAxioms.borcherds_identity`,
  `TauCeti.FormalVertexAxioms.borcherds_identity_finsum`: the full Borcherds identity.
* `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply`: the iterate / associativity formula.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum`,
  `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_finsum`,
  `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_finsum_rat`: skew-symmetry.

## References

* R. E. Borcherds, *Vertex algebras, Kac–Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.2 (skew-symmetry), §4.4 (state–field
  duality), §4.6 (commutator formula), and §4.8 (Borcherds identity).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 2.2.4.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.1 and §3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### Uniqueness from translation covariance -/

/-- A translation-covariant field that is local to every field of `A` coincides with
`Y(B₍₋₁₎|0⟩, z)` whenever `V` is additive-torsion-free. -/
theorem eq_field_of_lie_translation [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    {B : VertexOperator R V}
    (hLoc : ∀ c : V, ∃ N : ℕ, B.IsLocalOfOrder (A.field c) N)
    (hT : ∀ m : ℤ, ⁅A.translation, B[[m]]⁆ = (derivative B)[[m]]) :
    B = A.field ((B[[-1]]) A.vacuum) := by
  refine A.eq_field_of_ncoeff_apply_vacuum_eq hLoc fun m ↦ ?_
  rcases le_or_gt 0 m with hm | hm
  · rw [ncoeff_apply_eq_zero_of_lie_derivative A.translation_vacuum hT hm,
      A.ncoeff_field_apply_vacuum_of_nonneg _ m hm]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
    refine (AddCommute.all _ _).eq_of_nsmul_eq_nsmul k.factorial_ne_zero ?_
    rw [factorial_smul_ncoeff_apply_of_lie_derivative A.translation_vacuum hT k,
      A.factorial_smul_ncoeff_field_apply_vacuum]

/-! ### State–field `n`-th product duality -/

/-- **State–field `n`-th product duality.** For any states `a, b : V` and any integer `n : ℤ`,
`Y(a₍ₙ₎ b, z)` is the field-level `n`-th product `nthProduct n Y(a, z) Y(b, z)`. -/
theorem field_ncoeff_apply [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  have hLoc (c : V) :
      ∃ N : ℕ, (nthProduct n (A.field a) (A.field b)).IsLocalOfOrder (A.field c) N := by
    obtain ⟨N₁, h₁⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨N₂, h₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨N₃, h₃⟩ := A.exists_isLocalOfOrder b c
    exact ⟨_, h₁.nthProduct_left h₂ h₃ n⟩
  have hEq := A.eq_field_of_lie_translation hLoc
    (lie_ncoeff_nthProduct A.translation (A.lie_translation_ncoeff a)
      (A.lie_translation_ncoeff b) n)
  rw [ncoeff_neg_one_nthProduct_apply n (A.ncoeff_field_apply_vacuum_of_nonneg a)
    (A.ncoeff_field_apply_vacuum_of_nonneg b), A.ncoeff_neg_one_field_apply_vacuum] at hEq
  exact hEq.symm

/-- For `n : ℕ`, `Y(a₍ₙ₎ b, z)` is the nonnegative residue product
`Res_w (w - z)ⁿ [Y(a, w), Y(b, z)]`. -/
theorem field_ncoeff_natCast_apply [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- For `n = -1`, `Y(a₍₋₁₎ b, z)` is the normal-ordered product `:Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply [IsAddTorsionFree V] (A : FormalVertexAxioms R V) (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_one]

/-- For `n = -k - 1`, `Y(a₍₋ₖ₋₁₎ b, z)` is `: (D^[k] Y(a, z)) Y(b, z) :`. -/
theorem field_ncoeff_neg_succ_apply [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_succ]

/-- The state–Hasse-derivative identity `Y(a₍₋ₖ₋₁₎|0⟩, z) = D^[k] Y(a, z)`. -/
theorem field_ncoeff_neg_succ_apply_vacuum [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) A.vacuum) = hasseDeriv k (A.field a) := by
  have hLoc (c : V) : ∃ N : ℕ, (hasseDeriv k (A.field a)).IsLocalOfOrder (A.field c) N := by
    obtain ⟨N, hN⟩ := A.exists_isLocalOfOrder a c
    exact ⟨N + k, hN.hasseDeriv_left k⟩
  have hEq := A.eq_field_of_lie_translation hLoc
    (lie_ncoeff_hasseDeriv A.translation (A.lie_translation_ncoeff a) k)
  rwa [ncoeff_neg_one_hasseDeriv, eq_comm] at hEq

/-! ### Mode commutator formulas -/

/-- **Mode commutator formula** with an explicit locality bound `N`:
`[a₍ₘ₎, b₍ₙ₎] = ∑_{j < N} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`. -/
theorem lie_ncoeff_field_of_isLocalOfOrder [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    {a b : V} {N : ℕ} (h : (A.field a).IsLocalOfOrder (A.field b) N) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (A.field (((A.field a)[[(j : ℤ)]]) b))[[m + n - j]] := by
  have hd := congrFun (congrFun h.commutatorDistribution_eq_sum_deltaTerm m) n
  rw [commutatorDistribution_apply, ← Ring.lie_def, Finset.sum_apply, Finset.sum_apply] at hd
  rw [hd]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [FormalDistribution.deltaTerm_apply, FormalDistribution.residue_apply,
    FormalDistribution.mulSub_pow_apply, A.field_ncoeff_natCast_apply,
    ncoeff_nonnegResidueProduct]
  congr 1
  refine sum_congr rfl fun ij _ ↦ ?_
  simp [commutatorDistribution_apply]

/-- **Mode commutator formula**, cutoff-free form over all `j : ℕ`. -/
theorem lie_ncoeff_field_eq_finsum [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ᶠ j : ℕ, Ring.choose m j • (A.field (((A.field a)[[(j : ℤ)]]) b))[[m + n - j]] := by
  obtain ⟨N₁, h₁⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨N₂, h₂⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  rw [A.lie_ncoeff_field_of_isLocalOfOrder (h₁.mono (le_max_left N₁ N₂)) m n]
  symm
  refine finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  have hzero : ((A.field a)[[(j : ℤ)]]) b = 0 :=
    h₂ j (Nat.cast_le.mpr (le_trans (le_max_right N₁ N₂) hle))
  exact hj (by simp [hzero])

/-- Zero modes act as derivations of all modes: `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`. -/
@[simp]
theorem lie_ncoeff_zero_field [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℤ) :
    ⁅(A.field a)[[0]], (A.field b)[[n]]⁆ = (A.field (((A.field a)[[0]]) b))[[n]] := by
  obtain ⟨N, hN⟩ := A.exists_isLocalOfOrder a b
  rw [A.lie_ncoeff_field_of_isLocalOfOrder (hN.mono (Nat.le_add_right N 1)) 0 n,
    sum_range_succ']
  simp [Ring.choose_zero_succ]

/-! ### The Borcherds identity and iterate formulas -/

private def borcherdsLHS (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c

private def borcherdsRHS₁ (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c)

private def borcherdsRHS₂ (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) : V :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
    (Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c))

private theorem borcherdsLHS_eq_sum {A : FormalVertexAxioms R V} {a b c : V} {m n r : ℤ} {P : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → ((A.field a)[[n + i]]) b = 0) :
    borcherdsLHS A a b c m n r =
      ∑ i ∈ range P, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [hP i hle])

private theorem borcherdsRHS₁_eq_sum {A : FormalVertexAxioms R V} {a b c : V} {m n r : ℤ} {P : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → ((A.field b)[[r + i]]) c = 0) :
    borcherdsRHS₁ A a b c m n r =
      ∑ i ∈ range P, ((-1 : ℤ) ^ i * Ring.choose n i) •
        ((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [hP i hle])

private theorem borcherdsRHS₂_eq_sum {A : FormalVertexAxioms R V} {a b c : V} {m n r : ℤ} {P : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → ((A.field a)[[m + i]]) c = 0) :
    borcherdsRHS₂ A a b c m n r =
      ∑ i ∈ range P, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [hP i hle])

private theorem borcherdsLHS_zero (A : FormalVertexAxioms R V) (a b c : V) (n r : ℤ) :
    borcherdsLHS A a b c 0 n r = ((A.field (((A.field a)[[n]]) b))[[r]]) c := by
  obtain ⟨K, hK⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let P := K + n.natAbs + 1
  rw [borcherdsLHS_eq_sum (P := P + 1) (fun i hi ↦ hK _ (by omega)), sum_range_succ']
  simp [Ring.choose_zero_succ]

private theorem choose_neg_succ_eq (k i : ℕ) :
    (-1 : ℤ) ^ i * Ring.choose (-(k : ℤ) - 1) i = (k + i).choose k := by
  have heq : -(k : ℤ) - 1 = -((k : ℤ) + 1) := by ring
  have hidx : (k : ℤ) + 1 + i - 1 = ((k + i : ℕ) : ℤ) := by push_cast; ring
  rw [heq, Ring.choose_neg, hidx, Ring.choose_natCast, Units.smul_def,
    Int.coe_negOnePow_natCast, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul,
    Even.neg_one_pow ⟨i, two_mul i⟩, one_mul, Nat.choose_symm_add]

private theorem borcherdsRHS₁_natCast (A : FormalVertexAxioms R V) (a b c : V) (m : ℤ) (k : ℕ)
    (r : ℤ) :
    borcherdsRHS₁ A a b c m k r =
      ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i * k.choose i) •
        ((A.field a)[[m + k - i]]) (((A.field b)[[r + i]]) c) := by
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).trans (sum_congr rfl fun i _ ↦ ?_)
  · simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hle])
  · simp [Ring.choose_natCast]

private theorem borcherdsRHS₂_natCast (A : FormalVertexAxioms R V) (a b c : V) (m : ℤ) (k : ℕ)
    (r : ℤ) :
    borcherdsRHS₂ A a b c m k r =
      ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i * k.choose i) •
        (Int.negOnePow (k : ℤ) •
          ((A.field b)[[(k : ℤ) + r - i]]) (((A.field a)[[m + i]]) c)) := by
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).trans (sum_congr rfl fun i _ ↦ ?_)
  · simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hle])
  · simp [Ring.choose_natCast]

private theorem borcherds_zero_left_nonneg [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b c : V) (k : ℕ) (r : ℤ) :
    borcherdsLHS A a b c 0 k r = borcherdsRHS₁ A a b c 0 k r - borcherdsRHS₂ A a b c 0 k r := by
  rw [borcherdsLHS_zero, A.field_ncoeff_natCast_apply, ncoeff_nonnegResidueProduct,
    borcherdsRHS₁_natCast, borcherdsRHS₂_natCast, zero_add, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp, smul_sub,
    sum_sub_distrib, zero_add]
  congr 1
  · rw [← Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ k.choose j • (-1 : ℤ) ^ i • ((A.field a)[[(j : ℤ)]]) (((A.field b)[[r + i]]) c))]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Nat.choose_symm hik, Nat.cast_sub hik, ← natCast_zsmul, smul_smul, mul_comm]
  · rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ k.choose i • (-1 : ℤ) ^ j • ((A.field b)[[r + j]]) (((A.field a)[[(i : ℤ)]]) c))]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hpow : (-1 : ℤ) ^ i * (k.choose i : ℤ) * (-1 : ℤ) ^ k =
        (k.choose i : ℤ) * (-1 : ℤ) ^ (k - i) := by
      have hk : (-1 : ℤ) ^ k = (-1 : ℤ) ^ i * (-1 : ℤ) ^ (k - i) := by
        rw [← pow_add, Nat.add_sub_of_le hik]
      calc (-1 : ℤ) ^ i * (k.choose i : ℤ) * (-1 : ℤ) ^ k
          = ((-1 : ℤ) ^ i * (-1 : ℤ) ^ i) * (k.choose i : ℤ) * (-1 : ℤ) ^ (k - i) := by
            rw [hk]; ring
        _ = (k.choose i : ℤ) * (-1 : ℤ) ^ (k - i) := by
          rw [← pow_add, ← two_mul, Even.neg_one_pow ⟨i, two_mul i⟩, one_mul]
    rw [Units.smul_def, Int.coe_negOnePow_natCast, smul_smul, ← natCast_zsmul, smul_smul,
      Nat.cast_sub hik, show r + ((k : ℤ) - i) = (k : ℤ) + r - i by ring, hpow]

private theorem borcherds_zero_left_neg [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b c : V) (k : ℕ) (r : ℤ) :
    borcherdsLHS A a b c 0 (-(k : ℤ) - 1) r =
      borcherdsRHS₁ A a b c 0 (-(k : ℤ) - 1) r - borcherdsRHS₂ A a b c 0 (-(k : ℤ) - 1) r := by
  obtain ⟨K₁, hK₁⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨K₂, hK₂⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let P := K₁ + r.natAbs
  have bP (i : ℕ) (hi : P ≤ i) : ((A.field b)[[r + i]]) c = 0 := hK₁ _ (by omega)
  have bQ (i : ℕ) (hi : K₂ ≤ i) : ((A.field a)[[(i : ℤ)]]) c = 0 :=
    hK₂ _ (Nat.cast_le.mpr hi)
  have bQ' (j : ℕ) (hj : k + K₂ ≤ j) : ((hasseDeriv k (A.field a))[[(j : ℤ)]]) c = 0 := by
    rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, hK₂ _ (by omega),
      smul_zero, smul_zero]
  rw [borcherdsLHS_zero, A.field_ncoeff_neg_succ_apply, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum _ _ r c bP bQ', borcherdsRHS₁_eq_sum bP,
    borcherdsRHS₂_eq_sum (fun i hi ↦ by simpa using bQ i hi), sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul,
      choose_neg_succ_eq i k, choose_neg_succ_eq k i, add_comm i k, Nat.choose_symm_add, zero_add,
      show -(i : ℤ) - 1 - k = -(k : ℤ) - 1 - i by ring]
  · rw [sum_range_add, sum_eq_zero fun j hj ↦ by
      rw [ncoeff_hasseDeriv, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (mem_range.mp hj),
        Nat.cast_zero, zero_smul, smul_zero, LinearMap.zero_apply, map_zero], zero_add]
    refine sum_congr rfl fun i _ ↦ ?_
    have hsign : -((Int.negOnePow (-(k : ℤ) - 1) : ℤ)) = (-1 : ℤ) ^ k := by
      have he : -(k : ℤ) - 1 = -((k : ℤ) + 1) := by ring
      rw [he, Int.negOnePow_neg, Int.negOnePow_succ, Units.val_neg,
        Int.coe_negOnePow_natCast, neg_neg]
    rw [ncoeff_hasseDeriv, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, map_zsmul,
      Ring.choose_natCast, Nat.cast_add, add_sub_cancel_left, choose_neg_succ_eq k i,
      Units.smul_def, zero_add, ← neg_zsmul, smul_smul, smul_smul,
      show r - ((k : ℤ) + i) - 1 = -(k : ℤ) - 1 + r - i by ring]
    congr 1
    rw [← hsign]
    ring

private theorem borcherds_large_nat (A : FormalVertexAxioms R V) (a b c : V) {k : ℕ}
    (hLoc : (A.field a).IsLocalOfOrder (A.field b) k)
    (hTrunc : ∀ i : ℕ, ((A.field a)[[(k : ℤ) + i]]) b = 0) (m r : ℤ) :
    borcherdsLHS A a b c m k r - (borcherdsRHS₁ A a b c m k r - borcherdsRHS₂ A a b c m k r) =
      0 := by
  have hL : borcherdsLHS A a b c m k r = 0 := by
    rw [borcherdsLHS_eq_sum (P := 0) (fun i _ ↦ hTrunc i), range_zero, sum_empty]
  have h0 := LinearMap.congr_fun (isLocalOfOrder_iff.mp hLoc m r) c
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
    LinearMap.zero_apply, smul_sub, sum_sub_distrib] at h0
  rw [hL, zero_sub, neg_eq_zero, borcherdsRHS₁_natCast, borcherdsRHS₂_natCast, ← h0]
  congr 1
  · symm
    rw [← Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ k.choose j • (-1 : ℤ) ^ i • ((A.field a)[[m + j]]) (((A.field b)[[r + i]]) c))]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [Nat.choose_symm hik, Nat.cast_sub hik, ← natCast_zsmul, smul_smul, mul_comm,
      show m + ((k : ℤ) - i) = m + k - i by ring]
  · rw [Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ k.choose i • (-1 : ℤ) ^ j • ((A.field b)[[r + j]]) (((A.field a)[[m + i]]) c))]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hpow : (-1 : ℤ) ^ i * (k.choose i : ℤ) * (-1 : ℤ) ^ k =
        (k.choose i : ℤ) * (-1 : ℤ) ^ (k - i) := by
      have hk : (-1 : ℤ) ^ k = (-1 : ℤ) ^ i * (-1 : ℤ) ^ (k - i) := by
        rw [← pow_add, Nat.add_sub_of_le hik]
      calc (-1 : ℤ) ^ i * (k.choose i : ℤ) * (-1 : ℤ) ^ k
          = ((-1 : ℤ) ^ i * (-1 : ℤ) ^ i) * (k.choose i : ℤ) * (-1 : ℤ) ^ (k - i) := by
            rw [hk]; ring
        _ = (k.choose i : ℤ) * (-1 : ℤ) ^ (k - i) := by
          rw [← pow_add, ← two_mul, Even.neg_one_pow ⟨i, two_mul i⟩, one_mul]
    rw [Units.smul_def, Int.coe_negOnePow_natCast, smul_smul, ← natCast_zsmul, smul_smul,
      Nat.cast_sub hik, show r + ((k : ℤ) - i) = (k : ℤ) + r - i by ring, hpow]

private theorem borcherdsLHS_succ (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) :
    borcherdsLHS A a b c (m + 1) n r =
      borcherdsLHS A a b c m n (r + 1) + borcherdsLHS A a b c m (n + 1) r := by
  obtain ⟨K, hK⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  let P := K + n.natAbs + 1
  have b0 (i : ℕ) (hi : P + 1 ≤ i) : ((A.field a)[[n + i]]) b = 0 := hK _ (by omega)
  have b1 (i : ℕ) (hi : P ≤ i) : ((A.field a)[[n + 1 + i]]) b = 0 := hK _ (by omega)
  rw [borcherdsLHS_eq_sum b0, borcherdsLHS_eq_sum b0, borcherdsLHS_eq_sum b1]
  conv_lhs => rw [sum_range_succ']
  conv_rhs => rw [sum_range_succ']
  simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, add_zero, sub_zero,
    show m + 1 + r = m + (r + 1) by ring]
  have hcancel : ∀ x y z w : V, x = y + z → x + w = (y + w) + z := fun _ _ _ _ h ↦ by rw [h]; abel
  apply hcancel
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Ring.choose_succ_succ, Nat.cast_add, Nat.cast_one,
    show n + ((i : ℤ) + 1) = n + 1 + i by ring,
    show m + (r + 1) - ((i : ℤ) + 1) = m + r - i by ring, add_zsmul, add_comm]

private theorem borcherdsRHS₁_succ (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) :
    borcherdsRHS₁ A a b c (m + 1) n r =
      borcherdsRHS₁ A a b c m n (r + 1) + borcherdsRHS₁ A a b c m (n + 1) r := by
  obtain ⟨K, hK⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  let P := K + r.natAbs + 1
  have b0 (i : ℕ) (hi : P + 1 ≤ i) : ((A.field b)[[r + i]]) c = 0 := hK _ (by omega)
  have b1 (i : ℕ) (hi : P ≤ i) : ((A.field b)[[r + 1 + i]]) c = 0 := hK _ (by omega)
  rw [borcherdsRHS₁_eq_sum b0, borcherdsRHS₁_eq_sum b1, borcherdsRHS₁_eq_sum b0]
  conv_lhs => rw [sum_range_succ']
  conv_rhs => rw [add_comm, sum_range_succ']
  simp only [pow_zero, Ring.choose_zero_right, mul_one, one_smul, Nat.cast_zero, sub_zero,
    add_zero, show m + 1 + n = m + (n + 1) by ring]
  have hcancel : ∀ x y z w : V, x = y + z → x + w = (y + w) + z := fun _ _ _ _ h ↦ by rw [h]; abel
  apply hcancel
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hcoef : (-1 : ℤ) ^ (i + 1) * Ring.choose n (i + 1) =
      (-1 : ℤ) ^ (i + 1) * Ring.choose (n + 1) (i + 1) + (-1 : ℤ) ^ i * Ring.choose n i := by
    rw [Ring.choose_succ_succ, pow_succ]
    ring
  rw [Nat.cast_add, Nat.cast_one,
    show m + (n + 1) - ((i : ℤ) + 1) = m + n - i by ring,
    show r + ((i : ℤ) + 1) = r + 1 + i by ring, hcoef, add_zsmul]

private theorem borcherdsRHS₂_succ (A : FormalVertexAxioms R V) (a b c : V) (m n r : ℤ) :
    borcherdsRHS₂ A a b c (m + 1) n r =
      borcherdsRHS₂ A a b c m n (r + 1) + borcherdsRHS₂ A a b c m (n + 1) r := by
  obtain ⟨K, hK⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let P := K + m.natAbs + 1
  have b0 (i : ℕ) (hi : P + 1 ≤ i) : ((A.field a)[[m + i]]) c = 0 := hK _ (by omega)
  have b1 (i : ℕ) (hi : P ≤ i) : ((A.field a)[[m + 1 + i]]) c = 0 := hK _ (by omega)
  rw [borcherdsRHS₂_eq_sum b1, borcherdsRHS₂_eq_sum b0, borcherdsRHS₂_eq_sum b0]
  conv_rhs => rw [sum_range_succ', add_comm, sum_range_succ']
  simp only [pow_zero, Ring.choose_zero_right, mul_one, one_smul, Nat.cast_zero, sub_zero,
    add_zero, Int.negOnePow_succ, Units.neg_smul, show n + 1 + r = n + (r + 1) by ring]
  have hcancel : ∀ x y z : V, (x + -z) + (y + z) = x + y := fun _ _ _ ↦ by abel
  rw [hcancel, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hcoef : (-1 : ℤ) ^ i * Ring.choose n i =
      -((-1 : ℤ) ^ (i + 1) * Ring.choose (n + 1) (i + 1)) +
        (-1 : ℤ) ^ (i + 1) * Ring.choose n (i + 1) := by
    rw [Ring.choose_succ_succ, pow_succ]
    ring
  rw [Nat.cast_add, Nat.cast_one,
    show n + (r + 1) - ((i : ℤ) + 1) = n + r - i by ring,
    show m + ((i : ℤ) + 1) = m + 1 + i by ring, smul_neg, ← neg_zsmul, ← add_zsmul, hcoef]

private theorem eq_zero_of_pascal_recurrence {Δ : ℤ → ℤ → ℤ → V}
    (hRec : ∀ m n r : ℤ, Δ (m + 1) n r = Δ m n (r + 1) + Δ m (n + 1) r)
    (hZero : ∀ n r : ℤ, Δ 0 n r = 0)
    {M : ℕ} (hLarge : ∀ {k : ℕ}, M ≤ k → ∀ m r : ℤ, Δ m k r = 0)
    (m n r : ℤ) : Δ m n r = 0 := by
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    induction m generalizing n r with
    | zero => exact hZero n r
    | succ d ih => rw [Nat.cast_succ, hRec, ih, ih, add_zero]
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = -(d : ℤ) := ⟨(-m).toNat, by omega⟩
    clear hm
    induction d generalizing n r with
    | zero => simpa using hZero n r
    | succ d ih =>
      have hstep (n' r' : ℤ) : Δ (-((d + 1 : ℕ) : ℤ)) n' r' =
          -Δ (-((d + 1 : ℕ) : ℤ)) (n' + 1) (r' - 1) := by
        have h := hRec (-((d + 1 : ℕ) : ℤ)) n' (r' - 1)
        rw [show -((d + 1 : ℕ) : ℤ) + 1 = -(d : ℤ) by push_cast; ring, ih, sub_add_cancel] at h
        exact eq_neg_of_add_eq_zero_left h.symm
      have hdown (t : ℕ) : ∀ r' : ℤ, Δ (-((d + 1 : ℕ) : ℤ)) ((M : ℤ) - t) r' = 0 := by
        induction t with
        | zero => intro r'; simpa using hLarge le_rfl _ r'
        | succ t iht =>
          intro r'
          rw [hstep, show (M : ℤ) - ((t + 1 : ℕ) : ℤ) + 1 = (M : ℤ) - t by push_cast; ring,
            iht, neg_zero]
      rcases le_or_gt (M : ℤ) n with hMn | hMn
      · lift n to ℕ using le_trans (Nat.cast_nonneg M) hMn
        exact hLarge (Nat.cast_le.mp hMn) _ r
      · rw [show n = (M : ℤ) - ((M : ℤ) - n).toNat by omega, hdown]

private theorem borcherds_diff_eq_zero [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b c : V) (m n r : ℤ) :
    borcherdsLHS A a b c m n r -
      (borcherdsRHS₁ A a b c m n r - borcherdsRHS₂ A a b c m n r) = 0 := by
  obtain ⟨N₁, hLoc⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨N₂, hTrunc⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  refine eq_zero_of_pascal_recurrence
    (Δ := fun m' n' r' ↦ borcherdsLHS A a b c m' n' r' -
      (borcherdsRHS₁ A a b c m' n' r' - borcherdsRHS₂ A a b c m' n' r'))
    (fun m' n' r' ↦ by simp only [borcherdsLHS_succ, borcherdsRHS₁_succ, borcherdsRHS₂_succ]; abel)
    (fun n' r' ↦ ?_) (M := max N₁ N₂)
    (fun hk m' r' ↦ borcherds_large_nat A a b c (hLoc.mono (le_trans (le_max_left N₁ N₂) hk))
      (fun i ↦ hTrunc _ (by have := le_max_right N₁ N₂; omega)) m' r') m n r
  rcases le_or_gt 0 n' with hn | hn
  · lift n' to ℕ using hn
    exact sub_eq_zero.mpr (borcherds_zero_left_nonneg A a b c n' r')
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n' = -(k : ℤ) - 1 := ⟨(-n' - 1).toNat, by omega⟩
    exact sub_eq_zero.mpr (borcherds_zero_left_neg A a b c k r')

/-- **The Borcherds identity**, cutoff-free `finsum` form: for all states `a, b, c : V` and all
mode indices `m, n, r : ℤ`,
`∑ᵢ (m choose i) (a₍ₙ₊ᵢ₎ b)₍ₘ₊ᵣ₋ᵢ₎ c =`
`∑ᵢ (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c))`. -/
theorem borcherds_identity_finsum [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b c : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
  obtain ⟨K₁, hK₁⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨K₂, hK₂⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  let P := max K₁ K₂ + r.natAbs + m.natAbs
  have b₁ (i : ℕ) (hi : P ≤ i) : ((A.field b)[[r + i]]) c = 0 :=
    hK₁ _ (by have := le_max_left K₁ K₂; omega)
  have b₂ (i : ℕ) (hi : P ≤ i) : ((A.field a)[[m + i]]) c = 0 :=
    hK₂ _ (by have := le_max_right K₁ K₂; omega)
  have hRHS : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
      (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
        Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c))) =
      borcherdsRHS₁ A a b c m n r - borcherdsRHS₂ A a b c m n r := by
    rw [borcherdsRHS₁_eq_sum b₁, borcherdsRHS₂_eq_sum b₂, ← sum_sub_distrib]
    refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).trans
      (sum_congr rfl fun i _ ↦ smul_sub _ _ _)
    simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [b₁ i hle, b₂ i hle])
  rw [hRHS]
  exact sub_eq_zero.mp (borcherds_diff_eq_zero A a b c m n r)

/-- **The Borcherds identity**, explicit finite-sum form for any cutoff `K` beyond the lower
truncation bounds of `(a, b)`, `(b, c)`, and `(a, c)`. -/
theorem borcherds_identity [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b c : V) (m n r : ℤ) {K : ℕ}
    (hab : ∀ i : ℕ, K ≤ i → ((A.field a)[[n + i]]) b = 0)
    (hbc : ∀ i : ℕ, K ≤ i → ((A.field b)[[r + i]]) c = 0)
    (hac : ∀ i : ℕ, K ≤ i → ((A.field a)[[m + i]]) c = 0) :
    ∑ i ∈ range K, Ring.choose m i •
        ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c =
      ∑ i ∈ range K, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
  have hL := (borcherdsLHS_eq_sum (A := A) (c := c) (m := m) (r := r) hab).symm
  have hR : ∑ i ∈ range K, ((-1 : ℤ) ^ i * Ring.choose n i) •
      (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
        Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) := by
    symm
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [hbc i hle, hac i hle])
  rw [hL, hR]
  exact A.borcherds_identity_finsum a b c m n r

/-- **The iterate (associativity) formula** (`m = 0` of the Borcherds identity): expresses the
mode `(a₍ₙ₎ b)₍ᵣ₎ c` in terms of modes of `a` and `b` acting on `c`. -/
theorem ncoeff_field_ncoeff_apply [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c) -
          Int.negOnePow n • ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  have h := A.borcherds_identity_finsum a b c 0 n r
  rw [show (∑ᶠ i : ℕ, Ring.choose (0 : ℤ) i •
      ((A.field (((A.field a)[[n + i]]) b))[[0 + r - i]]) c) =
    borcherdsLHS A a b c 0 n r from rfl, borcherdsLHS_zero] at h
  simpa only [zero_add] using h

/-! ### Skew-symmetry -/

/-- **Skew-symmetry**, cutoff-free `finsum` form: for any states `a, b : V` and `n : ℤ`,
`a₍ₙ₎ b = ∑ᵢ (-1)^{n + i + 1} (b₍ₙ₊ᵢ₎ a)₍₋ᵢ₋₁₎ |0⟩`. -/
theorem ncoeff_field_apply_eq_finsum [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, Int.negOnePow (n + i + 1) •
        ((A.field (((A.field b)[[n + i]]) a))[[-(i : ℤ) - 1]]) A.vacuum := by
  have hb := A.borcherds_identity_finsum b a A.vacuum (-1) n 0
  have hRHS : (∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
      (((A.field b)[[-1 + n - i]]) (((A.field a)[[0 + i]]) A.vacuum) -
        Int.negOnePow n • ((A.field a)[[n + 0 - i]]) (((A.field b)[[-1 + i]]) A.vacuum))) =
      -(Int.negOnePow n • ((A.field a)[[n]]) b) := by
    rw [finsum_eq_single _ 0 fun i hi ↦ ?_]
    · simp [A.ncoeff_field_apply_vacuum_of_nonneg]
    · rw [zero_add, A.ncoeff_field_apply_vacuum_of_nonneg a i (Nat.cast_nonneg i),
        A.ncoeff_field_apply_vacuum_of_nonneg b (-1 + i) (by omega), map_zero, map_zero,
        smul_zero, sub_zero, smul_zero]
  rw [hRHS] at hb
  have hinv := congrArg (fun v : V ↦ -(Int.negOnePow n • v)) hb
  rw [smul_neg, neg_neg, smul_smul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul,
    one_smul] at hinv
  rw [← hinv]
  obtain ⟨K, hK⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let P := K + n.natAbs
  have bP (i : ℕ) (hi : P ≤ i) : ((A.field b)[[n + i]]) a = 0 := hK _ (by omega)
  rw [show (∑ᶠ i : ℕ, Ring.choose (-1 : ℤ) i •
      ((A.field (((A.field b)[[n + i]]) a))[[-1 + 0 - i]]) A.vacuum) =
    borcherdsLHS A b a A.vacuum (-1) n 0 from rfl, borcherdsLHS_eq_sum bP, smul_sum,
    ← sum_neg_distrib]
  symm
  refine (finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_).trans (sum_congr rfl fun i _ ↦ ?_)
  · simp only [mem_coe, mem_range]
    by_contra! hle
    exact hi (by simp [bP i hle])
  · have hchoose : Ring.choose (-1 : ℤ) i = (-1 : ℤ) ^ i := by
      simpa [Ring.multichoose_one, Units.smul_def, Int.coe_negOnePow_natCast] using
        Ring.choose_neg' (1 : ℤ) i
    have hpow : -((Int.negOnePow n : ℤ) * (-1 : ℤ) ^ i) =
        (Int.negOnePow (n + i + 1) : ℤ) := by
      rw [Int.negOnePow_succ, Int.negOnePow_add, Units.val_neg, Units.val_mul,
        Int.coe_negOnePow_natCast]
    rw [hchoose, Units.smul_def, Units.smul_def, smul_smul, ← neg_zsmul, hpow,
      show -(i : ℤ) - 1 = -1 + 0 - i by ring]

/-- **Skew-symmetry**, explicit finite-sum form for any cutoff `K` with `b₍ₙ₊ᵢ₎ a = 0` (`i ≥ K`). -/
theorem ncoeff_field_apply_eq_sum [IsAddTorsionFree V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℤ) {K : ℕ}
    (hba : ∀ i : ℕ, K ≤ i → ((A.field b)[[n + i]]) a = 0) :
    ((A.field a)[[n]]) b =
      ∑ i ∈ range K, Int.negOnePow (n + i + 1) •
        ((A.field (((A.field b)[[n + i]]) a))[[-(i : ℤ) - 1]]) A.vacuum := by
  rw [A.ncoeff_field_apply_eq_finsum a b n]
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (by simp [hba i hle])

/-- **Skew-symmetry** over a `ℚ`-module (`Y(a, z) b = e^{zT} Y(b, -z) a` in modes):
`a₍ₙ₎ b = ∑ᵢ (-1)^{n + i + 1} (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)`. -/
theorem ncoeff_field_apply_eq_finsum_rat [Module ℚ V] (A : FormalVertexAxioms R V)
    (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, Int.negOnePow (n + i + 1) •
        (i.factorial : ℚ)⁻¹ • (A.translation ^ i) (((A.field b)[[n + i]]) a) := by
  have := HasUniqueDiv.of_module_rat V
  rw [A.ncoeff_field_apply_eq_finsum a b n]
  exact finsum_congr fun i ↦ by rw [A.ncoeff_field_apply_vacuum_neg]

end FormalVertexAxioms

end TauCeti
