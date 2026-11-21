/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.Dong
public import TauCeti.Algebra.Vertex.Borcherds.Field
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Integer field products and the Borcherds identity

Let `A : FormalVertexAxioms R V` be a formal vertex algebra over a commutative ring `R`. While the
axioms of `FormalVertexAxioms` are division-free, recovering the negative modes of a field on the
vacuum from powers of the translation operator `T` via `k! • a₍₋ₖ₋₁₎|0⟩ = Tᵏ a` requires cancelling
`k!`, i.e. unique divisibility `[HasUniqueDiv V]` (satisfied in particular by every `ℚ`-module).

Under `[HasUniqueDiv V]`, Dong's lemma (`VertexOperator.IsLocalOfOrder.nthProduct_left`) and
uniqueness (`FormalVertexAxioms.eq_field_of_lie_translation_ncoeff`) identify the
state–field map on every integer mode product `(a₍ₙ₎ b)` (`n : ℤ`) with the `n`-th field product
`VertexOperator.nthProduct n (A.field a) (A.field b)`. From this and the field-level Borcherds
identity (`TauCeti.Algebra.Vertex.Borcherds.Field`), we deduce the Borcherds commutator and iterate
formulas and the state-level Borcherds identity.

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: state–field correspondence
  `Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)` for all `n : ℤ` under `[HasUniqueDiv V]`, together with the
  specializations `field_ncoeff_neg_one_apply`, `field_ncoeff_natCast_apply`,
  `field_ncoeff_zero_apply`, and `field_ncoeff_neg_succ_apply`.
* `TauCeti.FormalVertexAxioms.lie_ncoeff_field_eq_sum` and
  `TauCeti.FormalVertexAxioms.lie_ncoeff_field_finsum`: the Borcherds commutator formula
  `⁅a₍ₘ₎, b₍ₙ₎⁆ = ∑_{j < N} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`, its `m = 0` specialization
  `TauCeti.FormalVertexAxioms.lie_ncoeff_zero_field` (`⁅a₍₀₎, b₍ₙ₎⁆ = (a₍₀₎ b)₍ₙ₎`), and the
  derivation identity `TauCeti.FormalVertexAxioms.ncoeff_zero_field_ncoeff_apply`.
* `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply_apply_eq_sum` and
  `TauCeti.FormalVertexAxioms.ncoeff_field_ncoeff_apply`: the Borcherds iterate formula
  for `((a₍ₙ₎ b)₍q₎) c`.
* `TauCeti.FormalVertexAxioms.borcherds_finsum`, `TauCeti.FormalVertexAxioms.borcherds`, and
  `TauCeti.FormalVertexAxioms.exists_borcherds`: the full three-parameter Borcherds identity for
  all `m, n, q : ℤ` under `[HasUniqueDiv V]`, deduced from the field-level identity
  `VertexOperator.IsLocalOfOrder.borcherds_finsum`.

## References

* R. E. Borcherds, *Vertex algebras, Kac-Moody algebras, and the Monster*, Proc. Nat. Acad. Sci.
  U.S.A. 83 (1986), 3068–3071, §4.
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.5 (Theorem 4.5, state–field correspondence
  for `n`-th products) and §4.8 (Theorem 4.8, the Borcherds identity).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), 143–195, Proposition 3.2.7.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.2–3.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-! ### State–field correspondence for integer products -/

/-- **State–field correspondence for integer products.** When `V` has unique divisibility
(in particular over any `ℚ`-module), the field of every `n`-th product `a₍ₙ₎ b` (`n : ℤ`) is the
`n`-th field product `nthProduct n (Y(a, z)) (Y(b, z))`. -/
theorem field_ncoeff_apply [HasUniqueDiv V] (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_lie_translation_ncoeff (fun c ↦ ?_)
    (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n)
    ((ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
      (A.ncoeff_field_apply_vacuum_of_nonneg b) n).trans (by simp))
  obtain ⟨r₀, h₀⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨r₁, h₁⟩ := A.exists_isLocalOfOrder a c
  obtain ⟨r₂, h₂⟩ := A.exists_isLocalOfOrder b c
  exact ⟨_, h₀.nthProduct_left h₁ h₂ n⟩

/-- The field of the `(-1)`-st product `a₍₋₁₎ b` is the normal-ordered product `:Y(a,z) Y(b,z):`. -/
theorem field_ncoeff_neg_one_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  simp [A.field_ncoeff_apply]

/-- For `n : ℕ`, the field of `a₍ₙ₎ b` is `nonnegResidueProduct n (Y(a,z)) (Y(b,z))`. -/
theorem field_ncoeff_natCast_apply [HasUniqueDiv V] (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- The field of the `0`-th product `a₍₀₎ b` is `nonnegResidueProduct 0 (Y(a,z)) (Y(b,z))`. -/
theorem field_ncoeff_zero_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[0]]) b) = nonnegResidueProduct 0 (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_zero]

/-- For `k : ℕ`, `Y(a₍₋ₖ₋₁₎ b, z)` is `:(∂_z^{(k)} Y(a, z)) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply [HasUniqueDiv V] (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_natCast_sub_one]

/-! ### Borcherds commutator and iterate formulas -/

/-- **Borcherds commutator formula.** For any cutoff `N : ℕ` above which `a₍ⱼ₎ b = 0`,
`⁅a₍ₘ₎, b₍ₙ₎⁆ = ∑_{j < N} (m choose j) (a₍ⱼ₎ b)₍ₘ₊ₙ₋ⱼ₎`. -/
theorem lie_ncoeff_field_eq_sum [HasUniqueDiv V] (a b : V) (m n : ℤ) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → ((A.field a)[[(j : ℤ)]]) b = 0) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ j ∈ range N, Ring.choose m j • (A.field (((A.field a)[[(j : ℤ)]]) b))[[m + n - j]] := by
  obtain ⟨L, hL⟩ := A.exists_isLocalOfOrder a b
  rw [(hL.mono (le_max_right N L)).lie_ncoeff_eq_sum_nthProduct m n]
  simp_rw [← A.field_ncoeff_apply]
  symm
  refine sum_subset (range_mono (le_max_left N L)) fun j _ hj ↦ ?_
  simp [hN j (by simp only [mem_range] at hj; omega)]

/-- **Borcherds commutator formula** in `finsum` form, independent of a chosen locality bound. -/
theorem lie_ncoeff_field_finsum [HasUniqueDiv V] (a b : V) (m n : ℤ) :
    ⁅(A.field a)[[m]], (A.field b)[[n]]⁆ =
      ∑ᶠ i : ℕ, Ring.choose m i • (A.field (((A.field a)[[(i : ℤ)]]) b))[[m + n - i]] := by
  obtain ⟨N, h⟩ := A.exists_isLocalOfOrder a b
  have hN (j : ℕ) (hj : N ≤ j) : ((A.field a)[[(j : ℤ)]]) b = 0 :=
    A.ncoeff_field_apply_eq_zero_of_isLocalOfOrder h hj
  rw [A.lie_ncoeff_field_eq_sum a b m n hN, eq_comm]
  exact TauCeti.finsum_eq_sum_range_of_forall_eq_zero fun i hi ↦ by simp [hN i hi]

/-- The `0`-th mode `a₍₀₎` commutes with `Y(b, z)` by `[a₍₀₎, b₍ₙ₎] = (a₍₀₎ b)₍ₙ₎`. -/
@[simp]
theorem lie_ncoeff_zero_field [HasUniqueDiv V] (a b : V) (n : ℤ) :
    ⁅(A.field a)[[0]], (A.field b)[[n]]⁆ = (A.field (((A.field a)[[0]]) b))[[n]] := by
  obtain ⟨N, hN⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  rw [A.lie_ncoeff_field_eq_sum a b 0 n (N := N + 1) (fun j hj ↦ hN j (by omega)), sum_range_succ']
  simp

/-- The `0`-th mode `a₍₀₎` is a derivation of every `n`-th product (`n : ℤ`):
`a₍₀₎ (b₍ₙ₎ c) = (a₍₀₎ b)₍ₙ₎ c + b₍ₙ₎ (a₍₀₎ c)`. At `n = 0` this is the Leibniz identity for
`₍₀₎`. -/
theorem ncoeff_zero_field_ncoeff_apply [HasUniqueDiv V] (a b c : V) (n : ℤ) :
    ((A.field a)[[0]]) (((A.field b)[[n]]) c) =
      ((A.field (((A.field a)[[0]]) b))[[n]]) c +
        ((A.field b)[[n]]) (((A.field a)[[0]]) c) := by
  have h := LinearMap.congr_fun (A.lie_ncoeff_zero_field a b n) c
  rwa [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    sub_eq_iff_eq_add] at h

/-- **Borcherds iterate formula.** Mode expansion of `((a₍ₙ₎ b)₍q₎) c` for any `n, q : ℤ`. -/
theorem ncoeff_field_ncoeff_apply_apply_eq_sum [HasUniqueDiv V] (a b c : V) (n q : ℤ) {K : ℕ}
    (ha : ∀ j : ℕ, K ≤ j → ((A.field a)[[(j : ℤ)]]) c = 0)
    (hb : ∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0) :
    ((A.field (((A.field a)[[n]]) b))[[q]]) c =
      ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
        (((A.field a)[[n - j]]) (((A.field b)[[q + j]]) c) -
          Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[(j : ℤ)]]) c)) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct_apply_eq_sum n (A.field a) (A.field b) q c ha hb]

/-- **Mode iterate / associativity formula** (`m = 0` case of the Borcherds identity) in `finsum`
form: `((a₍ₙ₎ b)₍ᵣ₎) c = ∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ᵢ₎ c))`
for all `a, b, c : V` and all integers `n, r : ℤ`. -/
theorem ncoeff_field_ncoeff_apply [HasUniqueDiv V] (a b c : V) (n r : ℤ) :
    ((A.field (((A.field a)[[n]]) b))[[r]]) c =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[(i : ℤ)]]) c)) := by
  rw [A.field_ncoeff_apply, ncoeff_nthProduct_apply]

/-! ### The full Borcherds identity -/

/-- **The Borcherds identity** in `finsum` form: for all states `a, b, c : V` and `m, n, r : ℤ`,
`∑ᶠ i : ℕ, (m choose i) (a₍ₙ₊ᵢ₎ b)₍ₘ₊ᵣ₋ᵢ₎ c =`
`∑ᶠ i : ℕ, (-1)ⁱ (n choose i) (a₍ₘ₊ₙ₋ᵢ₎ (b₍ᵣ₊ᵢ₎ c) - (-1)ⁿ b₍ₙ₊ᵣ₋ᵢ₎ (a₍ₘ₊ᵢ₎ c))`. -/
theorem borcherds_finsum [HasUniqueDiv V] (a b c : V) (m n r : ℤ) :
    (∑ᶠ i : ℕ, Ring.choose m i • ((A.field (((A.field a)[[n + i]]) b))[[m + r - i]]) c) =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i * Ring.choose n i) •
        (((A.field a)[[m + n - i]]) (((A.field b)[[r + i]]) c) -
          (n.negOnePow : ℤ) • ((A.field b)[[n + r - i]]) (((A.field a)[[m + i]]) c)) :=
  let ⟨_, h⟩ := A.exists_isLocalOfOrder a b
  by simpa only [A.field_ncoeff_apply] using h.borcherds_finsum c m n r

/-- **The Borcherds identity.** For any states `a, b, c : V`, any modes `m, n, q : ℤ`, and any
cutoffs `K, L : ℕ` with `a₍ₘ₊ⱼ₎ c = 0` and `b₍q₊ⱼ₎ c = 0` for `K ≤ j` and `a₍ₙ₊ⱼ₎ b = 0` for
`L ≤ j`,
`∑_{j < K} (-1)ʲ (n choose j) (a₍ₘ₊ₙ₋ⱼ₎ (b₍q₊ⱼ₎ c) - (-1)ⁿ b₍ₙ₊q₋ⱼ₎ (a₍ₘ₊ⱼ₎ c)) =
  ∑_{j < L} (m choose j) ((a₍ₙ₊ⱼ₎ b)₍ₘ₊q₋ⱼ₎ c)`. -/
theorem borcherds [HasUniqueDiv V] (a b c : V) (m n q : ℤ) {K L : ℕ}
    (ha : ∀ j : ℕ, K ≤ j → ((A.field a)[[m + j]]) c = 0)
    (hb : ∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0)
    (hab : ∀ j : ℕ, L ≤ j → ((A.field a)[[n + j]]) b = 0) :
    ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
        (((A.field a)[[m + n - j]]) (((A.field b)[[q + j]]) c) -
          Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[m + j]]) c)) =
      ∑ j ∈ range L, Ring.choose m j •
        ((A.field (((A.field a)[[n + j]]) b))[[m + q - j]]) c := by
  have h := (A.borcherds_finsum a b c m n q).symm
  rw [finsum_eq_sum_range_of_forall_eq_zero (K := K) fun j hj ↦ by simp [ha j hj, hb j hj],
    (finsum_eq_sum_range_of_forall_eq_zero (K := L) fun j hj ↦ by simp [hab j hj])] at h
  rw [← h]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [mul_smul, Units.smul_def]

/-- **Existence form of the Borcherds identity**, producing a common finite cutoff `K : ℕ` for all
three mode sequences from field truncation. -/
theorem exists_borcherds [HasUniqueDiv V] (a b c : V) (m n q : ℤ) :
    ∃ K : ℕ,
      (∀ j : ℕ, K ≤ j → ((A.field a)[[m + j]]) c = 0) ∧
      (∀ j : ℕ, K ≤ j → ((A.field b)[[q + j]]) c = 0) ∧
      (∀ j : ℕ, K ≤ j → ((A.field a)[[n + j]]) b = 0) ∧
      ∑ j ∈ range K, (-1 : ℤ) ^ j • Ring.choose n j •
          (((A.field a)[[m + n - j]]) (((A.field b)[[q + j]]) c) -
            Int.negOnePow n • ((A.field b)[[n + q - j]]) (((A.field a)[[m + j]]) c)) =
        ∑ j ∈ range K, Ring.choose m j •
          ((A.field (((A.field a)[[n + j]]) b))[[m + q - j]]) c := by
  obtain ⟨Pₐ, hPₐ⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨P_b, hPb⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero c
  obtain ⟨P_ab, hPab⟩ := (A.field a).exists_forall_ncoeff_apply_eq_zero b
  have ha : ∀ j : ℕ, max Pₐ (max P_b P_ab) + m.natAbs + q.natAbs + n.natAbs ≤ j →
      ((A.field a)[[m + j]]) c = 0 := fun j hj ↦ hPₐ _ (by omega)
  have hb : ∀ j : ℕ, max Pₐ (max P_b P_ab) + m.natAbs + q.natAbs + n.natAbs ≤ j →
      ((A.field b)[[q + j]]) c = 0 := fun j hj ↦ hPb _ (by omega)
  have hab : ∀ j : ℕ, max Pₐ (max P_b P_ab) + m.natAbs + q.natAbs + n.natAbs ≤ j →
      ((A.field a)[[n + j]]) b = 0 := fun j hj ↦ hPab _ (by omega)
  exact ⟨_, ha, hb, hab, A.borcherds a b c m n q ha hb hab⟩

end FormalVertexAxioms

end TauCeti
