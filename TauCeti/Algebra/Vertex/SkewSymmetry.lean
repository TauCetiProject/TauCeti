/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Skew symmetry in formal vertex algebras

For states `a` and `b` of a formal vertex algebra (`TauCeti.FormalVertexAxioms`) over a
torsion-free module, the products `a₍ₙ₎ b` are determined by the products `b₍ₘ₎ a` in the
opposite order: **skew symmetry** `Y(a,z) b = e^{zT} Y(b,-z) a`, which in modes reads
`a₍ₙ₎ b = ∑_{s ≥ 0} (-1)^{n+s+1} T^{(s)} (b₍ₙ₊ₛ₎ a)` with divided powers `T^{(s)} = Tˢ / s!`.
The sum is finite because `b₍ₖ₎ a = 0` for `k` large. Skew symmetry is one of the basic
identities of vertex algebra theory; for instance it makes the zero product `a₍₀₎ b`
skew-symmetric up to `T`-exact terms.

Without division, the divided power `T^{(s)} c` is represented by the creation coefficient
`c₍₋ₛ₋₁₎|0⟩`, whose `s!`-fold multiple is `Tˢ c`
(`TauCeti.FormalVertexAxioms.factorial_smul_ncoeff_field_apply_vacuum`). The identities are
stated in this division-free form over a torsion-free module, as well as in the `Tˢ / s!` form over
`ℚ` (`TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum_translation_pow`,
`TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry`).

## Main results

* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_ncoeff_field_apply_vacuum_eq_sum`: a mode moves
  past a creation vector by `b₍q₎ (a₍ₚ₎|0⟩) = ∑_l (q choose l) (b₍q₋ₗ₎ a)₍ₚ₊ₗ₎|0⟩`, the
  coefficient form of `Y(b,w) e^{zT} a = e^{zT} Y(b,w-z) a`.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum_ncoeff_field_apply_vacuum` and
  `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum_vacuum`: finite-sum skew symmetry
  `a₍ₙ₎ b = ∑_s (-1)^{n+s+1} (b₍ₙ₊ₛ₎ a)₍₋ₛ₋₁₎|0⟩`.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_eq_sum_translation_pow`: finite-sum `e^{zT}` form
  over `ℚ`.
* `TauCeti.FormalVertexAxioms.ncoeff_zero_field_apply_add_mem_range_translation`:
  `a₍₀₎ b + b₍₀₎ a ∈ LinearMap.range A.translation`.
* `TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry_vacuum` and
  `TauCeti.FormalVertexAxioms.ncoeff_field_apply_skewSymmetry`: `finsum` skew symmetry in
  division-free and `ℚ`-algebra forms.

## Implementation notes

The proof is the coefficient form of the standard argument. Locality of order `N` applied to
the vacuum gives `a₍ₙ₎ b` as the `w⁰`-coefficient of `(z-w)ᴺ Y(b,w) Y(a,z)|0⟩`
(`TauCeti.FormalVertexAxioms.ncoeff_add_apply_eq_sum`). Moving `Y(b,w)` past the creation series
`Y(a,z)|0⟩ = e^{zT} a` rewrites this as the `w⁰`-coefficient of
`(-1)ᴺ e^{zT} (w-z)ᴺ Y(b,w-z) a`, and once `N` exceeds the order at which `b₍ₖ₎ a` vanishes,
that coefficient is `zᴺ e^{zT} Y(b,-z) a`. Binomial coefficients `q choose l` with integer `q`
are Mathlib's `Ring.choose`, and signs `(-1)^{n+s+1}` with integer exponents are
`Int.negOnePow`.

## References

* V. Kac, *Introduction to vertex algebras, Poisson vertex algebras, and integrable Hamiltonian
  PDE*, in *Perspectives in Lie theory*, Springer INdAM Ser. 19 (2017), equation (3.24).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.1 and §3.2.
-/

public section

open scoped VertexOperator
open Finset

namespace TauCeti.FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (A : FormalVertexAxioms R V)

/-- `ncoeff_field_apply_ncoeff_field_apply_vacuum_eq_sum` for the creation vectors
`a₍₋ₖ₋₁₎|0⟩ = T^{(k)} a`. -/
private theorem ncoeff_field_apply_ncoeff_field_apply_vacuum_neg_eq_sum [HasUniqueDiv V]
    (a b : V) (k : ℕ) (q : ℤ) {K : ℕ} (hK : k + 1 ≤ K) :
    ((A.field b)[[q]]) (((A.field a)[[-k - 1]]) A.vacuum) =
      ∑ l ∈ range K, Ring.choose q l •
        ((A.field (((A.field b)[[q - l]]) a))[[-k - 1 + l]]) A.vacuum := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  induction k generalizing q with
  | zero =>
    rw [sum_range_succ', sum_eq_zero fun l _ ↦ ?_]
    · simp
    · rw [A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by omega), smul_zero]
  | succ k ih =>
    obtain ⟨X, hX⟩ : ∃ X : ℕ → V, ∀ l : ℕ,
        X l = ((A.field (((A.field b)[[q - l]]) a))[[-((k + 1 : ℕ) : ℤ) - 1 + l]]) A.vacuum :=
      ⟨_, fun _ ↦ rfl⟩
    -- `T (a₍₋ₖ₋₁₎|0⟩) = (k + 1) • a₍₋ₖ₋₂₎|0⟩`
    have hT : A.translation (((A.field a)[[-k - 1]]) A.vacuum) =
        (k + 1) • ((A.field a)[[-((k + 1 : ℕ) : ℤ) - 1]]) A.vacuum := by
      rw [A.translation_ncoeff_apply_vacuum, ← natCast_zsmul,
        show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring,
        show -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring]
    -- `T` lowers the vacuum index of each term of `b₍q₎ (a₍₋ₖ₋₁₎|0⟩)`
    have hTl (l : ℕ) : A.translation
        (((A.field (((A.field b)[[q - l]]) a))[[-k - 1 + l]]) A.vacuum) =
          ((k + 1 : ℤ) - l) • X l := by
      rw [A.translation_ncoeff_apply_vacuum, show -(-(k : ℤ) - 1 + l) = (k + 1 : ℤ) - l by ring,
        show -(k : ℤ) - 1 + l - 1 = -((k + 1 : ℕ) : ℤ) - 1 + l by push_cast; ring, hX]
    have hl (l : ℕ) : ((A.field (((A.field b)[[q - 1 - l]]) a))[[-k - 1 + l]]) A.vacuum =
        X (l + 1) := by
      rw [hX, show q - ((l + 1 : ℕ) : ℤ) = q - 1 - l by push_cast; ring,
        show -((k + 1 : ℕ) : ℤ) - 1 + ((l + 1 : ℕ) : ℤ) = -k - 1 + l by push_cast; ring]
    -- the Pascal-type identity `(l + 1) C(q, l + 1) = q C(q - 1, l)`
    have hchoose (l : ℕ) : ((l + 1 : ℕ) : ℤ) * Ring.choose q (l + 1) =
        q * Ring.choose (q - 1) l := by
      simpa [Ring.choose_one_right] using Ring.choose_smul_choose q (n := l + 1) (k := 1) (by omega)
    have hXK : X (K + 1) = 0 :=
      (hX _).trans (A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by push_cast; omega))
    apply nsmul_right_injective (Nat.succ_ne_zero k)
    dsimp only
    rw [← map_nsmul, ← hT, A.ncoeff_field_apply_translation, ih q (by omega),
      ih (q - 1) (by omega), map_sum, smul_sum, smul_sum]
    simp only [map_zsmul, hTl, hl, ← hX]
    have h₂ : ∑ l ∈ range (K + 1), q • Ring.choose (q - 1) l • X (l + 1) =
        ∑ l ∈ range (K + 1), ((l : ℤ) * Ring.choose q l) • X l := by
      rw [sum_range_eq_add_sum_range_succ (fun l ↦ ((l : ℤ) * Ring.choose q l) • X l)
        (by simp [hXK]), Nat.cast_zero, zero_mul, zero_smul, zero_add]
      exact sum_congr rfl fun l _ ↦ by rw [smul_smul, ← hchoose l]
    rw [h₂, ← sum_add_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    module

/-- A mode moves past a creation vector:
`b₍q₎ (a₍ₚ₎|0⟩) = ∑_{l < K} (q choose l) (b₍q₋ₗ₎ a)₍ₚ₊ₗ₎|0⟩` for every `K ≥ -p`; the terms with
`l ≥ -p` vanish. Since `a₍₋ₖ₋₁₎|0⟩ = T^{(k)} a`, this is
`b₍q₎ T^{(k)} a = ∑_l (q choose l) T^{(k-l)} (b₍q₋ₗ₎ a)`, the coefficient form of
`Y(b,w) e^{zT} a = e^{zT} Y(b,w-z) a`. -/
theorem ncoeff_field_apply_ncoeff_field_apply_vacuum_eq_sum [HasUniqueDiv V]
    (a b : V) (q p : ℤ) {K : ℕ} (hK : -p ≤ K) :
    ((A.field b)[[q]]) (((A.field a)[[p]]) A.vacuum) =
      ∑ l ∈ range K, Ring.choose q l •
        ((A.field (((A.field b)[[q - l]]) a))[[p + l]]) A.vacuum := by
  rcases lt_or_ge p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -k - 1 := ⟨(-p - 1).toNat, by omega⟩
    exact A.ncoeff_field_apply_ncoeff_field_apply_vacuum_neg_eq_sum a b k q (by omega)
  · rw [A.ncoeff_field_apply_vacuum_of_nonneg _ _ hp, map_zero]
    exact (sum_eq_zero fun l _ ↦ by
      rw [A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by omega), smul_zero]).symm

/-- The coefficient of `z^{-p-1} w^{-q-1}` in `(z-w)ᴺ Y(b,w) Y(a,z)|0⟩` equals the
corresponding coefficient of `(-1)ᴺ e^{zT} (w-z)ᴺ Y(b,w-z) a`. -/
private theorem sum_antidiagonal_ncoeff_field_apply_ncoeff_field_apply_vacuum [HasUniqueDiv V]
    (a b : V) (N : ℕ) (q p : ℤ) {K : ℕ} (hK : -p ≤ K) :
    ∑ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((A.field b)[[q + ij.2]]) (((A.field a)[[p + ij.1]]) A.vacuum) =
      (-1 : ℤ) ^ N • ∑ l ∈ range K, Ring.choose q l •
        ((A.field (((A.field b)[[q + N - l]]) a))[[p + l]]) A.vacuum := by
  induction N generalizing q p with
  | zero =>
    simpa using A.ncoeff_field_apply_ncoeff_field_apply_vacuum_eq_sum a b q p hK
  | succ N ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (fun i j ↦ (-1 : ℤ) ^ j •
      ((A.field b)[[q + j]]) (((A.field a)[[p + i]]) A.vacuum)) N]
    -- Pascal's rule splits the order-`N + 1` sum into the order-`N` sums at `(q + 1, p)` and
    -- `(q, p + 1)`.
    have e₁ : ∀ ij ∈ antidiagonal N, N.choose ij.1 • (-1 : ℤ) ^ (ij.2 + 1) •
        ((A.field b)[[q + ↑(ij.2 + 1)]]) (((A.field a)[[p + ij.1]]) A.vacuum) =
        -(N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          ((A.field b)[[q + 1 + ij.2]]) (((A.field a)[[p + ij.1]]) A.vacuum)) := by
      intro ij _
      rw [show q + ((ij.2 + 1 : ℕ) : ℤ) = q + 1 + ij.2 by push_cast; ring, pow_succ]
      module
    have e₂ : ∀ ij ∈ antidiagonal N, N.choose ij.2 • (-1 : ℤ) ^ ij.2 •
        ((A.field b)[[q + ij.2]]) (((A.field a)[[p + ↑(ij.1 + 1)]]) A.vacuum) =
        N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          ((A.field b)[[q + ij.2]]) (((A.field a)[[p + 1 + ij.1]]) A.vacuum) := by
      intro ij hij
      rw [Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm,
        show p + ((ij.1 + 1 : ℕ) : ℤ) = p + 1 + ij.1 by push_cast; ring]
    rw [sum_congr rfl e₁, sum_congr rfl e₂, sum_neg_distrib, ih (q + 1) p hK,
      ih q (p + 1) (by omega)]
    obtain ⟨W, hW⟩ : ∃ W : ℕ → V, ∀ l : ℕ,
        W l = ((A.field (((A.field b)[[q + 1 + N - l]]) a))[[p + l]]) A.vacuum :=
      ⟨_, fun _ ↦ rfl⟩
    have hW₁ : ∀ l : ℕ, ((A.field (((A.field b)[[q + ↑(N + 1) - l]]) a))[[p + l]]) A.vacuum =
        W l := fun l ↦ by rw [hW, show q + ((N + 1 : ℕ) : ℤ) = q + 1 + N by push_cast; ring]
    have hW₂ : ∀ l : ℕ, ((A.field (((A.field b)[[q + N - l]]) a))[[p + 1 + l]]) A.vacuum =
        W (l + 1) := fun l ↦ by
      rw [hW, show q + 1 + N - ((l + 1 : ℕ) : ℤ) = q + N - l by push_cast; ring,
        show p + ((l + 1 : ℕ) : ℤ) = p + 1 + l by push_cast; ring]
    simp only [hW₁, hW₂, ← hW]
    -- Pascal's rule for `Ring.choose (q + 1)`, with the boundary term `W K = 0`.
    have hkey : ∑ l ∈ range K, Ring.choose (q + 1) l • W l =
        ∑ l ∈ range K, Ring.choose q l • W l + ∑ l ∈ range K, Ring.choose q l • W (l + 1) := by
      have hWK : W K = 0 := by
        rw [hW]
        exact A.ncoeff_field_apply_vacuum_of_nonneg _ _ (by omega)
      rw [sum_range_eq_add_sum_range_succ (fun l ↦ Ring.choose (q + 1) l • W l) (by simp [hWK]),
        sum_range_eq_add_sum_range_succ (fun l ↦ Ring.choose q l • W l) (by simp [hWK])]
      simp only [Ring.choose_succ_succ, Ring.choose_zero_right, add_smul, sum_add_distrib]
      abel
    rw [hkey, pow_succ]
    module

/-- **Skew symmetry** `Y(a,z) b = e^{zT} Y(b,-z) a`, in modes and without division:
`a₍ₙ₎ b = ∑_{s < M} (-1)^{n+s+1} (b₍ₙ₊ₛ₎ a)₍₋ₛ₋₁₎|0⟩` whenever `b₍ₖ₎ a = 0` for all `k ≥ n + M`.
Here `(b₍ₙ₊ₛ₎ a)₍₋ₛ₋₁₎|0⟩` is the divided power `T^{(s)} (b₍ₙ₊ₛ₎ a)`. -/
theorem ncoeff_field_apply_eq_sum_ncoeff_field_apply_vacuum [HasUniqueDiv V] (a b : V) (n : ℤ)
    (M : ℕ) (hM : ∀ k : ℤ, n + M ≤ k → ((A.field b)[[k]]) a = 0) :
    ((A.field a)[[n]]) b = ∑ s ∈ range M, (n + s + 1).negOnePow •
      ((A.field (((A.field b)[[n + s]]) a))[[-s - 1]]) A.vacuum := by
  obtain ⟨N₀, hN₀⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨N, hN, hnN⟩ : ∃ N : ℕ, N₀ ≤ N ∧ n + M ≤ N :=
    ⟨max N₀ (n + M).toNat, le_max_left _ _, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (K : ℤ) = N - n := ⟨(N - n).toNat, by omega⟩
  have h := A.ncoeff_add_apply_eq_sum (hN₀.mono hN) (n - N)
  rw [sub_add_cancel] at h
  rw [h, A.sum_antidiagonal_ncoeff_field_apply_ncoeff_field_apply_vacuum a b N (-1) (n - N)
    (K := K) (by omega), smul_sum, ← sum_range_reflect]
  refine (sum_subset (range_mono (by omega : M ≤ K)) fun s hs hsM ↦ ?_).symm.trans
    (sum_congr rfl fun s hs ↦ ?_)
  · rw [mem_range] at hs hsM
    simp [hM (-1 + N - ↑(K - 1 - s)) (by omega)]
  · rw [mem_range] at hs
    -- the sign `(-1)ᴺ (-1 choose (K - 1 - s))` is `(-1)^{n+s+1}`
    have hsign : (-1 : ℤ) ^ N * Ring.choose (-1 : ℤ) (K - 1 - s) = (n + s + 1).negOnePow := by
      have hchoose : Ring.choose (-1 : ℤ) (K - 1 - s) = ((K - 1 - s : ℕ) : ℤ).negOnePow := by
        simpa [Ring.choose_natCast, Units.smul_def] using Ring.choose_neg (1 : ℤ) (K - 1 - s)
      rw [hchoose, ← Int.coe_negOnePow_natCast, ← Units.val_mul, ← Int.negOnePow_add,
        Units.val_inj, Int.negOnePow_eq_iff]
      exact ⟨(N : ℤ) - n - s - 1, by omega⟩
    rw [show -1 + (N : ℤ) - ↑(K - 1 - s) = n + s by omega,
      show n - (N : ℤ) + ↑(K - 1 - s) = -s - 1 by omega, smul_smul, hsign, Units.smul_def]

/-- **Skew symmetry (division-free form).** Over any module with unique divisibility, for any
cutoff `K : ℕ` above which `b₍ₙ₊ⱼ₎ a = 0`,
`a₍ₙ₎ b = ∑_{j < K} (-1)^{n + j + 1} (b₍ₙ₊ⱼ₎ a)₍₋ⱼ₋₁₎|0⟩`. -/
theorem ncoeff_field_apply_eq_sum_vacuum [HasUniqueDiv V] (a b : V) (n : ℤ) {K : ℕ}
    (hba : ∀ j : ℕ, K ≤ j → ((A.field b)[[n + j]]) a = 0) :
    ((A.field a)[[n]]) b =
      ∑ j ∈ range K, Int.negOnePow (n + j + 1) •
        ((A.field (((A.field b)[[n + j]]) a))[[-j - 1]]) A.vacuum := by
  rw [A.ncoeff_field_apply_eq_sum_ncoeff_field_apply_vacuum a b n K fun k hk ↦ by
    have hk' : k = n + ((k - n).toNat : ℤ) := by omega
    rw [hk']
    exact hba (k - n).toNat (by omega)]

/-- **Skew symmetry (`e^{zT}` form).** Over a `ℚ`-module, for any cutoff `K : ℕ` above which
`b₍ₙ₊ⱼ₎ a = 0`, `a₍ₙ₎ b = ∑_{j < K} (-1)^{n + j + 1} (j!)⁻¹ • Tʲ (b₍ₙ₊ⱼ₎ a)`. -/
theorem ncoeff_field_apply_eq_sum_translation_pow [Module ℚ V] (a b : V) (n : ℤ) {K : ℕ}
    (hba : ∀ j : ℕ, K ≤ j → ((A.field b)[[n + j]]) a = 0) :
    ((A.field a)[[n]]) b =
      ∑ j ∈ range K, Int.negOnePow (n + j + 1) • (j.factorial : ℚ)⁻¹ •
        (A.translation ^ j) (((A.field b)[[n + j]]) a) := by
  have : HasUniqueDiv V := .of_module_rat V
  rw [A.ncoeff_field_apply_eq_sum_vacuum a b n hba]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [A.ncoeff_field_apply_vacuum_neg]

/-- Over a `ℚ`-module, the `0`-th product is skew-symmetric modulo `T(V)`:
`a₍₀₎ b + b₍₀₎ a ∈ LinearMap.range A.translation`. Together with `ncoeff_zero_field_ncoeff_apply`,
`ncoeff_field_translation`, and `translation_ncoeff_apply`, this supplies the identities needed for
the induced Lie bracket on `V / T(V)`. -/
theorem ncoeff_zero_field_apply_add_mem_range_translation [Module ℚ V] (a b : V) :
    ((A.field a)[[0]]) b + ((A.field b)[[0]]) a ∈ LinearMap.range A.translation := by
  obtain ⟨P, hP⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  rw [A.ncoeff_field_apply_eq_sum_translation_pow a b 0 (K := P + 1)
      (fun j hj ↦ by simpa using hP j (by omega)),
    sum_range_succ']
  simp only [Nat.cast_zero, add_zero, zero_add, Int.negOnePow_one, Units.neg_smul, one_smul,
    Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_apply_eq_self, neg_add_cancel_right]
  refine Submodule.sum_mem (LinearMap.range A.translation) fun j _ ↦ ?_
  refine ⟨Int.negOnePow (((j + 1 : ℕ) : ℤ) + 1) • ((j + 1).factorial : ℚ)⁻¹ •
      (A.translation ^ j) (((A.field b)[[(j + 1 : ℕ)]]) a), ?_⟩
  simp only [Units.smul_def]
  rw [map_zsmul, map_rat_smul, pow_succ', mul_apply_eq_comp]

/-- **Skew symmetry (division-free `finsum` form):**
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (b₍ₙ₊ᵢ₎ a)₍₋ᵢ₋₁₎|0⟩`. -/
theorem ncoeff_field_apply_skewSymmetry_vacuum [HasUniqueDiv V] (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        ((A.field (((A.field b)[[n + i]]) a))[[-(i : ℤ) - 1]]) A.vacuum := by
  obtain ⟨K, hK⟩ := (A.field b).exists_forall_ncoeff_apply_eq_zero a
  let M := ((K : ℤ) - n).toNat
  have hM : ∀ k : ℤ, n + M ≤ k → ((A.field b)[[k]]) a = 0 := fun k hk ↦ hK k (by omega)
  rw [TauCeti.finsum_eq_sum_range_of_forall_eq_zero (K := M) fun i hi ↦ by
      simp [hM (n + i) (by omega)],
    A.ncoeff_field_apply_eq_sum_ncoeff_field_apply_vacuum a b n M hM]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul]

/-- **Skew symmetry (`ℚ`-algebra `finsum` form):**
`a₍ₙ₎ b = ∑ᶠ i : ℕ, -(-1)ⁿ⁺ⁱ (i!)⁻¹ Tⁱ (b₍ₙ₊ᵢ₎ a)`. -/
theorem ncoeff_field_apply_skewSymmetry [Algebra ℚ R] (a b : V) (n : ℤ) :
    ((A.field a)[[n]]) b =
      ∑ᶠ i : ℕ, (-((n + i).negOnePow : ℤ)) •
        (algebraMap ℚ R (i.factorial : ℚ)⁻¹ • (A.translation ^ i) (((A.field b)[[n + i]]) a)) := by
  let : Module ℚ V := Module.compHom V (algebraMap ℚ R)
  have : HasUniqueDiv V := .of_module_rat V
  rw [A.ncoeff_field_apply_skewSymmetry_vacuum a b n]
  exact finsum_congr fun i ↦ by rw [A.ncoeff_field_neg_succ_apply_vacuum]

end TauCeti.FormalVertexAxioms
