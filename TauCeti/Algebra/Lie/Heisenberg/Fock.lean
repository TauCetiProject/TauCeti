/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.Algebra.Lie.Heisenberg.Affine
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.PDeriv
public import TauCeti.RingTheory.Derivation.FirstOrder

/-!
# The Fock module of the Heisenberg Lie algebra

Let `H` be a module over a commutative ring `R` with a bilinear form `B`. The (uncharged)
**Fock module of the Heisenberg algebra** of `H` is the symmetric algebra

`π = Sym(⊕_{n > 0} H t⁻ⁿ) = SymmetricAlgebra R (ℕ →₀ H)`

(`TauCeti.HeisenbergFockSpace`), in which the generator `ι (single j h)` stands for the state
`h(-(j+1)) |0⟩` and the vacuum `|0⟩` is `1`. It is the bosonic Fock space of the negative
modes `t⁻¹ H[t⁻¹]`, not of `H` itself. The **mode operators** `h(n)` of
`TauCeti.HeisenbergFockSpace.modeOperator` act on it as follows:

* a negative mode `h(-(j+1))` multiplies by the generator `ι (single j h)`;
* the zero mode `h(0)` acts by zero;
* a positive mode `h(j+1)` acts by the derivation sending each generator `ι v` to the scalar
  `(j+1) B(h, v j)`, contracting against the negative mode of the same index.

When `B` is symmetric these operators satisfy the Heisenberg relations
`[h(m), k(n)] = m B(h, k) δ_{m+n,0}` (`TauCeti.HeisenbergFockSpace.modeOperator_commutator`), so
for an abelian Lie algebra `H` the Fock space is a representation of the Heisenberg Lie algebra
`TauCeti.HeisenbergAlgebra B hB` in which the central element acts by `1`
(`TauCeti.HeisenbergAlgebra.fockRepresentation`). For `m, n > 0`,

`h(n) k(-m) |0⟩ = n B(h, k) δ_{n,m} |0⟩`

(`TauCeti.HeisenbergFockSpace.modeOperator_modeOperator_one`). The Fock space is generated from
the vacuum by the negative modes (`TauCeti.HeisenbergFockSpace.eq_top_of_one_mem`), and every state
is killed by all sufficiently high modes
(`TauCeti.HeisenbergFockSpace.exists_forall_modeOperator_eq_zero`), so the fields
`h(z) = ∑ₙ h(n) z^{-n-1}` are lower truncated on every state.

The **translation** operator `T` of `TauCeti.HeisenbergFockSpace.translation` is the derivation with
`T h(-(j+1))|0⟩ = (j+1) h(-(j+2))|0⟩`, the derivation induced on the symmetric algebra by
`t⁻ⁿ ↦ -d/dt t⁻ⁿ`. It kills the vacuum and satisfies the translation covariance
`[T, h(n)] = -n h(n-1)` (`TauCeti.HeisenbergFockSpace.translation_commutator`).

The form `B` may be degenerate, including zero. The mode operators and their relations need no
characteristic assumption; the Fock representation, like `TauCeti.HeisenbergAlgebra`, needs `R`
to be additively torsion-free (`HasUniqueDiv R`). For `B = 0` every positive mode vanishes, while
`h(-1)|0⟩ = ι (single 0 h)` is nonzero when `h` is.

## Main definitions

* `TauCeti.HeisenbergFockSpace`: the Fock module `Sym(⊕_{n > 0} H t⁻ⁿ)` of the Heisenberg
  algebra.
* `TauCeti.HeisenbergFockSpace.modeOperator`: the action of the modes `h(n)` on the Fock space.
* `TauCeti.HeisenbergFockSpace.translation`: the translation operator `T`.
* `TauCeti.HeisenbergAlgebra.fockRepresentation`: the Fock representation of the Heisenberg Lie
  algebra.

## Main results

* `TauCeti.HeisenbergFockSpace.modeOperator_commutator`: the Heisenberg relations.
* `TauCeti.HeisenbergFockSpace.map_modeOperator`: isometries intertwine the modes.
* `TauCeti.HeisenbergAlgebra.fockRepresentation_mode` and
  `TauCeti.HeisenbergAlgebra.fockRepresentation_centralElement`: the modes act by the mode
  operators and the central element acts by `1`.
* `TauCeti.HeisenbergFockSpace.modeOperator_modeOperator_one`:
  `h(n) k(-m)|0⟩ = n B(h, k) δ_{n,m}|0⟩`.
* `TauCeti.HeisenbergFockSpace.eq_top_of_one_mem`: the negative modes generate the Fock space from
  the vacuum.
* `TauCeti.HeisenbergFockSpace.exists_forall_modeOperator_eq_zero`: every state is killed by all
  high modes.
* `TauCeti.HeisenbergFockSpace.translation_commutator`: the translation covariance
  `[T, h(n)] = -n h(n-1)`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge University Press (2007),
  §6.2.1, for the Fock representation of the Heisenberg Lie algebra.
* E. Frenkel and D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., American
  Mathematical Society (2004), §2.1, for the Fock representation and its translation operator.
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., American Mathematical Society (1998), §3.5,
  for the free boson.
-/

public section

noncomputable section

open SymmetricAlgebra
open LieAlgebra LieAlgebra.LoopAlgebra LieModule.Cohomology
open LieAlgebra.ofTwoCocycle (centralElement)

namespace TauCeti

variable (R H : Type*) [CommRing R] [AddCommGroup H] [Module R H]

/-- The (uncharged) **Fock module of the Heisenberg algebra** of a module `H`: the symmetric
algebra `Sym(⊕_{n > 0} H t⁻ⁿ)` on `ℕ →₀ H`, in which the generator `ι (single j h)` is the state
`h(-(j+1))|0⟩` and the vacuum `|0⟩` is `1`. -/
abbrev HeisenbergFockSpace : Type _ := SymmetricAlgebra R (ℕ →₀ H)

namespace HeisenbergFockSpace

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R H} (B : LinearMap.BilinForm R H)

/-- The derivation by which the positive mode `h(j+1)` acts: it sends each generator `ι v` to the
scalar `(j+1) B(h, v j)`. -/
def annihilation (j : ℕ) :
    H →ₗ[R] Derivation R (HeisenbergFockSpace R H) (HeisenbergFockSpace R H) :=
  pderiv ∘ₗ (((j : R) + 1) • LinearMap.lcomp R R (Finsupp.lapply j) ∘ₗ B)

/-- The positive mode `h(j+1)` sends the generator `ι v` to the scalar `(j+1) B(h, v j)`. -/
@[simp]
theorem annihilation_ι (j : ℕ) (h : H) (v : ℕ →₀ H) :
    annihilation B j h (ι R (ℕ →₀ H) v) =
      algebraMap R (HeisenbergFockSpace R H) (((j : R) + 1) * B h (v j)) := by
  simp [annihilation, Algebra.smul_def]

/-- The **mode operator** `h(n)` on the Fock space: for `n = -(j+1) < 0` multiplication by the
generator `ι (single j h)`, for `n = 0` zero, and for `n = j + 1 > 0` the derivation
`TauCeti.HeisenbergFockSpace.annihilation B j h`. -/
def modeOperator : ℤ → H →ₗ[R] Module.End R (HeisenbergFockSpace R H)
  | .ofNat 0 => 0
  | .ofNat (j + 1) =>
    { toFun h := (annihilation B j h : Module.End R (HeisenbergFockSpace R H))
      map_add' h k := by rw [map_add, Derivation.coe_add_linearMap]
      map_smul' r h := by rw [map_smul, Derivation.coe_smul_linearMap, RingHom.id_apply] }
  | .negSucc j =>
    LinearMap.mul R (HeisenbergFockSpace R H) ∘ₗ ι R (ℕ →₀ H) ∘ₗ Finsupp.lsingle j

/-- The negative mode `h(-(j+1))`, indexed by the constructor `Int.negSucc j`, is left
multiplication by the generator `ι (single j h)`. -/
theorem modeOperator_negSucc (j : ℕ) (h : H) :
    modeOperator B (Int.negSucc j) h =
      LinearMap.mulLeft R (ι R (ℕ →₀ H) (Finsupp.single j h)) := by
  rw [modeOperator]
  ext p
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.mul_apply',
    LinearMap.mulLeft_apply]

/-- The negative mode `h(-(j+1))` is left multiplication by the generator `ι (single j h)`. -/
theorem modeOperator_neg_natCast_sub_one (j : ℕ) (h : H) :
    modeOperator B (-(j : ℤ) - 1) h =
      LinearMap.mulLeft R (ι R (ℕ →₀ H) (Finsupp.single j h)) := by
  rw [show -(j : ℤ) - 1 = Int.negSucc j by omega, modeOperator_negSucc]

/-- The negative mode `h(-(j+1))` multiplies by the generator `ι (single j h)`. -/
@[simp]
theorem modeOperator_neg_natCast_sub_one_apply (j : ℕ) (h : H) (p : HeisenbergFockSpace R H) :
    modeOperator B (-(j : ℤ) - 1) h p = ι R (ℕ →₀ H) (Finsupp.single j h) * p := by
  rw [modeOperator_neg_natCast_sub_one, LinearMap.mulLeft_apply]

/-- The zero mode acts by zero. -/
@[simp]
theorem modeOperator_zero : modeOperator B 0 = 0 :=
  (rfl)

/-- The positive mode `h(j+1)`, indexed by the constructor `Int.ofNat (j + 1)`, acts by the
derivation `TauCeti.HeisenbergFockSpace.annihilation B j h`. -/
theorem modeOperator_ofNat_succ (j : ℕ) (h : H) :
    modeOperator B (Int.ofNat (j + 1)) h =
      (annihilation B j h : Module.End R (HeisenbergFockSpace R H)) := by
  rw [modeOperator, LinearMap.coe_mk, AddHom.coe_mk]

/-- The positive mode `h(j+1)` acts by the derivation
`TauCeti.HeisenbergFockSpace.annihilation B j h`. -/
theorem modeOperator_natCast_add_one (j : ℕ) (h : H) :
    modeOperator B ((j : ℤ) + 1) h =
      (annihilation B j h : Module.End R (HeisenbergFockSpace R H)) := by
  rw [← Nat.cast_succ, ← Int.ofNat_eq_natCast, modeOperator_ofNat_succ]

/-- The positive mode `h(j+1)` acts by the derivation
`TauCeti.HeisenbergFockSpace.annihilation B j h`. -/
@[simp]
theorem modeOperator_natCast_add_one_apply (j : ℕ) (h : H) (p : HeisenbergFockSpace R H) :
    modeOperator B ((j : ℤ) + 1) h p = annihilation B j h p := by
  rw [modeOperator_natCast_add_one, Derivation.coeFn_coe]

/-- A positive mode acts by a derivation of the Fock space. -/
theorem modeOperator_mul_of_pos {n : ℤ} (hn : 0 < n) (h : H) (p q : HeisenbergFockSpace R H) :
    modeOperator B n h (p * q) = p * modeOperator B n h q + q * modeOperator B n h p := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 1 := ⟨(n - 1).toNat, by omega⟩
  simp [Derivation.leibniz]

/-- The vacuum is killed by the nonnegative modes. -/
@[simp]
theorem modeOperator_one_of_nonneg {n : ℤ} (hn : 0 ≤ n) (h : H) :
    modeOperator B n h 1 = 0 := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j : ℕ, n = 0 ∨ n = j + 1 :=
    ⟨(n - 1).toNat, by omega⟩
  · simp
  · simp

/-- The positive mode `h(j+1)` contracts the generator `k(-(i+1))|0⟩` to `(j+1) B(h, k)` when
`i = j`, and kills it otherwise. -/
theorem annihilation_ι_single (j i : ℕ) (h k : H) :
    annihilation B j h (ι R (ℕ →₀ H) (Finsupp.single i k)) =
      if i = j then algebraMap R (HeisenbergFockSpace R H) (((j : R) + 1) * B h k) else 0 := by
  rw [annihilation_ι]
  split_ifs with hij
  · rw [hij, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij), map_zero, mul_zero, map_zero]

/-- **The Fock vacuum computation.** For `m, n > 0`, `h(n) k(-m)|0⟩ = n B(h, k) δ_{n,m}|0⟩`. -/
theorem modeOperator_modeOperator_one (j i : ℕ) (h k : H) :
    modeOperator B ((j : ℤ) + 1) h (modeOperator B (-(i : ℤ) - 1) k 1) =
      if i = j then algebraMap R (HeisenbergFockSpace R H) (((j : R) + 1) * B h k) else 0 := by
  rw [modeOperator_neg_natCast_sub_one_apply, mul_one, modeOperator_natCast_add_one_apply,
    annihilation_ι_single]

/-- Two positive modes commute: their commutator is a derivation killing the generators. -/
private theorem annihilation_commute (j i : ℕ) (h k : H) :
    (annihilation B j h : Module.End R (HeisenbergFockSpace R H)) * annihilation B i k -
        (annihilation B i k : Module.End R (HeisenbergFockSpace R H)) * annihilation B j h = 0 := by
  have : ⁅annihilation B j h, annihilation B i k⁆ = 0 := derivation_ext fun v ↦ by
    simp [Derivation.commutator_apply]
  rw [← LieRing.of_associative_ring_bracket, ← Derivation.commutator_coe_linear_map, this,
    Derivation.coe_zero_linearMap]

/-- The positive mode `h(j+1)` and the negative mode `k(-(i+1))` commute up to the scalar
`(j+1) B(h, k) δ_{i,j}`. -/
private theorem annihilation_commutator_mulLeft (j i : ℕ) (h k : H) :
    (annihilation B j h : Module.End R (HeisenbergFockSpace R H)) *
          LinearMap.mulLeft R (ι R (ℕ →₀ H) (Finsupp.single i k)) -
        LinearMap.mulLeft R (ι R (ℕ →₀ H) (Finsupp.single i k)) * annihilation B j h =
      if i = j then (((j : R) + 1) * B h k) • 1 else 0 := by
  rw [← LieRing.of_associative_ring_bracket, Derivation.lie_mulLeft, annihilation_ι_single]
  split_ifs
  · ext p
    simp [Algebra.smul_def]
    ring
  · ext p
    simp

/-- **The Heisenberg relations** on the Fock space: for a symmetric form `B`,
`[h(m), k(n)] = m B(h, k) δ_{m+n,0}`. -/
theorem modeOperator_commutator (hB : B.IsSymm) (m n : ℤ) (h k : H) :
    modeOperator B m h * modeOperator B n k - modeOperator B n k * modeOperator B m h =
      (if m + n = 0 then (m : R) * B h k else 0) • 1 := by
  rcases m with (_ | j) | j <;> rcases n with (_ | i) | i
  · simp
  · simp [modeOperator_zero]
  · simp [modeOperator_zero]
  · simp [modeOperator_zero]
    omega
  · rw [modeOperator_ofNat_succ, modeOperator_ofNat_succ, annihilation_commute,
      Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
    split_ifs with hc
    · omega
    · rw [zero_smul]
  · rw [modeOperator_ofNat_succ, modeOperator_negSucc, annihilation_commutator_mulLeft,
      Int.ofNat_eq_natCast]
    split_ifs with hij hij' hij'
    · subst hij
      congr 1
      push_cast
      ring
    · omega
    · omega
    · rw [zero_smul]
  · simp [modeOperator_zero]
  · rw [modeOperator_ofNat_succ, modeOperator_negSucc, ← neg_sub, annihilation_commutator_mulLeft,
      Int.ofNat_eq_natCast]
    split_ifs with hij hij' hij'
    · subst hij
      rw [← neg_smul, hB.eq k h]
      congr 1
      push_cast
      ring
    · omega
    · omega
    · rw [zero_smul, neg_zero]
  · rw [modeOperator_negSucc, modeOperator_negSucc]
    split_ifs with hc
    · omega
    ext p
    simp [mul_left_comm]

variable {B} in
/-- **Isometries intertwine the modes.** For an isometry `f : (H, B) → (H', B')`, the induced map
of Fock spaces carries `h(n) p` to `(f h)(n) f(p)`. -/
theorem map_modeOperator {H' : Type*} [AddCommGroup H'] [Module R H']
    {B' : LinearMap.BilinForm R H'} (f : B →bᵢ B') (n : ℤ) (h : H) (p : HeisenbergFockSpace R H) :
    SymmetricAlgebra.map R (Finsupp.mapRange.linearMap f.toLinearMap) (modeOperator B n h p) =
      modeOperator B' n (f h)
        (SymmetricAlgebra.map R (Finsupp.mapRange.linearMap f.toLinearMap) p) := by
  rcases n with (_ | j) | j
  · simp
  · rw [Int.ofNat_eq_natCast, Nat.cast_succ, modeOperator_natCast_add_one_apply,
      modeOperator_natCast_add_one_apply]
    -- Both sides are derivations along the induced algebra map, so compare them on generators.
    induction p using SymmetricAlgebra.induction with
    | algebraMap r => simp
    | ι v => simp
    | mul p q hp hq => simp [Derivation.leibniz, hp, hq]
    | add p q hp hq => simp [hp, hq]
  · simp [modeOperator_negSucc]

/-- **The negative modes generate the Fock space from the vacuum**: a submodule containing the
vacuum and stable under every negative mode is the whole Fock space. -/
theorem eq_top_of_one_mem (W : Submodule R (HeisenbergFockSpace R H)) (h1 : 1 ∈ W)
    (hW : ∀ n < 0, ∀ (h : H), ∀ p ∈ W, modeOperator B n h p ∈ W) : W = ⊤ := by
  have hmul (a : HeisenbergFockSpace R H) : ∀ p ∈ W, a * p ∈ W := by
    induction a using SymmetricAlgebra.induction with
    | algebraMap r => exact fun p hp ↦ by simpa [Algebra.smul_def] using W.smul_mem r hp
    | ι v =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => exact fun p hp ↦ by simpa [add_mul] using W.add_mem (hv p hp) (hw p hp)
      | single j h =>
        exact fun p hp ↦ by simpa using hW (-(j : ℤ) - 1) (by omega) h p hp
    | mul a b ha hb => exact fun p hp ↦ by simpa [mul_assoc] using ha _ (hb p hp)
    | add a b ha hb => exact fun p hp ↦ by simpa [add_mul] using W.add_mem (ha p hp) (hb p hp)
  exact eq_top_iff.mpr fun p _ ↦ by simpa using hmul p 1 h1

/-- **Smoothness of the Fock space**: every state is killed by all sufficiently high modes. -/
theorem exists_forall_modeOperator_eq_zero (p : HeisenbergFockSpace R H) :
    ∃ N : ℕ, ∀ n : ℤ, N < n → ∀ h : H, modeOperator B n h p = 0 := by
  suffices ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ h : H, annihilation B j h p = 0 by
    obtain ⟨N, hN⟩ := this
    refine ⟨N, fun n hn h ↦ ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 1 := ⟨(n - 1).toNat, by omega⟩
    exact hN j (by omega) h
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => exact ⟨0, fun j _ h ↦ by simp⟩
  | ι v =>
    refine ⟨v.support.sup (· + 1), fun j hj h ↦ ?_⟩
    have hv : v j = 0 := Finsupp.notMem_support_iff.mp fun hjv ↦ by
      have := Finset.le_sup (f := (· + 1)) hjv
      omega
    simp [hv]
  | mul a b ha hb =>
    obtain ⟨M, hM⟩ := ha
    obtain ⟨N, hN⟩ := hb
    exact ⟨max M N, fun j hj h ↦ by
      simp [Derivation.leibniz, hM j (le_of_max_le_left hj) h, hN j (le_of_max_le_right hj) h]⟩
  | add a b ha hb =>
    obtain ⟨M, hM⟩ := ha
    obtain ⟨N, hN⟩ := hb
    exact ⟨max M N, fun j hj h ↦ by
      simp [hM j (le_of_max_le_left hj) h, hN j (le_of_max_le_right hj) h]⟩

/-- The endomorphism `single j h ↦ (j+1) • single (j+1) h` of `ℕ →₀ H`, the action of `-d/dt` on
the negative powers `t^{-(j+1)}`. -/
private def translationShift : Module.End R (ℕ →₀ H) :=
  Finsupp.lsum R fun j ↦ ((j : R) + 1) • Finsupp.lsingle (j + 1)

/-- The **translation** operator `T` of the Fock space: the derivation with
`T h(-(j+1))|0⟩ = (j+1) h(-(j+2))|0⟩`. -/
def translation : Derivation R (HeisenbergFockSpace R H) (HeisenbergFockSpace R H) :=
  derivationOfEnd R (ℕ →₀ H) translationShift

/-- `T h(-(j+1))|0⟩ = (j+1) h(-(j+2))|0⟩`. -/
@[simp]
theorem translation_ι_single (j : ℕ) (h : H) :
    translation (ι R (ℕ →₀ H) (Finsupp.single j h)) =
      ((j : R) + 1) • ι R (ℕ →₀ H) (Finsupp.single (j + 1) h) := by
  rw [translation, derivationOfEnd_ι, translationShift, Finsupp.lsum_single, LinearMap.smul_apply,
    Finsupp.lsingle_apply, map_smul]

/-- **Translation covariance** of the modes: `[T, h(n)] = -n h(n-1)`. -/
theorem translation_commutator (n : ℤ) (h : H) :
    (translation (R := R) (H := H) : Module.End R (HeisenbergFockSpace R H)) *
          modeOperator B n h -
        modeOperator B n h *
          (translation (R := R) (H := H) : Module.End R (HeisenbergFockSpace R H)) =
      -(n : R) • modeOperator B (n - 1) h := by
  rcases n with (_ | j) | j
  · simp
  · rw [modeOperator_ofNat_succ, Int.ofNat_eq_natCast, Nat.cast_succ, add_sub_cancel_right,
      ← LieRing.of_associative_ring_bracket, ← Derivation.commutator_coe_linear_map]
    -- Both sides are derivations, so it suffices to compare them on the generators.
    rcases j with _ | i
    · have key : ⁅translation, annihilation B 0 h⁆ = 0 := derivation_ext_single fun l k ↦ by
        rw [Derivation.commutator_apply]
        simp
      rw [key, Derivation.coe_zero_linearMap, Nat.cast_zero, modeOperator_zero,
        LinearMap.zero_apply, smul_zero]
    · have key : ⁅translation, annihilation B (i + 1) h⁆ =
          -((i : R) + 2) • annihilation B i h := derivation_ext_single fun l k ↦ by
        rw [Derivation.commutator_apply]
        simp only [annihilation_ι_single, apply_ite, map_zero, Derivation.map_algebraMap, ite_self,
          zero_sub, translation_ι_single, smul_apply]
        by_cases hl : l = i
        · subst hl
          simp [Algebra.smul_def, map_ofNat]
          ring
        · simp [hl]
      rw [key, Derivation.coe_smul_linearMap, Nat.cast_succ, modeOperator_natCast_add_one]
      congr 1
      push_cast
      ring
  · rw [Int.negSucc_sub_one, modeOperator_negSucc, modeOperator_negSucc,
      ← LieRing.of_associative_ring_bracket, Derivation.lie_mulLeft, translation_ι_single]
    ext p
    simp [Algebra.smul_def, add_mul, mul_assoc, add_comm]

end HeisenbergFockSpace

namespace HeisenbergAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R H : Type*} [CommRing R] [HasUniqueDiv R] [LieRing H] [LieAlgebra R H]
  [IsLieAbelian H] (B : LinearMap.BilinForm R H) (hB : B.IsSymm)

/-- The underlying linear map of the Fock representation: a pair `(u, z)` of a Laurent polynomial
`u = ∑ₙ uₙ tⁿ` and a central coordinate `z` acts by `∑ₙ uₙ(n) + z`. -/
private def fockAction : HeisenbergAlgebra B hB →ₗ[R] Module.End R (HeisenbergFockSpace R H) :=
  (Finsupp.lsum R (HeisenbergFockSpace.modeOperator B) ∘ₗ (toFinsupp R ℤ H).toLinearMap) ∘ₗ
      (ofTwoCocycle.proj (heisenbergCocycle B hB)).toLinearMap +
    (LinearMap.smulRight (TrivialLieModule.equiv R (loopAlgebra R ℤ H) R).toLinearMap 1) ∘ₗ
      LinearMap.snd R _ _ ∘ₗ (ofProdLinearEquiv (heisenbergCocycle B hB)).symm.toLinearMap

private theorem fockAction_mode (n : ℤ) (h : H) :
    fockAction B hB (mode B hB n h) = HeisenbergFockSpace.modeOperator B n h := by
  simp only [fockAction, LinearMap.add_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    ofTwoCocycle.proj_apply, LinearEquiv.coe_coe, coe_ofProdLinearEquiv_symm, mode_apply,
    Equiv.symm_apply_apply, toFinsupp_single_tmul, Finsupp.lsum_single, LinearMap.snd_apply,
    map_zero, add_zero]

private theorem fockAction_centralElement :
    fockAction B hB (centralElement (heisenbergCocycle B hB)) = 1 := by
  simp [fockAction, ofTwoCocycle.proj_apply, coe_ofProdLinearEquiv_symm]

/-- The Fock action takes brackets to commutators. Both sides are bilinear, so it suffices to
compare them on modes and on the central element, where this is the Heisenberg relation. -/
private theorem fockAction_lie (x y : HeisenbergAlgebra B hB) :
    fockAction B hB ⁅x, y⁆ =
      fockAction B hB x * fockAction B hB y - fockAction B hB y * fockAction B hB x := by
  let F : HeisenbergAlgebra B hB →ₗ[R] HeisenbergAlgebra B hB →ₗ[R]
      Module.End R (HeisenbergFockSpace R H) :=
    LinearMap.mk₂ R (fun x y ↦ fockAction B hB ⁅x, y⁆ -
        (fockAction B hB x * fockAction B hB y - fockAction B hB y * fockAction B hB x))
      (fun x x' y ↦ by simp only [add_lie, map_add, add_mul, mul_add]; abel)
      (fun r x y ↦ by simp only [smul_lie, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub])
      (fun x y y' ↦ by simp only [lie_add, map_add, add_mul, mul_add]; abel)
      (fun r x y ↦ by simp only [lie_smul, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub])
  have hK (z : HeisenbergAlgebra B hB) : ⁅z, centralElement (heisenbergCocycle B hB)⁆ = 0 :=
    (LieModule.mem_maxTrivSubmodule R _ _ _).mp (ofTwoCocycle.centralElement_mem_center _) z
  have hF : F = 0 := by
    refine linearMap_ext B hB (fun m h ↦ linearMap_ext B hB (fun n k ↦ ?_) ?_)
      (linearMap_ext B hB (fun n k ↦ ?_) ?_)
    · simp only [F, LinearMap.mk₂_apply, lie_mode_mode, fockAction_mode, map_smul,
        fockAction_centralElement, HeisenbergFockSpace.modeOperator_commutator B hB, sub_self,
        LinearMap.zero_apply]
    · simp [F, hK, fockAction_centralElement]
    · rw [LinearMap.mk₂_apply, ← lie_skew, hK]
      simp [fockAction_centralElement]
    · simp [F]
  simpa [F, sub_eq_zero] using congr($hF x y)

/-- The **Fock representation** of the Heisenberg Lie algebra: the mode `h(n)` acts by
`TauCeti.HeisenbergFockSpace.modeOperator B n h` and the central element `K` acts by `1`. -/
def fockRepresentation : HeisenbergAlgebra B hB →ₗ⁅R⁆ Module.End R (HeisenbergFockSpace R H) where
  __ := fockAction B hB
  map_lie' {x y} := by
    rw [LieRing.of_associative_ring_bracket]
    exact fockAction_lie B hB x y

/-- The mode `h(n)` acts on the Fock space by the mode operator `h(n)`. -/
@[simp]
theorem fockRepresentation_mode (n : ℤ) (h : H) :
    fockRepresentation B hB (mode B hB n h) = HeisenbergFockSpace.modeOperator B n h :=
  fockAction_mode B hB n h

/-- The central element `K` acts on the Fock space by `1`. -/
@[simp]
theorem fockRepresentation_centralElement :
    fockRepresentation B hB (centralElement (heisenbergCocycle B hB)) = 1 :=
  fockAction_centralElement B hB

end HeisenbergAlgebra

end TauCeti
