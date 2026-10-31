/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Basic.Finite.Prod

/-!
# The `k`-kernel of a sequence and Eilenberg's theorem

The `k`-kernel of a sequence `a : ℕ → Δ` is the set of its subsequences `n ↦ a (k ^ e * n + r)`
with `r < k ^ e`. Eilenberg's theorem characterises the `k`-automatic sequences, for `2 ≤ k`, as
those with a finite `k`-kernel. This is the form in which automaticity is established in the
proof of Christol's theorem, where the kernel of the coefficient sequence of an algebraic power
series is the orbit of the series under the Cartier operators, and in the comparison of
automaticity in the bases `k` and `k ^ m`.

The kernel is closed under the transitions `b ↦ (n ↦ b (k * n + d))` with `d < k`, so it is the
state set of an automaton with output `b ↦ b 0`, the kernel automaton `TauCeti.kernelDFAO`.
Reading the digits of `n` least significant digit first from the state `a`, it outputs `a n`;
it does so on every base-`k` representation of `n`, including those padded with trailing zeros.

## Main definitions and results

* `TauCeti.kernel k a`: the `k`-kernel of `a`.
* `TauCeti.self_mem_kernel`, `TauCeti.kernel_subset`: a sequence lies in its kernel, and the
  kernel of a kernel element is contained in the kernel.
* `TauCeti.kernelDFAO k a`: the kernel automaton, and
  `TauCeti.output_eval_kernelDFAO`: on any word of digits it outputs `a` at the value of the word.
* `TauCeti.isAutomatic_iff_finite_kernel`: **Eilenberg's theorem**, for `2 ≤ k` a sequence is
  `k`-automatic if and only if its `k`-kernel is finite.

## References

* Jakub Byszewski, Jakub Konieczny, *Automatic sequences and generalised polynomials*,
  Canad. J. Math. 72 (2020), Section 1, Definition 1.4.
* Andrew Bridy, *Automatic sequences and curves over finite fields*, Algebra & Number Theory
  11 (2017), Section 2.1, Theorem 2.2.
* Eric Rowland, Manon Stipulanti, Reem Yassawi, *An elementary proof of Bridy's theorem*,
  Section 3.
-/

public section

universe u

namespace TauCeti

variable {k : ℕ} {Δ : Type u} {a b : ℕ → Δ}

/-- The **`k`-kernel** of a sequence `a`: the set of its subsequences `n ↦ a (k ^ e * n + r)` with
`e : ℕ` and `r < k ^ e`. -/
def kernel (k : ℕ) (a : ℕ → Δ) : Set (ℕ → Δ) :=
  {b | ∃ e r : ℕ, r < k ^ e ∧ b = fun n ↦ a (k ^ e * n + r)}

/-- Membership in the `k`-kernel, unfolded. -/
theorem mem_kernel : b ∈ kernel k a ↔ ∃ e r : ℕ, r < k ^ e ∧ b = fun n ↦ a (k ^ e * n + r) :=
  Iff.rfl

/-- A sequence belongs to its own kernel, with `e = 0` and `r = 0`. -/
@[simp]
theorem self_mem_kernel (k : ℕ) (a : ℕ → Δ) : a ∈ kernel k a :=
  ⟨0, 0, by simp, by simp⟩

/-- The subsequence `n ↦ a (k * n + d)` with `d < k` belongs to the `k`-kernel of `a`. -/
theorem apply_mul_add_mem_kernel {d : ℕ} (hd : d < k) : (fun n ↦ a (k * n + d)) ∈ kernel k a :=
  ⟨1, d, by simpa using hd, by simp⟩

/-- The kernel of an element of the kernel of `a` is contained in the kernel of `a`. -/
theorem kernel_subset (hb : b ∈ kernel k a) : kernel k b ⊆ kernel k a := by
  rintro c ⟨f, s, hs, rfl⟩
  obtain ⟨e, r, hr, rfl⟩ := hb
  refine ⟨e + f, k ^ e * s + r, ?_, funext fun n ↦ congrArg a (by ring)⟩
  calc k ^ e * s + r < k ^ e * (s + 1) := by rw [mul_add_one]; omega
    _ ≤ k ^ e * k ^ f := Nat.mul_le_mul_left _ hs
    _ = k ^ (e + f) := (pow_add k e f).symm

/-- The kernel of a constant sequence is the singleton of that sequence. -/
@[simp]
theorem kernel_const (k : ℕ) (x : Δ) : kernel k (fun _ : ℕ ↦ x) = {fun _ ↦ x} := by
  refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 (self_mem_kernel k _))
  rintro _ ⟨e, r, -, rfl⟩
  exact Set.mem_singleton _

/-! ### The kernel automaton -/

/-- The **kernel automaton** of `a`: its states are the elements of the `k`-kernel of `a`, its
initial state is `a`, its output is the value at `0`, and on the digit `d` it moves from `b` to
`n ↦ b (k * n + d)`. -/
def kernelDFAO (k : ℕ) (a : ℕ → Δ) : DFAO (Fin k) (kernel k a) Δ where
  step b d := ⟨fun n ↦ b.1 (k * n + d), kernel_subset b.2 (apply_mul_add_mem_kernel d.2)⟩
  start := ⟨a, self_mem_kernel k a⟩
  output b := b.1 0

@[simp]
theorem coe_kernelDFAO_step (b : kernel k a) (d : Fin k) :
    ((kernelDFAO k a).step b d : ℕ → Δ) = fun n ↦ b.1 (k * n + d) :=
  (rfl)

@[simp]
theorem coe_kernelDFAO_start : ((kernelDFAO k a).start : ℕ → Δ) = a :=
  (rfl)

@[simp]
theorem kernelDFAO_output (b : kernel k a) : (kernelDFAO k a).output b = b.1 0 :=
  (rfl)

/-- From the state `b`, after reading the word `w` the kernel automaton is in the state
`n ↦ b (k ^ |w| * n + v)`, where `v` is the value of `w` read least significant digit first. -/
@[simp]
theorem coe_kernelDFAO_evalFrom (b : kernel k a) (w : List (Fin k)) :
    ((kernelDFAO k a).evalFrom b w : ℕ → Δ) =
      fun n ↦ b.1 (k ^ w.length * n + Nat.ofDigits k (w.map Fin.val)) := by
  induction w generalizing b with
  | nil => simp
  | cons d w ih =>
    rw [DFAO.evalFrom_cons, ih]
    funext n
    simp only [coe_kernelDFAO_step, List.length_cons, List.map_cons, Nat.ofDigits_cons]
    exact congrArg b.1 (by ring)

/-- After reading the word `w` the kernel automaton of `a` is in the state
`n ↦ a (k ^ |w| * n + v)`, where `v` is the value of `w` read least significant digit first. -/
@[simp]
theorem coe_kernelDFAO_eval (w : List (Fin k)) :
    ((kernelDFAO k a).eval w : ℕ → Δ) =
      fun n ↦ a (k ^ w.length * n + Nat.ofDigits k (w.map Fin.val)) := by
  simp [DFAO.eval_eq_evalFrom]

/-- The kernel automaton of `a` outputs `a` at the value of any word of base-`k` digits, read
least significant digit first. Trailing zeros are allowed: the output only depends on the value
of the word. -/
theorem output_eval_kernelDFAO (w : List (Fin k)) :
    (kernelDFAO k a).output ((kernelDFAO k a).eval w) = a (Nat.ofDigits k (w.map Fin.val)) := by
  simp

/-! ### Eilenberg's theorem -/

variable [NeZero k]

/-- A `k`-automatic sequence has a finite `k`-kernel. -/
theorem IsAutomatic.finite_kernel (ha : IsAutomatic k a) : (kernel k a).Finite := by
  obtain rfl | hk : k = 1 ∨ 2 ≤ k := by
    have := NeZero.ne k
    omega
  · -- In base one the kernel is the singleton of `a`.
    refine (Set.finite_singleton a).subset ?_
    rintro _ ⟨e, r, hr, rfl⟩
    obtain rfl : r = 0 := by simpa using hr
    simp
  have hrange := ha.finite_range
  obtain ⟨σ, _, M, hM⟩ := isAutomatic_iff.1 ha
  -- The kernel element with exponent `e` and residue `r` is determined by the value `a r` and the
  -- state reached on the digits of `r` padded with zeros to length `e`.
  let F : σ × Δ → ℕ → Δ := fun p n ↦
    if n = 0 then p.2 else M.output (M.evalFrom p.1 ((Nat.digits k n).map (Fin.ofNat k)))
  refine ((Set.finite_univ.prod hrange).image F).subset ?_
  rintro _ ⟨e, r, hr, rfl⟩
  refine ⟨(M.eval ((Nat.digits k r ++ List.replicate (e - (Nat.digits k r).length) 0).map
    (Fin.ofNat k)), a r), ⟨trivial, r, rfl⟩, funext fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F]
  -- For `n ≠ 0` the digits of `k ^ e * n + r` are those of `r`, padded with zeros to length `e`,
  -- followed by those of `n`.
  have hdigits : Nat.digits k (k ^ e * n + r) =
      Nat.digits k r ++ List.replicate (e - (Nat.digits k r).length) 0 ++ Nat.digits k n := by
    rw [Nat.digits_append_zeroes_append_digits hk (Nat.pos_of_ne_zero hn),
      Nat.add_sub_cancel' ((Nat.digits_length_le_iff hk r).2 hr), add_comm]
  simp only [F, hn, ite_false, hM, hdigits, List.map_append, DFAO.eval_append]

/-- For `2 ≤ k`, a sequence with a finite `k`-kernel is `k`-automatic: the kernel automaton
computes it. -/
theorem isAutomatic_of_finite_kernel (hk : 2 ≤ k) (h : (kernel k a).Finite) :
    IsAutomatic k a := by
  have := h.to_subtype
  have hw (n : ℕ) : ((Nat.digits k n).map (Fin.ofNat k)).map Fin.val = Nat.digits k n := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (Nat.digits k n)]
    refine List.map_congr_left fun d hd ↦ ?_
    simp [Nat.mod_eq_of_lt (Nat.digits_lt_base hk hd)]
  convert (kernelDFAO k a).isAutomatic with n
  rw [output_eval_kernelDFAO, hw, Nat.ofDigits_digits]

/-- **Eilenberg's theorem**: for `2 ≤ k`, a sequence is `k`-automatic if and only if its
`k`-kernel is finite. -/
theorem isAutomatic_iff_finite_kernel (hk : 2 ≤ k) : IsAutomatic k a ↔ (kernel k a).Finite :=
  ⟨IsAutomatic.finite_kernel, isAutomatic_of_finite_kernel hk⟩

/-! ### Checks -/

/-- The subsequence `n ↦ a (2 * n + 1)` belongs to the `2`-kernel. -/
example : (fun n ↦ a (2 * n + 1)) ∈ kernel 2 a :=
  apply_mul_add_mem_kernel one_lt_two

/-- The `2`-kernel of the parity sequence consists of the sequence and the two constants. -/
example : kernel 2 (fun n : ℕ ↦ n % 2) = {fun n ↦ n % 2, fun _ ↦ 0, fun _ ↦ 1} := by
  ext b
  simp only [mem_kernel, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨e, r, hr, rfl⟩
    rcases e with _ | e
    · obtain rfl : r = 0 := by simpa using hr
      simp
    · have h (n : ℕ) : (2 ^ (e + 1) * n + r) % 2 = r % 2 := by
        simp [pow_succ', mul_assoc, Nat.add_mod]
      simp only [h]
      rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
      · simp [h0]
      · simp [h1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, by simp, by simp⟩
    · exact ⟨1, 0, by simp, funext fun n ↦ by simp⟩
    · exact ⟨1, 1, by simp, funext fun n ↦ by omega⟩

/-- The identity sequence has an infinite `k`-kernel in every base `k ≥ 2`. -/
example (hk : 2 ≤ k) : (kernel k fun n : ℕ ↦ n).Infinite := fun h ↦
  Set.infinite_range_of_injective (fun _ _ h ↦ h) (isAutomatic_of_finite_kernel hk h).finite_range

end TauCeti
