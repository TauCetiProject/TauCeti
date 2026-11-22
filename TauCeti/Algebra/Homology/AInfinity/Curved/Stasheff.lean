/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Stasheff
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Order.Interval.Finset.Nat

/-!
# The curved Stasheff identities

A curved `A∞` algebra has operations `mₙ : A^{⊗ n} ⟶ A` of degree `2 - n` for every `n ≥ 0`,
including a nullary operation, the *curvature* `m₀ ∈ A²`. Its Stasheff identities are those of
`TauCeti/Algebra/Homology/AInfinity/Stasheff.lean` with the inner arity `s = 0` allowed: for every
`n ≥ 0`,

```text
∑_{n = r + s + t, s ≥ 0} (-1) ^ (r + s * t) m_{r + 1 + t} (1^{⊗ r} ⊗ m_s ⊗ 1^{⊗ t}) = 0.  (CSIₙ)
```

The term with `s = 0` inserts the curvature between the `r`-th and `(r + 1)`-th inputs, with the
sign `(-1) ^ r`, because the curvature has even degree. The identity in arity zero is
`m₁(m₀) = 0`, and the identity in arity one is

```text
m₁(m₁(a)) + m₂(m₀, a) - m₂(a, m₀) = 0,
```

so `m₁` squares to the commutator with the curvature in the right-module convention. The
identities of arity `n` involving the curvature have outer arity `n + 1`, so they disappear when
`m₀ = 0`, recovering the uncurved Stasheff identities, and also when `m_{n + 1} = 0`.

Each term is the existing `TauCeti.AInfinity.stasheffTerm` at inner arity `s = 0`, and the sign
comparison `TauCeti.AInfinity.suspendedStasheffTerm_eq_smul` with the suspended encoding holds for
every inner arity. So the curved identities are equivalently stated in the suspended (bar)
encoding, where no structural coefficient appears.

## Main definitions

* `TauCeti.AInfinity.curvedStasheffSum`: the left-hand side of `(CSIₙ)`.
* `TauCeti.AInfinity.curvedSuspendedStasheffSum`: the same sum in the suspended encoding.

## Main results

* `TauCeti.AInfinity.curvedStasheffSum_eq_stasheffSum_add`: the curved sum is the uncurved sum
  plus the curvature insertions `(-1) ^ r m_{n + 1}(x₀, …, x_{r - 1}, m₀, x_r, …, x_{n - 1})`.
* `TauCeti.AInfinity.curvedStasheffSum_of_m_zero_eq_zero` and
  `TauCeti.AInfinity.curvedStasheffSum_of_m_succ_eq_zero`: the curved sum is the uncurved one when
  the curvature vanishes, or when the operation of arity `n + 1` vanishes.
* `TauCeti.AInfinity.curvedStasheffSum_zero` and `TauCeti.AInfinity.curvedStasheffSum_one`: the
  identities in arities zero and one, written out.
* `TauCeti.AInfinity.curvedSuspendedStasheffSum_eq_zero_iff`: the suspended curved identity holds
  exactly when the unsuspended one does.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 3.2, for curved
  (filtered) `A∞` algebras.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the coefficient
  `(-1) ^ (r + s * t)`.
-/

public section

open _root_.MultilinearMap

namespace TauCeti

namespace AInfinity

variable {R : Type*} {A : Type*}

section CurvedStasheff

variable [Ring R] [AddCommMonoid A] [Module R A]
variable (m : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/-- The term of a Stasheff identity with inner arity zero inserts the curvature `m₀` at position
`p`, with the sign `(-1) ^ p`. -/
theorem stasheffTerm_inner_zero (p t : ℕ) :
    stasheffTerm m d x p 0 t =
      negOnePowCast R (p : ℤ) • evalNat (m (p + 1 + t)) (replaceBlock x p 0 (m 0 ![])) := by
  have h₀ : evalNat (m 0) (fun j ↦ x (p + j)) = m 0 ![] := by
    rw [evalNat_def]
    exact congrArg (m 0) (funext fun i ↦ i.elim0)
  rw [stasheffTerm_of_even m d x Even.zero, h₀]

/-- The left-hand side `(CSIₙ)` of the arity-`n` curved Stasheff identity: the sum of
`TauCeti.AInfinity.stasheffTerm` over all decompositions `n = p + s + t`, including the inner
arity `s = 0`. -/
def curvedStasheffSum (n : ℕ) : A :=
  ∑ p ∈ Finset.range (n + 1), ∑ s ∈ Finset.range (n - p + 1), stasheffTerm m d x p s (n - p - s)

/-- The defining double sum for the curved Stasheff identity. -/
theorem curvedStasheffSum_def (n : ℕ) : curvedStasheffSum m d x n =
    ∑ p ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.range (n - p + 1), stasheffTerm m d x p s (n - p - s) := (rfl)

/-- **The curved Stasheff sum is the uncurved one plus the curvature insertions.** -/
theorem curvedStasheffSum_eq_stasheffSum_add (n : ℕ) :
    curvedStasheffSum m d x n =
      stasheffSum m d x n + ∑ p ∈ Finset.range (n + 1), stasheffTerm m d x p 0 (n - p) := by
  rw [curvedStasheffSum_def, stasheffSum_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _),
    Finset.sum_insert (by simp), add_comm, Nat.sub_zero, zero_add]

/-- The arity-`n` curved Stasheff sum only reads the first `n` supplied degrees and inputs. -/
theorem curvedStasheffSum_congr {e : ℕ → ℤ} {y : ℕ → A} (n : ℕ)
    (hd : ∀ i < n, d i = e i) (hx : ∀ i < n, x i = y i) :
    curvedStasheffSum m d x n = curvedStasheffSum m e y n := by
  rw [curvedStasheffSum_def, curvedStasheffSum_def]
  refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hp hs
  exact stasheffTerm_congr m d x _ _ _ (fun i hi ↦ hd i (by omega)) fun i hi ↦ hx i (by omega)

/-- **Without curvature the curved Stasheff sum is the uncurved one.** -/
theorem curvedStasheffSum_of_m_zero_eq_zero (h : m 0 = 0) (n : ℕ) :
    curvedStasheffSum m d x n = stasheffSum m d x n := by
  rw [curvedStasheffSum_eq_stasheffSum_add,
    Finset.sum_eq_zero fun p _ ↦ stasheffTerm_eq_zero_of_inner_eq_zero m d x h, add_zero]

/-- The curvature insertions of arity `n` have outer arity `n + 1`, so they disappear when that
operation vanishes. -/
theorem curvedStasheffSum_of_m_succ_eq_zero {n : ℕ} (h : m (n + 1) = 0) :
    curvedStasheffSum m d x n = stasheffSum m d x n := by
  rw [curvedStasheffSum_eq_stasheffSum_add, Finset.sum_eq_zero fun p hp ↦ ?_, add_zero]
  refine stasheffTerm_eq_zero_of_outer_eq_zero m d x ?_
  rw [Finset.mem_range] at hp
  rwa [show p + 1 + (n - p) = n + 1 by omega]

/-- **The arity-zero curved identity** is `m₁(m₀) = 0`. -/
@[simp]
theorem curvedStasheffSum_zero : curvedStasheffSum m d x 0 = m 1 ![m 0 ![]] := by
  simp [curvedStasheffSum_eq_stasheffSum_add, stasheffTerm_inner_zero]

/-- **Naturality of the curved Stasheff sums.** A linear map which intertwines two families of
operations, including their curvatures, intertwines their curved Stasheff sums. -/
theorem map_curvedStasheffSum {B : Type*} [AddCommMonoid B] [Module R B] (f : A →ₗ[R] B)
    (m' : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ B) B)
    (hf : ∀ (k : ℕ) (y : Fin k → A), f (m k y) = m' k fun i ↦ f (y i)) (n : ℕ) :
    f (curvedStasheffSum m d x n) = curvedStasheffSum m' d (fun i ↦ f (x i)) n := by
  simp only [curvedStasheffSum_def, stasheffTerm_def, _root_.map_sum, map_smul, evalNat_def, hf,
    apply_replaceBlock f]

end CurvedStasheff

section CurvedStasheffGroup

variable [Ring R] [AddCommGroup A] [Module R A]
variable (m : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/-- **The arity-one curved identity** is `m₁(m₁(a)) + m₂(m₀, a) - m₂(a, m₀)`. -/
theorem curvedStasheffSum_one :
    curvedStasheffSum m d x 1 = m 1 ![m 1 ![x 0]] + m 2 ![m 0 ![], x 0] - m 2 ![x 0, m 0 ![]] := by
  simp [curvedStasheffSum_eq_stasheffSum_add, stasheffSum_one, stasheffTerm_inner_zero,
    Finset.sum_range_succ, sub_eq_add_neg, add_assoc]

end CurvedStasheffGroup

section CurvedSuspendedStasheff

variable [CommRing R] [AddCommMonoid A] [Module R A]
variable (m : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ A) A) (d : ℕ → ℤ) (x : ℕ → A)

/-- The left-hand side of the arity-`n` curved Stasheff identity in the suspended encoding: the sum
of `TauCeti.AInfinity.suspendedStasheffTerm` over all decompositions `n = p + s + t`, including the
inner arity `s = 0`, with no structural coefficient. -/
def curvedSuspendedStasheffSum (n : ℕ) : A :=
  ∑ p ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.range (n - p + 1), suspendedStasheffTerm m d x p s (n - p - s)

/-- The defining double sum for the suspended curved Stasheff identity. -/
theorem curvedSuspendedStasheffSum_def (n : ℕ) : curvedSuspendedStasheffSum m d x n =
    ∑ p ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.range (n - p + 1), suspendedStasheffTerm m d x p s (n - p - s) := (rfl)

/-- **The suspended and unsuspended curved Stasheff sums agree up to a global sign**, the
suspension sign of the whole arity. -/
@[simp]
theorem curvedSuspendedStasheffSum_eq_smul (n : ℕ) :
    curvedSuspendedStasheffSum m d x n =
      negOnePowCast R (suspExp n d) • curvedStasheffSum m d x n := by
  rw [curvedSuspendedStasheffSum_def, curvedStasheffSum_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hp hs
  rw [suspendedStasheffTerm_eq_smul, show p + s + (n - p - s) = n by omega]

/-- **The suspended curved Stasheff identity holds exactly when the unsuspended one does.** -/
theorem curvedSuspendedStasheffSum_eq_zero_iff (n : ℕ) :
    curvedSuspendedStasheffSum m d x n = 0 ↔ curvedStasheffSum m d x n = 0 := by
  rw [curvedSuspendedStasheffSum_eq_smul, negOnePowCast_smul_eq_zero_iff]

end CurvedSuspendedStasheff

end AInfinity

end TauCeti
