/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Analysis.Pseudodifferential.Symbol.Homogeneous

/-!
# Classical symbols

A *classical* (one-step polyhomogeneous) symbol of order `m` on `ℝⁿ` is a symbol `a ∈ S^m_{1,0}`
with an asymptotic expansion `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` into homogeneous terms: each `a_{m-j}`
is smooth away from `ξ = 0` and positively homogeneous of degree `m - j` in `ξ`, `χ` is a frequency
cutoff, and for every `N` the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N`.
The leading term `a_m` is the principal symbol. Differential operators with smooth coefficients
and their parametrices have classical symbols, and the principal symbol of a classical symbol is
what ellipticity, the symbol calculus and index theory are phrased in.

The homogeneous terms enter the expansion through their cut-off terms
`TauCeti.HomogeneousSymbol.cutoffSymbol χ a`, the symbols `χ(ξ) a(x, ξ)` of
`TauCeti/Analysis/Pseudodifferential/Symbol/Homogeneous.lean`. This file defines the carrier
`TauCeti.ClassicalSymbol n V W m` of classical symbols, with an actual remainder symbol
`TauCeti.ClassicalSymbol.remainder χ N` of order `m - N` after `N` terms, and proves:

* `TauCeti.ClassicalSymbol.exists_remainder`: the expansion holds for every frequency cutoff, not
  only for the one used to define the symbol;
* `TauCeti.ClassicalSymbol.term_eq_of_toSymbol_eq` and `TauCeti.ClassicalSymbol.ext`: the
  homogeneous terms are determined by the symbol, so a classical symbol is determined by its full
  symbol;
* the classical symbols of order `m` form a complex vector space, termwise;
* `TauCeti.ClassicalSymbol.principal`, the principal symbol, with
  `TauCeti.ClassicalSymbol.exists_sub_cutoffSymbol_principal`: the full symbol and its cut-off
  principal symbol differ by a symbol of order `m - 1`;
* `TauCeti.ClassicalSymbol.principal_eq_zero_iff` and
  `TauCeti.ClassicalSymbol.principal_surjective`: the principal symbol vanishes exactly on the
  classical symbols of order `m - 1`, and every homogeneous symbol of degree `m` is a principal
  symbol;
* `TauCeti.ClassicalSymbol.isSmoothing_toSymbol_iff`: a classical symbol is smoothing exactly when
  all of its homogeneous terms vanish; `TauCeti.ClassicalSymbol.ofIsSmoothing` makes every
  smoothing symbol classical;
* `TauCeti.ClassicalSymbol.termsLinearMap`: the homogeneous terms as a linear map, whose kernel
  consists of the smoothing classical symbols (`TauCeti.ClassicalSymbol.mem_ker_termsLinearMap`);
  `TauCeti.ClassicalSymbol.isSmoothing_toSymbol_sub_iff`: two classical symbols differ by a
  smoothing symbol exactly when their homogeneous terms agree;
* `TauCeti.ClassicalSymbol.ofHomogeneous`: the classical symbol `χ(ξ) a(x, ξ)` of a single
  homogeneous term, whose principal symbol is `a`;
* `TauCeti.ClassicalSymbol.inclusion`: a classical symbol of order `m - k`, `k ∈ ℕ`, is classical
  of order `m`, with `k` leading terms equal to zero;
* `TauCeti.ClassicalSymbol.tail`: the remainder `a - χ(ξ) a_m` after the principal term, a
  classical symbol of order `m - 1`;
* the exact sequence `0 → S^{m-1}_cl → S^m_cl → H^m → 0`: the principal symbol is surjective
  (`TauCeti.ClassicalSymbol.principal_surjective`), its kernel is the image of the classical
  symbols of order `m - 1` (`TauCeti.ClassicalSymbol.principal_eq_zero_iff_exists_inclusion`,
  `TauCeti.ClassicalSymbol.ker_principalLinearMap`), and
  `TauCeti.ClassicalSymbol.principalEquiv` identifies the quotient by them with the homogeneous
  symbols of degree `m`;
* `TauCeti.ClassicalSymbol.comp`: the pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of
  classical symbols of orders `m'` and `m` is classical of order `m' + m`, with the terms
  `cₖ = ∑_{i + j = k} bᵢ ∘ aⱼ` (`TauCeti.ClassicalSymbol.compTerms`), so the principal symbol is
  multiplicative (`TauCeti.ClassicalSymbol.principal_comp`). This is not the composition of the
  operators, whose lower order terms also involve derivatives of the symbols.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5
  and Proposition 18.1.3.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2, §2.9, Lemma 2.5.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

open HomogeneousSymbol

variable (n V W m) in
/-- A classical symbol of order `m` on `ℝⁿ`: a symbol `a` of order `m` together with homogeneous
terms `a_{m-j}` of degree `m - j` for `j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and
every `N`, the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N`. The expansion
then holds for every cutoff (`TauCeti.ClassicalSymbol.exists_remainder`), and the terms are
determined by the symbol (`TauCeti.ClassicalSymbol.ext`). -/
structure ClassicalSymbol where
  /-- The full symbol. -/
  toSymbol : Symbol n V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`;
  use `TauCeti.ClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : Symbol n V W (m - N), ∀ p,
      r.coefficient p =
        toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace ClassicalSymbol

section Remainder

variable (a : ClassicalSymbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol is a symbol of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      a.toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  obtain ⟨χ₀, h₀⟩ := a.exists_remainder'
  obtain ⟨r₀, hr₀⟩ := h₀ N
  -- The truncated expansions for `χ₀` and `χ` differ by `∑_{j<N} (χ₀ - χ)(ξ) a_{m-j}`, a sum of
  -- smoothing symbols.
  choose s hs using fun j =>
    Symbol.isSmoothing_iff.1 (isSmoothing_cutoffSymbol_sub_cutoffSymbol χ₀ χ (a.term j)) (m - N)
  refine ⟨r₀ + ∑ j ∈ Finset.range N, s j, fun p => ?_⟩
  simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_sum, Finset.sum_apply, hr₀,
    hs, Symbol.coefficient_sub, Pi.sub_apply, coefficient_cutoffSymbol, Finset.sum_sub_distrib]
  abel

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol after `N` terms, a symbol of
order `m - N`. -/
def remainder (N : ℕ) : Symbol n V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols with the same full symbol have
the same homogeneous terms. -/
theorem term_eq_of_toSymbol_eq {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol)
    (j : ℕ) : a.term j = b.term j := by
  obtain ⟨χ, -⟩ := a.exists_remainder'
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- Given the equality of the earlier terms, the difference of the remainders after `j + 1`
    -- terms is the cut-off term of `b_{m-j} - a_{m-j}`, of order `m - (j + 1) < m - j`.
    refine (sub_eq_zero.1 <| eq_zero_of_coefficient_eq_cutoffSymbol χ (m' := m - (j + 1 : ℕ))
      (by push_cast; linarith) (a.remainder χ (j + 1) - b.remainder χ (j + 1)) ?_).symm
    funext p
    have hsum : ∑ i ∈ Finset.range j, χ p.2 • (a.term i).coefficient p =
        ∑ i ∈ Finset.range j, χ p.2 • (b.term i).coefficient p :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.1 hi)]
    simp only [Symbol.coefficient_sub, Pi.sub_apply, coefficient_remainder,
      Finset.sum_range_succ, hsum, h, coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_sub,
      smul_sub]
    abel

/-- A classical symbol is determined by its full symbol. -/
@[ext]
theorem ext {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol) : a = b := by
  have ht : a.term = b.term := funext (term_eq_of_toSymbol_eq h)
  cases a
  cases b
  cases h
  cases ht
  rfl

theorem toSymbol_injective :
    Function.Injective (toSymbol : ClassicalSymbol n V W m → Symbol n V W m) :=
  fun _ _ => ext

end Uniqueness

/-! ### The vector space of classical symbols of order `m` -/

section Module

instance : Zero (ClassicalSymbol n V W m) where
  zero :=
    { toSymbol := 0
      term _ := 0
      exists_remainder' := ⟨default, fun _ => ⟨0, fun p => by simp⟩⟩ }

instance : Add (ClassicalSymbol n V W m) where
  add a b :=
    { toSymbol := a.toSymbol + b.toSymbol
      term j := a.term j + b.term j
      exists_remainder' := ⟨default, fun N => ⟨a.remainder default N + b.remainder default N,
        fun p => by
          simp only [Symbol.coefficient_add, Pi.add_apply, coefficient_remainder,
            HomogeneousSymbol.coefficient_add, smul_add, Finset.sum_add_distrib]
          abel⟩⟩ }

instance : SMul ℂ (ClassicalSymbol n V W m) where
  smul c a :=
    { toSymbol := c • a.toSymbol
      term j := c • a.term j
      exists_remainder' := ⟨default, fun N => ⟨c • a.remainder default N, fun p => by
        simp only [Symbol.coefficient_smul, Pi.smul_apply, coefficient_remainder,
          HomogeneousSymbol.coefficient_smul, smul_sub, Finset.smul_sum, smul_comm c]⟩⟩ }

instance : Neg (ClassicalSymbol n V W m) where
  neg a :=
    { toSymbol := -a.toSymbol
      term j := -a.term j
      exists_remainder' := ⟨default, fun N => ⟨-a.remainder default N, fun p => by
        simp only [Symbol.coefficient_neg, Pi.neg_apply, coefficient_remainder,
          HomogeneousSymbol.coefficient_neg, smul_neg, Finset.sum_neg_distrib]
        abel⟩⟩ }

instance : Sub (ClassicalSymbol n V W m) where
  sub a b := a + -b

instance : SMul ℕ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

variable (a b : ClassicalSymbol n V W m) (c : ℂ) (j : ℕ)

@[simp]
theorem toSymbol_zero : (0 : ClassicalSymbol n V W m).toSymbol = 0 := (rfl)

@[simp]
theorem toSymbol_add : (a + b).toSymbol = a.toSymbol + b.toSymbol := (rfl)

@[simp]
theorem toSymbol_smul : (c • a).toSymbol = c • a.toSymbol := (rfl)

@[simp]
theorem toSymbol_neg : (-a).toSymbol = -a.toSymbol := (rfl)

@[simp]
theorem toSymbol_sub : (a - b).toSymbol = a.toSymbol - b.toSymbol :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem toSymbol_nsmul (k : ℕ) : (k • a).toSymbol = k • a.toSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toSymbol

@[simp]
theorem toSymbol_zsmul (k : ℤ) : (k • a).toSymbol = k • a.toSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toSymbol

@[simp]
theorem term_zero : (0 : ClassicalSymbol n V W m).term j = 0 := (rfl)

@[simp]
theorem term_add : (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_smul : (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_neg : (-a).term j = -a.term j := (rfl)

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j :=
  (sub_eq_add_neg _ _).symm

instance : AddCommGroup (ClassicalSymbol n V W m) :=
  toSymbol_injective.addCommGroup _ toSymbol_zero toSymbol_add toSymbol_neg toSymbol_sub
    (fun a k => toSymbol_nsmul a k) (fun a k => toSymbol_zsmul a k)

instance : Module ℂ (ClassicalSymbol n V W m) :=
  toSymbol_injective.module ℂ ⟨⟨toSymbol, toSymbol_zero⟩, toSymbol_add⟩
    fun c a => toSymbol_smul a c

end Module

/-! ### The principal symbol -/

section Principal

variable (a b : ClassicalSymbol n V W m)

/-- The principal symbol of a classical symbol of order `m`: its leading homogeneous term `a_m`,
of degree `m`. -/
def principal : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  (a.term 0).castDegree (by simp)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  coefficient_castDegree _ _

/-- A classical symbol and its cut-off principal symbol differ by a symbol of order `m - 1`. -/
theorem exists_sub_cutoffSymbol_principal (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : Symbol n V W (m - 1),
      r.coefficient = (a.toSymbol - cutoffSymbol χ a.principal).coefficient :=
  ⟨Symbol.inclusion (by simp) (a.remainder χ 1), funext fun p => by simp⟩

@[simp]
theorem principal_zero : (0 : ClassicalSymbol n V W m).principal = 0 :=
  castDegree_zero _

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  castDegree_add _ _ _

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  castDegree_smul _ _ _

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  castDegree_neg _ _

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal := by
  simp [principal, castDegree_sub]

end Principal

/-! ### Smoothing symbols and single homogeneous terms -/

section Examples

/-- A smoothing symbol is a classical symbol, all of whose homogeneous terms vanish. -/
def ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) : ClassicalSymbol n V W m where
  toSymbol := a
  term _ := 0
  exists_remainder' := ⟨default, fun N => ⟨(Symbol.isSmoothing_iff.1 ha (m - N)).choose, fun p => by
    simp [(Symbol.isSmoothing_iff.1 ha (m - N)).choose_spec]⟩⟩

@[simp]
theorem toSymbol_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) :
    (ofIsSmoothing a ha).toSymbol = a :=
  (rfl)

@[simp]
theorem term_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) (j : ℕ) :
    (ofIsSmoothing a ha).term j = 0 :=
  (rfl)

/-- A classical symbol is smoothing exactly when all of its homogeneous terms vanish. -/
theorem isSmoothing_toSymbol_iff (a : ClassicalSymbol n V W m) :
    a.toSymbol.IsSmoothing ↔ ∀ j, a.term j = 0 := by
  refine ⟨fun ha j => ?_, fun ha => Symbol.isSmoothing_iff.2 fun m' => ?_⟩
  · exact (term_eq_of_toSymbol_eq (a := a) (b := ofIsSmoothing a.toSymbol ha) rfl j).trans
      (term_ofIsSmoothing _ _ j)
  · -- With vanishing terms the remainder after `N` terms is the symbol itself, of order `m - N`.
    obtain ⟨N, hN⟩ := exists_nat_ge (m - m')
    exact ⟨Symbol.inclusion (by linarith) (a.remainder default N), funext fun p => by simp [ha]⟩

/-- The classical symbol `χ(ξ) a(x, ξ)` of a single homogeneous term `a` of degree `m`: its
principal symbol is `a` and its other homogeneous terms vanish. -/
def ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ClassicalSymbol n V W m where
  toSymbol := cutoffSymbol χ a
  term
    | 0 => a.castDegree (by simp)
    | _ + 1 => 0
  exists_remainder' := ⟨χ, fun
    | 0 => ⟨Symbol.inclusion (by simp) (cutoffSymbol χ a), fun p => by simp⟩
    | N + 1 => ⟨0, fun p => by simp [Finset.sum_range_succ']⟩⟩

variable (χ : FrequencyCutoff (CoordinateSpace n))
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

@[simp]
theorem toSymbol_ofHomogeneous : (ofHomogeneous χ a).toSymbol = cutoffSymbol χ a :=
  (rfl)

@[simp]
theorem principal_ofHomogeneous : (ofHomogeneous χ a).principal = a :=
  castDegree_castDegree _ _ _ |>.trans (castDegree_rfl a)

@[simp]
theorem term_ofHomogeneous_succ (j : ℕ) : (ofHomogeneous χ a).term (j + 1) = 0 :=
  (rfl)

end Examples

section PrincipalKernel

/-- The principal symbol of a classical symbol of order `m` vanishes exactly when its full symbol
has order `m - 1`. -/
theorem principal_eq_zero_iff {a : ClassicalSymbol n V W m} :
    a.principal = 0 ↔ ∃ r : Symbol n V W (m - 1), r.coefficient = a.toSymbol.coefficient := by
  obtain ⟨r', hr'⟩ := a.exists_sub_cutoffSymbol_principal default
  constructor
  · intro h
    refine ⟨r', ?_⟩
    rw [hr', h]
    funext p
    simp
  · rintro ⟨r, hr⟩
    refine eq_zero_of_coefficient_eq_cutoffSymbol default (m' := m - 1) (by linarith) (r - r') ?_
    rw [Symbol.coefficient_sub, hr, hr', Symbol.coefficient_sub, sub_sub_cancel]

/-- Every homogeneous symbol of degree `m` is the principal symbol of a classical symbol of
order `m`. -/
theorem principal_surjective :
    Function.Surjective (principal : ClassicalSymbol n V W m → _) :=
  fun a ↦ ⟨ofHomogeneous default a, principal_ofHomogeneous default a⟩

end PrincipalKernel

/-! ### Inclusion of orders -/

section Inclusion

variable {m' : ℝ}

/-- **Inclusion of orders.** A classical symbol of order `m' = m - k`, `k ∈ ℕ`, is a classical
symbol of order `m` whose first `k` homogeneous terms vanish, followed by the terms of the original
expansion. The steps of an expansion are integers, so orders with a non-integer difference are not
comparable in the classical calculus. -/
def inclusion (k : ℕ) (hk : m' = m - k) :
    ClassicalSymbol n V W m' →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun b :=
    { toSymbol := Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b.toSymbol
      term j := if h : k ≤ j then (b.term (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring)
        else 0
      exists_remainder' := ⟨default, fun N => by
        rcases le_or_gt k N with hN | hN
        · -- After `N = k + M` terms the remainder is the remainder of `b` after `M` terms.
          obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
          refine ⟨Symbol.inclusion (le_of_eq (by rw [hk]; push_cast; ring))
            (b.remainder default M), fun p => ?_⟩
          rw [Symbol.coefficient_inclusion, coefficient_remainder, Symbol.coefficient_inclusion,
            Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range k) fun j hj => ?_,
            zero_add]
          · congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Nat.le_add_right, ↓reduceDIte, coefficient_castDegree]
            rw [coefficient_congr_index b.term (Nat.add_sub_cancel_left k i)]
          · simp [show ¬k ≤ j by simpa using hj]
        · -- Before the `k`-th term all terms vanish, and `b` has order `m - k ≤ m - N`.
          refine ⟨Symbol.inclusion (by rw [hk]; gcongr) b.toSymbol, fun p => ?_⟩
          rw [Symbol.coefficient_inclusion, Symbol.coefficient_inclusion,
            Finset.sum_eq_zero fun j hj => ?_, sub_zero]
          simp [show ¬k ≤ j by simp at hj; omega]⟩ }
  map_add' a b := ext (map_add (Symbol.inclusion _) a.toSymbol b.toSymbol)
  map_smul' c a := ext (map_smul (Symbol.inclusion _) c a.toSymbol)

variable (k : ℕ) (hk : m' = m - k) (b : ClassicalSymbol n V W m')

@[simp]
theorem toSymbol_inclusion :
    (inclusion k hk b).toSymbol =
      Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b.toSymbol :=
  (rfl)

theorem term_inclusion (j : ℕ) :
    (inclusion k hk b).term j =
      if h : k ≤ j then (b.term (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring) else 0 :=
  (rfl)

@[simp]
theorem term_inclusion_of_lt {j : ℕ} (hj : j < k) : (inclusion k hk b).term j = 0 := by
  simp [term_inclusion, show ¬k ≤ j by omega]

@[simp]
theorem term_inclusion_add (j : ℕ) :
    (inclusion k hk b).term (k + j) = (b.term j).castDegree (by rw [hk]; push_cast; ring) := by
  ext1
  simp only [term_inclusion, Nat.le_add_right, ↓reduceDIte, coefficient_castDegree]
  rw [coefficient_congr_index b.term (Nat.add_sub_cancel_left k j)]

theorem inclusion_injective :
    Function.Injective (inclusion (n := n) (V := V) (W := W) k hk) := fun _ _ h =>
  ext (Symbol.inclusion_injective _ (congrArg toSymbol h))

end Inclusion

/-! ### Removing the leading term -/

section Tail

variable (χ : FrequencyCutoff (CoordinateSpace n)) (a : ClassicalSymbol n V W m)

/-- **Removing the leading term.** The remainder `a - χ(ξ) a_m` of a classical symbol of order `m`
after its principal term, as a classical symbol of order `m - 1` with the homogeneous terms
`a_{m-1}, a_{m-2}, …`. -/
def tail : ClassicalSymbol n V W (m - 1) where
  toSymbol := Symbol.inclusion (le_of_eq (by simp)) (a.remainder χ 1)
  term j := (a.term (j + 1)).castDegree (by push_cast; ring)
  exists_remainder' := ⟨χ, fun N =>
    ⟨Symbol.inclusion (le_of_eq (by push_cast; ring)) (a.remainder χ (N + 1)), fun p => by
      rw [Symbol.coefficient_inclusion, Symbol.coefficient_inclusion, coefficient_remainder,
        coefficient_remainder, Finset.sum_range_succ', Finset.sum_range_one]
      simp only [coefficient_castDegree]
      abel⟩⟩

@[simp]
theorem coefficient_toSymbol_tail (p : CoordinateSpace n × CoordinateSpace n) :
    (a.tail χ).toSymbol.coefficient p =
      a.toSymbol.coefficient p - χ p.2 • (a.term 0).coefficient p := by
  simp [tail]

@[simp]
theorem term_tail (j : ℕ) :
    (a.tail χ).term j = (a.term (j + 1)).castDegree (by push_cast; ring) :=
  (rfl)

end Tail

/-! ### The principal symbol sequence

The principal symbol fits into the exact sequence `0 → S^{m-1}_cl → S^m_cl → H^m → 0`: it is
surjective onto the homogeneous symbols of degree `m`, and its kernel is the image of the classical
symbols of order `m - 1`. -/

section PrincipalSequence

variable (n V W m) in
/-- The principal symbol as a linear map. -/
def principalLinearMap :
    ClassicalSymbol n V W m →ₗ[ℂ] HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m
    where
  toFun := principal
  map_add' := principal_add
  map_smul' c a := principal_smul a c

@[simp]
theorem principalLinearMap_apply (a : ClassicalSymbol n V W m) :
    principalLinearMap n V W m a = a.principal :=
  (rfl)
/-- **The kernel of the principal symbol.** A classical symbol of order `m` has principal symbol
zero exactly when it is a classical symbol of order `m - 1`. -/
theorem principal_eq_zero_iff_exists_inclusion (a : ClassicalSymbol n V W m) :
    a.principal = 0 ↔ ∃ b : ClassicalSymbol n V W (m - 1), inclusion 1 (by simp) b = a := by
  refine ⟨fun h => ⟨a.tail default, ext ?_⟩, ?_⟩
  · -- With a vanishing leading term, the remainder after it is `a` itself.
    have h0 : (a.term 0).coefficient = 0 := by
      simpa using congrArg HomogeneousSymbol.coefficient h
    ext1
    funext p
    simp [h0]
  · rintro ⟨b, rfl⟩
    ext1
    simp

variable (n V W m) in
/-- **The kernel of the principal symbol** is the image of the classical symbols of order
`m - 1`. -/
theorem ker_principalLinearMap :
    LinearMap.ker (principalLinearMap n V W m) =
      LinearMap.range (inclusion (n := n) (V := V) (W := W) (m' := m - 1) 1 (by simp)) := by
  ext a
  simp only [LinearMap.mem_ker, principalLinearMap_apply, principal_eq_zero_iff_exists_inclusion,
    LinearMap.mem_range]

variable (n V W m) in
/-- The principal symbol identifies the quotient of the classical symbols of order `m` by the
classical symbols of order `m - 1` (`TauCeti.ClassicalSymbol.ker_principalLinearMap`) with the
homogeneous symbols of degree `m`. -/
def principalEquiv :
    (ClassicalSymbol n V W m ⧸
        LinearMap.range (inclusion (n := n) (V := V) (W := W) (m' := m - 1) 1 (by simp))) ≃ₗ[ℂ]
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  (Submodule.quotEquivOfEq _ _ (ker_principalLinearMap n V W m).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ principal_surjective)

@[simp]
theorem principalEquiv_mk (a : ClassicalSymbol n V W m) :
    principalEquiv n V W m (Submodule.Quotient.mk a) = a.principal :=
  (rfl)

end PrincipalSequence

/-! ### Pointwise composition -/

section Comp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}

/-- The homogeneous terms `cₖ = ∑_{i + j = k} qᵢ ∘ pⱼ` of the pointwise composition
`(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of two classical symbols, with the terms `qᵢ` of degree `m' - i` and
`pⱼ` of degree `m - j`. The term `cₖ` has degree `m' + m - k`. -/
def compTerms
    (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (k : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V U (m' + m - k) :=
  ∑ i ∈ Finset.range (k + 1),
    if h : i ≤ k then ((q i).comp (p (k - i))).castDegree (by rw [Nat.cast_sub h]; ring) else 0

section CompTerms

variable (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
  (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))

/-- The coefficient of `cₖ` is `∑_{i ≤ k} qᵢ ∘ pₖ₋ᵢ`. -/
theorem coefficient_compTerms (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (compTerms q p k).coefficient z =
      ∑ i ∈ Finset.range (k + 1), ((q i).coefficient z).comp ((p (k - i)).coefficient z) := by
  rw [compTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [Nat.le_of_lt_succ (Finset.mem_range.1 hi)]

@[simp]
theorem coefficient_compTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (compTerms q p 0).coefficient z = ((q 0).coefficient z).comp ((p 0).coefficient z) := by
  simp [coefficient_compTerms]

/-- The recursion `cₖ₊₁ = q₀ ∘ pₖ₊₁ + ∑_{i + j = k} qᵢ₊₁ ∘ pⱼ` for the terms of a composition. -/
theorem coefficient_compTerms_succ (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (compTerms q p (k + 1)).coefficient z =
      ((q 0).coefficient z).comp ((p (k + 1)).coefficient z) +
        (compTerms (m' := m' - 1) (fun i => (q (i + 1)).castDegree (by push_cast; ring)) p
          k).coefficient z := by
  rw [coefficient_compTerms, coefficient_compTerms, Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coefficient_castDegree, coefficient_congr_index p (Nat.add_sub_add_right k 1 i)]

end CompTerms

/-- The remainders of the pointwise composition of classical symbols after `N` terms have
order `m' + m - N`. -/
private theorem exists_remainder_comp (χ : FrequencyCutoff (CoordinateSpace n))
    (a : ClassicalSymbol n V W m) (N : ℕ) :
    ∀ {m' : ℝ} (b : ClassicalSymbol n W U m'), ∃ r : Symbol n V U (m' + m - N), ∀ p,
      r.coefficient p = (b.toSymbol.comp a.toSymbol).coefficient p -
        ∑ k ∈ Finset.range N, χ p.2 • (compTerms b.term a.term k).coefficient p := by
  -- Induct on the number `N` of terms, removing the leading term of `b` at each step.
  induction N with
  | zero => exact fun b => ⟨Symbol.inclusion (le_of_eq (by simp)) (b.toSymbol.comp a.toSymbol),
      fun p => by simp⟩
  | succ N ih =>
    intro m' b
    -- Split `b = χ(ξ) b₀ + b₁`, where `b₁` has order `m' - 1` and the terms `b₁, b₂, …`. Then
    -- `b ∘ a - ∑_{k ≤ N} χ cₖ = χ b₀ ∘ (a - ∑_{j ≤ N} χ aⱼ) + (b₁ ∘ a - ∑_{k < N} χ cₖ')` for
    -- `‖ξ‖ ≥ 2`, where `cₖ'` are the terms of `b₁ ∘ a`, and both summands have order
    -- `m' + m - (N + 1)`.
    obtain ⟨R, hR⟩ := ih (b.tail χ)
    have ht : (b.tail χ).term = fun i => (b.term (i + 1)).castDegree (by push_cast; ring) := rfl
    obtain ⟨r, hr⟩ := Symbol.exists_coefficient_eq_of_forall_le_norm
      ((b.toSymbol.comp a.toSymbol).contDiff_coefficient.sub
        (Symbol.contDiff_sum_coefficient (Finset.range (N + 1))
          fun k => cutoffSymbol χ (compTerms b.term a.term k)))
      (Symbol.inclusion (le_of_eq (by push_cast; ring))
          ((cutoffSymbol χ b.principal).comp (a.remainder χ (N + 1))) +
        Symbol.inclusion (le_of_eq (by push_cast; ring)) R : Symbol n V U (m' + m - (N + 1 : ℕ)))
      2 fun x ξ hξ => by
      have hχ := χ.apply_eq_one_of_two_le_norm hξ
      simp only [Finset.sum_apply, Symbol.coefficient_add, Pi.add_apply,
        Symbol.coefficient_inclusion, Symbol.coefficient_comp, hR, ht, coefficient_remainder,
        coefficient_toSymbol_tail, coefficient_cutoffSymbol, coefficient_principal, hχ,
        one_smul, Finset.sum_range_succ' _ N, coefficient_compTerms_succ,
        coefficient_compTerms_zero, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_finsetSum, Finset.sum_add_distrib]
      abel
    exact ⟨r, fun p => by simp [hr, Finset.sum_apply]⟩

/-- **Pointwise composition.** The pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of classical
symbols of orders `m'` and `m` is a classical symbol of order `m' + m`, whose terms
`cₖ = ∑_{i + j = k} bᵢ ∘ aⱼ` collect the products of the terms of total degree drop `k`. This is
not the composition of the operators: the lower order terms of the symbol of a composition of
operators also involve derivatives of the symbols. -/
def comp (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    ClassicalSymbol n V U (m' + m) where
  toSymbol := b.toSymbol.comp a.toSymbol
  term := compTerms b.term a.term
  exists_remainder' := ⟨default, fun N => exists_remainder_comp default a N b⟩

variable (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_comp : (b.comp a).toSymbol = b.toSymbol.comp a.toSymbol :=
  (rfl)

@[simp]
theorem term_comp (k : ℕ) : (b.comp a).term k = compTerms b.term a.term k :=
  (rfl)

theorem comp_add (b : ClassicalSymbol n W U m') (a₁ a₂ : ClassicalSymbol n V W m) :
    b.comp (a₁ + a₂) = b.comp a₁ + b.comp a₂ :=
  ext (Symbol.comp_add _ _ _)

theorem add_comp (b₁ b₂ : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (b₁ + b₂).comp a = b₁.comp a + b₂.comp a :=
  ext (Symbol.add_comp _ _ _)

@[simp]
theorem comp_smul (c : ℂ) : b.comp (c • a) = c • b.comp a :=
  ext (Symbol.comp_smul _ _ _)

@[simp]
theorem smul_comp (c : ℂ) : (c • b).comp a = c • b.comp a :=
  ext (Symbol.smul_comp _ _ _)

@[simp]
theorem comp_zero : b.comp (0 : ClassicalSymbol n V W m) = 0 :=
  ext (Symbol.comp_zero _)

@[simp]
theorem zero_comp : (0 : ClassicalSymbol n W U m').comp a = 0 :=
  ext (Symbol.zero_comp _)

/-- **The principal symbol is multiplicative** for the pointwise composition. -/
@[simp]
theorem principal_comp : (b.comp a).principal = b.principal.comp a.principal := by
  ext1
  funext z
  simp

@[simp]
theorem comp_neg (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    b.comp (-a) = -b.comp a :=
  ext (Symbol.comp_neg _ _)

@[simp]
theorem neg_comp (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (-b).comp a = -b.comp a :=
  ext (Symbol.neg_comp _ _)

theorem comp_sub (b : ClassicalSymbol n W U m') (a₁ a₂ : ClassicalSymbol n V W m) :
    b.comp (a₁ - a₂) = b.comp a₁ - b.comp a₂ :=
  ext (Symbol.comp_sub _ _ _)

theorem sub_comp (b₁ b₂ : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (b₁ - b₂).comp a = b₁.comp a - b₂.comp a :=
  ext (Symbol.sub_comp _ _ _)

/-- The product of two cut-off homogeneous terms is the cut-off composition of the terms, for the
product cutoff. -/
theorem ofHomogeneous_comp_ofHomogeneous (χ χ' : FrequencyCutoff (CoordinateSpace n))
    (b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U m')
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (ofHomogeneous χ b).comp (ofHomogeneous χ' a) = ofHomogeneous (χ * χ') (b.comp a) := by
  ext : 2
  funext p
  simp [smul_smul, mul_comm]

end Comp

/-! ### The homogeneous terms as a linear map -/

section Terms

variable (n V W m) in
/-- The homogeneous terms `(a_{m-j})ⱼ` of a classical symbol of order `m`, as a linear map to the
sequences of homogeneous symbols of degrees `m - j`. -/
def termsLinearMap : ClassicalSymbol n V W m →ₗ[ℂ]
    ∀ j : ℕ, HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j) where
  toFun a := a.term
  map_add' a b := funext fun j => term_add a b j
  map_smul' c a := funext fun j => term_smul a c j

@[simp]
theorem termsLinearMap_apply (a : ClassicalSymbol n V W m) : termsLinearMap n V W m a = a.term :=
  (rfl)

/-- The classical symbols with vanishing homogeneous terms are exactly the smoothing ones. -/
theorem mem_ker_termsLinearMap {a : ClassicalSymbol n V W m} :
    a ∈ LinearMap.ker (termsLinearMap n V W m) ↔ a.toSymbol.IsSmoothing := by
  simp only [LinearMap.mem_ker, termsLinearMap_apply, isSmoothing_toSymbol_iff, funext_iff,
    Pi.zero_apply]

/-- **Uniqueness modulo smoothing.** Two classical symbols of order `m` differ by a smoothing
symbol exactly when they have the same homogeneous terms. -/
theorem isSmoothing_toSymbol_sub_iff {a b : ClassicalSymbol n V W m} :
    (a.toSymbol - b.toSymbol).IsSmoothing ↔ a.term = b.term := by
  rw [← toSymbol_sub, isSmoothing_toSymbol_iff, funext_iff]
  simp [sub_eq_zero]

end Terms

end ClassicalSymbol

end TauCeti
