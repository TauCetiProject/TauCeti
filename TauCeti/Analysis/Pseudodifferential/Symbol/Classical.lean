/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
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
* `TauCeti.ClassicalSymbol.ofHomogeneous`: the classical symbol `χ(ξ) a(x, ξ)` of a single
  homogeneous term, whose principal symbol is `a`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5
  and Proposition 18.1.3.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2.
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
  have hsum : (∑ j ∈ Finset.range N, s j).coefficient p =
      ∑ j ∈ Finset.range N, (s j).coefficient p :=
    map_sum (AddMonoidHom.mk' (fun b : Symbol n V W (m - N) => b.coefficient p) fun _ _ => rfl) _ _
  simp only [Symbol.coefficient_add, Pi.add_apply, hsum, hr₀, hs, Symbol.coefficient_sub,
    Pi.sub_apply, coefficient_cutoffSymbol, Finset.sum_sub_distrib]
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

end ClassicalSymbol

end TauCeti
