/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Classical symbols

A symbol `a ∈ S^m_{1,0}` is *classical* (one-step polyhomogeneous) if it has an asymptotic
expansion `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)` into homogeneous terms `aₘ₋ⱼ` of degree `m - j`, cut off near
the zero frequency by a frequency cutoff `χ`: for every `N`, the remainder
`a - ∑_{j < N} χ(ξ) aₘ₋ⱼ(x, ξ)` is a symbol of order `m - N`. The leading term `aₘ` is the
principal symbol. Differential operators with smooth coefficients, their parametrices and their
complex powers all have classical symbols, and ellipticity is a condition on the principal symbol.

This file develops:

* `HomogeneousSymbol.cutoffSymbol`: the cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of
  degree `m` is a symbol of order `m`. The estimates at large frequencies come from the iterated
  derivatives `HomogeneousSymbol.iteratedSpatialDeriv` and
  `HomogeneousSymbol.iteratedFrequencyDeriv`, which compute the mixed derivatives `∂ₓ^α ∂_ξ^β a`
  away from the zero frequency and are homogeneous of degree `m - |β|`
  (`HomogeneousSymbol.coefficient_iteratedSpatialDeriv_iteratedFrequencyDeriv`).
* `HomogeneousSymbol.eq_zero_of_coefficient_eq`: a homogeneous term of degree `μ` that agrees at
  large frequencies with a symbol of lower order vanishes.
* `ClassicalSymbol n V W m`: symbols of order `m` with their homogeneous terms, such that the
  remainders have the right orders for every frequency cutoff. It suffices to check this for a
  single cutoff (`ClassicalSymbol.ofCutoff`), since two cutoffs differ by a function supported
  in a bounded set of frequencies.
* Uniqueness of the terms: if two classical symbols differ by a symbol of order `m - N`, their
  first `N` terms agree (`ClassicalSymbol.term_eq_of_exists_coefficient_eq_sub`). Hence a classical
  symbol is determined by its underlying symbol (`ClassicalSymbol.ext`), and classical symbols of
  order `m` form a complex vector space.
* `ClassicalSymbol.principalSymbol`: the principal symbol, a surjective linear map onto the
  homogeneous symbols of degree `m` (`ClassicalSymbol.principalSymbol_surjective`), whose kernel
  consists of the classical symbols that have order `m - 1`
  (`ClassicalSymbol.principalSymbol_eq_zero_iff`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

namespace HomogeneousSymbol

variable {X E V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### Iterated coordinate derivatives of homogeneous symbols -/

/-- The iterated frequency derivative `∂_ξ^β a = ∂_{ξ_{j₁}} ⋯ ∂_{ξ_{jₖ}} a` of a homogeneous
symbol of degree `m` along a word `β = [j₁, …, jₖ]` of coordinate indices; it is homogeneous of
degree `m - |β|`. -/
def iteratedFrequencyDeriv (a : HomogeneousSymbol X (CoordinateSpace n) V W m) :
    (β : List (Fin n)) → HomogeneousSymbol X (CoordinateSpace n) V W (m - β.length)
  | [] => a.castDegree (by simp)
  | j :: js =>
    ((a.iteratedFrequencyDeriv js).frequencyDeriv (EuclideanSpace.single j 1)).castDegree
      (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)

/-- At a nonzero frequency, the iterated frequency derivative is the iterated coordinate
derivative of the coefficient in the frequency. -/
@[simp]
theorem coefficient_iteratedFrequencyDeriv (a : HomogeneousSymbol X (CoordinateSpace n) V W m)
    (β : List (Fin n)) (x : X) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (a.iteratedFrequencyDeriv β).coefficient (x, ξ) =
      coordinateDeriv β (fun η => a.coefficient (x, η)) ξ := by
  induction β generalizing ξ with
  | nil => simp [iteratedFrequencyDeriv]
  | cons j js ih =>
    have h : (fun η => (a.iteratedFrequencyDeriv js).coefficient (x, η)) =ᶠ[𝓝 ξ]
        coordinateDeriv js (fun η => a.coefficient (x, η)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hξ] with η hη using ih hη
    rw [iteratedFrequencyDeriv, coefficient_castDegree, coefficient_frequencyDeriv _ _ hξ,
      h.fderiv_eq, coordinateDeriv_cons]

/-- The iterated spatial derivative `∂ₓ^α a = ∂_{x_{j₁}} ⋯ ∂_{x_{jₖ}} a` of a homogeneous symbol
along a word `α = [j₁, …, jₖ]` of coordinate indices; it has the same degree. -/
def iteratedSpatialDeriv (a : HomogeneousSymbol (CoordinateSpace n) E V W m) :
    List (Fin n) → HomogeneousSymbol (CoordinateSpace n) E V W m
  | [] => a
  | j :: js => (a.iteratedSpatialDeriv js).spatialDeriv (EuclideanSpace.single j 1)

/-- At a nonzero frequency, the iterated spatial derivative is the iterated coordinate derivative
of the coefficient in the position. -/
@[simp]
theorem coefficient_iteratedSpatialDeriv (a : HomogeneousSymbol (CoordinateSpace n) E V W m)
    (α : List (Fin n)) (x : CoordinateSpace n) {ξ : E} (hξ : ξ ≠ 0) :
    (a.iteratedSpatialDeriv α).coefficient (x, ξ) =
      coordinateDeriv α (fun y => a.coefficient (y, ξ)) x := by
  induction α generalizing x with
  | nil => simp [iteratedSpatialDeriv]
  | cons j js ih =>
    rw [iteratedSpatialDeriv, coefficient_spatialDeriv _ _ hξ, funext ih, coordinateDeriv_cons]

/-- At a nonzero frequency, the iterated derivatives of a homogeneous symbol of degree `m`
compute the mixed derivatives `∂ₓ^α ∂_ξ^β` of its coefficient; in particular these are
homogeneous of degree `m - |β|` there. -/
theorem coefficient_iteratedSpatialDeriv_iteratedFrequencyDeriv
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (α β : List (Fin n))
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ((a.iteratedFrequencyDeriv β).iteratedSpatialDeriv α).coefficient (x, ξ) =
      mixedDeriv α β a.coefficient x ξ := by
  rw [coefficient_iteratedSpatialDeriv _ _ _ hξ, mixedDeriv_def]
  congr 1
  funext y
  exact coefficient_iteratedFrequencyDeriv a β y hξ

/-! ### The cut-off term of a homogeneous symbol -/

/-- The mixed derivatives of the cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of degree
`m` satisfy the symbol estimates of order `m`. -/
private theorem exists_bound_mixedDeriv_smul_coefficient
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ p.2 • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set s := m - (β.length : ℝ)
  -- At bounded frequencies the smooth term is bounded by continuity.
  obtain ⟨C₁, hC₁, h₁⟩ := (contDiff_zero.2 ((a.contDiff_smul_coefficient χ).mixedDeriv α β
    ).continuous).exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le hK 2 s
  -- At large frequencies the term is `a`, whose mixed derivatives are homogeneous of degree `s`.
  obtain ⟨C₂, hC₂, h₂⟩ :=
    ((a.iteratedFrequencyDeriv β).iteratedSpatialDeriv α).exists_norm_coefficient_le hK
  refine ⟨C₁ + 2 ^ (|s| / 2) * C₂, by positivity, fun x hx ξ => ?_⟩
  have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by positivity
  rcases le_or_gt ‖ξ‖ 2 with hξ | hξ
  · have h := h₁ x hx ξ hξ
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hw)
  · have heq : (fun p : CoordinateSpace n × CoordinateSpace n => χ p.2 • a.coefficient p)
        =ᶠ[𝓝 (x, ξ)] a.coefficient := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds
        (show 2 < ‖(x, ξ).2‖ from hξ)] with p hp
      rw [χ.apply_eq_one_of_two_le_norm hp.le, one_smul]
    rw [Filter.EventuallyEq.mixedDeriv_eq heq,
      ← coefficient_iteratedSpatialDeriv_iteratedFrequencyDeriv a α β x
        (norm_pos_iff.1 (by linarith))]
    calc _ ≤ C₂ * ‖ξ‖ ^ s := h₂ x hx ξ
      _ ≤ C₂ * (2 ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2)) :=
        mul_le_mul_of_nonneg_left (norm_rpow_le_one_add_norm_sq_rpow (by linarith) s) hC₂
      _ ≤ _ := by nlinarith [mul_nonneg hC₁ hw]

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m`, for a frequency
cutoff `χ`, as a symbol of order `m`. -/
def cutoffSymbol (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) : Symbol n V W m where
  coefficient p := χ p.2 • a.coefficient p
  contDiff_coefficient := a.contDiff_smul_coefficient χ
  exists_bound _ hK α β := a.exists_bound_mixedDeriv_smul_coefficient χ hK α β

@[simp]
theorem coefficient_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.cutoffSymbol χ).coefficient p = χ p.2 • a.coefficient p :=
  (rfl)

/-- A homogeneous symbol of degree `μ` that agrees at all large frequencies with a symbol of
lower order `s < μ` is zero. -/
theorem eq_zero_of_coefficient_eq {μ s : ℝ} (hs : s < μ)
    {d : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W μ} {r : Symbol n V W s}
    {R : ℝ} (h : ∀ x ξ, R ≤ ‖ξ‖ → d.coefficient (x, ξ) = r.coefficient (x, ξ)) : d = 0 := by
  refine d.eq_zero_of_forall_exists_norm_le fun x => ?_
  obtain ⟨C, hC, hb⟩ := r.exists_bound {x} isCompact_singleton [] []
  refine ⟨C * 2 ^ (|s| / 2), max R 1, s, hs, fun ξ hξ => ?_⟩
  have hb' := hb x rfl ξ
  simp only [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero] at hb'
  rw [h x ξ ((le_max_left _ _).trans hξ), mul_assoc]
  exact hb'.trans (mul_le_mul_of_nonneg_left
    (one_add_norm_sq_rpow_le_norm_rpow ((le_max_right _ _).trans hξ) s) hC)

end HomogeneousSymbol

/-! ### Classical symbols -/

variable (n) in
/-- A classical symbol of order `m`: a symbol `a` of order `m` together with homogeneous terms
`aₘ₋ⱼ` of degree `m - j`, `j = 0, 1, 2, …`, such that for every frequency cutoff `χ` and every
`N` the remainder `a(x, ξ) - ∑_{j < N} χ(ξ) aₘ₋ⱼ(x, ξ)` is a symbol of order `m - N`.

Requiring this for every cutoff is no stronger than requiring it for one
(`TauCeti.ClassicalSymbol.ofCutoff`), and the terms are determined by the underlying symbol
(`TauCeti.ClassicalSymbol.ext`). -/
structure ClassicalSymbol (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) extends Symbol n V W m where
  /-- The homogeneous term `aₘ₋ⱼ` of degree `m - j` of the expansion. -/
  term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)
  exists_remainder : ∀ (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ),
    ∃ r : Symbol n V W (m - N), ∀ x ξ,
      r.coefficient (x, ξ) =
        coefficient (x, ξ) - ∑ j ∈ Finset.range N, χ ξ • (term j).coefficient (x, ξ)

namespace ClassicalSymbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- A symbol with homogeneous terms whose remainders after cutting off with one frequency cutoff
`χ` have the right orders is classical: two cutoffs differ only at frequencies `‖ξ‖ < 2`, so the
remainders for any other cutoff differ from these by symbols of every order. -/
def ofCutoff (a : Symbol n V W m)
    (term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (χ : FrequencyCutoff (CoordinateSpace n))
    (h : ∀ N : ℕ, ∃ r : Symbol n V W (m - N), ∀ x ξ,
      r.coefficient (x, ξ) =
        a.coefficient (x, ξ) - ∑ j ∈ Finset.range N, χ ξ • (term j).coefficient (x, ξ)) :
    ClassicalSymbol n V W m where
  toSymbol := a
  term := term
  exists_remainder χ' N := by
    obtain ⟨r, hr⟩ := h N
    have hf : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n =>
        ∑ j ∈ Finset.range N, (χ p.2 - χ' p.2) • (term j).coefficient p :=
      ContDiff.sum fun j _ => by
        simpa only [sub_smul] using
          ((term j).contDiff_smul_coefficient χ).sub ((term j).contDiff_smul_coefficient χ')
    refine ⟨r + Symbol.ofBoundedFrequencySupport _ hf 2 fun x ξ hξ => ?_, fun x ξ => ?_⟩
    · simp [χ.apply_eq_one_of_two_le_norm hξ, χ'.apply_eq_one_of_two_le_norm hξ]
    · simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_ofBoundedFrequencySupport,
        hr, sub_smul, Finset.sum_sub_distrib]
      abel

@[simp]
theorem toSymbol_ofCutoff (a : Symbol n V W m)
    (term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (χ : FrequencyCutoff (CoordinateSpace n)) (h) :
    (ofCutoff a term χ h).toSymbol = a :=
  (rfl)

@[simp]
theorem term_ofCutoff (a : Symbol n V W m)
    (term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (χ : FrequencyCutoff (CoordinateSpace n)) (h) :
    (ofCutoff a term χ h).term = term :=
  (rfl)

/-! ### Uniqueness of the homogeneous terms -/

/-- **Uniqueness of the homogeneous terms.** If the difference of two classical symbols of order
`m` is a symbol of order `m - N`, their first `N` homogeneous terms agree. -/
theorem term_eq_of_exists_coefficient_eq_sub {a b : ClassicalSymbol n V W m} {N : ℕ}
    (h : ∃ r : Symbol n V W (m - N), ∀ x ξ,
      r.coefficient (x, ξ) = a.coefficient (x, ξ) - b.coefficient (x, ξ))
    {j : ℕ} (hj : j < N) : a.term j = b.term j := by
  obtain ⟨r, hr⟩ := h
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- At frequencies `‖ξ‖ ≥ 2`, where the cutoff is `1`, the difference of the `j`-th terms is the
    -- difference of the two symbols minus that of the remainders after `j + 1` terms.
    obtain ⟨ra, hra⟩ := a.exists_remainder default (j + 1)
    obtain ⟨rb, hrb⟩ := b.exists_remainder default (j + 1)
    have hle : m - (N : ℝ) ≤ m - ((j + 1 : ℕ) : ℝ) := by
      have : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
      linarith
    refine sub_eq_zero.1 (HomogeneousSymbol.eq_zero_of_coefficient_eq
      (r := Symbol.inclusion hle r - ra + rb) (R := 2) (by push_cast; linarith) fun x ξ hξ => ?_)
    have hsum : ∑ i ∈ Finset.range j, (a.term i).coefficient (x, ξ) =
        ∑ i ∈ Finset.range j, (b.term i).coefficient (x, ξ) :=
      Finset.sum_congr rfl fun i hi => by
        rw [ih i (Finset.mem_range.1 hi) ((Finset.mem_range.1 hi).trans hj)]
    simp only [HomogeneousSymbol.coefficient_sub, Pi.sub_apply, Symbol.coefficient_add,
      Symbol.coefficient_sub, Symbol.coefficient_inclusion, Pi.add_apply, hr, hra, hrb,
      FrequencyCutoff.apply_eq_one_of_two_le_norm _ hξ, one_smul, Finset.sum_range_succ, hsum]
    abel

/-- A classical symbol is determined by its underlying symbol: the homogeneous terms are
unique. -/
@[ext]
theorem ext {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol) : a = b := by
  have ht : a.term = b.term := funext fun j =>
    term_eq_of_exists_coefficient_eq_sub (N := j + 1) ⟨0, fun x ξ => by simp [h]⟩
      (Nat.lt_succ_self j)
  obtain ⟨sa, ta, _⟩ := a
  obtain ⟨sb, tb, _⟩ := b
  dsimp only at h ht
  subst h ht
  rfl

theorem toSymbol_injective :
    Function.Injective (toSymbol : ClassicalSymbol n V W m → Symbol n V W m) :=
  fun _ _ => ext

/-! ### The vector space of classical symbols -/

section Module

instance : Zero (ClassicalSymbol n V W m) where
  zero :=
    { toSymbol := 0
      term := fun _ => 0
      exists_remainder := fun _ _ => ⟨0, fun x ξ => by simp⟩ }

instance : Add (ClassicalSymbol n V W m) where
  add a b :=
    { toSymbol := a.toSymbol + b.toSymbol
      term := fun j => a.term j + b.term j
      exists_remainder := fun χ N => by
        obtain ⟨ra, hra⟩ := a.exists_remainder χ N
        obtain ⟨rb, hrb⟩ := b.exists_remainder χ N
        refine ⟨ra + rb, fun x ξ => ?_⟩
        simp only [Symbol.coefficient_add, Pi.add_apply, hra, hrb,
          HomogeneousSymbol.coefficient_add, smul_add, Finset.sum_add_distrib]
        abel }

instance : Neg (ClassicalSymbol n V W m) where
  neg a :=
    { toSymbol := -a.toSymbol
      term := fun j => -a.term j
      exists_remainder := fun χ N => by
        obtain ⟨r, hr⟩ := a.exists_remainder χ N
        refine ⟨-r, fun x ξ => ?_⟩
        simp only [Symbol.coefficient_neg, Pi.neg_apply, hr, HomogeneousSymbol.coefficient_neg,
          smul_neg, Finset.sum_neg_distrib]
        abel }

instance : SMul ℂ (ClassicalSymbol n V W m) where
  smul c a :=
    { toSymbol := c • a.toSymbol
      term := fun j => c • a.term j
      exists_remainder := fun χ N => by
        obtain ⟨r, hr⟩ := a.exists_remainder χ N
        refine ⟨c • r, fun x ξ => ?_⟩
        simp only [Symbol.coefficient_smul, Pi.smul_apply, hr, HomogeneousSymbol.coefficient_smul,
          smul_sub, Finset.smul_sum, smul_comm c (χ ξ)] }

instance : Sub (ClassicalSymbol n V W m) where
  sub a b := a + -b

instance : SMul ℕ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem toSymbol_zero : (0 : ClassicalSymbol n V W m).toSymbol = 0 := (rfl)

@[simp]
theorem toSymbol_add (a b : ClassicalSymbol n V W m) :
    (a + b).toSymbol = a.toSymbol + b.toSymbol := (rfl)

@[simp]
theorem toSymbol_neg (a : ClassicalSymbol n V W m) : (-a).toSymbol = -a.toSymbol := (rfl)

@[simp]
theorem toSymbol_smul (c : ℂ) (a : ClassicalSymbol n V W m) :
    (c • a).toSymbol = c • a.toSymbol := (rfl)

@[simp]
theorem toSymbol_sub (a b : ClassicalSymbol n V W m) :
    (a - b).toSymbol = a.toSymbol - b.toSymbol :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem toSymbol_nsmul (k : ℕ) (a : ClassicalSymbol n V W m) :
    (k • a).toSymbol = k • a.toSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toSymbol

@[simp]
theorem toSymbol_zsmul (k : ℤ) (a : ClassicalSymbol n V W m) :
    (k • a).toSymbol = k • a.toSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toSymbol

@[simp]
theorem term_zero (j : ℕ) : (0 : ClassicalSymbol n V W m).term j = 0 := (rfl)

@[simp]
theorem term_add (a b : ClassicalSymbol n V W m) (j : ℕ) :
    (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_neg (a : ClassicalSymbol n V W m) (j : ℕ) : (-a).term j = -a.term j := (rfl)

@[simp]
theorem term_smul (c : ℂ) (a : ClassicalSymbol n V W m) (j : ℕ) :
    (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_sub (a b : ClassicalSymbol n V W m) (j : ℕ) :
    (a - b).term j = a.term j - b.term j :=
  (sub_eq_add_neg _ _).symm

instance : AddCommGroup (ClassicalSymbol n V W m) :=
  toSymbol_injective.addCommGroup _ toSymbol_zero toSymbol_add toSymbol_neg toSymbol_sub
    (fun a k => toSymbol_nsmul k a) (fun a k => toSymbol_zsmul k a)

instance : Module ℂ (ClassicalSymbol n V W m) :=
  toSymbol_injective.module ℂ ⟨⟨toSymbol, toSymbol_zero⟩, toSymbol_add⟩ toSymbol_smul

end Module

/-! ### The principal symbol -/

/-- The principal symbol of a classical symbol of order `m`: its leading homogeneous term, of
degree `m`. -/
def principalSymbol :
    ClassicalSymbol n V W m →ₗ[ℂ] HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m
    where
  toFun a := (a.term 0).castDegree (by simp)
  map_add' a b := by rw [term_add, HomogeneousSymbol.castDegree_add]
  map_smul' c a := by rw [term_smul, HomogeneousSymbol.castDegree_smul, RingHom.id_apply]

theorem principalSymbol_apply (a : ClassicalSymbol n V W m) :
    principalSymbol a = (a.term 0).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principalSymbol (a : ClassicalSymbol n V W m) :
    (principalSymbol a).coefficient = (a.term 0).coefficient := by
  rw [principalSymbol_apply, HomogeneousSymbol.coefficient_castDegree]

/-- Cutting off the principal symbol leaves a remainder of order `m - 1`. -/
theorem exists_coefficient_eq_sub_principalSymbol (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : Symbol n V W (m - 1), ∀ x ξ,
      r.coefficient (x, ξ) =
        a.coefficient (x, ξ) - χ ξ • (principalSymbol a).coefficient (x, ξ) := by
  obtain ⟨r, hr⟩ := a.exists_remainder χ 1
  exact ⟨Symbol.inclusion (by simp) r, fun x ξ => by simp [hr]⟩

/-- The kernel of the principal symbol map: the principal symbol of a classical symbol of order
`m` vanishes exactly when the symbol has order `m - 1`. -/
theorem principalSymbol_eq_zero_iff {a : ClassicalSymbol n V W m} :
    principalSymbol a = 0 ↔
      ∃ r : Symbol n V W (m - 1), ∀ x ξ, r.coefficient (x, ξ) = a.coefficient (x, ξ) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := a.exists_coefficient_eq_sub_principalSymbol default
    exact ⟨r, fun x ξ => by simp [hr, h]⟩
  · rintro ⟨r, hr⟩
    have h0 : a.term 0 = (0 : ClassicalSymbol n V W m).term 0 :=
      term_eq_of_exists_coefficient_eq_sub (N := 1)
        ⟨Symbol.inclusion (by simp) r, fun x ξ => by simp [hr]⟩ zero_lt_one
    rw [principalSymbol_apply, h0, term_zero, HomogeneousSymbol.castDegree_zero]

/-! ### The classical symbol of a cut-off homogeneous term -/

/-- The classical symbol `χ(ξ) a(x, ξ)` of order `m` obtained by cutting off a homogeneous symbol
`a` of degree `m` with a frequency cutoff `χ`: its principal symbol is `a` and its lower-order
terms vanish. -/
def ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ClassicalSymbol n V W m :=
  ofCutoff (a.cutoffSymbol χ) (fun j => match j with | 0 => a.castDegree (by simp) | _ + 1 => 0) χ
    fun N => by
      cases N with
      | zero => exact ⟨Symbol.inclusion (by simp) (a.cutoffSymbol χ), fun x ξ => by simp⟩
      | succ N => exact ⟨0, fun x ξ => by simp [Finset.sum_range_succ']⟩

@[simp]
theorem toSymbol_ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (ofHomogeneous χ a).toSymbol = a.cutoffSymbol χ :=
  (rfl)

@[simp]
theorem term_ofHomogeneous_succ (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (j : ℕ) :
    (ofHomogeneous χ a).term (j + 1) = 0 :=
  (rfl)

@[simp]
theorem principalSymbol_ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    principalSymbol (ofHomogeneous χ a) = a := by
  ext1
  simp [ofHomogeneous]

/-- Every homogeneous symbol of degree `m` is the principal symbol of a classical symbol of
order `m`. -/
theorem principalSymbol_surjective :
    Function.Surjective (principalSymbol : ClassicalSymbol n V W m →ₗ[ℂ] _) :=
  fun a => ⟨ofHomogeneous default a, principalSymbol_ofHomogeneous default a⟩

end ClassicalSymbol

end TauCeti
