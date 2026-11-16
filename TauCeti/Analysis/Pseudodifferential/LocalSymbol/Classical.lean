/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Homogeneous
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Classical symbols on an open set of positions

For an open set `U ⊆ ℝⁿ`, a classical symbol of order `m` on `U` is a symbol `a` of order `m` on
`U × ℝⁿ` (`TauCeti.LocalSymbol`) with an asymptotic expansion `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` into
homogeneous symbols `a_{m-j}` of degree `m - j` on `U` (`TauCeti.LocalHomogeneousSymbol`): for a
frequency cutoff `χ` and every `N`, the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order
`m - N` on `U`. These are the full symbols of classical pseudodifferential operators read in a chart
of a manifold, whose domain is an open subset of `ℝⁿ`; their homogeneous terms need not extend
smoothly to positions outside `U`.

This file defines the carrier `TauCeti.LocalClassicalSymbol U V W m` and relates it to the
classical symbols `TauCeti.ClassicalSymbol n V W m` on `ℝⁿ`:

* `TauCeti.ClassicalSymbol.restrictTopEquiv`: the classical symbols on `⊤` are the classical
  symbols on `ℝⁿ`;
* `TauCeti.ClassicalSymbol.restrict`: a classical symbol on `ℝⁿ` restricts to a classical symbol
  on `U`, with the restricted homogeneous terms;
* `TauCeti.LocalClassicalSymbol.restrict`: a classical symbol on `U` restricts to every smaller open
  set, and restrictions compose;
* `TauCeti.LocalClassicalSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `ℝⁿ` contained in `U`, a classical symbol on `U` extends by zero
  to a classical symbol on `ℝⁿ`, with the cut-off homogeneous terms; restricting it to an open set
  on which `ψ = 1` recovers the restriction of the original symbol
  (`TauCeti.LocalClassicalSymbol.restrict_extend_of_eqOn_one`).

Through these extensions the facts about classical symbols on `ℝⁿ` localize:

* `TauCeti.LocalClassicalSymbol.exists_remainder`: the expansion holds for every frequency cutoff,
  with the remainder `TauCeti.LocalClassicalSymbol.remainder χ N` of order `m - N`;
* `TauCeti.LocalClassicalSymbol.term_eq_of_toLocalSymbol_eq` and
  `TauCeti.LocalClassicalSymbol.ext`: the homogeneous terms are determined by the symbol;
* the classical symbols of order `m` on `U` form a complex vector space, termwise, and restriction
  and extension are linear.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definitions 18.1.1
  and 18.1.5.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15) and (1.17).
-/

public section

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace TauCeti

variable {n : ℕ}

/-- A classical symbol of order `m` on `U × ℝⁿ`, for an open set `U ⊆ ℝⁿ` of positions: a symbol
`a` of order `m` on `U` together with homogeneous terms `a_{m-j}` of degree `m - j` on `U` for
`j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N` on `U`. The expansion then holds for every
cutoff (`TauCeti.LocalClassicalSymbol.exists_remainder`), and the terms are determined by the
symbol (`TauCeti.LocalClassicalSymbol.ext`). -/
structure LocalClassicalSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The full symbol. -/
  toLocalSymbol : LocalSymbol U V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → LocalHomogeneousSymbol U V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`
  on `U`; use `TauCeti.LocalClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : LocalSymbol U V W (m - N), ∀ p,
      r.coefficient p =
        toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace LocalClassicalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

section Extend

/-- The cut-off extension `ψ(x) a(x, ξ)` of a classical symbol on `U`, as a classical symbol on
`ℝⁿ`; `TauCeti.LocalClassicalSymbol.extend` is this map as a linear map. -/
private def extendAux (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)
    (a : LocalClassicalSymbol U V W m) : ClassicalSymbol n V W m where
  toSymbol := LocalSymbol.extend ψ hψ hψU a.toLocalSymbol
  term j := LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j)
  exists_remainder' := by
    obtain ⟨χ, h⟩ := a.exists_remainder'
    refine ⟨χ, fun N => ?_⟩
    obtain ⟨r, hr⟩ := h N
    refine ⟨LocalSymbol.extend ψ hψ hψU r, fun p => ?_⟩
    simp only [LocalSymbol.coefficient_extend, LocalHomogeneousSymbol.coefficient_extend, hr,
      smul_sub, Finset.smul_sum, smul_comm (ψ p.1)]

private theorem toSymbol_extendAux (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (a : LocalClassicalSymbol U V W m) :
    (extendAux ψ hψ hψU a).toSymbol = LocalSymbol.extend ψ hψ hψU a.toLocalSymbol :=
  (rfl)

private theorem term_extendAux (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (extendAux ψ hψ hψU a).term j = LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j) :=
  (rfl)

end Extend

section Remainder

variable (a : LocalClassicalSymbol U V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` is a symbol of order `m - N` on `U`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : LocalSymbol U V W (m - N), ∀ p, r.coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  refine ⟨LocalSymbol.ofEventuallyEq _ (fun x hx ξ => ?_) fun x hx => ?_,
    fun p => congrFun (LocalSymbol.coefficient_ofEventuallyEq _ _ _) p⟩
  · simp [a.toLocalSymbol.coefficient_of_notMem x hx ξ,
      fun j => (a.term j).coefficient_of_notMem x hx ξ]
  · obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one
      U.isOpen (singleton_subset_iff.2 hx)
    refine ⟨(extendAux ψ hψ hψU a).remainder χ N, ?_⟩
    filter_upwards [hψ1 x rfl] with y hy η
    simp [toSymbol_extendAux, term_extendAux, hy]

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` after `N` terms, a symbol
of order `m - N` on `U`. -/
def remainder (N : ℕ) : LocalSymbol U V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

/-- The remainder after `N` terms, included in the symbols of order `m` on `U`, is the full symbol
minus the first `N` cut-off terms. -/
theorem inclusion_remainder (N : ℕ) :
    LocalSymbol.inclusion (by simp) (a.remainder χ N) = a.toLocalSymbol -
      ∑ k ∈ Finset.range N, LocalSymbol.inclusion (by simp)
        (LocalHomogeneousSymbol.cutoffSymbol χ (a.term k)) := by
  ext1
  funext p
  simp

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols on `U` with the same full
symbol have the same homogeneous terms. -/
theorem term_eq_of_toLocalSymbol_eq {a b : LocalClassicalSymbol U V W m}
    (h : a.toLocalSymbol = b.toLocalSymbol) (j : ℕ) : a.term j = b.term j := by
  refine LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => ?_
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one U.isOpen
      (singleton_subset_iff.2 hx)
  have hext := congrArg (fun c : HomogeneousSymbol _ _ V W (m - j) => c.coefficient (x, ξ))
    (ClassicalSymbol.term_eq_of_toSymbol_eq (a := extendAux ψ hψ hψU a)
      (b := extendAux ψ hψ hψU b) (by rw [toSymbol_extendAux, toSymbol_extendAux, h]) j)
  simpa [term_extendAux, (hψ1 x rfl).self_of_nhds] using hext

/-- A classical symbol on `U` is determined by its full symbol. -/
@[ext]
theorem ext {a b : LocalClassicalSymbol U V W m} (h : a.toLocalSymbol = b.toLocalSymbol) :
    a = b := by
  have ht : a.term = b.term := funext (term_eq_of_toLocalSymbol_eq h)
  cases a
  cases b
  cases h
  cases ht
  rfl

theorem toLocalSymbol_injective :
    Function.Injective (toLocalSymbol : LocalClassicalSymbol U V W m → LocalSymbol U V W m) :=
  fun _ _ => ext

end Uniqueness

/-! ### The vector space of classical symbols of order `m` on `U` -/

section Module

instance : Zero (LocalClassicalSymbol U V W m) where
  zero :=
    { toLocalSymbol := 0
      term _ := 0
      exists_remainder' := ⟨default, fun _ => ⟨0, fun p => by simp⟩⟩ }

instance : Add (LocalClassicalSymbol U V W m) where
  add a b :=
    { toLocalSymbol := a.toLocalSymbol + b.toLocalSymbol
      term j := a.term j + b.term j
      exists_remainder' := ⟨default, fun N => ⟨a.remainder default N + b.remainder default N,
        fun p => by
          simp only [LocalSymbol.coefficient_add, Pi.add_apply, coefficient_remainder,
            LocalHomogeneousSymbol.coefficient_add, smul_add, Finset.sum_add_distrib]
          abel⟩⟩ }

instance : SMul ℂ (LocalClassicalSymbol U V W m) where
  smul c a :=
    { toLocalSymbol := c • a.toLocalSymbol
      term j := c • a.term j
      exists_remainder' := ⟨default, fun N => ⟨c • a.remainder default N, fun p => by
        simp only [LocalSymbol.coefficient_smul, Pi.smul_apply, coefficient_remainder,
          LocalHomogeneousSymbol.coefficient_smul, smul_sub, Finset.smul_sum, smul_comm c]⟩⟩ }

instance : Neg (LocalClassicalSymbol U V W m) where
  neg a := (-1 : ℂ) • a

instance : Sub (LocalClassicalSymbol U V W m) where
  sub a b := a + -b

instance : SMul ℕ (LocalClassicalSymbol U V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (LocalClassicalSymbol U V W m) where
  smul k a := (k : ℂ) • a

variable (a b : LocalClassicalSymbol U V W m) (c : ℂ) (j : ℕ)

@[simp]
theorem toLocalSymbol_zero : (0 : LocalClassicalSymbol U V W m).toLocalSymbol = 0 := (rfl)

@[simp]
theorem toLocalSymbol_add : (a + b).toLocalSymbol = a.toLocalSymbol + b.toLocalSymbol := (rfl)

@[simp]
theorem toLocalSymbol_smul : (c • a).toLocalSymbol = c • a.toLocalSymbol := (rfl)

@[simp]
theorem toLocalSymbol_neg : (-a).toLocalSymbol = -a.toLocalSymbol :=
  neg_one_smul ℂ a.toLocalSymbol

@[simp]
theorem toLocalSymbol_sub : (a - b).toLocalSymbol = a.toLocalSymbol - b.toLocalSymbol := by
  rw [sub_eq_add_neg a.toLocalSymbol]
  exact congrArg (a.toLocalSymbol + ·) (toLocalSymbol_neg b)

@[simp]
theorem toLocalSymbol_nsmul (k : ℕ) : (k • a).toLocalSymbol = k • a.toLocalSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toLocalSymbol

@[simp]
theorem toLocalSymbol_zsmul (k : ℤ) : (k • a).toLocalSymbol = k • a.toLocalSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toLocalSymbol

@[simp]
theorem term_zero : (0 : LocalClassicalSymbol U V W m).term j = 0 := (rfl)

@[simp]
theorem term_add : (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_smul : (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_neg : (-a).term j = -a.term j :=
  neg_one_smul ℂ (a.term j)

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j := by
  rw [sub_eq_add_neg (a.term j)]
  exact congrArg (a.term j + ·) (term_neg b j)

@[simp]
theorem term_nsmul (k : ℕ) : (k • a).term j = k • a.term j :=
  Nat.cast_smul_eq_nsmul ℂ k (a.term j)

@[simp]
theorem term_zsmul (k : ℤ) : (k • a).term j = k • a.term j :=
  Int.cast_smul_eq_zsmul ℂ k (a.term j)

instance : AddCommGroup (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.addCommGroup _ toLocalSymbol_zero toLocalSymbol_add toLocalSymbol_neg
    toLocalSymbol_sub (fun a k => toLocalSymbol_nsmul a k) (fun a k => toLocalSymbol_zsmul a k)

instance : Module ℂ (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.module ℂ ⟨⟨toLocalSymbol, toLocalSymbol_zero⟩, toLocalSymbol_add⟩
    fun c a => toLocalSymbol_smul a c

@[simp]
theorem toLocalSymbol_sum {ι : Type*} (s : Finset ι) (a : ι → LocalClassicalSymbol U V W m) :
    (∑ i ∈ s, a i).toLocalSymbol = ∑ i ∈ s, (a i).toLocalSymbol :=
  map_sum (AddMonoidHom.mk' toLocalSymbol toLocalSymbol_add) a s

@[simp]
theorem term_sum {ι : Type*} (s : Finset ι) (a : ι → LocalClassicalSymbol U V W m) (j : ℕ) :
    (∑ i ∈ s, a i).term j = ∑ i ∈ s, (a i).term j :=
  map_sum (AddMonoidHom.mk' (fun a : LocalClassicalSymbol U V W m => a.term j)
    fun a b => term_add a b j) a s

variable (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ)

@[simp]
theorem remainder_zero : (0 : LocalClassicalSymbol U V W m).remainder χ N = 0 :=
  LocalSymbol.ext (funext fun p => by simp)

@[simp]
theorem remainder_add : (a + b).remainder χ N = a.remainder χ N + b.remainder χ N :=
  LocalSymbol.ext (funext fun p => by
    simp only [coefficient_remainder, toLocalSymbol_add, LocalSymbol.coefficient_add,
      Pi.add_apply, term_add, LocalHomogeneousSymbol.coefficient_add, smul_add,
      Finset.sum_add_distrib]
    abel)

@[simp]
theorem remainder_smul : (c • a).remainder χ N = c • a.remainder χ N :=
  LocalSymbol.ext (funext fun p => by
    simp only [coefficient_remainder, toLocalSymbol_smul, LocalSymbol.coefficient_smul,
      Pi.smul_apply, term_smul, LocalHomogeneousSymbol.coefficient_smul, smul_sub, Finset.smul_sum,
      smul_comm c])

@[simp]
theorem remainder_neg : (-a).remainder χ N = -a.remainder χ N := by
  rw [← neg_one_smul ℂ a, remainder_smul, neg_one_smul]

@[simp]
theorem remainder_sub : (a - b).remainder χ N = a.remainder χ N - b.remainder χ N := by
  rw [sub_eq_add_neg a b, remainder_add, remainder_neg, sub_eq_add_neg (a.remainder χ N)]

@[simp]
theorem remainder_nsmul (k : ℕ) : (k • a).remainder χ N = k • a.remainder χ N := by
  rw [← Nat.cast_smul_eq_nsmul ℂ k a, remainder_smul, Nat.cast_smul_eq_nsmul]

@[simp]
theorem remainder_zsmul (k : ℤ) : (k • a).remainder χ N = k • a.remainder χ N := by
  rw [← Int.cast_smul_eq_zsmul ℂ k a, remainder_smul, Int.cast_smul_eq_zsmul]

@[simp]
theorem remainder_sum {ι : Type*} (s : Finset ι) (a : ι → LocalClassicalSymbol U V W m) :
    (∑ i ∈ s, a i).remainder χ N = ∑ i ∈ s, (a i).remainder χ N :=
  map_sum (AddMonoidHom.mk' (fun a : LocalClassicalSymbol U V W m => a.remainder χ N)
    fun a b => remainder_add a b χ N) a s

end Module

section Extend

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- The extension by zero of the cut-off classical symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ`
whose support is a closed subset of `ℝⁿ` contained in `U`: a classical symbol on `ℝⁿ`, whose
homogeneous terms are the cut-off terms `ψ(x) a_{m-j}(x, ξ)`. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalClassicalSymbol U V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun := extendAux ψ hψ hψU
  map_add' _ _ := ClassicalSymbol.ext (map_add (LocalSymbol.extend ψ hψ hψU) _ _)
  map_smul' c _ := ClassicalSymbol.ext (map_smul (LocalSymbol.extend ψ hψ hψU) c _)

@[simp]
theorem toSymbol_extend (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).toSymbol = LocalSymbol.extend ψ hψ hψU a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_extend (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (extend ψ hψ hψU a).term j = LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j) :=
  (rfl)

/-- The remainders of the cut-off extension are the cut-off extensions of the remainders. -/
@[simp]
theorem remainder_extend (a : LocalClassicalSymbol U V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    (extend ψ hψ hψU a).remainder χ N = LocalSymbol.extend ψ hψ hψU (a.remainder χ N) :=
  Symbol.ext (funext fun p => by
    simp [smul_sub, Finset.smul_sum, smul_comm (ψ p.1)])

end Extend

section Restrict

/-- The restriction of a classical symbol on `U` to a smaller open set `U'`, with the restricted
homogeneous terms. -/
def restrict (h : U' ≤ U) : LocalClassicalSymbol U V W m →ₗ[ℂ] LocalClassicalSymbol U' V W m where
  toFun a :=
    { toLocalSymbol := LocalSymbol.restrict h a.toLocalSymbol
      term j := LocalHomogeneousSymbol.restrict h (a.term j)
      exists_remainder' := ⟨default, fun N => ⟨LocalSymbol.restrict h (a.remainder default N),
        fun ⟨x, ξ⟩ => by by_cases hx : x ∈ U' <;> simp [hx]⟩⟩ }
  map_add' a b := ext (by simp)
  map_smul' c a := ext (by simp)

@[simp]
theorem toLocalSymbol_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).toLocalSymbol = LocalSymbol.restrict h a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (restrict h a).term j = LocalHomogeneousSymbol.restrict h (a.term j) :=
  (rfl)

/-- The remainders of the restriction are the restrictions of the remainders. -/
@[simp]
theorem remainder_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    (restrict h a).remainder χ N = LocalSymbol.restrict h (a.remainder χ N) :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

@[simp]
theorem restrict_self (a : LocalClassicalSymbol U V W m) : restrict le_rfl a = a :=
  ext (by simp)

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalClassicalSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext (by simp)

end Restrict

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Over all of `ℝⁿ`, the classical symbols on an open set are exactly the classical symbols on
`ℝⁿ × ℝⁿ`: a classical symbol on `ℝⁿ × ℝⁿ` is a classical symbol on `⊤` with the same full symbol
and homogeneous terms, and this is a linear equivalence. -/
def restrictTopEquiv : ClassicalSymbol n V W m ≃ₗ[ℂ]
    LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  toFun a :=
    { toLocalSymbol := Symbol.restrictTopEquiv a.toSymbol
      term j := HomogeneousSymbol.restrictTopEquiv (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv (a.remainder default N), fun p => by simp⟩⟩ }
  map_add' _ _ := LocalClassicalSymbol.ext (by simp)
  map_smul' _ _ := LocalClassicalSymbol.ext (by simp)
  invFun a :=
    { toSymbol := Symbol.restrictTopEquiv.symm a.toLocalSymbol
      term j := HomogeneousSymbol.restrictTopEquiv.symm (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv.symm (a.remainder default N), fun p => by simp⟩⟩ }
  left_inv a := ClassicalSymbol.ext (Symbol.restrictTopEquiv.symm_apply_apply a.toSymbol)
  right_inv a := LocalClassicalSymbol.ext (Symbol.restrictTopEquiv.apply_symm_apply a.toLocalSymbol)

@[simp]
theorem toLocalSymbol_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) :
    (restrictTopEquiv a).toLocalSymbol = Symbol.restrictTopEquiv a.toSymbol := (rfl)

@[simp]
theorem term_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) (j : ℕ) :
    (restrictTopEquiv a).term j = HomogeneousSymbol.restrictTopEquiv (a.term j) := (rfl)

@[simp]
theorem toSymbol_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    (restrictTopEquiv.symm a : ClassicalSymbol n V W m).toSymbol =
      Symbol.restrictTopEquiv.symm a.toLocalSymbol := (rfl)

@[simp]
theorem term_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) (j : ℕ) :
    (restrictTopEquiv.symm a : ClassicalSymbol n V W m).term j =
      HomogeneousSymbol.restrictTopEquiv.symm (a.term j) := (rfl)

/-- The remainders of the classical symbol on `⊤` corresponding to a classical symbol on `ℝⁿ` are
the local symbols corresponding to its remainders. -/
@[simp]
theorem remainder_restrictTopEquiv_apply (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    (restrictTopEquiv a).remainder χ N = Symbol.restrictTopEquiv (a.remainder χ N) :=
  LocalSymbol.ext (funext fun p => by simp)

/-- The remainders of the classical symbol on `ℝⁿ` corresponding to a classical symbol on `⊤` are
the symbols corresponding to its remainders. -/
@[simp]
theorem remainder_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    (restrictTopEquiv.symm a : ClassicalSymbol n V W m).remainder χ N =
      Symbol.restrictTopEquiv.symm (a.remainder χ N) :=
  Symbol.ext (funext fun p => by simp)

variable (U) in
/-- The restriction of a classical symbol on `ℝⁿ` to the open set `U` of positions: the restriction
from `⊤` to `U` of the corresponding classical symbol on `⊤`, with the restricted full symbol and
homogeneous terms. -/
def restrict : ClassicalSymbol n V W m →ₗ[ℂ] LocalClassicalSymbol U V W m :=
  LocalClassicalSymbol.restrict le_top ∘ₗ restrictTopEquiv.toLinearMap

@[simp]
theorem toLocalSymbol_restrict (a : ClassicalSymbol n V W m) :
    (restrict U a).toLocalSymbol = a.toSymbol.restrict U :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [restrict, hx]

@[simp]
theorem term_restrict (a : ClassicalSymbol n V W m) (j : ℕ) :
    (restrict U a).term j = HomogeneousSymbol.restrict U (a.term j) :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [restrict, hx]

/-- The remainders of the restriction are the restrictions of the remainders. -/
@[simp]
theorem remainder_restrict (a : ClassicalSymbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n))
    (N : ℕ) : (restrict U a).remainder χ N = (a.remainder χ N).restrict U :=
  LocalSymbol.ext_of_mem fun x hx ξ => by simp [hx]

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : ClassicalSymbol n V W m) :
    LocalClassicalSymbol.restrict h (restrict U a) = restrict U' a :=
  LocalClassicalSymbol.restrict_restrict le_top h (restrictTopEquiv a)

/-- Restricting a classical symbol to all of `ℝⁿ` gives the corresponding classical symbol on
`⊤`. -/
@[simp]
theorem restrict_top (a : ClassicalSymbol n V W m) : restrict ⊤ a = restrictTopEquiv a :=
  LocalClassicalSymbol.restrict_self (restrictTopEquiv a)

/-- Restricting the classical symbol on `⊤` corresponding to a classical symbol on `ℝⁿ` gives the
restriction of that classical symbol. -/
@[simp]
theorem restrict_restrictTopEquiv (h : U ≤ ⊤) (a : ClassicalSymbol n V W m) :
    LocalClassicalSymbol.restrict h (restrictTopEquiv a) = restrict U a :=
  (rfl)

end ClassicalSymbol

namespace LocalClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the cut-off extension restricts to the
restriction of the original classical symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalClassicalSymbol U V W m) :
    ClassicalSymbol.restrict U' (extend ψ hψ hψU a) = restrict h a :=
  ext (by simp [LocalSymbol.restrict_extend_of_eqOn_one hψ hψU h hψ1])

/-- For a cutoff supported in a smaller open set `U' ⊆ U`, extending the restriction to `U'` is
extending the original classical symbol. -/
@[simp]
theorem extend_restrict (h : U' ≤ U) (hψU' : tsupport ψ ⊆ U') (a : LocalClassicalSymbol U V W m) :
    extend ψ hψ hψU' (restrict h a) = extend ψ hψ (hψU'.trans h) a :=
  ClassicalSymbol.ext (by simp)

end LocalClassicalSymbol

end TauCeti
