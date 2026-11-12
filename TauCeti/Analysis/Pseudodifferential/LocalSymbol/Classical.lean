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

For an open set `U ⊆ ℝⁿ`, a classical symbol of order `m` on `U` is a local symbol
`a ∈ S^m_{1,0}(U × ℝⁿ)` with an asymptotic expansion `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` into homogeneous
terms on `U`: each `a_{m-j}` is smooth on `U × (ℝⁿ \ {0})` and positively homogeneous of degree
`m - j`, `χ` is a frequency cutoff, and for every `N` the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` is a local symbol of order `m - N` on `U`. These are the full symbols of
classical pseudodifferential operators in a chart, whose domain is an open subset of `ℝⁿ`.

This file defines the carrier `TauCeti.LocalClassicalSymbol U V W m` and compares it with the
class `TauCeti.ClassicalSymbol n V W m` of classical symbols on `ℝⁿ`. The two classes are related by
localization: near a position of `U`, a classical symbol on `U` agrees with its extension by a
cutoff `ψ(x)` equal to `1` near that position, which is a classical symbol on `ℝⁿ`.

* `TauCeti.LocalClassicalSymbol.exists_remainder`: the expansion holds for every frequency cutoff;
* `TauCeti.LocalClassicalSymbol.term_eq_of_toLocalSymbol_eq` and
  `TauCeti.LocalClassicalSymbol.ext`: the homogeneous terms are determined by the full symbol;
* the classical symbols of order `m` on `U` form a complex vector space, termwise;
* `TauCeti.ClassicalSymbol.restrict` and `TauCeti.LocalClassicalSymbol.restrict`: a classical
  symbol restricts to every open set of positions, termwise, and restrictions compose;
* `TauCeti.ClassicalSymbol.restrictTopEquiv`: over all of `ℝⁿ`, the local classical symbols are
  exactly the classical symbols;
* `TauCeti.LocalClassicalSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `ℝⁿ` contained in `U`, a classical symbol on `U` extends by zero
  to a classical symbol on `ℝⁿ`, with terms `ψ(x) a_{m-j}(x, ξ)`; on an open set where `ψ = 1`
  the extension restricts back to the original symbol
  (`TauCeti.LocalClassicalSymbol.restrict_extend_of_eqOn_one`);
* `TauCeti.LocalClassicalSymbol.principal`: the principal symbol, compatible with restriction and
  extension, which differs from the full symbol by a local symbol of order `m - 1` after the
  frequency cutoff (`TauCeti.LocalClassicalSymbol.exists_sub_cutoffSymbol_principal`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15) and (1.17).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- A classical symbol of order `m` on the open set `U ⊆ ℝⁿ` of positions: a local symbol `a` of
order `m` on `U` together with homogeneous terms `a_{m-j}` on `U` of degree `m - j` for
`j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` is a local symbol of order `m - N` on `U`. The expansion then holds for
every cutoff (`TauCeti.LocalClassicalSymbol.exists_remainder`), and the terms are determined by
the symbol (`TauCeti.LocalClassicalSymbol.ext`). -/
structure LocalClassicalSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The full symbol. -/
  toLocalSymbol : LocalSymbol U V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → LocalHomogeneousSymbol U (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`;
  use `TauCeti.LocalClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : LocalSymbol U V W (m - N), ∀ p,
      r.coefficient p =
        toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace LocalClassicalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)}

section Extend

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- The cut-off extension `ψ(x) a(x, ξ)` of a classical symbol on `U`, a classical symbol on
`ℝⁿ`; `TauCeti.LocalClassicalSymbol.extend` is the same map, bundled as a linear map once the
vector space structure is available. -/
private def extendAux (a : LocalClassicalSymbol U V W m) : ClassicalSymbol n V W m where
  toSymbol := LocalSymbol.extend ψ hψ hψU a.toLocalSymbol
  term j := LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j)
  exists_remainder' := by
    obtain ⟨χ, hχ⟩ := a.exists_remainder'
    refine ⟨χ, fun N => ?_⟩
    obtain ⟨r, hr⟩ := hχ N
    exact ⟨LocalSymbol.extend ψ hψ hψU r, fun p => by
      simp [hr, smul_sub, Finset.smul_sum, smul_comm (ψ p.1) (χ p.2)]⟩

end Extend

section Remainder

variable (a : LocalClassicalSymbol U V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` is a local symbol of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : LocalSymbol U V W (m - N), ∀ p, r.coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  refine ⟨LocalSymbol.ofEventuallyEq _ (fun x hx ξ => by
      simp [a.toLocalSymbol.coefficient_of_notMem x hx, (a.term _).coefficient_of_notMem x hx])
    fun x hx => ?_, fun p => congrFun (LocalSymbol.coefficient_ofEventuallyEq _ _ _) p⟩
  -- Near `x`, the remainder is that of the extension of `a` by a cutoff equal to `1` near `x`.
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one
    U.isOpen (singleton_subset_iff.2 hx)
  obtain ⟨r, hr⟩ := (extendAux hψ hψU a).exists_remainder χ N
  refine ⟨r, ?_⟩
  filter_upwards [hψ1 x rfl] with y hy ξ
  simp [hr, extendAux, hy]

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` after `N` terms, a local
symbol of order `m - N`. -/
def remainder (N : ℕ) : LocalSymbol U V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols on `U` with the same full symbol
have the same homogeneous terms. -/
theorem term_eq_of_toLocalSymbol_eq {a b : LocalClassicalSymbol U V W m}
    (h : a.toLocalSymbol = b.toLocalSymbol) (j : ℕ) : a.term j = b.term j := by
  refine LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => ?_
  -- Compare the extensions of `a` and `b` by a cutoff equal to `1` near `x`.
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one U.isOpen
      (singleton_subset_iff.2 hx)
  have hab := congrArg (fun c => HomogeneousSymbol.coefficient c (x, ξ))
    (ClassicalSymbol.term_eq_of_toSymbol_eq (a := extendAux hψ hψU a) (b := extendAux hψ hψU b)
      (by simp [extendAux, h]) j)
  simpa [extendAux, (hψ1 x rfl).self_of_nhds] using hab

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
theorem toLocalSymbol_sub : (a - b).toLocalSymbol = a.toLocalSymbol - b.toLocalSymbol :=
  (congrArg (a.toLocalSymbol + ·) (toLocalSymbol_neg b)).trans (sub_eq_add_neg _ _).symm

@[simp]
theorem toLocalSymbol_nsmul (k : ℕ) : (k • a).toLocalSymbol = k • a.toLocalSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toLocalSymbol

@[simp]
theorem toLocalSymbol_zsmul (k : ℤ) : (k • a).toLocalSymbol = k • a.toLocalSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toLocalSymbol

instance : AddCommGroup (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.addCommGroup _ toLocalSymbol_zero toLocalSymbol_add toLocalSymbol_neg
    toLocalSymbol_sub (fun a k => toLocalSymbol_nsmul a k) (fun a k => toLocalSymbol_zsmul a k)

instance : Module ℂ (LocalClassicalSymbol U V W m) :=
  toLocalSymbol_injective.module ℂ ⟨⟨toLocalSymbol, toLocalSymbol_zero⟩, toLocalSymbol_add⟩
    fun c a => toLocalSymbol_smul a c

@[simp]
theorem term_zero : (0 : LocalClassicalSymbol U V W m).term j = 0 := (rfl)

@[simp]
theorem term_add : (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_smul : (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_neg : (-a).term j = -a.term j :=
  (neg_one_smul ℂ (a.term j))

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j :=
  (congrArg (a.term j + ·) (term_neg b j)).trans (sub_eq_add_neg _ _).symm

end Module

/-! ### Extension by a cutoff -/

section Extend

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- The extension by zero of the cut-off symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ` whose
support is a closed subset of `ℝⁿ` contained in `U`: a classical symbol on `ℝⁿ`, whose homogeneous
terms are the cut-off terms `ψ(x) a_{m-j}(x, ξ)`. -/
def extend (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    LocalClassicalSymbol U V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun := extendAux hψ hψU
  map_add' a b := ClassicalSymbol.ext (by simp [extendAux])
  map_smul' c a := ClassicalSymbol.ext (by simp [extendAux])

@[simp]
theorem toSymbol_extend (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).toSymbol = LocalSymbol.extend ψ hψ hψU a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_extend (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (extend ψ hψ hψU a).term j = LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j) :=
  (rfl)

end Extend

/-! ### Restriction to a smaller open set -/

section Restrict

/-- The restriction of a classical symbol on `U` to a smaller open set `U'`, termwise: the full
symbol and each homogeneous term are restricted to `U'`. -/
def restrict (h : U' ≤ U) : LocalClassicalSymbol U V W m →ₗ[ℂ] LocalClassicalSymbol U' V W m where
  toFun a :=
    { toLocalSymbol := LocalSymbol.restrict h a.toLocalSymbol
      term j := LocalHomogeneousSymbol.restrict h (a.term j)
      exists_remainder' := ⟨default, fun N => ⟨LocalSymbol.restrict h (a.remainder default N),
        fun ⟨x, ξ⟩ => by by_cases hx : x ∈ U' <;> simp [hx]⟩⟩ }
  map_add' a b := ext (map_add _ _ _)
  map_smul' c a := ext (map_smul _ _ _)

@[simp]
theorem toLocalSymbol_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).toLocalSymbol = LocalSymbol.restrict h a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (restrict h a).term j = LocalHomogeneousSymbol.restrict h (a.term j) :=
  (rfl)

@[simp]
theorem restrict_self (a : LocalClassicalSymbol U V W m) : restrict le_rfl a = a :=
  ext (LocalSymbol.restrict_self _)

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalClassicalSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext (LocalSymbol.restrict_restrict h h' _)

end Restrict

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

/-- The restriction of a classical symbol on `ℝⁿ` to the open set `U` of positions, termwise: the
full symbol and each homogeneous term are restricted to `U`. -/
def restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    ClassicalSymbol n V W m →ₗ[ℂ] LocalClassicalSymbol U V W m where
  toFun a :=
    { toLocalSymbol := a.toSymbol.restrict U
      term j := (a.term j).restrict U
      exists_remainder' := ⟨default, fun N => ⟨(a.remainder default N).restrict U,
        fun ⟨x, ξ⟩ => by by_cases hx : x ∈ U <;> simp [hx]⟩⟩ }
  map_add' a b := LocalClassicalSymbol.ext (by simp)
  map_smul' c a := LocalClassicalSymbol.ext (by simp)

@[simp]
theorem toLocalSymbol_restrict (a : ClassicalSymbol n V W m) :
    (a.restrict U).toLocalSymbol = a.toSymbol.restrict U :=
  (rfl)

@[simp]
theorem term_restrict (a : ClassicalSymbol n V W m) (j : ℕ) :
    (a.restrict U).term j = (a.term j).restrict U :=
  (rfl)

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : ClassicalSymbol n V W m) :
    LocalClassicalSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalClassicalSymbol.ext (Symbol.restrict_restrict h _)

/-- Over all of `ℝⁿ`, the local classical symbols are exactly the classical symbols: restriction
to `⊤` is a linear equivalence. -/
def restrictTopEquiv :
    ClassicalSymbol n V W m ≃ₗ[ℂ]
      LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  __ := restrict ⊤
  invFun a :=
    { toSymbol := Symbol.restrictTopEquiv.symm a.toLocalSymbol
      term j := HomogeneousSymbol.restrictTopEquiv.symm (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv.symm (a.remainder default N), fun p => by simp⟩⟩ }
  left_inv a := ClassicalSymbol.ext <| Symbol.ext <| funext fun p => by simp
  right_inv a := LocalClassicalSymbol.ext <| LocalSymbol.ext_of_mem fun x _ ξ => by simp

@[simp]
theorem restrictTopEquiv_apply (a : ClassicalSymbol n V W m) :
    restrictTopEquiv a = a.restrict ⊤ :=
  (rfl)

@[simp]
theorem toSymbol_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) :
    (restrictTopEquiv.symm a).toSymbol = Symbol.restrictTopEquiv.symm a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_restrictTopEquiv_symm_apply
    (a : LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m) (j : ℕ) :
    (restrictTopEquiv.symm a).term j = HomogeneousSymbol.restrictTopEquiv.symm (a.term j) :=
  (rfl)

end ClassicalSymbol

/-! ### The principal symbol -/

namespace LocalClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

section Extend

variable {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the extension restricts to the
restriction of the original symbol. -/
theorem restrict_extend_of_eqOn_one (h : U' ≤ U) (hψ1 : EqOn ψ 1 U')
    (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext (LocalSymbol.restrict_extend_of_eqOn_one hψ hψU h hψ1 _)

end Extend

section Principal

variable (a b : LocalClassicalSymbol U V W m)

/-- The principal symbol of a classical symbol of order `m` on `U`: its leading homogeneous term
`a_m`, of degree `m`. -/
def principal : LocalHomogeneousSymbol U (CoordinateSpace n) V W m :=
  (a.term 0).castDegree (by simp)

theorem principal_def : a.principal = (a.term 0).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  LocalHomogeneousSymbol.coefficient_castDegree _ _

/-- A classical symbol on `U` and its cut-off principal symbol differ by a local symbol of order
`m - 1`. -/
theorem exists_sub_cutoffSymbol_principal (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : LocalSymbol U V W (m - 1),
      r.coefficient =
        (a.toLocalSymbol - LocalHomogeneousSymbol.cutoffSymbol χ a.principal).coefficient :=
  ⟨LocalSymbol.inclusion (by simp) (a.remainder χ 1), funext fun p => by simp⟩

@[simp]
theorem principal_zero : (0 : LocalClassicalSymbol U V W m).principal = 0 :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal :=
  LocalHomogeneousSymbol.ext (by simp)

@[simp]
theorem principal_restrict (h : U' ≤ U) :
    (restrict h a).principal = LocalHomogeneousSymbol.restrict h a.principal :=
  LocalHomogeneousSymbol.ext (by simp [LocalHomogeneousSymbol.coefficient_restrict])

@[simp]
theorem principal_extend {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) :
    (extend ψ hψ hψU a).principal = LocalHomogeneousSymbol.extend ψ hψ hψU a.principal :=
  HomogeneousSymbol.ext (funext fun p => by simp [ClassicalSymbol.coefficient_principal])

end Principal

end LocalClassicalSymbol

/-- The principal symbol of the restriction of a classical symbol is the restriction of its
principal symbol. -/
@[simp]
theorem ClassicalSymbol.principal_restrict {U : TopologicalSpace.Opens (CoordinateSpace n)}
    (a : ClassicalSymbol n V W m) : (a.restrict U).principal = a.principal.restrict U :=
  LocalHomogeneousSymbol.ext (by simp [HomogeneousSymbol.coefficient_restrict])

end TauCeti
