/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.LocalHomogeneous
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Classical symbols on an open set of positions

In a chart of a manifold the symbols live on `U × ℝⁿ` for an open set `U ⊆ ℝⁿ` of positions
(`TauCeti.LocalSymbol`). This file restricts the classical symbols of
`TauCeti/Analysis/Pseudodifferential/Symbol/Classical.lean` to such open sets, with homogeneous
terms the homogeneous symbols on `U` of
`TauCeti/Analysis/Pseudodifferential/Symbol/LocalHomogeneous.lean`.

A *classical symbol of order `m` on `U`* (`TauCeti.LocalClassicalSymbol`) is a symbol `a` of
order `m` on `U` with homogeneous terms `a_{m-j}` of degree `m - j` on `U`, such that for some
frequency cutoff `χ` every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N` on
`U`. All statements are reduced to the classical symbols on `ℝⁿ` through the cut-off extensions
`TauCeti.LocalClassicalSymbol.extend`, using that a function which near every compact subset of
`U` agrees with a symbol on `ℝⁿ` is a symbol on `U` (`TauCeti.LocalSymbol.ofLocal`). We prove:

* `TauCeti.LocalClassicalSymbol.exists_remainder`: the expansion holds for every frequency
  cutoff;
* `TauCeti.LocalClassicalSymbol.term_eq_of_toLocalSymbol_eq` and
  `TauCeti.LocalClassicalSymbol.ext`: the homogeneous terms are determined by the full symbol;
* the classical symbols of order `m` on `U` form a complex vector space, termwise;
* `TauCeti.ClassicalSymbol.restrict` and `TauCeti.LocalClassicalSymbol.restrict`: a classical
  symbol restricts to a classical symbol on every smaller open set, with the restricted
  homogeneous terms and principal symbol, and restrictions compose;
* `TauCeti.ClassicalSymbol.restrictTopEquiv`: over all of `ℝⁿ` restriction is a linear
  equivalence, so the local classical symbols on `⊤` are exactly `TauCeti.ClassicalSymbol`;
* `TauCeti.LocalClassicalSymbol.extend`: after multiplication by a smooth cutoff `ψ(x)` whose
  support is a closed subset of `U`, a classical symbol on `U` extends by zero to a classical
  symbol on `ℝⁿ`, with the extended homogeneous terms; restricting it to an open set on which
  `ψ = 1` recovers the restriction of the original symbol
  (`TauCeti.LocalClassicalSymbol.restrict_extend_of_eqOn_one`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace TauCeti

/-! ### Classical symbols on an open set of positions -/

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- A classical symbol of order `m` on the open set `U` of positions: a symbol `a` of order `m` on
`U` together with homogeneous terms `a_{m-j}` of degree `m - j` on `U` for `j = 0, 1, 2, …`, such
that for some frequency cutoff `χ` and every `N`, the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a
symbol of order `m - N` on `U`. The expansion then holds for every cutoff
(`TauCeti.LocalClassicalSymbol.exists_remainder`), and the terms are determined by the symbol
(`TauCeti.LocalClassicalSymbol.ext`). -/
structure LocalClassicalSymbol (U : TopologicalSpace.Opens (CoordinateSpace n)) (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (m : ℝ) where
  /-- The full symbol. -/
  toLocalSymbol : LocalSymbol U V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → LocalHomogeneousSymbol U (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`
  on `U`; use `TauCeti.LocalClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : LocalSymbol U V W (m - N), ∀ p,
      r.coefficient p =
        toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace LocalClassicalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)} {ψ : CoordinateSpace n → ℝ}

/-- The cut-off extension of a classical symbol on `U`, before the linear structure is in place;
see `TauCeti.LocalClassicalSymbol.extend`. -/
private def extendAux (ψ : CoordinateSpace n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)
    (a : LocalClassicalSymbol U V W m) : ClassicalSymbol n V W m where
  toSymbol := LocalSymbol.extend ψ hψ hψU a.toLocalSymbol
  term j := LocalHomogeneousSymbol.extend ψ hψ hψU (a.term j)
  exists_remainder' := by
    obtain ⟨χ, h⟩ := a.exists_remainder'
    refine ⟨χ, fun N => ?_⟩
    obtain ⟨r, hr⟩ := h N
    exact ⟨LocalSymbol.extend ψ hψ hψU r, fun p => by
      simp [hr, smul_sub, Finset.smul_sum, smul_comm (ψ p.1) (χ p.2)]⟩

section Remainder

variable (a : LocalClassicalSymbol U V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` is a symbol of order `m - N` on `U`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : LocalSymbol U V W (m - N), ∀ p, r.coefficient p =
      a.toLocalSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  refine ⟨LocalSymbol.ofLocal (fun p => a.toLocalSymbol.coefficient p -
      ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p) (fun x hx ξ => ?_)
    fun K hKU hK => ?_, fun p => by simp⟩
  · simp [a.toLocalSymbol.coefficient_of_notMem x hx ξ, (a.term _).coefficient_of_notMem x hx ξ]
  · -- Near `K` the remainder is that of a cut-off extension equal to `a` near `K`.
    obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one U.isOpen hKU
    refine ⟨(a.extendAux ψ hψ hψU).remainder χ N, fun x hx => ?_⟩
    filter_upwards [hψ1 x hx] with y hy ξ
    simp [extendAux, hy]

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol on `U` after `N` terms, a
symbol of order `m - N` on `U`. -/
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
        (LocalHomogeneousSymbol.cutoffSymbol χ (a.term k)) :=
  LocalSymbol.ext <| funext fun p => by
    simp [Finset.sum_apply]

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols on `U` with the same full symbol
have the same homogeneous terms. -/
theorem term_eq_of_toLocalSymbol_eq {a b : LocalClassicalSymbol U V W m}
    (h : a.toLocalSymbol = b.toLocalSymbol) (j : ℕ) : a.term j = b.term j := by
  refine LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => ?_
  -- Compare the cut-off extensions by a cutoff equal to `1` at `x`.
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one U.isOpen
      (singleton_subset_iff.2 hx)
  have hext := ClassicalSymbol.term_eq_of_toSymbol_eq
    (a := a.extendAux ψ hψ hψU) (b := b.extendAux ψ hψ hψU) (by simp [extendAux, h]) j
  have := congrArg (fun c => c.coefficient (x, ξ)) hext
  simpa [extendAux, (hψ1 x rfl).self_of_nhds] using this

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

end Module

/-! ### Principal symbol, extension and restriction -/

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

end Principal

section Extend

variable (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U)

/-- The extension by zero of the cut-off classical symbol `ψ(x) a(x, ξ)`, for a smooth cutoff `ψ`
whose support is a closed subset of `ℝⁿ` contained in `U`: a classical symbol on `ℝⁿ`, whose
homogeneous terms are the cut-off extensions of those of `a`. -/
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

@[simp]
theorem principal_extend (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).principal = LocalHomogeneousSymbol.extend ψ hψ hψU a.principal :=
  HomogeneousSymbol.ext <| funext fun p => by simp

end Extend

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

/-- The restriction of a classical symbol on `ℝⁿ` to the open set `U` of positions: the restricted
full symbol, with the restricted homogeneous terms, is a classical symbol on `U`. -/
def restrict (U : TopologicalSpace.Opens (CoordinateSpace n)) :
    ClassicalSymbol n V W m →ₗ[ℂ] LocalClassicalSymbol U V W m where
  toFun a :=
    { toLocalSymbol := a.toSymbol.restrict U
      term j := (a.term j).restrict U
      exists_remainder' := ⟨default, fun N => ⟨(a.remainder default N).restrict U, fun ⟨x, ξ⟩ => by
        by_cases hx : x ∈ U <;> simp [hx]⟩⟩ }
  map_add' _ _ := LocalClassicalSymbol.ext (map_add (Symbol.restrict U) _ _)
  map_smul' c _ := LocalClassicalSymbol.ext (map_smul (Symbol.restrict U) c _)

@[simp]
theorem toLocalSymbol_restrict (a : ClassicalSymbol n V W m) :
    (a.restrict U).toLocalSymbol = a.toSymbol.restrict U :=
  (rfl)

@[simp]
theorem term_restrict (a : ClassicalSymbol n V W m) (j : ℕ) :
    (a.restrict U).term j = (a.term j).restrict U :=
  (rfl)

@[simp]
theorem principal_restrict (a : ClassicalSymbol n V W m) :
    (a.restrict U).principal = a.principal.restrict U :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [hx]

end ClassicalSymbol

namespace LocalClassicalSymbol

variable {U U' U'' : TopologicalSpace.Opens (CoordinateSpace n)}

section Restrict

/-- The restriction of a classical symbol on `U` to a smaller open set `U'`: the restricted full
symbol, with the restricted homogeneous terms, is a classical symbol on `U'`. -/
def restrict (h : U' ≤ U) : LocalClassicalSymbol U V W m →ₗ[ℂ] LocalClassicalSymbol U' V W m where
  toFun a :=
    { toLocalSymbol := LocalSymbol.restrict h a.toLocalSymbol
      term j := LocalHomogeneousSymbol.restrict h (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨LocalSymbol.restrict h (a.remainder default N), fun ⟨x, ξ⟩ => by
          by_cases hx : x ∈ U' <;> simp [hx]⟩⟩ }
  map_add' _ _ := ext (map_add (LocalSymbol.restrict h) _ _)
  map_smul' c _ := ext (map_smul (LocalSymbol.restrict h) c _)

@[simp]
theorem toLocalSymbol_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).toLocalSymbol = LocalSymbol.restrict h a.toLocalSymbol :=
  (rfl)

@[simp]
theorem term_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) (j : ℕ) :
    (restrict h a).term j = LocalHomogeneousSymbol.restrict h (a.term j) :=
  (rfl)

@[simp]
theorem principal_restrict (h : U' ≤ U) (a : LocalClassicalSymbol U V W m) :
    (restrict h a).principal = LocalHomogeneousSymbol.restrict h a.principal :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ => by simp [hx]

@[simp]
theorem restrict_self (a : LocalClassicalSymbol U V W m) : restrict le_rfl a = a :=
  ext (LocalSymbol.restrict_self _)

@[simp]
theorem restrict_restrict (h : U' ≤ U) (h' : U'' ≤ U') (a : LocalClassicalSymbol U V W m) :
    restrict h' (restrict h a) = restrict (h'.trans h) a :=
  ext (LocalSymbol.restrict_restrict _ _ _)

/-- On an open set `U' ⊆ U` on which the cutoff equals `1`, the cut-off extension restricts to
the restriction of the original classical symbol. -/
theorem restrict_extend_of_eqOn_one {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (h : U' ≤ U) (hψ1 : EqOn ψ 1 U') (a : LocalClassicalSymbol U V W m) :
    (extend ψ hψ hψU a).restrict U' = restrict h a :=
  ext (LocalSymbol.restrict_extend_of_eqOn_one hψ hψU h hψ1 _)

end Restrict

end LocalClassicalSymbol

namespace ClassicalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)}

@[simp]
theorem restrict_restrict (h : U' ≤ U) (a : ClassicalSymbol n V W m) :
    LocalClassicalSymbol.restrict h (a.restrict U) = a.restrict U' :=
  LocalClassicalSymbol.ext (Symbol.restrict_restrict h _)

/-- Over all of `ℝⁿ`, the classical symbols on open sets of positions are exactly the classical
symbols: restriction to `⊤` is a linear equivalence. -/
def restrictTopEquiv :
    ClassicalSymbol n V W m ≃ₗ[ℂ]
      LocalClassicalSymbol (⊤ : TopologicalSpace.Opens (CoordinateSpace n)) V W m where
  __ := restrict ⊤
  invFun a :=
    { toSymbol := Symbol.restrictTopEquiv.symm a.toLocalSymbol
      term j := HomogeneousSymbol.restrictTopEquiv.symm (a.term j)
      exists_remainder' := ⟨default, fun N =>
        ⟨Symbol.restrictTopEquiv.symm (a.remainder default N), fun p => by simp⟩⟩ }
  left_inv a := ext <| Symbol.ext <| funext fun p => by simp
  right_inv a := LocalClassicalSymbol.ext <| LocalSymbol.ext <| funext fun p => by simp

@[simp]
theorem toLocalSymbol_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) :
    (restrictTopEquiv a).toLocalSymbol = Symbol.restrictTopEquiv a.toSymbol :=
  Symbol.restrict_top a.toSymbol

@[simp]
theorem term_restrictTopEquiv_apply (a : ClassicalSymbol n V W m) (j : ℕ) :
    (restrictTopEquiv a).term j = HomogeneousSymbol.restrictTopEquiv (a.term j) :=
  HomogeneousSymbol.restrict_top (a.term j)

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

/-- Restricting a classical symbol to all of `ℝⁿ` gives the corresponding classical symbol on
`⊤`. -/
@[simp]
theorem restrict_top (a : ClassicalSymbol n V W m) : a.restrict ⊤ = restrictTopEquiv a :=
  (rfl)

end ClassicalSymbol

end TauCeti
