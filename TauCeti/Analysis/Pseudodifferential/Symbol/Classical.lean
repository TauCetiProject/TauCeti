/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Analysis.Pseudodifferential.CutoffSymbol

/-!
# Classical symbols and the principal symbol

A symbol `a` of order `m` is *classical* (or *polyhomogeneous*) if it has an asymptotic expansion

`a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)`

into homogeneous symbols `aₘ₋ⱼ` of the degrees `m - j`, `j ∈ ℕ`, made smooth at the zero
frequency by a frequency cutoff `χ`: for every `N`, the remainder `a - ∑_{j < N} χ(ξ) aₘ₋ⱼ(x, ξ)`
is a symbol of order `m - N`. The remainders are actual symbols, not an unspecified asymptotic
relation. The steps of the expansion are integers, so a classical symbol of order `m` is classical
of order `m + k` for every natural number `k`, while orders with a non-integer difference are not
comparable in the classical calculus.

This file develops the classical symbols of a fixed order as a subspace of the symbols:

* `TauCeti.Symbol.HasClassicalExpansion χ a p`: `a` has the expansion with the terms `p j` of
  degree `m - j` and the cutoff `χ`;
* `TauCeti.Symbol.HasClassicalExpansion.congr_cutoff`: the expansion does not depend on the cutoff;
* `TauCeti.Symbol.HasClassicalExpansion.unique`: the homogeneous terms are determined by the
  symbol;
* `TauCeti.Symbol.classical n V W m`: the subspace of classical symbols of order `m`, with the
  linear maps `TauCeti.Symbol.classicalTerm j` to the homogeneous terms;
* `TauCeti.Symbol.HasClassicalExpansion.inclusion`: a classical symbol of order `m - k`, `k ∈ ℕ`,
  is classical of order `m`, with `k` leading terms equal to zero; the injective linear map
  `TauCeti.Symbol.classicalInclusion` includes the classical symbols of order `m - k`;
* `TauCeti.Symbol.principalSymbol`: the leading term `aₘ`, a linear map onto the homogeneous
  symbols of degree `m` (`TauCeti.Symbol.principalSymbol_surjective`, with the right inverse
  `TauCeti.HomogeneousSymbol.toClassical`) whose kernel is the image of the classical symbols of
  order `m - 1` (`TauCeti.Symbol.ker_principalSymbol`). This is the exact sequence
  `0 → S^{m-1}_cl → S^m_cl → H^m → 0`, and `TauCeti.Symbol.principalSymbolEquiv` identifies the
  quotient by the classical symbols of order `m - 1` with the homogeneous symbols of degree `m`.

The smoothing symbols are exactly the symbols whose classical expansion has all homogeneous terms
zero (`TauCeti.Symbol.hasClassicalExpansion_zero_iff_isSmoothing`).

Classical symbols are closed under the pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)`
(`TauCeti.Symbol.HasClassicalExpansion.comp`, `TauCeti.Symbol.classicalComp`): if `b ∼ ∑ᵢ χ qᵢ`
and `a ∼ ∑ⱼ χ pⱼ`, then `b ∘ a ∼ ∑ₖ χ cₖ` with `cₖ = ∑_{i + j = k} qᵢ ∘ pⱼ`
(`TauCeti.Symbol.compTerms`), so classical orders add and the principal symbol is multiplicative
for the pointwise product (`TauCeti.Symbol.principalSymbol_classicalComp`). This is not the
composition of the operators: the lower order terms of the symbol of a composition of operators
also involve derivatives of the symbols.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2, §2.9, Lemma 2.5.
-/

public section

noncomputable section

namespace TauCeti

open HomogeneousSymbol

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

/-! ### Classical expansions -/

/-- The symbol `a` of order `m` has the classical expansion `a ∼ ∑ⱼ χ(ξ) pⱼ(x, ξ)` with the
homogeneous terms `pⱼ` of degree `m - j` and the frequency cutoff `χ`: for every `N`, the
remainder `a - ∑_{j < N} χ(ξ) pⱼ(x, ξ)` is a symbol of order `m - N`. -/
def HasClassicalExpansion (χ : FrequencyCutoff (CoordinateSpace n)) (a : Symbol n V W m)
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)) :
    Prop :=
  ∀ N : ℕ, ∃ r : Symbol n V W (m - N),
    r.coefficient = a.coefficient - ∑ j ∈ Finset.range N, (toSymbol χ (p j)).coefficient

variable {χ : FrequencyCutoff (CoordinateSpace n)} {a b : Symbol n V W m}
  {p q : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)}

/-- Unfolding `TauCeti.Symbol.HasClassicalExpansion`. -/
theorem hasClassicalExpansion_iff :
    HasClassicalExpansion χ a p ↔ ∀ N : ℕ, ∃ r : Symbol n V W (m - N),
      r.coefficient = a.coefficient - ∑ j ∈ Finset.range N, (toSymbol χ (p j)).coefficient :=
  Iff.rfl

/-- **Independence of the cutoff.** A classical expansion for one frequency cutoff is a classical
expansion, with the same homogeneous terms, for every other frequency cutoff. -/
theorem HasClassicalExpansion.congr_cutoff (h : HasClassicalExpansion χ a p)
    (χ' : FrequencyCutoff (CoordinateSpace n)) : HasClassicalExpansion χ' a p := fun N => by
  obtain ⟨r, hr⟩ := h N
  -- The two remainders agree for `‖ξ‖ ≥ 2`, where both cutoffs equal `1`.
  refine exists_coefficient_eq_of_forall_le_norm (a.contDiff_coefficient.sub
    (contDiff_sum_coefficient _ fun j => toSymbol χ' (p j))) r 2 fun x ξ hξ => ?_
  simp [hr, χ.apply_eq_one_of_two_le_norm hξ, χ'.apply_eq_one_of_two_le_norm hξ]

/-- **Uniqueness of the homogeneous terms.** Two classical expansions of the same symbol, possibly
for different cutoffs, have the same homogeneous terms. -/
theorem HasClassicalExpansion.unique {χ' : FrequencyCutoff (CoordinateSpace n)}
    (hp : HasClassicalExpansion χ a p) (hq : HasClassicalExpansion χ' a q) : p = q := by
  replace hq := hq.congr_cutoff χ
  funext j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- The remainders after `j + 1` terms differ by `χ(ξ) (pⱼ - qⱼ)`, of order `m - (j + 1)`, so
    -- `pⱼ = qⱼ` by the uniqueness of homogeneous terms.
    obtain ⟨r, hr⟩ := hp (j + 1)
    obtain ⟨s, hs⟩ := hq (j + 1)
    have hsum : ∑ i ∈ Finset.range j, (toSymbol χ (p i)).coefficient =
        ∑ i ∈ Finset.range j, (toSymbol χ (q i)).coefficient :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.1 hi)]
    rw [← sub_eq_zero]
    refine eq_zero_of_coefficient_toSymbol_eq χ (p j - q j) (by push_cast; linarith) (s - r) ?_
    rw [map_sub, coefficient_sub, coefficient_sub, hr, hs, Finset.sum_range_succ,
      Finset.sum_range_succ, hsum]
    abel

/-- The zero symbol has the classical expansion with all terms zero. -/
theorem hasClassicalExpansion_zero (χ : FrequencyCutoff (CoordinateSpace n)) :
    HasClassicalExpansion χ (0 : Symbol n V W m) 0 :=
  fun _ => ⟨0, by simp⟩

/-- The terms of a sum are the sums of the terms. -/
theorem HasClassicalExpansion.add (ha : HasClassicalExpansion χ a p)
    (hb : HasClassicalExpansion χ b q) : HasClassicalExpansion χ (a + b) (p + q) := fun N => by
  obtain ⟨r, hr⟩ := ha N
  obtain ⟨s, hs⟩ := hb N
  refine ⟨r + s, ?_⟩
  simp only [coefficient_add, hr, hs, Pi.add_apply, map_add, Finset.sum_add_distrib]
  abel

/-- The terms of a scalar multiple are the scalar multiples of the terms. -/
theorem HasClassicalExpansion.smul (ha : HasClassicalExpansion χ a p) (c : ℂ) :
    HasClassicalExpansion χ (c • a) (c • p) := fun N => by
  obtain ⟨r, hr⟩ := ha N
  exact ⟨c • r, by simp only [coefficient_smul, hr, Pi.smul_apply, map_smul, smul_sub,
    Finset.smul_sum]⟩

theorem HasClassicalExpansion.neg (ha : HasClassicalExpansion χ a p) :
    HasClassicalExpansion χ (-a) (-p) := by
  simpa using ha.smul (-1)

theorem HasClassicalExpansion.sub (ha : HasClassicalExpansion χ a p)
    (hb : HasClassicalExpansion χ b q) : HasClassicalExpansion χ (a - b) (p - q) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

/-- A smoothing symbol has the classical expansion whose homogeneous terms are all zero. -/
theorem IsSmoothing.hasClassicalExpansion_zero (ha : a.IsSmoothing)
    (χ : FrequencyCutoff (CoordinateSpace n)) : HasClassicalExpansion χ a 0 := fun N => by
  obtain ⟨r, hr⟩ := isSmoothing_iff.1 ha (m - N)
  exact ⟨r, by simp [hr]⟩

/-- Smoothing symbols are exactly the symbols with the classical expansion whose homogeneous
terms are all zero. -/
theorem hasClassicalExpansion_zero_iff_isSmoothing :
    HasClassicalExpansion χ a 0 ↔ a.IsSmoothing := by
  refine ⟨fun h => isSmoothing_iff.2 fun m'' => ?_, fun ha => ha.hasClassicalExpansion_zero χ⟩
  -- The remainder after `N ≥ m - m''` zero terms is `a` itself, of order `m - N ≤ m''`.
  obtain ⟨N, hN⟩ := exists_nat_ge (m - m'')
  obtain ⟨r, hr⟩ := h N
  exact ⟨Symbol.inclusion (by linarith) r, by simp [hr]⟩

/-- The remainder `a - χ(ξ) p₀` after the leading term of a classical expansion of a symbol `a` of
order `m` is a symbol of order `m - 1`. -/
theorem HasClassicalExpansion.exists_sub_leading (ha : HasClassicalExpansion χ a p) :
    ∃ r : Symbol n V W (m - 1), r.coefficient = a.coefficient - (toSymbol χ (p 0)).coefficient := by
  obtain ⟨r, hr⟩ := ha 1
  exact ⟨Symbol.inclusion (le_of_eq (by simp)) r, by simp [hr]⟩

/-- **Removing the leading term.** If `a` has the classical expansion with the terms
`p₀, p₁, …` and `r = a - χ(ξ) p₀` has order `m - 1`, then `r` has the classical expansion with the
terms `p₁, p₂, …`. -/
theorem HasClassicalExpansion.sub_leading (ha : HasClassicalExpansion χ a p)
    {r : Symbol n V W (m - 1)}
    (hr : r.coefficient = a.coefficient - (toSymbol χ (p 0)).coefficient) :
    HasClassicalExpansion χ r fun j => (p (j + 1)).castDegree (by push_cast; ring) := fun N => by
  obtain ⟨s, hs⟩ := ha (N + 1)
  refine ⟨Symbol.inclusion (le_of_eq (by push_cast; ring)) s, ?_⟩
  rw [coefficient_inclusion, hs, hr, Finset.sum_range_succ']
  simp only [coefficient_toSymbol_castDegree]
  abel

/-- **Inclusion of orders.** A symbol of order `m' = m - k` with a classical expansion, `k ∈ ℕ`,
has as a symbol of order `m` the classical expansion whose first `k` terms are zero, followed by
the terms of the original expansion. -/
theorem HasClassicalExpansion.inclusion {b : Symbol n V W m'}
    {q : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m' - j)}
    (hb : HasClassicalExpansion χ b q) (k : ℕ) (hk : m' = m - k) :
    HasClassicalExpansion χ (Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b)
      fun j => if h : k ≤ j then (q (j - k)).castDegree (by rw [hk, Nat.cast_sub h]; ring)
        else 0 := by
  intro N
  rcases le_or_gt k N with hN | hN
  · -- After `N = k + M` terms the remainder is the remainder of `b` after `M` terms.
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    obtain ⟨s, hs⟩ := hb M
    refine ⟨Symbol.inclusion (le_of_eq (by rw [hk]; push_cast; ring)) s, ?_⟩
    rw [coefficient_inclusion, hs, coefficient_inclusion, Finset.sum_range_add,
      Finset.sum_eq_zero (s := Finset.range k) fun j hj => ?_, zero_add]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Nat.le_add_right, ↓reduceDIte, coefficient_toSymbol_castDegree]
      funext z
      rw [coefficient_toSymbol, coefficient_toSymbol,
        coefficient_congr_index q (Nat.add_sub_cancel_left k i)]
    · simp [show ¬k ≤ j by simpa using hj]
  · -- Before the `k`-th term all terms vanish, and `b` has order `m - k ≤ m - N`.
    refine ⟨Symbol.inclusion (by rw [hk]; gcongr) b, ?_⟩
    rw [coefficient_inclusion, coefficient_inclusion, Finset.sum_eq_zero fun j hj => ?_, sub_zero]
    simp [show ¬k ≤ j by simp at hj; omega]

/-! ### Classical symbols -/

variable (n V W m) in
/-- The classical symbols of order `m`: the symbols with a classical expansion
`a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)` into homogeneous terms of the degrees `m - j`, `j ∈ ℕ`, a subspace of the
symbols of order `m`. The cutoff does not matter (`TauCeti.Symbol.mem_classical_iff`). -/
def classical : Submodule ℂ (Symbol n V W m) where
  carrier := {a | ∃ (χ : FrequencyCutoff (CoordinateSpace n))
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)),
    HasClassicalExpansion χ a p}
  zero_mem' := ⟨default, 0, hasClassicalExpansion_zero default⟩
  add_mem' := by
    rintro a b ⟨χ, p, hp⟩ ⟨χ', q, hq⟩
    exact ⟨χ, p + q, hp.add (hq.congr_cutoff χ)⟩
  smul_mem' c := by
    rintro a ⟨χ, p, hp⟩
    exact ⟨χ, c • p, hp.smul c⟩

/-- A symbol is classical exactly when it has a classical expansion for a given cutoff. -/
theorem mem_classical_iff (χ : FrequencyCutoff (CoordinateSpace n)) :
    a ∈ classical n V W m ↔ ∃ p, HasClassicalExpansion χ a p :=
  ⟨fun ⟨_, p, h⟩ => ⟨p, h.congr_cutoff χ⟩, fun ⟨p, h⟩ => ⟨χ, p, h⟩⟩

theorem HasClassicalExpansion.mem_classical (h : HasClassicalExpansion χ a p) :
    a ∈ classical n V W m :=
  ⟨χ, p, h⟩

/-- Smoothing symbols are classical. -/
theorem IsSmoothing.mem_classical (ha : a.IsSmoothing) : a ∈ classical n V W m :=
  (ha.hasClassicalExpansion_zero default).mem_classical

/-- A classical symbol of order `m' = m - k`, `k ∈ ℕ`, is classical of order `m`. -/
theorem inclusion_mem_classical {b : Symbol n V W m'} (hb : b ∈ classical n V W m') (k : ℕ)
    (hk : m' = m - k) :
    Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) b ∈ classical n V W m :=
  let ⟨_, _, h⟩ := hb
  (h.inclusion k hk).mem_classical

/-- The inclusion of the classical symbols of order `m' = m - k`, `k ∈ ℕ`, into the classical
symbols of order `m`, the restriction of `TauCeti.Symbol.inclusion`. -/
def classicalInclusion (k : ℕ) (hk : m' = m - k) : classical n V W m' →ₗ[ℂ] classical n V W m :=
  (Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg))).restrict
    fun _ hb => inclusion_mem_classical hb k hk

@[simp]
theorem coe_classicalInclusion (k : ℕ) (hk : m' = m - k) (b : classical n V W m') :
    (classicalInclusion k hk b : Symbol n V W m) =
      Symbol.inclusion (hk.le.trans (sub_le_self m k.cast_nonneg)) (b : Symbol n V W m') :=
  (rfl)

theorem classicalInclusion_injective (k : ℕ) (hk : m' = m - k) :
    Function.Injective (classicalInclusion (n := n) (V := V) (W := W) k hk) := fun _ _ h =>
  Subtype.ext (inclusion_injective _ (congrArg Subtype.val h))

/-- The homogeneous terms of a classical symbol, chosen once; `classicalTerm` bundles them. -/
private def terms (a : classical n V W m) :
    (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j) :=
  ((mem_classical_iff default).1 a.2).choose

private theorem hasClassicalExpansion_terms (a : classical n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) : HasClassicalExpansion χ a (terms a) :=
  ((mem_classical_iff default).1 a.2).choose_spec.congr_cutoff χ

/-- The homogeneous term `aₘ₋ⱼ` of degree `m - j` in the expansion `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)` of a
classical symbol `a` of order `m`. It is determined by `a`
(`TauCeti.Symbol.HasClassicalExpansion.classicalTerm_eq`) and does not depend on the cutoff. -/
def classicalTerm (j : ℕ) :
    classical n V W m →ₗ[ℂ]
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j) where
  toFun a := terms a j
  map_add' a b := congrFun ((hasClassicalExpansion_terms (a + b) default).unique
    ((hasClassicalExpansion_terms a default).add (hasClassicalExpansion_terms b default))) j
  map_smul' c a := congrFun ((hasClassicalExpansion_terms (c • a) default).unique
    ((hasClassicalExpansion_terms a default).smul c)) j

/-- A classical symbol has the classical expansion with its homogeneous terms, for every cutoff. -/
theorem hasClassicalExpansion_classicalTerm (a : classical n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) :
    HasClassicalExpansion χ a fun j => classicalTerm j a :=
  hasClassicalExpansion_terms a χ

/-- The terms of any classical expansion of a classical symbol are its homogeneous terms. -/
theorem HasClassicalExpansion.classicalTerm_eq {a : classical n V W m}
    (h : HasClassicalExpansion χ (a : Symbol n V W m) p) (j : ℕ) : classicalTerm j a = p j :=
  congrFun ((hasClassicalExpansion_classicalTerm a χ).unique h) j

/-- A classical symbol has a classical expansion exactly with its homogeneous terms. -/
theorem hasClassicalExpansion_iff_eq_classicalTerm (a : classical n V W m) :
    HasClassicalExpansion χ (a : Symbol n V W m) p ↔ p = fun j => classicalTerm j a :=
  ⟨fun h => funext fun j => (h.classicalTerm_eq j).symm,
    fun h => h ▸ hasClassicalExpansion_classicalTerm a χ⟩

/-! ### The principal symbol -/

/-- The principal symbol of a classical symbol `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)` of order `m`: its leading
homogeneous term `aₘ`, of degree `m`. -/
def principalSymbol :
    classical n V W m →ₗ[ℂ] HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m where
  toFun a := (classicalTerm 0 a).castDegree (by simp)
  map_add' a b := by simp
  map_smul' c a := by simp

theorem principalSymbol_apply (a : classical n V W m) :
    principalSymbol a = (classicalTerm 0 a).castDegree (by simp) :=
  (rfl)

@[simp]
theorem coefficient_principalSymbol (a : classical n V W m) :
    (principalSymbol a).coefficient = (classicalTerm 0 a).coefficient := by
  rw [principalSymbol_apply, coefficient_castDegree]

/-- The principal symbol is the leading term of any classical expansion. -/
theorem HasClassicalExpansion.principalSymbol_eq {a : classical n V W m}
    (h : HasClassicalExpansion χ (a : Symbol n V W m) p) :
    principalSymbol a = (p 0).castDegree (by simp) := by
  rw [principalSymbol_apply, h.classicalTerm_eq]

/-- A classical symbol of order `m` minus the cut-off principal symbol is a symbol of order
`m - 1`. -/
theorem exists_coefficient_eq_sub_principalSymbol (a : classical n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : Symbol n V W (m - 1),
      r.coefficient =
        (a : Symbol n V W m).coefficient - (toSymbol χ (principalSymbol a)).coefficient := by
  obtain ⟨r, hr⟩ := (hasClassicalExpansion_classicalTerm a χ).exists_sub_leading
  exact ⟨r, by rw [hr, principalSymbol_apply, coefficient_toSymbol_castDegree]⟩

end Symbol

namespace HomogeneousSymbol

open Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The cut-off term `χ(ξ) h(x, ξ)` of a homogeneous symbol `h` of degree `m` has the classical
expansion with the single term `h`. -/
theorem hasClassicalExpansion_toSymbol (χ : FrequencyCutoff (CoordinateSpace n))
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    HasClassicalExpansion χ (toSymbol χ h) (Pi.single 0 (h.castDegree (by simp))) := by
  rintro (_ | N)
  · exact ⟨Symbol.inclusion (le_of_eq (by simp)) (toSymbol χ h), by simp⟩
  · refine ⟨0, ?_⟩
    rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j _ => ?_, Pi.single_eq_same,
      coefficient_toSymbol_castDegree, zero_add, Symbol.coefficient_zero, sub_self]
    rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j), map_zero, Symbol.coefficient_zero]

/-- The cut-off term `χ(ξ) h(x, ξ)` of a homogeneous symbol `h` of degree `m` as a classical
symbol of order `m`. Its principal symbol is `h` (`TauCeti.Symbol.principalSymbol_toClassical`). -/
def toClassical (χ : FrequencyCutoff (CoordinateSpace n)) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] classical n V W m :=
  (toSymbol χ).codRestrict _ fun h => (hasClassicalExpansion_toSymbol χ h).mem_classical

@[simp]
theorem coe_toClassical (χ : FrequencyCutoff (CoordinateSpace n))
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (toClassical χ h : Symbol n V W m) = toSymbol χ h :=
  (rfl)

end HomogeneousSymbol

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The homogeneous terms of the cut-off term `χ(ξ) h(x, ξ)`: `h` and then zeros. -/
@[simp]
theorem classicalTerm_toClassical (χ : FrequencyCutoff (CoordinateSpace n))
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (j : ℕ) :
    classicalTerm j (toClassical χ h) =
      (Pi.single 0 (h.castDegree (by simp)) :
        (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)) j :=
  (hasClassicalExpansion_toSymbol χ h).classicalTerm_eq (a := toClassical χ h) j

/-- The principal symbol of the cut-off term `χ(ξ) h(x, ξ)` is `h`. -/
@[simp]
theorem principalSymbol_toClassical (χ : FrequencyCutoff (CoordinateSpace n))
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    principalSymbol (toClassical χ h) = h := by
  rw [(hasClassicalExpansion_toSymbol χ h).principalSymbol_eq (a := toClassical χ h),
    Pi.single_eq_same, castDegree_castDegree, castDegree_rfl]

/-- Every homogeneous symbol of degree `m` is the principal symbol of a classical symbol of
order `m`. -/
theorem principalSymbol_surjective :
    Function.Surjective (principalSymbol : classical n V W m →ₗ[ℂ] _) :=
  fun h => ⟨toClassical default h, principalSymbol_toClassical default h⟩

/-- **The kernel of the principal symbol.** A classical symbol of order `m` has principal symbol
zero exactly when it is a classical symbol of order `m - 1`. -/
theorem principalSymbol_eq_zero_iff (a : classical n V W m) :
    principalSymbol a = 0 ↔
      ∃ b ∈ classical n V W (m - 1), Symbol.inclusion (sub_one_lt m).le b = a := by
  obtain ⟨p, hp⟩ : ∃ p, HasClassicalExpansion default (a : Symbol n V W m) p :=
    ⟨_, hasClassicalExpansion_classicalTerm a default⟩
  rw [hp.principalSymbol_eq]
  constructor
  · intro h0
    have hp0 : p 0 = 0 := by
      ext1
      simpa using congrArg HomogeneousSymbol.coefficient h0
    -- The remainder after the leading term is `a` itself, with the remaining terms.
    obtain ⟨b, hb⟩ := hp.exists_sub_leading
    exact ⟨b, (hp.sub_leading hb).mem_classical, Symbol.ext (by simp [hb, hp0])⟩
  · rintro ⟨b, hb, hba⟩
    obtain ⟨q, hq⟩ := (mem_classical_iff default).1 hb
    have h := hq.inclusion (m := m) 1 (by simp)
    rw [hba] at h
    rw [← hp.classicalTerm_eq 0, h.classicalTerm_eq 0]
    simp

variable (n V W m) in
/-- **The kernel of the principal symbol** is the image of the classical symbols of order
`m - 1`. -/
theorem ker_principalSymbol :
    LinearMap.ker (principalSymbol : classical n V W m →ₗ[ℂ] _) =
      LinearMap.range (classicalInclusion (m' := m - 1) 1 (by simp)) := by
  ext a
  rw [LinearMap.mem_ker, principalSymbol_eq_zero_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact ⟨⟨b, hb⟩, Subtype.ext hba⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, rfl⟩

variable (n V W m) in
/-- The principal symbol identifies the quotient of the classical symbols of order `m` by the
classical symbols of order `m - 1` (`TauCeti.Symbol.ker_principalSymbol`) with the homogeneous
symbols of degree `m`. -/
def principalSymbolEquiv :
    (classical n V W m ⧸ LinearMap.range (classicalInclusion (m' := m - 1) 1 (by simp))) ≃ₗ[ℂ]
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  (Submodule.quotEquivOfEq _ _ (ker_principalSymbol n V W m).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ principalSymbol_surjective)

@[simp]
theorem principalSymbolEquiv_mk (a : classical n V W m) :
    principalSymbolEquiv n V W m (Submodule.Quotient.mk a) = principalSymbol a :=
  (rfl)

/-! ### Products -/

section Comp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
  {χ : FrequencyCutoff (CoordinateSpace n)}

/-- The homogeneous terms `cₖ = ∑_{i + j = k} qᵢ ∘ pⱼ` of the pointwise composition
`(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of two classical expansions, with the terms `qᵢ` of degree `m' - i`
and `pⱼ` of degree `m - j`. The term `cₖ` has degree `m' + m - k`. -/
def compTerms
    (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W U (m' - i))
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (k : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V U (m' + m - k) :=
  ∑ i ∈ Finset.range (k + 1),
    if h : i ≤ k then ((q i).comp (p (k - i))).castDegree (by rw [Nat.cast_sub h]; ring) else 0

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

variable {q p} in
/-- **Pointwise product of classical expansions.** The pointwise composition
`(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of symbols with classical expansions has the classical expansion whose
terms `cₖ = ∑_{i + j = k} qᵢ ∘ pⱼ` collect the products of the terms of total degree drop `k`. This
is not the expansion of the symbol of a composition of operators. -/
theorem HasClassicalExpansion.comp {b : Symbol n W U m'} (hb : HasClassicalExpansion χ b q)
    (ha : HasClassicalExpansion χ a p) : HasClassicalExpansion χ (b.comp a) (compTerms q p) := by
  intro N
  -- Induct on the number `N` of terms, removing the leading term of `b` at each step.
  induction N generalizing m' b q with
  | zero => exact ⟨Symbol.inclusion (le_of_eq (by simp)) (b.comp a), by simp⟩
  | succ N ih =>
    -- Split `b = χ(ξ) q₀ + b₁`, where `b₁` has order `m' - 1` and the terms `q₁, q₂, …`.
    obtain ⟨b₁, hb₁⟩ := hb.exists_sub_leading
    -- Then `b ∘ a - ∑_{k ≤ N} χ cₖ = χ q₀ ∘ (a - ∑_{j ≤ N} χ pⱼ) + (b₁ ∘ a - ∑_{k < N} χ cₖ')` for
    -- `‖ξ‖ ≥ 2`, where `cₖ'` are the terms of `b₁ ∘ a`, and both summands have order
    -- `m' + m - (N + 1)`.
    obtain ⟨R, hR⟩ := ih (hb.sub_leading hb₁)
    obtain ⟨s, hs⟩ := ha (N + 1)
    refine exists_coefficient_eq_of_forall_le_norm ((b.comp a).contDiff_coefficient.sub
      (contDiff_sum_coefficient _ fun k => toSymbol χ (compTerms q p k)))
      (Symbol.inclusion (le_of_eq (by push_cast; ring)) ((toSymbol χ (q 0)).comp s) +
        Symbol.inclusion (le_of_eq (by push_cast; ring)) R) 2 fun x ξ hξ => ?_
    have hχ := χ.apply_eq_one_of_two_le_norm hξ
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, coefficient_add, coefficient_inclusion,
      coefficient_comp, hs, hR, hb₁, coefficient_toSymbol, hχ, one_smul,
      Finset.sum_range_succ' _ N, coefficient_compTerms_succ, coefficient_compTerms_zero,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_finsetSum, Finset.sum_add_distrib]
    abel

/-- The pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of classical symbols of orders `m'` and
`m` is a classical symbol of order `m' + m`. -/
theorem comp_mem_classical {b : Symbol n W U m'} (hb : b ∈ classical n W U m')
    (ha : a ∈ classical n V W m) : b.comp a ∈ classical n V U (m' + m) := by
  obtain ⟨q, hq⟩ := (mem_classical_iff default).1 hb
  obtain ⟨p, hp⟩ := (mem_classical_iff default).1 ha
  exact (hq.comp hp).mem_classical

/-- The pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of classical symbols of orders `m'` and
`m`, as a classical symbol of order `m' + m`. -/
def classicalComp (b : classical n W U m') (a : classical n V W m) : classical n V U (m' + m) :=
  ⟨(b : Symbol n W U m').comp a, comp_mem_classical b.2 a.2⟩

@[simp]
theorem coe_classicalComp (b : classical n W U m') (a : classical n V W m) :
    (classicalComp b a : Symbol n V U (m' + m)) = (b : Symbol n W U m').comp a :=
  (rfl)

/-- The homogeneous terms of the pointwise composition of classical symbols are
`cₖ = ∑_{i + j = k} bᵢ ∘ aⱼ`. -/
theorem classicalTerm_classicalComp (b : classical n W U m') (a : classical n V W m) (k : ℕ) :
    classicalTerm k (classicalComp b a) =
      compTerms (fun i => classicalTerm i b) (fun j => classicalTerm j a) k :=
  ((hasClassicalExpansion_classicalTerm b default).comp
    (hasClassicalExpansion_classicalTerm a default)).classicalTerm_eq k

/-- **The principal symbol is multiplicative.** The principal symbol of the pointwise composition
of classical symbols is the composition of their principal symbols. -/
@[simp]
theorem principalSymbol_classicalComp (b : classical n W U m') (a : classical n V W m) :
    principalSymbol (classicalComp b a) = (principalSymbol b).comp (principalSymbol a) := by
  ext1
  funext z
  simp [classicalTerm_classicalComp]

end Comp

end Symbol

end TauCeti
