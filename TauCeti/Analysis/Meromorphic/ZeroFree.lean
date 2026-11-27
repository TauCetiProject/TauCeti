/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order

/-!
# Zero-free half-planes

A function `f : ℂ → ℂ` is *zero-free right of* `σ : ℝ` when `meromorphicOrderAt f s ≤ 0` at every
`s` with `σ < re s`. A zero is a point of positive order, so poles are allowed and no value of `f`
is read: the predicate treats alike a function with a pole at `s` whatever value it is given at
`s`. This is the form in which the Riemann hypothesis of a Dirichlet L-function is stated,
`ZeroFreeRightOf (1 / 2)` of its meromorphic continuation: the pole at `1`, when there is one
(for the trivial character), is allowed.

Mathlib's order of a function that is not meromorphic at a point is the junk value `0`. So a
point where `f` is not meromorphic passes the test automatically, while a point where `f` is
meromorphic of positive order fails it; the predicate says what its name suggests for functions
meromorphic on the half-plane, and the product rules below assume as much meromorphy as they
need.

The *zero abscissa* of a family `L : ι → ℂ → ℂ` is the supremum of `1 / 2` and of the real parts
of the zeros `ρ` of the members with `1 / 2 ≤ re ρ`. For a family each of whose members is
zero-free right of some fixed `σ` it is the least `σ ≥ 1 / 2` right of which every member is
zero-free, and it is approached by zeros of members when it exceeds `1 / 2`. Zeros left of the
critical line `re s = 1 / 2` are not counted, so the zero abscissa of a family of L-functions
satisfying the generalized Riemann hypothesis is `1 / 2`.

## Main definitions

* `TauCeti.ZeroFreeRightOf`: the predicate.
* `TauCeti.zeroAbscissa`: the zero abscissa of a family of functions.

## Main results

* `TauCeti.zeroFreeRightOf_iff`: the pointwise order characterization, which unfolds the
  predicate.
* `TauCeti.ZeroFreeRightOf.mono`, `TauCeti.zeroFreeRightOf_iff_forall_gt`: monotonicity in `σ`,
  and the predicate at `σ` as the conjunction of the predicates at all `σ' > σ`.
* `TauCeti.zeroFreeRightOf_congr`: the predicate depends only on punctured germs.
* `TauCeti.zeroFreeRightOf_iff_of_analyticAt`: for a function analytic on the half-plane, the
  predicate says that no value there is `0`.
* `TauCeti.ZeroFreeRightOf.mul`, `TauCeti.zeroFreeRightOf_mul_iff`,
  `TauCeti.zeroFreeRightOf_mul_iff_of_meromorphicOrderAt_eq_zero`,
  `TauCeti.zeroFreeRightOf_mul_iff_of_ne_zero`: products.
* `TauCeti.zeroFreeRightOf_conj_conj_iff`, `TauCeti.zeroFreeRightOf_comp_add_const`: reflection in
  the real axis and translation.
* `TauCeti.not_zeroFreeRightOf_zero`: the zero function is zero-free right of no `σ`.
* `TauCeti.zeroFreeRightOf_id_sub_const`: `s ↦ s - c` is zero-free right of `re c`.
* `TauCeti.zeroAbscissa_le_iff`, `TauCeti.zeroFreeRightOf_zeroAbscissa`,
  `TauCeti.re_le_zeroAbscissa`, `TauCeti.one_half_le_zeroAbscissa`: for a family zero-free right
  of a common `σ`, the zero abscissa is the least `σ' ≥ 1 / 2` right of which every member is
  zero-free.
* `TauCeti.exists_meromorphicOrderAt_pos_re_mem_Ioc`: a zero abscissa above `1 / 2` is
  approached from the left by real parts of zeros.
* `TauCeti.zeroAbscissa_congr`, `TauCeti.zeroAbscissa_mul_of_ne_zero`: the zero abscissa only
  depends on orders on `1 / 2 ≤ re s`, so is unchanged by factors analytic and nonzero there.

The pointwise statements about orders that these lift are in
`TauCeti.Analysis.Meromorphic.Order`.

## References

* OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane `Re(s) > 7/8`*, preprint of
  30 September 2026, Theorem 1.1 and section 2, for the convention that a zero-free half-plane
  is a statement about the meromorphic continuation in which poles are allowed, and (2.1) for
  the zero abscissa of a family.
-/

public section

open Filter Topology
open scoped ComplexConjugate

namespace TauCeti

/-- `f` is zero-free right of `σ`: at every `s` with `σ < re s` the order of `f` is at most `0`.
Poles are allowed, and no value of `f` is read. A point where `f` is not meromorphic passes the
test, since Mathlib's order is then the junk value `0`; a point where `f` is meromorphic of
positive order fails it. -/
def ZeroFreeRightOf (σ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s ≤ 0

variable {σ σ' : ℝ} {f g : ℂ → ℂ}

/-- The pointwise order characterization of `ZeroFreeRightOf`, used to unfold the predicate: `f`
is zero-free right of `σ` exactly when its order is at most `0` at every `s` with `σ < re s`. -/
theorem zeroFreeRightOf_iff :
    ZeroFreeRightOf σ f ↔ ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s ≤ 0 :=
  Iff.rfl

/-- A function zero-free right of `σ` is zero-free right of every `σ' ≥ σ`. -/
theorem ZeroFreeRightOf.mono (h : ZeroFreeRightOf σ f) (hσ : σ ≤ σ') : ZeroFreeRightOf σ' f :=
  fun s hs => h s (hσ.trans_lt hs)

/-- `f` is zero-free right of `σ` exactly when it is zero-free right of every `σ' > σ`. -/
theorem zeroFreeRightOf_iff_forall_gt :
    ZeroFreeRightOf σ f ↔ ∀ σ' > σ, ZeroFreeRightOf σ' f := by
  refine ⟨fun h σ' hσ' => h.mono hσ'.le, fun h s hs => ?_⟩
  obtain ⟨σ', hσ, hσ'⟩ := exists_between hs
  exact h σ' hσ s hσ'

/-- The predicate depends only on punctured germs: two functions that agree on a punctured
neighbourhood of every point right of `σ` are zero-free right of `σ` together. This lifts
`meromorphicOrderAt_congr`. -/
theorem zeroFreeRightOf_congr (h : ∀ s : ℂ, σ < s.re → f =ᶠ[𝓝[≠] s] g) :
    ZeroFreeRightOf σ f ↔ ZeroFreeRightOf σ g :=
  forall₂_congr fun s hs => by rw [meromorphicOrderAt_congr (h s hs)]

/-- A function analytic at every point right of `σ` is zero-free right of `σ` exactly when it
has no zero there. This lifts `AnalyticAt.meromorphicOrderAt_nonpos_iff`. -/
theorem zeroFreeRightOf_iff_of_analyticAt (hf : ∀ s : ℂ, σ < s.re → AnalyticAt ℂ f s) :
    ZeroFreeRightOf σ f ↔ ∀ s : ℂ, σ < s.re → f s ≠ 0 :=
  forall₂_congr fun s hs => (hf s hs).meromorphicOrderAt_nonpos_iff

/-- `s ↦ s - c` is zero-free right of `re c`: its only zero is `c`. -/
theorem zeroFreeRightOf_id_sub_const (c : ℂ) : ZeroFreeRightOf c.re (· - c) := by
  rw [zeroFreeRightOf_iff_of_analyticAt fun s _ => by fun_prop]
  intro s hs h
  rw [sub_eq_zero.1 h] at hs
  exact lt_irrefl _ hs

/-- The zero function is zero-free right of no `σ`: its order is `⊤` everywhere. -/
@[simp]
theorem not_zeroFreeRightOf_zero (σ : ℝ) : ¬ZeroFreeRightOf σ 0 := fun h => by
  have h0 : meromorphicOrderAt (0 : ℂ → ℂ) ((σ + 1 : ℝ) : ℂ) = ⊤ := by
    simp
  have := h ((σ + 1 : ℝ) : ℂ) (by simp)
  rw [h0] at this
  exact WithTop.zero_ne_top (top_le_iff.1 this)

/-- The product of two functions zero-free right of `σ`, one of which is meromorphic at every
point right of `σ`, is zero-free right of `σ`. At a point where the other factor is not
meromorphic the product is not meromorphic either, and its order is the junk value `0`. One
meromorphy hypothesis is needed: `(s - 2) * exp (conj s)` and `exp (-conj s)` are meromorphic at
no point, so both are zero-free right of every `σ`, while their product `s - 2` is not zero-free
right of `1`. This lifts `MeromorphicAt.meromorphicOrderAt_mul_nonpos`. -/
theorem ZeroFreeRightOf.mul (hf : ZeroFreeRightOf σ f) (hg : ZeroFreeRightOf σ g)
    (hfm : ∀ s : ℂ, σ < s.re → MeromorphicAt f s) : ZeroFreeRightOf σ (f * g) :=
  fun s hs => (hfm s hs).meromorphicOrderAt_mul_nonpos (hf s hs) (hg s hs)

/-- Let `f` and `g` be meromorphic at every point right of `σ`, such that no pole of either
there is a zero of the other. Then `f * g` is zero-free right of `σ` exactly when `f` and `g`
both are. The conditions at the poles are needed: `(s - 1)⁻¹ * (s - 1)` is zero-free right of
every `σ`. This lifts `MeromorphicAt.meromorphicOrderAt_mul_nonpos_iff`. -/
theorem zeroFreeRightOf_mul_iff (hfm : ∀ s : ℂ, σ < s.re → MeromorphicAt f s)
    (hgm : ∀ s : ℂ, σ < s.re → MeromorphicAt g s)
    (hfg : ∀ s : ℂ, σ < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt g s ≤ 0)
    (hgf : ∀ s : ℂ, σ < s.re → meromorphicOrderAt g s < 0 → meromorphicOrderAt f s ≤ 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f ∧ ZeroFreeRightOf σ g := by
  have key := fun (s : ℂ) (hs : σ < s.re) =>
    (hfm s hs).meromorphicOrderAt_mul_nonpos_iff (hgm s hs) (hfg s hs) (hgf s hs)
  exact ⟨fun h => ⟨fun s hs => ((key s hs).1 (h s hs)).1, fun s hs => ((key s hs).1 (h s hs)).2⟩,
    fun h => h.1.mul h.2 hfm⟩

/-- Multiplying by a function that is meromorphic of order `0` at every point right of `σ` does
not change whether a function is zero-free right of `σ`. No meromorphy of the other factor is
assumed and no value of `g` is read. This lifts
`MeromorphicAt.meromorphicOrderAt_mul_of_meromorphicOrderAt_eq_zero`. -/
theorem zeroFreeRightOf_mul_iff_of_meromorphicOrderAt_eq_zero
    (hgm : ∀ s : ℂ, σ < s.re → MeromorphicAt g s)
    (hg0 : ∀ s : ℂ, σ < s.re → meromorphicOrderAt g s = 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f :=
  forall₂_congr fun s hs => by
    rw [mul_comm, (hgm s hs).meromorphicOrderAt_mul_of_meromorphicOrderAt_eq_zero (hg0 s hs)]

/-- Multiplying by a function analytic and nonzero at every point right of `σ` does not change
whether a function is zero-free right of `σ`: the half-plane form of Mathlib's
`meromorphicOrderAt_mul_of_ne_zero`. -/
theorem zeroFreeRightOf_mul_iff_of_ne_zero (hg : ∀ s : ℂ, σ < s.re → AnalyticAt ℂ g s)
    (hg0 : ∀ s : ℂ, σ < s.re → g s ≠ 0) :
    ZeroFreeRightOf σ (f * g) ↔ ZeroFreeRightOf σ f :=
  zeroFreeRightOf_mul_iff_of_meromorphicOrderAt_eq_zero (fun s hs => (hg s hs).meromorphicAt)
    fun s hs => le_antisymm ((hg s hs).meromorphicOrderAt_nonpos_iff.2 (hg0 s hs))
      (hg s hs).meromorphicOrderAt_nonneg

/-- Reflection in the real axis: `conj ∘ f ∘ conj` is zero-free right of `σ` exactly when `f`
is. No meromorphy is assumed. This lifts `meromorphicOrderAt_conj_conj`. -/
@[simp]
theorem zeroFreeRightOf_conj_conj_iff :
    ZeroFreeRightOf σ (conj ∘ f ∘ conj) ↔ ZeroFreeRightOf σ f := by
  have hinv : Function.Involutive (conj : ℂ → ℂ) := Complex.conj_conj
  exact (hinv.toPerm conj).forall_congr fun s => by
    rw [hinv.coe_toPerm, meromorphicOrderAt_conj_conj, Complex.conj_re]

/-- Translation: `s ↦ f (s + a)` is zero-free right of `σ` exactly when `f` is zero-free right of
`σ + re a`. This lifts Mathlib's
`meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt`. -/
theorem zeroFreeRightOf_comp_add_const (a : ℂ) :
    ZeroFreeRightOf σ (fun s => f (s + a)) ↔ ZeroFreeRightOf (σ + a.re) f :=
  (Equiv.addRight a).forall_congr fun s => by
    rw [Equiv.coe_addRight, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt,
      Complex.add_re, add_lt_add_iff_right]

/-! ### The zero abscissa of a family -/

section ZeroAbscissa

variable {ι : Type*} {L L' D : ι → ℂ → ℂ} {ρ : ℂ} {b : ℝ}

/-- The set whose supremum is the zero abscissa: `1 / 2` together with the real parts of the
points `ρ` with `1 / 2 ≤ re ρ` at which some member `L η` has positive meromorphic order. -/
private noncomputable def zeroAbscissaSet (L : ι → ℂ → ℂ) : Set ℝ :=
  insert (1 / 2) {x : ℝ | ∃ η ρ, 1 / 2 ≤ ρ.re ∧ 0 < meromorphicOrderAt (L η) ρ ∧ ρ.re = x}

/-- The *zero abscissa* of a family `L : ι → ℂ → ℂ`: the supremum of `1 / 2` and of the real parts
of the points `ρ` with `1 / 2 ≤ re ρ` at which some member `L η` has positive meromorphic order.
Zeros left of the critical line are not counted, and poles are not zeros.

When the members have zeros with unbounded real parts (for instance when the family contains
the zero function), the set is unbounded and the value is Mathlib's junk value `sSup = 0`; the
results below exclude this by assuming every member zero-free right of a common `σ`. -/
noncomputable def zeroAbscissa (L : ι → ℂ → ℂ) : ℝ :=
  sSup (zeroAbscissaSet L)

/-- The defining formula of `zeroAbscissa`. -/
theorem zeroAbscissa_def (L : ι → ℂ → ℂ) :
    zeroAbscissa L = sSup (insert (1 / 2)
      {x : ℝ | ∃ η ρ, 1 / 2 ≤ ρ.re ∧ 0 < meromorphicOrderAt (L η) ρ ∧ ρ.re = x}) :=
  (rfl)

/-- A bound `b ≥ 1 / 2` bounds the set defining the zero abscissa exactly when every member is
zero-free right of `b`. -/
private theorem mem_upperBounds_zeroAbscissa_iff (hb : 1 / 2 ≤ b) :
    b ∈ upperBounds (zeroAbscissaSet L) ↔
      ∀ η, ZeroFreeRightOf b (L η) := by
  simp only [zeroAbscissaSet, upperBounds_insert, Set.mem_inter_iff, Set.mem_Ici, hb, true_and,
    mem_upperBounds, Set.mem_ofPred_eq, forall_exists_index, and_imp]
  refine ⟨fun h η s hs => not_lt.1 fun h0 => (h _ η s (hb.trans hs.le) h0 rfl).not_gt hs,
    fun h x η ρ _ h0 hx => hx ▸ not_lt.1 fun hρ => (h η ρ hρ).not_gt h0⟩

/-- A family zero-free right of a common `σ` has a bounded set of zero real parts. -/
private theorem bddAbove_of_zeroFreeRightOf {σ : ℝ} (h : ∀ η, ZeroFreeRightOf σ (L η)) :
    BddAbove (zeroAbscissaSet L) :=
  ⟨max σ (1 / 2), (mem_upperBounds_zeroAbscissa_iff (le_max_right _ _)).2 fun η =>
    (h η).mono (le_max_left _ _)⟩

/-- If every member of a family is zero-free right of some `σ ≥ 1 / 2`, then the zero abscissa is
at most `σ`. -/
theorem zeroAbscissa_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (h : ∀ η, ZeroFreeRightOf σ (L η)) :
    zeroAbscissa L ≤ σ :=
  csSup_le (Set.insert_nonempty _ _) ((mem_upperBounds_zeroAbscissa_iff hσ).2 h)

/-- The zero abscissa of a family zero-free right of a common `σ` is at least `1 / 2`. Without
the hypothesis it fails: the family consisting of the zero function has zero abscissa `0`. -/
theorem one_half_le_zeroAbscissa {σ : ℝ} (h : ∀ η, ZeroFreeRightOf σ (L η)) :
    1 / 2 ≤ zeroAbscissa L :=
  le_csSup (bddAbove_of_zeroFreeRightOf h) (Set.mem_insert _ _)

/-- In a family zero-free right of a common `σ`, every zero of a member has real part at most the
zero abscissa: zeros with `1 / 2 ≤ re ρ` are counted by it, and the others lie left of
`1 / 2 ≤ zeroAbscissa L`. -/
theorem re_le_zeroAbscissa {σ : ℝ} (h : ∀ η, ZeroFreeRightOf σ (L η)) {η : ι}
    (h0 : 0 < meromorphicOrderAt (L η) ρ) : ρ.re ≤ zeroAbscissa L := by
  rcases le_or_gt (1 / 2) ρ.re with hρ | hρ
  · exact le_csSup (bddAbove_of_zeroFreeRightOf h) (Set.mem_insert_of_mem _ ⟨η, ρ, hρ, h0, rfl⟩)
  · exact hρ.le.trans (one_half_le_zeroAbscissa h)

/-- Every member of a family zero-free right of a common `σ` is zero-free right of the zero
abscissa of the family. -/
theorem zeroFreeRightOf_zeroAbscissa {σ : ℝ} (h : ∀ η, ZeroFreeRightOf σ (L η)) (η : ι) :
    ZeroFreeRightOf (zeroAbscissa L) (L η) :=
  (mem_upperBounds_zeroAbscissa_iff (one_half_le_zeroAbscissa h)).1
    (fun _ hx => le_csSup (bddAbove_of_zeroFreeRightOf h) hx) η

/-- For a family zero-free right of a common `σ'` and for `σ ≥ 1 / 2`, the zero abscissa is at
most `σ` exactly when every member is zero-free right of `σ`. So the zero abscissa is the least
`σ ≥ 1 / 2` right of which the whole family is zero-free. -/
theorem zeroAbscissa_le_iff {σ σ' : ℝ} (hσ : 1 / 2 ≤ σ) (h : ∀ η, ZeroFreeRightOf σ' (L η)) :
    zeroAbscissa L ≤ σ ↔ ∀ η, ZeroFreeRightOf σ (L η) :=
  ⟨fun hle η => (zeroFreeRightOf_zeroAbscissa h η).mono hle, zeroAbscissa_le hσ⟩

/-- If the zero abscissa exceeds `1 / 2`, then for every `b` below it some member has a zero `ρ`
with `b < re ρ ≤ zeroAbscissa L`. No boundedness hypothesis is needed: an unbounded set of zero
real parts gives the junk value `0`, which does not exceed `1 / 2`. -/
theorem exists_meromorphicOrderAt_pos_re_mem_Ioc (h12 : 1 / 2 < zeroAbscissa L)
    (hb : b < zeroAbscissa L) :
    ∃ η ρ, 0 < meromorphicOrderAt (L η) ρ ∧ ρ.re ∈ Set.Ioc b (zeroAbscissa L) := by
  have hbdd : BddAbove (zeroAbscissaSet L) := by
    by_contra hbdd
    rw [zeroAbscissa, Real.sSup_of_not_bddAbove hbdd] at h12
    norm_num at h12
  obtain ⟨x, hx, hbx⟩ := exists_lt_of_lt_csSup (Set.insert_nonempty _ _) (max_lt h12 hb)
  rcases hx with rfl | ⟨η, ρ, hρ, h0, rfl⟩
  · exact absurd hbx (le_max_left _ _).not_gt
  · exact ⟨η, ρ, h0, (le_max_right _ _).trans_lt hbx,
      le_csSup hbdd (Set.mem_insert_of_mem _ ⟨η, ρ, hρ, h0, rfl⟩)⟩

/-- If some member of a family zero-free right of `re ρ` has a zero at `ρ` with `1 / 2 ≤ re ρ`,
then the zero abscissa is `re ρ`. -/
theorem zeroAbscissa_eq_re {η : ι} (hρ : 1 / 2 ≤ ρ.re) (h0 : 0 < meromorphicOrderAt (L η) ρ)
    (h : ∀ η', ZeroFreeRightOf ρ.re (L η')) : zeroAbscissa L = ρ.re :=
  le_antisymm (zeroAbscissa_le hρ h) (re_le_zeroAbscissa h h0)

/-- The zero abscissa of an empty family is `1 / 2`. -/
@[simp]
theorem zeroAbscissa_of_isEmpty [IsEmpty ι] (L : ι → ℂ → ℂ) : zeroAbscissa L = 1 / 2 := by
  simp [zeroAbscissa_def]

/-- The zero abscissa depends only on the orders of the members at points with `1 / 2 ≤ re s`. -/
theorem zeroAbscissa_congr
    (h : ∀ η s, 1 / 2 ≤ s.re → meromorphicOrderAt (L η) s = meromorphicOrderAt (L' η) s) :
    zeroAbscissa L = zeroAbscissa L' := by
  simp only [zeroAbscissa_def]
  congr 2
  ext x
  exact exists_congr fun η => exists_congr fun ρ => and_congr_right fun hρ => by rw [h η ρ hρ]

/-- Multiplying each member of a family by a function analytic and nonzero at every point with
`1 / 2 ≤ re s` does not change the zero abscissa. This applies to deleting or inserting finitely
many Euler factors whose Satake parameters have absolute value at most `1` (such as those of
Dirichlet L-functions), which are analytic and nonzero on `re s > 0`. -/
theorem zeroAbscissa_mul_of_ne_zero (hD : ∀ η s, 1 / 2 ≤ s.re → AnalyticAt ℂ (D η) s)
    (hD0 : ∀ η s, 1 / 2 ≤ s.re → D η s ≠ 0) :
    zeroAbscissa (fun η => L η * D η) = zeroAbscissa L :=
  zeroAbscissa_congr fun η s hs => by
    rw [mul_comm, meromorphicOrderAt_mul_of_ne_zero (hD η s hs) (hD0 η s hs)]

end ZeroAbscissa

end TauCeti
