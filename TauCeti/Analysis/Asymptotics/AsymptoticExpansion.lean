/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Asymptotic scales and asymptotic expansions

An *asymptotic scale* along a filter `l` is a sequence of functions `φ n` with
`φ (n + 1) = o(φ n)` along `l`. A function `f` has the *asymptotic expansion* `∑ a n φ n` along
`l` when, for every `N`, the remainder after the first `N` terms is `O(φ N)`. This is
Poincaré's notion of an asymptotic expansion in the generality of an arbitrary scale
(N. M. Temme, *Asymptotic Methods for Integrals*, §2.2; DLMF §2.1(iii) and §2.1(v)).

The definition of an expansion does not require the scale property; it is needed for the
remainder estimate `HasAsymptoticExpansion.isLittleO` and for uniqueness of the coefficients.

## Main definitions

* `Asymptotics.IsAsymptoticScale l φ`: `φ (n + 1) =o[l] φ n` for every `n`.
* `Asymptotics.HasAsymptoticExpansion l φ a f`: for every `N`,
  `f - ∑ n < N, φ n • a n =O[l] φ N`.

Both definitions are characterized by `isAsymptoticScale_iff` and `hasAsymptoticExpansion_iff`,
with introduction lemmas `IsAsymptoticScale.of_isLittleO`, `HasAsymptoticExpansion.of_isBigO` and
elimination lemmas `IsAsymptoticScale.isLittleO`, `HasAsymptoticExpansion.isBigO`.

## Main results

* `Asymptotics.IsAsymptoticScale.isLittleO_of_lt`, `isBigO_of_le`: comparison of any two
  functions of a scale.
* `Asymptotics.IsAsymptoticScale.mono`, `congr'`, `const_mul`, `mul_left`, `comp_tendsto`: the
  scale property under a finer filter, eventual equality, nonzero constant factors, a common
  factor and composition.
* `Asymptotics.hasAsymptoticExpansion_zero`, `HasAsymptoticExpansion.single_zero`,
  `IsAsymptoticScale.hasAsymptoticExpansion_single`, `HasAsymptoticExpansion.sum`: the zero
  expansion, single-term expansions and finite sums.
* `Asymptotics.HasAsymptoticExpansion.of_isLittleO`,
  `IsAsymptoticScale.hasAsymptoticExpansion_iff_isLittleO`: expansions from `o(φ N)` remainders.
* `Asymptotics.hasAsymptoticExpansion_congr`, `HasAsymptoticExpansion.congr'`, `congr_coeff`,
  `congr_scale`, `mono`: congruence and restriction of the filter.
* `Asymptotics.HasAsymptoticExpansion.smul_scale`: rescaling the scale by constants.
* `Asymptotics.HasAsymptoticExpansion.add`, `const_smul`, `neg`, `sub`: linearity.
* `Asymptotics.HasAsymptoticExpansion.smul_left`: multiplication of the function and of the scale
  by a common scalar function.
* `Asymptotics.HasAsymptoticExpansion.comp_tendsto`: composition with `Tendsto g l' l`.
* `Asymptotics.HasAsymptoticExpansion.isLittleO`: the remainder after `N + 1` terms is `o(φ N)`.
* `Asymptotics.HasAsymptoticExpansion.unique`: uniqueness of the coefficients.
* `Asymptotics.isAsymptoticScale_pow`: the powers of a function tending to `0` form a scale.

The definitions and proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean`.
-/

public section

noncomputable section

open Filter Finset
open scoped Topology

namespace Asymptotics

variable {α 𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {l : Filter α} {φ : ℕ → α → 𝕜}

/-- An asymptotic scale along `l`: each function is little-o of its predecessor. -/
def IsAsymptoticScale (l : Filter α) (φ : ℕ → α → 𝕜) : Prop :=
  ∀ n, φ (n + 1) =o[l] φ n

/-- `f` has the asymptotic expansion `∑ n, φ n • a n` along `l`: for every `N`, the remainder
after the first `N` terms is `O(φ N)` along `l`. -/
def HasAsymptoticExpansion (l : Filter α) (φ : ℕ → α → 𝕜) (a : ℕ → E) (f : α → E) : Prop :=
  ∀ N, (fun x => f x - ∑ n ∈ range N, φ n x • a n) =O[l] φ N

/-- The defining property of an asymptotic scale. -/
theorem isAsymptoticScale_iff : IsAsymptoticScale l φ ↔ ∀ n, φ (n + 1) =o[l] φ n := Iff.rfl

/-- Introduction rule for asymptotic scales. -/
theorem IsAsymptoticScale.of_isLittleO (h : ∀ n, φ (n + 1) =o[l] φ n) : IsAsymptoticScale l φ := h

/-- Each function of an asymptotic scale is little-o of its predecessor. -/
theorem IsAsymptoticScale.isLittleO (hφ : IsAsymptoticScale l φ) (n : ℕ) :
    φ (n + 1) =o[l] φ n := hφ n

/-- Every family is an asymptotic scale along `⊥`. -/
@[simp]
theorem isAsymptoticScale_bot : IsAsymptoticScale ⊥ φ := fun _ => isLittleO_bot _ _

namespace IsAsymptoticScale

/-- In an asymptotic scale, a later function is little-o of an earlier one. -/
theorem isLittleO_of_lt (hφ : IsAsymptoticScale l φ) {m n : ℕ} (h : m < n) :
    φ n =o[l] φ m := by
  induction n, h using Nat.le_induction with
  | base => exact hφ m
  | succ n _ ih => exact (hφ n).trans ih

/-- In an asymptotic scale, a later function is big-O of an earlier one. -/
theorem isBigO_of_le (hφ : IsAsymptoticScale l φ) {m n : ℕ} (h : m ≤ n) :
    φ n =O[l] φ m := by
  rcases h.eq_or_lt with rfl | h
  · exact isBigO_refl _ _
  · exact (hφ.isLittleO_of_lt h).isBigO

/-- An asymptotic scale along `l` is one along every finer filter. -/
theorem mono (hφ : IsAsymptoticScale l φ) {l' : Filter α} (hl : l' ≤ l) :
    IsAsymptoticScale l' φ := fun n => (hφ n).mono hl

/-- A family that agrees termwise eventually along `l` with an asymptotic scale is one. -/
theorem congr' (hφ : IsAsymptoticScale l φ) {ψ : ℕ → α → 𝕜} (h : ∀ n, φ n =ᶠ[l] ψ n) :
    IsAsymptoticScale l ψ := fun n => (hφ n).congr' (h (n + 1)) (h n)

/-- Multiplying the functions of a scale by nonzero constants gives a scale. -/
theorem const_mul (hφ : IsAsymptoticScale l φ) {κ : ℕ → 𝕜} (hκ : ∀ n, κ n ≠ 0) :
    IsAsymptoticScale l (fun n x => κ n * φ n x) := fun n =>
  ((hφ n).const_mul_left (κ (n + 1))).trans_isBigO (isBigO_self_const_mul (hκ n) (φ n) l)

/-- Multiplying every function of a scale by a common function gives a scale. -/
theorem mul_left (hφ : IsAsymptoticScale l φ) (g : α → 𝕜) :
    IsAsymptoticScale l (fun n x => g x * φ n x) := fun n =>
  (isBigO_refl g l).mul_isLittleO (hφ n)

/-- An asymptotic scale along `l` pulls back along a map tending to `l`. -/
theorem comp_tendsto (hφ : IsAsymptoticScale l φ) {β : Type*} {l' : Filter β} {g : β → α}
    (hg : Tendsto g l' l) : IsAsymptoticScale l' (fun n x => φ n (g x)) := fun n =>
  (hφ n).comp_tendsto hg

end IsAsymptoticScale

/-- Congruence of asymptotic scales under termwise eventual equality. -/
theorem isAsymptoticScale_congr {ψ : ℕ → α → 𝕜} (h : ∀ n, φ n =ᶠ[l] ψ n) :
    IsAsymptoticScale l φ ↔ IsAsymptoticScale l ψ :=
  ⟨fun hφ => hφ.congr' h, fun hψ => hψ.congr' fun n => (h n).symm⟩

/-- The defining property of an asymptotic expansion. -/
theorem hasAsymptoticExpansion_iff {a : ℕ → E} {f : α → E} :
    HasAsymptoticExpansion l φ a f ↔
      ∀ N, (fun x => f x - ∑ n ∈ range N, φ n x • a n) =O[l] φ N := Iff.rfl

/-- Every function has every expansion along `⊥`. -/
@[simp]
theorem hasAsymptoticExpansion_bot {a : ℕ → E} {f : α → E} :
    HasAsymptoticExpansion ⊥ φ a f := fun _ => isBigO_bot _ _

/-- The zero function has the zero expansion. -/
@[simp]
theorem hasAsymptoticExpansion_zero : HasAsymptoticExpansion l φ (0 : ℕ → E) 0 := fun N => by
  simpa using isBigO_zero (φ N) l

/-- A function has the zero expansion iff it is `O(φ N)` for every `N`. -/
theorem hasAsymptoticExpansion_zero_iff {f : α → E} :
    HasAsymptoticExpansion l φ 0 f ↔ ∀ N, f =O[l] φ N := by
  simp [hasAsymptoticExpansion_iff]

/-- A scalar function times a constant vector is big-O of the scalar function. -/
private theorem smul_const_isBigO (u : α → 𝕜) (c : E) : (fun x => u x • c) =O[l] u :=
  IsBigO.of_bound ‖c‖ (Eventually.of_forall fun x => by rw [norm_smul, mul_comm])

namespace HasAsymptoticExpansion

variable {a b : ℕ → E} {f g : α → E}

/-- Introduction rule for asymptotic expansions. -/
theorem of_isBigO (h : ∀ N, (fun x => f x - ∑ n ∈ range N, φ n x • a n) =O[l] φ N) :
    HasAsymptoticExpansion l φ a f := h

/-- The remainder after the first `N` terms of an asymptotic expansion is `O(φ N)`. -/
theorem isBigO (hf : HasAsymptoticExpansion l φ a f) (N : ℕ) :
    (fun x => f x - ∑ n ∈ range N, φ n x • a n) =O[l] φ N := hf N

/-- An expansion passes to a function that agrees eventually along `l`. -/
theorem congr' (hf : HasAsymptoticExpansion l φ a f) (hfg : f =ᶠ[l] g) :
    HasAsymptoticExpansion l φ a g := fun N =>
  (hf N).congr' (hfg.mono fun x hx => by simp only [hx]) EventuallyEq.rfl

/-- An expansion may be restated with equal coefficients. -/
theorem congr_coeff (hf : HasAsymptoticExpansion l φ a f) (hab : ∀ n, a n = b n) :
    HasAsymptoticExpansion l φ b f := funext hab ▸ hf

/-- An expansion along `l` is one along every finer filter. -/
theorem mono (hf : HasAsymptoticExpansion l φ a f) {l' : Filter α} (hl : l' ≤ l) :
    HasAsymptoticExpansion l' φ a f := fun N => (hf N).mono hl

/-- An expansion passes, with the same coefficients, to a scale that agrees termwise eventually
along `l`. -/
theorem congr_scale {ψ : ℕ → α → 𝕜} (hf : HasAsymptoticExpansion l φ a f)
    (h : ∀ n, φ n =ᶠ[l] ψ n) : HasAsymptoticExpansion l ψ a f := fun N => by
  have hall : ∀ᶠ x in l, ∀ n ∈ range N, φ n x = ψ n x :=
    (eventually_all_finset (range N)).mpr fun n _ => h n
  refine (hf N).congr' (hall.mono fun x hx => ?_) (h N)
  simp only
  rw [sum_congr rfl fun n hn => by rw [hx n hn]]

/-- Rescaling the scale by constants: if `φ n = κ n * ψ n` eventually along `l`, an expansion
with coefficients `a n` in `φ` is one with coefficients `κ n • a n` in `ψ`. -/
theorem smul_scale {ψ : ℕ → α → 𝕜} {κ : ℕ → 𝕜} (hf : HasAsymptoticExpansion l φ a f)
    (h : ∀ n, φ n =ᶠ[l] fun x => κ n * ψ n x) :
    HasAsymptoticExpansion l ψ (fun n => κ n • a n) f := fun N => by
  have hall : ∀ᶠ x in l, ∀ n ∈ range N, φ n x = κ n * ψ n x :=
    (eventually_all_finset (range N)).mpr fun n _ => h n
  refine ((hf N).trans ((isBigO_const_mul_self (κ N) (ψ N) l).congr' (h N).symm
    EventuallyEq.rfl)).congr' (hall.mono fun x hx => ?_) EventuallyEq.rfl
  simp only
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [hx n hn, smul_smul, mul_comm]

/-- Multiplying the function and the scale by a common scalar function preserves the
coefficients. -/
theorem smul_left (hf : HasAsymptoticExpansion l φ a f) (g : α → 𝕜) :
    HasAsymptoticExpansion l (fun n x => g x * φ n x) a (fun x => g x • f x) := fun N =>
  ((isBigO_refl g l).smul (hf N)).congr_left fun x => by
    simp only [smul_sub, smul_sum, smul_smul]

/-- An expansion along `l` pulls back along a map tending to `l`. -/
theorem comp_tendsto {β : Type*} {l' : Filter β} {g : β → α}
    (hf : HasAsymptoticExpansion l φ a f) (hg : Tendsto g l' l) :
    HasAsymptoticExpansion l' (fun n x => φ n (g x)) a (f ∘ g) :=
  fun N => (hf N).comp_tendsto hg

/-- Expansions in a common scale add coefficientwise: `f + g` has coefficients `a + b`. -/
theorem add (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ (a + b) (f + g) := fun N =>
  ((hf N).add (hg N)).congr_left fun x => by
    simp only [Pi.add_apply, smul_add, sum_add_distrib]; abel

/-- A constant multiple `c • f` has the coefficients `c • a`, for scalars `c` in any normed ring
acting on `E` compatibly with `𝕜`. -/
theorem const_smul {R : Type*} [SeminormedRing R] [Module R E] [IsBoundedSMul R E]
    [SMulCommClass 𝕜 R E] (hf : HasAsymptoticExpansion l φ a f) (c : R) :
    HasAsymptoticExpansion l φ (c • a) (c • f) := fun N =>
  ((hf N).const_smul_left c).congr_left fun x => by
    simp only [Pi.smul_apply, smul_sub, smul_sum]
    exact congrArg _ (sum_congr rfl fun n _ => (smul_comm (φ n x) c (a n)).symm)

/-- `-f` has the coefficients `-a`. -/
theorem neg (hf : HasAsymptoticExpansion l φ a f) :
    HasAsymptoticExpansion l φ (-a) (-f) := by
  simpa using hf.const_smul (-1 : 𝕜)

/-- Expansions in a common scale subtract coefficientwise: `f - g` has coefficients `a - b`. -/
theorem sub (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ (a - b) (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- A finite sum of expansions in a common scale has the summed coefficients. -/
theorem sum {ι : Type*} (s : Finset ι) {a : ι → ℕ → E} {f : ι → α → E}
    (h : ∀ i ∈ s, HasAsymptoticExpansion l φ (a i) (f i)) :
    HasAsymptoticExpansion l φ (∑ i ∈ s, a i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))

/-- The single term `φ 0 • c` has the expansion with the coefficient `c` at index `0`. -/
theorem single_zero (c : E) :
    HasAsymptoticExpansion l φ (Pi.single 0 c) (fun x => φ 0 x • c) := by
  intro N
  rcases N with _ | N
  · simpa using smul_const_isBigO (φ 0) c
  · simpa [Pi.single_apply, smul_ite, sum_ite_eq'] using isBigO_zero (φ (N + 1)) l

/-- If, for every `N`, the remainder after `N + 1` terms is `o(φ N)`, then `f` has the
expansion. This is the converse of `HasAsymptoticExpansion.isLittleO`; it needs no scale
property. -/
theorem of_isLittleO
    (h : ∀ N, (fun x => f x - ∑ n ∈ range (N + 1), φ n x • a n) =o[l] φ N) :
    HasAsymptoticExpansion l φ a f := fun N =>
  ((h N).isBigO.add (smul_const_isBigO (φ N) (a N))).congr_left fun x => by
    rw [sum_range_succ]; abel

/-- For an asymptotic scale, the remainder after `N + 1` terms is `o(φ N)`. -/
theorem isLittleO (hφ : IsAsymptoticScale l φ) (hf : HasAsymptoticExpansion l φ a f) (N : ℕ) :
    (fun x => f x - ∑ n ∈ range (N + 1), φ n x • a n) =o[l] φ N :=
  (hf (N + 1)).trans_isLittleO (hφ N)

/-- The form of `HasAsymptoticExpansion.isLittleO` with the term of index `N` split off. -/
theorem sub_smul_isLittleO (hφ : IsAsymptoticScale l φ) (hf : HasAsymptoticExpansion l φ a f)
    (N : ℕ) : (fun x => f x - ∑ n ∈ range N, φ n x • a n - φ N x • a N) =o[l] φ N :=
  (hf.isLittleO hφ N).congr_left fun x => by rw [sum_range_succ]; abel

/-- `-f` has the coefficients `-a` iff `f` has the coefficients `a`. -/
@[simp]
theorem _root_.Asymptotics.hasAsymptoticExpansion_neg_iff :
    HasAsymptoticExpansion l φ (-a) (-f) ↔ HasAsymptoticExpansion l φ a f :=
  ⟨fun h => by simpa using h.neg, neg⟩

end HasAsymptoticExpansion

/-- Congruence of expansions: termwise eventually equal scales, equal coefficients and eventually
equal functions give the same expansions. -/
theorem hasAsymptoticExpansion_congr {ψ : ℕ → α → 𝕜} {a b : ℕ → E} {f g : α → E}
    (hφψ : ∀ n, φ n =ᶠ[l] ψ n) (hab : ∀ n, a n = b n) (hfg : f =ᶠ[l] g) :
    HasAsymptoticExpansion l φ a f ↔ HasAsymptoticExpansion l ψ b g := by
  obtain rfl : a = b := funext hab
  exact ⟨fun h => (h.congr_scale hφψ).congr' hfg,
    fun h => (h.congr_scale fun n => (hφψ n).symm).congr' hfg.symm⟩

/-- In an asymptotic scale, the single term `φ k • c` has the expansion with the coefficient `c`
at index `k`. -/
theorem IsAsymptoticScale.hasAsymptoticExpansion_single (hφ : IsAsymptoticScale l φ) (k : ℕ)
    (c : E) : HasAsymptoticExpansion l φ (Pi.single k c) (fun x => φ k x • c) := by
  intro N
  by_cases hk : k < N
  · simpa [Pi.single_apply, smul_ite, sum_ite_eq', hk] using isBigO_zero (φ N) l
  · simpa [Pi.single_apply, smul_ite, sum_ite_eq', hk] using
      (smul_const_isBigO (φ k) c).trans (hφ.isBigO_of_le (not_lt.mp hk))

/-- For an asymptotic scale, an expansion is the same as `o(φ N)` remainders after `N + 1`
terms. -/
theorem IsAsymptoticScale.hasAsymptoticExpansion_iff_isLittleO (hφ : IsAsymptoticScale l φ)
    {a : ℕ → E} {f : α → E} :
    HasAsymptoticExpansion l φ a f ↔
      ∀ N, (fun x => f x - ∑ n ∈ range (N + 1), φ n x • a n) =o[l] φ N :=
  ⟨fun hf => hf.isLittleO hφ, HasAsymptoticExpansion.of_isLittleO⟩

/-- The coefficients of an expansion in an asymptotic scale whose functions are each frequently
nonzero along `l` are unique. -/
theorem HasAsymptoticExpansion.unique {a b : ℕ → E} {f : α → E} (hφ : IsAsymptoticScale l φ)
    (hne : ∀ n, ∃ᶠ x in l, φ n x ≠ 0) (ha : HasAsymptoticExpansion l φ a f)
    (hb : HasAsymptoticExpansion l φ b f) : a = b := by
  funext N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have hsum : ∀ x, ∑ n ∈ range N, φ n x • a n = ∑ n ∈ range N, φ n x • b n := fun x =>
    sum_congr rfl fun n hn => by rw [ih n (mem_range.mp hn)]
  have h := (ha.sub_smul_isLittleO hφ N).sub (hb.sub_smul_isLittleO hφ N)
  have h' : (fun x => φ N x • (b N - a N)) =o[l] φ N := h.congr_left fun x => by
    simp only [hsum, smul_sub]; abel
  exact (sub_eq_zero.mp (eq_zero_of_smul_isLittleO (hne N) h')).symm

/-- The powers of a function tending to `0` along `l` form an asymptotic scale. -/
theorem isAsymptoticScale_pow {w : α → 𝕜} (hw : Tendsto w l (𝓝 0)) :
    IsAsymptoticScale l (fun n x => w x ^ n) := by
  intro n
  have h := ((isLittleO_one_iff 𝕜).mpr hw).mul_isBigO (isBigO_refl (fun x => w x ^ n) l)
  simpa only [pow_succ, one_mul, mul_one, mul_comm] using h

end Asymptotics
