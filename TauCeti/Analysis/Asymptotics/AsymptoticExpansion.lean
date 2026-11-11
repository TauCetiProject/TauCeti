/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

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

## Main results

* `Asymptotics.HasAsymptoticExpansion.congr'`, `congr_coeff`, `congr_scale`: congruence.
* `Asymptotics.HasAsymptoticExpansion.smul_scale`: rescaling the scale by constants.
* `Asymptotics.HasAsymptoticExpansion.add`, `const_smul`, `neg`, `sub`: linearity.
* `Asymptotics.HasAsymptoticExpansion.mul_left`: multiplication of the function and of the scale
  by a common scalar function.
* `Asymptotics.HasAsymptoticExpansion.comp_tendsto`: composition with `Tendsto g l' l`.
* `Asymptotics.HasAsymptoticExpansion.isLittleO`: the remainder after `N + 1` terms is `o(φ N)`.
* `Asymptotics.HasAsymptoticExpansion.unique`: uniqueness of the coefficients.
* `Asymptotics.isAsymptoticScale_pow`: the powers of a function tending to `0` form a scale.
-/

@[expose] public section

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

namespace HasAsymptoticExpansion

variable {a b : ℕ → E} {f g : α → E}

/-- An expansion passes to a function that agrees eventually along `l`. -/
theorem congr' (hf : HasAsymptoticExpansion l φ a f) (hfg : f =ᶠ[l] g) :
    HasAsymptoticExpansion l φ a g := fun N =>
  (hf N).congr' (hfg.mono fun x hx => by simp only [hx]) EventuallyEq.rfl

/-- An expansion may be restated with equal coefficients. -/
theorem congr_coeff (hf : HasAsymptoticExpansion l φ a f) (hab : a = b) :
    HasAsymptoticExpansion l φ b f := hab ▸ hf

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
theorem mul_left (hf : HasAsymptoticExpansion l φ a f) (g : α → 𝕜) :
    HasAsymptoticExpansion l (fun n x => g x * φ n x) a (fun x => g x • f x) := fun N =>
  ((isBigO_refl g l).smul (hf N)).congr_left fun x => by
    simp only [smul_sub, smul_sum, smul_smul]

/-- An expansion along `l` pulls back along a map tending to `l`. -/
theorem comp_tendsto {β : Type*} {l' : Filter β} {g : β → α}
    (hf : HasAsymptoticExpansion l φ a f) (hg : Tendsto g l' l) :
    HasAsymptoticExpansion l' (fun n x => φ n (g x)) a (f ∘ g) :=
  fun N => (hf N).comp_tendsto hg

theorem add (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ (a + b) (f + g) := fun N =>
  ((hf N).add (hg N)).congr_left fun x => by
    simp only [Pi.add_apply, smul_add, sum_add_distrib]; abel

theorem const_smul (hf : HasAsymptoticExpansion l φ a f) (c : 𝕜) :
    HasAsymptoticExpansion l φ (c • a) (c • f) := fun N =>
  ((hf N).const_smul_left c).congr_left fun x => by
    simp only [Pi.smul_apply, smul_sub, smul_sum, smul_comm c (φ _ x)]

theorem neg (hf : HasAsymptoticExpansion l φ a f) :
    HasAsymptoticExpansion l φ (-a) (-f) := by
  simpa using hf.const_smul (-1 : 𝕜)

theorem sub (hf : HasAsymptoticExpansion l φ a f) (hg : HasAsymptoticExpansion l φ b g) :
    HasAsymptoticExpansion l φ (a - b) (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- For an asymptotic scale, the remainder after `N + 1` terms is `o(φ N)`. -/
theorem isLittleO (hφ : IsAsymptoticScale l φ) (hf : HasAsymptoticExpansion l φ a f) (N : ℕ) :
    (fun x => f x - ∑ n ∈ range (N + 1), φ n x • a n) =o[l] φ N :=
  (hf (N + 1)).trans_isLittleO (hφ N)

/-- The form of `HasAsymptoticExpansion.isLittleO` with the term of index `N` split off. -/
theorem sub_smul_isLittleO (hφ : IsAsymptoticScale l φ) (hf : HasAsymptoticExpansion l φ a f)
    (N : ℕ) : (fun x => f x - ∑ n ∈ range N, φ n x • a n - φ N x • a N) =o[l] φ N :=
  (hf.isLittleO hφ N).congr_left fun x => by rw [sum_range_succ]; abel

end HasAsymptoticExpansion

/-- If `ψ` is frequently nonzero along `l` and `ψ • c = o(ψ)`, then `c = 0`. -/
theorem eq_zero_of_smul_isLittleO {ψ : α → 𝕜} {c : E} (hψ : ∃ᶠ x in l, ψ x ≠ 0)
    (h : (fun x => ψ x • c) =o[l] ψ) : c = 0 := by
  by_contra hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨x, hx, hψx⟩ := (hψ.and_eventually (h.def (half_pos hcpos))).exists
  rw [norm_smul] at hψx
  have hψpos : 0 < ‖ψ x‖ := norm_pos_iff.mpr hx
  nlinarith

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
