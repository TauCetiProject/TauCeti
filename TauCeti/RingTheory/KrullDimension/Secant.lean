/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.Regular.PrefixQuotient
import TauCeti.Data.ENat.Monoid
import TauCeti.RingTheory.Depth.Basic
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.KrullDimension.Regular

/-!
# Secant sequences

For a module `M` over a commutative ring and a list `rs = (r₁, …, rₛ)`, the *prefix quotient*
`TauCeti.prefixQuotient M rs` is `M ⧸ (r₁, …, rₛ) M`. Over a local ring `(R, 𝔪)`, a list
`r₁, …, rₛ` is *secant* for `M` when every `rᵢ` lies in `𝔪` and every step strictly lowers the
dimension of the support:
`dim Supp M ⧸ (r₁, …, rᵢ) M < dim Supp M ⧸ (r₁, …, rᵢ₋₁) M` for `1 ≤ i ≤ s`. Only the empty list
is secant for the zero module. Secant sequences weaken regular sequences: the entries of a secant
sequence are parameters, but need not be regular. Česnavičius uses them to reformulate Kawasaki's
Macaulayfication, which blows up a Noetherian scheme along ideals built from products of such
sequences.

## Main definitions

* `TauCeti.IsSecant M rs`: the list `rs` is secant for `M`.

## Main results

* `TauCeti.supportDim_prefixQuotient_nil`, `TauCeti.supportDim_prefixQuotient_cons`: the support
  dimension of the prefix quotient by `[]` and by `r :: ts`;
  `TauCeti.supportDim_prefixQuotient_take_succ_cons` is the form used along prefixes of `r :: rs`.
* `TauCeti.isSecant_cons_iff`, `TauCeti.isSecant_append_iff`: secancy of a concatenation
  `rs ++ qs` is secancy of `rs` for `M` together with secancy of `qs` for `M ⧸ (rs) M`.
* `TauCeti.isSecant_iff_of_support_eq`: secancy for a finite module depends only on its support.
* `TauCeti.isSecant_iff_supportDim_add_length_eq`: for a nonzero finite module over a Noetherian
  local ring, `rs` is secant if and only if its entries lie in `𝔪` and
  `dim Supp M ⧸ (rs) M + length rs = dim Supp M`.
* `TauCeti.IsSecant.length_le_supportDim`: a secant list has length at most `dim Supp M`.
* `TauCeti.IsSecant.perm`, `TauCeti.IsSecant.sublist`: permutations and sublists of secant lists
  are secant.
* `TauCeti.isSecant_append_pow_cons_iff`: replacing an entry by a positive power of itself does
  not affect secancy.
* `TauCeti.IsSecant.append_mul`: if `r₁, …, rₙ` is secant and `i ≤ j ≤ n`, then
  `r₁, …, rᵢ₋₁, rᵢ rⱼ` is secant.
* `RingTheory.Sequence.IsRegular.isSecant`: a regular sequence is secant.
* `TauCeti.exists_isSecant_singleton`: a finite module over a Noetherian local ring whose support
  has positive dimension admits an element of `𝔪` that lowers that dimension.
* `TauCeti.exists_isSecant_supportDim_eq_zero`, `TauCeti.IsSecant.exists_append`: **secant
  parameter completion**. Every secant list for a nonzero finite module over a Noetherian local
  ring, in particular the empty one, extends to a secant list whose terminal quotient has
  zero-dimensional support.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, Duke Math. J. 170 (2021),
  Definition 3.1(i) and Remark 3.2.
* T. Kawasaki, *On Macaulayfication of Noetherian schemes*, Trans. Amer. Math. Soc. 352 (2000).
-/

public section

open Ideal Module IsLocalRing Pointwise RingTheory.Sequence

namespace TauCeti

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

section SupportDim

/-- The prefix quotient by the empty list has the same support dimension as the module. -/
@[simp]
theorem supportDim_prefixQuotient_nil :
    supportDim R (prefixQuotient M ([] : List R)) = supportDim R M :=
  supportDim_eq_of_equiv (prefixQuotient.nilEquiv M)

/-- The prefix quotient of `M` by `r :: ts` has the support dimension of the prefix quotient of
`M ⧸ r M` by `ts`. -/
@[simp]
theorem supportDim_prefixQuotient_cons (r : R) (ts : List R) :
    supportDim R (prefixQuotient M (r :: ts)) =
      supportDim R (prefixQuotient (QuotSMulTop r M) ts) :=
  supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r ts)

/-- The prefix quotient of `M` by the first `i + 1` entries of `r :: rs` has the support dimension
of the prefix quotient of `M ⧸ r M` by the first `i` entries of `rs`. -/
theorem supportDim_prefixQuotient_take_succ_cons (r : R) (rs : List R) (i : ℕ) :
    supportDim R (prefixQuotient M ((r :: rs).take (i + 1))) =
      supportDim R (prefixQuotient (QuotSMulTop r M) (rs.take i)) := by
  rw [List.take_succ_cons, supportDim_prefixQuotient_cons]

end SupportDim

section Secant

variable [IsLocalRing R]

/-- A list `r₁, …, rₛ` is *secant* for `M` when each `rᵢ` lies in the maximal ideal and each step
strictly lowers the dimension of the support of the prefix quotient:
`dim Supp M ⧸ (r₁, …, rᵢ) M < dim Supp M ⧸ (r₁, …, rᵢ₋₁) M`. Since the zero module has support
dimension `⊥`, only the empty list is secant for it. -/
@[mk_iff]
structure IsSecant (rs : List R) : Prop where
  mem_maximalIdeal : ∀ r ∈ rs, r ∈ maximalIdeal R
  supportDim_lt : ∀ i < rs.length,
    supportDim R (prefixQuotient M (rs.take (i + 1))) < supportDim R (prefixQuotient M (rs.take i))

variable {M}

/-- The empty list is secant for every module. -/
@[simp]
theorem IsSecant.nil : IsSecant M ([] : List R) :=
  ⟨by simp, by simp⟩

/-- Secancy is invariant under linear equivalence of modules. -/
theorem _root_.LinearEquiv.isSecant_iff (e : M ≃ₗ[R] N) {rs : List R} :
    IsSecant M rs ↔ IsSecant N rs := by
  have h (qs : List R) : supportDim R (prefixQuotient M qs) = supportDim R (prefixQuotient N qs) :=
    supportDim_eq_of_equiv (prefixQuotient.congr qs e)
  simp only [TauCeti.isSecant_iff, h]

/-- The list `r :: rs` is secant for `M` if and only if `r ∈ 𝔪`, `r` lowers the dimension of the
support of `M`, and `rs` is secant for `M ⧸ r M`. -/
theorem isSecant_cons_iff (r : R) (rs : List R) :
    IsSecant M (r :: rs) ↔ r ∈ maximalIdeal R ∧
      supportDim R (QuotSMulTop r M) < supportDim R M ∧ IsSecant (QuotSMulTop r M) rs := by
  rw [isSecant_iff, isSecant_iff, List.forall_mem_cons, List.length_cons]
  simp only [Nat.forall_lt_succ_left', supportDim_prefixQuotient_take_succ_cons]
  rw [List.take_zero, List.take_zero, supportDim_prefixQuotient_nil, supportDim_prefixQuotient_nil]
  tauto

/-- A one-element list `[r]` is secant for `M` if and only if `r ∈ 𝔪` lowers the dimension of the
support of `M`. -/
theorem isSecant_singleton_iff (r : R) :
    IsSecant M [r] ↔ r ∈ maximalIdeal R ∧ supportDim R (QuotSMulTop r M) < supportDim R M := by
  simp [isSecant_cons_iff, IsSecant.nil]

/-- **Secant concatenation.** The list `rs ++ qs` is secant for `M` if and only if `rs` is secant
for `M` and `qs` is secant for `M ⧸ (rs) M`. -/
theorem isSecant_append_iff (rs qs : List R) :
    IsSecant M (rs ++ qs) ↔ IsSecant M rs ∧ IsSecant (prefixQuotient M rs) qs := by
  induction rs generalizing M with
  | nil => simp [IsSecant.nil, (prefixQuotient.nilEquiv M).isSecant_iff]
  | cons r rs ih =>
    rw [List.cons_append, isSecant_cons_iff, ih, isSecant_cons_iff,
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs).isSecant_iff]
    simp only [and_assoc]

/-- Only the empty list is secant for the zero module. -/
theorem isSecant_iff_eq_nil [Subsingleton M] {rs : List R} : IsSecant M rs ↔ rs = [] := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ .nil⟩
  cases rs with
  | nil => rfl
  | cons r rs =>
    have := ((isSecant_cons_iff r rs).1 h).2.1
    simp [supportDim_eq_bot_of_subsingleton] at this

/-- Secancy for a finite module depends only on its support: the support of each prefix quotient
is the support of the module cut down by the zero locus of the prefix. -/
theorem isSecant_iff_of_support_eq [Module.Finite R M] [Module.Finite R N]
    (h : support R M = support R N) {rs : List R} : IsSecant M rs ↔ IsSecant N rs := by
  have hdim (ts : List R) :
      supportDim R (prefixQuotient M ts) = supportDim R (prefixQuotient N ts) :=
    supportDim_eq_of_support_eq (by rw [support_quotient, support_quotient, h])
  simp only [isSecant_iff, hdim]

/-- Replacing an entry of a list by a positive power of itself does not affect secancy for a
finite module. -/
theorem isSecant_append_pow_cons_iff [Module.Finite R M] (rs qs : List R) (r : R) {n : ℕ}
    (hn : n ≠ 0) : IsSecant M (rs ++ r ^ n :: qs) ↔ IsSecant M (rs ++ r :: qs) := by
  have hsupp : support R (QuotSMulTop (r ^ n) (prefixQuotient M rs)) =
      support R (QuotSMulTop r (prefixQuotient M rs)) := by
    rw [support_quotSMulTop, support_quotSMulTop,
      PrimeSpectrum.zeroLocus_singleton_pow _ _ (Nat.pos_of_ne_zero hn)]
  rw [isSecant_append_iff, isSecant_append_iff, isSecant_cons_iff, isSecant_cons_iff,
    (maximalIdeal.isMaximal R).isPrime.pow_mem_iff_mem n (Nat.pos_of_ne_zero hn),
    supportDim_eq_of_support_eq hsupp,
    isSecant_iff_of_support_eq hsupp]

section Noetherian

variable [IsNoetherianRing R] [Module.Finite R M]

/-- **The secant dimension formula.** Along a secant list the dimension of the support drops by
exactly one at each step: `dim Supp M ⧸ (rs) M + length rs = dim Supp M`. -/
theorem IsSecant.supportDim_add_length_eq [Nontrivial M] {rs : List R} (h : IsSecant M rs) :
    supportDim R (prefixQuotient M rs) + rs.length = supportDim R M := by
  induction rs generalizing M with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨hr, hlt, hrs⟩ := (isSecant_cons_iff r rs).1 h
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hr
    rw [supportDim_prefixQuotient_cons, List.length_cons, Nat.cast_add_one, ← add_assoc, ih hrs]
    exact supportDim_quotSMulTop_succ_eq_supportDim_of_lt hr hlt

/-- **The secant dimension formula.** For a nonzero finite module `M` over a Noetherian local ring,
a list `rs` is secant for `M` if and only if its entries lie in `𝔪` and
`dim Supp M ⧸ (rs) M + length rs = dim Supp M`. The hypothesis that `M` is nonzero is needed: for
the zero module both sides of the formula are `⊥` for every list. -/
theorem isSecant_iff_supportDim_add_length_eq [Nontrivial M] (rs : List R) :
    IsSecant M rs ↔ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
      supportDim R (prefixQuotient M rs) + rs.length = supportDim R M := by
  refine ⟨fun h ↦ ⟨h.mem_maximalIdeal, h.supportDim_add_length_eq⟩, ?_⟩
  induction rs generalizing M with
  | nil => exact fun _ ↦ .nil
  | cons r rs ih =>
    rintro ⟨hmem, hdim⟩
    have hr := hmem r List.mem_cons_self
    have hrs : ∀ s ∈ rs, s ∈ maximalIdeal R := fun s hs ↦ hmem s (List.mem_cons_of_mem r hs)
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hr
    rw [supportDim_prefixQuotient_cons, List.length_cons, Nat.cast_add_one, ← add_assoc] at hdim
    -- Neither `r` nor the remaining entries can lower the dimension by more than one each, so the
    -- total drop `length rs + 1` forces `r` to lower it by exactly one.
    have heq : supportDim R (QuotSMulTop r M) + 1 = supportDim R M :=
      le_antisymm
        ((add_le_add_left (supportDim_le_supportDim_quotient_add_length rs hrs) 1).trans hdim.le)
        (supportDim_le_supportDim_quotSMulTop_succ hr)
    refine (isSecant_cons_iff r rs).2 ⟨hr, lt_supportDim_of_add_one_eq heq, ih ⟨hrs, ?_⟩⟩
    rwa [← heq, ENat.WithBot.add_one_cancel] at hdim

/-- A secant list for a nonzero finite module has length at most the dimension of its support. -/
theorem IsSecant.length_le_supportDim [Nontrivial M] {rs : List R} (h : IsSecant M rs) :
    (rs.length : WithBot ℕ∞) ≤ supportDim R M := by
  have := prefixQuotient.nontrivial_of_forall_mem_maximalIdeal M h.mem_maximalIdeal
  obtain ⟨j, hj⟩ := exists_supportDim_eq_natCast (R := R) (M := prefixQuotient M rs)
  rw [← h.supportDim_add_length_eq, hj]
  exact_mod_cast Nat.le_add_left _ _

/-- A permutation of a secant list is secant. -/
theorem IsSecant.perm {rs qs : List R} (h : IsSecant M rs) (hp : rs.Perm qs) : IsSecant M qs := by
  cases subsingleton_or_nontrivial M
  · rw [isSecant_iff_eq_nil] at h ⊢
    exact List.perm_nil.1 (h ▸ hp).symm
  · rw [isSecant_iff_supportDim_add_length_eq] at h ⊢
    rw [← supportDim_eq_of_equiv (prefixQuotient.equivOfPerm M hp), ← hp.length_eq]
    exact ⟨fun r hr ↦ h.1 r (hp.mem_iff.2 hr), h.2⟩

/-- A sublist of a secant list is secant. -/
theorem IsSecant.sublist {rs qs : List R} (h : IsSecant M rs) (hs : qs.Sublist rs) :
    IsSecant M qs := by
  obtain ⟨ts, hts⟩ := hs.exists_perm_append
  exact ((isSecant_append_iff qs ts).1 (h.perm hts)).1

/-- **The truncated-product property.** If `r₁, …, rₙ` is secant and `i ≤ j ≤ n`, then
`r₁, …, rᵢ₋₁, rᵢ rⱼ` is secant. Here `rs = (r₁, …, rᵢ₋₁)`, `r = rᵢ` and `s = rⱼ`. -/
theorem IsSecant.append_mul {rs qs : List R} {r s : R} (h : IsSecant M (rs ++ r :: qs))
    (hs : s ∈ r :: qs) : IsSecant M (rs ++ [r * s]) := by
  rw [isSecant_append_iff] at h ⊢
  obtain ⟨hrs, h⟩ := h
  refine ⟨hrs, ?_⟩
  -- Both `r` and `s` lower the dimension of the support of `M ⧸ (rs) M`, hence so does `r * s`.
  have hs' : IsSecant (prefixQuotient M rs) [s] := by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h.sublist (by simp)
    · exact ((h.sublist ((List.singleton_sublist.2 hs).cons_cons r)).perm
        (List.Perm.swap s r [])).sublist (by simp)
  obtain ⟨hr, hlt, -⟩ := (isSecant_cons_iff r qs).1 h
  rw [isSecant_singleton_iff] at hs' ⊢
  exact ⟨mul_mem_right _ _ hr, by rw [supportDim_quotSMulTop_mul]; exact max_lt hlt hs'.2⟩

/-- A finite module over a Noetherian local ring whose support has positive dimension admits a
one-element secant list, that is, an element of `𝔪` that lowers the dimension of its support. -/
theorem exists_isSecant_singleton (h : 0 < supportDim R M) : ∃ x : R, IsSecant M [x] := by
  -- An element of `𝔪` outside every minimal prime of the annihilator of `M` lowers the dimension
  -- by one, and prime avoidance provides one.
  have : Nontrivial M := (supportDim_ne_bot_iff_nontrivial R M).1 (ne_bot_of_gt h)
  -- If `𝔪` were a minimal prime over `Ann M`, it would be the only point of the support.
  have hm : maximalIdeal R ∉ (annihilator R M).minimalPrimes :=
    fun hm ↦ h.not_ge (supportDim_nonpos_of_maximalIdeal_mem_minimalPrimes hm)
  obtain ⟨x, hx, hxS⟩ := Set.not_subset.1 <| mt (subset_iUnion_iff_mem_of_isMaximal_of_finite
    ((annihilator R M).finite_minimalPrimes_of_isNoetherianRing R) ⊥ ⊥
    (fun p hp _ _ ↦ hp.1.1) bot_ne_top bot_ne_top).1 hm
  have hdrop := supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (M := M) (fun p hp hxp ↦ hxS (Set.mem_biUnion hp hxp)) hx
  exact ⟨x, (isSecant_singleton_iff x).2 ⟨hx, lt_supportDim_of_add_one_eq hdrop⟩⟩

/-- **Existence of secant parameter lists.** A nonzero finite module over a Noetherian local ring
has a secant list whose terminal quotient has zero-dimensional support. -/
theorem exists_isSecant_supportDim_eq_zero [Nontrivial M] :
    ∃ qs : List R, IsSecant M qs ∧ supportDim R (prefixQuotient M qs) = 0 := by
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := R) (M := M)
  induction k generalizing M with
  | zero => exact ⟨[], .nil, by rw [supportDim_prefixQuotient_nil, hk, Nat.cast_zero]⟩
  | succ k ih =>
    obtain ⟨x, hx⟩ := exists_isSecant_singleton (M := M) (by rw [hk]; exact_mod_cast k.succ_pos)
    obtain ⟨hxm, hlt⟩ := (isSecant_singleton_iff x).1 hx
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    have hdim := supportDim_quotSMulTop_succ_eq_supportDim_of_lt hxm hlt
    rw [hk, Nat.cast_succ, ENat.WithBot.add_one_cancel] at hdim
    obtain ⟨qs, hqs, hqs0⟩ := ih hdim
    refine ⟨x :: qs, (isSecant_cons_iff x qs).2 ⟨hxm, hlt, hqs⟩, ?_⟩
    rwa [supportDim_prefixQuotient_cons]

/-- **Secant parameter completion.** Every secant list `rs` for a nonzero finite module over a
Noetherian local ring extends to a secant list `rs ++ qs` whose terminal quotient has
zero-dimensional support. -/
theorem IsSecant.exists_append [Nontrivial M] {rs : List R} (h : IsSecant M rs) :
    ∃ qs : List R, IsSecant M (rs ++ qs) ∧ supportDim R (prefixQuotient M (rs ++ qs)) = 0 := by
  have := prefixQuotient.nontrivial_of_forall_mem_maximalIdeal M h.mem_maximalIdeal
  obtain ⟨qs, hqs, hqs0⟩ := exists_isSecant_supportDim_eq_zero (R := R) (M := prefixQuotient M rs)
  exact ⟨qs, (isSecant_append_iff rs qs).2 ⟨h, hqs⟩,
    by rwa [supportDim_eq_of_equiv (prefixQuotient.appendEquiv M rs qs)]⟩

end Noetherian

end Secant

end TauCeti

namespace RingTheory.Sequence

open TauCeti

/-- A regular sequence on a finite module over a Noetherian local ring is secant: each regular
element of the maximal ideal lowers the dimension of the support by exactly one. -/
theorem IsRegular.isSecant {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {rs : List R} (h : IsRegular M rs) :
    IsSecant M rs :=
  have := h.nontrivial
  (isSecant_iff_supportDim_add_length_eq rs).2
    ⟨fun _ ↦ h.mem_maximalIdeal, supportDim_add_length_eq_supportDim_of_isRegular rs h⟩

end RingTheory.Sequence
