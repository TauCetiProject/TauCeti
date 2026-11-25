/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.AnnihilatorProduct
public import TauCeti.RingTheory.KrullDimension.Secant
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.KrullDimension.Module

/-!
# CM-secant sequences, parameter completion, and `p`-standard systems

For a module `M` over a local ring `(R, 𝔪)`, a list `r₁, …, rₛ` is *CM-secant* for `M`
(`TauCeti.IsCMSecant`, Česnavičius, Definition 3.1(ii)) when it is secant for `M`, the terminal
quotient `M ⧸ (r₁, …, rₛ) M` is Cohen–Macaulay, and for each `0 ≤ i < s` the preceding prefix
quotient `Mᵢ = M ⧸ (r₁, …, rᵢ) M` has finite support dimension `d : ℕ` with
`rᵢ₊₁ ∈ localCohomology.annihilatorProduct 𝔪 Mᵢ d`. Cohen–Macaulayness is required of the terminal
quotient only; intermediate quotients need not be Cohen–Macaulay, and prefixes of a CM-secant list
need not be CM-secant.

Over a Noetherian local ring, every secant list on a finite Cohen–Macaulay module is regular and
hence CM-secant (`Module.IsCohenMacaulay.isCMSecant_of_isSecant`), because all intermediate
prefix quotients remain Cohen–Macaulay with unit annihilator products. Combining this with secant
parameter completion shows that every CM-secant list on a nonzero finite module extends to a
CM-secant parameter list whose terminal quotient has zero-dimensional support
(`TauCeti.IsCMSecant.exists_append_supportDim_eq_zero`).

Finally, we define Kawasaki's *`p`-standard systems of parameters* (`TauCeti.IsPStandard`,
Kawasaki 1996, Definition 2.5) and establish the reversal equivalence
`TauCeti.isCMSecant_iff_isPStandard_reverse`: when the terminal quotient has support dimension at
most zero, a list is CM-secant if and only if its reversal is `p`-standard.

## Main definitions

* `TauCeti.IsCMSecant M rs`: `rs` is CM-secant for `M`.
* `TauCeti.IsPStandard M xs`: `xs` is a `p`-standard system of parameters for `M`.

## Main results

* `TauCeti.isCMSecant_nil_iff`, `TauCeti.isCMSecant_singleton_iff`, `TauCeti.IsCMSecant.append`,
  `TauCeti.IsCMSecant.drop`, `LinearEquiv.isCMSecant_iff`.
* `Module.IsCohenMacaulay.isRegular_of_isSecant`, `Module.IsCohenMacaulay.isRegular_iff_isSecant`,
  `Module.IsCohenMacaulay.isCMSecant_of_isSecant`, `Module.IsCohenMacaulay.isCMSecant_iff_isSecant`.
* `TauCeti.IsCMSecant.exists_append_supportDim_eq_zero`: extension of CM-secant lists to
  zero-dimensional terminal support.
* `TauCeti.isPStandard_nil_iff`, `LinearEquiv.isPStandard_iff`,
  `TauCeti.isCMSecant_iff_isPStandard_reverse`, `TauCeti.isPStandard_iff_isCMSecant_reverse`,
  `TauCeti.IsCMSecant.exists_append_isPStandard_reverse`.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, Duke Math. J. 170 (2021),
  Definition 3.1(ii), Remark 3.3, Remark 3.4.
* T. Kawasaki, *On Cohen–Macaulayfication of quasi-projective schemes*, J. Math. Soc. Japan 48
  (1996), Definition 2.5.
-/

public section

universe u v

open IsLocalRing Module localCohomology RingTheory.Sequence Pointwise

namespace TauCeti

section Transport

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Transport the paired finite-support-dimension witness and local-cohomology annihilator
membership across a linear equivalence. -/
private theorem exists_supportDim_and_mem_annihilatorProduct_congr (e : M ≃ₗ[R] N) (r : R) :
    (∃ d : ℕ, supportDim R M = d ∧ r ∈ annihilatorProduct (maximalIdeal R) M d) ↔
      ∃ d : ℕ, supportDim R N = d ∧ r ∈ annihilatorProduct (maximalIdeal R) N d := by
  simp only [supportDim_eq_of_equiv e, e.annihilatorProduct_eq]

end Transport

section CMSecant

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (M : Type u) [AddCommGroup M] [Module R M]
  {N : Type u} [AddCommGroup N] [Module R N]

/-- A list `rs` in a local ring `(R, 𝔪)` is *CM-secant* for an `R`-module `M` if it is secant for
`M`, the terminal quotient `M ⧸ (rs) M` is Cohen–Macaulay, and each entry `rs[i]` lies in the
local-cohomology annihilator product of the preceding prefix quotient `M ⧸ (rs.take i) M` at cutoff
equal to its support dimension. -/
@[mk_iff]
structure IsCMSecant (rs : List R) : Prop where
  isSecant : IsSecant M rs
  isCohenMacaulay_prefixQuotient : IsCohenMacaulay R (prefixQuotient M rs)
  exists_supportDim_and_mem_annihilatorProduct : ∀ i (hi : i < rs.length), ∃ d : ℕ,
    supportDim R (prefixQuotient M (rs.take i)) = d ∧
      rs[i] ∈ annihilatorProduct (maximalIdeal R) (prefixQuotient M (rs.take i)) d

variable {M}

/-- Every entry of a CM-secant list lies in the maximal ideal. -/
theorem IsCMSecant.mem_maximalIdeal {rs : List R} (h : IsCMSecant M rs) :
    ∀ r ∈ rs, r ∈ maximalIdeal R :=
  h.isSecant.mem_maximalIdeal

/-- Each step of a CM-secant list strictly lowers the support dimension of the prefix quotient. -/
theorem IsCMSecant.supportDim_lt {rs : List R} (h : IsCMSecant M rs) {i : ℕ} (hi : i < rs.length) :
    supportDim R (prefixQuotient M (rs.take (i + 1))) <
      supportDim R (prefixQuotient M (rs.take i)) :=
  h.isSecant.supportDim_lt i hi

/-- If `rs` is CM-secant and the `i`-th prefix quotient has support dimension `d`, then `rs[i]` lies
in the local-cohomology annihilator product of that prefix quotient at cutoff `d`. -/
theorem IsCMSecant.mem_annihilatorProduct {rs : List R} (h : IsCMSecant M rs) {i : ℕ}
    (hi : i < rs.length) {d : ℕ} (hd : supportDim R (prefixQuotient M (rs.take i)) = d) :
    rs[i] ∈ annihilatorProduct (maximalIdeal R) (prefixQuotient M (rs.take i)) d := by
  obtain ⟨d', hd', hmem⟩ := h.exists_supportDim_and_mem_annihilatorProduct i hi
  obtain rfl : d' = d := by exact_mod_cast hd'.symm.trans hd
  exact hmem

/-- The empty list is CM-secant for `M` if and only if `M` is Cohen–Macaulay. -/
@[simp]
theorem isCMSecant_nil_iff : IsCMSecant M ([] : List R) ↔ IsCohenMacaulay R M := by
  rw [isCMSecant_iff, (prefixQuotient.nilEquiv M).isCohenMacaulay_iff]
  simp [IsSecant.nil]

/-- Only the empty list is CM-secant for the zero module. -/
theorem isCMSecant_iff_eq_nil [Subsingleton M] {rs : List R} : IsCMSecant M rs ↔ rs = [] :=
  ⟨fun h ↦ isSecant_iff_eq_nil.1 h.isSecant,
    fun h ↦ h ▸ isCMSecant_nil_iff.2 isCohenMacaulay_of_subsingleton⟩

/-- CM-secancy is invariant under linear equivalence of modules. -/
theorem _root_.LinearEquiv.isCMSecant_iff (e : M ≃ₗ[R] N) {rs : List R} :
    IsCMSecant M rs ↔ IsCMSecant N rs := by
  rw [TauCeti.isCMSecant_iff, TauCeti.isCMSecant_iff, e.isSecant_iff,
    (prefixQuotient.congr rs e).isCohenMacaulay_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun i _ ↦ ?_
  exact exists_supportDim_and_mem_annihilatorProduct_congr
    (prefixQuotient.congr (rs.take i) e) rs[i]

/-- A one-element list `[r]` is CM-secant for `M` if and only if `[r]` is secant for `M`,
`M ⧸ r M` is Cohen–Macaulay, and `M` has finite support dimension `d` with `r ∈ a_𝔪(M, d)`. -/
theorem isCMSecant_singleton_iff (r : R) :
    IsCMSecant M [r] ↔ IsSecant M [r] ∧ IsCohenMacaulay R (QuotSMulTop r M) ∧
      ∃ d : ℕ, supportDim R M = d ∧ r ∈ annihilatorProduct (maximalIdeal R) M d := by
  rw [isCMSecant_iff, (prefixQuotient.singletonEquiv M r).isCohenMacaulay_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  have h0 := exists_supportDim_and_mem_annihilatorProduct_congr (prefixQuotient.nilEquiv M) r
  refine ⟨fun h ↦ h0.1 (h 0 (by simp)), fun h i hi ↦ ?_⟩
  obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
  exact h0.2 h

/-- **CM-secant concatenation.** Concatenating a CM-secant list `rs` on `M` with a CM-secant list
`qs` on `M ⧸ (rs) M` produces a CM-secant list `rs ++ qs` on `M`. -/
theorem IsCMSecant.append {rs qs : List R} (hrs : IsCMSecant M rs)
    (hqs : IsCMSecant (prefixQuotient M rs) qs) : IsCMSecant M (rs ++ qs) := by
  refine ⟨(isSecant_append_iff rs qs).2 ⟨hrs.isSecant, hqs.isSecant⟩,
    (prefixQuotient.appendEquiv M rs qs).isCohenMacaulay_iff.2
      hqs.isCohenMacaulay_prefixQuotient, fun i hi ↦ ?_⟩
  by_cases hlt : i < rs.length
  · let e := prefixQuotient.equivOfPerm M
      (List.Perm.of_eq (List.take_append_of_le_length (l₂ := qs) hlt.le))
    rw [List.getElem_append_left hlt]
    exact (exists_supportDim_and_mem_annihilatorProduct_congr e rs[i]).2
      (hrs.exists_supportDim_and_mem_annihilatorProduct i hlt)
  · let j := i - rs.length
    have hj : j < qs.length := by rw [List.length_append] at hi; omega
    have hlen : i = rs.length + j := by omega
    have ht : (rs ++ qs).take i = rs ++ qs.take j := by rw [hlen, List.take_length_add_append]
    let e := (prefixQuotient.equivOfPerm M (List.Perm.of_eq ht)).trans
      (prefixQuotient.appendEquiv M rs (qs.take j))
    rw [List.getElem_append_right (Nat.not_lt.1 hlt)]
    exact (exists_supportDim_and_mem_annihilatorProduct_congr e _).2
      (hqs.exists_supportDim_and_mem_annihilatorProduct j hj)

/-- Every suffix `rs.drop k` of a CM-secant list is CM-secant for `M ⧸ (rs.take k) M`. -/
theorem IsCMSecant.drop {rs : List R} (h : IsCMSecant M rs) (k : ℕ) :
    IsCMSecant (prefixQuotient M (rs.take k)) (rs.drop k) := by
  have he_term := (prefixQuotient.appendEquiv M (rs.take k) (rs.drop k)).symm.trans
    (prefixQuotient.equivOfPerm M (List.Perm.of_eq (List.take_append_drop k rs)))
  refine ⟨h.isSecant.drop k, he_term.isCohenMacaulay_iff.2 h.isCohenMacaulay_prefixQuotient,
    fun j hj ↦ ?_⟩
  have hkj : k + j < rs.length := by rw [List.length_drop] at hj; omega
  let e := (prefixQuotient.appendEquiv M (rs.take k) ((rs.drop k).take j)).symm.trans
    (prefixQuotient.equivOfPerm M (List.Perm.of_eq List.take_add.symm))
  rw [List.getElem_drop]
  exact (exists_supportDim_and_mem_annihilatorProduct_congr e _).2
    (h.exists_supportDim_and_mem_annihilatorProduct (k + j) hkj)

end CMSecant

end TauCeti

namespace Module.IsCohenMacaulay

open TauCeti

section Regular

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- On a nonzero finite Cohen–Macaulay module over a Noetherian local ring, every secant list is
regular. -/
theorem isRegular_of_isSecant [Nontrivial M] (h : IsCohenMacaulay R M) {rs : List R}
    (hsec : IsSecant M rs) : IsRegular M rs :=
  (h.isRegular_iff_supportDim_add_length_eq_supportDim rs hsec.mem_maximalIdeal).2
    hsec.supportDim_add_length_eq

/-- On a nonzero finite Cohen–Macaulay module over a Noetherian local ring, a list is regular if
and only if it is secant. -/
theorem isRegular_iff_isSecant [Nontrivial M] (h : IsCohenMacaulay R M) (rs : List R) :
    IsRegular M rs ↔ IsSecant M rs :=
  ⟨IsRegular.isSecant, h.isRegular_of_isSecant⟩

end Regular

section CMSecant

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Every secant list on a finite Cohen–Macaulay module over a Noetherian local ring is
CM-secant. -/
theorem isCMSecant_of_isSecant (h : IsCohenMacaulay R M) {rs : List R}
    (hsec : IsSecant M rs) : IsCMSecant M rs := by
  cases subsingleton_or_nontrivial M
  · rw [isSecant_iff_eq_nil.1 hsec, isCMSecant_nil_iff]
    exact h
  · have reg : IsRegular M rs := h.isRegular_of_isSecant hsec
    refine ⟨hsec, (isCohenMacaulay_quotient_ofList_smul_iff rs reg).2 h, fun i hi ↦ ?_⟩
    have := hsec.nontrivial_prefixQuotient_take hi
    obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast (R := R) (M := prefixQuotient M (rs.take i))
    have hcm_i : IsCohenMacaulay R (prefixQuotient M (rs.take i)) :=
      (isCohenMacaulay_quotient_ofList_smul_iff (rs.take i)
        (h.isRegular_of_isSecant (hsec.take i))).2 h
    refine ⟨d, hd, ?_⟩
    rw [hcm_i.annihilatorProduct_eq_top hd]
    trivial

/-- On a finite Cohen–Macaulay module over a Noetherian local ring, CM-secancy is equivalent to
secancy. -/
theorem isCMSecant_iff_isSecant (h : IsCohenMacaulay R M) (rs : List R) :
    IsCMSecant M rs ↔ IsSecant M rs :=
  ⟨IsCMSecant.isSecant, h.isCMSecant_of_isSecant⟩

end CMSecant

end Module.IsCohenMacaulay

namespace TauCeti

section Extension

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Extension of CM-secant lists to parameters.** Every CM-secant list on a nonzero finite module
over a Noetherian local ring extends to a CM-secant list whose terminal quotient has
zero-dimensional support. -/
theorem IsCMSecant.exists_append_supportDim_eq_zero [Nontrivial M] {rs : List R}
    (h : IsCMSecant M rs) :
    ∃ qs : List R, IsCMSecant M (rs ++ qs) ∧
      supportDim R (prefixQuotient M (rs ++ qs)) = 0 := by
  obtain ⟨qs, hsec, hdim⟩ := h.isSecant.exists_append
  have hqs : IsSecant (prefixQuotient M rs) qs := ((isSecant_append_iff rs qs).1 hsec).2
  exact ⟨qs, h.append (h.isCohenMacaulay_prefixQuotient.isCMSecant_of_isSecant hqs), hdim⟩

end Extension

section PStandard

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (M : Type u) [AddCommGroup M] [Module R M]
  {N : Type u} [AddCommGroup N] [Module R N]

/-- A *`p`-standard system of parameters* (Kawasaki 1996, Definition 2.5) for an `R`-module `M`
over a local ring `(R, 𝔪)` is a secant list `x₁, …, x_d` whose terminal quotient has support
dimension at most zero (hence zero when `M` is finite and nonzero, and `⊥` when `M = 0`) and such
that for every `0 ≤ j < d`, `x_{j+1}` lies in the local-cohomology annihilator product of
`M ⧸ (x_{j+2}, …, x_d) M` at cutoff equal to its support dimension. -/
@[mk_iff]
structure IsPStandard (xs : List R) : Prop where
  isSecant : IsSecant M xs
  supportDim_prefixQuotient_le_zero : supportDim R (prefixQuotient M xs) ≤ 0
  exists_supportDim_and_mem_annihilatorProduct : ∀ j (hj : j < xs.length), ∃ d : ℕ,
    supportDim R (prefixQuotient M (xs.drop (j + 1))) = d ∧
      xs[j] ∈ annihilatorProduct (maximalIdeal R) (prefixQuotient M (xs.drop (j + 1))) d

variable {M}

/-- For a nonzero finite module, the terminal quotient of a `p`-standard system of parameters has
support dimension zero. -/
theorem IsPStandard.supportDim_prefixQuotient_eq_zero [Module.Finite R M] [Nontrivial M]
    {xs : List R} (h : IsPStandard M xs) :
    supportDim R (prefixQuotient M xs) = 0 := by
  have := prefixQuotient.nontrivial_of_forall_mem_maximalIdeal M h.isSecant.mem_maximalIdeal
  refine le_antisymm h.supportDim_prefixQuotient_le_zero ?_
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1
    (supportDim_ne_bot_of_nontrivial R (prefixQuotient M xs))
  rw [← he]
  exact_mod_cast zero_le

/-- If `xs` is `p`-standard and the suffix quotient `M ⧸ (xs.drop (j + 1)) M` has support dimension
`d`, then `xs[j]` lies in its local-cohomology annihilator product at cutoff `d`. -/
theorem IsPStandard.mem_annihilatorProduct {xs : List R} (h : IsPStandard M xs) {j : ℕ}
    (hj : j < xs.length) {d : ℕ} (hd : supportDim R (prefixQuotient M (xs.drop (j + 1))) = d) :
    xs[j] ∈ annihilatorProduct (maximalIdeal R) (prefixQuotient M (xs.drop (j + 1))) d := by
  obtain ⟨d', hd', hmem⟩ := h.exists_supportDim_and_mem_annihilatorProduct j hj
  obtain rfl : d' = d := by exact_mod_cast hd'.symm.trans hd
  exact hmem

/-- The empty list is `p`-standard for `M` if and only if `supportDim R M ≤ 0`. -/
@[simp]
theorem isPStandard_nil_iff : IsPStandard M ([] : List R) ↔ supportDim R M ≤ 0 := by
  rw [isPStandard_iff, supportDim_prefixQuotient_nil]
  simp [IsSecant.nil]

/-- Only the empty list is `p`-standard for the zero module. -/
theorem isPStandard_iff_eq_nil [Subsingleton M] {xs : List R} : IsPStandard M xs ↔ xs = [] :=
  ⟨fun h ↦ isSecant_iff_eq_nil.1 h.isSecant,
    fun h ↦ h ▸ isPStandard_nil_iff.2 (by simp [supportDim_eq_bot_of_subsingleton])⟩

/-- Being a `p`-standard system of parameters is invariant under linear equivalence of modules. -/
theorem _root_.LinearEquiv.isPStandard_iff (e : M ≃ₗ[R] N) {xs : List R} :
    IsPStandard M xs ↔ IsPStandard N xs := by
  rw [TauCeti.isPStandard_iff, TauCeti.isPStandard_iff, e.isSecant_iff,
    supportDim_eq_of_equiv (prefixQuotient.congr xs e)]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun j _ ↦ ?_
  exact exists_supportDim_and_mem_annihilatorProduct_congr
    (prefixQuotient.congr (xs.drop (j + 1)) e) xs[j]

end PStandard

section Reversal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Reversal comparison.** Let `rs` be a list whose terminal quotient on a finite module `M` over
a Noetherian local ring has support dimension at most zero. Then `rs` is CM-secant for `M` if and
only if its reversal `rs.reverse` is a `p`-standard system of parameters for `M`. -/
theorem isCMSecant_iff_isPStandard_reverse {rs : List R}
    (hdim : supportDim R (prefixQuotient M rs) ≤ 0) :
    IsCMSecant M rs ↔ IsPStandard M rs.reverse := by
  have hdim_rev : supportDim R (prefixQuotient M rs.reverse) ≤ 0 := by
    rwa [supportDim_eq_of_equiv (prefixQuotient.equivOfPerm M rs.reverse_perm)]
  constructor
  · intro h
    refine ⟨h.isSecant.reverse, hdim_rev, fun j hj ↦ ?_⟩
    have hj' : j < rs.length := by simpa using hj
    have hi_eq : rs.length - (j + 1) = rs.length - 1 - j := by omega
    let e := (prefixQuotient.dropReverseEquiv M rs (j + 1)).trans
      (prefixQuotient.equivOfPerm M (List.Perm.of_eq (congrArg rs.take hi_eq)))
    rw [List.getElem_reverse hj]
    exact (exists_supportDim_and_mem_annihilatorProduct_congr e _).2
      (h.exists_supportDim_and_mem_annihilatorProduct (rs.length - 1 - j) (by omega))
  · intro h
    refine ⟨isSecant_reverse_iff rs |>.1 h.isSecant, isCohenMacaulay_of_supportDim_nonpos hdim,
      fun i hi ↦ ?_⟩
    let j := rs.length - 1 - i
    have hj : j < rs.reverse.length := by simp [j]; omega
    have hi_eq : rs.length - (j + 1) = i := by omega
    let e := (prefixQuotient.dropReverseEquiv M rs (j + 1)).trans
      (prefixQuotient.equivOfPerm M (List.Perm.of_eq (congrArg rs.take hi_eq)))
    have hget : rs.reverse[j] = rs[i] := by
      rw [List.getElem_reverse hj]
      congr 1
      omega
    have hstep := h.exists_supportDim_and_mem_annihilatorProduct j hj
    rw [hget] at hstep
    exact (exists_supportDim_and_mem_annihilatorProduct_congr e rs[i]).1 hstep

/-- A list `xs` is a `p`-standard system of parameters for a finite module `M` over a Noetherian
local ring if and only if `xs.reverse` is CM-secant for `M` and `M ⧸ (xs) M` has support dimension
at most zero. -/
theorem isPStandard_iff_isCMSecant_reverse (xs : List R) :
    IsPStandard M xs ↔
      IsCMSecant M xs.reverse ∧ supportDim R (prefixQuotient M xs) ≤ 0 := by
  have he : supportDim R (prefixQuotient M xs.reverse) = supportDim R (prefixQuotient M xs) :=
    supportDim_eq_of_equiv (prefixQuotient.equivOfPerm M xs.reverse_perm)
  refine ⟨fun h ↦ ⟨(isCMSecant_iff_isPStandard_reverse (he ▸ h.supportDim_prefixQuotient_le_zero)).2
      (by simpa only [List.reverse_reverse] using h), h.supportDim_prefixQuotient_le_zero⟩,
    fun ⟨hcm, hdim⟩ ↦ by
      simpa only [List.reverse_reverse] using
        (isCMSecant_iff_isPStandard_reverse (he ▸ hdim)).1 hcm⟩

/-- Every CM-secant list on a nonzero finite module over a Noetherian local ring extends to a
CM-secant list whose reversal is a `p`-standard system of parameters. -/
theorem IsCMSecant.exists_append_isPStandard_reverse [Nontrivial M] {rs : List R}
    (h : IsCMSecant M rs) :
    ∃ qs : List R, IsCMSecant M (rs ++ qs) ∧ IsPStandard M (rs ++ qs).reverse := by
  obtain ⟨qs, hcm, hdim⟩ := h.exists_append_supportDim_eq_zero
  exact ⟨qs, hcm, (isCMSecant_iff_isPStandard_reverse hdim.le).1 hcm⟩

end Reversal

end TauCeti
