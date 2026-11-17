/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.AnnihilatorProduct
public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.Secant.Basic
import TauCeti.RingTheory.CohenMacaulay.LocalCohomology
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.Ideal.OfList
import TauCeti.RingTheory.KrullDimension.Module

/-!
# CM-secant sequences, parameter completion, and `p`-standard systems

A sequence `r₁, …, rₛ` in a local ring `(R, 𝔪)` is *CM-secant* for an `R`-module `M`
(`RingTheory.Sequence.IsCMSecant`, Česnavičius, Definition 3.1(ii)) when `rs` is secant for `M`,
`M ⧸ (rs) M` is Cohen–Macaulay, and for each `0 ≤ i < s` the prefix quotient
`Mᵢ = M ⧸ (r₁, …, rᵢ) M` has finite support dimension `d : ℕ` with
`rᵢ₊₁ ∈ localCohomology.annihilatorProduct 𝔪 Mᵢ d`.

Over a Noetherian local ring, every secant sequence on a finite Cohen–Macaulay module is regular
and hence CM-secant (`Module.IsCohenMacaulay.isCMSecant_of_isSecant`). Together with secant
parameter completion this gives `IsCMSecant.exists_append_supportDim_eq_zero`. Finally, we define
Kawasaki's `p`-standard systems (`RingTheory.Sequence.IsPStandard`) and prove the exact reversal
equivalence `isCMSecant_iff_isPStandard_reverse`.

## Main definitions & results

* `RingTheory.Sequence.IsCMSecant`, `RingTheory.Sequence.IsPStandard`.
* `LinearEquiv.isCMSecant_iff`, `LinearEquiv.isPStandard_iff`, `IsCMSecant.append`,
  `IsCMSecant.drop`.
* `Module.IsCohenMacaulay.isRegular_iff_isSecant`, `isCMSecant_of_isSecant`,
  `isCMSecant_iff_isSecant`.
* `IsCMSecant.exists_append_supportDim_eq_zero`, `isCMSecant_iff_isPStandard_reverse`,
  `isPStandard_iff_isCMSecant_reverse`, `IsCMSecant.exists_append_isPStandard_reverse`.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, Duke Math. J. 170 (2021),
  Definition 3.1(ii), Remark 3.3, Remark 3.4.
* T. Kawasaki, *On Cohen–Macaulayfication of quasi-projective schemes*, J. Math. Soc. Japan 48
  (1996), Definition 2.5.
-/

public section

universe u v

open IsLocalRing Pointwise

namespace RingTheory.Sequence

section CMSecant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A sequence `rs` in a local ring `(R, 𝔪)` is *CM-secant* for an `R`-module `M` if it is secant
for `M`, the terminal quotient `M ⧸ (rs) M` is Cohen–Macaulay, and each entry `rs[i]` lies in the
local-cohomology annihilator product of the preceding prefix quotient `M ⧸ (rs.take i) M` at cutoff
equal to its support dimension. -/
def IsCMSecant (M : Type u) [AddCommGroup M] [Module R M] (rs : List R) : Prop :=
  IsSecant M rs ∧
    Module.IsCohenMacaulay R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ∧
    ∀ i : Fin rs.length, ∃ d : ℕ,
      Module.supportDim R (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) =
        (d : WithBot ℕ∞) ∧
        rs[i] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
          (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) d

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Unfolds `RingTheory.Sequence.IsCMSecant`. -/
theorem isCMSecant_iff {rs : List R} :
    IsCMSecant M rs ↔
      IsSecant M rs ∧
        Module.IsCohenMacaulay R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ∧
        ∀ i : Fin rs.length, ∃ d : ℕ,
          Module.supportDim R (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) =
            (d : WithBot ℕ∞) ∧
            rs[i] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
              (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) d :=
  (Iff.rfl)

/-- Every CM-secant sequence is secant. -/
theorem IsCMSecant.isSecant {rs : List R} (h : IsCMSecant M rs) : IsSecant M rs :=
  h.1

/-- The terminal quotient of a CM-secant sequence is Cohen–Macaulay. -/
theorem IsCMSecant.isCohenMacaulay_quotient {rs : List R} (h : IsCMSecant M rs) :
    Module.IsCohenMacaulay R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
  h.2.1

/-- Every entry of a CM-secant sequence lies in the maximal ideal. -/
theorem IsCMSecant.mem_maximalIdeal {rs : List R} (h : IsCMSecant M rs) {r : R} (hr : r ∈ rs) :
    r ∈ maximalIdeal R :=
  h.isSecant.mem_maximalIdeal hr

/-- Each step of a CM-secant sequence strictly lowers the support dimension of the prefix
quotient. -/
theorem IsCMSecant.supportDim_take_succ_lt {rs : List R} (h : IsCMSecant M rs) (i : Fin rs.length) :
    Module.supportDim R (M ⧸ Ideal.ofList (rs.take (i.val + 1)) • (⊤ : Submodule R M)) <
      Module.supportDim R (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) :=
  h.isSecant.supportDim_take_succ_lt i

/-- At step `i`, the preceding prefix quotient has finite support dimension `d : ℕ` and `rs[i]` lies
in its local-cohomology annihilator product at cutoff `d`. -/
theorem IsCMSecant.exists_supportDim_eq_and_mem_annihilatorProduct {rs : List R}
    (h : IsCMSecant M rs) (i : Fin rs.length) :
    ∃ d : ℕ,
      Module.supportDim R (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) =
        (d : WithBot ℕ∞) ∧
        rs[i] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
          (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) d :=
  h.2.2 i

/-- If `rs` is CM-secant and the `i`-th prefix quotient has support dimension `d`, then `rs[i]` lies
in the local-cohomology annihilator product of that prefix quotient at cutoff `d`. -/
theorem IsCMSecant.mem_annihilatorProduct {rs : List R} (h : IsCMSecant M rs) (i : Fin rs.length)
    {d : ℕ}
    (hd : Module.supportDim R (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) =
      (d : WithBot ℕ∞)) :
    rs[i] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
      (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) d := by
  obtain ⟨d', hd', hmem⟩ := h.exists_supportDim_eq_and_mem_annihilatorProduct i
  have heq : d' = d := by exact_mod_cast hd'.symm.trans hd
  rwa [← heq]

/-- The empty list is CM-secant for `M` iff `M` is Cohen–Macaulay. -/
@[simp]
theorem isCMSecant_nil_iff :
    IsCMSecant M ([] : List R) ↔ Module.IsCohenMacaulay R M := by
  rw [isCMSecant_iff]
  constructor
  · rintro ⟨_, hcm, _⟩
    exact (Submodule.quotOfListNilSMulTopEquiv R M).isCohenMacaulay_iff.mp hcm
  · intro hcm
    refine ⟨isSecant_nil, ?_, fun i ↦ Fin.elim0 i⟩
    exact (Submodule.quotOfListNilSMulTopEquiv R M).isCohenMacaulay_iff.mpr hcm

/-- For a subsingleton module, only the empty list is CM-secant. -/
theorem isCMSecant_iff_eq_nil_of_subsingleton [Subsingleton M] {rs : List R} :
    IsCMSecant M rs ↔ rs = [] := by
  refine ⟨fun h ↦ isSecant_iff_eq_nil_of_subsingleton.mp h.isSecant, fun h ↦ ?_⟩
  rw [h, isCMSecant_nil_iff]
  exact Module.isCohenMacaulay_of_subsingleton

/-- Characterization of CM-secancy for a singleton `[r]`. -/
theorem isCMSecant_singleton_iff {r : R} :
    IsCMSecant M [r] ↔
      IsSecant M [r] ∧ Module.IsCohenMacaulay R (QuotSMulTop r M) ∧
        ∃ d : ℕ, Module.supportDim R M = (d : WithBot ℕ∞) ∧
          r ∈ localCohomology.annihilatorProduct (maximalIdeal R) M d := by
  rw [isCMSecant_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [(Submodule.quotOfListSingletonSMulTopEquiv M r).isCohenMacaulay_iff]
  refine and_congr_right fun _ ↦ ?_
  have e := Submodule.quotOfListNilSMulTopEquiv R M
  refine ⟨fun h ↦ let ⟨d, hd, hmem⟩ := h ⟨0, by simp⟩; ⟨d,
      by rwa [show ([r] : List R).take 0 = [] from rfl, Module.supportDim_eq_of_equiv e] at hd,
      by rwa [show ([r] : List R).take 0 = [] from rfl, e.annihilatorProduct_eq] at hmem⟩,
    fun ⟨d, hd, hmem⟩ i ↦ by
      obtain rfl : i = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
      exact ⟨d, by rwa [show ([r] : List R).take 0 = [] from rfl, Module.supportDim_eq_of_equiv e],
        by rwa [show ([r] : List R).take 0 = [] from rfl, e.annihilatorProduct_eq]⟩⟩

private theorem exists_supportDim_mem_of_list_eq {as bs : List R} (hab : as = bs) {r : R} :
    (∃ d : ℕ, Module.supportDim R (M ⧸ Ideal.ofList as • (⊤ : Submodule R M)) = (d : WithBot ℕ∞) ∧
        r ∈ localCohomology.annihilatorProduct (maximalIdeal R)
          (M ⧸ Ideal.ofList as • (⊤ : Submodule R M)) d) ↔
      (∃ d : ℕ, Module.supportDim R (M ⧸ Ideal.ofList bs • (⊤ : Submodule R M)) = (d : WithBot ℕ∞) ∧
          r ∈ localCohomology.annihilatorProduct (maximalIdeal R)
            (M ⧸ Ideal.ofList bs • (⊤ : Submodule R M)) d) := by
  subst hab; rfl

/-- Concatenating a CM-secant sequence `rs` on `M` with a CM-secant sequence `qs` on
`M ⧸ (rs) M` produces a CM-secant sequence `rs ++ qs` on `M`. -/
theorem IsCMSecant.append {rs qs : List R} (hrs : IsCMSecant M rs)
    (hqs : IsCMSecant (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) qs) :
    IsCMSecant M (rs ++ qs) := by
  refine ⟨hrs.isSecant.append hqs.isSecant,
    (Submodule.quotOfListAppendSMulTopEquiv M rs qs).isCohenMacaulay_iff.mpr
      hqs.isCohenMacaulay_quotient, fun i ↦ ?_⟩
  by_cases hi : i.val < rs.length
  · let i' : Fin rs.length := ⟨i.val, hi⟩
    rw [show (rs ++ qs)[i] = rs[i'] from List.getElem_append_left hi]
    exact (exists_supportDim_mem_of_list_eq (List.take_append_of_le_length hi.le)).mpr
      (hrs.exists_supportDim_eq_and_mem_annihilatorProduct i')
  · have hj_lt : i.val < rs.length + qs.length := by simpa [List.length_append] using i.isLt
    have ht : (rs ++ qs).take i.val = rs ++ qs.take (i.val - rs.length) := by
      rw [List.take_append, List.take_of_length_le (by omega)]
    let j' : Fin qs.length := ⟨i.val - rs.length, by omega⟩
    rw [show (rs ++ qs)[i] = qs[j'] from List.getElem_append_right (by omega)]
    refine (exists_supportDim_mem_of_list_eq ht).mpr ?_
    obtain ⟨d, hd, hmem⟩ := hqs.exists_supportDim_eq_and_mem_annihilatorProduct j'
    have e := Submodule.quotOfListAppendSMulTopEquiv M rs (qs.take (i.val - rs.length))
    exact ⟨d, (Module.supportDim_eq_of_equiv e).trans hd, (e.annihilatorProduct_eq _ _).symm ▸ hmem⟩

/-- Every suffix `rs.drop k` of a CM-secant sequence is CM-secant for `M ⧸ (rs.take k) M`. -/
theorem IsCMSecant.drop {rs : List R} (h : IsCMSecant M rs) (k : ℕ) :
    IsCMSecant (M ⧸ Ideal.ofList (rs.take k) • (⊤ : Submodule R M)) (rs.drop k) := by
  refine ⟨h.isSecant.drop k,
    ((Submodule.quotOfListAppendSMulTopEquiv M (rs.take k) (rs.drop k)).symm.trans
      (Submodule.quotEquivOfEq _ _ (by rw [List.take_append_drop]))).isCohenMacaulay_iff.mpr
      h.isCohenMacaulay_quotient, fun j ↦ ?_⟩
  have hlen : j.val < rs.length - k := by simpa [List.length_drop] using j.isLt
  let i' : Fin rs.length := ⟨k + j.val, by omega⟩
  rw [show (rs.drop k)[j] = rs[i'] from List.getElem_drop]
  obtain ⟨d, hd, hmem⟩ := h.exists_supportDim_eq_and_mem_annihilatorProduct i'
  have e :=
    (Submodule.quotOfListAppendSMulTopEquiv M (rs.take k) ((rs.drop k).take j.val)).symm.trans
      (Submodule.quotEquivOfEq _ _
        (by rw [(List.take_add (l := rs) (i := k) (j := j.val)).symm]))
  exact ⟨d, (Module.supportDim_eq_of_equiv e).trans hd, (e.annihilatorProduct_eq _ _).symm ▸ hmem⟩

end CMSecant

end RingTheory.Sequence

namespace LinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Linearly equivalent modules have the same CM-secant sequences. -/
theorem isCMSecant_iff (e : M ≃ₗ[R] N) (rs : List R) :
    RingTheory.Sequence.IsCMSecant M rs ↔ RingTheory.Sequence.IsCMSecant N rs := by
  simp only [RingTheory.Sequence.isCMSecant_iff]
  refine and_congr (e.isSecant_iff rs) (and_congr (e.quotSMulTop _).isCohenMacaulay_iff ?_)
  refine forall_congr' fun i ↦ exists_congr fun d ↦ ?_
  rw [Module.supportDim_eq_of_equiv (e.quotSMulTop (Ideal.ofList (rs.take i.val))),
    (e.quotSMulTop (Ideal.ofList (rs.take i.val))).annihilatorProduct_eq]

end LinearEquiv

namespace Module.IsCohenMacaulay

section Regular

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- On a nonzero finite Cohen–Macaulay module over a Noetherian local ring, every secant sequence
is regular. -/
theorem isRegular_of_isSecant [Nontrivial M] (h : IsCohenMacaulay R M) {rs : List R}
    (hsec : RingTheory.Sequence.IsSecant M rs) : RingTheory.Sequence.IsRegular M rs :=
  (h.isRegular_iff_supportDim_add_length_eq_supportDim rs
    fun _ hr ↦ hsec.mem_maximalIdeal hr).mpr hsec.supportDim_add_length_eq

/-- On a nonzero finite Cohen–Macaulay module over a Noetherian local ring, a sequence is regular
if and only if it is secant. -/
theorem isRegular_iff_isSecant [Nontrivial M] (h : IsCohenMacaulay R M) (rs : List R) :
    RingTheory.Sequence.IsRegular M rs ↔ RingTheory.Sequence.IsSecant M rs :=
  ⟨RingTheory.Sequence.IsRegular.isSecant, h.isRegular_of_isSecant⟩

end Regular

section CMSecant

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Every secant sequence on a finite Cohen–Macaulay module over a Noetherian local ring is
CM-secant. -/
theorem isCMSecant_of_isSecant (h : IsCohenMacaulay R M) {rs : List R}
    (hsec : RingTheory.Sequence.IsSecant M rs) : RingTheory.Sequence.IsCMSecant M rs := by
  cases subsingleton_or_nontrivial M with
  | inl _ =>
    rw [RingTheory.Sequence.isSecant_iff_eq_nil_of_subsingleton.mp hsec,
      RingTheory.Sequence.isCMSecant_nil_iff]
    exact h
  | inr _ =>
    have reg : RingTheory.Sequence.IsRegular M rs := h.isRegular_of_isSecant hsec
    refine ⟨hsec, (isCohenMacaulay_quotient_ofList_smul_iff rs reg).mpr h, fun i ↦ ?_⟩
    have : Nontrivial (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) :=
      hsec.nontrivial_quotient_take i
    obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast
      (R := R) (M := M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M))
    have hcm_i : IsCohenMacaulay R (M ⧸ Ideal.ofList (rs.take i.val) • (⊤ : Submodule R M)) :=
      (isCohenMacaulay_quotient_ofList_smul_iff (rs.take i.val)
        (h.isRegular_of_isSecant (hsec.take i.val))).mpr h
    refine ⟨d, hd, ?_⟩
    rw [hcm_i.annihilatorProduct_eq_top hd.ge]
    trivial

/-- On a finite Cohen–Macaulay module over a Noetherian local ring, CM-secancy is equivalent to
secancy. -/
theorem isCMSecant_iff_isSecant (h : IsCohenMacaulay R M) (rs : List R) :
    RingTheory.Sequence.IsCMSecant M rs ↔ RingTheory.Sequence.IsSecant M rs :=
  ⟨RingTheory.Sequence.IsCMSecant.isSecant, h.isCMSecant_of_isSecant⟩

end CMSecant

end Module.IsCohenMacaulay

namespace RingTheory.Sequence

section Extension

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Extension of CM-secant sequences to parameters.** Every CM-secant sequence on a nonzero finite
module over a Noetherian local ring extends to a CM-secant sequence whose terminal quotient has
support dimension zero. -/
theorem IsCMSecant.exists_append_supportDim_eq_zero [Nontrivial M] {rs : List R}
    (h : IsCMSecant M rs) :
    ∃ qs : List R, IsCMSecant M (rs ++ qs) ∧
      Module.supportDim R (M ⧸ Ideal.ofList (rs ++ qs) • (⊤ : Submodule R M)) = 0 := by
  have : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) := h.isSecant.nontrivial_quotient
  obtain ⟨qs, hqs_sec, hqs_dim⟩ :=
    exists_isSecant_supportDim_eq_zero (R := R) (M := M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))
  refine ⟨qs, h.append (h.isCohenMacaulay_quotient.isCMSecant_of_isSecant hqs_sec), ?_⟩
  rwa [Module.supportDim_eq_of_equiv (Submodule.quotOfListAppendSMulTopEquiv M rs qs)]

end Extension

section PStandard

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A *`p`-standard system of parameters* (Kawasaki 1996, Definition 2.5) for an `R`-module `M`
over a local ring `(R, 𝔪)` is a secant sequence `x₁, …, x_d` whose terminal quotient has support
dimension at most zero (hence zero when `M` is finite and nonzero, and `⊥` when `M = 0`) and such
that for every `0 ≤ j < d`, `x_{j+1}` lies in the local-cohomology annihilator product of
`M ⧸ (x_{j+2}, …, x_d) M` at cutoff equal to its support dimension. -/
def IsPStandard (M : Type u) [AddCommGroup M] [Module R M] (xs : List R) : Prop :=
  IsSecant M xs ∧
    Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0 ∧
    ∀ j : Fin xs.length, ∃ d : ℕ,
      Module.supportDim R (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) =
        (d : WithBot ℕ∞) ∧
        xs[j] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
          (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) d

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Unfolds `RingTheory.Sequence.IsPStandard`. -/
theorem isPStandard_iff {xs : List R} :
    IsPStandard M xs ↔
      IsSecant M xs ∧
        Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0 ∧
        ∀ j : Fin xs.length, ∃ d : ℕ,
          Module.supportDim R (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) =
            (d : WithBot ℕ∞) ∧
            xs[j] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
              (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) d :=
  (Iff.rfl)

/-- Every `p`-standard system of parameters is secant. -/
theorem IsPStandard.isSecant {xs : List R} (h : IsPStandard M xs) : IsSecant M xs :=
  h.1

/-- The terminal quotient of a `p`-standard system of parameters has support dimension at most
zero. -/
theorem IsPStandard.supportDim_quotient_le_zero {xs : List R} (h : IsPStandard M xs) :
    Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0 :=
  h.2.1

/-- For a nonzero finite module, the terminal quotient of a `p`-standard system of parameters has
support dimension zero. -/
theorem IsPStandard.supportDim_quotient_eq_zero [Module.Finite R M] [Nontrivial M] {xs : List R}
    (h : IsPStandard M xs) :
    Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) = 0 := by
  have := h.isSecant.nontrivial_quotient
  refine le_antisymm h.supportDim_quotient_le_zero ?_
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1
    (Module.supportDim_ne_bot_of_nontrivial R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)))
  rw [← he]
  exact_mod_cast zero_le

/-- At step `j`, the suffix quotient `M ⧸ (xs.drop (j + 1)) M` has finite support dimension `d : ℕ`
and `xs[j]` lies in its local-cohomology annihilator product at cutoff `d`. -/
theorem IsPStandard.exists_supportDim_eq_and_mem_annihilatorProduct {xs : List R}
    (h : IsPStandard M xs) (j : Fin xs.length) :
    ∃ d : ℕ,
      Module.supportDim R (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) =
        (d : WithBot ℕ∞) ∧
        xs[j] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
          (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) d :=
  h.2.2 j

/-- If `xs` is `p`-standard and the suffix quotient `M ⧸ (xs.drop (j + 1)) M` has support dimension
`d`, then `xs[j]` lies in its local-cohomology annihilator product at cutoff `d`. -/
theorem IsPStandard.mem_annihilatorProduct {xs : List R} (h : IsPStandard M xs) (j : Fin xs.length)
    {d : ℕ}
    (hd : Module.supportDim R (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) =
      (d : WithBot ℕ∞)) :
    xs[j] ∈ localCohomology.annihilatorProduct (maximalIdeal R)
      (M ⧸ Ideal.ofList (xs.drop (j.val + 1)) • (⊤ : Submodule R M)) d := by
  obtain ⟨d', hd', hmem⟩ := h.exists_supportDim_eq_and_mem_annihilatorProduct j
  have heq : d' = d := by exact_mod_cast hd'.symm.trans hd
  rwa [← heq]

/-- The empty list is `p`-standard for `M` iff `supportDim R M ≤ 0`. -/
@[simp]
theorem isPStandard_nil_iff :
    IsPStandard M ([] : List R) ↔ Module.supportDim R M ≤ 0 := by
  rw [isPStandard_iff, Module.supportDim_eq_of_equiv (Submodule.quotOfListNilSMulTopEquiv R M)]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨isSecant_nil, h, fun j ↦ Fin.elim0 j⟩⟩

/-- For a subsingleton module, only the empty list is `p`-standard. -/
theorem isPStandard_iff_eq_nil_of_subsingleton [Subsingleton M] {xs : List R} :
    IsPStandard M xs ↔ xs = [] := by
  refine ⟨fun h ↦ isSecant_iff_eq_nil_of_subsingleton.mp h.isSecant, fun h ↦ ?_⟩
  rw [h, isPStandard_nil_iff, Module.supportDim_eq_bot_of_subsingleton]
  exact bot_le

end PStandard

end RingTheory.Sequence

namespace LinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Linearly equivalent modules have the same `p`-standard systems of parameters. -/
theorem isPStandard_iff (e : M ≃ₗ[R] N) (xs : List R) :
    RingTheory.Sequence.IsPStandard M xs ↔ RingTheory.Sequence.IsPStandard N xs := by
  simp only [RingTheory.Sequence.isPStandard_iff]
  refine and_congr (e.isSecant_iff xs) ?_
  rw [Module.supportDim_eq_of_equiv (e.quotSMulTop (Ideal.ofList xs))]
  refine and_congr_right fun _ ↦ forall_congr' fun j ↦ exists_congr fun d ↦ ?_
  rw [Module.supportDim_eq_of_equiv (e.quotSMulTop (Ideal.ofList (xs.drop (j.val + 1)))),
    (e.quotSMulTop (Ideal.ofList (xs.drop (j.val + 1)))).annihilatorProduct_eq]

end LinearEquiv

namespace RingTheory.Sequence

section Reversal

private def quotDropReverseEquivTake {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] (rs : List R) (i j : ℕ) (hij : i + j + 1 = rs.length) :
    (M ⧸ Ideal.ofList (rs.reverse.drop (j + 1)) • (⊤ : Submodule R M)) ≃ₗ[R]
      (M ⧸ Ideal.ofList (rs.take i) • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [show rs.reverse.drop (j + 1) = (rs.take i).reverse by
      rw [List.drop_reverse]; congr 2; omega])).trans
    (Submodule.quotOfListSMulTopEquivOfPerm M (rs.take i).reverse_perm)

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Reversal comparison.** Let `rs` be a list whose terminal quotient on a finite module `M` over
a Noetherian local ring has support dimension at most zero. Then `rs` is CM-secant for `M` if and
only if its reversal `rs.reverse` is a `p`-standard system of parameters for `M`. -/
theorem isCMSecant_iff_isPStandard_reverse {rs : List R}
    (hdim : Module.supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≤ 0) :
    IsCMSecant M rs ↔ IsPStandard M rs.reverse := by
  have hdim_rev : Module.supportDim R (M ⧸ Ideal.ofList rs.reverse • (⊤ : Submodule R M)) ≤ 0 := by
    rwa [Module.supportDim_eq_of_equiv (Submodule.quotOfListSMulTopEquivOfPerm M rs.reverse_perm)]
  constructor
  · intro h
    refine ⟨h.isSecant.reverse, hdim_rev, fun j ↦ ?_⟩
    have hj : j.val < rs.length := by simpa using j.isLt
    let i : Fin rs.length := ⟨rs.length - 1 - j.val, by omega⟩
    obtain ⟨d, hd, hmem⟩ := h.exists_supportDim_eq_and_mem_annihilatorProduct i
    have e := quotDropReverseEquivTake M rs i.val j.val (by dsimp [i]; omega)
    rw [show rs.reverse[j] = rs[i] from List.getElem_reverse j.isLt]
    exact ⟨d, (Module.supportDim_eq_of_equiv e).trans hd, (e.annihilatorProduct_eq _ _).symm ▸ hmem⟩
  · intro h
    refine ⟨by simpa using h.isSecant.reverse, Module.isCohenMacaulay_of_supportDim_nonpos hdim,
      fun i ↦ ?_⟩
    let j : Fin rs.reverse.length := ⟨rs.length - 1 - i.val, by simp; omega⟩
    obtain ⟨d, hd, hmem⟩ := h.exists_supportDim_eq_and_mem_annihilatorProduct j
    have e := (quotDropReverseEquivTake M rs i.val j.val (by dsimp [j]; omega)).symm
    have hget : rs.reverse[j] = rs[i] := by
      change rs.reverse[j.val] = rs[i.val]; rw [List.getElem_reverse]; congr 1; dsimp [j]; omega
    rw [hget] at hmem
    exact ⟨d, (Module.supportDim_eq_of_equiv e).trans hd, (e.annihilatorProduct_eq _ _).symm ▸ hmem⟩

/-- A sequence `xs` is a `p`-standard system of parameters for a finite module `M` over a
Noetherian local ring if and only if `xs.reverse` is CM-secant for `M` and `M ⧸ (xs) M` has
support dimension at most zero. -/
theorem isPStandard_iff_isCMSecant_reverse (xs : List R) :
    IsPStandard M xs ↔
      IsCMSecant M xs.reverse ∧
        Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0 := by
  have e_rev := Submodule.quotOfListSMulTopEquivOfPerm M xs.reverse_perm
  refine ⟨fun h ↦ ⟨(isCMSecant_iff_isPStandard_reverse
      ((Module.supportDim_eq_of_equiv e_rev).symm ▸ h.supportDim_quotient_le_zero)).mpr
      (by simpa using h), h.supportDim_quotient_le_zero⟩,
    fun ⟨hcm, hdim⟩ ↦ by
      simpa using (isCMSecant_iff_isPStandard_reverse
        ((Module.supportDim_eq_of_equiv e_rev).symm ▸ hdim)).mp hcm⟩

/-- Every CM-secant sequence on a nonzero finite module over a Noetherian local ring extends to a
CM-secant sequence whose reversal is a `p`-standard system of parameters. -/
theorem IsCMSecant.exists_append_isPStandard_reverse [Nontrivial M] {rs : List R}
    (h : IsCMSecant M rs) :
    ∃ qs : List R, IsCMSecant M (rs ++ qs) ∧ IsPStandard M (rs ++ qs).reverse := by
  obtain ⟨qs, hcm, hdim⟩ := h.exists_append_supportDim_eq_zero
  exact ⟨qs, hcm, (isCMSecant_iff_isPStandard_reverse hdim.le).mp hcm⟩

end Reversal

end RingTheory.Sequence
