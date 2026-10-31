/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.KrullDimension.Regular
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Data.ENat.Monoid
import TauCeti.RingTheory.CohenMacaulay.Normal
import TauCeti.RingTheory.IntegralClosure.GoingDown
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.KrullDimension.Module

/-!
# Regular sequences in Cohen–Macaulay modules

Let `M` be a nonzero finite Cohen–Macaulay module over a Noetherian local ring `(R, 𝔪)`. A
sequence `r₁, …, rₙ` of elements of `𝔪` is `M`-regular if and only if it cuts the dimension of
the support down by its length, `dim M ⧸ (r₁, …, rₙ) M + n = dim M` (Stacks, Proposition 10.103.4
(00N6)). One direction holds for every finite module
(`Module.supportDim_add_length_eq_supportDim_of_isRegular`); the content is the converse, for
which the Cohen–Macaulay hypothesis is essential.

The single-element case rests on unmixedness: every associated prime `p` of a Cohen–Macaulay
module satisfies `dim R ⧸ p = dim M`, so if `x` is a zero divisor on `M`, it lies in such a `p`,
which then lies in the support of `M ⧸ x M`, and the dimension does not drop at all.

The main application is to a local homomorphism `R → S` of local rings with `S` Noetherian and
Cohen–Macaulay. If `r₁, …, rₙ` generate the maximal ideal of `R` and
`dim S = dim S ⧸ 𝔪_R S + n`, then the images of the `rᵢ` form an `S`-regular sequence. For a
regular local ring `R` and a regular system of parameters, `n = dim R` and the hypothesis is the
dimension formula `dim S = dim R + dim S ⧸ 𝔪_R S` of miracle flatness (Stacks, Lemma 10.128.1
(00R4)), whose proof starts from exactly this regular sequence.

For a finite torsion-free algebra `B` over a Noetherian integrally closed local domain `A`, the
localization `B_𝔮` at a maximal ideal need not be finite over `A`, but going down along `A → B`
gives it the dimension of `A`, and its closed fibre `B_𝔮 ⧸ 𝔪_A B_𝔮` is Artinian. So `B_𝔮`
satisfies the dimension formula of miracle flatness, and a Cohen–Macaulay `B_𝔮` receives a
regular sequence from a regular system of parameters of `A`. In dimension two, normality of
`B_𝔮` already implies that it is Cohen–Macaulay (Stacks, Lemma 10.157.4 (031S)). This is the
input to miracle flatness for the localizations of finite normal algebras over a normal local
domain of dimension two, such as a regular local ring of dimension two, as in the proof of purity
for regular local rings (Stacks, Lemma 58.21.3 (0BMA)).

## Main results

* `Module.IsCohenMacaulay.isSMulRegular_of_supportDim_quotSMulTop_lt`: an element `x` with
  `dim M ⧸ x M < dim M` is `M`-regular (Stacks, Lemma 10.103.3 (00N5), part (a)).
* `Module.IsCohenMacaulay.isSMulRegular_iff_supportDim_quotSMulTop_lt`: for `x ∈ 𝔪` and `M ≠ 0`,
  this is a characterization of `M`-regular elements.
* `Module.IsCohenMacaulay.quotSMulTop`: under the same hypothesis `M ⧸ x M` is again
  Cohen–Macaulay (Stacks, Lemma 10.103.3 (00N5), part (b)).
* `Module.IsCohenMacaulay.isRegular_iff_supportDim_add_length_eq_supportDim`: for `M ≠ 0`, a
  sequence in `𝔪` is `M`-regular if and only if it cuts the dimension of the support down by its
  length (Stacks, Proposition 10.103.4 (00N6)).
* `Module.IsCohenMacaulay.isRegular_map_algebraMap`: generators of the maximal ideal of `R` whose
  number is `dim S - dim S ⧸ 𝔪_R S` map to an `S`-regular sequence.
* `Module.IsCohenMacaulay.isRegular_map_algebraMap_localization`: for a finite torsion-free
  algebra `B` over a Noetherian integrally closed local domain `A` and a maximal ideal `𝔮` of `B`
  with `B_𝔮` Cohen–Macaulay, `dim A` generators of the maximal ideal of `A` map to a
  `B_𝔮`-regular sequence.
* `TauCeti.isRegular_pair_localization_of_isIntegrallyClosed`: when `A` has dimension two and
  `B_𝔮` is a normal domain, `B_𝔮` is automatically Cohen–Macaulay, so every pair generating the
  maximal ideal of `A` maps to a `B_𝔮`-regular sequence.

## References

* [Stacks Project, Section 10.103](https://stacks.math.columbia.edu/tag/00N2),
  Lemma 10.103.3 (00N5) and Proposition 10.103.4 (00N6).
* [Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), the first step of
  its proof.
* [Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), the dimension-two
  case of its proof.
-/

public section

universe u v

open IsLocalRing RingTheory.Sequence Ideal

namespace Module.IsCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- In a finite Cohen–Macaulay module over a Noetherian local ring, an element `x` with
`dim M ⧸ x M < dim M` is `M`-regular. Stacks, Lemma 10.103.3 (00N5), part (a), where the drop is
assumed to be exactly one. -/
@[stacks 00N5 "(a)"]
theorem isSMulRegular_of_supportDim_quotSMulTop_lt (h : IsCohenMacaulay R M) {x : R}
    (hx : supportDim R (QuotSMulTop x M) < supportDim R M) : IsSMulRegular M x := by
  by_contra hreg
  -- A zero divisor lies in an associated prime `p`.
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact hreg
  obtain ⟨p, hp, hxp⟩ : ∃ p ∈ associatedPrimes R M, x ∈ p := by simpa using hmem
  have hp : IsAssociatedPrime p M := AssociatedPrimes.mem_iff.1 hp
  -- So `p` lies in the support of `M ⧸ x M`, which therefore has dimension `≥ dim R ⧸ p`.
  have hsupp : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ support R (QuotSMulTop x M) := by
    rw [support_quotSMulTop]
    refine ⟨mem_support_iff_of_finite.2 ?_, by simpa using hxp⟩
    exact Submodule.annihilator_top (R := R) (M := M) ▸ hp.annihilator_le
  have hle : ringKrullDim (R ⧸ p) ≤ supportDim R (QuotSMulTop x M) := by
    rw [supportDim_eq_ringKrullDim_quotient_annihilator]
    exact ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (mem_support_iff_of_finite.1 hsupp))
  -- By unmixedness `dim R ⧸ p = dim M`, so the dimension does not drop.
  exact (h.ringKrullDim_quotient_eq_supportDim hp ▸ hle).not_gt hx

/-- For `x` in the maximal ideal and a nonzero finite Cohen–Macaulay module `M` over a Noetherian
local ring, `x` is `M`-regular if and only if `dim M ⧸ x M < dim M`; the drop is then exactly one
(`Module.supportDim_quotSMulTop_succ_eq_supportDim`). -/
theorem isSMulRegular_iff_supportDim_quotSMulTop_lt [Nontrivial M] (h : IsCohenMacaulay R M)
    {x : R} (hx : x ∈ maximalIdeal R) :
    IsSMulRegular M x ↔ supportDim R (QuotSMulTop x M) < supportDim R M := by
  refine ⟨fun reg ↦ ?_, h.isSMulRegular_of_supportDim_quotSMulTop_lt⟩
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := R) (M := M)
  rw [hk]
  exact ENat.WithBot.lt_natCast_of_add_one_eq
    (hk ▸ supportDim_quotSMulTop_succ_eq_supportDim reg hx)

/-- If `x ∈ 𝔪` satisfies `dim M ⧸ x M < dim M` for a finite Cohen–Macaulay module `M` over a
Noetherian local ring, then `M ⧸ x M` is Cohen–Macaulay. Stacks, Lemma 10.103.3 (00N5),
part (b). -/
@[stacks 00N5 "(b)"]
theorem quotSMulTop (h : IsCohenMacaulay R M) {x : R} (hx : x ∈ maximalIdeal R)
    (hdim : supportDim R (QuotSMulTop x M) < supportDim R M) :
    IsCohenMacaulay R (QuotSMulTop x M) :=
  (isCohenMacaulay_quotSMulTop_iff (h.isSMulRegular_of_supportDim_quotSMulTop_lt hdim) hx).2 h

/-- **Regular sequences in a Cohen–Macaulay module.** For a nonzero finite Cohen–Macaulay module
`M` over a Noetherian local ring, a sequence `r₁, …, rₙ` of elements of the maximal ideal is
`M`-regular if and only if `dim M ⧸ (r₁, …, rₙ) M + n = dim M`. Stacks, Proposition 10.103.4
(00N6). -/
@[stacks 00N6]
theorem isRegular_iff_supportDim_add_length_eq_supportDim [Nontrivial M]
    (h : IsCohenMacaulay R M) (rs : List R) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    IsRegular M rs ↔
      supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  refine ⟨supportDim_add_length_eq_supportDim_of_isRegular rs, fun hdim ↦ ?_⟩
  induction rs generalizing M with
  | nil => exact IsRegular.nil R M
  | cons x rs ih =>
    have hx : x ∈ maximalIdeal R := hrs x List.mem_cons_self
    have hrs' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr ↦ hrs r (List.mem_cons_of_mem x hr)
    -- Write `N = M ⧸ x M` and `a = dim N ⧸ (r₂, …, rₙ) N`, so that `a + (n - 1) + 1 = dim M`.
    rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      List.length_cons, Nat.cast_add_one, ← add_assoc] at hdim
    obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := R) (M := M)
    -- Each of `r₂, …, rₙ` drops the dimension by at most one, so `dim N ≤ a + (n - 1) < dim M`.
    have hlt : supportDim R (QuotSMulTop x M) < supportDim R M :=
      (supportDim_le_supportDim_quotient_add_length rs hrs').trans_lt
        (hk ▸ ENat.WithBot.lt_natCast_of_add_one_eq (hdim.trans hk))
    have reg := h.isSMulRegular_of_supportDim_quotSMulTop_lt hlt
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
    -- Now `dim N + 1 = dim M`, and the induction hypothesis applies to `N`.
    rw [← supportDim_quotSMulTop_succ_eq_supportDim reg hx, ENat.WithBot.add_one_cancel] at hdim
    exact (isRegular_cons_iff M x rs).2 ⟨reg, ih (h.quotSMulTop hx hlt) hrs' hdim⟩

end Module.IsCohenMacaulay

namespace Module.IsCohenMacaulay

variable {R : Type*} {S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Let `R → S` be a local homomorphism of local rings with `S` Noetherian and Cohen–Macaulay. If
`r₁, …, rₙ` generate the maximal ideal of `R` and `dim S ⧸ 𝔪_R S + n = dim S`, then the images of
the `rᵢ` form an `S`-regular sequence. For a regular system of parameters of a regular local ring
`R`, this hypothesis is the dimension formula of miracle flatness (Stacks, Lemma 10.128.1
(00R4)). -/
theorem isRegular_map_algebraMap (hS : IsCohenMacaulay S S) {rs : List R}
    (hrs : ofList rs = maximalIdeal R)
    (hdim : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) + rs.length =
      ringKrullDim S) :
    IsRegular S (rs.map (algebraMap R S)) := by
  refine (hS.isRegular_iff_supportDim_add_length_eq_supportDim _ fun r hr ↦ ?_).2 ?_
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hr
    exact map_nonunit (algebraMap R S) r (hrs ▸ subset_span hr')
  · rw [← map_ofList, hrs, smul_eq_mul, mul_top, supportDim_quotient_eq_ringKrullDim,
      List.length_map, supportDim_self_eq_ringKrullDim, hdim]

end Module.IsCohenMacaulay

namespace Module.IsCohenMacaulay

variable {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- Let `A` be a Noetherian integrally closed local domain, `B` a finite torsion-free `A`-algebra
and `𝔮` a maximal ideal of `B` such that `B_𝔮` is Cohen–Macaulay. If `r₁, …, r_d` generate the
maximal ideal of `A`, where `d = dim A`, then their images form a `B_𝔮`-regular sequence. -/
theorem isRegular_map_algebraMap_localization {𝔮 : Ideal B} [𝔮.IsMaximal]
    (h : IsCohenMacaulay (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮)) {rs : List A}
    (hrs : ofList rs = maximalIdeal A) (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim A) :
    IsRegular (Localization.AtPrime 𝔮) (rs.map (algebraMap A (Localization.AtPrime 𝔮))) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hunder : 𝔮.under A = maximalIdeal A := eq_maximalIdeal inferInstance
  have : 𝔮.LiesOver (maximalIdeal A) := ⟨hunder.symm⟩
  have hmax : (maximalIdeal (Localization.AtPrime 𝔮)).comap
      (algebraMap A (Localization.AtPrime 𝔮)) = maximalIdeal A := by
    rw [← under_def, ← under_under (B := B), Localization.AtPrime.under_maximalIdeal, hunder]
  have : IsLocalHom (algebraMap A (Localization.AtPrime 𝔮)) :=
    ((local_hom_TFAE (algebraMap A (Localization.AtPrime 𝔮))).out 1 5).mpr hmax
  refine h.isRegular_map_algebraMap hrs ?_
  rw [ringKrullDim_localization_atPrime_quotient_map_eq_zero (maximalIdeal A) 𝔮, zero_add, hlen,
    ringKrullDim_localization_atPrime_eq_height_under A, hunder,
    maximalIdeal_height_eq_ringKrullDim]

end Module.IsCohenMacaulay

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- Let `A` be a two-dimensional Noetherian integrally closed local domain, `B` a finite
torsion-free `A`-algebra and `𝔮` a maximal ideal of `B` such that `B_𝔮` is a normal domain. Every
pair generating the maximal ideal of `A` maps to a regular sequence on `B_𝔮`. Here `B` need not
be local, and `B_𝔮` need not be finite over `A`. -/
theorem isRegular_pair_localization_of_isIntegrallyClosed (hdim : ringKrullDim A = 2)
    (𝔮 : Ideal B) [𝔮.IsMaximal] [IsDomain (Localization.AtPrime 𝔮)]
    [IsIntegrallyClosed (Localization.AtPrime 𝔮)] {x y : A} (hxy : span {x, y} = maximalIdeal A) :
    IsRegular (Localization.AtPrime 𝔮)
      [algebraMap A (Localization.AtPrime 𝔮) x, algebraMap A (Localization.AtPrime 𝔮) y] := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  -- Going down gives `B_𝔮` the dimension two of `A`, so the normal domain `B_𝔮` is
  -- Cohen–Macaulay.
  have : Ring.KrullDimLE 2 (Localization.AtPrime 𝔮) := by
    rw [Ring.krullDimLE_iff, Ideal.ringKrullDim_localization_atPrime_eq_height_under A,
      eq_maximalIdeal (inferInstance : (𝔮.under A).IsMaximal),
      maximalIdeal_height_eq_ringKrullDim, hdim]
    rfl
  exact Module.IsCohenMacaulay.isRegular_map_algebraMap_localization
    Module.isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two (rs := [x, y])
    (by rw [ofList_cons, ofList_singleton, ← span_insert, hxy]) (by rw [hdim]; rfl)

end TauCeti
