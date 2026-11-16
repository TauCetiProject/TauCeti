/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Algebra.CharP.Frobenius.Localization
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Flat.ProjectiveDimension
import TauCeti.RingTheory.KrullDimension.PowerSeries
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Kunz's theorem: flatness of Frobenius characterizes regularity

Let `R` be a Noetherian ring of prime characteristic `p` (more generally, exponential
characteristic `p > 1`). Kunz's theorem states that `R` is regular if and only if its Frobenius
endomorphism `a ↦ a ^ p` is flat (`TauCeti.isRegularRing_iff_flat_frobenius`). The forward
implication is proved in `TauCeti.RingTheory.RegularLocalRing.Frobenius`; this file establishes
the converse (`TauCeti.IsRegularRing.of_flat_frobenius`) and assembles the full characterization.

Following Bhatt and Scholze (Corollary 11.35), we reduce to a complete Noetherian local ring
`(A, 𝔪)`: for a general Noetherian ring `R`, regularity is tested at every localization `R_𝔭`,
where Frobenius stays flat because `𝔭` is its own Frobenius preimage; for a Noetherian local ring,
passing to the `𝔪`-adic completion `R̂` preserves regularity
(`TauCeti.AdicCompletion.isRegularLocalRing_iff`) and flatness of Frobenius
(`TauCeti.AdicCompletion.flat_frobenius`).

By the Cohen structure theorem (`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), the
complete local ring `A` of characteristic `p` is a quotient of a formal power series ring
`S = k⟦X₁, …, Xₑ⟧` over its residue field `k`, where `e = spanFinrank 𝔪`. The ring `S` is a
regular local ring of Krull dimension `e` (`MvPowerSeries.isRegularLocalRing`,
`MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`). Passing to colimit perfections gives
a surjection `S_perf → A_perf` (`PerfectRing.lift_surjective_iff`), so every `A_perf`-module has
projective dimension at most `e + 1` by
`IsPRadical.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`. Since the
Frobenius of `A` is flat, `A → A_perf` is faithfully flat
(`RingHom.FaithfullyFlat.of_isPerfectClosure`), so the projective dimension bound `e + 1` descends
from `A_perf ⊗[A] (A ⧸ 𝔪)` to the residue field `A ⧸ 𝔪`
(`ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`), and Serre's theorem
(`TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`) concludes that `A` is regular.

The hypothesis `1 < p` is necessary: in characteristic zero (`p = 1`), Frobenius is the identity,
which is flat on every ring, regular or not. Noetherianity is likewise part of regularity.

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of exponential
  characteristic `p > 1` with flat Frobenius is regular.
* `TauCeti.IsRegularRing.of_flat_frobenius`: a Noetherian ring of exponential characteristic
  `p > 1` with flat Frobenius is regular.
* `TauCeti.isRegularLocalRing_iff_flat_frobenius`: **Kunz's theorem for local rings**, a
  Noetherian local ring of exponential characteristic `p > 1` is regular if and only if its
  Frobenius endomorphism is flat.
* `TauCeti.isRegularRing_iff_flat_frobenius`: **Kunz's theorem**, a Noetherian ring of
  exponential characteristic `p > 1` is regular if and only if its Frobenius endomorphism is flat.

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Corollary 11.35.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace TauCeti

/-- **Converse of Kunz's theorem for complete local rings.** A complete Noetherian local ring of
prime characteristic `p` with flat Frobenius is regular. -/
private theorem isRegularLocalRing_of_flat_frobenius_of_isAdicComplete {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (p : ℕ)
    [Fact p.Prime] [CharP A p] (hF : (frobenius A p).Flat) : IsRegularLocalRing A := by
  have hp : p.Prime := Fact.out
  have : ExpChar A p := .prime hp
  let _ : Algebra (ZMod p) A := ZMod.algebra A p
  -- Present `A` as a quotient of `S = k⟦X₁, …, Xₑ⟧` via the Cohen structure theorem.
  set e := (maximalIdeal A).spanFinrank
  obtain ⟨_, _, φ, hφ, _, _⟩ :=
    exists_surjective_mvPowerSeries_spanFinrank (ZMod p) A (maximalIdeal A).fg_of_isNoetherianRing
  let S := MvPowerSeries (Fin e) (ResidueField A)
  have : CharP (ResidueField A) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (residue A), CharP.cast_eq_zero, map_zero]
  have : CharP S p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast MvPowerSeries.C, CharP.cast_eq_zero, map_zero]
  have hdimS : ringKrullDim S ≤ e := by
    rw [MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- Lift `φ : S →+* A` to a surjection between colimit perfections; Proposition 11.31 of
  -- Bhatt and Scholze gives global dimension `≤ e + 1` over `PerfectClosure A p`.
  let ψ : PerfectClosure S p →+* PerfectClosure A p :=
    PerfectRing.lift (PerfectClosure.of S p) ((PerfectClosure.of A p).comp φ) p
  have hψ : Function.Surjective ψ := (PerfectRing.lift_surjective_iff ..).2 fun z ↦ by
    obtain ⟨n, y', hy'⟩ := IsPRadical.pow_mem (PerfectClosure.of A p) p z
    obtain ⟨y, rfl⟩ := hφ y'
    exact ⟨n, y, hy'⟩
  have hpdPerf : ∀ M : ModuleCat.{u} (PerfectClosure A p), HasProjectiveDimensionLE M (e + 1) :=
    IsPRadical.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
      (PerfectClosure.of S p) p hdimS ψ hψ
  -- Faithfully flat descent along `A → PerfectClosure A p` bounds `pd_A (A ⧸ 𝔪)`.
  have hff : (PerfectClosure.of A p).FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_isPerfectClosure (PerfectClosure.of A p) p hF
  algebraize [PerfectClosure.of A p]
  have : Module.FaithfullyFlat A (PerfectClosure A p) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  have hpdRes : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) (e + 1) :=
    ModuleCat.hasProjectiveDimensionLT_of_tensorProduct (PerfectClosure A p) (A ⧸ maximalIdeal A)
      (hpdPerf _)
  have : HasProjectiveDimensionLE (ModuleCat.of A (Shrink.{u} (A ⧸ maximalIdeal A))) (e + 1) :=
    hasProjectiveDimensionLT_of_iso (Shrink.linearEquiv.{u} A (A ⧸ maximalIdeal A)).toModuleIso.symm
      (e + 2)
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE (e + 1)

/-- **Converse of Kunz's theorem for local rings.** A Noetherian local ring of exponential
characteristic `p > 1` with flat Frobenius is regular. -/
theorem IsRegularLocalRing.of_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p) (h : (frobenius R p).Flat) :
    IsRegularLocalRing R := by
  obtain _ | ⟨hp'⟩ := ‹ExpChar R p›
  · omega
  have : Fact p.Prime := ⟨hp'⟩
  have hF : (frobenius (AdicCompletion (maximalIdeal R) R) p).Flat :=
    AdicCompletion.flat_frobenius p h
  have : CharP (AdicCompletion (maximalIdeal R) R) p :=
    (expChar_prime_iff (R := AdicCompletion (maximalIdeal R) R) hp').1 inferInstance
  exact AdicCompletion.isRegularLocalRing_iff.1
    (isRegularLocalRing_of_flat_frobenius_of_isAdicComplete p hF)

/-- **Converse of Kunz's theorem.** A Noetherian ring of exponential characteristic `p > 1` whose
Frobenius endomorphism is flat is a regular ring. Stacks, Lemma 51.17.6 (0EC0), the implication
from flatness to regularity. -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [ExpChar R p] (hp : 1 < p) (h : (frobenius R p).Flat) : IsRegularRing R := by
  obtain _ | ⟨hp'⟩ := ‹ExpChar R p›
  · omega
  refine isRegularRing_iff.2 fun J hJ ↦ ?_
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hp').2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  have : ExpChar (Localization.AtPrime J) p := .prime hp'
  exact IsRegularLocalRing.of_flat_frobenius p hp <|
    frobenius_localization_atPrime_eq_localRingHom p J ▸ RingHom.Flat.localRingHom h J J _

/-- **Kunz's theorem for local rings.** A Noetherian local ring of exponential characteristic
`p > 1` is regular if and only if its Frobenius endomorphism is flat. -/
theorem isRegularLocalRing_iff_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p) :
    IsRegularLocalRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularLocalRing.flat_frobenius p, IsRegularLocalRing.of_flat_frobenius p hp⟩

/-- **Kunz's theorem.** A Noetherian ring of exponential characteristic `p > 1` is regular if and
only if its Frobenius endomorphism is flat. Stacks, Lemma 51.17.6 (0EC0). -/
@[stacks 0EC0]
theorem isRegularRing_iff_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [ExpChar R p] (hp : 1 < p) :
    IsRegularRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularRing.flat_frobenius p, IsRegularRing.of_flat_frobenius p hp⟩

end TauCeti
