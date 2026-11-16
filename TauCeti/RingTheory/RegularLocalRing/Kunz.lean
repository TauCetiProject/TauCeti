/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Flat.ProjectiveDimension
import TauCeti.RingTheory.KrullDimension.PowerSeries
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RingHom.Flat

/-!
# Kunz's theorem: rings with flat Frobenius are regular

Let `R` be a Noetherian ring of prime characteristic `p`. By Kunz's theorem, `R` is regular if and
only if its absolute Frobenius endomorphism `R → R`, `a ↦ a ^ p`, is flat
(`TauCeti.isRegularRing_iff_flat_frobenius`).

The forward implication (`TauCeti.IsRegularRing.flat_frobenius`) is proved in
`TauCeti.RingTheory.RegularLocalRing.Frobenius`. This file proves the converse
(`TauCeti.IsRegularRing.of_flat_frobenius`) by the perfection argument of Bhatt and Scholze:

1. Regularity is tested at localizations at prime ideals, and flatness of Frobenius localizes
   because `J.comap (frobenius R p) = J` for every prime `J`.
2. For a Noetherian local ring `(R, 𝔪)`, passing to the `𝔪`-adic completion `R̂` preserves flatness
   of Frobenius (`TauCeti.AdicCompletion.flat_frobenius`) and reflects regularity
   (`TauCeti.AdicCompletion.isRegularLocalRing_iff`), reducing to the case where `R` is complete.
3. By Cohen's structure theorem (`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), a complete
   Noetherian local ring `R` of prime characteristic `p` is a quotient of a formal power series
   ring `P₀ = κ⟦X₁, …, X_d⟧` over its residue field `κ`. The ring `P₀` is regular of Krull
   dimension `d` (`TauCeti.MvPowerSeries.isRegularLocalRing`,
   `MvPowerSeries.ringKrullDim_of_isNoetherianRing`).
4. Lifting the surjection `P₀ → R` to perfections gives a surjection `(P₀)_perf → R_perf`
   (`PerfectRing.lift_comp_surjective`), so every `R_perf`-module has projective dimension at most
   `d + 1` (`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`).
5. Since Frobenius of `R` is flat, `R → R_perf` is faithfully flat
   (`RingHom.FaithfullyFlat.of_isPerfectClosure`). Faithfully flat descent of projective dimension
   (`ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`) therefore yields `pd_R (R ⧸ 𝔪) ≤ d + 1`,
   and Serre's homological criterion (`TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`)
   concludes that `R` is regular.

The prime characteristic hypothesis `[Fact p.Prime]` is necessary for the converse: in
characteristic zero (`p = 1`), Frobenius is the identity, hence flat on every ring.

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of prime characteristic
  with flat Frobenius is regular.
* `TauCeti.isRegularLocalRing_iff_flat_frobenius`: local form of Kunz's characterization.
* `TauCeti.IsRegularRing.of_flat_frobenius`: a Noetherian ring of prime characteristic with flat
  Frobenius is regular.
* `TauCeti.isRegularRing_iff_flat_frobenius`: **Kunz's theorem**, a Noetherian ring of prime
  characteristic is regular if and only if its Frobenius endomorphism is flat.

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Corollary 11.35.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u

namespace TauCeti

/-- Complete local case of the converse of Kunz's theorem, proved via Cohen's structure theorem
and the finite global dimension of the perfection of `R`. -/
private theorem IsRegularLocalRing.of_flat_frobenius_of_isAdicComplete {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [ExpChar R p] [Fact p.Prime] (h : (frobenius R p).Flat) :
    IsRegularLocalRing R := by
  have hp : p.Prime := Fact.out
  have : CharP R p := (expChar_prime_iff (R := R) hp).1 inferInstance
  let : Algebra (ZMod p) R := (ZMod.castHom dvd_rfl R).toAlgebra
  -- Present `R` as a quotient of `P₀ = κ⟦X₁, …, X_d⟧`, which is regular of Krull dimension `d`.
  obtain ⟨_, _, φ, hφ, -, -⟩ :=
    exists_surjective_mvPowerSeries_spanFinrank (ZMod p) R (maximalIdeal R).fg_of_isNoetherianRing
  let d := (maximalIdeal R).spanFinrank
  let P₀ := MvPowerSeries (Fin d) (ResidueField R)
  have : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (residue R), CharP.cast_eq_zero, map_zero]
  have : CharP P₀ p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (MvPowerSeries.C (σ := Fin d) (R := ResidueField R)),
      CharP.cast_eq_zero, map_zero]
  have hdim : ringKrullDim P₀ ≤ d := by
    rw [MvPowerSeries.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Field.toIsField (ResidueField R)), zero_add, Nat.card_fin]
  -- Lift `φ : P₀ →+* R` to a surjection `(P₀)_perf →+* R_perf`.
  let S := PerfectClosure R p
  let ψ : PerfectClosure P₀ p →+* S :=
    PerfectRing.lift (PerfectClosure.of P₀ p) ((PerfectClosure.of R p).comp φ) p
  have hψ : Function.Surjective ψ :=
    PerfectRing.lift_comp_surjective (PerfectClosure.of P₀ p) (PerfectClosure.of R p) p hφ
  -- Every `S`-module has projective dimension at most `d + 1`, and `R → S` is faithfully flat.
  algebraize [PerfectClosure.of R p]
  have : Module.FaithfullyFlat R S :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := R) (S := S)).mp
      (RingHom.FaithfullyFlat.of_isPerfectClosure (PerfectClosure.of R p) p h)
  have hS : HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] (R ⧸ maximalIdeal R))) (d + 1) :=
    IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
      (PerfectClosure.of P₀ p) p hdim hψ _
  -- Faithfully flat descent gives `pd_R (R ⧸ 𝔪) ≤ d + 1`, so `R` is regular by Serre's theorem.
  have hR : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ maximalIdeal R)) (d + 1) :=
    ModuleCat.hasProjectiveDimensionLT_of_tensorProduct S (R ⧸ maximalIdeal R) hS
  have : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))) (d + 1) :=
    hasProjectiveDimensionLT_of_iso (Shrink.linearEquiv.{u} R (R ⧸ maximalIdeal R)).symm.toModuleIso
      (d + 2)
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE (d + 1)

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] [Fact p.Prime]

/-- **Converse of Kunz's theorem (local form).** A Noetherian local ring of prime characteristic
`p` whose Frobenius endomorphism is flat is a regular local ring. -/
theorem IsRegularLocalRing.of_flat_frobenius [IsLocalRing R] [IsNoetherianRing R]
    (h : (frobenius R p).Flat) : IsRegularLocalRing R :=
  AdicCompletion.isRegularLocalRing_iff.mp <|
    IsRegularLocalRing.of_flat_frobenius_of_isAdicComplete p (AdicCompletion.flat_frobenius p h)

/-- **Kunz's theorem (local form).** A Noetherian local ring of prime characteristic `p` is regular
if and only if its Frobenius endomorphism is flat. -/
theorem isRegularLocalRing_iff_flat_frobenius [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularLocalRing.flat_frobenius p, IsRegularLocalRing.of_flat_frobenius p⟩

/-- **Converse of Kunz's theorem.** A Noetherian ring of prime characteristic `p` whose Frobenius
endomorphism is flat is regular. -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius [IsNoetherianRing R] (h : (frobenius R p).Flat) :
    IsRegularRing R := by
  have hp : p.Prime := Fact.out
  have : CharP R p := (expChar_prime_iff (R := R) hp).1 inferInstance
  refine isRegularRing_iff.mpr fun J hJ ↦ ?_
  have hQ : J.comap (frobenius R p) = J.comap (RingHom.id R) := by
    ext a
    exact hJ.pow_mem_iff_mem p hp.pos
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  have : ExpChar (Localization.AtPrime J) p := .prime hp
  have hcomp : Localization.localRingHom _ J (frobenius R p) rfl =
      (frobenius (Localization.AtPrime J) p).comp
        (Localization.localRingHom _ J (RingHom.id R) hQ) :=
    IsLocalization.ringHom_ext (J.comap (frobenius R p)).primeCompl <| RingHom.ext fun a ↦ by
      simp [Localization.localRingHom_to_map, frobenius_def]
  let f_loc := Localization.localRingHom (J.comap (frobenius R p)) J (RingHom.id R) hQ
  let g_loc := Localization.localRingHom J (J.comap (frobenius R p)) (RingHom.id R)
    (by simpa using hQ.symm)
  have hgf : g_loc.comp f_loc = RingHom.id _ :=
    IsLocalization.ringHom_ext (J.comap (frobenius R p)).primeCompl <| RingHom.ext fun a ↦ by
      simp [f_loc, g_loc, Localization.localRingHom_to_map]
  have hfg : f_loc.comp g_loc = RingHom.id _ :=
    IsLocalization.ringHom_ext J.primeCompl <| RingHom.ext fun a ↦ by
      simp [f_loc, g_loc, Localization.localRingHom_to_map]
  have hbij : Function.Bijective f_loc :=
    Function.bijective_iff_has_inverse.mpr
      ⟨g_loc, fun x ↦ RingHom.congr_fun hgf x, fun x ↦ RingHom.congr_fun hfg x⟩
  have hflat : (frobenius (Localization.AtPrime J) p).Flat := by
    rw [← RingHom.Flat.comp_iff_of_bijective_right hbij, ← hcomp]
    exact RingHom.Flat.localRingHom h J _ rfl
  exact IsRegularLocalRing.of_flat_frobenius p hflat

/-- **Kunz's theorem.** A Noetherian ring of prime characteristic `p` is regular if and only if
its Frobenius endomorphism is flat. -/
@[stacks 0EC0]
theorem isRegularRing_iff_flat_frobenius [IsNoetherianRing R] :
    IsRegularRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularRing.flat_frobenius p, IsRegularRing.of_flat_frobenius p⟩

end TauCeti
