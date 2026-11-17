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
import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Algebra.CharP.Frobenius.Flat
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Flat.ProjectiveDimension
import TauCeti.RingTheory.KrullDimension.PowerSeries
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Descent
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Kunz's theorem: converse via perfection and full characterization

Let `R` be a Noetherian ring of prime characteristic `p` (equivalently, exponential characteristic
`p > 1`). Kunz's theorem states that `R` is regular if and only if its absolute Frobenius
endomorphism `x ↦ x ^ p` is flat (`TauCeti.isRegularRing_iff_flat_frobenius`). The forward
implication is proved in `TauCeti.RingTheory.RegularLocalRing.Frobenius`; this file proves the
converse (`TauCeti.IsRegularRing.of_flat_frobenius`) by the perfection argument of Bhatt and
Scholze.

After localizing at each prime ideal (using `TauCeti.flat_frobenius_of_isLocalization`) and passing
to the maximal-ideal completion (using `TauCeti.AdicCompletion.flat_frobenius` and descent of
regularity along flat local homomorphisms, `TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom`),
we reduce to a complete Noetherian local ring `R` of prime characteristic `p` with flat Frobenius.
By the Cohen structure theorem (`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), `R` admits
a surjection from a formal power series ring `P₀ = k⟦X₁, …, Xₑ⟧` over its residue field `k`,
which is regular of Krull dimension `e` (`TauCeti.MvPowerSeries.isRegularLocalRing` and
`MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`). Passing to perfect closures yields a
surjection `P₀^perf ↠ R^perf` (`PerfectRing.surjective_lift_comp`), so every `R^perf`-module has
projective dimension at most `e + 1`
(`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`). Since Frobenius
of `R` is flat, `R → R^perf` is faithfully flat (`RingHom.FaithfullyFlat.of_isPerfectClosure`),
so the projective dimension bound descends to the residue field `R ⧸ 𝔪`
(`ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`), and Serre's criterion
(`TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`) concludes that `R` is regular.

The hypothesis `1 < p` cannot be dropped: in characteristic zero (`p = 1`) Frobenius is the
identity map and is flat on every ring. Noetherianity is likewise necessary, as a non-Noetherian
perfect ring has bijective (hence flat) Frobenius.

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of exponential
  characteristic `p > 1` with flat Frobenius is a regular local ring.
* `TauCeti.isRegularLocalRing_iff_flat_frobenius`: a Noetherian local ring of exponential
  characteristic `p > 1` is regular iff its Frobenius is flat.
* `TauCeti.IsRegularRing.of_flat_frobenius`: **converse of Kunz's theorem**, a Noetherian ring of
  exponential characteristic `p > 1` with flat Frobenius is regular.
* `TauCeti.isRegularRing_iff_flat_frobenius`: **Kunz's theorem**, a Noetherian ring of exponential
  characteristic `p > 1` is regular iff its Frobenius is flat.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Corollary 11.35.
* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

namespace TauCeti

universe u

/-- Complete local case of the converse of Kunz's theorem: Cohen's structure theorem presents `R`
as a quotient of `k⟦X₁, …, Xₑ⟧`, whose perfection has global dimension at most `e + 1`; this
passes to `R^perf` and descends along the faithfully flat map `R → R^perf` to bound the projective
dimension of `R ⧸ 𝔪`. -/
private theorem IsRegularLocalRing.of_flat_frobenius_of_isAdicComplete {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (hF : (frobenius R p).Flat) : IsRegularLocalRing R := by
  have hp : p.Prime := Fact.out
  have : ExpChar R p := .prime hp
  set e := (maximalIdeal R).spanFinrank
  let P₀ := MvPowerSeries (Fin e) (ResidueField R)
  obtain ⟨φ, hφ⟩ : ∃ φ : P₀ →+* R, Function.Surjective φ := by
    let : Algebra (ZMod p) R := ZMod.algebra R p
    obtain ⟨_, _, φ, hφ, -, -⟩ :=
      exists_surjective_mvPowerSeries_spanFinrank (ZMod p) R (maximalIdeal R).fg_of_isNoetherianRing
    exact ⟨φ, hφ⟩
  have : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (residue R), CharP.cast_eq_zero, map_zero]
  have : CharP P₀ p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast MvPowerSeries.C, CharP.cast_eq_zero, map_zero]
  have : ExpChar P₀ p := .prime hp
  have hdim : ringKrullDim P₀ ≤ e := by
    rw [MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field (ResidueField R), zero_add, Nat.card_fin]
  -- Pass to perfections: `P₀^perf → R^perf` is surjective, so every `R^perf`-module has
  -- projective dimension at most `e + 1`.
  let L := PerfectClosure R p
  let ψ : PerfectClosure P₀ p →+* L :=
    PerfectRing.lift (PerfectClosure.of P₀ p) ((PerfectClosure.of R p).comp φ) p
  have hψ : Function.Surjective ψ := PerfectRing.surjective_lift_comp _ _ p hφ
  -- Faithfully flat descent along `R → R^perf` bounds the projective dimension of `R ⧸ 𝔪`.
  let : Algebra R L := (PerfectClosure.of R p).toAlgebra
  have : Module.FaithfullyFlat R L :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (RingHom.FaithfullyFlat.of_isPerfectClosure (PerfectClosure.of R p) p hF)
  have hL : HasProjectiveDimensionLE (ModuleCat.of L (L ⊗[R] (R ⧸ maximalIdeal R))) (e + 1) :=
    IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
      (PerfectClosure.of P₀ p) p hdim ψ hψ _
  have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ maximalIdeal R)) (e + 1) :=
    ModuleCat.hasProjectiveDimensionLT_of_tensorProduct L (R ⧸ maximalIdeal R) hL
  have : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))) (e + 1) :=
    hasProjectiveDimensionLT_of_iso (Shrink.linearEquiv.{u} R (R ⧸ maximalIdeal R)).toModuleIso.symm
      (e + 2)
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE.{u, u} (e + 1)

/-- **Converse of Kunz's theorem (local form).** A Noetherian local ring of exponential
characteristic `p > 1` whose Frobenius endomorphism is flat is a regular local ring
(Bhatt–Scholze, Corollary 11.35; Stacks, Lemma 51.17.6, tag 0EC0). -/
theorem IsRegularLocalRing.of_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p) (hF : (frobenius R p).Flat) :
    IsRegularLocalRing R := by
  have hprime : p.Prime := (expChar_is_prime_or_one R p).resolve_right hp.ne'
  have : Fact p.Prime := ⟨hprime⟩
  let R' := AdicCompletion (maximalIdeal R) R
  have hF' : (frobenius R' p).Flat := AdicCompletion.flat_frobenius p hF
  have : CharP R' p := (expChar_prime_iff (R := R') hprime).mp inferInstance
  have : IsRegularLocalRing R' := IsRegularLocalRing.of_flat_frobenius_of_isAdicComplete p hF'
  exact IsRegularLocalRing.of_flat_of_isLocalHom (S := R')

/-- **Kunz's theorem (local form).** A Noetherian local ring of exponential characteristic `p > 1`
is regular if and only if its Frobenius endomorphism is flat. -/
theorem isRegularLocalRing_iff_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p) :
    IsRegularLocalRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularLocalRing.flat_frobenius p, IsRegularLocalRing.of_flat_frobenius p hp⟩

/-- **Converse of Kunz's theorem.** A Noetherian ring of exponential characteristic `p > 1` whose
Frobenius endomorphism is flat is regular (Bhatt–Scholze, Corollary 11.35; Stacks, Lemma 51.17.6,
tag 0EC0). -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [ExpChar R p] (hp : 1 < p) (hF : (frobenius R p).Flat) : IsRegularRing R := by
  have hprime : p.Prime := (expChar_is_prime_or_one R p).resolve_right hp.ne'
  have : CharP R p := (expChar_prime_iff (R := R) hprime).mp inferInstance
  refine isRegularRing_iff.mpr fun J hJ ↦ ?_
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hprime).2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  have : ExpChar (Localization.AtPrime J) p := .prime hprime
  exact IsRegularLocalRing.of_flat_frobenius p hp
    (flat_frobenius_of_isLocalization p J.primeCompl hF)

/-- **Kunz's theorem.** A Noetherian ring of exponential characteristic `p > 1` is regular if and
only if its Frobenius endomorphism is flat (Kunz 1969; Stacks, Lemma 51.17.6, tag 0EC0). -/
@[stacks 0EC0]
theorem isRegularRing_iff_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [ExpChar R p] (hp : 1 < p) : IsRegularRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularRing.flat_frobenius p, IsRegularRing.of_flat_frobenius p hp⟩

end TauCeti
