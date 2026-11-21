/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.Algebra.CharP.Frobenius.Flat
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Flat.ProjectiveDimension
import TauCeti.RingTheory.KrullDimension.PowerSeries
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.IsPRadical
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Projective.Dimension
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Kunz's theorem: regularity from flatness of Frobenius

Let `R` be a Noetherian ring of prime characteristic `p`. Kunz's theorem characterizes regularity
of `R` by the flatness of its Frobenius endomorphism `a ↦ a ^ p`. The forward implication is
`TauCeti.IsRegularRing.flat_frobenius`; this file proves the converse via perfection, following
Bhatt and Scholze (Corollary 11.35), and packages the full equivalence.

For a Noetherian local ring `(R, 𝔪)` of prime characteristic `p` with flat Frobenius:

1. Pass to the `𝔪`-adic completion `R̂`, whose Frobenius is again flat
   (`TauCeti.AdicCompletion.flat_frobenius`) and which is regular if and only if `R` is
   (`TauCeti.AdicCompletion.isRegularLocalRing_iff`).
2. By Cohen's structure theorem (`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), `R̂` is a
   quotient of a multivariate power series ring `P₀ = κ⟦x₁, …, xₑ⟧` over its residue field `κ`.
   The ring `P₀` is a regular local ring (`TauCeti.MvPowerSeries.isRegularLocalRing`) of Krull
   dimension `e` (`MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`).
3. Passing to colimit perfections yields a surjection `P₀_perf → R̂_perf`
   (`PerfectRing.surjective_lift_comp`), so every `R̂_perf`-module has projective dimension at most
   `e + 1` (`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`).
4. Since Frobenius on `R̂` is flat, `R̂ → R̂_perf` is faithfully flat
   (`RingHom.FaithfullyFlat.of_isPerfectClosure`), so the projective dimension bound descends to
   the residue field of `R̂` (`ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`). By Serre's
   theorem (`TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`), `R̂` is regular.

The global converse (`TauCeti.IsRegularRing.of_flat_frobenius`) follows by localizing at every
prime ideal using `TauCeti.flat_frobenius_of_isLocalization`.

Prime characteristic is essential: in characteristic zero (`p = 1`), Frobenius is the identity and
is flat for every ring regardless of regularity.

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of prime characteristic
  `p` with flat Frobenius is regular.
* `TauCeti.IsRegularRing.of_flat_frobenius`: a Noetherian ring of prime characteristic `p` with
  flat Frobenius is regular.
* `TauCeti.isRegularLocalRing_iff_flat_frobenius` and `TauCeti.isRegularRing_iff_flat_frobenius`:
  **Kunz's theorem**, a Noetherian (local) ring of prime characteristic `p` is regular if and only
  if its Frobenius endomorphism is flat.

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Corollary 11.35.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open CategoryTheory IsLocalRing

namespace TauCeti

universe u

/-- **Converse of Kunz's theorem (local case).** A Noetherian local ring of prime characteristic
`p` whose Frobenius endomorphism is flat is a regular local ring. -/
theorem IsRegularLocalRing.of_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [ExpChar R p] (h : (frobenius R p).Flat) :
    IsRegularLocalRing R := by
  refine AdicCompletion.isRegularLocalRing_iff.mp ?_
  let R' := AdicCompletion (maximalIdeal R) R
  have hF : (frobenius R' p).Flat := AdicCompletion.flat_frobenius p h
  have hp : p.Prime := Fact.out
  have : CharP R' p := (expChar_prime_iff (R := R') hp).1 inferInstance
  -- Present `R'` as a quotient of a regular power series ring `P₀` by Cohen's structure theorem.
  let : Algebra (ZMod p) R' := (ZMod.castHom dvd_rfl R').toAlgebra
  obtain ⟨-, -, φ, hφ, -, -⟩ :=
    exists_surjective_mvPowerSeries_spanFinrank (ZMod p) R' (maximalIdeal R').fg_of_isNoetherianRing
  let e := (maximalIdeal R').spanFinrank
  let P₀ := _root_.MvPowerSeries (Fin e) (ResidueField R')
  have : CharP (ResidueField R') p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (residue R'), CharP.cast_eq_zero, map_zero]
  have : CharP P₀ p := charP_of_injective_ringHom _root_.MvPowerSeries.C_injective p
  have hdim : ringKrullDim P₀ ≤ e := by
    rw [_root_.MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]
  -- Lift `φ : P₀ →+* R'` to a surjection of colimit perfections to bound global dimension of
  -- `PerfectClosure R' p`.
  have := PerfectClosure.isPRadical P₀ p
  have := PerfectClosure.isPRadical R' p
  have hψ : Function.Surjective
      (PerfectRing.lift (PerfectClosure.of P₀ p) ((PerfectClosure.of R' p).comp φ) p) :=
    PerfectRing.surjective_lift_comp (PerfectClosure.of P₀ p) (PerfectClosure.of R' p) hφ p
  have hS : ∀ M : ModuleCat.{u} (PerfectClosure R' p), HasProjectiveDimensionLE M (e + 1) :=
    IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
      (PerfectClosure.of P₀ p) p hdim hψ
  -- Descend finite projective dimension of the residue field along the faithfully flat map
  -- `R' → PerfectClosure R' p`, then conclude regularity by Serre's theorem.
  have hff : (PerfectClosure.of R' p).FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_isPerfectClosure (PerfectClosure.of R' p) p hF
  algebraize [PerfectClosure.of R' p]
  have : Module.Finite R' (Shrink.{u} (R' ⧸ maximalIdeal R')) :=
    Module.Finite.equiv (Shrink.linearEquiv R' _).symm
  have : HasProjectiveDimensionLE (ModuleCat.of R' (Shrink.{u} (R' ⧸ maximalIdeal R'))) (e + 1) :=
    ModuleCat.hasProjectiveDimensionLT_of_tensorProduct (PerfectClosure R' p) _ (hS _)
  exact IsRegularLocalRing.of_hasProjectiveDimensionLE (e + 1)

/-- **Converse of Kunz's theorem (global case).** A Noetherian ring of prime characteristic `p`
whose Frobenius endomorphism is flat is a regular ring. -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [Fact p.Prime] [ExpChar R p] (h : (frobenius R p).Flat) : IsRegularRing R := by
  have hp : p.Prime := Fact.out
  have : CharP R p := (expChar_prime_iff (R := R) hp).1 inferInstance
  refine isRegularRing_iff.mpr fun q _ ↦ ?_
  have : CharP (Localization.AtPrime q) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  exact IsRegularLocalRing.of_flat_frobenius p (flat_frobenius_of_isLocalization p q.primeCompl h)

/-- **Kunz's theorem (local case).** A Noetherian local ring of prime characteristic `p` is regular
if and only if its Frobenius endomorphism is flat. -/
@[stacks 0EC0 "local case"]
theorem isRegularLocalRing_iff_flat_frobenius {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [ExpChar R p] :
    IsRegularLocalRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularLocalRing.flat_frobenius p, IsRegularLocalRing.of_flat_frobenius p⟩

/-- **Kunz's theorem.** A Noetherian ring of prime characteristic `p` is regular if and only if its
Frobenius endomorphism is flat. -/
@[stacks 0EC0]
theorem isRegularRing_iff_flat_frobenius {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ)
    [Fact p.Prime] [ExpChar R p] : IsRegularRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularRing.flat_frobenius p, IsRegularRing.of_flat_frobenius p⟩

end TauCeti
