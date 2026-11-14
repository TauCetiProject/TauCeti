/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Algebra.CharP.Frobenius.Flat
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Flat.ProjectiveDimension
import TauCeti.RingTheory.KrullDimension.PowerSeries
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.IsPRadical
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Descent
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Kunz's characterization of regular rings via flatness of Frobenius

Let `R` be a Noetherian ring of prime characteristic `p`. Kunz's theorem states that `R` is regular
if and only if its absolute Frobenius endomorphism `a ↦ a ^ p` is flat
(`TauCeti.isRegularRing_iff_flat_frobenius`). The forward implication from regularity to flatness of
Frobenius is proved in `TauCeti.RingTheory.RegularLocalRing.Frobenius`; this file establishes the
converse (`TauCeti.IsRegularLocalRing.of_flat_frobenius` and
`TauCeti.IsRegularRing.of_flat_frobenius`), following the perfection argument of Bhatt and Scholze
(Corollary 11.35).

For a Noetherian local ring `(R, 𝔪)` of characteristic `p` with flat Frobenius, pass to the `𝔪`-adic
completion `R̂`. Flatness of Frobenius persists on `R̂` (`TauCeti.AdicCompletion.flat_frobenius`),
making `R̂` reduced and its colimit perfection `R̂_perf = PerfectClosure R̂ p` faithfully flat over
`R̂` (`Module.FaithfullyFlat.of_isPerfectClosure_of_flat_frobenius`). By Cohen's structure theorem
for complete local `𝔽_p`-algebras (`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), `R̂` is a
quotient of a formal power series ring `P₀ = κ⟦X₁, …, X_e⟧` over its residue field `κ` in
`e = spanFinrank 𝔪_R̂` variables, which is regular of Krull dimension `e`. Passing to colimit
perfections produces a surjective homomorphism `(P₀)_perf →+* R̂_perf` between perfect rings
(`PerfectRing.lift` and `IsPRadical.surjective_of_surjective_comp`), along which Tor independence of
radical quotients of perfect rings bounds global dimension: every `R̂_perf`-module has projective
dimension at most `e + 1`
(`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective_of_perfectRing`). Faithfully
flat descent along `R̂ → R̂_perf` (`ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`) then
bounds the projective dimension of the residue field of `R̂` by `e + 1`, so `R̂` is regular by
Serre's theorem (`TauCeti.IsRegularLocalRing.of_hasProjectiveDimensionLE`), and regularity descends
from `R̂` to `R` along the flat local completion map
(`TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom`). For a general Noetherian ring `R`, Frobenius
commutes with localization at every prime ideal, reducing the global converse to the local one.

Both hypotheses beyond `[ExpChar R p]` are necessary for the converse:
* Primality of `p` (`[Fact p.Prime]`) cannot be relaxed to general exponential characteristic: in
  characteristic zero (`p = 1`), `frobenius R 1` is the identity and hence always flat, whereas
  `ℚ[X] ⧸ (X ^ 2)` is a Noetherian local ring that is not regular.
* `[IsNoetherianRing R]` is part of `IsRegularLocalRing` and `IsRegularRing`, and does not follow
  from flatness of Frobenius: the colimit perfection `PerfectClosure (ZMod p)⟦X⟧ p` is a local ring
  of characteristic `p` whose Frobenius is bijective (hence flat), yet its maximal ideal is not
  finitely generated so it is not Noetherian.

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of prime characteristic
  `p` with flat Frobenius is a regular local ring.
* `TauCeti.isRegularLocalRing_iff_flat_frobenius`: **Kunz's theorem (local form)**, a Noetherian
  local ring of prime characteristic `p` is regular if and only if its Frobenius endomorphism is
  flat.
* `TauCeti.IsRegularRing.of_flat_frobenius`: a Noetherian ring of prime characteristic `p` with flat
  Frobenius is a regular ring.
* `TauCeti.isRegularRing_iff_flat_frobenius`: **Kunz's theorem**, a Noetherian ring of prime
  characteristic `p` is regular if and only if its Frobenius endomorphism is flat.

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784, Theorem 2.1.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Corollary 11.35.
* [Stacks Project, Lemma 51.17.6](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open CategoryTheory IsLocalRing TensorProduct

universe u

namespace TauCeti

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [ExpChar R p]

/-- **Kunz's theorem, local converse.** If `R` is a Noetherian local ring of prime characteristic
`p` whose Frobenius endomorphism is flat, then `R` is a regular local ring (Bhatt and Scholze,
Corollary 11.35). -/
theorem IsRegularLocalRing.of_flat_frobenius [IsLocalRing R] [IsNoetherianRing R]
    (hF : (frobenius R p).Flat) : IsRegularLocalRing R := by
  have hp : p.Prime := Fact.out
  -- Pass to the completion `R̂` at the maximal ideal; flatness of Frobenius persists, and
  -- regularity descends back along the flat local map `R → R̂`.
  let Rhat := AdicCompletion (maximalIdeal R) R
  have hFhat : (frobenius Rhat p).Flat := TauCeti.AdicCompletion.flat_frobenius p hF
  have : IsReduced Rhat := isReduced_of_flat_frobenius p hp.one_lt hFhat
  have : CharP Rhat p := (expChar_prime_iff (R := Rhat) hp).1 inferInstance
  let : Algebra (ZMod p) Rhat := (ZMod.castHom dvd_rfl Rhat).toAlgebra
  -- By Cohen's structure theorem, `R̂` is a quotient of `P₀ = κ⟦X₁, …, X_e⟧`, which is regular of
  -- Krull dimension `e = spanFinrank 𝔪_R̂`.
  set e := (maximalIdeal Rhat).spanFinrank
  obtain ⟨_, -, π, hπ, -, -⟩ :=
    exists_surjective_mvPowerSeries_spanFinrank (ZMod p) Rhat
      (maximalIdeal Rhat).fg_of_isNoetherianRing
  let P₀ := MvPowerSeries (Fin e) (ResidueField Rhat)
  have : CharP (ResidueField Rhat) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (residue Rhat), CharP.cast_eq_zero, map_zero]
  have : CharP P₀ p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast MvPowerSeries.C, CharP.cast_eq_zero, map_zero]
  have : ExpChar P₀ p := .prime hp
  have hd : ringKrullDim P₀ ≤ (e : ℕ) := by
    rw [MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- Lift `π : P₀ →+* R̂` to a surjection `φ` between colimit perfections; then every module over
  -- `PerfectClosure R̂ p` has projective dimension at most `e + 1`.
  let φ := PerfectRing.lift (PerfectClosure.of P₀ p) ((PerfectClosure.of Rhat p).comp π) p
  have hφ : Function.Surjective φ :=
    IsPRadical.surjective_of_surjective_comp (PerfectClosure.of P₀ p) (PerfectClosure.of Rhat p) p
      hπ (PerfectRing.lift_comp (PerfectClosure.of P₀ p) ((PerfectClosure.of Rhat p).comp π) p)
  algebraize [PerfectClosure.of Rhat p]
  let S := PerfectClosure Rhat p
  have : IsPerfectClosure (algebraMap Rhat S) p := PerfectClosure.isPRadical Rhat p
  have : Module.FaithfullyFlat Rhat S :=
    Module.FaithfullyFlat.of_isPerfectClosure_of_flat_frobenius p hFhat
  let M := Shrink.{u} (Rhat ⧸ maximalIdeal Rhat)
  have : Module.Finite Rhat M := Module.Finite.equiv (Shrink.linearEquiv Rhat _).symm
  have hSM : HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[Rhat] M)) (e + 1) :=
    IsPerfectClosure.hasProjectiveDimensionLE_succ_of_surjective_of_perfectRing
      (PerfectClosure.of P₀ p) p hd hφ (ModuleCat.of S (S ⊗[Rhat] M))
  -- Descend finite projective dimension of the residue field along `R̂ → PerfectClosure R̂ p`,
  -- conclude regularity of `R̂` by Serre's theorem, and descend to `R`.
  have : HasProjectiveDimensionLE (ModuleCat.of Rhat M) (e + 1) :=
    ModuleCat.hasProjectiveDimensionLT_of_tensorProduct S M hSM
  have : IsRegularLocalRing Rhat := IsRegularLocalRing.of_hasProjectiveDimensionLE (e + 1)
  exact IsRegularLocalRing.of_flat_of_isLocalHom (S := Rhat)

/-- **Kunz's theorem (local form).** A Noetherian local ring of prime characteristic `p` is regular
if and only if its Frobenius endomorphism is flat. -/
theorem isRegularLocalRing_iff_flat_frobenius [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularLocalRing.flat_frobenius p, IsRegularLocalRing.of_flat_frobenius p⟩

/-- **Kunz's theorem, converse.** A Noetherian ring of prime characteristic `p` whose Frobenius
endomorphism is flat is a regular ring (Stacks, Lemma 51.17.6 (0EC0)). -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius [IsNoetherianRing R] (hF : (frobenius R p).Flat) :
    IsRegularRing R := by
  have hp : p.Prime := Fact.out
  have : CharP R p := (expChar_prime_iff (R := R) hp).1 inferInstance
  refine isRegularRing_iff.2 fun J hJ ↦ ?_
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  have : ExpChar (Localization.AtPrime J) p := .prime hp
  have hJ' : J = J.comap (frobenius R p) :=
    Ideal.ext fun a ↦ (hJ.pow_mem_iff_mem p hp.pos).symm
  have heq : Localization.localRingHom J J (frobenius R p) hJ' =
      frobenius (Localization.AtPrime J) p :=
    IsLocalization.ringHom_ext J.primeCompl <| RingHom.ext fun a ↦ by
      simp [Localization.localRingHom_to_map, frobenius_def]
  exact IsRegularLocalRing.of_flat_frobenius p (heq ▸ hF.localRingHom J J hJ')

/-- **Kunz's theorem.** A Noetherian ring of prime characteristic `p` is regular if and only if its
Frobenius endomorphism is flat (Stacks, Lemma 51.17.6 (0EC0)). -/
@[stacks 0EC0]
theorem isRegularRing_iff_flat_frobenius [IsNoetherianRing R] :
    IsRegularRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularRing.flat_frobenius p, IsRegularRing.of_flat_frobenius p⟩

end TauCeti
