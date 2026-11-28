/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
public import TauCeti.Topology.Algebra.Valued.WithVal
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Adic valuations and completions transport along an isomorphism of Dedekind domains

An isomorphism `e : R ≃+* R'` of Dedekind domains induces an isomorphism
`σ = IsFractionRing.ringEquivOfRingEquiv e : K ≃+* K'` of their fraction fields, and carries a
height one prime `v` of `R` to the height one prime of `R'` with underlying ideal
`Ideal.map e v.asIdeal`. This file proves that `σ` intertwines the two adic valuations: for a
height one prime `w` of `R'` with
`w.asIdeal = Ideal.map e v.asIdeal`,

```text
w.valuation K' (σ f) = v.valuation K f
```

for every `f : K`. Equivalently, `ord` at `w` of `σ f` is `ord` at `v` of `f`, which is the
algebraic content of the Galois descent `div (σ f) = σ_* (div f)` for divisors on a curve.

A field isomorphism `σ : K ≃+* K'` with this property is an isometry for the two adic
valuations, so it extends by continuity to an isomorphism of adic completions
`adicCompletionCongr v w σ hσ : K_v ≃+* K'_w`. For a Galois extension of global fields this is
how an automorphism permuting the places above a given place acts on their completions.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.intValuation_ringEquiv` and
  `IsDedekindDomain.HeightOneSpectrum.valuation_ringEquivOfRingEquiv`: the integer-valued and the
  fraction-field adic valuations transport.
* `IsDedekindDomain.HeightOneSpectrum.valuation_equivOfRingEquiv` and
  `IsDedekindDomain.HeightOneSpectrum.eq_equivOfRingEquiv_iff`: the transport `e v` of `v` carries
  the `v`-adic valuation along `σ`, and is the only height one prime of `R'` doing so.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`: the induced isomorphism of adic
  completions, with `adicCompletionCongr_algebraMap` (it extends `σ`),
  `continuous_adicCompletionCongr`, its universal property `eq_adicCompletionCongr_of_continuous`,
  its identity, composition, and inverse laws, `valued_adicCompletionCongr` (it preserves the
  valuations) and `adicCompletionCongr_mem_adicCompletionIntegers_iff` (so it carries the local
  integers onto the local integers), and `map_adicCompletionCongr_mem_range_map_subtype_iff` (so,
  applied entrywise, it carries `GL_n(𝒪_v)` onto `GL_n(𝒪'_w)`).

The ideal-level input this rests on — that `Ideal.map e` preserves divisibility and
factorisation multiplicities, and that Mathlib's `equivOfRingEquiv` is `Ideal.map e` on
underlying ideals — is not valuation theory and lives in
`TauCeti/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Implementation notes

The hypothesis on the two primes is stated as the equation `w.asIdeal = Ideal.map e v.asIdeal`
rather than as `w = equivOfRingEquiv e v`, so that a call site holding some independently
constructed `w` — a place of a curve, say — does not first have to identify it with the transport.
`asIdeal_equivOfRingEquiv` discharges the hypothesis whenever `w` *is* that transport, so nothing
is lost in the other direction.

`valuation_ringEquivOfRingEquiv_algebraMap` is `private`: it is the `algebraMap` special case
used to reduce the general statement to a quotient of two elements of `R`, and the reusable
restriction result is `intValuation_ringEquiv`.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit
`513e83879e2f`, `projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`: the proofs of
`intValuation_map_ringEquiv`, `valuation_map_ringEquiv_algebraMap` and `valuation_map_ringEquiv`
are that file's, with the vocabulary adapted to this repository's interfaces. The ideal-level
lemmas adapted from the same source are attributed in
`TauCeti/RingTheory/DedekindDomain/Ideal/Basic.lean`. The completion section is not from that
source; it follows the pattern of `adicCompletionExtension` in
`TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, II.3 (the Galois action on divisors).
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

section DedekindDomain

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/-- **The integer adic valuation transports along a ring isomorphism.** If the height one prime `w`
of `R'` is the image of the height one prime `v` of `R` under `e`, then the `w`-adic valuation of
`e r` is the `v`-adic valuation of `r`. -/
theorem intValuation_ringEquiv (e : R ≃+* R') {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.intValuation (e r) = v.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have her : e r ≠ 0 := by simp [hr]
    have hspan : Ideal.span {e r} = Ideal.map e (Ideal.span {r}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [w.intValuation_if_neg her, v.intValuation_if_neg hr, hvw, hspan,
      Ideal.count_factors_map_of_ringEquiv e]

variable {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/-- The fraction-field adic valuation transports on the image of `R`, which is the building block
for `valuation_ringEquivOfRingEquiv`. -/
private theorem valuation_ringEquivOfRingEquiv_algebraMap (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e (algebraMap R K r)) =
      v.valuation K (algebraMap R K r) := by
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap e r, valuation_of_algebraMap,
    valuation_of_algebraMap]
  exact intValuation_ringEquiv e hvw r

/-- **The adic valuation of the fraction field transports along a ring isomorphism.** With
`σ = IsFractionRing.ringEquivOfRingEquiv e` the induced isomorphism of fraction fields, and `w` the
image of `v` under `e`, the `w`-adic valuation of `σ f` is the `v`-adic valuation of `f`. This is
the algebraic engine of divisor Galois descent. -/
theorem valuation_ringEquivOfRingEquiv (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (f : K) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e f) = v.valuation K f := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, Valuation.map_div, Valuation.map_div,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw a,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw b]

/-- **The image of a height one prime.** The transport `e v = equivOfRingEquiv e v` of a height
one prime `v` of `R` carries the `v`-adic valuation along the induced isomorphism
`σ = IsFractionRing.ringEquivOfRingEquiv e` of fraction fields: `|σ f|_{e v} = |f|_v`. -/
theorem valuation_equivOfRingEquiv (e : R ≃+* R') (v : HeightOneSpectrum R) (f : K) :
    (equivOfRingEquiv e v).valuation K' (IsFractionRing.ringEquivOfRingEquiv e f) =
      v.valuation K f :=
  valuation_ringEquivOfRingEquiv e (asIdeal_equivOfRingEquiv e v) f

/-- **The image of a height one prime is characterised by its valuation**: a height one prime `w`
of `R'` satisfies `|σ f|_w = |f|_v` for all `f : K`, where
`σ = IsFractionRing.ringEquivOfRingEquiv e`, exactly when it is the transport
`equivOfRingEquiv e v` of `v`. -/
theorem eq_equivOfRingEquiv_iff (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} :
    w = equivOfRingEquiv e v ↔
      ∀ f : K, w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e f) = v.valuation K f := by
  refine ⟨fun h ↦ h ▸ valuation_equivOfRingEquiv e v, fun hw ↦ ?_⟩
  refine valuation_injective K' (Valuation.ext fun y ↦ ?_)
  obtain ⟨f, rfl⟩ := (IsFractionRing.ringEquivOfRingEquiv e : K ≃+* K').surjective y
  rw [hw, valuation_equivOfRingEquiv]

end DedekindDomain

section Completion

open WithZero WithZeroTopology

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K'] (v : HeightOneSpectrum R) (w : HeightOneSpectrum R')

/-- The isomorphism of adic completions `K_v ≃+* K'_w` extending a field isomorphism
`σ : K ≃+* K'` that carries the `v`-adic valuation to the `w`-adic valuation: the transport
`Valuation.Completion.congr` read through `adicCompletion.equiv`. -/
noncomputable def adicCompletionCongr (σ : K ≃+* K')
    (hσ : ∀ x, w.valuation K' (σ x) = v.valuation K x) :
    v.adicCompletion K ≃+* w.adicCompletion K' :=
  (adicCompletion.equiv K v).trans <|
    (Valuation.Completion.congr σ hσ).trans
      (adicCompletion.equiv K' w).symm

variable {v w} {σ : K ≃+* K'} (hσ : ∀ x, w.valuation K' (σ x) = v.valuation K x)

/-- On the underlying uniform-space completions, `adicCompletionCongr` is
`Valuation.Completion.congr`. -/
@[simp]
theorem toCompletion_adicCompletionCongr (x : v.adicCompletion K) :
    (adicCompletionCongr v w σ hσ x).toCompletion =
      Valuation.Completion.congr σ hσ x.toCompletion := by
  rw [adicCompletionCongr, RingEquiv.trans_apply, RingEquiv.trans_apply,
    adicCompletion.equiv_apply, ← adicCompletion.equiv_apply, RingEquiv.apply_symm_apply]

/-- `adicCompletionCongr` extends `σ`. -/
@[simp]
theorem adicCompletionCongr_algebraMap (x : K) :
    adicCompletionCongr v w σ hσ (algebraMap K (v.adicCompletion K) x) =
      algebraMap K' (w.adicCompletion K') (σ x) := by
  apply adicCompletion.ext
  simp [algebraMap_adicCompletion]

/-- `adicCompletionCongr` is continuous. -/
theorem continuous_adicCompletionCongr : Continuous (adicCompletionCongr v w σ hσ) :=
  (adicCompletion.continuous_ofCompletion K' w).comp
    ((Valuation.Completion.continuous_congr hσ).comp
      (adicCompletion.continuous_toCompletion K v))

/-- `adicCompletionCongr` is the only continuous ring homomorphism `K_v →+* K'_w` extending `σ`. -/
theorem eq_adicCompletionCongr_of_continuous {f : v.adicCompletion K →+* w.adicCompletion K'}
    (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K _ x) = algebraMap K' (w.adicCompletion K') (σ x)) :
    f = (adicCompletionCongr v w σ hσ).toRingHom :=
  DFunLike.coe_injective <| (v.denseRange_algebraMap K).equalizer hf
    (continuous_adicCompletionCongr hσ) (funext fun x ↦ by
      rw [Function.comp_apply, Function.comp_apply, hfK x, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adicCompletionCongr_algebraMap])

/-- `adicCompletionCongr` for the identity is the identity. -/
@[simp]
theorem adicCompletionCongr_one :
    adicCompletionCongr v v (1 : K ≃+* K) (fun _ ↦ rfl) =
      RingEquiv.refl (v.adicCompletion K) := by
  apply RingEquiv.toRingHom_injective
  exact (eq_adicCompletionCongr_of_continuous (fun _ ↦ rfl) continuous_id fun _ ↦ rfl).symm

/-- Transporting completions along two field isomorphisms is transport along their composite. -/
@[simp]
theorem adicCompletionCongr_trans {R'' K'' : Type*} [CommRing R''] [IsDedekindDomain R'']
    [Field K''] [Algebra R'' K''] [IsFractionRing R'' K''] (u : HeightOneSpectrum R'')
    (τ : K' ≃+* K'') (hτ : ∀ y, u.valuation K'' (τ y) = w.valuation K' y) :
    (adicCompletionCongr v w σ hσ).trans (adicCompletionCongr w u τ hτ) =
      adicCompletionCongr v u (σ.trans τ) (fun x ↦ by
        rw [RingEquiv.trans_apply, hτ, hσ]) := by
  ext x
  rw [RingEquiv.trans_apply, toCompletion_adicCompletionCongr, toCompletion_adicCompletionCongr,
    toCompletion_adicCompletionCongr, ← RingEquiv.trans_apply, Valuation.Completion.congr_trans]

/-- The inverse of `adicCompletionCongr` is the completion of the inverse isomorphism. -/
@[simp]
theorem adicCompletionCongr_symm :
    (adicCompletionCongr v w σ hσ).symm =
      adicCompletionCongr w v σ.symm (fun y ↦ by simpa using (hσ (σ.symm y)).symm) := by
  ext x
  rw [toCompletion_adicCompletionCongr, ← Valuation.Completion.congr_symm hσ,
    RingEquiv.eq_symm_apply, ← toCompletion_adicCompletionCongr hσ, RingEquiv.apply_symm_apply]

/-- `adicCompletionCongr` preserves the valuations of the completions. -/
@[simp]
theorem valued_adicCompletionCongr (x : v.adicCompletion K) :
    Valued.v (adicCompletionCongr v w σ hσ x) = Valued.v x := by
  rw [← adicCompletion.valued_toCompletion_apply, toCompletion_adicCompletionCongr,
    Valuation.Completion.valued_congr (v.valuation_surjective K),
    adicCompletion.valued_toCompletion_apply]

/-- `adicCompletionCongr` carries the local integers `𝒪_v` onto the local integers `𝒪'_w`. -/
@[simp]
theorem adicCompletionCongr_mem_adicCompletionIntegers_iff {x : v.adicCompletion K} :
    adicCompletionCongr v w σ hσ x ∈ w.adicCompletionIntegers K' ↔
      x ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, valued_adicCompletionCongr]

/-- Applied entrywise, `adicCompletionCongr` carries `GL_n(𝒪_v)` onto `GL_n(𝒪'_w)`: an element
`g ∈ GL_n(K_v)` lies in the image of `GL_n(𝒪_v)` exactly when its transport lies in the image of
`GL_n(𝒪'_w)`. -/
theorem map_adicCompletionCongr_mem_range_map_subtype_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : Matrix.GeneralLinearGroup ι (v.adicCompletion K)} :
    Matrix.GeneralLinearGroup.map
        (adicCompletionCongr v w σ hσ : v.adicCompletion K →+* w.adicCompletion K') g ∈
      (Matrix.GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers K').subtype).range ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := ι) (v.adicCompletionIntegers K).subtype).range := by
  -- `ValuationSubring.subtype A` is by definition the inclusion of the subring `A.toSubring`.
  refine ((Matrix.GeneralLinearGroup.mem_range_map_subtype_iff
    (w.adicCompletionIntegers K').toSubring).trans ?_).trans
      (Matrix.GeneralLinearGroup.mem_range_map_subtype_iff
        (v.adicCompletionIntegers K).toSubring).symm
  simp only [ValuationSubring.mem_toSubring, ← map_inv, Matrix.GeneralLinearGroup.map_apply,
    RingEquiv.coe_toRingHom, adicCompletionCongr_mem_adicCompletionIntegers_iff]

end Completion

end IsDedekindDomain.HeightOneSpectrum
