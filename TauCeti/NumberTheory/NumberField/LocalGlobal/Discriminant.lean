/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Exponent
import TauCeti.RingTheory.DedekindDomain.Discriminant.Valuation

/-!
# The relative discriminant from the local discriminant exponents

Let `L/K` be an extension of number fields, `v` a finite place of `K` and `w` a finite place of
`L` above it. The discriminant exponent `δ(L_w/K_v)` of the completion is the residue degree
`f(w ∣ v)` times the coefficient of the different of `L/K` at `w`
(`IsDedekindDomain.HeightOneSpectrum.discriminantExponent_adicCompletion`): both factors are
unchanged by completion. Since the coefficient of the relative discriminant at `v` is the sum of
these products over the places above `v`, it is the sum of the local discriminant exponents.

For `L/K` Galois, the places above `v` form one orbit of `Gal(L/K)`, of size the index of the
decomposition group `D_w`. Conjugate places have isomorphic completions over `K_v`, so the
coefficient of the relative discriminant at `v` is `[Gal(L/K) : D_w] · δ(L_w/K_v)`
(`IsDedekindDomain.HeightOneSpectrum.multiplicity_relDiscr_eq_index_mul_discriminantExponent`).
This is the form in which local discriminant formulas, such as the local conductor–discriminant
formula, pass to number fields.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.discriminantExponent_adicCompletion`: the discriminant
  exponent of `L_w/K_v` is `f(w ∣ v)` times the coefficient of the different at `w`.
* `IsDedekindDomain.HeightOneSpectrum.multiplicity_relDiscr_eq_index_mul_discriminantExponent`:
  for `L/K` Galois, the coefficient of the relative discriminant at `v` is the index of the
  decomposition group of `w` times the discriminant exponent of `L_w/K_v`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9 and Chapter III, §2.
-/

public section

open IsDedekindDomain _root_.NumberField
open scoped AdicCompletionExtension Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **The local discriminant exponent of a completion.** For a finite place `w` of `L` above the
finite place `v` of `K`, the discriminant exponent of `L_w/K_v` is the residue degree of `w` over
`v` times the coefficient at `w` of the different of `L/K`. -/
theorem discriminantExponent_adicCompletion :
    TauCeti.discriminantExponent (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
  rw [TauCeti.discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    TauCeti.inertiaDegree_def, finrank_residueField_adicCompletion,
    differentExponent_adicCompletion_eq_multiplicity_differentIdeal,
    multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal]

/-- **The relative discriminant of a Galois extension from one completion.** For `L/K` Galois and
a finite place `w` of `L` above the finite place `v` of `K`, the coefficient at `v` of the relative
discriminant of `L/K` is the index of the decomposition group of `w` times the discriminant
exponent of `L_w/K_v`. -/
theorem multiplicity_relDiscr_eq_index_mul_discriminantExponent [IsGalois K L] :
    multiplicity v.asIdeal (TauCeti.relDiscr (𝓞 K) (𝓞 L)) =
      (MulAction.stabilizer Gal(L/K) w.asIdeal).index *
        TauCeti.discriminantExponent (v.adicCompletion K) (w.adicCompletion L) := by
  classical
  -- The primes above `v` are the orbit of `w`, whose size is the index of its stabilizer.
  rw [TauCeti.multiplicity_relDiscr _ _ v.ne_bot (differentIdeal_ne_bot (A := 𝓞 K)),
    MulAction.index_stabilizer,
    Algebra.IsInvariant.orbit_eq_primesOver (𝓞 K) (𝓞 L) Gal(L/K) v.asIdeal w.asIdeal,
    Set.ncard_eq_toFinset_card', ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun P hP ↦ ?_
  rw [Set.mem_toFinset, ← Algebra.IsInvariant.orbit_eq_primesOver (𝓞 K) (𝓞 L) Gal(L/K) v.asIdeal
    w.asIdeal] at hP
  obtain ⟨σ, rfl⟩ := hP
  -- `σ • w` is a place of `L` above `v`, whose completion is isomorphic to `L_w` over `K_v`.
  obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 L), w'.asIdeal = σ • w.asIdeal :=
    ⟨⟨σ • w.asIdeal, inferInstance, fun h ↦
      w.ne_bot ((smul_left_cancel_iff σ).mp (h.trans (Ideal.smul_bot σ).symm))⟩, rfl⟩
  have : w'.asIdeal.LiesOver v.asIdeal := hw' ▸ inferInstance
  dsimp only
  rw [← hw', ← discriminantExponent_adicCompletion v w']
  exact (TauCeti.discriminantExponent_eq_of_algEquiv _ _ _ (completionCongr v σ hw')).symm

end IsDedekindDomain.HeightOneSpectrum
