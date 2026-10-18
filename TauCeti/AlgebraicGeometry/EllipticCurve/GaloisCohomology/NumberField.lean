/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Finiteness
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.FixingSubgroup
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere
import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion

/-!
# Finiteness of Selmer groups over number fields

The cohomological `m`-Selmer group of an elliptic curve over a number field is finite for
`m ≠ 0`. The local conditions here are imposed at all finite places. Adding archimedean
local conditions cuts out a subgroup, so does not affect the finiteness conclusion.

Restriction to the division field has finite kernel and carries Selmer classes to Selmer
classes, using the canonical maps between completions at primes lying above one another.
Over the division field all geometric `m`-torsion is rational. A common finite ramification
set and the Weil pairing then give finiteness from the arithmetic Kummer groups.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.2.
-/

public section

open TauCeti TauCeti.ContCohomology IsDedekindDomain NumberField
open scoped NumberField

namespace WeierstrassCurve

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- Over a number field whose absolute Galois group fixes the geometric `m`-torsion, the
`m`-Selmer group with local conditions at all finite places is finite for `m ≠ 0`. No set of
primes of good reduction needs to be supplied. -/
theorem finite_selmerGroup_of_forall_smul_eq_of_numberField
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    {m : ℕ} (hm : m ≠ 0)
    (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P) :
    Finite (W.selmerGroup τ m) := by
  obtain ⟨S, -, hgood, -⟩ :=
    exists_finset_isElliptic_integralModel_adicCompletion (𝓞 K) W (Nat.cast_ne_zero.2 hm) ∅
  exact W.finite_selmerGroup_of_forall_smul_eq (τ := τ) S.finite_toSet hgood hm h

/-- The cohomological `m`-Selmer group of an elliptic curve over a number field, with local
conditions at all finite places, is finite for every nonzero `m`. The conclusion is independent
of the embeddings of separable closures used to define restriction. -/
theorem finite_selmerGroup_of_numberField
    (τ : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    {m : ℕ} (hm : m ≠ 0) : Finite (W.selmerGroup τ m) := by
  classical
  let : NeZero m := ⟨hm⟩
  -- Work with an abstract extension while building its completion towers: this avoids
  -- instance searches through the ambient field of a concrete intermediate field.
  have descend {L : Type _} [Field L] [Algebra K L] [NumberField L]
      (hfix : ∀ (g : AbsoluteGaloisGroup L) (P : (W⁄L).TorsionCoeff m), g • P = P)
      (hker : ∀ ρ : SeparableClosure K →ₐ[K] SeparableClosure L,
        Finite (W.torsionRes ρ m).ker) : Finite (W.selmerGroup τ m) := by
    let ρ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
    let τL : ∀ w : HeightOneSpectrum (𝓞 L),
        SeparableClosure L →ₐ[L] SeparableClosure (w.adicCompletion L) :=
      fun _ ↦ IsSepClosed.lift
    have hL := (W⁄L).finite_selmerGroup_of_forall_smul_eq_of_numberField τL hm hfix
    -- Each completion of `L` extends the completion at its contracted prime of `K`.
    let under : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K) :=
      fun w ↦ w.under (𝓞 K)
    let (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.LiesOver (under w).asIdeal :=
      ⟨HeightOneSpectrum.under_asIdeal _ w⟩
    open scoped AdicCompletionExtension in
      exact W.finite_selmerGroup_of_finite_ker_torsionRes ρ τ τL under (hker ρ) hL
  let : NumberField (W.divisionField m) := NumberField.of_module_finite K _
  exact descend (W.forall_smul_eq_torsionCoeff_divisionField m)
    (W.finite_ker_torsionRes_divisionField m)

end WeierstrassCurve
