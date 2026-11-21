/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.LyingOver
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Torsor
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.RingTheory.Valuation.Galois

/-!
# Extensions of valuations to a normal extension

Let `L / K` be a field extension. A point of the valuation spectrum of a field is the point of
its valuation subring, so the extensions of a point `v` of `Spv K` to `L` are the valuation
subrings of `L` lying over that of `v`, with arbitrary rank. This file transports the conjugacy
of those extensions (`TauCeti/RingTheory/Valuation/Galois.lean`) to `Spv`:

* every point of `Spv K` extends to `L`;
* if `L / K` is purely inseparable, the extension is unique;
* if a finite group `G` acts on `L` by automorphisms fixing `K`, with fixed field purely
  inseparable over `K`, then the fibres of `Spv L → Spv K` are the `G`-orbits, for the action
  `g • y = comap (g⁻¹ • ·) y` used for finite étale torsors in
  `TauCeti/AlgebraicGeometry/AdicSpace/ValuationSpectrum/Torsor.lean`. For a normal extension
  with finitely many automorphisms, `G = Gal(L/K)` qualifies: its fixed field is the relative
  perfect closure `perfectClosure K L`, over which `Spv` therefore maps bijectively to `Spv K`.

For a finite group acting on a ring `A`, a prime of `A` has a residue field extension over the
residue field of its contraction to `Aᴳ` that is normal, with automorphisms induced by the
decomposition group (`IsFractionRing.stabilizerHom_surjective`); this file supplies the
valuation-theoretic input to describing the fibres of `Spv A → Spv Aᴳ` as orbits.

## Main results

* `TauCeti.ValuationSpectrum.comap_algebraMap_surjective`: `Spv L → Spv K` is surjective.
* `TauCeti.ValuationSpectrum.comap_algebraMap_bijective_of_isPurelyInseparable`: along a purely
  inseparable extension it is bijective.
* `TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_fixedPoints_le`: its
  fibres are the orbits of a finite group whose fixed field is purely inseparable over `K`.
* `TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_normal`: its fibres
  are the `Gal(L/K)`-orbits for a normal extension with finitely many automorphisms.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), proof of
  Theorem 3.1, Step 1.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Every point of `Spv K` extends to any field extension `L`.** -/
theorem comap_algebraMap_surjective :
    Function.Surjective (comap (algebraMap K L) : Spv L → Spv K) := by
  intro v
  have hv : v.supp = ⊥ := Ideal.eq_bot_of_prime _
  obtain ⟨w, -, hw⟩ := exists_supp_eq_comap_eq (algebraMap K L) v ⊥
    (by rw [hv, Ideal.comap_bot_of_injective _ (algebraMap K L).injective])
  exact ⟨w, hw⟩

/-- **A point of `Spv K` extends at most once along a purely inseparable extension.** -/
theorem comap_algebraMap_injective_of_isPurelyInseparable [IsPurelyInseparable K L] :
    Function.Injective (comap (algebraMap K L) : Spv L → Spv K) := by
  intro y y' h
  have hV := congrArg (fun w ↦ w.valuation.valuationSubring) h
  simp only [valuationSubring_valuation_comap] at hV
  rw [← ofValuation_valuationSubring_valuation y, ← ofValuation_valuationSubring_valuation y',
    ValuationSubring.comap_injective_of_isPurelyInseparable hV]

/-- **A point of `Spv K` extends uniquely along a purely inseparable extension**, for instance
to the relative perfect closure `perfectClosure K L`, which for a normal extension `L / K` is the
fixed field of `Gal(L/K)` (`TauCeti.mem_perfectClosure_iff_fixed`). -/
theorem comap_algebraMap_bijective_of_isPurelyInseparable [IsPurelyInseparable K L] :
    Function.Bijective (comap (algebraMap K L) : Spv L → Spv K) :=
  ⟨comap_algebraMap_injective_of_isPurelyInseparable, comap_algebraMap_surjective⟩

variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- **The fibres of `Spv L → Spv K` are the orbits of `G`** when `G` is a finite group acting on
`L` by automorphisms fixing `K`, with fixed field purely inseparable over `K` (for instance a
finite Galois group). Two points `y` and `y'` of `Spv L` have the same image in `Spv K` exactly
when `y' = g • y` for some `g ∈ G`, where `(g • y)(b) = y(g⁻¹ • b)`. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_fixedPoints_le
    (hG : FixedPoints.intermediateField (F := K) G ≤ perfectClosure K L) {y y' : Spv L} :
    comap (algebraMap K L) y = comap (algebraMap K L) y' ↔
      ∃ g : G, y' = comap (MulSemiringAction.toRingHom G L g⁻¹) y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ by rw [hg, comap_algebraMap_comap_toRingHom]⟩
  have hV := congrArg (fun w ↦ w.valuation.valuationSubring) h
  simp only [valuationSubring_valuation_comap] at hV
  obtain ⟨g, hg⟩ := ValuationSubring.exists_smul_eq_of_comap_eq hG hV
  refine ⟨g, ?_⟩
  rw [← ofValuation_valuationSubring_valuation y', ← hg,
    ValuationSubring.pointwise_smul_eq_comap, ← comap_ofValuation_valuation,
    ofValuation_valuationSubring_valuation]

omit [Group G] [Finite G] [MulSemiringAction G L] [SMulCommClass G K L] in
/-- **The extensions of a valuation to a normal extension are conjugate.** If `L / K` is normal
with finitely many automorphisms, two points `y` and `y'` of `Spv L` have the same image in
`Spv K` exactly when `y' = σ • y` for some `σ ∈ Gal(L/K)`, where `(σ • y)(b) = y(σ⁻¹ b)`. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_normal [Normal K L] [Finite Gal(L/K)]
    {y y' : Spv L} :
    comap (algebraMap K L) y = comap (algebraMap K L) y' ↔
      ∃ σ : Gal(L/K), y' = comap (MulSemiringAction.toRingHom Gal(L/K) L σ⁻¹) y :=
  comap_algebraMap_eq_comap_algebraMap_iff_of_fixedPoints_le (G := Gal(L/K)) fun _ hx ↦
    TauCeti.mem_perfectClosure_iff_fixed.mpr hx

end TauCeti.ValuationSpectrum
