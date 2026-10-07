/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.HerbrandQuotient
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.GaloisAction

/-!
# The Herbrand quotient of the semi-local units at a finite place

Let `L/K` be a cyclic extension of number fields and `v` a finite place of `K`. The Galois module
`∏_{w ∣ v} L_wˣ`, realized as the units of the semi-local algebra `K_v ⊗[K] L`
(`TauCeti.semilocalUnitsRep`), has Herbrand quotient the local degree `[L_w : K_v]` at any place
`w` above `v`. This is the factor at a finite place of `S` in the computation of the Herbrand
quotient of the `S`-ideles of `L`, which together with the Herbrand quotient of the `S`-units
gives the first fundamental inequality for cyclic extensions.

The proof combines three identifications. The semi-local units are coinduced from the units of
`L_w` as a representation of the decomposition group `D_w` (`TauCeti.semilocalUnitsCoindIso`), so
by Shapiro's lemma their Herbrand quotient is that of `L_wˣ` over `D_w`
(`TauCeti.TateCohomology.herbrandQuotient_coind`). The decomposition group is the Galois group of
`L_w/K_v` (`IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`), and for the cyclic local
extension `L_w/K_v` the Herbrand quotient of `L_wˣ` is `[L_w : K_v]`
(`TauCeti.herbrandQuotient_units_eq_finrank`).

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_semilocalUnitsRep`: `h((K_v ⊗[K] L)ˣ) = [L_w : K_v]`
  for `L/K` cyclic.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 2.4 and Proposition 2.7.
-/

public section
noncomputable section

open IsDedekindDomain Module
open scoped NumberField AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (v : HeightOneSpectrum (𝒪 K))

/-- **The Herbrand quotient of the semi-local units.** For a cyclic extension `L/K` of number
fields and a finite place `v` of `K`, the units of `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` have Herbrand
quotient `[L_w : K_v]` as a representation of `Gal(L/K)`, for any place `w` of `L` above `v`. -/
theorem herbrandQuotient_semilocalUnitsRep (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    TateCohomology.herbrandQuotient (semilocalUnitsRep L v) =
      finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have : IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
    isCyclic_of_surjective _ (decompositionHom_surjective v w)
  rw [TateCohomology.herbrandQuotient_eq_of_iso (semilocalUnitsCoindIso v w),
    TateCohomology.herbrandQuotient_coind,
    TateCohomology.herbrandQuotient_res_of_bijective
      ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩]
  exact herbrandQuotient_units_eq_finrank _ _

end TauCeti.ClassFieldTheory
