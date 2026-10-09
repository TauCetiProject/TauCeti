/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.HerbrandQuotient
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Unramified
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.GaloisAction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.IntegralUnits
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Shapiro
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# The Tate cohomology of the semi-local units at a finite place

Let `L/K` be a cyclic extension of number fields and `v` a finite place of `K`. This file computes
the two kinds of factor at `v` in the Tate cohomology of the `S`-ideles of `L`, which together with
the Herbrand quotient of the `S`-units gives the first fundamental inequality for cyclic
extensions.

* For `v ∈ S`, the factor is the Galois module `∏_{w ∣ v} L_wˣ`, realized as the units of the
  semi-local algebra `K_v ⊗[K] L` (`TauCeti.semilocalUnitsRep`). Its Herbrand quotient is the
  local degree `[L_w : K_v]` at any place `w` above `v`.
* For `v ∉ S`, and `v` unramified in `L`, the factor is `∏_{w ∣ v} 𝒪_wˣ`, realized as the
  integral semi-local units (`TauCeti.semilocalIntegralUnitsRep`). Its Tate cohomology vanishes
  in every degree, so it contributes nothing.

Both proofs combine three identifications. The semi-local units are coinduced from the units of
`L_w` as a representation of the decomposition group `D_w` (`TauCeti.semilocalUnitsCoindIso`,
and `TauCeti.semilocalIntegralUnitsCoindIso` for the integral units), so by Shapiro's lemma
(`TauCeti.TateCohomology.herbrandQuotient_coind` and `TauCeti.TateCohomology.coindIso`) the
computation takes place over `D_w`. The decomposition group is the Galois group of `L_w/K_v`
(`IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`). Finally, for the cyclic local
extension `L_w/K_v` the Herbrand quotient of `L_wˣ` is `[L_w : K_v]`
(`TauCeti.herbrandQuotient_units_eq_finrank`), and when `L_w/K_v` is unramified the units of its
ring of integers have no Tate cohomology
(`TauCeti.TateCohomology.isZero_tateCohomology_unitFiltration_zero_of_isUnramified`).

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_semilocalUnitsRep`: `h((K_v ⊗[K] L)ˣ) = [L_w : K_v]`
  for `L/K` cyclic.
* `TauCeti.ClassFieldTheory.isZero_tateCohomology_semilocalIntegralUnitsRep`:
  `H-hat^n(Gal(L/K), ∏_{w ∣ v} 𝒪_wˣ) = 0` for `L/K` cyclic and `v` unramified in `L`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 2.4 and Proposition 2.7.
-/

public section
noncomputable section

open CategoryTheory IsDedekindDomain Limits Module
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

/-- **The integral semi-local units at an unramified place have no Tate cohomology.** For a cyclic
extension `L/K` of number fields and a finite place `v` of `K` unramified in `L`, the units of
`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` whose every component is a unit of `𝒪_w` have vanishing Tate
cohomology `H-hat^n(Gal(L/K), -)` in every degree `n : ℤ`. Unramifiedness is asked of one place
`w` above `v`; the Galois group permutes the places above `v` transitively, so they are then all
unramified. -/
theorem isZero_tateCohomology_semilocalIntegralUnitsRep (w : HeightOneSpectrum (𝒪 L))
    [w.asIdeal.LiesOver v.asIdeal] [Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal] (n : ℤ) :
    IsZero (tateCohomology (semilocalIntegralUnitsRep L v) n) :=
  (TateCohomology.isZero_tateCohomology_unitFiltration_zero_of_isUnramified n).of_iso <|
    (tateCohomologyFunctor n).mapIso (semilocalIntegralUnitsCoindIso v w) ≪≫
      TateCohomology.coindIso _ _ n ≪≫
      -- `decompositionIntegralUnitsRep v w` is by definition the restriction along
      -- `decompositionHom v w`, the underlying hom of this equivalence
      (TateCohomology.resIso (MulEquiv.ofBijective (decompositionHom v w)
        ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩) n).app _

end TauCeti.ClassFieldTheory
