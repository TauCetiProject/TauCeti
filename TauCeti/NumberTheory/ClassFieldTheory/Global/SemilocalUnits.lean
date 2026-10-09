/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Archimedean
public import TauCeti.NumberTheory.LocalField.UnitFiltration.HerbrandQuotient
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Unramified
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.GaloisAction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.InfiniteGaloisAction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.IntegralUnits
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Shapiro
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# The Tate cohomology of the semi-local units

Let `L/K` be a cyclic extension of number fields and `v` a place of `K`. This file computes
the factors at `v` in the Tate cohomology of the `S`-ideles of `L`, which together with the
Herbrand quotient of the `S`-units gives the first fundamental inequality for cyclic extensions.

* For a finite place `v ∈ S`, the factor is the Galois module `∏_{w ∣ v} L_wˣ`, realized as the
  units of the semi-local algebra `K_v ⊗[K] L` (`TauCeti.semilocalUnitsRep`). Its Herbrand
  quotient is the local degree `[L_w : K_v]` at any place `w` above `v`.
* For a finite place `v ∉ S`, and `v` unramified in `L`, the factor is `∏_{w ∣ v} 𝒪_wˣ`, realized
  as the integral semi-local units (`TauCeti.semilocalIntegralUnitsRep`). Its Tate cohomology
  vanishes in every degree, so it contributes nothing.
* For an infinite place `v`, which always lies in `S`, the factor is again `∏_{w ∣ v} L_wˣ`, the
  units of `K_v ⊗[K] L` (`TauCeti.GlobalNumberFields.infiniteSemilocalUnitsRep`). Its Herbrand
  quotient is the local degree `[L_w : K_v]`: `2` when `v` is real and the places above it are
  complex, and `1` otherwise.

All three proofs combine three identifications. The semi-local units are coinduced from the units
of `L_w` as a representation of the decomposition group `D_w` (`TauCeti.semilocalUnitsCoindIso`,
`TauCeti.semilocalIntegralUnitsCoindIso` for the integral units, and
`TauCeti.GlobalNumberFields.infiniteSemilocalUnitsCoindIso` at the infinite places), so by
Shapiro's lemma (`TauCeti.TateCohomology.herbrandQuotient_coind` and
`TauCeti.TateCohomology.coindIso`) the computation takes place over `D_w`. The decomposition
group is the Galois group of `L_w/K_v` (`IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`
and `NumberField.InfinitePlace.decompositionEquiv`). Finally, for the cyclic local extension
`L_w/K_v` the Herbrand quotient of `L_wˣ` is `[L_w : K_v]`
(`TauCeti.herbrandQuotient_units_eq_finrank` at a finite place; at an infinite place
`TauCeti.herbrandQuotient_units_eq_finrank_of_ringEquiv` over `K_v ≃ ℝ`, and
`TauCeti.herbrandQuotient_units_eq_one_of_isAlgClosed` over `K_v ≃ ℂ`), and when `L_w/K_v` is
unramified the units of its ring of integers have no Tate cohomology
(`TauCeti.TateCohomology.isZero_tateCohomology_unitFiltration_zero_of_isUnramified`).

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_semilocalUnitsRep`: `h((K_v ⊗[K] L)ˣ) = [L_w : K_v]`
  for `L/K` cyclic and `v` finite.
* `TauCeti.ClassFieldTheory.isZero_tateCohomology_semilocalIntegralUnitsRep`:
  `H-hat^n(Gal(L/K), ∏_{w ∣ v} 𝒪_wˣ) = 0` for `L/K` cyclic and `v` unramified in `L`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_units_eq_finrank_completion`:
  `h(L_wˣ) = [L_w : K_v]` for an infinite place `w`, as a representation of `Aut(L_w/K_v)`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_infiniteSemilocalUnitsRep`:
  `h((K_v ⊗[K] L)ˣ) = [L_w : K_v]` for `L/K` cyclic and `v` infinite.

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

section InfinitePlace

open NumberField NumberField.InfinitePlace
open scoped NumberField.LiesOver

/-- **The Herbrand quotient of an archimedean completion.** For an infinite place `w` of `L` above
the infinite place `v` of `K`, the units of `L_w` have Herbrand quotient `[L_w : K_v]` as a
representation of `Aut(L_w/K_v)`: it is `2` when `w` is complex above a real `v`, and `1`
otherwise. -/
theorem herbrandQuotient_units_eq_finrank_completion {K L : Type} [Field K] [Field L]
    [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] :
    TateCohomology.herbrandQuotient (Rep.ofAlgebraAutOnUnits v.Completion w.Completion) =
      finrank v.Completion w.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact herbrandQuotient_units_eq_finrank_of_ringEquiv
      (Completion.ringEquivRealOfIsReal hv).symm _
  · -- over the algebraically closed field `K_v ≃ ℂ` both sides are `1`
    have : IsAlgClosed v.Completion :=
      IsAlgClosed.of_ringEquiv ℂ _ (Completion.ringEquivComplexOfIsComplex hv).symm
    have hw : w.IsUnramified K := isUnramified_iff.mpr (.inr (by rwa [LiesOver.comap_eq w v]))
    rw [IsUnramified.finrank_eq_one v hw, Nat.cast_one]
    exact herbrandQuotient_units_eq_one_of_isAlgClosed _ _

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- **The Herbrand quotient of the semi-local units at an infinite place.** For a cyclic
extension `L/K` of number fields and an infinite place `v` of `K`, the units of
`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` have Herbrand quotient `[L_w : K_v]` as a representation of
`Gal(L/K)`, for any place `w` of `L` above `v`. -/
theorem herbrandQuotient_infiniteSemilocalUnitsRep (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] :
    TateCohomology.herbrandQuotient (GlobalNumberFields.infiniteSemilocalUnitsRep L v) =
      finrank v.Completion w.Completion := by
  classical
  rw [TateCohomology.herbrandQuotient_eq_of_iso
      (GlobalNumberFields.infiniteSemilocalUnitsCoindIso v w),
    TateCohomology.herbrandQuotient_coind,
    TateCohomology.herbrandQuotient_res_of_bijective
      ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩]
  exact herbrandQuotient_units_eq_finrank_completion v w

end InfinitePlace

end TauCeti.ClassFieldTheory
