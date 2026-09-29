/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The one-variable restricted power-series algebra

This file identifies the two models of the one-variable Tate algebra used in Tau Ceti. The Huber
development uses restricted multivariate power series indexed by `Fin 1`, while Weierstrass
division uses Mathlib's univariate `PowerSeries`, whose variable type is `Unit`. Renaming the
variable along `finOneEquiv` identifies their restrictedness conditions and hence gives an
equivalence between the two subrings.

Over a complete nonarchimedean normed ring, the Huber completion agrees with the plain restricted
series ring. Composing that comparison with the variable-renaming equivalence identifies the
completed Huber algebra with Mathlib's univariate restricted-series ring. For a complete
nonarchimedean field, the latter is noetherian by one-variable Weierstrass division, so the
completed Huber algebra is noetherian as well.

## Main results

* `TauCeti.Huber.restrictedMvPowerSeriesSubringOneEquiv`: the two uncompleted one-variable
  restricted-series models are equivalent as rings.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionOneEquiv`: over a complete base, the completed
  Huber model is equivalent to Mathlib's univariate restricted-series ring.
* `TauCeti.Huber.isNoetherianRing_restrictedMvPowerSeriesCompletion_one`: the completed
  one-variable Tate algebra over a complete nonarchimedean field is noetherian.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, for noetherianity of Tate algebras.
* T. Wedhorn, *Adic Spaces*, §5.6, for restricted power series and their topology.
-/

public section

namespace TauCeti.Huber

open Filter

section Comparison

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R]

omit [IsUltrametricDist R] [NonarchimedeanRing R] in
private theorem coeff_renameEquiv_finOne (f : MvPowerSeries (Fin 1) R) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.renameEquiv R finOneEquiv f) =
      MvPowerSeries.coeff ((Finsupp.uniqueEquiv (0 : Fin 1)).symm n) f := by
  change MvPowerSeries.coeff (Finsupp.single () n)
      (MvPowerSeries.rename finOneEquiv f) = _
  rw [show Finsupp.single () n = Finsupp.embDomain finOneEquiv.toEmbedding
      ((Finsupp.uniqueEquiv (0 : Fin 1)).symm n) by ext; simp]
  exact MvPowerSeries.coeff_embDomain_rename _ _ _

omit [IsUltrametricDist R] [NonarchimedeanRing R] in
/-- **Renaming the sole variable preserves restrictedness.** The Huber predicate asks directly
that the coefficients tend to zero, while Mathlib's radius-one predicate asks the same of their
norms. The exponent sets are identified by the unique-coordinate equivalence. -/
theorem isRestricted_renameEquiv_finOne_iff (f : MvPowerSeries (Fin 1) R) :
    IsRestricted f ↔
      PowerSeries.IsRestricted 1 (MvPowerSeries.renameEquiv R finOneEquiv f) := by
  rw [isRestricted_iff_coeff, PowerSeries.isRestricted_iff]
  simp only [one_pow, mul_one]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro hf
    exact (hf.comp (Finsupp.uniqueEquiv (0 : Fin 1)).symm.injective.tendsto_cofinite).congr'
      (Filter.Eventually.of_forall fun n ↦ (coeff_renameEquiv_finOne f n).symm)
  · intro hf
    refine (hf.comp (Finsupp.uniqueEquiv (0 : Fin 1)).injective.tendsto_cofinite).congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [coeff_renameEquiv_finOne]
    exact congrArg (fun m ↦ MvPowerSeries.coeff m f)
      ((Finsupp.uniqueEquiv (0 : Fin 1)).left_inv n)

omit [NonarchimedeanRing R] in
private theorem powerSeries_isRestricted_coe
    (f : PowerSeries.IsRestricted.subring (R := R) 1) :
    PowerSeries.IsRestricted 1 (f : PowerSeries R) := by
  change MvPowerSeries.IsRestricted (fun _ : Unit ↦ (1 : ℝ)) (f : PowerSeries R)
  exact f.2

/-- **The two one-variable restricted-series models are the same ring.** The Huber model uses
`Fin 1` as its variable type; Mathlib's `PowerSeries` uses `Unit`. The equivalence is variable
renaming along `finOneEquiv`, restricted to the subrings whose coefficients tend to zero. -/
noncomputable def restrictedMvPowerSeriesSubringOneEquiv :
    restrictedMvPowerSeriesSubring 1 R ≃+*
      PowerSeries.IsRestricted.subring (R := R) 1 where
  toFun f := ⟨MvPowerSeries.renameEquiv R finOneEquiv f,
    (isRestricted_renameEquiv_finOne_iff (R := R) (f : MvPowerSeries (Fin 1) R)).mp
      (mem_restrictedMvPowerSeriesSubring.mp f.2)⟩
  invFun f := ⟨(MvPowerSeries.renameEquiv R finOneEquiv).symm f,
    mem_restrictedMvPowerSeriesSubring.mpr <|
      (isRestricted_renameEquiv_finOne_iff (R := R)
        ((MvPowerSeries.renameEquiv R finOneEquiv).symm (f : PowerSeries R))).mpr <| by
          simpa only [AlgEquiv.apply_symm_apply] using powerSeries_isRestricted_coe f⟩
  left_inv f := Subtype.ext <| (MvPowerSeries.renameEquiv R finOneEquiv).left_inv f
  right_inv f := Subtype.ext <| (MvPowerSeries.renameEquiv R finOneEquiv).right_inv f
  map_mul' f g := Subtype.ext <| map_mul (MvPowerSeries.renameEquiv R finOneEquiv)
    (f : MvPowerSeries (Fin 1) R) g
  map_add' f g := Subtype.ext <| map_add (MvPowerSeries.renameEquiv R finOneEquiv)
    (f : MvPowerSeries (Fin 1) R) g

/-- The one-variable equivalence is variable renaming on underlying power series. -/
@[simp]
theorem coe_restrictedMvPowerSeriesSubringOneEquiv
    (f : restrictedMvPowerSeriesSubring 1 R) :
    ((restrictedMvPowerSeriesSubringOneEquiv f :
        PowerSeries.IsRestricted.subring (R := R) 1) : PowerSeries R) =
      MvPowerSeries.renameEquiv R finOneEquiv
        (f : MvPowerSeries (Fin 1) R) := by
  simp [restrictedMvPowerSeriesSubringOneEquiv]

end Comparison

section Complete

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R]
  [CompleteSpace R]

/-- **The completed one-variable Huber algebra is the univariate restricted-series ring.**
Completeness identifies the completion with the trivial-weight restricted-series subring; the
trivial-weight comparison and variable renaming then give the displayed ring equivalence. -/
noncomputable def restrictedMvPowerSeriesCompletionOneEquiv :
    restrictedMvPowerSeriesCompletion 1 R ≃+*
      PowerSeries.IsRestricted.subring (R := R) 1 :=
  (restrictedMvPowerSeriesCompletionEquiv 1 R).trans <|
    (RingEquiv.subringCongr
      (weightedRestrictedSubring_one_weight (k := 1) (A := R))).trans
        restrictedMvPowerSeriesSubringOneEquiv

/-- The completed comparison sends a restricted series in the canonical dense subring to the
same series, with its sole variable renamed from `Fin 1` to `Unit`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionOneEquiv_coe
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionOneEquiv
        (f : restrictedMvPowerSeriesCompletion 1 R) =
      restrictedMvPowerSeriesSubringOneEquiv
        (RingEquiv.subringCongr
          (weightedRestrictedSubring_one_weight (k := 1) (A := R)) f) := by
  simp [restrictedMvPowerSeriesCompletionOneEquiv, RingEquiv.trans_apply]

end Complete

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K]

/-- **The completed one-variable Tate algebra over a complete nonarchimedean field is
noetherian.** This is the one-variable case of noetherianity for the canonical Huber completion,
transported from the restricted univariate series ring where Weierstrass division proves the
stronger principal-ideal theorem. -/
theorem isNoetherianRing_restrictedMvPowerSeriesCompletion_one :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion 1 K) := by
  let _ := TauCeti.PowerSeries.isNoetherianRing_isRestricted_subring (K := K) (c := 1) zero_lt_one
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionOneEquiv (R := K)).symm

end Field

end TauCeti.Huber
