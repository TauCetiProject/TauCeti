/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.RingTheory.Dagger.MaximalSpectrum
import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.RingTheory.Dagger.KrullDimension
import TauCeti.RingTheory.Dagger.Regular
import TauCeti.RingTheory.Flat.Localization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Regular
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.MiracleFlatness

/-!
# The Tate algebra is faithfully flat over the Monsky–Washnitzer algebra

Let `K` be a complete nontrivially normed ultrametric field, `W = K⟨X₁, …, Xₙ⟩†` the
Monsky–Washnitzer algebra and `T = K⟨X₁, …, Xₙ⟩` the Tate algebra. This file shows that the
inclusion `W → T` is faithfully flat.

Flatness is checked at the maximal ideals `m` of `T`. The contraction `n = m ∩ W` is maximal and
generates `m` (`TauCeti.Dagger.washnitzerAlgebra.map_comap_toTate_of_isMaximal`), so the local
homomorphism `W_n → T_m` sends the maximal ideal of `W_n` onto that of `T_m`. Both local rings are
regular of dimension `n`, and the closed fibre `T_m ⧸ n T_m` is a field, of dimension zero. Since a
regular local ring is Cohen–Macaulay, miracle flatness (`TauCeti.Algebra.flat_of_isCohenMacaulay`)
shows that `T_m` is flat over `W_n`. Faithfulness holds because every maximal ideal of `W`
generates a maximal, hence proper, ideal of `T`
(`TauCeti.Dagger.washnitzerAlgebra.isMaximal_map_toTate`).

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.flat_localRingHom_toTate`: for a maximal ideal `m` of `T`, the
  local ring of `T` at `m` is flat over the local ring of `W` at `m ∩ W`.
* `TauCeti.Dagger.washnitzerAlgebra.flat_toTate`: `W → T` is flat.
* `TauCeti.Dagger.washnitzerAlgebra.faithfullyFlat_toTate`: `W → T` is faithfully flat.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.5.
* [The Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), miracle
  flatness.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries _root_.IsLocalRing

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W " σ:max => washnitzerAlgebra σ K
local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- **The Tate algebra is flat over the Monsky–Washnitzer algebra at each classical point.** For a
maximal ideal `m` of `T = K⟨X⟩`, the local ring `T_m` is flat over the local ring of
`W = K⟨X⟩†` at `m ∩ W`. -/
theorem flat_localRingHom_toTate (m : Ideal (T σ)) [m.IsMaximal] :
    (Localization.localRingHom (m.comap (toTate σ K)) m (toTate σ K).toRingHom rfl).Flat := by
  set n := m.comap (toTate σ K)
  have : n.IsMaximal := isAffinoidAlgebra_tate.comap_isMaximal _ m
  set f := Localization.localRingHom n m (toTate σ K).toRingHom rfl
  algebraize [f]
  rw [RingHom.Flat]
  -- The maximal ideal of `W_n` generates that of `T_m`, since `n` generates `m`.
  have hmax : (maximalIdeal (Localization.AtPrime n)).map
      (algebraMap (Localization.AtPrime n) (Localization.AtPrime m)) =
        maximalIdeal (Localization.AtPrime m) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    have hcomp : (algebraMap (Localization.AtPrime n) (Localization.AtPrime m)).comp
        (algebraMap (W σ) (Localization.AtPrime n)) =
          (algebraMap (T σ) (Localization.AtPrime m)).comp (toTate σ K).toRingHom :=
      RingHom.ext fun x ↦ Localization.localRingHom_to_map _ _ _ rfl x
    rw [hcomp, ← Ideal.map_map, AlgHom.toRingHom_eq_coe, Ideal.map_coe,
      map_comap_toTate_of_isMaximal]
  have : IsNoetherianRing (Localization.AtPrime m) := IsLocalization.isNoetherianRing m.primeCompl _
    TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring
  have : IsLocalHom (algebraMap (Localization.AtPrime n) (Localization.AtPrime m)) :=
    Localization.isLocalHom_localRingHom n m _ rfl
  -- Miracle flatness: both local rings have dimension `n`, and the closed fibre is a field.
  refine TauCeti.Algebra.flat_of_isCohenMacaulay TauCeti.IsRegularLocalRing.isCohenMacaulay ?_
  rw [hmax, ringKrullDim_eq_zero_of_isField (Ideal.Quotient.maximal_ideal_iff_isField_quotient _
      |>.mp (maximalIdeal.isMaximal _)), add_zero,
    IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
    Ideal.height_eq_natCard_of_isMaximal_isRestricted_subring,
    Ideal.ringKrullDim_localization_atPrime_of_isMaximal_washnitzerAlgebra]
  norm_cast

/-- **The Tate algebra is flat over the Monsky–Washnitzer algebra.** The inclusion
`K⟨X₁, …, Xₙ⟩† → K⟨X₁, …, Xₙ⟩` is a flat ring homomorphism. -/
theorem flat_toTate : (toTate σ K).toRingHom.Flat := by
  algebraize [(toTate σ K).toRingHom]
  refine Module.flat_of_isLocalized_maximal (T σ) (T σ) (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap (T σ) _) fun m _ ↦ ?_
  exact (Localization.flat_localRingHom_iff _ m rfl).mp (flat_localRingHom_toTate m)

/-- **The Tate algebra is faithfully flat over the Monsky–Washnitzer algebra.** The inclusion
`K⟨X₁, …, Xₙ⟩† → K⟨X₁, …, Xₙ⟩` is a faithfully flat ring homomorphism. -/
theorem faithfullyFlat_toTate : (toTate σ K).toRingHom.FaithfullyFlat := by
  -- `algebraize` turns `hflat` into the `Module.Flat` instance that `FaithfullyFlat` extends.
  have hflat := flat_toTate (σ := σ) (K := K)
  algebraize [(toTate σ K).toRingHom]
  refine ⟨fun n hn ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, ne_eq, Submodule.restrictScalars_eq_top_iff]
  exact (isMaximal_map_toTate n).ne_top

end TauCeti.Dagger.washnitzerAlgebra
