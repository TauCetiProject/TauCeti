/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.RingTheory.LaurentSeries.ValuationRing
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Laurent series over a finite field form a local field

For a field `K`, the formal Laurent series `K⸨X⸩` carry Mathlib's `X`-adic valuation
`LaurentSeries.valued`. This file equips `K⸨X⸩` with the valuative relation that valuation
induces, checks that the `X`-adic topology is the valuative topology and that the relation is
nontrivial, and identifies the ring of integers of the relation with the power series and its
residue field with `K`. When `K` is finite, `K⸨X⸩` is a nonarchimedean local field: it is the
equal-characteristic local field `𝔽_q((X))`, with residue field `𝔽_q`.

## Main results

* `TauCeti.LaurentSeries.integer_eq_powerSeries_as_subring`: the ring of integers `𝒪[K⸨X⸩]` is
  the subring of power series.
* `TauCeti.LaurentSeries.valuativeResidueFieldEquiv`: the residue field `𝓀[K⸨X⸩]` is `K`, the
  residue of an integer being its constant coefficient
  (`TauCeti.LaurentSeries.valuativeResidueFieldEquiv_residue`); hence
  `TauCeti.LaurentSeries.natCard_residueField` and `TauCeti.LaurentSeries.ringChar_residueField`.
* `TauCeti.LaurentSeries.isNonarchimedeanLocalField`: for a finite field `K`, `K⸨X⸩` is a
  nonarchimedean local field.

## Implementation notes

Local compactness is transported from the `X`-adic completion of `K⟮X⟯`, which is a
nonarchimedean local field by
`IsDedekindDomain.HeightOneSpectrum.isNonarchimedeanLocalField_adicCompletion`, along Mathlib's
uniform equivalence `LaurentSeries.comparePkg` between that completion and `K⸨X⸩`.

## References

* J.-P. Serre, *Local Fields*, Chapter II, where the complete discretely valued fields of equal
  characteristic with perfect residue field `k` are identified with `k((X))`.
-/

public section
noncomputable section

open ValuativeRel
open scoped LaurentSeries PowerSeries Polynomial WithZero

namespace TauCeti.LaurentSeries

open _root_.LaurentSeries (powerSeries_as_subring)

variable (K : Type*) [Field K]

/-- The valuative relation on `K⸨X⸩` induced by its `X`-adic valuation. -/
instance instValuativeRel : ValuativeRel K⸨X⸩ :=
  .ofValuation Valued.v

/-- The `X`-adic valuation is compatible with the valuative relation it induces. -/
instance instCompatibleValued : (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- The `X`-adic topology of `K⸨X⸩` is induced by its valuative relation. -/
instance isValuativeTopology : IsValuativeTopology K⸨X⸩ :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰)
    (Valued.is_topological_valuation _)

/-- The valuative relation on `K⸨X⸩` is nontrivial: `X` has valuation `exp (-1)`. -/
instance isNontrivial : ValuativeRel.IsNontrivial K⸨X⸩ := by
  refine (ValuativeRel.isNontrivial_iff_isNontrivial (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰)).mpr
    ⟨⟨((PowerSeries.X : K⟦X⟧) : K⸨X⸩), ?_⟩⟩
  have h := _root_.LaurentSeries.valuation_X_pow K 1
  rw [pow_one] at h
  rw [h]
  exact ⟨WithZero.exp_ne_zero, by simp⟩

/-- The ring of integers of the valuative relation on `K⸨X⸩` is the subring of power series. -/
theorem integer_eq_powerSeries_as_subring : 𝒪[K⸨X⸩] = powerSeries_as_subring K := by
  rw [Huber.LaurentSeries.powerSeries_as_subring_eq_integer]
  ext x
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (valuation K⸨X⸩)).symm.trans
    (Valuation.vle_one_iff (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰))

/-- The residue field of the valuative relation on `K⸨X⸩` is the coefficient field `K`. -/
def valuativeResidueFieldEquiv : 𝓀[K⸨X⸩] ≃+* K :=
  (IsLocalRing.ResidueField.mapEquiv
    (RingEquiv.subringCongr (integer_eq_powerSeries_as_subring K))).trans
    (residueFieldEquiv K)

/-- The residue of an integer of `K⸨X⸩` is its constant coefficient. -/
@[simp]
theorem valuativeResidueFieldEquiv_residue (f : 𝒪[K⸨X⸩]) :
    valuativeResidueFieldEquiv K (IsLocalRing.residue _ f) = (f : K⸨X⸩).coeff 0 := by
  rw [valuativeResidueFieldEquiv, RingEquiv.trans_apply,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
    residueFieldEquiv_residue]
  simp

/-- The residue field of `K⸨X⸩` has as many elements as `K`. -/
@[simp]
theorem natCard_residueField : Nat.card 𝓀[K⸨X⸩] = Nat.card K :=
  Nat.card_congr (valuativeResidueFieldEquiv K).toEquiv

/-- The residue characteristic of `K⸨X⸩` is the characteristic of `K`. -/
@[simp]
theorem ringChar_residueField : ringChar 𝓀[K⸨X⸩] = ringChar K :=
  have := charP_of_injective_ringHom
    (f := ((valuativeResidueFieldEquiv K).symm : K →+* 𝓀[K⸨X⸩]))
    (valuativeResidueFieldEquiv K).symm.injective (ringChar K)
  ringChar.eq _ _

/-- **`𝔽_q((X))` is a nonarchimedean local field.** For a finite field `K`, the Laurent series
`K⸨X⸩`, with their `X`-adic topology and valuation, form a nonarchimedean local field. -/
instance isNonarchimedeanLocalField [Finite K] : IsNonarchimedeanLocalField K⸨X⸩ := by
  have : Finite (K[X] ⧸ (Polynomial.idealX K).asIdeal) := by
    have h : (Polynomial.idealX K).asIdeal = Ideal.span {Polynomial.X - Polynomial.C 0} := by
      simp
    rw [h]
    exact Finite.of_equiv K (Polynomial.quotientSpanXSubCAlgEquiv (0 : K)).toEquiv.symm
  have : LocallyCompactSpace K⸨X⸩ :=
    (_root_.LaurentSeries.comparePkg K).symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  exact ⟨⟩

end TauCeti.LaurentSeries
