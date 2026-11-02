/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
import TauCeti.NumberTheory.LocalField.Squares
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Algebra.Group.Units.Basic

/-!
# A global nonsquare at prescribed places

For finitely many finite and real places of a number field, one field element is a nonsquare
in every corresponding completion. At a finite place its valuation is prescribed to be one;
at a real place its image is negative. At every other real place it is positive, hence a square.
The simultaneous choice uses weak approximation.

This supplies the radicand in the unprescribed form of Hilbert sign prescription: at each
selected place the associated quadratic extension is a field rather than a split algebra. With
no real place selected, it supplies the radicand `β` of the correction planes `⟨1, -β⟩` and
`⟨α, -αβ⟩` in the construction of a form with prescribed local behavior, which must be a square
at every archimedean place.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:19 and 72:1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-- Given finite sets of finite and real places, there is one global unit that is a nonsquare
in each of their completions. At each selected finite place it has valuation one, at each
selected real place it is negative, and at every other real place it is positive. -/
theorem exists_fieldUnit_not_isSquare_at_places
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset {w : InfinitePlace K // w.IsReal}) :
    ∃ a : Kˣ,
      (∀ v ∈ S, v.valuation K (a : K) = WithZero.exp (-1) ∧
        ¬ IsSquare (v.unitAtFinitePlace a)) ∧
      (∀ w ∈ T, embedding_of_isReal w.2 (a : K) < 0 ∧
        ¬ IsSquare (unitAtRealPlace w a)) ∧
      ∀ w ∉ T, 0 < embedding_of_isReal w.2 (a : K) := by
  classical
  let s : {w : InfinitePlace K // w.IsReal} → ℤˣ := fun w => if w ∈ T then -1 else 1
  obtain ⟨a, ha, hs⟩ := GlobalNumberFields.exists_fieldUnit_valuation_eq_and_signHom_eq
    S (fun _ => -1) s
  refine ⟨a, fun v hv => ⟨ha v hv, ?_⟩, fun w hw => ?_, fun w hw =>
    (GlobalNumberFields.signHom_apply_eq_one_iff a w).mp (by simpa [s, hw] using congrFun hs w)⟩
  · -- Valuation one makes the local image a uniformizer, hence a nonsquare.
    let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have hval : Valued.v (v.unitAtFinitePlace a : v.adicCompletion K) = WithZero.exp (-1) := by
      rw [v.unitAtFinitePlace_apply, algebraMap_adicCompletion, Function.comp_apply,
        v.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply, ha v hv]
    have hπ : TauCeti.IsUniformizer (v.adicCompletion K) (v.unitAtFinitePlace a) :=
      v.isUniformizer_iff_valued_eq_exp_neg_one.2 hval
    exact TauCeti.not_isSquare_of_isUniformizer hπ
  have hneg : embedding_of_isReal w.2 (a : K) < 0 :=
    (GlobalNumberFields.signHom_apply_eq_neg_one_iff a w).mp
      (by simpa [s, hw] using (congrFun hs w))
  refine ⟨hneg, ?_⟩
  exact TauCeti.isSquare_units_val_iff.not.mp
    (not_isSquare_of_neg (by simpa only [unitAtRealPlace_apply] using hneg))

end TauCeti.NumberField.QuadraticForm
