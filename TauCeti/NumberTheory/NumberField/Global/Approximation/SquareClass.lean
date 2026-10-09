/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Algebra.GroupWithZero.Squares
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.Algebra.Group.Even

/-!
# Weak approximation in local square classes

A nonzero element of a number field can realize independently prescribed square classes at
finitely many finite and real places. The finite-place statement includes dyadic places.
This is the coefficientwise approximation needed to construct quadratic forms with prescribed
local behavior.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open Filter IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped Topology

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- One global field unit realizes any prescribed square classes at finitely many finite and
real places. The quotients are read in the actual completions and in the real embeddings. -/
theorem exists_fieldUnit_isSquare_div_at_places
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset {w : InfinitePlace K // w.IsReal})
    (a : ∀ v : S, (v.1.adicCompletion K)ˣ) (b : T → ℝˣ) :
    ∃ x : Kˣ,
      (∀ v : S, IsSquare
        (algebraMap K (v.1.adicCompletion K) (x : K) / (a v : v.1.adicCompletion K))) ∧
      (∀ w : T, IsSquare (embedding_of_isReal w.1.2 (x : K) / (b w : ℝ))) := by
  classical
  let target := ((fun v : S => (a v : v.1.adicCompletion K)), fun w : T => (b w : ℝ))
  have hf (v : S) : ∀ᶠ y in 𝓝 target,
      y.1 v ≠ 0 ∧ IsSquare (y.1 v / (a v : v.1.adicCompletion K)) := by
    let _ : Finite (𝓞 K ⧸ v.1.asIdeal) :=
      Ring.HasFiniteQuotients.finiteQuotient v.1.ne_bot
    have : CharZero (v.1.adicCompletion K) :=
      charZero_of_injective_algebraMap (algebraMap K (v.1.adicCompletion K)).injective
    have hcont : Continuous (fun y : (∀ v : S, v.1.adicCompletion K) × (T → ℝ) => y.1 v) :=
      (continuous_apply v).comp continuous_fst
    have hopen : IsOpen {u : (v.1.adicCompletion K)ˣ | IsSquare u} := by
      simpa only [← square_eq_range_powMonoidHom, Subgroup.coe_square]
        using isOpen_range_powMonoidHom (two_ne_zero' (v.1.adicCompletion K))
    exact Filter.Tendsto.eventually_isSquare_div_of_isOpen_squares
      (f := fun y : (∀ v : S, v.1.adicCompletion K) × (T → ℝ) => y.1 v)
      hcont.continuousAt hopen (a v).ne_zero
  have hr (w : T) : ∀ᶠ y in 𝓝 target, y.2 w ≠ 0 ∧ IsSquare (y.2 w / (b w : ℝ)) := by
    have hcont : Continuous (fun y : (∀ v : S, v.1.adicCompletion K) × (T → ℝ) =>
        y.2 w / (b w : ℝ)) :=
      ((continuous_apply w).comp continuous_snd).div_const _
    have hpos : ∀ᶠ y in 𝓝 target, 0 < y.2 w / (b w : ℝ) :=
      hcont.continuousAt.eventually
        (isOpen_Ioi.mem_nhds (by
          simpa only [target, div_self (b w).ne_zero, Set.mem_Ioi]
            using (zero_lt_one : (0 : ℝ) < 1)))
    filter_upwards [hpos] with y hy
    exact ⟨fun hzero => by simp [hzero] at hy, Real.isSquare_iff.mpr hy.le⟩
  have he := (eventually_all.mpr hf).and (eventually_all.mpr hr)
  obtain ⟨y, hy, x, rfl⟩ := mem_closure_iff_nhds.mp
    ((denseRange_algebraMap_embedding_of_isReal S T) target) _ he
  by_cases hx : x = 0
  · have hS : IsEmpty S := ⟨fun v => (hy.1 v).1 (by simp [hx])⟩
    have hT : IsEmpty T := ⟨fun w => (hy.2 w).1 (by simp [hx])⟩
    exact ⟨1, fun v => isEmptyElim v, fun w => isEmptyElim w⟩
  · exact ⟨Units.mk0 x hx, fun v => (hy.1 v).2, fun w => (hy.2 w).2⟩

/-- Local coefficient square classes whose products agree with a global unit can be realized
by global coefficients whose product is exactly that unit. -/
theorem exists_coefficients_prod_eq_isSquare_div_at_places
    {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset {w : InfinitePlace K // w.IsReal}) (d : Kˣ)
    (a : ∀ v : S, Fin (n + 1) → (v.1.adicCompletion K)ˣ)
    (b : T → Fin (n + 1) → ℝˣ)
    (ha : ∀ v : S, IsSquare (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom d /
      ∏ i, a v i))
    (hb : ∀ w : T, IsSquare (Units.map (embedding_of_isReal w.1.2).toMonoidHom d /
      ∏ i, b w i)) :
    ∃ c : Fin (n + 1) → Kˣ, (∏ i, c i) = d ∧
      (∀ (v : S) i, IsSquare
        (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom (c i) / a v i)) ∧
      (∀ (w : T) i, IsSquare
        (Units.map (embedding_of_isReal w.1.2).toMonoidHom (c i) / b w i)) := by
  classical
  choose c hc hr using fun i : Fin n => exists_fieldUnit_isSquare_div_at_places S T
    (fun v => a v i.castSucc) (fun w => b w i.castSucc)
  let e : Fin (n + 1) → Kˣ := Fin.snoc c (d / ∏ i, c i)
  have he : (∏ i, e i) = d := by
    simp [e, Fin.prod_univ_castSucc]
  refine ⟨e, he, ?_, ?_⟩
  · intro v i
    have hhead (j : Fin n) : IsSquare
        (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom (e j.castSucc) /
          a v j.castSucc) := by
      apply isSquare_units_val_iff.mp
      -- Expand the square witness to normalize the scalar and unit coercions.
      simpa [e, IsSquare] using hc j v
    refine Fin.lastCases ?_ hhead i
    have hp : IsSquare ((∏ i, Units.map
        (algebraMap K (v.1.adicCompletion K)).toMonoidHom (e i)) / ∏ i, a v i) := by
      rw [← map_prod, he]
      exact ha v
    exact isSquare_div_last_of_isSquare_div_prod
      (a := fun i => Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom (e i))
      (b := a v) hhead hp
  · intro w i
    have hhead (j : Fin n) : IsSquare
        (Units.map (embedding_of_isReal w.1.2).toMonoidHom (e j.castSucc) / b w j.castSucc) := by
      apply isSquare_units_val_iff.mp
      -- Expand the square witness to normalize the scalar and unit coercions.
      simpa [e, IsSquare] using hr j w
    refine Fin.lastCases ?_ hhead i
    have hp : IsSquare ((∏ i, Units.map
        (embedding_of_isReal w.1.2).toMonoidHom (e i)) / ∏ i, b w i) := by
      rw [← map_prod, he]
      exact hb w
    exact isSquare_div_last_of_isSquare_div_prod
      (a := fun i => Units.map (embedding_of_isReal w.1.2).toMonoidHom (e i))
      (b := b w) hhead hp

end TauCeti.GlobalNumberFields
