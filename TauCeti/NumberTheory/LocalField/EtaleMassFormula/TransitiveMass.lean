/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol.GaloisSet
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount

/-!
# The transitive étale mass by residue degree

For a nonarchimedean local field `K` with residue cardinality `q` and positive integers `f` and `e`,
the labelled Galois sets of size `f * e` whose splitting symbol is the singleton `{(f, e)}` are
transitive and have mass `1 / (f * q ^ (f * (e - 1)))`
(`TauCeti.etaleMass_isTransitive_splittingSymbol`).

A Galois set of size `f * e` has splitting symbol `{(f, e)}` precisely when it is transitive and the
fixed field of the stabilizer of `0` has residue degree `f`
(`TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff_of_mul`). Applying the transitive bridge
`TauCeti.GaloisSet.tsum_isTransitive` to the weight equal to `q ^ (-d(L))` on subextensions of
residue degree `f` and `0` elsewhere reduces the unnormalized sum to `(f * e - 1)!` times
`TauCeti.tsum_inertiaDegree_eq`, giving `(f * e - 1)! * e / q ^ (f * (e - 1))`
(`TauCeti.tsum_splittingSymbol_eq_singleton`). Dividing by `(f * e)! = f * e * (f * e - 1)!` yields
the mass `1 / (f * q ^ (f * (e - 1)))`.

## Main results

* `TauCeti.tsum_splittingSymbol_eq_singleton`: the unnormalized discriminant-weighted sum over
  labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}` equals
  `(f * e - 1)! * (e / q ^ (f * (e - 1)))`, including `e = 0`.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: for `f ≠ 0` and `e ≠ 0`, the mass of the
  labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}` is
  `1 / (f * q ^ (f * (e - 1)))`.
* `TauCeti.etaleMass_splittingSymbol_singleton_one` and
  `TauCeti.etaleMass_splittingSymbol_one_singleton`: the unramified (`e = 1`) and totally ramified
  (`f = 1`) cases.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Unnormalized sum over transitive Galois sets of a given splitting symbol.** For `f ≠ 0`, the
labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}` satisfy
`∑_ρ q ^ (-d(ρ)) = (f * e - 1)! * (e / q ^ (f * (e - 1)))`, where `q` is the residue cardinality of
`K`. For `e = 0` both sides vanish. -/
theorem tsum_splittingSymbol_eq_singleton {f : ℕ} (hf : f ≠ 0) (e : ℕ) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((f * e - 1).factorial : ℝ≥0∞) *
        (e / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  rcases eq_or_ne e 0 with rfl | he
  · have : IsEmpty {ρ : GaloisSet K (f * 0) // ρ.splittingSymbol = {(f, 0)}} :=
      ⟨fun ρ ↦ Multiset.singleton_ne_zero (f, 0)
        ((ρ.1.splittingSymbol_eq_zero_iff.2 (mul_zero f)).symm.trans ρ.2).symm⟩
    simp
  · let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos (Nat.pos_of_ne_zero hf) (Nat.pos_of_ne_zero he)⟩
    let s₁ : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
      {ρ | (letI := ρ.1.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree) = f}
    let ε : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ s₁ :=
      (Equiv.subtypeEquivRight fun ρ ↦ ρ.splittingSymbol_eq_singleton_iff_of_mul hf i₀).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
    let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
      {L | L.inertiaDegree = f}.indicator fun L ↦
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent
    let s₂ : Set {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} :=
      {L | L.1.inertiaDegree = f}
    let δ : s₂ ≃
        {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun L : IntermediateField K (SeparableClosure K) ↦ Module.finrank K L = f * e)
        (fun L ↦ L.inertiaDegree = f)
    rw [← ε.symm.tsum_eq]
    have hε : ∀ ρ : s₁,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (ε.symm ρ).1.discriminantExponent =
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent := fun _ ↦ rfl
    rw [tsum_congr hε, _root_.tsum_subtype s₁ fun ρ ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent]
    have hind : ∀ ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        s₁.indicator (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) ρ =
          (letI := ρ.1.mulAction
          g (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
      intro ρ
      let := ρ.1.mulAction
      simp only [g, s₁, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with h
      · rw [ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀]
      · rfl
    rw [tsum_congr hind, GaloisSet.tsum_isTransitive i₀ g]
    congr 1
    have hg : ∀ L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
        g L.1 =
          s₂.indicator (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent) L := by
      intro L
      simp only [g, s₂, Set.indicator_apply, Set.mem_ofPred_eq]
    have hδ : ∀ x : s₂,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ x.1.1.discriminantExponent =
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (δ x).1.discriminantExponent := fun _ ↦ rfl
    rw [tsum_congr hg, ← _root_.tsum_subtype s₂, tsum_congr hδ,
      δ.tsum_eq fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent]
    exact tsum_inertiaDegree_eq hf e

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `f ≠ 0` and `e ≠ 0`, the
labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
`1 / (f * q ^ (f * (e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol {f e : ℕ} (hf : f ≠ 0) (he : e ≠ 0) :
    ((f * e).factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  rw [tsum_splittingSymbol_eq_singleton hf e]
  have hfac : ((f * e).factorial : ℝ≥0∞) =
      (f : ℝ≥0∞) * ((e : ℝ≥0∞) * ((f * e - 1).factorial : ℝ≥0∞)) := by
    rw [← Nat.mul_factorial_pred (mul_ne_zero hf he)]
    push_cast
    ring
  set c : ℝ≥0∞ := (e : ℝ≥0∞) * ((f * e - 1).factorial : ℝ≥0∞)
  set qpow : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))
  have hf0 : (f : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hf
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 he)
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  have hc_mul : ((f * e - 1).factorial : ℝ≥0∞) * ((e : ℝ≥0∞) * qpow⁻¹) = c * qpow⁻¹ := by
    simp only [c]
    ring
  rw [hfac, ENNReal.mul_inv (.inl hf0) (.inr hc0), div_eq_mul_inv (e : ℝ≥0∞) qpow, hc_mul,
    mul_assoc, ← mul_assoc c⁻¹, ENNReal.inv_mul_cancel hc0 hctop, one_mul,
    ← ENNReal.mul_inv (.inl hf0) (.inl (ENNReal.natCast_ne_top f)), ← one_div]

/-- **The unramified transitive mass**: for `f ≠ 0`, the Galois sets of size `f` with splitting
symbol `{(f, 1)}` have mass `1 / f`. They are the labellings of the unramified extension of degree
`f`, whose automorphism group has order `f` and whose discriminant exponent is `0`. -/
theorem etaleMass_splittingSymbol_singleton_one {f : ℕ} (hf : f ≠ 0) :
    (f.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K f // ρ.splittingSymbol = {(f, 1)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (f : ℝ≥0∞) := by
  have h := etaleMass_isTransitive_splittingSymbol (K := K) hf one_ne_zero
  rw [mul_one, tsub_self, mul_zero, pow_zero, mul_one] at h
  exact h

/-- **The totally ramified transitive mass**: for `e ≠ 0`, the Galois sets of size `e` with
splitting symbol `{(1, e)}` have mass `1 / q ^ (e - 1)`. -/
theorem etaleMass_splittingSymbol_one_singleton {e : ℕ} (he : e ≠ 0) :
    (e.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K e // ρ.splittingSymbol = {(1, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (e - 1) := by
  have h := etaleMass_isTransitive_splittingSymbol (K := K) one_ne_zero he
  rw [one_mul, one_mul, Nat.cast_one, one_mul] at h
  exact h

end TauCeti
