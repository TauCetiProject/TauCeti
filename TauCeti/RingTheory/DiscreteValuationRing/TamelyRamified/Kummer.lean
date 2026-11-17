/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.TFAE
import TauCeti.Algebra.Algebra.Hom
import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Kummer
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Unramified.Field

/-!
# Kummer characterization of tamely ramified extensions of a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension. Combining the Kummer case of Abhyankar's lemma in
`TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Kummer` (Stacks, Lemma 15.116.4 (0BRM))
with the reverse implication in `TauCeti.RingTheory.DiscreteValuationRing.Kummer` gives the
three-way Kummer characterization of tame ramification (Stacks, Lemma 15.116.7 (0EXW)): `L` is
tamely ramified with respect to `A` if and only if `L` embeds into a finite separable extension of
some tame Kummer base `K(π ^ (1 / e))` that is unramified with respect to the integral closure of
`A` in `K(π ^ (1 / e))`, and if and only if there is a base exponent `e₀` invertible in the residue
field of `A` such that every tame multiple `e₀ * d` admits such an unramified extension.

## Usage notes

* In `isTamelyRamifiedWRT_tfae` and `isTamelyRamifiedWRT_iff_exists_kummer`, the Kummer base
  `K(π ^ (1 / e))` is represented as `K⟮β⟯` inside an `L`-overfield `E : Type u` in `L`'s universe.

## Main results

* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae` and
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`: all three equivalent clauses of the
  Kummer characterization of tame ramification (Stacks, Lemma 15.116.7 (0EXW)).

## References

* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
-/

public section

universe u

open scoped TensorProduct
open IsLocalRing _root_.IntermediateField

namespace TauCeti.Algebra

/-- Constructing the finite separable unramified Kummer witness of exponent `n` from tame
ramification when `n > 0` is divisible by every maximal ideal's ramification index. -/
private theorem exists_unramified_kummer_of_forall_ramificationIdx_dvd
    {A K : Type*} {L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
      (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
      (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
      β ^ n = algebraMap A E π ∧
        FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
        IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  let Ω : Type u := AlgebraicClosure L
  have : IsScalarTower A L Ω := .to₁₃₄ A K L Ω
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  let β : L⟮α⟯ := AdjoinSimple.gen L α
  have : IsScalarTower A K L⟮α⟯ := .to₁₂₄ A K L L⟮α⟯
  have hβ : β ^ n = algebraMap A L⟮α⟯ π := AdjoinSimple.gen_pow_eq_algebraMap_iff.mpr hα
  have hβK : AdjoinSimple.gen K β ^ n = algebraMap A K⟮β⟯ π :=
    AdjoinSimple.gen_pow_eq_algebraMap_iff.mpr hβ
  have hgenK : K⟮AdjoinSimple.gen K β⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top β
  have hgenL : L⟮algebraMap K⟮β⟯ L⟮α⟯ (AdjoinSimple.gen K β)⟯ = ⊤ := by
    rw [AdjoinSimple.algebraMap_gen]
    exact _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  obtain ⟨hDVR, hunr⟩ := h.isUnramifiedWRT_of_pow_eq_of_irreducible hπ hβK hgenK hgenL hdvd
  have hintL : IsIntegral L β :=
    IsIntegral.of_pow hn (by rw [hβ, IsScalarTower.algebraMap_apply A K L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯]; exact isIntegral_algebraMap)
  -- `K(β) ⊗[K] L` maps onto `L(β) = L(α)` via `adjoinBaseChangeTensorLift`.
  let := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
  let ι : L⟮β⟯ →ₐ[K⟮β⟯] L⟮α⟯ :=
    { (L⟮β⟯).val.toRingHom with
      commutes' := fun x ↦ by
        simp [AlgHom.algebraMap_toAlgebra_apply, IntermediateField.algebraMap_apply] }
  let ψ : K⟮β⟯ ⊗[K] L →ₐ[K⟮β⟯] L⟮α⟯ :=
    ι.comp (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L β)
  have hι : Function.Surjective ι := fun y ↦
    ⟨⟨y, (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α : L⟮β⟯ = ⊤) ▸ mem_top⟩, rfl⟩
  have hψ : Function.Surjective ψ :=
    hι.comp (TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hintL)
  obtain ⟨_, hsep⟩ := ψ.finiteDimensional_and_isSeparable_of_surjective_tensorProduct hψ
  exact ⟨L⟮α⟯, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, β, hDVR, hβ, inferInstance, hsep, hunr⟩

variable {A : Type*} (K : Type*) (L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Kummer characterization of tamely ramified extensions of a discrete valuation ring.**
Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension. The following are equivalent (Stacks, Lemma 15.116.7):
1. `L` is tamely ramified with respect to `A`;
2. there exist `e` invertible in the residue field of `A` and a finite separable extension `E` of
   `K(π ^ (1 / e))` containing `L` that is unramified with respect to the integral closure of `A`
   in `K(π ^ (1 / e))`;
3. there exists `e₀` invertible in the residue field of `A` such that for every `d` invertible in
   the residue field of `A`, there is a finite separable extension `E` of `K(π ^ (1 / (e₀ * d)))`
   containing `L` that is unramified with respect to the integral closure of `A` in
   `K(π ^ (1 / (e₀ * d)))`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWRT_tfae {π : A} (hπ : Irreducible π) :
    List.TFAE
      [IsTamelyRamifiedWRT A L,
        ∃ (e : ℕ) (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E)
          (_ : Algebra L E) (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
          (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
          IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A E π ∧
            FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
            IsUnramifiedWRT (integralClosure A K⟮β⟯) E,
        ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
          ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
            ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E)
              (_ : Algebra L E) (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
              (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
              β ^ (e₀ * d) = algebraMap A E π ∧
                FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
                IsUnramifiedWRT (integralClosure A K⟮β⟯) E] := by
  tfae_have 1 → 3 := fun h ↦ by
    obtain ⟨e₀, he₀, hdvd⟩ := h.exists_isUnit_forall_ramificationIdx_dvd K
    refine ⟨e₀, he₀, fun d hd ↦ ?_⟩
    have hed : IsUnit ((e₀ * d : ℕ) : A ⧸ maximalIdeal A) := by
      rw [Nat.cast_mul]
      exact he₀.mul hd
    let := Ideal.Quotient.field (maximalIdeal A)
    have hne : e₀ * d ≠ 0 := by
      rintro h0
      simp [h0] at hed
    exact exists_unramified_kummer_of_forall_ramificationIdx_dvd h hπ (Nat.pos_of_ne_zero hne)
      (fun P _ ↦ (hdvd P).trans (dvd_mul_right e₀ d))
  tfae_have 3 → 2 := by
    rintro ⟨e₀, he₀, h⟩
    obtain ⟨E, _, _, _, _, _, _, β, hDVR, hβ, hfin, hsep, hunr⟩ := h 1 (by simp)
    exact ⟨e₀, E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, β, hDVR, he₀, by simpa using hβ, hfin, hsep, hunr⟩
  tfae_have 2 → 1 := by
    rintro ⟨e, E, _, _, _, _, _, _, β, _, he, hβ, -, -, hunr⟩
    exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
      hπ he hβ hunr
  tfae_finish

/-- A finite separable extension `L` of the fraction field `K` of a discrete valuation ring `A`
with uniformizer `π` is tamely ramified with respect to `A` if and only if it embeds into a finite
separable extension `E` of some tame Kummer extension `K(π ^ (1 / e))` that is unramified with
respect to the integral closure of `A` in `K(π ^ (1 / e))`. -/
@[stacks 0EXW "(1) ↔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ (e : ℕ) (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E)
        (_ : Algebra L E) (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
        (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
        IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A E π ∧
          FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
          IsUnramifiedWRT (integralClosure A K⟮β⟯) E :=
  (isTamelyRamifiedWRT_tfae K L hπ).out 1 2

end TauCeti.Algebra
