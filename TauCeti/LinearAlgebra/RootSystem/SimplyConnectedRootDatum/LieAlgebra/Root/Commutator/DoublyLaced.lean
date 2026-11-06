/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.RingTheory.Nilpotent.RootString.Basic
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# The doubly-laced Chevalley commutator formula

For the pinned root vectors on a Kostant-stable lattice, this file proves the Chevalley
commutator formula when the root string consists of `β`, `α + β`, `2α + β` and there is no
root `α + 2β`. The coefficients are the native integer structure constants:
`c₁₁ = N_{α,β}` and `c₂₁ = N_{α,β} N_{α,α+β} / 2`. The division is exact in the integers;
no factorial is inverted in the value ring. The result therefore holds over every commutative
ring, including characteristic two, and for any Kostant-stable lattice with nilpotent simple
root operators.

The proof specializes `TauCeti.baseChangeExp_conj_of_commutator_eq_two_nsmul` to the pinned
Chevalley system, discharging its bracket hypotheses from the integral root datum. The operator
translation follows
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_lie_eq`;
here the all-root maps act directly on the scalar-extended lattice rather than on scheme points.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, with the convention
  `⁅x, y⁆ = x y x⁻¹ y⁻¹`.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid}

private theorem doublyLaced_vanishing_brackets {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root) :
    ⁅t.chevalleySystem ht α, t.chevalleySystem ht δ⁆ = 0 ∧
      ⁅t.chevalleySystem ht β, t.chevalleySystem ht γ⁆ = 0 := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hlin := (t.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root'
    (i := α) (j := β) ⟨γ, hγ⟩
  constructor
  · refine lie_chevalleySystem_eq_zero hαδ fun hz => ?_
    have hs : ∑ i : Fin 2, (![3, 1] : Fin 2 → ℤ) i •
        ![(t.simplyConnectedRootDatum ht).root α,
          (t.simplyConnectedRootDatum ht).root β] i = 0 := by
      calc _ = (t.simplyConnectedRootDatum ht).root α +
            (t.simplyConnectedRootDatum ht).root δ := by
              simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                one_smul, hδ, hγ]
              module
           _ = 0 := hz
    have := (Fintype.linearIndependent_iff.mp hlin _ hs) 1
    norm_num at this
  · refine lie_chevalleySystem_eq_zero hβγ fun hz => ?_
    have hs : ∑ i : Fin 2, (![1, 2] : Fin 2 → ℤ) i •
        ![(t.simplyConnectedRootDatum ht).root α,
          (t.simplyConnectedRootDatum ht).root β] i = 0 := by
      calc _ = (t.simplyConnectedRootDatum ht).root β +
            (t.simplyConnectedRootDatum ht).root γ := by
              simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                one_smul, hγ]
              module
           _ = 0 := hz
    have := (Fintype.linearIndependent_iff.mp hlin _ hs) 0
    norm_num at this

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- The Chevalley commutator formula for the roots `α + β` and `2α + β`, with the native
structure constants and the exact integral coefficient `N_{α,β} N_{α,α+β} / 2`. -/
theorem commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hαδ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβγ : (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root γ ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
          (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (Multiplicative.ofAdd
            (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
              (u ^ 2 * v))) := by
  obtain ⟨hil, hjk⟩ := doublyLaced_vanishing_brackets hγ hδ hαδ hβγ
  let e := t.chevalleySystem ht
  let X := fun η => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e η))
  let c := t.structureConstant ht α β
  let d := t.structureConstant ht α β * t.structureConstant ht α γ / 2
  -- Translate the two root-string brackets to the rational operator algebra.
  have hxy : X α * X β = X β * X α + c • X γ :=
    mul_eq_mul_add_zsmul_of_lie_eq ρ (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
  have hdiv : 2 * d = c * t.structureConstant ht α γ :=
    Int.mul_ediv_cancel' (two_dvd_structureConstant_mul_structureConstant hγ)
  have hxz : X α * (c • X γ) = (c • X γ) * X α + 2 • (d • X δ) := by
    have hb : c • ⁅e α, e γ⁆ = (2 * d) • e δ := by
      rw [lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul, hdiv]
    simpa only [one_zsmul, one_mul] using
      (zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
        (p := 1) (q := c) (r := d) (n := 2) (by simpa using hb))
  have hxw : Commute (X α) (d • X δ) :=
    (commute_of_lie_eq_zero ρ hil).smul_right d
  have hyz : Commute (X β) (c • X γ) :=
    (commute_of_lie_eq_zero ρ hjk).smul_right c
  have hyw : Commute (X β) (d • X δ) :=
    hyz.of_commutator_eq_of_commutator_eq_smul_left hxy
      (by simpa only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat] using hxz)
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0))
  -- Integral divided powers let the exponential identity descend to every value ring.
  have hstable (k : ℤ) (η : Fin t.numRoots) (n : ℕ) :
      ∀ w ∈ M, Associative.dividedPower n (k • X η) • w ∈ M := by
    intro w hw
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil η n w hw) _
  have hcomm := commute_baseChangeExp M hyw
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil β) (hstable d δ) v (u ^ 2 * v)
  have hconj := baseChangeExp_conj_of_commutator_eq_two_nsmul M hxy hxz hxw hyz
    (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
    ((isNilpotent_apply_ι_chevalleySystem ρ hnil γ).smul c)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil α)
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil β)
    (hstable c γ) (hstable d δ) u v
  -- Move the β factor to the right and cancel it against its inverse.
  have hyzExp := commute_baseChangeExp M hyz
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil β) (hstable c γ) v (u * v)
  rw [hyzExp.eq, mul_assoc (baseChangeExp (c • X γ) M (hstable c γ) (u * v)),
    hcomm.eq, ← mul_assoc] at hconj
  rw [commutatorElement_def,
    ← (chevalleyRootSubgroup ρ M hM hnil α A).map_inv,
    ← (chevalleyRootSubgroup ρ M hM hnil β A).map_inv,
    ← ofAdd_neg, ← ofAdd_neg]
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [hconj, mul_assoc,
    ← baseChangeExp_add _ M _ (isNilpotent_apply_ι_chevalleySystem ρ hnil β),
    add_neg_cancel, baseChangeExp_zero _ M _ (isNilpotent_apply_ι_chevalleySystem ρ hnil β),
    mul_one, baseChangeExp_zsmul c M _ _
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ),
    baseChangeExp_zsmul d M _ _ (isNilpotent_apply_ι_chevalleySystem ρ hnil δ)]

end

end TauCeti.DynkinType
