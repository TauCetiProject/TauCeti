/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortLong

/-!
# The ordered short–long G₂ element commutator

The four-factor root-collection identity puts the long-root factor first. Moving it to the
right changes the highest-root coefficient. This file proves the element-commutator formula
in increasing root height, with factors at α + β, 2α + β, 3α + β and 3α + 2β.

For the integral coefficients c, d, a, b in
`chevalleyRootSubgroup_mul_of_g2_short_long`, the highest-root coefficient is 2b, not b.
The correction follows from the class-two relation for β and 3α + β and the Jacobi identity.
All divisions take place in ℤ before scalar extension, so the formula includes characteristics
two and three and nonreduced value rings. No faithfulness or weight-basis assumption is needed.

The proof consumes the native collection identity and
`commutatorElement_chevalleyRootSubgroup_of_lie_eq` rather than reconstructing exponentials.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2. The commutator convention here is
  x y x⁻¹ y⁻¹, not Carter's x⁻¹ y⁻¹ x y.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {ht : G2.Valid} {α β γ δ ε ζ : Fin G2.numRoots}

private theorem short_long_extra_vanishing
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ) :
    let e := G2.chevalleySystem ht
    ⁅e β, e δ⁆ = 0 ∧ ⁅e β, e ζ⁆ = 0 := by
  let P := G2.simplyConnectedRootDatum ht
  let : P.IsReduced := G2.isReduced_simplyConnectedRootDatum ht
  have htwo : P.root β + P.root δ = (2 : ℕ) • P.root γ := by rw [hδ, hγ]; abel
  have hthree : P.root β + P.root ζ = (3 : ℕ) • P.root γ := by
    rw [hζ, hδ, hγ]
    abel
  constructor
  · apply lie_chevalleySystem_eq_zero
    · rw [htwo]
      exact P.nsmul_notMem_range_root
    · rw [htwo]
      simpa only [ofNat_zsmul] using
        smul_ne_zero (by decide : (2 : ℤ) ≠ 0) (P.ne_zero γ)
  · apply lie_chevalleySystem_eq_zero
    · rw [hthree]
      exact P.nsmul_notMem_range_root
    · rw [hthree]
      simpa only [ofNat_zsmul] using
        smul_ne_zero (by decide : (3 : ℤ) ≠ 0) (P.ne_zero γ)

private theorem short_long_highest_coefficient
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    a * N β ε = b := by
  let e := G2.chevalleySystem ht
  let N := G2.structureConstant ht
  let c := N α β
  let d := c * (N α γ / 2)
  let a := d * (N α δ / 3)
  let b := d * c * (N δ γ / 3)
  obtain ⟨_, hαδ, hδγ⟩ := lie_chevalleySystem_three_step hγ hδ hε hζ
  have hβδ := (short_long_extra_vanishing hγ hδ hζ).1
  have hβε : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root β + (G2.simplyConnectedRootDatum ht).root ε := by
    rw [hζ, hε, hδ, hγ]
    abel
  have hjac : (3 * (a * N β ε)) • e ζ = (3 * b) • e ζ := by
    calc
      _ = ⁅e β, d • ⁅e α, e δ⁆⁆ := by
        rw [hαδ, lie_smul, lie_chevalleySystem_eq_structureConstant_zsmul hβε, smul_smul]
        congr 1
        ring
      _ = d • (⁅⁅e β, e α⁆, e δ⁆ + ⁅e α, ⁅e β, e δ⁆⁆) := by
        rw [lie_smul, leibniz_lie]
      _ = (d * c) • ⁅e δ, e γ⁆ := by
        rw [hβδ, lie_zero, add_zero, ← lie_skew (e β) (e α),
          lie_chevalleySystem_eq_structureConstant_zsmul hγ, neg_lie, smul_lie,
          ← lie_skew (e δ) (e γ), smul_neg, smul_smul, smul_neg]
      _ = _ := hδγ
  have he : e ζ ≠ 0 := (G2.isSl2Triple_chevalleySystem ht ζ).e_ne_zero
  have hc : ((3 * (a * N β ε) : ℤ) : ℚ) = ((3 * b : ℤ) : ℚ) :=
    (smul_left_injective ℚ he) (by simpa only [Int.cast_smul_eq_zsmul] using hjac)
  have hc' : 3 * (a * N β ε) = 3 * b := by exact_mod_cast hc
  exact mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) hc'

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ z ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ w ∈ M, ρ z w ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- The ordered short–long G₂ element-commutator formula on a Kostant-stable lattice.
The factors are in increasing root height. The highest-root coefficient is twice the
coefficient in the root-collection formula, with the divisions performed in ℤ. -/
theorem commutatorElement_chevalleyRootSubgroup_of_g2_short_long
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let x := fun i w => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
    ⁅x α u, x β v⁆ =
      x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
        x ε ((a : A) * (u ^ 3 * v)) * x ζ ((2 * b : ℤ) * (u ^ 3 * v ^ 2)) := by
  let N := G2.structureConstant ht
  let c := N α β
  let d := c * (N α γ / 2)
  let a := d * (N α δ / 3)
  let b := d * c * (N δ γ / 3)
  let x := fun i (w : A) => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
  -- Keep the local coefficients opaque to group associativity simplification below, which
  -- would otherwise also reassociate the products inside their integer definitions.
  change ⁅x α u, x β v⁆ = x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
    x ε ((a : A) * (u ^ 3 * v)) * x ζ ((2 * b : ℤ) * (u ^ 3 * v ^ 2))
  -- Conjugation by the long-root factor fixes three factors and corrects the fourth.
  obtain ⟨_, _, hβγ, _, _, _, hεζ⟩ :=
    lie_chevalleySystem_g2_three_step_vanishing ht hγ hδ hε hζ
  obtain ⟨hβδ, hβζ⟩ := short_long_extra_vanishing hγ hδ hζ
  have hcomm (i j : Fin G2.numRoots)
      (hij : ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht j⁆ = 0) (s t : A) :
      Commute (x i s) (x j t) := by
    apply Units.ext
    simpa only [x, Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd] using
      (commute_baseChangeExp M (commute_of_lie_eq_zero ρ hij)
        (dividedPower_chevalleySystem_smul_mem ρ M hM hnil i)
        (dividedPower_chevalleySystem_smul_mem ρ M hM hnil j) s t).eq
  have hconj (i : Fin G2.numRoots)
      (hβi : ⁅G2.chevalleySystem ht β, G2.chevalleySystem ht i⁆ = 0) (s : A) :
      MulAut.conj (x β v) (x i s) = x i s := by
    rw [MulAut.conj_apply, (hcomm β i hβi v s).eq, mul_inv_cancel_right]
  have hβε : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root β + (G2.simplyConnectedRootDatum ht).root ε := by
    rw [hζ, hε, hδ, hγ]
    abel
  have hconjε : MulAut.conj (x β v) (x ε ((a : A) * (u ^ 3 * v))) =
      x ε ((a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) := by
    rw [conj_eq_commutatorElement_mul,
      commutatorElement_chevalleyRootSubgroup_of_lie_eq ρ M hM hnil
        (lie_chevalleySystem_eq_structureConstant_zsmul hβε) hβζ hεζ]
    have hc : (N β ε : A) * (v * ((a : A) * (u ^ 3 * v))) =
        (b : A) * (u ^ 3 * v ^ 2) := by
      have hab : (a : A) * (N β ε : A) = (b : A) := by
        have hab : a * N β ε = b := short_long_highest_coefficient hγ hδ hε hζ
        rw [← Int.cast_mul, hab]
      calc
        _ = ((a : A) * (N β ε : A)) * (u ^ 3 * v ^ 2) := by ring
        _ = _ := by rw [hab]
    rw [hc, (hcomm ε ζ hεζ _ _).eq]
  have hprod : x α u * x β v = x β v * x γ ((c : A) * (u * v)) *
      x δ ((d : A) * (u ^ 2 * v)) * x ε ((a : A) * (u ^ 3 * v)) *
        x ζ ((b : A) * (u ^ 3 * v ^ 2)) * x α u :=
    chevalleyRootSubgroup_mul_of_g2_short_long ht ρ M hM hnil hγ hδ hε hζ A u v
  have hstart : ⁅x α u, x β v⁆ = MulAut.conj (x β v)
      (x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
        x ε ((a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2))) := by
    rw [commutatorElement_def, hprod, MulAut.conj_apply]
    group
  have hdouble : x ζ ((b : A) * (u ^ 3 * v ^ 2)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) =
      x ζ ((2 * b : ℤ) * (u ^ 3 * v ^ 2)) := by
    rw [← map_mul, ← ofAdd_add]
    congr 2
    push_cast
    ring
  -- Collect the two highest-root parameters after distributing conjugation.
  rw [hstart, map_mul, map_mul, map_mul, hconj γ hβγ, hconj δ hβδ, hconjε, hconj ζ hβζ]
  simpa only [mul_assoc] using congrArg
    (fun z => x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
      x ε ((a : A) * (u ^ 3 * v)) * z) hdouble

end

end TauCeti.DynkinType
