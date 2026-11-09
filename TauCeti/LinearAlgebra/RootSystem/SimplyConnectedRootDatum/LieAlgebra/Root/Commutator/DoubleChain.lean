/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.DoublyLaced
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.RingTheory.Nilpotent.RootString.Basic

/-!
# The two-factor Chevalley commutator for a double root chain

For the pinned root vectors, if `γ = α + β` and `δ = 2α + β` outside type `G₂`, then

`⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ((N_{α,β} N_{α,γ} / 2) u² v)`.

The integer quotient in this formula is exact: `N_{α,γ} = ±2`. The formula holds on every
Kostant-stable lattice over every commutative value ring, including characteristic two.
No division is performed in the value ring. All bracket equations and vanishing conditions
are deduced from the pinned root datum, rather than assumed of a family of operators.

The proof applies the integral divided-power identity
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul` to the named root vectors.
The operator transport follows
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_lie_eq`, using
all-root divided-power stability rather than assuming that the roots are simple generators.
The element-commutator formula specializes
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq`, discharging
its non-root hypotheses from the double chain.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid}
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

-- Match tensor products to the integral algebra instance stored by the value-ring objects.
attribute [local instance high] Algebra.toModule

/-- The second iterated bracket in a double chain has its exact integral divided-power
coefficient. -/
private theorem lie_lie_chevalleySystem_double_chain (h : t ≠ .G2)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ) :
    ⁅t.chevalleySystem ht α, ⁅t.chevalleySystem ht α, t.chevalleySystem ht β⁆⁆ =
      (2 * (t.structureConstant ht α β * (t.structureConstant ht α γ / 2))) •
        t.chevalleySystem ht δ := by
  rw [lie_chevalleySystem_eq_structureConstant_zsmul hγ, lie_zsmul,
    lie_chevalleySystem_eq_structureConstant_zsmul hδ, smul_smul]
  rcases structureConstant_eq_two_or_eq_neg_two_of_double_chain h hγ hδ with hc | hc <;>
    simp [hc, mul_comm]

/-- Reordering two root-subgroup elements in a double chain produces the sum-root and
last-root factors, with the integral Chevalley coefficients. -/
theorem chevalleyRootSubgroup_mul_of_double_chain (h : t ≠ .G2)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) *
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A
          (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil δ A
          (.ofAdd (((t.structureConstant ht α β * (t.structureConstant ht α γ / 2) : ℤ) : A) *
            (u ^ 2 * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u) := by
  let c := t.structureConstant ht α β
  let d := t.structureConstant ht α β * (t.structureConstant ht α γ / 2)
  let x i := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht i))
  have hxy := mul_eq_mul_add_zsmul_of_lie_eq ρ
    (lie_chevalleySystem_eq_structureConstant_zsmul hγ)
  have hxz := zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
    (a := t.chevalleySystem ht α) (b := t.chevalleySystem ht γ)
    (b' := t.chevalleySystem ht δ) (p := 1) (q := c) (r := d) (n := 2) (by
      simpa only [c, d, one_mul, Nat.cast_ofNat,
        lie_chevalleySystem_eq_structureConstant_zsmul hγ, lie_zsmul] using
        lie_lie_chevalleySystem_double_chain h hγ hδ)
  have hαδ := root_add_last_notMem_of_double_chain h hγ hδ
  have hβγ := root_add_middle_notMem_of_double_chain h hγ hδ
  have hxw := commute_of_lie_eq_zero ρ (lie_chevalleySystem_eq_zero hαδ.1 hαδ.2)
  have hyz := commute_of_lie_eq_zero ρ (lie_chevalleySystem_eq_zero hβγ.1 hβγ.2)
  have hMs (i : Fin t.numRoots) (z : ℤ) (n : ℕ) (m : V) (hm : m ∈ M) :
      Associative.dividedPower n (z • x i) • m ∈ M := by
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil i n m hm) _
  have hMc := hMs γ c
  have hMd := hMs δ d
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [← baseChangeExp_zsmul c M _ hMc (isNilpotent_apply_ι_chevalleySystem ρ hnil γ),
    ← baseChangeExp_zsmul d M _ hMd (isNilpotent_apply_ι_chevalleySystem ρ hnil δ)]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M hxy
    (by simpa using hxz) (hxw.smul_right d) (hyz.smul_right c)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
    ((isNilpotent_apply_ι_chevalleySystem ρ hnil γ).smul c) _ _ hMc hMd u v

/-- The Chevalley element-commutator formula for the double root chain
`β`, `α + β`, `2α + β`, over every commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_double_chain (h : t ≠ .G2)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
      chevalleyRootSubgroup ρ M hM hnil δ A
        (.ofAdd (((t.structureConstant ht α β * (t.structureConstant ht α γ / 2) : ℤ) : A) *
          (u ^ 2 * v))) := by
  have hdiv : (2 : ℤ) ∣ t.structureConstant ht α γ := by
    rcases structureConstant_eq_two_or_eq_neg_two_of_double_chain h hγ hδ with hc | hc <;>
      simp [hc]
  simpa only [Int.mul_ediv_assoc _ hdiv] using
    commutatorElement_chevalleyRootSubgroup_of_add_eq_of_add_eq ρ M hM hnil hγ hδ
      (root_add_last_notMem_of_double_chain h hγ hδ).1
      (root_add_middle_notMem_of_double_chain h hγ hδ).1 A u v

end

end TauCeti.DynkinType
