/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SimplyLaced
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.Basic

/-!
# Commutators of the pinned all-root subgroups in simply-laced types

The root subgroups `DynkinType.chevalleyRootSubgroup` of a Kostant-stable lattice satisfy
Steinberg's commutator formula in types A, D and E over every commutative value ring. If
`γ = α + β` is a root, the commutator is `x_γ(N_{α,β}uv)`, with the integer and sign supplied by
`DynkinType.structureConstant`. If the sum is neither a root nor zero, the root subgroups
commute; this latter assertion holds in every type.

The root-string conditions are consequences of the pinned datum, not additional Lie-bracket
hypotheses on the representation. In a simply-laced type, a root sum has Cartan pairing `-1`,
so neither `2α + β` nor `α + 2β` is a root or zero. The corresponding brackets vanish, and the
integral exponential identity `baseChangeExp_mul_baseChangeExp_of_commutator_eq` gives the
formula without inverting factorials in the value ring. No faithfulness or weight basis is
required of the representation beyond the hypotheses of the existing root-subgroup construction.

The commutator convention is `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra
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

attribute [local instance high] Algebra.toModule

/-- Root subgroups commute when their roots sum to neither a root nor zero, in every type
and over every commutative value ring. -/
theorem commute_chevalleyRootSubgroup_of_add_notMem {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h₀ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (A : CommAlgCat ℤ) (u v : Multiplicative A) :
    Commute (chevalleyRootSubgroup ρ M hM hnil α A u)
      (chevalleyRootSubgroup ρ M hM hnil β A v) := by
  apply Units.ext
  simp only [Units.val_mul, chevalleyRootSubgroup_val]
  exact commute_baseChangeExp M
    (commute_of_lie_eq_zero ρ (lie_chevalleySystem_eq_zero h h₀)) _ _ _ _

/-- **The simply-laced Chevalley commutator formula.** At every root sum `γ = α + β`,
`⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β}uv)`. The structure constant and both vanishing higher brackets
are determined by the pinned Chevalley system. The value ring may have arbitrary characteristic. -/
theorem commutatorElement_chevalleyRootSubgroup_of_isSimplyLaced (hs : t.IsSimplyLaced)
    {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (A : CommAlgCat ℤ) (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u),
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v)⁆ =
      chevalleyRootSubgroup ρ M hM hnil γ A
        (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) := by
  have hαγ := lie_chevalleySystem_eq_zero
    (root_add_notMem_of_root_eq_add hs hγ) (root_add_ne_zero_of_root_eq_add hs hγ)
  have hγ' := hγ.trans (add_comm _ _)
  have hβγ := lie_chevalleySystem_eq_zero
    (root_add_notMem_of_root_eq_add hs hγ') (root_add_ne_zero_of_root_eq_add hs hγ')
  have hbr := lie_chevalleySystem_eq_structureConstant_zsmul hγ
  let c := t.structureConstant ht α β
  have hMc : ∀ n, ∀ z ∈ M, Associative.dividedPower n
      (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))) • z ∈ M := by
    intro n z hz
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ n z hz) _
  have hxy : chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) =
      chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) *
        chevalleyRootSubgroup ρ M hM hnil γ A (Multiplicative.ofAdd ((c : A) * (u * v))) *
        chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) := by
    apply Units.ext
    simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
    rw [← baseChangeExp_zsmul c M
      (dividedPower_chevalleySystem_smul_mem ρ M hM hnil γ) hMc
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ)]
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M
      (mul_eq_mul_add_zsmul_of_lie_eq ρ hbr)
      ((commute_of_lie_eq_zero ρ hαγ).smul_right c)
      ((commute_of_lie_eq_zero ρ hβγ).smul_right c)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil β) _ _ hMc u v
  have hyz := commute_chevalleyRootSubgroup_of_add_notMem ρ M hM hnil
    (root_add_notMem_of_root_eq_add hs hγ') (root_add_ne_zero_of_root_eq_add hs hγ') A
    (Multiplicative.ofAdd v) (Multiplicative.ofAdd ((c : A) * (u * v)))
  rw [commutatorElement_def, hxy, mul_inv_cancel_right, hyz.eq, mul_inv_cancel_right]

end

end TauCeti.DynkinType
