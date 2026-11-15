/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.CompletedScalars
public import TauCeti.RingTheory.Huber.Adic
public import Mathlib.Data.ZMod.Basic

/-!
# Checks for completed scalars on finite modules

For the `2`-adic topology on `ℤ`, the completed-scalar comparison on the free rank-one
module sends a sum of elementary tensors to the expected integer. The completion of the
finite module `ℤ/3ℤ`, with its natural topology over the same base, vanishes. This checks
that the construction accepts non-Hausdorff original modules, not just complete modules.
-/

public section

open Topology TensorProduct UniformSpace TauCeti.Huber

noncomputable section

namespace TauCeti.Examples.HuberCompletedModule

/-- The `2`-adic topology used for the integer completion checks. -/
local instance integerTopology : TopologicalSpace ℤ := (Ideal.span {(2 : ℤ)}).adicTopology

private local instance integerUniformSpace : UniformSpace ℤ :=
  IsTopologicalAddGroup.rightUniformSpace ℤ
private local instance integerIsUniformAddGroup : IsUniformAddGroup ℤ :=
  isUniformAddGroup_of_addCommGroup

private theorem isAdic_two : IsAdic (Ideal.span {(2 : ℤ)}) := (rfl)

private theorem fg_two : (Ideal.span {(2 : ℤ)}).FG := Submodule.fg_span_singleton 2

private abbrev integerPair : PairOfDefinition ℤ :=
  PairOfDefinition.adic (Ideal.span {2}) isAdic_two fg_two

private instance : IsNoetherianRing integerPair.ringOfDefinition := by
  rw [integerPair, PairOfDefinition.adic_ringOfDefinition]
  exact isNoetherianRing_of_ringEquiv ℤ Subring.topEquiv.symm

-- This tests additivity and the order of the two factors over an incomplete coefficient ring.
example :
    letI := moduleTopology (Completion ℤ) (Completion ℤ ⊗[ℤ] ℤ)
    integerPair.completionTensorHomeomorph
        (Completion.coeRingHom (2 : ℤ) ⊗ₜ (3 : ℤ) +
          Completion.coeRingHom (5 : ℤ) ⊗ₜ (7 : ℤ)) = Completion.coeRingHom (41 : ℤ) := by
  let := moduleTopology (Completion ℤ) (Completion ℤ ⊗[ℤ] ℤ)
  simp only [map_add, PairOfDefinition.completionTensorHomeomorph_apply,
    Completion.coe_coeRingHom, Completion.ofTensorProduct_coe_tmul]
  norm_num [← Completion.coe_add]

section Torsion

private local instance torsionTopology : TopologicalSpace (ZMod 3) := moduleTopology ℤ (ZMod 3)
private local instance torsionIsModuleTopology : IsModuleTopology ℤ (ZMod 3) := ⟨rfl⟩
private local instance torsionIsTopologicalAddGroup : IsTopologicalAddGroup (ZMod 3) :=
  IsModuleTopology.isTopologicalAddGroup ℤ (ZMod 3)
private local instance torsionUniformSpace : UniformSpace (ZMod 3) :=
  IsTopologicalAddGroup.rightUniformSpace (ZMod 3)
private local instance torsionIsUniformAddGroup : IsUniformAddGroup (ZMod 3) :=
  isUniformAddGroup_of_addCommGroup
private local instance torsionUniformContinuousConstSMul : UniformContinuousConstSMul ℤ (ZMod 3) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℤ (ZMod 3)

-- The completed action exists even though `ℤ/3ℤ` is not separated for this topology.
example :
    letI := integerPair.completionModule (M := ZMod 3)
    IsModuleTopology (Completion ℤ) (Completion (ZMod 3)) :=
  integerPair.isModuleTopology_completionModule

-- Powers of `4` tend to zero but act as the identity on `ℤ/3ℤ`.
example : Subsingleton (Completion (ZMod 3)) := by
  let := integerPair.completionModule (M := ZMod 3)
  have := integerPair.continuousSMul_completionModule (M := ZMod 3)
  have h4 : IsTopologicallyNilpotent (4 : ℤ) := by
    apply isAdic_two.isTopologicallyNilpotent_iff_mem_radical.mpr
    exact Ideal.le_radical (Ideal.mem_span_singleton.mpr (by norm_num))
  have h4' : IsTopologicallyNilpotent (Completion.coeRingHom (4 : ℤ)) :=
    h4.map Completion.continuous_coeRingHom
  have hfour : (4 : ZMod 3) = 1 := by decide
  have hseq (m : ZMod 3) (n : ℕ) :
      (Completion.coeRingHom (4 : ℤ) ^ n) • (m : Completion (ZMod 3)) =
      (m : Completion (ZMod 3)) := by
    rw [← map_pow Completion.coeRingHom, Completion.coe_coeRingHom,
      integerPair.coe_smul_completion, ← Completion.coe_smul]
    congr 1
    rw [← Int.cast_smul_eq_zsmul (R := ZMod 3), Int.cast_pow]
    simp [hfour]
  have hzero (m : ZMod 3) : (m : Completion (ZMod 3)) = 0 := by
    have hlim := h4'.smul_const (m : Completion (ZMod 3))
    simp only [hseq, zero_smul] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have hzero' (x : Completion (ZMod 3)) : x = 0 :=
    Completion.induction_on x (isClosed_eq continuous_id continuous_const) hzero
  exact ⟨fun x y ↦ (hzero' x).trans (hzero' y).symm⟩

end Torsion

end TauCeti.Examples.HuberCompletedModule
