/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Extension

/-!
# The arithmetic class-module extension over a finite Galois group

For a finite normal extension `L/K` embedded in a separable closure of `K`, let `V` be the
open subgroup fixing `L`. The pro-`p` class-module extension has kernel `Vᵃᵇ(p)` and quotient
`G_K/V`. This file reads its conjugation action and its projection over `Gal(L/K)`, using
the topological Galois correspondence. Its total group and kernel remain the canonical
class-module carriers. The construction relabels `abelianizationProPProfiniteExtension`
through `quotientGaloisSubgroupEquiv`, using `ProfiniteGroupExtension.relabelQuotient`.

This supplies an arithmetic extension over the same finite group as a free profinite
presentation of `Gal(L/K)`, so equivariant kernel maps can be lifted between the extensions.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti

universe u v

variable (p : ℕ) (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Normal K L] (j : L →ₐ[K] SeparableClosure K)

/-- The action of `Gal(L/K)` on the pro-`p` abelianization of the subgroup fixing `L`,
transported from the canonical quotient conjugation action. -/
abbrev galoisClassModuleAction :
    MulDistribMulAction (L ≃ₐ[K] L)
      (abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup) :=
  MulDistribMulAction.compHom _
    (quotientGaloisSubgroupEquiv K L j).symm.toMulEquiv.toMonoidHom

/-- The transported action is conjugation by the corresponding class in `G_K/V`. -/
theorem galoisClassModuleAction_smul (t : L ≃ₐ[K] L)
    (x : abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup) :
    letI := galoisClassModuleAction p K L j
    t • x = (quotientGaloisSubgroupEquiv K L j).symm t • x :=
  (rfl)

/-- In the transported action, restriction to `L` acts by the class of the original
absolute Galois automorphism. -/
@[simp]
theorem galoisClassModuleAction_restrict_smul (s : AbsoluteGaloisGroup K)
    (x : abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup) :
    let := galoisClassModuleAction p K L j
    j.restrictNormalHom s • x =
      (s : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L j).toSubgroup) • x := by
  let := galoisClassModuleAction p K L j
  dsimp only
  rw [galoisClassModuleAction_smul, ← quotientGaloisSubgroupEquiv_mk K L j s,
    ContinuousMulEquiv.symm_apply_apply]

/-- The finite Galois group's transported conjugation action is jointly continuous. -/
theorem continuousSMul_galoisClassModuleAction :
    let := galoisClassModuleAction p K L j
    ContinuousSMul (L ≃ₐ[K] L)
      (abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup) :=
  MulAction.continuousSMul_compHom (quotientGaloisSubgroupEquiv K L j).symm.continuous

-- Relabelling retains the total group and requires both quotient models in the same universe.
variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Normal K L]
  (j : L →ₐ[K] SeparableClosure K)

/-- The arithmetic pro-`p` class-module extension with quotient `Gal(L/K)` and its
prescribed conjugation action on `Vᵃᵇ(p)`. -/
abbrev galoisClassModuleExtension :
    let := galoisClassModuleAction p K L j
    ProfiniteGroupExtension (L ≃ₐ[K] L)
      (abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup) := by
  let := galoisClassModuleAction p K L j
  letI : IsClosed ((galoisSubgroup K L j).toSubgroup : Set (AbsoluteGaloisGroup K)) :=
    (galoisSubgroup K L j).isClosed
  exact (abelianizationProPProfiniteExtension p (AbsoluteGaloisGroup K)
    (galoisSubgroup K L j).toSubgroup).relabelQuotient
    (quotientGaloisSubgroupEquiv K L j) (fun q x ↦ by
      rw [galoisClassModuleAction_smul, ContinuousMulEquiv.symm_apply_apply])

end TauCeti
