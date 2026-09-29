/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.ZModFour
public import TauCeti.Topology.Algebra.GroupExtension.CohomFp

/-!
# The class of the extension `ℤ/4` in `H²(ℤ/2, 𝔽₂)`

The extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` of `TauCeti/GroupTheory/GroupExtension/ZModFour.lean` is
an extension of finite discrete groups, hence a profinite extension of `ℤ/2` by `ℤ/2` inducing the
trivial action (`TauCeti.ProfiniteGroupExtension.zmodFour`). Its class in `H²(ℤ/2, 𝔽₂)`, read in
Mathlib's continuous cohomology of the trivial `𝔽₂`-representation through
`TauCeti.ProfiniteGroupExtension.cohomFpClass`, is `TauCeti.zmodFourExtensionClass`. It is nonzero,
because the extension has no homomorphic section at all, let alone a continuous one
(`TauCeti.isEmpty_splitting_zmodFourExtension`).

The group `H²(ℤ/2, 𝔽₂)` is a line, so this nonzero class is the cup square of the generator of
`H¹(ℤ/2, 𝔽₂)`; that identification is
`TauCeti.cupFp_cyclicTwoClass_self_eq_zmodFourExtensionClass` in
`TauCeti/Topology/Algebra/Group/Profinite/Demushkin/CyclicTwo.lean`.

## Main declarations

* `TauCeti.ProfiniteGroupExtension.zmodFour`: the profinite extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1`
  of `ℤ/2` by `ℤ/2` with the trivial action; its underlying extension is `TauCeti.zmodFourExtension`
  (`TauCeti.ProfiniteGroupExtension.zmodFour_toGroupExtension`).
* `TauCeti.zmodFourExtensionClass`: **the class of the extension `ℤ/4` in `H²(ℤ/2, 𝔽₂)`**, and
  `TauCeti.zmodFourExtensionClass_ne_zero`: it is nonzero.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open Multiplicative

-- The extension `ℤ/4` is central, so the action of `ℤ/2` on its kernel `ℤ/2` it induces is the
-- trivial one, `TauCeti.trivialMulDistribMulAction`. A bundled profinite extension carries the
-- action as an instance, so the trivial action is installed locally, exactly as in
-- `TauCeti.RepresentationTheory.ProjectiveRepresentation.SchurMultiplier`; the class
-- `TauCeti.zmodFourExtensionClass` mentions no action, and is what downstream files consume.
attribute [local instance] trivialMulDistribMulAction

/-- **The extension `1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` as a profinite extension** of `ℤ/2` by `ℤ/2`
inducing the trivial action: its total group `ℤ/4` is finite and discrete, and abelian, so
conjugation on the kernel is trivial. It is an abbreviation so that its total group and group
structure remain definitionally those of `Multiplicative (ZMod 4)`, as for
`TauCeti.ProfiniteGroupExtension.ofFactorSet`. -/
abbrev ProfiniteGroupExtension.zmodFour :
    ProfiniteGroupExtension (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)) where
  E := Multiplicative (ZMod 4)
  toGroupExtension := zmodFourExtension
  continuous_inl := continuous_of_discreteTopology
  continuous_rightHom := continuous_of_discreteTopology
  inducesAction :=
    (GroupExtension.inducesAction_iff_smul_eq_self
      (le_top.trans_eq Subgroup.center_eq_top.symm)).2 fun _ _ =>
        trivialMulDistribMulAction_smul _ _

/-- The underlying extension of the profinite extension `ℤ/4` is `TauCeti.zmodFourExtension`. -/
@[simp]
theorem ProfiniteGroupExtension.zmodFour_toGroupExtension :
    ProfiniteGroupExtension.zmodFour.toGroupExtension = zmodFourExtension :=
  (rfl)

/-- **The class of the extension `ℤ/4` in `H²(ℤ/2, 𝔽₂)`**: the class of the profinite extension
`1 → ℤ/2 → ℤ/4 → ℤ/2 → 1` in Mathlib's continuous cohomology of the trivial
`𝔽₂`-representation of `ℤ/2`. -/
noncomputable def zmodFourExtensionClass : cohomFp 2 (Multiplicative (ZMod 2)) 2 :=
  -- The trivial action of the discrete group `ℤ/2` on the discrete group `ℤ/2` is continuous; its
  -- scalar multiplication is named, because `ℤ/2` also acts on itself by multiplication.
  ProfiniteGroupExtension.zmodFour.cohomFpClass
    (hcont := @ContinuousSMul.mk _ _ (trivialMulDistribMulAction _ _).toMulAction.toSMul _ _
      continuous_of_discreteTopology)
    trivialMulDistribMulAction_smul

theorem zmodFourExtensionClass_def :
    zmodFourExtensionClass =
      ProfiniteGroupExtension.zmodFour.cohomFpClass
        (hcont := @ContinuousSMul.mk _ _ (trivialMulDistribMulAction _ _).toMulAction.toSMul _ _
          continuous_of_discreteTopology)
        trivialMulDistribMulAction_smul :=
  (rfl)

/-- **The class of the extension `ℤ/4` in `H²(ℤ/2, 𝔽₂)` is nonzero**: the extension has no
homomorphic section. -/
theorem zmodFourExtensionClass_ne_zero : zmodFourExtensionClass ≠ 0 := by
  rw [zmodFourExtensionClass_def, Ne, ProfiniteGroupExtension.cohomFpClass_eq_zero_iff,
    ProfiniteGroupExtension.zmodFour_toGroupExtension]
  rintro ⟨s, -⟩
  exact isEmpty_splitting_zmodFourExtension.elim s

end TauCeti
