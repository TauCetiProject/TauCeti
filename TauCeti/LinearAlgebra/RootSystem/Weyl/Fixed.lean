/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.RepresentationTheory.Basic
import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The fixed Weyl subgroup and its faithful fixed-space action

For an automorphism `σ` of a root pairing, `RootPairing.fixedWeylGroup` is the subgroup of
Weyl elements commuting with `σ`. Restriction gives a homomorphism from this subgroup to
the linear automorphisms of `LinearMap.fixedSubmodule σ.weightMap`.

For a base-preserving automorphism of a finite reduced crystallographic pairing over an
ordered ring, that restriction is injective. Indeed, the sum of the positive roots is both
`σ`-fixed and strictly dominant, and a Weyl element fixing a strictly dominant vector is
identity. This does not require the roots to span the ambient module, simple-orbit
orthogonality, or a folded root system. In particular the centralizer subgroup should not
be confused with the pointwise stabilizer of the fixed space: the latter is trivial.

This is the faithfulness argument underlying the fixed Weyl group comparison in
J. R. Stembridge, *Folding by automorphisms* (20 August 2008), Claim 3.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- The Weyl elements fixed by conjugation by `σ`, namely those commuting with it in the
root-pairing automorphism group. This is not the pointwise stabilizer of the fixed space. -/
noncomputable def fixedWeylGroup (σ : P.Aut) : Subgroup P.weylGroup :=
  (Subgroup.centralizer {σ}).comap P.weylGroup.subtype

/-- Membership in the fixed Weyl subgroup is commutation in the original automorphism group. -/
@[simp]
theorem mem_fixedWeylGroup (σ : P.Aut) (w : P.weylGroup) :
    w ∈ P.fixedWeylGroup σ ↔ σ * (w : P.Aut) = (w : P.Aut) * σ := by
  simp only [fixedWeylGroup, Subgroup.mem_comap, Subgroup.coe_subtype,
    Subgroup.mem_centralizer_singleton_iff, eq_comm]

/-- Equivalently, conjugation by `σ` fixes the original Weyl automorphism. -/
theorem mem_fixedWeylGroup_iff_conj_eq (σ : P.Aut) (w : P.weylGroup) :
    w ∈ P.fixedWeylGroup σ ↔ σ * (w : P.Aut) * σ⁻¹ = (w : P.Aut) := by
  rw [mem_fixedWeylGroup, mul_inv_eq_iff_eq_mul]

/-- The identity automorphism has the whole Weyl group as its fixed subgroup. -/
@[simp]
theorem fixedWeylGroup_one : P.fixedWeylGroup 1 = ⊤ := by
  ext w
  simp

variable (σ : P.Aut)

/-- A centralizing Weyl element takes `σ`-fixed vectors to `σ`-fixed vectors. -/
theorem fixedWeylGroup_smul_mem (w : P.fixedWeylGroup σ) {x : M}
    (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    (w : P.weylGroup) • x ∈ LinearMap.fixedSubmodule σ.weightMap := by
  have hc := congrArg (fun a : P.Aut ↦ Equiv.weightHom P a x)
    ((P.mem_fixedWeylGroup σ w.val).mp w.property)
  rw [LinearMap.mem_fixedSubmodule_iff, ← Equiv.weightEquiv_apply,
    ← Equiv.weightHom_apply P] at hx ⊢
  rw [Subgroup.smul_def]
  -- Unfold only the ambient automorphism action, defined by evaluating `Equiv.weightHom`.
  dsimp only [HSMul.hSMul, SMul.smul, Equiv.instDistribMulActionAut]
  simpa only [map_mul, mul_apply_eq_comp, hx] using hc

/-- The linear representation on the fixed space, obtained by restricting the native Weyl
representation. Its vectors are fixed vectors, not classes in an invariant quotient. -/
noncomputable def fixedWeylGroupRep :
    Representation R (P.fixedWeylGroup σ) (LinearMap.fixedSubmodule σ.weightMap) :=
  Representation.subrepresentation
    (P.weylGroupRootRep.comp (P.fixedWeylGroup σ).subtype) _
    (fun w _ hx ↦ P.fixedWeylGroup_smul_mem σ w hx)

/-- The restricted representation agrees with the original Weyl action after inclusion. -/
@[simp]
theorem coe_fixedWeylGroupRep_apply (w : P.fixedWeylGroup σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.fixedWeylGroupRep σ w x : M) = (w : P.weylGroup) • (x : M) := (rfl)

/-- Restriction of centralizing Weyl elements to linear automorphisms of the fixed space. -/
noncomputable def fixedWeylGroupToLinearEquiv :
    P.fixedWeylGroup σ →*
      (LinearMap.fixedSubmodule σ.weightMap ≃ₗ[R] LinearMap.fixedSubmodule σ.weightMap) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R _).toMonoidHom.comp
    (P.fixedWeylGroupRep σ).asGroupHom

/-- The restriction homomorphism has the original action on underlying vectors. -/
@[simp]
theorem coe_fixedWeylGroupToLinearEquiv_apply (w : P.fixedWeylGroup σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.fixedWeylGroupToLinearEquiv σ w x : M) = (w : P.weylGroup) • (x : M) := (rfl)

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)

include b hσ

/-- The pointwise stabilizer in the Weyl group of the fixed space of a based automorphism is
trivial. This applies even to Weyl elements not assumed to centralize the automorphism. -/
theorem eq_one_of_forall_fixed_smul_eq_self (w : P.weylGroup)
    (hw : ∀ x ∈ LinearMap.fixedSubmodule σ.weightMap, w • x = x) : w = 1 := by
  let := P.flip_isReduced
  exact eq_one_of_smul_eq_self_of_mem_openDominantChamber P b w
    (twoWeylVector_mem_openDominantChamber P b)
    (hw _ (LinearMap.mem_fixedSubmodule_iff.mpr (P.weightMap_twoWeylVector b σ hσ)))

/-- Restriction of the fixed Weyl subgroup to the fixed space is faithful. No spanning or
simple-orbit orthogonality assumption is needed. -/
theorem fixedWeylGroupToLinearEquiv_injective :
    Function.Injective (P.fixedWeylGroupToLinearEquiv σ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  apply Subtype.ext
  exact P.eq_one_of_forall_fixed_smul_eq_self σ b hσ w.val fun x hx ↦ by
    have he := congrArg (fun e ↦ (e ⟨x, hx⟩ : M)) hw
    simpa using he

end Ordered

end RootPairing
