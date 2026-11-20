/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.ProjectiveTrace
import TauCeti.NumberTheory.Padics.GroupAlgebra.Projective
import TauCeti.NumberTheory.Padics.GroupAlgebra.Reduction
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule

/-!
# Characters of projective `ℤ_p[G]`-lifts

Let `X₁` and `X₂` be finitely generated projective `ℤ_p[G]`-modules whose reductions modulo `p`
are identified with `𝔽_p`-representations `η₁` and `η₂` of a finite group `G`. The characters of
`X₁` and `X₂` are compared through `η₁` and `η₂`: an isomorphism of `η₁` and `η₂` on a subgroup
lifts to the restrictions of `X₁` and `X₂`, which then have the same trace on that subgroup.

## Main results

* `TauCeti.trace_ofModule'_eq_of_equiv_comp`: if `η₁` and `η₂` are isomorphic on a subgroup `C`,
  then every element of `C` acts with the same trace on `X₁` and on `X₂`.
* `TauCeti.trace_ofModule'_eq_of_forall_equiv_comp_zpowers`: if `η₁` and `η₂` are isomorphic on
  the cyclic subgroup of every `p`-regular element, then `X₁` and `X₂` have the same character.

These are the character comparisons in the proof of Swan's theorem
(`TauCeti.nonempty_linearEquiv_of_projective_of_tensorRat`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10).
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

public section

open scoped TensorProduct Pointwise MonoidAlgebra
namespace TauCeti

universe u

attribute [local instance] padicReductionModule

section Lift

variable (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G] {W₁ W₂ : Type*}
  [AddCommGroup W₁] [Module (ZMod p) W₁] [AddCommGroup W₂] [Module (ZMod p) W₂]
  (η₁ : Representation (ZMod p) G W₁) (η₂ : Representation (ZMod p) G W₂)
  (X₁ X₂ : Type*) [AddCommGroup X₁] [Module ℤ_[p] X₁] [Module (MonoidAlgebra ℤ_[p] G) X₁]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X₁] [Module.Finite (MonoidAlgebra ℤ_[p] G) X₁]
  [Module.Projective (MonoidAlgebra ℤ_[p] G) X₁] [AddCommGroup X₂] [Module ℤ_[p] X₂]
  [Module (MonoidAlgebra ℤ_[p] G) X₂] [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X₂]
  [Module.Finite (MonoidAlgebra ℤ_[p] G) X₂] [Module.Projective (MonoidAlgebra ℤ_[p] G) X₂]
  (f₁ : (X₁ ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
    (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X₁)) →ₛₗ[MonoidAlgebra.mapRingHom G
      (PadicInt.toZMod (p := p))] η₁.asModule) (hf₁ : Function.Bijective f₁)
  (f₂ : (X₂ ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
    (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X₂)) →ₛₗ[MonoidAlgebra.mapRingHom G
      (PadicInt.toZMod (p := p))] η₂.asModule) (hf₂ : Function.Bijective f₂)

include hf₁ hf₂

/-- Let `X₁` and `X₂` be finitely generated projective `ℤ_p[G]`-modules whose reductions modulo `p`
are identified with `𝔽_p`-representations `η₁` and `η₂`. If `η₁` and `η₂` become isomorphic on a
subgroup `C`, then an element of `C` acts with the same trace on `X₁` and on `X₂`: the isomorphism
lifts to `ℤ_p[C]`-modules, which conjugates the two actions. -/
theorem trace_ofModule'_eq_of_equiv_comp (C : Subgroup G) {g : G} (hg : g ∈ C)
    (e : _root_.Representation.Equiv (η₁.comp C.subtype) (η₂.comp C.subtype)) :
    LinearMap.trace ℤ_[p] X₁ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁ g) =
      LinearMap.trace ℤ_[p] X₂ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂ g) := by
  classical
  let A := MonoidAlgebra ℤ_[p] G
  let AC := MonoidAlgebra ℤ_[p] C
  let kC := MonoidAlgebra (ZMod p) C
  -- Restrict scalars of `X₁` and `X₂` to `ℤ_p[C]`.
  let _ : Module AC A := (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype).toModule
  let _ : Module AC X₁ := .compHom X₁ (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
  let _ : Module AC X₂ := .compHom X₂ (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
  obtain ⟨_, _, _, _, _⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := ℤ_[p]) C
      (fun _ _ ↦ rfl) X₁ fun _ _ ↦ rfl
  obtain ⟨_, _, _, _, _⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := ℤ_[p]) C
      (fun _ _ ↦ rfl) X₂ fun _ _ ↦ rfl
  -- Transport `e` through the lifts to an isomorphism of the reductions over `C`.
  let Q₁ := X₁ ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A X₁)
  let Q₂ := X₂ ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A X₂)
  let _ : Module kC Q₁ := .compHom Q₁ (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
  let _ : Module kC Q₂ := .compHom Q₂ (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
  let e₁ := η₁.linearEquivAsModuleComp C.subtype (fun _ _ ↦ rfl)
    (padicReductionLinearEquivOfBijective p G f₁ hf₁)
  let e₂ := η₂.linearEquivAsModuleComp C.subtype (fun _ _ ↦ rfl)
    (padicReductionLinearEquivOfBijective p G f₂ hf₂)
  let eRedC := (padicReductionRestrictLinearEquiv p C C.subtype X₁ (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)).trans (e₁.trans ((TauCeti.Representation.asModuleLinearEquivOfEquiv e).trans
      (e₂.symm.trans (padicReductionRestrictLinearEquiv p C C.subtype X₂ (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl)).symm)))
  have := padicReduction_compatibleSMul_padicInt p C (padicReduction_smul p C X₁)
    (padicReduction_smul p C X₂)
  obtain ⟨eX⟩ := nonempty_linearEquiv_of_projective_of_reduction p C X₁ X₂
    ⟨eRedC.restrictScalars AC⟩
  -- The `ℤ_p[C]`-linear isomorphism `eX` conjugates the action of `g ∈ C`.
  have hconj : (eX.restrictScalars ℤ_[p]).conj (Representation.ofModule' X₁ g) =
      Representation.ofModule' X₂ g := LinearMap.ext fun x ↦ by
    rw [LinearEquiv.conj_apply_apply]
    simpa using Representation.map_ofModule'_comp C.subtype (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      eX.toLinearMap ⟨g, hg⟩ (eX.symm x)
  rw [← hconj, LinearMap.trace_conj']

/-- **Equal characters from isomorphic restrictions to cyclic subgroups.** Let `X₁` and `X₂` be
finitely generated projective `ℤ_p[G]`-modules whose reductions modulo `p` are identified with
`𝔽_p`-representations `η₁` and `η₂`. Suppose `η₁` and `η₂` become isomorphic on the cyclic
subgroup generated by every `p`-regular element. Then `X₁` and `X₂` have the same character: it
vanishes at `p`-singular elements for projective modules, and at `p`-regular elements it is
computed on the cyclic subgroup. -/
theorem trace_ofModule'_eq_of_forall_equiv_comp_zpowers
    (hη : ∀ g : G, ¬p ∣ orderOf g → Nonempty (_root_.Representation.Equiv
      (η₁.comp (Subgroup.zpowers g).subtype) (η₂.comp (Subgroup.zpowers g).subtype)))
    (g : G) :
    LinearMap.trace ℤ_[p] X₁ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁ g) =
      LinearMap.trace ℤ_[p] X₂ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂ g) := by
  by_cases hg : p ∣ orderOf g
  · have hp : ¬IsUnit (p : ℤ_[p]) := PadicInt.p_nonunit
    rw [trace_ofModule'_eq_zero_of_dvd_orderOf X₁ hp hg,
      trace_ofModule'_eq_zero_of_dvd_orderOf X₂ hp hg]
  · obtain ⟨e⟩ := hη g hg
    exact trace_ofModule'_eq_of_equiv_comp p η₁ η₂ X₁ X₂ f₁ hf₁ f₂ hf₂
      (Subgroup.zpowers g) (Subgroup.mem_zpowers g) e

end Lift

end TauCeti
