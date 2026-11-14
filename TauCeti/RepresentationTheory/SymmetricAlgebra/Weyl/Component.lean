/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.WeylGroup
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Degrees
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Prod

/-!
# Weyl polynomial invariants and degrees across irreducible components

For a finite root system `P` over a field `K`, the weight space `M` is the internal direct sum of
the component spaces `P.componentSpace C` (`C : P.Component`), and the Weyl group decomposes as
`P.weylGroup ≃* ∀ C : P.Component, (P.componentPairing C).weylGroup`
(`RootPairing.weylGroupComponentEquiv`). Passing to dual spaces and symmetric algebras reduces the
polynomial invariant theory of `P` to that of its irreducible components `P.componentPairing C`:

* `RootPairing.componentDualEquiv`: the `K`-linear equivalence
  `(∀ C : P.Component, Module.Dual K (P.componentSpace C)) ≃ₗ[K] Module.Dual K M` dual to the
  component projections `P.componentProj C`.
* `RootPairing.map_dualMap_componentProj_mem_symmetricAlgebraInvariants`: pulling back a
  component-invariant polynomial along `(P.componentProj C).dualMap` produces a `P.weylGroup`-
  invariant polynomial on `M`.
* `RootPairing.bijective_aeval_weylGroupRootRep_dual_of_componentPairing`: basic invariants of the
  irreducible components `P.componentPairing C`, pulled back along `(P.componentProj C).dualMap`,
  form a polynomial generating system of `Sym(M*)^W`.
* `RootPairing.map_univ_eq_bind_componentPairing_of_bijective_aeval`: the multiset of degrees of
  `P` is the multiset union (`Multiset.bind`) of the degree multisets of its irreducible
  components.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 2; Ch. V, §5, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§2.2 and 3.7.
-/

public section

open SymmetricAlgebra TauCeti.SymmetricAlgebra

namespace RootPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- **Decomposition of the dual weight space along irreducible components:** a family of linear
forms `φ C` on `P.componentSpace C` sums via `(P.componentProj C).dualMap` to a linear form on `M`,
with inverse given by restriction to each `P.componentSpace C`. -/
noncomputable def componentDualEquiv :
    (∀ C : P.Component, Module.Dual K (P.componentSpace C)) ≃ₗ[K] Module.Dual K M := by
  let _ : Fintype P.Component := Fintype.ofFinite P.Component
  exact
    { toFun := fun φ ↦ ∑ C : P.Component, (P.componentProj C).dualMap (φ C)
      map_add' := fun φ ψ ↦ by
        ext x
        simp [Finset.sum_add_distrib]
      map_smul' := fun c φ ↦ by
        ext x
        simp [Finset.mul_sum]
      invFun := fun ψ C ↦ ψ.comp (P.componentSpace C).subtype
      left_inv := fun φ ↦ by
        funext D
        ext x
        simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply,
          LinearMap.sum_apply, LinearMap.dualMap_apply]
        rw [Finset.sum_eq_single D]
        · rw [componentProj_apply_of_mem x.2]
        · intro C _ hCD
          rw [componentProj_apply_of_ne hCD.symm x.2, map_zero]
        · exact fun hD ↦ absurd (Finset.mem_univ D) hD
      right_inv := fun ψ ↦ by
        ext x
        simp only [LinearMap.sum_apply, LinearMap.dualMap_apply, LinearMap.coe_comp,
          Submodule.coe_subtype, Function.comp_apply, ← map_sum, P.sum_componentProj x] }

/-- Restricting `ψ : M*` along `P.componentDualEquiv.symm` evaluates `ψ` on `P.componentSpace C`. -/
@[simp]
theorem componentDualEquiv_symm_apply (ψ : Module.Dual K M) (C : P.Component)
    (x : P.componentSpace C) :
    P.componentDualEquiv.symm ψ C x = ψ x.1 :=
  (rfl)

/-- `P.componentDualEquiv φ` evaluates on `x : M` by summing `φ C (P.componentProj C x)` over all
components `C`. -/
theorem componentDualEquiv_apply [Fintype P.Component]
    (φ : ∀ C : P.Component, Module.Dual K (P.componentSpace C)) (x : M) :
    P.componentDualEquiv φ x = ∑ C : P.Component, φ C (P.componentProj C x) := by
  conv_lhs => rw [← P.sum_componentProj x, map_sum]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [← P.componentDualEquiv_symm_apply, P.componentDualEquiv.symm_apply_apply]

/-- On a single component coordinate, `P.componentDualEquiv` agrees with
`(P.componentProj C).dualMap`. -/
theorem componentDualEquiv_single [DecidableEq P.Component] (C : P.Component)
    (φ : Module.Dual K (P.componentSpace C)) :
    P.componentDualEquiv
        (LinearMap.single K (fun D ↦ Module.Dual K (P.componentSpace D)) C φ) =
      (P.componentProj C).dualMap φ := by
  let _ : Fintype P.Component := Fintype.ofFinite P.Component
  ext x
  rw [P.componentDualEquiv_apply, Finset.sum_eq_single C]
  · simp [LinearMap.single_apply]
  · intro D _ hDC
    simp [LinearMap.single_apply, hDC]
  · exact fun hC ↦ absurd (Finset.mem_univ C) hC

/-- `(P.componentProj C).dualMap` intertwines the contragredient Weyl representation of the
component `C` (pulled back along `P.weylGroupComponentProj C`) with `P.weylGroupRootRep.dual`. -/
theorem isIntertwiningMap_dualMap_componentProj (C : P.Component) :
    Representation.IsIntertwiningMap
      ((P.componentPairing C).weylGroupRootRep.dual.comp (P.weylGroupComponentProj C))
      P.weylGroupRootRep.dual
      (P.componentProj C).dualMap := by
  refine ⟨fun w φ ↦ ?_⟩
  ext x
  simp [Representation.dual_apply, Module.Dual.transpose_apply, weylGroupRootRep,
    P.componentProj_weylGroup_smul]

/-- Pulling back a component-invariant polynomial along `(P.componentProj C).dualMap` yields a
`P.weylGroup`-invariant polynomial on `M`. -/
theorem map_dualMap_componentProj_mem_symmetricAlgebraInvariants (C : P.Component)
    {p : SymmetricAlgebra K (Module.Dual K (P.componentSpace C))}
    (hp : p ∈ (P.componentPairing C).weylGroupRootRep.dual.symmetricAlgebraInvariants) :
    SymmetricAlgebra.map K (P.componentProj C).dualMap p ∈
      P.weylGroupRootRep.dual.symmetricAlgebraInvariants := by
  refine Representation.map_mem_symmetricAlgebraInvariants
    (P.isIntertwiningMap_dualMap_componentProj C) ?_
  rw [(P.componentPairing C).weylGroupRootRep.dual.symmetricAlgebraInvariants_comp_of_surjective
    (P.weylGroupComponentProj C) (fun u ↦ by
      classical
      exact ⟨P.weylGroupComponentLift C u,
        P.weylGroupComponentProj_weylGroupComponentLift_self C u⟩)]
  exact hp

/-- **Basic invariants of a finite root system from its irreducible components.** If for each
irreducible component `C : P.Component`, `f C` is a polynomial generating family for the component
Weyl invariants `Sym((M_C)*)^(W_C)`, then their pullbacks along `(P.componentProj C).dualMap` form
a polynomial generating family for `Sym(M*)^W`. -/
theorem bijective_aeval_weylGroupRootRep_dual_of_componentPairing
    {κ : P.Component → Type*}
    {f : ∀ C : P.Component,
      κ C → (P.componentPairing C).weylGroupRootRep.dual.symmetricAlgebraInvariants}
    (hf : ∀ C, Function.Bijective (MvPolynomial.aeval (R := K) (f C)))
    {F : (Σ C : P.Component, κ C) → P.weylGroupRootRep.dual.symmetricAlgebraInvariants}
    (hF : ∀ C k, (F ⟨C, k⟩ : SymmetricAlgebra K (Module.Dual K M)) =
      SymmetricAlgebra.map K (P.componentProj C).dualMap (f C k)) :
    Function.Bijective (MvPolynomial.aeval (R := K) F) := by
  classical
  let _ : Fintype P.Component := Fintype.ofFinite P.Component
  let _ : ∀ C : P.Component, Finite (P.componentPairing C).weylGroup :=
    fun C ↦ (P.componentPairing C).finite_weylGroup
  let G : P.Component → Type _ := fun C ↦ ↥(P.componentPairing C).weylGroup
  let V C := Module.Dual K (P.componentSpace C)
  let ρ C := (P.componentPairing C).weylGroupRootRep.dual
  let ρPi := Representation.pi fun C : P.Component ↦ (ρ C).comp (Pi.evalMonoidHom G C)
  let FPi : (Σ C : P.Component, κ C) → ρPi.symmetricAlgebraInvariants := fun ⟨C, k⟩ ↦
    ⟨SymmetricAlgebra.map K (LinearMap.single K V C) (f C k),
      Representation.map_mem_symmetricAlgebraInvariants
        (ρ := (ρ C).comp (Pi.evalMonoidHom G C)) (ρ' := ρPi)
        ⟨fun g φ ↦ by
          ext D
          by_cases hDC : D = C
          · subst hDC; simp [ρPi, V, LinearMap.single_apply]
          · simp [ρPi, V, hDC, LinearMap.single_apply]⟩
        (by
          rw [(ρ C).symmetricAlgebraInvariants_comp_of_surjective (Pi.evalMonoidHom G C)
            (Function.surjective_eval C)]
          exact (f C k).2)⟩
  have hFPi : Function.Bijective (MvPolynomial.aeval (R := K) FPi) :=
    Representation.bijective_aeval_symmetricAlgebraInvariants_pi ρ hf (fun _ _ ↦ rfl)
  refine Representation.bijective_aeval_symmetricAlgebraInvariants_of_equiv
    P.weylGroupComponentEquiv.symm P.componentDualEquiv (Equiv.refl _)
    (fun g φ ↦ ?_) hFPi fun ⟨C, k⟩ ↦ ?_
  · ext x
    rw [P.componentDualEquiv_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, P.componentDualEquiv_apply]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    have hw : P.weylGroupComponentProj C (P.weylGroupComponentEquiv.symm g) = g C := by
      simpa using congrFun (P.weylGroupComponentEquiv.apply_symm_apply g) C
    simp [ρPi, ρ, Representation.dual_apply, Module.Dual.transpose_apply,
      weylGroupRootRep, P.componentProj_weylGroup_smul, hw]
  · dsimp only [Equiv.refl_apply, FPi]
    rw [hF C k, ← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map]
    exact DFunLike.congr_fun (congrArg (SymmetricAlgebra.map K)
      (LinearMap.ext (P.componentDualEquiv_single C)).symm) _

/-- **The invariant degrees of a finite root system are the multiset union of the invariant
degrees of its irreducible components.** -/
theorem map_univ_eq_bind_componentPairing_of_bijective_aeval
    [Fintype P.Component] {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ k, (f k : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d k))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {κC : P.Component → Type*} [∀ C, Fintype (κC C)]
    {fC : ∀ C : P.Component,
      κC C → (P.componentPairing C).weylGroupRootRep.dual.symmetricAlgebraInvariants}
    {dC : ∀ C : P.Component, κC C → ℕ}
    (hfC : ∀ C k, (fC C k : SymmetricAlgebra K (Module.Dual K (P.componentSpace C))) ∈
      homogeneousSubmodule K (Module.Dual K (P.componentSpace C)) (dC C k))
    (hbijC : ∀ C, Function.Bijective (MvPolynomial.aeval (R := K) (fC C))) :
    Finset.univ.val.map d =
      Finset.univ.val.bind fun C : P.Component ↦ Finset.univ.val.map (dC C) := by
  let F : (Σ C : P.Component, κC C) → P.weylGroupRootRep.dual.symmetricAlgebraInvariants :=
    fun ⟨C, k⟩ ↦ ⟨SymmetricAlgebra.map K (P.componentProj C).dualMap (fC C k),
      P.map_dualMap_componentProj_mem_symmetricAlgebraInvariants C (fC C k).2⟩
  have hF_hom : ∀ x : Σ C : P.Component, κC C,
      (F x : SymmetricAlgebra K (Module.Dual K M)) ∈
        homogeneousSubmodule K (Module.Dual K M) (dC x.1 x.2) :=
    fun ⟨C, k⟩ ↦ map_mem_homogeneousSubmodule (P.componentProj C).dualMap (hfC C k)
  have hF_bij : Function.Bijective (MvPolynomial.aeval (R := K) F) :=
    P.bijective_aeval_weylGroupRootRep_dual_of_componentPairing hbijC (fun _ _ ↦ rfl)
  rw [P.weylGroupRootRep.dual.map_univ_eq_of_bijective_aeval_symmetricAlgebraInvariants
      hf hbij hF_hom hF_bij]
  have huniv : (Finset.univ : Finset (Σ C : P.Component, κC C)) =
      Finset.univ.sigma fun _ ↦ Finset.univ := by
    ext ⟨C, k⟩
    simp
  rw [huniv, ← Finset.disjiUnion_map_sigma_mk, Finset.disjiUnion_val, Multiset.map_bind]
  refine Multiset.bind_congr fun C _ ↦ ?_
  rw [Finset.map_val, Multiset.map_map]
  rfl

end RootPairing
