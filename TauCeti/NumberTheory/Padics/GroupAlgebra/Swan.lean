/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.GroupAlgebra.Rational
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RepresentationTheory.Basic
import TauCeti.Algebra.Module.Projective.Reduction
import TauCeti.Algebra.Module.Projective.Trans
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.ProjectiveTrace
import TauCeti.NumberTheory.Padics.GroupAlgebra.Invariants
import TauCeti.NumberTheory.Padics.GroupAlgebra.Projective
import TauCeti.NumberTheory.Padics.GroupAlgebra.Reduction
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.LinHom.Basic
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Jacobson.Semiprimary
import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# Swan's theorem for `ℤ_p[G]`

For a finite group `G`, two finitely generated projective `ℤ_p[G]`-modules are isomorphic when
their rationalizations are isomorphic. This is Swan's theorem, NSW (5.6.10)(ii).

The proof first detects the reductions modulo `p` by counting maps to every simple
`𝔽_p[G]`-module. Those counts are dimensions of invariant spaces in conjugation
representations. Projective lifts turn the dimensions into integral invariant ranks, which the
character formula computes from traces. Traces at `p`-singular elements vanish for projective
modules. For a `p`-regular element, restriction to its cyclic subgroup reduces trace equality to
the prime-to-`p` case of Swan's theorem. The resulting equivalence modulo `p` lifts to an
integral equivalence because both modules are projective.

## Main result

* `TauCeti.nonempty_linearEquiv_of_projective_of_tensorRat`: finitely generated projective
  `ℤ_p[G]`-modules with isomorphic rationalizations are isomorphic.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(ii).
* R. G. Swan, *Induced representations and projective modules*, Ann. of Math. 71 (1960).
-/

open scoped TensorProduct Pointwise MonoidAlgebra
namespace TauCeti

universe u v w

attribute [local instance] padicReductionModule

section Helpers

/-- The image of a monomial of the group algebra of a subgroup `C` in the group algebra of `G`. -/
private theorem mapDomainAlgHom_single_subtype (R : Type*) [CommSemiring R] {G : Type*} [Group G]
    (C : Subgroup G) (c : C) :
    MonoidAlgebra.mapDomainAlgHom R R C.subtype (MonoidAlgebra.single c 1) =
      MonoidAlgebra.single (c : G) 1 := by
  rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
  rfl

/-- Restricting a finitely generated projective `ℤ_p[G]`-module `X` to the group algebra of a
subgroup `C` gives a finitely generated projective `ℤ_p[C]`-module on which `ℤ_p` and `ℤ_p[G]`
act compatibly, for any `ℤ_p[C]`-module structures on `ℤ_p[G]` and `X` acting through
`mapDomainRingHom`. -/
private theorem restrictSubgroup_facts (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [inst : Module (MonoidAlgebra ℤ_[p] C) (MonoidAlgebra ℤ_[p] G)]
    (hA : ∀ (r : MonoidAlgebra ℤ_[p] C) (s : MonoidAlgebra ℤ_[p] G),
      r • s = MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype r * s)
    (X : Type*) [AddCommGroup X] [Module ℤ_[p] X] [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X] [Module.Finite (MonoidAlgebra ℤ_[p] G) X]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) X] [Module (MonoidAlgebra ℤ_[p] C) X]
    (hX : ∀ (r : MonoidAlgebra ℤ_[p] C) (x : X),
      r • x = MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype r • x) :
    IsScalarTower (MonoidAlgebra ℤ_[p] C) (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra ℤ_[p] G) ∧
      IsScalarTower (MonoidAlgebra ℤ_[p] C) (MonoidAlgebra ℤ_[p] G) X ∧
      IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] C) X ∧ Module.Finite (MonoidAlgebra ℤ_[p] C) X ∧
      Module.Projective (MonoidAlgebra ℤ_[p] C) X := by
  classical
  let A := MonoidAlgebra ℤ_[p] G
  let AC := MonoidAlgebra ℤ_[p] C
  let φA : AC →ₐ[ℤ_[p]] A := MonoidAlgebra.mapDomainAlgHom ℤ_[p] ℤ_[p] C.subtype
  obtain rfl : inst = (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype).toModule :=
    Module.ext' _ _ hA
  let _ : Module AC A := (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype).toModule
  have hAA : IsScalarTower AC A A := ⟨fun r s t ↦ mul_assoc (φA r) s t⟩
  let b := TauCeti.MonoidAlgebra.basisCosets ℤ_[p] C.subtype C.subtype_injective
  have : Module.Free AC A := .of_basis b
  have : Module.Finite AC A := .of_basis b
  have hAX : IsScalarTower AC A X := ⟨fun r s x ↦ by
    rw [hX r (s • x)]
    exact mul_smul (φA r) s x⟩
  refine ⟨hAA, hAX, ⟨fun a r x ↦ ?_⟩, .trans A X, .trans A X⟩
  rw [hX (a • r) x, hX r x]
  exact (congrArg (· • x) (map_smul φA a r)).trans (smul_assoc a (φA r) x)

/-- Projective `𝔽_p[G]`-representations that are the reductions of `ℤ_p[G]`-lattices with the same
characters have equally many invariants: both counts are `p` to the rank of the invariants of the
lattice, which is the average of the character. -/
private theorem natCard_invariants_eq_of_trace_eq (p : ℕ) [Fact p.Prime] {G : Type u} [Group G]
    [Finite G] {W₁ W₂ : Type*} [AddCommGroup W₁] [Module (ZMod p) W₁] [AddCommGroup W₂]
    [Module (ZMod p) W₂] (η₁ : Representation (ZMod p) G W₁) (η₂ : Representation (ZMod p) G W₂)
    [Module.Projective (MonoidAlgebra (ZMod p) G) η₁.asModule]
    [Module.Projective (MonoidAlgebra (ZMod p) G) η₂.asModule]
    (X₁ X₂ : Type*) [AddCommGroup X₁] [Module ℤ_[p] X₁] [Module (MonoidAlgebra ℤ_[p] G) X₁]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X₁] [Module.Finite ℤ_[p] X₁]
    [Module.Projective ℤ_[p] X₁] [AddCommGroup X₂] [Module ℤ_[p] X₂]
    [Module (MonoidAlgebra ℤ_[p] G) X₂] [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X₂]
    [Module.Finite ℤ_[p] X₂] [Module.Projective ℤ_[p] X₂]
    (f₁ : (X₁ ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X₁)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] η₁.asModule) (hf₁ : Function.Bijective f₁)
    (f₂ : (X₂ ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X₂)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] η₂.asModule) (hf₂ : Function.Bijective f₂)
    (htr : ∀ g : G, LinearMap.trace ℤ_[p] X₁ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁ g) =
      LinearMap.trace ℤ_[p] X₂ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂ g)) :
    Nat.card η₁.invariants = Nat.card η₂.invariants := by
  classical
  rw [Representation.natCard_invariants_eq_pow_finrank_of_bijective p η₁ X₁ f₁ hf₁,
    Representation.natCard_invariants_eq_pow_finrank_of_bijective p η₂ X₂ f₂ hf₂]
  congr 1
  rw [← Representation.finrank_invariants_baseChange_ratPadic p
      (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁),
    ← Representation.finrank_invariants_baseChange_ratPadic p
      (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂)]
  let _ := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : ℚ_[p]) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  apply Nat.cast_injective (R := ℚ_[p])
  rw [← (Representation.baseChange ℚ_[p]
      (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁)).card_inv_mul_sum_char_eq_finrank,
    ← (Representation.baseChange ℚ_[p]
      (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂)).card_inv_mul_sum_char_eq_finrank]
  congr 1
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [Representation.character, Representation.baseChange_apply,
    LinearMap.trace_baseChange]
  exact congrArg _ (htr g)

/-- **Swan's theorem for a subgroup of order prime to `p`, modulo `p`.** If the rationalizations of
two finitely generated projective `ℤ_p[G]`-modules `M` and `N` are isomorphic, then on a subgroup
`C` of order prime to `p` the reductions `M / pM` and `N / pN` are isomorphic as
`𝔽_p`-representations: there is an `𝔽_p`-linear isomorphism that commutes with the action of
every element of `C`. -/
private theorem exists_linearEquiv_commute_reduction_of_not_dvd (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] (C : Subgroup G) (hC : ¬p ∣ Nat.card C)
    (M : Type v) (N : Type w) [AddCommGroup M] [Module ℤ_[p] M]
    [Module (MonoidAlgebra ℤ_[p] G) M] [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) M] [Module.Projective (MonoidAlgebra ℤ_[p] G) M]
    [AddCommGroup N] [Module ℤ_[p] N] [Module (MonoidAlgebra ℤ_[p] G) N]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) N] [Module.Finite (MonoidAlgebra ℤ_[p] G) N]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) N]
    [Module (ZMod p) (M ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) M))]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G)
      (M ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) M))]
    [Module (ZMod p) (N ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) N))]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G)
      (N ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) N))]
    (h : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[MonoidAlgebra ℤ_[p] G] (N ⊗[ℤ_[p]] ℚ_[p]))) :
    ∃ e : (M ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) M)) ≃ₗ[ZMod p]
      (N ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) N)),
      ∀ c ∈ C, ∀ x, e (Representation.ofModule' (k := ZMod p) (G := G) _ c x) =
        Representation.ofModule' (k := ZMod p) (G := G) _ c (e x) := by
  classical
  let A := MonoidAlgebra ℤ_[p] G
  let kC := MonoidAlgebra (ZMod p) C
  let φk : kC →ₐ[ZMod p] MonoidAlgebra (ZMod p) G :=
    MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p) C.subtype
  -- Restrict scalars of `M` and `N` to `ℤ_p[C]`.
  let _ : Module (MonoidAlgebra ℤ_[p] C) A :=
    (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype).toModule
  let _ : Module (MonoidAlgebra ℤ_[p] C) M :=
    .compHom M (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
  let _ : Module (MonoidAlgebra ℤ_[p] C) N :=
    .compHom N (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
  obtain ⟨_, _, _, _, _⟩ := restrictSubgroup_facts p C (fun _ _ ↦ rfl) M fun _ _ ↦ rfl
  obtain ⟨_, _, _, _, _⟩ := restrictSubgroup_facts p C (fun _ _ ↦ rfl) N fun _ _ ↦ rfl
  -- Swan's theorem for `C` identifies `M` and `N` over `ℤ_p[C]`, hence their reductions.
  obtain ⟨eMN⟩ := nonempty_linearEquiv_of_projective_of_tensorRat_of_not_dvd p hC M N
    (h.map fun e ↦ e.restrictScalars (MonoidAlgebra ℤ_[p] C))
  let _ : Module kC (M ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A M)) :=
    .compHom _ (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
  let _ : Module kC (N ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A N)) :=
    .compHom _ (MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype)
  have : IsScalarTower (ZMod p) kC (M ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A M)) :=
    ⟨fun a r x ↦ (congrArg (· • x) (map_smul φk a r)).trans (smul_assoc a (φk r) x)⟩
  have : IsScalarTower (ZMod p) kC (N ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A N)) :=
    ⟨fun a r x ↦ (congrArg (· • x) (map_smul φk a r)).trans (smul_assoc a (φk r) x)⟩
  let e : (M ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A M)) ≃ₗ[kC]
      (N ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A N)) :=
    (padicReductionRestrictLinearEquiv p C C.subtype M (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)).symm.trans
      ((padicReductionCongr p C eMN).trans
        (padicReductionRestrictLinearEquiv p C C.subtype N (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)))
  refine ⟨e.restrictScalars (ZMod p), fun c hc x ↦ ?_⟩
  have hφk := mapDomainAlgHom_single_subtype (ZMod p) C ⟨c, hc⟩
  rw [TauCeti.Representation.ofModule'_apply, TauCeti.Representation.ofModule'_apply, ← hφk]
  -- `k[C]` acts on the reductions through `φk`.
  exact e.map_smul (MonoidAlgebra.single ⟨c, hc⟩ 1) x

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
private theorem trace_ofModule'_eq_of_equiv_comp (C : Subgroup G) {g : G} (hg : g ∈ C)
    (e : _root_.Representation.Equiv (η₁.comp C.subtype) (η₂.comp C.subtype)) :
    LinearMap.trace ℤ_[p] X₁ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁ g) =
      LinearMap.trace ℤ_[p] X₂ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂ g) := by
  classical
  let A := MonoidAlgebra ℤ_[p] G
  let AC := MonoidAlgebra ℤ_[p] C
  let kC := MonoidAlgebra (ZMod p) C
  -- Restrict scalars of `X₁` and `X₂` to `ℤ_p[C]`.
  let φA : AC →ₐ[ℤ_[p]] A := MonoidAlgebra.mapDomainAlgHom ℤ_[p] ℤ_[p] C.subtype
  let _ : Module AC A := (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype).toModule
  have : IsScalarTower AC A A := ⟨fun r s t ↦ mul_assoc (φA r) s t⟩
  let _ : Module AC X₁ := .compHom X₁ (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
  let _ : Module AC X₂ := .compHom X₂ (MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype)
  obtain ⟨_, _, _, _, _⟩ := restrictSubgroup_facts p C (fun _ _ ↦ rfl) X₁ fun _ _ ↦ rfl
  obtain ⟨_, _, _, _, _⟩ := restrictSubgroup_facts p C (fun _ _ ↦ rfl) X₂ fun _ _ ↦ rfl
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
  have hφA := mapDomainAlgHom_single_subtype ℤ_[p] C ⟨g, hg⟩
  have hconj : (eX.restrictScalars ℤ_[p]).conj (Representation.ofModule' X₁ g) =
      Representation.ofModule' X₂ g := LinearMap.ext fun x ↦ by
    rw [LinearEquiv.conj_apply_apply, TauCeti.Representation.ofModule'_apply,
      TauCeti.Representation.ofModule'_apply, ← hφA, LinearEquiv.restrictScalars_apply,
      LinearEquiv.restrictScalars_symm_apply]
    -- `ℤ_p[C]` acts on `X₁` and `X₂` through `φA`.
    exact (eX.map_smul _ _).trans (congrArg _ (eX.apply_symm_apply x))
  rw [← hconj, LinearMap.trace_conj']

/-- **Equal characters from isomorphic restrictions to cyclic subgroups.** Let `X₁` and `X₂` be
finitely generated projective `ℤ_p[G]`-modules whose reductions modulo `p` are identified with
`𝔽_p`-representations `η₁` and `η₂`. Suppose `η₁` and `η₂` become isomorphic on the cyclic
subgroup generated by every `p`-regular element. Then `X₁` and `X₂` have the same character: it
vanishes at `p`-singular elements for projective modules, and at `p`-regular elements it is
computed on the cyclic subgroup. -/
private theorem trace_ofModule'_eq_of_forall_equiv_comp_zpowers
    (hη : ∀ g : G, ¬p ∣ orderOf g → Nonempty (_root_.Representation.Equiv
      (η₁.comp (Subgroup.zpowers g).subtype) (η₂.comp (Subgroup.zpowers g).subtype)))
    (g : G) :
    LinearMap.trace ℤ_[p] X₁ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₁ g) =
      LinearMap.trace ℤ_[p] X₂ (Representation.ofModule' (k := ℤ_[p]) (G := G) X₂ g) := by
  by_cases hg : p ∣ orderOf g
  · rw [trace_ofModule'_eq_zero_of_dvd_orderOf X₁ (p := p)
        (show ¬IsUnit (p : ℤ_[p]) from PadicInt.p_nonunit) hg,
      trace_ofModule'_eq_zero_of_dvd_orderOf X₂ (p := p)
        (show ¬IsUnit (p : ℤ_[p]) from PadicInt.p_nonunit) hg]
  · obtain ⟨e⟩ := hη g hg
    exact trace_ofModule'_eq_of_equiv_comp p η₁ η₂ X₁ X₂ f₁ hf₁ f₂ hf₂
      (Subgroup.zpowers g) (Subgroup.mem_zpowers g) e

end Lift

/-- **Counting maps to a finite module.** The reductions modulo `p` of two finitely generated
projective `ℤ_p[G]`-modules with isomorphic rationalizations have the same number of `𝔽_p[G]`-maps
to every finite `𝔽_p[G]`-module `S`. Projective lifts turn these counts into invariant ranks of
conjugation representations, which the characters of the lifts determine. -/
private theorem natCard_linearMap_reduction_eq_of_tensorRat (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] (M : Type v) (N : Type w) [AddCommGroup M]
    [Module ℤ_[p] M] [Module (MonoidAlgebra ℤ_[p] G) M]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M] [Module.Finite (MonoidAlgebra ℤ_[p] G) M]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) M] [AddCommGroup N] [Module ℤ_[p] N]
    [Module (MonoidAlgebra ℤ_[p] G) N] [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) N]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) N] [Module.Projective (MonoidAlgebra ℤ_[p] G) N]
    (h : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[MonoidAlgebra ℤ_[p] G] (N ⊗[ℤ_[p]] ℚ_[p])))
    (S : Type u) [AddCommGroup S] [Module (MonoidAlgebra (ZMod p) G) S] [Finite S] :
    Nat.card ((M ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) M)) →ₗ[MonoidAlgebra (ZMod p) G] S) =
      Nat.card ((N ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) N)) →ₗ[MonoidAlgebra (ZMod p) G] S) := by
  classical
  let kG := MonoidAlgebra (ZMod p) G
  let M₀ := M ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
    (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) M)
  let N₀ := N ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
    (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) N)
  let _ : Module.Finite kG M₀ := padicReduction_module_finite p G M
  let _ : Module.Finite kG N₀ := padicReduction_module_finite p G N
  let _ : Module.Projective kG M₀ := padicReduction_module_projective p G M
  let _ : Module.Projective kG N₀ := padicReduction_module_projective p G N
  let _ : Module (ZMod p) M₀ := Module.compHom M₀ (algebraMap (ZMod p) kG)
  let _ : Module (ZMod p) N₀ := Module.compHom N₀ (algebraMap (ZMod p) kG)
  let _ : Module (ZMod p) S := Module.compHom S (algebraMap (ZMod p) kG)
  let _ : IsScalarTower (ZMod p) kG M₀ := IsScalarTower.of_compHom (ZMod p) kG M₀
  let _ : IsScalarTower (ZMod p) kG N₀ := IsScalarTower.of_compHom (ZMod p) kG N₀
  let _ : IsScalarTower (ZMod p) kG S := IsScalarTower.of_compHom (ZMod p) kG S
  let _ : Module.Finite (ZMod p) M₀ := .trans kG M₀
  let _ : Module.Finite (ZMod p) N₀ := .trans kG N₀
  let _ : Module.Finite (ZMod p) S := inferInstance
  let ρM := Representation.ofModule' (k := ZMod p) (G := G) M₀
  let ρN := Representation.ofModule' (k := ZMod p) (G := G) N₀
  let σ := Representation.ofModule' (k := ZMod p) (G := G) S
  let eM := TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) M₀
  let eN := TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) N₀
  let _ : Module.Finite kG ρM.asModule := Module.Finite.equiv eM.symm
  let _ : Module.Finite kG ρN.asModule := Module.Finite.equiv eN.symm
  let _ : Module.Projective kG ρM.asModule := Module.Projective.of_equiv' eM.symm
  let _ : Module.Projective kG ρN.asModule := Module.Projective.of_equiv' eN.symm
  rw [Representation.natCard_linearMap_eq_natCard_invariants_linHom (k := ZMod p) M₀ S,
    Representation.natCard_linearMap_eq_natCard_invariants_linHom (k := ZMod p) N₀ S]
  -- Lift the conjugation representations to projective `ℤ_p[G]`-modules `XM` and `XN`.
  obtain ⟨_, XM, hXMf, hXMp, fM, hfM⟩ :=
    exists_projective_reduction_bijective_of_projective p G (Representation.linHom ρM σ).asModule
  obtain ⟨_, XN, hXNf, hXNp, fN, hfN⟩ :=
    exists_projective_reduction_bijective_of_projective p G (Representation.linHom ρN σ).asModule
  let _ : Module.Finite (MonoidAlgebra ℤ_[p] G) XM := hXMf
  let _ : Module.Projective (MonoidAlgebra ℤ_[p] G) XM := hXMp
  let _ : Module.Finite (MonoidAlgebra ℤ_[p] G) XN := hXNf
  let _ : Module.Projective (MonoidAlgebra ℤ_[p] G) XN := hXNp
  let _ : Module.Finite ℤ_[p] XM := .trans (MonoidAlgebra ℤ_[p] G) XM
  let _ : Module.Finite ℤ_[p] XN := .trans (MonoidAlgebra ℤ_[p] G) XN
  let _ : Module.Projective ℤ_[p] XM := Module.Projective.trans (MonoidAlgebra ℤ_[p] G) XM
  let _ : Module.Projective ℤ_[p] XN := Module.Projective.trans (MonoidAlgebra ℤ_[p] G) XN
  refine natCard_invariants_eq_of_trace_eq p _ _ XM XN fM hfM fN hfN
    (trace_ofModule'_eq_of_forall_equiv_comp_zpowers p _ _ XM XN fM hfM fN hfN fun g hg ↦ ?_)
  obtain ⟨e, he⟩ := exists_linearEquiv_commute_reduction_of_not_dvd p (Subgroup.zpowers g)
    (by simpa only [Nat.card_zpowers] using hg) M N h
  exact Representation.nonempty_equiv_linHom_comp_of_equivariant ρM ρN σ _ e fun c x ↦ he c c.2 x

end Helpers

public section

/-- **Swan's theorem for `ℤ_p[G]`** (NSW (5.6.10)(ii)). Two finitely generated projective
`ℤ_p[G]`-modules with isomorphic rationalizations are isomorphic. -/
theorem nonempty_linearEquiv_of_projective_of_tensorRat
    (p : ℕ) [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module ℤ_[p] M]
    [Module (MonoidAlgebra ℤ_[p] G) M]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) M]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) M]
    [AddCommGroup N] [Module ℤ_[p] N] [Module (MonoidAlgebra ℤ_[p] G) N]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) N]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) N]
    [Module.Projective (MonoidAlgebra ℤ_[p] G) N]
    (h : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[MonoidAlgebra ℤ_[p] G]
      (N ⊗[ℤ_[p]] ℚ_[p]))) :
    Nonempty (M ≃ₗ[MonoidAlgebra ℤ_[p] G] N) := by
  classical
  let A := MonoidAlgebra ℤ_[p] G
  let kG := MonoidAlgebra (ZMod p) G
  let I := Ideal.span {(p : A)}
  let M₀ := M ⧸ I • (⊤ : Submodule A M)
  let N₀ := N ⧸ I • (⊤ : Submodule A N)
  let _ : Module.Finite kG M₀ := padicReduction_module_finite p G M
  let _ : Module.Finite kG N₀ := padicReduction_module_finite p G N
  let _ : Module.Projective kG M₀ := padicReduction_module_projective p G M
  let _ : Module.Projective kG N₀ := padicReduction_module_projective p G N
  let _ : Finite (G →₀ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  let _ : Finite kG := Finite.of_injective _ MonoidAlgebra.coeff_injective
  let _ : Finite (kG ⧸ Ring.jacobson kG) :=
    Finite.of_surjective (Ideal.Quotient.mk (Ring.jacobson kG)) Ideal.Quotient.mk_surjective
  -- Detect the reductions modulo `p` by counting maps to every simple `𝔽_p[G]`-module.
  obtain ⟨ered⟩ : Nonempty (M₀ ≃ₗ[kG] N₀) := by
    apply nonempty_linearEquiv_of_projective_of_natCard_linearMap_eq M₀ N₀
    intro S _ _ _
    let _ : Finite S := IsSimpleModule.finite_of_finite_quotient_jacobson (R := kG) S
    exact natCard_linearMap_reduction_eq_of_tensorRat p M N h S
  have := padicReduction_compatibleSMul_padicInt p G (padicReduction_smul p G M)
    (padicReduction_smul p G N)
  exact nonempty_linearEquiv_of_projective_of_reduction p G M N ⟨ered.restrictScalars A⟩

end

end TauCeti
