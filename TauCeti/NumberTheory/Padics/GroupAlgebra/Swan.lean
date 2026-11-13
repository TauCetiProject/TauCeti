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
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.NumberTheory.Padics.GroupAlgebra.Invariants
import TauCeti.NumberTheory.Padics.GroupAlgebra.Projective
import TauCeti.NumberTheory.Padics.GroupAlgebra.Reduction
import TauCeti.NumberTheory.Padics.GroupAlgebra.Trace
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
  obtain ⟨_, _, _, _, _⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := ℤ_[p]) C
      (fun _ _ ↦ rfl) M fun _ _ ↦ rfl
  obtain ⟨_, _, _, _, _⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := ℤ_[p]) C
      (fun _ _ ↦ rfl) N fun _ _ ↦ rfl
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
  exact ⟨e.restrictScalars (ZMod p), fun c hc x ↦
    Representation.map_ofModule'_comp C.subtype (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) e.toLinearMap
      ⟨c, hc⟩ x⟩

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
  refine Representation.natCard_invariants_eq_of_trace_eq p _ _ XM XN fM hfM fN hfN
    (trace_ofModule'_eq_of_forall_equiv_comp_zpowers p _ _ XM XN fM hfM fN hfN fun g hg ↦ ?_)
  obtain ⟨e, he⟩ := exists_linearEquiv_commute_reduction_of_not_dvd p (Subgroup.zpowers g)
    (by simpa only [Nat.card_zpowers] using hg) M N h
  exact ⟨Representation.Equiv.linHomComp (ρ := ρM) (ρ' := ρN) (f := (Subgroup.zpowers g).subtype)
    (.mk e fun c ↦ LinearMap.ext fun x ↦ he c c.2 x) σ⟩

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
