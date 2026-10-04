/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.GroupAlgebra.Rational
import TauCeti.Algebra.Module.Projective.Reduction
import TauCeti.Algebra.Module.Projective.Trans
import TauCeti.Algebra.MonoidAlgebra.CosetBasis
import TauCeti.Algebra.MonoidAlgebra.ProjectiveTrace
import TauCeti.NumberTheory.Padics.GroupAlgebra.Invariants
import TauCeti.NumberTheory.Padics.GroupAlgebra.Projective
import TauCeti.NumberTheory.Padics.GroupAlgebra.Reduction
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.LinHom
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

public section

open scoped TensorProduct Pointwise MonoidAlgebra
namespace TauCeti

private theorem reduction_mapDomain_commutes
    {p : ℕ} [Fact p.Prime] {G H : Type*} [Monoid G] [Monoid H] (f : G →* H)
    (a : MonoidAlgebra ℤ_[p] G) :
    MonoidAlgebra.mapRingHom H (PadicInt.toZMod (p := p))
        (MonoidAlgebra.mapDomainRingHom ℤ_[p] f a) =
      MonoidAlgebra.mapDomainRingHom (ZMod p) f
        (MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a) := by
  exact DFunLike.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom (PadicInt.toZMod (p := p)) f) a

private noncomputable def reductionLinearEquivOfRestrict
    {p : ℕ} [Fact p.Prime] {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (M N : Type*) [AddCommGroup M] [Module ℤ_[p] M]
    [Module (MonoidAlgebra ℤ_[p] H) M]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] H) M]
    [AddCommGroup N] [Module ℤ_[p] N] [Module (MonoidAlgebra ℤ_[p] H) N]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] H) N]
    [Module (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra ℤ_[p] H)]
    [Module (MonoidAlgebra ℤ_[p] G) M] [Module (MonoidAlgebra ℤ_[p] G) N]
    [IsScalarTower (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra ℤ_[p] H) M]
    [IsScalarTower (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra ℤ_[p] H) N]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) N]
    (hscalar : ∀ a b, a • b = MonoidAlgebra.mapDomainRingHom ℤ_[p] f a * b)
    (e : M ≃ₗ[MonoidAlgebra ℤ_[p] G] N) :
    let AH := MonoidAlgebra ℤ_[p] H
    let kH := MonoidAlgebra (ZMod p) H
    let J_M := Ideal.span {(p : AH)} • (⊤ : Submodule AH M)
    let J_N := Ideal.span {(p : AH)} • (⊤ : Submodule AH N)
    let _ : Module kH (M ⧸ J_M) := padicReductionModule p H M
    let _ : Module kH (N ⧸ J_N) := padicReductionModule p H N
    let _ : Module (MonoidAlgebra (ZMod p) G) (M ⧸ J_M) := Module.compHom _
      (MonoidAlgebra.mapDomainRingHom (ZMod p) f)
    let _ : Module (MonoidAlgebra (ZMod p) G) (N ⧸ J_N) := Module.compHom _
      (MonoidAlgebra.mapDomainRingHom (ZMod p) f)
    (M ⧸ J_M) ≃ₗ[MonoidAlgebra (ZMod p) G] (N ⧸ J_N) := by
  let AG := MonoidAlgebra ℤ_[p] G
  let AH := MonoidAlgebra ℤ_[p] H
  let kG := MonoidAlgebra (ZMod p) G
  let kH := MonoidAlgebra (ZMod p) H
  let J_M := Ideal.span {(p : AH)} • (⊤ : Submodule AH M)
  let J_N := Ideal.span {(p : AH)} • (⊤ : Submodule AH N)
  let _ : Module kH (M ⧸ J_M) := padicReductionModule p H M
  let _ : Module kH (N ⧸ J_N) := padicReductionModule p H N
  let ψ : kG →+* kH := MonoidAlgebra.mapDomainRingHom (ZMod p) f
  let _ : Module kG (M ⧸ J_M) := Module.compHom _ ψ
  let _ : Module kG (N ⧸ J_N) := Module.compHom _ ψ
  have he : Submodule.map e.toLinearMap (J_M.restrictScalars AG) =
      J_N.restrictScalars AG := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change x ∈ J_M at hx
      change e x ∈ J_N
      dsimp [J_M, J_N] at hx ⊢
      rw [← map_natCast (algebraMap ℤ_[p] AH) p] at hx ⊢
      obtain ⟨z, rfl⟩ := (Submodule.mem_span_algebraMap_smul_top_iff (p : ℤ_[p])).mp hx
      exact (Submodule.mem_span_algebraMap_smul_top_iff (p : ℤ_[p])).mpr
        ⟨e z, ((e.restrictScalars ℤ_[p]).map_smul (p : ℤ_[p]) z).symm⟩
    · intro y hy
      change y ∈ J_N at hy
      dsimp [J_N] at hy
      rw [← map_natCast (algebraMap ℤ_[p] AH) p] at hy
      obtain ⟨z, hz⟩ := (Submodule.mem_span_algebraMap_smul_top_iff (p : ℤ_[p])).mp hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ∈ J_M
      dsimp [J_M]
      rw [← map_natCast (algebraMap ℤ_[p] AH) p]
      refine (Submodule.mem_span_algebraMap_smul_top_iff (p : ℤ_[p])).mpr ⟨e.symm z, ?_⟩
      calc
        (p : ℤ_[p]) • e.symm z = e.symm ((p : ℤ_[p]) • z) :=
          ((e.symm.restrictScalars ℤ_[p]).map_smul _ _).symm
        _ = e.symm y := congrArg e.symm hz
  let eAG : (M ⧸ J_M) ≃ₗ[AG] (N ⧸ J_N) :=
    (Submodule.Quotient.restrictScalarsEquiv AG J_M).symm.trans
      ((Submodule.Quotient.equiv _ _ e he).trans
        (Submodule.Quotient.restrictScalarsEquiv AG J_N))
  exact
    { toFun := eAG
      invFun := eAG.symm
      map_add' := eAG.map_add
      map_smul' := fun b x ↦ by
        obtain ⟨a, rfl⟩ := padicMonoidAlgebraReduction_surjective p G b
        simp only [RingHom.id_apply]
        have hsquare := reduction_mapDomain_commutes f a
        change eAG (ψ (MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a) • x) =
          ψ (MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a) • eAG x
        rw [show ψ (MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a) =
          MonoidAlgebra.mapRingHom H (PadicInt.toZMod (p := p))
            (MonoidAlgebra.mapDomainRingHom ℤ_[p] f a) from hsquare.symm]
        rw [padicReduction_smul, padicReduction_smul]
        have hsmulM : MonoidAlgebra.mapDomainRingHom ℤ_[p] f a • x = a • x := by
          calc
            MonoidAlgebra.mapDomainRingHom ℤ_[p] f a • x = (a • (1 : AH)) • x := by
              rw [hscalar, mul_one]
            _ = a • ((1 : AH) • x) := smul_assoc a (1 : AH) x
            _ = a • x := by rw [one_smul]
        have hsmulN : MonoidAlgebra.mapDomainRingHom ℤ_[p] f a • eAG x = a • eAG x := by
          calc
            MonoidAlgebra.mapDomainRingHom ℤ_[p] f a • eAG x =
                (a • (1 : AH)) • eAG x := by rw [hscalar, mul_one]
            _ = a • ((1 : AH) • eAG x) := smul_assoc a (1 : AH) (eAG x)
            _ = a • eAG x := by rw [one_smul]
        rw [hsmulM, hsmulN, eAG.map_smul]
      left_inv := eAG.left_inv
      right_inv := eAG.right_inv }

private noncomputable def reductionRestrictionEquiv
    {p : ℕ} [Fact p.Prime] {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (X : Type*) [AddCommGroup X] [Module ℤ_[p] X]
    [Module (MonoidAlgebra ℤ_[p] H) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] H) X]
    [Module (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra ℤ_[p] H)]
    [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra ℤ_[p] H) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X]
    (hscalar : ∀ a b, a • b = MonoidAlgebra.mapDomainRingHom ℤ_[p] f a * b) :
    let AG := MonoidAlgebra ℤ_[p] G
    let AH := MonoidAlgebra ℤ_[p] H
    let kG := MonoidAlgebra (ZMod p) G
    let kH := MonoidAlgebra (ZMod p) H
    let J_G := Ideal.span {(p : AG)} • (⊤ : Submodule AG X)
    let J_H := Ideal.span {(p : AH)} • (⊤ : Submodule AH X)
    let _ : Module kG (X ⧸ J_G) := padicReductionModule p G X
    let _ : Module kH (X ⧸ J_H) := padicReductionModule p H X
    let _ : Module kG (X ⧸ J_H) := Module.compHom _
      (MonoidAlgebra.mapDomainRingHom (ZMod p) f)
    (X ⧸ J_G) ≃ₗ[kG] (X ⧸ J_H) := by
  let AG := MonoidAlgebra ℤ_[p] G
  let AH := MonoidAlgebra ℤ_[p] H
  let kG := MonoidAlgebra (ZMod p) G
  let kH := MonoidAlgebra (ZMod p) H
  let J_G := Ideal.span {(p : AG)} • (⊤ : Submodule AG X)
  let J_H := Ideal.span {(p : AH)} • (⊤ : Submodule AH X)
  let _ : Module kG (X ⧸ J_G) := padicReductionModule p G X
  let _ : Module kH (X ⧸ J_H) := padicReductionModule p H X
  let ψ : kG →+* kH := MonoidAlgebra.mapDomainRingHom (ZMod p) f
  let _ : Module kG (X ⧸ J_H) := Module.compHom _ ψ
  have hJ : J_G = J_H.restrictScalars AG := by
    ext x
    change x ∈ J_G ↔ x ∈ J_H
    dsimp [J_G, J_H]
    rw [← map_natCast (algebraMap ℤ_[p] AG) p,
      ← map_natCast (algebraMap ℤ_[p] AH) p,
      Submodule.mem_span_algebraMap_smul_top_iff,
      Submodule.mem_span_algebraMap_smul_top_iff]
  let eAG : (X ⧸ J_G) ≃ₗ[AG] (X ⧸ J_H) :=
    (Submodule.quotEquivOfEq _ _ hJ).trans
      (Submodule.Quotient.restrictScalarsEquiv AG J_H)
  exact
    { toFun := eAG
      invFun := eAG.symm
      map_add' := eAG.map_add
      map_smul' := fun b x ↦ by
        obtain ⟨a, rfl⟩ := padicMonoidAlgebraReduction_surjective p G b
        simp only [RingHom.id_apply]
        have hsquare := reduction_mapDomain_commutes f a
        rw [padicReduction_smul]
        change eAG (a • x) = ψ (MonoidAlgebra.mapRingHom G
          (PadicInt.toZMod (p := p)) a) • eAG x
        rw [show ψ (MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a) =
          MonoidAlgebra.mapRingHom H (PadicInt.toZMod (p := p))
            (MonoidAlgebra.mapDomainRingHom ℤ_[p] f a) from hsquare.symm,
          padicReduction_smul]
        have hsmul : MonoidAlgebra.mapDomainRingHom ℤ_[p] f a • eAG x = a • eAG x := by
          calc
            MonoidAlgebra.mapDomainRingHom ℤ_[p] f a • eAG x =
                (a • (1 : AH)) • eAG x := by rw [hscalar, mul_one]
            _ = a • ((1 : AH) • eAG x) := smul_assoc a (1 : AH) (eAG x)
            _ = a • eAG x := by rw [one_smul]
        rw [eAG.map_smul, hsmul]
      left_inv := eAG.left_inv
      right_inv := eAG.right_inv }

private noncomputable def projectiveLiftReductionMap
    {p : ℕ} [Fact p.Prime] {G : Type*} [Monoid G]
    (X Y : Type*) [AddCommGroup X] [Module ℤ_[p] X]
    [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X]
    [AddCommGroup Y] [Module (ZMod p) Y] [Module (MonoidAlgebra (ZMod p) G) Y]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) Y]
    (f : (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] Y) :
    X →ₛₗ[PadicInt.toZMod (p := p)] Y := by
  let _ : Module (MonoidAlgebra (ZMod p) G)
      (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) := padicReductionModule p G X
  exact
    { toFun := fun x ↦ f (padicReductionMk p G X x)
      map_add' := fun x y ↦ by simp
      map_smul' := fun r x ↦ by
        rw [← algebraMap_smul (MonoidAlgebra ℤ_[p] G),
          LinearMap.map_smulₛₗ (padicReductionMk p G X), padicReduction_smul,
          LinearMap.map_smulₛₗ f]
        rw [show MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p))
            (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G) r) =
          algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (PadicInt.toZMod r) by
            exact DFunLike.congr_fun
              (MonoidAlgebra.mapRingHom_comp_algebraMap (M := G)
                (PadicInt.toZMod (p := p))) r]
        exact algebraMap_smul (MonoidAlgebra (ZMod p) G) _ _ }

private theorem projectiveLiftReductionMap_surjective
    {p : ℕ} [Fact p.Prime] {G : Type*} [Monoid G]
    (X Y : Type*) [AddCommGroup X] [Module ℤ_[p] X]
    [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X]
    [AddCommGroup Y] [Module (ZMod p) Y] [Module (MonoidAlgebra (ZMod p) G) Y]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) Y]
    (f : (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] Y)
    (hf : Function.Surjective f) :
    Function.Surjective (projectiveLiftReductionMap X Y f) := by
  let _ : Module (MonoidAlgebra (ZMod p) G)
      (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) := padicReductionModule p G X
  exact hf.comp (padicReductionMk_surjective p G X)

private theorem projectiveLiftReductionMap_apply_group
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (X Y : Type*) [AddCommGroup X] [Module ℤ_[p] X]
    [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X]
    [AddCommGroup Y] [Module (ZMod p) Y] [Module (MonoidAlgebra (ZMod p) G) Y]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) Y]
    (f : (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] Y)
    (g : G) (x : X) :
    projectiveLiftReductionMap X Y f
        (Representation.ofModule' (k := ℤ_[p]) (G := G) X g x) =
      Representation.ofModule' (k := ZMod p) (G := G) Y g
        (projectiveLiftReductionMap X Y f x) := by
  let _ : Module (MonoidAlgebra (ZMod p) G)
      (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) := padicReductionModule p G X
  rw [TauCeti.Representation.ofModule'_apply, TauCeti.Representation.ofModule'_apply]
  change f (padicReductionMk p G X (MonoidAlgebra.single g 1 • x)) =
    MonoidAlgebra.single g 1 • f (padicReductionMk p G X x)
  rw [LinearMap.map_smulₛₗ (padicReductionMk p G X), padicReduction_smul,
    LinearMap.map_smulₛₗ f]
  simp

private theorem projectiveLiftReductionMap_eq_zero_iff
    {p : ℕ} [Fact p.Prime] {G : Type*} [Monoid G]
    (X Y : Type*) [AddCommGroup X] [Module ℤ_[p] X]
    [Module (MonoidAlgebra ℤ_[p] G) X]
    [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) X]
    [AddCommGroup Y] [Module (ZMod p) Y] [Module (MonoidAlgebra (ZMod p) G) Y]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) Y]
    (f : (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] Y)
    (hf : Function.Injective f) (x : X) :
    projectiveLiftReductionMap X Y f x = 0 ↔
      x ∈ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] X) := by
  let _ : Module (MonoidAlgebra (ZMod p) G)
      (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) := padicReductionModule p G X
  change f (padicReductionMk p G X x) = 0 ↔ _
  rw [show f (padicReductionMk p G X x) = 0 ↔ padicReductionMk p G X x = 0 by
    exact ⟨fun h ↦ hf (h.trans (map_zero f).symm), fun h ↦ by rw [h, map_zero]⟩,
    padicReductionMk_eq_zero_iff]
  rw [← map_natCast (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G)) p,
    Submodule.mem_span_algebraMap_smul_top_iff]
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, Submodule.mem_top, hw⟩
  · rintro ⟨w, -, hw⟩
    exact ⟨w, hw⟩

private noncomputable def projectiveLiftReductionLinearEquiv
    {p : ℕ} [Fact p.Prime] {G : Type*} [Monoid G]
    (X Y : Type*) [AddCommGroup X]
    [Module (MonoidAlgebra ℤ_[p] G) X]
    [AddCommGroup Y] [Module (MonoidAlgebra (ZMod p) G) Y]
    (f : (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) →ₛₗ[MonoidAlgebra.mapRingHom G
        (PadicInt.toZMod (p := p))] Y)
    (hf : Function.Bijective f) :
    let _ : Module (MonoidAlgebra (ZMod p) G)
      (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) := padicReductionModule p G X
    (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
      (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) ≃ₗ[MonoidAlgebra (ZMod p) G] Y := by
  let _ : Module (MonoidAlgebra (ZMod p) G)
      (X ⧸ Ideal.span {(p : MonoidAlgebra ℤ_[p] G)} •
        (⊤ : Submodule (MonoidAlgebra ℤ_[p] G) X)) := padicReductionModule p G X
  apply LinearEquiv.ofBijective
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun b x ↦ by
        obtain ⟨a, rfl⟩ := padicMonoidAlgebraReduction_surjective p G b
        rw [padicReduction_smul, LinearMap.map_smulₛₗ f]
        rfl }
  exact hf

private noncomputable def invariantsLinearEquivOfEquiv
    {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.invariants ≃ₗ[k] σ.invariants where
  toFun x := ⟨e x, fun g ↦ by
    calc
      σ g (e x) = e (ρ g x) :=
        (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g x).symm
      _ = e x := congrArg e (x.property g)⟩
  invFun x := ⟨e.symm x, fun g ↦ by
    calc
      ρ g (e.symm x) = e.symm (σ g x) :=
        (Representation.IntertwiningMap.isIntertwining σ ρ e.symm.toIntertwiningMap g x).symm
      _ = e.symm x := congrArg e.symm (x.property g)⟩
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' r x := Subtype.ext (e.map_smul r x)
  left_inv x := Subtype.ext (e.left_inv x)
  right_inv x := Subtype.ext (e.right_inv x)

private noncomputable def precompLinearEquiv
    {k V V' W : Type*} [CommSemiring k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] V') : (V →ₗ[k] W) ≃ₗ[k] (V' →ₗ[k] W) where
  toFun f := f ∘ₗ e.symm.toLinearMap
  invFun f := f ∘ₗ e.toLinearMap
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv f := by ext x; exact congrArg f (e.symm_apply_apply x)
  right_inv f := by ext x; exact congrArg f (e.apply_symm_apply x)

universe u v w

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
  let _ : Module kG M₀ := padicReductionModule p G M
  let _ : Module kG N₀ := padicReductionModule p G N
  let _ : Module.Finite kG M₀ := padicReduction_module_finite p G M
  let _ : Module.Finite kG N₀ := padicReduction_module_finite p G N
  let _ : Module.Projective kG M₀ := padicReduction_module_projective p G M
  let _ : Module.Projective kG N₀ := padicReduction_module_projective p G N
  let _ : Finite (G →₀ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  let _ : Finite kG := Finite.of_injective _ MonoidAlgebra.coeff_injective
  let _ : Finite (kG ⧸ Ring.jacobson kG) :=
    Finite.of_surjective (Ideal.Quotient.mk (Ring.jacobson kG))
      Ideal.Quotient.mk_surjective
  have hred : Nonempty (M₀ ≃ₗ[kG] N₀) := by
    apply nonempty_linearEquiv_of_projective_of_natCard_linearMap_eq M₀ N₀
    intro S _ _ _
    let _ : Finite S := IsSimpleModule.finite_of_finite_quotient_jacobson (R := kG) S
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
    let eM : ρM.asModule ≃ₗ[kG] M₀ :=
      TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) M₀
    let eN : ρN.asModule ≃ₗ[kG] N₀ :=
      TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) N₀
    let eS : σ.asModule ≃ₗ[kG] S :=
      TauCeti.Representation.ofModule'AsModuleEquiv (k := ZMod p) (G := G) S
    let _ : Module.Finite kG ρM.asModule := Module.Finite.equiv eM.symm
    let _ : Module.Finite kG ρN.asModule := Module.Finite.equiv eN.symm
    let _ : Module.Projective kG ρM.asModule := Module.Projective.of_equiv' eM.symm
    let _ : Module.Projective kG ρN.asModule := Module.Projective.of_equiv' eN.symm
    let YM := Representation.linHom ρM σ
    let YN := Representation.linHom ρN σ
    let ePostM : (ρM.asModule →ₗ[kG] σ.asModule) ≃ₗ[ZMod p]
        (ρM.asModule →ₗ[kG] S) :=
      { toFun := fun f ↦ eS.toLinearMap ∘ₗ f
        invFun := fun f ↦ eS.symm.toLinearMap ∘ₗ f
        map_add' := fun f g ↦ by ext; simp
        map_smul' := fun r f ↦ by
          ext x
          simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
          exact (eS.restrictScalars (ZMod p)).map_smul r (f x)
        left_inv := fun f ↦ by ext; simp
        right_inv := fun f ↦ by ext; simp }
    let ePostN : (ρN.asModule →ₗ[kG] σ.asModule) ≃ₗ[ZMod p]
        (ρN.asModule →ₗ[kG] S) :=
      { toFun := fun f ↦ eS.toLinearMap ∘ₗ f
        invFun := fun f ↦ eS.symm.toLinearMap ∘ₗ f
        map_add' := fun f g ↦ by ext; simp
        map_smul' := fun r f ↦ by
          ext x
          simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
          exact (eS.restrictScalars (ZMod p)).map_smul r (f x)
        left_inv := fun f ↦ by ext; simp
        right_inv := fun f ↦ by ext; simp }
    let eHomM : YM.invariants ≃ₗ[ZMod p] (M₀ →ₗ[kG] S) :=
      (Representation.invariantsEquivIntertwiningMap ρM σ).trans
        ((Representation.IntertwiningMap.equivLinearMapAsModule ρM σ).trans
          (ePostM.trans (LinearEquiv.congrLeft S (ZMod p) eM)))
    let eHomN : YN.invariants ≃ₗ[ZMod p] (N₀ →ₗ[kG] S) :=
      (Representation.invariantsEquivIntertwiningMap ρN σ).trans
        ((Representation.IntertwiningMap.equivLinearMapAsModule ρN σ).trans
          (ePostN.trans (LinearEquiv.congrLeft S (ZMod p) eN)))
    rw [← Nat.card_congr eHomM.toEquiv, ← Nat.card_congr eHomN.toEquiv]
    let _ : Module.Finite kG YM.asModule := inferInstance
    let _ : Module.Finite kG YN.asModule := inferInstance
    let _ : Module.Projective kG YM.asModule := inferInstance
    let _ : Module.Projective kG YN.asModule := inferInstance
    obtain ⟨_, XM, hXMf, hXMp, fM, hfM⟩ :=
      exists_projective_reduction_bijective_of_projective p G YM.asModule
    obtain ⟨_, XN, hXNf, hXNp, fN, hfN⟩ :=
      exists_projective_reduction_bijective_of_projective p G YN.asModule
    let _ : Module.Finite A XM := hXMf
    let _ : Module.Projective A XM := hXMp
    let _ : Module.Finite A XN := hXNf
    let _ : Module.Projective A XN := hXNp
    let _ : Module.Finite ℤ_[p] XM := .trans A XM
    let _ : Module.Finite ℤ_[p] XN := .trans A XN
    let _ : Module.Projective ℤ_[p] XM := Module.Projective.trans (S := A)
    let _ : Module.Projective ℤ_[p] XN := Module.Projective.trans (S := A)
    let ηM := Representation.ofModule' (k := ZMod p) (G := G) YM.asModule
    let ηN := Representation.ofModule' (k := ZMod p) (G := G) YN.asModule
    let ξM := Representation.ofModule' (k := ℤ_[p]) (G := G) XM
    let ξN := Representation.ofModule' (k := ℤ_[p]) (G := G) XN
    let eηM : ηM.Equiv YM := TauCeti.Representation.equivOfAsModuleLinearEquiv
      (TauCeti.Representation.ofModule'AsModuleEquiv YM.asModule)
    let eηN : ηN.Equiv YN := TauCeti.Representation.equivOfAsModuleLinearEquiv
      (TauCeti.Representation.ofModule'AsModuleEquiv YN.asModule)
    let _ : Module.Projective kG ηM.asModule := Module.Projective.of_equiv'
      (TauCeti.Representation.ofModule'AsModuleEquiv YM.asModule).symm
    let _ : Module.Projective kG ηN.asModule := Module.Projective.of_equiv'
      (TauCeti.Representation.ofModule'AsModuleEquiv YN.asModule).symm
    have hcountM : Nat.card YM.invariants =
        p ^ Module.finrank ℤ_[p] ξM.invariants := by
      rw [← Nat.card_congr (invariantsLinearEquivOfEquiv eηM).toEquiv]
      exact Representation.natCard_invariants_eq_pow_finrank_of_reduction p ξM ηM
        (projectiveLiftReductionMap XM YM.asModule fM)
        (projectiveLiftReductionMap_surjective XM YM.asModule fM hfM.2)
        (projectiveLiftReductionMap_apply_group XM YM.asModule fM)
        (projectiveLiftReductionMap_eq_zero_iff XM YM.asModule fM hfM.1)
    have hcountN : Nat.card YN.invariants =
        p ^ Module.finrank ℤ_[p] ξN.invariants := by
      rw [← Nat.card_congr (invariantsLinearEquivOfEquiv eηN).toEquiv]
      exact Representation.natCard_invariants_eq_pow_finrank_of_reduction p ξN ηN
        (projectiveLiftReductionMap XN YN.asModule fN)
        (projectiveLiftReductionMap_surjective XN YN.asModule fN hfN.2)
        (projectiveLiftReductionMap_apply_group XN YN.asModule fN)
        (projectiveLiftReductionMap_eq_zero_iff XN YN.asModule fN hfN.1)
    rw [hcountM, hcountN]
    congr 1
    rw [← Representation.finrank_invariants_baseChange_ratPadic p ξM,
      ← Representation.finrank_invariants_baseChange_ratPadic p ξN]
    let _ := Fintype.ofFinite G
    let _ : Invertible (Nat.card G : ℚ_[p]) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    apply Nat.cast_injective (R := ℚ_[p])
    rw [← (Representation.baseChange ℚ_[p] ξM).card_inv_mul_sum_char_eq_finrank,
      ← (Representation.baseChange ℚ_[p] ξN).card_inv_mul_sum_char_eq_finrank]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    simp only [Representation.character, Representation.baseChange_apply,
      LinearMap.trace_baseChange]
    congr 1
    by_cases hg : p ∣ orderOf g
    · rw [trace_ofModule'_eq_zero_of_dvd_orderOf XM (p := p)
          (show ¬IsUnit (p : ℤ_[p]) by exact PadicInt.p_nonunit) hg,
        trace_ofModule'_eq_zero_of_dvd_orderOf XN (p := p)
          (show ¬IsUnit (p : ℤ_[p]) by exact PadicInt.p_nonunit) hg]
    · let C := Subgroup.zpowers g
      let AC := MonoidAlgebra ℤ_[p] C
      let kC := MonoidAlgebra (ZMod p) C
      let φA : AC →+* A := MonoidAlgebra.mapDomainRingHom ℤ_[p] C.subtype
      let φk : kC →+* kG := MonoidAlgebra.mapDomainRingHom (ZMod p) C.subtype
      let _ : Module AC A := φA.toModule
      let _ : IsScalarTower AC A A := ⟨fun r s t ↦ mul_assoc (φA r) s t⟩
      let _ : Module AC M := Module.compHom M φA
      let _ : Module AC N := Module.compHom N φA
      let _ : IsScalarTower AC A M := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
      let _ : IsScalarTower AC A N := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
      let _ : IsScalarTower ℤ_[p] AC M := ⟨fun r s x ↦ by
        change φA (r • s) • x = r • (φA s • x)
        rw [show φA (r • s) = r • φA s by simp [φA, AC, A]]
        exact smul_assoc r _ x⟩
      let _ : IsScalarTower ℤ_[p] AC N := ⟨fun r s x ↦ by
        change φA (r • s) • x = r • (φA s • x)
        rw [show φA (r • s) = r • φA s by simp [φA, AC, A]]
        exact smul_assoc r _ x⟩
      let b := TauCeti.MonoidAlgebra.basisCosets ℤ_[p] C.subtype C.subtype_injective
      let _ : Module.Free AC A := .of_basis b
      let _ : Module.Finite AC A := .of_basis b
      let _ : Module.Projective AC A := inferInstance
      let _ : Module.Projective AC M :=
        @Module.Projective.trans AC A M _ _ _ _ _ _ _ _ inferInstance inferInstance
      let _ : Module.Projective AC N :=
        @Module.Projective.trans AC A N _ _ _ _ _ _ _ _ inferInstance inferInstance
      let _ : Module.Finite AC M := .trans A M
      let _ : Module.Finite AC N := .trans A N
      obtain ⟨eMN⟩ := nonempty_linearEquiv_of_projective_of_tensorRat_of_not_dvd p
        (by simpa only [C, Nat.card_zpowers] using hg) M N
        (h.map fun e ↦ e.restrictScalars AC)
      let _ : Module kC M₀ := Module.compHom M₀ φk
      let _ : Module kC N₀ := Module.compHom N₀ φk
      let _ : Module kC S := Module.compHom S φk
      let _ : IsScalarTower (ZMod p) kC M₀ := ⟨fun r a x ↦ by
        change φk (r • a) • x = r • (φk a • x)
        rw [show φk (r • a) = r • φk a by simp [φk, kC, kG]]
        exact smul_assoc r _ x⟩
      let _ : IsScalarTower (ZMod p) kC N₀ := ⟨fun r a x ↦ by
        change φk (r • a) • x = r • (φk a • x)
        rw [show φk (r • a) = r • φk a by simp [φk, kC, kG]]
        exact smul_assoc r _ x⟩
      let _ : IsScalarTower (ZMod p) kC S := ⟨fun r a x ↦ by
        change φk (r • a) • x = r • (φk a • x)
        rw [show φk (r • a) = r • φk a by simp [φk, kC, kG]]
        exact smul_assoc r _ x⟩
      let eMN₀ : M₀ ≃ₗ[kC] N₀ := reductionLinearEquivOfRestrict C.subtype M N
        (fun _ _ ↦ rfl) eMN
      have heMN₀ (c : C) (x : M₀) : eMN₀ (ρM c x) = ρN c (eMN₀ x) := by
        have he := eMN₀.map_smul (MonoidAlgebra.single c (1 : ZMod p)) x
        rw [TauCeti.Representation.ofModule'_apply, TauCeti.Representation.ofModule'_apply]
        change eMN₀ ((MonoidAlgebra.single (c : G) (1 : ZMod p) : kG) • x) =
          (MonoidAlgebra.single (c : G) (1 : ZMod p) : kG) • eMN₀ x
        rw [← show φk (MonoidAlgebra.single c (1 : ZMod p)) =
          (MonoidAlgebra.single (c : G) (1 : ZMod p) : kG) by
            change MonoidAlgebra.mapDomain C.subtype (MonoidAlgebra.single c 1) = _
            rw [MonoidAlgebra.mapDomain_single]
            rfl]
        exact he
      let eBase : M₀ ≃ₗ[ZMod p] N₀ :=
        { toFun := eMN₀
          invFun := eMN₀.symm
          map_add' := eMN₀.map_add
          map_smul' := fun r x ↦ by
            have he := eMN₀.map_smul (algebraMap (ZMod p) kC r) x
            simpa only [algebraMap_smul, RingHom.id_apply] using he
          left_inv := eMN₀.left_inv
          right_inv := eMN₀.right_inv }
      let ePre : (M₀ →ₗ[ZMod p] S) ≃ₗ[ZMod p] (N₀ →ₗ[ZMod p] S) :=
        precompLinearEquiv eBase
      let YMC : Representation (ZMod p) C (M₀ →ₗ[ZMod p] S) := YM.comp C.subtype
      let YNC : Representation (ZMod p) C (N₀ →ₗ[ZMod p] S) := YN.comp C.subtype
      let eY : YMC.Equiv YNC :=
        .mk ePre (by
          intro c
          apply LinearMap.ext
          intro f
          apply LinearMap.ext
          intro x
          simp only [YMC, YNC, ePre, LinearMap.comp_apply]
          apply congrArg (σ c)
          apply congrArg f
          apply eMN₀.injective
          change eMN₀ (ρM (↑(c⁻¹) : G) (eMN₀.symm x)) =
            eMN₀ (eMN₀.symm (ρN (↑(c⁻¹) : G) x))
          rw [heMN₀, eMN₀.apply_symm_apply, eMN₀.apply_symm_apply])
      let _ : Module AC XM := Module.compHom XM φA
      let _ : Module AC XN := Module.compHom XN φA
      let _ : IsScalarTower AC A XM := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
      let _ : IsScalarTower AC A XN := ⟨fun r s x ↦ mul_smul (φA r) s x⟩
      let _ : IsScalarTower ℤ_[p] AC XM := ⟨fun r s x ↦ by
        change φA (r • s) • x = r • (φA s • x)
        rw [show φA (r • s) = r • φA s by simp [φA, AC, A]]
        exact smul_assoc r _ x⟩
      let _ : IsScalarTower ℤ_[p] AC XN := ⟨fun r s x ↦ by
        change φA (r • s) • x = r • (φA s • x)
        rw [show φA (r • s) = r • φA s by simp [φA, AC, A]]
        exact smul_assoc r _ x⟩
      let _ : Module.Projective AC XM :=
        @Module.Projective.trans AC A XM _ _ _ _ _ _ _ _ inferInstance inferInstance
      let _ : Module.Projective AC XN :=
        @Module.Projective.trans AC A XN _ _ _ _ _ _ _ _ inferInstance inferInstance
      let _ : Module.Finite AC XM := .trans A XM
      let _ : Module.Finite AC XN := .trans A XN
      let QXM := XM ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A XM)
      let QXN := XN ⧸ Ideal.span {(p : A)} • (⊤ : Submodule A XN)
      let _ : Module kG QXM := padicReductionModule p G XM
      let _ : Module kG QXN := padicReductionModule p G XN
      let _ : Module kC QXM := Module.compHom QXM φk
      let _ : Module kC QXN := Module.compHom QXN φk
      let eLiftM : QXM ≃ₗ[kG] YM.asModule :=
        projectiveLiftReductionLinearEquiv XM YM.asModule fM hfM
      let eLiftN : QXN ≃ₗ[kG] YN.asModule :=
        projectiveLiftReductionLinearEquiv XN YN.asModule fN hfN
      let eLiftMC : QXM ≃ₗ[kC] YMC.asModule :=
        { toFun := eLiftM
          invFun := eLiftM.symm
          map_add' := eLiftM.map_add
          map_smul' := fun a x ↦ by
            change eLiftM (φk a • x) = YMC.asAlgebraHom a (eLiftM x)
            rw [eLiftM.map_smul]
            have hYM : YM.asAlgebraHom.comp
                (MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p) C.subtype) =
                YMC.asAlgebraHom :=
              MonoidAlgebra.algHom_ext (fun c ↦ by simp [YMC]) (Subsingleton.elim _ _)
            exact congrArg (fun T : Module.End (ZMod p) (M₀ →ₗ[ZMod p] S) ↦ T (eLiftM x))
              (AlgHom.congr_fun hYM a)
          left_inv := eLiftM.left_inv
          right_inv := eLiftM.right_inv }
      let eLiftNC : QXN ≃ₗ[kC] YNC.asModule :=
        { toFun := eLiftN
          invFun := eLiftN.symm
          map_add' := eLiftN.map_add
          map_smul' := fun a x ↦ by
            change eLiftN (φk a • x) = YNC.asAlgebraHom a (eLiftN x)
            rw [eLiftN.map_smul]
            have hYN : YN.asAlgebraHom.comp
                (MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p) C.subtype) =
                YNC.asAlgebraHom :=
              MonoidAlgebra.algHom_ext (fun c ↦ by simp [YNC]) (Subsingleton.elim _ _)
            exact congrArg (fun T : Module.End (ZMod p) (N₀ →ₗ[ZMod p] S) ↦ T (eLiftN x))
              (AlgHom.congr_fun hYN a)
          left_inv := eLiftN.left_inv
          right_inv := eLiftN.right_inv }
      let eYmod : YMC.asModule ≃ₗ[kC] YNC.asModule :=
        TauCeti.Representation.asModuleLinearEquivOfEquiv eY
      let JXM := Ideal.span {(p : AC)} • (⊤ : Submodule AC XM)
      let JXN := Ideal.span {(p : AC)} • (⊤ : Submodule AC XN)
      let _ : Module kC (XM ⧸ JXM) := padicReductionModule p C XM
      let _ : Module kC (XN ⧸ JXN) := padicReductionModule p C XN
      let eRestM : (XM ⧸ JXM) ≃ₗ[kC] QXM :=
        reductionRestrictionEquiv C.subtype XM (fun _ _ ↦ rfl)
      let eRestN : (XN ⧸ JXN) ≃ₗ[kC] QXN :=
        reductionRestrictionEquiv C.subtype XN (fun _ _ ↦ rfl)
      let eRedC : (XM ⧸ JXM) ≃ₗ[kC] (XN ⧸ JXN) :=
        eRestM.trans (eLiftMC.trans (eYmod.trans (eLiftNC.symm.trans eRestN.symm)))
      let eRedCA : (XM ⧸ JXM) ≃ₗ[AC] (XN ⧸ JXN) :=
        { toFun := eRedC
          invFun := eRedC.symm
          map_add' := eRedC.map_add
          map_smul' := fun a x ↦ by
            calc
              eRedC (a • x) = eRedC
                  (MonoidAlgebra.mapRingHom C (PadicInt.toZMod (p := p)) a • x) := by
                    rw [padicReduction_smul]
              _ = MonoidAlgebra.mapRingHom C (PadicInt.toZMod (p := p)) a • eRedC x :=
                eRedC.map_smul _ _
              _ = a • eRedC x := padicReduction_smul p C XN a (eRedC x)
          left_inv := eRedC.left_inv
          right_inv := eRedC.right_inv }
      obtain ⟨eX⟩ := nonempty_linearEquiv_of_projective_of_reduction p C XM XN ⟨eRedCA⟩
      let eXZ : XM ≃ₗ[ℤ_[p]] XN :=
        { toFun := eX
          invFun := eX.symm
          map_add' := eX.map_add
          map_smul' := eX.toLinearMap.map_smul_of_tower
          left_inv := eX.left_inv
          right_inv := eX.right_inv }
      have heX (x : XM) : eXZ (ξM g x) = ξN g (eXZ x) := by
        let cg : C := ⟨g, by simp [C]⟩
        have he := eX.map_smul (MonoidAlgebra.single cg (1 : ℤ_[p])) x
        rw [TauCeti.Representation.ofModule'_apply, TauCeti.Representation.ofModule'_apply]
        change eX ((MonoidAlgebra.single g (1 : ℤ_[p]) : A) • x) =
          (MonoidAlgebra.single g (1 : ℤ_[p]) : A) • eX x
        rw [← show φA (MonoidAlgebra.single cg (1 : ℤ_[p])) =
          (MonoidAlgebra.single g (1 : ℤ_[p]) : A) by
            change MonoidAlgebra.mapDomain C.subtype (MonoidAlgebra.single cg 1) = _
            rw [MonoidAlgebra.mapDomain_single]
            rfl]
        exact he
      have hconj : eXZ.conj (Representation.ofModule' XM g) =
          Representation.ofModule' XN g := by
        apply LinearMap.ext
        intro x
        simp only [LinearEquiv.conj_apply_apply]
        rw [heX, eXZ.apply_symm_apply]
      rw [← hconj, LinearMap.trace_conj']
  obtain ⟨ered⟩ := hred
  let eredA : M₀ ≃ₗ[A] N₀ :=
    { toFun := ered
      invFun := ered.symm
      map_add' := ered.map_add
      map_smul' := fun a x ↦ by
        calc
          ered (a • x) = ered
              (MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a • x) := by
                rw [padicReduction_smul]
          _ = MonoidAlgebra.mapRingHom G (PadicInt.toZMod (p := p)) a • ered x :=
            ered.map_smul _ _
          _ = a • ered x := padicReduction_smul p G N a (ered x)
      left_inv := ered.left_inv
      right_inv := ered.right_inv }
  exact nonempty_linearEquiv_of_projective_of_reduction p G M N ⟨eredA⟩

end TauCeti
