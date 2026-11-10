/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.GroupTheory.Coset.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TauCeti.Algebra.Module.Projective.Trans

/-!
# Coset bases of group algebras

An injective group homomorphism `p : M →* N` makes `R[N]` free as a left `R[M]`-module, with
scalars acting through `mapDomainRingHom R p`. The basis consists of the inverses of chosen
left-coset representatives of `p.range`, which represent its right cosets.

## Main definitions

* `TauCeti.MonoidAlgebra.basisCosets`: the coset basis of `R[N]` over `R[M]`.
* `MonoidAlgebra.restrictSubgroup_isScalarTower_finite_projective`: restricting a finitely
  generated projective `R[G]`-module to the group algebra of a subgroup of a finite group keeps it
  finitely generated and projective, with the scalar towers needed for that.
-/

public section

noncomputable section

open MonoidAlgebra

namespace TauCeti.MonoidAlgebra

variable {R M N : Type*} [Semiring R] [Group M] [Group N]

/-- Regroup coefficients using `(q, m) ↦ p m * q.out⁻¹`, obtained by inverting the usual
left-coset decomposition. -/
private def cosetAddEquiv (p : M →* N) (hp : Function.Injective p) :
    ((N ⧸ p.range) →₀ R[M]) ≃+ R[N] :=
  (Finsupp.mapRange.addEquiv coeffAddEquiv).trans <|
    Finsupp.curryAddEquiv.symm.trans <|
      (Finsupp.domCongr ((Equiv.prodCongr (Equiv.refl _)
        ((Equiv.inv M).trans (MonoidHom.ofInjective hp).toEquiv)).trans
          (Subgroup.groupEquivQuotientProdSubgroup.symm.trans (Equiv.inv N)))).trans
            coeffAddEquiv.symm

private theorem cosetAddEquiv_single_single (p : M →* N) (hp : Function.Injective p)
    (q : N ⧸ p.range) (m : M) (r : R) :
    cosetAddEquiv p hp (Finsupp.single q (single m r)) = single (p m * q.out⁻¹) r := by
  simp [cosetAddEquiv, Finsupp.curryAddEquiv, Finsupp.curryEquiv,
    Subgroup.groupEquivQuotientProdSubgroup_symm_apply, MonoidHom.ofInjective_apply]

private theorem cosetAddEquiv_single (p : M →* N) (hp : Function.Injective p)
    (q : N ⧸ p.range) (a : R[M]) :
    cosetAddEquiv p hp (Finsupp.single q a) = mapDomain p a * single q.out⁻¹ 1 := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.single_add, ha, hb, mapDomain_add, add_mul]
  | single m r => simp [cosetAddEquiv_single_single, single_mul_single]

/-- The coset decomposition is linear for the source group-algebra action. -/
private def cosetLinearEquiv (p : M →* N) (hp : Function.Injective p) :
    letI := (mapDomainRingHom R p).toModule
    ((N ⧸ p.range) →₀ R[M]) ≃ₗ[R[M]] R[N] := by
  letI := (mapDomainRingHom R p).toModule
  refine { cosetAddEquiv p hp with map_smul' := ?_ }
  intro a x
  simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | single q b =>
    rw [Finsupp.smul_single, smul_eq_mul, cosetAddEquiv_single, cosetAddEquiv_single,
      RingHom.toModule_smul]
    simp [mapDomainRingHom_apply, mapDomain_mul, mul_assoc]

variable (R)

/-- Inverses of left-coset representatives form a basis of the target group algebra over the
source of an injective group-algebra map. These inverses represent the right cosets, as required
for the left scalar action through `mapDomainRingHom R p`. -/
def basisCosets (p : M →* N) (hp : Function.Injective p) :
    letI := (mapDomainRingHom R p).toModule
    Module.Basis (N ⧸ p.range) R[M] R[N] := by
  letI := (mapDomainRingHom R p).toModule
  exact ⟨(cosetLinearEquiv p hp).symm⟩

/-- The coset basis vector is the monomial at the inverse of the chosen representative. -/
@[simp]
theorem basisCosets_apply (p : M →* N) (hp : Function.Injective p) (q : N ⧸ p.range) :
    basisCosets R p hp q = single q.out⁻¹ (1 : R) := by
  simp [basisCosets, Module.Basis.coe_ofRepr, cosetLinearEquiv, cosetAddEquiv_single]

end TauCeti.MonoidAlgebra

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G] [Finite G]

/-- Restricting a finitely generated projective `R[G]`-module `X` of a finite group `G` to the
group algebra of a subgroup `C` gives a finitely generated projective `R[C]`-module, on which `R`
and `R[G]` act compatibly. Here `R[C]` acts on `R[G]` and on `X` through
`mapDomainRingHom R C.subtype`, as the hypotheses `hA` and `hX` state. -/
theorem restrictSubgroup_isScalarTower_finite_projective (C : Subgroup G)
    [inst : Module R[C] R[G]]
    (hA : ∀ (r : R[C]) (s : R[G]), r • s = mapDomainRingHom R C.subtype r * s)
    (X : Type*) [AddCommMonoid X] [Module R X] [Module R[G] X] [IsScalarTower R R[G] X]
    [Module.Finite R[G] X] [Module.Projective R[G] X] [Module R[C] X]
    (hX : ∀ (r : R[C]) (x : X), r • x = mapDomainRingHom R C.subtype r • x) :
    IsScalarTower R[C] R[G] R[G] ∧ IsScalarTower R[C] R[G] X ∧ IsScalarTower R R[C] X ∧
      Module.Finite R[C] X ∧ Module.Projective R[C] X := by
  let φ : R[C] →ₐ[R] R[G] := mapDomainAlgHom R R C.subtype
  obtain rfl : inst = (mapDomainRingHom R C.subtype).toModule := Module.ext' _ _ hA
  let _ : Module R[C] R[G] := (mapDomainRingHom R C.subtype).toModule
  have hAA : IsScalarTower R[C] R[G] R[G] := ⟨fun r s t ↦ mul_assoc (φ r) s t⟩
  let b := TauCeti.MonoidAlgebra.basisCosets R C.subtype C.subtype_injective
  have : Module.Free R[C] R[G] := .of_basis b
  have : Module.Finite R[C] R[G] := .of_basis b
  have hAX : IsScalarTower R[C] R[G] X := ⟨fun r s x ↦ by
    rw [hX r (s • x)]
    exact mul_smul (φ r) s x⟩
  refine ⟨hAA, hAX, ⟨fun a r x ↦ ?_⟩, .trans R[G] X, .trans R[G] X⟩
  rw [hX (a • r) x, hX r x]
  exact (congrArg (· • x) (map_smul φ a r)).trans (smul_assoc a (φ r) x)

end MonoidAlgebra
