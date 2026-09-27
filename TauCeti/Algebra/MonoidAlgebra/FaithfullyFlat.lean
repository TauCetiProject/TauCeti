/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.GroupTheory.Coset.Basic

/-!
# Faithful flatness of maps of group algebras

An injective group homomorphism `p : M →* N` makes `R[N]` free as a left `R[M]`-module.
The basis consists of the inverses of chosen left-coset representatives of `p.range`, which
represent its right cosets. For commutative groups and a nonzero commutative base ring, the
induced ring map is faithfully flat exactly when `p` is injective.
This is the coordinate-algebra criterion for faithful flatness of morphisms of diagonalizable
groups.
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

section CommRing

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- An injective homomorphism of commutative groups induces a faithfully flat group-algebra
map, including over the zero ring. -/
theorem faithfullyFlat_mapDomainRingHom_of_injective (k : Type*) [CommRing k]
    (p : G →* H) (hp : Function.Injective p) :
    (mapDomainRingHom k p).FaithfullyFlat := by
  let := (mapDomainRingHom k p).toAlgebra
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (basisCosets k p hp).repr

/-- Over a nonzero commutative ring, the group-algebra map is faithfully flat exactly when
the homomorphism of character groups is injective. -/
@[simp]
theorem faithfullyFlat_mapDomainRingHom_iff (k : Type*) [CommRing k] [Nontrivial k]
    (p : G →* H) : (mapDomainRingHom k p).FaithfullyFlat ↔ Function.Injective p := by
  refine ⟨fun h x y hxy => ?_, faithfullyFlat_mapDomainRingHom_of_injective k p⟩
  apply single_left_injective (R := k) one_ne_zero
  apply h.injective
  simpa using congrArg (fun z => single z (1 : k)) hxy

end CommRing

end TauCeti.MonoidAlgebra
