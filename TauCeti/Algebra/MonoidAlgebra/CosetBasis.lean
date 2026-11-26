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

/-!
# Coset bases of group algebras

An injective group homomorphism `p : M →* N` makes `R[N]` free as a left `R[M]`-module, with
scalars acting through `mapDomainRingHom R p`. The basis consists of the inverses of chosen
left-coset representatives of `p.range`, which represent its right cosets.

## Main definitions

* `TauCeti.MonoidAlgebra.basisCosets`: the coset basis of `R[N]` over `R[M]`.

## Main results

* `TauCeti.MonoidAlgebra.bijective_mapDomain_add_mapDomain_mul_single`: when `p.range` has the
  two right cosets `p.range` and `p.range * g`, every element of `R[N]` is uniquely
  `p(a) + p(b) * g`.
* `Subgroup.restrictSubgroup_isScalarTower_finite_projective`: restricting a finitely
  generated projective `R[G]`-module to the group algebra of a finite-index subgroup keeps it
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

variable {R}

/-- **A group algebra over a subgroup with two right cosets.** Let `p : M →* N` be injective and
let `g ∉ p.range` be such that every element of `N` lies in `p.range` or in `p.range * g`, so that
these are the two right cosets of `p.range`. Then every element of `R[N]` is uniquely
`p(a) + p(b) * g` with `a, b ∈ R[M]`: as a module over `R[M]` through `mapDomain p`, `R[N]` is
free with basis `1, g`. -/
theorem bijective_mapDomain_add_mapDomain_mul_single (p : M →* N) (hp : Function.Injective p)
    {g : N} (hg : g ∉ p.range) (h : ∀ x, x ∈ p.range ∨ x * g⁻¹ ∈ p.range) :
    Function.Bijective fun ab : R[M] × R[M] ↦
      mapDomain p ab.1 + mapDomain p ab.2 * single g (1 : R) := by
  -- The coefficients at `p m` and `p m * g` read off the two components.
  have h₁ (a b : R[M]) (m : M) :
      (mapDomain p a + mapDomain p b * single g (1 : R)).coeff (p m) = a.coeff m := by
    have : p m * g⁻¹ ∉ Set.range p := by
      rintro ⟨k, hk⟩
      exact hg ⟨k⁻¹ * m, by simp [hk]⟩
    simp [coeff_mul_single_apply, Finsupp.mapDomain_apply_of_injective hp,
      Finsupp.mapDomain_of_notMem_range _ _ this]
  have h₂ (a b : R[M]) (m : M) :
      (mapDomain p a + mapDomain p b * single g (1 : R)).coeff (p m * g) = b.coeff m := by
    have : p m * g ∉ Set.range p := by
      rintro ⟨k, hk⟩
      exact hg ⟨m⁻¹ * k, by simp [hk]⟩
    simp [coeff_mul_single_apply, Finsupp.mapDomain_apply_of_injective hp,
      Finsupp.mapDomain_of_notMem_range _ _ this]
  refine ⟨fun ⟨a, b⟩ ⟨a', b'⟩ hab ↦ ?_, fun u ↦ ?_⟩
  · have hc (x : N) := congrArg (fun v : R[N] ↦ v.coeff x) hab
    refine Prod.ext (coeff_injective (Finsupp.ext fun m ↦ ?_))
      (coeff_injective (Finsupp.ext fun m ↦ ?_))
    · simpa only [h₁] using hc (p m)
    · simpa only [h₂] using hc (p m * g)
  · refine ⟨(ofCoeff (u.coeff.comapDomain p hp.injOn),
      ofCoeff (u.coeff.comapDomain (fun m ↦ p m * g) ((mul_left_injective g).comp hp).injOn)), ?_⟩
    refine coeff_injective (Finsupp.ext fun x ↦ ?_)
    rcases h x with ⟨m, rfl⟩ | ⟨m, hm⟩
    · rw [h₁]
      simp
    · obtain rfl : x = p m * g := by rw [hm, inv_mul_cancel_right]
      rw [h₂]
      simp

end TauCeti.MonoidAlgebra

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G]

/-- Restricting a finitely generated projective `R[G]`-module `X` of a group `G` to the
group algebra of a finite-index subgroup `C` gives a finitely generated projective `R[C]`-module,
on which `R` and `R[G]` act compatibly. Here `R[C]` acts on `R[G]` and on `X` through
`mapDomainRingHom R C.subtype`, as the hypotheses `hA` and `hX` state. -/
theorem _root_.Subgroup.restrictSubgroup_isScalarTower_finite_projective (C : Subgroup G)
    [C.FiniteIndex] [inst : Module R[C] R[G]]
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
  have : Finite (G ⧸ C.subtype.range) := by
    rw [Subgroup.range_subtype]
    infer_instance
  have : Module.Free R[C] R[G] := .of_basis b
  have : Module.Finite R[C] R[G] := .of_basis b
  have hAX : IsScalarTower R[C] R[G] X := ⟨fun r s x ↦ by
    rw [hX r (s • x)]
    exact mul_smul (φ r) s x⟩
  refine ⟨hAA, hAX, ⟨fun a r x ↦ ?_⟩, .trans R[G] X, .trans R[C] R[G] X⟩
  rw [hX (a • r) x, hX r x]
  exact (congrArg (· • x) (map_smul φ a r)).trans (smul_assoc a (φ r) x)

end MonoidAlgebra
