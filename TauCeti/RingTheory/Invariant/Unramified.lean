/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Trivial inertia implies unramifiedness for finite invariant extensions

Let a finite group act on a commutative algebra over an infinite field. At a prime with trivial
inertia, the local ring is formally unramified over the invariant ring. Neither faithfulness nor an
assumption on the characteristic or the dimension of the algebra is needed.

The orbit polynomial supplies the relation on differentials: its derivative at an element `a`
is the product of `a - g • a` over the nonidentity elements. If none of these differences lies
in the prime, that derivative is a unit in the local ring and the differential of `a` vanishes.
Finite avoidance for linear subspaces then forces every differential to vanish. In particular,
this applies to finite linear quotients whose height-one inertia has already been computed.

## References

* [Stacks Project, Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE)
  for the orbit polynomial and invariant extensions.
* [Stacks Project, Unramified ring maps](https://stacks.math.columbia.edu/tag/00US)
  for the differential criterion for unramifiedness.

The proof uses Mathlib's `Algebra.IsInvariant.charpoly_mem_lifts` and
`Submodule.exists_forall_notMem_of_forall_ne_top`.
-/

public section

open Polynomial

namespace Ideal

variable {R A G : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Finite G] [MulSemiringAction G A] [Algebra.IsInvariant R A G]

/-- An element whose displacements by nonidentity group elements avoid a prime has zero
universal differential in the local ring over the invariant base. -/
theorem differential_eq_zero_of_forall_sub_smul_notMem (Q : Ideal A) [Q.IsPrime] {a : A}
    (ha : ∀ g : G, g ≠ 1 → a - g • a ∉ Q) :
    KaehlerDifferential.D R (Localization.AtPrime Q)
      (algebraMap A (Localization.AtPrime Q) a) = 0 := by
  classical
  let := Fintype.ofFinite G
  let S := Localization.AtPrime Q
  let D := (KaehlerDifferential.D R S).compAlgebraMap A
  -- The orbit polynomial has invariant coefficients, so it differentiates over `R`.
  obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts R A G a
  simp only [coe_mapRingHom] at hp
  have hpa : aeval a p = 0 := by
    rw [aeval_def, ← eval_map, hp, MulSemiringAction.eval_charpoly]
  have hder : aeval a p.derivative =
      ∏ g ∈ Finset.univ.erase (1 : G), (a - g • a) := by
    rw [← Polynomial.aeval_map_algebraMap A, ← derivative_map, hp,
      coe_aeval_eq_eval, TauCeti.MulSemiringAction.eval_derivative_charpoly]
  have hunit : IsUnit (algebraMap A S (aeval a p.derivative)) := by
    apply IsLocalization.map_units S
      (⟨_, ?_⟩ : Q.primeCompl)
    rw [hder]
    exact fun h ↦ by
      obtain ⟨g, hg, h⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q)).mp h
      exact ha g (Finset.mem_erase.mp hg).1 h
  have hzero := D.map_aeval p a
  rw [hpa, map_zero] at hzero
  have hDa : D a = 0 := hunit.smul_eq_zero.mp (by
    simpa only [IsScalarTower.algebraMap_smul] using hzero.symm)
  exact hDa

variable {k R A G : Type*} [Field k] [Infinite k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.IsInvariant R A G]

include k in
/-- For a finite invariant extension of algebras over an infinite field, a prime with trivial
inertia is unramified over the invariant ring. This includes positive characteristic and does
not require finite generation of the algebra or faithfulness of the group action. -/
theorem isUnramifiedAt_of_inertia_eq_bot (Q : Ideal A) [Q.IsPrime]
    (hQ : Q.inertia G = ⊥) : Algebra.IsUnramifiedAt R Q := by
  classical
  let := Fintype.ofFinite G
  let S := Localization.AtPrime Q
  let D := (KaehlerDifferential.D R S).compAlgebraMap A
  let d : A →ₗ[k] Ω[S⁄R] := D.toLinearMap.restrictScalars k
  -- If `d` were nonzero, avoid both its kernel and every displacement subspace.
  have hd : d = 0 := by
    by_contra hd
    let L (g : G) : A →ₗ[k] A :=
      ((MulSemiringAction.toAlgHom R A g).toLinearMap.restrictScalars k) - LinearMap.id
    let U : Option {g : G // g ≠ 1} → Submodule k A
      | none => LinearMap.ker d
      | some g => (Q.restrictScalars k).comap (L g)
    have mem_U (g : {g : G // g ≠ 1}) (a : A) :
        a ∈ U (some g) ↔ (g : G) • a - a ∈ Q := by
      simp [U, L, Submodule.mem_comap, MulSemiringAction.toAlgHom_apply]
    have hU : ∀ i, U i ≠ ⊤ := by
      intro i
      cases i with
      | none => exact fun h ↦ hd (LinearMap.ker_eq_top.mp h)
      | some g =>
        intro h
        have hg : (g : G) ∈ Q.inertia G := Ideal.mem_inertia.2 fun a ↦ by
          have ha : a ∈ U (some g) := h ▸ Submodule.mem_top
          exact (mem_U g a).mp ha
        exact g.2 (by simpa [hQ] using hg)
    obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top U hU
    have hdiff (g : G) (hg : g ≠ 1) : a - g • a ∉ Q := by
      intro h
      have hneg : g • a - a ∈ Q := by simpa only [neg_sub] using Q.neg_mem h
      exact ha (some ⟨g, hg⟩) ((mem_U ⟨g, hg⟩ a).mpr hneg)
    exact ha none (Q.differential_eq_zero_of_forall_sub_smul_notMem hdiff)
  have hD (a : A) : KaehlerDifferential.D R S (algebraMap A S a) = 0 :=
    LinearMap.congr_fun hd a
  have hzero : (⊤ : Submodule S Ω[S⁄R]) ≤ ⊥ := by
    rw [← KaehlerDifferential.span_range_map_derivation_of_isLocalization R A S Q.primeCompl,
      Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [Function.comp_apply, KaehlerDifferential.map_D]
    exact hD a
  exact ⟨(subsingleton_iff_forall_eq 0).mpr fun z ↦ hzero trivial⟩

end Ideal
