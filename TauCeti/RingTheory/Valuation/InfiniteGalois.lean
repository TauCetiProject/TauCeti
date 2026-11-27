/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.RingTheory.Valuation.Center
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Invariant.Galois
import TauCeti.RingTheory.Valuation.AlgebraicExtension
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Conjugacy of the extensions of a valuation subring to an infinite Galois extension

Let `L / K` be a Galois extension, possibly infinite, and `O` a valuation subring of `K`. This
file shows that `Gal(L/K)` acts transitively on the valuation subrings of `L` lying over `O`
(`ValuationSubring.exists_algEquiv_smul_eq_of_comap_eq_of_isGalois`). The finite case, for any
finite group whose fixed field is purely inseparable over `K`, is
`ValuationSubring.exists_smul_eq_of_comap_eq`; here no finiteness is assumed, but the whole
automorphism group is needed. A countable dense subgroup `G` of `Gal(ℚ^alg/ℚ)` has fixed field `ℚ`,
but its orbits are countable, while `ℚ^alg` has uncountably many valuation subrings over each
`p`-adic valuation subring of `ℚ`. A group `G` acting on `L` and mapping onto `Gal(L/K)` is
transitive as well (`ValuationSubring.exists_smul_eq_of_comap_eq_of_surjective`).

## Method

Let `B` be the integral closure of `O` in `L`. Every valuation subring `A` of `L` over `O`
contains `B` and has a centre `P_A` on `B`, a prime lying over the maximal ideal of `O`.

* Two valuation subrings over `O` with the same centre are equal
  (`ValuationSubring.eq_of_comap_eq_of_isCenteredAt`). If `A ≠ A'`, the separation lemma
  `ValuationSubring.exists_mem_nonunits_valuation_eq_one` gives `u`, a nonunit of `A` and a unit
  of `A'`, lying in every valuation subring over `O`; so `u` is integral over `O`, lies in `B`,
  and belongs to `P_A` but not to `P_{A'}`.
* `Gal(L/K)` is profinite, acts continuously on `B` with the discrete topology (stabilizers of
  algebraic elements are open, `TauCeti.InfiniteGalois.continuousSMul_integralClosure`), and the
  invariants of `B` are `O`, since `O` is integrally closed in `K`
  (`TauCeti.InfiniteGalois.isInvariant_integralClosure`). Mathlib's
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` then moves `P_A` to `P_{A'}`, and the
  first point moves `A` to `A'`.

## Main results

* `ValuationSubring.eq_of_comap_eq_of_isCenteredAt`: the valuation subrings of an algebraic
  extension over `O` are determined by their centres on the integral closure of `O`.
* `ValuationSubring.exists_algEquiv_smul_eq_of_comap_eq_of_isGalois`: **conjugacy of the
  extensions** under `Gal(L/K)` for a Galois extension `L / K` of any degree.
* `ValuationSubring.comap_eq_comap_iff_exists_algEquiv_smul_eq`: the extensions of `O` form one
  orbit.
* `ValuationSubring.exists_smul_eq_of_comap_eq_of_surjective`: the same for a group mapping onto
  `Gal(L/K)`.

## References

* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005,
  Theorem 3.2.15, for the conjugacy of the extensions of a valuation to a normal extension.
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter I, §9, and Chapter II, §9.
-/

public section

open scoped Pointwise

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Extensions of a valuation subring are determined by their centres.** Two valuation subrings
of an algebraic extension `L / K` with the same restriction `O` to `K`, centred at the same ideal
of the integral closure of `O` in `L`, are equal. -/
theorem eq_of_comap_eq_of_isCenteredAt [Algebra.IsAlgebraic K L] {O : ValuationSubring K}
    {A A' : ValuationSubring L} (hA : A.comap (algebraMap K L) = O)
    (hA' : A'.comap (algebraMap K L) = O) {P : Ideal (integralClosure O L)}
    (hcA : A.IsCenteredAt P) (hcA' : A'.IsCenteredAt P) : A = A' := by
  by_contra hne
  obtain ⟨u, huA, huA', hu⟩ := exists_mem_nonunits_valuation_eq_one hne (hA.trans hA'.symm)
  -- `u` is integral over `O`, so it is an element `b` of the integral closure
  let b : integralClosure O L := ⟨u, (isIntegral_iff_forall_comap_le O).mpr fun W hW ↦
    hu W (hA ▸ hW)⟩
  have hb : b ∈ P := (hcA.algebraMap_mem_nonunits_iff b).mp huA
  rw [← hcA'.algebraMap_mem_nonunits_iff, mem_nonunits_iff] at hb
  exact hb.ne huA'

/-- The centre of a valuation subring `A` of `L` on the integral closure of `O = A ∩ K` lies over
the maximal ideal of `O`. -/
private theorem mem_centerIdeal_algebraMap_iff {O : ValuationSubring K} {A : ValuationSubring L}
    (hA : O = A.comap (algebraMap K L)) {P : Ideal (integralClosure O L)} (hP : A.IsCenteredAt P)
    (o : O) : algebraMap O (integralClosure O L) o ∈ P ↔ o ∈ IsLocalRing.maximalIdeal O := by
  subst hA
  rw [← hP.algebraMap_mem_nonunits_iff, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply _ K L, ← coe_mem_nonunits_iff, mem_nonunits_comap,
    ValuationSubring.algebraMap_apply]

variable [IsGalois K L]

/-- **The extensions of a valuation subring to a Galois extension are conjugate.** Let `L / K` be
a Galois extension, possibly infinite. Two valuation subrings of `L` with the same restriction to
`K` are conjugate under `Gal(L/K)`. -/
theorem exists_algEquiv_smul_eq_of_comap_eq_of_isGalois {A A' : ValuationSubring L}
    (h : A.comap (algebraMap K L) = A'.comap (algebraMap K L)) :
    ∃ σ : Gal(L/K), σ • A = A' := by
  set O := A.comap (algebraMap K L) with hO
  have hA (b : integralClosure O L) : A.valuation (algebraMap _ L b) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (algebraMap_integralClosure_mem le_rfl b)
  have hA' (b : integralClosure O L) : A'.valuation (algebraMap _ L b) ≤ 1 :=
    (A'.valuation_le_one_iff _).mpr (algebraMap_integralClosure_mem h.le b)
  have hc := A.isCenteredAt_centerIdeal hA
  have hc' := A'.isCenteredAt_centerIdeal hA'
  have := hc.isPrime
  have := hc'.isPrime
  have hunder : (A.valuation.centerIdeal _ hA).under O =
      (A'.valuation.centerIdeal _ hA').under O := by
    ext o
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.under_def, Ideal.mem_comap,
      mem_centerIdeal_algebraMap_iff hO hc, mem_centerIdeal_algebraMap_iff h hc']
  let _ : TopologicalSpace (integralClosure O L) := ⊥
  have : DiscreteTopology (integralClosure O L) := ⟨rfl⟩
  have := TauCeti.InfiniteGalois.continuousSMul_integralClosure O K L
  have := TauCeti.InfiniteGalois.isInvariant_integralClosure O K L
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (G := Gal(L/K)) _ _ hunder
  refine ⟨σ, eq_of_comap_eq_of_isCenteredAt (comap_algebraMap_pointwise_smul σ A) h.symm
    (hc.smul σ) ?_⟩
  rw [← hσ]
  exact hc'

/-- **The extensions of a valuation subring to a Galois extension form one orbit.** For a Galois
extension `L / K`, possibly infinite, two valuation subrings of `L` have the same restriction to
`K` exactly when they are conjugate under `Gal(L/K)`. -/
theorem comap_eq_comap_iff_exists_algEquiv_smul_eq {A A' : ValuationSubring L} :
    A.comap (algebraMap K L) = A'.comap (algebraMap K L) ↔ ∃ σ : Gal(L/K), σ • A = A' :=
  ⟨exists_algEquiv_smul_eq_of_comap_eq_of_isGalois,
    fun ⟨σ, hσ⟩ ↦ hσ ▸ (comap_algebraMap_pointwise_smul σ A).symm⟩

/-- **Conjugacy under a group mapping onto the Galois group.** Let `L / K` be Galois and `G` a
group acting on `L` by automorphisms fixing `K`, such that every `K`-automorphism of `L` is the
action of an element of `G`. Two valuation subrings of `L` with the same restriction to `K` are
conjugate under `G`. -/
theorem exists_smul_eq_of_comap_eq_of_surjective {G : Type*} [Group G] [MulSemiringAction G L]
    [SMulCommClass G K L] (hG : Function.Surjective (MulSemiringAction.toAlgAut G K L))
    {A A' : ValuationSubring L} (h : A.comap (algebraMap K L) = A'.comap (algebraMap K L)) :
    ∃ g : G, g • A = A' := by
  obtain ⟨σ, rfl⟩ := exists_algEquiv_smul_eq_of_comap_eq_of_isGalois h
  obtain ⟨g, rfl⟩ := hG σ
  refine ⟨g, ValuationSubring.ext _ _ fun x ↦ ?_⟩
  rw [mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    AlgEquiv.smul_def, MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]

end ValuationSubring
