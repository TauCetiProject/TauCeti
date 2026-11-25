/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Henselian.Integral
import TauCeti.RingTheory.Valuation.AlgebraicExtension
import TauCeti.RingTheory.Valuation.RamificationGroup
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Unique prolongation of a henselian valuation

A henselian valuation subring `A` of `K` admits a unique prolongation to each algebraic
extension `L / K`: the unique valuation subring whose pullback to `K` is `A` is the
integral closure of `A` in `L`. Uniqueness means equality of valuation subrings, independent
of value groups or normalizations. This applies in particular to complete discrete valuation
rings. Every `K`-automorphism of `L` preserves the prolongation, so the decomposition group
for its ramification action is the full group.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, Proposition 3 (the discrete case).
* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005, §4.1.
-/

public section

namespace ValuationSubring

open IsLocalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A valuation subring dominating the local integral closure restricts to the base
valuation subring. -/
private theorem comap_eq_of_dominates_integralClosure {W : ValuationSubring L}
    {A : ValuationSubring K} (hW : (integralClosure A L).toSubring ≤ W.toSubring)
    (hlocal : IsLocalHom (Subring.inclusion hW)) : W.comap (algebraMap K L) = A := by
  let C := integralClosure A L
  have : IsLocalRing W.toSubring := inferInstanceAs (IsLocalRing W)
  have : IsLocalRing C := (Subring.inclusion hW).domain_isLocalRing
  refine comap_eq_of_map_maximalIdeal_le (algebraMap A C) (algebraMap C L)
    (map_maximalIdeal_le _) (fun c ↦ (W.mem_toSubring _).mp (hW c.property)) ?_
    (algebraMap K L) ?_
  · intro c hc
    exact coe_mem_nonunits_iff.mpr (map_nonunit (Subring.inclusion hW) c hc)
  · intro a
    -- Both scalar towers send `a` to its image in `L` under the same algebra map.
    simp only [← IsScalarTower.algebraMap_apply A C L, IsScalarTower.algebraMap_apply A K L,
      algebraMap_apply]

/-- In an algebraic extension, membership in a prolongation of a henselian valuation subring
forces integrality. -/
private theorem isIntegral_of_mem_of_comap_eq {B : ValuationSubring L} {A : ValuationSubring K}
    [HenselianRing A (maximalIdeal A)] [Algebra.IsAlgebraic K L]
    (hB : B.comap (algebraMap K L) = A) {x : L} (hx : x ∈ B) : IsIntegral A x := by
  let C := integralClosure A L
  let R : LocalSubring L :=
    { toSubring := C.toSubring, isLocalRing := TauCeti.IsIntegralClosure.isLocalRing A L C }
  by_contra hxA
  have hxC : x ∉ C.toSubring := fun h ↦
    hxA ((mem_integralClosure_iff A L).mp (Subalgebra.mem_toSubring.mp h))
  obtain ⟨W, hW, hxW⟩ := LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := R) hxC
  have hBW : B ≠ W := fun h ↦ hxW (h ▸ hx)
  have : IsLocalRing R.toSubring := R.isLocalRing
  have : IsLocalHom (Subring.inclusion hW.1) := hW.2
  have hW' : W.comap (algebraMap K L) = A := comap_eq_of_dominates_integralClosure hW.1 hW.2
  obtain ⟨u, huB, huW, hu⟩ := exists_mem_nonunits_valuation_eq_one hBW (hB.trans hW'.symm)
  -- The separating element is integral and a unit in `W`, hence a unit in `C` and in `B`.
  have huA : IsIntegral A u :=
    A.isIntegral_iff_forall_comap_le.mpr (fun V hAV ↦ hu V (hB.le.trans hAV))
  have huC : u ∈ C.toSubring := Subalgebra.mem_toSubring.mpr ((mem_integralClosure_iff A L).mpr huA)
  have hunit : IsUnit (⟨u, huC⟩ : R.toSubring) :=
    IsUnit.of_map (Subring.inclusion hW.1) _ ((W.valuation_eq_one_iff ⟨u, hW.1 huC⟩).mpr huW)
  have hCB : C.toSubring ≤ B.toSubring := B.integralClosure_toSubring_le_iff.mpr hB.ge
  have huB' : IsUnit (⟨u, hCB huC⟩ : B) := hunit.map (Subring.inclusion hCB)
  exact notMem_maximalIdeal.mpr huB' (coe_mem_nonunits_iff.mp huB)

/-- An element algebraic over `K` belongs to a prolongation `B` of a henselian valuation
subring `A` of `K` exactly when it is integral over `A`. -/
theorem mem_iff_isIntegral_of_comap_eq {B : ValuationSubring L} {A : ValuationSubring K}
    [HenselianRing A (maximalIdeal A)] (hB : B.comap (algebraMap K L) = A)
    {x : L} (hx : IsAlgebraic K x) : x ∈ B ↔ IsIntegral A x := by
  constructor
  · intro hxB
    let E := IntermediateField.adjoin K {x}
    have : Algebra.IsAlgebraic K E := IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
    have hE : (B.comap (algebraMap E L)).comap (algebraMap K E) = A := by
      rwa [comap_comap, ← IsScalarTower.algebraMap_eq]
    let y : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
    have hy : IsIntegral A y := isIntegral_of_mem_of_comap_eq hE (mem_comap.mpr hxB)
    simpa [y] using hy.map (IsScalarTower.toAlgHom A E L)
  · intro hxA
    exact (B.mem_toSubring x).mp (B.integralClosure_toSubring_le_iff.mpr hB.ge
      (Subalgebra.mem_toSubring.mpr ((mem_integralClosure_iff A L).mpr hxA)))

/-- A valuation subring prolonging a henselian valuation subring to an algebraic extension
is the integral closure of the base valuation subring. -/
theorem toSubring_eq_integralClosure_of_comap_eq {B : ValuationSubring L} {A : ValuationSubring K}
    [HenselianRing A (maximalIdeal A)] [Algebra.IsAlgebraic K L]
    (hB : B.comap (algebraMap K L) = A) : B.toSubring = (integralClosure A L).toSubring := by
  ext x
  simpa only [mem_toSubring, Subalgebra.mem_toSubring, mem_integralClosure_iff] using
    mem_iff_isIntegral_of_comap_eq hB (Algebra.IsAlgebraic.isAlgebraic x)

/-- A henselian valuation subring has a unique prolongation to every algebraic field extension.
Uniqueness is equality of valuation subrings, hence is independent of normalization. -/
theorem existsUnique_comap_eq_of_henselianRing (A : ValuationSubring K)
    [HenselianRing A (maximalIdeal A)] [Algebra.IsAlgebraic K L] :
    ∃! B : ValuationSubring L, B.comap (algebraMap K L) = A := by
  obtain ⟨B, hB⟩ := A.exists_comap_eq (algebraMap K L)
  exact ⟨B, hB, fun W hW ↦ toSubring_injective
    ((W.toSubring_eq_integralClosure_of_comap_eq hW).trans
      (B.toSubring_eq_integralClosure_of_comap_eq hB).symm)⟩

/-- Every `K`-automorphism of an algebraic extension `L / K` preserves a valuation subring `B`
that prolongs a henselian valuation subring of `K`. Thus its decomposition group is the whole
`K`-automorphism group. -/
theorem decompositionSubgroup_eq_top_of_comap_eq {B : ValuationSubring L} {A : ValuationSubring K}
    [HenselianRing A (maximalIdeal A)] [Algebra.IsAlgebraic K L]
    (hB : B.comap (algebraMap K L) = A) : B.decompositionSubgroup K = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro σ
  rw [mem_decompositionSubgroup_iff]
  intro x
  rw [mem_iff_isIntegral_of_comap_eq hB (Algebra.IsAlgebraic.isAlgebraic (σ x)),
    mem_iff_isIntegral_of_comap_eq hB (Algebra.IsAlgebraic.isAlgebraic x)]
  simpa only [AlgEquiv.restrictScalars_apply] using
    isIntegral_algEquiv (σ.restrictScalars A) (x := x)

end ValuationSubring
