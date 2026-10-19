/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ClassModule
public import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.Strict
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Sylow
public import TauCeti.Topology.Algebra.GroupExtension.RelabelQuotient
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.ClassIdentification

/-!
# The pro-`p` class module of a local absolute Galois group

Let `K` be a nonarchimedean local field, `p` a prime invertible in `K` (for instance the residue
characteristic when `K` has characteristic zero), and `V` an open normal subgroup of `G_K`. This
file proves that the class `u_{G_K/V}(p)` of the extension

```text
1 → V^ab(p) → G_K ⧸ ⁅V, V⁆V(p) → G_K ⧸ V → 1
```

generates `H²(G_K ⧸ V, V^ab(p))`, and that this cyclic group has order the `p`-part of
`#(G_K ⧸ V)`. When `V = G_L` for a finite Galois extension `L / K`, local reciprocity identifies
`V^ab(p)` with the `p`-adic completion of `Lˣ`, so this is the statement that the class of the
arithmetic extension generates `H²(Gal(L/K), A(L))`. It is the input from strict cohomological
dimension to the computation of the generator rank of `G_K`.

The result is the general class-module theorem `TauCeti.abelianizationProPClass_generates` at
`G_K`, whose strict `p`-cohomological dimension is two
(`TauCeti.ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit`).
The finite-layer form transports this class to the actual extension over `Gal(L/K)`
along the quotient identification, retaining both generation and the exact order.

## Main results

* `TauCeti.galoisClassModuleExtension_contCohomologyClass_generates`: the class of the
  actual arithmetic extension over `Gal(L/K)` generates, with the same exact order.
* `TauCeti.contCohomologyClass_absoluteGaloisGroup_generates`: `u_{G_K/V}(p)` generates
  `H²(G_K ⧸ V, V^ab(p))`, of order the `p`-part of `#(G_K ⧸ V)`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.6.4)(iii),
  (7.2.5) and the proof of (7.4.1).
-/

public section

namespace TauCeti

open ContCohomology

/-- **The class of the arithmetic extension generates.** For a nonarchimedean local field `K`, a
prime `p` invertible in `K`, and an open normal subgroup `V` of `G_K`, the class of the extension
`1 → V^ab(p) → G_K ⧸ ⁅V, V⁆V(p) → G_K ⧸ V → 1` generates `H²(G_K ⧸ V, V^ab(p))`, a cyclic group
whose order is the `p`-part of `#(G_K ⧸ V)`. -/
theorem contCohomologyClass_absoluteGaloisGroup_generates {p : ℕ} [Fact p.Prime] {K : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (hp : IsUnit (p : K)) {V : Subgroup (Field.absoluteGaloisGroup K)} [V.Normal]
    (hV : IsOpen (V : Set (Field.absoluteGaloisGroup K))) :
    AddSubgroup.zmultiples
        (abelianizationProPClass p (Field.absoluteGaloisGroup K) V hV) = ⊤ ∧
      Nat.card (H2 (Field.absoluteGaloisGroup K ⧸ V)
          (Additive (abelianizationProP p (Field.absoluteGaloisGroup K) V))) =
        p ^ padicValNat p (Nat.card (Field.absoluteGaloisGroup K ⧸ V)) :=
  abelianizationProPClass_generates Fact.out
    (ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit hp).le hV

/-- The class of the arithmetic pro-`p` extension over `Gal(L/K)` generates its second
cohomology, a cyclic group of order the `p`-part of the extension degree. The coefficients
are the pro-`p` abelianization of the subgroup fixing the embedded finite layer. -/
theorem galoisClassModuleExtension_contCohomologyClass_generates {p : ℕ} [Fact p.Prime]
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Normal K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (hp : IsUnit (p : K)) (j : L →ₐ[K] SeparableClosure K) :
    let := galoisClassModuleAction p K L j
    let := continuousSMul_galoisClassModuleAction p K L j
    AddSubgroup.zmultiples (galoisClassModuleExtension p K L j).contCohomologyClass = ⊤ ∧
      Nat.card (H2 (L ≃ₐ[K] L)
        (Additive (abelianizationProP p (AbsoluteGaloisGroup K)
          (galoisSubgroup K L j).toSubgroup))) =
        p ^ padicValNat p (Nat.card (L ≃ₐ[K] L)) := by
  let V := (galoisSubgroup K L j).toSubgroup
  let : IsClosed (V : Set (AbsoluteGaloisGroup K)) := (galoisSubgroup K L j).isClosed
  let := galoisClassModuleAction p K L j
  let := continuousSMul_galoisClassModuleAction p K L j
  let X := abelianizationProPProfiniteExtension p (AbsoluteGaloisGroup K) V
  let e := quotientGaloisSubgroupEquiv K L j
  have hsmul (q : AbsoluteGaloisGroup K ⧸ V)
      (x : abelianizationProP p (AbsoluteGaloisGroup K) V) : e q • x = q • x := by
    rw [galoisClassModuleAction_smul, ContinuousMulEquiv.symm_apply_apply]
  have hscd : strictCohomologicalDimensionAt.{0} p (AbsoluteGaloisGroup K) ≤ 2 := by
    rw [← strictCohomologicalDimensionAt_congr (absoluteGaloisGroupRestrictEquiv K)]
    exact (ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit
      hp).le
  obtain ⟨hgen, hcard⟩ := abelianizationProPClass_generates Fact.out hscd
    (galoisSubgroup K L j).isOpen
  refine ⟨?_, ?_⟩
  · apply (X.zmultiples_contCohomologyClass_relabelQuotient_eq_top_iff e hsmul).mpr
    simpa only [X, abelianizationProPProfiniteExtension_contCohomologyClass p _ V
      (galoisSubgroup K L j).isOpen] using hgen
  · let c := explicitMap2Equiv (AbsoluteGaloisGroup K ⧸ V)
      (Additive (abelianizationProP p (AbsoluteGaloisGroup K) V)) (L ≃ₐ[K] L)
      (Additive (abelianizationProP p (AbsoluteGaloisGroup K) V)) e.symm
      (AddEquiv.refl _) continuous_id continuous_id
      (fun h m ↦ by
        simpa using congrArg (@Additive.ofMul (abelianizationProP p (AbsoluteGaloisGroup K) V))
          (hsmul (e.symm h) m.toMul).symm)
    rw [← Nat.card_congr c.toEquiv, hcard, Nat.card_congr e.toEquiv]

end TauCeti
