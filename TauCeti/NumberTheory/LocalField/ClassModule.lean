/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.Strict
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Sylow

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

## Main results

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

end TauCeti
