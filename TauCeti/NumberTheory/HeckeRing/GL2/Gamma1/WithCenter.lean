/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic

/-!
# The Hecke triple of `Γ₁(N)·{±I}`

`Gamma1/Basic.lean` puts `Γ₁(N)` into a Hecke triple `Γ₁(N) ≤ Δ₀(N) ≤ commensurator(Γ₁(N))`.
This file does the same for `Γ₁(N)·{±I}`, the subgroup `(Gamma1 N).withCenter` obtained by
adjoining the centre of `SL₂(ℤ)`.

## Why the enlarged group is the one some statements need

`Γ₁(N)` does **not** contain `-I` once `N ≥ 3` — `-I` has diagonal `(-1, -1)` while `Γ₁(N)` asks
for `≡ (1, 1)`, so `CongruenceSubgroup.neg_one_mem_Gamma1_iff` holds exactly when `N ∣ 2`. Any
statement whose hypothesis is "this subgroup contains `-I`" is therefore simply false at `Γ₁(N)`
for almost every level, and a fundamental-domain or Petersson argument that needs it has to run
over a group that does contain it.

`Γ.withCenter = Γ ⊔ Z(G)` contains `-I` for **every** `Γ`, and it is the group TauCeti's Petersson
layer already works with: `CuspForm.peterssonInnerCosets` sums over `SL(2, ℤ) ⧸ Γ.withCenter`.
That this enlarged group is itself a Hecke triple with the same `Δ₀(N)` is what lets a Hecke
coset be formed over it at all.

Nothing here is deep — the point is that the passage from `Γ₁(N)` to `Γ₁(N)·{±I}` costs nothing
on either side of the triple. Containment in `Δ₀(N)` survives because `Γ₀(N)` already contains
`-I`, so it absorbs the central factor and `Γ₁(N)·{±I} ≤ Γ₀(N)` still holds; commensurability
survives because the enlarged group still has finite index in `SL₂(ℤ)`, containing `Γ₁(N)`.

**This file declares only the instance.** Neither half of the triple mentions `Γ₁(N)`: the
`Δ₀(N)` containment needs only `H ≤ Γ₀(N)` and is `map_withCenter_le_Delta0` in
`Gamma0/Basic.lean`, while the commensurator half needs only finite index — nothing about
`withCenter` at all — and is `Delta0_le_commensurator_map` in `Delta0.lean`.

## Main results

* the `IsHeckeTriple (Delta0 N) H H` instance for `H := (Gamma1 N).withCenter.map (mapGL ℚ)`,
  which is `map_withCenter_le_Delta0` applied at `Γ₁(N)`. The `FiniteIndex` instance it needs is
  supplied generically by `Subgroup.instFiniteIndexWithCenter`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1–3.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn Subgroup

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable (N : ℕ)

variable [NeZero N]

/-- **The Hecke triple of `Γ₁(N)·{±I}`**: `Γ₁(N)·{±I} ≤ Δ₀(N) ≤ commensurator(Γ₁(N)·{±I})` inside
`GL₂(ℚ)`, with the same monoid `Δ₀(N)` as the triple of `Γ₁(N)` itself. -/
instance : IsHeckeTriple (Delta0 N) (((Gamma1 N).withCenter).map (mapGL ℚ))
    (((Gamma1 N).withCenter).map (mapGL ℚ)) :=
  IsHeckeTriple.of_diagonal (map_withCenter_le_Delta0 N (Gamma1_in_Gamma0 N))
    (Delta0_le_commensurator_map N ((Gamma1 N).withCenter))

end HeckeRing.GL2
