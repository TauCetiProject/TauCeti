/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank

/-!
# The deficiency of a pro-`p` group

Let `G` be a topologically finitely generated pro-`p` group with generator rank `d(G)` and finite
relation rank `r(G) = dim_{𝔽_p} H²(G, 𝔽_p)`. Its **deficiency** is the integer
`def(G) = d(G) - r(G)`. The deficiency bounds every finite presentation of `G`: for a presentation
`G ≅ ⟨X ∣ rels⟩` of `G` by a free pro-`p` group `F` on a finite type `X` and a finite set of
relators `rels`,

```text
#X - #rels ≤ def(G)   in ℤ,
```

with equality exactly when `rels` is a minimal set of normal generators of the relation subgroup.
So the deficiency bounds `#X - #rels` over the finite presentations of `G`, and a presentation whose
relators form a minimal set of normal generators realizes the bound.

The inequality is the count `#X + r(G) = d(G) + d(R ⧸ Rᵖ[R, F])` of the five-term exact sequence of
the presentation (`TauCeti.presentedProP.card_add_finrank_cohomFp_two`), in which
`d(R ⧸ Rᵖ[R, F])`, the least number of generators of the relation subgroup `R` as a closed normal
subgroup of `F`, is at most `#rels` since the relators generate `R` normally
(`TauCeti.presentedProP.topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card`). The
relation rank of a group presented by finitely many relators is finite
(`TauCeti.presentedProP.module_finite_cohomFp_two_of_finite`), which is what makes the deficiency
of such a group defined. Every statement here is about the canonical carrier `cohomFp p G 2` of
the relation rank, so no action of `G` on `𝔽_p` appears. The definition itself needs neither the
primality of `p` nor that `G` be pro-`p`: for any natural number `p` and topological group `G` it is
the difference of `d(G)` and the `ZMod p`-rank `Module.finrank (ZMod p) (cohomFp p G 2)` of the
cohomology with trivial `ZMod p` coefficients, and the reading of that rank as the relation rank
`r(G)` is the pro-`p` case.

## Main definitions

* `TauCeti.deficiency`: the deficiency `def(G) = d(G) - finrank_{ZMod p} H²(G, ZMod p)`, in `ℤ`, of
  a topologically finitely generated topological group `G` whose cohomology `cohomFp p G 2` with
  trivial `ZMod p` coefficients is a finitely generated `ZMod p`-module, for any natural number `p`;
  for a prime `p` and a pro-`p` group `G` this is `d(G) - r(G)`. Both finiteness proofs are carried,
  as `TauCeti.topologicalGeneratorRankNat` carries its own.

## Main results

* `TauCeti.deficiency_add_finrank_cohomFp_two`: `d(G) = def(G) + finrank_{ZMod p} H²(G, ZMod p)`,
  that is `d(G) = def(G) + r(G)` for a pro-`p` group `G`.
* `TauCeti.presentedProP.card_sub_card_le_deficiency`: `#X - #rels ≤ def(G)`, and
  `TauCeti.presentedProP.card_sub_card_eq_deficiency_iff`: equality holds exactly when the
  number of relators is the least number of normal generators of the relation subgroup.
* `TauCeti.deficiency_congr`: the deficiency is an isomorphism invariant.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.4) and
  (3.9.5).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.3.
-/

public section

namespace TauCeti

open Subgroup

universe u v w

section Deficiency

-- The deficiency needs no primality of `p`, so the section precedes the `Fact p.Prime` variable.
variable (p : ℕ) (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The deficiency** `def(G) = d(G) - finrank_{ZMod p} H²(G, ZMod p)`, in `ℤ`, of a topologically
finitely generated topological group `G` whose cohomology `cohomFp p G 2` with trivial `ZMod p`
coefficients is a finitely generated `ZMod p`-module: the topological generator rank minus the
`ZMod p`-rank `Module.finrank (ZMod p) (cohomFp p G 2)`, for any natural number `p`. The
subtraction is in `ℤ`, so no natural-number truncation occurs, and both finiteness proofs are
carried, as `TauCeti.topologicalGeneratorRankNat` carries its own, so that the value is never a
truncation artefact. For a prime `p` and a pro-`p` group `G` the rank is the relation rank
`r(G) = dim_{𝔽_p} H²(G, 𝔽_p)`, so `def(G) = d(G) - r(G)`, and for a finite presentation
`⟨X ∣ rels⟩` of `G` the deficiency is an upper bound for `#X - #rels`
(`TauCeti.presentedProP.card_sub_card_le_deficiency`), attained exactly when
`#rels = d(R ⧸ Rᵖ[R, F])` (`TauCeti.presentedProP.card_sub_card_eq_deficiency_iff`). -/
noncomputable def deficiency (hfg : IsTopologicallyFinitelyGenerated G)
    (_hfin : Module.Finite (ZMod p) (cohomFp p G 2)) : ℤ :=
  (topologicalGeneratorRankNat G hfg : ℤ) - Module.finrank (ZMod p) (cohomFp p G 2)

/-- The deficiency is the generator rank minus the `ZMod p`-rank of `cohomFp p G 2`, which is the
relation rank `r(G)` for a prime `p` and a pro-`p` group `G`. -/
theorem deficiency_def (hfg : IsTopologicallyFinitelyGenerated G)
    (hfin : Module.Finite (ZMod p) (cohomFp p G 2)) :
    deficiency p G hfg hfin =
      (topologicalGeneratorRankNat G hfg : ℤ) - Module.finrank (ZMod p) (cohomFp p G 2) :=
  (rfl)

/-- **`d(G) = def(G) + finrank_{ZMod p} H²(G, ZMod p)`**: the generator rank is the deficiency plus
the `ZMod p`-rank of `cohomFp p G 2`, which is the relation rank `r(G)` for a prime `p` and a
pro-`p` group `G`. -/
@[simp]
theorem deficiency_add_finrank_cohomFp_two (hfg : IsTopologicallyFinitelyGenerated G)
    (hfin : Module.Finite (ZMod p) (cohomFp p G 2)) :
    deficiency p G hfg hfin + Module.finrank (ZMod p) (cohomFp p G 2) =
      topologicalGeneratorRankNat G hfg := by
  rw [deficiency_def, sub_add_cancel]

variable {G} in
/-- **The deficiency is an isomorphism invariant.** -/
theorem deficiency_congr [LocallyCompactSpace G] {H : Type w} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (e : G ≃ₜ* H) (hG : IsTopologicallyFinitelyGenerated G)
    (hGfin : Module.Finite (ZMod p) (cohomFp p G 2)) (hH : IsTopologicallyFinitelyGenerated H)
    (hHfin : Module.Finite (ZMod p) (cohomFp p H 2)) :
    deficiency p G hG hGfin = deficiency p H hH hHfin := by
  rw [deficiency_def, deficiency_def, topologicalGeneratorRankNat_congr e,
    finrank_cohomFp_two_congr p e]

end Deficiency

namespace presentedProP

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Finite X] {rels : Set (freeProP p X)} {G : Type v}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : presentedProP p X rels ≃ₜ* G)
include e

/-- **The deficiency inequality.** For a presentation `G ≅ ⟨X ∣ rels⟩` of a pro-`p` group on a
finite type `X` with finitely many relators, `#X - #rels ≤ def(G)` in `ℤ`: a presentation with
`#X` generators needs at least `#X - def(G)` relators. The group `G` is topologically finitely
generated as a group presented on a finite type, and its relation rank is finite as it is presented
by finitely many relators. -/
theorem card_sub_card_le_deficiency (hrels : rels.Finite) :
    (Nat.card X : ℤ) - Nat.card rels ≤
      deficiency p G
        ((isTopologicallyFinitelyGenerated_congr e).mp isTopologicallyFinitelyGenerated)
        (module_finite_cohomFp_two_of_finite e hrels) := by
  have h1 := card_add_finrank_cohomFp_two e
    (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels)
  have h2 := topologicalGeneratorRankNat_quotient_pLowerCentralStep_le_card hrels
  rw [deficiency_def]
  omega

/-- **Equality in the deficiency inequality.** For a presentation `G ≅ ⟨X ∣ rels⟩` of a pro-`p`
group on a finite type `X` with finitely many relators, `#X - #rels = def(G)` exactly when the
number of relators is the least number of generators of the relation subgroup `R` as a closed
normal subgroup, that is `d(R ⧸ Rᵖ[R, F])`. So a presentation whose relators form a minimal set of
normal generators realizes the deficiency. -/
theorem card_sub_card_eq_deficiency_iff (hrels : rels.Finite) :
    (Nat.card X : ℤ) - Nat.card rels =
        deficiency p G
          ((isTopologicallyFinitelyGenerated_congr e).mp isTopologicallyFinitelyGenerated)
          (module_finite_cohomFp_two_of_finite e hrels) ↔
      Nat.card rels = topologicalGeneratorRankNat ((normalClosure rels).topologicalClosure ⧸
        (pLowerCentralStep p (normalClosure rels).topologicalClosure).subgroupOf
          (normalClosure rels).topologicalClosure)
        (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels) := by
  have h1 := card_add_finrank_cohomFp_two e
    (isTopologicallyFinitelyGenerated_quotient_pLowerCentralStep_of_finite hrels)
  rw [deficiency_def]
  omega

end presentedProP

end TauCeti
