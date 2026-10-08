/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow

/-!
# Prime-to-`p` restriction for the pro-`p` class module

Let `V` be an open normal subgroup of a compact group `G`. The class module `V^ab(p)` is a pro-`p`
group, so for `m` prime to `p` its `m`-th power map is a homeomorphism
(`TauCeti.IsProP.powHomeomorph`). Hence multiplication by `m` is bijective on
`Hⁱ(G ⧸ V, V^ab(p))` for `i = 1, 2`. For a subgroup `S` of `G ⧸ V` of index prime to `p`,
`cor ∘ res` is multiplication by `[G ⧸ V : S]`, so restriction to `S` is injective in degrees one
and two (`TauCeti.ContCohomology.explicitRes1_injective_of_nsmul_homeomorph` and its degree-two
analogue).

This is the step of NSW (3.6.3) and (3.6.4), (i) ⇒ (iii), that reduces the class module of a
finite quotient to that of a Sylow `p`-subgroup.

The definitions and injectivity results in this file are adapted from the Tau Ceti lookahead branch
`lookahead/ProfiniteCohomology/abelianization-pro-p-class-generates`.

## Main definitions

* `TauCeti.abelianizationProPRes1`, `TauCeti.abelianizationProPRes2`: restriction of
  `Hⁱ(G ⧸ V, V^ab(p))` to a subgroup `S` of `G ⧸ V`, for `i = 1, 2`.

## Main results

* `TauCeti.abelianizationProPRes1_injective`: restriction of `H¹(G ⧸ V, V^ab(p))` to a subgroup
  of index prime to `p` is injective.
* `TauCeti.abelianizationProPRes2_injective`: the same in degree two.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.6.3) and (3.6.4).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- For `m` prime to `p`, multiplication by `m` on the additive class module `V^ab(p)` of an open
subgroup `V` is a homeomorphism: it is the `m`-th power map of the pro-`p` group `V^ab(p)`. -/
private noncomputable def abelianizationProPNsmulHomeomorph (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) {m : ℕ} (hm : p.Coprime m) :
    Additive (abelianizationProP p G V) ≃ₜ Additive (abelianizationProP p G V) :=
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  let e := (isProP_maximalProPQuotient (p := p) (G := TopologicalAbelianization V)).powHomeomorph hm
  { toFun a := Additive.ofMul (e a.toMul)
    invFun a := Additive.ofMul (e.symm a.toMul)
    left_inv a := by simp
    right_inv a := by simp
    continuous_toFun := continuous_ofMul.comp (e.continuous.comp continuous_toMul)
    continuous_invFun := continuous_ofMul.comp (e.symm.continuous.comp continuous_toMul) }

private theorem abelianizationProPNsmulHomeomorph_apply (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) {m : ℕ} (hm : p.Coprime m)
    (a : Additive (abelianizationProP p G V)) :
    abelianizationProPNsmulHomeomorph hp V hV hm a = m • a := by
  simp [abelianizationProPNsmulHomeomorph]

/-- Restriction `H¹(G ⧸ V, V^ab(p)) → H¹(S, V^ab(p))` of the first cohomology of the class module
to a subgroup `S` of `G ⧸ V`. -/
noncomputable abbrev abelianizationProPRes1 (p : ℕ) (V : Subgroup G) [V.Normal]
    (S : Subgroup (G ⧸ V)) :
    H1 (G ⧸ V) (Additive (abelianizationProP p G V)) →+
      H1 S (Additive (abelianizationProP p G V)) :=
  explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V)) S

/-- Restriction `H²(G ⧸ V, V^ab(p)) → H²(S, V^ab(p))` of the second cohomology of the class module
to a subgroup `S` of `G ⧸ V`. -/
noncomputable abbrev abelianizationProPRes2 (p : ℕ) (V : Subgroup G) [V.Normal]
    (S : Subgroup (G ⧸ V)) :
    H2 (G ⧸ V) (Additive (abelianizationProP p G V)) →+
      H2 S (Additive (abelianizationProP p G V)) :=
  explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V)) S

/-- **Restriction to a subgroup of index prime to `p` is injective on `H¹(G ⧸ V, V^ab(p))`**, for
an open normal subgroup `V` of a compact group `G`. -/
theorem abelianizationProPRes1_injective (hp : p.Prime) (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) (S : Subgroup (G ⧸ V)) (hS : ¬p ∣ S.index) :
    Function.Injective (abelianizationProPRes1 p V S) := by
  let _ : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  let _ : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  let _ : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hm : p.Coprime S.index := hp.coprime_iff_not_dvd.mpr hS
  exact explicitRes1_injective_of_nsmul_homeomorph _ _ S (isOpen_discrete (S : Set (G ⧸ V)))
    (abelianizationProPNsmulHomeomorph hp V hV hm)
    (abelianizationProPNsmulHomeomorph_apply hp V hV hm)

/-- **Restriction to a subgroup of index prime to `p` is injective on `H²(G ⧸ V, V^ab(p))`**, for
an open normal subgroup `V` of a compact group `G`. -/
theorem abelianizationProPRes2_injective (hp : p.Prime) (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) (S : Subgroup (G ⧸ V)) (hS : ¬p ∣ S.index) :
    Function.Injective (abelianizationProPRes2 p V S) := by
  let _ : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  let _ : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  let _ : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hm : p.Coprime S.index := hp.coprime_iff_not_dvd.mpr hS
  exact explicitRes2_injective_of_nsmul_homeomorph _ _ S (isOpen_discrete (S : Set (G ⧸ V)))
    (abelianizationProPNsmulHomeomorph hp V hV hm)
    (abelianizationProPNsmulHomeomorph_apply hp V hV hm)

end TauCeti
