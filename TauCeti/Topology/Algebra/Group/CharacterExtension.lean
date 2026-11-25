/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.Duality
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Extending characters through a finite quotient by an open subgroup

Let `G` be a commutative topological group, `H` a subgroup and `N` an open subgroup of finite
index. A character `χ : H →* Mˣ` extends to a continuous character `Ψ : G →* Mˣ` trivial on `N`
exactly when `χ` is trivial on `H ⊓ N`, provided the coefficient monoid `M` has enough roots of
unity for the exponent of `G ⧸ N`. Such an extension factors through the finite group `G ⧸ N`,
so it has finite image, of exponent dividing that of `G ⧸ N`.

The extension is built in the finite group `G ⧸ N`: the condition on `χ` says it kills the
kernel of the map `H → G ⧸ N`, so `MonoidHom.exists_comp_eq_iff_ker_le_ker` extends it along
that map to a character of `G ⧸ N`, and composing with the quotient map gives a character of `G`
which is continuous because `G ⧸ N` is discrete. Nothing about `N` beyond openness and finite
index is used; in particular `N` is supplied, not constructed. For complex coefficients the
roots-of-unity hypothesis holds by `IsSepClosed.hasEnoughRootsOfUnity`, the exponent of the
finite group `G ⧸ N` being nonzero.

This is the abstract step in the construction of idele class characters with prescribed local
components, where `G` is the idele class group and `N` the image of an open subgroup of the ideles.

## Main results

* `MonoidHom.exists_continuous_domRestrict_eq_of_subgroupOf_le_ker`: a character of `H` trivial on
  `H ⊓ N` extends to a continuous character of `G` trivial on `N`, with finite image of exponent
  dividing that of `G ⧸ N`.
* `MonoidHom.exists_continuous_domRestrict_eq_iff`: such a continuous extension trivial on `N`
  exists if and only if the character is trivial on `H ⊓ N`.

## References

* L. Clozel, M. Harris, R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l Galois
  representations*, Publ. Math. IHÉS 108 (2008), proof of Lemma 4.1.1.
-/

public section

namespace MonoidHom

variable {G M : Type*} [CommGroup G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [CommMonoid M] [TopologicalSpace M] {H N : Subgroup G}

/-- **Extension of characters through a finite quotient by an open subgroup.** Let `N` be an open
subgroup of finite index of a commutative topological group `G`, and let `M` have enough roots of
unity for the exponent of `G ⧸ N`. A character `χ` of a subgroup `H` that is trivial on `H ⊓ N`
extends to a continuous character `Ψ` of `G` that is trivial on `N`; its image is finite, of
exponent dividing that of `G ⧸ N`. -/
theorem exists_continuous_domRestrict_eq_of_subgroupOf_le_ker (hN : IsOpen (N : Set G))
    [N.FiniteIndex] [HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ N))] (χ : H →* Mˣ)
    (hχ : N.subgroupOf H ≤ χ.ker) :
    ∃ Ψ : G →* Mˣ, Continuous Ψ ∧ Ψ.domRestrict H = χ ∧ N ≤ Ψ.ker ∧ Finite Ψ.range ∧
      Monoid.exponent Ψ.range ∣ Monoid.exponent (G ⧸ N) := by
  -- Extend `χ` along the map `H → G ⧸ N`, whose kernel is `N.subgroupOf H`.
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  obtain ⟨φ, hφ⟩ := (exists_comp_eq_iff_ker_le_ker (R := M) f χ).mpr fun h hh ↦
    hχ (by simpa [f, Subgroup.mem_subgroupOf] using hh)
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have hr : (φ.comp (QuotientGroup.mk' N)).range = φ.range := by
    rw [range_comp, range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← range_eq_map]
  refine ⟨φ.comp (QuotientGroup.mk' N),
    (continuous_of_discreteTopology (f := φ)).comp QuotientGroup.continuous_mk, ?_,
    fun n hn ↦ by simp [(QuotientGroup.eq_one_iff n).mpr hn],
    hr ▸ Finite.of_surjective _ φ.rangeRestrict_surjective,
    hr ▸ MonoidHom.exponent_dvd φ.rangeRestrict_surjective⟩
  exact ext fun h ↦ by simpa [f] using congr($hφ h)

/-- **The finite-quotient extension criterion.** Let `N` be an open subgroup of finite index of a
commutative topological group `G`, and let `M` have enough roots of unity for the exponent of
`G ⧸ N`. A character `χ` of a subgroup `H` extends to a continuous character of `G` trivial on
`N` if and only if `χ` is trivial on `H ⊓ N`. -/
theorem exists_continuous_domRestrict_eq_iff (hN : IsOpen (N : Set G)) [N.FiniteIndex]
    [HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ N))] (χ : H →* Mˣ) :
    (∃ Ψ : G →* Mˣ, Continuous Ψ ∧ Ψ.domRestrict H = χ ∧ N ≤ Ψ.ker) ↔
      N.subgroupOf H ≤ χ.ker := by
  refine ⟨?_, fun hχ ↦ ?_⟩
  · rintro ⟨Ψ, -, rfl, hΨ⟩ h hh
    exact hΨ (Subgroup.mem_subgroupOf.mp hh)
  · obtain ⟨Ψ, hc, hΨ, hN', -⟩ := exists_continuous_domRestrict_eq_of_subgroupOf_le_ker hN χ hχ
    exact ⟨Ψ, hc, hΨ, hN'⟩

end MonoidHom
