/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# Normalizer orbits and conjugacy classes

The normalizer `N(H)` of a subgroup `H` of a group `G` acts on `H` by conjugation, so elements of
`H` in one `N(H)`-orbit are conjugate in `G`. This gives a map from the `N(H)`-orbits on `H` to the
orbits of `G` on itself under conjugation. The map is injective exactly when elements of `H`
conjugate in `G` are already conjugate in `N(H)`, and surjective exactly when the conjugates of `H`
cover `G`. For a maximal torus of a compact connected Lie group both conditions hold.

## Main declarations

* `Subgroup.normalizerOrbitMap`: the map from `N(H)`-orbits on `H` to conjugation orbits on `G`.
* `Subgroup.normalizerOrbitMap_injective_iff`, `Subgroup.normalizerOrbitMap_surjective_iff`: the
  group-theoretic meaning of injectivity and surjectivity.
-/

public section

open MulAction

namespace Subgroup

variable {G : Type*} [Group G]

/-- The map sending the `N(H)`-orbit of an element of `H` to its conjugation orbit in `G`. -/
def normalizerOrbitMap (H : Subgroup G) :
    orbitRel.Quotient (normalizer (H : Set G)) H → orbitRel.Quotient (ConjAct G) G :=
  MulActionHom.orbitRelQuotientMap (σ := fun n ↦ ConjAct.toConjAct (n : G))
    ⟨Subtype.val, fun _ _ ↦ rfl⟩

@[simp]
theorem normalizerOrbitMap_mk (H : Subgroup G) (h : H) :
    H.normalizerOrbitMap (Quotient.mk'' h) = Quotient.mk'' (h : G) :=
  MulActionHom.orbitRelQuotientMap_mk _ h

/-- The map from `N(H)`-orbits to conjugation orbits is injective exactly when elements of `H`
that are conjugate in `G` are conjugate by an element of `N(H)`. -/
theorem normalizerOrbitMap_injective_iff (H : Subgroup G) :
    Function.Injective H.normalizerOrbitMap ↔
      ∀ t ∈ H, ∀ u ∈ H, IsConj t u → ∃ n ∈ normalizer (H : Set G), n * t * n⁻¹ = u := by
  constructor
  · intro h t ht u hu hc
    have heq : H.normalizerOrbitMap (Quotient.mk'' ⟨u, hu⟩) =
        H.normalizerOrbitMap (Quotient.mk'' ⟨t, ht⟩) := by
      simpa only [normalizerOrbitMap_mk] using ConjAct.mk_eq_mk_iff_isConj.mpr hc.symm
    obtain ⟨n, hn⟩ := Quotient.eq''.mp (h heq)
    exact ⟨n, n.2, congrArg Subtype.val hn⟩
  · intro h a b
    refine Quotient.inductionOn₂' a b fun a b hab ↦ ?_
    simp only [normalizerOrbitMap_mk, ConjAct.mk_eq_mk_iff_isConj] at hab
    obtain ⟨n, hn, e⟩ := h a a.2 b b.2 hab
    exact (Quotient.eq''.mpr (orbitRel_apply.mpr ⟨⟨n, hn⟩, Subtype.ext e⟩)).symm

/-- The map from `N(H)`-orbits to conjugation orbits is surjective exactly when the conjugates of
`H` cover `G`. -/
theorem normalizerOrbitMap_surjective_iff (H : Subgroup G) :
    Function.Surjective H.normalizerOrbitMap ↔
      ⋃ a : G, (H.map (MulAut.conj a).toMonoidHom : Set G) = Set.univ := by
  constructor
  · intro h
    refine Set.eq_univ_of_forall fun g ↦ ?_
    obtain ⟨q, hq⟩ := h (Quotient.mk'' g)
    induction q using Quotient.inductionOn' with
    | h t =>
      rw [normalizerOrbitMap_mk] at hq
      obtain ⟨c, rfl⟩ := isConj_iff.mp (ConjAct.mk_eq_mk_iff_isConj.mp hq)
      exact Set.mem_iUnion.mpr ⟨c, t, t.2, rfl⟩
  · intro h q
    induction q using Quotient.inductionOn' with
    | h g =>
      obtain ⟨a, t, ht, rfl⟩ := Set.mem_iUnion.mp (h ▸ Set.mem_univ g)
      exact ⟨Quotient.mk'' ⟨t, ht⟩, (H.normalizerOrbitMap_mk _).trans
        (ConjAct.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨a, rfl⟩))⟩

end Subgroup
