/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence

/-!
# Conjugation and the connecting maps of continuous cohomology

Let `0 → A → B → C → 0` be a short exact sequence of discrete `G`-modules, and let `U` and
`V = gUg⁻¹` be conjugate compact subgroups of `G`. Restricting the sequence to `U` and to `V`
gives two short exact sequences, and the conjugation maps `(g)_* : Hⁿ(U, -) ⟶ Hⁿ(V, -)`
commute with their connecting maps, in every degree:

```text
Hⁿ(U, C) ---δ---> Hⁿ⁺¹(U, A)
   |                  |
 (g)_*              (g)_*
   v                  v
Hⁿ(V, C) ---δ---> Hⁿ⁺¹(V, A)
```

This is the instance at the compatible pair `(v ↦ g⁻¹ v g, g • ·)` of the naturality of the
connecting map in compatible pairs,
`TauCeti.ContCohomology.DiscreteShortExact.delta_map`: the action of `g` is a morphism from the
restricted sequence over `U` to the one over `V`, because the maps of a short exact sequence of
`G`-modules are `G`-equivariant. For a normal subgroup, `(g)_*` is
`TauCeti.ContinuousCohomology.conjNormalMap`
(`TauCeti.ContinuousCohomology.conjMap_eq_conjNormalMap`), so the square also moves the
conjugation action on `Hⁿ(V, -)` through a connecting map, as in the passage from `H²(V, ℤ)`
to characters of `V` through the Bockstein sequence.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.delta_conjMap`: **conjugation commutes with the
  connecting map** in every degree, as morphisms of `TopModuleCat ℤ`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_conjMap_apply`: the same identity on classes,
  `(g)_* (δ x) = δ ((g)_* x)`.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_conjNormalMap`: for a normal subgroup, the
  conjugation action `conjNormalMap` on `Hⁿ(V, -)` commutes with the connecting map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §5, for the conjugation maps and their compatibility with the connecting maps.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology.DiscreteShortExact

open TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C) (U V : Subgroup G) [CompactSpace U] [CompactSpace V]

/-- **Conjugation commutes with the connecting map** in every degree: for conjugate compact
subgroups `U` and `V = gUg⁻¹` of `G` and a short exact sequence `S` of discrete `G`-modules, the
connecting map of `S` restricted to `U`, followed by conjugation `(g)_*`, is `(g)_*` followed by
the connecting map of `S` restricted to `V`:

```text
Hⁿ(U, C) ---δ---> Hⁿ⁺¹(U, A)
   |                  |
 (g)_*              (g)_*
   v                  v
Hⁿ(V, C) ---δ---> Hⁿ⁺¹(V, A)
```
-/
@[reassoc]
theorem delta_conjMap (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ) :
    (S.restrict U).delta n ≫ conjMap U V A g hVU (n + 1) =
      conjMap U V C g hVU n ≫ (S.restrict V).delta n := by
  rw [conjMap_def, conjMap_def, conjPair_def, conjPair_def]
  exact (S.restrict U).delta_map (S.restrict V) (conjHom U V g hVU)
    (DistribSMul.toAddMonoidHom A g) (DistribSMul.toAddMonoidHom B g)
    (DistribSMul.toAddMonoidHom C g) (conjHom_smul U V g hVU)
    (conjHom_smul U V g hVU) (conjHom_smul U V g hVU)
    (fun a => by simp [S.incl_equivariant]) (fun b => by simp [S.proj_equivariant]) n

/-- **`(g)_* (δ x) = δ ((g)_* x)`** for every class `x ∈ Hⁿ(U, C)`: conjugation commutes with the
connecting maps in every degree. -/
@[simp]
theorem delta_conjMap_apply (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom) (n : ℕ)
    (x : continuousCohomology n (ofDiscreteModule ℤ U C)) :
    conjMap U V A g hVU (n + 1) ((S.restrict U).delta n x) =
      (S.restrict V).delta n (conjMap U V C g hVU n x) := by
  rw [← ConcreteCategory.comp_apply, S.delta_conjMap U V g hVU n, ConcreteCategory.comp_apply]

/-- **Conjugation on a normal subgroup commutes with the connecting map**: for a compact normal
subgroup `V`, the action `conjNormalMap` of `g` on `Hⁿ(V, -)` commutes with the connecting map of
the restriction of `S` to `V`. -/
@[reassoc]
theorem delta_conjNormalMap [V.Normal] (g : G) (n : ℕ) :
    (S.restrict V).delta n ≫ conjNormalMap V A g (n + 1) =
      conjNormalMap V C g n ≫ (S.restrict V).delta n := by
  have hV : V = V.map (MulAut.conj g).toMonoidHom := (Subgroup.Normal.map_conj_eq V g).symm
  simpa only [conjMap_eq_conjNormalMap] using S.delta_conjMap V V g hV n

end TauCeti.ContCohomology.DiscreteShortExact
