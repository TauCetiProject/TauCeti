/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Selmer structures and their Selmer groups

Let `M` be a `G`-module. A **Selmer structure** on `M`, relative to a family `(H i, N i)` of
"local" groups and modules, consists of a localisation map `H¹(G, M) → H¹(H i, N i)` for each
index `i`, given as the pullback along a compatible pair `(H i → G, M → N i)`, together with a
**local condition**: a subgroup of each `H¹(H i, N i)`. Its **Selmer group** is the subgroup of
`H¹(G, M)` of classes whose every localisation satisfies the local condition,

```text
Sel_𝓕(M) = {c ∈ H¹(G, M) | ∀ i, loc_i c ∈ 𝓕_i}.
```

In the arithmetic application `G` is the absolute Galois group of a global field `K`, `M` is a
discrete `G_K`-module, the index runs over the places `v` of `K`, `H v = G_{K_v}` maps to `G_K`
through a choice of embedding of separable closures, and `N v` is the corresponding module over
`K_v`. The `m`-Selmer group and the Shafarevich–Tate group of an elliptic curve
(`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer.lean`) are the Selmer groups of
two Selmer structures of this kind. Allowing a coefficient map `M → N i`, rather than restricting
the action on `M` itself, is what lets the local module be formed over a separable closure of the
local field. Rubin also requires the local conditions at almost all places to be the unramified
classes; that is a property of a Selmer structure over a global field, not part of the data here,
and none of the statements below use it.

## Main definitions

* `TauCeti.ContCohomology.SelmerStructure`: localisation data and local conditions.
* `TauCeti.ContCohomology.SelmerStructure.localization`: the localisation map
  `H¹(G, M) → H¹(H i, N i)`.
* `TauCeti.ContCohomology.SelmerStructure.selmerGroup`: the Selmer group.

## Main results

* `TauCeti.ContCohomology.SelmerStructure.mem_selmerGroup_iff`: a class is Selmer exactly when
  every localisation satisfies the local condition.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.1.
-/

public section

noncomputable section

namespace TauCeti.ContCohomology

variable (G : Type*) [Monoid G] [TopologicalSpace G]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {ι : Type*} (H : ι → Type*) [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]
  (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, IsTopologicalAddGroup (N i)] [∀ i, DistribMulAction (H i) (N i)]
  [∀ i, ContinuousSMul (H i) (N i)]

/-- **A Selmer structure** on the `G`-module `M`, relative to the local groups `H i` and local
modules `N i`: for each index `i`, a compatible pair `(groupHom i, coeffHom i)` along which
`H¹(G, M)` is localised to `H¹(H i, N i)`, and a local condition subgroup of `H¹(H i, N i)`. -/
structure SelmerStructure where
  /-- The map from the `i`th local group to `G`, such as the inclusion of a decomposition
  group. -/
  groupHom : ∀ i, H i →ₜ* G
  /-- The map from `M` to the `i`th local module. -/
  coeffHom : ∀ i, M →+ N i
  continuous_coeffHom : ∀ i, Continuous (coeffHom i)
  coeffHom_smul : ∀ i (h : H i) (x : M), coeffHom i (groupHom i h • x) = h • coeffHom i x
  /-- The local condition at `i`, a subgroup of `H¹(H i, N i)`. -/
  localCondition : ∀ i, AddSubgroup (H1 (H i) (N i))

namespace SelmerStructure

variable {G M H N} (𝓕 : SelmerStructure G M H N)

/-- **The localisation map** `H¹(G, M) → H¹(H i, N i)` of a Selmer structure: pullback along the
compatible pair `(groupHom i, coeffHom i)`. -/
def localization (i : ι) : H1 G M →+ H1 (H i) (N i) :=
  explicitMap1 _ _ _ _ (𝓕.groupHom i) (𝓕.coeffHom i) (𝓕.continuous_coeffHom i) (𝓕.coeffHom_smul i)

/-- `𝓕.localization i` is the pullback along `(𝓕.groupHom i, 𝓕.coeffHom i)`. -/
theorem localization_eq_explicitMap1 (i : ι) :
    𝓕.localization i = explicitMap1 _ _ _ _ (𝓕.groupHom i) (𝓕.coeffHom i)
      (𝓕.continuous_coeffHom i) (𝓕.coeffHom_smul i) :=
  (rfl)

/-- **The Selmer group** of a Selmer structure: the classes in `H¹(G, M)` whose localisation at
every index lies in the local condition. -/
def selmerGroup : AddSubgroup (H1 G M) :=
  ⨅ i, (𝓕.localCondition i).comap (𝓕.localization i)

/-- A class is Selmer exactly when its localisation at every index satisfies the local
condition. -/
@[simp]
theorem mem_selmerGroup_iff {c : H1 G M} :
    c ∈ 𝓕.selmerGroup ↔ ∀ i, 𝓕.localization i c ∈ 𝓕.localCondition i := by
  simp only [selmerGroup, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]

end SelmerStructure

end TauCeti.ContCohomology
