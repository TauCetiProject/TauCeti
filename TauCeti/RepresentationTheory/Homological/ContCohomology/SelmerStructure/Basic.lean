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
(`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/Selmer/Basic.lean`) are the Selmer
groups of two Selmer structures of this kind. Allowing a coefficient map `M → N i`, rather than
restricting the action on `M` itself, is what lets the local module be formed over a separable
closure of the local field. Rubin also requires the local conditions at almost all places to be
the unramified classes; that is a property of a Selmer structure over a global field, not part of
the data here, and none of the statements below use it.

## Main definitions

* `TauCeti.ContCohomology.SelmerStructure`: localisation data and local conditions.
* `TauCeti.ContCohomology.SelmerStructure.localization`: the localisation map
  `H¹(G, M) → H¹(H i, N i)`.
* `TauCeti.ContCohomology.SelmerStructure.selmerGroup`: the Selmer group.
* `TauCeti.ContCohomology.SelmerStructure.withLocalConditions`: replace the local conditions
  without changing the localisation data.
* `TauCeti.ContCohomology.SelmerStructure.relax`: the `S`-relaxed Selmer structure replacing the
  local conditions on `S` by `⊤` while keeping `𝓕.localCondition` outside `S`.

## Main results

* `TauCeti.ContCohomology.SelmerStructure.mem_selmerGroup_iff`: a class is Selmer exactly when
  every localisation satisfies the local condition.
* `TauCeti.ContCohomology.SelmerStructure.mem_selmerGroup_relax_iff`: a class is `S`-relaxed
  Selmer exactly when every localisation outside `S` satisfies the local condition.
* `TauCeti.ContCohomology.SelmerStructure.selmerGroup_le_relax` and
  `TauCeti.ContCohomology.SelmerStructure.selmerGroup_relax_mono`: inclusion and monotonicity of
  relaxed Selmer groups.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.5.
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

/-- Every localisation of a Selmer class satisfies the corresponding local condition. -/
theorem localization_mem (c : 𝓕.selmerGroup) (i : ι) :
    𝓕.localization i c ∈ 𝓕.localCondition i :=
  (mem_selmerGroup_iff 𝓕).mp c.property i

section LocalConditions

variable (A B : ∀ i, AddSubgroup (H1 (H i) (N i)))

/-- Replace only the local conditions of a Selmer structure. -/
def withLocalConditions : SelmerStructure G M H N :=
  { 𝓕 with localCondition := A }

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Updating local conditions leaves the group homomorphisms unchanged. -/
@[simp]
theorem withLocalConditions_groupHom :
    (𝓕.withLocalConditions A).groupHom = 𝓕.groupHom :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Updating local conditions leaves the coefficient homomorphisms unchanged. -/
@[simp]
theorem withLocalConditions_coeffHom :
    (𝓕.withLocalConditions A).coeffHom = 𝓕.coeffHom :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- The updated structure has the prescribed local conditions. -/
@[simp]
theorem withLocalConditions_localCondition :
    (𝓕.withLocalConditions A).localCondition = A :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Replacing the local conditions twice retains only the last system. -/
@[simp]
theorem withLocalConditions_withLocalConditions :
    (𝓕.withLocalConditions A).withLocalConditions B = 𝓕.withLocalConditions B :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Replacing the local conditions by the original ones changes nothing. -/
@[simp]
theorem withLocalConditions_self : 𝓕.withLocalConditions 𝓕.localCondition = 𝓕 :=
  (rfl)

/-- Updating local conditions leaves the localisation maps unchanged. -/
@[simp]
theorem withLocalConditions_localization :
    (𝓕.withLocalConditions A).localization = 𝓕.localization := by
  funext i
  rw [localization_eq_explicitMap1, localization_eq_explicitMap1]
  rfl

/-! ### Relaxed Selmer structures -/

variable (S : Set ι)

/-- **The `S`-relaxed Selmer structure** `𝓕.relax S` (Rubin I.5.2): replaces the local condition
at indices in `S` with the full group `⊤` and keeps `𝓕.localCondition i` outside `S`. -/
def relax : SelmerStructure G M H N :=
  𝓕.withLocalConditions fun i ↦ ⨅ (_ : i ∉ S), 𝓕.localCondition i

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- The defining formula for `SelmerStructure.relax`. -/
theorem relax_def :
    𝓕.relax S = 𝓕.withLocalConditions fun i ↦ ⨅ (_ : i ∉ S), 𝓕.localCondition i :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Relaxing local conditions leaves the group homomorphisms unchanged. -/
@[simp]
theorem relax_groupHom : (𝓕.relax S).groupHom = 𝓕.groupHom :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Relaxing local conditions leaves the coefficient homomorphisms unchanged. -/
@[simp]
theorem relax_coeffHom : (𝓕.relax S).coeffHom = 𝓕.coeffHom :=
  (rfl)

/-- Relaxing local conditions leaves the localisation maps unchanged. -/
@[simp]
theorem relax_localization : (𝓕.relax S).localization = 𝓕.localization :=
  𝓕.withLocalConditions_localization _

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- At an index in `S`, the relaxed local condition is `⊤`. -/
@[simp]
theorem relax_localCondition_of_mem {i : ι} (hi : i ∈ S) :
    (𝓕.relax S).localCondition i = ⊤ := by
  rw [relax_def, withLocalConditions_localCondition]
  exact iInf_neg (not_not.mpr hi)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Outside `S`, the relaxed local condition agrees with the original one. -/
@[simp]
theorem relax_localCondition_of_notMem {i : ι} (hi : i ∉ S) :
    (𝓕.relax S).localCondition i = 𝓕.localCondition i := by
  rw [relax_def, withLocalConditions_localCondition]
  exact iInf_pos hi

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Every original local condition is contained in the relaxed one. -/
theorem localCondition_le_relax (i : ι) :
    𝓕.localCondition i ≤ (𝓕.relax S).localCondition i := by
  rw [relax_def, withLocalConditions_localCondition]
  exact le_iInf fun _ ↦ le_rfl

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Replacing the local conditions of a relaxed structure retains only the new system. -/
@[simp]
theorem withLocalConditions_relax :
    (𝓕.relax S).withLocalConditions A = 𝓕.withLocalConditions A :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Relaxing on `S` and then on `T` is relaxing on `S ∪ T`. -/
@[simp]
theorem relax_relax (T : Set ι) : (𝓕.relax S).relax T = 𝓕.relax (S ∪ T) := by
  rw [relax_def, withLocalConditions_relax, relax_def]
  congr 1
  funext i
  rw [withLocalConditions_localCondition, iInf_and', Set.mem_union, not_or, and_comm]

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Relaxing on the empty set leaves the Selmer structure unchanged. -/
@[simp]
theorem relax_empty : 𝓕.relax (∅ : Set ι) = 𝓕 := by
  simp [relax_def]

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Membership in the `S`-relaxed local condition at `i` holds unconditionally for `i ∈ S` and
reduces to `𝓕.localCondition i` outside `S`. -/
@[simp]
theorem mem_relax_localCondition_iff {i : ι} {x : H1 (H i) (N i)} :
    x ∈ (𝓕.relax S).localCondition i ↔ i ∉ S → x ∈ 𝓕.localCondition i := by
  simp only [relax_def, withLocalConditions_localCondition, AddSubgroup.mem_iInf]

/-- Membership in the `S`-relaxed Selmer group is satisfaction of the local conditions outside
`S`. -/
theorem mem_selmerGroup_relax_iff {c : H1 G M} :
    c ∈ (𝓕.relax S).selmerGroup ↔ ∀ i ∉ S, 𝓕.localization i c ∈ 𝓕.localCondition i := by
  simp only [mem_selmerGroup_iff, relax_localization, mem_relax_localCondition_iff]

/-- The original Selmer group is contained in every `S`-relaxed Selmer group. -/
theorem selmerGroup_le_relax : 𝓕.selmerGroup ≤ (𝓕.relax S).selmerGroup := by
  intro c hc
  rw [mem_selmerGroup_iff] at hc
  rw [mem_selmerGroup_relax_iff]
  exact fun i _ ↦ hc i

/-- Enlarging the set of relaxed indices enlarges the relaxed Selmer group. -/
theorem selmerGroup_relax_mono {T : Set ι} (h : S ⊆ T) :
    (𝓕.relax S).selmerGroup ≤ (𝓕.relax T).selmerGroup := by
  intro c hc
  rw [mem_selmerGroup_relax_iff] at hc ⊢
  exact fun i hiT ↦ hc i fun hiS ↦ hiT (h hiS)

end LocalConditions

end SelmerStructure

end TauCeti.ContCohomology
