/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SelmerData
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Selmer structures with compact and rational coefficients

The discrete Selmer structures of `TauCeti.ContCohomology.SelmerStructure` localise the explicit
`H¹` of a discrete module. For a compact lattice `T`, a rational representation `V = T ⊗ ℚ_p` or
any other topological representation `X : TopRep R G` over a topological ring `R`, the same
diagram is formed with Mathlib's continuous cohomology `continuousCohomology 1 X`, an `R`-module.
Fix local groups `H i` with continuous homomorphisms `φ i : H i →ₜ* G` (in the arithmetic
application, decomposition groups `G_{K_v} → G_{K,Σ}`). A Selmer structure on `X` consists of a
local coefficient morphism `res (φ i) X ⟶ Y i` and an `R`-submodule of `H¹(H i, Y i)` for each
`i`. Its localisation maps are the maps `ContinuousCohomology.map (φ i)` of these compatible
pairs, and it gives Selmer data over `R` (`TauCeti.SelmerData`), whose operations (relaxed and
strict conditions, the kernel description) then apply.

The local groups are a parameter rather than a field, so that Selmer structures on different
coefficients over the same places can be compared. A coefficient morphism `a : X ⟶ X'` together
with local morphisms `b i : Y i ⟶ Y' i` making the coefficient squares commute commutes with the
localisation maps (`TauCeti.ContinuousCohomology.TopSelmerStructure.localization_comp_coeffMap`).
So `a` carries Selmer classes into Selmer classes for the pushed-forward local conditions, and the
pulled-back local conditions cut out the preimage of the Selmer module. For `T → V → A = V/T`
this is the propagation of a local condition on `V` to `T` (preimage) and to `A` (image). The
comparison of the discrete quotient `A` with the discrete interface is
`TauCeti/RepresentationTheory/Homological/ContCohomology/SelmerStructure/ContinuousDiscrete.lean`.

## Main definitions

* `TauCeti.ContinuousCohomology.TopSelmerStructure`: local coefficient morphisms and local
  conditions for a topological representation.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.localization`: the `R`-linear localisation map
  `H¹(G, X) → H¹(H i, Y i)`.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.toSelmerData`: the Selmer data over `R`.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.withLocalConditions`: replace the local
  conditions.

## Main results

* `TauCeti.ContinuousCohomology.TopSelmerStructure.mem_selmerModule_toSelmerData_iff`: a class
  is Selmer exactly when every localisation satisfies the local condition.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.localization_comp_coeffMap`: localisation
  commutes with change of coefficients.
* `TauCeti.ContinuousCohomology.TopSelmerStructure.map_selmerModule_le`,
  `TauCeti.ContinuousCohomology.TopSelmerStructure.selmerModule_eq_comap`: Selmer classes map to
  Selmer classes, and pulled-back conditions give the preimage of the Selmer module.

## References

* B. Mazur and K. Rubin, *Kolyvagin systems*, Mem. Amer. Math. Soc. 168 (2004), arXiv v1,
  Definition 1.1 and Definition 2.1.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.1 and I.5.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type*} {H : ι → Type v} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)]

variable (φ : ∀ i, H i →ₜ* G) (X : TopRep.{max v w} R G) (Y : ∀ i, TopRep.{max v w} R (H i))

/-- **A Selmer structure on a topological representation** `X` of `G`, over the local groups
`φ i : H i →ₜ* G`: a local coefficient morphism `res (φ i) X ⟶ Y i` along which `H¹(G, X)` is
localised to `H¹(H i, Y i)`, and a local condition, an `R`-submodule of `H¹(H i, Y i)`, for each
index `i`. -/
structure TopSelmerStructure where
  /-- The local coefficient morphism `res (φ i) X ⟶ Y i`. -/
  coeffHom : ∀ i, TopRep.res (φ i : H i →* G) X ⟶ Y i
  /-- The local condition at `i`, an `R`-submodule of `H¹(H i, Y i)`. -/
  localCondition : ∀ i, Submodule R (continuousCohomology 1 (Y i))

namespace TopSelmerStructure

variable {φ X Y} (𝓕 : TopSelmerStructure φ X Y)

/-- **The localisation map** `H¹(G, X) → H¹(H i, Y i)` of a Selmer structure: the map on
continuous cohomology of the compatible pair `(φ i, 𝓕.coeffHom i)`. -/
def localization (i : ι) : continuousCohomology 1 X →ₗ[R] continuousCohomology 1 (Y i) :=
  (map (φ i) (𝓕.coeffHom i) 1).hom.toLinearMap

/-- `𝓕.localization i` is the map of the compatible pair `(φ i, 𝓕.coeffHom i)`. -/
theorem localization_apply (i : ι) (c : continuousCohomology 1 X) :
    𝓕.localization i c = map (φ i) (𝓕.coeffHom i) 1 c :=
  (rfl)

/-- **The Selmer data over `R` of a Selmer structure**: its localisation maps and local
conditions. -/
def toSelmerData : SelmerData R ι (continuousCohomology 1 X) fun i => continuousCohomology 1 (Y i)
    where
  localization := 𝓕.localization
  localCondition := 𝓕.localCondition

/-- The localisation maps of `𝓕.toSelmerData` are those of `𝓕`. -/
@[simp]
theorem toSelmerData_localization : 𝓕.toSelmerData.localization = 𝓕.localization :=
  (rfl)

/-- The local conditions of `𝓕.toSelmerData` are those of `𝓕`. -/
@[simp]
theorem toSelmerData_localCondition : 𝓕.toSelmerData.localCondition = 𝓕.localCondition :=
  (rfl)

/-- A class is Selmer exactly when its localisation at every index satisfies the local
condition. -/
theorem mem_selmerModule_toSelmerData_iff {c : continuousCohomology 1 X} :
    c ∈ 𝓕.toSelmerData.selmerModule ↔ ∀ i, 𝓕.localization i c ∈ 𝓕.localCondition i :=
  𝓕.toSelmerData.mem_selmerModule_iff

/-- Replace the local conditions of a Selmer structure, keeping the coefficient morphisms. -/
def withLocalConditions (L : ∀ i, Submodule R (continuousCohomology 1 (Y i))) :
    TopSelmerStructure φ X Y :=
  { 𝓕 with localCondition := L }

omit [IsTopologicalGroup G] in
/-- Replacing the local conditions keeps the coefficient morphisms. -/
@[simp]
theorem withLocalConditions_coeffHom (L : ∀ i, Submodule R (continuousCohomology 1 (Y i))) :
    (𝓕.withLocalConditions L).coeffHom = 𝓕.coeffHom :=
  (rfl)

omit [IsTopologicalGroup G] in
/-- The replaced Selmer structure has the prescribed local conditions. -/
@[simp]
theorem withLocalConditions_localCondition
    (L : ∀ i, Submodule R (continuousCohomology 1 (Y i))) :
    (𝓕.withLocalConditions L).localCondition = L :=
  (rfl)

/-- Replacing the local conditions keeps the localisation maps. -/
@[simp]
theorem withLocalConditions_localization
    (L : ∀ i, Submodule R (continuousCohomology 1 (Y i))) :
    (𝓕.withLocalConditions L).localization = 𝓕.localization :=
  (rfl)

/-- Replacing the local conditions of a Selmer structure replaces those of its Selmer data. -/
theorem toSelmerData_withLocalConditions
    (L : ∀ i, Submodule R (continuousCohomology 1 (Y i))) :
    (𝓕.withLocalConditions L).toSelmerData = 𝓕.toSelmerData.withLocalConditions L :=
  SelmerData.ext (by simp) (by simp)

/-! ### Change of coefficients -/

section Map

variable {X' : TopRep.{max v w} R G} {Y' : ∀ i, TopRep.{max v w} R (H i)}
  (𝓖 : TopSelmerStructure φ X' Y')
  {a : X ⟶ X'} {b : ∀ i, Y i ⟶ Y' i}

/-- **Localisation commutes with change of coefficients.** For a coefficient morphism
`a : X ⟶ X'` and local morphisms `b i : Y i ⟶ Y' i` making the coefficient squares commute, the
coefficient map of `a` followed by the localisation of `𝓖` is the localisation of `𝓕` followed by
the coefficient map of `b i`. -/
theorem localization_comp_coeffMap
    (h : ∀ i, (TopRep.resFunctor (φ i : H i →* G)).map a ≫ 𝓖.coeffHom i = 𝓕.coeffHom i ≫ b i)
    (i : ι) :
    𝓖.localization i ∘ₗ (coeffMap a 1).hom.toLinearMap =
      (coeffMap (b i) 1).hom.toLinearMap ∘ₗ 𝓕.localization i := by
  ext c
  exact congr($((map_comp_coeffMap (φ i) (𝓕.coeffHom i) (𝓖.coeffHom i) a (b i) (h i) 1).symm) c)

/-- **Selmer classes map to Selmer classes** under a change of coefficients commuting with the
local coefficient morphisms that carries each local condition of `𝓕` into that of `𝓖`. -/
theorem map_selmerModule_le
    (h : ∀ i, (TopRep.resFunctor (φ i : H i →* G)).map a ≫ 𝓖.coeffHom i = 𝓕.coeffHom i ≫ b i)
    (hL : ∀ i, (𝓕.localCondition i).map (coeffMap (b i) 1).hom.toLinearMap ≤
      𝓖.localCondition i) :
    𝓕.toSelmerData.selmerModule.map (coeffMap a 1).hom.toLinearMap ≤
      𝓖.toSelmerData.selmerModule :=
  𝓕.toSelmerData.map_selmerModule_le 𝓖.toSelmerData (𝓕.localization_comp_coeffMap 𝓖 h) hL

/-- **Propagation to a target of coefficients.** A change of coefficients commuting with the
local coefficient morphisms carries the Selmer module of `𝓕` into that of `𝓖` with its local
conditions replaced by the images of those of `𝓕`; for `V → A = V/T` this is the propagated
condition on `A`. -/
theorem map_selmerModule_le_withLocalConditions_map
    (h : ∀ i, (TopRep.resFunctor (φ i : H i →* G)).map a ≫ 𝓖.coeffHom i = 𝓕.coeffHom i ≫ b i) :
    𝓕.toSelmerData.selmerModule.map (coeffMap a 1).hom.toLinearMap ≤
      (𝓖.withLocalConditions fun i =>
        (𝓕.localCondition i).map (coeffMap (b i) 1).hom.toLinearMap).toSelmerData.selmerModule :=
  𝓕.map_selmerModule_le _ h fun _ => le_rfl

/-- **Propagation to a source of coefficients.** If a change of coefficients commutes with the
local coefficient morphisms and the local conditions of `𝓕` are the preimages of those of `𝓖`,
then the Selmer module of `𝓕` is the preimage of that of `𝓖`; for `T → V` this is the
propagated condition on the lattice `T`. -/
theorem selmerModule_eq_comap
    (h : ∀ i, (TopRep.resFunctor (φ i : H i →* G)).map a ≫ 𝓖.coeffHom i = 𝓕.coeffHom i ≫ b i)
    (hL : ∀ i, 𝓕.localCondition i =
      (𝓖.localCondition i).comap (coeffMap (b i) 1).hom.toLinearMap) :
    𝓕.toSelmerData.selmerModule =
      𝓖.toSelmerData.selmerModule.comap (coeffMap a 1).hom.toLinearMap := by
  have hF : 𝓕.toSelmerData = 𝓕.toSelmerData.withLocalConditions fun i =>
      (𝓖.localCondition i).comap (coeffMap (b i) 1).hom.toLinearMap :=
    SelmerData.ext (by simp) (funext fun i => by simp [hL i])
  rw [hF]
  exact 𝓕.toSelmerData.selmerModule_withLocalConditions_comap 𝓖.toSelmerData
    (𝓕.localization_comp_coeffMap 𝓖 h)

end Map

end TopSelmerStructure

end TauCeti.ContinuousCohomology
