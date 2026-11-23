/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# The cotangent map of a closed immersion is surjective

For a closed immersion `i : Z ⟶ X` over `Spec R`, the cotangent map
`cotangentMap R i : i^* Ω_{X/R} ⟶ Ω_{Z/R}` is an epimorphism of `𝒪_Z`-modules (Stacks, Lemma
29.33.15 (01UZ)). Over an affine open `V` of `X`, `Γ(X, V) → Γ(Z, i⁻¹ V)` is surjective and the
map on sections over `i⁻¹ V` is `KaehlerDifferential.mapBaseChange`, which is surjective by
`KaehlerDifferential.mapBaseChange_surjective`; the opens `i⁻¹ V` form a basis of `Z`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.Hom.epi_of_surjective_app_of_isBasis`: a morphism of
  `𝒪_X`-modules that is surjective on the sections over the members of a basis of `X` is an
  epimorphism.
* `TauCeti.AlgebraicGeometry.surjective_cotangentMap_app_preimage`: for a closed immersion `i` and
  an affine open `V` of `X`, `cotangentMap R i` is surjective on the sections over `i⁻¹ V`.
* `TauCeti.AlgebraicGeometry.epi_cotangentMap_of_isClosedImmersion`: for a closed immersion `i`,
  `cotangentMap R i` is an epimorphism.

## References

* [Stacks Project, Lemma 29.33.15](https://stacks.math.columbia.edu/tag/01UZ)
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace TauCeti

universe u

/-- A morphism of `𝒪_X`-modules that is surjective on the sections over the members of a basis of
the topology of `X` is an epimorphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.epi_of_surjective_app_of_isBasis
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) {ι : Type*} {B : ι → X.Opens}
    (hB : Opens.IsBasis (Set.range B)) (hf : ∀ i, Function.Surjective (f.app (B i))) :
    Epi f := by
  have : Sheaf.IsLocallySurjective ((AlgebraicGeometry.Scheme.Modules.toSheaf X).map f) := by
    constructor
    intro U s x hx
    obtain ⟨_, ⟨i, rfl⟩, hxi, hiU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
    exact ⟨B i, homOfLE hiU, hf i (N.presheaf.map (homOfLE hiU).op s), hxi⟩
  exact (AlgebraicGeometry.Scheme.Modules.toSheaf X).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] {X Z : Scheme.{u}} [X.Over (Spec (.of R))]
  [Z.Over (Spec (.of R))] (i : Z ⟶ X) [i.IsOver (Spec (.of R))] [IsClosedImmersion i]

/-- For a closed immersion `i : Z ⟶ X` over `Spec R` and an affine open `V` of `X`, the cotangent
map `cotangentMap R i` is surjective on the sections over `i⁻¹ V`: there it is
`KaehlerDifferential.mapBaseChange` for the surjection `Γ(X, V) → Γ(Z, i⁻¹ V)`. -/
theorem surjective_cotangentMap_app_preimage (V : X.affineOpens) :
    Function.Surjective ((cotangentMap R i).app (i ⁻¹ᵁ V.val)) := by
  let U : Z.affineOpens := ⟨i ⁻¹ᵁ V.val, V.property.preimage i⟩
  let : Algebra R Γ(X, V) := ((X.baseRingToStructurePresheaf R).app (op V.val)).hom.toAlgebra
  let : Algebra R Γ(Z, U) := ((Z.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(Z, U) := (i.appLE V.val U.val le_rfl).hom.toAlgebra
  have : IsScalarTower R Γ(X, V) Γ(Z, U) :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_appLE R i V.val U.val le_rfl
  have hs : Function.Surjective (algebraMap Γ(X, V) Γ(Z, U)) := by
    rw [RingHom.algebraMap_toAlgebra, ← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective V.val V.property
  intro y
  obtain ⟨ω, hω⟩ := (KaehlerDifferential.mapBaseChange_surjective R Γ(X, V) Γ(Z, U) hs)
    ((relativeDifferentialsSectionsEquiv R Z U).symm y)
  refine ⟨pullbackRelativeDifferentialsSectionsEquiv R i V U le_rfl ω, ?_⟩
  rw [cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv R i V U le_rfl ω, hω,
    LinearEquiv.apply_symm_apply]

/-- **The cotangent map of a closed immersion is surjective** (Stacks, Lemma 29.33.15 (01UZ)): for
a closed immersion `i : Z ⟶ X` over `Spec R`, `cotangentMap R i : i^* Ω_{X/R} ⟶ Ω_{Z/R}` is an
epimorphism of `𝒪_Z`-modules. -/
theorem epi_cotangentMap_of_isClosedImmersion : Epi (cotangentMap R i) := by
  refine Scheme.Modules.Hom.epi_of_surjective_app_of_isBasis _ (B := fun V : X.affineOpens ↦
    i ⁻¹ᵁ V.val) ?_ (surjective_cotangentMap_app_preimage R i)
  refine Opens.isBasis_iff_nbhd.mpr fun {W z} hz ↦ ?_
  -- `W = i⁻¹ W'` for an open `W'` of `X`, since `i` is an embedding.
  obtain ⟨W', hW'⟩ := i.isEmbedding.isOpen_iff.mp W.isOpen
  have hzW' : z ∈ i ⁻¹' W' := hW'.2 ▸ hz
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hzW' hW'.1
  exact ⟨i ⁻¹ᵁ V, ⟨⟨V, hV⟩, rfl⟩, hzV, fun y hy ↦ (hW'.2 ▸ hVW hy : y ∈ (W : Set Z))⟩

end AlgebraicGeometry

end TauCeti
