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
  convert X.isBasis_affineOpens.of_isInducing i.isEmbedding.isInducing using 1
  ext W
  simp only [Set.mem_range, Set.mem_ofPred_eq, Subtype.exists, exists_prop, ← SetLike.coe_set_eq,
    Scheme.Hom.coe_preimage, Opens.coe_mk]

end AlgebraicGeometry

end TauCeti
