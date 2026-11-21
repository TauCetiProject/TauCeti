/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpringSystem.Tetrahedron.Character
public import TauCeti.Analysis.SpringSystem.Tetrahedron.MatchingStabilizer
import TauCeti.Algebra.Lie.Orthogonal.CrossProduct

/-!
# The decomposition of the displacements of the spring tetrahedron into irreducibles

The symmetric group `S₄` acts on the displacements `u ∈ ℝ¹²` of the spring tetrahedron by
`(σ • u)ᵢ = R_σ u_{σ⁻¹ i}` (`TauCeti.tetrahedronDisplacementRep`), and its character is
`1 + χ_E + 2 χ_V + χ_{sgn ⊗ V}` (`TauCeti.char_tetrahedronDisplacementRep_eq`), where `V` is the
standard representation of `S₄` and `E` its two-dimensional irreducible representation. This file
constructs the decomposition itself, as an equivalence of representations

`1 ⊕ E ⊕ V ⊕ V ⊕ (sgn ⊗ V) ≃ ℝ¹²`

whose summands are the normal modes of the force matrix `H`, written in the coordinates
`uᵢ = t + A qᵢ` of `TauCeti.tetrahedronAffineFieldEquiv`:

* the trivial summand is the breathing line `uᵢ = a qᵢ`, the eigenspace of `H` for `-8`;
* `E` is the eigenspace for `-2`, the span of the matching seeds `uᵢ = Aₘ qᵢ`, and the summand
  sends a sum-zero vector `c` on the three perfect matchings to `∑ₘ cₘ Sₘ`;
* the vibrational copy of `V` is the eigenspace for `-4`, the span of the vertex seeds
  `uᵢ = Aⱼ qᵢ`, and the summand sends a sum-zero vector `c` on the four vertices to `∑ⱼ cⱼ Vⱼ`;
* the translational copy of `V` is the space of translations `uᵢ = t`, through the frame map
  `c ↦ ∑ⱼ cⱼ qⱼ` (`TauCeti.tetrahedronStandardEquiv`);
* `sgn ⊗ V` is the space of infinitesimal rotations `uᵢ = ω ⨯₃ qᵢ`, again through the frame map.

The translations and the rotations together form the kernel of `H`. The two copies of `V` are told
apart by `H`, which vanishes on translations and is `-4` on vibrations, and not by Schur's lemma on
their sum, which has no preferred decomposition. The rotations carry the sign twist because a
tetrahedral symmetry `R_σ` has determinant `sgn σ` (`TauCeti.det_tetrahedronSymmetryMatrix`), so it
preserves the cross product only up to that sign: `(R_σ x) ⨯₃ (R_σ y) = sgn σ • R_σ (x ⨯₃ y)`.

The decomposition is orthogonal for the standard inner product on `ℝ¹²`: distinct eigenspaces of
the symmetric matrix `H` are orthogonal, and translations are orthogonal to rotations because the
centred vertices sum to zero.

## Main definitions

* `TauCeti.tetrahedronBreathingMap`, `TauCeti.tetrahedronMatchingMap`,
  `TauCeti.tetrahedronVibrationMap`: the intertwining maps from the trivial representation, from `E`
  and from `V` onto the eigenspaces of `H` for `-8`, `-2` and `-4`.
* `TauCeti.tetrahedronTranslationMap`, `TauCeti.tetrahedronRotationMap`: the intertwining maps from
  `ℝ³` and from its sign twist onto the translations and the infinitesimal rotations.
* `TauCeti.tetrahedronModeEquiv`: the equivalence of representations
  `1 ⊕ E ⊕ V ⊕ V ⊕ (sgn ⊗ V) ≃ ℝ¹²`.

## Main results

* `TauCeti.range_tetrahedronBreathingMap`, `TauCeti.range_tetrahedronMatchingMap`,
  `TauCeti.range_tetrahedronVibrationMap`: the three summands are the eigenspaces of `H` for `-8`,
  `-2` and `-4`.
* `TauCeti.range_tetrahedronTranslationMap_sup_range_tetrahedronRotationMap`: the translations and
  the rotations span the kernel of `H`.
* `TauCeti.tetrahedronSpringMatrix_mulVec_tetrahedronModeEquiv`: `H` acts on the five summands by
  `-8`, `-2`, `-4`, `0` and `0`.
* `TauCeti.dotProduct_tetrahedronTranslationMap_tetrahedronRotationMap`: translations are
  orthogonal to rotations; the other summands are orthogonal as distinct eigenspaces of `H`
  (`TauCeti.dotProduct_eq_zero_of_mem_eigenspace_tetrahedronSpringMatrix`).

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261 (Cornell,
  2001), pp. 3–5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §2.3.
-/

public section

open Matrix Equiv Representation LieAlgebra.Orthogonal

namespace TauCeti

/-! ### Translations and infinitesimal rotations -/

/-- **The translations** `t ↦ (uᵢ = t)ᵢ`, the field `(t, 0)` in the coordinates `uᵢ = t + A qᵢ`,
as an intertwining map from the symmetry representation on `ℝ³`. -/
noncomputable def tetrahedronTranslationMap :
    IntertwiningMap tetrahedronSymmetryRep tetrahedronDisplacementRep :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (tetrahedronAffineFieldEquiv.toLinearMap ∘ₗ LinearMap.inl ℝ _ _) fun σ t ↦ by
      simp [tetrahedronSymmetryRep_apply, tetrahedronDisplacementRep_affineFieldEquiv]

/-- The translation by `t` is the field `(t, 0)`. -/
theorem tetrahedronTranslationMap_apply (t : Fin 3 → ℝ) :
    tetrahedronTranslationMap t = tetrahedronAffineFieldEquiv (t, 0) :=
  (rfl)

/-- **The infinitesimal rotations** `ω ↦ (uᵢ = ω ⨯₃ qᵢ)ᵢ`, the field `(0, ω̂)`, as an intertwining
map from the sign twist of the symmetry representation on `ℝ³`: the sign appears because `R_σ`
preserves the cross product only up to `sgn σ`. -/
noncomputable def tetrahedronRotationMap :
    IntertwiningMap (charTwist (signLinearCharacter ℝ (Fin 4)) tetrahedronSymmetryRep)
      tetrahedronDisplacementRep :=
  (tetrahedronAffineFieldEquiv.toLinearMap ∘ₗ LinearMap.inr ℝ _ _ ∘ₗ
      crossProductMatrix ℝ).intertwiningMap_of_isIntertwiningMap _ _ fun σ ω ↦ by
    simp only [charTwist_apply, coe_signLinearCharacter_apply, LinearMap.smul_apply,
      tetrahedronSymmetryRep_apply, map_smul, LinearMap.coe_comp, LinearEquiv.coe_coe,
      LinearMap.coe_inr, Function.comp_apply, tetrahedronDisplacementRep_affineFieldEquiv,
      mulVec_zero, tetrahedronSymmetryMatrix_mul_crossProductMatrix_mul]
    rw [← map_smul, Prod.smul_mk, smul_zero]

/-- The rotation with angular velocity `ω` is the field `(0, ω̂)`. -/
theorem tetrahedronRotationMap_apply (ω : Fin 3 → ℝ) :
    tetrahedronRotationMap ω = tetrahedronAffineFieldEquiv (0, crossProductMatrix ℝ ω) :=
  (rfl)

/-- The rotation with angular velocity `ω` moves the vertex `i` by `ω ⨯₃ qᵢ`. -/
theorem curry_tetrahedronRotationMap (ω : Fin 3 → ℝ) (i : Fin 4) :
    Function.curry (tetrahedronRotationMap ω) i = ω ⨯₃ tetrahedronCenteredVertex i := by
  ext k
  simp [tetrahedronRotationMap_apply, tetrahedronAffineFieldEquiv_apply, crossProductMatrix_mulVec]

/-- **Translations are orthogonal to rotations**: `∑ᵢ t ⬝ (ω ⨯₃ qᵢ) = t ⬝ (ω ⨯₃ ∑ᵢ qᵢ) = 0`. -/
theorem dotProduct_tetrahedronTranslationMap_tetrahedronRotationMap (t ω : Fin 3 → ℝ) :
    tetrahedronTranslationMap t ⬝ᵥ tetrahedronRotationMap ω = 0 := by
  have h : ∑ i, t ⬝ᵥ (ω ⨯₃ tetrahedronCenteredVertex i) = 0 := by
    rw [← dotProduct_sum, ← map_sum, sum_tetrahedronCenteredVertex, map_zero, dotProduct_zero]
  rw [← h, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← curry_tetrahedronRotationMap ω i]
  simp [tetrahedronTranslationMap_apply, tetrahedronAffineFieldEquiv_apply]

/-- The translations lie in the kernel of the force matrix. -/
theorem tetrahedronTranslationMap_mem_eigenspace (t : Fin 3 → ℝ) :
    tetrahedronTranslationMap t ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' 0 := by
  rw [tetrahedronTranslationMap_apply, tetrahedronAffineFieldEquiv_mem_eigenspace_zero_iff]
  simp

/-- The infinitesimal rotations lie in the kernel of the force matrix. -/
theorem tetrahedronRotationMap_mem_eigenspace (ω : Fin 3 → ℝ) :
    tetrahedronRotationMap ω ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' 0 := by
  rw [tetrahedronRotationMap_apply, tetrahedronAffineFieldEquiv_mem_eigenspace_zero_iff,
    transpose_crossProductMatrix]

/-- **The translations and the rotations span the kernel of the force matrix**: a field
`(t, A)` lies in the kernel exactly when `A` is skew-symmetric, that is `A = ω̂`. -/
theorem range_tetrahedronTranslationMap_sup_range_tetrahedronRotationMap :
    LinearMap.range tetrahedronTranslationMap.toLinearMap ⊔
        LinearMap.range tetrahedronRotationMap.toLinearMap =
      Module.End.eigenspace tetrahedronSpringMatrix.toLin' 0 := by
  refine le_antisymm (sup_le ?_ ?_) fun u hu ↦ ?_
  · rintro _ ⟨t, rfl⟩
    exact tetrahedronTranslationMap_mem_eigenspace t
  · rintro _ ⟨ω, rfl⟩
    exact tetrahedronRotationMap_mem_eigenspace ω
  obtain ⟨⟨t, A⟩, rfl⟩ := tetrahedronAffineFieldEquiv.surjective u
  rw [tetrahedronAffineFieldEquiv_mem_eigenspace_zero_iff] at hu
  obtain ⟨ω, hω⟩ := (soThreeEquiv ℝ).surjective ⟨A, (mem_so (A := A)).2 hu⟩
  have hA : crossProductMatrix ℝ ω = A := (coe_soThreeEquiv ω).symm.trans (congrArg Subtype.val hω)
  refine Submodule.mem_sup.2 ⟨_, ⟨t, rfl⟩, _, ⟨ω, rfl⟩, ?_⟩
  rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.toLinearMap_apply,
    tetrahedronTranslationMap_apply, tetrahedronRotationMap_apply, hA, ← map_add, Prod.mk_add_mk,
    add_zero, zero_add]

/-! ### The breathing mode -/

/-- **The breathing line** `a ↦ (uᵢ = a qᵢ)ᵢ`, as an intertwining map from the trivial
representation. -/
noncomputable def tetrahedronBreathingMap :
    IntertwiningMap (trivial ℝ (Perm (Fin 4)) ℝ) tetrahedronDisplacementRep :=
  (LinearMap.toSpanSingleton ℝ _ tetrahedronBreathingMode).intertwiningMap_of_isIntertwiningMap
    _ _ fun σ a ↦ by simp [tetrahedronDisplacementRep_breathingMode]

/-- The breathing map sends `a` to `a` times the breathing mode. -/
theorem tetrahedronBreathingMap_apply (a : ℝ) :
    tetrahedronBreathingMap a = a • tetrahedronBreathingMode :=
  (rfl)

/-- The breathing line lies in the eigenspace of the force matrix for `-8`. -/
theorem tetrahedronBreathingMap_mem_eigenspace (a : ℝ) :
    tetrahedronBreathingMap a ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-8) :=
  Submodule.smul_mem _ a tetrahedronBreathingMode_mem_eigenspace

/-- **The breathing line is the eigenspace of the force matrix for `-8`.** -/
theorem range_tetrahedronBreathingMap :
    LinearMap.range tetrahedronBreathingMap.toLinearMap =
      Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-8) := by
  refine le_antisymm ?_ fun u hu ↦ ?_
  · rintro _ ⟨a, rfl⟩
    exact tetrahedronBreathingMap_mem_eigenspace a
  obtain ⟨⟨t, A⟩, rfl⟩ := tetrahedronAffineFieldEquiv.surjective u
  obtain ⟨rfl, a, rfl⟩ := (tetrahedronAffineFieldEquiv_mem_eigenspace_neg_eight_iff t A).1 hu
  refine ⟨a, ?_⟩
  rw [IntertwiningMap.toLinearMap_apply, tetrahedronBreathingMap_apply,
    tetrahedronBreathingMode_def, ← map_smul, Prod.smul_mk, smul_zero]

/-! ### The vibrational copy of the standard representation -/

/-- **The vibrational copy of `V`**: a sum-zero vector `c` on the four vertices goes to the
combination `∑ⱼ cⱼ Vⱼ` of the vibration seeds `(Vⱼ)ᵢ = Aⱼ qᵢ`, which the symmetries permute as
they permute the vertices. -/
noncomputable def tetrahedronVibrationMap :
    IntertwiningMap (standardRepresentation ℝ (Fin 4)) tetrahedronDisplacementRep :=
  (augmentationLinearCombination ℝ (Perm (Fin 4))
      tetrahedronVibrationSeed).intertwiningMap_of_isIntertwiningMap _ _ fun σ v ↦ by
    simp only [augmentationLinearCombination_apply, coe_standardRepresentation_apply,
      coeff_ofMulAction, map_sum, map_smul, tetrahedronDisplacementRep_vibrationSeed]
    rw [← Equiv.sum_comp σ]
    simp [Perm.smul_def]

/-- The vibrational copy of `V` sends `c` to `∑ⱼ cⱼ Vⱼ`. -/
theorem tetrahedronVibrationMap_apply
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronVibrationMap v =
      ∑ j, (v : MonoidAlgebra ℝ (Fin 4)).coeff j • tetrahedronVibrationSeed j :=
  augmentationLinearCombination_apply _ v

/-- **The vibrational copy of `V` is the eigenspace of the force matrix for `-4`.** -/
theorem range_tetrahedronVibrationMap :
    LinearMap.range tetrahedronVibrationMap.toLinearMap =
      Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-4) := by
  rw [← span_range_tetrahedronVibrationSeed]
  exact range_augmentationLinearCombination (by norm_num) sum_tetrahedronVibrationSeed

/-- The vibrational copy of `V` lies in the eigenspace of the force matrix for `-4`. -/
theorem tetrahedronVibrationMap_mem_eigenspace
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronVibrationMap v ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-4) :=
  range_tetrahedronVibrationMap ▸ LinearMap.mem_range_self _ v

/-! ### The two-dimensional summand -/

/-- **The summand `E`**: a sum-zero vector `c` on the three perfect matchings goes to the
combination `∑ₘ cₘ Sₘ` of the matching seeds `(Sₘ)ᵢ = Aₘ qᵢ`, which the symmetries permute as they
permute the matchings. -/
noncomputable def tetrahedronMatchingMap :
    IntertwiningMap (symmetricGroupFourTwoDimensionalRepresentation ℝ)
      tetrahedronDisplacementRep :=
  (augmentationLinearCombination ℝ (Perm (Fin 3))
      tetrahedronMatchingSeed).intertwiningMap_of_isIntertwiningMap _ _ fun σ v ↦ by
    simp only [augmentationLinearCombination_apply,
      symmetricGroupFourTwoDimensionalRepresentation_apply, coe_standardRepresentation_apply,
      coeff_ofMulAction, map_sum, map_smul, tetrahedronDisplacementRep_matchingSeed]
    rw [← Equiv.sum_comp (symmetricGroupFourMatchingHom σ)]
    simp [Perm.smul_def]

/-- The summand `E` sends `c` to `∑ₘ cₘ Sₘ`. -/
theorem tetrahedronMatchingMap_apply
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 3)) (Fin 3)).toSubmodule) :
    tetrahedronMatchingMap v =
      ∑ m, (v : MonoidAlgebra ℝ (Fin 3)).coeff m • tetrahedronMatchingSeed m :=
  augmentationLinearCombination_apply _ v

/-- **The summand `E` is the eigenspace of the force matrix for `-2`.** -/
theorem range_tetrahedronMatchingMap :
    LinearMap.range tetrahedronMatchingMap.toLinearMap =
      Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-2) := by
  rw [← span_range_tetrahedronMatchingSeed]
  exact range_augmentationLinearCombination (by norm_num) sum_tetrahedronMatchingSeed

/-- The summand `E` lies in the eigenspace of the force matrix for `-2`. -/
theorem tetrahedronMatchingMap_mem_eigenspace
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 3)) (Fin 3)).toSubmodule) :
    tetrahedronMatchingMap v ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-2) :=
  range_tetrahedronMatchingMap ▸ LinearMap.mem_range_self _ v

/-! ### The decomposition -/

/-- The translational copy of `V`, through the frame map `c ↦ ∑ⱼ cⱼ qⱼ`. -/
private noncomputable abbrev tetrahedronStandardTranslationMap :
    IntertwiningMap (standardRepresentation ℝ (Fin 4)) tetrahedronDisplacementRep :=
  tetrahedronTranslationMap.comp tetrahedronStandardEquiv.toIntertwiningMap

/-- The rotations as the sign twist of `V`, through the frame map `c ↦ ∑ⱼ cⱼ qⱼ`. -/
private noncomputable abbrev tetrahedronStandardRotationMap :
    IntertwiningMap (charTwist (signLinearCharacter ℝ (Fin 4)) (standardRepresentation ℝ (Fin 4)))
      tetrahedronDisplacementRep :=
  tetrahedronRotationMap.comp
    (IntertwiningMap.charTwistLinearEquiv _ tetrahedronStandardEquiv.toIntertwiningMap)

/-- The sum of the five summands, as a linear map. -/
private noncomputable abbrev tetrahedronModeMap :
    (ℝ × (augmentationSubrepresentation ℝ (Perm (Fin 3)) (Fin 3)).toSubmodule ×
      (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule ×
      (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule ×
      (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) →ₗ[ℝ]
      (Fin 4 × Fin 3 → ℝ) :=
  tetrahedronBreathingMap.toLinearMap.coprod <| tetrahedronMatchingMap.toLinearMap.coprod <|
    tetrahedronVibrationMap.toLinearMap.coprod <|
      tetrahedronStandardTranslationMap.toLinearMap.coprod
        tetrahedronStandardRotationMap.toLinearMap

private theorem tetrahedronModeMap_surjective : Function.Surjective tetrahedronModeMap := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← sup_eigenspace_tetrahedronSpringMatrix_eq_top,
    ← range_tetrahedronTranslationMap_sup_range_tetrahedronRotationMap,
    ← range_tetrahedronMatchingMap, ← range_tetrahedronVibrationMap,
    ← range_tetrahedronBreathingMap]
  refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨(0, 0, 0, tetrahedronStandardEquiv.symm t, 0), by simp⟩
  · rintro _ ⟨ω, rfl⟩
    exact ⟨(0, 0, 0, 0, tetrahedronStandardEquiv.symm ω), by simp⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨(0, c, 0, 0, 0), by simp⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨(0, 0, c, 0, 0), by simp⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨(a, 0, 0, 0, 0), by simp⟩

private theorem tetrahedronModeMap_bijective : Function.Bijective tetrahedronModeMap := by
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2
    tetrahedronModeMap_surjective, tetrahedronModeMap_surjective⟩
  simp [Module.finrank_prod]

/-- **The decomposition of the displacements of the spring tetrahedron into irreducibles**, the
equivalence of representations `1 ⊕ E ⊕ V ⊕ V ⊕ (sgn ⊗ V) ≃ ℝ¹²` sending `(a, c, c', c'', c''')`
to the sum of the breathing mode `a qᵢ`, the combination `∑ₘ cₘ Sₘ` of matching seeds, the
combination `∑ⱼ c'ⱼ Vⱼ` of vibration seeds, the translation by `∑ⱼ c''ⱼ qⱼ` and the rotation with
angular velocity `∑ⱼ c'''ⱼ qⱼ`. -/
noncomputable def tetrahedronModeEquiv :
    ((trivial ℝ (Perm (Fin 4)) ℝ).prod <| (symmetricGroupFourTwoDimensionalRepresentation ℝ).prod <|
      (standardRepresentation ℝ (Fin 4)).prod <| (standardRepresentation ℝ (Fin 4)).prod <|
        charTwist (signLinearCharacter ℝ (Fin 4)) (standardRepresentation ℝ (Fin 4))).Equiv
      tetrahedronDisplacementRep :=
  .mk (LinearEquiv.ofBijective tetrahedronModeMap tetrahedronModeMap_bijective) fun σ ↦
    LinearMap.ext fun x ↦ by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, prod_apply_apply,
        IntertwiningMap.toLinearMap_apply, IntertwiningMap.isIntertwining, map_add]

/-- The decomposition sends `(a, c, c', c'', c''')` to the sum of the images of its five
components. -/
theorem tetrahedronModeEquiv_apply (a : ℝ)
    (c : (augmentationSubrepresentation ℝ (Perm (Fin 3)) (Fin 3)).toSubmodule)
    (c' c'' c''' : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronModeEquiv (a, c, c', c'', c''') =
      tetrahedronBreathingMap a + tetrahedronMatchingMap c + tetrahedronVibrationMap c' +
        tetrahedronTranslationMap (tetrahedronStandardEquiv c'') +
          tetrahedronRotationMap (tetrahedronStandardEquiv c''') := by
  simp [tetrahedronModeEquiv, add_assoc]

/-- **The force matrix is diagonal in the decomposition**: it acts on the breathing line by `-8`,
on `E` by `-2`, on the vibrational copy of `V` by `-4`, and kills the translations and the
rotations. -/
theorem tetrahedronSpringMatrix_mulVec_tetrahedronModeEquiv (a : ℝ)
    (c : (augmentationSubrepresentation ℝ (Perm (Fin 3)) (Fin 3)).toSubmodule)
    (c' c'' c''' : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronSpringMatrix *ᵥ tetrahedronModeEquiv (a, c, c', c'', c''') =
      tetrahedronModeEquiv ((-8 : ℝ) • a, (-2 : ℝ) • c, (-4 : ℝ) • c', 0, 0) := by
  have hmem {μ : ℝ} {u : Fin 4 × Fin 3 → ℝ}
      (hu : u ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' μ) :
      tetrahedronSpringMatrix *ᵥ u = μ • u := by
    rwa [Module.End.mem_eigenspace_iff, toLin'_apply] at hu
  rw [tetrahedronModeEquiv_apply, tetrahedronModeEquiv_apply, mulVec_add, mulVec_add, mulVec_add,
    mulVec_add, hmem (tetrahedronBreathingMap_mem_eigenspace a),
    hmem (tetrahedronMatchingMap_mem_eigenspace c),
    hmem (tetrahedronVibrationMap_mem_eigenspace c'),
    hmem (tetrahedronTranslationMap_mem_eigenspace _),
    hmem (tetrahedronRotationMap_mem_eigenspace _)]
  simp [← map_smul]

end TauCeti
