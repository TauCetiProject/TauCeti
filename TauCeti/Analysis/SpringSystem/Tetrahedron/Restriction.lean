/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Analysis.SpringSystem.Tetrahedron.Basic

/-!
# The spring tetrahedron restricted to a vertex stabilizer

The symmetric group `S₄` acts on the displacements `u ∈ ℝ¹²` of the spring tetrahedron, and its
force matrix `H` has the eigenvalues `0`, `-2`, `-4` and `-8`
(`TauCeti.Analysis.SpringSystem.Tetrahedron.Basic`).
This file restricts the action to the stabilizer `S₃` of a vertex `i` and describes the fixed
displacements by explicit seeds, in the coordinates `uⱼ = t + A qⱼ`:

* the breathing mode `uⱼ = qⱼ`, in the eigenspace for `-8`;
* the translation seed `uⱼ = qᵢ`, in the kernel of `H`;
* the vibration seed `uⱼ = Aᵢ qⱼ`, with `Aᵢ = qᵢ qᵢᵀ - ¼ 1`, in the eigenspace for `-4`.

These three span the `S₃`-fixed displacements, which therefore form a three-dimensional space.
The symmetries permute the seeds of the four vertices, `σ • Vᵢ = V_{σ i}`, so the `S₄`-orbit of a
vibration seed consists of the four distinct vibration seeds; they sum to zero and span the
eigenspace for `-4`, because the four matrices `Aᵢ` span the symmetric matrices with zero
diagonal. These are symmetric spanning sets of the irreducible summands, not bases.

The computations use that a transposition acts on `ℝ³` by the reflection in the plane orthogonal
to its edge, and that `σ` acts in the coordinates `(t, A)` by `(R_σ t, R_σ A R_σ⁻¹)`.

## Main definitions

* `TauCeti.tetrahedronVertexSeedMatrix`: the matrix `Aᵢ = qᵢ qᵢᵀ - ¼ 1`.
* `TauCeti.tetrahedronBreathingMode`, `TauCeti.tetrahedronTranslationSeed`,
  `TauCeti.tetrahedronVibrationSeed`: the displacements `uⱼ = qⱼ`, `uⱼ = qᵢ` and `uⱼ = Aᵢ qⱼ`.

## Main results

* `TauCeti.mem_span_range_tetrahedronVertexSeedMatrix_iff`: the `Aᵢ` span the symmetric
  matrices with zero diagonal.
* `TauCeti.ncard_range_tetrahedronDisplacementRep_vibrationSeed`: the `S₄`-orbit of a vibration
  seed has four elements, and `TauCeti.stabilizer_tetrahedronVibrationSeed`: its stabilizer is the
  vertex stabilizer.
* `TauCeti.span_range_tetrahedronVibrationSeed`: the vibration seeds span the eigenspace of `H`
  for `-4`.
* `TauCeti.invariants_tetrahedronDisplacementRep_comp_stabilizer` and
  `TauCeti.finrank_invariants_tetrahedronDisplacementRep_comp_stabilizer`: the `S₃`-fixed
  displacements are spanned by the three seeds and form a space of dimension `3`.

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261 (Cornell,
  2001), pp. 3–5.
-/

public section

namespace TauCeti

open Matrix

/-! ### The vertex seed matrices -/

/-- The seed matrix `Aᵢ = qᵢ qᵢᵀ - ¼ 1` of the vertex `i`: the trace-free part of `qᵢ qᵢᵀ`
(recall `qᵢ ⬝ qᵢ = ¾`). It is symmetric with zero diagonal, and conjugation by `R_σ` moves it to
`A_{σ i}` (`tetrahedronSymmetryMatrix_mul_vertexSeedMatrix_mul`), so it is fixed by the
symmetries fixing `i`. -/
noncomputable def tetrahedronVertexSeedMatrix (i : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  vecMulVec (tetrahedronCenteredVertex i) (tetrahedronCenteredVertex i) - (4 : ℝ)⁻¹ • 1

/-- The defining formula `Aᵢ = qᵢ qᵢᵀ - ¼ 1`. -/
theorem tetrahedronVertexSeedMatrix_def (i : Fin 4) :
    tetrahedronVertexSeedMatrix i =
      vecMulVec (tetrahedronCenteredVertex i) (tetrahedronCenteredVertex i) - (4 : ℝ)⁻¹ • 1 :=
  (rfl)

/-- The entries of `Aᵢ`: zero on the diagonal and `qᵢₖ qᵢₗ = ±¼` off it. -/
theorem tetrahedronVertexSeedMatrix_apply (i : Fin 4) (k l : Fin 3) :
    tetrahedronVertexSeedMatrix i k l =
      if k = l then 0 else tetrahedronCenteredVertex i k * tetrahedronCenteredVertex i l := by
  rw [tetrahedronVertexSeedMatrix_def]
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [tetrahedronCenteredVertex_eq] <;> norm_num

/-- The seed matrices are symmetric. -/
theorem isSymm_tetrahedronVertexSeedMatrix (i : Fin 4) :
    (tetrahedronVertexSeedMatrix i).IsSymm := by
  ext k l
  simp only [transpose_apply, tetrahedronVertexSeedMatrix_apply, eq_comm (a := l), mul_comm]

/-- The seed matrices have zero diagonal. -/
@[simp]
theorem diag_tetrahedronVertexSeedMatrix (i : Fin 4) :
    (tetrahedronVertexSeedMatrix i).diag = 0 := by
  ext k
  simp [tetrahedronVertexSeedMatrix_apply]

/-- Conjugation by `R_σ` moves the seed matrix of `i` to that of `σ i`. -/
@[simp]
theorem tetrahedronSymmetryMatrix_mul_vertexSeedMatrix_mul (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    tetrahedronSymmetryMatrix σ * tetrahedronVertexSeedMatrix i * tetrahedronSymmetryMatrix σ⁻¹ =
      tetrahedronVertexSeedMatrix (σ i) := by
  have h : tetrahedronCenteredVertex i ᵥ* tetrahedronSymmetryMatrix σ⁻¹ =
      tetrahedronCenteredVertex (σ i) := by
    rw [← mulVec_transpose, transpose_tetrahedronSymmetryMatrix, inv_inv,
      tetrahedronSymmetryMatrix_mulVec]
  rw [tetrahedronVertexSeedMatrix_def, tetrahedronVertexSeedMatrix_def, Matrix.mul_sub,
    Matrix.sub_mul, mul_vecMulVec, vecMulVec_mul, tetrahedronSymmetryMatrix_mulVec, h,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← map_mul, mul_inv_cancel, map_one]

/-- The four seed matrices sum to zero. -/
theorem sum_tetrahedronVertexSeedMatrix : ∑ i, tetrahedronVertexSeedMatrix i = 0 := by
  simp only [tetrahedronVertexSeedMatrix_def, Finset.sum_sub_distrib,
    sum_vecMulVec_tetrahedronCenteredVertex, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

/-- The four seed matrices are distinct. -/
theorem tetrahedronVertexSeedMatrix_injective : Function.Injective tetrahedronVertexSeedMatrix := by
  intro i j h
  have h' := And.intro (congrFun (congrFun h 0) 1) (congrFun (congrFun h 0) 2)
  simp only [tetrahedronVertexSeedMatrix_apply] at h'
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [tetrahedronCenteredVertex_eq] at h'

/-- The seed matrices span the symmetric matrices with zero diagonal. -/
theorem mem_span_range_tetrahedronVertexSeedMatrix_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ Submodule.span ℝ (Set.range tetrahedronVertexSeedMatrix) ↔ A.IsSymm ∧ A.diag = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · simp [IsSymm, transpose_sum, (isSymm_tetrahedronVertexSeedMatrix _).eq]
    · ext k
      simp [Matrix.sum_apply, tetrahedronVertexSeedMatrix_apply]
  · rintro ⟨hA, hd⟩
    refine ⟨![A 0 1 + A 0 2 + A 1 2, A 0 1 - A 0 2 - A 1 2, -A 0 1 + A 0 2 - A 1 2,
      -A 0 1 - A 0 2 + A 1 2], ?_⟩
    have hd' (k : Fin 3) : A k k = 0 := congrFun hd k
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [Fin.sum_univ_four, tetrahedronVertexSeedMatrix_apply, tetrahedronCenteredVertex_eq,
        hd', ← hA.apply 0 1, ← hA.apply 0 2, ← hA.apply 1 2] <;> ring

/-! ### The breathing mode and the vertex seeds -/

/-- The breathing mode `uⱼ = qⱼ`, which moves every vertex radially. -/
noncomputable def tetrahedronBreathingMode : Fin 4 × Fin 3 → ℝ :=
  tetrahedronAffineFieldEquiv (0, 1)

/-- The breathing mode is the field `(t, A) = (0, 1)`. -/
theorem tetrahedronBreathingMode_def :
    tetrahedronBreathingMode = tetrahedronAffineFieldEquiv (0, 1) :=
  (rfl)

/-- The translation seed `uⱼ = qᵢ` of the vertex `i`: every vertex moves along the direction of
the vertex `i`. -/
noncomputable def tetrahedronTranslationSeed (i : Fin 4) : Fin 4 × Fin 3 → ℝ :=
  tetrahedronAffineFieldEquiv (tetrahedronCenteredVertex i, 0)

/-- The translation seed of `i` is the field `(t, A) = (qᵢ, 0)`. -/
theorem tetrahedronTranslationSeed_def (i : Fin 4) :
    tetrahedronTranslationSeed i = tetrahedronAffineFieldEquiv (tetrahedronCenteredVertex i, 0) :=
  (rfl)

/-- The vibration seed `uⱼ = Aᵢ qⱼ` of the vertex `i`, where `Aᵢ = qᵢ qᵢᵀ - ¼ 1` is
`tetrahedronVertexSeedMatrix i`. -/
noncomputable def tetrahedronVibrationSeed (i : Fin 4) : Fin 4 × Fin 3 → ℝ :=
  tetrahedronAffineFieldEquiv (0, tetrahedronVertexSeedMatrix i)

/-- The vibration seed of `i` is the field `(t, A) = (0, Aᵢ)`. -/
theorem tetrahedronVibrationSeed_def (i : Fin 4) :
    tetrahedronVibrationSeed i = tetrahedronAffineFieldEquiv (0, tetrahedronVertexSeedMatrix i) :=
  (rfl)

/-- The breathing mode has squared norm `∑ⱼ qⱼ ⬝ qⱼ = 3`. -/
@[simp]
theorem dotProduct_tetrahedronBreathingMode_self :
    tetrahedronBreathingMode ⬝ᵥ tetrahedronBreathingMode = 3 := by
  rw [tetrahedronBreathingMode_def]
  simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_three,
    tetrahedronCenteredVertex_eq]
  norm_num

/-- The breathing mode is fixed by every symmetry. -/
@[simp]
theorem tetrahedronDisplacementRep_breathingMode (σ : Equiv.Perm (Fin 4)) :
    tetrahedronDisplacementRep σ tetrahedronBreathingMode = tetrahedronBreathingMode := by
  rw [tetrahedronBreathingMode_def, tetrahedronDisplacementRep_affineFieldEquiv, mulVec_zero,
    Matrix.mul_one, ← map_mul, mul_inv_cancel, map_one]

/-- The symmetries permute the translation seeds: `σ • Tᵢ = T_{σ i}`. -/
@[simp]
theorem tetrahedronDisplacementRep_translationSeed (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    tetrahedronDisplacementRep σ (tetrahedronTranslationSeed i) =
      tetrahedronTranslationSeed (σ i) := by
  simp [tetrahedronTranslationSeed_def, tetrahedronDisplacementRep_affineFieldEquiv]

/-- The symmetries permute the vibration seeds: `σ • Vᵢ = V_{σ i}`. -/
@[simp]
theorem tetrahedronDisplacementRep_vibrationSeed (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    tetrahedronDisplacementRep σ (tetrahedronVibrationSeed i) =
      tetrahedronVibrationSeed (σ i) := by
  simp [tetrahedronVibrationSeed_def, tetrahedronDisplacementRep_affineFieldEquiv]

/-- The four translation seeds sum to zero. -/
theorem sum_tetrahedronTranslationSeed : ∑ i, tetrahedronTranslationSeed i = 0 := by
  simp only [tetrahedronTranslationSeed_def]
  rw [← map_sum, ← prod_mk_sum, sum_tetrahedronCenteredVertex, Finset.sum_const_zero,
    Prod.mk_zero_zero, map_zero]

/-- The four vibration seeds sum to zero. -/
theorem sum_tetrahedronVibrationSeed : ∑ i, tetrahedronVibrationSeed i = 0 := by
  simp only [tetrahedronVibrationSeed_def]
  rw [← map_sum, ← prod_mk_sum, sum_tetrahedronVertexSeedMatrix, Finset.sum_const_zero,
    Prod.mk_zero_zero, map_zero]

/-- The four vibration seeds are distinct. -/
theorem tetrahedronVibrationSeed_injective : Function.Injective tetrahedronVibrationSeed :=
  tetrahedronAffineFieldEquiv.injective.comp <|
    (Prod.mk_right_injective 0).comp tetrahedronVertexSeedMatrix_injective

/-- The stabilizer of the vibration seed of `i` in `S₄` is the stabilizer of the vertex `i`. -/
theorem stabilizer_tetrahedronVibrationSeed (i : Fin 4) :
    tetrahedronDisplacementRep.stabilizer (tetrahedronVibrationSeed i) =
      MulAction.stabilizer (Equiv.Perm (Fin 4)) i := by
  ext σ
  rw [Representation.mem_stabilizer, MulAction.mem_stabilizer_iff,
    tetrahedronDisplacementRep_vibrationSeed, tetrahedronVibrationSeed_injective.eq_iff,
    Equiv.Perm.smul_def]

/-- The `S₄`-orbit of a vibration seed is the set of the four vibration seeds. -/
theorem range_tetrahedronDisplacementRep_vibrationSeed (i : Fin 4) :
    Set.range (fun σ ↦ tetrahedronDisplacementRep σ (tetrahedronVibrationSeed i)) =
      Set.range tetrahedronVibrationSeed := by
  ext u
  simp only [Set.mem_range, tetrahedronDisplacementRep_vibrationSeed]
  exact ⟨fun ⟨σ, h⟩ ↦ ⟨σ i, h⟩, fun ⟨j, h⟩ ↦ ⟨Equiv.swap i j, by rwa [Equiv.swap_apply_left]⟩⟩

/-- The `S₄`-orbit of a vibration seed has exactly four elements. -/
theorem ncard_range_tetrahedronDisplacementRep_vibrationSeed (i : Fin 4) :
    (Set.range (fun σ ↦ tetrahedronDisplacementRep σ (tetrahedronVibrationSeed i))).ncard = 4 := by
  rw [range_tetrahedronDisplacementRep_vibrationSeed,
    Set.ncard_range_of_injective tetrahedronVibrationSeed_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-! ### The seeds in the eigenspaces of the force matrix -/

/-- The breathing mode lies in the eigenspace of the force matrix for `-8`. -/
theorem tetrahedronBreathingMode_mem_eigenspace :
    tetrahedronBreathingMode ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-8) := by
  rw [tetrahedronBreathingMode_def, tetrahedronAffineFieldEquiv_mem_eigenspace_neg_eight_iff]
  exact ⟨rfl, 1, (one_smul _ _).symm⟩

/-- The translation seeds lie in the kernel of the force matrix. -/
theorem tetrahedronTranslationSeed_mem_eigenspace (i : Fin 4) :
    tetrahedronTranslationSeed i ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' 0 := by
  rw [tetrahedronTranslationSeed_def, tetrahedronAffineFieldEquiv_mem_eigenspace_zero_iff]
  simp

/-- The vibration seeds lie in the eigenspace of the force matrix for `-4`. -/
theorem tetrahedronVibrationSeed_mem_eigenspace (i : Fin 4) :
    tetrahedronVibrationSeed i ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-4) := by
  rw [tetrahedronVibrationSeed_def, tetrahedronAffineFieldEquiv_mem_eigenspace_neg_four_iff]
  exact ⟨rfl, isSymm_tetrahedronVertexSeedMatrix i, diag_tetrahedronVertexSeedMatrix i⟩

/-- The four vibration seeds span the eigenspace of the force matrix for `-4`, the vibrational
copy of the standard module. -/
theorem span_range_tetrahedronVibrationSeed :
    Submodule.span ℝ (Set.range tetrahedronVibrationSeed) =
      Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-4) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun u hu ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact tetrahedronVibrationSeed_mem_eigenspace i
  obtain ⟨⟨t, A⟩, rfl⟩ := tetrahedronAffineFieldEquiv.surjective u
  obtain ⟨rfl, hA⟩ := (tetrahedronAffineFieldEquiv_mem_eigenspace_neg_four_iff t A).mp hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((mem_span_range_tetrahedronVertexSeedMatrix_iff A).mpr hA)
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, ?_⟩
  simp only [tetrahedronVibrationSeed_def, ← map_smul, ← map_sum, Prod.smul_mk, smul_zero]
  rw [← prod_mk_sum, Finset.sum_const_zero]

/-! ### The vertex stabilizer -/

/-- A displacement `(t + A qₗ)ₗ` fixed by the transposition of `j` and `k` has `t` and `A` fixed by
the reflection `S = 1 - (qⱼ - qₖ)(qⱼ - qₖ)ᵀ`. -/
private theorem fixed_of_tetrahedronDisplacementRep_swap {j k : Fin 4} {t : Fin 3 → ℝ}
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hu : tetrahedronDisplacementRep (Equiv.swap j k) (tetrahedronAffineFieldEquiv (t, A)) =
      tetrahedronAffineFieldEquiv (t, A)) :
    (1 - vecMulVec (tetrahedronCenteredVertex j - tetrahedronCenteredVertex k)
        (tetrahedronCenteredVertex j - tetrahedronCenteredVertex k)) *ᵥ t = t ∧
      (1 - vecMulVec (tetrahedronCenteredVertex j - tetrahedronCenteredVertex k)
          (tetrahedronCenteredVertex j - tetrahedronCenteredVertex k)) * A *
        (1 - vecMulVec (tetrahedronCenteredVertex j - tetrahedronCenteredVertex k)
          (tetrahedronCenteredVertex j - tetrahedronCenteredVertex k)) = A := by
  rwa [tetrahedronDisplacementRep_affineFieldEquiv, Equiv.swap_inv,
    tetrahedronAffineFieldEquiv.injective.eq_iff, Prod.mk.injEq,
    tetrahedronSymmetryMatrix_swap] at hu

/-- The displacements fixed by the stabilizer `S₃` of the vertex `i` are the combinations of the
breathing mode, the translation seed and the vibration seed of `i`. -/
theorem invariants_tetrahedronDisplacementRep_comp_stabilizer (i : Fin 4) :
    Representation.invariants (tetrahedronDisplacementRep.comp
        (MulAction.stabilizer (Equiv.Perm (Fin 4)) i).subtype) =
      Submodule.span ℝ (Set.range ![tetrahedronBreathingMode, tetrahedronTranslationSeed i,
        tetrahedronVibrationSeed i]) := by
  refine le_antisymm (fun u hu ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨⟨t, A⟩, rfl⟩ := tetrahedronAffineFieldEquiv.surjective u
    have hsw {j k : Fin 4} (hj : j ≠ i) (hk : k ≠ i) :=
      fixed_of_tetrahedronDisplacementRep_swap (hu ⟨Equiv.swap j k, by
        rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
          Equiv.swap_apply_of_ne_of_ne hj.symm hk.symm]⟩)
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![A 0 0, 4 / 3 * (tetrahedronCenteredVertex i ⬝ᵥ t),
      16 * tetrahedronCenteredVertex i 0 * tetrahedronCenteredVertex i 1 * A 0 1], ?_⟩
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, tetrahedronBreathingMode_def,
      tetrahedronTranslationSeed_def, tetrahedronVibrationSeed_def, ← map_smul, ← map_add,
      Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add]
    congr 1
    -- Invariance under the reflections of two transpositions fixing `i` already pins down `t`
    -- and `A`; read off the coordinates in each of the four cases.
    fin_cases i
    on_goal 1 =>
      obtain ⟨h1, h2⟩ := hsw (j := 1) (k := 2) (by decide) (by decide)
      obtain ⟨h3, h4⟩ := hsw (j := 2) (k := 3) (by decide) (by decide)
    on_goal 2 =>
      obtain ⟨h1, h2⟩ := hsw (j := 0) (k := 2) (by decide) (by decide)
      obtain ⟨h3, h4⟩ := hsw (j := 2) (k := 3) (by decide) (by decide)
    on_goal 3 =>
      obtain ⟨h1, h2⟩ := hsw (j := 0) (k := 1) (by decide) (by decide)
      obtain ⟨h3, h4⟩ := hsw (j := 1) (k := 3) (by decide) (by decide)
    on_goal 4 =>
      obtain ⟨h1, h2⟩ := hsw (j := 0) (k := 1) (by decide) (by decide)
      obtain ⟨h3, h4⟩ := hsw (j := 1) (k := 2) (by decide) (by decide)
    all_goals
      clear hsw hu
      simp only [Prod.ext_iff, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ] at h1 h2 h3 h4 ⊢
      norm_num [tetrahedronCenteredVertex_eq, mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.mul_apply, tetrahedronVertexSeedMatrix_apply] at h1 h2 h3 h4 ⊢
      grind
  · rintro _ ⟨n, rfl⟩ ⟨σ, hσ⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hσ
    fin_cases n <;> simp [hσ]

/-- The breathing mode and the translation and vibration seeds of a vertex are linearly
independent. -/
theorem linearIndependent_tetrahedronBreathingMode_translationSeed_vibrationSeed (i : Fin 4) :
    LinearIndependent ℝ ![tetrahedronBreathingMode, tetrahedronTranslationSeed i,
      tetrahedronVibrationSeed i] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, tetrahedronBreathingMode_def,
    tetrahedronTranslationSeed_def, tetrahedronVibrationSeed_def, ← map_smul, ← map_add,
    Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add,
    LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero, funext_iff, ← Matrix.ext_iff] at hg
  have h0 := hg.1 0
  have h00 := hg.2 0 0
  have h01 := hg.2 0 1
  fin_cases i <;>
    norm_num [tetrahedronCenteredVertex_eq, tetrahedronVertexSeedMatrix_apply] at h0 h00 h01 <;>
    intro n <;> fin_cases n <;> simp [h0, h00, h01]

/-- The space of displacements fixed by the stabilizer `S₃` of a vertex is three-dimensional. -/
theorem finrank_invariants_tetrahedronDisplacementRep_comp_stabilizer (i : Fin 4) :
    Module.finrank ℝ (Representation.invariants (tetrahedronDisplacementRep.comp
      (MulAction.stabilizer (Equiv.Perm (Fin 4)) i).subtype)) = 3 := by
  rw [invariants_tetrahedronDisplacementRep_comp_stabilizer, finrank_span_eq_card
    (linearIndependent_tetrahedronBreathingMode_translationSeed_vibrationSeed i), Fintype.card_fin]

end TauCeti
