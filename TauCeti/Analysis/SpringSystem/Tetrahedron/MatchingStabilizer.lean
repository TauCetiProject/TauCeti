/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpringSystem.Tetrahedron.Restriction
public import TauCeti.GroupTheory.Perm.FinFour.Matching

/-!
# The spring tetrahedron restricted to the stabilizer of a perfect matching

The symmetric group `S₄` acts on the displacements `u ∈ ℝ¹²` of the spring tetrahedron, and its
force matrix `H` has the eigenvalues `0`, `-2`, `-4` and `-8`
(`TauCeti.Analysis.SpringSystem.Tetrahedron.Basic`). This file restricts the action to the
stabilizer `D₄` of a perfect matching `m` of the four vertices, the centralizer of the double
transposition `symmetricGroupFourMatching m`; for `M₂ = 02|13` it is the square subgroup
`⟨(0123), (02)⟩` (`TauCeti.centralizer_symmetricGroupFourMatching_two_eq_closure`).

The two opposite edges of `m` have a common perpendicular, a coordinate axis, spanned by the unit
vector `wₘ = q₀ + q_{M(0)}`. The seed of `m` is the displacement `uⱼ = Aₘ qⱼ` with
`Aₘ = 3 wₘ wₘᵀ - 1`, the diagonal matrix with entry `2` on the axis of `m` and `-1` on the other
two; for `M₂` it is `diag(-1, 2, -1)`. A symmetry `σ` moves the seed of `m` to the seed of
`q σ m`, where `q : S₄ →* S₃` is the action on matchings, so:

* the `S₄`-orbit of a seed consists of the three matching seeds; they sum to zero, which is their
  only linear relation, and they span the eigenspace of `H` for `-2`, the two-dimensional
  irreducible summand `E`;
* the stabilizer of the seed of `m` is the stabilizer `D₄` of `m`, so its `D₄`-orbit is a
  singleton.

The `D₄`-fixed displacements are spanned by the breathing mode and the seed of `m`, so they form a
two-dimensional space. Its intersection with `E` is the line of the seed, which is orthogonal to the
breathing mode: projecting a fixed displacement orthogonally away from the breathing mode lands on
that line. As for the vertex stabilizer (`TauCeti.Analysis.SpringSystem.Tetrahedron.Restriction`),
the seeds form a symmetric spanning set of `E`, not a basis.

## Main definitions

* `TauCeti.tetrahedronMatchingAxis`: the unit vector `wₘ = q₀ + q_{M(0)}` along the axis of `m`.
* `TauCeti.tetrahedronMatchingSeedMatrix`: the matrix `Aₘ = 3 wₘ wₘᵀ - 1`.
* `TauCeti.tetrahedronMatchingSeed`: the displacement `uⱼ = Aₘ qⱼ`.

## Main results

* `TauCeti.sum_smul_tetrahedronMatchingSeedMatrix_eq_zero_iff` and
  `TauCeti.mem_span_range_tetrahedronMatchingSeedMatrix_iff`: the three seed matrices satisfy only
  the relation `A₀ + A₁ + A₂ = 0`, and span the trace-zero diagonal matrices.
* `TauCeti.tetrahedronDisplacementRep_matchingSeed`: `σ` sends the seed of `m` to that of `q σ m`.
* `TauCeti.range_tetrahedronSymmetryMatrix_mul_matchingSeedMatrix_mul`: the conjugation orbit of a
  seed matrix is the set of the three seed matrices.
* `TauCeti.ncard_range_tetrahedronDisplacementRep_matchingSeed`: the `S₄`-orbit of a matching seed
  has three elements, and `TauCeti.stabilizer_tetrahedronMatchingSeed`: its stabilizer is the
  stabilizer of the matching, so
  `TauCeti.range_tetrahedronDisplacementRep_centralizer_matchingSeed`: its `D₄`-orbit is a
  singleton.
* `TauCeti.dotProduct_tetrahedronMatchingSeed`: the Gram matrix of the matching seeds.
* `TauCeti.span_range_tetrahedronMatchingSeed`: the matching seeds span the eigenspace of `H` for
  `-2`.
* `TauCeti.invariants_tetrahedronDisplacementRep_comp_centralizer` and
  `TauCeti.finrank_invariants_tetrahedronDisplacementRep_comp_centralizer`: the `D₄`-fixed
  displacements are spanned by the breathing mode and the seed, and form a space of dimension `2`.
* `TauCeti.invariants_tetrahedronDisplacementRep_comp_centralizer_inf_eigenspace`: the fixed line
  in the eigenspace for `-2` is the line of the seed, and
  `TauCeti.sub_smul_tetrahedronBreathingMode_mem_span_matchingSeed`: it is the orthogonal
  projection of the fixed space away from the breathing mode.

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261 (Cornell,
  2001), pp. 3–5.
-/

public section

namespace TauCeti

open Matrix

/-! ### The axes of the matchings -/

/-- The axis `wₘ = q₀ + q_{M(0)}` of the matching `m`: the vector from the midpoint of the edge of
`m` avoiding the vertex `0` to the midpoint of the edge through `0`. It is a unit vector along a
coordinate axis (`tetrahedronMatchingAxis_eq`). -/
noncomputable def tetrahedronMatchingAxis (m : Fin 3) : Fin 3 → ℝ :=
  tetrahedronCenteredVertex 0 + tetrahedronCenteredVertex (symmetricGroupFourMatching m 0)

/-- The defining formula `wₘ = q₀ + q_{M(0)}`. -/
theorem tetrahedronMatchingAxis_def (m : Fin 3) :
    tetrahedronMatchingAxis m =
      tetrahedronCenteredVertex 0 + tetrahedronCenteredVertex (symmetricGroupFourMatching m 0) :=
  (rfl)

/-- The axes of `M₀ = 01|23`, `M₁ = 03|12` and `M₂ = 02|13` are `-e₂`, `-e₀` and `-e₁`. -/
theorem tetrahedronMatchingAxis_eq :
    tetrahedronMatchingAxis = ![![0, 0, -1], ![-1, 0, 0], ![0, -1, 0]] := by
  ext m k
  fin_cases m <;> fin_cases k <;>
    simp [tetrahedronMatchingAxis_def, Equiv.swap_apply_def, tetrahedronCenteredVertex_eq] <;>
    norm_num

/-- Each pair `{x, M(x)}` of the matching `m` gives `qₓ + q_{M(x)} = ± wₘ`, so its projection
`(qₓ + q_{M(x)})(qₓ + q_{M(x)})ᵀ` is the same for every vertex `x`. -/
private theorem vecMulVec_tetrahedronCenteredVertex_add_matching (m : Fin 3) (x : Fin 4) :
    vecMulVec (tetrahedronCenteredVertex x +
        tetrahedronCenteredVertex (symmetricGroupFourMatching m x))
      (tetrahedronCenteredVertex x + tetrahedronCenteredVertex (symmetricGroupFourMatching m x)) =
      vecMulVec (tetrahedronMatchingAxis m) (tetrahedronMatchingAxis m) := by
  have h : tetrahedronCenteredVertex x +
        tetrahedronCenteredVertex (symmetricGroupFourMatching m x) = tetrahedronMatchingAxis m ∨
      tetrahedronCenteredVertex x +
        tetrahedronCenteredVertex (symmetricGroupFourMatching m x) =
          -tetrahedronMatchingAxis m := by
    rw [tetrahedronMatchingAxis_eq, tetrahedronCenteredVertex_eq]
    fin_cases m <;> fin_cases x <;> simp [funext_iff, Fin.forall_fin_succ, Equiv.swap_apply_def] <;>
      norm_num
  rcases h with h | h <;> simp [h]

/-- The symmetry `R_σ` carries the axis of `m` to `q_{σ 0} + q_{M'(σ 0)}`, where `M'` is the double
transposition of the matching `q σ m`. -/
private theorem tetrahedronSymmetryMatrix_mulVec_matchingAxis (σ : Equiv.Perm (Fin 4)) (m : Fin 3) :
    tetrahedronSymmetryMatrix σ *ᵥ tetrahedronMatchingAxis m =
      tetrahedronCenteredVertex (σ 0) + tetrahedronCenteredVertex
        (symmetricGroupFourMatching (symmetricGroupFourMatchingHom σ m) (σ 0)) := by
  rw [tetrahedronMatchingAxis_def, mulVec_add, tetrahedronSymmetryMatrix_mulVec,
    tetrahedronSymmetryMatrix_mulVec,
    symmetricGroupFourMatching_symmetricGroupFourMatchingHom_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-! ### The seed matrices of the matchings -/

/-- The seed matrix `Aₘ = 3 wₘ wₘᵀ - 1` of the matching `m`: the diagonal matrix with entry `2` on
the axis of `m` and `-1` elsewhere (`tetrahedronMatchingSeedMatrix_eq`). Conjugation by `R_σ` moves
it to `A_{q σ m}` (`tetrahedronSymmetryMatrix_mul_matchingSeedMatrix_mul`). -/
noncomputable def tetrahedronMatchingSeedMatrix (m : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (3 : ℝ) • vecMulVec (tetrahedronMatchingAxis m) (tetrahedronMatchingAxis m) - 1

/-- The defining formula `Aₘ = 3 wₘ wₘᵀ - 1`. -/
theorem tetrahedronMatchingSeedMatrix_def (m : Fin 3) :
    tetrahedronMatchingSeedMatrix m =
      (3 : ℝ) • vecMulVec (tetrahedronMatchingAxis m) (tetrahedronMatchingAxis m) - 1 :=
  (rfl)

/-- The seed matrices of `M₀`, `M₁` and `M₂` are `diag(-1, -1, 2)`, `diag(2, -1, -1)` and
`diag(-1, 2, -1)`. -/
theorem tetrahedronMatchingSeedMatrix_eq :
    tetrahedronMatchingSeedMatrix =
      ![diagonal ![-1, -1, 2], diagonal ![2, -1, -1], diagonal ![-1, 2, -1]] := by
  ext m k l
  fin_cases m <;> fin_cases k <;> fin_cases l <;>
    simp [tetrahedronMatchingSeedMatrix_def, tetrahedronMatchingAxis_eq] <;> norm_num

/-- The seed matrices are diagonal. -/
@[simp]
theorem isDiag_tetrahedronMatchingSeedMatrix (m : Fin 3) :
    (tetrahedronMatchingSeedMatrix m).IsDiag := by
  rw [tetrahedronMatchingSeedMatrix_eq]
  fin_cases m <;> exact isDiag_diagonal _

/-- The seed matrices have trace zero. -/
@[simp]
theorem trace_tetrahedronMatchingSeedMatrix (m : Fin 3) :
    (tetrahedronMatchingSeedMatrix m).trace = 0 := by
  rw [tetrahedronMatchingSeedMatrix_eq]
  fin_cases m <;> simp [trace, Fin.sum_univ_three] <;> norm_num

/-- Conjugation by `R_σ` moves the seed matrix of `m` to that of `q σ m`. -/
@[simp]
theorem tetrahedronSymmetryMatrix_mul_matchingSeedMatrix_mul (σ : Equiv.Perm (Fin 4))
    (m : Fin 3) :
    tetrahedronSymmetryMatrix σ * tetrahedronMatchingSeedMatrix m *
        tetrahedronSymmetryMatrix σ⁻¹ =
      tetrahedronMatchingSeedMatrix (symmetricGroupFourMatchingHom σ m) := by
  have h : tetrahedronMatchingAxis m ᵥ* tetrahedronSymmetryMatrix σ⁻¹ =
      tetrahedronSymmetryMatrix σ *ᵥ tetrahedronMatchingAxis m := by
    rw [← mulVec_transpose, transpose_tetrahedronSymmetryMatrix, inv_inv]
  rw [tetrahedronMatchingSeedMatrix_def, tetrahedronMatchingSeedMatrix_def, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, h,
    tetrahedronSymmetryMatrix_mulVec_matchingAxis, vecMulVec_tetrahedronCenteredVertex_add_matching,
    Matrix.mul_one, ← map_mul, mul_inv_cancel, map_one]

/-- The orbit of a seed matrix under conjugation by the symmetries is the set of the three seed
matrices. -/
theorem range_tetrahedronSymmetryMatrix_mul_matchingSeedMatrix_mul (m : Fin 3) :
    Set.range (fun σ ↦ tetrahedronSymmetryMatrix σ * tetrahedronMatchingSeedMatrix m *
        tetrahedronSymmetryMatrix σ⁻¹) = Set.range tetrahedronMatchingSeedMatrix := by
  ext A
  simp only [Set.mem_range, tetrahedronSymmetryMatrix_mul_matchingSeedMatrix_mul]
  refine ⟨fun ⟨σ, h⟩ ↦ ⟨_, h⟩, fun ⟨n, h⟩ ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := symmetricGroupFourMatchingHom_surjective (Equiv.swap m n)
  exact ⟨σ, by rwa [hσ, Equiv.swap_apply_left]⟩

/-- The three seed matrices sum to zero. -/
theorem sum_tetrahedronMatchingSeedMatrix : ∑ m, tetrahedronMatchingSeedMatrix m = 0 := by
  rw [tetrahedronMatchingSeedMatrix_eq]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [Fin.sum_univ_three] <;> norm_num

/-- **The only linear relation among the seed matrices is `A₀ + A₁ + A₂ = 0`**: a combination
vanishes exactly when its coefficients are equal. -/
theorem sum_smul_tetrahedronMatchingSeedMatrix_eq_zero_iff (c : Fin 3 → ℝ) :
    ∑ m, c m • tetrahedronMatchingSeedMatrix m = 0 ↔ ∃ a, ∀ m, c m = a := by
  constructor
  · intro h
    have h' (k : Fin 3) := congrFun (congrFun h k) k
    simp only [tetrahedronMatchingSeedMatrix_eq, Fin.sum_univ_three, Matrix.add_apply,
      Matrix.smul_apply, Matrix.zero_apply] at h'
    refine ⟨c 0, fun m ↦ ?_⟩
    have h0 := h' 0
    have h1 := h' 1
    have h2 := h' 2
    norm_num at h0 h1 h2
    fin_cases m <;> simp <;> linarith
  · rintro ⟨a, ha⟩
    simp only [ha, ← Finset.smul_sum, sum_tetrahedronMatchingSeedMatrix, smul_zero]

/-- The seed matrices are distinct. -/
theorem tetrahedronMatchingSeedMatrix_injective :
    Function.Injective tetrahedronMatchingSeedMatrix := by
  intro m n h
  have h' := congrArg (fun A ↦ (A 0 0, A 1 1)) h
  rw [tetrahedronMatchingSeedMatrix_eq] at h'
  fin_cases m <;> fin_cases n <;> first | rfl | norm_num at h'

/-- The seed matrices span the diagonal matrices of trace zero. -/
theorem mem_span_range_tetrahedronMatchingSeedMatrix_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ Submodule.span ℝ (Set.range tetrahedronMatchingSeedMatrix) ↔ A.IsDiag ∧ A.trace = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun k l hkl ↦ ?_, ?_⟩
    · simp [Matrix.sum_apply, isDiag_tetrahedronMatchingSeedMatrix _ hkl]
    simp [trace_sum]
  · rintro ⟨hA, ht⟩
    refine ⟨![A 2 2 / 3, A 0 0 / 3, A 1 1 / 3], ?_⟩
    rw [trace, Fin.sum_univ_three, diag_apply, diag_apply, diag_apply] at ht
    ext k l
    rcases eq_or_ne k l with rfl | hkl
    · fin_cases k <;>
        simp [tetrahedronMatchingSeedMatrix_eq, Fin.sum_univ_three] <;> linarith
    · rw [hA hkl]
      fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl |
        simp [tetrahedronMatchingSeedMatrix_eq, Fin.sum_univ_three]

/-! ### The matching seeds -/

/-- The seed `uⱼ = Aₘ qⱼ` of the matching `m`, where `Aₘ = 3 wₘ wₘᵀ - 1` is
`tetrahedronMatchingSeedMatrix m`. -/
noncomputable def tetrahedronMatchingSeed (m : Fin 3) : Fin 4 × Fin 3 → ℝ :=
  tetrahedronAffineFieldEquiv (0, tetrahedronMatchingSeedMatrix m)

/-- The seed of `m` is the field `(t, A) = (0, Aₘ)`. -/
theorem tetrahedronMatchingSeed_def (m : Fin 3) :
    tetrahedronMatchingSeed m = tetrahedronAffineFieldEquiv (0, tetrahedronMatchingSeedMatrix m) :=
  (rfl)

/-- The symmetries permute the matching seeds as they permute the matchings:
`σ • Sₘ = S_{q σ m}`. -/
@[simp]
theorem tetrahedronDisplacementRep_matchingSeed (σ : Equiv.Perm (Fin 4)) (m : Fin 3) :
    tetrahedronDisplacementRep σ (tetrahedronMatchingSeed m) =
      tetrahedronMatchingSeed (symmetricGroupFourMatchingHom σ m) := by
  simp [tetrahedronMatchingSeed_def, tetrahedronDisplacementRep_affineFieldEquiv]

/-- The three matching seeds sum to zero. -/
theorem sum_tetrahedronMatchingSeed : ∑ m, tetrahedronMatchingSeed m = 0 := by
  simp only [tetrahedronMatchingSeed_def]
  rw [← map_sum, ← prod_mk_sum, sum_tetrahedronMatchingSeedMatrix, Finset.sum_const_zero,
    Prod.mk_zero_zero, map_zero]

/-- **The only linear relation among the matching seeds is `S₀ + S₁ + S₂ = 0`.** -/
theorem sum_smul_tetrahedronMatchingSeed_eq_zero_iff (c : Fin 3 → ℝ) :
    ∑ m, c m • tetrahedronMatchingSeed m = 0 ↔ ∃ a, ∀ m, c m = a := by
  simp only [tetrahedronMatchingSeed_def, ← map_smul, ← map_sum, Prod.smul_mk, smul_zero,
    ← prod_mk_sum, Finset.sum_const_zero, LinearEquiv.map_eq_zero_iff, Prod.mk_eq_zero, true_and,
    sum_smul_tetrahedronMatchingSeedMatrix_eq_zero_iff]

/-- The three matching seeds are distinct. -/
theorem tetrahedronMatchingSeed_injective : Function.Injective tetrahedronMatchingSeed :=
  tetrahedronAffineFieldEquiv.injective.comp <|
    (Prod.mk_right_injective 0).comp tetrahedronMatchingSeedMatrix_injective

/-- The stabilizer of the seed of `m` in `S₄` is the stabilizer of the matching `m`, the
centralizer of its double transposition. -/
theorem stabilizer_tetrahedronMatchingSeed (m : Fin 3) :
    tetrahedronDisplacementRep.stabilizer (tetrahedronMatchingSeed m) =
      Subgroup.centralizer {symmetricGroupFourMatching m} := by
  ext σ
  rw [Representation.mem_stabilizer, mem_centralizer_symmetricGroupFourMatching_iff,
    tetrahedronDisplacementRep_matchingSeed, tetrahedronMatchingSeed_injective.eq_iff]

/-- The `S₄`-orbit of a matching seed is the set of the three matching seeds. -/
theorem range_tetrahedronDisplacementRep_matchingSeed (m : Fin 3) :
    Set.range (fun σ ↦ tetrahedronDisplacementRep σ (tetrahedronMatchingSeed m)) =
      Set.range tetrahedronMatchingSeed := by
  ext u
  simp only [Set.mem_range, tetrahedronDisplacementRep_matchingSeed]
  refine ⟨fun ⟨σ, h⟩ ↦ ⟨_, h⟩, fun ⟨n, h⟩ ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := symmetricGroupFourMatchingHom_surjective (Equiv.swap m n)
  exact ⟨σ, by rwa [hσ, Equiv.swap_apply_left]⟩

/-- The `S₄`-orbit of a matching seed has exactly three elements. -/
theorem ncard_range_tetrahedronDisplacementRep_matchingSeed (m : Fin 3) :
    (Set.range (fun σ ↦ tetrahedronDisplacementRep σ (tetrahedronMatchingSeed m))).ncard = 3 := by
  rw [range_tetrahedronDisplacementRep_matchingSeed,
    Set.ncard_range_of_injective tetrahedronMatchingSeed_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The orbit of the seed of `m` under the stabilizer `D₄` of `m` is a singleton. -/
theorem range_tetrahedronDisplacementRep_centralizer_matchingSeed (m : Fin 3) :
    Set.range (fun σ : Subgroup.centralizer {symmetricGroupFourMatching m} ↦
      tetrahedronDisplacementRep σ (tetrahedronMatchingSeed m)) = {tetrahedronMatchingSeed m} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨1, by simp⟩, ?_⟩
  rintro _ ⟨⟨σ, hσ⟩, rfl⟩
  rw [mem_centralizer_symmetricGroupFourMatching_iff] at hσ
  simp [hσ]

/-! ### The matching seeds in the eigenspace for `-2` -/

/-- The matching seeds lie in the eigenspace of the force matrix for `-2`. -/
theorem tetrahedronMatchingSeed_mem_eigenspace (m : Fin 3) :
    tetrahedronMatchingSeed m ∈ Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-2) := by
  rw [tetrahedronMatchingSeed_def, tetrahedronAffineFieldEquiv_mem_eigenspace_neg_two_iff]
  exact ⟨rfl, isDiag_tetrahedronMatchingSeedMatrix m, trace_tetrahedronMatchingSeedMatrix m⟩

/-- The three matching seeds span the eigenspace of the force matrix for `-2`, the
two-dimensional irreducible summand. -/
theorem span_range_tetrahedronMatchingSeed :
    Submodule.span ℝ (Set.range tetrahedronMatchingSeed) =
      Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-2) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun u hu ↦ ?_
  · rintro _ ⟨m, rfl⟩
    exact tetrahedronMatchingSeed_mem_eigenspace m
  obtain ⟨⟨t, A⟩, rfl⟩ := tetrahedronAffineFieldEquiv.surjective u
  obtain ⟨rfl, hA⟩ := (tetrahedronAffineFieldEquiv_mem_eigenspace_neg_two_iff t A).mp hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((mem_span_range_tetrahedronMatchingSeedMatrix_iff A).mpr hA)
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, ?_⟩
  simp only [tetrahedronMatchingSeed_def, ← map_smul, ← map_sum, Prod.smul_mk, smul_zero]
  rw [← prod_mk_sum, Finset.sum_const_zero]

/-- The matching seeds are orthogonal to the breathing mode. -/
@[simp]
theorem dotProduct_tetrahedronMatchingSeed_breathingMode (m : Fin 3) :
    tetrahedronMatchingSeed m ⬝ᵥ tetrahedronBreathingMode = 0 := by
  rw [tetrahedronMatchingSeed_def, tetrahedronBreathingMode_def, tetrahedronMatchingSeedMatrix_eq]
  fin_cases m <;>
    simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_three, mulVec,
      tetrahedronCenteredVertex_eq] <;> norm_num

/-- The breathing mode is orthogonal to the matching seeds. -/
@[simp]
theorem dotProduct_tetrahedronBreathingMode_matchingSeed (m : Fin 3) :
    tetrahedronBreathingMode ⬝ᵥ tetrahedronMatchingSeed m = 0 := by
  rw [dotProduct_comm, dotProduct_tetrahedronMatchingSeed_breathingMode]

/-- The Gram matrix of the matching seeds: each has squared norm `6`, and two distinct seeds have
inner product `-3`. -/
theorem dotProduct_tetrahedronMatchingSeed (m n : Fin 3) :
    tetrahedronMatchingSeed m ⬝ᵥ tetrahedronMatchingSeed n = if m = n then 6 else -3 := by
  rw [tetrahedronMatchingSeed_def, tetrahedronMatchingSeed_def, tetrahedronMatchingSeedMatrix_eq]
  fin_cases m <;> fin_cases n <;>
    simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_three, mulVec,
      tetrahedronCenteredVertex_eq] <;> norm_num

/-- Each matching seed has squared norm `6`. -/
@[simp]
theorem dotProduct_tetrahedronMatchingSeed_self (m : Fin 3) :
    tetrahedronMatchingSeed m ⬝ᵥ tetrahedronMatchingSeed m = 6 := by
  simp [dotProduct_tetrahedronMatchingSeed]

/-! ### The stabilizer of a matching -/

/-- The displacements fixed by the stabilizer `D₄` of the matching `m` are the combinations of
the breathing mode and the seed of `m`. -/
theorem invariants_tetrahedronDisplacementRep_comp_centralizer (m : Fin 3) :
    Representation.invariants (tetrahedronDisplacementRep.comp
        (Subgroup.centralizer {symmetricGroupFourMatching m}).subtype) =
      Submodule.span ℝ (Set.range ![tetrahedronBreathingMode, tetrahedronMatchingSeed m]) := by
  refine le_antisymm (fun u hu ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨⟨t, A⟩, rfl⟩ := tetrahedronAffineFieldEquiv.surjective u
    have hfix {σ : Equiv.Perm (Fin 4)} (hσ : symmetricGroupFourMatchingHom σ m = m) :
        tetrahedronSymmetryMatrix σ *ᵥ t = t ∧
          tetrahedronSymmetryMatrix σ * A * tetrahedronSymmetryMatrix σ⁻¹ = A := by
      have h := hu ⟨σ, mem_centralizer_symmetricGroupFourMatching_iff.mpr hσ⟩
      rwa [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mk,
        tetrahedronDisplacementRep_affineFieldEquiv, tetrahedronAffineFieldEquiv.injective.eq_iff,
        Prod.mk.injEq] at h
    have hswap {a b : Fin 4}
        (hab : Equiv.swap a b ∈ Subgroup.centralizer {symmetricGroupFourMatching m}) :=
      hfix (mem_centralizer_symmetricGroupFourMatching_iff.mp hab)
    simp only [Equiv.swap_inv, tetrahedronSymmetryMatrix_swap] at hswap
    have hswap₂ {a b c d : Fin 4} (h : Equiv.swap a b * Equiv.swap c d ∈
        Subgroup.centralizer {symmetricGroupFourMatching m}) :=
      hfix (mem_centralizer_symmetricGroupFourMatching_iff.mp h)
    simp only [map_mul, _root_.mul_inv_rev, Equiv.swap_inv,
      tetrahedronSymmetryMatrix_swap] at hswap₂
    rw [Submodule.mem_span_range_iff_exists_fun]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      tetrahedronBreathingMode_def, tetrahedronMatchingSeed_def, ← map_smul, ← map_add,
      Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero,
      tetrahedronAffineFieldEquiv.injective.eq_iff]
    -- Invariance under the two transpositions along the edges of `m` and under the double
    -- transposition of another matching pins down `t = 0` and `A`, a diagonal matrix with equal
    -- entries off the axis of `m`; read off the coefficients in each of the three cases.
    obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
    on_goal 1 =>
      obtain ⟨h1, h2⟩ := hswap (a := 0) (b := 1) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_zero]; decide)
      obtain ⟨h3, h4⟩ := hswap (a := 2) (b := 3) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_zero]; decide)
      obtain ⟨h5, h6⟩ := hswap₂ (a := 0) (b := 3) (c := 1) (d := 2) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_zero]; decide)
      refine ⟨![(2 * A 0 0 + A 2 2) / 3, (A 2 2 - A 0 0) / 3], ?_⟩
    on_goal 2 =>
      obtain ⟨h1, h2⟩ := hswap (a := 0) (b := 3) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_one]; decide)
      obtain ⟨h3, h4⟩ := hswap (a := 1) (b := 2) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_one]; decide)
      obtain ⟨h5, h6⟩ := hswap₂ (a := 0) (b := 1) (c := 2) (d := 3) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_one]; decide)
      refine ⟨![(2 * A 1 1 + A 0 0) / 3, (A 0 0 - A 1 1) / 3], ?_⟩
    on_goal 3 =>
      obtain ⟨h1, h2⟩ := hswap (a := 0) (b := 2) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_two]; decide)
      obtain ⟨h3, h4⟩ := hswap (a := 1) (b := 3) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_two]; decide)
      obtain ⟨h5, h6⟩ := hswap₂ (a := 0) (b := 1) (c := 2) (d := 3) (by
        rw [Subgroup.mem_centralizer_singleton_iff, symmetricGroupFourMatching_two]; decide)
      refine ⟨![(2 * A 0 0 + A 1 1) / 3, (A 1 1 - A 0 0) / 3], ?_⟩
    all_goals
      clear hswap hswap₂ hfix hu
      simp only [Prod.ext_iff, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ] at *
      norm_num [tetrahedronCenteredVertex_eq, mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.mul_apply, tetrahedronMatchingSeedMatrix_eq, one_apply] at h1 h2 h3 h4 h5 h6 ⊢
      grind
  · rintro _ ⟨n, rfl⟩ ⟨σ, hσ⟩
    rw [mem_centralizer_symmetricGroupFourMatching_iff] at hσ
    fin_cases n <;> simp [hσ]

/-- The breathing mode and the seed of a matching are linearly independent. -/
theorem linearIndependent_tetrahedronBreathingMode_matchingSeed (m : Fin 3) :
    LinearIndependent ℝ ![tetrahedronBreathingMode, tetrahedronMatchingSeed m] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  simp only [tetrahedronBreathingMode_def, tetrahedronMatchingSeed_def, ← map_smul, ← map_add,
    Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, LinearEquiv.map_eq_zero_iff,
    Prod.mk_eq_zero, true_and] at hab
  have h0 := congrFun (congrFun hab 0) 0
  have h1 := congrFun (congrFun hab 1) 1
  have h2 := congrFun (congrFun hab 2) 2
  rw [tetrahedronMatchingSeedMatrix_eq] at h0 h1 h2
  fin_cases m <;> norm_num at h0 h1 h2 <;> constructor <;> linarith

/-- The space of displacements fixed by the stabilizer `D₄` of a matching is two-dimensional. -/
theorem finrank_invariants_tetrahedronDisplacementRep_comp_centralizer (m : Fin 3) :
    Module.finrank ℝ (Representation.invariants (tetrahedronDisplacementRep.comp
      (Subgroup.centralizer {symmetricGroupFourMatching m}).subtype)) = 2 := by
  rw [invariants_tetrahedronDisplacementRep_comp_centralizer, finrank_span_eq_card
    (linearIndependent_tetrahedronBreathingMode_matchingSeed m), Fintype.card_fin]

/-- **The `D₄`-fixed line in the eigenspace for `-2`** is the line of the seed of the matching. -/
theorem invariants_tetrahedronDisplacementRep_comp_centralizer_inf_eigenspace (m : Fin 3) :
    Representation.invariants (tetrahedronDisplacementRep.comp
        (Subgroup.centralizer {symmetricGroupFourMatching m}).subtype) ⊓
        Module.End.eigenspace tetrahedronSpringMatrix.toLin' (-2) =
      ℝ ∙ tetrahedronMatchingSeed m := by
  rw [invariants_tetrahedronDisplacementRep_comp_centralizer]
  refine le_antisymm (fun u hu ↦ ?_) ?_
  · obtain ⟨hu, hE⟩ := Submodule.mem_inf.mp hu
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hE ⊢
    have hc : c 0 = 0 := by
      simp only [tetrahedronBreathingMode_def, tetrahedronMatchingSeed_def, ← map_smul, ← map_add,
        Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero,
        tetrahedronAffineFieldEquiv_mem_eigenspace_neg_two_iff] at hE
      have h := hE.2.2
      simpa [trace_add, trace_smul] using h
    rw [hc, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨Submodule.subset_span ⟨1, rfl⟩, tetrahedronMatchingSeed_mem_eigenspace m⟩

/-- **Orthogonal projection separates the `D₄`-fixed line of `E` from the breathing mode**:
removing from a displacement fixed by the stabilizer of `m` its orthogonal component along the
breathing mode leaves a multiple of the seed of `m`. -/
theorem sub_smul_tetrahedronBreathingMode_mem_span_matchingSeed (m : Fin 3)
    {u : Fin 4 × Fin 3 → ℝ} (hu : u ∈ Representation.invariants (tetrahedronDisplacementRep.comp
      (Subgroup.centralizer {symmetricGroupFourMatching m}).subtype)) :
    u - (3⁻¹ * (u ⬝ᵥ tetrahedronBreathingMode)) • tetrahedronBreathingMode ∈
      ℝ ∙ tetrahedronMatchingSeed m := by
  rw [invariants_tetrahedronDisplacementRep_comp_centralizer] at hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_dotProduct,
    smul_dotProduct, dotProduct_tetrahedronBreathingMode_self,
    dotProduct_tetrahedronMatchingSeed_breathingMode, smul_eq_mul, mul_zero, add_zero]
  rw [show 3⁻¹ * (c 0 * 3) = c 0 by ring, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end TauCeti
