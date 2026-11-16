/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Amplification of operators to a finite Hilbert sum

For a Hilbert space `H` over `ℝ` or `ℂ` and a finite index type `ι`, an operator `s` on `H`
acts diagonally on the Hilbert sum `PiLp 2 (fun _ : ι => H)` of copies of `H`, as
`s ⊕ ⋯ ⊕ s`. This diagonal amplification is a star algebra homomorphism,
`PiLp.diagStarAlgHom`. Conversely, every operator `T` on the Hilbert sum has matrix entries
`ContinuousLinearMap.piLpEntry T i j : H →L[𝕜] H`, and `T` acts through them
(`ContinuousLinearMap.apply_eq_sum_piLpEntry`). Conversely, any `ι × ι` matrix `M` of bounded
operators on `H` defines an operator `ContinuousLinearMap.ofPiLpEntry M` on the Hilbert sum with
those entries. The amplification of `s` has `s` on the diagonal and `0` off it
(`ContinuousLinearMap.piLpEntry_diagStarAlgHom`).

Matrix entries satisfy the standard matrix-algebra laws for addition, scaling, multiplication,
and adjoints (`ContinuousLinearMap.piLpEntry_mul`, `ContinuousLinearMap.piLpEntry_star`), and
are bounded in norm by the operator norm (`ContinuousLinearMap.norm_piLpEntry_le`). For a unital
star subalgebra `S` of `H →L[𝕜] H`, the operators on `PiLp 2 (fun _ : ι => H)` whose entries lie
in `S` form a unital star subalgebra `StarSubalgebra.piLpMatrix S ι`. Its commutant is the
diagonal amplification of `S'` (`StarSubalgebra.centralizer_piLpMatrix`), and its double
commutant consists of the operators whose entries lie in `S''`
(`StarSubalgebra.mem_centralizer_centralizer_piLpMatrix_iff`).

Amplification turns statements about finitely many vectors of `H` into statements about a single
vector of the Hilbert sum, and turns non-self-adjoint operators into self-adjoint `2 × 2` block
operators.
-/

public section

open scoped InnerProductSpace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace ContinuousLinearMap

variable [DecidableEq ι]

/-- The `(i, j)` matrix entry of an operator on the Hilbert sum of copies of `H`: the component
at `i` of the image of a vector supported at `j`. -/
noncomputable def piLpEntry (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) : H →L[𝕜] H :=
  PiLp.proj 2 (fun _ : ι => H) i ∘L T ∘L
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single 𝕜 (fun _ : ι => H) j

@[simp]
theorem piLpEntry_apply (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) (h : H) : T.piLpEntry i j h = T (PiLp.single 2 j h) i :=
  (rfl)

/-- An operator on the Hilbert sum acts through its matrix entries. -/
theorem apply_eq_sum_piLpEntry [Fintype ι]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (w : PiLp 2 (fun _ : ι => H)) (i : ι) : T w i = ∑ j, T.piLpEntry i j (w j) := by
  have hw : w = ∑ j, WithLp.toLp 2 (Pi.single j (w j)) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum]

end ContinuousLinearMap

namespace PiLp

variable [Fintype ι] [CompleteSpace H]

variable (𝕜 H ι) in
/-- The diagonal amplification `s ↦ s ⊕ ⋯ ⊕ s` of operators on `H` to the Hilbert sum of copies
of `H` indexed by `ι`, as a star algebra homomorphism. -/
noncomputable def diagStarAlgHom :
    (H →L[𝕜] H) →⋆ₐ[𝕜] (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  toFun s := (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.piMap (fun _ => s) ∘L
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).toContinuousLinearMap
  map_one' := by ext; simp
  map_mul' s t := by ext; simp
  map_zero' := by ext; simp
  map_add' s t := by ext; simp
  commutes' r := by ext; simp [Algebra.algebraMap_eq_smul_one]
  map_star' s := by
    simp only [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro w w'
    simp [PiLp.inner_apply, ContinuousLinearMap.adjoint_inner_left]

@[simp]
theorem diagStarAlgHom_apply (s : H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) (i : ι) :
    diagStarAlgHom 𝕜 H ι s w i = s (w i) :=
  (rfl)

@[simp]
theorem diagStarAlgHom_apply_single [DecidableEq ι] (s : H →L[𝕜] H) (j : ι) (h : H) :
    diagStarAlgHom 𝕜 H ι s (PiLp.single 2 j h) = PiLp.single 2 j (s h) := by
  ext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end PiLp

namespace ContinuousLinearMap

variable [Fintype ι] [DecidableEq ι] [CompleteSpace H]

/-- The diagonal amplification of `s` has `s` on the diagonal and `0` off it. -/
theorem piLpEntry_diagStarAlgHom (s : H →L[𝕜] H) (i j : ι) :
    (PiLp.diagStarAlgHom 𝕜 H ι s).piLpEntry i j = if i = j then s else 0 := by
  ext h
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

end ContinuousLinearMap

namespace ContinuousLinearMap

section EntryAlgebra

variable [DecidableEq ι]

@[simp]
theorem piLpEntry_zero (i j : ι) :
    (0 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j = 0 := by
  ext h; simp

@[simp]
theorem piLpEntry_one (i j : ι) :
    (1 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j =
      if i = j then 1 else 0 := by
  ext h
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

@[simp]
theorem piLpEntry_add [ContinuousAdd (PiLp 2 (fun _ : ι => H))]
    (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S + T).piLpEntry i j = S.piLpEntry i j + T.piLpEntry i j := by
  ext h; simp

@[simp]
theorem piLpEntry_neg [IsTopologicalAddGroup (PiLp 2 (fun _ : ι => H))]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (-T).piLpEntry i j = -T.piLpEntry i j := by
  ext h; simp

@[simp]
theorem piLpEntry_sub [IsTopologicalAddGroup (PiLp 2 (fun _ : ι => H))]
    (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S - T).piLpEntry i j = S.piLpEntry i j - T.piLpEntry i j := by
  ext h; simp

@[simp]
theorem piLpEntry_smul {R : Type*} [Monoid R] [DistribMulAction R H]
    [SMulCommClass 𝕜 R H] [ContinuousConstSMul R H]
    [ContinuousConstSMul R (PiLp 2 (fun _ : ι => H))]
    (c : R) (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (c • T).piLpEntry i j = c • T.piLpEntry i j := by
  ext h; simp

end EntryAlgebra

section MatrixEntries

/-- Construct an operator on the finite Hilbert sum `PiLp 2 (fun _ : ι => H)` from its `ι × ι`
matrix of bounded operators on `H`. -/
noncomputable def ofPiLpEntry [Fintype ι] (M : ι → ι → (H →L[𝕜] H)) :
    PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => ∑ j, M i j ∘L PiLp.proj 2 (fun _ : ι => H) j

@[simp]
theorem ofPiLpEntry_apply [Fintype ι] (M : ι → ι → (H →L[𝕜] H))
    (w : PiLp 2 (fun _ : ι => H)) (i : ι) :
    ofPiLpEntry M w i = ∑ j, M i j (w j) := by
  simp [ofPiLpEntry]

@[simp]
theorem piLpEntry_ofPiLpEntry [Fintype ι] [DecidableEq ι]
    (M : ι → ι → (H →L[𝕜] H)) (i j : ι) :
    (ofPiLpEntry M).piLpEntry i j = M i j := by
  ext h
  simp [PiLp.single_apply, apply_ite]

/-- Two operators on the finite Hilbert sum are equal if all their matrix entries agree. -/
theorem ext_piLpEntry [Finite ι] [DecidableEq ι]
    {S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    (h : ∀ i j, S.piLpEntry i j = T.piLpEntry i j) : S = T := by
  have := Fintype.ofFinite ι
  ext w i
  rw [S.apply_eq_sum_piLpEntry, T.apply_eq_sum_piLpEntry]
  simp [h]

@[simp]
theorem ofPiLpEntry_piLpEntry [Fintype ι] [DecidableEq ι]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    ofPiLpEntry T.piLpEntry = T :=
  ext_piLpEntry fun i j => piLpEntry_ofPiLpEntry T.piLpEntry i j

/-- Composition of operators on the finite Hilbert sum acts by matrix multiplication on their
matrix entries. -/
theorem piLpEntry_mul [Fintype ι] [DecidableEq ι]
    (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S * T).piLpEntry i j = ∑ k, S.piLpEntry i k * T.piLpEntry k j := by
  ext h
  simp only [piLpEntry_apply, mul_apply_eq_comp, sum_apply]
  rw [S.apply_eq_sum_piLpEntry]
  rfl

/-- Every matrix entry has operator norm at most the operator norm of the block operator. -/
theorem norm_piLpEntry_le [Fintype ι] [DecidableEq ι]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    ‖T.piLpEntry i j‖ ≤ ‖T‖ := by
  refine opNorm_le_bound _ (norm_nonneg T) fun h => ?_
  calc ‖T.piLpEntry i j h‖
      = ‖T (PiLp.single 2 j h) i‖ := rfl
    _ ≤ ‖T (PiLp.single 2 j h)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖T‖ * ‖PiLp.single 2 j h‖ := T.le_opNorm _
    _ = ‖T‖ * ‖h‖ := by rw [PiLp.norm_single (p := 2) (β := fun _ : ι => H)]

/-- The `2 × 2` off-diagonal block operator `[[0, x], [y, 0]]` on `H ⊕ H` has operator norm
equal to `max ‖x‖ ‖y‖`. -/
theorem norm_ofPiLpEntry_offDiag (x y : H →L[𝕜] H) :
    ‖ofPiLpEntry ![![0, x], ![y, 0]]‖ = max ‖x‖ ‖y‖ := by
  let X := ofPiLpEntry ![![0, x], ![y, 0]]
  have hM : 0 ≤ max ‖x‖ ‖y‖ := le_max_of_le_left (norm_nonneg x)
  refine le_antisymm (X.opNorm_le_bound hM fun w => ?_) ?_
  · have hsq : ‖X w‖ ^ 2 ≤ (max ‖x‖ ‖y‖ * ‖w‖) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => H), mul_pow,
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => H)]
      simp only [Fin.sum_univ_two, X, ofPiLpEntry_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, zero_apply, zero_add, add_zero]
      have h1 : ‖x (w 1)‖ ^ 2 ≤ (max ‖x‖ ‖y‖ * ‖w 1‖) ^ 2 := by
        gcongr
        exact (x.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      have h2 : ‖y (w 0)‖ ^ 2 ≤ (max ‖x‖ ‖y‖ * ‖w 0‖) ^ 2 := by
        gcongr
        exact (y.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
      linarith [mul_pow (max ‖x‖ ‖y‖) ‖w 1‖, mul_pow (max ‖x‖ ‖y‖) ‖w 0‖]
    nlinarith [norm_nonneg (X w), mul_nonneg hM (norm_nonneg w)]
  · refine max_le ?_ ?_
    · simpa [X] using X.norm_piLpEntry_le 0 1
    · simpa [X] using X.norm_piLpEntry_le 1 0

/-- Extracting a fixed matrix entry is continuous. -/
@[fun_prop]
theorem continuous_piLpEntry [DecidableEq ι] [IsUniformAddGroup (PiLp 2 (fun _ : ι => H))]
    [ContinuousConstSMul 𝕜 (PiLp 2 (fun _ : ι => H))] (i j : ι) :
    Continuous fun T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) =>
      T.piLpEntry i j :=
  ((PiLp.proj 2 (fun _ : ι => H) i).postcomp H).continuous.comp
    ((((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single 𝕜 (fun _ : ι => H) j).precomp
        (PiLp 2 (fun _ : ι => H))).continuous)

variable [Fintype ι] [DecidableEq ι] [CompleteSpace H]

/-- Taking the adjoint of an operator on the finite Hilbert sum transposes its matrix entries and
takes the adjoint of each entry. -/
@[simp]
theorem piLpEntry_star (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (star T).piLpEntry i j = star (T.piLpEntry j i) := by
  simp only [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff (T.adjoint.piLpEntry i j)
    (T.piLpEntry j i)).mpr fun x y => ?_
  have h1 : ⟪T.adjoint.piLpEntry i j x, y⟫_𝕜 =
      ⟪T.adjoint (PiLp.single 2 j x), PiLp.single 2 i y⟫_𝕜 := by
    simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]
  have h2 : ⟪x, T.piLpEntry j i y⟫_𝕜 = ⟪PiLp.single 2 j x, T (PiLp.single 2 i y)⟫_𝕜 := by
    rw [PiLp.inner_apply, Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_left]

/-- An operator on the finite Hilbert sum is self-adjoint if and only if its matrix of entries is
Hermitian (`star (T.piLpEntry j i) = T.piLpEntry i j`). -/
theorem isSelfAdjoint_iff_piLpEntry
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    IsSelfAdjoint T ↔ ∀ i j, star (T.piLpEntry j i) = T.piLpEntry i j := by
  refine ⟨fun h i j => ?_, fun h => ext_piLpEntry fun i j => ?_⟩
  · rw [← piLpEntry_star, h.star_eq]
  · rw [piLpEntry_star, h i j]

end MatrixEntries

end ContinuousLinearMap

namespace StarSubalgebra

variable [Fintype ι] [DecidableEq ι] [CompleteSpace H]

/-- The unital star subalgebra of operators on `PiLp 2 (fun _ : ι => H)` whose matrix entries all
lie in `S`. -/
noncomputable def piLpMatrix (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    StarSubalgebra 𝕜 (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  carrier := {T | ∀ i j, T.piLpEntry i j ∈ S}
  mul_mem' {A B} hA hB i j := by
    rw [ContinuousLinearMap.piLpEntry_mul]
    exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [ContinuousLinearMap.piLpEntry_one]
    split_ifs
    · exact one_mem S
    · exact zero_mem S
  add_mem' {A B} hA hB i j := by
    rw [ContinuousLinearMap.piLpEntry_add]
    exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by
    rw [ContinuousLinearMap.piLpEntry_zero]
    exact zero_mem S
  algebraMap_mem' c i j := by
    rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.piLpEntry_smul,
      ContinuousLinearMap.piLpEntry_one]
    split_ifs
    · simpa [Algebra.algebraMap_eq_smul_one] using S.algebraMap_mem c
    · simp [zero_mem S]
  star_mem' {A} hA i j := by
    rw [ContinuousLinearMap.piLpEntry_star]
    exact star_mem (hA j i)

@[simp]
theorem mem_piLpMatrix_iff (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    {T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    T ∈ S.piLpMatrix ι ↔ ∀ i j, T.piLpEntry i j ∈ S :=
  Iff.rfl

/-- If `S` is norm-closed, then its matrix amplification `S.piLpMatrix ι` is norm-closed. -/
instance isClosed_piLpMatrix (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    [hS : IsClosed (S : Set (H →L[𝕜] H))] :
    IsClosed (S.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))) := by
  have h : (S.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))) =
      ⋂ i, ⋂ j, (fun T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) =>
        T.piLpEntry i j) ⁻¹' (S : Set (H →L[𝕜] H)) := by
    ext T
    simp
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    hS.preimage (ContinuousLinearMap.continuous_piLpEntry i j)

/-- The commutant of the matrix algebra `S.piLpMatrix ι` is the diagonal amplification of the
commutant `S'`. -/
theorem centralizer_piLpMatrix (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    (S.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))).centralizer =
      PiLp.diagStarAlgHom 𝕜 H ι '' (S : Set (H →L[𝕜] H)).centralizer := by
  ext R
  constructor
  · intro hR
    by_cases hι : Nonempty ι
    · obtain ⟨i₀⟩ := hι
      refine ⟨R.piLpEntry i₀ i₀, ?_, ?_⟩
      · intro s hs
        have hds : PiLp.diagStarAlgHom 𝕜 H ι s ∈ S.piLpMatrix ι := fun i j => by
          rw [ContinuousLinearMap.piLpEntry_diagStarAlgHom]
          split_ifs
          · exact hs
          · exact zero_mem S
        have hcomm := congrArg (fun T => T.piLpEntry i₀ i₀) (hR _ hds)
        simpa [ContinuousLinearMap.piLpEntry_mul, ContinuousLinearMap.piLpEntry_diagStarAlgHom]
          using hcomm
      · refine ContinuousLinearMap.ext_piLpEntry fun i j => ?_
        rw [ContinuousLinearMap.piLpEntry_diagStarAlgHom]
        -- Matrix units `E_{k l}` have entries `0` and `1`, hence lie in `S.piLpMatrix ι`.
        have hunit (k l : ι) :
            ContinuousLinearMap.ofPiLpEntry (𝕜 := 𝕜) (H := H)
              (fun a b => if a = k ∧ b = l then 1 else 0) ∈ S.piLpMatrix ι := fun a b => by
          rw [ContinuousLinearMap.piLpEntry_ofPiLpEntry]
          split_ifs
          · exact one_mem S
          · exact zero_mem S
        by_cases hij : i = j
        · subst hij
          have hcomm := congrArg (fun T => T.piLpEntry i₀ i) (hR _ (hunit i₀ i))
          simpa [ContinuousLinearMap.piLpEntry_mul,
            ContinuousLinearMap.piLpEntry_ofPiLpEntry] using hcomm.symm
        · have hcomm := congrArg (fun T => T.piLpEntry i j) (hR _ (hunit j j))
          simpa [ContinuousLinearMap.piLpEntry_mul,
            ContinuousLinearMap.piLpEntry_ofPiLpEntry, hij] using hcomm
    · rw [not_nonempty_iff] at hι
      refine ⟨0, fun s _ => by simp, ContinuousLinearMap.ext_piLpEntry fun i => hι.elim i⟩
  · rintro ⟨r, hr, rfl⟩ T hT
    refine ContinuousLinearMap.ext_piLpEntry fun i j => ?_
    simp only [ContinuousLinearMap.piLpEntry_mul, ContinuousLinearMap.piLpEntry_diagStarAlgHom,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    exact hr _ (hT i j)

/-- An operator on `PiLp 2 (fun _ : ι => H)` lies in the double commutant of `S.piLpMatrix ι` if
and only if all its matrix entries lie in the double commutant `S''`. -/
theorem mem_centralizer_centralizer_piLpMatrix_iff (S : StarSubalgebra 𝕜 (H →L[𝕜] H))
    {T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    T ∈ (S.piLpMatrix ι :
        Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))).centralizer.centralizer ↔
      ∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer := by
  rw [S.centralizer_piLpMatrix ι]
  constructor
  · intro hT i j r hr
    have hcomm := congrArg (fun A => A.piLpEntry i j) (hT _ ⟨r, hr, rfl⟩)
    simpa [ContinuousLinearMap.piLpEntry_mul, ContinuousLinearMap.piLpEntry_diagStarAlgHom]
      using hcomm
  · rintro hT _ ⟨r, hr, rfl⟩
    refine ContinuousLinearMap.ext_piLpEntry fun i j => ?_
    simp only [ContinuousLinearMap.piLpEntry_mul, ContinuousLinearMap.piLpEntry_diagStarAlgHom,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    exact hT i j r hr

end StarSubalgebra
