/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Amplification and operator matrices on a finite Hilbert sum

For a Hilbert space `H` over `ℝ` or `ℂ` and a finite index type `ι`, an operator `s` on `H`
acts diagonally on the Hilbert sum `PiLp 2 (fun _ : ι => H)` of copies of `H`, as
`s ⊕ ⋯ ⊕ s`. This diagonal amplification is a star algebra homomorphism,
`PiLp.diagStarAlgHom`. Conversely, every operator `T` on the Hilbert sum has matrix entries
`ContinuousLinearMap.piLpEntry T i j : H →L[𝕜] H`, and `T` acts through them
(`ContinuousLinearMap.apply_eq_sum_piLpEntry`), is determined by them
(`ContinuousLinearMap.ext_piLpEntry`), and converges pointwise if and only if every matrix entry
converges pointwise (`ContinuousLinearMap.tendsto_piLp_apply_iff`).

In the opposite direction, `PiLp.singleEntryCLM i j s` places `s` in the `(i, j)` block and `0`
elsewhere, decomposing every operator on the Hilbert sum into a finite double sum of matrix units
(`PiLp.sum_sum_singleEntryCLM_piLpEntry`). For `i ≠ j`, the self-adjoint off-diagonal block
`singleEntryCLM i j s + singleEntryCLM j i (star s)` has operator norm equal to `‖s‖`
(`PiLp.norm_singleEntryCLM_add_singleEntryCLM_star`).

For a unital star subalgebra `S : StarSubalgebra 𝕜 (H →L[𝕜] H)`, `S.piLpMatrix ι` is the unital
star subalgebra of operators on the Hilbert sum whose matrix entries lie in `S`. Its commutant
consists of block-diagonal operators with constant diagonal entry in `S'`
(`StarSubalgebra.coe_piLpMatrix_centralizer`), so its double commutant consists of operators whose
matrix entries lie in `S''` (`StarSubalgebra.coe_piLpMatrix_centralizer_centralizer`).
-/

public section

open Filter Topology
open scoped InnerProductSpace

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace ContinuousLinearMap

section EntryAlgebra

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

@[simp]
theorem piLpEntry_zero (i j : ι) :
    (0 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j = 0 := by
  ext; simp

@[simp]
theorem piLpEntry_add (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S + T).piLpEntry i j = S.piLpEntry i j + T.piLpEntry i j := by
  ext; simp

@[simp]
theorem piLpEntry_neg (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (-T).piLpEntry i j = -T.piLpEntry i j := by
  ext; simp

@[simp]
theorem piLpEntry_sub (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S - T).piLpEntry i j = S.piLpEntry i j - T.piLpEntry i j := by
  ext; simp

@[simp]
theorem piLpEntry_smul {R : Type*} [Semiring R] [Module R H] [SMulCommClass 𝕜 R H]
    [ContinuousConstSMul R H] (c : R)
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (c • T).piLpEntry i j = c • T.piLpEntry i j := by
  ext; simp

@[simp]
theorem piLpEntry_sum {α : Type*} (s : Finset α)
    (T : α → PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (∑ a ∈ s, T a).piLpEntry i j = ∑ a ∈ s, (T a).piLpEntry i j := by
  ext; simp [sum_apply]

@[simp]
theorem piLpEntry_one (i j : ι) :
    (1 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j =
      if i = j then 1 else 0 := by
  ext h
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- An operator on the Hilbert sum acts through its matrix entries. -/
theorem apply_eq_sum_piLpEntry [Fintype ι]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (w : PiLp 2 (fun _ : ι => H)) (i : ι) : T w i = ∑ j, T.piLpEntry i j (w j) := by
  have hw : w = ∑ j, WithLp.toLp 2 (Pi.single j (w j)) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum]

/-- Operators on the finite Hilbert sum are determined by their matrix entries. -/
theorem ext_piLpEntry [Finite ι]
    {S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    (h : ∀ i j, S.piLpEntry i j = T.piLpEntry i j) : S = T := by
  have := Fintype.ofFinite ι
  ext w i
  rw [S.apply_eq_sum_piLpEntry, T.apply_eq_sum_piLpEntry]
  simp_rw [h]

/-- Pointwise convergence of operators on the finite Hilbert sum is equivalent to pointwise
convergence of every matrix entry. -/
theorem tendsto_piLp_apply_iff [Finite ι] {α : Type*} {l : Filter α}
    {T : α → PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    {T₀ : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    (∀ w, Tendsto (fun a => T a w) l (𝓝 (T₀ w))) ↔
      ∀ i j h, Tendsto (fun a => (T a).piLpEntry i j h) l (𝓝 (T₀.piLpEntry i j h)) := by
  have := Fintype.ofFinite ι
  refine ⟨fun hw i j h =>
    ((PiLp.proj (𝕜 := 𝕜) 2 (fun _ : ι => H) i).continuous.tendsto _).comp
      (hw (PiLp.single 2 j h)), fun h w => ?_⟩
  have hcoord (i : ι) : Tendsto (fun a => T a w i) l (𝓝 (T₀ w i)) := by
    simp_rw [apply_eq_sum_piLpEntry]
    exact tendsto_finsetSum _ fun j _ => h i j (w j)
  exact ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.continuous.tendsto _).comp
    (tendsto_pi_nhds.2 hcoord)

variable [Fintype ι]

@[simp]
theorem piLpEntry_mul
    (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S * T).piLpEntry i j = ∑ k, S.piLpEntry i k * T.piLpEntry k j := by
  ext h
  rw [piLpEntry_apply, mul_apply_eq_comp, S.apply_eq_sum_piLpEntry]
  simp only [sum_apply, mul_apply_eq_comp, piLpEntry_apply]

@[simp]
theorem piLpEntry_star [CompleteSpace H]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (star T).piLpEntry i j = star (T.piLpEntry j i) := by
  simp only [star_eq_adjoint]
  rw [eq_adjoint_iff]
  intro x y
  have lhs : ⟪(T.adjoint).piLpEntry i j x, y⟫_𝕜 =
      ⟪T.adjoint (PiLp.single 2 j x), PiLp.single 2 i y⟫_𝕜 := by
    rw [PiLp.inner_apply, Finset.sum_eq_single i (fun k _ hki => by simp [hki])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  have rhs : ⟪x, T.piLpEntry j i y⟫_𝕜 =
      ⟪PiLp.single 2 j x, T (PiLp.single 2 i y)⟫_𝕜 := by
    rw [PiLp.inner_apply, Finset.sum_eq_single j (fun k _ hkj => by simp [hkj])
      (fun hj => absurd (Finset.mem_univ j) hj)]
    simp
  rw [lhs, rhs, adjoint_inner_left]

/-- Every matrix entry has operator norm bounded by the operator norm on the Hilbert sum. -/
theorem norm_piLpEntry_le
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    ‖T.piLpEntry i j‖ ≤ ‖T‖ := by
  refine (T.piLpEntry i j).opNorm_le_bound (norm_nonneg T) fun h => ?_
  let v : PiLp 2 (fun _ : ι => H) := PiLp.single 2 j h
  calc ‖T.piLpEntry i j h‖ = ‖T v i‖ := rfl
    _ ≤ ‖T v‖ := PiLp.norm_apply_le (T v) i
    _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
    _ = ‖T‖ * ‖h‖ := by rw [PiLp.norm_single]

end EntryAlgebra

end ContinuousLinearMap

namespace PiLp

section SingleEntry

variable [DecidableEq ι]

/-- The operator on `PiLp 2 (fun _ : ι => H)` with `s` in the `(i, j)` matrix entry and `0`
everywhere else: it sends `w` to `PiLp.single 2 i (s (w j))`. -/
noncomputable def singleEntryCLM (i j : ι) (s : H →L[𝕜] H) :
    PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single 𝕜 (fun _ : ι => H) i ∘L s ∘L
      PiLp.proj 2 (fun _ : ι => H) j

@[simp]
theorem singleEntryCLM_apply (i j : ι) (s : H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) :
    singleEntryCLM i j s w = PiLp.single 2 i (s (w j)) :=
  (rfl)

@[simp]
theorem _root_.ContinuousLinearMap.piLpEntry_singleEntryCLM (i j k l : ι) (s : H →L[𝕜] H) :
    (singleEntryCLM i j s).piLpEntry k l = if k = i ∧ l = j then s else 0 := by
  ext h
  by_cases hki : k = i <;> by_cases hlj : l = j <;> simp [hki, hlj]

@[simp]
theorem singleEntryCLM_zero (i j : ι) : singleEntryCLM i j (0 : H →L[𝕜] H) = 0 := by
  ext w k; simp

@[simp]
theorem singleEntryCLM_add (i j : ι) (s t : H →L[𝕜] H) :
    singleEntryCLM i j (s + t) = singleEntryCLM i j s + singleEntryCLM i j t := by
  ext w k; simp [PiLp.single_add]

@[simp]
theorem singleEntryCLM_neg (i j : ι) (s : H →L[𝕜] H) :
    singleEntryCLM i j (-s) = -singleEntryCLM i j s := by
  ext w k
  by_cases hki : k = i <;> simp [hki]

@[simp]
theorem singleEntryCLM_sub (i j : ι) (s t : H →L[𝕜] H) :
    singleEntryCLM i j (s - t) = singleEntryCLM i j s - singleEntryCLM i j t := by
  ext w k; simp [PiLp.single_sub]

@[simp]
theorem singleEntryCLM_smul {R : Type*} [Semiring R] [Module R H] [SMulCommClass 𝕜 R H]
    [ContinuousConstSMul R H] (i j : ι) (c : R) (s : H →L[𝕜] H) :
    singleEntryCLM i j (c • s) = c • singleEntryCLM i j s := by
  ext w m
  by_cases hm : m = i
  · subst hm; simp
  · simp [hm]

@[simp]
theorem singleEntryCLM_mul (i j k l : ι) (s t : H →L[𝕜] H) :
    singleEntryCLM i j s * singleEntryCLM k l t =
      if j = k then singleEntryCLM i l (s * t) else 0 := by
  ext w m
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

variable [Fintype ι]

/-- Every operator on the finite Hilbert sum is the sum of its single-entry blocks. -/
theorem sum_sum_singleEntryCLM_piLpEntry
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    (∑ i, ∑ j, singleEntryCLM i j (T.piLpEntry i j)) = T := by
  refine ContinuousLinearMap.ext_piLpEntry fun k l => ?_
  simp [ite_and]

@[simp]
theorem norm_singleEntryCLM (i j : ι) (s : H →L[𝕜] H) :
    ‖singleEntryCLM i j s‖ = ‖s‖ := by
  refine le_antisymm ?_ ?_
  · refine (singleEntryCLM i j s).opNorm_le_bound (norm_nonneg s) fun w => ?_
    rw [singleEntryCLM_apply, PiLp.norm_single]
    exact (s.le_opNorm (w j)).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le w j) (norm_nonneg s))
  · calc ‖s‖ = ‖(singleEntryCLM i j s).piLpEntry i j‖ := by simp
      _ ≤ ‖singleEntryCLM i j s‖ := (singleEntryCLM i j s).norm_piLpEntry_le i j

@[simp]
theorem star_singleEntryCLM [CompleteSpace H] (i j : ι) (s : H →L[𝕜] H) :
    star (singleEntryCLM i j s) = singleEntryCLM j i (star s) := by
  refine ContinuousLinearMap.ext_piLpEntry fun k l => ?_
  rw [ContinuousLinearMap.piLpEntry_star]
  by_cases hkl : k = j ∧ l = i
  · rcases hkl with ⟨rfl, rfl⟩; simp
  · have hlk : ¬ (l = i ∧ k = j) := fun ⟨h1, h2⟩ => hkl ⟨h2, h1⟩
    simp [hkl, hlk]

/-- An off-diagonal block plus its adjoint is self-adjoint. -/
theorem isSelfAdjoint_singleEntryCLM_add_singleEntryCLM_star [CompleteSpace H]
    (i j : ι) (s : H →L[𝕜] H) :
    IsSelfAdjoint (singleEntryCLM i j s + singleEntryCLM j i (star s)) := by
  rw [← star_singleEntryCLM]
  exact IsSelfAdjoint.add_star_self (singleEntryCLM i j s)

/-- For distinct indices `i ≠ j`, the off-diagonal self-adjoint block placing `s` at `(i, j)` and
`star s` at `(j, i)` has operator norm equal to `‖s‖`. -/
@[simp]
theorem norm_singleEntryCLM_add_singleEntryCLM_star [CompleteSpace H] {i j : ι}
    (hij : i ≠ j) (s : H →L[𝕜] H) :
    ‖singleEntryCLM i j s + singleEntryCLM j i (star s)‖ = ‖s‖ := by
  set D := singleEntryCLM i j s + singleEntryCLM j i (star s)
  refine le_antisymm ?_ ?_
  · refine D.opNorm_le_bound (norm_nonneg s) fun w => ?_
    refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg s) (norm_nonneg w))).1 ?_
    have hDsq : ‖D w‖ ^ 2 = ‖s (w j)‖ ^ 2 + ‖(star s) (w i)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      have hsub : (∑ k, ‖D w k‖ ^ 2) = ∑ k ∈ ({i, j} : Finset ι), ‖D w k‖ ^ 2 := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp [D, hk.1, hk.2]
      rw [hsub, Finset.sum_pair hij]
      simp [D, hij, hij.symm]
    have hwsq : ‖w j‖ ^ 2 + ‖w i‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_pair (f := fun k => ‖w k‖ ^ 2) hij.symm]
      exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    have hs1 : ‖s (w j)‖ ^ 2 ≤ (‖s‖ * ‖w j‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (s.le_opNorm _)
    have hs2 : ‖(star s) (w i)‖ ^ 2 ≤ (‖s‖ * ‖w i‖) ^ 2 := by
      have hst : ‖(star s) (w i)‖ ≤ ‖s‖ * ‖w i‖ := by
        simpa only [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map] using
          (star s).le_opNorm (w i)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hst
    rw [hDsq, mul_pow]
    nlinarith
  · calc ‖s‖ = ‖D.piLpEntry i j‖ := by simp [D, hij]
      _ ≤ ‖D‖ := D.norm_piLpEntry_le i j

end SingleEntry

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
@[simp]
theorem piLpEntry_diagStarAlgHom (s : H →L[𝕜] H) (i j : ι) :
    (PiLp.diagStarAlgHom 𝕜 H ι s).piLpEntry i j = if i = j then s else 0 := by
  ext h
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

end ContinuousLinearMap

namespace StarSubalgebra

section MatrixAmplification

variable [CompleteSpace H]

/-- The unital star subalgebra of operators on `PiLp 2 (fun _ : ι => H)` whose `(i, j)` matrix
entries all belong to `S`. -/
noncomputable def piLpMatrix (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    StarSubalgebra 𝕜 (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  carrier := {T | ∀ i j, T.piLpEntry i j ∈ S}
  mul_mem' {A B} hA hB i j := by
    rw [ContinuousLinearMap.piLpEntry_mul]
    exact sum_mem fun k _ ↦ S.mul_mem (hA i k) (hB k j)
  add_mem' {A B} hA hB i j := by
    rw [ContinuousLinearMap.piLpEntry_add]
    exact S.add_mem (hA i j) (hB i j)
  algebraMap_mem' r i j := by
    rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.piLpEntry_smul,
      ContinuousLinearMap.piLpEntry_one]
    by_cases hij : i = j
    · simp [hij, ← Algebra.algebraMap_eq_smul_one, S.algebraMap_mem r]
    · simp [hij]
  star_mem' {A} hA i j := by
    rw [ContinuousLinearMap.piLpEntry_star]
    exact star_mem (hA j i)

@[simp]
theorem mem_piLpMatrix_iff {S : StarSubalgebra 𝕜 (H →L[𝕜] H)} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    T ∈ S.piLpMatrix ι ↔ ∀ i j, T.piLpEntry i j ∈ S :=
  (Iff.rfl)

@[simp]
theorem coe_piLpMatrix (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    (S.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))) =
      {T | ∀ i j, T.piLpEntry i j ∈ S} :=
  (rfl)

/-- Placing an element of `S` in a single `(i, j)` block gives an element of `S.piLpMatrix ι`. -/
theorem singleEntryCLM_mem_piLpMatrix {S : StarSubalgebra 𝕜 (H →L[𝕜] H)} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) {s : H →L[𝕜] H} (hs : s ∈ S) :
    PiLp.singleEntryCLM i j s ∈ S.piLpMatrix ι := by
  intro k l
  rw [ContinuousLinearMap.piLpEntry_singleEntryCLM]
  split_ifs
  · exact hs
  · exact S.zero_mem

/-- Diagonal amplification maps `S` into `S.piLpMatrix ι`. -/
theorem diagStarAlgHom_mem_piLpMatrix {S : StarSubalgebra 𝕜 (H →L[𝕜] H)} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : H →L[𝕜] H} (hs : s ∈ S) :
    PiLp.diagStarAlgHom 𝕜 H ι s ∈ S.piLpMatrix ι := by
  intro i j
  rw [ContinuousLinearMap.piLpEntry_diagStarAlgHom]
  split_ifs
  · exact hs
  · exact S.zero_mem

/-- The commutant of the operator-matrix algebra `S.piLpMatrix ι` consists of block-diagonal
operators with constant diagonal entry in `S'`. -/
theorem coe_piLpMatrix_centralizer (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*) [Fintype ι]
    [DecidableEq ι] :
    (S.piLpMatrix ι : Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))).centralizer =
      {R | (∀ i j, i ≠ j → R.piLpEntry i j = 0) ∧
        (∀ i j, R.piLpEntry i i = R.piLpEntry j j) ∧
        ∀ i, R.piLpEntry i i ∈ (S : Set (H →L[𝕜] H)).centralizer} := by
  ext R
  simp only [Set.mem_centralizer_iff, SetLike.mem_coe, mem_piLpMatrix_iff, Set.mem_ofPred_eq]
  constructor
  · intro hR
    refine ⟨fun i j hij ↦ ?_, fun i j ↦ ?_, fun i s hs ↦ ?_⟩
    · have hcomm := congrArg (fun T ↦ T.piLpEntry i j)
        (hR (PiLp.singleEntryCLM i i 1) (S.singleEntryCLM_mem_piLpMatrix i i S.one_mem))
      have hlhs : (PiLp.singleEntryCLM i i (1 : H →L[𝕜] H) * R).piLpEntry i j =
          R.piLpEntry i j := by
        rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
        · simp
        · intro k _ hki; simp [hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hrhs : (R * PiLp.singleEntryCLM i i (1 : H →L[𝕜] H)).piLpEntry i j = 0 := by
        rw [ContinuousLinearMap.piLpEntry_mul]
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        simp [hij.symm]
      rw [hlhs, hrhs] at hcomm
      exact hcomm
    · have hcomm := congrArg (fun T ↦ T.piLpEntry i j)
        (hR (PiLp.singleEntryCLM i j 1) (S.singleEntryCLM_mem_piLpMatrix i j S.one_mem))
      have hlhs : (PiLp.singleEntryCLM i j (1 : H →L[𝕜] H) * R).piLpEntry i j =
          R.piLpEntry j j := by
        rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single j]
        · simp
        · intro k _ hkj; simp [hkj]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      have hrhs : (R * PiLp.singleEntryCLM i j (1 : H →L[𝕜] H)).piLpEntry i j =
          R.piLpEntry i i := by
        rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
        · simp
        · intro k _ hki; simp [hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hlhs, hrhs] at hcomm
      exact hcomm.symm
    · have hcomm := congrArg (fun T ↦ T.piLpEntry i i)
        (hR (PiLp.singleEntryCLM i i s) (S.singleEntryCLM_mem_piLpMatrix i i hs))
      have hlhs : (PiLp.singleEntryCLM i i s * R).piLpEntry i i = s * R.piLpEntry i i := by
        rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
        · simp
        · intro k _ hki; simp [hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hrhs : (R * PiLp.singleEntryCLM i i s).piLpEntry i i = R.piLpEntry i i * s := by
        rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
        · simp
        · intro k _ hki; simp [hki]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rwa [hlhs, hrhs] at hcomm
  · rintro ⟨hoff, hdiag, hcomm⟩ A hA
    refine ContinuousLinearMap.ext_piLpEntry fun i j ↦ ?_
    have hlhs : (A * R).piLpEntry i j = A.piLpEntry i j * R.piLpEntry j j := by
      rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single j]
      · intro k _ hkj; simp [hoff k j hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hrhs : (R * A).piLpEntry i j = R.piLpEntry i i * A.piLpEntry i j := by
      rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
      · intro k _ hki; simp [hoff i k hki.symm]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hlhs, hrhs, hdiag i j]
    exact hcomm j (A.piLpEntry i j) (hA i j)

/-- **Double commutant of an operator-matrix algebra.** An operator on `PiLp 2 (fun _ : ι => H)`
lies in the double commutant of `S.piLpMatrix ι` if and only if each of its matrix entries lies in
the double commutant of `S`. -/
theorem coe_piLpMatrix_centralizer_centralizer (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    (S.piLpMatrix ι :
        Set (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))).centralizer.centralizer =
      {T | ∀ i j, T.piLpEntry i j ∈ (S : Set (H →L[𝕜] H)).centralizer.centralizer} := by
  rw [S.coe_piLpMatrix_centralizer ι]
  ext T
  simp only [Set.mem_centralizer_iff, Set.mem_ofPred_eq]
  constructor
  · intro hT i j y hy
    have hdiag_mem :
        (∀ a b : ι, a ≠ b → (PiLp.diagStarAlgHom 𝕜 H ι y).piLpEntry a b = 0) ∧
        (∀ a b : ι, (PiLp.diagStarAlgHom 𝕜 H ι y).piLpEntry a a =
          (PiLp.diagStarAlgHom 𝕜 H ι y).piLpEntry b b) ∧
        ∀ a : ι, ∀ m ∈ S, m * (PiLp.diagStarAlgHom 𝕜 H ι y).piLpEntry a a =
          (PiLp.diagStarAlgHom 𝕜 H ι y).piLpEntry a a * m := by
      refine ⟨fun a b hab ↦ by simp [hab], fun a b ↦ by simp, fun a m hm ↦ ?_⟩
      simpa using hy m hm
    have hcomm := congrArg (fun M ↦ M.piLpEntry i j) (hT (PiLp.diagStarAlgHom 𝕜 H ι y) hdiag_mem)
    have hlhs : (PiLp.diagStarAlgHom 𝕜 H ι y * T).piLpEntry i j = y * T.piLpEntry i j := by
      rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [hki.symm]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hrhs : (T * PiLp.diagStarAlgHom 𝕜 H ι y).piLpEntry i j = T.piLpEntry i j * y := by
      rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single j]
      · simp
      · intro k _ hkj; simp [hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rwa [hlhs, hrhs] at hcomm
  · rintro hT R ⟨hoff, hdiag, hcomm⟩
    refine ContinuousLinearMap.ext_piLpEntry fun i j ↦ ?_
    have hlhs : (R * T).piLpEntry i j = R.piLpEntry i i * T.piLpEntry i j := by
      rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single i]
      · intro k _ hki; simp [hoff i k hki.symm]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hrhs : (T * R).piLpEntry i j = T.piLpEntry i j * R.piLpEntry j j := by
      rw [ContinuousLinearMap.piLpEntry_mul, Finset.sum_eq_single j]
      · intro k _ hkj; simp [hoff k j hkj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hlhs, hrhs, hdiag i j]
    exact hT i j (R.piLpEntry j j) (hcomm j)

end MatrixAmplification

end StarSubalgebra
