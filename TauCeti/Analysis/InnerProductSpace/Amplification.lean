/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.Normed.Lp.PiLp

import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Amplification and operator matrices on a finite Hilbert sum

For a Hilbert space `H` over `ℝ` or `ℂ` and a finite index type `ι`, an operator `s` on `H`
acts diagonally on the Hilbert sum `PiLp 2 (fun _ : ι => H)` of copies of `H`, as
`s ⊕ ⋯ ⊕ s`. This diagonal amplification is a star algebra homomorphism,
`PiLp.diagStarAlgHom`. Conversely, every operator `T` on the Hilbert sum has matrix entries
`ContinuousLinearMap.piLpEntry T i j : H →L[𝕜] H`, and `T` acts through them
(`ContinuousLinearMap.apply_eq_sum_piLpEntry`), so it is determined by them
(`ContinuousLinearMap.ext_piLpEntry`), and converges pointwise if and only if every matrix entry
converges pointwise (`ContinuousLinearMap.forall_tendsto_apply_iff_forall_tendsto_piLpEntry_apply`).
Extracting a matrix entry is also a continuous linear map for the strong operator topology
(`PointwiseConvergenceCLM.piLpEntryCLM`). Every family of entries arises from the operator
`ContinuousLinearMap.ofPiLpEntries`. Entries compute products as matrix products
(`ContinuousLinearMap.piLpEntry_mul`) and adjoints as conjugate transposes
(`ContinuousLinearMap.piLpEntry_star`), and are bounded in norm by the operator
(`ContinuousLinearMap.norm_piLpEntry_le`); the adjoint formula reads coordinates off through
`PiLp.inner_single_left`. The amplification of `s` has `s` on the diagonal
and `0` off it (`ContinuousLinearMap.piLpEntry_diagStarAlgHom`).

In the opposite direction, `PiLp.singleEntryCLM i j s` places `s` in the `(i, j)` block and `0`
elsewhere, decomposing every operator on the Hilbert sum into a finite double sum of matrix units
(`PiLp.sum_sum_singleEntryCLM_piLpEntry`). For `i ≠ j`, the self-adjoint off-diagonal block
`singleEntryCLM i j s + singleEntryCLM j i (star s)` has operator norm equal to `‖s‖`
(`PiLp.norm_singleEntryCLM_add_singleEntryCLM_star`).

Amplification turns statements about finitely many vectors of `H` into statements about a single
vector of the Hilbert sum; in particular, `PiLp.diagStarAlgHom_mem_centralizer_centralizer` sends
the double commutant `s''` of any set of operators `s` into the double commutant of its diagonal
copy, which is how the von Neumann density theorem passes from one vector to finitely many.
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
  PiLp.proj 2 (fun _ : ι => H) i ∘L T ∘L PiLp.singleCLM 2 𝕜 (fun _ : ι => H) j

@[simp]
theorem piLpEntry_apply (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) (h : H) : T.piLpEntry i j h = T (PiLp.single 2 j h) i := by
  simp [piLpEntry]

@[simp]
theorem piLpEntry_zero (i j : ι) :
    (0 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j = 0 := by ext; simp

@[simp]
theorem piLpEntry_add (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S + T).piLpEntry i j = S.piLpEntry i j + T.piLpEntry i j := by ext; simp

@[simp]
theorem piLpEntry_neg (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (-T).piLpEntry i j = -T.piLpEntry i j := by ext; simp

@[simp]
theorem piLpEntry_sub (S T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (S - T).piLpEntry i j = S.piLpEntry i j - T.piLpEntry i j := by ext; simp

@[simp]
theorem piLpEntry_smul {R : Type*} [Semiring R] [Module R H] [SMulCommClass 𝕜 R H]
    [ContinuousConstSMul R H] (c : R)
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (c • T).piLpEntry i j = c • T.piLpEntry i j := by ext; simp

@[simp]
theorem piLpEntry_sum {α : Type*} (s : Finset α)
    (T : α → PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (∑ a ∈ s, T a).piLpEntry i j = ∑ a ∈ s, (T a).piLpEntry i j := by ext; simp [sum_apply]

@[simp]
theorem piLpEntry_one (i j : ι) :
    (1 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j =
      if i = j then 1 else 0 := by
  ext h; by_cases hij : i = j <;> simp [hij]

/-- An operator on the Hilbert sum acts through its matrix entries. -/
theorem apply_eq_sum_piLpEntry [Fintype ι]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (w : PiLp 2 (fun _ : ι => H)) (i : ι) : T w i = ∑ j, T.piLpEntry i j (w j) := by
  have hw : w = ∑ j, WithLp.toLp 2 (Pi.single j (w j)) := by ext k; simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum]

/-- Two operators on the Hilbert sum with the same matrix entries are equal. -/
theorem ext_piLpEntry [Finite ι]
    {T U : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    (h : ∀ i j, T.piLpEntry i j = U.piLpEntry i j) : T = U := by
  have := Fintype.ofFinite ι
  ext w i
  simp only [apply_eq_sum_piLpEntry, h]

/-- Pointwise convergence of operators on the finite Hilbert sum is equivalent to pointwise
convergence of every matrix entry. -/
theorem forall_tendsto_apply_iff_forall_tendsto_piLpEntry_apply [Finite ι] {α : Type*}
    {l : Filter α}
    {T : α → PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    {T₀ : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} :
    (∀ w, Tendsto (fun a => T a w) l (𝓝 (T₀ w))) ↔
      ∀ i j h, Tendsto (fun a => (T a).piLpEntry i j h) l (𝓝 (T₀.piLpEntry i j h)) := by
  have := Fintype.ofFinite ι
  refine ⟨fun hw i j h => by
    simpa [piLpEntry_apply, Function.comp_def] using
      ((PiLp.proj (𝕜 := 𝕜) 2 (fun _ : ι => H) i).continuous.tendsto _).comp
        (hw (PiLp.single 2 j h)), fun h w => ?_⟩
  have hcoord (i : ι) : Tendsto (fun a => T a w i) l (𝓝 (T₀ w i)) := by
    simp_rw [apply_eq_sum_piLpEntry]; exact tendsto_finsetSum _ fun j _ => h i j (w j)
  exact ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.continuous.tendsto _).comp
    (tendsto_pi_nhds.2 hcoord)

/-- The matrix entries of a product are the matrix products of the entries. -/
theorem piLpEntry_mul [Fintype ι]
    (T U : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i k : ι) : (T * U).piLpEntry i k = ∑ j, T.piLpEntry i j * U.piLpEntry j k := by
  ext h
  rw [piLpEntry_apply, mul_apply_eq_comp, apply_eq_sum_piLpEntry T, sum_apply]
  simp only [mul_apply_eq_comp, piLpEntry_apply]

/-- Right multiplication by a block-diagonal operator multiplies column `j` on the right by its
`(j, j)` entry. -/
theorem piLpEntry_mul_of_offDiag_zero_right [Finite ι]
    {A R : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    (hoff : ∀ a b, a ≠ b → R.piLpEntry a b = 0) (i j : ι) :
    (A * R).piLpEntry i j = A.piLpEntry i j * R.piLpEntry j j := by
  have := Fintype.ofFinite ι
  rw [piLpEntry_mul, Finset.sum_eq_single j]
  · intro k _ hkj; simp [hoff k j hkj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- Left multiplication by a block-diagonal operator multiplies row `i` on the left by its
`(i, i)` entry. -/
theorem piLpEntry_mul_of_offDiag_zero_left [Finite ι]
    {R A : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    (hoff : ∀ a b, a ≠ b → R.piLpEntry a b = 0) (i j : ι) :
    (R * A).piLpEntry i j = R.piLpEntry i i * A.piLpEntry i j := by
  have := Fintype.ofFinite ι
  rw [piLpEntry_mul, Finset.sum_eq_single i]
  · intro k _ hki; simp [hoff i k hki.symm]
  · intro hi; exact absurd (Finset.mem_univ i) hi

variable [Fintype ι]

/-- The matrix entries of the adjoint are the adjoints of the transposed entries. -/
@[simp]
theorem piLpEntry_star [CompleteSpace H]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (star T).piLpEntry i j = star (T.piLpEntry j i) := by
  refine ContinuousLinearMap.ext fun h => ext_inner_left 𝕜 fun u => ?_
  rw [star_eq_adjoint, star_eq_adjoint, piLpEntry_apply, adjoint_inner_right, piLpEntry_apply,
    ← PiLp.inner_single_left (F := fun _ : ι => H) i u, adjoint_inner_right, ← inner_conj_symm,
    PiLp.inner_single_left (F := fun _ : ι => H) j, inner_conj_symm]

/-- For a self-adjoint operator on the finite Hilbert sum, taking the adjoint of the `(i, j)`
matrix entry gives the `(j, i)` matrix entry. -/
theorem _root_.IsSelfAdjoint.star_piLpEntry [CompleteSpace H]
    {T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)} (hT : IsSelfAdjoint T)
    (i j : ι) : star (T.piLpEntry i j) = T.piLpEntry j i := by
  rw [← piLpEntry_star, hT.star_eq]

/-- Every matrix entry of an operator on the Hilbert sum has norm at most that of the operator. -/
theorem norm_piLpEntry_le (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) : ‖T.piLpEntry i j‖ ≤ ‖T‖ :=
  opNorm_le_bound _ (norm_nonneg T) fun h => by
    rw [piLpEntry_apply]
    exact (PiLp.norm_apply_le (T (PiLp.single 2 j h)) i).trans
      ((T.le_opNorm _).trans_eq (by rw [PiLp.norm_single]))

end EntryAlgebra

variable [Fintype ι]

/-- The operator on the Hilbert sum with prescribed matrix entries `A i j`: it sends `w` to the
vector with components `∑ j, A i j (w j)`. -/
noncomputable def ofPiLpEntries (A : ι → ι → H →L[𝕜] H) :
    PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => ∑ j, A i j ∘L PiLp.proj 2 (fun _ : ι => H) j

@[simp]
theorem ofPiLpEntries_apply (A : ι → ι → H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) (i : ι) :
    ofPiLpEntries A w i = ∑ j, A i j (w j) := by
  simp [ofPiLpEntries, sum_apply]

variable [DecidableEq ι]

@[simp]
theorem piLpEntry_ofPiLpEntries (A : ι → ι → H →L[𝕜] H) (i j : ι) :
    (ofPiLpEntries A).piLpEntry i j = A i j := by
  ext h
  rw [piLpEntry_apply, ofPiLpEntries_apply,
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

@[simp]
theorem ofPiLpEntries_piLpEntry (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    ofPiLpEntries T.piLpEntry = T :=
  ext_piLpEntry fun i j => piLpEntry_ofPiLpEntries _ i j

end ContinuousLinearMap

namespace PointwiseConvergenceCLM

variable [DecidableEq ι]

variable (𝕜 H) in
/-- Extracting the `(i, j)` matrix entry of an operator on `PiLp 2 (fun _ : ι => H)`, as a
continuous linear map for the strong operator (pointwise convergence) topology. -/
noncomputable def piLpEntryCLM (i j : ι) :
    (PiLp 2 (fun _ : ι => H) →Lₚₜ[𝕜] PiLp 2 (fun _ : ι => H)) →L[𝕜] (H →Lₚₜ[𝕜] H) :=
  (postcomp H (PiLp.proj 2 (fun _ : ι => H) i)).comp
    (precomp (PiLp 2 (fun _ : ι => H)) (PiLp.singleCLM 2 𝕜 (fun _ : ι => H) j))

/-- Evaluating `piLpEntryCLM 𝕜 H i j T` at `h` gives the `i`-th coordinate of `T` applied to the
single-entry vector supported at `j`. -/
@[simp]
theorem piLpEntryCLM_apply (i j : ι)
    (T : PiLp 2 (fun _ : ι => H) →Lₚₜ[𝕜] PiLp 2 (fun _ : ι => H)) (h : H) :
    piLpEntryCLM 𝕜 H i j T h = T (PiLp.single 2 j h) i := by
  rw [← PiLp.singleCLM_apply (p := 2) (𝕜 := 𝕜) (β := fun _ : ι => H) j h]
  rfl

/-- On the image of `toPointwiseConvergenceCLM`, `piLpEntryCLM` agrees with
`ContinuousLinearMap.piLpEntry`. -/
theorem piLpEntryCLM_toPointwiseConvergenceCLM [ContinuousSMul 𝕜 (PiLp 2 (fun _ : ι => H))]
    (i j : ι) (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    piLpEntryCLM 𝕜 H i j
        (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) _ _ T) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H (T.piLpEntry i j) := by
  ext h
  rw [piLpEntryCLM_apply]
  exact (ContinuousLinearMap.piLpEntry_apply T i j h).symm

end PointwiseConvergenceCLM

namespace PiLp

section SingleEntry

variable [DecidableEq ι]

/-- The operator on `PiLp 2 (fun _ : ι => H)` with `s` in the `(i, j)` matrix entry and `0`
everywhere else: it sends `w` to `PiLp.single 2 i (s (w j))`. -/
noncomputable def singleEntryCLM (i j : ι) (s : H →L[𝕜] H) :
    PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H) :=
  PiLp.singleCLM 2 𝕜 (fun _ : ι => H) i ∘L s ∘L PiLp.proj 2 (fun _ : ι => H) j

@[simp]
theorem singleEntryCLM_apply (i j : ι) (s : H →L[𝕜] H) (w : PiLp 2 (fun _ : ι => H)) :
    singleEntryCLM i j s w = PiLp.single 2 i (s (w j)) := by
  simp [singleEntryCLM]

@[simp]
theorem _root_.ContinuousLinearMap.piLpEntry_singleEntryCLM (i j k l : ι) (s : H →L[𝕜] H) :
    (singleEntryCLM i j s).piLpEntry k l = if k = i ∧ l = j then s else 0 := by
  ext h; by_cases hki : k = i <;> by_cases hlj : l = j <;> simp [hki, hlj]

@[simp]
theorem singleEntryCLM_zero (i j : ι) : singleEntryCLM i j (0 : H →L[𝕜] H) = 0 := by ext w k; simp

@[simp]
theorem singleEntryCLM_add (i j : ι) (s t : H →L[𝕜] H) :
    singleEntryCLM i j (s + t) = singleEntryCLM i j s + singleEntryCLM i j t := by
  ext w k; simp [PiLp.single_add]

@[simp]
theorem singleEntryCLM_neg (i j : ι) (s : H →L[𝕜] H) :
    singleEntryCLM i j (-s) = -singleEntryCLM i j s := by
  ext w k; by_cases hki : k = i <;> simp [hki]

@[simp]
theorem singleEntryCLM_sub (i j : ι) (s t : H →L[𝕜] H) :
    singleEntryCLM i j (s - t) = singleEntryCLM i j s - singleEntryCLM i j t := by
  ext w k; simp [PiLp.single_sub]

@[simp]
theorem singleEntryCLM_smul {R : Type*} [Semiring R] [Module R H] [SMulCommClass 𝕜 R H]
    [ContinuousConstSMul R H] (i j : ι) (c : R) (s : H →L[𝕜] H) :
    singleEntryCLM i j (c • s) = c • singleEntryCLM i j s := by
  ext w m; by_cases hm : m = i <;> simp [hm]

@[simp]
theorem singleEntryCLM_mul_singleEntryCLM (i j k l : ι) (s t : H →L[𝕜] H) :
    singleEntryCLM i j s * singleEntryCLM k l t =
      if j = k then singleEntryCLM i l (s * t) else 0 := by
  ext w m; by_cases hjk : j = k <;> simp [hjk]

/-- Left multiplication by a single-entry block selects the corresponding row of matrix
entries. -/
@[simp]
theorem _root_.ContinuousLinearMap.piLpEntry_singleEntryCLM_mul (i j k l : ι) (s : H →L[𝕜] H)
    (R : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    (singleEntryCLM i j s * R).piLpEntry k l =
      if k = i then s * R.piLpEntry j l else 0 := by
  ext h; by_cases hki : k = i <;> simp [hki, mul_apply_eq_comp]

/-- Right multiplication by a single-entry block selects the corresponding column of matrix
entries. -/
@[simp]
theorem _root_.ContinuousLinearMap.piLpEntry_mul_singleEntryCLM (i j k l : ι) (s : H →L[𝕜] H)
    (R : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    (R * singleEntryCLM i j s).piLpEntry k l =
      if l = j then R.piLpEntry k i * s else 0 := by
  ext h; by_cases hlj : l = j
  · simp [hlj, mul_apply_eq_comp]
  · simp [hlj, mul_apply_eq_comp, ← PiLp.toLp_single]

variable [Fintype ι]

/-- Every operator on the finite Hilbert sum is the sum of its single-entry blocks. -/
theorem sum_sum_singleEntryCLM_piLpEntry
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) :
    (∑ i, ∑ j, singleEntryCLM i j (T.piLpEntry i j)) = T := by
  refine ContinuousLinearMap.ext_piLpEntry fun k l => by simp [ite_and]

@[simp]
theorem norm_singleEntryCLM (i j : ι) (s : H →L[𝕜] H) :
    ‖singleEntryCLM i j s‖ = ‖s‖ := by
  refine le_antisymm ((singleEntryCLM i j s).opNorm_le_bound (norm_nonneg s) fun w => ?_) ?_
  · rw [singleEntryCLM_apply, PiLp.norm_single]
    exact (s.le_opNorm (w j)).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le w j) (norm_nonneg s))
  · simpa using (singleEntryCLM i j s).norm_piLpEntry_le i j

@[simp]
theorem star_singleEntryCLM [CompleteSpace H] (i j : ι) (s : H →L[𝕜] H) :
    star (singleEntryCLM i j s) = singleEntryCLM j i (star s) := by
  refine ContinuousLinearMap.ext_piLpEntry fun k l => ?_
  rw [ContinuousLinearMap.piLpEntry_star, ContinuousLinearMap.piLpEntry_singleEntryCLM,
    ContinuousLinearMap.piLpEntry_singleEntryCLM]
  by_cases hk : k = j <;> by_cases hl : l = i <;> simp [hk, hl]

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
  refine le_antisymm (D.opNorm_le_bound (norm_nonneg s) fun w => ?_)
    (by simpa [D, hij] using D.norm_piLpEntry_le i j)
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg s) (norm_nonneg w))).1 ?_
  have hDsq : ‖D w‖ ^ 2 = ‖s (w j)‖ ^ 2 + ‖(star s) (w i)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset ι))
      fun k _ hk => by simp_all [D], Finset.sum_pair hij]
    simp [D, hij, hij.symm]
  have hwsq : ‖w j‖ ^ 2 + ‖w i‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_pair (f := fun k => ‖w k‖ ^ 2) hij.symm]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hs1 : ‖s (w j)‖ ^ 2 ≤ (‖s‖ * ‖w j‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (s.le_opNorm _)
  have hs2 : ‖(star s) (w i)‖ ^ 2 ≤ (‖s‖ * ‖w i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      (by simpa only [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map] using
        (star s).le_opNorm (w i))
  rw [hDsq, mul_pow]
  nlinarith

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

/-- The diagonal amplification of an operator in `s''` lies in the double commutant of the
diagonal amplification of `s`. -/
theorem diagStarAlgHom_mem_centralizer_centralizer {s : Set (H →L[𝕜] H)} {x : H →L[𝕜] H}
    (hx : x ∈ s.centralizer.centralizer) :
    diagStarAlgHom 𝕜 H ι x ∈ (diagStarAlgHom 𝕜 H ι '' s).centralizer.centralizer := by
  classical
  intro T hT
  -- the matrix entries of an operator commuting with the diagonal copy of `s` lie in `s'`
  have hentry (i j : ι) : T.piLpEntry i j ∈ s.centralizer := by
    intro a ha
    have haT := hT _ ⟨a, ha, rfl⟩
    ext h
    have h' := congr_arg (fun w => w i) (DFunLike.congr_fun haT (PiLp.single 2 j h))
    simp only [mul_apply_eq_comp, diagStarAlgHom_apply, diagStarAlgHom_apply_single] at h'
    simpa [mul_apply_eq_comp] using h'
  ext w i
  simp only [mul_apply_eq_comp]
  rw [ContinuousLinearMap.apply_eq_sum_piLpEntry, diagStarAlgHom_apply,
    ContinuousLinearMap.apply_eq_sum_piLpEntry, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diagStarAlgHom_apply]
  simpa using DFunLike.congr_fun (hx _ (hentry i j)) (w j)

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

/-- Multiplying on the right by the diagonal amplification of `s` multiplies every matrix entry
on the right by `s`. -/
@[simp]
theorem piLpEntry_mul_diagStarAlgHom
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (s : H →L[𝕜] H) (i j : ι) :
    (T * PiLp.diagStarAlgHom 𝕜 H ι s).piLpEntry i j = T.piLpEntry i j * s := by
  ext h
  simp [mul_apply_eq_comp]

/-- Multiplying on the left by the diagonal amplification of `s` multiplies every matrix entry
on the left by `s`. -/
@[simp]
theorem piLpEntry_diagStarAlgHom_mul
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (s : H →L[𝕜] H) (i j : ι) :
    (PiLp.diagStarAlgHom 𝕜 H ι s * T).piLpEntry i j = s * T.piLpEntry i j := by
  ext h
  simp [mul_apply_eq_comp]

end ContinuousLinearMap
