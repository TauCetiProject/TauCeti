/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic

import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Amplification of operators to a finite Hilbert sum

For a Hilbert space `H` over `ℝ` or `ℂ` and a finite index type `ι`, an operator `s` on `H`
acts diagonally on the Hilbert sum `PiLp 2 (fun _ : ι => H)` of copies of `H`, as
`s ⊕ ⋯ ⊕ s`. This diagonal amplification is a star algebra homomorphism,
`PiLp.diagStarAlgHom`, defined as the block-diagonal operator `PiLp.piMap 2` with every block
`s` (`PiLp.diagStarAlgHom_eq_piMap`). Conversely, every operator `T` on the Hilbert
sum has matrix entries `ContinuousLinearMap.piLpEntry T i j : H →L[𝕜] H`, and `T` acts through
them (`ContinuousLinearMap.apply_eq_sum_piLpEntry`), so it is determined by them
(`ContinuousLinearMap.ext_piLpEntry`); every family of entries arises from the operator
`ContinuousLinearMap.ofPiLpEntries`. Entries compute products as matrix products
(`ContinuousLinearMap.piLpEntry_mul`) and adjoints as conjugate transposes
(`ContinuousLinearMap.piLpEntry_star`), and are bounded in norm by the operator
(`ContinuousLinearMap.norm_piLpEntry_le`); the adjoint formula reads coordinates off through
`PiLp.inner_single_left`. The amplification of `s` has `s` on the diagonal
and `0` off it (`ContinuousLinearMap.piLpEntry_diagStarAlgHom`).

Amplification turns statements about finitely many vectors of `H` into statements about a single
vector of the Hilbert sum; in particular, `PiLp.diagStarAlgHom_mem_centralizer_centralizer` sends
the double commutant `s''` of any set of operators `s` into the double commutant of its diagonal
copy, which is how the von Neumann density theorem passes from one vector to finitely many.
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

/-- Two operators on the Hilbert sum with the same matrix entries are equal. -/
theorem ext_piLpEntry [Finite ι]
    {T U : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)}
    (h : ∀ i j, T.piLpEntry i j = U.piLpEntry i j) : T = U := by
  have := Fintype.ofFinite ι
  ext w i
  simp only [apply_eq_sum_piLpEntry, h]

@[simp]
theorem piLpEntry_zero (i j : ι) :
    (0 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j = 0 := by
  ext; simp

@[simp]
theorem piLpEntry_one (i j : ι) :
    (1 : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)).piLpEntry i j =
      if i = j then 1 else 0 := by
  ext h
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

variable [Fintype ι]

/-- The matrix entries of a product are the matrix products of the entries. -/
theorem piLpEntry_mul (T U : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i k : ι) : (T * U).piLpEntry i k = ∑ j, T.piLpEntry i j * U.piLpEntry j k := by
  ext h
  rw [piLpEntry_apply, mul_apply_eq_comp, apply_eq_sum_piLpEntry T, sum_apply]
  simp only [mul_apply_eq_comp, piLpEntry_apply]

/-- The matrix entries of the adjoint are the adjoints of the transposed entries. -/
@[simp]
theorem piLpEntry_star [CompleteSpace H]
    (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    (star T).piLpEntry i j = star (T.piLpEntry j i) := by
  refine ContinuousLinearMap.ext fun h => ext_inner_left 𝕜 fun u => ?_
  rw [star_eq_adjoint, star_eq_adjoint, piLpEntry_apply, adjoint_inner_right, piLpEntry_apply,
    ← PiLp.inner_single_left (F := fun _ : ι => H) i u, adjoint_inner_right, ← inner_conj_symm,
    PiLp.inner_single_left (F := fun _ : ι => H) j, inner_conj_symm]

/-- Every matrix entry of an operator on the Hilbert sum has norm at most that of the operator. -/
theorem norm_piLpEntry_le (T : PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H))
    (i j : ι) : ‖T.piLpEntry i j‖ ≤ ‖T‖ :=
  opNorm_le_bound _ (norm_nonneg T) fun h => by
    rw [piLpEntry_apply]
    exact (PiLp.norm_apply_le (T (PiLp.single 2 j h)) i).trans
      ((T.le_opNorm _).trans_eq (by rw [PiLp.norm_single]))

end ContinuousLinearMap

namespace ContinuousLinearMap

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

namespace PiLp

variable [Fintype ι] [CompleteSpace H]

variable (𝕜 H ι) in
/-- The diagonal amplification `s ↦ s ⊕ ⋯ ⊕ s` of operators on `H` to the Hilbert sum of copies
of `H` indexed by `ι`, as a star algebra homomorphism. -/
noncomputable def diagStarAlgHom :
    (H →L[𝕜] H) →⋆ₐ[𝕜] (PiLp 2 (fun _ : ι => H) →L[𝕜] PiLp 2 (fun _ : ι => H)) where
  toFun s := piMap 2 fun _ : ι => s
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
  piMap_apply 2 (fun _ => s) w i

/-- The diagonal amplification of `s` is the block-diagonal operator with every block `s`. -/
theorem diagStarAlgHom_eq_piMap (s : H →L[𝕜] H) :
    diagStarAlgHom 𝕜 H ι s = piMap 2 fun _ : ι => s :=
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
