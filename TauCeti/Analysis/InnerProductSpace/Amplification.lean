/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Amplification of operators to a finite Hilbert sum

For a Hilbert space `H` over `ℝ` or `ℂ` and a finite index type `ι`, an operator `s` on `H`
acts diagonally on the Hilbert sum `PiLp 2 (fun _ : ι => H)` of copies of `H`, as
`s ⊕ ⋯ ⊕ s`. This diagonal amplification is a star algebra homomorphism,
`PiLp.diagStarAlgHom`. Conversely, every operator `T` on the Hilbert sum has matrix entries
`ContinuousLinearMap.piLpEntry T i j : H →L[𝕜] H`, and `T` acts through them
(`ContinuousLinearMap.apply_eq_sum_piLpEntry`). The amplification of `s` has `s` on the diagonal
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

end ContinuousLinearMap
