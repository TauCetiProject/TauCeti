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
(`ContinuousLinearMap.apply_eq_sum_piLpEntry`).

Amplification turns statements about finitely many vectors of `H` into statements about a single
vector of the Hilbert sum; this is how the von Neumann density theorem passes from one vector to
finitely many.
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

end PiLp
