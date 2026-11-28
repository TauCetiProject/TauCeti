/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Corner.Basic
public import TauCeti.LinearAlgebra.ExtendByZero

/-!
# Functions on standard Young tableaux, decomposed over the corners

Every standard Young tableau of a nonempty shape `μ` carries its largest label at exactly one
corner `c` of `μ`, and deleting it leaves a standard Young tableau of shape `erase μ c`
(`TauCeti.StandardYoungTableau.sigmaCornerEquiv`). Transported to the coefficient modules, this
splits the functions on the standard tableaux of shape `μ` into a family of functions on the
standard tableaux of the shapes `erase μ c`, one for each corner `c`
(`TauCeti.StandardYoungTableau.cornerFunEquiv`). The summand at `c` is the extension by zero
along `TauCeti.StandardYoungTableau.extend`
(`TauCeti.StandardYoungTableau.cornerFunEquiv_single`).

This is the splitting of tableau-indexed bases used by branching rules, kept apart from
`TauCeti.Combinatorics.Young.StandardTableau.Corner.Basic` so that the combinatorics there does
not import linear algebra.

## Main definitions

* `TauCeti.StandardYoungTableau.cornerFunEquiv`: the decomposition of the functions on the
  standard tableaux of a nonempty shape over the corners carrying the largest label.

## Main results

* `TauCeti.StandardYoungTableau.cornerFunEquiv_eq_sum`: the decomposition is the sum over the
  corners of the extensions by zero.
-/

public section

namespace TauCeti.StandardYoungTableau

open Function.ExtendByZero

variable {μ : YoungDiagram} {c : ℕ × ℕ} {R : Type*} [Semiring R]

/-- **The corner decomposition** of the functions on the standard tableaux of a nonempty shape
`μ`: a family of functions on the standard tableaux of the shapes `erase μ c`, one for each corner
`c` of `μ`, is assembled into the function whose value at a tableau carrying its largest label at
`c` is the value of the `c`-th function at the tableau left after deleting `c`
(`TauCeti.StandardYoungTableau.cornerFunEquiv_apply_extend`). -/
noncomputable def cornerFunEquiv (hμ0 : 0 < μ.card) :
    (Π c : {c : ℕ × ℕ // c ∈ μ.corners}, StandardYoungTableau (μ.erase c.val) → R) ≃ₗ[R]
      (StandardYoungTableau μ → R) :=
  (LinearEquiv.piCurry R fun _ _ => R).symm.trans
    (LinearEquiv.funCongrLeft R R (sigmaCornerEquiv hμ0)).symm

/-- The component at the corner `c` of the inverse of the corner decomposition reads a function
off at the tableaux obtained by restoring `c` with the largest label. -/
@[simp]
theorem cornerFunEquiv_symm_apply (hμ0 : 0 < μ.card) (f : StandardYoungTableau μ → R)
    (c : {c : ℕ × ℕ // c ∈ μ.corners}) (V : StandardYoungTableau (μ.erase c.val)) :
    (cornerFunEquiv hμ0).symm f c V = f (extend (YoungDiagram.mem_corners.mp c.property) V) := by
  simp [cornerFunEquiv, Sigma.curry]

/-- The value of the corner decomposition at the tableau obtained by restoring the corner `c`
with the largest label. -/
@[simp]
theorem cornerFunEquiv_apply_extend (hμ0 : 0 < μ.card)
    (φ : Π c : {c : ℕ × ℕ // c ∈ μ.corners}, StandardYoungTableau (μ.erase c.val) → R)
    (hc : YoungDiagram.IsCorner μ c) (V : StandardYoungTableau (μ.erase c)) :
    cornerFunEquiv hμ0 φ (extend hc V) = φ ⟨c, YoungDiagram.mem_corners.mpr hc⟩ V := by
  rw [← cornerFunEquiv_symm_apply hμ0 (cornerFunEquiv hμ0 φ)
    ⟨c, YoungDiagram.mem_corners.mpr hc⟩ V, LinearEquiv.symm_apply_apply]

/-- The corner decomposition sends a function supported on the corner `c` to its extension by
zero from the tableaux carrying their largest label at `c`. -/
theorem cornerFunEquiv_single (hμ0 : 0 < μ.card) (hc : YoungDiagram.IsCorner μ c)
    (ψ : StandardYoungTableau (μ.erase c) → R) :
    cornerFunEquiv hμ0 (Pi.single ⟨c, YoungDiagram.mem_corners.mpr hc⟩ ψ) =
      linearMap R R (extend hc) ψ := by
  funext U
  obtain ⟨⟨c', V⟩, rfl⟩ := (sigmaCornerEquiv hμ0).surjective U
  rw [sigmaCornerEquiv_apply, cornerFunEquiv_apply_extend]
  by_cases h : c' = ⟨c, YoungDiagram.mem_corners.mpr hc⟩
  · subst h
    rw [Pi.single_eq_same, linearMap_apply_of_injective R (extend_injective hc)]
  · have hV : extend (YoungDiagram.mem_corners.mp c'.property) V ∉ Set.range (extend hc) :=
      fun hV => h (Subtype.ext ((extend_mem_range_extend_iff hc _ V).mp hV))
    rw [Pi.single_eq_of_ne h, linearMap_apply_of_notMem_range R _ hV, Pi.zero_apply]

/-- The corner decomposition is the sum over the corners of the extensions by zero. -/
theorem cornerFunEquiv_eq_sum (hμ0 : 0 < μ.card)
    (φ : Π c : {c : ℕ × ℕ // c ∈ μ.corners}, StandardYoungTableau (μ.erase c.val) → R) :
    cornerFunEquiv hμ0 φ =
      ∑ c, linearMap R R (extend (YoungDiagram.mem_corners.mp c.property)) (φ c) := by
  conv_lhs => rw [← Finset.univ_sum_single φ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun c _ =>
    cornerFunEquiv_single hμ0 (YoungDiagram.mem_corners.mp c.property) (φ c)

end TauCeti.StandardYoungTableau
