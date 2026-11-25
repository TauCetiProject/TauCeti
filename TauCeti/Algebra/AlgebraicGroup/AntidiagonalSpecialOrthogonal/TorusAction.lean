/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.RootSubgroup
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight

/-!
# The diagonal torus of `SO_l^J` acts on its root subgroups through the roots

Let `SO_l^J` be the special orthogonal group of the antidiagonal form `J_l`
(`TauCeti.AntidiagonalSpecialOrthogonal`), `T` its diagonal torus
`diag(t₁, …, tₙ, (1), tₙ⁻¹, …, t₁⁻¹)` with `n = l / 2`, and `x_ij(a) = 1 + a(E_ij - E_{j' i'})`
one of its root subgroups, where `i' = l - 1 - i`. Write `w_k` for the weight of the `k`-th
diagonal entry of `T` (`TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusWeight`), so that
`w_{k'} = -w_k`. Conjugating by a diagonal matrix `d` with `d_{k'} = d_k⁻¹` scales `E_ij` by
`d_i d_j⁻¹` and `E_{j' i'}` by `d_{j'} d_{i'}⁻¹ = d_j⁻¹ d_i`, so

`t x_ij(a) t⁻¹ = x_ij(α(t) a)`,  `α = w_i - w_j`.

The character `α` is the root of the root subgroup: `ε_i - ε_j` for `i, j < n`, `ε_i + ε_{j'}`
for `i < n ≤ j`, and `-(ε_{i'} + ε_j)` for `j < n ≤ i`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.diagonal_mul_rootMatrix_mul_diagonal_inv`: the matrix
  identity.
* `TauCeti.AntidiagonalSpecialOrthogonal.RootSubgroupIndex.root`: the root `w_i - w_j`.
* `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv`: the
  action on algebra-valued points, with the root evaluated as a character of the split torus.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3, for the root subgroups of the
  orthogonal groups in the antidiagonal model.
* The statement follows
  `TauCeti.Symplectic.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv_eq_root`.
-/

public section

open Matrix WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u v w

/-! ### The matrix identity -/

section Matrices

variable {A : Type w} [CommRing A] {l : ℕ} (r : RootSubgroupIndex l)

/-- **Conjugating a root matrix by a diagonal matrix of the torus shape.** If `d_{k'} = d_k⁻¹`
for every `k`, then `d x_ij(a) d⁻¹ = x_ij(d_i d_j⁻¹ a)`. -/
theorem diagonal_mul_rootMatrix_mul_diagonal_inv (d : Fin l → Aˣ)
    (hd : ∀ k, d (Fin.rev k) = (d k)⁻¹) (a : A) :
    diagonal (fun k ↦ (d k : A)) * rootMatrix r a * diagonal (fun k ↦ (((d k)⁻¹ : Aˣ) : A)) =
      rootMatrix r ((d r.i : A) * (((d r.j)⁻¹ : Aˣ) : A) * a) := by
  ext p q
  have hi := hd r.i
  have hj := hd r.j
  simp only [diagonal_mul, mul_diagonal, rootMatrix_def, rootNilpotent_def]
  by_cases hpq : p = q
  · subst hpq
    have h1 : ¬ (r.i = p ∧ r.j = p) := fun h => r.ne (h.1.trans h.2.symm)
    have h2 : ¬ (Fin.rev r.j = p ∧ Fin.rev r.i = p) := fun h =>
      r.ne (Fin.rev_injective (h.2.trans h.1.symm))
    simp [h1, h2]
  · by_cases h1 : r.i = p ∧ r.j = q
    · obtain ⟨rfl, rfl⟩ := h1
      have h2 : ¬ (Fin.rev r.j = r.i ∧ Fin.rev r.i = r.j) := fun h =>
        r.j_ne_rev_i (by rw [← h.1, Fin.rev_rev])
      simp [hpq, h2]
      ring
    · by_cases h2 : Fin.rev r.j = p ∧ Fin.rev r.i = q
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hpq, hi, hj]
        ring
      · simp [hpq, h1, h2]

/-- The invertible-matrix form of `diagonal_mul_rootMatrix_mul_diagonal_inv`. -/
theorem diagGL_mul_rootHom_mul_inv (d : Fin l → Aˣ) (hd : ∀ k, d (Fin.rev k) = (d k)⁻¹)
    (a : Multiplicative A) :
    diagGL d * rootHom r A a * (diagGL d)⁻¹ =
      rootHom r A
        (Multiplicative.ofAdd ((d r.i : A) * (((d r.j)⁻¹ : Aˣ) : A) * a.toAdd)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, diagGL_coe, diagGL_coe, coe_rootHom, coe_rootHom,
    toAdd_ofAdd]
  exact diagonal_mul_rootMatrix_mul_diagonal_inv r d hd a.toAdd

end Matrices

/-! ### The roots -/

variable {l : ℕ}

/-- **The root of a root subgroup** of `SO_l^J`: the difference `w_i - w_j` of the weights of the
diagonal torus at the two indices of `x_ij`. -/
def RootSubgroupIndex.root (r : RootSubgroupIndex l) : ULift.{u} (Fin (l / 2)) → ℤ :=
  diagonalTorusWeight.{u} l r.i - diagonalTorusWeight.{u} l r.j

/-- The root of `x_ij` is `w_i - w_j`. -/
theorem RootSubgroupIndex.root_def (r : RootSubgroupIndex l) :
    r.root.{u} = diagonalTorusWeight.{u} l r.i - diagonalTorusWeight.{u} l r.j :=
  (rfl)

/-! ### The action on points -/

section Points

variable {R : Type u} [CommRing R] (r : RootSubgroupIndex l) {A : Type v} [CommRing A]
  [Algebra R A]

/-- **The diagonal torus of `SO_l^J` acts on each root subgroup through its root.** Conjugation by
a point `t` of the diagonal torus scales the parameter of `x_ij` by the value at `t` of the
character `w_i - w_j`. -/
theorem diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints R l A t * rootSubgroupPoints r c * (diagonalTorusPoints R l A t)⁻¹ =
      rootSubgroupPoints r
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            (((DiagonalizableGroup.charOfPoint t.ofConv
                (SplitTorus.weightCharacter r.root.{u}) : Aˣ) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))) := by
  apply (pointsMulEquiv R l (A := A)).injective
  rw [map_mul, map_mul, map_inv, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, MulEquiv.apply_symm_apply,
    SplitTorus.charOfPoint_weightCharacter, RootSubgroupIndex.root_def, torusCharacter_sub,
    div_eq_mul_inv, Units.val_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, pointsMulEquiv_diagonalTorusPoints,
    coe_rootPoints, coe_rootPoints]
  exact diagGL_mul_rootHom_mul_inv r _ (fun k => by
    rw [diagonalTorusWeight_rev, torusCharacter_neg]) _

end Points

end TauCeti.AntidiagonalSpecialOrthogonal
