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
for `i < n ≤ j`, `-(ε_{i'} + ε_j)` for `j < n ≤ i`, and `ε_{j'} - ε_{i'}` for `n ≤ i, j`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.diagonal_mul_rootMatrix_mul_diagonal_inv`: the matrix
  identity.
* `TauCeti.AntidiagonalSpecialOrthogonal.RootSubgroupIndex.root`: the root `w_i - w_j`.
* `TauCeti.AntidiagonalSpecialOrthogonal.charOfPoint_weightCharacter_root`: the root evaluated at
  a point of the split torus.
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

/-- **Conjugating a root subgroup element by an invertible diagonal matrix of the torus
shape.** If `d_{k'} = d_k⁻¹` for every `k`, then `d x_ij(a) d⁻¹ = x_ij(d_i d_j⁻¹ a)`: conjugation
distributes over the two commuting transvections making up `x_ij(a)`, and rescales each of them. -/
theorem diagGL_mul_rootHom_mul_inv (d : Fin l → Aˣ) (hd : ∀ k, d (Fin.rev k) = (d k)⁻¹)
    (a : Multiplicative A) :
    diagGL d * rootHom r A a * (diagGL d)⁻¹ =
      rootHom r A
        (Multiplicative.ofAdd ((d r.i : A) * (((d r.j)⁻¹ : Aˣ) : A) * a.toAdd)) := by
  have hrev : Fin.rev r.j ≠ Fin.rev r.i := fun h ↦ r.ne (Fin.rev_injective h).symm
  have hx (b : Multiplicative A) :
      rootHom r A b = transvectionUnit r.ne b.toAdd * transvectionUnit hrev (-b.toAdd) :=
    Units.ext <| by simp [rootMatrix_eq_transvection_mul_transvection]
  rw [hx, hx, ← conj_mul, diagGL_mul_transvectionUnit_mul_inv,
    diagGL_mul_transvectionUnit_mul_inv, hd r.i, hd r.j, inv_inv]
  congr 2 <;> simp only [toAdd_ofAdd] <;> ring

/-- The matrix form of `diagGL_mul_rootHom_mul_inv`. -/
theorem diagonal_mul_rootMatrix_mul_diagonal_inv (d : Fin l → Aˣ)
    (hd : ∀ k, d (Fin.rev k) = (d k)⁻¹) (a : A) :
    diagonal (fun k ↦ (d k : A)) * rootMatrix r a * diagonal (fun k ↦ (((d k)⁻¹ : Aˣ) : A)) =
      rootMatrix r ((d r.i : A) * (((d r.j)⁻¹ : Aˣ) : A) * a) := by
  simpa [← map_inv] using congrArg Units.val (diagGL_mul_rootHom_mul_inv r d hd (.ofAdd a))

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

/-- **The root of `x_ij` as a character of the diagonal torus.** Evaluated at a point `t` of the
split torus, the root `w_i - w_j` is the quotient of the values of the weights `w_i` and `w_j`. -/
theorem charOfPoint_weightCharacter_root
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint t.ofConv (SplitTorus.weightCharacter r.root.{u}) =
      torusCharacter (SplitTorus.pointsMulEquiv t) (diagonalTorusWeight l r.i) /
        torusCharacter (SplitTorus.pointsMulEquiv t) (diagonalTorusWeight l r.j) := by
  rw [SplitTorus.charOfPoint_weightCharacter, RootSubgroupIndex.root_def, torusCharacter_sub]

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
  have hd (k : Fin l) :
      torusCharacter (SplitTorus.pointsMulEquiv t) (diagonalTorusWeight l (Fin.rev k)) =
        (torusCharacter (SplitTorus.pointsMulEquiv t) (diagonalTorusWeight l k))⁻¹ := by
    rw [diagonalTorusWeight_rev, torusCharacter_neg]
  apply (pointsMulEquiv R l (A := A)).injective
  simp only [map_mul, map_inv]
  rw [pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints,
    charOfPoint_weightCharacter_root]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rootPoints]
  -- `simp` does not fire this point-map lemma here, while `rw` matches it up to instances.
  rw [pointsMulEquiv_diagonalTorusPoints, diagGL_mul_rootHom_mul_inv r _ hd]
  simp [div_eq_mul_inv]

end Points

end TauCeti.AntidiagonalSpecialOrthogonal
