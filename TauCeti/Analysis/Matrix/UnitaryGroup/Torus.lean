/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import TauCeti.Algebra.Group.Subgroup.Centralizer
public import TauCeti.Analysis.Matrix.Normal
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The diagonal torus of the unitary group

The diagonal unitary matrices form a subgroup `TauCeti.unitaryTorus n` of the unitary group
`U(n) = Matrix.unitaryGroup n ℂ`. A diagonal matrix is unitary exactly when its diagonal entries
have modulus one (`Matrix.diagonal_mem_unitaryGroup_iff`), so this subgroup is the image of the
injective homomorphism `TauCeti.unitaryTorusHom n : (n → Circle) →* U(n)`,
`z ↦ diag (z₁, …, zₙ)`: a product of `card n` circles.

The main result is that **every element of `U(n)` is conjugate into this torus**
(`TauCeti.exists_conj_mem_unitaryTorus`). A unitary matrix is normal, so by the spectral theorem
for normal matrices (`Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`) it is diagonalized
by a unitary change of basis, and the resulting diagonal matrix is again unitary. Read through the
parametrization, every unitary matrix is conjugate in `U(n)` to `diag (z₁, …, zₙ)` for some points
`zᵢ` of the circle, namely its eigenvalues (`TauCeti.exists_isConj_unitaryTorusHom`). This is the
`U(n)` case of the theorem that a compact connected Lie group is the union of the conjugates of a
maximal torus; for `SU(2)` the same statement is `TauCeti.SU2.exists_conj_mem_torus`.

The diagonal torus is also **its own centralizer** (`TauCeti.centralizer_unitaryTorus`): a unitary
matrix commuting with the diagonal matrix `diag (1, …, -1, …, 1)`, with `-1` in position `i`, has
vanishing off-diagonal entries in row `i`. Consequently no strictly larger commutative subgroup of
`U(n)` contains it (`TauCeti.eq_unitaryTorus_of_le_of_isMulCommutative`), which is the maximality
of the diagonal torus among the commutative subgroups of `U(n)`.

## Main definitions

* `TauCeti.unitaryTorusHom`: the homomorphism `(n → Circle) →* U(n)` onto the diagonal matrices.
* `TauCeti.unitaryTorus`: the diagonal torus of `U(n)`, its range.

## Main results

* `TauCeti.mem_unitaryTorus_iff`: the diagonal torus consists of the diagonal unitary matrices.
* `TauCeti.exists_conj_mem_unitaryTorus`: every element of `U(n)` is conjugate into the diagonal
  torus.
* `TauCeti.exists_isConj_unitaryTorusHom`: every element of `U(n)` is conjugate to
  `diag (z₁, …, zₙ)` for some points `zᵢ` of the circle.
* `TauCeti.centralizer_unitaryTorus`: the diagonal torus is its own centralizer in `U(n)`.
* `TauCeti.eq_unitaryTorus_of_le_of_isMulCommutative`: the diagonal torus is a maximal commutative
  subgroup of `U(n)`.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §1.
-/

public section

namespace TauCeti

open Matrix

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The homomorphism `(n → Circle) →* U(n)` sending `z` to the diagonal matrix with diagonal
entries `z i`. Its range is the diagonal torus `TauCeti.unitaryTorus n`. -/
noncomputable def unitaryTorusHom : (n → Circle) →* unitaryGroup n ℂ where
  toFun z := ⟨diagonal fun i => (z i : ℂ),
    diagonal_mem_unitaryGroup_iff.mpr fun i => (z i).coe_mem_unitary⟩
  map_one' := Subtype.ext <| by simp
  map_mul' z w := Subtype.ext <| by simp [diagonal_mul_diagonal]

variable {n}

/-- As a matrix, `TauCeti.unitaryTorusHom n z` is the diagonal matrix with diagonal entries
`z i`. -/
@[simp]
theorem coe_unitaryTorusHom (z : n → Circle) :
    (unitaryTorusHom n z : Matrix n n ℂ) = diagonal fun i => (z i : ℂ) :=
  (rfl)

/-- The parametrization `TauCeti.unitaryTorusHom n` of the diagonal torus by `card n` circles is
injective: distinct tuples of circle points give distinct diagonal matrices. -/
theorem unitaryTorusHom_injective : Function.Injective (unitaryTorusHom n) := fun z w h => by
  funext i
  have := congr_fun₂ (congrArg Subtype.val h) i i
  simpa only [coe_unitaryTorusHom, diagonal_apply_eq, Circle.coe_inj] using this

variable (n) in
/-- The **diagonal torus** of the unitary group `U(n)`: the subgroup of diagonal unitary matrices,
the image of `(n → Circle)` under `TauCeti.unitaryTorusHom n`. -/
noncomputable def unitaryTorus : Subgroup (unitaryGroup n ℂ) :=
  (unitaryTorusHom n).range

/-- The diagonal torus of `U(n)` is commutative, being the image of the commutative group
`n → Circle`. -/
instance : IsMulCommutative (unitaryTorus n) :=
  inferInstanceAs (IsMulCommutative (unitaryTorusHom n).range)

/-- An element of `U(n)` lies in the diagonal torus exactly when it is `TauCeti.unitaryTorusHom n z`
for some tuple `z` of circle points. -/
theorem mem_unitaryTorus_iff_exists_unitaryTorusHom {g : unitaryGroup n ℂ} :
    g ∈ unitaryTorus n ↔ ∃ z : n → Circle, unitaryTorusHom n z = g :=
  MonoidHom.mem_range

/-- The diagonal matrix `TauCeti.unitaryTorusHom n z` lies in the diagonal torus. -/
theorem unitaryTorusHom_mem_unitaryTorus (z : n → Circle) :
    unitaryTorusHom n z ∈ unitaryTorus n :=
  ⟨z, rfl⟩

/-- The diagonal torus of `U(n)` consists of exactly the unitary matrices that are diagonal. -/
theorem mem_unitaryTorus_iff {g : unitaryGroup n ℂ} :
    g ∈ unitaryTorus n ↔ (g : Matrix n n ℂ).IsDiag := by
  refine ⟨fun ⟨z, hz⟩ => hz ▸ isDiag_diagonal _, fun hg => ?_⟩
  -- The diagonal entries of a diagonal unitary matrix are unitary, so lie on the circle.
  have hunit := diagonal_mem_unitaryGroup_iff.mp (hg.diagonal_diag.symm ▸ g.2)
  refine ⟨fun i => ⟨(g : Matrix n n ℂ) i i,
    mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary (hunit i))⟩, Subtype.ext ?_⟩
  exact hg.diagonal_diag

/-- **Every element of `U(n)` is conjugate into the diagonal torus.** A unitary matrix is normal,
so a unitary change of basis diagonalizes it. -/
theorem exists_conj_mem_unitaryTorus (g : unitaryGroup n ℂ) :
    ∃ u : unitaryGroup n ℂ, u * g * u⁻¹ ∈ unitaryTorus n := by
  obtain ⟨U, hU, d, hd⟩ := exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (g : Matrix n n ℂ)
  refine ⟨(⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹, mem_unitaryTorus_iff.mpr ?_⟩
  -- Inversion in `U(n)` is `star`, which commutes with the coercion to matrices.
  have hcoe : (((⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹ * g * ((⟨U, hU⟩ : unitaryGroup n ℂ)⁻¹)⁻¹ :
      unitaryGroup n ℂ) : Matrix n n ℂ) = star U * g * U := by
    rw [inv_inv, Submonoid.coe_mul, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
  rw [hcoe, hd]
  exact isDiag_diagonal d

/-- Every element of `U(n)` is conjugate to `diag (z₁, …, zₙ)` for some points `zᵢ` of the circle:
`TauCeti.exists_conj_mem_unitaryTorus` read through the parametrization
`TauCeti.unitaryTorusHom` of the diagonal torus. -/
theorem exists_isConj_unitaryTorusHom (g : unitaryGroup n ℂ) :
    ∃ z : n → Circle, IsConj g (unitaryTorusHom n z) := by
  obtain ⟨u, hu⟩ := exists_conj_mem_unitaryTorus g
  obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hu
  exact ⟨z, isConj_iff.mpr ⟨u, hz.symm⟩⟩

/-- **The diagonal torus of `U(n)` is its own centralizer**: a unitary matrix commuting with every
diagonal unitary matrix is diagonal. -/
theorem centralizer_unitaryTorus :
    Subgroup.centralizer (unitaryTorus n : Set (unitaryGroup n ℂ)) = unitaryTorus n := by
  refine le_antisymm (fun g hg => mem_unitaryTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  -- The diagonal matrix with `-1` in position `i` and `1` elsewhere separates `i` from `j`.
  let z : n → Circle := Pi.mulSingle i (-1)
  have hcomm : Commute (diagonal fun l => (z l : ℂ)) (g : Matrix n n ℂ) := by
    simpa [Commute, SemiconjBy] using congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hg _ (unitaryTorusHom_mem_unitaryTorus z))
  refine apply_eq_zero_of_commute_diagonal hcomm ?_
  norm_num [z, Pi.mulSingle_eq_of_ne hij.symm]

/-- **The diagonal torus is a maximal commutative subgroup of `U(n)`**: a commutative subgroup
containing it is equal to it. -/
theorem eq_unitaryTorus_of_le_of_isMulCommutative (H : Subgroup (unitaryGroup n ℂ))
    [IsMulCommutative H] (hle : unitaryTorus n ≤ H) :
    H = unitaryTorus n :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative centralizer_unitaryTorus hle

end TauCeti
