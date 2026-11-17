/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
-- Private: orthonormal coordinates and unitary frames are used only in proofs.
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# Compatible complex structures of self-dual two-vectors in dimension four

Let `V` be an oriented four-dimensional real inner product space and `F ∈ ⋀² V` a two-vector,
representing the two-form `ω(u, w) = ⟪F, u ∧ w⟫`. An almost complex structure `J` is
*compatible* with `ω` and the inner product when `⟪u, v⟫ = ω(u, J v)`. Such a `J` is unique,
namely the contraction `A = TauCeti.twoVectorContraction F` with `⟪A u, w⟫ = ω(u, w)`, and `F` is
then its Kähler two-vector (`TauCeti.AlmostComplexStructure.toLinearMap_eq_twoVectorContraction`,
`TauCeti.AlmostComplexStructure.kahlerForm_eq_of_inner_eq`). This file proves the converse: a
compatible `J` exists exactly when `F` is self-dual and `‖F‖ = √2`, for the orientation in which
`ω ∧ ω` is positive.

The computation is the one in an oriented orthonormal frame `e`. Self-duality makes the
coordinates of `F` along `e₂ ∧ e₃`, `e₁ ∧ e₃` and `e₁ ∧ e₂` equal to `a`, `-b` and `c`, those along
`e₀ ∧ e₁`, `e₀ ∧ e₂` and `e₀ ∧ e₃` (`Orientation.inner_ιMulti_two_of_hodgeStar_eq_self`), so that
`‖F‖² = 2 (a² + b² + c²)` (`Orientation.norm_sq_of_hodgeStar_eq_self`). The matrix of `A` in the
frame is the skew-symmetric matrix

`!![0, -a, -b, -c; a, 0, -c, b; b, c, 0, -a; c, -b, a, 0]`

(`TauCeti.repr_twoVectorContraction_of_hodgeStar_eq_self`), the transpose of the Gram matrix
`(ω(eᵢ, eⱼ))` of `ω`, and its square is `-(a² + b² + c²)` times the identity. Hence `A` is
conformal with factor `‖F‖² / 2`
(`TauCeti.inner_twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self`) and
`A² = -(‖F‖² / 2)` (`TauCeti.twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self`).
When `‖F‖² = 2`, `A` is
an almost complex structure (`TauCeti.AlmostComplexStructure.ofSelfDual`), compatible with `ω`, and
its complex orientation is the given one.

Conversely, if `J` is compatible with `ω`, then `F` is the Kähler two-vector of the orthogonal
complex structure `J`, which has norm `√2` and is self-dual for the complex orientation of `J`. If
`ω ∧ ω` is positive, that is `⟪⋆F, F⟫ > 0`, the complex orientation is the given one, since `F`
would otherwise be anti-self-dual and `⟪⋆F, F⟫ = -‖F‖²`. So, for the symplectic orientation of
`ω`, a compatible complex structure exists exactly when `⋆F = F` and `‖F‖² = 2`
(`TauCeti.AlmostComplexStructure.exists_inner_eq_inner_ιMulti_apply_iff`), and it is then unique
(`TauCeti.AlmostComplexStructure.existsUnique_inner_eq_inner_ιMulti_apply`). This is the pointwise
statement behind the almost complex structures determined by a metric and a self-dual symplectic
form on a four-manifold.

## Main definitions

* `TauCeti.AlmostComplexStructure.ofSelfDual`: the almost complex structure `u ↦ u ⌟ F` of a
  self-dual two-vector `F` with `‖F‖² = 2`.

## Main results

* `TauCeti.repr_twoVectorContraction_of_hodgeStar_eq_self`: the matrix of `u ↦ u ⌟ F` in an
  oriented orthonormal frame, for self-dual `F`.
* `TauCeti.inner_twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self`: for self-dual `F`,
  `⟪u ⌟ F, w ⌟ F⟫ = (‖F‖² / 2) ⟪u, w⟫`.
* `TauCeti.twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self`: for self-dual `F`,
  `(u ⌟ F) ⌟ F = -(‖F‖² / 2) u`.
* `TauCeti.AlmostComplexStructure.inner_eq_inner_ιMulti_ofSelfDual_apply`,
  `TauCeti.AlmostComplexStructure.kahlerForm_ofSelfDual`,
  `TauCeti.AlmostComplexStructure.exists_orthonormalBasis_ofSelfDual`: `ofSelfDual` is compatible
  with `F`, `F` is its Kähler two-vector, and it has a positively oriented unitary frame.
* `TauCeti.AlmostComplexStructure.hodgeStar_eq_self_of_inner_eq`: a two-vector with a compatible
  complex structure is self-dual for its symplectic orientation.
* `TauCeti.AlmostComplexStructure.exists_inner_eq_inner_ιMulti_apply_iff`: for the symplectic
  orientation, a compatible complex structure exists exactly when `⋆F = F` and `‖F‖² = 2`.
* `TauCeti.AlmostComplexStructure.existsUnique_inner_eq_inner_ιMulti_apply`: it is then unique.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52** (2012), Section 2.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  {F : ⋀[ℝ]^2 V}

namespace TauCeti

/-! ### The contraction by a self-dual two-vector -/

/-- **The matrix of the contraction by a self-dual two-vector.** In a positively oriented
orthonormal basis `e`, with `a`, `b`, `c` the coordinates of `F` along `e₀ ∧ e₁`, `e₀ ∧ e₂` and
`e₀ ∧ e₃`, the map `u ↦ u ⌟ F` has the matrix `!![0, -a, -b, -c; a, 0, -c, b; b, c, 0, -a;
c, -b, a, 0]`. -/
theorem repr_twoVectorContraction_of_hodgeStar_eq_self {e : OrthonormalBasis (Fin 4) ℝ V}
    (he : e.toBasis.orientation = o) (hF : o.hodgeStar hkl F = F) (v : V) (i : Fin 4) :
    e.repr (twoVectorContraction F v) i =
      ![-(⟪F, ιMulti ℝ 2 ![e 0, e 1]⟫ * e.repr v 1 + ⟪F, ιMulti ℝ 2 ![e 0, e 2]⟫ * e.repr v 2 +
          ⟪F, ιMulti ℝ 2 ![e 0, e 3]⟫ * e.repr v 3),
        ⟪F, ιMulti ℝ 2 ![e 0, e 1]⟫ * e.repr v 0 - ⟪F, ιMulti ℝ 2 ![e 0, e 3]⟫ * e.repr v 2 +
          ⟪F, ιMulti ℝ 2 ![e 0, e 2]⟫ * e.repr v 3,
        ⟪F, ιMulti ℝ 2 ![e 0, e 2]⟫ * e.repr v 0 + ⟪F, ιMulti ℝ 2 ![e 0, e 3]⟫ * e.repr v 1 -
          ⟪F, ιMulti ℝ 2 ![e 0, e 1]⟫ * e.repr v 3,
        ⟪F, ιMulti ℝ 2 ![e 0, e 3]⟫ * e.repr v 0 - ⟪F, ιMulti ℝ 2 ![e 0, e 2]⟫ * e.repr v 1 +
          ⟪F, ιMulti ℝ 2 ![e 0, e 1]⟫ * e.repr v 2] i := by
  obtain ⟨h23, h13, h12⟩ := o.inner_ιMulti_two_of_hodgeStar_eq_self hkl he hF
  rw [e.repr_apply_apply, real_inner_comm, inner_twoVectorContraction_apply,
    e.inner_ιMulti_two_eq_sum F v (e i), h23, h13, h12]
  fin_cases i <;> simp [OrthonormalBasis.repr_self] <;> ring

/-- **The contraction by a self-dual two-vector is conformal**:
`⟪u ⌟ F, w ⌟ F⟫ = (‖F‖² / 2) ⟪u, w⟫` when `⋆F = F` in dimension four. -/
theorem inner_twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self
    (hF : o.hodgeStar hkl F = F) (u w : V) :
    ⟪twoVectorContraction F u, twoVectorContraction F w⟫ = ‖F‖ ^ 2 / 2 * ⟪u, w⟫ := by
  set e := o.finOrthonormalBasis (by norm_num) (Fact.out : finrank ℝ V = 4)
  have he : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four,
    repr_twoVectorContraction_of_hodgeStar_eq_self hkl he hF,
    o.norm_sq_of_hodgeStar_eq_self hkl he hF, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The contraction by a self-dual two-vector squares to a negative multiple of the identity**:
`(u ⌟ F) ⌟ F = -(‖F‖² / 2) u` when `⋆F = F` in dimension four. -/
theorem twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self
    (hF : o.hodgeStar hkl F = F) (u : V) :
    twoVectorContraction F (twoVectorContraction F u) = -(‖F‖ ^ 2 / 2) • u := by
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [inner_twoVectorContraction_apply_left,
    inner_twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self hkl hF,
    real_inner_smul_left]
  ring

/-! ### The compatible complex structure of a self-dual two-vector -/

namespace AlmostComplexStructure

/-- The **almost complex structure of a self-dual two-vector** `F` with `‖F‖² = 2` in an oriented
four-dimensional inner product space: the contraction `u ↦ u ⌟ F`, which squares to `-1` by
`TauCeti.twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self`. It is the unique almost
complex structure with `⟪u, v⟫ = ⟪F, u ∧ J v⟫`
(`TauCeti.AlmostComplexStructure.inner_eq_inner_ιMulti_ofSelfDual_apply`,
`TauCeti.AlmostComplexStructure.eq_ofSelfDual`). -/
def ofSelfDual (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2) : AlmostComplexStructure V where
  toLinearMap := twoVectorContraction F
  square_neg := by
    ext u
    simp [twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self hkl hF, hF₂]

variable {hkl}

/-- `ofSelfDual` is the contraction by `F`. -/
theorem ofSelfDual_apply (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2) (u : V) :
    ofSelfDual hkl hF hF₂ u = twoVectorContraction F u :=
  (rfl)

/-- The underlying linear map of `ofSelfDual` is the contraction by `F`. -/
@[simp]
theorem toLinearMap_ofSelfDual (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2) :
    (ofSelfDual hkl hF hF₂).toLinearMap = twoVectorContraction F :=
  (rfl)

/-- **`ofSelfDual` is compatible with `F`**: `⟪u, v⟫ = ⟪F, u ∧ J v⟫`. -/
theorem inner_eq_inner_ιMulti_ofSelfDual_apply (hF : o.hodgeStar hkl F = F)
    (hF₂ : ‖F‖ ^ 2 = 2) (u v : V) :
    ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, ofSelfDual hkl hF hF₂ v]⟫ := by
  rw [ofSelfDual_apply, ← inner_twoVectorContraction_apply,
    inner_twoVectorContraction_twoVectorContraction_of_hodgeStar_eq_self hkl hF, hF₂]
  ring

/-- `ofSelfDual` is orthogonal. -/
theorem inner_ofSelfDual_apply_ofSelfDual_apply (hF : o.hodgeStar hkl F = F)
    (hF₂ : ‖F‖ ^ 2 = 2) (u v : V) :
    ⟪ofSelfDual hkl hF hF₂ u, ofSelfDual hkl hF hF₂ v⟫ = ⟪u, v⟫ :=
  inner_apply_apply_of_inner_eq (inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂) u v

/-- `F` is the Kähler two-vector of `ofSelfDual`. -/
@[simp]
theorem kahlerForm_ofSelfDual (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2) :
    (ofSelfDual hkl hF hF₂).kahlerForm = F :=
  kahlerForm_eq_of_inner_eq (inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂)

/-- **Uniqueness of the compatible complex structure**: an almost complex structure `J` with
`⟪u, v⟫ = ⟪F, u ∧ J v⟫` is `ofSelfDual`. -/
theorem eq_ofSelfDual (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2)
    {J : AlmostComplexStructure V} (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) :
    J = ofSelfDual hkl hF hF₂ :=
  toLinearMap_injective (toLinearMap_eq_twoVectorContraction hJ)

/-- **A compatible complex structure has a positively oriented unitary frame** for the symplectic
orientation: if `⟪u, v⟫ = ⟪F, u ∧ J v⟫` and `⟪⋆F, F⟫ > 0`, then some positively oriented
orthonormal basis `e` has `J e₀ = e₁` and `J e₂ = e₃`. So the complex orientation of `J` is the
symplectic orientation of `F`. -/
theorem exists_orthonormalBasis_of_inner_eq {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) (hpos : 0 < ⟪o.hodgeStar hkl F, F⟫) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V,
      e.toBasis.orientation = o ∧ J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  set b := o.finOrthonormalBasis (by norm_num) (Fact.out : finrank ℝ V = 4)
  obtain ⟨e, -, h₀, h₂⟩ :=
    exists_unitary_orthonormalBasis_of_norm_eq_one (inner_apply_apply_of_inner_eq hJ)
      (b.orthonormal.1 0)
  refine ⟨e, ?_, h₀, h₂⟩
  -- The frame `e` orients `V` so that the Kähler two-vector `F` of `J` is self-dual. For the
  -- opposite orientation `F` would be anti-self-dual, with `⟪⋆F, F⟫ = -‖F‖² ≤ 0`.
  rcases Orientation.eq_or_eq_neg e.toBasis.orientation o
      ((Fintype.card_fin 4).trans (Fact.out : finrank ℝ V = 4).symm) with he | he
  · exact he
  · -- For the opposite orientation `F` is self-dual, so for `o` it is anti-self-dual.
    have h := hodgeStar_kahlerForm h₀ h₂ hkl he
    rw [kahlerForm_eq_of_inner_eq hJ, Orientation.hodgeStar_neg_orientation, neg_eq_iff_eq_neg] at h
    rw [h, inner_neg_left, real_inner_self_eq_norm_sq] at hpos
    nlinarith [sq_nonneg ‖F‖]

/-- `ofSelfDual` has a positively oriented unitary frame: its complex orientation is the given
one. -/
theorem exists_orthonormalBasis_ofSelfDual (hF : o.hodgeStar hkl F = F) (hF₂ : ‖F‖ ^ 2 = 2) :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V, e.toBasis.orientation = o ∧
      ofSelfDual hkl hF hF₂ (e 0) = e 1 ∧ ofSelfDual hkl hF hF₂ (e 2) = e 3 :=
  exists_orthonormalBasis_of_inner_eq (inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂)
    (by rw [hF, real_inner_self_eq_norm_sq, hF₂]; norm_num)

/-- **A two-vector with a compatible complex structure is self-dual** for its symplectic
orientation: if `⟪u, v⟫ = ⟪F, u ∧ J v⟫` and `⟪⋆F, F⟫ > 0`, then `⋆F = F`. -/
theorem hodgeStar_eq_self_of_inner_eq {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) (hpos : 0 < ⟪o.hodgeStar hkl F, F⟫) :
    o.hodgeStar hkl F = F := by
  obtain ⟨e, he, h₀, h₂⟩ := exists_orthonormalBasis_of_inner_eq hJ hpos
  rw [← kahlerForm_eq_of_inner_eq hJ]
  exact hodgeStar_kahlerForm h₀ h₂ hkl he

/-- **Compatible complex structures of a two-vector in dimension four.** For the symplectic
orientation, in which `⟪⋆F, F⟫ = vol (F ∧ F)` is positive, there is an almost complex structure `J`
with `⟪u, v⟫ = ⟪F, u ∧ J v⟫` exactly when `F` is self-dual and `‖F‖² = 2`. -/
theorem exists_inner_eq_inner_ιMulti_apply_iff :
    ((∃ J : AlmostComplexStructure V, ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫) ∧
        0 < ⟪o.hodgeStar hkl F, F⟫) ↔
      o.hodgeStar hkl F = F ∧ ‖F‖ ^ 2 = 2 := by
  constructor
  · rintro ⟨⟨J, hJ⟩, hpos⟩
    refine ⟨hodgeStar_eq_self_of_inner_eq hJ hpos, ?_⟩
    rw [← kahlerForm_eq_of_inner_eq hJ]
    exact norm_kahlerForm_sq_eq_two (inner_apply_apply_of_inner_eq hJ)
  · rintro ⟨hF, hF₂⟩
    refine ⟨⟨ofSelfDual hkl hF hF₂, inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂⟩, ?_⟩
    rw [hF, real_inner_self_eq_norm_sq, hF₂]
    norm_num

/-- **The compatible complex structure of a self-dual two-vector of norm `√2` is unique.** -/
theorem existsUnique_inner_eq_inner_ιMulti_apply (hF : o.hodgeStar hkl F = F)
    (hF₂ : ‖F‖ ^ 2 = 2) :
    ∃! J : AlmostComplexStructure V, ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫ :=
  ⟨ofSelfDual hkl hF hF₂, inner_eq_inner_ιMulti_ofSelfDual_apply hF hF₂,
    fun _ hJ ↦ eq_ofSelfDual hF hF₂ hJ⟩

end AlmostComplexStructure

end TauCeti
