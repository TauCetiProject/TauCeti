/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Geometry.Symplectic.AlmostComplex
-- Private: orthonormal coordinates and the `4 × 4` determinant are used only in proofs.
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Kähler two-vector of an orthogonal complex structure

Let `V` be a finite-dimensional real inner product space and `J` an almost complex structure on
`V` that is orthogonal, `⟪J v, J w⟫ = ⟪v, w⟫`. Its **Kähler form** `ω(v, w) = ⟪J v, w⟫`, so that
`⟪v, w⟫ = ω(v, J w)`, is identified through the inner product with the two-vector
`TauCeti.AlmostComplexStructure.kahlerForm J ∈ ⋀² V`, characterized by
`⟪ω, u ∧ w⟫ = ⟪J u, w⟫`, and `‖ω‖² = dim V / 2`. In dimension four, in a unitary frame
`e₁, e₂ = J e₁, e₃, e₄ = J e₃`, it is `ω = e₁ ∧ e₂ + e₃ ∧ e₄`. The endomorphism `J` acts on
two-forms as a derivation `D_J (u ∧ w) = J u ∧ w + u ∧ J w` (`exteriorPower.lieMap 2 J`),
which is skew-adjoint and kills `ω`.

In dimension four, for the complex orientation, the one in which unitary frames are positively
oriented, `ω` is self-dual, and on the self-dual two-forms
`Λ⁺ = ℝ ω ⊕ (ℝ ω)ᗮ` the operator `D_J / 2` is zero on `ω` and squares to `-1` on its
orthogonal complement: `D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. This is the complex structure
`ρ ↦ ω_u × ρ`, `ω_u = ω / √2`, of the anti-`J`-invariant self-dual forms. Finally the
self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`; this is what makes the principal symbol of
the anti-self-dual deformation operator complex linear.

Statements in dimension four take a positively oriented orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex one; the
conclusions do not depend on the choice of such a frame.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerForm J`: the Kähler two-vector `ω ∈ ⋀² V`.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_apply_left`: an orthogonal `J` is skew-adjoint.
* `inner_kahlerForm_ιMulti`: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`.
* `inner_kahlerForm_self`: `⟪ω, ω⟫ = dim V / 2`.
* `lieMap_kahlerForm`: `D_J ω = 0`.
* `inner_apply_apply_of_orthonormalBasis`: a `J` with a unitary frame is orthogonal.
* `kahlerForm_eq_ιMulti_add_ιMulti`: `ω = e₀ ∧ e₁ + e₂ ∧ e₃` in a unitary frame.
* `hodgeStar_kahlerForm`: `⋆ω = ω` for the complex orientation.
* `lieMap_lieMap_of_hodgeStar_eq_self`:
  `D_J² η = 2 ⟪ω, η⟫ ω - 4 η` for self-dual `η`.
* `ιMulti_sub_ιMulti_add_hodgeStar`: the self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

/-- The **Kähler form** of an almost complex structure `J` on a real inner product space, as a
two-vector: `ω = (1 / 2) ∑ᵢ bᵢ ∧ J bᵢ` for an orthonormal basis `b`. When `J` is orthogonal it
represents the two-form `ω(u, w) = ⟪J u, w⟫` (`inner_kahlerForm_ιMulti`), so it does not depend
on the basis. -/
def kahlerForm (J : AlmostComplexStructure V) : ⋀[ℝ]^2 V :=
  (2⁻¹ : ℝ) • ∑ i, ιMulti ℝ 2 ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)]

section Orthogonal

variable {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

omit [FiniteDimensional ℝ V] in
/-- An orthogonal almost complex structure is skew-adjoint, `⟪J v, w⟫ = -⟪v, J w⟫`. -/
theorem inner_apply_left (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ :=
  J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ v w

/-- **The Kähler two-vector represents the Kähler form**: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`. -/
@[simp]
theorem inner_kahlerForm_ιMulti (u w : V) :
    ⟪J.kahlerForm, ιMulti ℝ 2 ![u, w]⟫ = ⟪J u, w⟫ := by
  -- Expanding in the orthonormal basis `b`, each sum is `±⟪J u, w⟫`.
  have hsum (x y : V) : ∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ *
      ⟪J (stdOrthonormalBasis ℝ V i), y⟫ = ⟪J x, y⟫ := by
    rw [inner_apply_left hJ x, ← (stdOrthonormalBasis ℝ V).sum_inner_mul_inner x (J y),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_apply_left hJ, real_inner_comm x]
    ring
  simp only [kahlerForm, real_inner_smul_left, sum_inner, inner_ιMulti_two,
    Finset.sum_sub_distrib, hsum]
  rw [inner_apply_left hJ w u, real_inner_comm w (J u)]
  ring

/-- `⟪ω, ω⟫ = dim V / 2`: in a unitary frame `ω = e₁ ∧ e₂ + e₃ ∧ e₄ + ⋯` is a sum of
`dim V / 2` orthonormal two-vectors. -/
theorem inner_kahlerForm_self : ⟪J.kahlerForm, J.kahlerForm⟫ = finrank ℝ V / 2 := by
  have hn (v : V) : ‖J v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_real_inner, hJ, ← norm_eq_sqrt_real_inner]
  nth_rewrite 2 [kahlerForm]
  simp [inner_sum, real_inner_smul_right, inner_kahlerForm_ιMulti hJ, hn, div_eq_inv_mul]

/-- `‖ω‖² = dim V / 2`, the simp normal form of `inner_kahlerForm_self`. -/
@[simp]
theorem norm_kahlerForm_sq : ‖J.kahlerForm‖ ^ 2 = finrank ℝ V / 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_kahlerForm_self hJ]

/-- The derivation action of `J` on two-forms kills the Kähler form: `D_J ω = 0`. -/
@[simp]
theorem lieMap_kahlerForm :
    exteriorPower.lieMap 2 J.toLinearMap J.kahlerForm = 0 := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_lieMap_two_left (inner_apply_left hJ), lieMap_two_apply_ιMulti]
  simp [inner_add_right, inner_kahlerForm_ιMulti hJ, hJ]

end Orthogonal

/-! ### Dimension four -/

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

variable (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

omit [FiniteDimensional ℝ V] in
include h₀ h₂ in
/-- The coordinates of `J v` in a unitary frame: `J` rotates each of the planes `⟨e₀, e₁⟩` and
`⟨e₂, e₃⟩` by a right angle. -/
private theorem repr_apply (v : V) (i : Fin 4) :
    e.repr (J v) i = ![-e.repr v 1, e.repr v 0, -e.repr v 3, e.repr v 2] i := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  have hv : J v = ∑ i, e.repr v i • J (e i) := by
    conv_lhs => rw [← e.sum_repr v]
    simp [map_sum, map_smul]
  rw [hv, Fin.sum_univ_four, h₀, h₁, h₂, h₃]
  fin_cases i <;> simp [OrthonormalBasis.repr_self]

omit [FiniteDimensional ℝ V] in
include h₀ h₂ in
/-- An almost complex structure with a unitary frame, `J e₀ = e₁` and `J e₂ = e₃` for an
orthonormal basis `e`, is orthogonal. -/
theorem inner_apply_apply_of_orthonormalBasis (v w : V) : ⟪J v, J w⟫ = ⟪v, w⟫ := by
  simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, repr_apply h₀ h₂,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  ring

include h₀ h₂ in
/-- In a unitary frame the Kähler two-vector is `ω = e₀ ∧ e₁ + e₂ ∧ e₃`. -/
theorem kahlerForm_eq_ιMulti_add_ιMulti :
    J.kahlerForm = ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3] := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_kahlerForm_ιMulti (inner_apply_apply_of_orthonormalBasis h₀ h₂), inner_add_left,
    inner_ιMulti_two, inner_ιMulti_two]
  simp only [← e.repr_apply_apply, e.inner_eq_sum_repr (J _), conj_trivial, Fin.sum_univ_four,
    repr_apply h₀ h₂, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)

include he h₀ h₂ in
/-- **The Kähler two-vector is self-dual** for the complex orientation, `⋆ω = ω`: in a positively
oriented unitary frame, `⋆(e₀ ∧ e₁) = e₂ ∧ e₃`. -/
theorem hodgeStar_kahlerForm : o.hodgeStar hkl J.kahlerForm = J.kahlerForm := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, map_add, inner_add_left, inner_add_left,
    o.inner_hodgeStar_ιMulti_two hkl, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
    inner_ιMulti_two]
  simp [o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four, Basis.toMatrix_apply,
    ← e.repr_apply_apply, OrthonormalBasis.repr_self]
  ring

include he h₀ h₂ in
/-- The square of the derivation action of `J` on the self-dual part of a two-form:
`D_J² (x + ⋆x) = 4 ⟪ω, x⟫ ω - 4 (x + ⋆x)`. -/
private theorem lieMap_lieMap_add_hodgeStar
    (x : ⋀[ℝ]^2 V) :
    exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap
      (x + o.hodgeStar hkl x)) =
      (4 * ⟪J.kahlerForm, x⟫) • J.kahlerForm - (4 : ℝ) • (x + o.hodgeStar hkl x) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set D := exteriorPower.lieMap 2 J.toLinearMap
  -- Move both derivations to the right, where they act on the wedge `u ∧ w`.
  have hD (z y : ⋀[ℝ]^2 V) : ⟪D (D z), y⟫ = ⟪z, D (D y)⟫ := by
    rw [inner_lieMap_two_left (inner_apply_left hJ),
      inner_lieMap_two_left (inner_apply_left hJ), neg_neg]
  have key : D ∘ₗ D ∘ₗ (LinearMap.id + (o.hodgeStar hkl).toLinearMap) =
      (4 : ℝ) • (innerₗ _ J.kahlerForm).smulRight J.kahlerForm -
        (4 : ℝ) • (LinearMap.id + (o.hodgeStar hkl).toLinearMap) := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply,
      innerₗ_apply_apply, hD, D, exteriorPower.lieMap_two_apply_ιMulti, map_add,
      J.apply_apply, inner_add_left, inner_add_right, inner_sub_left, real_inner_smul_left,
      inner_kahlerForm_ιMulti hJ, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
      o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four]
    simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_neg,
      Finsupp.neg_apply, PiLp.neg_apply, repr_apply h₀ h₂]
    ring
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply,
    innerₗ_apply_apply, smul_smul] using LinearMap.congr_fun key x

include he h₀ h₂ in
/-- **`J` acts on the self-dual two-forms as a rotation about `ω`**: for self-dual `η`,
`D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. Since `⟪ω, ω⟫ = 2`, the map `D_J / 2` is zero on `ω` and squares to
`-1` on the orthogonal complement of `ω` in `Λ⁺`. -/
theorem lieMap_lieMap_of_hodgeStar_eq_self
    {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = η) :
    exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap η) =
      (2 * ⟪J.kahlerForm, η⟫) • J.kahlerForm - (4 : ℝ) • η := by
  have h := lieMap_lieMap_add_hodgeStar h₀ h₂ hkl he η
  rw [hη, map_add, map_add] at h
  linear_combination (norm := module) (2⁻¹ : ℝ) • h

include he h₀ h₂ in
/-- **The self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`**:
`z + ⋆z = 2 ⟪ξ, a⟫ ω` for `z = ξ ∧ J a - J ξ ∧ a`. For `a = ξ` a unit vector this says that
`2 ξ ∧ J ξ - ω` is anti-self-dual. -/
theorem ιMulti_sub_ιMulti_add_hodgeStar (ξ a : V) :
    ιMulti ℝ 2 ![ξ, J a] - ιMulti ℝ 2 ![J ξ, a] +
        o.hodgeStar hkl (ιMulti ℝ 2 ![ξ, J a] - ιMulti ℝ 2 ![J ξ, a]) =
      (2 * ⟪ξ, a⟫) • J.kahlerForm := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  simp only [map_sub, inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_kahlerForm_ιMulti hJ, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
    o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four]
  simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    repr_apply h₀ h₂]
  ring

end Frame

end TauCeti.AlmostComplexStructure
