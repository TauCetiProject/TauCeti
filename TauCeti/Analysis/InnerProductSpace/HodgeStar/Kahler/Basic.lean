/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
-- Private: orthonormal coordinates and the `4 × 4` determinant are used only in proofs.
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour

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

Conversely, if a two-vector `F` and an almost complex structure `J` satisfy
`⟪u, v⟫ = ⟪F, u ∧ J v⟫`, then `J` is the contraction `u ↦ u ⌟ F`
(`TauCeti.twoVectorContraction F`), so such a `J` is unique; it is orthogonal and `F` is its
Kähler two-vector.

In dimension four, for the complex orientation, the one in which unitary frames are positively
oriented, `ω` is self-dual, and on the self-dual two-forms
`Λ⁺ = ℝ ω ⊕ (ℝ ω)ᗮ` the operator `D_J / 2` is zero on `ω` and squares to `-1` on its
orthogonal complement: `D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. This is the complex structure
`ρ ↦ ω_u × ρ`, `ω_u = ω / √2`, of the anti-`J`-invariant self-dual forms. On the
anti-self-dual two-forms `D_J` vanishes, so these are `J`-invariant. Finally the
self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`; this is what makes the principal symbol of
the anti-self-dual deformation operator complex linear.

The Hodge-star and self-duality results in dimension four take a positively oriented
orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex one; the
conclusions do not depend on the choice of such a frame.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerForm J`: the Kähler two-vector `ω ∈ ⋀² V`.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_apply_left`: an orthogonal `J` is skew-adjoint.
* `inner_kahlerForm_ιMulti`: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`.
* `inner_kahlerForm_self`: `⟪ω, ω⟫ = dim V / 2`.
* `norm_ιMulti_apply_sq`: `‖v ∧ J v‖² = ‖v‖⁴`.
* `lieMap_kahlerForm`: `D_J ω = 0`.
* `lieMap_lieMap_lieMap`: `D_J³ = -4 D_J`, so `η + D_J² η / 4` is `J`-invariant
  (`lieMap_add_smul_lieMap_lieMap`).
* `inner_lieMap_lieMap_ιMulti`: `⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))`.
* `toLinearMap_eq_twoVectorContraction`: a `J` with `⟪u, v⟫ = ⟪F, u ∧ J v⟫` is the
  contraction by `F`; it is orthogonal (`inner_apply_apply_of_inner_eq`) and `F` is its Kähler
  two-vector (`kahlerForm_eq_of_inner_eq`).
* `repr_apply`: the coordinates of `J v` in a unitary frame.
* `inner_apply_apply_of_orthonormalBasis`: a `J` with a unitary frame is orthogonal.
* `kahlerForm_eq_ιMulti_add_ιMulti`: `ω = e₀ ∧ e₁ + e₂ ∧ e₃` in a unitary frame.
* `hodgeStar_kahlerForm`: `⋆ω = ω` for the complex orientation.
* `inner_kahlerForm_hodgeStar`: `⟪ω, ⋆F⟫ = ⟪ω, F⟫`.
* `inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg`: `ω` is orthogonal to anti-self-dual forms.
* `lieMap_lieMap_of_hodgeStar_eq_self`:
  `D_J² η = 2 ⟪ω, η⟫ ω - 4 η` for self-dual `η`.
* `lieMap_of_hodgeStar_eq_neg`: `D_J η = 0` for anti-self-dual `η`.
* `ιMulti_sub_ιMulti_add_hodgeStar`: the self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`.
* `eq_smul_kahlerForm_add_of_lieMap_eq_zero`: a `J`-invariant `η` is
  `(⟪ω, η⟫ / 2) ω + (η - ⋆η) / 2`.

The supporting norm-preservation and four-frame construction lemmas live in
`TauCeti.Geometry.Symplectic.Complex.InnerProductSpace` and
`TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis`, respectively.

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

/-- The Kähler two-vector is half the sum of `bᵢ ∧ J bᵢ` in the standard orthonormal basis. -/
theorem kahlerForm_def (J : AlmostComplexStructure V) :
    J.kahlerForm = (2⁻¹ : ℝ) • ∑ i,
      ιMulti ℝ 2 ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)] := (rfl)

/-! ### The derivation action of `J` on two-vectors -/

/-- `D_J² (u ∧ w) = 2 (J u ∧ J w) - 2 (u ∧ w)`. -/
theorem lieMap_lieMap_ιMulti (J : AlmostComplexStructure V) (u w : V) :
    lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![u, w])) =
      (2 : ℝ) • ιMulti ℝ 2 ![J u, J w] - (2 : ℝ) • ιMulti ℝ 2 ![u, w] := by
  refine ext_inner_ιMulti_two fun a b ↦ ?_
  simp only [lieMap_two_apply_ιMulti, map_add, inner_add_left, inner_sub_left,
    real_inner_smul_left, inner_ιMulti_two, apply_apply, inner_neg_left]
  ring

/-- **`D_J³ = -4 D_J` on two-vectors.** Hence `D_J² / 4` is minus the projection onto the
anti-`J`-invariant two-vectors, the `-4`-eigenspace of `D_J²`, and `η + D_J² η / 4` is the
`J`-invariant part of `η`. -/
theorem lieMap_lieMap_lieMap (J : AlmostComplexStructure V) (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)) =
      -(4 : ℝ) • lieMap 2 J.toLinearMap η := by
  set D := lieMap 2 J.toLinearMap
  have key : D ∘ₗ D ∘ₗ D = -(4 : ℝ) • D := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, D]
    rw [lieMap_lieMap_ιMulti]
    simp only [map_sub, map_smul, lieMap_two_apply_ιMulti, inner_add_left, inner_sub_left,
      real_inner_smul_left, inner_ιMulti_two, apply_apply, inner_neg_left]
    ring
  exact LinearMap.congr_fun key η

/-- The two-form `η + D_J² η / 4` is `J`-invariant. -/
theorem lieMap_add_smul_lieMap_lieMap (J : AlmostComplexStructure V) (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap
        (η + (4⁻¹ : ℝ) • lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)) = 0 := by
  rw [map_add, map_smul, lieMap_lieMap_lieMap, smul_smul]
  norm_num

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
  nth_rewrite 2 [kahlerForm]
  simp [inner_sum, real_inner_smul_right, inner_kahlerForm_ιMulti hJ, norm_apply hJ,
    div_eq_inv_mul]

/-- `‖ω‖² = dim V / 2`, the simp normal form of `inner_kahlerForm_self`. -/
@[simp]
theorem norm_kahlerForm_sq : ‖J.kahlerForm‖ ^ 2 = finrank ℝ V / 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_kahlerForm_self hJ]

/-- `‖v ∧ J v‖² = ‖v‖⁴` for an orthogonal `J`, since `J v` is orthogonal to `v` and has the same
norm. -/
theorem norm_ιMulti_apply_sq (v : V) : ‖ιMulti ℝ 2 ![v, J v]‖ ^ 2 = ‖v‖ ^ 4 := by
  have h0 : ⟪v, J v⟫ = 0 := by
    have := inner_apply_left hJ v v
    rw [real_inner_comm] at this
    linarith
  rw [← real_inner_self_eq_norm_sq, inner_ιMulti_two, hJ, h0, real_inner_self_eq_norm_sq]
  ring

/-- The derivation action of `J` on two-forms kills the Kähler form: `D_J ω = 0`. -/
@[simp]
theorem lieMap_kahlerForm :
    exteriorPower.lieMap 2 J.toLinearMap J.kahlerForm = 0 := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_lieMap_left (inner_apply_left hJ), lieMap_two_apply_ιMulti]
  simp [inner_add_right, inner_kahlerForm_ιMulti hJ, hJ]

/-- `D_J² η` (minus four times the anti-`J`-invariant part of `η`), read on pairs of vectors:
`⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))` for an orthogonal `J`. -/
theorem inner_lieMap_lieMap_ιMulti (η : ⋀[ℝ]^2 V) (u w : V) :
    ⟪lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η), ιMulti ℝ 2 ![u, w]⟫ =
      2 * (⟪η, ιMulti ℝ 2 ![J u, J w]⟫ - ⟪η, ιMulti ℝ 2 ![u, w]⟫) := by
  rw [inner_lieMap_left (inner_apply_left hJ), inner_lieMap_left (inner_apply_left hJ), neg_neg,
    lieMap_lieMap_ιMulti, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  ring

end Orthogonal

/-! ### Almost complex structures represented by a two-vector -/

section Contraction

variable {F : ⋀[ℝ]^2 V} {J : AlmostComplexStructure V}
  (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫)
include hJ

/-- **Uniqueness of the compatible complex structure.** An almost complex structure `J` with
`g(u, v) = ω(u, J v)`, where `ω(u, w) = ⟪F, u ∧ w⟫`, is the contraction by `F`. -/
theorem toLinearMap_eq_twoVectorContraction : J.toLinearMap = twoVectorContraction F := by
  -- Taking `v = -J w` gives `⟪u ⌟ F, w⟫ = -⟪u, J w⟫`.
  have hA (u w : V) : ⟪twoVectorContraction F u, w⟫ = -⟪u, J w⟫ := by
    have h := hJ u (-J w)
    rw [map_neg, J.apply_apply, neg_neg, inner_neg_right] at h
    rw [inner_twoVectorContraction_apply, ← h]
  refine LinearMap.ext fun u ↦ ext_inner_right ℝ fun w ↦ ?_
  rw [inner_twoVectorContraction_apply_left, real_inner_comm (twoVectorContraction F w) u, hA,
    neg_neg, real_inner_comm]

/-- An almost complex structure with `g(u, v) = ω(u, J v)` is orthogonal. -/
theorem inner_apply_apply_of_inner_eq (u v : V) : ⟪J u, J v⟫ = ⟪u, v⟫ := by
  have h : J u = twoVectorContraction F u :=
    LinearMap.congr_fun (toLinearMap_eq_twoVectorContraction hJ) u
  rw [h, inner_twoVectorContraction_apply, hJ]

/-- A two-vector `F` with `g(u, v) = ω(u, J v)` is the Kähler two-vector of `J`. -/
theorem kahlerForm_eq_of_inner_eq : J.kahlerForm = F := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  have h : J u = twoVectorContraction F u :=
    LinearMap.congr_fun (toLinearMap_eq_twoVectorContraction hJ) u
  rw [inner_kahlerForm_ιMulti (inner_apply_apply_of_inner_eq hJ), h,
    inner_twoVectorContraction_apply]

end Contraction

/-! ### Dimension four -/

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

variable (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

omit [FiniteDimensional ℝ V] in
include h₀ h₂ in
/-- The coordinates of `J v` in a unitary frame: `J` rotates each of the planes `⟨e₀, e₁⟩` and
`⟨e₂, e₃⟩` by a right angle. -/
theorem repr_apply (v : V) (i : Fin 4) :
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
/-- **The Hodge star preserves the `ω`-component** of a two-form, `⟪ω, ⋆F⟫ = ⟪ω, F⟫`, since `ω`
is self-dual for the complex orientation. -/
theorem inner_kahlerForm_hodgeStar (F : ⋀[ℝ]^2 V) :
    ⟪J.kahlerForm, o.hodgeStar hkl F⟫ = ⟪J.kahlerForm, F⟫ :=
  o.inner_hodgeStar_right_of_hodgeStar_eq_self even_two hkl (hodgeStar_kahlerForm h₀ h₂ hkl he) F

include he h₀ h₂ in
/-- **The Kähler form is orthogonal to the anti-self-dual forms**: `⟪ω, μ⟫ = 0` when `⋆μ = -μ`,
since `ω` is self-dual for the complex orientation. -/
theorem inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) : ⟪J.kahlerForm, μ⟫ = 0 := by
  have h := o.inner_hodgeStar_right_of_hodgeStar_eq_neg even_two hkl hμ J.kahlerForm
  rw [hodgeStar_kahlerForm h₀ h₂ hkl he, real_inner_comm] at h
  linarith

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
    rw [inner_lieMap_left (inner_apply_left hJ),
      inner_lieMap_left (inner_apply_left hJ), neg_neg]
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
/-- **`J` acts trivially on the anti-self-dual two-forms**: `D_J η = 0` for `⋆η = -η`. Since
`D_J` is skew-adjoint, this says that an anti-self-dual two-form is `J`-invariant,
`η(J u, J w) = η(u, w)`, as is `ω`; the anti-self-dual forms are the primitive `(1,1)`-forms. -/
theorem lieMap_of_hodgeStar_eq_neg {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = -η) :
    exteriorPower.lieMap 2 J.toLinearMap η = 0 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set D := exteriorPower.lieMap 2 J.toLinearMap
  -- `D_J` kills the anti-self-dual part `x - ⋆x` of every two-vector `x`.
  have key : D ∘ₗ (LinearMap.id - (o.hodgeStar hkl).toLinearMap) = 0 := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearMap.zero_apply, inner_zero_left,
      inner_lieMap_left (inner_apply_left hJ), D, exteriorPower.lieMap_two_apply_ιMulti,
      inner_add_right, inner_sub_left, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
      o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four]
    simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      repr_apply h₀ h₂]
    ring
  have h := LinearMap.congr_fun key η
  rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hη,
    sub_neg_eq_add, map_add, LinearMap.zero_apply] at h
  rwa [← two_smul ℝ (D η), smul_eq_zero, or_iff_right two_ne_zero] at h

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

include he h₀ h₂ in
/-- **A `J`-invariant two-form is a multiple of `ω` plus an anti-self-dual form**: for
`D_J η = 0`, `η = (⟪ω, η⟫ / 2) ω + (η - ⋆η) / 2`. -/
theorem eq_smul_kahlerForm_add_of_lieMap_eq_zero {η : ⋀[ℝ]^2 V}
    (hη : lieMap 2 J.toLinearMap η = 0) :
    η = (⟪J.kahlerForm, η⟫ / 2) • J.kahlerForm + (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η) := by
  set p := (2⁻¹ : ℝ) • (η + o.hodgeStar hkl η)
  set m := (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η)
  have hp : o.hodgeStar hkl p = p := o.hodgeStar_smul_add_hodgeStar even_two hkl η
  have hm : o.hodgeStar hkl m = -m := o.hodgeStar_smul_sub_hodgeStar even_two hkl η
  have hpm : p + m = η := by simp only [p, m]; module
  -- The self-dual part `p` is `J`-invariant, as `η` and its anti-self-dual part are.
  have hDp : lieMap 2 J.toLinearMap p = 0 := by
    have h := congrArg (lieMap 2 J.toLinearMap) hpm
    rwa [map_add, lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hm, add_zero, hη] at h
  have h2 := lieMap_lieMap_of_hodgeStar_eq_self h₀ h₂ hkl he hp
  rw [hDp, map_zero] at h2
  have hω : ⟪J.kahlerForm, p⟫ = ⟪J.kahlerForm, η⟫ := by
    rw [← hpm, inner_add_right, inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hm,
      add_zero]
  rw [hω] at h2
  calc η = p + m := hpm.symm
    _ = _ := by
      congr 1
      linear_combination (norm := module) (4⁻¹ : ℝ) • h2

end Frame

end TauCeti.AlmostComplexStructure
