/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Geometry.Symplectic.AlmostComplex
-- Private: the wedge-pairing transport lemma and orthonormal coordinates are used only in proofs.
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Kähler two-vector of an orthogonal complex structure

Let `V` be a finite-dimensional real inner product space and `J` an almost complex structure on
`V` that is orthogonal, `⟪J v, J w⟫ = ⟪v, w⟫`. Its **Kähler form** `ω(v, w) = ⟪J v, w⟫`, so that
`⟪v, w⟫ = ω(v, J w)`, is identified through the inner product with the two-vector
`TauCeti.AlmostComplexStructure.kahlerForm J ∈ ⋀² V`, characterized by
`⟪ω, u ∧ w⟫ = ⟪J u, w⟫`, and `‖ω‖² = dim V / 2`. In dimension four, in a unitary frame
`e₁, e₂ = J e₁, e₃, e₄ = J e₃`, it is `ω = e₁ ∧ e₂ + e₃ ∧ e₄`. The endomorphism `J` acts on
two-forms as a derivation `D_J (u ∧ w) = J u ∧ w + u ∧ J w` (`LinearMap.exteriorSquareDerivation`),
which is skew-adjoint and kills `ω`.

In dimension four the derivation action of any skew-adjoint endomorphism commutes with the Hodge
star. For the complex orientation, the one in which unitary frames are positively oriented, `ω`
is self-dual, and on the self-dual two-forms
`Λ⁺ = ℝ ω ⊕ (ℝ ω)ᗮ` the operator `D_J / 2` is zero on `ω` and squares to `-1` on its
orthogonal complement: `D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. This is the complex structure
`ρ ↦ ω_u × ρ`, `ω_u = ω / √2`, of the anti-`J`-invariant self-dual forms. Finally the
self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`; this is what makes the principal symbol of
the anti-self-dual deformation operator complex linear.

Statements in dimension four take a positively oriented orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex one; the
conclusions do not depend on the choice of such a frame. Their proofs reduce, by
`exteriorPower.ext_inner_ιMulti`, to identities between inner products and volumes of vectors,
which are polynomial identities in the coordinates of the frame.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerForm J`: the Kähler two-vector `ω ∈ ⋀² V`.

## Main results

* `Orientation.inner_hodgeStar_ιMulti_two`: in dimension four,
  `⟪⋆(a ∧ b), u ∧ w⟫ = vol(a, b, u, w)`.
* `Orientation.hodgeStar_exteriorSquareDerivation`: in dimension four, the derivation action of a
  skew-adjoint endomorphism commutes with the Hodge star, `⋆ D_A = D_A ⋆`.

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_apply_left`: an orthogonal `J` is skew-adjoint.
* `inner_kahlerForm_ιMulti`: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`.
* `inner_kahlerForm_self`: `⟪ω, ω⟫ = dim V / 2`.
* `exteriorSquareDerivation_kahlerForm`: `D_J ω = 0`.
* `inner_apply_apply_of_orthonormalBasis`: a `J` with a unitary frame is orthogonal.
* `kahlerForm_eq_ιMulti_add_ιMulti`: `ω = e₀ ∧ e₁ + e₂ ∧ e₃` in a unitary frame.
* `hodgeStar_kahlerForm`: `⋆ω = ω` for the complex orientation.
* `exteriorSquareDerivation_exteriorSquareDerivation_of_hodgeStar_eq_self`:
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

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A two-element family is the vector of its two entries. -/
private theorem fin_two_eq_vecCons (v : Fin 2 → V) : v = ![v 0, v 1] := by
  ext i
  fin_cases i <;> rfl

namespace Orientation

variable [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4))

/-- In dimension four, the Hodge star of a wedge of two vectors pairs with another such wedge to
the volume of the four vectors: `⟪⋆(a ∧ b), u ∧ w⟫ = vol(a, b, u, w)`. -/
theorem inner_hodgeStar_ιMulti_two (hkl : 2 + 2 = finrank ℝ V) (a b u w : V) :
    ⟪o.hodgeStar hkl (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ = o.volumeForm ![a, b, u, w] := by
  -- Read the wedge of the four vectors in the degree `finrank ℝ V`.
  have key : ∀ {d : ℕ} (hd : d = 4) (f : Fin 4 → V),
      ExteriorAlgebra.ιMulti ℝ d (f ∘ finCongr hd) = ExteriorAlgebra.ιMulti ℝ 4 f := by
    rintro d rfl f
    rfl
  rw [inner_hodgeStar_apply, wedgePairing_apply_eq_of_coe_mul_eq _ hkl _ _
    (ιMulti ℝ _ (![a, b, u, w] ∘ finCongr (Fact.out : finrank ℝ V = 4))), volumeEquiv_ιMulti]
  · congr 1
  · simp only [ιMulti_apply_coe, key, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 1
    ext i
    fin_cases i <;> rfl

end Orientation

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
theorem inner_apply_left (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ := by
  have h := hJ v (J w)
  rw [J.apply_apply, inner_neg_right] at h
  linarith

/-- **The Kähler two-vector represents the Kähler form**: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`. -/
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

/-- The derivation action of `J` on two-forms kills the Kähler form: `D_J ω = 0`. -/
theorem exteriorSquareDerivation_kahlerForm :
    J.toLinearMap.exteriorSquareDerivation J.kahlerForm = 0 := by
  refine ext_inner_ιMulti fun v ↦ ?_
  rw [fin_two_eq_vecCons v, inner_exteriorSquareDerivation_left (inner_apply_left hJ)]
  simp [inner_add_right, inner_kahlerForm_ιMulti hJ, hJ]

end Orthogonal

/-! ### Dimension four -/

/-- The `4 × 4` determinant, expanded. -/
private theorem det_fin_four (m : Matrix (Fin 4) (Fin 4) ℝ) : m.det =
    m 0 0 * (m 1 1 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 1 * m 3 3 - m 2 3 * m 3 1)
      + m 1 3 * (m 2 1 * m 3 2 - m 2 2 * m 3 1))
    - m 0 1 * (m 1 0 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
      + m 1 3 * (m 2 0 * m 3 2 - m 2 2 * m 3 0))
    + m 0 2 * (m 1 0 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) - m 1 1 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
      + m 1 3 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))
    - m 0 3 * (m 1 0 * (m 2 1 * m 3 2 - m 2 2 * m 3 1) - m 1 1 * (m 2 0 * m 3 2 - m 2 2 * m 3 0)
      + m 1 2 * (m 2 0 * m 3 1 - m 2 1 * m 3 0)) := by
  have h₁ : (Fin.succAbove 1 2 : Fin 4) = 3 := rfl
  have h₂ : (Fin.succAbove 2 2 : Fin 4) = 3 := rfl
  have h₃ : (Fin.succAbove 3 2 : Fin 4) = 2 := rfl
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succ_succAbove_one,
    h₁, h₂, h₃]
  ring

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

omit [FiniteDimensional ℝ V] in
/-- The inner product in the coordinates of an orthonormal basis. -/
private theorem inner_eq_sum_repr (e : OrthonormalBasis (Fin 4) ℝ V) (v w : V) :
    ⟪v, w⟫ = ∑ i, e.repr v i * e.repr w i := by
  rw [← e.repr.inner_map_map v w, PiLp.inner_apply]
  simp [mul_comm]

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
  simp only [inner_eq_sum_repr e, Fin.sum_univ_four, repr_apply h₀ h₂, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  ring

include h₀ h₂ in
/-- In a unitary frame the Kähler two-vector is `ω = e₀ ∧ e₁ + e₂ ∧ e₃`. -/
theorem kahlerForm_eq_ιMulti_add_ιMulti :
    J.kahlerForm = ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3] := by
  refine ext_inner_ιMulti fun v ↦ ?_
  rw [fin_two_eq_vecCons v, inner_kahlerForm_ιMulti (inner_apply_apply_of_orthonormalBasis h₀ h₂),
    inner_add_left, inner_ιMulti_two, inner_ιMulti_two]
  simp only [← e.repr_apply_apply, inner_eq_sum_repr e (J _), Fin.sum_univ_four,
    repr_apply h₀ h₂, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Two endomorphisms of `⋀² V` agree when they have the same inner products on wedges. -/
private theorem linearMap_ext_two {f g : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V}
    (h : ∀ a b u w, ⟪f (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ =
      ⟪g (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫) : f = g := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ext_inner_ιMulti fun v' ↦ ?_)
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
    fin_two_eq_vecCons v, fin_two_eq_vecCons v']
  exact h _ _ _ _

variable [Fact (finrank ℝ V = 4)] (o : Orientation ℝ V (Fin 4)) (hkl : 2 + 2 = finrank ℝ V)

omit [FiniteDimensional ℝ V] in
/-- The volume form of four vectors in the coordinates of a positively oriented orthonormal
basis. -/
private theorem volumeForm_eq (he : e.toBasis.orientation = o) (a b u w : V) :
    o.volumeForm ![a, b, u, w] = (Matrix.of fun i j ↦ e.repr (![a, b, u, w] j) i).det := by
  rw [o.volumeForm_robust e he, Module.Basis.det_apply]
  rfl

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
/-- The coordinates of `A v` for a skew-adjoint `A`, in terms of the six entries
`⟪eᵢ, A eⱼ⟫`, `i < j`, of its matrix in an orthonormal basis. -/
private theorem repr_apply_of_skew (e : OrthonormalBasis (Fin 4) ℝ V) {A : V →ₗ[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (v : V) (i : Fin 4) :
    e.repr (A v) i =
      ![⟪e 0, A (e 1)⟫ * e.repr v 1 + ⟪e 0, A (e 2)⟫ * e.repr v 2 + ⟪e 0, A (e 3)⟫ * e.repr v 3,
        -⟪e 0, A (e 1)⟫ * e.repr v 0 + ⟪e 1, A (e 2)⟫ * e.repr v 2 + ⟪e 1, A (e 3)⟫ * e.repr v 3,
        -⟪e 0, A (e 2)⟫ * e.repr v 0 - ⟪e 1, A (e 2)⟫ * e.repr v 1 + ⟪e 2, A (e 3)⟫ * e.repr v 3,
        -⟪e 0, A (e 3)⟫ * e.repr v 0 - ⟪e 1, A (e 3)⟫ * e.repr v 1 -
          ⟪e 2, A (e 3)⟫ * e.repr v 2] i := by
  have hm (i j : Fin 4) : ⟪e i, A (e j)⟫ = -⟪e j, A (e i)⟫ := by
    rw [← hA, real_inner_comm]
  have hd (i : Fin 4) : ⟪e i, A (e i)⟫ = 0 := by linarith [hm i i]
  have hv : e.repr (A v) i = ∑ j, e.repr v j * ⟪e i, A (e j)⟫ := by
    conv_lhs => rw [← e.sum_repr v]
    simp [OrthonormalBasis.repr_apply_apply]
  rw [hv, Fin.sum_univ_four]
  fin_cases i <;>
    simp [hd, hm 1 0, hm 2 0, hm 3 0, hm 2 1, hm 3 1, hm 3 2] <;> ring

/-- **Skew-adjoint endomorphisms commute with the Hodge star on two-forms** in dimension four:
`⋆ (D_A x) = D_A (⋆ x)` for the derivation action `D_A` of a skew-adjoint `A`. This is the
infinitesimal form of the invariance of `⋆` under rotations; it holds because `D_A` acts on
`⋀⁴ V` by `tr A = 0`. -/
theorem _root_.Orientation.hodgeStar_exteriorSquareDerivation {A : V →ₗ[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x : ⋀[ℝ]^2 V) :
    o.hodgeStar hkl (A.exteriorSquareDerivation x) =
      A.exteriorSquareDerivation (o.hodgeStar hkl x) := by
  set e := (stdOrthonormalBasis ℝ V).reindex (finCongr (Fact.out : finrank ℝ V = 4))
    |>.adjustToOrientation o
  have he : e.toBasis.orientation = o := OrthonormalBasis.orientation_adjustToOrientation _ _
  refine LinearMap.congr_fun (linearMap_ext_two (f := (o.hodgeStar hkl).toLinearMap ∘ₗ
    A.exteriorSquareDerivation) (g := A.exteriorSquareDerivation ∘ₗ
    (o.hodgeStar hkl).toLinearMap) fun a b u w ↦ ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, inner_exteriorSquareDerivation_left hA,
    LinearMap.exteriorSquareDerivation_ιMulti, map_add, inner_add_left, inner_add_right,
    o.inner_hodgeStar_ιMulti_two hkl, volumeForm_eq o he, det_fin_four]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, repr_apply_of_skew e hA]
  ring

variable {o} (he : e.toBasis.orientation = o)

include he h₀ h₂ in
/-- **The Kähler two-vector is self-dual** for the complex orientation, `⋆ω = ω`: in a positively
oriented unitary frame, `⋆(e₀ ∧ e₁) = e₂ ∧ e₃`. -/
theorem hodgeStar_kahlerForm : o.hodgeStar hkl J.kahlerForm = J.kahlerForm := by
  refine ext_inner_ιMulti fun v ↦ ?_
  rw [fin_two_eq_vecCons v, kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, map_add, inner_add_left,
    inner_add_left, o.inner_hodgeStar_ιMulti_two hkl, o.inner_hodgeStar_ιMulti_two hkl,
    volumeForm_eq o he, volumeForm_eq o he, det_fin_four, det_fin_four, inner_ιMulti_two,
    inner_ιMulti_two]
  simp [← e.repr_apply_apply, OrthonormalBasis.repr_self]
  ring

include he h₀ h₂ in
/-- The square of the derivation action of `J` on the self-dual part of a two-form:
`D_J² (x + ⋆x) = 4 ⟪ω, x⟫ ω - 4 (x + ⋆x)`. -/
private theorem exteriorSquareDerivation_exteriorSquareDerivation_add_hodgeStar
    (x : ⋀[ℝ]^2 V) :
    J.toLinearMap.exteriorSquareDerivation (J.toLinearMap.exteriorSquareDerivation
      (x + o.hodgeStar hkl x)) =
      (4 * ⟪J.kahlerForm, x⟫) • J.kahlerForm - (4 : ℝ) • (x + o.hodgeStar hkl x) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set D := J.toLinearMap.exteriorSquareDerivation
  -- Move both derivations to the right, where they act on the wedge `u ∧ w`.
  have hD (z y : ⋀[ℝ]^2 V) : ⟪D (D z), y⟫ = ⟪z, D (D y)⟫ := by
    rw [inner_exteriorSquareDerivation_left (inner_apply_left hJ),
      inner_exteriorSquareDerivation_left (inner_apply_left hJ), neg_neg]
  have key : D ∘ₗ D ∘ₗ (LinearMap.id + (o.hodgeStar hkl).toLinearMap) =
      (4 : ℝ) • (innerₗ _ J.kahlerForm).smulRight J.kahlerForm -
        (4 : ℝ) • (LinearMap.id + (o.hodgeStar hkl).toLinearMap) := by
    refine linearMap_ext_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply,
      innerₗ_apply_apply, hD, D, LinearMap.exteriorSquareDerivation_ιMulti, map_add,
      J.apply_apply, inner_add_left, inner_add_right, inner_sub_left, real_inner_smul_left,
      inner_kahlerForm_ιMulti hJ, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
      volumeForm_eq o he, det_fin_four]
    simp only [inner_eq_sum_repr e, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, map_neg, PiLp.neg_apply, repr_apply h₀ h₂]
    ring
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply,
    innerₗ_apply_apply, smul_smul] using LinearMap.congr_fun key x

include he h₀ h₂ in
/-- **`J` acts on the self-dual two-forms as a rotation about `ω`**: for self-dual `η`,
`D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. Since `⟪ω, ω⟫ = 2`, the map `D_J / 2` is zero on `ω` and squares to
`-1` on the orthogonal complement of `ω` in `Λ⁺`. -/
theorem exteriorSquareDerivation_exteriorSquareDerivation_of_hodgeStar_eq_self
    {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = η) :
    J.toLinearMap.exteriorSquareDerivation (J.toLinearMap.exteriorSquareDerivation η) =
      (2 * ⟪J.kahlerForm, η⟫) • J.kahlerForm - (4 : ℝ) • η := by
  have h := exteriorSquareDerivation_exteriorSquareDerivation_add_hodgeStar h₀ h₂ hkl he η
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
  refine ext_inner_ιMulti fun v ↦ ?_
  rw [fin_two_eq_vecCons v]
  simp only [map_sub, inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_kahlerForm_ιMulti hJ, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
    volumeForm_eq o he, det_fin_four]
  simp only [inner_eq_sum_repr e, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, repr_apply h₀ h₂]
  ring

end Frame

end TauCeti.AlmostComplexStructure
