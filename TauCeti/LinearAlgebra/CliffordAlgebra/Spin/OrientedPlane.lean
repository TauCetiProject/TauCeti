/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Rotation
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
import TauCeti.Analysis.InnerProductSpace.TwoDim
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.Two

/-!
# The Spin group of an oriented Euclidean plane

Let `V` be an oriented Euclidean plane, with the geometric Clifford convention
`Q v = -‖v‖²`, so that `c(v)² = -‖v‖²`. Its volume element `ω = c(e₀) c(e₁)`, for any positively
oriented orthonormal basis `(e₀, e₁)`, squares to `-1`, and the unit complex number `z` gives the
element

`z ↦ Re z + Im z · ω`,

which for `z = exp (i θ)` is `cos θ + sin θ e₀ e₁`. This is a frame-free isomorphism of the unit
circle onto `Spin(V)` (`Orientation.spinCircleEquiv`). This file pins the characters of the three
basic representations of `Spin(V)` in these coordinates.

* **Vectors.** The element `z` acts on `V` by multiplication by `z²` for the complex structure
  given by the quarter turn `J` of the orientation: `v ↦ Re (z²) v + Im (z²) J v`. In particular
  `cos θ + sin θ e₀ e₁` rotates `V` by the angle `2θ`, and the complex line `(V, J)` has weight
  `z²`.
* **Half-spinors.** On every module `E` over the complexified Clifford algebra, the chirality
  element is `Γ = i c(e₀) c(e₁)` (`CliffordAlgebra.complexVolume`), so `ω` acts as `-iΓ` and `z`
  acts on the positive half-spinors `E⁺ = {Γ = 1}` by `z⁻¹` and on the negative half-spinors
  `E⁻ = {Γ = -1}` by `z`. Thus `E⁺` has weight `z⁻¹` and `E⁻` has weight `z`. These are the
  characters behind the isomorphisms `(S⁻)² ≅ (V, J)`, `(S⁺)² ≅ (V, J)*` and `S⁻ ≅ (S⁺)*` for
  the half-spin lines of the spinor module; the isomorphisms themselves are not constructed here.
* **Positive form.** Under the comparison `CliffordAlgebra.spinGroupEquivNeg` of `Spin(Q)` with
  the Spin group of the positive definite form `-Q`, which negates bivectors, the element
  `Re z + Im z · ω` goes to `Re z - Im z · ω₊`, with `ω₊` the volume element of `-Q`; that is,
  `cos θ + sin θ e₀ e₁` goes to `cos θ - sin θ e₀ e₁`.

Reversing the orientation negates `ω`, so it replaces `z` by `z⁻¹`
(`Orientation.spinCircle_neg_orientation`), and it interchanges the two half-spinor labels.

These are the pointwise inputs for spin structures on oriented rank-two bundles: a spin lift of
an oriented Euclidean plane bundle is a square root of the corresponding Hermitian line bundle.
The positive-form coordinate isomorphism of `Spin(2)` with the circle, as topological groups, is
`CliffordAlgebra.realCliffordSpinTwoContinuousMulEquivCircle`; the isomorphism here is attached
to the orientation rather than to coordinates, and uses the negative form.

## Main definitions

* `Orientation.spinCircle o hQ`: the homomorphism `z ↦ Re z + Im z · ω` from the unit circle to
  the Spin group of an oriented Euclidean plane with `Q v = -‖v‖²`.
* `Orientation.spinCircleEquiv o hQ`: the same map, as an isomorphism `Circle ≃* Spin(Q)`.

## Main results

* `Orientation.coe_spinCircle` and `Orientation.spinCircle_eq_spinCircle`: the Clifford value of
  `z`, and its frame formula `Re z + Im z c(e₀) c(e₁)` for every positively oriented orthonormal
  basis.
* `Orientation.spinVectorAction_spinCircle`: `z` acts on `V` by `z²` for the complex structure `J`,
  and `Orientation.spinVectorAction_spinCircle_exp`: `exp (i θ)` acts as the rotation by `2θ`.
* `Orientation.ofBaseChangeAux_spinCircle`: in the complexified Clifford algebra,
  `z = Re z - i Im z Γ`.
* `Orientation.ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace_one` and
  `Orientation.ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace_neg_one`: `z` acts on the
  positive half-spinors by `z⁻¹` and on the negative ones by `z`.
* `Orientation.coe_spinGroupEquivNeg_spinCircle`: the corresponding element for the positive form
  is `Re z - Im z · ω₊`.
* `Orientation.spinCircle_neg_orientation`: reversing the orientation inverts the parameter.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and §5.
-/

public section

noncomputable section

open Module CliffordAlgebra Module.End
open scoped InnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 2)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 2)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- A positively oriented orthonormal basis of the plane. -/
private def frame : OrthonormalBasis (Fin 2) ℝ V :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)).adjustToOrientation o

private theorem frame_orientation : (o.frame).toBasis.orientation = o :=
  OrthonormalBasis.orientation_adjustToOrientation _ _

include hQ

/-- The volume element of the plane is `c(e₀) c(e₁)` for every positively oriented orthonormal
basis. -/
private theorem volumeElement_eq_ι_mul_ι {b : OrthonormalBasis (Fin 2) ℝ V}
    (hb : b.toBasis.orientation = o) : volumeElement Q o = ι Q (b 0) * ι Q (b 1) := by
  rw [volumeElement_eq o b hb (b.isOrthoᵢ_associated hQ)]
  simp [List.finRange_succ]

/-- **The circle subgroup of the Spin group of an oriented Euclidean plane**, for
`Q v = -‖v‖²`: the unit complex number `z` maps to `Re z + Im z · ω`, where `ω` is the volume
element (`Orientation.coe_spinCircle`). In a positively oriented orthonormal basis `(e₀, e₁)` this
is `Re z + Im z c(e₀) c(e₁)` (`Orientation.spinCircle_eq_spinCircle`). It is an isomorphism onto
`Spin(Q)` (`Orientation.spinCircleEquiv`). -/
def spinCircle : Circle →* spinGroup Q :=
  CliffordAlgebra.spinCircle Q (o.frame 0) (o.frame 1) (o.frame.isOrtho_apply hQ (by decide))
    (o.frame.map_apply_mul_map_apply hQ 0 1)

/-- The Clifford value of `o.spinCircle hQ z` is `Re z + Im z · ω`, with `ω` the volume element of
the orientation. -/
@[simp]
theorem coe_spinCircle (z : Circle) :
    (o.spinCircle hQ z : CliffordAlgebra Q) =
      algebraMap ℝ _ (z : ℂ).re + (z : ℂ).im • volumeElement Q o := by
  rw [spinCircle, CliffordAlgebra.coe_spinCircle, volumeElement_eq_ι_mul_ι o hQ o.frame_orientation]

/-- **Frame formula**: for every positively oriented orthonormal basis `(e₀, e₁)`, the circle
subgroup of the orientation is the circle subgroup `z ↦ Re z + Im z c(e₀) c(e₁)` of the pair
`(e₀, e₁)`. -/
theorem spinCircle_eq_spinCircle {b : OrthonormalBasis (Fin 2) ℝ V}
    (hb : b.toBasis.orientation = o) :
    o.spinCircle hQ = CliffordAlgebra.spinCircle Q (b 0) (b 1) (b.isOrtho_apply hQ (by decide))
      (b.map_apply_mul_map_apply hQ 0 1) := by
  ext z
  rw [coe_spinCircle, CliffordAlgebra.coe_spinCircle, volumeElement_eq_ι_mul_ι o hQ hb]

/-- Reversing the orientation inverts the parameter of the circle subgroup. -/
@[simp]
theorem spinCircle_neg_orientation (z : Circle) :
    (-o).spinCircle hQ z = o.spinCircle hQ z⁻¹ := by
  apply Subtype.ext
  rw [coe_spinCircle, coe_spinCircle, Circle.coe_inv_eq_conj, volumeElement_neg_orientation]
  simp

/-! ### The action on vectors -/

/-- **The tangent weight**: the circle element `z` acts on the plane by multiplication by `z²`
for the complex structure given by the quarter turn `J` of the orientation,
`v ↦ Re (z²) v + Im (z²) J v`. -/
theorem spinVectorAction_spinCircle (z : Circle) (v : V) :
    spinVectorAction Q (o.spinCircle hQ z) v =
      ((z : ℂ) ^ 2).re • v + ((z : ℂ) ^ 2).im • o.rightAngleRotation v := by
  let b := o.frame
  have hb : b.toBasis.orientation = o := o.frame_orientation
  have h : (spinVectorAction Q (o.spinCircle hQ z) : V →ₗ[ℝ] V) =
      ((z : ℂ) ^ 2).re • LinearMap.id + ((z : ℂ) ^ 2).im •
        (o.rightAngleRotation.toLinearEquiv : V →ₗ[ℝ] V) := by
    refine b.toBasis.ext fun i ↦ ?_
    fin_cases i
    · simp [spinCircle_eq_spinCircle o hQ hb, spinVectorAction_spinCircle_left,
        o.rightAngleRotation_basis_zero hb, hQ, b.orthonormal.1 0, sub_eq_add_neg]
    · simp [spinCircle_eq_spinCircle o hQ hb, spinVectorAction_spinCircle_right,
        o.rightAngleRotation_basis_one hb, hQ, b.orthonormal.1 1]
  simpa using LinearMap.congr_fun h v

/-- The circle element `exp (i θ)`, that is `cos θ + sin θ e₀ e₁`, acts on the plane as the
rotation by the angle `2θ`. -/
theorem spinVectorAction_spinCircle_exp (θ : ℝ) (v : V) :
    spinVectorAction Q (o.spinCircle hQ (Circle.exp θ)) v = o.rotation (2 * θ : ℝ) v := by
  have h : ((Circle.exp θ : ℂ)) ^ 2 = Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [Circle.coe_exp, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [spinVectorAction_spinCircle, h, o.rotation_apply, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-! ### The action on half-spinors -/

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

omit hQ in
/-- In the complexified Clifford algebra the volume element is `-i Γ`. -/
private theorem ofBaseChangeAux_volumeElement :
    ofBaseChangeAux ℂ Q (volumeElement Q o) = -(Complex.I • complexVolume Q o) := by
  rw [complexVolume_def, show (2 + 1) / 2 = 1 by rfl, pow_one, smul_smul, Complex.I_mul_I,
    neg_one_smul, neg_neg]

/-- In the complexified Clifford algebra the circle element `z` is `Re z - i Im z Γ`, with `Γ`
the chirality element of the orientation. -/
theorem ofBaseChangeAux_spinCircle (z : Circle) :
    ofBaseChangeAux ℂ Q (o.spinCircle hQ z) =
      ((z : ℂ).re : ℂ) • 1 - (Complex.I * (z : ℂ).im) • complexVolume Q o := by
  rw [coe_spinCircle, map_add, map_smul, AlgHom.commutes, ofBaseChangeAux_volumeElement,
    Algebra.algebraMap_eq_smul_one]
  -- Real scalars act on the complexified algebra through `ℝ → ℂ`.
  refine (congrArg₂ (· + ·) (algebraMap_smul ℂ (z : ℂ).re (1 : CliffordAlgebra (Q.baseChange ℂ)))
    (algebraMap_smul ℂ (z : ℂ).im (-(Complex.I • complexVolume Q o)))).symm.trans ?_
  rw [Complex.coe_algebraMap]
  module

/-- The circle element `z` acts on the `μ`-eigenspace of `Γ` by `Re z - i μ Im z`. -/
private theorem ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) (z : Circle) :
    ofBaseChangeAux ℂ Q (o.spinCircle hQ z) • ψ =
      (((z : ℂ).re : ℂ) - Complex.I * μ * (z : ℂ).im) • ψ := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ
  rw [ofBaseChangeAux_spinCircle, sub_smul, smul_assoc, one_smul, smul_assoc, hψ, smul_smul]
  module

/-- **The positive half-spinor weight**: the circle element `z` acts on the positive half-spinors
`{Γ = 1}` of every complex Clifford module by `z⁻¹`. -/
theorem ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace_one {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace 1) (z : Circle) :
    ofBaseChangeAux ℂ Q (o.spinCircle hQ z) • ψ = (z : ℂ)⁻¹ • ψ := by
  rw [ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace o hQ hψ, ← Circle.coe_inv,
    Circle.coe_inv_eq_conj]
  congr 1
  apply Complex.ext <;> simp

/-- **The negative half-spinor weight**: the circle element `z` acts on the negative half-spinors
`{Γ = -1}` of every complex Clifford module by `z`. -/
theorem ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace_neg_one {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-1)) (z : Circle) :
    ofBaseChangeAux ℂ Q (o.spinCircle hQ z) • ψ = (z : ℂ) • ψ := by
  rw [ofBaseChangeAux_spinCircle_smul_of_mem_eigenspace o hQ hψ]
  congr 1
  apply Complex.ext <;> simp

/-! ### The positive definite form -/

/-- **The bivector sign**: under the isomorphism `CliffordAlgebra.spinGroupEquivNeg` with the Spin
group of the positive definite form `-Q`, the circle element `Re z + Im z · ω` goes to
`Re z - Im z · ω₊`, where `ω₊` is the volume element of `-Q`. Thus `cos θ + sin θ e₀ e₁` goes to
`cos θ - sin θ e₀ e₁`. -/
theorem coe_spinGroupEquivNeg_spinCircle (z : Circle) :
    (spinGroupEquivNeg Q (o.spinCircle hQ z) : CliffordAlgebra (-Q)) =
      algebraMap ℝ _ (z : ℂ).re - (z : ℂ).im • volumeElement (-Q) o := by
  let b := o.frame
  have hb : b.toBasis.orientation = o := o.frame_orientation
  have hQb : Q (b 0) = -1 := by simp [hQ, b.orthonormal.1 0]
  -- The circle element is the product of `e₀` with `-Re z e₀ + Im z e₁`.
  have hx : (o.spinCircle hQ z : CliffordAlgebra Q) =
      ι Q (b 0) * ι Q (-((z : ℂ).re • b 0) + (z : ℂ).im • b 1) := by
    rw [coe_spinCircle, volumeElement_eq_ι_mul_ι o hQ hb]
    simp only [map_add, map_neg, map_smul, mul_add, mul_neg, mul_smul_comm, ι_sq_scalar, hQb]
    simp [Algebra.algebraMap_eq_smul_one]
  have hneg : (QuadraticMap.associated (-Q)).IsOrthoᵢ b.toBasis :=
    LinearMap.isOrthoᵢ_def.2 fun i j hij ↦ by
    rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply,
      LinearMap.isOrthoᵢ_def.1 (b.isOrthoᵢ_associated hQ) i j hij, neg_zero]
  rw [coe_spinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι Q hx, volumeElement_eq o b hb hneg]
  simp only [map_add, map_neg, map_smul, mul_add, mul_neg, mul_smul_comm, ι_sq_scalar]
  simp [List.finRange_succ, Algebra.algebraMap_eq_smul_one, hQb, sub_eq_add_neg, add_comm]

/-! ### The isomorphism with the circle -/

omit hQ in
/-- The coordinates of `r + s ω` in the Clifford basis of a positively oriented orthonormal basis
are `r` and `s`; in particular `r + s ω` determines `r` and `s`. -/
private theorem eq_of_algebraMap_add_smul_volumeElement_eq {r s r' s' : ℝ}
    (h : algebraMap ℝ (CliffordAlgebra Q) r + s • volumeElement Q o =
      algebraMap ℝ _ r' + s' • volumeElement Q o) : r = r' ∧ s = s' := by
  let B := basis Q o.frame.toBasis
  have hω : volumeElement Q o = B Finset.univ := volumeElement_eq_basis o _ o.frame_orientation
  have h₁ : (algebraMap ℝ (CliffordAlgebra Q) : ℝ → _) = fun t ↦ t • B ∅ := by
    ext t
    simp [B, Algebra.algebraMap_eq_smul_one]
  have hne : (∅ : Finset (Fin 2)) ≠ Finset.univ := Finset.univ_nonempty.ne_empty.symm
  have h' := congrArg B.repr h
  rw [hω, h₁] at h'
  constructor
  · simpa [Finsupp.single_apply, hne] using congrArg (· ∅) h'
  · simpa [Finsupp.single_apply, hne] using congrArg (· Finset.univ) h'

/-- The circle subgroup is injective. -/
theorem spinCircle_injective : Function.Injective (o.spinCircle hQ) := by
  intro z z' h
  have h' := congrArg ((↑) : spinGroup Q → CliffordAlgebra Q) h
  rw [coe_spinCircle, coe_spinCircle] at h'
  obtain ⟨hre, him⟩ := eq_of_algebraMap_add_smul_volumeElement_eq o h'
  exact Circle.ext (Complex.ext hre him)

/-- Since `ω² = -1`, the elements `r + s ω` multiply as the complex numbers `r + s i`. -/
private theorem algebraMap_add_smul_volumeElement_mul (a b c d : ℝ) :
    (algebraMap ℝ (CliffordAlgebra Q) a + b • volumeElement Q o) *
        (algebraMap ℝ _ c + d • volumeElement Q o) =
      algebraMap ℝ _ (a * c - b * d) + (a * d + b * c) • volumeElement Q o := by
  have hsq : volumeElement Q o * volumeElement Q o = -1 := by
    rw [volumeElement_mul_self o hQ]
    norm_num
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hsq]
  module

/-- Every element of the Spin group of the plane is `r + s ω` with `r² + s² = 1`. -/
private theorem exists_coe_eq_algebraMap_add_smul_volumeElement (x : spinGroup Q) :
    ∃ r s : ℝ, r ^ 2 + s ^ 2 = 1 ∧
      (x : CliffordAlgebra Q) = algebraMap ℝ _ r + s • volumeElement Q o := by
  let b := o.frame
  have hb : b.toBasis.orientation = o := o.frame_orientation
  have hQb : Q (b 0) = -1 := by simp [hQ, b.orthonormal.1 0]
  let _ : Invertible (Q (b 0)) := invertibleOfNonzero (by rw [hQb]; norm_num)
  obtain ⟨w, hw⟩ := (mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two Q Fact.out (b 0)).1
    (spinGroup.mem_even x.2)
  -- Expand `w` in the basis: `e₀ (α e₀ + β e₁) = -α + β ω`.
  have hxω : (x : CliffordAlgebra Q) =
      algebraMap ℝ _ (-⟪b 0, w⟫_ℝ) + ⟪b 1, w⟫_ℝ • volumeElement Q o := by
    conv_lhs => rw [hw, ← b.sum_repr' w, Fin.sum_univ_two]
    rw [volumeElement_eq_ι_mul_ι o hQ hb]
    simp only [map_add, map_smul, mul_add, mul_smul_comm, ι_sq_scalar, hQb]
    simp [Algebra.algebraMap_eq_smul_one]
  refine ⟨-⟪b 0, w⟫_ℝ, ⟪b 1, w⟫_ℝ, ?_, hxω⟩
  -- The spinor norm `x x⋆ = r² + s²` is one.
  have hn := spinGroup.mul_star_self_of_mem x.2
  have hstar : star (volumeElement Q o) = -volumeElement Q o := by
    rw [star_volumeElement]
    norm_num
  rw [hxω, star_add, CliffordAlgebra.star_smul, hstar, star_algebraMap, smul_neg, ← neg_smul,
    algebraMap_add_smul_volumeElement_mul o hQ, ← map_one (algebraMap ℝ (CliffordAlgebra Q)),
    ← zero_add (algebraMap ℝ (CliffordAlgebra Q) 1), ← zero_smul ℝ (volumeElement Q o),
    add_comm (0 • _)] at hn
  have h := (eq_of_algebraMap_add_smul_volumeElement_eq o hn).1
  linear_combination h

/-- The circle subgroup is onto the Spin group of the plane. -/
theorem spinCircle_surjective : Function.Surjective (o.spinCircle hQ) := by
  intro x
  obtain ⟨r, s, hrs, hx⟩ := exists_coe_eq_algebraMap_add_smul_volumeElement o hQ x
  let z : Circle := ⟨r + s * Complex.I, mem_sphere_zero_iff_norm.2 (by
    rw [Complex.norm_add_mul_I, hrs, Real.sqrt_one])⟩
  refine ⟨z, Subtype.ext ?_⟩
  rw [coe_spinCircle, hx]
  simp [z]

/-- **The Spin group of an oriented Euclidean plane is the circle**: for `Q v = -‖v‖²`, the map
`z ↦ Re z + Im z · ω` is an isomorphism from the unit circle onto `Spin(Q)`. -/
def spinCircleEquiv : Circle ≃* spinGroup Q :=
  MulEquiv.ofBijective (o.spinCircle hQ) ⟨o.spinCircle_injective hQ, o.spinCircle_surjective hQ⟩

@[simp]
theorem spinCircleEquiv_apply (z : Circle) : o.spinCircleEquiv hQ z = o.spinCircle hQ z :=
  (rfl)

end Orientation
