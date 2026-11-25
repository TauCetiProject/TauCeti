/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
-- Private: eigenspace transport along intertwiners and projection congruence are used only inside
-- proofs.
import TauCeti.LinearAlgebra.Eigenspace.Transport
import TauCeti.LinearAlgebra.Projection

/-!
# The chirality operator of a real Clifford action

Let `V` be an oriented real inner product space of dimension `n`, `Q` a quadratic form on `V`, and
`ρ : Cℓ(V, Q) → End_ℂ(S)` a real algebra map into the complex endomorphisms of a complex vector
space `S`, with Clifford multiplication `c(v) = ρ (ι Q v)`. (The algebraic formulas for `ρ_ℂ(Γ)`
and its commutation/anticommutation relations hold for real algebra maps into any complex algebra.)
Its complex-linear extension `ρ_ℂ = CliffordAlgebra.liftBaseChange ℂ Q ρ` makes `S` a module over
the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)`, on which the vector `1 ⊗ v` acts by `c(v)`
(`CliffordAlgebra.liftBaseChange_ι_tmul`). The normalized complex volume element `Γ`
(`CliffordAlgebra.complexVolume`) of that algebra therefore acts on `S` by

  `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ ρ(vol) = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`

for the real volume element `vol` (`CliffordAlgebra.volumeElement`) and every positively oriented
orthonormal basis `e` that is orthogonal for `Q` (in particular every positively oriented
orthonormal basis when `Q v = -‖v‖²`). In even dimension `n = 2ℓ` the factor is `i ^ ℓ`, and this
operator anticommutes with every real generator `c(v)` and odd element of `Cℓ(V, Q)`, while in odd
dimension it commutes with the whole image of `ρ`, and in every dimension it commutes with the even
subalgebra.

For `Q v = -‖v‖²`, `ρ_ℂ(Γ)` is an involution (`CliffordAlgebra.map_complexVolume_mul_self`,
`AlgHom.involutive_complexVolume`) whose `±1`-eigenspaces `S⁺` and `S⁻` are complementary by
`(liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hQ`, with explicit projections
`2⁻¹ • (1 ± ρ_ℂ(Γ))`. By contrast, for `Q = 0` in positive dimension both `±1`-eigenspaces vanish.

On a complex inner product space, `ρ_ℂ` is a `*`-representation for the conjugate-linear Clifford
involution `CliffordAlgebra.conjStar` exactly when the real generators act skew-Hermitianly
(`CliffordAlgebra.inner_liftBaseChange_eq_conjStar_iff`,
`CliffordAlgebra.adjoint_liftBaseChange_eq_liftBaseChange_conjStar_iff`), the second clause of the
geometric convention `AlgHom.IsGeometricClifford`
(`AlgHom.IsGeometricClifford.inner_liftBaseChange_apply_left`). Since `Γ` is fixed by `conjStar`,
under the geometric convention `ρ_ℂ(Γ)` is self-adjoint, the half-spinor spaces are orthogonal
(`S⁺ ⟂ S⁻`), and norms split orthogonally as `‖ψ‖² = ‖ψ⁺‖² + ‖ψ⁻‖²`.

## Main results

* `CliffordAlgebra.liftBaseChange_complexVolume`, `CliffordAlgebra.liftBaseChange_complexVolume_eq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_of_neg_norm_sq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_two_mul_eq_of_neg_norm_sq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_prod_pairs_of_neg_norm_sq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_prod_pairs_mul_of_neg_norm_sq`: real-action and
  orthonormal-frame formulas for `ρ_ℂ(Γ)`.
* `CliffordAlgebra.liftBaseChange_complexVolume_mul_map_ι`,
  `CliffordAlgebra.liftBaseChange_complexVolume_mul_map_of_mem_odd`,
  `CliffordAlgebra.commute_liftBaseChange_complexVolume_map_of_mem_even`,
  `CliffordAlgebra.commute_liftBaseChange_complexVolume_map_of_odd`: parity and commutation laws
  against real Clifford elements.
* `CliffordAlgebra.projection_eigenspace_liftBaseChange_complexVolume_apply`,
  `CliffordAlgebra.projection_eigenspace_liftBaseChange_complexVolume_neg_one_apply`: the explicit
  half-spin projections `2⁻¹ • (1 ± Γ)` onto `S⁺` and `S⁻` for `Q v = -‖v‖²`.
* `CliffordAlgebra.map_ι_apply_mem_eigenspace_liftBaseChange_complexVolume_neg`,
  `CliffordAlgebra.map_mem_eigenspace_liftBaseChange_complexVolume_neg_of_mem_odd`,
  `CliffordAlgebra.finrank_eigenspace_liftBaseChange_complexVolume_neg`: eigenspace exchange and
  equal complex dimensions in even positive dimension.
* `CliffordAlgebra.eigenspace_liftBaseChange_complexVolume_eq_bot_of_forall_eq_zero`: negative
  control for `Q = 0` in positive dimension.
* `CliffordAlgebra.comp_liftBaseChange_complexVolume_eq`,
  `CliffordAlgebra.map_eigenspace_liftBaseChange_complexVolume`: naturality along intertwining
  maps and orientation-preserving norm-preserving isometries.
* `CliffordAlgebra.isSymmetric_liftBaseChange_complexVolume`,
  `CliffordAlgebra.adjoint_liftBaseChange_complexVolume`,
  `CliffordAlgebra.isSelfAdjoint_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.isSymmetric_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.inner_eigenspace_liftBaseChange_complexVolume_eq_zero`,
  `AlgHom.IsGeometricClifford.norm_sq_eq_add_norm_sq_projection_complexVolume`,
  `AlgHom.IsGeometricClifford.isOrtho_eigenspace_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.isSelfAdjoint_liftBaseChange_complexVolume`: self-adjointness of
  `ρ_ℂ(Γ)`, orthogonality `S⁺ ⟂ S⁻`, and Pythagorean norm splitting.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, §12.1, pp. 632–633, for the chirality
  operator `Γ = i ^ ℓ c(e₁) ⋯ c(e₂ℓ)` of a Clifford module.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Module Module.End TauCeti
open scoped InnerProductSpace TensorProduct

namespace CliffordAlgebra

section Algebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V}

section Semiring

variable {B : Type*} [Semiring B] [Algebra ℂ B] [Algebra ℝ B] [IsScalarTower ℝ ℂ B]

section GeneralDim

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **The chirality operator of a real Clifford action**: the complex-linear extension of `ρ` sends
the normalized complex volume element `Γ` to `i ^ ⌊(n + 1) / 2⌋ ρ(vol)`, for the real volume
element `vol`. In dimension `2ℓ` the factor is `i ^ ℓ`. -/
theorem liftBaseChange_complexVolume :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • ρ (volumeElement Q o) := by
  rw [complexVolume_def, map_smul, liftBaseChange_ofBaseChangeAux]

/-- **Frame formula for the chirality operator**: `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` for
every positively oriented orthonormal basis `e` that is orthogonal for `Q`, for instance for
`Q v = -‖v‖²` (`OrthonormalBasis.isOrthoᵢ_associated`). -/
theorem liftBaseChange_complexVolume_eq (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • (((List.finRange n).map b).map fun v ↦ ρ (ι Q v)).prod := by
  rw [liftBaseChange_complexVolume, volumeElement_eq o b hb hQb, map_list_prod, List.map_map,
    Function.comp_def]

/-- For `Q v = -‖v‖²`, every positively oriented orthonormal basis gives the frame formula
`i ^ ⌊(n + 1) / 2⌋ c(b₁) ⋯ c(bₙ)`. -/
theorem liftBaseChange_complexVolume_eq_of_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • (((List.finRange n).map b).map fun v ↦ ρ (ι Q v)).prod :=
  liftBaseChange_complexVolume_eq o ρ b hb (b.isOrthoᵢ_associated hQ)

/-- **In even dimension `Γ` intertwines the real grade involution**:
`Γ (ρ x) = ρ (involute x) Γ`. -/
theorem liftBaseChange_complexVolume_mul_map_eq_involute (hn : Even n) (x : CliffordAlgebra Q) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ x =
      ρ (involute x) * liftBaseChange ℂ Q ρ (complexVolume Q o) := by
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) Q ρ x, ← map_mul,
    complexVolume_mul_eq_involute_mul o hn, ← ofBaseChangeAux_involute, map_mul,
    liftBaseChange_ofBaseChangeAux]

/-- **In odd dimension `Γ` commutes with the entire image of the real Clifford algebra.** -/
theorem commute_liftBaseChange_complexVolume_map_of_odd (hn : Odd n) (x : CliffordAlgebra Q) :
    Commute (liftBaseChange ℂ Q ρ (complexVolume Q o)) (ρ x) := by
  rw [Commute, SemiconjBy, ← liftBaseChange_ofBaseChangeAux (A := ℂ) Q ρ x, ← map_mul, ← map_mul,
    Subalgebra.mem_center_iff.mp (complexVolume_mem_center o hn)]

/-- `Γ` commutes with every even element of the real Clifford algebra, in every dimension. -/
theorem commute_liftBaseChange_complexVolume_map_of_mem_even {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) :
    Commute (liftBaseChange ℂ Q ρ (complexVolume Q o)) (ρ x) := by
  simpa using (commute_complexVolume_of_mem_even o
    (ofBaseChangeAux_mem_evenOdd (A := ℂ) hx)).map (liftBaseChange ℂ Q ρ)

/-- For `Q = 0` in positive dimension, the image of `Γ` squares to `0`. -/
theorem liftBaseChange_complexVolume_mul_self_of_forall_eq_zero (hn : n ≠ 0) (hQ : ∀ v, Q v = 0) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * liftBaseChange ℂ Q ρ (complexVolume Q o) = 0 := by
  rw [← map_mul, complexVolume_mul_self_of_forall_eq_zero o hn hQ, map_zero]

end GeneralDim

section EvenDim

variable {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ)] (o : Orientation ℝ V (Fin (2 * ℓ)))
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **Even-dimensional frame formula**: in dimension `2ℓ`, for any positively oriented orthonormal
basis `b` orthogonal for `Q`, `Γ` maps to `i ^ ℓ c(b₁) ⋯ c(b₂ℓ)`. -/
theorem liftBaseChange_complexVolume_two_mul_eq (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ℓ • (((List.finRange (2 * ℓ)).map b).map fun v ↦ ρ (ι Q v)).prod := by
  rw [liftBaseChange_complexVolume_eq o ρ b hb hQb, show (2 * ℓ + 1) / 2 = ℓ by omega]

/-- **Even-dimensional frame formula for `Q v = -‖v‖²`**: in any positively oriented orthonormal
basis `b`, `Γ` maps to `i ^ ℓ c(b₁) ⋯ c(b₂ℓ)`. -/
theorem liftBaseChange_complexVolume_two_mul_eq_of_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V) (hb : b.toBasis.orientation = o) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ℓ • (((List.finRange (2 * ℓ)).map b).map fun v ↦ ρ (ι Q v)).prod :=
  liftBaseChange_complexVolume_two_mul_eq o ρ b hb (b.isOrthoᵢ_associated hQ)

/-- **Paired-product formula in dimension `2ℓ`**: `Γ` maps to
`i ^ ℓ (c(b₁) c(b₂)) ⋯ (c(b₂ℓ₋₁) c(b₂ℓ))`. -/
theorem liftBaseChange_complexVolume_eq_prod_pairs (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) = Complex.I ^ ℓ • (List.ofFn fun k : Fin ℓ ↦
      ρ (ι Q (b ⟨2 * k, by omega⟩)) * ρ (ι Q (b ⟨2 * k + 1, by omega⟩))).prod := by
  rw [complexVolume_eq_prod_pairs b hb hQb, map_smul, map_list_prod, List.map_ofFn]
  simp [Function.comp_def]

/-- **Paired-product formula in dimension `2ℓ` for `Q v = -‖v‖²`**: in any positively oriented
orthonormal basis `b`, `Γ` maps to `i ^ ℓ (c(b₁) c(b₂)) ⋯ (c(b₂ℓ₋₁) c(b₂ℓ))`. -/
theorem liftBaseChange_complexVolume_eq_prod_pairs_of_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V) (hb : b.toBasis.orientation = o) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) = Complex.I ^ ℓ • (List.ofFn fun k : Fin ℓ ↦
      ρ (ι Q (b ⟨2 * k, by omega⟩)) * ρ (ι Q (b ⟨2 * k + 1, by omega⟩))).prod :=
  liftBaseChange_complexVolume_eq_prod_pairs o ρ b hb (b.isOrthoᵢ_associated hQ)

end EvenDim

section OddDim

variable {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ + 1)] (o : Orientation ℝ V (Fin (2 * ℓ + 1)))
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **Paired-product formula in odd dimension `2ℓ + 1`**: `ω_ℂ` maps to
`i ^ (ℓ + 1) (c(b₁) c(b₂)) ⋯ (c(b₂ℓ₋₁) c(b₂ℓ)) c(b₂ℓ₊₁)`. -/
theorem liftBaseChange_complexVolume_eq_prod_pairs_mul
    (b : OrthonormalBasis (Fin (2 * ℓ + 1)) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) = Complex.I ^ (ℓ + 1) • ((List.ofFn fun k : Fin ℓ ↦
      ρ (ι Q (b ⟨2 * k, by omega⟩)) * ρ (ι Q (b ⟨2 * k + 1, by omega⟩))).prod *
      ρ (ι Q (b (Fin.last (2 * ℓ))))) := by
  rw [complexVolume_eq_prod_pairs_mul b hb hQb, map_smul, map_mul, map_list_prod, List.map_ofFn]
  simp [Function.comp_def]

/-- **Paired-product formula in odd dimension `2ℓ + 1` for `Q v = -‖v‖²`**: in any positively
oriented orthonormal basis `b`, `ω_ℂ` maps to
`i ^ (ℓ + 1) (c(b₁) c(b₂)) ⋯ (c(b₂ℓ₋₁) c(b₂ℓ)) c(b₂ℓ₊₁)`. -/
theorem liftBaseChange_complexVolume_eq_prod_pairs_mul_of_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin (2 * ℓ + 1)) ℝ V) (hb : b.toBasis.orientation = o) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) = Complex.I ^ (ℓ + 1) • ((List.ofFn fun k : Fin ℓ ↦
      ρ (ι Q (b ⟨2 * k, by omega⟩)) * ρ (ι Q (b ⟨2 * k + 1, by omega⟩))).prod *
      ρ (ι Q (b (Fin.last (2 * ℓ))))) :=
  liftBaseChange_complexVolume_eq_prod_pairs_mul o ρ b hb (b.isOrthoᵢ_associated hQ)

end OddDim

end Semiring

section Ring

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))
  {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℝ B] [IsScalarTower ℝ ℂ B]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **In even dimension the chirality operator anticommutes with Clifford multiplication**:
`ρ_ℂ(Γ) c(v) = -c(v) ρ_ℂ(Γ)`. -/
theorem liftBaseChange_complexVolume_mul_map_ι (hn : Even n) (v : V) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ (ι Q v) =
      -(ρ (ι Q v) * liftBaseChange ℂ Q ρ (complexVolume Q o)) := by
  simpa only [liftBaseChange_ι_tmul, one_smul] using
    map_complexVolume_mul_map_ι o hn (liftBaseChange ℂ Q ρ) (1 ⊗ₜ v)

/-- In even dimension `Γ` anticommutes with every odd element of the real Clifford algebra. -/
theorem liftBaseChange_complexVolume_mul_map_of_mem_odd (hn : Even n) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 1) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ x =
      -(ρ x * liftBaseChange ℂ Q ρ (complexVolume Q o)) := by
  rw [liftBaseChange_complexVolume_mul_map_eq_involute o ρ hn, involute_eq_of_mem_odd hx, map_neg,
    neg_mul]

end Ring

end Algebra

/-! ### Chirality eigenspaces of a real Clifford action -/

section BaseChangeModule

variable {V S : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [AddCommGroup S] [Module ℂ S] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- The `CliffordAlgebra (Q.baseChange ℂ)`-module structure on `S` induced by `liftBaseChange`. -/
@[instance_reducible]
private def compBaseChangeModule : Module (CliffordAlgebra (Q.baseChange ℂ)) S :=
  Module.compHom S (liftBaseChange ℂ Q ρ).toRingHom

/-- Scalar multiplication under `compBaseChangeModule` applies `liftBaseChange ℂ Q ρ`. -/
private theorem compBaseChangeModule_smul (a : CliffordAlgebra (Q.baseChange ℂ)) (ψ : S) :
    letI := compBaseChangeModule ρ
    a • ψ = liftBaseChange ℂ Q ρ a ψ :=
  (rfl)

/-- Scalar-tower compatibility of `compBaseChangeModule` over `ℂ`. -/
private theorem compBaseChangeScalarTower :
    letI := compBaseChangeModule ρ
    IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S := by
  let := compBaseChangeModule ρ
  refine IsScalarTower.of_algebraMap_smul fun z ψ ↦ ?_
  rw [compBaseChangeModule_smul, AlgHom.commutes, Module.algebraMap_end_apply]

/-- Left scalar multiplication under `compBaseChangeModule` as a `ℂ`-linear endomorphism equals
`liftBaseChange ℂ Q ρ`. -/
private theorem lsmul_compBaseChangeModule (a : CliffordAlgebra (Q.baseChange ℂ)) :
    letI := compBaseChangeModule ρ
    haveI := compBaseChangeScalarTower ρ
    Algebra.lsmul ℂ ℂ S a = liftBaseChange ℂ Q ρ a := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  ext ψ
  simp only [Algebra.lsmul_coe]
  exact compBaseChangeModule_smul ρ a ψ

end BaseChangeModule

section Module

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S]

section RankZero

variable [Fact (finrank ℝ V = 0)] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- In rank zero with the positive orientation, `Γ = 1`, so its `+1`-eigenspace is all of `S`. -/
theorem eigenspace_liftBaseChange_complexVolume_positiveOrientation_one :
    (liftBaseChange ℂ Q ρ
      (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)))).eigenspace 1 = ⊤ := by
  ext ψ
  simp

/-- In rank zero with the positive orientation, `Γ = 1`, so its `-1`-eigenspace is `⊥`. -/
theorem eigenspace_liftBaseChange_complexVolume_positiveOrientation_neg_one :
    (liftBaseChange ℂ Q ρ
      (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)))).eigenspace (-1) = ⊥ := by
  ext ψ
  simp only [mem_eigenspace_iff, complexVolume_positiveOrientation, map_one, one_apply_eq_self,
    neg_smul, one_smul, Submodule.mem_bot]
  have := HasUniqueDiv.of_isTorsionFree ℂ S
  exact self_eq_neg

end RankZero

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- Reversing the orientation negates `Γ` and therefore exchanges its `μ`- and `-μ`-eigenspaces. -/
theorem eigenspace_liftBaseChange_complexVolume_neg_orientation (μ : ℂ) :
    (liftBaseChange ℂ Q ρ (complexVolume Q (-o))).eigenspace μ =
      (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ) := by
  ext ψ
  simp [neg_eq_iff_eq_neg]

/-- In even dimension an odd element of the real Clifford algebra maps the `μ`-eigenspace of `Γ`
into the `-μ`-eigenspace. -/
theorem map_mem_eigenspace_liftBaseChange_complexVolume_neg_of_mem_odd (hn : Even n)
    {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 1) {μ : ℂ} {ψ : S}
    (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ x ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ] at hψ ⊢
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) Q ρ x, ← compBaseChangeModule_smul ρ]
  exact smul_mem_eigenspace_complexVolume_neg_of_mem_odd o hn
    (ofBaseChangeAux_mem_evenOdd (A := ℂ) hx) hψ

/-- **Clifford multiplication exchanges the half-spinors**: in even dimension, `c(v)` maps the
`μ`-eigenspace of `ρ_ℂ(Γ)` into its `-μ`-eigenspace. -/
theorem map_ι_apply_mem_eigenspace_liftBaseChange_complexVolume_neg (hn : Even n) (v : V)
    {μ : ℂ} {ψ : S} (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ (ι Q v) ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ) := by
  rw [mem_eigenspace_iff] at hψ ⊢
  rw [← mul_apply_eq_comp, liftBaseChange_complexVolume_mul_map_ι o ρ hn, LinearMap.neg_apply,
    mul_apply_eq_comp, hψ, map_smul, neg_smul]

/-- In odd dimension every element of the real Clifford algebra preserves each eigenspace of `Γ`. -/
theorem map_mem_eigenspace_liftBaseChange_complexVolume_of_odd (hn : Odd n)
    (x : CliffordAlgebra Q) {μ : ℂ} {ψ : S}
    (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ x ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ] at hψ ⊢
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) Q ρ x, ← compBaseChangeModule_smul ρ]
  exact smul_mem_eigenspace_complexVolume_of_odd o hn (ofBaseChangeAux ℂ Q x) hψ

/-- Every even element of the real Clifford algebra preserves each eigenspace of `Γ`, in any
dimension. -/
theorem map_mem_eigenspace_liftBaseChange_complexVolume_of_mem_even {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) {μ : ℂ} {ψ : S}
    (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ x ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ] at hψ ⊢
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) Q ρ x, ← compBaseChangeModule_smul ρ]
  exact smul_mem_eigenspace_complexVolume_of_mem_even o
    (ofBaseChangeAux_mem_evenOdd (A := ℂ) hx) hψ

/-- **Equal dimension of opposite eigenspaces**: in even positive dimension, for every quadratic
form `Q` and every `μ : ℂ`, the `-μ`- and `μ`-eigenspaces of `Γ` on `S` have equal complex
dimension. -/
theorem finrank_eigenspace_liftBaseChange_complexVolume_neg (hn : Even n) (hn0 : n ≠ 0) (μ : ℂ) :
    finrank ℂ ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ)) =
      finrank ℂ ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ]
  exact finrank_eigenspace_complexVolume_neg (E := S) o hn hn0 μ

/-- **Negative control for `Q = 0`**: in positive dimension, when `Q = 0`, `Γ² = 0`, so every
nonzero eigenvalue has trivial eigenspace. In particular both `±1`-eigenspaces are `⊥` and fail to
be complementary on any nontrivial module. -/
theorem eigenspace_liftBaseChange_complexVolume_eq_bot_of_forall_eq_zero (hn0 : n ≠ 0)
    (hQ : ∀ v, Q v = 0) {μ : ℂ} (hμ : μ ≠ 0) :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ = ⊥ := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ]
  exact eigenspace_complexVolume_eq_bot_of_forall_eq_zero (E := S) o hn0 hQ hμ

section Naturality

variable {V' F : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  [Fact (finrank ℝ V' = n)] {Q' : QuadraticForm ℝ V'} {o' : Orientation ℝ V' (Fin n)}
  [AddCommGroup F] [Module ℂ F] {ρ' : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ F}
  {e : Q.IsometryEquiv Q'} {o} {ρ}

/-- A complex-linear map `U : S →ₗ[ℂ] F` intertwining the real Clifford generators along a
norm-preserving quadratic isometry `e` with `o.map (Fin n) e = o'` intertwines the chirality
operators. -/
theorem comp_liftBaseChange_complexVolume_eq {U : S →ₗ[ℂ] F} (he : ∀ v, ‖e v‖ = ‖v‖)
    (ho : o.map (Fin n) e.toLinearEquiv = o')
    (hU : ∀ (v : V) (ψ : S), U (ρ (ι Q v) ψ) = ρ' (ι Q' (e v)) (U ψ)) :
    U ∘ₗ liftBaseChange ℂ Q ρ (complexVolume Q o) =
      liftBaseChange ℂ Q' ρ' (complexVolume Q' o') ∘ₗ U := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  let := compBaseChangeModule ρ'
  have := compBaseChangeScalarTower ρ'
  rw [← lsmul_compBaseChangeModule ρ, ← lsmul_compBaseChangeModule ρ']
  refine comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp (E := S) (F := F) he ho fun v ψ ↦ ?_
  rw [compBaseChangeModule_smul ρ, compBaseChangeModule_smul ρ']
  simp [hU]

/-- An intertwiner as in `CliffordAlgebra.comp_liftBaseChange_complexVolume_eq` preserves each
chirality eigenspace. -/
theorem apply_mem_eigenspace_liftBaseChange_complexVolume {U : S →ₗ[ℂ] F} (he : ∀ v, ‖e v‖ = ‖v‖)
    (ho : o.map (Fin n) e.toLinearEquiv = o')
    (hU : ∀ (v : V) (ψ : S), U (ρ (ι Q v) ψ) = ρ' (ι Q' (e v)) (U ψ))
    {μ : ℂ} {ψ : S} (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    U ψ ∈ (liftBaseChange ℂ Q' ρ' (complexVolume Q' o')).eigenspace μ :=
  mapsTo_genEigenspace_of_comp U (comp_liftBaseChange_complexVolume_eq he ho hU).symm μ 1 hψ

/-- A complex-linear equivalence intertwining the real Clifford generators along a norm-preserving
orientation-preserving quadratic isometry maps each chirality eigenspace onto the corresponding
chirality eigenspace of the target. -/
theorem map_eigenspace_liftBaseChange_complexVolume {U : S ≃ₗ[ℂ] F} (he : ∀ v, ‖e v‖ = ‖v‖)
    (ho : o.map (Fin n) e.toLinearEquiv = o')
    (hU : ∀ (v : V) (ψ : S), U (ρ (ι Q v) ψ) = ρ' (ι Q' (e v)) (U ψ)) (μ : ℂ) :
    ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ).map U.toLinearMap =
      (liftBaseChange ℂ Q' ρ' (complexVolume Q' o')).eigenspace μ := by
  have h := comp_liftBaseChange_complexVolume_eq (U := U.toLinearMap) he ho hU
  rw [eigenspace_eq_comap_of_intertwine (e := U)
    (g := liftBaseChange ℂ Q' ρ' (complexVolume Q' o')) (LinearMap.congr_fun h) μ]
  exact Submodule.map_comap_eq_of_surjective U.surjective _

end Naturality

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **The positive chirality projection** onto `S⁺` along `S⁻` is `2⁻¹ • (1 + Γ)`. -/
theorem projection_eigenspace_liftBaseChange_complexVolume_apply (ψ : S) :
    Submodule.projection _ _ ((liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hQ) ψ =
      (2 : ℂ)⁻¹ • (ψ + liftBaseChange ℂ Q ρ (complexVolume Q o) ψ) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  have hfg := (lsmul_compBaseChangeModule ρ (complexVolume Q o)).symm
  have hp := Submodule.projection_congr
    (congrArg (Module.End.eigenspace · 1) hfg) (congrArg (Module.End.eigenspace · (-1)) hfg)
    ((liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hQ)
    (isCompl_eigenspace_complexVolume (Q := Q) (E := S) o hQ)
  rw [LinearMap.congr_fun hp ψ, projection_eigenspace_complexVolume_apply (Q := Q) (E := S) o hQ,
    compBaseChangeModule_smul]
  simp [halfOneAdd_def, invOf_eq_inv]

/-- **The negative chirality projection** onto `S⁻` along `S⁺` is `2⁻¹ • (1 - Γ)`. -/
theorem projection_eigenspace_liftBaseChange_complexVolume_neg_one_apply (ψ : S) :
    Submodule.projection _ _
        ((liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hQ).symm ψ =
      (2 : ℂ)⁻¹ • (ψ - liftBaseChange ℂ Q ρ (complexVolume Q o) ψ) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  have hfg := (lsmul_compBaseChangeModule ρ (complexVolume Q o)).symm
  have hp := Submodule.projection_congr
    (congrArg (Module.End.eigenspace · (-1)) hfg) (congrArg (Module.End.eigenspace · 1) hfg)
    ((liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hQ).symm
    (isCompl_eigenspace_complexVolume (Q := Q) (E := S) o hQ).symm
  rw [LinearMap.congr_fun hp ψ,
    projection_eigenspace_complexVolume_neg_one_apply (Q := Q) (E := S) o hQ,
    compBaseChangeModule_smul]
  simp [halfOneAdd_def, invOf_eq_inv, sub_eq_add_neg]

end Form

end Module

/-! ### Self-adjointness of the chirality operator -/

section ChiralitySymmetry

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

/-- Whenever real vectors act skew-Hermitianly on `S`, the chirality operator
`liftBaseChange ℂ Q ρ (complexVolume Q o)` is symmetric for the inner product of `S` (for every
quadratic form `Q` and without assuming `S` finite-dimensional). -/
theorem isSymmetric_liftBaseChange_complexVolume
    [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y)) :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).IsSymmetric := fun x y ↦ by
  rw [(inner_liftBaseChange_eq_conjStar_iff ρ).mpr hρ, conjStar_complexVolume]

/-- On a finite-dimensional Hermitian module with skew-adjoint real generators, the chirality
operator equals its own adjoint. -/
theorem adjoint_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v)) :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).adjoint =
      liftBaseChange ℂ Q ρ (complexVolume Q o) := by
  rw [adjoint_liftBaseChange_eq_liftBaseChange_conjStar_iff.mpr hρ, conjStar_complexVolume]

/-- On a finite-dimensional Hermitian module with skew-adjoint real generators, the chirality
operator is self-adjoint (`IsSelfAdjoint`). -/
theorem isSelfAdjoint_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v)) :
    IsSelfAdjoint (liftBaseChange ℂ Q ρ (complexVolume Q o)) :=
  LinearMap.isSelfAdjoint_iff'.mpr (adjoint_liftBaseChange_complexVolume o hρ)

end ChiralitySymmetry

end CliffordAlgebra

namespace AlgHom.IsGeometricClifford

open CliffordAlgebra

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V}

section SeminormedS

variable [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
  (o : Orientation ℝ V (Fin n))
include hρ

/-- **The chirality operator of a geometric action is self-adjoint**: `ρ_ℂ(Γ)` is symmetric,
since `Γ` is fixed by `conjStar`. -/
theorem isSymmetric_liftBaseChange_complexVolume :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).IsSymmetric :=
  CliffordAlgebra.isSymmetric_liftBaseChange_complexVolume o hρ.inner_map_ι_apply_left

/-- **Orthogonality of positive and negative half-spinors**: any `+1`-eigenvector and
`-1`-eigenvector of `liftBaseChange ℂ Q ρ (complexVolume Q o)` are orthogonal. -/
theorem inner_eigenspace_liftBaseChange_complexVolume_eq_zero {ψ₁ ψ₂ : S}
    (h₁ : ψ₁ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1)
    (h₂ : ψ₂ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1)) :
    ⟪ψ₁, ψ₂⟫_ℂ = 0 := by
  rw [Module.End.mem_eigenspace_iff, one_smul] at h₁
  rw [Module.End.mem_eigenspace_iff, neg_one_smul] at h₂
  have hsymm := hρ.isSymmetric_liftBaseChange_complexVolume o ψ₁ ψ₂
  rw [h₁, h₂, inner_neg_right] at hsymm
  exact self_eq_neg.mp hsymm

/-- **Pythagorean chirality decomposition**: on a geometric Hermitian Clifford module, the squared
norm of every spinor `ψ` is the sum of the squared norms of its positive and negative chiral
projections. -/
theorem norm_sq_eq_add_norm_sq_projection_complexVolume (ψ : S) :
    ‖ψ‖ ^ 2 =
      ‖Submodule.projection _ _
          ((liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hρ.apply_eq_neg_norm_sq)
          ψ‖ ^ 2 +
      ‖Submodule.projection _ _
          ((liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o
            hρ.apply_eq_neg_norm_sq).symm ψ‖ ^ 2 := by
  set hc := (liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hρ.apply_eq_neg_norm_sq
  have hsum := Submodule.projection_add_projection_eq_self hc ψ
  have horth : ⟪Submodule.projection _ _ hc ψ, Submodule.projection _ _ hc.symm ψ⟫_ℂ = 0 :=
    hρ.inner_eigenspace_liftBaseChange_complexVolume_eq_zero o
      (Submodule.projection_apply_mem hc ψ) (Submodule.projection_apply_mem hc.symm ψ)
  conv_lhs => rw [← hsum]
  rw [norm_add_sq (𝕜 := ℂ), horth, map_zero, mul_zero, add_zero]

end SeminormedS

/-- **The half-spinor spaces of a geometric action are orthogonal**: `S⁺ ⟂ S⁻`. -/
theorem isOrtho_eigenspace_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
    (o : Orientation ℝ V (Fin n)) :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1 ⟂
      (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1) :=
  Submodule.isOrtho_iff_inner_eq.mpr fun _ h₁ _ h₂ ↦
    hρ.inner_eigenspace_liftBaseChange_complexVolume_eq_zero o h₁ h₂

/-- **Self-adjointness of `Γ`** on a finite-dimensional geometric Hermitian Clifford module. -/
theorem isSelfAdjoint_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
    (o : Orientation ℝ V (Fin n)) :
    IsSelfAdjoint (liftBaseChange ℂ Q ρ (complexVolume Q o)) :=
  CliffordAlgebra.isSelfAdjoint_liftBaseChange_complexVolume o hρ.adjoint_map_ι

end AlgHom.IsGeometricClifford
