/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
-- Private: orthogonality of orthonormal frames for `Q v = -‖v‖²` and eigenspace transport along
-- intertwiners are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# The chirality operator of a real Clifford algebra action on a complex module

Let `V` be an oriented real inner product space of dimension `n` with quadratic form `Q`, and let
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` be a real algebra homomorphism into the complex
endomorphisms of a complex vector space `S`, as on a fibre of a complex Clifford-module bundle. The
normalized complex volume element `Γ = CliffordAlgebra.complexVolume Q o` lives in the complexified
algebra `CliffordAlgebra (Q.baseChange ℂ)`, so it acts on `S` through the complex-linear scalar
extension `CliffordAlgebra.liftBaseChange ℂ Q ρ`.

This file expresses that operator and its eigenspaces directly in terms of the real action
`c(v) = ρ (ι Q v)` without assuming any topology, inner product, or finite-dimensionality on `S`:

* `liftBaseChange ℂ Q ρ (complexVolume Q o) = i ^ ⌊(n + 1) / 2⌋ • ρ (volumeElement Q o)`, which in
  any positively oriented orthonormal frame `e` orthogonal for `Q` (in particular any positively
  oriented orthonormal frame when `Q v = -‖v‖²`) equals `i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`, and in
  even dimension `2ℓ` equals `i ^ ℓ c(e₁) ⋯ c(e₂ℓ)`.
* In even dimension this operator anticommutes with every real generator `c(v)` and odd element of
  `CliffordAlgebra Q`, while in odd dimension it commutes with the whole image of `ρ`, and in every
  dimension it commutes with the even subalgebra.
* For `Q v = -‖v‖²` it is an involution splitting `S` into complementary `+1`- and `-1`-eigenspaces
  `S⁺` and `S⁻` with projections `2⁻¹ • (1 ± Γ)`. By contrast, for `Q = 0` in positive dimension
  both `±1`-eigenspaces vanish, so on a nontrivial module they are not complementary.

## Main results

* `CliffordAlgebra.liftBaseChange_complexVolume`, `CliffordAlgebra.liftBaseChange_complexVolume_eq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_of_neg_norm_sq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_two_mul_eq_of_neg_norm_sq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_prod_pairs_of_neg_norm_sq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_prod_pairs_mul_of_neg_norm_sq`: the real-action
  and orthonormal-frame formulas for `liftBaseChange ℂ Q ρ (complexVolume Q o)`.
* `CliffordAlgebra.liftBaseChange_complexVolume_mul_map_ι_of_even`,
  `CliffordAlgebra.commute_liftBaseChange_complexVolume_map_of_mem_even`,
  `CliffordAlgebra.commute_liftBaseChange_complexVolume_map_of_odd`: parity and commutation laws
  against real Clifford elements.
* `CliffordAlgebra.isCompl_eigenspace_liftBaseChange_complexVolume`,
  `CliffordAlgebra.projection_eigenspace_liftBaseChange_complexVolume_apply`,
  `CliffordAlgebra.projection_eigenspace_liftBaseChange_complexVolume_neg_one_apply`: the
  half-spin decomposition `S = S⁺ ⊕ S⁻` and its explicit projections `2⁻¹ • (1 ± Γ)` for
  `Q v = -‖v‖²`.
* `CliffordAlgebra.map_ι_mem_eigenspace_liftBaseChange_complexVolume_neg`: in even dimension, real
  vectors exchange the `μ`- and `-μ`-eigenspaces.
* `CliffordAlgebra.finrank_eigenspace_liftBaseChange_complexVolume_neg`: in even positive
  dimension, the `-μ`- and `μ`-eigenspaces have equal complex dimension.
* `CliffordAlgebra.eigenspace_liftBaseChange_complexVolume_eq_bot_of_forall_eq_zero`: negative
  control for `Q = 0` in positive dimension.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 12, §12.1.
-/

public section

noncomputable section

open Module Module.End TauCeti
open scoped TensorProduct

namespace CliffordAlgebra

section Algebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V}

section Semiring

variable {B : Type*} [Semiring B] [Algebra ℝ B] [Algebra ℂ B] [IsScalarTower ℝ ℂ B]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

section GeneralDim

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- Under `CliffordAlgebra.liftBaseChange`, the normalized complex volume element acts as
`i ^ ⌊(n + 1) / 2⌋` times the image of the real volume element. -/
theorem liftBaseChange_complexVolume :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • ρ (volumeElement Q o) := by
  rw [complexVolume_def, map_smul, liftBaseChange_ofBaseChangeAux]

/-- **Frame formula for a real algebra map**: in any positively oriented orthonormal basis `b`
orthogonal for `Q`, the complexified volume element maps to
`i ^ ⌊(n + 1) / 2⌋ c(b₁) ⋯ c(bₙ)`. -/
theorem liftBaseChange_complexVolume_eq (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • (((List.finRange n).map b).map fun v ↦ ρ (ι Q v)).prod := by
  rw [liftBaseChange_complexVolume, volumeElement_eq o b hb hQb, map_list_prod, List.map_map]
  rfl

/-- For `Q v = -‖v‖²`, every positively oriented orthonormal basis gives the frame formula
`i ^ ⌊(n + 1) / 2⌋ c(b₁) ⋯ c(bₙ)`. -/
theorem liftBaseChange_complexVolume_eq_of_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • (((List.finRange n).map b).map fun v ↦ ρ (ι Q v)).prod :=
  liftBaseChange_complexVolume_eq ρ o b hb (b.isOrthoᵢ_associated hQ)

/-- **In even dimension `Γ` intertwines the real grade involution**:
`Γ (ρ x) = ρ (involute x) Γ`. -/
theorem liftBaseChange_complexVolume_mul_map_eq_involute (hn : Even n) (x : CliffordAlgebra Q) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ x =
      ρ (involute x) * liftBaseChange ℂ Q ρ (complexVolume Q o) := by
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) ρ x, ← map_mul,
    complexVolume_mul_eq_involute_mul o hn, ← ofBaseChangeAux_involute, map_mul,
    liftBaseChange_ofBaseChangeAux]

/-- **In odd dimension `Γ` commutes with the entire image of the real Clifford algebra.** -/
theorem commute_liftBaseChange_complexVolume_map_of_odd (hn : Odd n) (x : CliffordAlgebra Q) :
    Commute (liftBaseChange ℂ Q ρ (complexVolume Q o)) (ρ x) := by
  rw [Commute, SemiconjBy, ← liftBaseChange_ofBaseChangeAux (A := ℂ) ρ x, ← map_mul, ← map_mul,
    Subalgebra.mem_center_iff.mp (complexVolume_mem_center o hn)]

/-- `Γ` commutes with every even element of the real Clifford algebra, in every dimension. -/
theorem commute_liftBaseChange_complexVolume_map_of_mem_even {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) :
    Commute (liftBaseChange ℂ Q ρ (complexVolume Q o)) (ρ x) := by
  simpa using (commute_complexVolume_of_mem_even o
    (ofBaseChangeAux_mem_evenOdd (A := ℂ) hx)).map (liftBaseChange ℂ Q ρ)

/-- For `Q v = -‖v‖²`, the image of `Γ` under `CliffordAlgebra.liftBaseChange` squares to `1`. -/
@[simp]
theorem liftBaseChange_complexVolume_mul_self (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * liftBaseChange ℂ Q ρ (complexVolume Q o) = 1 := by
  rw [← map_mul, complexVolume_mul_self o hQ, map_one]

/-- For `Q = 0` in positive dimension, the image of `Γ` squares to `0`. -/
theorem liftBaseChange_complexVolume_mul_self_of_forall_eq_zero (hn : n ≠ 0) (hQ : ∀ v, Q v = 0) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * liftBaseChange ℂ Q ρ (complexVolume Q o) = 0 := by
  rw [← map_mul, complexVolume_mul_self_of_forall_eq_zero o hn hQ, map_zero]

end GeneralDim

section EvenDim

variable {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ)] (o : Orientation ℝ V (Fin (2 * ℓ)))

/-- **Even-dimensional frame formula**: in dimension `2ℓ`, for any positively oriented orthonormal
basis `b` orthogonal for `Q`, `Γ` maps to `i ^ ℓ c(b₁) ⋯ c(b₂ℓ)`. -/
theorem liftBaseChange_complexVolume_two_mul_eq (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ℓ • (((List.finRange (2 * ℓ)).map b).map fun v ↦ ρ (ι Q v)).prod := by
  rw [liftBaseChange_complexVolume_eq ρ o b hb hQb, show (2 * ℓ + 1) / 2 = ℓ by omega]

/-- **Even-dimensional frame formula for `Q v = -‖v‖²`**: in any positively oriented orthonormal
basis `b`, `Γ` maps to `i ^ ℓ c(b₁) ⋯ c(b₂ℓ)`. -/
theorem liftBaseChange_complexVolume_two_mul_eq_of_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V) (hb : b.toBasis.orientation = o) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ℓ • (((List.finRange (2 * ℓ)).map b).map fun v ↦ ρ (ι Q v)).prod :=
  liftBaseChange_complexVolume_two_mul_eq ρ o b hb (b.isOrthoᵢ_associated hQ)

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
  liftBaseChange_complexVolume_eq_prod_pairs ρ o b hb (b.isOrthoᵢ_associated hQ)

end EvenDim

section OddDim

variable {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ + 1)] (o : Orientation ℝ V (Fin (2 * ℓ + 1)))

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
  liftBaseChange_complexVolume_eq_prod_pairs_mul ρ o b hb (b.isOrthoᵢ_associated hQ)

end OddDim

end Semiring

section Ring

variable {B : Type*} [Ring B] [Algebra ℝ B] [Algebra ℂ B] [IsScalarTower ℝ ℂ B]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B) {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **In even dimension `Γ` anticommutes with every real vector** under `ρ`:
`Γ c(v) = -c(v) Γ`. -/
theorem liftBaseChange_complexVolume_mul_map_ι_of_even (hn : Even n) (v : V) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ (ι Q v) =
      -(ρ (ι Q v) * liftBaseChange ℂ Q ρ (complexVolume Q o)) := by
  rw [← liftBaseChange_ι_one_tmul (A := ℂ) ρ v, ← map_mul, complexVolume_mul_ι_of_even o hn,
    map_neg, map_mul]

/-- In even dimension `Γ` anticommutes with every odd element of the real Clifford algebra. -/
theorem liftBaseChange_complexVolume_mul_map_of_mem_odd (hn : Even n) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 1) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ x =
      -(ρ x * liftBaseChange ℂ Q ρ (complexVolume Q o)) := by
  rw [liftBaseChange_complexVolume_mul_map_eq_involute ρ o hn, involute_eq_of_mem_odd hx, map_neg,
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

private theorem projection_congr_end {S : Type*} [AddCommGroup S] [Module ℂ S]
    {f g : Module.End ℂ S} (hfg : f = g) {μ₁ μ₂ : ℂ}
    (hf : IsCompl (f.eigenspace μ₁) (f.eigenspace μ₂))
    (hg : IsCompl (g.eigenspace μ₁) (g.eigenspace μ₂)) :
    Submodule.projection _ _ hf = Submodule.projection _ _ hg := by
  subst hfg
  rfl

section Module

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

section RankZero

variable [Fact (finrank ℝ V = 0)]

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
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  exact (two_ne_zero : (2 : ℂ) ≠ 0).isUnit.smul_eq_zero.mp
    (by rw [two_smul ℂ ψ]; exact eq_neg_iff_add_eq_zero.mp h)

end RankZero

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

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
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) ρ x, ← compBaseChangeModule_smul ρ]
  exact smul_mem_eigenspace_complexVolume_neg_of_mem_odd o hn
    (ofBaseChangeAux_mem_evenOdd (A := ℂ) hx) hψ

/-- **Real vectors exchange the half-spinors**: in even dimension, `c(v)` maps the `μ`-eigenspace
of `Γ` into the `-μ`-eigenspace. -/
theorem map_ι_mem_eigenspace_liftBaseChange_complexVolume_neg (hn : Even n) (v : V) {μ : ℂ} {ψ : S}
    (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ (ι Q v) ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ) :=
  map_mem_eigenspace_liftBaseChange_complexVolume_neg_of_mem_odd ρ o hn (ι_mem_evenOdd_one Q v) hψ

/-- In odd dimension every element of the real Clifford algebra preserves each eigenspace of `Γ`. -/
theorem map_mem_eigenspace_liftBaseChange_complexVolume_of_odd (hn : Odd n)
    (x : CliffordAlgebra Q) {μ : ℂ} {ψ : S}
    (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ x ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ] at hψ ⊢
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) ρ x, ← compBaseChangeModule_smul ρ]
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
  rw [← liftBaseChange_ofBaseChangeAux (A := ℂ) ρ x, ← compBaseChangeModule_smul ρ]
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

/-- For `Q v = -‖v‖²`, the chirality operator of `ρ` is an involution on `S`. -/
theorem liftBaseChange_complexVolume_involutive :
    Function.Involutive (liftBaseChange ℂ Q ρ (complexVolume Q o)) := fun ψ ↦ by
  rw [← mul_apply_eq_comp, liftBaseChange_complexVolume_mul_self ρ o hQ, one_apply_eq_self]

/-- **The chirality decomposition of a real Clifford action**: for `Q v = -‖v‖²`, `S` is the direct
sum of the `+1`- and `-1`-eigenspaces of `liftBaseChange ℂ Q ρ (complexVolume Q o)`. -/
theorem isCompl_eigenspace_liftBaseChange_complexVolume :
    IsCompl ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1)
      ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1)) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  rw [← lsmul_compBaseChangeModule ρ]
  exact isCompl_eigenspace_complexVolume (E := S) o hQ

/-- **The positive chirality projection** onto `S⁺` along `S⁻` is `2⁻¹ • (1 + Γ)`. -/
theorem projection_eigenspace_liftBaseChange_complexVolume_apply (ψ : S) :
    Submodule.projection _ _ (isCompl_eigenspace_liftBaseChange_complexVolume ρ o hQ) ψ =
      (2 : ℂ)⁻¹ • (ψ + liftBaseChange ℂ Q ρ (complexVolume Q o) ψ) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  have hp := projection_congr_end (lsmul_compBaseChangeModule ρ (complexVolume Q o)).symm
    (isCompl_eigenspace_liftBaseChange_complexVolume ρ o hQ)
    (isCompl_eigenspace_complexVolume (Q := Q) (E := S) o hQ)
  rw [LinearMap.congr_fun hp ψ, projection_eigenspace_complexVolume_apply (Q := Q) (E := S) o hQ,
    compBaseChangeModule_smul]
  simp [halfOneAdd_def, invOf_eq_inv]

/-- **The negative chirality projection** onto `S⁻` along `S⁺` is `2⁻¹ • (1 - Γ)`. -/
theorem projection_eigenspace_liftBaseChange_complexVolume_neg_one_apply (ψ : S) :
    Submodule.projection _ _ (isCompl_eigenspace_liftBaseChange_complexVolume ρ o hQ).symm ψ =
      (2 : ℂ)⁻¹ • (ψ - liftBaseChange ℂ Q ρ (complexVolume Q o) ψ) := by
  let := compBaseChangeModule ρ
  have := compBaseChangeScalarTower ρ
  have hp := projection_congr_end (lsmul_compBaseChangeModule ρ (complexVolume Q o)).symm
    (isCompl_eigenspace_liftBaseChange_complexVolume ρ o hQ).symm
    (isCompl_eigenspace_complexVolume (Q := Q) (E := S) o hQ).symm
  rw [LinearMap.congr_fun hp ψ,
    projection_eigenspace_complexVolume_neg_one_apply (Q := Q) (E := S) o hQ,
    compBaseChangeModule_smul]
  simp [halfOneAdd_def, invOf_eq_inv, sub_eq_add_neg]

end Form

end Module

end CliffordAlgebra
