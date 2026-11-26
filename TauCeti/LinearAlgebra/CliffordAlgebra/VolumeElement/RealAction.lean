/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod
-- Private: tensor-product formal-adjoint identity is used only inside proofs.
import TauCeti.Analysis.InnerProductSpace.TensorProduct.Basic

/-!
# The chirality operator of a real Clifford action

Let `V` be an oriented real inner product space of dimension `n`, `Q` a quadratic form on `V`
and `ρ : Cℓ(V, Q) → End_ℂ(S)` a real algebra map into the complex endomorphisms of a complex
vector space `S`, with Clifford multiplication `c(v) = ρ (ι Q v)`. (The formulas for `ρ_ℂ(Γ)` and
its anticommutation with `c(v)` hold for real algebra maps into any complex algebra.) Its
complex-linear extension
`ρ_ℂ = CliffordAlgebra.liftBaseChange ℂ Q ρ` makes `S` a module over the complexified Clifford
algebra `Cℓ(ℂ ⊗ V, Q_ℂ)`, on which the vector `1 ⊗ v` acts by `c(v)`
(`CliffordAlgebra.liftBaseChange_ι_tmul`). The normalized complex volume element `Γ`
(`CliffordAlgebra.complexVolume`) of that algebra therefore acts on `S`, by

  `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ ρ(vol) = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`

for the real volume element `vol` (`CliffordAlgebra.volumeElement`) and every positively oriented
orthonormal basis `e` that is orthogonal for `Q`. In even dimension `n = 2ℓ` the factor is `i ^ ℓ`,
and for `Q v = -‖v‖²` this operator is an involution anticommuting with every `c(v)`: its `±1`
eigenspaces are the half-spinor spaces `S⁺` and `S⁻` of `S`, exchanged by Clifford multiplication.
They are complementary by `AlgHom.isCompl_eigenspace_complexVolume` applied to `ρ_ℂ`, as
`(liftBaseChange ℂ Q ρ).isCompl_eigenspace_complexVolume o hQ`.

On a complex inner product space, `ρ_ℂ` is a `*`-representation for the conjugate-linear Clifford
involution `CliffordAlgebra.conjStar` exactly when the real generators act skew-Hermitianly
(`CliffordAlgebra.adjoint_liftBaseChange_eq_liftBaseChange_conjStar_iff`), the second clause of
the geometric convention `AlgHom.IsGeometricClifford`
(`AlgHom.IsGeometricClifford.inner_liftBaseChange_apply_left`). Since `Γ` is fixed by `conjStar`,
under the geometric convention `ρ_ℂ(Γ)` is symmetric (and self-adjoint in finite dimension) and the
half-spinor spaces are orthogonal. Moreover, this chirality grading makes the graded tensor product
`CliffordAlgebra.complexProdTensor` preserve `AlgHom.IsGeometricClifford` on `WithLp 2 (V × W)`.
These are the forms of `Γ` and `S^±` used for Clifford-module bundles, whose fibres carry real
Clifford actions.

## Main results

* `CliffordAlgebra.liftBaseChange_complexVolume`,
  `CliffordAlgebra.liftBaseChange_complexVolume_of_eq_two_mul`:
  `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ ρ(vol)` (and `i ^ ℓ ρ(vol)` when `n = 2ℓ`), and
  `CliffordAlgebra.liftBaseChange_complexVolume_eq`,
  `CliffordAlgebra.liftBaseChange_complexVolume_eq_of_eq_two_mul`: their frame formulas
  `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` (and `i ^ ℓ c(e₁) ⋯ c(e₂ℓ)`).
* `CliffordAlgebra.liftBaseChange_complexVolume_mul_map_ι`: in even dimension `ρ_ℂ(Γ)`
  anticommutes with every `c(v)`, and
  `CliffordAlgebra.map_ι_apply_mem_eigenspace_liftBaseChange_complexVolume_neg`: `c(v)` maps the
  `μ`-eigenspace of `ρ_ℂ(Γ)` into its `-μ`-eigenspace.
* `AlgHom.IsGeometricClifford.isSymmetric_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.isSelfAdjoint_liftBaseChange_complexVolume`: under the geometric
  convention `ρ_ℂ(Γ)` is symmetric (and self-adjoint in finite dimension), and
  `AlgHom.IsGeometricClifford.isOrtho_eigenspace_liftBaseChange_complexVolume`: `S⁺ ⟂ S⁻`.
* `AlgHom.IsGeometricClifford.complexProdTensor`: graded tensor product preservation of the
  geometric convention on `WithLp 2 (V × W)`.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, §12.1, pp. 632–633, for the chirality
  operator `Γ = i ^ ℓ c(e₁) ⋯ c(e₂ℓ)` of a Clifford module.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open Module Module.End
open scoped InnerProductSpace TensorProduct

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

section Semiring

variable {B : Type*} [Semiring B] [Algebra ℂ B] [Algebra ℝ B] [IsScalarTower ℝ ℂ B]
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

/-- **Even-dimensional chirality formula**: on an oriented `n`-dimensional real inner product
space with `n = 2ℓ`, `ρ_ℂ(Γ) = i ^ ℓ • ρ(vol)`. -/
theorem liftBaseChange_complexVolume_of_eq_two_mul {ℓ : ℕ} (hn : n = 2 * ℓ) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) = Complex.I ^ ℓ • ρ (volumeElement Q o) := by
  have hℓ : (n + 1) / 2 = ℓ := by omega
  rw [liftBaseChange_complexVolume o ρ, hℓ]

/-- **Even-dimensional frame formula for the chirality operator**: when `n = 2ℓ`,
`ρ_ℂ(Γ) = i ^ ℓ • c(e₁) ⋯ c(e₂ℓ)` for every positively oriented orthonormal basis `e` orthogonal
for `Q`. -/
theorem liftBaseChange_complexVolume_eq_of_eq_two_mul (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis)
    {ℓ : ℕ} (hn : n = 2 * ℓ) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) =
      Complex.I ^ ℓ • (((List.finRange n).map b).map fun v ↦ ρ (ι Q v)).prod := by
  have hℓ : (n + 1) / 2 = ℓ := by omega
  rw [liftBaseChange_complexVolume_eq o ρ b hb hQb, hℓ]

end Semiring

section Ring

variable {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℝ B] [IsScalarTower ℝ ℂ B]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **In even dimension the chirality operator anticommutes with Clifford multiplication**:
`ρ_ℂ(Γ) c(v) = -c(v) ρ_ℂ(Γ)`. -/
theorem liftBaseChange_complexVolume_mul_map_ι (hn : Even n) (v : V) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ (ι Q v) =
      -(ρ (ι Q v) * liftBaseChange ℂ Q ρ (complexVolume Q o)) := by
  simpa only [liftBaseChange_ι_tmul, one_smul] using
    map_complexVolume_mul_map_ι o hn (liftBaseChange ℂ Q ρ) (1 ⊗ₜ v)

end Ring

section Module

variable {S : Type*} [AddCommGroup S] [Module ℂ S] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- **Clifford multiplication exchanges the half-spinors**: in even dimension, `c(v)` maps the
`μ`-eigenspace of `ρ_ℂ(Γ)` into its `-μ`-eigenspace. -/
theorem map_ι_apply_mem_eigenspace_liftBaseChange_complexVolume_neg (hn : Even n) (v : V)
    {μ : ℂ} {ψ : S} (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ (ι Q v) ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ) := by
  rw [mem_eigenspace_iff] at hψ ⊢
  rw [← mul_apply_eq_comp, liftBaseChange_complexVolume_mul_map_ι o ρ hn, LinearMap.neg_apply,
    mul_apply_eq_comp, hψ, map_smul, neg_smul]

end Module

end CliffordAlgebra

namespace AlgHom.IsGeometricClifford

open CliffordAlgebra

section Chirality

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))
include hρ

/-- **The chirality operator of a geometric action is self-adjoint**: `ρ_ℂ(Γ)` is symmetric,
since `Γ` is fixed by `conjStar`. -/
theorem isSymmetric_liftBaseChange_complexVolume :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).IsSymmetric := fun s t ↦ by
  rw [hρ.inner_liftBaseChange_apply_left, conjStar_complexVolume]

/-- **Self-adjointness of `Γ`**: on any finite-dimensional geometric Clifford module,
`liftBaseChange ℂ Q ρ (complexVolume Q o)` is self-adjoint (`IsSelfAdjoint`). -/
theorem isSelfAdjoint_liftBaseChange_complexVolume [FiniteDimensional ℂ S] :
    IsSelfAdjoint (liftBaseChange ℂ Q ρ (complexVolume Q o)) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).1
    (hρ.isSymmetric_liftBaseChange_complexVolume o)

/-- **The half-spinor spaces of a geometric action are orthogonal**: `S⁺ ⟂ S⁻`. -/
theorem isOrtho_eigenspace_liftBaseChange_complexVolume :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1 ⟂
      (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1) :=
  (hρ.isSymmetric_liftBaseChange_complexVolume o).orthogonalFamily_eigenspaces.isOrtho
    (by norm_num)

end Chirality

section TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₂ : QuadraticForm ℝ W} {Q₁₂ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Graded tensor product of geometric Clifford actions**: if `ρ₁` is a geometric Clifford action
of an even-dimensional oriented space `(V, Q)` on `E` and `ρ₂` is a geometric Clifford action of
`(W, Q₂)` on `F`, then restricting `CliffordAlgebra.complexProdTensor` (graded by the chirality of
`V`) along `CliffordAlgebra.ofBaseChangeAux ℂ Q₁₂` to `CliffordAlgebra Q₁₂` on `WithLp 2 (V × W)`
yields a geometric Clifford action on `E ⊗[ℂ] F`. -/
theorem complexProdTensor
    {ρ₁ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F}
    (hρ₁ : ρ₁.IsGeometricClifford) (hρ₂ : ρ₂.IsGeometricClifford)
    (o₁ : Orientation ℝ V (Fin n)) (hn : Even n)
    (hQ₁₂ : ∀ x, Q₁₂ x = -‖x‖ ^ 2) :
    (((CliffordAlgebra.complexProdTensor
      (QuadraticMap.apply_prod_eq_add_of_neg_norm_sq
        hρ₁.apply_eq_neg_norm_sq hρ₂.apply_eq_neg_norm_sq hQ₁₂)
      o₁ hρ₁.apply_eq_neg_norm_sq hn (liftBaseChange ℂ Q ρ₁)
      (liftBaseChange ℂ Q₂ ρ₂)).restrictScalars ℝ).comp
        (ofBaseChangeAux ℂ Q₁₂)).IsGeometricClifford := by
  refine (AlgHom.isGeometricClifford_restrictScalars_comp_ofBaseChangeAux_iff (Q := Q₁₂) _).2
    ⟨hQ₁₂, fun x u₁ u₂ ↦ ?_⟩
  obtain ⟨⟨v, w⟩, rfl⟩ := WithLp.toLp_surjective 2 x
  simp only [CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp,
    CliffordAlgebra.liftBaseChange_ι_tmul, one_smul, LinearMap.add_apply, inner_add_left,
    inner_add_right, neg_add]
  congr 1
  · rw [LinearMap.rTensor_def,
      TensorProduct.inner_map_left (f' := -ρ₁ (ι Q v)) (g' := LinearMap.id)
        (fun a a' ↦ by simp [hρ₁.inner_map_ι_apply_left]) (fun _ _ ↦ rfl),
      ← LinearMap.rTensor_def, LinearMap.rTensor_neg, LinearMap.neg_apply, inner_neg_right,
      LinearMap.rTensor_def]
  · rw [TensorProduct.inner_map_left (f' := liftBaseChange ℂ Q ρ₁ (complexVolume Q o₁))
        (g' := (-1 : ℂ) • ρ₂ (ι Q₂ w))
        (fun a a' ↦ hρ₁.isSymmetric_liftBaseChange_complexVolume o₁ a a')
        (fun b b' ↦ by simp [hρ₂.inner_map_ι_apply_left]),
      TensorProduct.map_smul_right, LinearMap.smul_apply, neg_one_smul, inner_neg_right]

end TensorProduct

end AlgHom.IsGeometricClifford
