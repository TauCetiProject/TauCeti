/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
-- Private: the splitting of a space by an involution is used only inside a proof.
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# The chirality operator of a real Clifford action

Let `V` be an oriented real inner product space of dimension `n`, `Q` a quadratic form on `V`
and `ρ : Cℓ(V, Q) → End_ℂ(S)` a real algebra map into the complex endomorphisms of a complex
vector space `S`, with Clifford multiplication `c(v) = ρ (ι Q v)`. Its complex-linear extension
`ρ_ℂ = CliffordAlgebra.liftBaseChange ℂ Q ρ` makes `S` a module over the complexified Clifford
algebra `Cℓ(ℂ ⊗ V, Q_ℂ)`, on which the vector `1 ⊗ v` acts by `c(v)`
(`CliffordAlgebra.liftBaseChange_ι_tmul`). The normalized complex volume element `Γ`
(`CliffordAlgebra.complexVolume`) of that algebra therefore acts on `S`, by

  `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ ρ(vol) = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`

for the real volume element `vol` (`CliffordAlgebra.volumeElement`) and every positively oriented
orthonormal basis `e` that is orthogonal for `Q`. In even dimension `n = 2ℓ` the factor is `i ^ ℓ`,
and for `Q v = -‖v‖²` this operator is an involution anticommuting with every `c(v)`: its `±1`
eigenspaces are the half-spinor spaces `S⁺` and `S⁻` of `S`, complementary and exchanged by
Clifford multiplication.

On a complex inner product space, `ρ_ℂ` is a `*`-representation for the conjugate-linear Clifford
involution `CliffordAlgebra.conjStar` exactly when the real generators act skew-Hermitianly, the
second clause of the geometric convention `AlgHom.IsGeometricClifford`. Since `Γ` is fixed by
`conjStar`, under the geometric convention `ρ_ℂ(Γ)` is self-adjoint and the half-spinor spaces are
orthogonal. These are the forms of `Γ` and `S^±` used for Clifford-module bundles, whose fibres
carry real Clifford actions.

## Main results

* `CliffordAlgebra.liftBaseChange_complexVolume`: `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ ρ(vol)`, and
  `CliffordAlgebra.liftBaseChange_complexVolume_eq`: its frame formula
  `ρ_ℂ(Γ) = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`.
* `CliffordAlgebra.liftBaseChange_complexVolume_mul_map_ι`: in even dimension `ρ_ℂ(Γ)`
  anticommutes with every `c(v)`, and
  `CliffordAlgebra.map_ι_apply_mem_eigenspace_liftBaseChange_complexVolume_neg`: `c(v)` maps the
  `μ`-eigenspace of `ρ_ℂ(Γ)` into its `-μ`-eigenspace.
* `CliffordAlgebra.isCompl_eigenspace_liftBaseChange_complexVolume`: for `Q v = -‖v‖²`, the
  half-spinor spaces `S⁺` and `S⁻` are complementary.
* `CliffordAlgebra.adjoint_liftBaseChange_eq_conjStar_iff`: on a finite-dimensional Hermitian
  module, `ρ_ℂ` is a `*`-representation for `conjStar` exactly when every `c(v)` is
  skew-adjoint.
* `AlgHom.IsGeometricClifford.inner_liftBaseChange_apply_left`: under the geometric convention,
  `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫` on a module of any dimension;
  `AlgHom.IsGeometricClifford.isSymmetric_liftBaseChange_complexVolume`: `ρ_ℂ(Γ)` is
  self-adjoint; `AlgHom.IsGeometricClifford.isOrtho_eigenspace_liftBaseChange_complexVolume`:
  `S⁺ ⟂ S⁻`.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, §12.1, pp. 632–633, for the chirality
  operator `Γ = i ^ ℓ c(e₁) ⋯ c(e₂ℓ)` of a Clifford module.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open Module Module.End
open scoped InnerProductSpace TensorProduct

namespace CliffordAlgebra

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}

/-- **`*`-representations of the complexified Clifford algebra**: on a finite-dimensional
Hermitian module, the complex-linear extension `ρ_ℂ` of a real Clifford action satisfies
`ρ_ℂ(a)* = ρ_ℂ(conjStar a)` for every `a` exactly when Clifford multiplication by every real
vector is skew-adjoint. -/
theorem adjoint_liftBaseChange_eq_conjStar_iff :
    (∀ a, LinearMap.adjoint (liftBaseChange ℂ Q ρ a) = liftBaseChange ℂ Q ρ (conjStar Q a)) ↔
      ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v) := by
  simpa only [liftBaseChange_ι_tmul, one_smul] using
    adjoint_map_eq_map_conjStar_iff (liftBaseChange ℂ Q ρ)

end Hermitian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

section Module

variable {S : Type*} [AddCommGroup S] [Module ℂ S] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

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

/-- **In even dimension the chirality operator anticommutes with Clifford multiplication**:
`ρ_ℂ(Γ) c(v) = -c(v) ρ_ℂ(Γ)`. -/
theorem liftBaseChange_complexVolume_mul_map_ι (hn : Even n) (v : V) :
    liftBaseChange ℂ Q ρ (complexVolume Q o) * ρ (ι Q v) =
      -(ρ (ι Q v) * liftBaseChange ℂ Q ρ (complexVolume Q o)) := by
  have h := congrArg (liftBaseChange ℂ Q ρ) (complexVolume_mul_ι_of_even o hn (1 ⊗ₜ v))
  simpa only [map_mul, map_neg, liftBaseChange_ι_tmul, one_smul] using h

/-- **Clifford multiplication exchanges the half-spinors**: in even dimension, `c(v)` maps the
`μ`-eigenspace of `ρ_ℂ(Γ)` into its `-μ`-eigenspace. -/
theorem map_ι_apply_mem_eigenspace_liftBaseChange_complexVolume_neg (hn : Even n) (v : V)
    {μ : ℂ} {ψ : S} (hψ : ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace μ) :
    ρ (ι Q v) ψ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-μ) := by
  rw [mem_eigenspace_iff] at hψ ⊢
  rw [← mul_apply_eq_comp, liftBaseChange_complexVolume_mul_map_ι o ρ hn, LinearMap.neg_apply,
    mul_apply_eq_comp, hψ, map_smul, neg_smul]

/-- **The half-spinor decomposition of a real Clifford action**: for `Q v = -‖v‖²`, the
eigenspaces `S⁺` and `S⁻` of `ρ_ℂ(Γ)` for the eigenvalues `1` and `-1` are complementary. -/
theorem isCompl_eigenspace_liftBaseChange_complexVolume (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    IsCompl ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1)
      ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1)) := by
  refine TauCeti.isCompl_eigenspace_one_neg_one two_ne_zero.isUnit fun ψ ↦ ?_
  rw [← mul_apply_eq_comp, ← map_mul, complexVolume_mul_self o hQ, map_one, one_apply_eq_self]

end Module

end CliffordAlgebra

namespace AlgHom.IsGeometricClifford

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- **A geometric action is a `*`-representation**: under the geometric convention, the
complex-linear extension `ρ_ℂ` satisfies `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫`, on a module
of any dimension. -/
theorem inner_liftBaseChange_apply_left (a : CliffordAlgebra (Q.baseChange ℂ)) (s t : S) :
    ⟪liftBaseChange ℂ Q ρ a s, t⟫_ℂ = ⟪s, liftBaseChange ℂ Q ρ (conjStar Q a) t⟫_ℂ := by
  refine sesqForm_map_eq_map_conjStar (liftBaseChange ℂ Q ρ) (innerₛₗ ℂ) (fun v x y ↦ ?_) a s t
  simpa only [innerₛₗ_apply_apply, liftBaseChange_ι_tmul, one_smul] using
    hρ.inner_map_ι_apply_left v x y

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **The chirality operator of a geometric action is self-adjoint**: `ρ_ℂ(Γ)` is symmetric,
since `Γ` is fixed by `conjStar`. -/
theorem isSymmetric_liftBaseChange_complexVolume :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).IsSymmetric := fun s t ↦ by
  rw [hρ.inner_liftBaseChange_apply_left, conjStar_complexVolume]

/-- **The half-spinor spaces of a geometric action are orthogonal**: `S⁺ ⟂ S⁻`. -/
theorem isOrtho_eigenspace_liftBaseChange_complexVolume :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1 ⟂
      (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1) :=
  (hρ.isSymmetric_liftBaseChange_complexVolume o).orthogonalFamily_eigenspaces.isOrtho
    (by norm_num)

end AlgHom.IsGeometricClifford
