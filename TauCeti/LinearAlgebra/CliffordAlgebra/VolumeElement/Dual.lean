/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.Dual.Annihilator
import TauCeti.Algebra.Ring.Parity
import TauCeti.LinearAlgebra.Eigenspace.Dual
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# The chirality of the reverse-dual Clifford module

Let `V` be an oriented real inner product space of dimension `n`, and let
`ρ : Cℓ(ℂ ⊗ V, Q_ℂ) → End_ℂ S` be a module over the complexified Clifford algebra. Its reverse
dual `S*` (`AlgHom.cliffordReverseDual`) is the action `(a · φ)(s) = φ (ρ (reverse a) s)`, under
which each vector acts by the transpose of its action on `S`. Reversal multiplies the
normalized complex volume element `Γ` (`CliffordAlgebra.complexVolume`) by `(-1) ^ ⌊n / 2⌋`, so
`Γ` acts on the reverse dual by

  `Γ_(S*) = (-1) ^ ⌊n / 2⌋ Γ_Sᵀ`.

In even dimension `n = 2ℓ` this is the chirality `(-1) ^ ℓ Γ_Sᵀ` of the reverse dual. It differs
from the parity `Γ_Sᵀ` induced on `S*` by the grading of `S` exactly when `ℓ` is odd.

For `Q v = -‖v‖²` the element `Γ` is an involution, so a functional is a `μ`-eigenvector of
`Γ_Sᵀ` exactly when it vanishes on the `-μ`-eigenspace of `Γ_S`. Hence the eigenspaces of `Γ` on
the reverse dual are

  `(S*)^μ = (S^(-ε μ))^⊥ ≃ (S^(ε μ))*`,  `ε = (-1) ^ ⌊n / 2⌋`,

for `μ = ±1`, the isomorphism being restriction of functionals. In even dimension `2ℓ` with `ℓ`
even, the positive half-spinors of the reverse dual are the dual of the positive half-spinors of
`S`; when `ℓ` is odd the two labels are exchanged. In odd dimension the same formula labels the
two central factors of the reverse dual by the eigenvalue of `ω_ℂ`. Nothing is assumed of `S`:
it need not be finite-dimensional or irreducible.

## Main results

* `AlgHom.cliffordReverseDual_complexVolume`: `Γ` acts on the reverse dual by
  `(-1) ^ ⌊n / 2⌋ Γ_Sᵀ`.
* `AlgHom.eigenspace_cliffordReverseDual_complexVolume`: the `μ`-eigenspace of `Γ` on the
  reverse dual is the annihilator of the `-(-1) ^ ⌊n / 2⌋ μ`-eigenspace of `Γ` on `S`.
* `AlgHom.cliffordReverseDualComplexVolumeEigenspaceEquiv`: restriction identifies the
  `μ`-eigenspace of `Γ` on the reverse dual with the dual of the `(-1) ^ ⌊n / 2⌋ μ`-eigenspace of
  `Γ` on `S`, and `AlgHom.finrank_eigenspace_cliffordReverseDual_complexVolume` gives the
  dimension count.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open CliffordAlgebra Module Module.End

namespace AlgHom

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V}
variable {S : Type*} [AddCommGroup S] [Module ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) (o : Orientation ℝ V (Fin n))

/-- **The chirality of the reverse dual**: the normalized complex volume element `Γ` acts on the
reverse dual by `(-1) ^ ⌊n / 2⌋` times the transpose of its action on `S`. In dimension `2ℓ`
this is `(-1) ^ ℓ Γ_Sᵀ`. -/
@[simp]
theorem cliffordReverseDual_complexVolume :
    cliffordReverseDual ρ (complexVolume Q o) =
      (-1 : ℂ) ^ (n / 2) • (ρ (complexVolume Q o)).dualMap := by
  ext φ s
  simp [cliffordReverseDual_apply_apply, reverse_complexVolume]

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- For `Q v = -‖v‖²`, the element `Γ` acts on every module as an involution. -/
private theorem involutive_complexVolume :
    Function.Involutive (ρ (complexVolume Q o)) := fun s ↦ by
  rw [← mul_apply_eq_comp, ← map_mul, complexVolume_mul_self o hQ, map_one, one_apply_eq_self]

/-- The `±1`-eigenspaces of `Γ` on a module are complementary. -/
private theorem isCompl_eigenspace_complexVolume_neg {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    IsCompl ((ρ (complexVolume Q o)).eigenspace μ) ((ρ (complexVolume Q o)).eigenspace (-μ)) := by
  have h := TauCeti.isCompl_eigenspace_one_neg_one two_ne_zero.isUnit
    (involutive_complexVolume ρ o hQ)
  rcases hμ with rfl | rfl
  · exact h
  · rw [neg_neg]
    exact h.symm

/-- **The chirality decomposition of the reverse dual**: for `μ = ±1`, the `μ`-eigenspace of
`Γ` on the reverse dual consists of the functionals vanishing on the
`-(-1) ^ ⌊n / 2⌋ μ`-eigenspace of `Γ` on `S`. -/
theorem eigenspace_cliffordReverseDual_complexVolume {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    (cliffordReverseDual ρ (complexVolume Q o)).eigenspace μ =
      ((ρ (complexVolume Q o)).eigenspace (-((-1) ^ (n / 2) * μ))).dualAnnihilator := by
  have hinv := involutive_complexVolume ρ o hQ
  have hμ' : μ * μ = 1 := by rcases hμ with rfl | rfl <;> norm_num
  rcases neg_one_pow_eq_or ℂ (n / 2) with h | h
  · rw [cliffordReverseDual_complexVolume, h, one_smul, one_mul]
    exact eigenspace_dualMap_eq_dualAnnihilator two_ne_zero.isUnit hinv hμ'
  · have hneg : Function.Involutive (-ρ (complexVolume Q o)) := fun s ↦ by
      simp [hinv s]
    have hdual : cliffordReverseDual ρ (complexVolume Q o) = (-ρ (complexVolume Q o)).dualMap := by
      ext φ s
      simp [h]
    rw [hdual, eigenspace_dualMap_eq_dualAnnihilator two_ne_zero.isUnit hneg hμ']
    congr 1
    ext s
    simp [h, neg_eq_iff_eq_neg]

/-- **The eigenspaces of `Γ` on the reverse dual**: for `μ = ±1`, restriction of functionals
identifies the `μ`-eigenspace of `Γ` on the reverse dual with the dual of the
`(-1) ^ ⌊n / 2⌋ μ`-eigenspace of `Γ` on `S`. In dimension `2ℓ` this identifies the half-spinors
of the reverse dual with the duals of the half-spinors of `S`, exchanging the labels when `ℓ` is
odd. -/
def cliffordReverseDualComplexVolumeEigenspaceEquiv {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    (cliffordReverseDual ρ (complexVolume Q o)).eigenspace μ ≃ₗ[ℂ]
      Dual ℂ ((ρ (complexVolume Q o)).eigenspace ((-1) ^ (n / 2) * μ)) :=
  (LinearEquiv.ofEq _ _ (eigenspace_cliffordReverseDual_complexVolume ρ o hQ hμ)).trans
    (Submodule.dualAnnihilatorEquivOfIsCompl _ _ (isCompl_eigenspace_complexVolume_neg ρ o hQ
      (TauCeti.neg_one_pow_mul_eq_or hμ (n / 2))))

/-- The identification `AlgHom.cliffordReverseDualComplexVolumeEigenspaceEquiv` restricts a
functional. -/
@[simp]
theorem cliffordReverseDualComplexVolumeEigenspaceEquiv_apply {μ : ℂ} (hμ : μ = 1 ∨ μ = -1)
    (φ : (cliffordReverseDual ρ (complexVolume Q o)).eigenspace μ)
    (s : (ρ (complexVolume Q o)).eigenspace ((-1) ^ (n / 2) * μ)) :
    cliffordReverseDualComplexVolumeEigenspaceEquiv ρ o hQ hμ φ s = (φ : Dual ℂ S) s := by
  simp [cliffordReverseDualComplexVolumeEigenspaceEquiv]

/-- The inverse of `AlgHom.cliffordReverseDualComplexVolumeEigenspaceEquiv` agrees with the
given functional on the `(-1) ^ ⌊n / 2⌋ μ`-eigenspace of `Γ` on `S`. -/
@[simp]
theorem coe_cliffordReverseDualComplexVolumeEigenspaceEquiv_symm_apply_of_mem {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1)
    (ψ : Dual ℂ ((ρ (complexVolume Q o)).eigenspace ((-1) ^ (n / 2) * μ))) {s : S}
    (hs : s ∈ (ρ (complexVolume Q o)).eigenspace ((-1) ^ (n / 2) * μ)) :
    ((cliffordReverseDualComplexVolumeEigenspaceEquiv ρ o hQ hμ).symm ψ : Dual ℂ S) s =
      ψ ⟨s, hs⟩ := by
  simpa [cliffordReverseDualComplexVolumeEigenspaceEquiv] using
    LinearMap.ofIsCompl_apply_left (φ := ψ) (ψ := 0) _ ⟨s, hs⟩

/-- The inverse of `AlgHom.cliffordReverseDualComplexVolumeEigenspaceEquiv` vanishes on the
`-(-1) ^ ⌊n / 2⌋ μ`-eigenspace of `Γ` on `S`: it extends a functional by zero. -/
@[simp]
theorem coe_cliffordReverseDualComplexVolumeEigenspaceEquiv_symm_apply_of_mem_neg {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1)
    (ψ : Dual ℂ ((ρ (complexVolume Q o)).eigenspace ((-1) ^ (n / 2) * μ))) {s : S}
    (hs : s ∈ (ρ (complexVolume Q o)).eigenspace (-((-1) ^ (n / 2) * μ))) :
    ((cliffordReverseDualComplexVolumeEigenspaceEquiv ρ o hQ hμ).symm ψ : Dual ℂ S) s = 0 := by
  simpa [cliffordReverseDualComplexVolumeEigenspaceEquiv] using
    LinearMap.ofIsCompl_apply_right (φ := ψ) (ψ := 0) _ ⟨s, hs⟩

/-- For `μ = ±1`, the `μ`-eigenspace of `Γ` on the reverse dual has the dimension of the
`(-1) ^ ⌊n / 2⌋ μ`-eigenspace of `Γ` on `S`. As usual for `Module.finrank`, both sides are `0`
when that eigenspace is infinite-dimensional. -/
theorem finrank_eigenspace_cliffordReverseDual_complexVolume {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((cliffordReverseDual ρ (complexVolume Q o)).eigenspace μ) =
      finrank ℂ ((ρ (complexVolume Q o)).eigenspace ((-1) ^ (n / 2) * μ)) := by
  rw [(cliffordReverseDualComplexVolumeEigenspaceEquiv ρ o hQ hμ).finrank_eq,
    Subspace.dual_finrank_eq]

end Form

end AlgHom
