/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Data.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.OfReal
import Mathlib.LinearAlgebra.Matrix.Integer
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The Siegel upper half space and the action of the integral symplectic group

The **Siegel upper half space** of genus `g` is the set
`H_g = {Ω ∈ M_g(ℂ) | Ωᵀ = Ω, Im Ω positive definite}`
(`TauCeti.SiegelUpperHalfSpace g`). An integral block matrix `M = [[A, B], [C, D]]` acts on period
matrices by the fractional linear formula `M · Ω = (A Ω + B) (C Ω + D)⁻¹`
(`TauCeti.siegelAction`), defined for all integral block matrices and all complex period matrices
through Mathlib's matrix inverse; `A Ω + B` is `TauCeti.siegelNumerator M Ω` and `C Ω + D` is the
automorphy factor `TauCeti.siegelFactor M Ω`.

For a symplectic `M` and `Ω ∈ H_g`, write `P = A Ω + B` and `Q = C Ω + D`. The symplectic relations
`Aᵀ C = Cᵀ A`, `Bᵀ D = Dᵀ B`, `Aᵀ D - Cᵀ B = 1` give `Pᵀ Q = Qᵀ P` and
`Qᴴ P - Pᴴ Q = Ω - Ωᴴ = 2 i Im Ω`. The second identity shows that `Q` is injective, hence
invertible, and that `Im (P Q⁻¹) = Q⁻ᴴ (Im Ω) Q⁻¹`; the first shows that `P Q⁻¹` is symmetric. So
the symplectic group preserves `H_g` (`TauCeti.siegelAction_mem`), and the action is compatible
with products (`TauCeti.siegelAction_mul`), with the cocycle relation for the automorphy factor
(`TauCeti.siegelFactor_mul`).

This is the period domain and its symplectic action, in the column convention for the lattice
`ℤ^g + Ω ℤ^g`. Mathlib's `Matrix.J` is `[[0, -1], [1, 0]]`; its symplectic group is the usual one.

## Main definitions

* `TauCeti.SiegelUpperHalfSpace g`: the Siegel upper half space of genus `g`.
* `TauCeti.siegelNumerator M Ω`: the numerator `A Ω + B`.
* `TauCeti.siegelFactor M Ω`: the automorphy factor `C Ω + D`.
* `TauCeti.siegelAction M Ω`: the fractional linear action `(A Ω + B) (C Ω + D)⁻¹`.
* `TauCeti.siegelUpperHalfSpaceOneEquiv`: the genus-one Siegel space is the upper half plane.

## Main results

* `TauCeti.mem_siegelUpperHalfSpace_one_iff`: in genus one, `Ω ∈ H_1` exactly when
  `0 < Im Ω₀₀`.
* `TauCeti.siegelUpperHalfSpace_zero`: in genus zero, `H_0` is the single empty matrix.
* `TauCeti.SiegelUpperHalfSpace.det_im_ne_zero`: a period matrix with singular imaginary part is
  not in `H_g`.
* `TauCeti.siegelAction_one` and `TauCeti.siegelAction_translation`: the identity fixes every
  period matrix and `[[1, B], [0, 1]]` sends `Ω` to `Ω + B`.
* `TauCeti.transpose_siegelNumerator_mul_siegelFactor` and
  `TauCeti.conjTranspose_siegelFactor_mul_siegelNumerator_sub`: for symplectic `M` and symmetric
  `Ω`, `Pᵀ Q = Qᵀ P` and `Qᴴ P - Pᴴ Q = Ω - Ωᴴ`.
* `TauCeti.isUnit_det_siegelFactor`: for symplectic `M` and `Ω ∈ H_g`, `C Ω + D` is invertible.
* `TauCeti.transpose_siegelAction` and `TauCeti.siegelAction_map_im_map_ofReal`: for symplectic
  `M` and `Ω ∈ H_g`, `M · Ω` is symmetric with `Im (M · Ω) = Q⁻ᴴ (Im Ω) Q⁻¹`, `Q = C Ω + D`.
* `TauCeti.siegelAction_mem`: for symplectic `M` and `Ω ∈ H_g`, `M · Ω ∈ H_g`.
* `TauCeti.siegelAction_mul` and `TauCeti.siegelFactor_mul`: `(M N) · Ω = M · (N · Ω)` and
  `j(M N, Ω) = j(M, N · Ω) j(N, Ω)` for symplectic `N` and `Ω ∈ H_g`.

## References

* Faltings–Chai, I.6, pp. 29–30, for the Siegel space and the action of `Sp_{2g}(ℤ)`.
-/

public section

open Matrix Complex

open scoped ComplexOrder

namespace TauCeti

variable {g : ℕ}

/-! ### The Siegel upper half space -/

/-- The **Siegel upper half space** of genus `g`: the complex symmetric `g × g` matrices `Ω` whose
imaginary part `Im Ω` is positive definite. -/
def SiegelUpperHalfSpace (g : ℕ) : Set (Matrix (Fin g) (Fin g) ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

theorem mem_siegelUpperHalfSpace_iff {Ω : Matrix (Fin g) (Fin g) ℂ} :
    Ω ∈ SiegelUpperHalfSpace g ↔ Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef :=
  Iff.rfl

namespace SiegelUpperHalfSpace

variable {Ω : Matrix (Fin g) (Fin g) ℂ}

theorem transpose_eq (hΩ : Ω ∈ SiegelUpperHalfSpace g) : Ωᵀ = Ω :=
  hΩ.1

theorem posDef_im (hΩ : Ω ∈ SiegelUpperHalfSpace g) : (Ω.map Complex.im).PosDef :=
  hΩ.2

/-- **A period matrix with singular imaginary part is not in the Siegel space.** -/
theorem det_im_ne_zero (hΩ : Ω ∈ SiegelUpperHalfSpace g) : (Ω.map Complex.im).det ≠ 0 :=
  hΩ.2.det_pos.ne'

theorem notMem_of_det_im_eq_zero (h : (Ω.map Complex.im).det = 0) :
    Ω ∉ SiegelUpperHalfSpace g :=
  fun hΩ ↦ det_im_ne_zero hΩ h

end SiegelUpperHalfSpace

/-- **Genus one.** A `1 × 1` period matrix lies in the Siegel space exactly when its entry lies in
the upper half plane. -/
theorem mem_siegelUpperHalfSpace_one_iff {Ω : Matrix (Fin 1) (Fin 1) ℂ} :
    Ω ∈ SiegelUpperHalfSpace 1 ↔ 0 < (Ω 0 0).im := by
  have hΩ : Ω.map Complex.im = diagonal fun _ ↦ (Ω 0 0).im := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp
  rw [mem_siegelUpperHalfSpace_iff, hΩ, posDef_diagonal_iff]
  refine ⟨fun h ↦ h.2 0, fun h ↦ ⟨?_, fun _ ↦ h⟩⟩
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, transpose_apply]

/-- **The genus-one Siegel space is the upper half plane**, through `τ ↦ (τ)`. -/
noncomputable def siegelUpperHalfSpaceOneEquiv : UpperHalfPlane ≃ SiegelUpperHalfSpace 1 where
  toFun τ := ⟨of fun _ _ ↦ (τ : ℂ), mem_siegelUpperHalfSpace_one_iff.2 τ.im_pos⟩
  invFun Ω := ⟨Ω.val 0 0, mem_siegelUpperHalfSpace_one_iff.1 Ω.property⟩
  left_inv τ := rfl
  right_inv Ω := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl

@[simp]
theorem coe_siegelUpperHalfSpaceOneEquiv_apply (τ : UpperHalfPlane) (i j : Fin 1) :
    (siegelUpperHalfSpaceOneEquiv τ : Matrix (Fin 1) (Fin 1) ℂ) i j = τ :=
  (rfl)

@[simp]
theorem coe_siegelUpperHalfSpaceOneEquiv_symm_apply (Ω : SiegelUpperHalfSpace 1) :
    (siegelUpperHalfSpaceOneEquiv.symm Ω : ℂ) = (Ω : Matrix (Fin 1) (Fin 1) ℂ) 0 0 :=
  (rfl)

/-- **Genus zero.** The Siegel space of genus zero is the single (empty) matrix. -/
theorem siegelUpperHalfSpace_zero : SiegelUpperHalfSpace 0 = {0} := by
  ext Ω
  rw [Set.mem_singleton_iff, Subsingleton.elim Ω 0, eq_self_iff_true, iff_true]
  refine ⟨Subsingleton.elim _ _, PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_⟩
  · exact Subsingleton.elim _ _
  · exact (hx (Subsingleton.elim x 0)).elim

/-! ### The action of integral block matrices -/

/-- The **numerator** `A Ω + B` of the fractional linear action of an integral block matrix
`M = [[A, B], [C, D]]` at a complex `g × g` matrix `Ω`. -/
def siegelNumerator (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (M.map ((↑) : ℤ → ℂ)).toBlocks₁₁ * Ω + (M.map ((↑) : ℤ → ℂ)).toBlocks₁₂

/-- The **automorphy factor** `C Ω + D` of an integral block matrix `M = [[A, B], [C, D]]` at a
complex `g × g` matrix `Ω`. -/
def siegelFactor (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Ω : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (M.map ((↑) : ℤ → ℂ)).toBlocks₂₁ * Ω + (M.map ((↑) : ℤ → ℂ)).toBlocks₂₂

/-- The **action of an integral block matrix** `M = [[A, B], [C, D]]` on complex `g × g` matrices:
`M · Ω = (A Ω + B) (C Ω + D)⁻¹`, with Mathlib's matrix inverse (which is `0` when `C Ω + D` is
singular). For symplectic `M` it preserves the Siegel space (`TauCeti.siegelAction_mem`). -/
noncomputable def siegelAction (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  siegelNumerator M Ω * (siegelFactor M Ω)⁻¹

theorem siegelNumerator_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelNumerator M Ω = (M.map ((↑) : ℤ → ℂ)).toBlocks₁₁ * Ω + (M.map ((↑) : ℤ → ℂ)).toBlocks₁₂ :=
  (rfl)

theorem siegelFactor_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelFactor M Ω = (M.map ((↑) : ℤ → ℂ)).toBlocks₂₁ * Ω + (M.map ((↑) : ℤ → ℂ)).toBlocks₂₂ :=
  (rfl)

theorem siegelAction_def (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelAction M Ω = siegelNumerator M Ω * (siegelFactor M Ω)⁻¹ :=
  (rfl)

@[simp]
theorem siegelNumerator_one (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelNumerator 1 Ω = Ω := by
  simp [siegelNumerator_def, ← fromBlocks_one, fromBlocks_map]

@[simp]
theorem siegelFactor_one (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelFactor 1 Ω = 1 := by
  simp [siegelFactor_def, ← fromBlocks_one, fromBlocks_map]

/-- The identity fixes every period matrix. -/
@[simp]
theorem siegelAction_one (Ω : Matrix (Fin g) (Fin g) ℂ) : siegelAction 1 Ω = Ω := by
  rw [siegelAction_def, siegelNumerator_one, siegelFactor_one, inv_one, Matrix.mul_one]

@[simp]
theorem siegelNumerator_translation (B : Matrix (Fin g) (Fin g) ℤ)
    (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelNumerator (fromBlocks 1 B 0 1) Ω = Ω + B.map ((↑) : ℤ → ℂ) := by
  simp [siegelNumerator_def, fromBlocks_map]

@[simp]
theorem siegelFactor_translation (B : Matrix (Fin g) (Fin g) ℤ) (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelFactor (fromBlocks 1 B 0 1) Ω = 1 := by
  simp [siegelFactor_def, fromBlocks_map]

/-- **Translations.** The matrix `[[1, B], [0, 1]]` sends `Ω` to `Ω + B`. -/
@[simp]
theorem siegelAction_translation (B : Matrix (Fin g) (Fin g) ℤ) (Ω : Matrix (Fin g) (Fin g) ℂ) :
    siegelAction (fromBlocks 1 B 0 1) Ω = Ω + B.map ((↑) : ℤ → ℂ) := by
  rw [siegelAction_def, siegelNumerator_translation, siegelFactor_translation, inv_one,
    Matrix.mul_one]

section Symplectic

variable {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}

/-- The symplectic relations on the complex blocks of an integral symplectic matrix. -/
private theorem symplectic_relations (hM : M ∈ symplecticGroup (Fin g) ℤ) :
    let X := M.map ((↑) : ℤ → ℂ)
    X.toBlocks₁₁ᵀ * X.toBlocks₂₁ = X.toBlocks₂₁ᵀ * X.toBlocks₁₁ ∧
      X.toBlocks₁₂ᵀ * X.toBlocks₂₂ = X.toBlocks₂₂ᵀ * X.toBlocks₁₂ ∧
      X.toBlocks₁₁ᵀ * X.toBlocks₂₂ - X.toBlocks₂₁ᵀ * X.toBlocks₁₂ = 1 := by
  intro X
  exact SymplecticGroup.mem_iff_toBlocks.1 (SymplecticGroup.map_mem hM (Int.castRingHom ℂ))

variable {Ω : Matrix (Fin g) (Fin g) ℂ}

/-- The identities `Pᵀ Q = Qᵀ P` and `Qᴴ P - Pᴴ Q = Ω - Ωᴴ` for `P = A Ω + B` and `Q = C Ω + D`,
for real blocks satisfying the symplectic relations and a symmetric `Ω`. -/
private theorem key_identities_aux {A B C D Ω : Matrix (Fin g) (Fin g) ℂ}
    (h₁ : Aᵀ * C = Cᵀ * A) (h₂ : Bᵀ * D = Dᵀ * B) (h₃ : Aᵀ * D - Cᵀ * B = 1) (hA : Aᴴ = Aᵀ)
    (hB : Bᴴ = Bᵀ) (hC : Cᴴ = Cᵀ) (hD : Dᴴ = Dᵀ) (hΩ : Ωᵀ = Ω) :
    (A * Ω + B)ᵀ * (C * Ω + D) = (C * Ω + D)ᵀ * (A * Ω + B) ∧
      (C * Ω + D)ᴴ * (A * Ω + B) - (A * Ω + B)ᴴ * (C * Ω + D) = Ω - Ωᴴ := by
  have h₄ : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg transpose h₃
  constructor
  · rw [← sub_eq_zero]
    calc _ = Ωᵀ * (Aᵀ * C - Cᵀ * A) * Ω + Ωᵀ * (Aᵀ * D - Cᵀ * B) +
          (Bᵀ * C - Dᵀ * A) * Ω + (Bᵀ * D - Dᵀ * B) := by
          simp only [transpose_add, transpose_mul]
          noncomm_ring
      _ = 0 := by
          rw [h₁, h₂, h₃, ← neg_sub (Dᵀ * A) (Bᵀ * C), h₄, hΩ]
          noncomm_ring
  · calc _ = Ωᴴ * (Cᵀ * A - Aᵀ * C) * Ω + Ωᴴ * (Cᵀ * B - Aᵀ * D) +
          (Dᵀ * A - Bᵀ * C) * Ω + (Dᵀ * B - Bᵀ * D) := by
          simp only [conjTranspose_add, conjTranspose_mul, hA, hB, hC, hD]
          noncomm_ring
      _ = Ω - Ωᴴ := by
          rw [h₁, h₂, ← neg_sub (Aᵀ * D) (Cᵀ * B), h₃, h₄]
          noncomm_ring

/-- For symplectic `M = [[A, B], [C, D]]` and symmetric `Ω`, the numerator `P = A Ω + B` and the
automorphy factor `Q = C Ω + D` satisfy `Pᵀ Q = Qᵀ P`. -/
theorem transpose_siegelNumerator_mul_siegelFactor (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ωᵀ = Ω) :
    (siegelNumerator M Ω)ᵀ * siegelFactor M Ω = (siegelFactor M Ω)ᵀ * siegelNumerator M Ω := by
  obtain ⟨h₁, h₂, h₃⟩ := symplectic_relations hM
  exact (key_identities_aux h₁ h₂ h₃ (conjTranspose_map_intCast _) (conjTranspose_map_intCast _)
    (conjTranspose_map_intCast _) (conjTranspose_map_intCast _) hΩ).1

/-- For symplectic `M = [[A, B], [C, D]]` and symmetric `Ω`, the numerator `P = A Ω + B` and the
automorphy factor `Q = C Ω + D` satisfy `Qᴴ P - Pᴴ Q = Ω - Ωᴴ`. -/
theorem conjTranspose_siegelFactor_mul_siegelNumerator_sub
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hΩ : Ωᵀ = Ω) :
    (siegelFactor M Ω)ᴴ * siegelNumerator M Ω - (siegelNumerator M Ω)ᴴ * siegelFactor M Ω =
      Ω - Ωᴴ := by
  obtain ⟨h₁, h₂, h₃⟩ := symplectic_relations hM
  exact (key_identities_aux h₁ h₂ h₃ (conjTranspose_map_intCast _) (conjTranspose_map_intCast _)
    (conjTranspose_map_intCast _) (conjTranspose_map_intCast _) hΩ).2

/-- **The automorphy factor is invertible.** For symplectic `M` and `Ω` in the Siegel space,
`C Ω + D` is invertible. -/
theorem isUnit_det_siegelFactor (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : IsUnit (siegelFactor M Ω).det := by
  -- if `Q v = 0` for `Q = C Ω + D`, then `v* (Im Ω) v = 0` by `Qᴴ P - Pᴴ Q = 2 i Im Ω`, so `v = 0`
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have h := conjTranspose_siegelFactor_mul_siegelNumerator_sub hM
    (SiegelUpperHalfSpace.transpose_eq hΩ)
  set P := siegelNumerator M Ω
  set Q := siegelFactor M Ω
  have key : star v ⬝ᵥ ((Qᴴ * P - Pᴴ * Q) *ᵥ v) = 0 := by
    simp [sub_mulVec, ← mulVec_mulVec, hv, dotProduct_mulVec, ← star_mulVec]
  have hY := ((SiegelUpperHalfSpace.posDef_im hΩ).map_ofReal).dotProduct_mulVec_pos hv0
  rw [map_im_map_ofReal_of_transpose_eq (SiegelUpperHalfSpace.transpose_eq hΩ), ← h,
    smul_mulVec, dotProduct_smul, key, smul_zero] at hY
  exact lt_irrefl _ hY

/-- **The action is symmetric.** For symplectic `M` and `Ω` in the Siegel space, `M · Ω` is a
symmetric matrix. -/
theorem transpose_siegelAction (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : (siegelAction M Ω)ᵀ = siegelAction M Ω := by
  have h₁ := transpose_siegelNumerator_mul_siegelFactor hM (SiegelUpperHalfSpace.transpose_eq hΩ)
  have hQ := isUnit_det_siegelFactor hM hΩ
  set P := siegelNumerator M Ω
  set Q := siegelFactor M Ω
  rw [siegelAction_def, transpose_mul, transpose_nonsing_inv]
  have hQt : IsUnit Qᵀ.det := by rwa [det_transpose]
  calc (Qᵀ)⁻¹ * Pᵀ = (Qᵀ)⁻¹ * (Pᵀ * Q) * Q⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hQ]
    _ = P * Q⁻¹ := by rw [h₁, nonsing_inv_mul_cancel_left _ _ hQt]

/-- **The imaginary part of the action.** For symplectic `M` and `Ω` in the Siegel space,
`Im (M · Ω) = Q⁻ᴴ (Im Ω) Q⁻¹` as complex matrices, where `Q = C Ω + D`. -/
theorem siegelAction_map_im_map_ofReal (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    ((siegelAction M Ω).map Complex.im).map ((↑) : ℝ → ℂ) =
      (siegelFactor M Ω)⁻¹ᴴ * (Ω.map Complex.im).map ((↑) : ℝ → ℂ) * (siegelFactor M Ω)⁻¹ := by
  have h₂ := conjTranspose_siegelFactor_mul_siegelNumerator_sub hM
    (SiegelUpperHalfSpace.transpose_eq hΩ)
  have hQ := isUnit_det_siegelFactor hM hΩ
  rw [map_im_map_ofReal_of_transpose_eq (transpose_siegelAction hM hΩ),
    map_im_map_ofReal_of_transpose_eq (SiegelUpperHalfSpace.transpose_eq hΩ), ← h₂,
    Matrix.mul_smul, Matrix.smul_mul, siegelAction_def]
  set P := siegelNumerator M Ω
  set Q := siegelFactor M Ω
  congr 1
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · have hQh : IsUnit Qᴴ.det := by rwa [det_conjTranspose, isUnit_star]
    rw [conjTranspose_nonsing_inv, nonsing_inv_mul_cancel_left _ _ hQh]
  · rw [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hQ]

/-- **The symplectic group preserves the Siegel space.** For symplectic `M` and `Ω` in the Siegel
space, `M · Ω` lies in the Siegel space: it is symmetric (`TauCeti.transpose_siegelAction`) with
imaginary part `Q⁻ᴴ (Im Ω) Q⁻¹` (`TauCeti.siegelAction_map_im_map_ofReal`). -/
theorem siegelAction_mem (hM : M ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) : siegelAction M Ω ∈ SiegelUpperHalfSpace g := by
  refine ⟨transpose_siegelAction hM hΩ, ?_⟩
  have hQ := isUnit_det_siegelFactor hM hΩ
  have hinj : Function.Injective (siegelFactor M Ω)⁻¹.mulVec :=
    mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hQ))
  have hpos := ((SiegelUpperHalfSpace.posDef_im hΩ).map_ofReal).conjTranspose_mul_mul_same hinj
  rw [← siegelAction_map_im_map_ofReal hM hΩ] at hpos
  convert hpos.map_re using 1
  ext i j
  simp

end Symplectic

section Mul

variable {M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {Ω : Matrix (Fin g) (Fin g) ℂ}

/-- Multiplying the numerator and the automorphy factor of `M` at `N · Ω` by `Q = j(N, Ω)` clears
the inverse: they become `A_M P + B_M Q` and `C_M P + D_M Q`, where `P = A_N Ω + B_N`. -/
private theorem siegelNumerator_siegelFactor_mul_of_isUnit (hN : IsUnit (siegelFactor N Ω).det) :
    siegelNumerator M (siegelAction N Ω) * siegelFactor N Ω =
        (M.map ((↑) : ℤ → ℂ)).toBlocks₁₁ * siegelNumerator N Ω +
          (M.map ((↑) : ℤ → ℂ)).toBlocks₁₂ * siegelFactor N Ω ∧
      siegelFactor M (siegelAction N Ω) * siegelFactor N Ω =
        (M.map ((↑) : ℤ → ℂ)).toBlocks₂₁ * siegelNumerator N Ω +
          (M.map ((↑) : ℤ → ℂ)).toBlocks₂₂ * siegelFactor N Ω := by
  rw [siegelNumerator_def M, siegelFactor_def M, siegelAction_def]
  constructor <;> rw [Matrix.add_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_right _ _ hN]

/-- **The cocycle relation for the numerator**, `A_{MN} Ω + B_{MN} = (A_M (N · Ω) + B_M) j(N, Ω)`,
whenever `j(N, Ω)` is invertible. -/
theorem siegelNumerator_mul_of_isUnit (hN : IsUnit (siegelFactor N Ω).det) :
    siegelNumerator (M * N) Ω = siegelNumerator M (siegelAction N Ω) * siegelFactor N Ω := by
  rw [(siegelNumerator_siegelFactor_mul_of_isUnit hN).1, siegelNumerator_def, siegelNumerator_def,
    siegelFactor_def, map_mul_intCast, toBlocks₁₁_mul, toBlocks₁₂_mul]
  noncomm_ring

/-- **The cocycle relation** `j(M N, Ω) = j(M, N · Ω) j(N, Ω)` for the automorphy factor, whenever
`j(N, Ω)` is invertible. -/
theorem siegelFactor_mul_of_isUnit (hN : IsUnit (siegelFactor N Ω).det) :
    siegelFactor (M * N) Ω = siegelFactor M (siegelAction N Ω) * siegelFactor N Ω := by
  rw [(siegelNumerator_siegelFactor_mul_of_isUnit hN).2, siegelNumerator_def, siegelFactor_def,
    siegelFactor_def, map_mul_intCast, toBlocks₂₁_mul, toBlocks₂₂_mul]
  noncomm_ring

/-- **Compatibility with products**, whenever `j(N, Ω)` is invertible. -/
theorem siegelAction_mul_of_isUnit (hN : IsUnit (siegelFactor N Ω).det) :
    siegelAction (M * N) Ω = siegelAction M (siegelAction N Ω) := by
  rw [siegelAction_def (M * N), siegelNumerator_mul_of_isUnit hN, siegelFactor_mul_of_isUnit hN,
    Matrix.mul_inv_rev, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hN, siegelAction_def M]

/-- **The cocycle relation for the numerator** for symplectic `N` and `Ω` in the Siegel space. -/
theorem siegelNumerator_mul (hN : N ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelNumerator (M * N) Ω = siegelNumerator M (siegelAction N Ω) * siegelFactor N Ω :=
  siegelNumerator_mul_of_isUnit (isUnit_det_siegelFactor hN hΩ)

/-- **The cocycle relation** for symplectic `N` and `Ω` in the Siegel space. -/
theorem siegelFactor_mul (hN : N ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelFactor (M * N) Ω = siegelFactor M (siegelAction N Ω) * siegelFactor N Ω :=
  siegelFactor_mul_of_isUnit (isUnit_det_siegelFactor hN hΩ)

/-- **The action is compatible with products:** `(M N) · Ω = M · (N · Ω)` for symplectic `N` and
`Ω` in the Siegel space. -/
theorem siegelAction_mul (hN : N ∈ symplecticGroup (Fin g) ℤ)
    (hΩ : Ω ∈ SiegelUpperHalfSpace g) :
    siegelAction (M * N) Ω = siegelAction M (siegelAction N Ω) :=
  siegelAction_mul_of_isUnit (isUnit_det_siegelFactor hN hΩ)

end Mul

end TauCeti
