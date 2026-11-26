/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.FrameChange
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# Loops of symplectic matrices preserving a coordinate Lagrangian have Maslov index zero

Split `ℝ²ⁿ = ℝⁿ ⊕ ℝⁿ` into positions and momenta, as in the symplectic frames `(∂_q, ∂_p)` of a
cotangent bundle, with the standard form `Matrix.J`. A symplectic matrix

`M = [[A, B], [C, D]]`

preserves the *vertical* Lagrangian `0 ⊕ ℝⁿ`, spanned by the momentum directions, exactly when
`B = 0`, and the *horizontal* Lagrangian `ℝⁿ ⊕ 0` exactly when `C = 0`. This file proves that a loop
of symplectic matrices preserving either one has Maslov index zero
(`TauCeti.GLSymplectic.maslovIndex_eq_zero_of_toBlocks₁₂_eq_zero`,
`TauCeti.GLSymplectic.maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero`). So the Conley–Zehnder index of
a path of symplectic matrices does not change when its frame is changed along a loop preserving the
vertical Lagrangian (`TauCeti.GLSymplectic.conleyZehnderIndex_frameChange_of_toBlocks₁₂_eq_zero`):
by the frame-change law `CZ(g⁻¹ Ψ g(0)) = CZ(Ψ) + 2 μ(g)`, the correction vanishes.

This is the independence statement behind the canonical grading of the Floer homology of a
cotangent bundle `T*Q` (Barraud–Damian–Humilière–Oancea, §4.2): along a `1`-periodic orbit, the
symplectic frames of `T(T*Q)` taken to send the vertical distribution to the momentum directions
differ by a loop preserving the vertical Lagrangian, so they all give the same Conley–Zehnder
index.

The proof has two steps.

* **The Levi subgroup.** On a block diagonal symplectic matrix `diag(A, A⁻ᵀ)`, the image of `A`
  under the Levi embedding `TauCeti.GLSymplectic.leviHom`, the map `ρ` defining the Maslov index is
  the sign of `det A` (`TauCeti.GLSymplectic.maslovPhase_leviHom`). Indeed if `A = P U` is the polar
  decomposition of `A`, then `diag(A, A⁻ᵀ) = diag(P, P⁻¹) diag(U, U)` is the polar decomposition of
  `diag(A, A⁻ᵀ)` (`TauCeti.GLSymplectic.coe_polarUnitary_leviHom`), and `diag(U, U)` is the
  realification of the real orthogonal matrix `U`, whose complex determinant is
  `det U = sign (det A)`. A loop along which `ρ` takes only the values `1` and `-1` has constant
  `ρ`, hence Maslov index zero
  (`TauCeti.GLSymplectic.maslovIndex_eq_zero_of_forall_maslovPhase_sq_eq_one`).
* **Contracting the off-diagonal block.** If `B = 0`, the symplectic condition reads `Aᵀ D = 1` and
  `Aᵀ C = Cᵀ A` (`SymplecticGroup.fromBlocks_zero₁₂_mem_iff`), which persist when `C` is replaced
  by `s C`. So `s ↦ [[A, 0], [s C, D]]`, `s ∈ [0, 1]`, deforms a loop preserving the vertical
  Lagrangian through such loops into a loop in the Levi subgroup
  (`TauCeti.GLSymplectic.exists_leviHom_eq_of_toBlocks₁₂_eq_zero_of_toBlocks₂₁_eq_zero`), without
  changing its Maslov index. The horizontal case is the vertical one conjugated by `J`, which
  exchanges the two Lagrangians, and the Maslov index is invariant under conjugation
  (`TauCeti.GLSymplectic.maslovIndex_map_conj`).

The first step does not extend to the whole stabilizer: on the shear `[[1, 0], [c, 1]]` of
`Sp(2, ℝ)`, `c ≠ 0`, the orthogonal polar factor is a rotation by a nonzero angle, so `ρ` is not
`±1`. Only the loops, not the individual matrices, see a trivial Maslov phase. Nor does the
vanishing hold without the Lagrangian condition: the loop `t ↦ e^{2π i t}` of `U(1) ⊆ Sp(2, ℝ)`,
whose rotations by angles other than `0` and `π` preserve no line, has Maslov index `1`
(`TauCeti.GLSymplectic.maslovIndex_scalarRotationLoop`).

## Main results

* `TauCeti.GLSymplectic.maslovPhase_leviHom`: `ρ(diag(A, A⁻ᵀ)) = sign (det A)`.
* `TauCeti.GLSymplectic.maslovIndex_eq_zero_of_toBlocks₁₂_eq_zero`: a loop of symplectic matrices
  preserving the vertical Lagrangian has Maslov index zero.
* `TauCeti.GLSymplectic.maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero`: the same for the horizontal
  Lagrangian.
* `TauCeti.GLSymplectic.conleyZehnderIndex_frameChange_of_toBlocks₁₂_eq_zero`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_frameChange_of_toBlocks₂₁_eq_zero`: changing the frame
  along such a loop keeps the Conley–Zehnder index.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of the Floer
  homology of `T*Q`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford Graduate
  Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (the map `ρ` and the Maslov
  index of loops of symplectic matrices).
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup
open scoped MatrixOrder unitInterval

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The map `ρ` on the Levi subgroup -/

/-- **`ρ` on the Levi subgroup.** The map `ρ` sends the block diagonal symplectic matrix
`diag(A, A⁻ᵀ)` to the sign of `det A`: the orthogonal polar factor `diag(U, U)` is the
realification of the real orthogonal matrix `U`, whose determinant is `det A / |det A|`. -/
theorem maslovPhase_leviHom (A : GL n ℝ) :
    (maslovPhase (leviHom A) : ℂ) = ((SignType.sign (A : Matrix n n ℝ).det : ℝ) : ℂ) := by
  set U := Units.polarUnitary A
  have hUc : (U : Matrix n n ℝ).map (algebraMap ℝ ℂ) ∈ unitaryGroup n ℂ :=
    map_ofReal_mem_unitaryGroup U.property
  have hincl : Subgroup.inclusion inf_le_left (polarUnitary (leviHom A)) =
      ofUnitary ⟨_, hUc⟩ := by
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_inclusion, coe_polarUnitary_leviHom, coe_ofUnitary, realify_map_ofReal]
  rw [← maslovPhase_inclusion_polarUnitary, hincl, maslovPhase_ofUnitary, coe_detCircle]
  have hdet : (U : Matrix n n ℝ).det = SignType.sign (A : Matrix n n ℝ).det := by
    have h := det_polarUnitary A
    simp only [Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq] at h
    rw [h, div_eq_iff (abs_ne_zero.2 A.det_ne_zero), mul_comm, abs_mul_sign]
  rw [Subtype.coe_mk, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  simp

/-- On the Levi subgroup, `ρ` squares to `1`. -/
theorem maslovPhase_leviHom_sq (A : GL n ℝ) : maslovPhase (leviHom A) ^ 2 = 1 := by
  ext
  rw [Circle.coe_pow, maslovPhase_leviHom, Circle.coe_one]
  rcases A.det_ne_zero.lt_or_gt with h | h <;> simp [h]

/-! ### Loops preserving a coordinate Lagrangian -/

/-- **A loop preserving the vertical Lagrangian has Maslov index zero.** If every matrix of a loop
of symplectic matrices has vanishing upper right block, so that it maps the momentum directions
`0 ⊕ ℝⁿ` to themselves, the loop has Maslov index zero. -/
theorem maslovIndex_eq_zero_of_toBlocks₁₂_eq_zero {A : GLSymplectic n ℝ} (γ : Path A A)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₁₂ = 0) :
    maslovIndex γ = 0 := by
  let m : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ ((γ t : GL (n ⊕ n) ℝ) : Matrix _ _ ℝ)
  have hm : Continuous m := Units.continuous_val.comp (continuous_subtypeVal.comp γ.continuous)
  have hm₀ : m 1 = m 0 := by simp [m]
  -- Contract the lower left block: `F (s, t) = [[A_t, 0], [(1 - s) C_t, D_t]]`.
  let G : I × I → symplecticGroup n ℝ := fun p ↦
    ⟨fromBlocks (m p.2).toBlocks₁₁ 0 ((1 - (p.1 : ℝ)) • (m p.2).toBlocks₂₁) (m p.2).toBlocks₂₂,
      SymplecticGroup.fromBlocks_zero₁₂_smul_mem (by
        rw [← hγ p.2, fromBlocks_toBlocks]
        exact mem_iff_mem_symplecticGroup.1 (γ p.2).property) _⟩
  have hG : Continuous G := by
    have hm₂ : Continuous fun p : I × I ↦ m p.2 := hm.comp continuous_snd
    refine Continuous.subtype_mk (Continuous.matrix_fromBlocks
      (continuous_matrix fun i j ↦ hm₂.matrix_elem _ _) continuous_const
      (((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
        (continuous_matrix fun i j ↦ hm₂.matrix_elem _ _)))
      (continuous_matrix fun i j ↦ hm₂.matrix_elem _ _)) _
  let F : C(I × I, GLSymplectic n ℝ) :=
    ⟨fun p ↦ symplecticGroupContinuousMulEquiv n ℝ (G p),
      (symplecticGroupContinuousMulEquiv n ℝ).continuous.comp hG⟩
  have hF (p : I × I) : ((F p : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      fromBlocks (m p.2).toBlocks₁₁ 0 ((1 - (p.1 : ℝ)) • (m p.2).toBlocks₂₁)
        (m p.2).toBlocks₂₂ := by
    simp [F, G]
  have hFend (s : I) : F (s, 0) = F (s, 1) := by
    refine Subtype.ext (Units.ext ?_)
    rw [hF, hF, hm₀]
  -- At the end of the contraction the loop lies in the Levi subgroup.
  let δ : Path (F (1, 0)) (F (1, 0)) :=
    { toFun := fun t ↦ F (1, t)
      continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
      source' := rfl
      target' := (hFend 1).symm }
  have hγδ : maslovIndex γ = maslovIndex δ :=
    maslovIndex_eq_of_homotopy γ δ F
      (fun t ↦ Subtype.ext (Units.ext (by
        rw [hF, Set.Icc.coe_zero, sub_zero, one_smul, ← hγ t]
        exact fromBlocks_toBlocks _)))
      (fun t ↦ rfl) hFend
  rw [hγδ]
  refine maslovIndex_eq_zero_of_forall_maslovPhase_sq_eq_one δ fun t ↦ ?_
  obtain ⟨B, -, hB⟩ := exists_leviHom_eq_of_toBlocks₁₂_eq_zero_of_toBlocks₂₁_eq_zero (M := δ t)
    (by simp [δ, hF]) (by simp [δ, hF])
  rw [hB]
  exact maslovPhase_leviHom_sq B

/-- **A loop preserving the horizontal Lagrangian has Maslov index zero.** If every matrix of a
loop of symplectic matrices has vanishing lower left block, so that it maps the positions
`ℝⁿ ⊕ 0` to themselves, the loop has Maslov index zero. Conjugation by `J` exchanges the two
coordinate Lagrangians. -/
theorem maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero {A : GLSymplectic n ℝ} (γ : Path A A)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₁ = 0) :
    maslovIndex γ = 0 := by
  rw [← maslovIndex_map_conj (symJ n ℝ)]
  refine maslovIndex_eq_zero_of_toBlocks₁₂_eq_zero _ fun t ↦ ?_
  have h := hγ t
  simp only [Path.map_coe, Function.comp_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    coe_units_inv, coe_symJ, J_inv]
  rw [← fromBlocks_toBlocks ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ), h]
  simp [J, fromBlocks_multiply, fromBlocks_neg]

/-! ### The Conley–Zehnder index in vertical frames -/

/-- **Vertical frames give the same Conley–Zehnder index.** Changing the frame of a path of
symplectic matrices along a loop preserving the vertical Lagrangian, `t ↦ g(t)⁻¹ Ψ(t) g(0)`, keeps
its Conley–Zehnder index. -/
theorem conleyZehnderIndex_frameChange_of_toBlocks₁₂_eq_zero {A B C : GLSymplectic n ℝ}
    (g : Path A A)
    (hg : ∀ t, ((g t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₁₂ = 0)
    (Ψ : Path B C) :
    conleyZehnderIndex (frameChange g Ψ) = conleyZehnderIndex Ψ := by
  simp [conleyZehnderIndex_frameChange, maslovIndex_eq_zero_of_toBlocks₁₂_eq_zero g hg]

/-- **Horizontal frames give the same Conley–Zehnder index.** Changing the frame of a path of
symplectic matrices along a loop preserving the horizontal Lagrangian keeps its Conley–Zehnder
index. -/
theorem conleyZehnderIndex_frameChange_of_toBlocks₂₁_eq_zero {A B C : GLSymplectic n ℝ}
    (g : Path A A)
    (hg : ∀ t, ((g t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₁ = 0)
    (Ψ : Path B C) :
    conleyZehnderIndex (frameChange g Ψ) = conleyZehnderIndex Ψ := by
  simp [conleyZehnderIndex_frameChange, maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero g hg]

end TauCeti.GLSymplectic
