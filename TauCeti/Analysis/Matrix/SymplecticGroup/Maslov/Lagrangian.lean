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
* **Contracting the off-diagonal block.** If `B = 0`, the symplectic condition reads `A Dᵀ = 1` and
  `C Dᵀ = D Cᵀ`, which persist when `C` is replaced by `s C`. So `s ↦ [[A, 0], [s C, D]]`,
  `s ∈ [0, 1]`, deforms a loop preserving the vertical Lagrangian through such loops into a loop in
  the Levi subgroup, without changing its Maslov index. The horizontal case is the vertical one
  conjugated by `J`, which exchanges the two Lagrangians, and the Maslov index is invariant under
  conjugation (`TauCeti.GLSymplectic.maslovIndex_map_conj`).

The first step does not extend to the whole stabilizer: on the shear `[[1, 0], [c, 1]]` of
`Sp(2, ℝ)`, `c ≠ 0`, the orthogonal polar factor is a rotation by a nonzero angle, so `ρ` is not
`±1`. Only the loops, not the individual matrices, see a trivial Maslov phase. Nor does the
vanishing hold without the Lagrangian condition: the loop `t ↦ e^{2π i t}` of `U(1) ⊆ Sp(2, ℝ)`,
whose rotations by angles other than `0` and `π` preserve no line, has Maslov index `1`
(`TauCeti.GLSymplectic.maslovIndex_scalarRotationLoop`).

## Main results

* `TauCeti.GLSymplectic.coe_polarUnitary_leviHom`: the orthogonal polar factor of
  `diag(A, A⁻ᵀ)` is `diag(U, U)`, for the orthogonal polar factor `U` of `A`.
* `TauCeti.GLSymplectic.maslovPhase_leviHom`: `ρ(diag(A, A⁻ᵀ)) = sign (det A)`.
* `TauCeti.GLSymplectic.maslovIndex_eq_zero_of_forall_maslovPhase_sq_eq_one`: a loop along which
  `ρ = ±1` has Maslov index zero.
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

/-- **The polar decomposition on the Levi subgroup.** If `A = P U` is the polar decomposition of
`A`, then `diag(A, A⁻ᵀ) = diag(P, P⁻¹) diag(U, U)` is that of `diag(A, A⁻ᵀ)`: its orthogonal polar
factor is `diag(U, U)`. -/
theorem coe_polarUnitary_leviHom (A : GL n ℝ) :
    ((polarUnitary (leviHom A) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      fromBlocks (Units.polarUnitary A : Matrix n n ℝ) 0 0 (Units.polarUnitary A) := by
  set P := CFC.sqrt ((A : Matrix n n ℝ) * star (A : Matrix n n ℝ))
  set U := Units.polarUnitary A
  have hP : P.PosDef := posDef_sqrt_mul_star A
  have hPU : P * (U : Matrix n n ℝ) = A := Units.sqrt_mul_star_mul_polarUnitary A
  have hU : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  have hPinv : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP.isUnit)
  have hPsymm : (P⁻¹)ᵀ = P⁻¹ := by
    rw [transpose_nonsing_inv, ← conjTranspose_eq_transpose_of_trivial, hP.isHermitian.eq]
  -- The inverse transpose of `A = P U` is `P⁻¹ U`.
  have hAinv : (((A⁻¹ : GL n ℝ) : Matrix n n ℝ))ᵀ = P⁻¹ * (U : Matrix n n ℝ) := by
    have h : (A : Matrix n n ℝ) * (P⁻¹ * (U : Matrix n n ℝ))ᵀ = 1 := by
      rw [transpose_mul, hPsymm, ← hPU, ← conjTranspose_eq_transpose_of_trivial,
        ← star_eq_conjTranspose, mul_assoc, ← mul_assoc (U : Matrix n n ℝ), hU, one_mul,
        hPinv]
    rw [coe_units_inv, inv_eq_right_inv h, transpose_transpose]
  have hW : fromBlocks (U : Matrix n n ℝ) 0 0 (U : Matrix n n ℝ) ∈
      unitaryGroup (n ⊕ n) ℝ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
      ← star_eq_conjTranspose, hU]
    simp
  have hQ : 0 ≤ fromBlocks P 0 0 P⁻¹ := by
    rw [nonneg_iff_posSemidef]
    let _ : Invertible P := hP.isUnit.invertible
    simpa using (PosDef.fromBlocks₁₁ (0 : Matrix n n ℝ) P⁻¹ hP).2 (by simpa using hP.inv.posSemidef)
  rw [coe_polarUnitary, Units.polarUnitary_eq_of_mul_eq _ hQ (v := ⟨_, hW⟩) (by
    rw [coe_leviHom, fromBlocks_multiply, hPU, hAinv]
    simp)]

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
    have habs : |(A : Matrix n n ℝ).det| ≠ 0 :=
      abs_ne_zero.2 (A.isUnit.map (detMonoidHom (n := n) (R := ℝ))).ne_zero
    have h := det_polarUnitary A
    rw [Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id] at h
    rw [show (U : Matrix n n ℝ).det = _ from h, div_eq_iff habs, mul_comm, abs_mul_sign]
  change ((U : Matrix n n ℝ).map (algebraMap ℝ ℂ)).det = _
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  rfl

/-- On the Levi subgroup, `ρ` squares to `1`. -/
theorem maslovPhase_leviHom_sq (A : GL n ℝ) : maslovPhase (leviHom A) ^ 2 = 1 := by
  ext
  rw [Circle.coe_pow, maslovPhase_leviHom, Circle.coe_one]
  have h0 : (A : Matrix n n ℝ).det ≠ 0 := (A.isUnit.map (detMonoidHom (n := n) (R := ℝ))).ne_zero
  rcases h0.lt_or_gt with h | h <;> simp [h]

/-! ### Loops preserving a coordinate Lagrangian -/

/-- A symplectic matrix `[[A, 0], [C, D]]` preserving the vertical Lagrangian stays symplectic
when its lower left block `C` is scaled: the symplectic condition reads `A Dᵀ = 1` and
`C Dᵀ = D Cᵀ`. -/
private theorem fromBlocks_smul_mem_symplecticGroup {M : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hM : M ∈ symplecticGroup n ℝ) (h : M.toBlocks₁₂ = 0) (c : ℝ) :
    fromBlocks M.toBlocks₁₁ 0 (c • M.toBlocks₂₁) M.toBlocks₂₂ ∈ symplecticGroup n ℝ := by
  rw [SymplecticGroup.mem_iff] at hM ⊢
  rw [← fromBlocks_toBlocks M, h] at hM
  simp only [J, fromBlocks_transpose, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, transpose_zero,
    Matrix.smul_mul, Matrix.mul_smul, transpose_smul, fromBlocks_inj] at hM ⊢
  obtain ⟨-, h₁₂, h₂₁, h₂₂⟩ := hM
  refine ⟨trivial, ?_, h₂₁, ?_⟩
  · simpa using h₁₂
  · rw [← smul_neg, ← smul_add, h₂₂, smul_zero]

/-- On a symplectic matrix preserving both coordinate Lagrangians, `ρ` squares to `1`: such a
matrix is `diag(A, A⁻ᵀ)` for an invertible `A`. -/
private theorem maslovPhase_sq_of_toBlocks_eq_zero {M : GLSymplectic n ℝ}
    (h₁₂ : ((M : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₁₂ = 0)
    (h₂₁ : ((M : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₁ = 0) :
    maslovPhase M ^ 2 = 1 := by
  set m := ((M : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) with hm
  have hmem : m ∈ symplecticGroup n ℝ := mem_iff_mem_symplecticGroup.1 M.property
  rw [SymplecticGroup.mem_iff, ← fromBlocks_toBlocks m, h₁₂, h₂₁] at hmem
  simp only [J, fromBlocks_transpose, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, transpose_zero] at hmem
  have hAD : m.toBlocks₁₁ * m.toBlocks₂₂ᵀ = 1 := neg_injective (fromBlocks_inj.1 hmem).2.1
  let A : GL n ℝ := ⟨m.toBlocks₁₁, m.toBlocks₂₂ᵀ, hAD, mul_eq_one_comm.1 hAD⟩
  have hMA : M = leviHom A := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_leviHom, ← hm]
    conv_lhs => rw [← fromBlocks_toBlocks m, h₁₂, h₂₁]
    simp [A]
  rw [hMA]
  exact maslovPhase_leviHom_sq A

/-- **A loop with `ρ = ±1` has Maslov index zero.** If `ρ` takes only the values `1` and `-1`
along a loop of symplectic matrices, it is constant along the loop, which therefore has Maslov
index zero. -/
theorem maslovIndex_eq_zero_of_forall_maslovPhase_sq_eq_one {A : GLSymplectic n ℝ}
    (γ : Path A A) (h : ∀ t, maslovPhase (γ t) ^ 2 = 1) : maslovIndex γ = 0 := by
  have hcont : Continuous fun t ↦ ((maslovPhase (γ t) : Circle) : ℂ) :=
    continuous_subtypeVal.comp (continuous_maslovPhase.comp γ.continuous)
  have hconst : ∀ t, ((maslovPhase (γ t) : Circle) : ℂ) = maslovPhase (γ 0) := by
    have h' := isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hcont.continuousOn
      (fun t _ ↦ by simpa using congrArg ((↑) : Circle → ℂ) (h t))
    intro t
    rcases h' with h' | h' <;> exact (h' (Set.mem_univ t)).trans (h' (Set.mem_univ 0)).symm
  rw [maslovIndex_def, Circle.degree_congr _ (Path.refl (maslovPhase (γ 0)))
    fun t ↦ Subtype.ext (hconst t), Circle.degree_refl]

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
      fromBlocks_smul_mem_symplecticGroup (mem_iff_mem_symplecticGroup.1 (γ p.2).property)
        (hγ p.2) _⟩
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
        rw [hF]
        simp only [Set.Icc.coe_zero, sub_zero, one_smul]
        conv_rhs => rw [← fromBlocks_toBlocks ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ),
          hγ t])))
      (fun t ↦ rfl) hFend
  rw [hγδ]
  exact maslovIndex_eq_zero_of_forall_maslovPhase_sq_eq_one δ fun t ↦
    maslovPhase_sq_of_toBlocks_eq_zero (by simp [δ, hF]) (by simp [δ, hF])

/-- **A loop preserving the horizontal Lagrangian has Maslov index zero.** If every matrix of a
loop of symplectic matrices has vanishing lower left block, so that it maps the positions
`ℝⁿ ⊕ 0` to themselves, the loop has Maslov index zero. Conjugation by `J` exchanges the two
coordinate Lagrangians. -/
theorem maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero {A : GLSymplectic n ℝ} (γ : Path A A)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₂₁ = 0) :
    maslovIndex γ = 0 := by
  rw [← maslovIndex_map_conj (symJ n ℝ)]
  refine maslovIndex_eq_zero_of_toBlocks₁₂_eq_zero _ fun t ↦ ?_
  change (((symJ n ℝ * γ t * (symJ n ℝ)⁻¹ : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ).toBlocks₁₂ = 0
  have h := hγ t
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_units_inv, coe_symJ, J_inv]
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
