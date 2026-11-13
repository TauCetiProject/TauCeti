/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Unitary
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Lagrangian
public import TauCeti.Topology.Algebra.Star.Unitary

/-!
# The Robbin–Salamon index of a loop of Lagrangian subspaces

There are two Maslov indices of a loop of Lagrangian subspaces of `ℂⁿ`, defined differently.

* The **phase-degree index** `TauCeti.TotallyRealLoop.maslovIndex` of a loop of maximal totally
  real subspaces is the degree of its loop of Maslov phases `t ↦ det A / conj (det A)`, where `A`
  is a complex-linear automorphism carrying a fixed reference subspace to the subspace at time `t`.
* The **Robbin–Salamon index** `Matrix.UnitaryGroup.maslovIndex` of a path `γ` of unitary frames is
  Souriau's spectral formula for the index of the path of Lagrangians `γ t ℝⁿ` relative to `ℝⁿ`.
  It is defined for every path, with half-integer contributions from the endpoints.

This file shows that the two agree when the path of Lagrangians closes up
(`Matrix.UnitaryGroup.intCast_maslovIndex_lagrangianLoop`): the Robbin–Salamon index of a path of
unitary frames whose Lagrangians close up into a loop is the phase-degree index of that loop. This
is the comparison between the phase-degree normalization of the Maslov index of loops, the one
used for totally real boundary conditions, and the path index of Robbin and Salamon, through which
the Conley–Zehnder index of a symplectic path is defined by its graph. The pointwise input is that
the Maslov phase of `U ℝⁿ` relative to `ℝⁿ` is `det U ^ 2` for a unitary `U`
(`Matrix.UnitaryGroup.maslovPhase_eq_det_sq`), which is also the determinant of the Souriau map
`U Uᵀ`. Together with
`TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`, which deforms every loop of maximal
totally real subspaces of `ℂⁿ` to a loop of Lagrangian subspaces framed by unitary matrices, it
expresses the phase-degree index of every such loop as a Robbin–Salamon index.

The Lagrangians framed by two unitary matrices agree exactly when their Souriau maps `U Uᵀ` agree
(`Matrix.UnitaryGroup.souriau_eq_souriau_iff_realImage_eq`); a path of unitary frames whose
Lagrangians close up therefore defines a loop of maximal totally real subspaces
(`Matrix.UnitaryGroup.lagrangianLoop`).

Through the comparison, the Robbin–Salamon index of paths whose Lagrangians close up inherits the
invariance of the phase-degree index under free homotopies, along which the endpoints move
(`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_souriau_eq`). For a general path the
Robbin–Salamon index is only invariant under homotopies fixing the endpoints
(`Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic`).

## Main declarations

* `Matrix.UnitaryGroup.souriau_eq_souriau_iff_realImage_eq`: `U Uᵀ = V Vᵀ` exactly when
  `U ℝⁿ = V ℝⁿ`.
* `Matrix.UnitaryGroup.maslovPhase_eq_det_sq`: the Maslov phase of `U ℝⁿ` relative to `ℝⁿ`.
* `Matrix.UnitaryGroup.lagrangianLoop`: the loop `t ↦ γ t ℝⁿ` of a path of unitary frames whose
  Lagrangians close up.
* `Matrix.UnitaryGroup.intCast_maslovIndex_lagrangianLoop`: its phase-degree index is the
  Robbin–Salamon index of `γ`.
* `Matrix.UnitaryGroup.maslovIndex_eq_of_homotopy_of_souriau_eq`: free homotopy invariance of the
  Robbin–Salamon index of paths whose Lagrangians close up.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the loop axiom, comparing the index of a loop of Lagrangians with the degree of
  `det²`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (the Maslov index of loops of totally real
  subspaces through the phase `det / conj det`).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117--148 (the map `U ↦ U Uᵀ`).
-/

public section

open TauCeti
open scoped ComplexConjugate unitInterval

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Souriau map determines the Lagrangian.** Two unitary frames have the same Souriau map
`U Uᵀ = V Vᵀ` exactly when they frame the same Lagrangian subspace `U ℝⁿ = V ℝⁿ`. -/
theorem souriau_eq_souriau_iff_realImage_eq {U V : unitaryGroup n ℂ} :
    souriau U = souriau V ↔ (U : Matrix n n ℂ).realImage = (V : Matrix n n ℂ).realImage := by
  constructor
  · intro h
    -- The unitary matrix `W = Uᴴ V` satisfies `W Wᵀ = Uᴴ (U Uᵀ) conj U = 1`, so it is real.
    set W : Matrix n n ℂ := star (U : Matrix n n ℂ) * V with hWdef
    have hWu : W ∈ unitaryGroup n ℂ := mul_mem (Unitary.star_mem U.2) V.2
    have hWT : W * Wᵀ = 1 := by
      have hUV : (V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᵀ =
          (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᵀ := by
        rw [← coe_souriau, ← coe_souriau, h]
      calc W * Wᵀ = star (U : Matrix n n ℂ) * ((V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᵀ) *
            (star (U : Matrix n n ℂ))ᵀ := by
            rw [hWdef, transpose_mul]; simp only [mul_assoc]
        _ = (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
            (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ))ᵀ := by
            rw [hUV, transpose_mul]; simp only [mul_assoc]
        _ = 1 := by rw [star_mul_self U, transpose_one, one_mul]
    -- `O(n, ℂ) ∩ U(n) = O(n)`, so `W` is a real orthogonal matrix `O`.
    have hWO : Unitary.toUnits (⟨W, hWu⟩ : unitaryGroup n ℂ) ∈
        GLOrthogonal n ℂ ⊓ unitarySubgroup (GL n ℂ) :=
      ⟨GLOrthogonal.mem_iff'.2 hWT, mem_unitarySubgroup_GL_iff_mem_unitaryGroup.2 hWu⟩
    obtain ⟨O, -, hOW⟩ := (GLOrthogonal.inf_unitarySubgroup_eq_map_real n ℂ).le hWO
    have hV : (V : Matrix n n ℂ) = U * (O : Matrix n n ℝ).map ((↑) : ℝ → ℂ) := by
      have hOW' : (O : Matrix n n ℝ).map ((↑) : ℝ → ℂ) = W := by
        simpa [Matrix.GeneralLinearGroup.val_map_apply, Unitary.val_toUnits_apply] using
          congrArg Units.val hOW
      rw [hOW', hWdef, ← mul_assoc, mem_unitaryGroup_iff.1 U.2, one_mul]
    rw [hV, realImage_mul_map_ofReal _ O.isUnit]
  · intro h
    -- Frames of the same Lagrangian differ by a real orthogonal matrix, which drops out of `U Uᵀ`.
    have hre (W : unitaryGroup n ℂ) :
        ((((Unitary.toUnits W : GL n ℂ) : Matrix n n ℂ))ᴴ *
          ((Unitary.toUnits W : GL n ℂ) : Matrix n n ℂ)).map Complex.re = 1 := by
      simp [← star_eq_conjTranspose, star_mul_self W]
    obtain ⟨O, hO, hVO⟩ := exists_mem_orthogonalGroup_eq_mul_map_ofReal
      (M := Unitary.toUnits U) (M' := Unitary.toUnits V) h (hre U) (hre V)
    have hV : V = U * ⟨O.map ((↑) : ℝ → ℂ), map_ofReal_mem_unitaryGroup hO⟩ :=
      Subtype.ext (by simpa using hVO)
    rw [hV, souriau_mul_of_mul_transpose_eq_one _ _ (map_ofReal_mul_transpose_eq_one hO)]

/-- The **loop of Lagrangians** `t ↦ γ t ℝⁿ` of a path `γ` of unitary frames whose Souriau maps
agree at the endpoints, as a loop of maximal totally real subspaces of `ℂⁿ`. -/
noncomputable def lagrangianLoop {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : souriau U = souriau V) : TotallyRealLoop (EuclideanSpace ℂ n) :=
  TotallyRealLoop.ofRealImage (fun t ↦ Unitary.toUnits (γ t))
    (Unitary.continuous_toUnits.comp γ.continuous) <| by
      simpa using souriau_eq_souriau_iff_realImage_eq.1 h

/-- The loop of Lagrangians of `γ` at time `t` is `γ t ℝⁿ`. -/
@[simp]
theorem lagrangianLoop_apply {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : souriau U = souriau V) (t : I) :
    lagrangianLoop γ h t = (γ t : Matrix n n ℂ).realImage :=
  TotallyRealLoop.ofRealImage_apply _ _ _ t

/-- The Maslov phase of the Lagrangian `U ℝⁿ` relative to `ℝⁿ`, for a unitary matrix `U`, is
`det U / conj (det U) = det U ^ 2`. The subspace is given as any `L = U ℝⁿ`, so that the lemma
applies whatever proof of maximal total reality the phase carries. -/
theorem maslovPhase_eq_det_sq (U : unitaryGroup n ℂ) {L : Submodule ℝ (EuclideanSpace ℂ n)}
    (hL : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ) L)
    (hLU : L = (U : Matrix n n ℂ).realImage) :
    isMaximalTotallyReal_realSubspace.maslovPhase hL = (U : Matrix n n ℂ).det ^ 2 := by
  have hdet : (U : Matrix n n ℂ).det ≠ 0 := GeneralLinearGroup.det_ne_zero (Unitary.toUnits U)
  -- `det_toEuclideanCLE` is stated over a general `RCLike` field, so its instances on
  -- `EuclideanSpace ℂ n` agree with the ones in the phase only up to unfolding and `rw` cannot
  -- match it; restate it for the `toLinearEquiv` coercion produced by `maslovPhase_map`.
  have hdetU : LinearMap.det (((U : Matrix n n ℂ).toEuclideanCLE hdet).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = (U : Matrix n n ℂ).det :=
    det_toEuclideanCLE _ hdet
  rw [IsMaximalTotallyReal.maslovPhase_congr _ _
      (isMaximalTotallyReal_realSubspace.map_linearEquiv
        ((U : Matrix n n ℂ).toEuclideanCLE hdet).toLinearEquiv)
      (hLU.trans (realImage_eq_map_toEuclideanCLE hdet)),
    IsMaximalTotallyReal.maslovPhase_map, hdetU, div_eq_iff ((map_ne_zero _).2 hdet)]
  -- `conj (det U) * det U = 1` since `det U` is unitary.
  have hconj : conj (U : Matrix n n ℂ).det * (U : Matrix n n ℂ).det = 1 :=
    Unitary.star_mul_self_of_mem (det_of_mem_unitary U.2)
  linear_combination -(U : Matrix n n ℂ).det * hconj

/-- **Loop comparison.** Let `γ` be a path of unitary frames whose path of Lagrangians `t ↦ γ t ℝⁿ`
closes up. The phase-degree Maslov index (`TauCeti.TotallyRealLoop.maslovIndex`) of this loop of
Lagrangians is the Robbin–Salamon index of `γ`. -/
@[simp]
theorem intCast_maslovIndex_lagrangianLoop {U V : unitaryGroup n ℂ} (γ : Path U V)
    (h : souriau U = souriau V) :
    ((lagrangianLoop γ h).maslovIndex : ℝ) = maslovIndex γ := by
  rw [maslovIndex_eq_degree γ h,
    (lagrangianLoop γ h).maslovIndex_eq_degree isMaximalTotallyReal_realSubspace
      ((detSouriauPath γ).cast rfl (congrArg detCircle h)) fun t ↦ ?_]
  rw [maslovPhase_eq_det_sq (γ t) _ (lagrangianLoop_apply γ h t)]
  simp [detCircle_souriau, coe_detCircle]

/-- **Free homotopy invariance.** Let `F` be a continuous two-parameter family of unitary frames
such that for every `s` the path of Lagrangians `t ↦ F (s, t) ℝⁿ` closes up, that is, the endpoint
frames of `t ↦ F (s, t)` have the same Souriau map. Then the paths `t ↦ F (0, t)` and
`t ↦ F (1, t)` have the same Robbin–Salamon index, although the endpoints move along the
homotopy. -/
theorem maslovIndex_eq_of_homotopy_of_souriau_eq {U₀ V₀ U₁ V₁ : unitaryGroup n ℂ}
    (γ₀ : Path U₀ V₀) (γ₁ : Path U₁ V₁) (F : I × I → unitaryGroup n ℂ) (hF : Continuous F)
    (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t)
    (hF01 : ∀ s, souriau (F (s, 0)) = souriau (F (s, 1))) :
    maslovIndex γ₀ = maslovIndex γ₁ := by
  have hγ₀ : souriau U₀ = souriau V₀ := by simpa [h₀] using hF01 0
  have hγ₁ : souriau U₁ = souriau V₁ := by simpa [h₁] using hF01 1
  rw [← intCast_maslovIndex_lagrangianLoop γ₀ hγ₀,
    ← intCast_maslovIndex_lagrangianLoop γ₁ hγ₁]
  exact congrArg _ <| TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy _ _
    (fun p ↦ Unitary.toUnits (F p)) (Unitary.continuous_toUnits.comp hF)
    (fun t ↦ by simp [h₀]) (fun t ↦ by simp [h₁])
    fun s ↦ souriau_eq_souriau_iff_realImage_eq.1 (hF01 s)

end Matrix.UnitaryGroup
