/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normal
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.LinearAlgebra.TotallyReal.Complex

/-!
# The eigenvalue `1` of the Souriau map and the zero axiom

For a unitary frame `U` of the Lagrangian `Λ = U ℝⁿ ⊆ ℂⁿ`, the Souriau map `W = U Uᵀ`
(`Matrix.UnitaryGroup.souriau`) fixes exactly the complex span of the real points `Λ ∩ ℝⁿ`
(`Matrix.UnitaryGroup.eigenspace_toEuclideanLin_souriau_one`). A real vector `x` lies in `Λ`
exactly when `W x = x`, and the fixed vectors of `W` are stable under conjugation because the
entrywise conjugate of `W` is its inverse. As `W` is unitary, hence normal, the multiplicity of `1`
as a root of its characteristic polynomial is the dimension of its fixed vectors, so it is the
dimension of `Λ ∩ ℝⁿ` (`Matrix.UnitaryGroup.rootMultiplicity_one_charpoly_souriau`).

This turns the zero axiom `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_rootMultiplicity_eq`, stated
through the Souriau maps, into the zero axiom of Robbin and Salamon: a path of Lagrangians whose
intersections with `ℝⁿ` keep the same dimension has Maslov index zero
(`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_finrank_eq`).

## Main results

* `Matrix.UnitaryGroup.eigenspace_toEuclideanLin_souriau_one`: the fixed vectors of the Souriau map
  of `U` are the complex span of `U ℝⁿ ∩ ℝⁿ`.
* `Matrix.UnitaryGroup.rootMultiplicity_one_charpoly_souriau`: the multiplicity of the eigenvalue
  `1` of the Souriau map is the dimension of `U ℝⁿ ∩ ℝⁿ`.
* `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_finrank_eq`: the zero axiom for paths of Lagrangian
  frames.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the zero axiom).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117--148 (the eigenvalues of
  `U Uᵀ` and the intersection with `ℝⁿ`).
-/

public section

open Module Module.End TauCeti

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real vector `x` is fixed by the Souriau map `U Uᵀ` exactly when it lies in `U ℝⁿ`. -/
private theorem souriau_mulVec_eq_self_iff (U : unitaryGroup n ℂ) {x : n → ℂ}
    (hx : star x = x) :
    (souriau U : Matrix n n ℂ) *ᵥ x = x ↔
      ∃ y : n → ℂ, star y = y ∧ (U : Matrix n n ℂ) *ᵥ y = x := by
  rw [coe_souriau, ← mulVec_mulVec]
  constructor
  · intro h
    refine ⟨_, ?_, h⟩
    calc star ((U : Matrix n n ℂ)ᵀ *ᵥ x) = (U : Matrix n n ℂ)ᴴ *ᵥ x := by
          rw [star_mulVec, hx, conjTranspose_transpose_eq_transpose_conjTranspose,
            vecMul_transpose]
      _ = (U : Matrix n n ℂ)ᵀ *ᵥ x := by
          conv_lhs => rw [← h]
          rw [mulVec_mulVec, ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem U.property,
            one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    congr 1
    calc (U : Matrix n n ℂ)ᵀ *ᵥ ((U : Matrix n n ℂ) *ᵥ y)
        = (U : Matrix n n ℂ)ᵀ *ᵥ star ((U : Matrix n n ℂ) *ᵥ y) := by rw [hx]
      _ = y := by
          rw [star_mulVec, ← mulVec_transpose, conjTranspose_transpose, hy, mulVec_mulVec,
            transpose_mul_map_star, one_mulVec]

/-- The entrywise conjugate of the Souriau map `U Uᵀ` is its inverse `conj(U) Uᴴ`. -/
private theorem mul_map_star_souriau (U : unitaryGroup n ℂ) :
    (souriau U : Matrix n n ℂ) * (souriau U : Matrix n n ℂ).map star = 1 := by
  have h : (souriau U : Matrix n n ℂ).map star =
      (U : Matrix n n ℂ).map star * (U : Matrix n n ℂ)ᴴ := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, coe_souriau, Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix n n ℂ)ᵀ,
    transpose_mul_map_star, Matrix.one_mul, ← star_eq_conjTranspose]
  exact Unitary.mul_star_self_of_mem U.property

/-- The eigenvectors of a Souriau map at `1` are stable under conjugation. -/
private theorem souriau_mulVec_star_eq_star (U : unitaryGroup n ℂ) {x : n → ℂ}
    (hx : (souriau U : Matrix n n ℂ) *ᵥ x = x) :
    (souriau U : Matrix n n ℂ) *ᵥ star x = star x := by
  conv_lhs => rw [← hx, star_mulVec, ← mulVec_transpose, conjTranspose_transpose, mulVec_mulVec,
    mul_map_star_souriau, one_mulVec]

/-- A vector of `ℂⁿ` lies in `U ℝⁿ ∩ ℝⁿ` exactly when it is real and fixed by the Souriau map. -/
private theorem mem_realImage_inf_realSubspace_iff (U : unitaryGroup n ℂ)
    (v : EuclideanSpace ℂ n) :
    v ∈ (U : Matrix n n ℂ).realImage ⊓ realSubspace n ↔
      star (WithLp.ofLp v) = WithLp.ofLp v ∧
        (souriau U : Matrix n n ℂ) *ᵥ WithLp.ofLp v = WithLp.ofLp v := by
  have hreal (w : EuclideanSpace ℂ n) :
      w ∈ realSubspace n ↔ star (WithLp.ofLp w) = WithLp.ofLp w := by
    simp [funext_iff, Complex.conj_eq_iff_im]
  rw [Submodule.mem_inf, hreal, and_comm, and_congr_right_iff]
  intro hv
  rw [souriau_mulVec_eq_self_iff U hv, mem_realImage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨WithLp.ofLp x, (hreal x).1 hx, by simp [toEuclideanCLM_apply]⟩
  · rintro ⟨y, hy, hyv⟩
    exact ⟨WithLp.toLp 2 y, (hreal _).2 hy, by simp [toEuclideanCLM_apply, hyv]⟩

/-- **The fixed vectors of the Souriau map.** The eigenspace at `1` of the Souriau map `U Uᵀ` is
the complex span of the real points `U ℝⁿ ∩ ℝⁿ` of the Lagrangian `U ℝⁿ`. -/
theorem eigenspace_toEuclideanLin_souriau_one (U : unitaryGroup n ℂ) :
    eigenspace (toEuclideanLin (souriau U : Matrix n n ℂ)) 1 =
      Submodule.span ℂ
        (((U : Matrix n n ℂ).realImage ⊓ realSubspace n : Submodule ℝ _) :
          Set (EuclideanSpace ℂ n)) := by
  refine le_antisymm (fun v hv ↦ ?_) (Submodule.span_le.2 fun v hv ↦ ?_)
  · set x := WithLp.ofLp v
    have hx : (souriau U : Matrix n n ℂ) *ᵥ x = x := by
      simpa [x] using congrArg WithLp.ofLp (mem_eigenspace_iff.1 hv)
    have hx' := souriau_mulVec_star_eq_star U hx
    -- The real and imaginary parts of `v` are real vectors fixed by the Souriau map.
    have hmem (c : ℂ) (hc : star c = c) (y : n → ℂ) (hy : star y = y)
        (hfix : (souriau U : Matrix n n ℂ) *ᵥ y = y) :
        WithLp.toLp 2 (c • y) ∈ (U : Matrix n n ℂ).realImage ⊓ realSubspace n :=
      (mem_realImage_inf_realSubspace_iff U _).2 ⟨by simp [star_smul, hc, hy],
        by rw [WithLp.ofLp_toLp, mulVec_smul, hfix]⟩
    have hre := hmem (2⁻¹) (by simp) (x + star x) (by simp [add_comm])
      (by rw [mulVec_add, hx, hx'])
    have him := hmem (2⁻¹) (by simp) (Complex.I • (star x - x))
      (by simp [star_sub, star_smul, smul_sub]; abel) (by rw [mulVec_smul, mulVec_sub, hx, hx'])
    have hv : v = WithLp.toLp 2 ((2⁻¹ : ℂ) • (x + star x)) +
        Complex.I • WithLp.toLp 2 ((2⁻¹ : ℂ) • Complex.I • (star x - x)) := by
      ext i
      simp only [x, PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        Pi.star_apply, smul_eq_mul]
      linear_combination (-(1 : ℂ) / 2 * (star (v.ofLp i) - v.ofLp i)) * Complex.I_sq
    rw [hv]
    exact Submodule.add_mem _ (Submodule.subset_span hre)
      (Submodule.smul_mem _ _ (Submodule.subset_span him))
  · obtain ⟨-, hfix⟩ := (mem_realImage_inf_realSubspace_iff U v).1 hv
    rw [SetLike.mem_coe, mem_eigenspace_iff, one_smul]
    exact (WithLp.ofLp_injective 2).eq_iff.1 (by simpa using hfix)

/-- **The multiplicity of `1` as an eigenvalue of the Souriau map** `U Uᵀ` is the dimension of the
intersection `U ℝⁿ ∩ ℝⁿ` of the Lagrangian `U ℝⁿ` with `ℝⁿ`. -/
theorem rootMultiplicity_one_charpoly_souriau (U : unitaryGroup n ℂ) :
    (souriau U : Matrix n n ℂ).charpoly.rootMultiplicity 1 =
      finrank ℝ ((U : Matrix n n ℂ).realImage ⊓ realSubspace n : Submodule ℝ _) := by
  rw [rootMultiplicity_charpoly_of_isStarNormal, eigenspace_toEuclideanLin_souriau_one,
    (isMaximalTotallyReal_realSubspace.isTotallyReal.mono inf_le_right).finrank_span_complex]

/-- **The zero axiom.** A path of unitary frames along which the intersections `γ t ℝⁿ ∩ ℝⁿ` of the
Lagrangians with `ℝⁿ` keep the same dimension has Maslov index zero. -/
theorem maslovIndex_eq_zero_of_finrank_eq {U V : unitaryGroup n ℂ} (γ : Path U V) {k : ℕ}
    (h : ∀ t, finrank ℝ ((γ t : Matrix n n ℂ).realImage ⊓ realSubspace n : Submodule ℝ _) = k) :
    maslovIndex γ = 0 :=
  maslovIndex_eq_zero_of_rootMultiplicity_eq γ fun t ↦
    (rootMultiplicity_one_charpoly_souriau (γ t)).trans (h t)

end Matrix.UnitaryGroup
