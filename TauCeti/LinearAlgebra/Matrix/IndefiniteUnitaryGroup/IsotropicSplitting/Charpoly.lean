/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.InvariantSubmodule
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.IsotropicSplitting

/-!
# Characteristic polynomials on the stabiliser of an isotropic frame

Let `D` be an isotropic splitting of a hermitian Gram matrix `A` over a field `K` with involution,
with isotropic frame `k : Matrix n p K`, and let `g` be a matrix with `g k = k a`, so that `g`
keeps the isotropic subspace `W` spanned by the columns of `k`.

* If `p` is nonempty, `W` is a nonzero isotropic subspace, so the characteristic polynomial of `g`
  is not irreducible.
* If moreover `g` lies in the unitary group of `A`, then `g` also keeps the orthogonal `W^⊥` of
  `W`, the kernel of `kᴴ A`. For a unipotent element `u = n(c, b)`, `u - 1` maps every vector
  into `W^⊥` and maps `W^⊥` into `W`, and `u` fixes `W` pointwise, so `g n(c, b)` and `g` have
  the same characteristic polynomial.

## Main results

* `TauCeti.IsotropicSplitting.not_irreducible_charpoly`: a matrix with `g k = k a` and `p`
  nonempty has a characteristic polynomial that is not irreducible.
* `TauCeti.IsotropicSplitting.charpoly_mul_unipotent`: for `g` in the unitary group of `A` with
  `g k = k a`, the characteristic polynomial of `g n(c, b)` is that of `g`.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `Lib/Adelic/TraceFormula/IsotropicStabiliser.lean`
  (`New.IsIsotropicFrame.not_irreducible_charpoly`, `New.IsIsotropicFrame.charpoly_radical_mul`),
  for the statements.
-/

public section

open Matrix

namespace TauCeti.IsotropicSplitting

variable {K : Type*} [Field K] [StarRing K]
  {n n₀ p : Type*} [Fintype n] [Fintype n₀] [Fintype p] [DecidableEq n] [DecidableEq n₀]
  [DecidableEq p] {A : Matrix n n K} {A₀ : Matrix n₀ n₀ K} (D : IsotropicSplitting A A₀ p)

/-- **An element keeping an isotropic frame has a reducible characteristic polynomial.** If
`g k = k a` for the isotropic frame `k` of a splitting along a nonempty `p`, the characteristic
polynomial of `g` is not irreducible. -/
theorem not_irreducible_charpoly [Nonempty p] {g : Matrix n n K} {a : Matrix p p K}
    (hk : g * D.k = D.k * a) : ¬ Irreducible g.charpoly := by
  -- The columns of `k` are nonzero, since `kCoord k = 1`.
  have hW : LinearMap.range D.k.mulVecLin ≠ ⊥ := fun h ↦ by
    obtain ⟨i⟩ := ‹Nonempty p›
    have h0 := congrArg (D.kCoord *ᵥ ·)
      (LinearMap.congr_fun (LinearMap.range_eq_bot.mp h) (Pi.single i 1))
    simp only [mulVecLin_apply, LinearMap.zero_apply, mulVec_mulVec, kCoord_mul_k, one_mulVec,
      mulVec_zero] at h0
    simpa using congrFun h0 i
  -- So `K^n` is nonzero, and the invertible `A` is nonzero.
  obtain ⟨x, -, hx⟩ := (Submodule.ne_bot_iff _).mp hW
  obtain ⟨i, -⟩ := Function.ne_iff.mp hx
  have : Nonempty n := ⟨i⟩
  refine not_irreducible_charpoly_of_isotropic D.isUnit.ne_zero hW ?_ ?_
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc]
  · rintro _ ⟨x, rfl⟩
    exact ⟨a *ᵥ x, by simp [mulVec_mulVec, hk]⟩

/-- The unipotent element `n(c, b)` moves a vector `x` with `kᴴ A x = 0` by `k (cᴴ A₀ w)`, where
`w` is the core coordinate of `x`. -/
private theorem unipotent_mulVec_sub [Invertible (2 : K)] {j : Kˣ} (hj : star (j : K) = -j)
    (c : Matrix n₀ p K) (b : Matrix p p K) {x : n → K} (hx : D.lCoord *ᵥ x = 0) :
    ((D.unipotent hj c b : GL n K) : Matrix n n K) *ᵥ x - x =
      D.k *ᵥ ((cᴴ * A₀ * D.ιCoord) *ᵥ x) := by
  simp only [val_unipotent, sub_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec, hx,
    mulVec_zero, Matrix.mul_assoc]
  abel

/-- **A unipotent element does not change the characteristic polynomial on the stabiliser of an
isotropic frame.** For `g` in the unitary group of `A` with `g k = k a`, and a unipotent element
`n(c, b)` of the splitting, `g n(c, b)` and `g` have the same characteristic polynomial. -/
theorem charpoly_mul_unipotent [Invertible (2 : K)] {j : Kˣ} (hj : star (j : K) = -j)
    (g : unitaryGroupOf A) {a : Matrix p p K}
    (hk : ((g : GL n K) : Matrix n n K) * D.k = D.k * a) (c : Matrix n₀ p K) (b : Matrix p p K) :
    (((g : GL n K) : Matrix n n K) * ((D.unipotent hj c b : GL n K) : Matrix n n K)).charpoly =
      ((g : GL n K) : Matrix n n K).charpoly := by
  -- `a` is a unit `t`, and `kᴴ A` is moved by `g` to `(t⁻¹)ᴴ kᴴ A` and fixed by `n(c, b)`.
  obtain ⟨t, rfl⟩ := D.isUnit_of_mul_k hk
  have hlg := D.lCoord_mul_of_mul_k g t hk
  have hul := D.lCoord_mul_of_mul_k (D.unipotent hj c b) 1 (by simp)
  simp only [Units.val_one, inv_one, conjTranspose_one, Matrix.one_mul] at hul
  set G := ((g : GL n K) : Matrix n n K)
  set U := ((D.unipotent hj c b : GL n K) : Matrix n n K)
  rw [← charpoly_toLin', ← charpoly_toLin' G, toLin'_mul]
  refine LinearMap.charpoly_comp_eq_charpoly (W := LinearMap.range D.k.mulVecLin)
    (W' := LinearMap.ker D.lCoord.mulVecLin) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨(t : Matrix p p K) *ᵥ x, by simp [G, mulVec_mulVec, hk]⟩
  · intro x hx
    simp only [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_comap, toLin'_apply] at hx ⊢
    rw [mulVec_mulVec, hlg, ← mulVec_mulVec, hx, mulVec_zero]
  · intro x
    simp [mulVec_sub, mulVec_mulVec, hul]
  · intro x hx
    exact ⟨_, (D.unipotent_mulVec_sub hj c b hx).symm⟩
  · rintro _ ⟨x, rfl⟩
    simp [U, mulVec_mulVec]

end TauCeti.IsotropicSplitting
