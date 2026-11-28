/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.NumberTheory.Padics.Complex.FixedPoints

/-!
# Hodge–Tate jumps from period matrices and twisted dual pairings

Reads Hodge–Tate jumps from an invertible matrix whose rows transform by χ(j g) ^ (-k i) near
1, and uses matrix inversion to compute the Hodge–Tate jumps of a twisted dual representation.

## Main results

* PadicComplex.transpose_inv_mul_eq_of_mul_eq_diagonal: matrix inversion step for twisted duals.
* PadicComplex.hasHodgeTateJumps_of_matrix_rows: jumps from an invertible Hodge–Tate row matrix.
* PadicComplex.hasHodgeTateJumps_of_pairing: multiset of Hodge–Tate jumps of a twisted dual.
* PadicComplex.hodgeTateJump_eq_of_pairing: hodgeTateJump j σ γ u = hodgeTateJump j ρ γ (-u - c).

## Provenance

Adapted from New.Period.hasJumps_of_rows and New.Period.jump_eq_of_pairing in
src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean of grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Topology Filter Module Matrix

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {Γ R T T' ι : Type*} [Monoid Γ] [CommRing R] [AddCommGroup T]
  [AddCommGroup T'] [Module R T] [Module R T']

/-- Matrix inversion step for twisted duals: if Q * P = 1, P * Q = 1, Nᵀ * M = s • 1, and
Q * M = diagonal d * Q.map φ for a ring endomorphism φ and invertible diagonal entries d,
then (Pᵀ * N) i l = s * (d i)⁻¹ * φ (P l i). -/
theorem transpose_inv_mul_eq_of_mul_eq_diagonal {K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (φ : K →+* K) {Q P M N : Matrix ι ι K} {d : ι → K} {s : K}
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (hNM : Nᵀ * M = s • 1)
    (hQM : Q * M = Matrix.diagonal d * Q.map φ) (hd : ∀ i, d i ≠ 0) (i l : ι) :
    (Pᵀ * N) i l = s * (d i)⁻¹ * φ (P l i) := by
  have hQPφ : Q.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hMP : M * P.map φ = P * Matrix.diagonal d := by
    calc M * P.map φ = (P * Q) * (M * P.map φ) := by rw [hPQ, one_mul]
      _ = P * (Q * M * P.map φ) := by simp only [Matrix.mul_assoc]
      _ = P * Matrix.diagonal d := by rw [hQM, Matrix.mul_assoc, hQPφ, Matrix.mul_one]
  have hNP : Nᵀ * P * Matrix.diagonal d = s • P.map φ := by
    calc Nᵀ * P * Matrix.diagonal d = Nᵀ * (M * P.map φ) := by rw [Matrix.mul_assoc, hMP]
      _ = s • P.map φ := by rw [← Matrix.mul_assoc, hNM, smul_mul, one_mul]
  have hentry := congrFun (congrFun hNP l) i
  simp only [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hentry
  have htr : (Pᵀ * N) i l = (Nᵀ * P) l i := by
    rw [← Matrix.transpose_apply (Nᵀ * P), Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [htr, ← mul_left_inj' (hd i)]
  calc (Nᵀ * P) l i * d i = s * φ (P l i) := hentry
    _ = s * (d i)⁻¹ * φ (P l i) * d i := by
        rw [mul_right_comm, mul_assoc s, inv_mul_cancel₀ (hd i), mul_one]

/-- If P is an invertible matrix whose rows satisfy
(P * (toMatrix w w (σ g)).map γ) i l = χ(j g) ^ (-k i) · (j g)(P i l) near 1, and γ takes
algebraic values, then the multiset of Hodge–Tate jumps of σ at γ is the multiset of k. -/
theorem hasHodgeTateJumps_of_matrix_rows [Fintype ι] [DecidableEq ι]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {σ : Representation R Γ T} {γ : R →+* ℂ_[p]}
    (hγ : ∀ r : R, γ r ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    (w : Basis ι R T) {P : Matrix ι ι ℂ_[p]} (hP : IsUnit P.det) (k : ι → ℤ)
    (hrows : ∀ᶠ g in comap j (𝓝 1), ∀ i l,
      (P * (LinearMap.toMatrix w w (σ g)).map γ) i l =
        twist (-k i) (j g).toRingEquiv * j g • P i l) :
    HasHodgeTateJumps j σ γ (Finset.univ.val.map k) := by
  let : Algebra R ℂ_[p] := γ.toAlgebra
  let evalW : (T →ₛₗ[γ] ℂ_[p]) ≃ₗ[ℂ_[p]] (ι → ℂ_[p]) := LinearEquiv.ofBijective
    (LinearMap.pi fun l ↦ LinearMap.id.flip (w l)) ⟨fun _ _ h ↦ w.ext (congrFun h),
      fun u ↦ ⟨⟨(w.constr ℕ u).toAddHom, (w.constr ℕ u).map_smul'⟩, funext (w.constr_basis ℕ u)⟩⟩
  have hPT : IsUnit Pᵀ.det := by simpa [Matrix.det_transpose] using hP
  let eP : (ι → ℂ_[p]) ≃ₗ[ℂ_[p]] (ι → ℂ_[p]) := LinearEquiv.ofLinearMap (Matrix.mulVecLin Pᵀ)
    (Matrix.mulVecLin Pᵀ⁻¹) (by rw [← Matrix.mulVecLin_mul, Matrix.mul_nonsing_inv _ hPT,
      Matrix.mulVecLin_one]) (by rw [← Matrix.mulVecLin_mul, Matrix.nonsing_inv_mul _ hPT,
      Matrix.mulVecLin_one])
  let b' := (Pi.basisFun ℂ_[p] ι).map (eP ≪≫ₗ evalW.symm)
  have hb'_w (i l : ι) : b' i (w l) = P i l := by change evalW (b' i) l = P i l; simp [b', eP]
  refine hasHodgeTateJumps_of_basis hj b' fun i ↦ mem_hodgeTateMaps.mpr fun x ↦ ?_
  filter_upwards [hrows, eventually_all.mpr fun l ↦
    (mem_range_coe_iff_eventually_smul_eq.mp (hγ (w.repr x l))).comap j] with g hgr hgf
  have hstep (l : ι) : b' i (σ g (w l)) = twist (-k i) (j g).toRingEquiv * j g • P i l := by
    rw [← hgr i l, Matrix.mul_apply]
    calc b' i (σ g (w l)) = b' i (∑ t, (LinearMap.toMatrix w w (σ g)) t l • w t) := by
          congr 1; simp only [LinearMap.toMatrix_apply]; exact (w.sum_repr _).symm
      _ = ∑ t, P i t * ((LinearMap.toMatrix w w (σ g)).map γ) t l := by
          simp [map_sum, map_smulₛₗ, hb'_w, mul_comm]
  calc b' i (σ g x) = b' i (σ g (∑ l, w.repr x l • w l)) := by rw [w.sum_repr]
    _ = ∑ l, γ (w.repr x l) * (twist (-k i) (j g).toRingEquiv * j g • P i l) := by
        simp only [map_sum, map_smul, map_smulₛₗ, smul_eq_mul, hstep]
    _ = twist (-k i) (j g).toRingEquiv * j g • b' i (∑ l, w.repr x l • w l) := by
        simp only [map_sum, map_smulₛₗ, smul_eq_mul, hb'_w, Finset.smul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ ↦ by rw [smul_mul', hgf l]; ring
    _ = twist (-k i) (j g).toRingEquiv * j g • b' i x := by rw [w.sum_repr]

/-- Let T have a finite R-basis  and a ℂ_p-basis  of Hodge–Tate maps of weights k.
If e : T' ≃ₗ[R] (T →ₗ[R] R) satisfies e (σ g x) (ρ g y) = a g • e x y with
γ (a g) = χ(j g) ^ c near 1, and γ takes algebraic values, then σ has Hodge–Tate jumps
-c - k i. -/
theorem hasHodgeTateJumps_of_pairing [Fintype ι]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {ρ : Representation R Γ T} {σ : Representation R Γ T'} {γ : R →+* ℂ_[p]}
    (hγ : ∀ r : R, γ r ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    (v : Basis ι R T) {k : ι → ℤ} (b : Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p]))
    (hb : ∀ i, b i ∈ hodgeTateMaps j ρ γ (k i)) (e : T' ≃ₗ[R] (T →ₗ[R] R))
    (a : Γ → R) (c : ℤ) (ha : ∀ᶠ g in comap j (𝓝 1), γ (a g) = twist c (j g).toRingEquiv)
    (h_equiv : ∀ g x y, e (σ g x) (ρ g y) = a g • e x y) :
    HasHodgeTateJumps j σ γ (Finset.univ.val.map fun i ↦ -c - k i) := by
  classical
  let : Algebra R ℂ_[p] := γ.toAlgebra; let w : Basis ι R T' := v.dualBasis.map e.symm
  let evalV : (T →ₛₗ[γ] ℂ_[p]) ≃ₗ[ℂ_[p]] (ι → ℂ_[p]) := LinearEquiv.ofBijective
    (LinearMap.pi fun l ↦ LinearMap.id.flip (v l)) ⟨fun _ _ h ↦ v.ext (congrFun h),
      fun u ↦ ⟨⟨(v.constr ℕ u).toAddHom, (v.constr ℕ u).map_smul'⟩, funext (v.constr_basis ℕ u)⟩⟩
  let Q : Matrix ι ι ℂ_[p] := Matrix.of fun i l ↦ b i (v l)
  let φ := b.equivFun.symm ≪≫ₗ evalV
  have hQ_det : IsUnit Q.det := by
    have hQT : Qᵀ = LinearMap.toMatrix (Pi.basisFun ℂ_[p] ι) (Pi.basisFun ℂ_[p] ι)
        φ.toLinearMap := by ext l i; simp [Q, φ, evalV]; rfl
    rw [← Matrix.det_transpose]; refine isUnit_det_of_right_inverse (B := LinearMap.toMatrix
      (Pi.basisFun ℂ_[p] ι) (Pi.basisFun ℂ_[p] ι) φ.symm.toLinearMap) ?_
    rw [hQT, ← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]
  have hQP := Matrix.mul_nonsing_inv Q hQ_det; have hPQ := Matrix.nonsing_inv_mul Q hQ_det
  refine hasHodgeTateJumps_of_matrix_rows hj hγ w
    (by rw [Matrix.det_transpose]; exact isUnit_det_of_right_inverse hPQ) (fun i ↦ -c - k i) ?_
  filter_upwards [ha, eventually_all.mpr fun r ↦ eventually_all.mpr fun l ↦
    (mem_hodgeTateMaps.mp (hb r)) (v l)] with g hga hQg i l
  let M := LinearMap.toMatrix v v (ρ g); let N := LinearMap.toMatrix w w (σ g)
  have hNM : (N.map γ)ᵀ * M.map γ = γ (a g) • 1 := by
    ext r m
    have hpair : ∑ t, N t r * M t m = if r = m then a g else 0 := by
      have h1 : e (σ g (w r)) (ρ g (v m)) = ∑ t, N t r * M t m := by
        rw [← v.sum_repr (ρ g (v m)), map_sum]
        simp [M, N, w, LinearMap.toMatrix_apply, Basis.dualBasis_repr, mul_comm]
      rw [← h1, h_equiv]; simp [w, Finsupp.single_apply, eq_comm]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, ← map_mul, ← map_sum,
      hpair, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp
  have hQM : Q * M.map γ = Matrix.diagonal (fun r ↦ twist (-k r) (j g).toRingEquiv) *
      Q.map (MulSemiringAction.toRingHom _ ℂ_[p] (j g)) := by
    ext r m; rw [Matrix.mul_apply, Matrix.diagonal_mul]; simp only [Matrix.map_apply]
    have hsum : b r (ρ g (v m)) = ∑ t, Q r t * γ (M t m) := by
      rw [← v.sum_repr (ρ g (v m)), map_sum]; simp [Q, M, LinearMap.toMatrix_apply, mul_comm]
    rw [← hsum, hQg r m]; rfl
  have hinv : (twist (-k i) (j g).toRingEquiv)⁻¹ = twist (k i) (j g).toRingEquiv :=
    inv_eq_of_mul_eq_one_right (by rw [← twist_add, neg_add_cancel, twist_zero])
  rw [transpose_inv_mul_eq_of_mul_eq_diagonal (MulSemiringAction.toRingHom _ ℂ_[p] (j g))
    hQP hPQ hNM hQM (fun r ↦ twist_ne_zero _ _) i l, hga, hinv, ← twist_add,
    show c + k i = -(-c - k i) by omega]; rfl

/-- Under the hypotheses of hasHodgeTateJumps_of_pairing, the multiplicity of the jump u of σ
equals the multiplicity of the jump -u - c of ρ. -/
theorem hodgeTateJump_eq_of_pairing [Finite ι]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {ρ : Representation R Γ T} {σ : Representation R Γ T'} {γ : R →+* ℂ_[p]}
    (hγ : ∀ r : R, γ r ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    (v : Basis ι R T) {k : ι → ℤ} (b : Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p]))
    (hb : ∀ i, b i ∈ hodgeTateMaps j ρ γ (k i)) (e : T' ≃ₗ[R] (T →ₗ[R] R))
    (a : Γ → R) (c : ℤ) (ha : ∀ᶠ g in comap j (𝓝 1), γ (a g) = twist c (j g).toRingEquiv)
    (h_equiv : ∀ g x y, e (σ g x) (ρ g y) = a g • e x y) (u : ℤ) :
    hodgeTateJump j σ γ u = hodgeTateJump j ρ γ (-u - c) := by
  let := Fintype.ofFinite ι
  have hσ := (hasHodgeTateJumps_iff j σ γ _).mp
    (hasHodgeTateJumps_of_pairing hj hγ v b hb e a c ha h_equiv) u
  have hρ := (hasHodgeTateJumps_iff j ρ γ _).mp (hasHodgeTateJumps_of_basis hj b hb) (-u - c)
  rw [hσ, hρ, Multiset.count_map, Multiset.count_map]
  exact congrArg Multiset.card (Multiset.filter_congr fun i _ ↦ by omega)

end PadicComplex
