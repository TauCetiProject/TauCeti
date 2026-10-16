/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.PointModTorsion.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The regulator along an isogeny

Let `f : W₁ → W₂` be a nonzero morphism of elliptic curves over a field with a theory of heights,
and write `E₁ = W₁.Point ⧸ torsion` and `E₂ = W₂.Point ⧸ torsion` for the points modulo torsion,
assumed finitely generated. The map `E₁ → E₂` induced by `f`, again written `f`, is injective,
its image has finite index, and `E₁`, `E₂` have the same rank `r`; these facts are proved in
`TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.PointModTorsion.Isogeny`. This file proves
how the regulator changes along `f`:

  `Reg(W₁) · (deg f) ^ r = [E₂ : f E₁] ^ 2 · Reg(W₂)`.

Indeed, by `TauCeti.Isogeny.Hom.neronTatePairing_pointMap` the Néron–Tate pairing satisfies
`⟨f P, f Q⟩ = deg f · ⟨P, Q⟩`. So on a basis `(Pᵢ)` of `E₁` the Gram matrix of `(f Pᵢ)` is
`deg f` times the Gram matrix of `(Pᵢ)`. Expanding `(f Pᵢ)` in a basis of `E₂` instead writes it as
`Mᵀ G M` for the matrix `M` of `f`, whose determinant is `± [E₂ : f E₁]`. Since
`[E₂ : f E₁] · [E₁ : f̂ E₂] = (deg f) ^ r`, this is equivalent to the symmetric form

  `Reg(W₁) · [E₁ : f̂ E₂] = [E₂ : f E₁] · Reg(W₂)`,

the regulator part of Cassels' theorem that the Birch and Swinnerton-Dyer quotient is invariant
under isogeny. The indices here are those of the free quotients. Neither statement needs the
Néron–Tate pairing to be positive definite.

## Main results

* `TauCeti.Isogeny.Hom.regulator_mul_degree_pow_eq_index_sq_mul_regulator`:
  `Reg(W₁) · (deg f) ^ r = [E₂ : f E₁] ^ 2 · Reg(W₂)`.
* `TauCeti.Isogeny.Hom.regulator_mul_index_dual_eq_index_mul_regulator`:
  `Reg(W₁) · [E₁ : f̂ E₂] = [E₂ : f E₁] · Reg(W₂)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9 and III.6.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open Height Matrix Module WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] [DecidableEq F] [AdmissibleAbsValues F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  [Module.Finite ℤ (PointModTorsion W₁)] [Module.Finite ℤ (PointModTorsion W₂)]

/-- **The regulator along an isogeny**: for a nonzero morphism `f : W₁ → W₂` and `r` the rank,
`Reg(W₁) · (deg f) ^ r = [E₂ : f E₁] ^ 2 · Reg(W₂)`, where `[E₂ : f E₁]` is the index of the
image of the points of `W₁` modulo torsion in the points of `W₂` modulo torsion. -/
theorem regulator_mul_degree_pow_eq_index_sq_mul_regulator {f : Hom W₁ W₂} (hf : f ≠ 0) :
    regulator W₁ * (f.degree : ℝ) ^ finrank ℤ (PointModTorsion W₁) =
      ((LinearMap.range f.pointModTorsionMap).toAddSubgroup.index : ℝ) ^ 2 * regulator W₂ := by
  let b₁ := finBasisOfFinrankEq ℤ (PointModTorsion W₁) rfl
  let b₂ := finBasisOfFinrankEq ℤ (PointModTorsion W₂) (finrank_pointModTorsion_eq hf).symm
  -- the Gram matrix of `(f Pᵢ)`, computed once through `⟨f x, f y⟩ = deg f · ⟨x, y⟩` and once by
  -- expanding `f Pᵢ` in the basis `b₂`
  have hgram : (f.degree : ℝ) • neronTateGramMatrix W₁ b₁ =
      ((LinearMap.toMatrix b₁ b₂ f.pointModTorsionMap).map (algebraMap ℤ ℝ))ᵀ *
        neronTateGramMatrix W₂ b₂ * (LinearMap.toMatrix b₁ b₂ f.pointModTorsionMap).map
          (algebraMap ℤ ℝ) := by
    rw [neronTateGramMatrix_eq_toMatrix₂Aux, neronTateGramMatrix_eq_toMatrix₂Aux,
      ← LinearMap.toMatrix₂Aux_compl₁₂]
    ext i j
    simp
  have hdet := congrArg Matrix.det hgram
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin,
    algebraMap_int_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast] at hdet
  rw [regulator_eq_abs_det_neronTateGramMatrix W₁ b₁,
    regulator_eq_abs_det_neronTateGramMatrix W₂ b₂,
    LinearMap.index_range_eq_natAbs_det_toMatrix b₁ b₂ (pointModTorsionMap_injective hf),
    Nat.cast_natAbs, Int.cast_abs]
  have hd : (0 : ℝ) ≤ (f.degree : ℝ) ^ finrank ℤ (PointModTorsion W₁) := by positivity
  calc _ = |(f.degree : ℝ) ^ finrank ℤ (PointModTorsion W₁) * (neronTateGramMatrix W₁ b₁).det| := by
        rw [abs_mul, abs_of_nonneg hd, mul_comm]
    _ = _ := by
        rw [hdet, abs_mul, abs_mul, sq]
        ring

/-- **The regulator along an isogeny, in Cassels' form**: for a nonzero morphism `f : W₁ → W₂`,
`Reg(W₁) · [E₁ : f̂ E₂] = [E₂ : f E₁] · Reg(W₂)`, where the indices are those of the images of the
points modulo torsion under `f` and its dual. -/
theorem regulator_mul_index_dual_eq_index_mul_regulator {f : Hom W₁ W₂} (hf : f ≠ 0) :
    regulator W₁ * (LinearMap.range f.dual.pointModTorsionMap).toAddSubgroup.index =
      (LinearMap.range f.pointModTorsionMap).toAddSubgroup.index * regulator W₂ := by
  have h := regulator_mul_degree_pow_eq_index_sq_mul_regulator hf
  have hidx := index_mul_index_dual_eq_degree_pow hf
  -- the index of `f` is nonzero, its product with the index of the dual being `(deg f) ^ r ≠ 0`
  have hne : ((LinearMap.range f.pointModTorsionMap).toAddSubgroup.index : ℝ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 fun h0 ↦ ?_
    rw [h0, zero_mul, eq_comm] at hidx
    exact pow_ne_zero _ ((degree_eq_zero_iff f).not.2 hf) hidx
  rw [← Nat.cast_inj (R := ℝ), Nat.cast_mul, Nat.cast_pow] at hidx
  rw [← hidx] at h
  refine mul_left_cancel₀ hne ?_
  linear_combination h

end TauCeti.Isogeny.Hom
