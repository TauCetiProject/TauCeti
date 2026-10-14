/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The regulator along an isogeny

Let `f : W₁ → W₂` be a nonzero morphism of elliptic curves over a field with a theory of heights,
and write `E₁ = W₁.Point ⧸ torsion` and `E₂ = W₂.Point ⧸ torsion` for the points modulo torsion,
assumed finitely generated. The map `E₁ → E₂` induced by `f`, again written `f`, is injective, its
image has finite index, and `E₁`, `E₂` have the same rank `r`, since `f̂ ∘ f` and `f ∘ f̂` are
multiplication by `deg f`. This file proves how the regulator changes along `f`:

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

## Main definitions

* `TauCeti.Isogeny.Hom.pointModTorsionMap`: the map induced by a morphism on the points modulo
  torsion.

## Main results

* `TauCeti.Isogeny.Hom.neronTatePairingModTorsion_pointModTorsionMap`: the descended Néron–Tate
  pairing scales by the degree.
* `TauCeti.Isogeny.Hom.pointModTorsionMap_injective`: a nonzero morphism is injective on the points
  modulo torsion.
* `TauCeti.Isogeny.Hom.finrank_pointModTorsion_eq`: the two curves have the same rank.
* `TauCeti.Isogeny.Hom.index_mul_index_dual_eq_degree_pow`: `[E₂ : f E₁] · [E₁ : f̂ E₂]` is
  `(deg f) ^ r`.
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

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-! ### The map on the points modulo torsion -/

/-- **The map induced by a morphism on the points modulo torsion.** A morphism acts additively on
points, so it carries torsion points to torsion points. -/
noncomputable def pointModTorsionMap (f : Hom W₁ W₂) :
    PointModTorsion W₁ →ₗ[ℤ] PointModTorsion W₂ :=
  (Submodule.torsion ℤ W₁.Point).mapQ (Submodule.torsion ℤ W₂.Point)
    f.pointMapHom.toIntLinearMap fun P ⟨a, ha⟩ ↦
      ⟨a, by simpa [Submonoid.smul_def] using congrArg f.pointMap ha⟩

/-- The induced map sends the class of `P` to the class of `f P`. -/
@[simp]
theorem pointModTorsionMap_mk (f : Hom W₁ W₂) (P : W₁.Point) :
    f.pointModTorsionMap (Submodule.Quotient.mk P) = Submodule.Quotient.mk (f.pointMap P) := by
  simp [pointModTorsionMap]

/-- The identity induces the identity. -/
@[simp]
theorem pointModTorsionMap_id : (id W₁).pointModTorsionMap = LinearMap.id :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun P ↦ by simp

/-- **The induced maps compose.** -/
theorem pointModTorsionMap_comp [W₃.IsElliptic] (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g.comp f).pointModTorsionMap = g.pointModTorsionMap ∘ₗ f.pointModTorsionMap :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun P ↦ by simp [comp_pointMap]

/-- **`f̂ ∘ f` induces multiplication by `deg f`** on the points modulo torsion. -/
@[simp]
theorem dual_pointModTorsionMap_comp (f : Hom W₁ W₂) :
    f.dual.pointModTorsionMap ∘ₗ f.pointModTorsionMap = f.degree • LinearMap.id :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun P ↦ by
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, pointModTorsionMap_mk, ← comp_pointMap,
      dual_comp_self, nsmul_pointMap, id_pointMap, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_smul]

/-- **`f ∘ f̂` induces multiplication by `deg f`** on the points modulo torsion. -/
@[simp]
theorem pointModTorsionMap_comp_dual (f : Hom W₁ W₂) :
    f.pointModTorsionMap ∘ₗ f.dual.pointModTorsionMap = f.degree • LinearMap.id := by
  simpa only [dual_dual, degree_dual] using f.dual.dual_pointModTorsionMap_comp

variable [AdmissibleAbsValues F] in
/-- **The descended Néron–Tate pairing scales by the degree**:
`⟨f x, f y⟩ = deg f · ⟨x, y⟩` on the points modulo torsion. -/
@[simp]
theorem neronTatePairingModTorsion_pointModTorsionMap (f : Hom W₁ W₂)
    (x y : PointModTorsion W₁) :
    neronTatePairingModTorsion W₂ (f.pointModTorsionMap x) (f.pointModTorsionMap y) =
      f.degree * neronTatePairingModTorsion W₁ x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ P =>
    induction y using Submodule.Quotient.induction_on with
    | _ Q => simp

/-- **A nonzero morphism is injective on the points modulo torsion**: `f̂ ∘ f` is multiplication by
`deg f ≠ 0`, and the points modulo torsion are torsion-free. -/
theorem pointModTorsionMap_injective {f : Hom W₁ W₂} (hf : f ≠ 0) :
    Function.Injective f.pointModTorsionMap := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have h := LinearMap.congr_fun f.dual_pointModTorsionMap_comp x
  rw [LinearMap.comp_apply, hx, map_zero, LinearMap.smul_apply, LinearMap.id_apply,
    ← natCast_zsmul] at h
  exact (smul_eq_zero.1 h.symm).resolve_left (by simpa [degree_eq_zero_iff] using hf)

/-- **Isogenous curves have the same rank**: a nonzero morphism `f` and its dual are injective on
the points modulo torsion. -/
theorem finrank_pointModTorsion_eq [Module.Finite ℤ (PointModTorsion W₂)] {f : Hom W₁ W₂}
    (hf : f ≠ 0) : finrank ℤ (PointModTorsion W₁) = finrank ℤ (PointModTorsion W₂) := by
  have : Module.Finite ℤ (PointModTorsion W₁) := .of_injective _ (pointModTorsionMap_injective hf)
  exact le_antisymm (LinearMap.finrank_le_finrank_of_injective (pointModTorsionMap_injective hf))
    (LinearMap.finrank_le_finrank_of_injective
      (pointModTorsionMap_injective (dual_eq_zero_iff.not.2 hf)))

/-! ### The indices and the regulators -/

section Regulator

variable [Module.Finite ℤ (PointModTorsion W₁)] [Module.Finite ℤ (PointModTorsion W₂)]

omit [Module.Finite ℤ (PointModTorsion W₁)] in
/-- **The indices of `f` and of its dual multiply to `(deg f) ^ r`**, for `r` the rank:
`[E₂ : f E₁] · [E₁ : f̂ E₂] = (deg f) ^ r`. -/
theorem index_mul_index_dual_eq_degree_pow {f : Hom W₁ W₂} (hf : f ≠ 0) :
    (LinearMap.range f.pointModTorsionMap).toAddSubgroup.index *
        (LinearMap.range f.dual.pointModTorsionMap).toAddSubgroup.index =
      f.degree ^ finrank ℤ (PointModTorsion W₁) := by
  have : Module.Finite ℤ (PointModTorsion W₁) := .of_injective _ (pointModTorsionMap_injective hf)
  let b₁ := finBasisOfFinrankEq ℤ (PointModTorsion W₁) rfl
  let b₂ := finBasisOfFinrankEq ℤ (PointModTorsion W₂) (finrank_pointModTorsion_eq hf).symm
  -- in these bases the indices are the absolute determinants of the matrices of `f` and `f̂`,
  -- whose product is the matrix of `f̂ ∘ f = deg f`
  rw [LinearMap.index_range_eq_natAbs_det_toMatrix b₁ b₂ (pointModTorsionMap_injective hf),
    mul_comm, LinearMap.index_range_eq_natAbs_det_toMatrix b₂ b₁
      (pointModTorsionMap_injective (dual_eq_zero_iff.not.2 hf)),
    ← Int.natAbs_mul, ← Matrix.det_mul, ← LinearMap.toMatrix_comp, dual_pointModTorsionMap_comp,
    ← natCast_zsmul, LinearEquiv.map_smul, LinearMap.toMatrix_id, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin, Int.natAbs_pow, Int.natAbs_natCast]

variable [AdmissibleAbsValues F]

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

end Regulator

end TauCeti.Isogeny.Hom
