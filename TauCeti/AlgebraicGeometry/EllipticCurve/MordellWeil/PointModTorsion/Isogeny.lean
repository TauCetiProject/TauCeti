/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.PointModTorsion.Basic
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The points modulo torsion along an isogeny

Let `f : W₁ → W₂` be a nonzero morphism of elliptic curves over a field, and write
`E₁ = W₁.Point ⧸ torsion` and `E₂ = W₂.Point ⧸ torsion` for the points modulo torsion. A morphism
acts additively on points, so it induces a map `E₁ → E₂`, again written `f`. Since `f̂ ∘ f` and
`f ∘ f̂` are multiplication by `deg f ≠ 0` and `E₁`, `E₂` are torsion-free, this map is injective.
When `E₂` is finitely generated, so is `E₁`, the two have the same rank `r`, and the images of
`f` and of its dual have finite index, with `[E₂ : f E₁] · [E₁ : f̂ E₂] = (deg f) ^ r`. Over a
field with heights, the descended Néron–Tate pairing scales by the degree,
`⟨f x, f y⟩ = deg f · ⟨x, y⟩`, by `TauCeti.Isogeny.Hom.neronTatePairing_pointMap`.

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

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.
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
@[simp]
theorem pointModTorsionMap_comp [W₃.IsElliptic] (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g.comp f).pointModTorsionMap = g.pointModTorsionMap ∘ₗ f.pointModTorsionMap :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun P ↦ by simp [comp_pointMap]

/-- **`f̂ ∘ f` induces multiplication by `deg f`** on the points modulo torsion. -/
@[simp]
theorem dual_pointModTorsionMap_comp_pointModTorsionMap (f : Hom W₁ W₂) :
    f.dual.pointModTorsionMap ∘ₗ f.pointModTorsionMap = f.degree • LinearMap.id :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun P ↦ by
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, pointModTorsionMap_mk, ← comp_pointMap,
      dual_comp_self, nsmul_pointMap, id_pointMap, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_smul]

/-- **`f ∘ f̂` induces multiplication by `deg f`** on the points modulo torsion. -/
@[simp]
theorem pointModTorsionMap_comp_dual_pointModTorsionMap (f : Hom W₁ W₂) :
    f.pointModTorsionMap ∘ₗ f.dual.pointModTorsionMap = f.degree • LinearMap.id := by
  simpa only [dual_dual, degree_dual] using f.dual.dual_pointModTorsionMap_comp_pointModTorsionMap

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
  have h := LinearMap.congr_fun f.dual_pointModTorsionMap_comp_pointModTorsionMap x
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

/-- **The indices of `f` and of its dual multiply to `(deg f) ^ r`**, for `r` the rank:
`[E₂ : f E₁] · [E₁ : f̂ E₂] = (deg f) ^ r`. -/
theorem index_mul_index_dual_eq_degree_pow [Module.Finite ℤ (PointModTorsion W₂)] {f : Hom W₁ W₂}
    (hf : f ≠ 0) :
    (LinearMap.range f.pointModTorsionMap).toAddSubgroup.index *
        (LinearMap.range f.dual.pointModTorsionMap).toAddSubgroup.index =
      f.degree ^ finrank ℤ (PointModTorsion W₁) := by
  have : Module.Finite ℤ (PointModTorsion W₁) := .of_injective _ (pointModTorsionMap_injective hf)
  let b₁ := finBasisOfFinrankEq ℤ (PointModTorsion W₁) rfl
  let b₂ := finBasisOfFinrankEq ℤ (PointModTorsion W₂) (finrank_pointModTorsion_eq hf).symm
  have hb₁ := LinearMap.index_range_eq_natAbs_det_toMatrix b₁ b₂ (pointModTorsionMap_injective hf)
  have hb₂ := LinearMap.index_range_eq_natAbs_det_toMatrix b₂ b₁
    (pointModTorsionMap_injective (dual_eq_zero_iff.not.2 hf))
  -- in these bases the indices are the absolute determinants of the matrices of `f` and `f̂`,
  -- so their product is the absolute determinant of the matrix of `f̂ ∘ f`
  have hprod : (LinearMap.range f.pointModTorsionMap).toAddSubgroup.index *
      (LinearMap.range f.dual.pointModTorsionMap).toAddSubgroup.index =
        (LinearMap.toMatrix b₁ b₁
          (f.dual.pointModTorsionMap ∘ₗ f.pointModTorsionMap)).det.natAbs := by
    rw [hb₁, hb₂, mul_comm, ← Int.natAbs_mul, ← Matrix.det_mul, ← LinearMap.toMatrix_comp]
  -- and `f̂ ∘ f` is multiplication by `deg f`, whose matrix has determinant `(deg f) ^ r`
  rw [hprod, dual_pointModTorsionMap_comp_pointModTorsionMap, ← natCast_zsmul, map_smul,
    LinearMap.toMatrix_id, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    Int.natAbs_pow, Int.natAbs_natCast]

end TauCeti.Isogeny.Hom
