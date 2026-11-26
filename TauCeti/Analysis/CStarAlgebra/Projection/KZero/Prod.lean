/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Algebra.Star.Projection.Add
public import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Unitization.Basic
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# `K₀` of a direct sum of C⋆-algebras

Let `e`, `e + x` and `e + y` be matrix projections over a C⋆-algebra with `x y = 0`. Then
`e + x + y` is a projection (`IsStarProjection.add_add_of_mul_eq_zero`), and
`[e + x + y] + [e] = [e + x] + [e + y]` in the projection monoid
(`TauCeti.ProjectionMonoid.mk_add_add_add_mk_of_mul_eq_zero`). The proof is a rotation homotopy:
`diag(e + x + y, e)` and `diag(e + x, e + y)` are joined by the path of projections
`diag(e, e) + diag(x, 0) + R_t diag(y, 0) R_t⋆`, where `R_t` is the rotation by the angle `t`
acting on the two blocks, and homotopic projections are Murray–von Neumann equivalent.

For C⋆-algebras `A` and `B`, a projection `p` over the unitization `(A × B)⁺` has scalar part `e`,
`A`-part `x` and `B`-part `y`, which satisfy these hypotheses. So the endomorphisms of `(A × B)⁺`
induced by the corner maps `inl ∘ fst` and `inr ∘ snd` add up, on `K₀((A × B)⁺)`, to the identity
plus the scalar part, and on the `K₀`-group of the nonunital algebra `A × B` to the identity
(`TauCeti.UnitizationKZero.map_inl_comp_fst_add_map_inr_comp_snd`). Hence
`K₀(A × B) ≃ K₀(A) × K₀(B)` (`TauCeti.UnitizationKZero.prodFstSndEquiv`).

## Main statements

* `TauCeti.ProjectionMonoid.mk_add_add_add_mk_of_mul_eq_zero`:
  `[e + x + y] + [e] = [e + x] + [e + y]` when `x y = 0`.
* `TauCeti.UnitizationKZero.map_inl_comp_fst_add_map_inr_comp_snd`: the corner maps of `A × B`
  add up to the identity of `K₀(A × B)`.
* `TauCeti.UnitizationKZero.prodFstSndEquiv`: `K₀(A × B) ≃+ K₀(A) × K₀(B)`, induced by the
  projections and inverse to the sum of the maps induced by the inclusions.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Section 5.5 (finite direct sums).
-/

public section

open Matrix

namespace TauCeti

section Rotation

variable {C : Type*} [NonUnitalCStarAlgebra C] {n : Type*} [Fintype n] {e x y : Matrix n n C}

/-- The rotation path at the angle with cosine `c` and sine `s` consists of projections. -/
private theorem isStarProjection_rotation (he : IsStarProjection e)
    (hex : IsStarProjection (e + x)) (hey : IsStarProjection (e + y)) (hxy : x * y = 0)
    {c s : ℂ} (hc : star c = c) (hs : star s = s) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsStarProjection (fromBlocks (e + x + c ^ 2 • y) ((c * s) • y) ((c * s) • y)
      (e + s ^ 2 • y)) := by
  have hx := he.isIdempotentElem.mul_add_mul_add_mul_eq hex.isIdempotentElem
  have hy := he.isIdempotentElem.mul_add_mul_add_mul_eq hey.isIdempotentElem
  have he' := he.isIdempotentElem.eq
  have hxs := hex.isSelfAdjoint.of_add_right he.isSelfAdjoint
  have hys := hey.isSelfAdjoint.of_add_right he.isSelfAdjoint
  have hyx : y * x = 0 := by
    simpa only [hys.star_eq] using hxs.star_mul_eq_zero_of_mul_eq_zero hxy
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, fromBlocks_multiply]
    congr 1
    · simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hxy, hyx,
        smul_zero, add_zero]
      linear_combination (norm := module) he' + hx + c ^ 2 • hy + hcs • (c ^ 2 • (y * y))
    · simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hxy,
        add_zero]
      linear_combination (norm := module) (c * s) • hy + hcs • ((c * s) • (y * y))
    · simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hyx,
        smul_zero, add_zero]
      linear_combination (norm := module) (c * s) • hy + hcs • ((c * s) • (y * y))
    · simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
      linear_combination (norm := module) he' + s ^ 2 • hy + hcs • (s ^ 2 • (y * y))
  · have he's : eᴴ = e := he.isSelfAdjoint
    have hx's : xᴴ = x := hxs
    have hy's : yᴴ = y := hys
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
    simp [fromBlocks_conjTranspose, conjTranspose_smul, he's, hx's, hy's, hc, hs, star_pow,
      star_mul']

/-- **Rotation of orthogonal summands.** If `e`, `e + x` and `e + y` are matrix projections over a
C⋆-algebra and `x y = 0`, then `[e + x + y] + [e] = [e + x] + [e + y]` in the projection
monoid. -/
theorem ProjectionMonoid.mk_add_add_add_mk_of_mul_eq_zero (he : IsStarProjection e)
    (hex : IsStarProjection (e + x)) (hey : IsStarProjection (e + y)) (hxy : x * y = 0) :
    mk (e + x + y) (he.add_add_of_mul_eq_zero hex hey hxy) + mk e he =
      mk (e + x) hex + mk (e + y) hey := by
  classical
  rw [← mk_fromBlocks, ← mk_fromBlocks]
  apply mk_eq_mk
  let c : ℝ → ℂ := fun t ↦ (Real.cos t : ℂ)
  let s : ℝ → ℂ := fun t ↦ (Real.sin t : ℂ)
  have hc : Continuous c := Complex.continuous_ofReal.comp Real.continuous_cos
  have hs : Continuous s := Complex.continuous_ofReal.comp Real.continuous_sin
  have h := Continuous.isMurrayVonNeumannEquivalent
    (f := fun t ↦ fromBlocks (e + x + c t ^ 2 • y) ((c t * s t) • y) ((c t * s t) • y)
      (e + s t ^ 2 • y))
    (Continuous.matrix_fromBlocks (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
    (fun t ↦ isStarProjection_rotation he hex hey hxy (Complex.conj_ofReal _)
      (Complex.conj_ofReal _) (by
        simp only [c, s]
        exact_mod_cast Real.cos_sq_add_sin_sq t))
    0 (Real.pi / 2)
  simpa [c, s] using h

end Rotation

namespace UnitizationKZero

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The corner map `(a, b) ↦ (a, 0)` of `A × B`. -/
private abbrev cornerFst : A × B →⋆ₙₐ[ℂ] A × B :=
  (NonUnitalStarAlgHom.inl ℂ A B).comp (NonUnitalStarAlgHom.fst ℂ A B)

/-- The corner map `(a, b) ↦ (0, b)` of `A × B`. -/
private abbrev cornerSnd : A × B →⋆ₙₐ[ℂ] A × B :=
  (NonUnitalStarAlgHom.inr ℂ A B).comp (NonUnitalStarAlgHom.snd ℂ A B)

/-- The unitization of the corner map `(a, b) ↦ (a, 0)`, as a star ring endomorphism of
`(A × B)⁺`. -/
private abbrev starMapFst : Unitization ℂ (A × B) →⋆ₙ+* Unitization ℂ (A × B) :=
  NonUnitalStarRingHom.ofClass (Unitization.starMap (cornerFst (A := A) (B := B)))

/-- The unitization of the corner map `(a, b) ↦ (0, b)`, as a star ring endomorphism of
`(A × B)⁺`. -/
private abbrev starMapSnd : Unitization ℂ (A × B) →⋆ₙ+* Unitization ℂ (A × B) :=
  NonUnitalStarRingHom.ofClass (Unitization.starMap (cornerSnd (A := A) (B := B)))

/-- The scalar part `(r, a) ↦ (r, 0)` of `(A × B)⁺`, the unitization of the zero map. -/
private abbrev scalarPart : Unitization ℂ (A × B) →⋆ₙ+* Unitization ℂ (A × B) :=
  NonUnitalStarRingHom.ofClass (Unitization.starMap (0 : A × B →⋆ₙₐ[ℂ] A × B))

/-- On the projection monoid of `(A × B)⁺`, the corner maps add up to the identity plus the
scalar part. -/
private theorem projectionMonoid_map_add_map (v : ProjectionMonoid (Unitization ℂ (A × B))) :
    ProjectionMonoid.map starMapFst v + ProjectionMonoid.map starMapSnd v =
      v + ProjectionMonoid.map (scalarPart (A := A) (B := B)) v := by
  induction v using ProjectionMonoid.ind with
  | mk k p hp =>
    let e := p.map scalarPart
    let x : Matrix (Fin k) (Fin k) (Unitization ℂ (A × B)) :=
      p.map fun u ↦ ((cornerFst u.snd : A × B) : Unitization ℂ (A × B))
    let y : Matrix (Fin k) (Fin k) (Unitization ℂ (A × B)) :=
      p.map fun u ↦ ((cornerSnd u.snd : A × B) : Unitization ℂ (A × B))
    have hex : p.map starMapFst = e + x := by
      ext i j <;> simp [e, x, scalarPart, Unitization.algebraMap_eq_inl]
    have hey : p.map starMapSnd = e + y := by
      ext i j <;> simp [e, y, scalarPart, Unitization.algebraMap_eq_inl]
    have hp' : p = e + x + y := by
      ext i j <;> simp [e, x, y, scalarPart, Unitization.algebraMap_eq_inl]
    have hxy : x * y = 0 := by
      refine Matrix.ext fun i j ↦ ?_
      simp [x, y, Matrix.mul_apply, ← Unitization.inr_mul, Prod.zero_eq_mk.symm]
    have he : IsStarProjection e := hp.matrix_map scalarPart
    have hpx : IsStarProjection (e + x) := hex ▸ hp.matrix_map _
    have hpy : IsStarProjection (e + y) := hey ▸ hp.matrix_map _
    simp only [ProjectionMonoid.map_mk]
    calc _ = ProjectionMonoid.mk (e + x) hpx + ProjectionMonoid.mk (e + y) hpy := by
          congr 1
          · exact ProjectionMonoid.mk_eq_mk (by rw [hex]; exact .refl hpx)
          · exact ProjectionMonoid.mk_eq_mk (by rw [hey]; exact .refl hpy)
      _ = ProjectionMonoid.mk (e + x + y)
            (he.add_add_of_mul_eq_zero hpx hpy hxy) +
          ProjectionMonoid.mk e he :=
        (ProjectionMonoid.mk_add_add_add_mk_of_mul_eq_zero he hpx hpy hxy).symm
      _ = _ := by
          congr 1
          exact ProjectionMonoid.mk_eq_mk (by rw [← hp']; exact .refl hp)

/-- On `K₀((A × B)⁺)`, the corner maps add up to the identity plus the scalar part. -/
private theorem projectionKZero_map_add_map :
    ProjectionKZero.map starMapFst + ProjectionKZero.map starMapSnd =
      AddMonoidHom.id _ + ProjectionKZero.map (scalarPart (A := A) (B := B)) :=
  Algebra.GrothendieckAddGroup.addHom_ext fun v ↦ by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.id_apply, ProjectionKZero.map_of, ← map_add,
      projectionMonoid_map_add_map]

/-- **Additivity of the corner maps.** The maps `K₀(A × B) → K₀(A × B)` induced by the corner
maps `(a, b) ↦ (a, 0)` and `(a, b) ↦ (0, b)` add up to the identity. -/
theorem map_inl_comp_fst_add_map_inr_comp_snd :
    map ((NonUnitalStarAlgHom.inl ℂ A B).comp (NonUnitalStarAlgHom.fst ℂ A B)) +
        map ((NonUnitalStarAlgHom.inr ℂ A B).comp (NonUnitalStarAlgHom.snd ℂ A B)) =
      AddMonoidHom.id (UnitizationKZero ℂ (A × B)) := by
  ext x
  have h := DFunLike.congr_fun (projectionKZero_map_add_map (A := A) (B := B))
    (x : ProjectionKZero (Unitization ℂ (A × B)))
  have h₀ : ProjectionKZero.map (scalarPart (A := A) (B := B)) x = 0 := by
    simpa only [coe_map, AddMonoidHom.zero_apply, ZeroMemClass.coe_zero] using congrArg Subtype.val
      (DFunLike.congr_fun (map_zero (R := ℂ) (A := A × B) (B := A × B)) x)
  rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, h₀, add_zero, AddMonoidHom.id_apply] at h
  rw [AddMonoidHom.add_apply, AddSubgroup.coe_add, coe_map, coe_map, AddMonoidHom.id_apply]
  exact h

/-- **`K₀` of a direct sum.** The projections of `A × B` induce an isomorphism
`K₀(A × B) ≃+ K₀(A) × K₀(B)`, whose inverse is the sum of the maps induced by the inclusions. -/
noncomputable def prodFstSndEquiv :
    UnitizationKZero ℂ (A × B) ≃+ UnitizationKZero ℂ A × UnitizationKZero ℂ B where
  toFun x := (map (NonUnitalStarAlgHom.fst ℂ A B) x, map (NonUnitalStarAlgHom.snd ℂ A B) x)
  invFun y := map (NonUnitalStarAlgHom.inl ℂ A B) y.1 + map (NonUnitalStarAlgHom.inr ℂ A B) y.2
  left_inv x := by
    have h := DFunLike.congr_fun (map_inl_comp_fst_add_map_inr_comp_snd (A := A) (B := B)) x
    rwa [map_comp, map_comp] at h
  right_inv y := by
    have h₁ : (NonUnitalStarAlgHom.fst ℂ A B).comp (NonUnitalStarAlgHom.inl ℂ A B) =
        NonUnitalStarAlgHom.id ℂ A := by ext; simp
    have h₂ : (NonUnitalStarAlgHom.snd ℂ A B).comp (NonUnitalStarAlgHom.inr ℂ A B) =
        NonUnitalStarAlgHom.id ℂ B := by ext; simp
    have h₃ : (NonUnitalStarAlgHom.fst ℂ A B).comp (NonUnitalStarAlgHom.inr ℂ A B) = 0 := by
      ext; simp
    have h₄ : (NonUnitalStarAlgHom.snd ℂ A B).comp (NonUnitalStarAlgHom.inl ℂ A B) = 0 := by
      ext; simp
    refine Prod.ext ?_ ?_ <;> simp [← AddMonoidHom.comp_apply, ← map_comp, h₁, h₂, h₃, h₄]
  map_add' x y := by simp

@[simp]
theorem prodFstSndEquiv_apply (x : UnitizationKZero ℂ (A × B)) :
    prodFstSndEquiv x =
      (map (NonUnitalStarAlgHom.fst ℂ A B) x, map (NonUnitalStarAlgHom.snd ℂ A B) x) :=
  (rfl)

@[simp]
theorem prodFstSndEquiv_symm_apply (y : UnitizationKZero ℂ A × UnitizationKZero ℂ B) :
    prodFstSndEquiv.symm y =
      map (NonUnitalStarAlgHom.inl ℂ A B) y.1 + map (NonUnitalStarAlgHom.inr ℂ A B) y.2 :=
  (rfl)

end UnitizationKZero

end TauCeti
