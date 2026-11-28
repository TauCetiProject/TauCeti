/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Hyperbolic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import Mathlib.LinearAlgebra.Determinant

/-!
# Levi elements in hyperbolic coordinates

For a commutative ring `R` with involution `σ`, the hyperbolic signed hermitian space
`H^ι` has two totally isotropic coordinate subspaces. An invertible matrix `a` acting on
the second subspace extends to the isometry `((σ(a⁻¹))ᵀ, a)` of `H^ι`. These extensions
give the Levi action in this polarization.

The construction works over rings, so it applies to rational, local and adelic coordinates.
Transport along an isometric equivalence gives the corresponding action in any complete
hyperbolic splitting.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Springer (1985), Chapter 7.
* S. Kudla, *Notes on the local theta correspondence* (1996), §1.
-/

public section

open Matrix
open Matrix.GeneralLinearGroup

namespace TauCeti.SignedHermitianSpace

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  (σ : R →+* R)

/-- The Levi action on hyperbolic coordinates: act by `a` on the second coordinate
and by the inverse `σ`-transpose of `a` on the first coordinate. -/
def hyperbolicLevi : GL ι R →* ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)) where
  toFun a := (toLin (inverseTranspose (GeneralLinearGroup.map σ a))).toLinearEquiv.prodCongr
    (toLin a).toLinearEquiv
  map_one' := by
    ext x <;> simp
  map_mul' a b := by
    ext x <;> simp [mul_apply_eq_comp]

/-- The formula for the Levi action in the two hyperbolic coordinates. -/
@[simp]
theorem hyperbolicLevi_apply (a : GL ι R) (x : (ι → R) × (ι → R)) :
    hyperbolicLevi σ a x =
      ((((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ *ᵥ x.1, (a : Matrix ι ι R) *ᵥ x.2) := by
  simp [hyperbolicLevi, coe_inverseTranspose, ← map_inv,
    mulVec_transpose]

/-- The underlying linear map of a Levi element is the product of its two matrix actions. -/
@[simp]
theorem hyperbolicLevi_toLinearMap (a : GL ι R) :
    (hyperbolicLevi σ a : Module.End R ((ι → R) × (ι → R))) =
      (mulVecLin ((((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ)).prodMap
        (mulVecLin (a : Matrix ι ι R)) := by
  apply LinearMap.ext
  exact fun x ↦ hyperbolicLevi_apply σ a x

/-- The action on the second coordinate determines the Levi parameter. -/
theorem hyperbolicLevi_injective : Function.Injective (hyperbolicLevi σ (ι := ι)) := by
  intro a b h
  apply Units.ext
  apply Matrix.mulVec_injective
  funext x
  have hx := congrArg Prod.snd (DFunLike.congr_fun h (0, x))
  simpa using hx

/-- A diagonal Levi element scales the two isotropic coordinates by mutually dual units.
This is the diagonal torus used in hyperbolic coordinates. -/
theorem hyperbolicLevi_diagGL_apply (d : ι → Rˣ) (x : (ι → R) × (ι → R)) :
    hyperbolicLevi σ (diagGL d) x =
      ((fun i ↦ σ ((d i)⁻¹ : Rˣ) * x.1 i), (fun i ↦ (d i : R) * x.2 i)) := by
  ext i <;> simp [hyperbolicLevi_apply, diagGL_coe, ← map_inv, diagonal_map, mulVec_diagonal]

/-- The determinant of a Levi element is the determinant of its prescribed action divided
by its `σ`-conjugate, written using the inverse matrix to work over any commutative ring. -/
theorem det_hyperbolicLevi (a : GL ι R) :
    LinearMap.det (hyperbolicLevi σ a : Module.End R ((ι → R) × (ι → R))) =
      σ (((a⁻¹ : GL ι R) : Matrix ι ι R).det) * (a : Matrix ι ι R).det := by
  rw [hyperbolicLevi_toLinearMap, LinearMap.det_prodMap]
  rw [← Matrix.toLin'_apply', ← Matrix.toLin'_apply',
    LinearMap.det_toLin', LinearMap.det_toLin', Matrix.det_transpose,
    RingHom.map_det, RingHom.mapMatrix_apply]

variable {σ} {ε : ℤˣ} [RingHomInvPair σ σ]

/-- Levi elements preserve the hyperbolic signed hermitian form. -/
theorem hyperbolicLevi_mem_isometryGroup (a : GL ι R) :
    hyperbolicLevi σ a ∈ (hyperbolic R σ ε ι).form.isometryGroup := by
  rw [LinearMap.mem_isometryGroup_iff]
  intro x y
  simp only [hyperbolicLevi_apply, hyperbolic_form_apply, Finset.sum_add_distrib,
    ← Finset.smul_sum]
  congr 1
  · have hmap : (fun i ↦ σ (((((a⁻¹ : GL ι R) : Matrix ι ι R).map σ)ᵀ *ᵥ x.1) i)) =
        (((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ *ᵥ (σ ∘ x.1)) := by
      ext i
      simp [mulVec, dotProduct]
    rw [← dotProduct, hmap, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec,
      Units.inv_mul, one_mulVec]
    rfl
  · have hmap : (fun i ↦ σ (((a : Matrix ι ι R) *ᵥ x.2) i)) =
        (a : Matrix ι ι R).map σ *ᵥ (σ ∘ x.2) := by
      ext i
      exact RingHom.map_mulVec σ _ _ i
    rw [← dotProduct, hmap, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec,
      ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul]
    simp [dotProduct]

/-- A Levi element is the unique hyperbolic isometry with the prescribed action on the
second coordinate subspace that also preserves the first coordinate subspace. -/
theorem eq_hyperbolicLevi_of_apply_snd
    (g : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R)))
    (hg : g ∈ (hyperbolic R σ ε ι).form.isometryGroup) (a : GL ι R)
    (hfirst : ∀ x, (g (x, 0)).2 = 0)
    (hsecond : ∀ y, g (0, y) = (0, (a : Matrix ι ι R) *ᵥ y)) :
    g = hyperbolicLevi σ a := by
  have hf := hyperbolicLevi_mem_isometryGroup (σ := σ) (ε := ε) a
  have hfst (x : ι → R) : g (x, 0) = hyperbolicLevi σ a (x, 0) := by
    apply Prod.ext
    · funext i
      apply (RingHomInvPair.toRingEquiv σ σ).injective
      let y := ((a⁻¹ : GL ι R) : Matrix ι ι R) *ᵥ Pi.single i 1
      have hy : (a : Matrix ι ι R) *ᵥ y = Pi.single i 1 := by
        dsimp only [y]
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      have h := ((LinearMap.mem_isometryGroup_iff.mp hg) (x, 0) (0, y)).trans
        ((LinearMap.mem_isometryGroup_iff.mp hf) (x, 0) (0, y)).symm
      simp only [hsecond, hyperbolicLevi_apply, mulVec_zero, hy] at h
      simpa [hyperbolic_form_apply, Pi.single_apply] using h
    · simp [hfirst]
  apply LinearEquiv.ext
  rintro ⟨x, y⟩
  have hsplit : (x, y) = (x, 0) + (0, y) := by simp
  rw [hsplit, map_add, hfst, hsecond, map_add]
  simp only [hyperbolicLevi_apply, mulVec_zero]

/-- Characterization of the Levi action by its two isotropic coordinate subspaces. -/
theorem eq_hyperbolicLevi_iff
    (g : ((ι → R) × (ι → R)) ≃ₗ[R] ((ι → R) × (ι → R))) (a : GL ι R) :
    g = hyperbolicLevi σ a ↔
      g ∈ (hyperbolic R σ ε ι).form.isometryGroup ∧
      (∀ x, (g (x, 0)).2 = 0) ∧
      (∀ y, g (0, y) = (0, (a : Matrix ι ι R) *ᵥ y)) := by
  constructor
  · rintro rfl
    exact ⟨hyperbolicLevi_mem_isometryGroup a, by simp, by simp⟩
  · rintro ⟨hg, hfirst, hsecond⟩
    exact eq_hyperbolicLevi_of_apply_snd g hg a hfirst hsecond

variable {V : Type*} [AddCommGroup V] [Module R V]
  {H : SignedHermitianSpace R V σ ε}

namespace IsometryEquiv

/-- The Levi action in a complete hyperbolic splitting `e`: conjugate the coordinate
Levi action by `e`, as an element of the isometry group of the target space. -/
def levi (e : IsometryEquiv (hyperbolic R σ ε ι) H) : GL ι R →* H.form.isometryGroup where
  toFun a := ⟨e.toLinearEquiv.symm.trans ((hyperbolicLevi σ a).trans e.toLinearEquiv), by
    rw [LinearMap.mem_isometryGroup_iff]
    intro x y
    simp only [LinearEquiv.trans_apply, coe_toLinearEquiv, coe_symm_toLinearEquiv, e.map_app]
    rw [LinearMap.mem_isometryGroup_iff.mp (hyperbolicLevi_mem_isometryGroup a)]
    exact e.symm.map_app x y⟩
  map_one' := by
    apply Subtype.ext
    ext x
    simp
  map_mul' a b := by
    apply Subtype.ext
    ext x
    simp [mul_apply_eq_comp]

/-- The defining conjugation formula for a Levi element in a splitting. -/
theorem levi_apply (e : IsometryEquiv (hyperbolic R σ ε ι) H) (a : GL ι R) (v : V) :
    (e.levi a : V ≃ₗ[R] V) v = e (hyperbolicLevi σ a (e.symm v)) := by
  simp only [levi, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    coe_toLinearEquiv, coe_symm_toLinearEquiv]

/-- The underlying linear map of a Levi element is conjugated by the splitting. -/
theorem levi_toLinearMap (e : IsometryEquiv (hyperbolic R σ ε ι) H) (a : GL ι R) :
    ((e.levi a : V ≃ₗ[R] V) : Module.End R V) =
      e.toLinearEquiv.conj (hyperbolicLevi σ a : Module.End R ((ι → R) × (ι → R))) := by
  ext v
  simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.coe_coe,
    coe_toLinearEquiv, coe_symm_toLinearEquiv] using e.levi_apply a v

/-- The determinant of a Levi element is independent of the complete splitting. -/
theorem det_levi (e : IsometryEquiv (hyperbolic R σ ε ι) H) (a : GL ι R) :
    LinearMap.det ((e.levi a : V ≃ₗ[R] V) : Module.End R V) =
      σ (((a⁻¹ : GL ι R) : Matrix ι ι R).det) * (a : Matrix ι ι R).det := by
  rw [levi_toLinearMap, LinearEquiv.conj_apply]
  exact (LinearMap.det_conj _ e.toLinearEquiv).trans (det_hyperbolicLevi σ a)

/-- In the coordinates of the splitting, the Levi action is the coordinate Levi action. -/
@[simp]
theorem levi_apply_image (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (a : GL ι R) (x : (ι → R) × (ι → R)) :
    (e.levi a : V ≃ₗ[R] V) (e x) = e (hyperbolicLevi σ a x) := by
  rw [levi_apply, e.symm_apply_apply]

/-- The Levi action associated to a complete splitting is faithful. -/
theorem levi_injective (e : IsometryEquiv (hyperbolic R σ ε ι) H) :
    Function.Injective e.levi := by
  intro a b h
  apply hyperbolicLevi_injective σ
  apply LinearEquiv.ext
  intro x
  apply e.toLinearEquiv.injective
  have hx := DFunLike.congr_fun (congrArg Subtype.val h) (e x)
  simpa using hx

/-- Among isometries, the Levi element is characterized by its action on the second
coordinate subspace and preservation of the first coordinate subspace of the splitting. -/
theorem eq_levi_iff (e : IsometryEquiv (hyperbolic R σ ε ι) H)
    (g : H.form.isometryGroup) (a : GL ι R) :
    g = e.levi a ↔
      (∀ x, (e.symm ((g : V ≃ₗ[R] V) (e (x, 0)))).2 = 0) ∧
      (∀ y, (g : V ≃ₗ[R] V) (e (0, y)) = e (0, (a : Matrix ι ι R) *ᵥ y)) := by
  constructor
  · rintro rfl
    constructor <;> intro x <;> simp
  · rintro ⟨hfirst, hsecond⟩
    let f := e.toLinearEquiv.trans ((g : V ≃ₗ[R] V).trans e.toLinearEquiv.symm)
    have hf : f ∈ (hyperbolic R σ ε ι).form.isometryGroup := by
      rw [LinearMap.mem_isometryGroup_iff]
      intro x y
      simp only [f, LinearEquiv.trans_apply, coe_toLinearEquiv, coe_symm_toLinearEquiv,
        e.symm.map_app]
      rw [LinearMap.isometryGroup_map_app, e.map_app]
    have hf_eq : f = hyperbolicLevi σ a := eq_hyperbolicLevi_of_apply_snd f hf a
      (fun x ↦ by simpa only [f, LinearEquiv.trans_apply, coe_toLinearEquiv,
        coe_symm_toLinearEquiv] using hfirst x)
      (fun y ↦ by simp [f, hsecond])
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply e.toLinearEquiv.symm.injective
    have hv := DFunLike.congr_fun hf_eq (e.symm v)
    simpa [f, levi_apply, coe_toLinearEquiv, coe_symm_toLinearEquiv] using hv

end IsometryEquiv

end TauCeti.SignedHermitianSpace
