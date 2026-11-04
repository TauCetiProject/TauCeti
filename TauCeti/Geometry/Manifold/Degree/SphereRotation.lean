/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The rotation family of a sphere and its degree

Let `E` be an oriented real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`, and
fix `p ∈ Sⁿ`. The unit tangent vectors of `Sⁿ` at `p` are the unit vectors `v` of the hyperplane
`p^⊥ = (ℝ ∙ p)ᗮ`, the image of the tangent space at `p` in `E` (`range_mvfderiv_subtypeVal`), so
they form the unit sphere `Sⁿ⁻¹` of `p^⊥`. Rotating `p` towards `v` traces the great circle
`z ↦ Re z • p + Im z • v`. These circles assemble into the **rotation family**
(`TauCeti.sphereRotationFamily`)

`F : Sⁿ⁻¹ × S¹ → Sⁿ`, `F (v, z) = Re z • p + Im z • v`,

with `S¹` the unit circle of `ℂ`. Each point `q ≠ ±p` lies on exactly two of these circles, as
`F (v₀, z₀)` and `F (-v₀, z̄₀)` (`TauCeti.sphereRotationFamily_eq_iff`), while `F` collapses
`Sⁿ⁻¹ × {±1}` to `±p`.

We orient `Sⁿ` and `Sⁿ⁻¹ ⊆ p^⊥` by their outward normals (`TauCeti.sphereOrientation`), the
hyperplane `p^⊥` with `p` as positive normal (`Orientation.orthogonalSpanSingleton`), `S¹` as the
unit circle of `ℂ`, and `Sⁿ⁻¹ × S¹` as a product with the first factor first. The derivative of `F`
is computed in `TauCeti.mvfderiv_coe_sphereRotationFamily_apply`. At a point with `Im z ≠ 0` it is
invertible, with orientation sign `(-1)ⁿ⁻¹ · sign(Im z)ⁿ⁻¹`. The two preimages of `q ≠ ±p` have
`Im z` of opposite signs, so every such `q` is a regular value
(`TauCeti.isRegularValue_sphereRotationFamily`) at which the degree of `F` is `1 + (-1)ⁿ⁻¹`
(`TauCeti.degreeAtRegularValue_sphereRotationFamily`). For odd `n` the degree is `2`
(`TauCeti.degreeAtRegularValue_sphereRotationFamily_of_even`), and for even `n` it is `0`.

Evaluated at `p`, the rotation of `Sⁿ` by the angle of `z` in the plane spanned by `p` and `v`
gives `F (v, z)`. So `F` is the evaluation at `p` of a family of rotations, and its degree two
in odd dimensions is the input to the direct proof that odd spheres are covered by
diffeomorphisms (Barraud–Damian–Humilière–Oancea, Proposition 6.34).

In the statements, `n = m + 1`, so that `Sⁿ⁻¹ = Sᵐ` is modelled on `ℝᵐ`.

## Main declarations

* `TauCeti.sphereRotationFamily`: the rotation family `(v, z) ↦ Re z • p + Im z • v`.
* `TauCeti.contMDiff_sphereRotationFamily`: it is smooth.
* `TauCeti.mvfderiv_coe_sphereRotationFamily_apply`: its derivative.
* `TauCeti.sphereRotationFamily_eq_iff`: the two preimages of a point `q ≠ ±p`.
* `TauCeti.isRegularValue_sphereRotationFamily`: every point other than `±p` is a regular value.
* `TauCeti.degreeAtRegularValue_sphereRotationFamily`: the degree is `1 + (-1)ⁿ⁻¹` there.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.34).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Metric Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-! ### Two identities for alternating forms -/

section Alternating

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {m : ℕ}

/-- Moving the last of the `m + 1` vectors after the first one to the second place costs the sign
`(-1)ᵐ`. -/
private theorem alternatingMap_cons_snoc (f : M [⋀^Fin (m + 1 + 1)]→ₗ[ℝ] ℝ) (q y : M)
    (u : Fin m → M) :
    f (Fin.cons q (Fin.snoc u y)) = (-1) ^ m * f (Fin.cons q (Fin.cons y u)) := by
  have e (v : Fin (m + 1) → M) : f (Fin.cons q v) = f.curryLeft q v :=
    (f.curryLeft_apply_apply q v).symm
  have h := (f.curryLeft q).map_perm (Fin.cons y u) (Fin.last m).cycleRange
  rw [Fin.cons_comp_cycleRange, Fin.insertNth_last', Fin.sign_cycleRange, Fin.val_last] at h
  rw [e, e, h, Units.smul_def]
  simp

/-- Replacing the first two vectors `p, v` by `a p + s v, α p + β v` multiplies an alternating form
by the determinant `a β - s α`. -/
private theorem alternatingMap_cons_cons_add_smul (f : M [⋀^Fin (m + 1 + 1)]→ₗ[ℝ] ℝ)
    (p v : M) (w : Fin m → M) (a s α β : ℝ) :
    f (Fin.cons (a • p + s • v) (Fin.cons (α • p + β • v) w)) =
      (a * β - s * α) * f (Fin.cons p (Fin.cons v w)) := by
  have e (x y : M) : f (Fin.cons x (Fin.cons y w)) = (f.curryLeft x).curryLeft y w := by
    rw [AlternatingMap.curryLeft_apply_apply, AlternatingMap.curryLeft_apply_apply]
    rfl
  have hswap : (f.curryLeft v).curryLeft p w = -(f.curryLeft p).curryLeft v w := by
    have h := congrArg (fun f ↦ f w) (f.curryLeft_same (p + v))
    simp only [map_add, AlternatingMap.curryLeft_add, LinearMap.add_apply,
      add_apply, AlternatingMap.curryLeft_same, zero_apply,
      zero_add, add_zero] at h
    linear_combination h
  rw [e, e]
  simp only [map_add, map_smul, AlternatingMap.curryLeft_add, AlternatingMap.curryLeft_smul,
    LinearMap.add_apply, LinearMap.smul_apply, add_apply,
    smul_apply, AlternatingMap.curryLeft_same, zero_apply,
    smul_zero, smul_eq_mul, hswap]
  ring

/-- The alternating-form computation behind the orientation sign of the rotation family. -/
private theorem alternatingMap_rotation (f : M [⋀^Fin (m + 1 + 1)]→ₗ[ℝ] ℝ) (p v : M)
    (u : Fin m → M) (a s α β : ℝ) :
    f (Fin.cons (a • p + s • v) (Fin.snoc (fun j ↦ s • u j) (α • p + β • v))) =
      (-1) ^ m * s ^ m * (a * β - s * α) * f (Fin.cons p (Fin.cons v u)) := by
  have hs : f (Fin.cons p (Fin.cons v fun j ↦ s • u j)) =
      s ^ m * f (Fin.cons p (Fin.cons v u)) := by
    have h := f.map_smul_univ (Fin.cons 1 (Fin.cons 1 fun _ ↦ s)) (Fin.cons p (Fin.cons v u))
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h
    rw [← h]
    congr 1
    ext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i) i <;> simp
  rw [alternatingMap_cons_snoc, alternatingMap_cons_cons_add_smul, hs]
  ring

end Alternating

/-! ### The rotation family -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
  [Fact (finrank ℝ E = m + 1 + 1)]

private theorem inner_coe_coe_sphere (p : sphere (0 : E) 1)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2

private theorem norm_coe_coe_sphere (p : sphere (0 : E) 1)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) : ‖((v : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := by
  -- The norm of a submodule is the norm of the coercion.
  exact norm_eq_of_mem_sphere v

/-- For orthonormal `p, v`, the vector `a • p + s • v` has squared norm `a² + s²`. -/
private theorem norm_sq_smul_add_smul {p v : E} (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : ⟪p, v⟫ = 0)
    (a s : ℝ) : ‖a • p + s • v‖ ^ 2 = a ^ 2 + s ^ 2 := by
  rw [@norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hpv,
    hp, hv]
  simp [sq_abs]

private theorem re_sq_add_im_sq (z : sphere (0 : ℂ) 1) :
    (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  calc (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = Complex.normSq z := by rw [Complex.normSq_apply]; ring
    _ = ‖(z : ℂ)‖ ^ 2 := (Complex.sq_norm _).symm
    _ = 1 := by rw [norm_eq_of_mem_sphere z, one_pow]

/-- The **rotation family** at a point `p` of the unit sphere `Sⁿ` of `E`: a unit vector `v` of
`p^⊥`, that is a unit tangent vector of `Sⁿ` at `p`, and a point `z` of the unit circle of `ℂ` are
sent to `Re z • p + Im z • v`, the point reached by rotating `p` towards `v` by the angle of
`z`. -/
def sphereRotationFamily (p : sphere (0 : E) 1) :
    sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 → sphere (0 : E) 1 := fun x ↦
  ⟨(x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E), by
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      norm_sq_smul_add_smul (norm_eq_of_mem_sphere p) (norm_coe_coe_sphere p x.1)
        (inner_coe_coe_sphere p x.1), re_sq_add_im_sq]⟩

@[simp]
theorem coe_sphereRotationFamily (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    (sphereRotationFamily p x : E) =
      (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- The rotation family is smooth. -/
theorem contMDiff_sphereRotationFamily (p : sphere (0 : E) 1) :
    ContMDiff ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) ∞ (sphereRotationFamily p) := by
  have hv : ContMDiff ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) :=
    ((ℝ ∙ (p : E))ᗮ.subtypeL.contDiff.contMDiff.comp contMDiff_coe_sphere).comp contMDiff_fst
  have hz : ContMDiff ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ (x.2 : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  exact ContMDiff.codRestrict_sphere
    (((Complex.reCLM.contDiff.contMDiff.comp hz).smul contMDiff_const).add
      ((Complex.imCLM.contDiff.contMDiff.comp hz).smul hv))
    fun x ↦ (sphereRotationFamily p x).2

/-- The derivative of the inclusion `Sᵐ ⊆ p^⊥ ⊆ E`, read in `E`, is the derivative of the
inclusion into `p^⊥` followed by the inclusion of `p^⊥`. -/
private theorem mvfderiv_coe_coe_sphere_apply (p : sphere (0 : E) 1)
    (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (a : TangentSpace (𝓡 m) v) :
    mvfderiv (𝓡 m) (fun v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ↦ ((v : (ℝ ∙ (p : E))ᗮ) : E)) v a =
      ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v a :
        (ℝ ∙ (p : E))ᗮ) : E) := by
  have hι := (contMDiff_coe_sphere (E := (ℝ ∙ (p : E))ᗮ) (n := m) (m := 1) v).mdifferentiableAt
    one_ne_zero
  have h := mvfderiv_comp_apply (g := Submodule.subtypeL (ℝ ∙ (p : E))ᗮ) v
    (Submodule.subtypeL (ℝ ∙ (p : E))ᗮ).mdifferentiableAt hι a
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h
  -- `mvfderiv` of the inclusion into `p^⊥` is its `mfderiv`, and the identification of the tangent
  -- spaces of `p^⊥` with `p^⊥` is the identity.
  exact h

/-- The derivative of a real-linear function of the circle coordinate, read on the product. -/
private theorem mvfderiv_clm_coe_snd_apply (p : sphere (0 : E) 1) (L : ℂ →L[ℝ] ℝ)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (w : TangentSpace ((𝓡 m).prod (𝓡 1)) x) :
    mvfderiv ((𝓡 m).prod (𝓡 1))
        (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) x w =
      L (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
        (Manifold.tangentSpaceProdEquiv x w).2) := by
  have hκ := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x.2).mdifferentiableAt one_ne_zero
  have h := mvfderiv_comp_apply (g := L) x.2 L.mdifferentiableAt hκ
    (Manifold.tangentSpaceProdEquiv x w).2
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h
  rw [show (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) =
    (L ∘ ((↑) : sphere (0 : ℂ) 1 → ℂ)) ∘ Prod.snd from rfl, mvfderiv_comp_snd_apply,
    Manifold.tangentSpaceProdEquiv_apply]
  rw [Manifold.tangentSpaceProdEquiv_apply] at h
  -- As above, `mvfderiv` of the inclusion of the circle is its `mfderiv`.
  exact h

/-- **The derivative of the rotation family.** Read in `E`, a tangent vector `(a, b)` at `(v, z)`
is sent to `Re b • p + Im b • v + Im z • a`, where `a` and `b` are read in `p^⊥` and in `ℂ` through
the derivatives of the inclusions. -/
theorem mvfderiv_coe_sphereRotationFamily_apply (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (w : TangentSpace ((𝓡 m).prod (𝓡 1)) x) :
    mvfderiv ((𝓡 m).prod (𝓡 1)) (fun y ↦ (sphereRotationFamily p y : E)) x w =
      (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x w).2).re • (p : E) +
        (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x w).2).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) +
        (x.2 : ℂ).im • ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ)
          x.1 (Manifold.tangentSpaceProdEquiv x w).1 : (ℝ ∙ (p : E))ᗮ) : E) := by
  have hι := (contMDiff_coe_sphere (E := (ℝ ∙ (p : E))ᗮ) (n := m) (m := 1) x.1).mdifferentiableAt
    one_ne_zero
  have hκ := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x.2).mdifferentiableAt one_ne_zero
  have hv : MDifferentiableAt ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ, E)
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((y.1 : (ℝ ∙ (p : E))ᗮ) : E)) x :=
    ((Submodule.subtypeL (ℝ ∙ (p : E))ᗮ).mdifferentiableAt.comp x.1 hι).comp x
      mdifferentiableAt_fst
  have hre : MDifferentiableAt ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ)
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) x :=
    (Complex.reCLM.mdifferentiableAt.comp x.2 hκ).comp x
      mdifferentiableAt_snd
  have him : MDifferentiableAt ((𝓡 m).prod (𝓡 1)) 𝓘(ℝ)
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) x :=
    (Complex.imCLM.mdifferentiableAt.comp x.2 hκ).comp x
      mdifferentiableAt_snd
  have hv' : mvfderiv ((𝓡 m).prod (𝓡 1))
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        ((y.1 : (ℝ ∙ (p : E))ᗮ) : E)) x w =
      ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) x.1
        (Manifold.tangentSpaceProdEquiv x w).1 : (ℝ ∙ (p : E))ᗮ) : E) := by
    rw [← mvfderiv_coe_coe_sphere_apply, Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_fst_apply
      (fun v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ↦ ((v : (ℝ ∙ (p : E))ᗮ) : E)) x w
  -- Write the map as a sum of products of scalar and vector-valued functions.
  rw [show (fun y ↦ (sphereRotationFamily p y : E)) =
    ((fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) •
        fun _ ↦ (p : E)) +
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) •
        fun y ↦ ((y.1 : (ℝ ∙ (p : E))ᗮ) : E) from rfl,
    mvfderiv_add (hre.smul mdifferentiableAt_const) (him.smul hv),
    mvfderiv_smul hre mdifferentiableAt_const, mvfderiv_smul him hv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [mvfderiv_clm_coe_snd_apply p Complex.reCLM x w,
    mvfderiv_clm_coe_snd_apply p Complex.imCLM x w,
    hv', mvfderiv_const]
  simp only [zero_apply, smul_zero, zero_add, Complex.reCLM_apply, Complex.imCLM_apply]
  abel

/-! ### Fibres -/

/-- Two points of the domain, one of them off `Sᵐ × {±1}`, have the same image exactly when they
are equal or exchanged by the involution `(v, z) ↦ (-v, z̄)`. -/
theorem sphereRotationFamily_eq_sphereRotationFamily_iff (p : sphere (0 : E) 1)
    {x y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im ≠ 0) :
    sphereRotationFamily p y = sphereRotationFamily p x ↔
      y = x ∨ (((y.1 : (ℝ ∙ (p : E))ᗮ) : E) = -((x.1 : (ℝ ∙ (p : E))ᗮ) : E) ∧
        (y.2 : ℂ) = (starRingEnd ℂ) (x.2 : ℂ)) := by
  constructor
  · intro h
    have hE := congrArg Subtype.val h
    simp only [coe_sphereRotationFamily] at hE
    -- Pairing with `p` recovers the real parts.
    have hre : (y.2 : ℂ).re = (x.2 : ℂ).re := by
      have h' := congrArg (fun w ↦ ⟪(p : E), w⟫) hE
      simpa only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        norm_eq_of_mem_sphere p, inner_coe_coe_sphere, mul_zero, add_zero, one_pow,
        mul_one] using h'
    have him : (y.2 : ℂ).im • ((y.1 : (ℝ ∙ (p : E))ᗮ) : E) =
        (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
      rw [hre] at hE
      exact add_left_cancel hE
    have hsq : (y.2 : ℂ).im ^ 2 = (x.2 : ℂ).im ^ 2 := by
      linarith [re_sq_add_im_sq y.2, re_sq_add_im_sq x.2, congrArg (· ^ 2) hre]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with him' | him'
    · left
      rw [him'] at him
      refine Prod.ext (Subtype.ext (Subtype.ext (smul_right_injective E hx him)))
        (Subtype.ext (Complex.ext hre him'))
    · right
      rw [him', neg_smul, ← smul_neg] at him
      exact ⟨neg_eq_iff_eq_neg.1 (smul_right_injective E hx him),
        Complex.ext (by simpa using hre) (by simpa using him')⟩
  · rintro (rfl | ⟨hv, hz⟩)
    · rfl
    · refine Subtype.ext ?_
      simp only [coe_sphereRotationFamily, hv, hz, Complex.conj_re, Complex.conj_im, neg_smul,
        smul_neg, neg_neg]

/-- A point with `Im z = 0` is sent to `p` or to `-p`. -/
private theorem sphereRotationFamily_eq_or_eq_neg_of_im_eq_zero (p : sphere (0 : E) 1)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1} (hx : (x.2 : ℂ).im = 0) :
    sphereRotationFamily p x = p ∨ sphereRotationFamily p x = -p := by
  have hre : (x.2 : ℂ).re ^ 2 = 1 ^ 2 := by
    linarith [re_sq_add_im_sq x.2, sq_eq_zero_iff.2 hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hre with h | h
  · exact .inl (Subtype.ext (by simp [h, hx]))
  · exact .inr (Subtype.ext (by simp [h, hx]))

/-- Every point of the sphere other than `±p` is the image of a point with `Im z > 0`. -/
theorem exists_sphereRotationFamily_eq (p : sphere (0 : E) 1) {q : sphere (0 : E) 1}
    (hqp : q ≠ p) (hqp' : q ≠ -p) :
    ∃ x, 0 < (x.2 : ℂ).im ∧ sphereRotationFamily p x = q := by
  -- Split `q = c • p + r` with `r` orthogonal to `p`, and normalize `r`.
  set c : ℝ := ⟪(q : E), (p : E)⟫ with hc
  set r : E := (q : E) - c • (p : E) with hr
  have hp := norm_eq_of_mem_sphere p
  have hpr : ⟪(p : E), r⟫ = 0 := by
    rw [hr, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hp, hc,
      real_inner_comm]
    ring
  have hr0 : r ≠ 0 := by
    intro h0
    have hq : (q : E) = c • (p : E) := by rw [← sub_eq_zero, ← hr, h0]
    have hc1 : |c| = 1 := by
      rw [← norm_eq_of_mem_sphere q, hq, norm_smul, hp, mul_one, Real.norm_eq_abs]
    rcases abs_eq (zero_le_one' ℝ) |>.1 hc1 with h | h
    · exact hqp (Subtype.ext (by rw [hq, h, one_smul]))
    · exact hqp' (Subtype.ext (by rw [hq, h, coe_neg_sphere, neg_one_smul]))
  have hs : 0 < ‖r‖ := norm_pos_iff.2 hr0
  have hq' : c • (p : E) + r = q := by rw [hr]; abel
  have hcs : c ^ 2 + ‖r‖ ^ 2 = 1 := by
    have h := @norm_add_sq_real E _ _ (c • (p : E)) r
    rw [hq', norm_eq_of_mem_sphere q, norm_smul, real_inner_smul_left, hpr, hp,
      Real.norm_eq_abs, mul_one, sq_abs] at h
    linarith
  have hv : ‖‖r‖⁻¹ • r‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  -- The norm of an element of `p^⊥` is its norm in `E`.
  let v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    ⟨⟨‖r‖⁻¹ • r, Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_right.2 hpr)⟩,
      mem_sphere_zero_iff_norm.2 hv⟩
  let z : sphere (0 : ℂ) 1 := ⟨⟨c, ‖r‖⟩, by
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      Complex.sq_norm, Complex.normSq_mk]
    linarith⟩
  refine ⟨(v, z), hs, Subtype.ext ?_⟩
  rw [coe_sphereRotationFamily, ← hq']
  -- The real and imaginary parts of `z` are `c` and `‖r‖`, and `v` is `‖r‖⁻¹ • r`.
  change c • (p : E) + ‖r‖ • (‖r‖⁻¹ • r) = c • (p : E) + r
  rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-! ### Orientation signs -/

/-- The derivative of the rotation family followed by that of the inclusion of `Sᵐ⁺¹` is the
derivative of the family read in `E`. -/
private theorem mvfderiv_coe_mfderiv_sphereRotationFamily_apply (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1)
    (w : TangentSpace ((𝓡 m).prod (𝓡 1)) x) :
    mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E) (sphereRotationFamily p x)
        (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x w) =
      mvfderiv ((𝓡 m).prod (𝓡 1)) (fun y ↦ (sphereRotationFamily p y : E)) x w :=
  (mvfderiv_comp_apply x
    ((contMDiff_coe_sphere (E := E) (n := m + 1) (m := 1) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_sphereRotationFamily p x).mdifferentiableAt (by simp)) w).symm

/-- A tangent basis `b` of the unit sphere of `p^⊥` at `v` is positive for the outward-normal
orientation exactly when `p, v, b₁, …, bₘ`, read in `E`, has positive volume, and this volume does
not vanish. -/
private theorem volumeForm_cons_cons_mvfderiv (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (b : Basis (Fin m) ℝ (TangentSpace (𝓡 m) v)) :
    o.volumeForm (Fin.cons (p : E) (Fin.cons ((v : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
        ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b j) :
          (ℝ ∙ (p : E))ᗮ) : E))) ≠ 0 ∧
      (b.orientation = (sphereOrientation
          (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).orientationAt v ↔
        0 < o.volumeForm (Fin.cons (p : E) (Fin.cons ((v : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
          ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b j) :
            (ℝ ∙ (p : E))ᗮ) : E)))) := by
  -- `v` followed by the image of `b` is a basis `W` of `p^⊥`, oriented like `b`.
  have hli := LinearIndependent.finCons_mvfderiv_coe_sphere v b.linearIndependent
  let W := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin]
    exact (Fact.out : finrank ℝ (ℝ ∙ (p : E))ᗮ = m + 1).symm)
  have hW : (fun i ↦ (W i : E)) = Fin.cons ((v : (ℝ ∙ (p : E))ᗮ) : E) fun j ↦
      ((mvfderiv (𝓡 m) ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b j) :
        (ℝ ∙ (p : E))ᗮ) : E) := by
    ext i
    -- Both sides are `Fin.cons` of the same entries, the coercion taken inside or outside.
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp only [W, coe_basisOfLinearIndependentOfCardEqFinrank] <;> rfl
  refine ⟨?_, ?_⟩
  · rw [← hW]
    exact Orientation.volumeForm_apply_ne_zero_iff.2
      (LinearIndependent.finCons_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
        W.linearIndependent)
  · rw [orientation_eq_orientationAt_sphereOrientation_iff,
      show (Fin.cons ((v : (ℝ ∙ (p : E))ᗮ)) fun i ↦ mvfderiv (𝓡 m)
        ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v (b i)) = ⇑W by simp [W],
      Orientation.volumeForm_apply_pos_iff, Orientation.orientation_eq_orthogonalSpanSingleton_iff,
      hW]

/-- A positively oriented tangent vector `w` of the unit circle at `z`, read in `ℂ`, points
counterclockwise: `Re z Im w - Im z Re w > 0`. -/
private theorem re_mul_im_sub_im_mul_re_pos {z : sphere (0 : ℂ) 1}
    (c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z))
    (hc : c.orientation = (sphereOrientation Complex.orientation).orientationAt z) :
    0 < (z : ℂ).re * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).im -
      (z : ℂ).im * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).re := by
  have h := (orientation_eq_orientationAt_sphereOrientation_iff Complex.orientation c).1 hc
  have hcons : (Fin.cons (z : ℂ) fun i ↦ mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z
      (c i) : Fin 2 → ℂ) = ![(z : ℂ), mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)] := by
    ext i
    fin_cases i <;> rfl
  rw [hcons, ← Orientation.areaForm_to_volumeForm, Complex.areaForm] at h
  generalize mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0) = w at h ⊢
  simpa [Complex.mul_im] using h

/-- At a point with `Im z ≠ 0`, the rotation family preserves the orientations when
`(-1)ᵐ (Im z)ᵐ > 0` and reverses them when `(-1)ᵐ (Im z)ᵐ < 0`. -/
private theorem isOrientationPreservingAt_sphereRotationFamily_and
    (o : Orientation ℝ E (Fin (m + 1 + 1))) (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) (hx : (x.2 : ℂ).im ≠ 0) :
    (0 < (-1) ^ m * (x.2 : ℂ).im ^ m →
      IsOrientationPreservingAt
        ((sphereOrientation (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).prod
          (sphereOrientation Complex.orientation)) (sphereOrientation o)
        (sphereRotationFamily p) x) ∧
    ((-1) ^ m * (x.2 : ℂ).im ^ m < 0 →
      IsOrientationReversingAt
        ((sphereOrientation (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).prod
          (sphereOrientation Complex.orientation)) (sphereOrientation o)
        (sphereRotationFamily p) x) := by
  have hp0 := ne_zero_of_mem_unit_sphere p
  set op := o.orthogonalSpanSingleton hp0
  -- A basis of the tangent space of the first factor, which may be positively or negatively
  -- oriented (when `m = 0` it is empty), a positively oriented one of the second factor, and
  -- their product.
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 m) x.1)
    (((sphereOrientation op).finrank_tangentSpace_eq x.1).trans (Fintype.card_fin m))
  let c := (finBasisOfFinrankEq ℝ (TangentSpace (𝓡 1) x.2)
    (((sphereOrientation Complex.orientation).finrank_tangentSpace_eq x.2).trans
      (Fintype.card_fin 1))).adjustToOrientation
      ((sphereOrientation Complex.orientation).orientationAt x.2)
  have hc : c.orientation = (sphereOrientation Complex.orientation).orientationAt x.2 :=
    Basis.orientation_adjustToOrientation _ _
  let B : Basis (Fin (m + 1)) ℝ (TangentSpace ((𝓡 m).prod (𝓡 1)) x) :=
    (b.prod c).reindex finSumFinEquiv
  have hB : B.orientation = ((sphereOrientation op).prod
      (sphereOrientation Complex.orientation)).orientationAt x ↔
      b.orientation = (sphereOrientation op).orientationAt x.1 := by
    -- `B` is the reindexed product basis, read as a basis of the tangent space of the product.
    change ((b.prod c).reindex finSumFinEquiv).orientation = _ ↔ _
    rw [Manifold.Orientation.orientationAt_prod, ← hc, ← Orientation.prod_basis_orientation b c
      (((sphereOrientation op).finrank_tangentSpace_eq x.1).trans (Fintype.card_fin m))
      (((sphereOrientation Complex.orientation).finrank_tangentSpace_eq x.2).trans
        (Fintype.card_fin 1))]
    rcases b.orientation.eq_or_eq_neg ((sphereOrientation op).orientationAt x.1)
      ((sphereOrientation op).finrank_tangentSpace_eq x.1).symm with h | h
    · simp only [h]
    · rw [h, Orientation.prod_neg_left]
      exact iff_of_false (Module.Ray.ne_neg_self _).symm (Module.Ray.ne_neg_self _).symm
  -- The orientations of `b` and of `c`, read in `E` and in `ℂ`.
  obtain ⟨hD0, h₁⟩ := volumeForm_cons_cons_mvfderiv o p x.1 b
  have h₂ := re_mul_im_sub_im_mul_re_pos c hc
  set v : E := ((x.1 : (ℝ ∙ (p : E))ᗮ) : E)
  set a : Fin m → E := fun j ↦ ((mvfderiv (𝓡 m)
    ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) x.1 (b j) : (ℝ ∙ (p : E))ᗮ) : E)
  set β : ℂ := mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2 (c 0)
  -- The images of the basis `B`, read in `E`.
  have himage : (fun i ↦ mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E)
      (sphereRotationFamily p x)
        (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x (B i))) =
      Fin.snoc (fun j ↦ (x.2 : ℂ).im • a j) (β.re • (p : E) + β.im • v) := by
    have hBi (i : Fin (m + 1)) :
        Manifold.tangentSpaceProdEquiv x (B i) = (b.prod c) (finSumFinEquiv.symm i) := by
      rw [Manifold.tangentSpaceProdEquiv_apply]
      exact Basis.reindex_apply _ _ _
    funext i
    rw [mvfderiv_coe_mfderiv_sphereRotationFamily_apply, mvfderiv_coe_sphereRotationFamily_apply,
      hBi]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [finSumFinEquiv_symm_last, Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd,
        Fin.snoc_last, ContinuousLinearMap.map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
    · rw [finSumFinEquiv_symm_apply_castSucc, Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd,
        Fin.snoc_castSucc, ContinuousLinearMap.map_zero, Complex.zero_re, Complex.zero_im,
        zero_smul, zero_smul, zero_add, zero_add]
  have hvol : o.volumeForm (Fin.cons (sphereRotationFamily p x : E) fun i ↦
      mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E) (sphereRotationFamily p x)
        (mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x (B i))) =
      (-1) ^ m * (x.2 : ℂ).im ^ m * ((x.2 : ℂ).re * β.im - (x.2 : ℂ).im * β.re) *
        o.volumeForm (Fin.cons (p : E) (Fin.cons v a)) := by
    rw [himage, coe_sphereRotationFamily]
    exact alternatingMap_rotation _ _ _ _ _ _ _ _
  set D := o.volumeForm (Fin.cons (p : E) (Fin.cons v a))
  have hκ0 : (-1 : ℝ) ^ m * (x.2 : ℂ).im ^ m ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hx)
  have hvol0 := mul_ne_zero (mul_ne_zero hκ0 h₂.ne') hD0
  -- The image of `B` is a basis of the tangent space of the target, oriented by the sign of
  -- the volume computed above.
  have hli : LinearIndependent ℝ fun i ↦
      mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x (B i) := by
    have h := Orientation.volumeForm_apply_ne_zero_iff.1 (by rw [hvol]; exact hvol0)
    exact LinearIndependent.of_comp (mvfderiv (𝓡 (m + 1)) ((↑) : sphere (0 : E) 1 → E)
      (sphereRotationFamily p x)).toLinearMap (linearIndependent_finCons.1 h).1
  let b' := basisOfLinearIndependentOfCardEqFinrank hli
    ((sphereOrientation o).finrank_tangentSpace_eq (sphereRotationFamily p x)).symm
  have hb' (i : Fin (m + 1)) :
      mfderiv ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) x (B i) = b' i := by
    simp [b']
  have hb'pos : b'.orientation = (sphereOrientation o).orientationAt (sphereRotationFamily p x) ↔
      0 < (-1) ^ m * (x.2 : ℂ).im ^ m * ((x.2 : ℂ).re * β.im - (x.2 : ℂ).im * β.re) * D := by
    rw [orientation_eq_orientationAt_sphereOrientation_iff, ← hvol]
    simp [b']
  constructor
  · intro hκ
    rw [isOrientationPreservingAt_iff_of_basis B b' hb', hB, h₁, hb'pos]
    exact (mul_pos_iff_of_pos_left (mul_pos hκ h₂)).symm
  · intro hκ
    have hneg : b'.orientation =
        -(sphereOrientation o).orientationAt (sphereRotationFamily p x) ↔
        (-1) ^ m * (x.2 : ℂ).im ^ m * ((x.2 : ℂ).re * β.im - (x.2 : ℂ).im * β.re) * D < 0 := by
      rw [← Orientation.ne_iff_eq_neg _ _
        ((sphereOrientation o).finrank_tangentSpace_eq _).symm, Ne, hb'pos, not_lt]
      exact ⟨fun h ↦ lt_of_le_of_ne h hvol0, le_of_lt⟩
    rw [isOrientationReversingAt_iff_of_basis B b' hb', hB, h₁, hneg]
    refine ⟨fun hD ↦ mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hκ h₂) hD, fun h ↦ ?_⟩
    by_contra hD
    exact not_lt.2 (mul_nonneg_of_nonpos_of_nonpos (mul_neg_of_neg_of_pos hκ h₂).le
      (not_lt.1 hD)) h

/-- At a point with `Im z > 0`, the orientation sign of the rotation family is `(-1)ᵐ`. -/
theorem orientationSign_sphereRotationFamily_of_im_pos (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1}
    (hx : 0 < (x.2 : ℂ).im) :
    orientationSign
      ((sphereOrientation (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).prod
        (sphereOrientation Complex.orientation)) (sphereOrientation o)
      (sphereRotationFamily p) x = (-1) ^ m := by
  have h := isOrientationPreservingAt_sphereRotationFamily_and o p x hx.ne'
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow]
    refine orientationSign_of_isOrientationPreservingAt (h.1 ?_)
    rw [hm.neg_one_pow, one_mul]
    positivity
  · rw [hm.neg_one_pow]
    refine orientationSign_of_isOrientationReversingAt (h.2 ?_)
    rw [hm.neg_one_pow, neg_one_mul, neg_lt_zero]
    positivity

/-- At a point with `Im z < 0`, the rotation family preserves orientations. -/
theorem orientationSign_sphereRotationFamily_of_im_neg (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im < 0) :
    orientationSign
      ((sphereOrientation (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).prod
        (sphereOrientation Complex.orientation)) (sphereOrientation o)
      (sphereRotationFamily p) x = 1 := by
  refine orientationSign_of_isOrientationPreservingAt
    ((isOrientationPreservingAt_sphereRotationFamily_and o p x hx.ne).1 ?_)
  rw [← mul_pow]
  exact pow_pos (by linarith) m

/-! ### Regular values and the degree -/

/-- Every point of the sphere other than `±p` is a regular value of the rotation family. -/
theorem isRegularValue_sphereRotationFamily (p : sphere (0 : E) 1) {q : sphere (0 : E) 1}
    (hqp : q ≠ p) (hqp' : q ≠ -p) :
    IsRegularValue ((𝓡 m).prod (𝓡 1)) (𝓡 (m + 1)) (sphereRotationFamily p) q := by
  rw [isRegularValue_iff]
  intro x hx
  have him : (x.2 : ℂ).im ≠ 0 := fun h0 ↦
    (sphereRotationFamily_eq_or_eq_neg_of_im_eq_zero p h0).elim (fun h ↦ hqp (hx ▸ h))
      fun h ↦ hqp' (hx ▸ h)
  -- Any orientation of `E` shows that the derivative is invertible there.
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (m + 1)
  have h := isOrientationPreservingAt_sphereRotationFamily_and (m := m)
    (finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = m + 1 + 1)).orientation p x him
  have hκ : (-1 : ℝ) ^ m * (x.2 : ℂ).im ^ m ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ him)
  obtain ⟨e, he⟩ := hκ.lt_or_gt.elim (fun hneg ↦ (h.2 hneg).isInvertible_mfderiv)
    fun hpos ↦ (h.1 hpos).isInvertible_mfderiv
  rw [isRegularPoint_iff, ← he]
  exact e.surjective

/-- **The degree of the rotation family.** At every point `q ≠ ±p` of `Sᵐ⁺¹`, a regular value
(`TauCeti.isRegularValue_sphereRotationFamily`), the rotation family `Sᵐ × S¹ → Sᵐ⁺¹` has degree
`1 + (-1)ᵐ` for the outward-normal orientations. The two preimages of `q` contribute `(-1)ᵐ` and
`1`. -/
theorem degreeAtRegularValue_sphereRotationFamily (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) {q : sphere (0 : E) 1} (hqp : q ≠ p) (hqp' : q ≠ -p) :
    degreeAtRegularValue
      ((sphereOrientation (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).prod
        (sphereOrientation Complex.orientation)) (sphereOrientation o)
      (sphereRotationFamily p) q = 1 + (-1) ^ m := by
  classical
  obtain ⟨x, hxim, rfl⟩ := exists_sphereRotationFamily_eq p hqp hqp'
  -- The second preimage is the image of `x` under `(v, z) ↦ (-v, z̄)`.
  let x' : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 :=
    (-x.1, ⟨(starRingEnd ℂ) (x.2 : ℂ), by
      rw [mem_sphere_zero_iff_norm, Complex.norm_conj]
      exact norm_eq_of_mem_sphere x.2⟩)
  have hx'im : (x'.2 : ℂ).im < 0 := by
    change ((starRingEnd ℂ) (x.2 : ℂ)).im < 0
    rw [Complex.conj_im]
    linarith
  have hne : x ≠ x' := fun h ↦ by
    have h' := congrArg (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
      (y.2 : ℂ).im) h
    linarith
  rw [degreeAtRegularValue_eq_sum (s := {x, x'}) fun y ↦ ?_, Finset.sum_pair hne,
    orientationSign_sphereRotationFamily_of_im_pos o p hxim,
    orientationSign_sphereRotationFamily_of_im_neg o p hx'im, add_comm]
  rw [Finset.mem_insert, Finset.mem_singleton,
    sphereRotationFamily_eq_sphereRotationFamily_iff p hxim.ne']
  refine or_congr_right ⟨?_, fun ⟨h₁, h₂⟩ ↦ Prod.ext (Subtype.ext (Subtype.ext ?_))
    (Subtype.ext h₂)⟩
  · rintro rfl
    exact ⟨by simp [x'], rfl⟩
  · simp [x', h₁]

/-- For odd `n = m + 1`, the rotation family `Sⁿ⁻¹ × S¹ → Sⁿ` has degree `2` at every point
`q ≠ ±p`. -/
theorem degreeAtRegularValue_sphereRotationFamily_of_even (o : Orientation ℝ E (Fin (m + 1 + 1)))
    (p : sphere (0 : E) 1) (hm : Even m) {q : sphere (0 : E) 1} (hqp : q ≠ p) (hqp' : q ≠ -p) :
    degreeAtRegularValue
      ((sphereOrientation (o.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p))).prod
        (sphereOrientation Complex.orientation)) (sphereOrientation o)
      (sphereRotationFamily p) q = 2 := by
  rw [degreeAtRegularValue_sphereRotationFamily o p hqp hqp', hm.neg_one_pow]
  norm_num

end TauCeti
