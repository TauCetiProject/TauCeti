/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.MFDeriv.Pi

/-!
# The coordinate time forms of a torus

For a finite family of positive periods `p i`, the torus `∀ i, AddCircle (p i)` is a smooth
manifold, modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` (`TauCeti.instIsManifoldPi`). Its tangent
space at every point is `ι → ℝ`. Each coordinate carries the time form `dt_(p i)` of its circle
(`AddCircle.timeForm`). Its pullback along the coordinate projection is the coordinate time form
`dt_i = pr_i^* dt_(p i)` of the torus (`TauCeti.torusTimeForm p i`), which sends a tangent vector
`v : ι → ℝ` to its `i`-th coordinate `v i`. These are the angle one-forms of the torus.

The coordinate time forms are smooth and closed. On the coordinate fiber through `x`, the circle
`AddCircle (p i)` embedded by `Function.update x i`, the form `dt_i` restricts to `dt_(p i)`, and
every other coordinate form `dt_j` restricts to zero. Hence the integral of `dt_i` along one
circuit of the `i`-th coordinate circle is the period `p i`, while that of `dt_j` is zero; the
integral of `∑ j, c j • dt_j` around it is `c i * p i`. A product
of maps of circles pulls `dt_i` back to the coordinate pullback of the `i`-th factor's pullback of
`dt_(q i)`. In particular the diagonal rescaling of all periods, by the rescaling diffeomorphisms
`AddCircle (p i) ≃ AddCircle (q i)`, pulls `dt_i` back to `(p i)⁻¹ * q i` times `dt_i`.

## Main definitions

* `TauCeti.torusTimeForm p i`: the coordinate time form `dt_i` of the torus.

## Main results

* `TauCeti.torusTimeForm_apply`: `dt_i` sends a tangent vector to its `i`-th coordinate;
  `TauCeti.sum_smul_torusTimeForm_apply` evaluates a constant-coefficient combination.
* `TauCeti.isClosed_torusTimeForm`: `dt_i` is closed.
* `TauCeti.mpullback_update_torusTimeForm_self`,
  `TauCeti.mpullback_update_torusTimeForm_of_ne`: the restrictions of the coordinate time forms
  to a coordinate fiber.
* `TauCeti.pathIntegral_torusTimeForm_update_self`,
  `TauCeti.pathIntegral_torusTimeForm_update_of_ne`: the integrals of the coordinate time forms
  along the coordinate circles, which give the periods.
* `TauCeti.mpullback_update_sum_smul_torusTimeForm`,
  `TauCeti.pathIntegral_sum_smul_torusTimeForm_update`: the same for a constant-coefficient
  combination `∑ j, c j • dt_j`, whose integral around the `i`-th coordinate circle is
  `c i * p i`.
* `TauCeti.mpullback_piMap_torusTimeForm`,
  `TauCeti.mpullback_piMap_diffeomorphAddCircle_torusTimeForm`: pullbacks along products of maps
  of circles, and along the diagonal rescaling of the periods.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 11 (covectors on the torus and line integrals).
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The coordinate time form `dt_i` of the torus `∀ i, AddCircle (p i)`: the pullback of the time
form of the `i`-th circle along the `i`-th coordinate projection. -/
def torusTimeForm (i : ι) :
    SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ 1 :=
  SmoothForm.mpullback (fun x ↦ x i) contMDiff_apply (AddCircle.timeForm (p i))

/-- The coordinate time form is the pullback of the time form of the `i`-th circle along the `i`-th
coordinate projection. -/
theorem torusTimeForm_def (i : ι) :
    torusTimeForm p i =
      SmoothForm.mpullback (fun x ↦ x i) contMDiff_apply (AddCircle.timeForm (p i)) :=
  (rfl)

/-- The coordinate time form `dt_i` sends a tangent vector of the torus, an element of `ι → ℝ`, to
its `i`-th coordinate. -/
@[simp]
theorem torusTimeForm_apply (i : ι) (x : ∀ i, AddCircle (p i))
    (v : Fin 1 → TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    (torusTimeForm p i).1 x v = v 0 i := by
  rw [torusTimeForm_def, SmoothForm.mpullback_apply, mfderiv_apply, AddCircle.timeForm_apply]
  -- `ContinuousLinearMap.proj i` evaluates the tangent vector `v 0 : ι → ℝ` at `i`.
  rfl

/-- The constant-coefficient combination `∑ j, c j • dt_j` of the coordinate time forms sends a
tangent vector `v : ι → ℝ` of the torus to `∑ j, c j * v j`. -/
theorem sum_smul_torusTimeForm_apply (c : ι → ℝ) (x : ∀ i, AddCircle (p i))
    (v : Fin 1 → TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    (∑ j, c j • torusTimeForm p j).1 x v = ∑ j, c j * v 0 j := by
  simp [Finset.sum_apply]

/-- The coordinate time forms of the torus are closed. -/
theorem isClosed_torusTimeForm (i : ι) : (torusTimeForm p i).IsClosed :=
  (AddCircle.isClosed_timeForm (p i)).mpullback _ _

/-- A product of smooth maps `f i : AddCircle (p i) → AddCircle (q i)` pulls the coordinate time
form `dt_i` back to the coordinate pullback of the pullback of `dt_(q i)` along `f i`. -/
theorem mpullback_piMap_torusTimeForm {q : ι → ℝ} [∀ i, Fact (0 < q i)]
    {f : ∀ i, AddCircle (p i) → AddCircle (q i)} (hf : ∀ i, ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (f i)) (i : ι) :
    SmoothForm.mpullback (Pi.map f) (ContMDiff.piMap hf) (torusTimeForm q i) =
      SmoothForm.mpullback (fun x ↦ x i) contMDiff_apply
        (SmoothForm.mpullback (f i) (hf i) (AddCircle.timeForm (q i))) := by
  rw [torusTimeForm, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp, ← LinearMap.comp_apply,
    ← SmoothForm.mpullback_comp]
  -- Both sides pull back along `x ↦ f i (x i)`, written as `(· i) ∘ Pi.map f` and `f i ∘ (· i)`.
  rfl

/-- The diagonal rescaling of the periods, by the rescaling diffeomorphisms
`AddCircle (p j) ≃ AddCircle (q j)` of all coordinates, pulls the coordinate time form `dt_i` of
periods `q` back to `(p i)⁻¹ * q i` times that of periods `p`. -/
@[simp]
theorem mpullback_piMap_diffeomorphAddCircle_torusTimeForm (q : ι → ℝ) [∀ i, Fact (0 < q i)]
    (i : ι) :
    SmoothForm.mpullback (Pi.map fun j ↦ AddCircle.diffeomorphAddCircle (p j) (q j) ∞)
        (ContMDiff.piMap fun j ↦ (AddCircle.diffeomorphAddCircle (p j) (q j) ∞).contMDiff)
        (torusTimeForm q i) = ((p i)⁻¹ * q i) • torusTimeForm p i := by
  rw [mpullback_piMap_torusTimeForm p
    (fun j ↦ (AddCircle.diffeomorphAddCircle (p j) (q j) ∞).contMDiff), torusTimeForm, ← map_smul]
  congr 1
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, AddCircle.mpullback_diffeomorphAddCircle_timeForm, SetLike.val_smul]

variable [DecidableEq ι]

/-- On the coordinate fiber through `x` in the `i`-th coordinate, the coordinate time form `dt_i`
restricts to the time form of the `i`-th circle. -/
@[simp]
theorem mpullback_update_torusTimeForm_self (x : ∀ i, AddCircle (p i)) (i : ι) :
    SmoothForm.mpullback (update x i) (contMDiff_update x i) (torusTimeForm p i) =
      AddCircle.timeForm (p i) := by
  have h : (fun z : ∀ j, AddCircle (p j) ↦ z i) ∘ update x i = id := funext fun y ↦ update_self ..
  rw [torusTimeForm, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, h, TauCeti.mpullback_id]

/-- On the coordinate fiber through `x` in the `i`-th coordinate, every other coordinate time form
`dt_j` restricts to zero. -/
@[simp]
theorem mpullback_update_torusTimeForm_of_ne (x : ∀ i, AddCircle (p i)) {i j : ι} (h : j ≠ i) :
    SmoothForm.mpullback (update x i) (contMDiff_update x i) (torusTimeForm p j) = 0 := by
  have hconst : (fun z : ∀ j, AddCircle (p j) ↦ z j) ∘ update x i = fun _ ↦ x j :=
    funext fun y ↦ update_of_ne h ..
  rw [torusTimeForm, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  refine Subtype.ext <| funext fun y ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [SmoothForm.coe_mpullback, mpullback_apply, hconst, mfderiv_const]
  exact (AddCircle.timeForm (p j)).1 _ |>.map_coord_zero 0 rfl

/-- The integral of the coordinate time form `dt_i` along the `i`-th coordinate circle through `x`,
`t ↦ update x i t`, from `a` to `b` is `b - a`. In particular one circuit `0 ≤ t ≤ p i` has
integral the period `p i`. -/
@[simp]
theorem pathIntegral_torusTimeForm_update_self (x : ∀ i, AddCircle (p i)) (i : ι) (a b : ℝ) :
    pathIntegral (torusTimeForm p i).1 (fun t : ℝ ↦ update x i (t : AddCircle (p i))) a b =
      b - a := by
  have h := pathIntegral_mpullback (torusTimeForm p i).1 (a := a) (b := b)
    (fun _ _ ↦ (hasMFDerivAt_update x i _).mdifferentiableAt)
    (fun t _ ↦ (AddCircle.hasMFDerivAt_coe (p i) t).mdifferentiableAt)
  rw [← SmoothForm.coe_mpullback _ (contMDiff_update (I := fun _ : ι ↦ 𝓘(ℝ)) x i),
    mpullback_update_torusTimeForm_self,
    AddCircle.pathIntegral_timeForm_coe] at h
  -- The curve of `h` is `update x i ∘ (↑)`, the curve of the statement.
  exact h.symm

/-- The integral of the coordinate time form `dt_j` along the `i`-th coordinate circle through `x`
vanishes when `j ≠ i`. -/
@[simp]
theorem pathIntegral_torusTimeForm_update_of_ne (x : ∀ i, AddCircle (p i)) {i j : ι} (h : j ≠ i)
    (a b : ℝ) :
    pathIntegral (torusTimeForm p j).1 (fun t : ℝ ↦ update x i (t : AddCircle (p i))) a b = 0 := by
  have hγ := pathIntegral_mpullback (torusTimeForm p j).1 (a := a) (b := b)
    (fun _ _ ↦ (hasMFDerivAt_update x i _).mdifferentiableAt)
    (fun t _ ↦ (AddCircle.hasMFDerivAt_coe (p i) t).mdifferentiableAt)
  rw [← SmoothForm.coe_mpullback _ (contMDiff_update (I := fun _ : ι ↦ 𝓘(ℝ)) x i),
    mpullback_update_torusTimeForm_of_ne p x h,
    ZeroMemClass.coe_zero, pathIntegral_zero] at hγ
  -- The curve of `hγ` is `update x i ∘ (↑)`, the curve of the statement.
  exact hγ.symm

/-- On the coordinate fiber through `x` in the `i`-th coordinate, the constant-coefficient
combination `∑ j, c j • dt_j` of the coordinate time forms restricts to `c i` times the time form
of the `i`-th circle. -/
theorem mpullback_update_sum_smul_torusTimeForm (c : ι → ℝ) (x : ∀ i, AddCircle (p i)) (i : ι) :
    SmoothForm.mpullback (update x i) (contMDiff_update x i) (∑ j, c j • torusTimeForm p j) =
      c i • AddCircle.timeForm (p i) := by
  rw [map_sum, Finset.sum_eq_single i (fun j _ hj ↦ by
      rw [map_smul, mpullback_update_torusTimeForm_of_ne p x hj, smul_zero]) (by simp),
    map_smul, mpullback_update_torusTimeForm_self]

/-- The integral of the constant-coefficient combination `∑ j, c j • dt_j` of the coordinate time
forms along the `i`-th coordinate circle through `x`, `t ↦ update x i t`, from `a` to `b` is
`c i * (b - a)`. In particular its integral over one circuit `0 ≤ t ≤ p i` is `c i * p i`. -/
theorem pathIntegral_sum_smul_torusTimeForm_update (c : ι → ℝ) (x : ∀ i, AddCircle (p i)) (i : ι)
    (a b : ℝ) :
    pathIntegral (∑ j, c j • torusTimeForm p j).1
        (fun t : ℝ ↦ update x i (t : AddCircle (p i))) a b = c i * (b - a) := by
  have h := pathIntegral_mpullback (∑ j, c j • torusTimeForm p j).1 (a := a) (b := b)
    (fun _ _ ↦ (hasMFDerivAt_update x i _).mdifferentiableAt)
    (fun t _ ↦ (AddCircle.hasMFDerivAt_coe (p i) t).mdifferentiableAt)
  rw [← SmoothForm.coe_mpullback _ (contMDiff_update (I := fun _ : ι ↦ 𝓘(ℝ)) x i),
    mpullback_update_sum_smul_torusTimeForm, SetLike.val_smul, pathIntegral_smul,
    AddCircle.pathIntegral_timeForm_coe, smul_eq_mul] at h
  -- The curve of `h` is `update x i ∘ (↑)`, the curve of the statement.
  exact h.symm

end TauCeti
