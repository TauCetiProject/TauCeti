/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.Diffeomorph.Pi
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.MFDeriv.Pi
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Family
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The coordinate time forms and the volume form of a torus

For a finite family of positive periods `p i`, the torus `∀ i, AddCircle (p i)` is a smooth
manifold, modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` (`TauCeti.instIsManifoldPi`). Its tangent
space at every point is `ι → ℝ`. Each coordinate carries the time form `dt_(p i)` of its circle
(`AddCircle.timeForm`). Its pullback along the coordinate projection is the coordinate time form
`dt_i = pr_i^* dt_(p i)` of the torus (`TauCeti.torusTimeForm p i`), which sends a tangent vector
`v : ι → ℝ` to its `i`-th coordinate `v i`. These are the angle one-forms of the torus.

The coordinate time forms are smooth and closed, and they form a global frame of the cotangent
bundle of the torus: at every point they are the coordinate functionals of `ι → ℝ`. On the
coordinate fiber through `x`, the circle `AddCircle (p i)` embedded by `Function.update x i`, the
form `dt_i` restricts to `dt_(p i)`, and every other coordinate form `dt_j` restricts to zero. Hence
the integral of `dt_i` along one circuit of the `i`-th coordinate circle is the period `p i`, while
that of `dt_j` is zero; the integral of `∑ j, c j • dt_j` around it is `c i * p i`. A product of
maps of circles pulls `dt_i` back to the coordinate pullback of the `i`-th factor's pullback of
`dt_(q i)`. In particular the diagonal rescaling of all periods, by the rescaling diffeomorphisms
`AddCircle (p i) ≃ AddCircle (q i)`, pulls `dt_i` back to `(p i)⁻¹ * q i` times `dt_i`. Reindexing
the factors along a map `e` of index sets, `x ↦ (j ↦ x (e j))`, pulls `dt_j` back to `dt_(e j)`.
When all periods are equal, an invertible integer matrix `A`, acting by `x ↦ A • x`, pulls `dt_i`
back to `∑ j, A i j • dt_j`, so it pulls `∑ j, b j • dt_j` back to `∑ k, (Aᵀ b)_k • dt_k`.

For an ordered index set `Fin n`, the ordered wedge product `dt_0 ∧ ⋯ ∧ dt_(n-1)` of the
coordinate time forms is the volume form of the torus (`TauCeti.torusVolumeForm p`). It sends
tangent vectors `v 0, …, v (n - 1)`, elements of `Fin n → ℝ`, to the determinant of the matrix
`(v j i)` of their coordinates, so it vanishes nowhere. Reordering the factors by a permutation `σ`
pulls it back to `sign σ` times itself, and the diagonal rescaling of the periods pulls it back to
`∏ i, (p i)⁻¹ * q i` times itself.

The forms are compatible with grouping the factors. Concatenating the factors,
`(x, y) ↦ Fin.addCases x y` from `T^m × T^k` to `T^(m + k)` (`Diffeomorph.piAddCases`), pulls the
coordinate time forms of the first `m` factors back to those of `T^m` along the first projection,
those of the last `k` factors back to those of `T^k` along the second projection, and the volume
form back to the wedge product `pr₁^* vol_m ∧ pr₂^* vol_k`. Appending a circle,
`(x, t) ↦ Fin.snoc x t` from `T^m × AddCircle (p m)` to `T^(m + 1)` (`Diffeomorph.piSnoc`), pulls
the volume form back to `pr₁^* vol_m ∧ pr₂^* dt_(p m)`. Splitting off the first circle instead,
the association map `x ↦ (x 0, Fin.tail x)` from `T^(m + 1)` to `AddCircle (p 0) × T^m` is the
inverse of `(t, x) ↦ Fin.cons t x` (`Diffeomorph.piCons`). It pulls the time form of the first
circle back to `dt_0` and the coordinate time form `dt_i` of `T^m` back to `dt_(i + 1)`, and
`Fin.cons` pulls the volume form back to `pr₁^* dt_(p 0) ∧ pr₂^* vol_m`, read in degree `m + 1`.
A torus with a single factor is its circle:
its volume form is the time form of that factor. The torus with no factors is a point, on which the
volume form is the constant `1`, so a point factor `T^0` does not contribute to the volume form of
`T^m × T^0`.

## Main definitions

* `TauCeti.torusTimeForm p i`: the coordinate time form `dt_i` of the torus.
* `TauCeti.torusVolumeForm p`: the volume form `dt_0 ∧ ⋯ ∧ dt_(n-1)` of the torus.

## Main results

* `TauCeti.torusTimeForm_apply`: `dt_i` sends a tangent vector to its `i`-th coordinate;
  `TauCeti.sum_smul_torusTimeForm_apply` evaluates a constant-coefficient combination.
* `TauCeti.isLocalFrameOn_torusTimeForm`: the coordinate time forms are a global frame of the
  cotangent bundle of the torus.
* `TauCeti.isClosed_torusTimeForm`, `TauCeti.isClosed_sum_smul_torusTimeForm`: `dt_i` and the
  constant-coefficient combinations `∑ j, c j • dt_j` are closed.
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
* `TauCeti.mpullback_reindex_torusTimeForm`: naturality under reindexing of the factors.
* `TauCeti.mpullback_generalLinearGroup_smul_torusTimeForm`: an invertible integer matrix `A`
  acting on a torus of equal periods pulls `dt_i` back to `∑ j, A i j • dt_j`;
  `TauCeti.mpullback_generalLinearGroup_smul_sum_smul_torusTimeForm` pulls `∑ j, b j • dt_j` back
  to `∑ k, (Aᵀ b)_k • dt_k`.
* `TauCeti.torusVolumeForm_apply`, `TauCeti.torusVolumeForm_apply_ne_zero`: the determinant
  formula for the volume form, which vanishes nowhere, and its two-dimensional case
  `TauCeti.torusVolumeForm_fin_two_apply`, `dt₀ ∧ dt₁ (v, w) = v₀ w₁ - w₀ v₁`;
  `TauCeti.torusVolumeForm_apply_eq_apply_zero`: its coefficients are constant.
* `TauCeti.mpullback_reindex_torusVolumeForm`,
  `TauCeti.mpullback_piMap_diffeomorphAddCircle_torusVolumeForm`: the permutation sign law and the
  rescaling law for the volume form.
* `TauCeti.mpullback_piAddCases_torusTimeForm_castAdd`,
  `TauCeti.mpullback_piAddCases_torusTimeForm_natAdd`,
  `TauCeti.mpullback_piAddCases_torusVolumeForm`: concatenating two tori.
* `TauCeti.mpullback_piSnoc_torusTimeForm_castSucc`, `TauCeti.mpullback_piSnoc_torusTimeForm_last`,
  `TauCeti.mpullback_piSnoc_torusVolumeForm`: appending a circle to a torus.
* `TauCeti.mpullback_piCons_torusTimeForm_zero`, `TauCeti.mpullback_piCons_torusTimeForm_succ`,
  `TauCeti.mpullback_piCons_torusVolumeForm`: prepending a circle to a torus;
  `TauCeti.mpullback_piCons_symm_mpullback_fst_timeForm`,
  `TauCeti.mpullback_piCons_symm_mpullback_snd_torusTimeForm`: the association map splitting off
  the first circle pulls the time forms of the factors back to the coordinate time forms.
* `TauCeti.mpullback_piUnique_timeForm`, `TauCeti.torusVolumeForm_fin_one`: the one-factor torus
  is its circle.
* `TauCeti.torusVolumeForm_fin_zero_apply`, `TauCeti.mpullback_piAddCases_torusVolumeForm_zero`:
  the empty torus is a point, and deleting a point factor does not change the volume form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 11 (covectors on the torus and line integrals) and
  Chapter 14 (wedge products of covectors).
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

section TimeForm

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
    (torusTimeForm p i).val x v = v 0 i := by
  rw [torusTimeForm_def, SmoothForm.mpullback_apply, mfderiv_apply, AddCircle.timeForm_apply]
  -- `ContinuousLinearMap.proj i` evaluates the tangent vector `v 0 : ι → ℝ` at `i`.
  rfl

/-- The constant-coefficient combination `∑ j, c j • dt_j` of the coordinate time forms sends a
tangent vector `v : ι → ℝ` of the torus to `∑ j, c j * v j`. -/
theorem sum_smul_torusTimeForm_apply (c : ι → ℝ) (x : ∀ i, AddCircle (p i))
    (v : Fin 1 → TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    (∑ j, c j • torusTimeForm p j).val x v = ∑ j, c j * v 0 j := by
  simp [Finset.sum_apply]

/-- The coordinate time forms of the torus are closed. -/
theorem isClosed_torusTimeForm (i : ι) : (torusTimeForm p i).IsClosed :=
  (AddCircle.isClosed_timeForm (p i)).mpullback _ _

/-- The constant-coefficient combinations `∑ j, c j • dt_j` of the coordinate time forms of the
torus are closed. -/
theorem isClosed_sum_smul_torusTimeForm (c : ι → ℝ) : (∑ j, c j • torusTimeForm p j).IsClosed := by
  rw [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [map_smul, (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).1 (isClosed_torusTimeForm p j),
    smul_zero]

/-- The coordinate time forms `dt_i` of the torus `∀ i, AddCircle (p i)` form a global frame of its
cotangent bundle: at every point they are the coordinate functionals of `ι → ℝ`, the dual basis of
its standard basis. -/
theorem isLocalFrameOn_torusTimeForm :
    IsLocalFrameOn (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ((ι → ℝ) →L[ℝ] ℝ) ∞
      (fun i ↦ ⇑(SmoothForm.degreeOneEquiv (torusTimeForm p i))) univ := by
  classical
  let b := (Pi.basisFun ℝ ι).dualBasis.map LinearMap.toContinuousLinearMap
  have hb : ∀ (x : ∀ i, AddCircle (p i)) (i : ι),
      SmoothForm.degreeOneEquiv (torusTimeForm p i) x = b i :=
    fun x i ↦ ContinuousLinearMap.ext fun v ↦ by
      rw [SmoothForm.degreeOneEquiv_apply_apply, torusTimeForm_apply]
      -- The `i`-th vector of the dual basis is the `i`-th coordinate functional.
      exact ((fun w : ι → ℝ ↦ show b i w = w i by simp [b]) v).symm
  refine isLocalFrameOn_degreeOneEquiv_iff.2 fun x _ ↦ ?_
  simp only [hb]
  exact ⟨b.linearIndependent, b.span_eq.ge⟩

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

/-- Reindexing the factors of the torus along a map `e` of index sets, `x ↦ (j ↦ x (e j))`, pulls
the `j`-th coordinate time form of the reindexed torus back to the `e j`-th coordinate time
form. -/
@[simp]
theorem mpullback_reindex_torusTimeForm {ι' : Type*} [Fintype ι'] (e : ι' → ι) (j : ι') :
    SmoothForm.mpullback (fun (x : ∀ i, AddCircle (p i)) (l : ι') ↦ x (e l))
        (contMDiff_pi_iff.2 fun _ ↦ contMDiff_apply) (torusTimeForm (fun l ↦ p (e l)) j) =
      torusTimeForm p (e j) := by
  rw [torusTimeForm, torusTimeForm, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  -- Both sides pull back the time form of `AddCircle (p (e j))` along `x ↦ x (e j)`.
  rfl

variable [DecidableEq ι]

/-- An invertible integer matrix `A`, acting on the torus `ι → AddCircle q` of equal periods, pulls
the coordinate time form `dt_i` back to `∑ j, A i j • dt_j`. -/
theorem mpullback_generalLinearGroup_smul_torusTimeForm (q : ℝ) [Fact (0 < q)] (A : GL ι ℤ)
    (i : ι) :
    SmoothForm.mpullback (fun x : ι → AddCircle q ↦ A • x) (contMDiff_const_smul A)
        (torusTimeForm (fun _ ↦ q) i) =
      ∑ j, ((A : Matrix ι ι ℤ) i j : ℝ) • torusTimeForm (fun _ ↦ q) j := by
  refine Subtype.ext (funext fun x ↦ ?_)
  ext v
  rw [SmoothForm.mpullback_apply, torusTimeForm_apply, sum_smul_torusTimeForm_apply]
  -- The derivative of `x ↦ A • x` is multiplication by `A`; take its `i`-th coordinate.
  simpa [Matrix.mulVec, dotProduct] using
    congrFun (AddCircle.mfderiv_generalLinearGroup_smul_apply q A x (v 0)) i

open Matrix in
/-- An invertible integer matrix `A`, acting on the torus `ι → AddCircle q` of equal periods, pulls
the constant-coefficient combination `∑ j, b j • dt_j` back to `∑ k, (Aᵀ b)_k • dt_k`. -/
theorem mpullback_generalLinearGroup_smul_sum_smul_torusTimeForm (q : ℝ) [Fact (0 < q)]
    (A : GL ι ℤ) (b : ι → ℝ) :
    SmoothForm.mpullback (fun x : ι → AddCircle q ↦ A • x) (contMDiff_const_smul A)
        (∑ j, b j • torusTimeForm (fun _ ↦ q) j) =
      ∑ k, (((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ))ᵀ *ᵥ b) k • torusTimeForm (fun _ ↦ q) k := by
  simp only [map_sum, map_smul, mpullback_generalLinearGroup_smul_torusTimeForm,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.sum_smul]
  congr 1
  simp [Matrix.mulVec, dotProduct, mul_comm]

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
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, hconst, mpullback_const one_ne_zero, ZeroMemClass.coe_zero]

/-- The integral of the coordinate time form `dt_i` along the `i`-th coordinate circle through `x`,
`t ↦ update x i t`, from `a` to `b` is `b - a`. In particular one circuit `0 ≤ t ≤ p i` has
integral the period `p i`. -/
@[simp]
theorem pathIntegral_torusTimeForm_update_self (x : ∀ i, AddCircle (p i)) (i : ι) (a b : ℝ) :
    pathIntegral (torusTimeForm p i).val (fun t : ℝ ↦ update x i (t : AddCircle (p i))) a b =
      b - a := by
  have h := pathIntegral_mpullback (torusTimeForm p i).val (a := a) (b := b)
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
    pathIntegral (torusTimeForm p j).val (fun t : ℝ ↦ update x i (t : AddCircle (p i))) a b = 0
        := by
  have hγ := pathIntegral_mpullback (torusTimeForm p j).val (a := a) (b := b)
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
    pathIntegral (∑ j, c j • torusTimeForm p j).val
        (fun t : ℝ ↦ update x i (t : AddCircle (p i))) a b = c i * (b - a) := by
  have h := pathIntegral_mpullback (∑ j, c j • torusTimeForm p j).val (a := a) (b := b)
    (fun _ _ ↦ (hasMFDerivAt_update x i _).mdifferentiableAt)
    (fun t _ ↦ (AddCircle.hasMFDerivAt_coe (p i) t).mdifferentiableAt)
  rw [← SmoothForm.coe_mpullback _ (contMDiff_update (I := fun _ : ι ↦ 𝓘(ℝ)) x i),
    mpullback_update_sum_smul_torusTimeForm, SetLike.val_smul, pathIntegral_smul,
    AddCircle.pathIntegral_timeForm_coe, smul_eq_mul] at h
  -- The curve of `h` is `update x i ∘ (↑)`, the curve of the statement.
  exact h.symm

end TimeForm

section VolumeForm

variable {n : ℕ} (p : Fin n → ℝ) [∀ i, Fact (0 < p i)]

/-- The **volume form** `dt_0 ∧ ⋯ ∧ dt_(n-1)` of the torus `∀ i : Fin n, AddCircle (p i)`: the
ordered wedge product of its coordinate time forms. -/
def torusVolumeForm :
    SmoothForm (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ n :=
  SmoothForm.wedgeFamily (torusTimeForm p)

/-- The volume form of the torus is the wedge product of its coordinate time forms. -/
theorem torusVolumeForm_def : torusVolumeForm p = SmoothForm.wedgeFamily (torusTimeForm p) :=
  (rfl)

/-- The volume form of the torus sends tangent vectors `v 0, …, v (n - 1)`, elements of
`Fin n → ℝ`, to the determinant of the matrix `(v j i)` of their coordinates. -/
@[simp]
theorem torusVolumeForm_apply (x : ∀ i, AddCircle (p i))
    (v : Fin n → TangentSpace (ModelWithCorners.pi fun _ : Fin n ↦ 𝓘(ℝ)) x) :
    (torusVolumeForm p).val x v = (Matrix.of fun i j ↦ v j i).det := by
  rw [torusVolumeForm, SmoothForm.wedgeFamily_apply]
  simp only [torusTimeForm_apply, Matrix.cons_val_fin_one]

/-- On a two-torus the volume form `dt₀ ∧ dt₁` sends tangent vectors `v` and `w` to
`v₀ w₁ - w₀ v₁`. -/
theorem torusVolumeForm_fin_two_apply (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)]
    (x : ∀ i, AddCircle (p i)) (v w : TangentSpace (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x) :
    (torusVolumeForm p).val x ![v, w] = v 0 * w 1 - w 0 * v 1 := by
  rw [torusVolumeForm_apply, Matrix.det_fin_two]
  simp

/-- The volume form of the torus has constant coefficients in the product charts: at every point
it is the same alternating map of `Fin n → ℝ` as at `0`. -/
theorem torusVolumeForm_apply_eq_apply_zero (x : ∀ i, AddCircle (p i)) :
    ((torusVolumeForm p).val x : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) = (torusVolumeForm p).val 0 := by
  ext w
  -- Both sides are the determinant of `w`, read at the points `x` and `0`.
  exact (torusVolumeForm_apply p x w).trans (torusVolumeForm_apply p 0 w).symm

/-- The volume form of the torus takes the value `1` on the coordinate basis of a tangent
space. -/
theorem torusVolumeForm_apply_basisFun (x : ∀ i, AddCircle (p i)) :
    (torusVolumeForm p).val x (Pi.basisFun ℝ (Fin n)) = 1 := by
  refine (torusVolumeForm_apply p x _).trans ?_
  convert Matrix.det_one (n := Fin n) (R := ℝ)
  ext i j
  simp [Matrix.one_apply, Pi.single_apply]

/-- The volume form of the torus vanishes nowhere. -/
theorem torusVolumeForm_apply_ne_zero (x : ∀ i, AddCircle (p i)) : (torusVolumeForm p).val x ≠ 0 :=
  fun h ↦ one_ne_zero <| (torusVolumeForm_apply_basisFun p x).symm.trans
    (DFunLike.congr_fun h _)

/-- **The permutation sign law.** Reordering the factors of the torus by a permutation `σ`,
`x ↦ (j ↦ x (σ j))`, pulls the volume form of the reordered torus back to `sign σ` times the
volume form. -/
@[simp]
theorem mpullback_reindex_torusVolumeForm (σ : Equiv.Perm (Fin n)) :
    SmoothForm.mpullback (fun (x : ∀ i, AddCircle (p i)) (j : Fin n) ↦ x (σ j))
        (contMDiff_pi_iff.2 fun _ ↦ contMDiff_apply) (torusVolumeForm fun j ↦ p (σ j)) =
      (Equiv.Perm.sign σ : ℝ) • torusVolumeForm p := by
  rw [torusVolumeForm, SmoothForm.mpullback_wedgeFamily]
  simp_rw [mpullback_reindex_torusTimeForm]
  exact SmoothForm.wedgeFamily_comp_perm (torusTimeForm p) σ

/-- The diagonal rescaling of the periods, by the rescaling diffeomorphisms
`AddCircle (p i) ≃ AddCircle (q i)` of all coordinates, pulls the volume form of periods `q` back
to `∏ i, (p i)⁻¹ * q i` times that of periods `p`. -/
@[simp]
theorem mpullback_piMap_diffeomorphAddCircle_torusVolumeForm (q : Fin n → ℝ)
    [∀ i, Fact (0 < q i)] :
    SmoothForm.mpullback (Pi.map fun j ↦ AddCircle.diffeomorphAddCircle (p j) (q j) ∞)
        (ContMDiff.piMap fun j ↦ (AddCircle.diffeomorphAddCircle (p j) (q j) ∞).contMDiff)
        (torusVolumeForm q) = (∏ i, (p i)⁻¹ * q i) • torusVolumeForm p := by
  rw [torusVolumeForm, SmoothForm.mpullback_wedgeFamily]
  simp_rw [mpullback_piMap_diffeomorphAddCircle_torusTimeForm]
  exact SmoothForm.wedgeFamily_smul _ (torusTimeForm p)

end VolumeForm

/-! ### Products of tori -/

section Product

variable {m k : ℕ}

/-- **Concatenating tori, first block.** The concatenation `(x, y) ↦ Fin.addCases x y` from
`T^m × T^k` to `T^(m + k)` pulls the coordinate time form of the factor `Fin.castAdd k i` back to
the pullback along the first projection of the coordinate time form `dt_i` of `T^m`. -/
@[simp]
theorem mpullback_piAddCases_torusTimeForm_castAdd (p : Fin (m + k) → ℝ) [∀ i, Fact (0 < p i)]
    (i : Fin m) :
    SmoothForm.mpullback (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusTimeForm p (Fin.castAdd k i)) =
      SmoothForm.mpullback Prod.fst contMDiff_fst
        (torusTimeForm (fun i : Fin m ↦ p (Fin.castAdd k i)) i) := by
  rw [torusTimeForm_def, torusTimeForm_def]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext fun _ ↦ by simp) _

/-- **Concatenating tori, second block.** The concatenation `(x, y) ↦ Fin.addCases x y` from
`T^m × T^k` to `T^(m + k)` pulls the coordinate time form of the factor `Fin.natAdd m j` back to
the pullback along the second projection of the coordinate time form `dt_j` of `T^k`. -/
@[simp]
theorem mpullback_piAddCases_torusTimeForm_natAdd (p : Fin (m + k) → ℝ) [∀ i, Fact (0 < p i)]
    (j : Fin k) :
    SmoothForm.mpullback (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusTimeForm p (Fin.natAdd m j)) =
      SmoothForm.mpullback Prod.snd contMDiff_snd
        (torusTimeForm (fun j : Fin k ↦ p (Fin.natAdd m j)) j) := by
  rw [torusTimeForm_def, torusTimeForm_def]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext fun _ ↦ by simp) _

/-- **Appending a circle, the first factors.** The map `(x, t) ↦ Fin.snoc x t` from
`T^m × AddCircle (p m)` to `T^(m + 1)` pulls the coordinate time form of the factor
`Fin.castSucc i` back to the pullback along the first projection of the coordinate time form
`dt_i` of `T^m`. -/
@[simp]
theorem mpullback_piSnoc_torusTimeForm_castSucc (p : Fin (m + 1) → ℝ) [∀ i, Fact (0 < p i)]
    (i : Fin m) :
    SmoothForm.mpullback (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusTimeForm p i.castSucc) =
      SmoothForm.mpullback Prod.fst contMDiff_fst
        (torusTimeForm (fun i : Fin m ↦ p i.castSucc) i) := by
  rw [torusTimeForm_def, torusTimeForm_def]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext fun _ ↦ by simp) _

/-- **Appending a circle, the last factor.** The map `(x, t) ↦ Fin.snoc x t` from
`T^m × AddCircle (p m)` to `T^(m + 1)` pulls the coordinate time form of the last factor back to
the pullback along the second projection of the time form of the appended circle. -/
@[simp]
theorem mpullback_piSnoc_torusTimeForm_last (p : Fin (m + 1) → ℝ) [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusTimeForm p (Fin.last m)) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm (p (Fin.last m))) := by
  have h : (fun x : ∀ i, AddCircle (p i) ↦ x (Fin.last m)) ∘
      ⇑(Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞) = Prod.snd :=
    funext fun _ ↦ by simp
  simp only [torusTimeForm_def, SmoothForm.mpullback_mpullback, h]

/-- **Splitting off the first circle, the first factor.** The map `(t, x) ↦ Fin.cons t x` from
`AddCircle (p 0) × T^m` to `T^(m + 1)`, inverse to the association map splitting off the first
circle, pulls the coordinate time form of the first factor back to the pullback along the first
projection of the time form of that circle. -/
@[simp]
theorem mpullback_piCons_torusTimeForm_zero (p : Fin (m + 1) → ℝ) [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusTimeForm p 0) =
      SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (p 0)) := by
  have h : (fun x : ∀ i, AddCircle (p i) ↦ x 0) ∘
      ⇑(Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞) = Prod.fst :=
    funext fun _ ↦ by simp
  simp only [torusTimeForm_def, SmoothForm.mpullback_mpullback, h]

/-- **Splitting off the first circle, the remaining factors.** The map `(t, x) ↦ Fin.cons t x`
from `AddCircle (p 0) × T^m` to `T^(m + 1)` pulls the coordinate time form of the factor
`Fin.succ i` back to the pullback along the second projection of the coordinate time form `dt_i`
of `T^m`. -/
@[simp]
theorem mpullback_piCons_torusTimeForm_succ (p : Fin (m + 1) → ℝ) [∀ i, Fact (0 < p i)]
    (i : Fin m) :
    SmoothForm.mpullback (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusTimeForm p i.succ) =
      SmoothForm.mpullback Prod.snd contMDiff_snd
        (torusTimeForm (fun i : Fin m ↦ p i.succ) i) := by
  rw [torusTimeForm_def, torusTimeForm_def]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext fun _ ↦ by simp) _

/-- **The association map, the first circle.** The association map `x ↦ (x 0, Fin.tail x)` from
`T^(m + 1)` to `AddCircle (p 0) × T^m` pulls the time form of the first circle, read on the
product along the first projection, back to the coordinate time form `dt_0`. -/
@[simp]
theorem mpullback_piCons_symm_mpullback_fst_timeForm (p : Fin (m + 1) → ℝ)
    [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).symm
        (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).symm.contMDiff
        (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (p 0))) =
      torusTimeForm p 0 := by
  have h : Prod.fst ∘ ⇑(Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).symm =
      fun x : ∀ i, AddCircle (p i) ↦ x 0 :=
    funext fun _ ↦ by simp
  simp only [torusTimeForm_def, SmoothForm.mpullback_mpullback, h]

/-- **The association map, the remaining circles.** The association map `x ↦ (x 0, Fin.tail x)`
from `T^(m + 1)` to `AddCircle (p 0) × T^m` pulls the coordinate time form `dt_i` of `T^m`, read
on the product along the second projection, back to the coordinate time form of the factor
`Fin.succ i`. -/
@[simp]
theorem mpullback_piCons_symm_mpullback_snd_torusTimeForm (p : Fin (m + 1) → ℝ)
    [∀ i, Fact (0 < p i)] (i : Fin m) :
    SmoothForm.mpullback (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).symm
        (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).symm.contMDiff
        (SmoothForm.mpullback Prod.snd contMDiff_snd
          (torusTimeForm (fun i : Fin m ↦ p i.succ) i)) =
      torusTimeForm p i.succ := by
  have h : (fun x : ∀ i : Fin m, AddCircle (p i.succ) ↦ x i) ∘ Prod.snd ∘
      ⇑(Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).symm =
      fun x : ∀ i, AddCircle (p i) ↦ x i.succ :=
    funext fun _ ↦ by simp [Fin.tail]
  simp only [torusTimeForm_def, SmoothForm.mpullback_mpullback, Function.comp_assoc, h]

/-- **Concatenating tori, volume form.** The concatenation `(x, y) ↦ Fin.addCases x y` from
`T^m × T^k` to `T^(m + k)` pulls the volume form of `T^(m + k)` back to the wedge product
`pr₁^* vol_m ∧ pr₂^* vol_k` of the pullbacks of the volume forms of the two factors. -/
@[simp]
theorem mpullback_piAddCases_torusVolumeForm (p : Fin (m + k) → ℝ) [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusVolumeForm p) =
      SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst
          (torusVolumeForm fun i : Fin m ↦ p (Fin.castAdd k i)))
        (SmoothForm.mpullback Prod.snd contMDiff_snd
          (torusVolumeForm fun j : Fin k ↦ p (Fin.natAdd m j))) := by
  classical
  -- The product of the coordinate bases of `(Fin m → ℝ) × (Fin k → ℝ)`, the first block first.
  let b := ((Pi.basisFun ℝ (Fin m)).prod (Pi.basisFun ℝ (Fin k))).reindex finSumFinEquiv
  refine Subtype.ext (funext fun q ↦ ?_)
  -- The differential of the concatenation sends `b` to the coordinate basis of `Fin (m + k) → ℝ`,
  -- so the left side takes the value `1` on `b`.
  have hd : (fun i ↦ mfderiv _ _ (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ))
      (fun i ↦ AddCircle (p i)) ∞) q (b i)) = Pi.basisFun ℝ (Fin (m + k)) := funext fun i ↦
    (Diffeomorph.mfderiv_piAddCases_apply (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞ q
      (b i).1 (b i).2).trans (Module.Basis.addCases_basisFun_prod_reindex_finSumFinEquiv i)
  have hL : (SmoothForm.mpullback _ (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ))
      (fun i ↦ AddCircle (p i)) ∞).contMDiff (torusVolumeForm p)).val q b = 1 :=
    (SmoothForm.mpullback_apply _ _ _ q b).trans (by rw [hd, torusVolumeForm_apply_basisFun])
  -- On the right, the wedge of the pullbacks evaluates on the block frame `b` to the product of the
  -- two volume forms on the coordinate bases.
  have hR : (SmoothForm.wedge
      (SmoothForm.mpullback Prod.fst contMDiff_fst
        (torusVolumeForm fun i : Fin m ↦ p (Fin.castAdd k i)))
      (SmoothForm.mpullback Prod.snd contMDiff_snd
        (torusVolumeForm fun j : Fin k ↦ p (Fin.natAdd m j)))).val q
      (Fin.append (fun i ↦ (Pi.basisFun ℝ (Fin m) i, 0))
        fun j ↦ (0, Pi.basisFun ℝ (Fin k) j)) = 1 :=
    (SmoothForm.wedge_mpullback_fst_snd_apply_append _ _ q (Pi.basisFun ℝ (Fin m))
      (Pi.basisFun ℝ (Fin k))).trans
      (by rw [torusVolumeForm_apply_basisFun, torusVolumeForm_apply_basisFun, one_mul])
  -- Both sides are top-degree forms on the tangent space `(Fin m → ℝ) × (Fin k → ℝ)` that agree on
  -- the basis `b`, so they are equal.
  refine sub_eq_zero.1 ((ContinuousAlternatingMap.map_basis_eq_zero_iff _ b).1 ?_)
  exact (ContinuousAlternatingMap.sub_apply _ _ _).trans
    ((congrArg₂ (· - ·) hL
      (Module.Basis.coe_prod_reindex_finSumFinEquiv (Pi.basisFun ℝ (Fin m))
        (Pi.basisFun ℝ (Fin k)) ▸ hR)).trans (sub_self 1))

/-- **The one-factor torus, time form.** For an index type with a single element, evaluation at
it, from the torus to its circle, pulls the time form of the circle back to the coordinate time
form. -/
@[simp]
theorem mpullback_piUnique_timeForm {ι : Type*} [Fintype ι] [Unique ι] (p : ι → ℝ)
    [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (AddCircle.timeForm (p default)) =
      torusTimeForm p default := by
  have h : ⇑(Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞) =
      fun x ↦ x default :=
    funext fun x ↦ Diffeomorph.piUnique_apply _ _ _ x
  simp only [torusTimeForm_def, h]

/-- **The one-factor torus is its circle.** For a single factor the volume form is the coordinate
time form. -/
theorem torusVolumeForm_fin_one (p : Fin 1 → ℝ) [∀ i, Fact (0 < p i)] :
    torusVolumeForm p = torusTimeForm p 0 := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [torusVolumeForm_apply, torusTimeForm_apply, Matrix.det_unique, Matrix.of_apply,
    Fin.default_eq_zero]

/-- **Appending a circle, volume form.** The map `(x, t) ↦ Fin.snoc x t` from
`T^m × AddCircle (p m)` to `T^(m + 1)` pulls the volume form of `T^(m + 1)` back to the wedge
product `pr₁^* vol_m ∧ pr₂^* dt` of the pullbacks of the volume form of `T^m` and of the time form
of the appended circle. -/
@[simp]
theorem mpullback_piSnoc_torusVolumeForm (p : Fin (m + 1) → ℝ) [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusVolumeForm p) =
      SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (torusVolumeForm fun i : Fin m ↦ p i.castSucc))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm (p (Fin.last m)))) := by
  -- Appending a circle is concatenating with the one-factor torus:
  -- `Fin.snoc x t = Fin.addCases x (fun _ : Fin 1 ↦ t)`.
  have h : ⇑(Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞) ∘ id =
      ⇑(Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞) ∘
        Prod.map id (Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ))
          (fun j : Fin 1 ↦ AddCircle (p (Fin.natAdd m j))) ∞).symm :=
    funext fun x ↦ funext fun i ↦ by
      induction i using Fin.lastCases with
      | last =>
        simp only [Function.comp_apply, id_eq, Prod.map_fst, Prod.map_snd,
          Diffeomorph.piSnoc_apply, Diffeomorph.piAddCases_apply,
          Diffeomorph.piUnique_symm_apply, Fin.snoc_last]
        exact ((Fin.addCases_right (motive := fun i ↦ AddCircle (p i)) (0 : Fin 1)).trans
          (uniqueElim_default (α := fun j : Fin 1 ↦ AddCircle (p (Fin.natAdd m j))) x.2)).symm
      | cast i =>
        simp only [Function.comp_apply, id_eq, Prod.map_fst, Prod.map_snd,
          Diffeomorph.piSnoc_apply, Diffeomorph.piAddCases_apply, Fin.snoc_castSucc]
        exact (Fin.addCases_left (motive := fun i ↦ AddCircle (p i)) i).symm
  have h₁ : (fun x : ∀ j : Fin 1, AddCircle (p (Fin.natAdd m j)) ↦ x 0) ∘
      ⇑(Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ))
        (fun j : Fin 1 ↦ AddCircle (p (Fin.natAdd m j))) ∞).symm = id :=
    funext fun t ↦ by
      simp only [Function.comp_apply, Diffeomorph.piUnique_symm_apply, id_eq]
      exact uniqueElim_default (α := fun j : Fin 1 ↦ AddCircle (p (Fin.natAdd m j))) t
  have key := SmoothForm.mpullback_mpullback_of_comp_eq contMDiff_id
    (Diffeomorph.piSnoc (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
    (contMDiff_id.prodMap (Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ))
      (fun j : Fin 1 ↦ AddCircle (p (Fin.natAdd m j))) ∞).symm.contMDiff)
    (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff h
    (torusVolumeForm p)
  rw [SmoothForm.mpullback_id, LinearMap.id_apply] at key
  rw [key, mpullback_piAddCases_torusVolumeForm]
  refine (SmoothForm.mpullback_prodMap_wedge_mpullback_fst_snd contMDiff_id
    (Diffeomorph.piUnique (fun _ ↦ 𝓘(ℝ))
      (fun j : Fin 1 ↦ AddCircle (p (Fin.natAdd m j))) ∞).symm.contMDiff _ _).trans ?_
  rw [torusVolumeForm_fin_one]
  simp only [SmoothForm.mpullback_id, LinearMap.id_apply, torusTimeForm_def,
    SmoothForm.mpullback_mpullback, h₁]
  -- The periods agree definitionally: `Fin.castAdd 1 i` is `i.castSucc`, and `Fin.natAdd m 0` is
  -- `Fin.last m`.
  rfl

/-- **Splitting off the first circle, volume form.** The map `(t, x) ↦ Fin.cons t x` from
`AddCircle (p 0) × T^m` to `T^(m + 1)` pulls the volume form of `T^(m + 1)` back to the wedge
product `pr₁^* dt ∧ pr₂^* vol_m` of the pullbacks of the time form of the first circle and of the
volume form of `T^m`, transported from degree `1 + m` to degree `m + 1`. -/
theorem mpullback_piCons_torusVolumeForm (p : Fin (m + 1) → ℝ) [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusVolumeForm p) =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦
          SmoothForm (𝓘(ℝ).prod (ModelWithCorners.pi fun _ : Fin m ↦ 𝓘(ℝ)))
            (AddCircle (p 0) × ∀ i : Fin m, AddCircle (p i.succ)) ℝ q) (add_comm 1 m)
        (SmoothForm.wedge
          (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (p 0)))
          (SmoothForm.mpullback Prod.snd contMDiff_snd
            (torusVolumeForm fun i : Fin m ↦ p i.succ))) := by
  -- The product of the unit basis of `ℝ` and the coordinate basis of `Fin m → ℝ`, the circle
  -- first, indexed by `Fin (m + 1)`.
  let b := ((Module.Basis.singleton (Fin 1) ℝ).prod (Pi.basisFun ℝ (Fin m))).reindex
    (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
  have hb : ⇑b = fun r ↦
      Fin.append (fun i ↦ (Module.Basis.singleton (Fin 1) ℝ i, (0 : Fin m → ℝ)))
        (fun j ↦ ((0 : ℝ), Pi.basisFun ℝ (Fin m) j)) (Fin.cast (add_comm 1 m).symm r) :=
    Module.Basis.coe_prod_reindex_finSumFinEquiv_trans_finCongr _ _ _
  refine Subtype.ext (funext fun q ↦ ?_)
  -- The differential of `Fin.cons` sends `b` to the coordinate basis of `Fin (m + 1) → ℝ`, so the
  -- left side takes the value `1` on `b`.
  have hd : (fun i ↦ mfderiv _ _ (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ))
      (fun i ↦ AddCircle (p i)) ∞) q (b i)) = Pi.basisFun ℝ (Fin (m + 1)) := funext fun i ↦
    (Diffeomorph.mfderiv_piCons_apply (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞ q
      (b i).1 (b i).2).trans
      (Module.Basis.cons_singleton_prod_basisFun_reindex_finSumFinEquiv_trans_finCongr i)
  have hL : (SmoothForm.mpullback _ (Diffeomorph.piCons (fun _ ↦ 𝓘(ℝ))
      (fun i ↦ AddCircle (p i)) ∞).contMDiff (torusVolumeForm p)).val q b = 1 :=
    (SmoothForm.mpullback_apply _ _ _ q b).trans (by rw [hd, torusVolumeForm_apply_basisFun])
  -- On the right, the transported wedge of the pullbacks evaluates on `b` to the product of the
  -- time form on the unit vector and the volume form on the coordinate basis.
  have hR : (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦
      SmoothForm (𝓘(ℝ).prod (ModelWithCorners.pi fun _ : Fin m ↦ 𝓘(ℝ)))
        (AddCircle (p 0) × ∀ i : Fin m, AddCircle (p i.succ)) ℝ q) (add_comm 1 m)
      (SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm (p 0)))
        (SmoothForm.mpullback Prod.snd contMDiff_snd
          (torusVolumeForm fun i : Fin m ↦ p i.succ)))).val q b = 1 := by
    refine (SmoothForm.cast_apply _ _ q b).trans ?_
    have hbc : (⇑b ∘ Fin.cast (add_comm 1 m) : Fin (1 + m) →
        TangentSpace (𝓘(ℝ).prod (ModelWithCorners.pi fun _ : Fin m ↦ 𝓘(ℝ))) q) =
        Fin.append (fun i ↦ (Module.Basis.singleton (Fin 1) ℝ i, (0 : Fin m → ℝ)))
          (fun j ↦ ((0 : ℝ), Pi.basisFun ℝ (Fin m) j)) :=
      funext fun r ↦ (congrFun hb _).trans (by simp)
    rw [hbc]
    refine (SmoothForm.wedge_mpullback_fst_snd_apply_append _ _ q _
      (Pi.basisFun ℝ (Fin m))).trans ?_
    simp only [Module.Basis.coe_singleton, torusVolumeForm_apply_basisFun, mul_one]
    exact AddCircle.timeForm_apply (p 0) q.1 _
  -- Both sides are top-degree forms on the tangent space `ℝ × (Fin m → ℝ)` that agree on the
  -- basis `b`, so they are equal.
  refine sub_eq_zero.1 ((ContinuousAlternatingMap.map_basis_eq_zero_iff _ b).1 ?_)
  exact (ContinuousAlternatingMap.sub_apply _ _ _).trans
    ((congrArg₂ (· - ·) hL hR).trans (sub_self 1))

/-- **The empty torus is a point.** For no factors the volume form is the constant function `1`,
the positive orientation form of a point. -/
theorem torusVolumeForm_fin_zero_apply (p : Fin 0 → ℝ) [∀ i, Fact (0 < p i)]
    (x : ∀ i, AddCircle (p i))
    (v : Fin 0 → TangentSpace (ModelWithCorners.pi fun _ : Fin 0 ↦ 𝓘(ℝ)) x) :
    (torusVolumeForm p).val x v = 1 := by
  rw [torusVolumeForm_apply, Matrix.det_isEmpty]

/-- **Deleting a point factor.** For `k = 0` the concatenation `(x, y) ↦ Fin.addCases x y` from
`T^m × T^0` to `T^m` pulls the volume form back to the pullback of the volume form of `T^m` along
the first projection: the point factor `T^0` does not contribute. -/
theorem mpullback_piAddCases_torusVolumeForm_zero (p : Fin (m + 0) → ℝ)
    [∀ i, Fact (0 < p i)] :
    SmoothForm.mpullback (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞)
        (Diffeomorph.piAddCases (fun _ ↦ 𝓘(ℝ)) (fun i ↦ AddCircle (p i)) ∞).contMDiff
        (torusVolumeForm p) =
      SmoothForm.mpullback Prod.fst contMDiff_fst
        (torusVolumeForm fun i : Fin m ↦ p (Fin.castAdd 0 i)) := by
  rw [mpullback_piAddCases_torusVolumeForm]
  refine Subtype.ext (funext fun q ↦ ?_)
  rw [SmoothForm.wedge_zero_right_apply_eq_smul, SmoothForm.mpullback_apply,
    torusVolumeForm_fin_zero_apply, one_smul]

end Product

end TauCeti
