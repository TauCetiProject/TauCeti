/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Decomposition
import Mathlib.Tactic.Module
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# The Böhm–Wilking deformation of algebraic curvature tensors

Let `V` be a finite-dimensional real inner product space of dimension `n`. Böhm and Wilking deform
curvature tensors by rescaling the scalar and trace-free Ricci summands of the orthogonal splitting
`r = weyl r + tracelessRicciPart r + scalarPart r`. For real parameters `a, b` their linear map is

`ℓ_(a,b)(r) = r + 2 (n - 1) a r_I + (n - 2) b r_Ric₀`,

where `r_I = scalarPart r` is `(Scal / (n (n - 1))) I`, with `I` the identity curvature
operator, and `r_Ric₀ = tracelessRicciPart r` is `(2 / (n - 2)) Ric₀ ∧ id` on bivectors. This is
`TauCeti.FourTensor.boehmWilkingDeformation a b`. It fixes the Weyl part, multiplies the
trace-free Ricci part by `1 + (n - 2) b` and the scalar part by `1 + 2 (n - 1) a`. Consequently
these deformations commute and compose by multiplying their eigenfactors, `ℓ_(0,0)` is the
identity, and `ℓ_(a,b)` is invertible, with inverse again of the form `ℓ_(a',b')`, as soon as both
eigenfactors are nonzero. The deformation is equivariant under linear isometries and preserves the
algebraic curvature tensors.

Böhm and Wilking transport a cone `C` of curvature tensors invariant under the reaction ODE
`R' = Q(R)` to the cone `ℓ_(a,b)(C)` and study the discrepancy `ℓ_(a,b)⁻¹ Q(ℓ_(a,b) R) - Q(R)`;
the invertible deformation on all four-tensors, `TauCeti.FourTensor.boehmWilkingDeformationEquiv`,
and its restriction to the algebraic curvature tensors,
`TauCeti.FourTensor.algebraicCurvatureBoehmWilkingEquiv`, are the maps these constructions use.

## Main definitions

* `TauCeti.FourTensor.boehmWilkingDeformation a b`: the linear map `ℓ_(a,b)` on `FourTensor V`.
* `TauCeti.FourTensor.boehmWilkingDeformationEquiv`: `ℓ_(a,b)` as a continuous linear
  automorphism of `FourTensor V` when `1 + 2 (n - 1) a ≠ 0` and `1 + (n - 2) b ≠ 0`.
* `TauCeti.FourTensor.algebraicCurvatureBoehmWilkingEquiv`: its restriction to
  `algebraicCurvatureSubmodule V`.

## Main results

* `TauCeti.FourTensor.boehmWilkingDeformation_eq_weyl_add`: the eigen-decomposition
  `ℓ_(a,b) r = weyl r + (1 + (n - 2) b) • tracelessRicciPart r + (1 + 2 (n - 1) a) • scalarPart r`.
* `TauCeti.FourTensor.scalar_boehmWilkingDeformation`,
  `TauCeti.FourTensor.tracelessRicci_boehmWilkingDeformation` and
  `TauCeti.FourTensor.ricci_boehmWilkingDeformation`: the contractions of `ℓ_(a,b) r`.
* `TauCeti.FourTensor.boehmWilkingDeformation_apply_eq_add_kulkarniNomizu`: away from dimension
  two, `ℓ_(a,b) r = r + (b Ric₀ + (a Scal / n) g) ⊙ g`.
* `TauCeti.FourTensor.boehmWilkingDeformation_comp`: the composition law.
* `TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDeformation`: the bivector operator of
  `ℓ_(a,b) r` is `R + 2 (n - 1) a (Scal / (n (n - 1))) I + (n - 2) b (2 / (n - 2)) Ric₀ ∧ id`.
* `LinearIsometryEquiv.boehmWilkingDeformation_compContinuousLinearMap`: `O(n)`-equivariance.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
-/

public section

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The deformation map -/

/-- The **Böhm–Wilking deformation** `ℓ_(a,b)(r) = r + 2 (n - 1) a r_I + (n - 2) b r_Ric₀` of
four-tensors on an `n`-dimensional real inner product space, where `r_I = scalarPart r` and
`r_Ric₀ = tracelessRicciPart r`. It fixes the Weyl part and rescales the scalar and trace-free
Ricci parts by `1 + 2 (n - 1) a` and `1 + (n - 2) b`. -/
def boehmWilkingDeformation (a b : ℝ) : FourTensor V →ₗ[ℝ] FourTensor V :=
  LinearMap.id + (2 * ((Module.finrank ℝ V : ℝ) - 1) * a) • scalarPart +
    (((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicciPart

/-- Definition of `boehmWilkingDeformation a b r`. -/
theorem boehmWilkingDeformation_apply (a b : ℝ) (r : FourTensor V) :
    boehmWilkingDeformation a b r =
      r + (2 * ((Module.finrank ℝ V : ℝ) - 1) * a) • scalarPart r +
        (((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicciPart r := (rfl)

/-- **Eigen-decomposition** of the Böhm–Wilking deformation: `ℓ_(a,b)` fixes the Weyl part and
multiplies the trace-free Ricci and scalar parts by `1 + (n - 2) b` and `1 + 2 (n - 1) a`. -/
theorem boehmWilkingDeformation_eq_weyl_add (a b : ℝ) (r : FourTensor V) :
    boehmWilkingDeformation a b r =
      weyl r + (1 + ((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicciPart r +
        (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) • scalarPart r := by
  rw [boehmWilkingDeformation_apply, weyl_apply]
  module

/-- `ℓ_(a,b)` fixes the Weyl part. -/
@[simp] theorem weyl_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    weyl (boehmWilkingDeformation a b r) = weyl r := by
  simp [boehmWilkingDeformation_apply]

/-- `ℓ_(a,b)` multiplies the scalar part by `1 + 2 (n - 1) a`. -/
@[simp] theorem scalarPart_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    scalarPart (boehmWilkingDeformation a b r) =
      (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) • scalarPart r := by
  simp [boehmWilkingDeformation_apply, add_smul]

/-- `ℓ_(a,b)` multiplies the trace-free Ricci part by `1 + (n - 2) b`. -/
@[simp] theorem tracelessRicciPart_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    tracelessRicciPart (boehmWilkingDeformation a b r) =
      (1 + ((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicciPart r := by
  simp [boehmWilkingDeformation_apply, add_smul]

/-- `ℓ_(a,b)` multiplies the scalar contraction by `1 + 2 (n - 1) a`, in every dimension. -/
@[simp] theorem scalar_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    scalar (boehmWilkingDeformation a b r) =
      (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) * scalar r := by
  by_cases h1 : Module.finrank ℝ V = 1
  · simp [boehmWilkingDeformation_apply, h1]
  · simp [boehmWilkingDeformation_apply, scalar_scalarPart h1]
    ring

/-- `ℓ_(a,b)` multiplies the trace-free Ricci contraction by `1 + (n - 2) b`, in every
dimension. -/
@[simp] theorem tracelessRicci_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    tracelessRicci (boehmWilkingDeformation a b r) =
      (1 + ((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicci r := by
  by_cases h2 : Module.finrank ℝ V = 2
  · simp [boehmWilkingDeformation_apply, h2]
  · simp [boehmWilkingDeformation_apply, tracelessRicci_tracelessRicciPart h2, add_smul]

/-- The Ricci contraction of `ℓ_(a,b) r` is
`(1 + (n - 2) b) Ric₀ + (1 + 2 (n - 1) a) (Scal / n) g`, in every dimension. -/
theorem ricci_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    ricci (boehmWilkingDeformation a b r) =
      (1 + ((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicci r +
        ((1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) * scalar r / Module.finrank ℝ V) •
          innerₗ V := by
  rw [← tracelessRicci_boehmWilkingDeformation a b r, ← scalar_boehmWilkingDeformation a b r,
    tracelessRicci_apply]
  abel

/-- Away from dimension two, the Böhm–Wilking deformation adds a Kulkarni–Nomizu product with
the inner product: `ℓ_(a,b)(r) = r + (b Ric₀ + (a Scal / n) g) ⊙ g`. -/
theorem boehmWilkingDeformation_apply_eq_add_kulkarniNomizu (hn : Module.finrank ℝ V ≠ 2)
    (a b : ℝ) (r : FourTensor V) :
    boehmWilkingDeformation a b r = r + kulkarniNomizu (b • tracelessRicci r +
      (a * scalar r / Module.finrank ℝ V) • innerₗ V) (innerₗ V) := by
  have hcc : constantCurvature V = (1 / 2 : ℝ) • kulkarniNomizu (innerₗ V) (innerₗ V) :=
    ext_vec fun u v z w ↦ by simp only [constantCurvature_apply, smul_apply, kulkarniNomizu_apply,
      innerₗ_apply_apply, smul_eq_mul]; ring
  rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
  · -- In dimension at most one, both `Ric₀` and the constant-curvature tensor vanish.
    have h1 : Module.finrank ℝ V ≤ 1 := by omega
    have hgg : kulkarniNomizu (innerₗ V) (innerₗ V) = 0 := by
      have h0 := isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one h1
      rw [hcc] at h0
      exact (smul_eq_zero.mp h0).resolve_left (by norm_num)
    simp [boehmWilkingDeformation_apply, scalarPart_apply, tracelessRicciPart_apply, hcc, hgg,
      tracelessRicci_eq_zero_of_finrank_le_one r h1]
  have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by norm_cast; omega)
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  have e1 : 2 * ((Module.finrank ℝ V : ℝ) - 1) * a *
      (scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) * (1 / 2) =
      a * scalar r / Module.finrank ℝ V := by
    field_simp
  have e2 : ((Module.finrank ℝ V : ℝ) - 2) * b * ((Module.finrank ℝ V : ℝ) - 2)⁻¹ = b := by
    field_simp
  rw [boehmWilkingDeformation_apply, scalarPart_apply, tracelessRicciPart_apply, hcc,
    map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_smul, smul_smul, smul_smul, e1, e2]
  rw [add_assoc, add_comm (_ • kulkarniNomizu (innerₗ V) (innerₗ V))]

/-- `ℓ_(a,b)` fixes every four-tensor with vanishing Ricci contraction, in particular every Weyl
curvature tensor. -/
theorem boehmWilkingDeformation_apply_of_ricci_eq_zero (a b : ℝ) {r : FourTensor V}
    (hr : ricci r = 0) : boehmWilkingDeformation a b r = r := by
  have hs : scalar r = 0 := by rw [scalar_apply, hr, map_zero]
  have ht : tracelessRicci r = 0 := by rw [tracelessRicci_apply, hr, hs]; ext; simp
  simp [boehmWilkingDeformation_apply, scalarPart_apply, tracelessRicciPart_apply, hs, ht]

/-- `ℓ_(a,b)` multiplies the constant-curvature tensor by `1 + 2 (n - 1) a`. -/
@[simp] theorem boehmWilkingDeformation_constantCurvature (a b : ℝ) :
    boehmWilkingDeformation a b (constantCurvature V) =
      (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) • constantCurvature V := by
  by_cases h1 : Module.finrank ℝ V ≤ 1
  · simp [isAlgebraicCurvature_constantCurvature.eq_zero_of_finrank_le_one h1]
  have hn : (Module.finrank ℝ V : ℝ) * ((Module.finrank ℝ V : ℝ) - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (sub_ne_zero.mpr (by norm_cast; omega))
  have hs : scalarPart (constantCurvature V) = constantCurvature V := by
    rw [scalarPart_apply, scalar_constantCurvature, div_self hn, one_smul]
  have ht : tracelessRicciPart (constantCurvature V) = 0 := by
    rw [← hs, tracelessRicciPart_scalarPart]
  rw [boehmWilkingDeformation_apply, hs, ht, smul_zero, add_zero, add_smul, one_smul]

/-- The bivector operator of `ℓ_(a,b) r` is `R + 2 (n - 1) a R_I + (n - 2) b R_Ric₀`, with
`R_I = (Scal / (n (n - 1))) • (id ∧ id)` and `R_Ric₀ = (2 / (n - 2)) • (Ric₀♯ ∧ id)`. -/
theorem curvatureEndomorphism_boehmWilkingDeformation (a b : ℝ) (r : FourTensor V) :
    curvatureEndomorphism (boehmWilkingDeformation a b r) =
      curvatureEndomorphism r +
        (2 * ((Module.finrank ℝ V : ℝ) - 1) * a) •
          ((scalar r / (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1))) •
            exteriorPower.symmMap₂ LinearMap.id LinearMap.id) +
        (((Module.finrank ℝ V : ℝ) - 2) * b) •
          ((2 / ((Module.finrank ℝ V : ℝ) - 2)) •
            exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) LinearMap.id) := by
  rw [boehmWilkingDeformation_apply, map_add, map_add, map_smul, map_smul,
    curvatureEndomorphism_scalarPart, curvatureEndomorphism_tracelessRicciPart]

/-! ### Composition and invertibility -/

/-- `ℓ_(0,0)` is the identity. -/
@[simp] theorem boehmWilkingDeformation_zero_zero :
    boehmWilkingDeformation (V := V) 0 0 = LinearMap.id := by
  ext1 r
  simp [boehmWilkingDeformation_apply]

/-- **Composition law**: `ℓ_(a,b) ∘ ℓ_(a',b') = ℓ_(a'',b'')`, where the eigenfactors multiply,
`1 + 2 (n - 1) a'' = (1 + 2 (n - 1) a) (1 + 2 (n - 1) a')` and
`1 + (n - 2) b'' = (1 + (n - 2) b) (1 + (n - 2) b')`. -/
theorem boehmWilkingDeformation_comp (a b a' b' : ℝ) :
    boehmWilkingDeformation (V := V) a b ∘ₗ boehmWilkingDeformation a' b' =
      boehmWilkingDeformation (a + a' + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a * a')
        (b + b' + ((Module.finrank ℝ V : ℝ) - 2) * b * b') := by
  ext1 r
  rw [LinearMap.comp_apply, boehmWilkingDeformation_eq_weyl_add a b,
    weyl_boehmWilkingDeformation, tracelessRicciPart_boehmWilkingDeformation,
    scalarPart_boehmWilkingDeformation, boehmWilkingDeformation_eq_weyl_add]
  module

/-- Two Böhm–Wilking deformations commute. -/
theorem boehmWilkingDeformation_comp_comm (a b a' b' : ℝ) :
    boehmWilkingDeformation (V := V) a b ∘ₗ boehmWilkingDeformation a' b' =
      boehmWilkingDeformation a' b' ∘ₗ boehmWilkingDeformation a b := by
  rw [boehmWilkingDeformation_comp, boehmWilkingDeformation_comp]
  congr 1 <;> ring

/-- `ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))` is a right inverse of `ℓ_(a,b)` when both
eigenfactors are nonzero. -/
theorem boehmWilkingDeformation_comp_inv {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    boehmWilkingDeformation (V := V) a b ∘ₗ
        boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
          (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b)) =
      LinearMap.id := by
  rw [boehmWilkingDeformation_comp, ← boehmWilkingDeformation_zero_zero]
  congr 1
  · linear_combination (-a) * mul_inv_cancel₀ ha
  · linear_combination (-b) * mul_inv_cancel₀ hb

/-- `ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))` is a left inverse of `ℓ_(a,b)` when both
eigenfactors are nonzero. -/
theorem boehmWilkingDeformation_inv_comp {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    boehmWilkingDeformation (V := V)
        (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
        (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b)) ∘ₗ
      boehmWilkingDeformation a b = LinearMap.id := by
  rw [boehmWilkingDeformation_comp_comm, boehmWilkingDeformation_comp_inv ha hb]

/-- The Böhm–Wilking deformation `ℓ_(a,b)` as a continuous linear automorphism of `FourTensor V`,
for parameters whose eigenfactors `1 + 2 (n - 1) a` and `1 + (n - 2) b` are nonzero. Its inverse
is `ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))`. -/
def boehmWilkingDeformationEquiv {a b : ℝ} (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) : FourTensor V ≃L[ℝ] FourTensor V :=
  (LinearEquiv.ofLinearMap (boehmWilkingDeformation a b)
    (boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
      (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b)))
    (boehmWilkingDeformation_comp_inv ha hb)
    (boehmWilkingDeformation_inv_comp ha hb)).toContinuousLinearEquiv

/-- `boehmWilkingDeformationEquiv` applies `ℓ_(a,b)`. -/
@[simp] theorem boehmWilkingDeformationEquiv_apply {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) (r : FourTensor V) :
    boehmWilkingDeformationEquiv ha hb r = boehmWilkingDeformation a b r := (rfl)

/-- The inverse of `boehmWilkingDeformationEquiv` applies
`ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))`. -/
@[simp] theorem boehmWilkingDeformationEquiv_symm_apply {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) (r : FourTensor V) :
    (boehmWilkingDeformationEquiv ha hb).symm r =
      boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
        (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b)) r := (rfl)

/-! ### Algebraic curvature tensors -/

/-- `ℓ_(a,b)` maps algebraic curvature tensors to algebraic curvature tensors. -/
theorem IsAlgebraicCurvature.boehmWilkingDeformation {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (a b : ℝ) :
    IsAlgebraicCurvature (FourTensor.boehmWilkingDeformation a b r) :=
  mem_algebraicCurvatureSubmodule.mp <| (algebraicCurvatureSubmodule V).add_mem
    ((algebraicCurvatureSubmodule V).add_mem (mem_algebraicCurvatureSubmodule.mpr hr)
      (Submodule.smul_mem _ _
        (mem_algebraicCurvatureSubmodule.mpr (isAlgebraicCurvature_scalarPart r))))
    (Submodule.smul_mem _ _ (mem_algebraicCurvatureSubmodule.mpr hr.tracelessRicciPart))

/-- The Böhm–Wilking deformation `ℓ_(a,b)` restricted to a continuous linear automorphism of
`algebraicCurvatureSubmodule V`, for nonzero eigenfactors `1 + 2 (n - 1) a` and `1 + (n - 2) b`. -/
def algebraicCurvatureBoehmWilkingEquiv {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    algebraicCurvatureSubmodule V ≃L[ℝ] algebraicCurvatureSubmodule V :=
  ContinuousLinearEquiv.ofSubmodules (boehmWilkingDeformationEquiv ha hb) _ _ <| le_antisymm
    (Submodule.map_le_iff_le_comap.mpr fun r hr ↦ mem_algebraicCurvatureSubmodule.mpr <|
      (mem_algebraicCurvatureSubmodule.mp hr).boehmWilkingDeformation a b)
    fun r hr ↦ ⟨(boehmWilkingDeformationEquiv ha hb).symm r, by
      rw [SetLike.mem_coe, boehmWilkingDeformationEquiv_symm_apply]
      exact mem_algebraicCurvatureSubmodule.mpr <|
        (mem_algebraicCurvatureSubmodule.mp hr).boehmWilkingDeformation _ _,
      (boehmWilkingDeformationEquiv ha hb).apply_symm_apply r⟩

/-- `algebraicCurvatureBoehmWilkingEquiv` applies `ℓ_(a,b)`. -/
@[simp] theorem coe_algebraicCurvatureBoehmWilkingEquiv_apply {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) (r : algebraicCurvatureSubmodule V) :
    (algebraicCurvatureBoehmWilkingEquiv ha hb r : FourTensor V) =
      boehmWilkingDeformation a b r := by
  simp [algebraicCurvatureBoehmWilkingEquiv]

/-- The inverse of `algebraicCurvatureBoehmWilkingEquiv` applies
`ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))`. -/
@[simp] theorem coe_algebraicCurvatureBoehmWilkingEquiv_symm_apply {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) (r : algebraicCurvatureSubmodule V) :
    ((algebraicCurvatureBoehmWilkingEquiv ha hb).symm r : FourTensor V) =
      boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
        (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b)) r := by
  simp [algebraicCurvatureBoehmWilkingEquiv]

end TauCeti.FourTensor

namespace LinearIsometryEquiv

open TauCeti TauCeti.FourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The Böhm–Wilking deformation is equivariant under linear isometric equivalences; in
particular it commutes with the action of the orthogonal group `O(n)`. -/
theorem boehmWilkingDeformation_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (a b : ℝ)
    (r : FourTensor V) :
    boehmWilkingDeformation a b
        (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) =
      (boehmWilkingDeformation a b r).compContinuousLinearMap fun _ ↦
        e.toLinearIsometry.toContinuousLinearMap := by
  ext m
  simp [boehmWilkingDeformation_apply, e.scalarPart_compContinuousLinearMap,
    e.tracelessRicciPart_compContinuousLinearMap, e.toLinearEquiv.finrank_eq]

end LinearIsometryEquiv
