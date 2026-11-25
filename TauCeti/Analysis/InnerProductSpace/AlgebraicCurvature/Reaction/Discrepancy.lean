/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Deformation
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction.Basic

/-!
# The Böhm–Wilking discrepancy

Let `V` be a finite-dimensional real inner product space of dimension `n` with inner product `g`,
let `Q = reactionTensor` be the reaction term of the curvature evolution `R' = Q(R)` under Ricci
flow, and `B = reactionBilinear V` its polarization. Böhm and Wilking deform an algebraic
curvature tensor by `ℓ_(a,b)(r) = r + k ⊙ g`, adding a Kulkarni–Nomizu product with the inner
product (`TauCeti.FourTensor.boehmWilkingDeformation_apply_eq_add_kulkarniNomizu`, with
`k = b Ric₀ + (a Scal / n) g`). From the reaction on such products
(`TauCeti.FourTensor.reactionBilinear_kulkarniNomizu_innerₗ_right`,
`TauCeti.FourTensor.reactionTensor_kulkarniNomizu_innerₗ`) this file derives their formula for
the discrepancy between `Q` and its conjugate by `ℓ_(a,b)`, the identity that transports
`Q`-invariant cones `C` to `Q`-invariant cones `ℓ_(a,b)(C)`.

For `X = Q / 2`, the discrepancy is `D_(a,b)(r) = ℓ_(a,b)⁻¹ X(ℓ_(a,b) r) - X(r)`
(`TauCeti.FourTensor.boehmWilkingDiscrepancy`), so that `ℓ_(a,b)⁻¹ Q(ℓ_(a,b) r) = Q(r) + 2 D`.
For `n ≥ 3`, nonzero eigenfactors and algebraic `r`,
`D_(a,b)(r) = ((n - 2) b² - 2 (a - b)) Ric₀ ∧ Ric₀ + 2 a Ric ∧ Ric + 2 b² Ric₀² ∧ id + κ I`
with `κ = tr(Ric₀♯ Ric₀♯) / (n (1 + 2 (n - 1) a)) · (n b² (1 - 2 b) - 2 (a - b) (1 - 2 b + n b²))`
and `I` the constant-curvature tensor. It is stated for four-tensors, with `A ∧ B` written as
`(A ⊙ B) / 2` (`TauCeti.FourTensor.boehmWilkingDiscrepancy_eq`), and for bivector operators
(`TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDiscrepancy`). The discrepancy depends
only on the Ricci tensor of `r`, not on its Weyl part.

## Main definitions

* `TauCeti.FourTensor.boehmWilkingDiscrepancy`: the discrepancy `D_(a,b)`.

## Main results

* `TauCeti.FourTensor.reactionTensor_boehmWilkingDeformation`,
  `TauCeti.FourTensor.boehmWilkingDeformationEquiv_symm_reactionTensor`,
  `TauCeti.FourTensor.boehmWilkingDiscrepancy_eq`, and
  `TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDiscrepancy`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, Section 2, Theorem 2.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The Böhm–Wilking discrepancy -/

/-- The reaction tensor of a Böhm–Wilking deformation `ℓ_(a,b)(r) = r + k ⊙ g`, where
`k = b Ric₀ + (a Scal / n) g`, of an algebraic curvature tensor `r` in dimension `n ≠ 2`:
`Q(ℓ_(a,b) r) = Q(r) + 2 (r(k) ⊙ g + k ⊙ Ric(r)) + Q(k ⊙ g)`. -/
theorem reactionTensor_boehmWilkingDeformation {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hn : Module.finrank ℝ V ≠ 2) (a b : ℝ) :
    reactionTensor (boehmWilkingDeformation a b r) = reactionTensor r +
      (2 : ℝ) • (kulkarniNomizu (curvatureAction r (b • tracelessRicci r +
          (a * scalar r / Module.finrank ℝ V) • innerₗ V)) (innerₗ V) +
        kulkarniNomizu (b • tracelessRicci r + (a * scalar r / Module.finrank ℝ V) • innerₗ V)
          (ricci r)) +
      reactionTensor (kulkarniNomizu (b • tracelessRicci r +
        (a * scalar r / Module.finrank ℝ V) • innerₗ V) (innerₗ V)) := by
  rw [boehmWilkingDeformation_apply_eq_add_kulkarniNomizu hn, reactionTensor_add,
    reactionBilinear_kulkarniNomizu_innerₗ_right hr ((hr.isSymm_tracelessRicci.smul b).add
      ((BilinForm.isSymm_iff.mpr isSymm_inner).smul _))]

variable (V) in
/-- The **Böhm–Wilking discrepancy** `D_(a,b)(r) = ℓ_(a,b)⁻¹ X(ℓ_(a,b) r) - X(r)` of the vector
field `X = Q / 2`, where `Q = reactionTensor` and `ℓ_(a,b) = boehmWilkingDeformation a b`. It
measures how far the deformation `ℓ_(a,b)` is from intertwining the reaction ODE `R' = Q(R)`
with itself: `ℓ_(a,b)⁻¹ Q(ℓ_(a,b) r) = Q(r) + 2 D_(a,b)(r)`
(`TauCeti.FourTensor.boehmWilkingDeformationEquiv_symm_reactionTensor`). The inverse is written
as `ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))`, which inverts `ℓ_(a,b)` whenever both
eigenfactors `1 + 2 (n - 1) a` and `1 + (n - 2) b` are nonzero. -/
def boehmWilkingDiscrepancy (a b : ℝ) (r : FourTensor V) : FourTensor V :=
  (1 / 2 : ℝ) • (boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
      (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b))
      (reactionTensor (boehmWilkingDeformation a b r)) - reactionTensor r)

/-- Definition of `boehmWilkingDiscrepancy V a b r`. -/
theorem boehmWilkingDiscrepancy_def (a b : ℝ) (r : FourTensor V) :
    boehmWilkingDiscrepancy V a b r =
      (1 / 2 : ℝ) • (boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
        (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b))
        (reactionTensor (boehmWilkingDeformation a b r)) - reactionTensor r) := (rfl)

/-- For nonzero eigenfactors, the inverse Böhm–Wilking deformation carries the reaction of the
deformed tensor to the reaction plus twice the discrepancy:
`ℓ_(a,b)⁻¹ Q(ℓ_(a,b) r) = Q(r) + 2 D_(a,b)(r)`. -/
theorem boehmWilkingDeformationEquiv_symm_reactionTensor {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) (r : FourTensor V) :
    (boehmWilkingDeformationEquiv ha hb).symm (reactionTensor (boehmWilkingDeformation a b r)) =
      reactionTensor r + (2 : ℝ) • boehmWilkingDiscrepancy V a b r := by
  rw [boehmWilkingDiscrepancy_def, smul_smul, boehmWilkingDeformationEquiv_symm_apply]
  norm_num

/-- **The Böhm–Wilking discrepancy formula** (Böhm–Wilking, Theorem 2). For an algebraic curvature
tensor `r` on an `n`-dimensional space, `n ≥ 3`, and nonzero eigenfactors
`1 + 2 (n - 1) a` and `1 + (n - 2) b`,
`D_(a,b)(r) = ((n - 2) b² - 2 (a - b)) / 2 · Ric₀ ⊙ Ric₀ + a · Ric ⊙ Ric + b² · Ric₀² ⊙ g + κ I`,
where `Ric₀² = ⟪Ric₀♯ Ric₀♯ ·, ·⟫`, `I` is the constant-curvature tensor and
`κ = tr(Ric₀♯ Ric₀♯) / (n (1 + 2 (n - 1) a)) · (n b² (1 - 2 b) - 2 (a - b) (1 - 2 b + n b²))`.
In particular `D_(a,b)(r)` depends only on the Ricci tensor of `r`, not on its Weyl part. Since
the bivector operator of `A ⊙ B` is `2 A♯ ∧ B♯`, this is the operator identity of
`TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDiscrepancy`. -/
theorem boehmWilkingDiscrepancy_eq {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hn : 2 < Module.finrank ℝ V) {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    boehmWilkingDiscrepancy V a b r =
      ((((Module.finrank ℝ V : ℝ) - 2) * b ^ 2 - 2 * (a - b)) / 2) •
          kulkarniNomizu (tracelessRicci r) (tracelessRicci r) +
        a • kulkarniNomizu (ricci r) (ricci r) +
        b ^ 2 • kulkarniNomizu ((innerₗ V).comp
          (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r)) (innerₗ V) +
        (LinearMap.trace ℝ V (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r) /
            (Module.finrank ℝ V * (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a)) *
          (Module.finrank ℝ V * b ^ 2 * (1 - 2 * b) -
            2 * (a - b) * (1 - 2 * b + Module.finrank ℝ V * b ^ 2))) • constantCurvature V := by
  have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by norm_cast; omega)
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by norm_cast; omega)
  -- Write `ℓ_(a,b) r = r + k ⊙ g` and let `m` be its Ricci form.
  obtain ⟨k, hk_def⟩ : ∃ k : BilinForm ℝ V,
      k = b • tracelessRicci r + (a * scalar r / Module.finrank ℝ V) • innerₗ V := ⟨_, rfl⟩
  have hk : k.IsSymm :=
    hk_def ▸ (hr.isSymm_tracelessRicci.smul b).add ((BilinForm.isSymm_iff.mpr isSymm_inner).smul _)
  have hA : curvatureAction (boehmWilkingDeformation a b r) =
      curvatureAction r + curvatureAction (kulkarniNomizu k (innerₗ V)) := by
    rw [hk_def, boehmWilkingDeformation_apply_eq_add_kulkarniNomizu hn.ne', map_add]
  obtain ⟨m, hm_def⟩ : ∃ m : BilinForm ℝ V, m = ricci (boehmWilkingDeformation a b r) :=
    ⟨_, rfl⟩
  have hm : m = (1 + ((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicci r +
      ((1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) * scalar r / Module.finrank ℝ V) •
        innerₗ V := hm_def ▸ ricci_boehmWilkingDeformation a b r
  have hmsymm : m.IsSymm := hm_def ▸ (hr.boehmWilkingDeformation a b).isSymm_ricci
  have hρ : ricci r = tracelessRicci r + (scalar r / Module.finrank ℝ V) • innerₗ V := by
    rw [tracelessRicci_apply]; exact (sub_add_cancel (G := BilinForm ℝ V) _ _).symm
  -- Expand the inverse deformation through the Ricci and scalar contractions of `Q(ℓ_(a,b) r)`,
  -- and every reaction and action term through the contraction formulas above.
  rw [boehmWilkingDiscrepancy_def, boehmWilkingDeformation_apply, scalarPart_apply,
    tracelessRicciPart_apply, tracelessRicci_apply,
    (hr.boehmWilkingDeformation a b).ricci_reactionTensor,
    (hr.boehmWilkingDeformation a b).scalar_reactionTensor, ← hm_def,
    hA, LinearMap.add_apply, curvatureAction_kulkarniNomizu_innerₗ hk hmsymm,
    reactionTensor_boehmWilkingDeformation hr hn.ne', ← hk_def,
    reactionTensor_kulkarniNomizu_innerₗ hk, hm, hk_def, hρ]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    curvatureAction_innerₗ, hρ, bilinFormToEnd_innerₗ, tracelessRicciEndomorphism_apply]
  -- Evaluate on four vectors: what remains is an identity of real polynomials in `a`, `b`, `n`,
  -- the scalar curvature, `tr(Ric₀♯ Ric₀♯)` and the values of the bilinear forms involved.
  refine ext_vec fun u v z w ↦ ?_
  simp only [sub_apply, add_apply, smul_apply, kulkarniNomizu_apply, constantCurvature_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.id_comp, LinearMap.comp_id, map_add, map_smul, LinearMap.trace_id,
    LinearMap.BilinForm.trace_bilinFormToEnd, metricTrace_tracelessRicci,
    LinearMap.BilinMap.metricTrace_inner,
    innerₗ_apply_apply, LinearMap.BilinForm.inner_bilinFormToEnd_left, smul_eq_mul]
  generalize hα : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a = α at ha ⊢
  generalize hβ : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b = β at hb ⊢
  obtain rfl : a = (α - 1) / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
    rw [← hα]; field_simp; ring
  obtain rfl : b = (β - 1) / ((Module.finrank ℝ V : ℝ) - 2) := by
    rw [← hβ]; field_simp; ring
  field_simp
  ring

/-- **The Böhm–Wilking discrepancy formula, operator form** (Böhm–Wilking, Theorem 2). On
bivectors, with `Ric♯` and `Ric₀♯` the Ricci and trace-free Ricci endomorphisms and `A ∧ B`
the operator `exteriorPower.symmMap₂ A B`,
`D_(a,b)(R) = ((n - 2) b² - 2 (a - b)) Ric₀ ∧ Ric₀ + 2 a Ric ∧ Ric + 2 b² Ric₀² ∧ id + κ I`
with `I = id` and `κ` as in `TauCeti.FourTensor.boehmWilkingDiscrepancy_eq`. -/
theorem curvatureEndomorphism_boehmWilkingDiscrepancy {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : 2 < Module.finrank ℝ V) {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    curvatureEndomorphism (boehmWilkingDiscrepancy V a b r) =
      (((Module.finrank ℝ V : ℝ) - 2) * b ^ 2 - 2 * (a - b)) •
          exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) (tracelessRicciEndomorphism r) +
        (2 * a) • exteriorPower.symmMap₂ (ricciEndomorphism r) (ricciEndomorphism r) +
        (2 * b ^ 2) • exteriorPower.symmMap₂
          (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r) LinearMap.id +
        (LinearMap.trace ℝ V (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r) /
            (Module.finrank ℝ V * (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a)) *
          (Module.finrank ℝ V * b ^ 2 * (1 - 2 * b) -
            2 * (a - b) * (1 - 2 * b + Module.finrank ℝ V * b ^ 2))) • LinearMap.id := by
  rw [boehmWilkingDiscrepancy_eq hr hn ha hb]
  simp only [map_add, map_smul, curvatureEndomorphism_kulkarniNomizu,
    curvatureEndomorphism_constantCurvature, LinearMap.bilinFormToEnd_innerₗ_comp,
    bilinFormToEnd_innerₗ, ← tracelessRicciEndomorphism_apply, ← ricciEndomorphism_apply,
    smul_smul]
  module

end TauCeti.FourTensor
