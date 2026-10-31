/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Killing vector fields

A *Killing vector field* on a Riemannian manifold is a smooth vector field `X` along which the
metric has vanishing Lie derivative:

`X ⟪Y, Z⟫ = ⟪[X, Y], Z⟫ + ⟪Y, [X, Z]⟫` for all smooth vector fields `Y`, `Z`.

Classically, Killing fields are the vector fields whose local flows act by isometries; this file
works with the infinitesimal condition, which involves only the metric and the Lie bracket. For a
metric-compatible torsion-free connection `∇`, such as the Levi-Civita connection, the Lie
derivative of the metric is `(𝓛_X g)(Y, Z) = ⟪∇_Y X, Z⟫ + ⟪Y, ∇_Z X⟫`, so a
smooth field is Killing exactly when `∇X` is skew-adjoint at every point (the *Killing equation*).

Differentiating the Killing equation and combining it with the Ricci identity and the first
Bianchi identity determines the whole second covariant derivative of `X` by the curvature:

`∇²X(Y, Z) = R(Y, X) Z`, where `∇²X(Y, Z) = ∇_Y ∇_Z X - ∇_{∇_Y Z} X`.

Evaluated along a geodesic `γ` this gives `D_t² (X ∘ γ) = ∇²X(γ', γ') = -R(X, γ') γ'`, so the
restriction of a Killing field to every geodesic is a Jacobi field.

## Main definitions and results

* `TauCeti.Manifold.IsKillingField`: a smooth vector field along which the Lie derivative of the
  metric vanishes.
* `CovariantDerivative.IsMetricCompatible.isKillingField_iff`: for a metric-compatible
  torsion-free connection, a vector field is Killing exactly when it is smooth and satisfies the
  Killing equation `⟪∇_u X, v⟫ = -⟪u, ∇_v X⟫`.
* `TauCeti.Manifold.isKillingField_zero`, `TauCeti.Manifold.IsKillingField.add` and
  `TauCeti.Manifold.IsKillingField.const_smul`: Killing fields form a real vector space.
* `TauCeti.Manifold.IsKillingField.secondCovariantDerivative_eq_curvatureTensor`: the identity
  `∇²X(u, v) = R(u, X) v`.
* `TauCeti.Manifold.IsKillingField.alongCurveWithin_alongCurveWithin_eq` and
  `TauCeti.Manifold.IsKillingField.isJacobiFieldOn`: along a geodesic,
  `D_t² (X ∘ γ) = -R(X, γ') γ'`, so a Killing field restricts to a Jacobi field.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 3, exercises on Killing
  fields (the Killing equation), and Chapter 5 (Jacobi fields).
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 8 (Killing
  fields, and the formula `∇²X(Y, Z) = R(Y, X) Z` for their second covariant derivative).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 4 and 7 (the second covariant derivative and the Ricci identity) and Chapter 10
  (Jacobi fields).
-/

public section

open Bundle CovariantDerivative Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {X : Π x : M, TangentSpace I x}

variable (I X) in
/-- A **Killing vector field**: a smooth vector field `X` along which the Lie derivative of the
metric vanishes, `X ⟪Y, Z⟫ = ⟪[X, Y], Z⟫ + ⟪Y, [X, Z]⟫` for all smooth vector fields `Y`, `Z`. -/
structure IsKillingField : Prop where
  /-- A Killing field is smooth. -/
  contMDiff : CMDiff ∞ (T% X)
  /-- The Lie derivative of the metric along the field vanishes. -/
  mvfderiv_inner : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ x : M, mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x) =
      inner ℝ (mlieBracket I X Y x) (Z x) + inner ℝ (Y x) (mlieBracket I X Z x)

/-- The zero vector field is a Killing field. -/
theorem isKillingField_zero : IsKillingField I (0 : Π x : M, TangentSpace I x) where
  contMDiff := contMDiff_zeroSection ℝ (TangentSpace I)
  mvfderiv_inner Y Z _ _ x := by
    simp only [Pi.zero_apply, map_zero, mlieBracket_zero_left, inner_zero_left,
      inner_zero_right, add_zero]

section LinearCombination

variable [CompleteSpace E]

/-- The sum of two Killing fields is a Killing field. -/
theorem IsKillingField.add {X' : Π x : M, TangentSpace I x} (h : IsKillingField I X)
    (h' : IsKillingField I X') : IsKillingField I (X + X') where
  contMDiff := h.contMDiff.add_section h'.contMDiff
  mvfderiv_inner Y Z hY hZ x := by
    have hX := h.contMDiff.mdifferentiable (by simp) x
    have hX' := h'.contMDiff.mdifferentiable (by simp) x
    rw [Pi.add_apply, map_add, h.mvfderiv_inner hY hZ x, h'.mvfderiv_inner hY hZ x,
      mlieBracket_add_left hX hX', mlieBracket_add_left hX hX', inner_add_left, inner_add_right]
    ring

/-- A constant multiple of a Killing field is a Killing field. -/
theorem IsKillingField.const_smul (h : IsKillingField I X) (c : ℝ) :
    IsKillingField I (c • X) where
  contMDiff := h.contMDiff.const_smul_section
  mvfderiv_inner Y Z hY hZ x := by
    have hX := h.contMDiff.mdifferentiable (by simp) x
    rw [Pi.smul_apply, map_smul, h.mvfderiv_inner hY hZ x, mlieBracket_const_smul_left hX,
      mlieBracket_const_smul_left hX, inner_smul_left, inner_smul_right, smul_eq_mul,
      RCLike.conj_to_real]
    ring

end LinearCombination

section Connection

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

variable [T2Space M]

/-- **The Killing equation.** For a metric-compatible torsion-free connection `∇`, such as the
Levi-Civita connection, a vector field `X` is Killing exactly when it is smooth and `∇X` is
skew-adjoint at every point: `⟪∇_u X, v⟫ = -⟪u, ∇_v X⟫`. -/
theorem _root_.CovariantDerivative.IsMetricCompatible.isKillingField_iff
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) :
    IsKillingField I X ↔ CMDiff ∞ (T% X) ∧
      ∀ (x : M) (u v : TangentSpace I x), inner ℝ (cov X x u) v = -inner ℝ u (cov X x v) := by
  refine ⟨fun h ↦ ⟨h.contMDiff, fun x u v ↦ ?_⟩, fun ⟨hX, h⟩ ↦ ⟨hX, fun Y Z hY hZ x ↦ ?_⟩⟩
  · obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
    obtain ⟨Z, hZ, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
    have hLie := hcov.mvfderiv_inner_sub_inner_mlieBracket ht
      (h.contMDiff.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)
      (hZ.mdifferentiable (by simp) x)
    rw [h.mvfderiv_inner hY hZ x] at hLie
    linarith
  · have hLie := hcov.mvfderiv_inner_sub_inner_mlieBracket ht
      (hX.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)
      (hZ.mdifferentiable (by simp) x)
    rw [h x (Y x) (Z x)] at hLie
    linarith

/-- **The Killing equation** for a Killing field: for a metric-compatible torsion-free
connection, `∇X` is skew-adjoint, `⟪∇_u X, v⟫ = -⟪u, ∇_v X⟫`. -/
theorem IsKillingField.inner_covariantDerivative_eq_neg (h : IsKillingField I X)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (u v : TangentSpace I x) :
    inner ℝ (cov X x u) v = -inner ℝ u (cov X x v) :=
  ((hcov.isKillingField_iff ht).1 h).2 x u v

end Connection

section SecondDerivative

variable [FiniteDimensional ℝ E] [T2Space M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

/-- The second covariant derivative of a Killing field is skew-adjoint in its last two
arguments: `⟪∇²X(u, v), w⟫ = -⟪v, ∇²X(u, w)⟫`. This is the covariant derivative of the Killing
equation. -/
theorem IsKillingField.inner_secondCovariantDerivative_eq_neg (h : IsKillingField I X)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (u v w : TangentSpace I x) :
    inner ℝ (cov.secondCovariantDerivative cov X x u v) w =
      -inner ℝ v (cov.secondCovariantDerivative cov X x u w) := by
  have hX := h.contMDiff
  have hskew := h.inner_covariantDerivative_eq_neg hcov ht
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  -- The fields `A = ∇_V X` and `B = ∇_W X` satisfy `⟪A, W⟫ + ⟪V, B⟫ = 0` identically.
  set A : Π y : M, TangentSpace I y := fun y ↦ cov X y (V y)
  set B : Π y : M, TangentSpace I y := fun y ↦ cov X y (W y)
  have hA : CMDiff ∞ (T% A) := cov.contMDiff_apply hV hX
  have hB : CMDiff ∞ (T% B) := cov.contMDiff_apply hW hX
  have hzero : (fun y ↦ inner ℝ (A y) (W y)) = -fun y ↦ inner ℝ (V y) (B y) :=
    funext fun y ↦ by rw [Pi.neg_apply]; exact hskew y (V y) (W y)
  -- Differentiate this identity in the direction `u` using metric compatibility.
  have hderiv : mvfderiv I (fun y ↦ inner ℝ (A y) (W y)) x u =
      -mvfderiv I (fun y ↦ inner ℝ (V y) (B y)) x u := by
    rw [hzero, mvfderiv_neg, neg_apply]
  have hAW := hcov.mvfderiv_inner_eq (FiberBundle.extend E u) (hA.mdifferentiable (by simp) x)
    (hW.mdifferentiable (by simp) x)
  have hVB := hcov.mvfderiv_inner_eq (FiberBundle.extend E u) (hV.mdifferentiable (by simp) x)
    (hB.mdifferentiable (by simp) x)
  simp only [FiberBundle.extend_apply_self] at hAW hVB
  rw [hAW, hVB] at hderiv
  rw [secondCovariantDerivative_apply cov cov hX x hV,
    secondCovariantDerivative_apply cov cov hX x hW, inner_sub_left, inner_sub_right]
  have hskew₁ := hskew x (cov V x u) (W x)
  have hskew₂ := hskew x (V x) (cov W x u)
  simp only [A, B] at hderiv
  linarith

/-- **The second covariant derivative of a Killing field** is determined by curvature:
`∇²X(u, v) = R(u, X) v`, where `∇²X(u, v) = ∇_u ∇_v X - ∇_{∇_u v} X`, for any metric-compatible
torsion-free connection. -/
theorem IsKillingField.secondCovariantDerivative_eq_curvatureTensor (h : IsKillingField I X)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative cov X x u v = cov.curvatureTensor x u (X x) v := by
  set ξ := X x
  let T : TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ :=
    fun a b c ↦ inner ℝ (cov.secondCovariantDerivative cov X x a b) c
  let R : TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x → ℝ :=
    fun a b c d ↦ inner ℝ (cov.curvatureTensor x a b c) d
  have hskew (a b c : TangentSpace I x) : T a b c = -T a c b := by
    simpa only [T, real_inner_comm b] using h.inner_secondCovariantDerivative_eq_neg hcov ht x a b c
  have hricci (a b c : TangentSpace I x) : T a b c - T b a c = R a b ξ c := by
    simp only [T, R, ← inner_sub_left]
    rw [secondCovariantDerivative_sub_swap_of_isTorsionFree cov cov
      ((isTorsionFree_iff_torsion_eq_zero cov).2 ht) h.contMDiff]
  have hfirst (a b c d : TangentSpace I x) : R a b c d = -R b a c d := by
    simp only [R, cov.curvatureTensor_antisymm x a b, LinearMap.neg_apply, inner_neg_left]
  have hlast (a b c d : TangentSpace I x) : R a b c d = -R a b d c := by
    simpa only [R, real_inner_comm] using hcov.inner_curvatureTensor_eq_neg x a b c d
  have hpairs (a b c d : TangentSpace I x) : R a b c d = R c d a b :=
    hcov.inner_curvatureTensor_swap_pairs ht x a b c d
  have hbianchi (a b c d : TangentSpace I x) : R a b c d + R b c a d + R c a b d = 0 := by
    simpa only [R, inner_add_left, inner_zero_left] using
      congrArg (fun q ↦ inner ℝ q d) (cov.curvatureTensor_cyclic_eq_zero ht x a b c)
  refine ext_inner_right ℝ fun c ↦ ?_
  -- Restate the goal through the abbreviations `T` and `R` used by the hypotheses below, so that
  -- `linarith` sees the same atoms; the two sides are these abbreviations unfolded.
  change T u v c = R u ξ v c
  -- Alternating the skew-symmetry and the Ricci identity around the three slots gives
  -- `2 T(u, v, c) = R(u, v, ξ, c) + R(c, v, ξ, u) - R(u, c, ξ, v)`.
  have h₁ := hskew u v c
  have h₂ := hricci u c v
  have h₃ := hskew c u v
  have h₄ := hricci c v u
  have h₅ := hskew v c u
  have h₆ := hricci u v c
  -- The curvature symmetries and the first Bianchi identity reduce the right side to
  -- `2 R(u, ξ, v, c)`.
  have h₇ := hpairs c v ξ u
  have h₈ := hfirst ξ u c v
  have h₉ := hlast u ξ c v
  have h₁₀ := hpairs u c ξ v
  have h₁₁ := hfirst ξ v u c
  have h₁₂ := hbianchi u v ξ c
  have h₁₃ := hfirst ξ u v c
  linarith

end SecondDerivative

section Geodesic

variable [FiniteDimensional ℝ E] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-- Along a geodesic, the second covariant derivative of the restriction of a Killing field `X`,
tested against a smooth vector field `Z`, is `⟪D_t² (X ∘ γ), Z⟫ = -⟪γ', ∇²X(γ', Z)⟫`. Both sides
come from differentiating `⟪D_t (X ∘ γ), Z⟫ = ⟪∇_{γ'} X, Z⟫ = -⟪γ', ∇_Z X⟫` along `γ`. -/
private theorem IsKillingField.inner_alongCurveWithin_alongCurveWithin_eq
    (h : IsKillingField I X) (hγ : IsGeodesicCurveOn I γ s) (ht : t ∈ s)
    {Z : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z)) :
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ X (γ r)) s) s t) (Z (γ t)) =
      -inner ℝ (curveVelocityWithin I γ s t)
        ((leviCivitaConnection I M).secondCovariantDerivative (leviCivitaConnection I M) X (γ t)
          (curveVelocityWithin I γ s t) (Z (γ t))) := by
  have hcov := isMetricCompatible_leviCivitaConnection (M := M) I
  have hX := h.contMDiff
  have hskew := h.inner_covariantDerivative_eq_neg hcov
    (torsion_leviCivitaConnection_eq_zero (M := M) I)
  set γ' := curveVelocityWithin I γ s
  set V : ∀ r, TangentSpace I (γ r) := fun r ↦ X (γ r)
  set W := alongCurveWithin (leviCivitaConnection I M) γ V s
  have hs := hγ.uniqueDiffOn
  have hγd := hγ.mdifferentiableOn
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  -- Regularity of the fields along `γ` whose inner products are differentiated.
  have hlift {Y : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) :
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (Y (γ r))) s :=
    (hY.of_le (by simp)).comp_contMDiffOn hγ.contMDiffOn
  have hcoord {Y : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun r ↦ Y (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ _
      (((hlift hY) t ht).mdifferentiableWithinAt (by norm_num))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hWcoord : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t :=
    differentiableWithinAt_sectionCoord_alongCurveWithin_leviCivitaConnection hs (hlift hX) ht
  have hγ'coord : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ γ' (γ t)) s t :=
    differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ.contMDiffOn ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  -- With `A = ∇_Z X`, the Killing equation gives `⟪W, Z⟫ = ⟪∇_{γ'} X, Z⟫ = -⟪γ', A⟫` along `γ`.
  set A : Π y : M, TangentSpace I y := fun y ↦ leviCivitaConnection I M X y (Z y)
  have hA : CMDiff ∞ (T% A) := (leviCivitaConnection I M).contMDiff_apply hZ hX
  have hpull {Y : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y)) {r : ℝ} (hr : r ∈ s) :
      alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ Y (γ r)) s r =
        leviCivitaConnection I M Y (γ r) (γ' r) :=
    alongCurveWithin_pullback_curveVelocityWithin _ γ Y (hs r hr) (hγd r hr)
      (hY.mdifferentiable (by simp) (γ r))
  have heqOn : EqOn (fun r ↦ inner ℝ (W r) (Z (γ r))) (fun r ↦ -inner ℝ (γ' r) (A (γ r))) s :=
    fun r hr ↦ by
      simp only [W, V, hpull hX hr, A]
      exact hskew _ _ _
  -- Differentiate both sides with the metric product rule along `γ`.
  have hleft := hcov.hasDerivWithinAt_inner_alongCurveWithin (hs t ht) (hγd t ht) hWcoord
    (hcoord hZ)
  have hright := (hcov.hasDerivWithinAt_inner_alongCurveWithin (hs t ht) (hγd t ht) hγ'coord
    (hcoord hA)).neg
  have hderiv := (hs t ht).eq_deriv _ (hleft.congr_of_mem (fun r hr ↦ (heqOn hr).symm) ht)
    hright
  -- The acceleration of `γ` vanishes, and the derivatives of pulled-back fields are ambient
  -- covariant derivatives.
  rw [hpull hZ ht, hpull hA ht, ← accelerationWithin_def,
    hγ.accelerationWithin_eq_zero t ht, inner_zero_left, zero_add] at hderiv
  simp only [W, V, hpull hX ht] at hderiv
  rw [secondCovariantDerivative_apply _ _ hX (γ t) hZ (γ' t), inner_sub_right]
  have hcross := hskew (γ t) (γ' t) (leviCivitaConnection I M Z (γ t) (γ' t))
  linarith

/-- **The Jacobi equation for a Killing field.** Along a geodesic `γ`, the restriction of a
Killing field `X` satisfies `D_t² (X ∘ γ) = -R(X, γ') γ'`. -/
theorem IsKillingField.alongCurveWithin_alongCurveWithin_eq (h : IsKillingField I X)
    (hγ : IsGeodesicCurveOn I γ s) (ht : t ∈ s) :
    alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ X (γ r)) s) s t =
      -(leviCivitaConnection I M).curvatureTensor (γ t) (X (γ t))
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t) := by
  have hcov := isMetricCompatible_leviCivitaConnection (M := M) I
  have htor := torsion_leviCivitaConnection_eq_zero (M := M) I
  set u := curveVelocityWithin I γ s t
  set ξ := X (γ t)
  set q := alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ X (γ r)) s) s t -
    -(leviCivitaConnection I M).curvatureTensor (γ t) ξ u u
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
  -- Test the Jacobi defect `q` against a smooth field `Z` with `Z (γ t) = q`.
  obtain ⟨Z, hZ, hZt⟩ := FiberBundle.exists_contMDiff_section_eq I E q
  have hD := h.inner_alongCurveWithin_alongCurveWithin_eq hγ ht hZ
  rw [h.secondCovariantDerivative_eq_curvatureTensor hcov htor, hZt] at hD
  rw [inner_sub_left, hD, inner_neg_left]
  -- The curvature symmetries give `⟪u, R(u, ξ) q⟫ = ⟪R(ξ, u) u, q⟫`.
  have hsym₁ := hcov.inner_curvatureTensor_swap_pairs htor (γ t) ξ u u q
  have hsym₂ := hcov.inner_curvatureTensor_eq_neg (γ t) u q ξ u
  have hsym₃ := hcov.inner_curvatureTensor_swap_pairs htor (γ t) u ξ q u
  have hsym₄ := real_inner_comm u ((leviCivitaConnection I M).curvatureTensor (γ t) u ξ q)
  have hsym₅ := real_inner_comm ξ ((leviCivitaConnection I M).curvatureTensor (γ t) u q u)
  have hsym₆ := congrArg (fun T ↦ inner ℝ (T u) ξ)
    ((leviCivitaConnection I M).curvatureTensor_antisymm (γ t) q u)
  simp only [LinearMap.neg_apply, inner_neg_left] at hsym₆
  linarith

/-- **A Killing field restricts to a Jacobi field along every geodesic.** -/
theorem IsKillingField.isJacobiFieldOn (h : IsKillingField I X) (hγ : IsGeodesicCurveOn I γ s) :
    IsJacobiFieldOn I γ (fun r ↦ X (γ r)) s where
  isGeodesicCurveOn := hγ
  contMDiffOn := (h.contMDiff.of_le (by simp)).comp_contMDiffOn hγ.contMDiffOn
  equation r hr := by
    rw [h.alongCurveWithin_alongCurveWithin_eq hγ hr, neg_add_cancel]

end Geodesic

end TauCeti.Manifold
