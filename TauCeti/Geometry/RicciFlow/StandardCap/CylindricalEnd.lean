/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry
public import TauCeti.Geometry.RicciFlow.StandardCap.Metric
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The cylindrical end of a standard cap

Beyond any radius where a standard cap profile is constant at `√2`, its polar coordinates
identify the exterior with a round product cylinder. The coordinate `r` is the Euclidean norm
in the cap coordinates. The spherical coordinate is the unit direction, with its round metric
rescaled by two. The resulting isometry identifies each product slice with a Euclidean sphere
of the corresponding radius.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Definition 12.1.
* [LeanEval Poincaré submissions](https://github.com/frenzymath/lean-eval-submissions).
* [Poincaré conjecture formalization](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle Metric Set TopologicalSpace
open scoped ContDiff Manifold Pointwise Topology

namespace TauCeti

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The cylinder points of radial coordinate strictly greater than `R`. -/
def standardCapCylinderEnd (R : ℝ) : Opens (standardCapRadialDomain × sphere (0 : V) 1) :=
  ⟨{p | R < (p.1 : ℝ)},
    isOpen_lt continuous_const (continuous_subtypeVal.comp continuous_fst)⟩

omit [InnerProductSpace ℝ V] in
/-- A cylinder point belongs to the end when its axial coordinate exceeds the cutoff. -/
@[simp]
theorem mem_standardCapCylinderEnd {R : ℝ}
    (p : standardCapRadialDomain × sphere (0 : V) 1) :
    p ∈ standardCapCylinderEnd V R ↔ R < (p.1 : ℝ) := by
  rw [standardCapCylinderEnd]
  rfl

/-- The cap exterior beyond Euclidean radius `R`. -/
def standardCapExterior (R : ℝ) : Opens V :=
  ⟨{x | R < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩

omit [InnerProductSpace ℝ V] in
/-- A cap point lies in the exterior when its Euclidean norm exceeds the cutoff. -/
@[simp]
theorem mem_standardCapExterior {R : ℝ} (x : V) :
    x ∈ standardCapExterior V R ↔ R < ‖x‖ :=
  (Iff.rfl)

variable {V} {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

private def capEndPolarMap {R : ℝ} (p : standardCapCylinderEnd V R) : standardCapExterior V R :=
  ⟨standardCapPolar V p, by
    rw [mem_standardCapExterior, norm_standardCapPolar]
    exact (mem_standardCapCylinderEnd V p.val).mp p.property⟩

private theorem bijective_capEndPolarMap {R : ℝ} (hR : 0 ≤ R) :
    Function.Bijective (capEndPolarMap (V := V) (R := R)) := by
  constructor
  · intro p q hpq
    have heq : standardCapPolar V p = standardCapPolar V q := congrArg Subtype.val hpq
    have hswap : (p.val.2, p.val.1) = (q.val.2, q.val.1) :=
      (homeomorphUnitSphereProd V).symm.injective <| Subtype.ext <| by
        simpa only [homeomorphUnitSphereProd_symm_apply_coe, standardCapPolar_apply] using heq
    exact Subtype.ext (Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap))
  · intro x
    have hx := (mem_standardCapExterior V (x : V)).mp x.property
    have hx0 := norm_pos_iff.mp (hR.trans_lt hx)
    obtain ⟨p, hp⟩ : (x : V) ∈ range (standardCapPolar V) := by
      rw [range_standardCapPolar]
      exact hx0
    have hpR : p ∈ standardCapCylinderEnd V R := by
      rw [mem_standardCapCylinderEnd, ← norm_standardCapPolar p, hp]
      exact hx
    exact ⟨⟨p, hpR⟩, Subtype.ext hp⟩

private theorem isLocalDiffeomorph_capEndPolarMap {R : ℝ} :
    IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) ∞
      (capEndPolarMap (V := V) (R := R)) := by
  have hpolar : IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) ∞ (standardCapPolar V) :=
    isLocalDiffeomorph_of_mfderiv_eq contMDiff_standardCapPolar (by simp)
      isInvertible_mfderiv_standardCapPolar
  intro p
  have hin := isLocalDiffeomorph_subtype_val
    (I := 𝓘(ℝ).prod (𝓡 n)) (n := ∞) (U := standardCapCylinderEnd V R) p
  have hcomp : IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) ∞
      ((Subtype.val : standardCapExterior V R → V) ∘ capEndPolarMap) p :=
    hin.comp (hg := hpolar p.val)
  have hcontinuous : Continuous (capEndPolarMap (V := V) (R := R)) :=
    ((contMDiff_standardCapPolar (n := n) (m := ∞)).continuous.comp
      continuous_subtypeVal).subtype_mk _
  exact hcomp.of_comp_left (isLocalDiffeomorph_subtype_val (capEndPolarMap p))
    hcontinuous.continuousAt

private def standardCapExteriorPolar {R : ℝ} (hR : 0 ≤ R) :
    standardCapCylinderEnd V R ≃ₘ^∞⟮𝓘(ℝ).prod (𝓡 n), 𝓘(ℝ, V)⟯ standardCapExterior V R :=
  isLocalDiffeomorph_capEndPolarMap.diffeomorphOfBijective (bijective_capEndPolarMap hR)

private theorem standardCapExteriorPolar_apply {R : ℝ} (hR : 0 ≤ R)
    (p : standardCapCylinderEnd V R) :
    (standardCapExteriorPolar (n := n) hR p : V) = (p.val.1 : ℝ) • (p.val.2 : V) := by
  rw [standardCapExteriorPolar, IsLocalDiffeomorph.coe_diffeomorphOfBijective]
  exact standardCapPolar_apply p.val

/-- The round cylinder metric with axial coefficient one and sphere radius `√2`, restricted
to the positive radial half-line. -/
def standardCapCylinderMetric :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun p : standardCapRadialDomain × sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
  (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
    standardCapRadialDomain).prodTangentSpace
      (sphereRoundMetricOfRadius (E := V) (Real.sqrt 2) (Real.sqrt_pos.2 two_pos))

/-- The cap cylinder metric pairs the axial coordinates and twice the round inner product
of the spherical coordinates. -/
theorem standardCapCylinderMetric_inner
    (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (standardCapCylinderMetric (V := V)).inner p v w =
      (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
        standardCapRadialDomain).inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
      2 * inner ℝ (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 := by
  rw [standardCapCylinderMetric, ContMDiffRiemannianMetric.prodTangentSpace_inner,
    sphereRoundMetricOfRadius_inner, Real.sq_sqrt two_pos.le]

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)

/-- At radius where the profile is `√2`, the polar metric is the round cylinder metric. -/
theorem puncturedMetric_inner_eq_standardCapCylinderMetric
    (p : standardCapRadialDomain × sphere (0 : V) 1) (hp : f p.1 = Real.sqrt 2)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.puncturedMetric V).inner p v w = (standardCapCylinderMetric (V := V)).inner p v w := by
  rw [hf.puncturedMetric_inner, standardCapCylinderMetric_inner, hp, Real.sq_sqrt two_pos.le]
  rw [ContMDiffRiemannianMetric.ofLE_inner, sphereRoundMetric_inner, inner_tangentSpace_sphere]

private def cylindricalEndIsometryAux {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ r > R, f r = Real.sqrt 2) :
    letI : RiemannianBundle (fun p : standardCapCylinderEnd V R ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
      ⟨((standardCapCylinderMetric (V := V)).restrictOpenTangentSpace
        (standardCapCylinderEnd V R)).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : standardCapExterior V R ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨((hf.metric V).restrictOpenTangentSpace (standardCapExterior V R)).toRiemannianMetric⟩
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (standardCapCylinderEnd V R) (standardCapExterior V R) := by
  letI : RiemannianBundle (fun p : standardCapCylinderEnd V R ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
    ⟨((standardCapCylinderMetric (V := V)).restrictOpenTangentSpace
      (standardCapCylinderEnd V R)).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : standardCapExterior V R ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨((hf.metric V).restrictOpenTangentSpace (standardCapExterior V R)).toRiemannianMetric⟩
  let Φ := standardCapExteriorPolar (V := V) (n := n) hR
  refine { toDiffeomorph := Φ, inner_mfderiv' := ?_ }
  intro p v w
  -- Identify both restricted tangent metrics through the differentials of the inclusions.
  change ((hf.metric V).restrictOpenTangentSpace _).inner (Φ p)
    (mfderiv _ _ Φ p v) (mfderiv _ _ Φ p w) =
      ((standardCapCylinderMetric (V := V)).restrictOpenTangentSpace _).inner p v w
  have hcomp : (Subtype.val : standardCapExterior V R → V) ∘ Φ =
      standardCapPolar V ∘ (Subtype.val : standardCapCylinderEnd V R → _) := by
    funext p
    simpa only [Function.comp_apply, standardCapPolar_apply] using
      standardCapExteriorPolar_apply hR p
  have hout : MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, V)
      (Subtype.val : standardCapExterior V R → V) :=
    (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
  have hin : MDifferentiable (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n))
      (Subtype.val : standardCapCylinderEnd V R → _) :=
    (contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp)
  have hchain (u : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (Subtype.val : standardCapExterior V R → V) (Φ p)
          (mfderiv _ _ Φ p u) =
        mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) (standardCapPolar V) p.val
          (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n))
            (Subtype.val : standardCapCylinderEnd V R → _) p u) := by
    rw [← mfderiv_comp_apply p (hout (Φ p)) (Φ.mdifferentiable (by simp) p), hcomp,
      mfderiv_comp_apply p ((contMDiff_standardCapPolar (m := ∞)).mdifferentiable (by simp) p.val)
        (hin p)]
  simp only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] at hchain
  rw [ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
    ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner, hchain v, hchain w]
  have hpoint : (Φ p : V) = standardCapPolar V p.val := congrFun hcomp p
  rw [hpoint]
  exact (hf.metric_inner_mfderiv_standardCapPolar p.val _ _).trans
    (hf.puncturedMetric_inner_eq_standardCapCylinderMetric p.val
      (hfR _ ((mem_standardCapCylinderEnd V p.val).mp p.property)) _ _)

variable {R : ℝ}

local notation "cylinderMetric" =>
  ContMDiffRiemannianMetric.restrictOpenTangentSpace
    (standardCapCylinderMetric (V := V) (n := n))
    (standardCapCylinderEnd V R)
local notation "exteriorMetric" =>
  ContMDiffRiemannianMetric.restrictOpenTangentSpace
    (IsStandardCapProfile.metric V hf) (standardCapExterior V R)

private theorem cylindricalEndIsometryAux_apply (hR : 0 ≤ R)
    (hfR : ∀ r > R, f r = Real.sqrt 2) (p : standardCapCylinderEnd V R) :
    letI : RiemannianBundle (fun p : standardCapCylinderEnd V R ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(cylinderMetric).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : standardCapExterior V R ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨(exteriorMetric).toRiemannianMetric⟩
    (hf.cylindricalEndIsometryAux (n := n) hR hfR p : V) =
      (p.val.1 : ℝ) • (p.val.2 : V) :=
  standardCapExteriorPolar_apply hR p

/-- The standard cap exterior is isometric to the round product cylinder beyond any radius
where the profile is constantly `√2`. -/
def cylindricalEndIsometry (hR : 0 ≤ R) (hfR : ∀ r > R, f r = Real.sqrt 2) :
    letI : FiniteDimensional ℝ V :=
      Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = n + 1)
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (WithMetric cylinderMetric) (WithMetric exteriorMetric) :=
  letI : FiniteDimensional ℝ V :=
    Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = n + 1)
  letI : RiemannianBundle (fun p : standardCapCylinderEnd V R ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(cylinderMetric).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : standardCapExterior V R ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨(exteriorMetric).toRiemannianMetric⟩
  ((WithMetric.riemannianIsometry cylinderMetric).trans
    (hf.cylindricalEndIsometryAux hR hfR)).trans
    (WithMetric.riemannianIsometry exteriorMetric).symm

/-- In ambient coordinates the cylindrical isometry takes `(r, u)` to `r • u`. -/
@[simp]
theorem cylindricalEndIsometry_apply (hR : 0 ≤ R)
    (hfR : ∀ r > R, f r = Real.sqrt 2) (p : standardCapCylinderEnd V R) :
    letI : FiniteDimensional ℝ V :=
      Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = n + 1)
    ((hf.cylindricalEndIsometry (n := n) hR hfR
      (WithMetric.toWithMetric cylinderMetric p)).ofWithMetric : V) =
      (p.val.1 : ℝ) • (p.val.2 : V) := by
  let : RiemannianBundle (fun p : standardCapCylinderEnd V R ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) := ⟨(cylinderMetric).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : standardCapExterior V R ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨(exteriorMetric).toRiemannianMetric⟩
  simp only [cylindricalEndIsometry, RiemannianIsometry.trans_apply,
    WithMetric.coe_riemannianIsometry, WithMetric.coe_riemannianIsometry_symm,
    WithMetric.ofWithMetric_toWithMetric]
  exact hf.cylindricalEndIsometryAux_apply hR hfR p

/-- The inverse cylinder coordinates of a cap exterior point are its norm and its unit
direction. -/
@[simp]
theorem cylindricalEndIsometry_symm_apply (hR : 0 ≤ R)
    (hfR : ∀ r > R, f r = Real.sqrt 2) (x : standardCapExterior V R) :
    letI : FiniteDimensional ℝ V :=
      Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = n + 1)
    let p := ((hf.cylindricalEndIsometry (n := n) hR hfR).symm
      (WithMetric.toWithMetric exteriorMetric x)).ofWithMetric
    (p.val.1 : ℝ) = ‖(x : V)‖ ∧ (p.val.2 : V) = ‖(x : V)‖⁻¹ • (x : V) := by
  let : FiniteDimensional ℝ V :=
    Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = n + 1)
  let Φ := hf.cylindricalEndIsometry (V := V) (n := n) hR hfR
  let p := (Φ.symm (WithMetric.toWithMetric exteriorMetric x)).ofWithMetric
  have hΦ : Φ (WithMetric.toWithMetric cylinderMetric p) =
      WithMetric.toWithMetric exteriorMetric x :=
    Φ.apply_symm_apply _
  have hpolar : (p.val.1 : ℝ) • (p.val.2 : V) = (x : V) :=
    (hf.cylindricalEndIsometry_apply hR hfR p).symm.trans
      (congrArg (fun y ↦ (y.ofWithMetric : V)) hΦ)
  have hr := p.val.1.property
  have hnorm : (p.val.1 : ℝ) = ‖(x : V)‖ := by
    rw [← hpolar, norm_smul, norm_eq_of_mem_sphere p.val.2, mul_one, Real.norm_of_nonneg hr.le]
  refine ⟨hnorm, ?_⟩
  rw [← hnorm, ← hpolar, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The cylindrical isometry sends an axial slice of radius `r` onto the sphere of that
radius in cap coordinates. -/
theorem range_cylindricalEndIsometry_slice {r : ℝ} (hR : 0 ≤ R)
    (hfR : ∀ t > R, f t = Real.sqrt 2) (hr : R < r) :
    letI : FiniteDimensional ℝ V :=
      Module.finite_of_finrank_eq_succ (Fact.out : Module.finrank ℝ V = n + 1)
    range (fun u : sphere (0 : V) 1 ↦
      ((hf.cylindricalEndIsometry (n := n) hR hfR
        (WithMetric.toWithMetric cylinderMetric ⟨(⟨r, hR.trans_lt hr⟩, u),
          (mem_standardCapCylinderEnd V _).mpr hr⟩)).ofWithMetric : V)) =
      sphere (0 : V) r := by
  simp only [cylindricalEndIsometry_apply, range_smul, Subtype.range_coe]
  rw [smul_sphere' (hR.trans_lt hr).ne', smul_zero,
    Real.norm_of_nonneg (hR.trans hr.le), mul_one]

end IsStandardCapProfile

end TauCeti
