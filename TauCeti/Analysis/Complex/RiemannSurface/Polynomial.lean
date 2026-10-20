/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Degree.Operations
public import TauCeti.Algebra.Polynomial.Reverse
public import TauCeti.Analysis.Complex.RiemannSurface.BranchValues
public import TauCeti.Analysis.Polynomial.Order
public import TauCeti.Geometry.Manifold.Instances.OnePoint
public import TauCeti.Topology.Compactification.OnePoint.Map
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial maps of the Riemann sphere

A nonconstant complex polynomial `p` of degree `d` extends to the Riemann sphere `OnePoint ℂ` by
sending `∞` to `∞`; this extension is Mathlib's `OnePoint.map`. In the affine chart it is
`z ↦ p(z)`. In the inverted chart at `∞` it is `w ↦ w ^ d / q(w)`, where `q = p.reverse` is the
reversed polynomial, `q(w) = w ^ d p(w⁻¹)`, whose value at `0` is the leading coefficient of `p`.
So the extension is holomorphic, and its local multiplicity is `d` at `∞`. At a finite point `z`
the local multiplicity is the multiplicity of `z` as a root of `p - p(z)`, and it exceeds `1`
exactly when `z` is a critical point of `p`, a root of the derivative.

The fibre over `∞` is the single point `∞`, so the degree of the extension is `d`, and its branch
values lie in `∞` together with the critical values of `p`. When `d ≥ 2` they are exactly `∞`
together with the critical values; when `d = 1` the extension is a Möbius transformation and
has no branch values. These are the polynomial branched covers of the sphere, among them the
power maps `z ↦ z ^ n` and the polynomial Belyi maps.

The last section treats the example `z ↦ 4z(1 - z)` of degree `2`: its only critical point is
`1/2`, with critical value `1`, so its branch values are `1` and `∞`, and its fibre over `0` is
the two points `0` and `1`.

## Main declarations

* `TauCeti.RiemannSurface.invChart_onePointMap_eval_invChart_symm`: the extension read in the
  inverted chart at `∞`.
* `TauCeti.RiemannSurface.continuous_onePointMap_eval` and
  `TauCeti.RiemannSurface.mdifferentiable_onePointMap_eval`: the extension is continuous and
  holomorphic.
* `TauCeti.RiemannSurface.localMultiplicity_onePointMap_eval_coe`: at a finite point `z` its local
  multiplicity is the root multiplicity of `p - p(z)` at `z`, and
  `TauCeti.RiemannSurface.one_lt_localMultiplicity_onePointMap_eval_coe_iff`: it exceeds `1`
  exactly at the critical points of `p`.
* `TauCeti.RiemannSurface.localMultiplicity_onePointMap_eval_coe_of_not_isRoot`: away from the
  critical points it is `1`.
* `TauCeti.RiemannSurface.localMultiplicity_onePointMap_eval_infty`: its local multiplicity at
  `∞` is the degree of `p`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.spherePolynomial`: the extension as a finite
  holomorphic map of the Riemann sphere.
* `TauCeti.RiemannSurface.degree_onePointMap_eval`: its degree is the degree of `p`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.branchValues_spherePolynomial_subset`: its branch
  values lie in `{∞}` together with the critical values of `p`, and
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.branchValues_spherePolynomial`: for degree at
  least `2` they are exactly `∞` together with the critical values of `p`.
* `TauCeti.RiemannSurface.degree_onePointMap_four_mul_mul_one_sub`,
  `TauCeti.RiemannSurface.preimage_onePointMap_four_mul_mul_one_sub_zero`,
  `TauCeti.RiemannSurface.preimage_onePointMap_four_mul_mul_one_sub_one` and
  `TauCeti.RiemannSurface.branchValues_spherePolynomial_four_mul_X_mul_one_sub_X`:
  the map `z ↦ 4z(1 - z)` has degree `2`, fibres `{0, 1}` over `0` and `{1/2}` over `1`, and
  branch values `1` and `∞`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1.5 (c) (the charts of the Riemann sphere) and §2 (the local behaviour of
  holomorphic maps).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 (multiplicities of polynomial maps of the
  sphere).
-/

public noncomputable section

open Filter Function OnePoint Polynomial Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {p : ℂ[X]}

/-- In the inverted chart at `∞`, the extension of a nonconstant polynomial `p` to the Riemann
sphere is `w ↦ w ^ d / p.reverse.eval w`, where `d` is the degree of `p`. -/
theorem invChart_onePointMap_eval_invChart_symm (hp : 0 < p.natDegree) (w : ℂ) :
    invChart (OnePoint.map (fun z : ℂ ↦ p.eval z) (invChart.symm w)) =
      w ^ p.natDegree / p.reverse.eval w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [zero_pow hp.ne']
  · rw [invChart_symm_of_ne_zero hw, map_some, invChart_coe, p.eval_reverse_of_ne_zero hw,
      div_mul_cancel_left₀ (pow_ne_zero _ hw)]

/-- **Polynomial maps of the Riemann sphere are continuous.** The extension of a nonconstant
polynomial to `OnePoint ℂ`, sending `∞` to `∞`, is continuous: a polynomial tends to infinity at
infinity. -/
theorem continuous_onePointMap_eval (hp : 0 < p.natDegree) :
    Continuous (OnePoint.map fun z : ℂ ↦ p.eval z) := by
  refine OnePoint.continuous_map p.continuous ?_
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact,
    ← tendsto_norm_atTop_iff_cobounded]
  exact p.tendsto_norm_atTop (natDegree_pos_iff_degree_pos.1 hp) tendsto_norm_cobounded_atTop

/-- Near `∞`, the extension of a nonconstant polynomial to the Riemann sphere is
`w ↦ w ^ d / p.reverse.eval w` read in the inverted chart. -/
private theorem onePointMap_eval_eventuallyEq_infty (hp : 0 < p.natDegree) :
    (OnePoint.map fun z : ℂ ↦ p.eval z) =ᶠ[𝓝 (∞ : OnePoint ℂ)]
      ((invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).symm ∘
        (fun w : ℂ ↦ w ^ p.natDegree / p.reverse.eval w) ∘ invChart) := by
  have hsrc : ∀ᶠ x in 𝓝 (∞ : OnePoint ℂ), x ∈ invChart.source :=
    invChart.open_source.mem_nhds (by simp)
  have hmap : ∀ᶠ x in 𝓝 (∞ : OnePoint ℂ),
      OnePoint.map (fun z : ℂ ↦ p.eval z) x ∈ invChart.source :=
    (continuous_onePointMap_eval hp).continuousAt.preimage_mem_nhds
      (invChart.open_source.mem_nhds (by simp))
  filter_upwards [hsrc, hmap] with x hx hfx
  rw [comp_apply, comp_apply, ← invChart_onePointMap_eval_invChart_symm hp, invChart.left_inv hx,
    invChart.left_inv hfx]

/-- The reversed polynomial of a nonconstant polynomial does not vanish at `0`, where its value
is the leading coefficient. -/
private theorem eval_zero_reverse_ne_zero (hp : 0 < p.natDegree) : p.reverse.eval 0 ≠ 0 := by
  simpa using ne_zero_of_natDegree_gt hp

/-- The chart expression `w ↦ w ^ d / p.reverse.eval w` at `∞` is analytic at `0`. -/
private theorem analyticAt_pow_div_eval_reverse (hp : 0 < p.natDegree) :
    AnalyticAt ℂ (fun w : ℂ ↦ w ^ p.natDegree / p.reverse.eval w) 0 :=
  ((analyticAt_id (𝕜 := ℂ)).pow _).div ((AnalyticOnNhd.eval_polynomial _) 0 (mem_univ _))
    (eval_zero_reverse_ne_zero hp)

/-- **Polynomial maps of the Riemann sphere are holomorphic.** The extension of a nonconstant
polynomial to `OnePoint ℂ`, sending `∞` to `∞`, is holomorphic. -/
theorem mdifferentiable_onePointMap_eval (hp : 0 < p.natDegree) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (OnePoint.map fun z : ℂ ↦ p.eval z) := by
  intro x
  induction x using OnePoint.rec with
  | infty =>
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ (onePointMap_eval_eventuallyEq_infty hp)
    exact (mdifferentiableAt_atlas_symm (Or.inr rfl) (by simp)).comp _
      ((analyticAt_pow_div_eval_reverse hp).differentiableAt.mdifferentiableAt.comp_of_eq _
        (mdifferentiableAt_atlas (Or.inr rfl) (by simp)) (by simp))
  | coe z =>
    -- Off `∞`, the map is `z ↦ p(z)` read in the affine chart.
    have h : (OnePoint.map fun z : ℂ ↦ p.eval z) =ᶠ[𝓝 (z : OnePoint ℂ)]
        (((↑) : ℂ → OnePoint ℂ) ∘ (fun w : ℂ ↦ p.eval w) ∘ affineChart) := by
      filter_upwards [affineChart.open_source.mem_nhds
        (by simp : (z : OnePoint ℂ) ∈ affineChart.source)] with x hx
      induction x using OnePoint.rec with
      | infty => simp at hx
      | coe w => simp
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ h
    exact ((contMDiff_coe _).mdifferentiableAt (by simp)).comp _
      (p.differentiableAt.mdifferentiableAt.comp _
        (mdifferentiableAt_atlas (Or.inl rfl) (by simp)))

/-- At a finite point `z`, the local multiplicity of the extension of a nonconstant polynomial `p`
to the Riemann sphere is the multiplicity of `z` as a root of `p - p(z)`. -/
theorem localMultiplicity_onePointMap_eval_coe (hp : 0 < p.natDegree) (z : ℂ) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) (z : OnePoint ℂ) =
      (p - C (p.eval z)).rootMultiplicity z := by
  have h := analyticOrderAt_eval (sub_C_ne_zero hp (p.eval z)) z
  simp only [eval_sub, eval_C] at h
  simp [localMultiplicity_def, analyticOrderNatAt, h]

/-- At a finite point `z`, the extension of a nonconstant polynomial `p` to the Riemann sphere has
local multiplicity greater than `1` exactly when `z` is a critical point of `p`. -/
theorem one_lt_localMultiplicity_onePointMap_eval_coe_iff (hp : 0 < p.natDegree) {z : ℂ} :
    1 < localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) (z : OnePoint ℂ) ↔
      p.derivative.IsRoot z := by
  rw [localMultiplicity_onePointMap_eval_coe hp,
    one_lt_rootMultiplicity_iff_isRoot (sub_C_ne_zero hp (p.eval z))]
  simp

/-- Away from the critical points of a nonconstant polynomial `p`, its extension to the Riemann
sphere has local multiplicity `1`. -/
theorem localMultiplicity_onePointMap_eval_coe_of_not_isRoot (hp : 0 < p.natDegree) {z : ℂ}
    (hz : ¬ p.derivative.IsRoot z) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) (z : OnePoint ℂ) = 1 := by
  have h1 := (one_lt_localMultiplicity_onePointMap_eval_coe_iff hp).not.2 hz
  have h0 : 0 < localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) (z : OnePoint ℂ) := by
    rw [localMultiplicity_onePointMap_eval_coe hp]
    exact (rootMultiplicity_pos (sub_C_ne_zero hp (p.eval z))).2 (by simp)
  omega

/-- The extension of a nonconstant polynomial `p` to the Riemann sphere has local multiplicity
the degree of `p` at `∞`, where it is `w ↦ w ^ d / p.reverse.eval w` in the inverted chart. -/
@[simp]
theorem localMultiplicity_onePointMap_eval_infty (hp : 0 < p.natDegree) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ p.eval z) (∞ : OnePoint ℂ) = p.natDegree := by
  have h : analyticOrderAt (fun w : ℂ ↦ w ^ p.natDegree / p.reverse.eval w) 0 = p.natDegree :=
    (analyticAt_pow_div_eval_reverse hp).analyticOrderAt_eq_natCast.2
      ⟨fun w ↦ (p.reverse.eval w)⁻¹,
        ((AnalyticOnNhd.eval_polynomial _) 0 (mem_univ _)).inv (eval_zero_reverse_ne_zero hp),
        inv_ne_zero (eval_zero_reverse_ne_zero hp),
        .of_forall fun w ↦ by simp [div_eq_mul_inv]⟩
  simp [localMultiplicity_def, invChart_onePointMap_eval_invChart_symm hp, analyticOrderNatAt, h]

namespace FiniteHolomorphicMap

/-- The extension of a nonconstant polynomial `p` to the Riemann sphere, sending `∞` to `∞`, as a
finite holomorphic map. -/
def spherePolynomial (hp : 0 < p.natDegree) : FiniteHolomorphicMap (OnePoint ℂ) (OnePoint ℂ) :=
  .ofMDifferentiable (mdifferentiable_onePointMap_eval hp) ⟨(0 : ℂ), ∞, by simp⟩

@[simp]
theorem coe_spherePolynomial (hp : 0 < p.natDegree) :
    ⇑(spherePolynomial hp) = OnePoint.map fun z : ℂ ↦ p.eval z :=
  coe_ofMDifferentiable _ _

/-- The branch values of the extension of a nonconstant polynomial `p` to the Riemann sphere lie
in `{∞}` together with the critical values of `p`. -/
theorem branchValues_spherePolynomial_subset (hp : 0 < p.natDegree) :
    (spherePolynomial hp).branchValues ⊆
      insert ∞ ((fun z ↦ ((p.eval z : ℂ) : OnePoint ℂ)) '' {z | p.derivative.IsRoot z}) := by
  intro y hy
  obtain ⟨x, rfl, hx⟩ := (mem_branchValues_iff _ _).1 hy
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    rw [coe_spherePolynomial, one_lt_localMultiplicity_onePointMap_eval_coe_iff hp] at hx
    exact mem_insert_of_mem _ ⟨z, hx, by simp⟩

/-- **The branch values of a polynomial map of the Riemann sphere.** For a polynomial `p` of
degree at least `2`, the branch values of its extension to the Riemann sphere are exactly `∞`,
where the local multiplicity is the degree, together with the critical values of `p`. -/
theorem branchValues_spherePolynomial (hp : 1 < p.natDegree) :
    (spherePolynomial (zero_lt_one.trans hp)).branchValues =
      insert ∞ ((fun z ↦ ((p.eval z : ℂ) : OnePoint ℂ)) '' {z | p.derivative.IsRoot z}) := by
  refine (branchValues_spherePolynomial_subset _).antisymm (insert_subset_iff.2 ⟨?_, ?_⟩)
  · refine (mem_branchValues_iff _ _).2 ⟨∞, by simp, ?_⟩
    rwa [coe_spherePolynomial, localMultiplicity_onePointMap_eval_infty (zero_lt_one.trans hp)]
  · rintro _ ⟨z, hz, rfl⟩
    refine (mem_branchValues_iff _ _).2 ⟨z, by simp, ?_⟩
    rwa [coe_spherePolynomial,
      one_lt_localMultiplicity_onePointMap_eval_coe_iff (zero_lt_one.trans hp)]

end FiniteHolomorphicMap

open FiniteHolomorphicMap in
/-- The extension of a nonconstant polynomial `p` to the Riemann sphere has degree the degree of
`p`: its fibre over `∞` is the single point `∞`, of local multiplicity the degree of `p`. -/
@[simp]
theorem degree_onePointMap_eval (hp : 0 < p.natDegree) :
    degree (OnePoint.map fun z : ℂ ↦ p.eval z) = p.natDegree := by
  have hne : ∀ x, ¬ EventuallyConst (OnePoint.map fun z : ℂ ↦ p.eval z) (𝓝 x) := by
    simpa using (spherePolynomial hp).not_eventuallyConst
  rw [← fiberMultiplicitySum_eq_degree (mdifferentiable_onePointMap_eval hp) hne ∞,
    fiberMultiplicitySum_def, preimage_onePointMap_infty, finsum_mem_singleton,
    localMultiplicity_onePointMap_eval_infty hp]

/-! ### The map `z ↦ 4z(1 - z)` -/

section FourMulMulOneSub

/-- The polynomial `4X(1 - X)` has degree `2`. -/
theorem natDegree_four_mul_X_mul_one_sub_X : (C 4 * X * (1 - X) : ℂ[X]).natDegree = 2 := by
  compute_degree!

/-- The polynomial `4X(1 - X)` is nonconstant. -/
theorem natDegree_four_mul_X_mul_one_sub_X_pos : 0 < (C 4 * X * (1 - X) : ℂ[X]).natDegree := by
  rw [natDegree_four_mul_X_mul_one_sub_X]
  exact two_pos

/-- The extension of `4X(1 - X)` to the Riemann sphere is the extension of `z ↦ 4z(1 - z)`. -/
theorem onePointMap_eval_four_mul_X_mul_one_sub_X :
    (OnePoint.map fun z : ℂ ↦ (C 4 * X * (1 - X) : ℂ[X]).eval z) =
      OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z) := by
  simp

/-- The derivative `4 - 8z` of `4z(1 - z)` vanishes only at `1/2`. -/
private theorem isRoot_derivative_four_mul_X_mul_one_sub_X_iff {z : ℂ} :
    (derivative (C 4 * X * (1 - X) : ℂ[X])).IsRoot z ↔ z = 2⁻¹ := by
  have hd : (derivative (C 4 * X * (1 - X) : ℂ[X])).eval z = 4 - 8 * z := by
    simp
    ring
  rw [IsRoot.def, hd]
  constructor <;> intro h
  · linear_combination (-1 / 8 : ℂ) * h
  · linear_combination (-8 : ℂ) * h

/-- The map `z ↦ 4z(1 - z)` of the Riemann sphere has degree `2`. -/
@[simp]
theorem degree_onePointMap_four_mul_mul_one_sub :
    degree (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) = 2 := by
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X,
    degree_onePointMap_eval natDegree_four_mul_X_mul_one_sub_X_pos,
    natDegree_four_mul_X_mul_one_sub_X]

/-- The fibre of `z ↦ 4z(1 - z)` over `0` consists of the two points `0` and `1`. -/
theorem preimage_onePointMap_four_mul_mul_one_sub_zero :
    (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) ⁻¹' {((0 : ℂ) : OnePoint ℂ)} =
      {((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ)} := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe z => simp [sub_eq_zero, eq_comm (a := (1 : ℂ))]

/-- The fibre of `z ↦ 4z(1 - z)` over `1` is the single point `1/2`. -/
theorem preimage_onePointMap_four_mul_mul_one_sub_one :
    (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) ⁻¹' {((1 : ℂ) : OnePoint ℂ)} =
      {((2⁻¹ : ℂ) : OnePoint ℂ)} := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    simp only [mem_preimage, map_some, mem_singleton_iff, coe_eq_coe]
    constructor
    · intro h
      have h' : (2 * z - 1) ^ 2 = 0 := by linear_combination -h
      linear_combination (1 / 2 : ℂ) * (pow_eq_zero_iff two_ne_zero).1 h'
    · rintro rfl
      norm_num

/-- The map `z ↦ 4z(1 - z)` is unramified away from `1/2` and `∞`, in particular at the two points
`0` and `1` over `0`. -/
theorem localMultiplicity_onePointMap_four_mul_mul_one_sub_coe_of_ne {z : ℂ} (hz : z ≠ 2⁻¹) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) (z : OnePoint ℂ) = 1 := by
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X]
  exact localMultiplicity_onePointMap_eval_coe_of_not_isRoot
    natDegree_four_mul_X_mul_one_sub_X_pos (isRoot_derivative_four_mul_X_mul_one_sub_X_iff.not.2 hz)

/-- The map `z ↦ 4z(1 - z)` is ramified of index `2` at `1/2`, the only point over `1`. -/
@[simp]
theorem localMultiplicity_onePointMap_four_mul_mul_one_sub_half :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) ((2⁻¹ : ℂ) : OnePoint ℂ) = 2 := by
  have h : (C 4 * X * (1 - X) : ℂ[X]) - C ((C 4 * X * (1 - X) : ℂ[X]).eval 2⁻¹) =
      C (-4) * (X - C 2⁻¹) ^ 2 :=
    Polynomial.funext fun z ↦ by
      simp only [eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
      ring
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X,
    localMultiplicity_onePointMap_eval_coe natDegree_four_mul_X_mul_one_sub_X_pos, h,
    rootMultiplicity_mul_X_sub_C_pow (by simp), rootMultiplicity_C, zero_add]

/-- The map `z ↦ 4z(1 - z)` is ramified of index `2` at `∞`, the only point over `∞`. -/
@[simp]
theorem localMultiplicity_onePointMap_four_mul_mul_one_sub_infty :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) (∞ : OnePoint ℂ) = 2 := by
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X,
    localMultiplicity_onePointMap_eval_infty natDegree_four_mul_X_mul_one_sub_X_pos,
    natDegree_four_mul_X_mul_one_sub_X]

/-- The branch values of `z ↦ 4z(1 - z)` are exactly `1` and `∞`: its only critical point is
`1/2`, with critical value `1`. -/
theorem branchValues_spherePolynomial_four_mul_X_mul_one_sub_X :
    (FiniteHolomorphicMap.spherePolynomial natDegree_four_mul_X_mul_one_sub_X_pos).branchValues =
      {((1 : ℂ) : OnePoint ℂ), ∞} := by
  have h : {z : ℂ | (derivative (C 4 * X * (1 - X) : ℂ[X])).IsRoot z} = {2⁻¹} :=
    Set.ext fun _ ↦ isRoot_derivative_four_mul_X_mul_one_sub_X_iff
  rw [FiniteHolomorphicMap.branchValues_spherePolynomial
      (by rw [natDegree_four_mul_X_mul_one_sub_X]; exact one_lt_two), h, image_singleton,
    pair_comm]
  norm_num

end FourMulMulOneSub

end TauCeti.RiemannSurface
