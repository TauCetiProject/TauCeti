/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Torus
public import TauCeti.Analysis.Complex.RiemannSurface.SphereMap
import TauCeti.Algebra.Module.ZLattice.Quotient
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Pair
import TauCeti.Geometry.Manifold.Instances.Quotient

/-!
# The Weierstrass `℘` function as a degree-two map from a torus to the sphere

Let `L` be a period pair and `X = ℂ / L` the complex torus, the orbit space
`AddAction.orbitRel.Quotient L.lattice ℂ` with its quotient complex structure. The Weierstrass
function `℘` is periodic, so it descends to `PeriodPair.torusWeierstrassP L : X → ℂ`. It is
meromorphic on `X` (`PeriodPair.meromorphicAt_torusWeierstrassP`), with a double pole at the
class of `0` and no other poles, so it defines a finite holomorphic map
`PeriodPair.weierstrassSphereMap L : X → ℙ¹` to the Riemann sphere whose only point over `∞` is
the class of `0`.

The double pole gives local multiplicity `2` over `∞`
(`PeriodPair.localMultiplicity_weierstrassSphereMap_zero`), so the map has degree `2`
(`PeriodPair.degree_weierstrassSphereMap`). The zero divisor is canonical on `X`, so
Riemann–Hurwitz over the sphere, `deg K = -2 deg f + deg R_f`, gives ramification degree `4`
(`PeriodPair.ramificationDegree_weierstrassSphereMap`). Since `℘` is even and periodic, the map
is invariant under `x ↦ -x` and so is not injective near any of the four half-period points
`0, ω₁/2, ω₂/2, (ω₁ + ω₂)/2` (`PeriodPair.torusHalfPeriods`). These are four distinct points
(`PeriodPair.ncard_torusHalfPeriods`), so the ramification degree `4` forces simple ramification
at each of them and nowhere else
(`PeriodPair.setOf_one_lt_localMultiplicity_weierstrassSphereMap`).

This is the genus-one Check of the canonical-divisor form of Riemann–Hurwitz: a degree-two map
from a torus branched at four points gives `0 = -2 · 2 + 4`, where `0` is the degree of every
canonical divisor of the torus. The comparison with the analytic and topological genus is not
made here.

## Main declarations

* `PeriodPair.torusWeierstrassP`: `℘` on the torus `ℂ / L`.
* `PeriodPair.weierstrassSphereMap`: the finite holomorphic map `ℂ / L → ℙ¹` defined by `℘`.
* `PeriodPair.weierstrassSphereMap_eq_infty_iff`: its only pole is the class of `0`.
* `PeriodPair.mk_mem_torusHalfPeriods_iff` and
  `PeriodPair.mem_torusHalfPeriods_iff_two_nsmul_eq_zero`: the half-period points are the classes
  of the points `z` with `2 z ∈ L`, that is, the `2`-torsion points of the torus.
* `PeriodPair.degree_weierstrassSphereMap`: it has degree `2`.
* `PeriodPair.ramificationDegree_weierstrassSphereMap`: it has ramification degree `4`.
* `PeriodPair.localMultiplicity_weierstrassSphereMap_of_mem` and
  `PeriodPair.localMultiplicity_weierstrassSphereMap_of_notMem`: it has local multiplicity `2`
  at the four half-period points and `1` everywhere else.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §1 (the Weierstrass `℘` function as a map to
  the sphere).
-/

public noncomputable section

open Filter Function OnePoint Set Topology TauCeti.RiemannSurface

open scoped Manifold

namespace PeriodPair

open TauCeti.AlgebraicGeometry

variable (L : PeriodPair)

/-- The orbit projection `ℂ → ℂ / L`. -/
local notation "mk" => Quotient.mk (AddAction.orbitRel L.lattice ℂ)

/-! ### The Weierstrass function on the torus -/

/-- **The Weierstrass function on the torus** `ℂ / L`: the descent of the lattice-periodic
function `℘[L]`. Its value at the class of `0` is the junk value `℘[L] 0 = 0`. -/
def torusWeierstrassP : AddAction.orbitRel.Quotient L.lattice ℂ → ℂ :=
  Quotient.lift ℘[L] fun z w h ↦ by
    obtain ⟨l, rfl⟩ := h
    simp only [Submodule.vadd_def, vadd_eq_add]
    rw [add_comm, weierstrassP_add_coe]

@[simp]
theorem torusWeierstrassP_mk (z : ℂ) : L.torusWeierstrassP (mk z) = ℘[L] z :=
  (rfl)

/-- The Weierstrass function on the torus takes the junk value `0` at the class of `0`. -/
@[simp]
theorem torusWeierstrassP_zero : L.torusWeierstrassP 0 = 0 := by
  rw [← Submodule.orbitRelQuotient_mk_zero L.lattice, torusWeierstrassP_mk, weierstrassP_zero]

/-- The Weierstrass function on the torus is even. -/
@[simp]
theorem torusWeierstrassP_neg (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    L.torusWeierstrassP (-x) = L.torusWeierstrassP x := by
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
  rw [← Submodule.orbitRelQuotient_mk_neg, torusWeierstrassP_mk, torusWeierstrassP_mk,
    weierstrassP_neg]

/-- The Weierstrass function on the torus is meromorphic at every point. -/
theorem meromorphicAt_torusWeierstrassP (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    MeromorphicAt L.torusWeierstrassP x := by
  rw [meromorphicAt_def]
  exact (L.meromorphic_weierstrassP _).congr
    ((TauCeti.comp_chartAt_addQuotient_symm_eventuallyEq L.torusWeierstrassP x).symm.filter_mono
      nhdsWithin_le_nhds)

/-- The order of the Weierstrass function on the torus at `x` is the order of `℘` at the
coordinate of `x`. -/
private theorem meromorphicOrderAt_torusWeierstrassP_eq
    (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    meromorphicOrderAt L.torusWeierstrassP x = _root_.meromorphicOrderAt ℘[L] (chartAt ℂ x x) := by
  rw [meromorphicOrderAt_def]
  exact _root_.meromorphicOrderAt_congr
    ((TauCeti.comp_chartAt_addQuotient_symm_eventuallyEq L.torusWeierstrassP x).filter_mono
      nhdsWithin_le_nhds)

/-- **`℘` has a double pole at the class of `0`.** -/
@[simp]
theorem meromorphicOrderAt_torusWeierstrassP_zero :
    meromorphicOrderAt L.torusWeierstrassP 0 = -2 := by
  rw [meromorphicOrderAt_torusWeierstrassP_eq]
  refine L.order_weierstrassP _ ?_
  rw [← Submodule.orbitRelQuotient_mk_eq_zero_iff, TauCeti.addQuotientMk_chartAt_self]

/-- Away from the class of `0`, the Weierstrass function on the torus is continuous. -/
theorem continuousAt_torusWeierstrassP {x : AddAction.orbitRel.Quotient L.lattice ℂ}
    (hx : x ≠ 0) : ContinuousAt L.torusWeierstrassP x := by
  have hmem : chartAt ℂ x x ∉ L.lattice := by
    rwa [← Submodule.orbitRelQuotient_mk_eq_zero_iff, TauCeti.addQuotientMk_chartAt_self]
  refine ContinuousAt.congr ?_ (TauCeti.eventuallyEq_comp_chartAt_addQuotient _ x).symm
  exact ((L.analyticOnNhd_weierstrassP _ hmem).continuousAt).comp
    ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))

/-- The Weierstrass function on the torus is not constant near the class of `0`. -/
theorem not_eventuallyConst_torusWeierstrassP :
    ¬ EventuallyConst L.torusWeierstrassP (𝓝[≠] 0) :=
  not_eventuallyConst_of_meromorphicOrderAt_ne_zero
    (by rw [meromorphicOrderAt_torusWeierstrassP_zero]; decide)
    (by rw [meromorphicOrderAt_torusWeierstrassP_zero]; decide)

/-! ### The map to the sphere -/

/-- **The Weierstrass map** `ℂ / L → ℙ¹`: the finite holomorphic map to the Riemann sphere defined
by the Weierstrass function on the torus. -/
def weierstrassSphereMap :
    FiniteHolomorphicMap (AddAction.orbitRel.Quotient L.lattice ℂ) (OnePoint ℂ) :=
  .ofMeromorphic L.meromorphicAt_torusWeierstrassP L.not_eventuallyConst_torusWeierstrassP

theorem coe_weierstrassSphereMap :
    ⇑L.weierstrassSphereMap = sphereMap L.torusWeierstrassP :=
  FiniteHolomorphicMap.coe_ofMeromorphic _ _

/-- **The only pole of `℘` on the torus is the class of `0`.** -/
@[simp]
theorem weierstrassSphereMap_eq_infty_iff {x : AddAction.orbitRel.Quotient L.lattice ℂ} :
    L.weierstrassSphereMap x = ∞ ↔ x = 0 := by
  rw [coe_weierstrassSphereMap, sphereMap_eq_infty_iff (L.meromorphicAt_torusWeierstrassP x)]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, meromorphicOrderAt_torusWeierstrassP_zero]; decide⟩
  by_contra hx
  exact (meromorphicOrderAt_nonneg_of_continuousAt (L.continuousAt_torusWeierstrassP hx)).not_gt h

/-- Away from the class of `0`, the Weierstrass map takes the value of `℘`. -/
@[simp]
theorem weierstrassSphereMap_of_ne_zero {x : AddAction.orbitRel.Quotient L.lattice ℂ}
    (hx : x ≠ 0) : L.weierstrassSphereMap x = L.torusWeierstrassP x := by
  rw [coe_weierstrassSphereMap, sphereMap_of_continuousAt (L.continuousAt_torusWeierstrassP hx)]

/-- The Weierstrass map sends the class of `0` to `∞`. -/
theorem weierstrassSphereMap_zero : L.weierstrassSphereMap 0 = ∞ :=
  L.weierstrassSphereMap_eq_infty_iff.2 rfl

/-- The Weierstrass map is invariant under `x ↦ -x`. -/
@[simp]
theorem weierstrassSphereMap_neg (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    L.weierstrassSphereMap (-x) = L.weierstrassSphereMap x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · rw [L.weierstrassSphereMap_of_ne_zero (neg_ne_zero.2 hx), L.weierstrassSphereMap_of_ne_zero hx,
      torusWeierstrassP_neg]

/-- **The Weierstrass map has local multiplicity `2` at the class of `0`**, the order of the pole
of `℘`. -/
theorem localMultiplicity_weierstrassSphereMap_zero :
    localMultiplicity L.weierstrassSphereMap 0 = 2 := by
  have h := L.weierstrassSphereMap.meromorphicOrderAt_affineChart_comp_of_eq_infty
    L.weierstrassSphereMap_zero
  -- Read in the affine coordinate, the Weierstrass map is `℘` away from `0`.
  have hcongr : (fun y ↦ affineChart (L.weierstrassSphereMap y)) =ᶠ[𝓝[≠] 0]
      L.torusWeierstrassP := by
    simpa [coe_weierstrassSphereMap] using
      affineChart_sphereMap_eventuallyEq (L.meromorphicAt_torusWeierstrassP 0)
  rw [meromorphicOrderAt_congr hcongr, meromorphicOrderAt_torusWeierstrassP_zero] at h
  have h' : ((-2 : ℤ) : WithTop ℤ) =
      ((-(localMultiplicity L.weierstrassSphereMap 0 : ℤ) : ℤ) : WithTop ℤ) := h
  have := WithTop.coe_injective h'
  omega

/-- The fibre of the Weierstrass map over `∞` is the class of `0`. -/
private theorem toFinset_finite_fiber_infty :
    (L.weierstrassSphereMap.finite_fiber ∞).toFinset = {0} := by
  ext x
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
    Finset.mem_singleton, weierstrassSphereMap_eq_infty_iff]

/-- **The Weierstrass map has degree `2`.** -/
@[simp]
theorem degree_weierstrassSphereMap : degree L.weierstrassSphereMap = 2 := by
  rw [degree_eq_fiber_sum _ ∞, toFinset_finite_fiber_infty, Finset.sum_singleton,
    localMultiplicity_weierstrassSphereMap_zero]

/-- **The Weierstrass map has ramification degree `4`**, by Riemann–Hurwitz over the sphere for
the canonical divisor `0` of the torus. -/
@[simp]
theorem ramificationDegree_weierstrassSphereMap :
    ramificationDegree L.weierstrassSphereMap = 4 := by
  have h := isCanonicalDivisor_zero_torus.degree_eq_neg_two_mul_degree_add_ramificationDegree
    L.weierstrassSphereMap
  rw [map_zero, degree_weierstrassSphereMap] at h
  omega

/-! ### The branch points -/

/-- The four **half-period points** `0`, `ω₁/2`, `ω₂/2`, `(ω₁ + ω₂)/2` of the torus `ℂ / L`. -/
def torusHalfPeriods : Set (AddAction.orbitRel.Quotient L.lattice ℂ) :=
  {0, mk (L.ω₁ / 2), mk (L.ω₂ / 2), mk ((L.ω₁ + L.ω₂) / 2)}

theorem torusHalfPeriods_def :
    L.torusHalfPeriods = {0, mk (L.ω₁ / 2), mk (L.ω₂ / 2), mk ((L.ω₁ + L.ω₂) / 2)} :=
  (rfl)

/-- A point of the torus is a half-period point when it is one of the four classes `0`, `ω₁/2`,
`ω₂/2`, `(ω₁ + ω₂)/2`. -/
@[simp]
theorem mem_torusHalfPeriods_iff {x : AddAction.orbitRel.Quotient L.lattice ℂ} :
    x ∈ L.torusHalfPeriods ↔
      x = 0 ∨ x = mk (L.ω₁ / 2) ∨ x = mk (L.ω₂ / 2) ∨ x = mk ((L.ω₁ + L.ω₂) / 2) :=
  .rfl

/-- A rational combination `α ω₁ + β ω₂` with a non-integral coefficient is not a period. -/
private theorem rat_combination_notMem {α β : ℚ} (h : α.den ≠ 1 ∨ β.den ≠ 1) {z : ℂ}
    (hz : z = α * L.ω₁ + β * L.ω₂) : z ∉ L.lattice := by
  rw [hz, mul_ω₁_add_mul_ω₂_mem_lattice]
  tauto

/-- The four half-period points are distinct. -/
private theorem halfPeriods_pairwise_ne :
    (0 : AddAction.orbitRel.Quotient L.lattice ℂ) ≠ mk (L.ω₁ / 2) ∧
      (0 : AddAction.orbitRel.Quotient L.lattice ℂ) ≠ mk (L.ω₂ / 2) ∧
      (0 : AddAction.orbitRel.Quotient L.lattice ℂ) ≠ mk ((L.ω₁ + L.ω₂) / 2) ∧
      mk (L.ω₁ / 2) ≠ mk (L.ω₂ / 2) ∧ mk (L.ω₁ / 2) ≠ mk ((L.ω₁ + L.ω₂) / 2) ∧
      mk (L.ω₂ / 2) ≠ mk ((L.ω₁ + L.ω₂) / 2) := by
  simp only [ne_eq, eq_comm (a := (0 : AddAction.orbitRel.Quotient L.lattice ℂ)),
    Submodule.orbitRelQuotient_mk_eq_zero_iff, Submodule.orbitRelQuotient_mk_eq_mk_iff]
  refine ⟨L.ω₁_div_two_notMem_lattice, L.ω₂_div_two_notMem_lattice,
    rat_combination_notMem L (α := 1 / 2) (β := 1 / 2) (by simp) (by push_cast; ring),
    rat_combination_notMem L (α := 1 / 2) (β := -1 / 2) (by norm_num) (by push_cast; ring),
    rat_combination_notMem L (α := 0) (β := -1 / 2) (by norm_num) (by push_cast; ring),
    rat_combination_notMem L (α := -1 / 2) (β := 0) (by norm_num) (by push_cast; ring)⟩

/-- There are exactly four half-period points. -/
@[simp]
theorem ncard_torusHalfPeriods : L.torusHalfPeriods.ncard = 4 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := L.halfPeriods_pairwise_ne
  rw [torusHalfPeriods, ncard_insert_of_notMem (by simp [h₁, h₂, h₃]),
    ncard_insert_of_notMem (by simp [h₄, h₅]), ncard_pair h₆]

/-- The half-period points are the classes of the points `h` with `2 h ∈ L`. -/
private theorem two_mul_mem_lattice_of_mem_torusHalfPeriods
    {x : AddAction.orbitRel.Quotient L.lattice ℂ} (hx : x ∈ L.torusHalfPeriods) :
    ∃ h : ℂ, 2 * h ∈ L.lattice ∧ mk h = x := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp, Submodule.orbitRelQuotient_mk_zero _⟩
  · exact ⟨_, by simpa [mul_div_cancel₀] using L.ω₁_mem_lattice, rfl⟩
  · exact ⟨_, by simpa [mul_div_cancel₀] using L.ω₂_mem_lattice, rfl⟩
  · exact ⟨_, by simpa [mul_div_cancel₀] using add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice, rfl⟩

/-- **The half-period points are the classes of the points `z` with `2 z ∈ L`.** -/
theorem mk_mem_torusHalfPeriods_iff (z : ℂ) : mk z ∈ L.torusHalfPeriods ↔ 2 * z ∈ L.lattice := by
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · obtain ⟨h, h2, hh⟩ := L.two_mul_mem_lattice_of_mem_torusHalfPeriods hz
    rw [Submodule.orbitRelQuotient_mk_eq_mk_iff] at hh
    convert L.lattice.sub_mem h2 (L.lattice.smul_mem (2 : ℤ) hh) using 1
    rw [zsmul_eq_mul]
    push_cast
    ring
  -- Writing `2 z = m ω₁ + n ω₂`, the class of `z` is that of `(m % 2) ω₁ / 2 + (n % 2) ω₂ / 2`.
  obtain ⟨m, n, e⟩ := mem_lattice.1 hz
  have hm : (m : ℂ) = ((m % 2 : ℤ) : ℂ) + 2 * ((m / 2 : ℤ) : ℂ) := by
    exact_mod_cast (by omega : m = m % 2 + 2 * (m / 2))
  have hn : (n : ℂ) = ((n % 2 : ℤ) : ℂ) + 2 * ((n / 2 : ℤ) : ℂ) := by
    exact_mod_cast (by omega : n = n % 2 + 2 * (n / 2))
  have hmk : mk z = mk (((m % 2 : ℤ) : ℂ) / 2 * L.ω₁ + ((n % 2 : ℤ) : ℂ) / 2 * L.ω₂) := by
    rw [Submodule.orbitRelQuotient_mk_eq_mk_iff, mem_lattice]
    exact ⟨m / 2, n / 2, by linear_combination e / 2 - (L.ω₁ / 2) * hm - (L.ω₂ / 2) * hn⟩
  rw [hmk, mem_torusHalfPeriods_iff]
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2 <;>
    rcases Int.emod_two_eq_zero_or_one n with hn2 | hn2 <;>
    simp only [hm2, hn2, Int.cast_zero, Int.cast_one]
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inl (congrArg mk (by ring))))
  · exact Or.inr (Or.inl (congrArg mk (by ring)))
  · exact Or.inr (Or.inr (Or.inr (congrArg mk (by ring))))

/-- **The half-period points are the `2`-torsion points of the torus.** -/
theorem mem_torusHalfPeriods_iff_two_nsmul_eq_zero (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    x ∈ L.torusHalfPeriods ↔ 2 • x = 0 := by
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective x
  rw [mk_mem_torusHalfPeriods_iff, two_nsmul, ← Submodule.orbitRelQuotient_mk_add,
    Submodule.orbitRelQuotient_mk_eq_zero_iff, two_mul]

/-- **The Weierstrass map is ramified at a nonzero half-period point.** Since `℘` is even and
periodic, it takes the same value at `z` and at `2 h - z`, and these have distinct classes for
`z ≠ h` near `h`, so the map is injective on no neighbourhood of the class of `h`. -/
private theorem one_lt_localMultiplicity_weierstrassSphereMap_of_two_mul_mem {h : ℂ}
    (h2 : 2 * h ∈ L.lattice) (hh : h ∉ L.lattice) :
    1 < localMultiplicity L.weierstrassSphereMap (mk h) := by
  set f := L.weierstrassSphereMap
  refine lt_of_le_of_ne (localMultiplicity_pos f (mk h)) fun h1 ↦ ?_
  obtain ⟨U, hU, hinj⟩ :=
    (localMultiplicity_eq_one_iff (.of_forall fun y ↦ f.holomorphic y)).1 h1.symm
  have hx0 : mk h ≠ 0 := by rwa [Ne, Submodule.orbitRelQuotient_mk_eq_zero_iff]
  -- `V` is a neighbourhood of `mk h` in `U` avoiding the pole.
  set V := U ∩ {y | y ≠ 0}
  have hV : V ∈ 𝓝 (mk h) := inter_mem hU (isOpen_ne.mem_nhds hx0)
  have hcont : Continuous mk := continuous_quotient_mk'
  have hA : mk ⁻¹' V ∈ 𝓝 h := hcont.continuousAt.preimage_mem_nhds hV
  have hB : (fun z ↦ 2 * h - z) ⁻¹' (mk ⁻¹' V) ∈ 𝓝 h := by
    refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa [two_mul] using hA
  have hC : ∀ᶠ z in 𝓝[≠] h, 2 * z ∉ L.lattice :=
    ((Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).map_punctured_nhds_eq h).le
      (L.eventually_notMem_lattice (2 * h))
  have hAB : ∀ᶠ z in 𝓝[≠] h, z ∈ mk ⁻¹' V ∩ (fun z ↦ 2 * h - z) ⁻¹' (mk ⁻¹' V) :=
    nhdsWithin_le_nhds (inter_mem hA hB)
  obtain ⟨z, ⟨hzA, hzB⟩, h2z⟩ := (hAB.and hC).exists
  have hzB' : mk (2 * h - z) ∈ V := hzB
  have hfeq : f (mk z) = f (mk (2 * h - z)) := by
    rw [L.weierstrassSphereMap_of_ne_zero hzA.2, L.weierstrassSphereMap_of_ne_zero hzB'.2,
      torusWeierstrassP_mk, torusWeierstrassP_mk, ← L.weierstrassP_neg (2 * h - z), neg_sub,
      L.weierstrassP_sub_coe z ⟨_, h2⟩]
  have heq := hinj hzA.1 hzB'.1 hfeq
  rw [Submodule.orbitRelQuotient_mk_eq_mk_iff] at heq
  refine h2z ?_
  convert add_mem heq h2 using 1
  ring

/-- The Weierstrass map is ramified at every half-period point. -/
private theorem one_lt_localMultiplicity_weierstrassSphereMap_of_mem
    {x : AddAction.orbitRel.Quotient L.lattice ℂ} (hx : x ∈ L.torusHalfPeriods) :
    1 < localMultiplicity L.weierstrassSphereMap x := by
  by_cases hx0 : x = 0
  · rw [hx0, localMultiplicity_weierstrassSphereMap_zero]
    norm_num
  obtain ⟨h, h2, rfl⟩ := L.two_mul_mem_lattice_of_mem_torusHalfPeriods hx
  exact L.one_lt_localMultiplicity_weierstrassSphereMap_of_two_mul_mem h2
    (by rwa [Submodule.orbitRelQuotient_mk_eq_zero_iff] at hx0)

open Classical in
/-- The ramification degree `4` is concentrated at the four half-period points, one at each. -/
private theorem localMultiplicity_weierstrassSphereMap_sub_one (x :
    AddAction.orbitRel.Quotient L.lattice ℂ) :
    localMultiplicity L.weierstrassSphereMap x - 1 = if x ∈ L.torusHalfPeriods then 1 else 0 := by
  classical
  set f := L.weierstrassSphereMap
  set g : AddAction.orbitRel.Quotient L.lattice ℂ → ℕ := fun x ↦ localMultiplicity f x - 1
  have hfin := f.finite_support_localMultiplicity_sub_one
  set s := hfin.toFinset
  set t : Finset (AddAction.orbitRel.Quotient L.lattice ℂ) :=
    {0, mk (L.ω₁ / 2), mk (L.ω₂ / 2), mk ((L.ω₁ + L.ω₂) / 2)}
  have ht : ∀ y, y ∈ t ↔ y ∈ L.torusHalfPeriods := fun y ↦ by simp [t, torusHalfPeriods]
  have htcard : t.card = 4 := by
    rw [← Set.ncard_coe_finset, show (t : Set _) = L.torusHalfPeriods from Set.ext ht,
      ncard_torusHalfPeriods]
  have hgt : ∀ y ∈ t, 1 ≤ g y := fun y hy ↦
    Nat.le_sub_one_of_lt (L.one_lt_localMultiplicity_weierstrassSphereMap_of_mem ((ht y).1 hy))
  have hts : t ⊆ s := fun y hy ↦ hfin.mem_toFinset.2 (Nat.one_le_iff_ne_zero.1 (hgt y hy))
  have hsum : ∑ y ∈ s, g y = 4 := by
    rw [← finsum_eq_sum g hfin, ← ramificationDegree_def, ramificationDegree_weierstrassSphereMap]
  have hsplit := Finset.sum_sdiff hts (f := g)
  have hlow : t.card ≤ ∑ y ∈ t, g y := by
    simpa using Finset.card_nsmul_le_sum t g 1 hgt
  have hrest : ∑ y ∈ s \ t, g y = 0 := by omega
  have htsum : ∑ y ∈ t, g y = ∑ _y ∈ t, 1 := by simp; omega
  split_ifs with hx
  · exact ((Finset.sum_eq_sum_iff_of_le hgt).1 htsum.symm x ((ht x).2 hx)).symm
  · by_cases hxs : x ∈ s
    · exact Finset.sum_eq_zero_iff.1 hrest x (Finset.mem_sdiff.2 ⟨hxs, fun h ↦ hx ((ht x).1 h)⟩)
    · simpa [s, g] using hxs

/-- **The Weierstrass map has local multiplicity `2` at each half-period point.** -/
@[simp]
theorem localMultiplicity_weierstrassSphereMap_of_mem
    {x : AddAction.orbitRel.Quotient L.lattice ℂ} (hx : x ∈ L.torusHalfPeriods) :
    localMultiplicity L.weierstrassSphereMap x = 2 := by
  have h := L.localMultiplicity_weierstrassSphereMap_sub_one x
  simp only [hx, ↓reduceIte] at h
  omega

/-- **The Weierstrass map is unramified away from the half-period points.** -/
@[simp]
theorem localMultiplicity_weierstrassSphereMap_of_notMem
    {x : AddAction.orbitRel.Quotient L.lattice ℂ} (hx : x ∉ L.torusHalfPeriods) :
    localMultiplicity L.weierstrassSphereMap x = 1 := by
  have h := L.localMultiplicity_weierstrassSphereMap_sub_one x
  have hpos := localMultiplicity_pos L.weierstrassSphereMap x
  simp only [hx, ↓reduceIte] at h
  omega

/-- **The branch points of the Weierstrass map are the four half-period points.** -/
@[simp]
theorem setOf_one_lt_localMultiplicity_weierstrassSphereMap :
    {x | 1 < localMultiplicity L.weierstrassSphereMap x} = L.torusHalfPeriods := by
  ext x
  by_cases hx : x ∈ L.torusHalfPeriods
  · simp [hx, localMultiplicity_weierstrassSphereMap_of_mem]
  · simp [hx, localMultiplicity_weierstrassSphereMap_of_notMem]

/-- **The genus-one Check of Riemann–Hurwitz.** The Weierstrass map is a degree-two map from the
torus to the sphere, branched at four points, and every canonical divisor `K` of the torus
satisfies `deg K = -2 deg f + deg R_f` as `0 = -2 · 2 + 4`. -/
example {K : WeilDivisor (AddAction.orbitRel.Quotient L.lattice ℂ)} (hK : IsCanonicalDivisor K) :
    WeilDivisor.degree K = 0 ∧ degree L.weierstrassSphereMap = 2 ∧
      L.torusHalfPeriods.ncard = 4 ∧ ramificationDegree L.weierstrassSphereMap = 4 ∧
      WeilDivisor.degree K =
        -2 * (degree L.weierstrassSphereMap : ℤ) + ramificationDegree L.weierstrassSphereMap :=
  ⟨degree_eq_zero_of_isCanonicalDivisor_torus hK, L.degree_weierstrassSphereMap,
    L.ncard_torusHalfPeriods, L.ramificationDegree_weierstrassSphereMap,
    hK.degree_eq_neg_two_mul_degree_add_ramificationDegree _⟩

end PeriodPair
