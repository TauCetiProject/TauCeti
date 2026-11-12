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
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction
import TauCeti.Analysis.SpecialFunctions.Elliptic.PeriodPair
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
    change ℘[L] ((l : ℂ) + w) = ℘[L] w
    rw [add_comm, weierstrassP_add_coe]

@[simp]
theorem torusWeierstrassP_mk (z : ℂ) : L.torusWeierstrassP (mk z) = ℘[L] z :=
  (rfl)

variable {L}

/-- The inverse of the chart of `ℂ / L` at `x` is the orbit projection on the chart target. -/
private theorem symm_chartAt_eq_mk (x : AddAction.orbitRel.Quotient L.lattice ℂ) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) : (chartAt ℂ x).symm w = mk w := by
  obtain ⟨z, hz⟩ := TauCeti.exists_symm_eq_addQuotientMk_of_mem_atlas_addQuotient
    (chart_mem_atlas ℂ x)
  simpa [chartAt_self_eq] using (hz w hw).2

/-- The coordinate of `x` in its chart is a representative of `x`. -/
private theorem mk_chartAt_self (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    mk (chartAt ℂ x x) = x := by
  rw [← symm_chartAt_eq_mk x ((chartAt ℂ x).map_source (mem_chart_source ℂ x)),
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]

/-- Read in the chart at `x`, a function on `ℂ / L` is its pullback to `ℂ`. -/
private theorem comp_symm_chartAt_eventuallyEq {E : Type*}
    (F : AddAction.orbitRel.Quotient L.lattice ℂ → E)
    (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    F ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)] F ∘ mk := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with w hw
  simp [symm_chartAt_eq_mk x hw]

/-- Near `x`, a function on `ℂ / L` is its pullback to `ℂ` composed with the chart at `x`. -/
private theorem eventuallyEq_comp_chartAt {E : Type*}
    (F : AddAction.orbitRel.Quotient L.lattice ℂ → E)
    (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    F =ᶠ[𝓝 x] (F ∘ mk) ∘ chartAt ℂ x := by
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp [← symm_chartAt_eq_mk x ((chartAt ℂ x).map_source hy), (chartAt ℂ x).left_inv hy]

variable (L)

/-- The Weierstrass function on the torus is meromorphic at every point. -/
theorem meromorphicAt_torusWeierstrassP (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    MeromorphicAt L.torusWeierstrassP x := by
  rw [meromorphicAt_def]
  exact (L.meromorphic_weierstrassP _).congr
    ((comp_symm_chartAt_eventuallyEq L.torusWeierstrassP x).symm.filter_mono nhdsWithin_le_nhds)

/-- The order of the Weierstrass function on the torus at `x` is the order of `℘` at the
coordinate of `x`. -/
private theorem meromorphicOrderAt_torusWeierstrassP_eq
    (x : AddAction.orbitRel.Quotient L.lattice ℂ) :
    meromorphicOrderAt L.torusWeierstrassP x = _root_.meromorphicOrderAt ℘[L] (chartAt ℂ x x) := by
  rw [meromorphicOrderAt_def]
  exact _root_.meromorphicOrderAt_congr
    ((comp_symm_chartAt_eventuallyEq L.torusWeierstrassP x).filter_mono nhdsWithin_le_nhds)

/-- **`℘` has a double pole at the class of `0`.** -/
@[simp]
theorem meromorphicOrderAt_torusWeierstrassP_zero :
    meromorphicOrderAt L.torusWeierstrassP 0 = -2 := by
  rw [meromorphicOrderAt_torusWeierstrassP_eq]
  refine L.order_weierstrassP _ ?_
  rw [← Submodule.orbitRelQuotient_mk_eq_zero_iff, mk_chartAt_self]

/-- Away from the class of `0`, the Weierstrass function on the torus is continuous. -/
theorem continuousAt_torusWeierstrassP {x : AddAction.orbitRel.Quotient L.lattice ℂ}
    (hx : x ≠ 0) : ContinuousAt L.torusWeierstrassP x := by
  have hmem : chartAt ℂ x x ∉ L.lattice := by
    rwa [← Submodule.orbitRelQuotient_mk_eq_zero_iff, mk_chartAt_self]
  refine ContinuousAt.congr ?_ (eventuallyEq_comp_chartAt _ x).symm
  exact ((L.analyticOnNhd_weierstrassP _ hmem).continuousAt).comp
    ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))

/-- The Weierstrass function on the torus is not constant near the class of `0`. -/
theorem not_eventuallyConst_torusWeierstrassP :
    ¬ EventuallyConst L.torusWeierstrassP (𝓝[≠] 0) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 h
  have hord := TauCeti.RiemannSurface.meromorphicOrderAt_congr hc
  rw [meromorphicOrderAt_torusWeierstrassP_zero,
    TauCeti.RiemannSurface.meromorphicOrderAt_const] at hord
  split_ifs at hord <;> simp at hord

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
theorem weierstrassSphereMap_eq_infty_iff {x : AddAction.orbitRel.Quotient L.lattice ℂ} :
    L.weierstrassSphereMap x = ∞ ↔ x = 0 := by
  rw [coe_weierstrassSphereMap, sphereMap_eq_infty_iff (L.meromorphicAt_torusWeierstrassP x)]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, meromorphicOrderAt_torusWeierstrassP_zero]; decide⟩
  by_contra hx
  exact (meromorphicOrderAt_nonneg_of_continuousAt (L.continuousAt_torusWeierstrassP hx)).not_gt h

/-- Away from the class of `0`, the Weierstrass map takes the value of `℘`. -/
theorem weierstrassSphereMap_of_ne_zero {x : AddAction.orbitRel.Quotient L.lattice ℂ}
    (hx : x ≠ 0) : L.weierstrassSphereMap x = L.torusWeierstrassP x := by
  rw [coe_weierstrassSphereMap, sphereMap_of_continuousAt (L.continuousAt_torusWeierstrassP hx)]

/-- **The Weierstrass map has local multiplicity `2` at the class of `0`**, the order of the pole
of `℘`. -/
@[simp]
theorem localMultiplicity_weierstrassSphereMap_zero :
    localMultiplicity L.weierstrassSphereMap 0 = 2 := by
  set f := L.weierstrassSphereMap
  have hf0 : f 0 = ∞ := L.weierstrassSphereMap_eq_infty_iff.2 rfl
  -- The affine coordinate is meromorphic at `∞`, with a simple pole there.
  have hmer : MeromorphicAt (affineChart : OnePoint ℂ → ℂ) (f 0) := by
    rw [hf0, ← MeromorphicFunction.finitePart_coordinate]
    exact MeromorphicFunction.coordinate.meromorphicAt_finitePart _
  have h := meromorphicOrderAt_comp hmer (.of_forall fun y ↦ f.holomorphic y)
    (f.not_eventuallyConst 0)
  -- Read in the affine coordinate, `f` is `℘` away from `0`.
  have hcongr : (affineChart : OnePoint ℂ → ℂ) ∘ f =ᶠ[𝓝[≠] 0] L.torusWeierstrassP := by
    simpa [f, Function.comp_def, coe_weierstrassSphereMap] using
      affineChart_sphereMap_eventuallyEq (L.meromorphicAt_torusWeierstrassP 0)
  rw [meromorphicOrderAt_congr hcongr, meromorphicOrderAt_torusWeierstrassP_zero, hf0,
    meromorphicOrderAt_affineChart_infty] at h
  have h' : ((-2 : ℤ) : WithTop ℤ) = ((-1 * (localMultiplicity f 0 : ℤ) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_mul]
    exact h
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

/-- **The Weierstrass map is ramified at a nonzero half-period point.** Since `℘` is even and
periodic, it takes the same value at `z` and at `2 h - z`, and these have distinct classes for
`z ≠ h` near `h`, so the map is injective on no neighbourhood of the class of `h`. -/
private theorem one_lt_localMultiplicity_weierstrassSphereMap_of_two_mul_mem {h : ℂ}
    (h2 : 2 * h ∈ L.lattice) (hh : h ∉ L.lattice) :
    1 < localMultiplicity L.weierstrassSphereMap (mk h) := by
  set f := L.weierstrassSphereMap
  have hmd : ∀ᶠ y in 𝓝 (mk h), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y :=
    .of_forall fun y ↦ f.holomorphic y
  have hpos := (localMultiplicity_pos_iff hmd).2 (f.not_eventuallyConst _)
  refine lt_of_le_of_ne hpos fun h1 ↦ ?_
  obtain ⟨U, hU, hinj⟩ := (localMultiplicity_eq_one_iff hmd).1 h1.symm
  have hx0 : mk h ≠ 0 := by rwa [Ne, Submodule.orbitRelQuotient_mk_eq_zero_iff]
  -- `V` is a neighbourhood of `mk h` in `U` avoiding the pole.
  set V := U ∩ {y | y ≠ 0}
  have hV : V ∈ 𝓝 (mk h) := inter_mem hU (isOpen_ne.mem_nhds hx0)
  have hcont : Continuous mk := continuous_quotient_mk'
  have hA : mk ⁻¹' V ∈ 𝓝 h := hcont.continuousAt.preimage_mem_nhds hV
  have hB : (fun z ↦ 2 * h - z) ⁻¹' (mk ⁻¹' V) ∈ 𝓝 h := by
    refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa [two_mul] using hA
  have hC : (fun z ↦ 2 * z) ⁻¹' (↑L.lattice \ {2 * h})ᶜ ∈ 𝓝 h :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      (L.compl_lattice_sdiff_singleton_mem_nhds _)
  have hall : ∀ᶠ z in 𝓝[≠] h, z ∈ mk ⁻¹' V ∩ ((fun z ↦ 2 * h - z) ⁻¹' (mk ⁻¹' V) ∩
      (fun z ↦ 2 * z) ⁻¹' (↑L.lattice \ {2 * h})ᶜ) :=
    nhdsWithin_le_nhds (inter_mem hA (inter_mem hB hC))
  obtain ⟨z, hzh, hzA, hzB, hzC⟩ := (eventually_mem_nhdsWithin.and hall).exists
  rw [mem_compl_singleton_iff] at hzh
  have h2z : 2 * z ∉ L.lattice := fun hm ↦
    hzC ⟨hm, fun heq ↦ hzh (mul_left_cancel₀ two_ne_zero heq)⟩
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
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := L.halfPeriods_pairwise_ne
  set t : Finset (AddAction.orbitRel.Quotient L.lattice ℂ) :=
    {0, mk (L.ω₁ / 2), mk (L.ω₂ / 2), mk ((L.ω₁ + L.ω₂) / 2)}
  have ht : ∀ y, y ∈ t ↔ y ∈ L.torusHalfPeriods := fun y ↦ by simp [t, torusHalfPeriods]
  have htcard : t.card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h₁, h₂, h₃]),
      Finset.card_insert_of_notMem (by simp [h₄, h₅]), Finset.card_pair h₆]
  have hgt : ∀ y ∈ t, 1 ≤ g y := fun y hy ↦
    Nat.le_sub_one_of_lt (L.one_lt_localMultiplicity_weierstrassSphereMap_of_mem ((ht y).1 hy))
  have hts : t ⊆ s := fun y hy ↦ hfin.mem_toFinset.2 (Nat.one_le_iff_ne_zero.1 (hgt y hy))
  have hsum : ∑ y ∈ s, g y = 4 := by
    rw [← finsum_eq_sum_of_support_subset g
      fun y hy ↦ Finset.mem_coe.2 (hfin.mem_toFinset.2 hy), ← ramificationDegree_def,
      ramificationDegree_weierstrassSphereMap]
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
theorem localMultiplicity_weierstrassSphereMap_of_mem
    {x : AddAction.orbitRel.Quotient L.lattice ℂ} (hx : x ∈ L.torusHalfPeriods) :
    localMultiplicity L.weierstrassSphereMap x = 2 := by
  have h := L.localMultiplicity_weierstrassSphereMap_sub_one x
  simp only [hx, ↓reduceIte] at h
  omega

/-- **The Weierstrass map is unramified away from the half-period points.** -/
theorem localMultiplicity_weierstrassSphereMap_of_notMem
    {x : AddAction.orbitRel.Quotient L.lattice ℂ} (hx : x ∉ L.torusHalfPeriods) :
    localMultiplicity L.weierstrassSphereMap x = 1 := by
  have h := L.localMultiplicity_weierstrassSphereMap_sub_one x
  have hpos := (localMultiplicity_pos_iff (.of_forall fun y ↦
    L.weierstrassSphereMap.holomorphic y)).2 (L.weierstrassSphereMap.not_eventuallyConst x)
  simp only [hx, ↓reduceIte] at h
  omega

/-- **The branch points of the Weierstrass map are the four half-period points.** -/
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
