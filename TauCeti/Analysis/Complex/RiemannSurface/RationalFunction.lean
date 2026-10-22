/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.Topology.Compactification.OnePoint.Nhds

/-!
# The meromorphic functions on the Riemann sphere are the rational functions

The coordinate `z` of the Riemann sphere `OnePoint ℂ`, that is the identity map, is a meromorphic
function with a simple pole at `∞` (`TauCeti.RiemannSurface.MeromorphicFunction.coordinate`). A
polynomial `p` evaluated at it is the meromorphic function whose value at a finite point `z` is
`p(z)`, and it vanishes identically only when `p = 0`. So evaluation at the coordinate extends to
the field of rational functions, and this file shows that it is an isomorphism of `ℂ`-algebras

```text
ℂ(X) ≃ₐ[ℂ] M(OnePoint ℂ),        X ↦ z
```

(`TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`): every meromorphic function on the
Riemann sphere is a rational function of the coordinate.

Surjectivity is the classical argument with the divisor. A nonzero meromorphic function `f` on the
sphere has finitely many zeros and poles, since the sphere is compact. On `ℂ` its finite part is
therefore the product of `∏ (z - u) ^ d(u)`, over its finitely many zeros and poles `u` with
`d(u)` the order of `f` at `u`, and an analytic function `g` without zeros
(`MeromorphicOn.extract_zeros_poles`). The quotient `G` of `f` by the rational function
`∏ (z - u) ^ d(u)` is then finite and nonzero at every point of `ℂ`. If `G` is finite at `∞` it
has no poles, and if `G` has a pole at `∞` then `1 / G` has none; in both cases the maximum
principle on the compact sphere
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_algebraMap_eq_of_forall_ne_infty`) shows that
`G` is constant, so `f` is rational.

This identifies the field of meromorphic functions on the sphere with the rational function field
`ℂ(t)`, the base field over which the meromorphic functions on a compact Riemann surface with a
nonconstant holomorphic map to the sphere are studied algebraically.

## Main definitions

* `TauCeti.RiemannSurface.MeromorphicFunction.coordinate`: the coordinate `z` of the Riemann sphere
  as a meromorphic function.
* `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`: the isomorphism of `ℂ`-algebras
  between the rational functions over `ℂ` and the meromorphic functions on the Riemann sphere,
  sending `X` to the coordinate.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.aeval_coordinate_apply_coe`: a polynomial evaluated
  at the coordinate takes the value `p(z)` at a finite point `z`.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_algebraMap_eq_of_forall_coe_ne`: a
  meromorphic function on the Riemann sphere with neither zeros nor poles in `ℂ` is constant.
* `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv_apply_coe`: the meromorphic function of
  a rational function `r` takes the value `r(z)` at every finite point `z` at which the denominator
  of `r` does not vanish.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2, Theorem 2.9 (the meromorphic functions on the Riemann sphere are the rational functions).
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Proposition 1.26.
-/

public noncomputable section

open Filter Function OnePoint Polynomial Set Topology

open scoped Manifold nonZeroDivisors

namespace TauCeti.RiemannSurface.MeromorphicFunction

/-! ### The coordinate and polynomials -/

/-- The coordinate `z` of the Riemann sphere: the identity map of `OnePoint ℂ`, as a meromorphic
function. It has a simple pole at `∞`. -/
def coordinate : MeromorphicFunction (OnePoint ℂ) where
  toFun := id
  mdifferentiable' := mdifferentiable_id
  ne_infty' h := OnePoint.coe_ne_infty (0 : ℂ) (congrFun h ((0 : ℂ) : OnePoint ℂ))

@[simp]
theorem coordinate_apply (x : OnePoint ℂ) : coordinate x = x := by
  simp [coordinate]

/-- A polynomial `p` evaluated at the coordinate of the Riemann sphere takes the value `p(z)` at a
finite point `z`. -/
@[simp]
theorem aeval_coordinate_apply_coe (p : ℂ[X]) (z : ℂ) :
    aeval coordinate p (z : OnePoint ℂ) = ↑(p.eval z) := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_apply_of_eq_coe hp hq, eval_add]
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_apply_of_eq_coe h (coordinate_apply _)]
    simp [mul_assoc]

/-- Evaluation of polynomials at the coordinate of the Riemann sphere is injective: a nonzero
polynomial does not vanish at every point of `ℂ`. -/
private theorem aeval_coordinate_injective :
    Injective (aeval coordinate : ℂ[X] →ₐ[ℂ] MeromorphicFunction (OnePoint ℂ)) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ Polynomial.funext fun z ↦ ?_
  have h := aeval_coordinate_apply_coe p z
  rw [hp, coe_zero] at h
  simpa using (coe_injective h).symm

/-- Rational functions as meromorphic functions on the Riemann sphere: evaluation at the
coordinate. -/
private def ofRatFunc : RatFunc ℂ →ₐ[ℂ] MeromorphicFunction (OnePoint ℂ) :=
  RatFunc.liftAlgHom (aeval coordinate)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ aeval_coordinate_injective)

private theorem ofRatFunc_algebraMap (p : ℂ[X]) :
    ofRatFunc (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval coordinate p := by
  simpa [ofRatFunc] using RatFunc.liftAlgHom_apply_div (aeval coordinate)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ aeval_coordinate_injective) p 1

/-! ### Every meromorphic function on the sphere is rational -/

/-- At a finite point `y` outside a finite set `s`, the product of the `(z - u) ^ n u` over `u ∈ s`
takes the value `∏ (y - u) ^ n u`. -/
private theorem prod_coordinate_sub_zpow_apply (s : Finset ℂ) (n : ℂ → ℤ) {y : ℂ} (hy : y ∉ s) :
    (∏ u ∈ s, (coordinate - algebraMap ℂ _ u) ^ n u) (y : OnePoint ℂ) =
      ↑(∏ u ∈ s, (y - u) ^ n u) :=
  prod_apply_of_eq_coe fun u hu ↦ zpow_apply_of_eq_coe
    (sub_apply_of_eq_coe (coordinate_apply _) (congrFun (coe_algebraMap u) _))
    (sub_ne_zero.2 fun h : y = u ↦ hy (h ▸ hu)) _

/-- **A meromorphic function on the Riemann sphere with neither zeros nor poles in `ℂ` is
constant.** -/
theorem exists_algebraMap_eq_of_forall_coe_ne {f : MeromorphicFunction (OnePoint ℂ)}
    (hinf : ∀ z : ℂ, f z ≠ ∞) (h0 : ∀ z : ℂ, f z ≠ ((0 : ℂ) : OnePoint ℂ)) :
    ∃ c : ℂ, algebraMap ℂ _ c = f := by
  by_cases hf : f ∞ = ∞
  · -- At a pole at `∞`, the inverse of `f` has no poles, so it is constant.
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_ne_infty (f := f⁻¹) fun x ↦ by
      induction x using OnePoint.rec with
      | infty => simp [inv_apply_of_eq_infty hf]
      | coe z => simp [inv_apply (hinf z) (h0 z)]
    exact ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩
  · exact exists_algebraMap_eq_of_forall_ne_infty fun x ↦ by
      induction x using OnePoint.rec with
      | infty => exact hf
      | coe z => exact hinf z

/-- The finite part of a meromorphic function on the Riemann sphere, read on `ℂ`. -/
private abbrev finitePartCoe (f : MeromorphicFunction (OnePoint ℂ)) : ℂ → ℂ :=
  fun z ↦ f.finitePart z

private theorem meromorphicOn_finitePartCoe (f : MeromorphicFunction (OnePoint ℂ)) :
    MeromorphicOn (finitePartCoe f) univ := fun z _ ↦ by
  simpa [comp_def] using (meromorphicAt_def _ _).1 (f.meromorphicAt_finitePart z)

/-- The zeros and poles on `ℂ` of the finite part of a nonzero meromorphic function on the Riemann
sphere are among its finitely many zeros and poles on the sphere. -/
private theorem finite_support_divisor_finitePartCoe {f : MeromorphicFunction (OnePoint ℂ)}
    (hf : f ≠ 0) : (MeromorphicOn.divisor (finitePartCoe f) univ).support.Finite := by
  refine (((finite_setOf_eq_zero hf).union f.finite_setOf_eq_infty).preimage
    coe_injective.injOn).subset fun u hu ↦ ?_
  by_contra hreg
  simp only [mem_preimage, mem_union, not_or] at hreg
  -- At a point where `f` is finite and nonzero, its finite part is continuous with a nonzero
  -- value, so it has order zero there.
  have hc : ContinuousAt (finitePartCoe f) u :=
    (continuousAt_finitePart hreg.2).comp continuous_coe.continuousAt
  have hne : finitePartCoe f u ≠ 0 := fun h ↦
    hreg.1 ((coe_finitePart hreg.2).symm.trans (congrArg _ h))
  have hord := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (meromorphicOn_finitePartCoe f u (mem_univ u))).1 ⟨_, hne, hc.tendsto.mono_left
      nhdsWithin_le_nhds⟩
  simp [MeromorphicOn.divisor_apply (meromorphicOn_finitePartCoe f) (mem_univ u), hord] at hu

/-- The finite part of a nonzero meromorphic function on the Riemann sphere, read on `ℂ`, does not
vanish identically near any point. -/
private theorem meromorphicOrderAt_finitePartCoe_ne_top {f : MeromorphicFunction (OnePoint ℂ)}
    (hf : f ≠ 0) (u : ℂ) : _root_.meromorphicOrderAt (finitePartCoe f) u ≠ ⊤ := fun h ↦ by
  obtain ⟨y, hy⟩ := (((OnePoint.tendsto_coe_nhdsNE u).eventually
    (eventually_finitePart_ne_zero hf (u : OnePoint ℂ))).and
    (meromorphicOrderAt_eq_top_iff.1 h)).exists
  exact hy.1 hy.2

/-- The value at `y` of the finitely supported product `∏ᶠ u, (· - u) ^ d u`, as a finite
product. -/
private theorem finprod_sub_zpow_apply {d : ℂ → ℤ} (hd : d.support.Finite) (y : ℂ) :
    (∏ᶠ u, (· - u) ^ d u) y = ∏ u ∈ hd.toFinset, (y - u) ^ d u :=
  (congrFun (Function.FactorizedRational.finprod_eq_fun hd) y).trans <|
    finprod_eq_prod_of_mulSupport_subset _ fun u hu ↦
      hd.mem_toFinset.2 fun h ↦ hu (by simp [h])

/-- At a point `y` outside a finite set `s`, the product of the `(y - u) ^ n u` over `u ∈ s` does
not vanish. -/
private theorem prod_sub_zpow_ne_zero {s : Finset ℂ} (n : ℂ → ℤ) {y : ℂ} (hy : y ∉ s) :
    ∏ u ∈ s, (y - u) ^ n u ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hu ↦ zpow_ne_zero _ (sub_ne_zero.2 fun h ↦ hy (h ▸ hu))

/-- If on `ℂ` the finite part of `f` is `∏ (z - u) ^ d(u)` times an analytic function `g`, away
from a codiscrete set, then the quotient of `f` by the rational function `∏ (z - u) ^ d(u)` agrees
with `g` at every point of `ℂ`. -/
private theorem mul_inv_prod_coordinate_sub_zpow_apply {f : MeromorphicFunction (OnePoint ℂ)}
    {d : ℂ → ℤ} (hd : d.support.Finite) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g univ)
    (hfg : finitePartCoe f =ᶠ[codiscreteWithin univ] (∏ᶠ u, (· - u) ^ d u) • g) (z : ℂ) :
    (f * (∏ u ∈ hd.toFinset, (coordinate - algebraMap ℂ _ u) ^ d u)⁻¹) z = ↑(g z) := by
  set s := hd.toFinset with hs
  set G := f * (∏ u ∈ s, (coordinate - algebraMap ℂ _ u) ^ d u)⁻¹
  have hev : ∀ᶠ y : ℂ in 𝓝[≠] z, G y = ↑(g y) := by
    have hs' : ∀ᶠ y : ℂ in 𝓝[≠] z, y ∉ s := by
      filter_upwards [(s.finite_toSet.sdiff (t := {z})).isClosed.compl_mem_nhds
        (fun h ↦ h.2 rfl) |> nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyz
      exact fun h ↦ hy ⟨h, hyz⟩
    filter_upwards [hs', (OnePoint.tendsto_coe_nhdsNE z).eventually (f.eventually_ne_infty z),
      eventually_codiscrete_iff_forall_eventually_nhdsNE.1 hfg z] with y hy hfy hFy
    have hφy := prod_coordinate_sub_zpow_apply s d hy
    rw [mul_apply_of_eq_coe (coe_finitePart hfy).symm
      (inv_apply_of_eq_coe hφy (prod_sub_zpow_ne_zero d hy))]
    congr 1
    simp only [finitePartCoe] at hFy
    rw [hFy, Pi.smul_apply', smul_eq_mul, finprod_sub_zpow_apply hd, ← hs]
    field_simp [prod_sub_zpow_ne_zero d hy]
  refine apply_eq_of_tendsto (φ := fun y ↦ ↑(g (affineChart y))) ?_ ?_
  · rw [OnePoint.nhdsNE_coe_eq, tendsto_map'_iff]
    simpa [comp_def, affineChart_coe] using ((continuous_coe.tendsto _).comp
      (hg z (mem_univ z)).continuousAt).mono_left nhdsWithin_le_nhds
  · rw [OnePoint.nhdsNE_coe_eq, eventually_map]
    simpa [affineChart_coe] using hev

/-- **Every meromorphic function on the Riemann sphere is a rational function of the
coordinate.** -/
private theorem ofRatFunc_surjective : Surjective ofRatFunc := by
  classical
  let S := ofRatFunc.fieldRange
  intro f
  suffices f ∈ S from AlgHom.mem_fieldRange.1 this
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem S
  have hfin := finite_support_divisor_finitePartCoe hf
  -- Factor the zeros and poles of `f` on `ℂ` out of its finite part.
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOn_finitePartCoe f).extract_zeros_poles
    (fun u ↦ meromorphicOrderAt_finitePartCoe_ne_top hf u) hfin
  set d := MeromorphicOn.divisor (finitePartCoe f) univ
  set s := hfin.toFinset
  -- The rational function `φ = ∏ (z - u) ^ d(u)` with the same zeros and poles on `ℂ`.
  set φ : MeromorphicFunction (OnePoint ℂ) :=
    ∏ u ∈ s, (coordinate - algebraMap ℂ _ u) ^ d u
  have hcoord : coordinate ∈ S :=
    AlgHom.mem_fieldRange.2 ⟨RatFunc.X, by simpa using ofRatFunc_algebraMap Polynomial.X⟩
  have hφS : φ ∈ S := prod_mem fun u _ ↦ zpow_mem (sub_mem hcoord (algebraMap_mem S u)) _
  have hφne : φ ≠ 0 := by
    obtain ⟨y, hy⟩ := s.finite_toSet.infinite_compl.nonempty
    intro h
    have : φ y = _ := prod_coordinate_sub_zpow_apply s d hy
    rw [h, coe_zero] at this
    exact prod_sub_zpow_ne_zero d hy (coe_injective this).symm
  -- The quotient `G = f / φ` agrees on `ℂ` with the analytic function `g` without zeros, so it is
  -- constant, and `f = G * φ` is rational.
  set G := f * φ⁻¹
  have hG : ∀ z : ℂ, G z = ↑(g z) := mul_inv_prod_coordinate_sub_zpow_apply hfin hg hfg
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_coe_ne (f := G) (fun z ↦ by simp [hG])
    fun z ↦ by simpa [hG] using hg0 ⟨z, mem_univ z⟩
  have hGS : G ∈ S := hc ▸ algebraMap_mem S c
  simpa [G, mul_assoc, inv_mul_cancel₀ hφne] using mul_mem hGS hφS

/-- **The meromorphic functions on the Riemann sphere are the rational functions.** Evaluation at
the coordinate `z` is an isomorphism of `ℂ`-algebras from the field of rational functions over `ℂ`
to the field of meromorphic functions on the Riemann sphere. -/
def ratFuncEquiv : RatFunc ℂ ≃ₐ[ℂ] MeromorphicFunction (OnePoint ℂ) :=
  AlgEquiv.ofBijective ofRatFunc ⟨ofRatFunc.toRingHom.injective, ofRatFunc_surjective⟩

private theorem ratFuncEquiv_apply (r : RatFunc ℂ) : ratFuncEquiv r = ofRatFunc r :=
  AlgEquiv.ofBijective_apply _ _ r

/-- On polynomials, the isomorphism `ratFuncEquiv` is evaluation at the coordinate. -/
@[simp]
theorem ratFuncEquiv_algebraMap (p : ℂ[X]) :
    ratFuncEquiv (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval coordinate p := by
  rw [ratFuncEquiv_apply, ofRatFunc_algebraMap]

/-- The isomorphism `ratFuncEquiv` sends the variable `X` to the coordinate. -/
@[simp]
theorem ratFuncEquiv_X : ratFuncEquiv RatFunc.X = coordinate := by
  simpa using ratFuncEquiv_algebraMap Polynomial.X

/-- The meromorphic function of a rational function `r` takes the value `r(z)` at every finite
point `z` at which the denominator of `r` does not vanish. -/
theorem ratFuncEquiv_apply_coe (r : RatFunc ℂ) {z : ℂ} (hz : r.denom.eval z ≠ 0) :
    ratFuncEquiv r z = ↑(r.eval (RingHom.id ℂ) z) := by
  have hnum := aeval_coordinate_apply_coe r.num z
  have hden := aeval_coordinate_apply_coe r.denom z
  rw [ratFuncEquiv_apply, ofRatFunc, RatFunc.liftAlgHom_apply, div_eq_mul_inv,
    mul_apply_of_eq_coe hnum (inv_apply_of_eq_coe hden hz), RatFunc.eval, eval₂_id, eval₂_id,
    div_eq_mul_inv]

end TauCeti.RiemannSurface.MeromorphicFunction
