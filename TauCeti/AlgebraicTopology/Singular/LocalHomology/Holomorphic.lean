/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.AlgebraicTopology.Singular.LocalHomology.ProperExtension
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.LinearIndependent.Prod
import TauCeti.LinearAlgebra.LinearMap.Coprod
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Local indices of holomorphic maps are positive

Let `E` be a finite-dimensional complex normed space, regarded as a real manifold modelled on
itself and oriented by a homological orientation `o` (`TauCeti.HomologicalOrientation`), used on
both the source and the target of a continuous map `f : E → E`. If `f` is holomorphic near a point
`x` which is isolated in its fibre `f⁻¹(f x)`, then the topological local index of `f` at `x`
(`TauCeti.HomologicalOrientation.localIndex`) is positive
(`TauCeti.HomologicalOrientation.localIndex_pos_of_analyticAt`). Since a point which is not isolated
in its fibre has local index `0` by convention, the local index of a holomorphic map is always
nonnegative, and it is positive exactly at the isolated points of the fibres
(`TauCeti.HomologicalOrientation.localIndex_pos_iff_eventually_ne_of_analyticAt`). For maps of one
variable this is `TauCeti.HomologicalOrientation.localIndex_pos_iff_of_analyticAt` of
`TauCeti.Analysis.Complex.Conformal.LocalIndex`, where the index is the order of vanishing.

Positivity is the source of the positivity of intersections of holomorphic curves. Two holomorphic
discs `u₁, u₂ : ℂ → ℂ²` meeting at an isolated point `u₁ z₀ = u₂ w₀` have, as local intersection
number, the local index of `(z, w) ↦ u₁ z - u₂ w` at `(z₀, w₀)`, and it is positive
(`TauCeti.HomologicalOrientation.localIndex_pos_of_apply_eq_sub`). This is the model case,
for the standard complex structure of `ℂ²`, of the local intersection multiplicities of distinct
branches of pseudoholomorphic curves in a four-manifold.

The same positivity of real Jacobians shows that local indices do not change under changes of
coordinates whose derivative at the point is complex linear and injective: on the target, for the
difference `a - b` of two maps
(`TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt`), and on the
source (`TauCeti.HomologicalOrientation.localIndex_comp_eq_of_hasStrictFDerivAt`). These are the
specializations of the real statements
`TauCeti.HomologicalOrientation.localIndex_eq_sign_det_mul_of_apply_eq_sub` and
`TauCeti.HomologicalOrientation.localIndex_comp_eq_mul_sign_det`. The target changes include the
unitary maps and the holomorphic changes of coordinates, which preserve the standard complex
structure. A `C¹` chart whose derivative at the intersection point carries a different complex
structure there to the standard one has a derivative that is not complex linear for the standard
structure; such charts fall under the real statement
`TauCeti.HomologicalOrientation.localIndex_eq_sign_det_mul_of_apply_eq_sub`, once the sign of its
real Jacobian determinant is known.

## Proof

A complex-linear map has real determinant `|det_ℂ|²` (`LinearMap.det_restrictScalars_eq_normSq`),
so at a point where the complex derivative is invertible the local index, the sign of the real
Jacobian, is `1` (`TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasFDerivAt`). Hence the
degree of a proper map is the number of preimages of a value all of whose preimages are such
regular points (`TauCeti.HomologicalOrientation.degree_eq_ncard_of_hasFDerivAt`), and the local
index at an isolated point is the number of solutions in a small ball of `f z = y` for nearby such
values `y` (`TauCeti.HomologicalOrientation.localIndex_eq_ncard_of_hasFDerivAt`).

This alone does not give positivity, since the derivative of `f` may be singular everywhere near
`x`, in which case no value near `f x` has a regular preimage. The proof perturbs `f`. Choose a
closed ball `B` about `x` whose only solution of `f z = f x` is `x`, and replace `f` by a proper map
`g` agreeing with it on `B` and staying at distance at least `δ > 0` from `f x` outside the interior
of `B` (`ContinuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub`); the local index of `f`
at `x` is the degree of `g`. For a small `ε > 0` such that `-ε` is not an eigenvalue of `Df(x)`, the
map `G z = g z + ε ρ(z - x)`, with `ρ` the radial retraction onto the ball of radius `r` of `B`, is
`f + ε (· - x)` on `B` and moves `g` by at most `ε r < δ`. So the straight homotopy from `g` to `G`
never takes the value `f x` outside `B`, and `g` and `G` have the same degree. Now `G` has the
invertible derivative `Df(x) + ε` at `x`, hence local index `1` there, so `G` maps the interior of
`B` onto a neighbourhood of `f x`; by the equal-dimensional Sard theorem
(`TauCeti.dense_setOf_forall_surjective_fderiv`) this neighbourhood contains a value all of whose
preimages are regular, and it has at least one. So the degree of `G` is a positive number of
preimages.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasFDerivAt`: at a point with invertible
  complex derivative the local index is `1`.
* `TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt`,
  `TauCeti.HomologicalOrientation.localIndex_comp_eq_of_hasStrictFDerivAt`: local indices are
  invariant under changes of coordinates of the target and of the source with complex-linear
  derivative.
* `TauCeti.HomologicalOrientation.degree_eq_ncard_of_hasFDerivAt`: the degree of a proper map is the
  number of preimages of a value whose preimages have invertible complex derivatives.
* `TauCeti.HomologicalOrientation.localIndex_eq_ncard_of_hasFDerivAt`: the local index counts the
  solutions in a small ball of `f z = y` for such values `y` near `f x`.
* `TauCeti.HomologicalOrientation.localIndex_pos_of_analyticAt`: **the local index of a holomorphic
  map at an isolated point of its fibre is positive.**
* `TauCeti.HomologicalOrientation.localIndex_pos_iff_eventually_ne_of_analyticAt`,
  `TauCeti.HomologicalOrientation.localIndex_nonneg_of_analyticAt`: positivity exactly at isolated
  points, and nonnegativity everywhere.
* `TauCeti.HomologicalOrientation.localIndex_pos_of_apply_eq_sub`: **positivity of the local
  intersection numbers of holomorphic discs in `ℂ²`**;
  `TauCeti.HomologicalOrientation.localIndex_eq_one_of_apply_eq_sub`: a transverse intersection
  counts `1`.

The examples at the end of the file compute the local intersection numbers of the line `w = 0`
with the lines `z = 0` and `w = z` (both `1`) and with itself (there is no isolated intersection,
and the index is `0`). Tangent and critical intersections, such as that of the line `w = 0` with the
parabola `w = z²`, are computed by orders of vanishing in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.GraphIntersection`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix E (local intersection numbers and their positivity).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages of a regular value).
-/

public section

noncomputable section

open Filter Metric Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

section Holomorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
  (o : HomologicalOrientation E E n)

/-- **The local index at a point with invertible complex derivative is `1`.** If `f` is complex
differentiable at `x` with injective derivative, its local index at `x`, for the same orientation of
`E` on source and target, is `1`: the real Jacobian determinant `|det_ℂ f'|²` is positive. -/
theorem localIndex_eq_one_of_hasFDerivAt (hE : finrank ℝ E = n) {f : C(E, E)} {f' : E →L[ℂ] E}
    {x : E} (hf : HasFDerivAt f f' x) (hf' : Function.Injective f') :
    o.localIndex o f x = 1 := by
  have hpos : 0 < (f'.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hf'
  rw [o.localIndex_eq_sign_det hE (hf.restrictScalars ℝ) hpos.ne', sign_pos hpos,
    SignType.coe_one]

/-- **The degree of a holomorphic proper map counts preimages.** If every preimage of `y` under the
proper map `f : E → E` is a point where `f` is complex differentiable with injective derivative,
then the degree of `f` is the number of preimages of `y`. -/
theorem degree_eq_ncard_of_hasFDerivAt (hE : finrank ℝ E = n) {f : C(E, E)} (hf : IsProperMap f)
    {f' : E → E →L[ℂ] E} {y : E} (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hinj : ∀ x ∈ f ⁻¹' {y}, Function.Injective (f' x)) :
    o.degree o hE f = (f ⁻¹' {y}).ncard :=
  o.degree_eq_ncard_of_det_pos hE hf (f' := fun x ↦ (f' x).restrictScalars ℝ)
    (fun x hx ↦ (hderiv x hx).restrictScalars ℝ)
    fun x hx ↦ LinearMap.det_restrictScalars_pos_iff_injective.2 (hinj x hx)

/-- **The local index of a holomorphic map counts nearby solutions.** Suppose that `x` is the only
solution of `f z = f x` in the ball of radius `r` about `x`, that `f` stays at distance at least
`δ` from `f x` on the sphere of radius `r`, and that `y` is a value within `δ` of `f x` at whose
preimages in the ball `f` is complex differentiable with injective derivative. Then the local index
of `f` at `x` is the number of solutions of `f z = y` in the ball. -/
theorem localIndex_eq_ncard_of_hasFDerivAt (hE : finrank ℝ E = n) {f : C(E, E)} {x y : E}
    {r δ : ℝ} (hr : 0 ≤ r) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) (hy : ‖y - f x‖ < δ) {f' : E → E →L[ℂ] E}
    (hderiv : ∀ z ∈ ball x r, f z = y → HasFDerivAt f (f' z) z)
    (hinj : ∀ z ∈ ball x r, f z = y → Function.Injective (f' z)) :
    o.localIndex o f x = {z ∈ ball x r | f z = y}.ncard := by
  obtain ⟨g, hgp, hgf, -, hgfib, hidx⟩ :=
    o.exists_isProperMap_eqOn_localIndex_eq_degree o hE hE hr ((norm_nonneg _).trans_lt hy) hfδ
      hiso
  replace hgfib := hgfib y hy
  rw [hidx, o.degree_eq_ncard_of_hasFDerivAt hE hgp (f' := f') (y := y), hgfib]
  · intro z hz
    rw [hgfib] at hz
    exact (hderiv z hz.1 hz.2).congr_of_eventuallyEq
      (eventually_of_mem (isOpen_ball.mem_nhds hz.1) fun _ hw ↦ hgf (ball_subset_closedBall hw))
  · intro z hz
    rw [hgfib] at hz
    exact hinj z hz.1 hz.2

/-- **The local index of a holomorphic map at an isolated point of its fibre is positive.** If `f`
is analytic at `x` and `x` is isolated in the fibre `f⁻¹(f x)`, then the local index of `f` at `x`,
for the same orientation of `E` on source and target, is positive. -/
theorem localIndex_pos_of_analyticAt (hE : finrank ℝ E = n) {f : C(E, E)} {x : E}
    (hf : AnalyticAt ℂ f x) (hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x) : 0 < o.localIndex o f x := by
  -- A ball of radius `r` about `x` on which `f` is analytic and `x` is the only solution of
  -- `f z = f x`, and a lower bound `δ` for `‖f - f x‖` on its boundary sphere.
  obtain ⟨r, hr, δ, hδ, hfa, hfδ, hiso'⟩ :=
    f.continuous.continuousOn.exists_closedBall_subset_and_le_dist
      (U := {z | AnalyticAt ℂ f z}) hf.eventually_analyticAt hiso
  -- A small `ε` with `ε r < δ` such that `-ε` is not an eigenvalue of `Df(x)`.
  obtain ⟨ε, ⟨hε, hεδ⟩, hεA⟩ : ∃ ε ∈ Ioo 0 (δ / r),
      ¬Module.End.HasEigenvalue (fderiv ℂ f x : Module.End ℂ E) (-(ε : ℂ)) :=
    (Ioo_infinite (div_pos hδ hr)).exists_notMem_finite
      ((Module.End.finite_hasEigenvalue (fderiv ℂ f x : Module.End ℂ E)).preimage
        fun a _ b _ h ↦ by simpa using h)
  have hεr : |ε| * r < δ := by
    rw [abs_of_pos hε]
    exact (lt_div_iff₀ hr).1 hεδ
  -- The local index of `f` is the degree of a proper map `G`, equal to `f + ε (· - x)` near `x`,
  -- complex differentiable there with derivative `Df + ε`, which is invertible at `x`.
  obtain ⟨G, hGp, hidx, hGf, hGout⟩ := o.exists_isProperMap_localIndex_eq_degree o hE hr.le
    (fun z hz ↦ dist_eq_norm (f z) (f x) ▸ hfδ z hz)
    (fun z hz ↦ hiso' z (ball_subset_closedBall hz)) hεr
  have hGeq {z : E} (hz : z ∈ ball x r) :
      (G : E → E) =ᶠ[𝓝 z] fun w ↦ f w + (ε : ℂ) • (w - x) :=
    eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw ↦ by
      simpa [Complex.coe_smul] using hGf (ball_subset_closedBall hw)
  have hDx : Function.Injective (fderiv ℂ f x + (ε : ℂ) • ContinuousLinearMap.id ℂ E) :=
    (injective_iff_map_eq_zero _).2 fun v hv ↦ by_contra fun hv0 ↦ hεA
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2
        (by rw [neg_smul, eq_neg_iff_add_eq_zero]; simpa using hv), hv0⟩)
  rw [hidx]
  refine o.degree_pos_of_hasFDerivAt hE hGp (U := ball x r)
    (D := fun z ↦ (fderiv ℂ f z + (ε : ℂ) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ)
    (fun z hz ↦ (((hfa (ball_subset_closedBall hz)).differentiableAt.hasFDerivAt.add
      (((hasFDerivAt_id z).sub_const x).const_smul (ε : ℂ))).congr_of_eventuallyEq
      (hGeq hz)).restrictScalars ℝ)
    (fun z _ ↦ LinearMap.det_restrictScalars_nonneg _)
    (LinearMap.det_restrictScalars_pos_iff_injective.2 hDx).ne' ?_
  -- Values within `δ - |ε| r` of `G x = f x` have all their preimages in the open ball.
  have hGx : G x = f x := by simp [hGf (mem_closedBall_self hr.le)]
  rw [hGx]
  filter_upwards [ball_mem_nhds (f x) (sub_pos.2 hεr)] with y' hy' z (hz : G z = y')
  by_contra hzb
  have h := hGout z (not_lt.1 (mem_ball.not.1 hzb))
  rw [hz, ← dist_eq_norm] at h
  linarith [mem_ball.1 hy']

/-- **The local index of a holomorphic map is positive exactly at isolated points of its
fibres.** If `f` is analytic at `x`, its local index at `x` is positive if and only if `x` is
isolated in the fibre `f⁻¹(f x)`. -/
theorem localIndex_pos_iff_eventually_ne_of_analyticAt (hE : finrank ℝ E = n) {f : C(E, E)}
    {x : E} (hf : AnalyticAt ℂ f x) :
    0 < o.localIndex o f x ↔ ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  refine ⟨fun h ↦ ?_, o.localIndex_pos_of_analyticAt hE hf⟩
  by_contra hiso
  rw [o.localIndex_of_frequently_eq o f (by simpa using not_eventually.1 hiso)] at h
  exact lt_irrefl 0 h

/-- **The local index of a holomorphic map is nonnegative.** -/
theorem localIndex_nonneg_of_analyticAt (hE : finrank ℝ E = n) {f : C(E, E)} {x : E}
    (hf : AnalyticAt ℂ f x) : 0 ≤ o.localIndex o f x := by
  by_cases hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · exact (o.localIndex_pos_of_analyticAt hE hf hiso).le
  · rw [o.localIndex_of_frequently_eq o f (by simpa using not_eventually.1 hiso)]

end Holomorphic

/-! ### Changes of coordinates -/

section CoordinateChange

/-- **Local intersection indices are invariant under changes of coordinates of the target with
complex-linear derivative.** Let `F p = a p - b p` for maps `a, b : M → E` continuous at `x` with
`a x = b x`. If `Ψ : E → E` is strictly differentiable at `a x` with an injective complex-linear
derivative, such as a holomorphic chart or a unitary map, then `G' p = Ψ (a p) - Ψ (b p)` has the
same local index as `F` at `x`: the real Jacobian determinant `|det_ℂ|²` of the derivative is
positive. -/
theorem localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt {M G E : Type} [TopologicalSpace M]
    [T2Space M] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [ChartedSpace G M] [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
    (o : HomologicalOrientation M G n) (o' : HomologicalOrientation E E n) (hE : finrank ℝ E = n)
    {F G' : C(M, E)} {a b : M → E} {Ψ : E → E} {L : E →L[ℂ] E} {x : M}
    (hF : ∀ p, F p = a p - b p) (hG' : ∀ p, G' p = Ψ (a p) - Ψ (b p))
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hab : a x = b x)
    (hΨ : HasStrictFDerivAt Ψ (L.restrictScalars ℝ) (a x)) (hL : Function.Injective L) :
    o.localIndex o' G' x = o.localIndex o' F x := by
  have hpos : 0 < (L.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hL
  rw [o.localIndex_eq_sign_det_mul_of_apply_eq_sub o' hE hF hG' ha hb hab hΨ hpos.ne',
    sign_pos hpos, SignType.coe_one, one_mul]

/-- **Local indices are invariant under changes of coordinates of the source with complex-linear
derivative.** If `φ : E → E` is strictly differentiable at `x` with an injective complex-linear
derivative, such as a holomorphic reparametrization, then the local index of `F ∘ φ` at `x` is
that of `F` at `φ x`. Only the target dimension must equal `n`; the source dimension may differ. -/
theorem localIndex_comp_eq_of_hasStrictFDerivAt {E N G : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [TopologicalSpace N] [T2Space N]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [ChartedSpace G N] {n : ℕ}
    (o : HomologicalOrientation E E n) (o' : HomologicalOrientation N G n) (hG : finrank ℝ G = n)
    {F : C(E, N)} {φ : C(E, E)} {φ' : E →L[ℂ] E} {x : E}
    (hφ : HasStrictFDerivAt φ (φ'.restrictScalars ℝ) x) (hφ' : Function.Injective φ') :
    o.localIndex o' (F.comp φ) x = o.localIndex o' F (φ x) := by
  have hpos : 0 < (φ'.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hφ'
  rw [o.localIndex_comp_eq_mul_sign_det o' hG hφ hpos.ne', sign_pos hpos, SignType.coe_one,
    mul_one]

end CoordinateChange

/-! ### Intersections of holomorphic discs in `ℂ²` -/

section Disc

variable {n : ℕ} (o : HomologicalOrientation (ℂ × ℂ) (ℂ × ℂ) n)

/-- **Positivity of intersections of holomorphic discs in `ℂ²`.** Let `u₁` and `u₂` be holomorphic
near `z₀` and `w₀`, meeting at `u₁ z₀ = u₂ w₀` in an isolated point: `u₁ z ≠ u₂ w` for
`(z, w) ≠ (z₀, w₀)` near `(z₀, w₀)`. Then their local intersection number, the local index at
`(z₀, w₀)` of the map `F (z, w) = u₁ z - u₂ w`, is positive. -/
theorem localIndex_pos_of_apply_eq_sub (hn : finrank ℝ (ℂ × ℂ) = n) {F : C(ℂ × ℂ, ℂ × ℂ)}
    {u₁ u₂ : ℂ → ℂ × ℂ} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ : ℂ} (h₁ : AnalyticAt ℂ u₁ z₀)
    (h₂ : AnalyticAt ℂ u₂ w₀) (h : u₁ z₀ = u₂ w₀)
    (hiso : ∀ᶠ p in 𝓝[≠] (z₀, w₀), u₁ p.1 ≠ u₂ p.2) : 0 < o.localIndex o F (z₀, w₀) := by
  refine o.localIndex_pos_of_analyticAt hn
    (((h₁.comp analyticAt_fst).sub (h₂.comp analyticAt_snd)).congr
      (.of_forall fun p ↦ (hF p).symm)) ?_
  filter_upwards [hiso] with p hp
  rw [hF p, hF (z₀, w₀), h, sub_self]
  exact sub_ne_zero.2 hp

/-- **A transverse intersection of holomorphic discs counts `1`.** If `u₁` and `u₂` have
derivatives `a` at `z₀` and `b` at `w₀` which are linearly independent over `ℂ`, then the local
index at `(z₀, w₀)` of the map `F (z, w) = u₁ z - u₂ w` is `1`. -/
theorem localIndex_eq_one_of_apply_eq_sub (hn : finrank ℝ (ℂ × ℂ) = n) {F : C(ℂ × ℂ, ℂ × ℂ)}
    {u₁ u₂ : ℂ → ℂ × ℂ} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ : ℂ} {a b : ℂ × ℂ}
    (h₁ : HasDerivAt u₁ a z₀) (h₂ : HasDerivAt u₂ b w₀) (hab : LinearIndependent ℂ ![a, b]) :
    o.localIndex o F (z₀, w₀) = 1 :=
  o.localIndex_eq_one_of_hasFDerivAt hn
    ((h₁.hasFDerivAt_comp_fst_sub_comp_snd h₂).congr_of_eventuallyEq (.of_forall hF))
    (LinearMap.injective_fst_smulRight_sub_snd_smulRight_iff.2 hab)

/-! #### Examples -/

/-- The line `w = 0` of `ℂ²` has derivative `(1, 0)`. -/
private theorem hasDerivAt_lineZero (z : ℂ) :
    HasDerivAt (fun z : ℂ ↦ ((z, 0) : ℂ × ℂ)) ((1 : ℂ), (0 : ℂ)) z :=
  (hasDerivAt_id z).prodMk (hasDerivAt_const z 0)

/-- The coordinate lines `w = 0` and `z = 0` of `ℂ²` meet at the origin with local intersection
number `1`. -/
example (hn : finrank ℝ (ℂ × ℂ) = n) :
    o.localIndex o ⟨fun p ↦ (p.1, -p.2), by fun_prop⟩ (0, 0) = 1 :=
  o.localIndex_eq_one_of_apply_eq_sub hn (u₁ := fun z ↦ (z, 0)) (u₂ := fun w ↦ (0, w))
    (fun p ↦ by simp) (hasDerivAt_lineZero 0)
    ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id 0))
    (linearIndependent_pair_mk_one_iff.2 (by simp))

/-- The lines `w = 0` and `w = z` of `ℂ²` meet at the origin with local intersection number `1`. -/
example (hn : finrank ℝ (ℂ × ℂ) = n) :
    o.localIndex o ⟨fun p ↦ (p.1 - p.2, -p.2), by fun_prop⟩ (0, 0) = 1 :=
  o.localIndex_eq_one_of_apply_eq_sub hn (u₁ := fun z ↦ (z, 0)) (u₂ := fun w ↦ (w, w))
    (fun p ↦ by simp) (hasDerivAt_lineZero 0) ((hasDerivAt_id 0).prodMk (hasDerivAt_id 0))
    (linearIndependent_pair_mk_one_iff.2 (by simp))

/-- The line `w = 0` meets itself along a whole line: `(z, z)` is not isolated among the solutions
of `z - w = 0`, and the local index there is `0`. -/
example (z : ℂ) : o.localIndex o ⟨fun p ↦ (p.1 - p.2, 0), by fun_prop⟩ (z, z) = 0 := by
  refine o.localIndex_of_frequently_eq o _ ?_
  have h : Tendsto (fun t : ℂ ↦ (z + t, z + t)) (𝓝[≠] 0) (𝓝[≠] (z, z)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun t : ℂ ↦ (z + t, z + t) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact h.frequently (Frequently.of_forall fun t ↦ by simp)

end Disc

end HomologicalOrientation

end TauCeti
