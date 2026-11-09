/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.MappingTorus.Iterate
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit.Homology
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint

/-!
# The time period homomorphism of a mapping torus

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, modelled on a
finite-dimensional space, and let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping
torus, with projection `p : Y_φ → ℝ / ℤ` and closed time form `dt = p^* dt₁`
(`TauCeti.SmoothMappingTorus.timeForm`). Integrating `dt` over singular `1`-cycles gives the
**time period homomorphism**

`N : H₁(Y_φ; ℤ) → ℝ`,  `N(h) = ∫_h dt`

(`TauCeti.SmoothMappingTorus.timePeriodHom`), the period homomorphism `TauCeti.homologyPeriodHom` of
the time form. It is the grading by which the classes of closed orbits of the suspension flow are
ordered in the Novikov completion of the group ring of `H₁(Y_φ; ℤ)`: the series counting closed
orbits, or the orbit tori `S¹ × γ` of the symplectic suspension, are finite below every bound on
`N`. In general `N` is not injective: it vanishes on torsion classes and on the classes carried by
a fibre, so the completion is indexed by `H₁(Y_φ; ℤ)` itself and not by the values of `N`.

This file computes `N`:

* on the class `[γ]` of the closed orbit through a point of period `d`, `N [γ] = d`, so the classes
  of closed orbits of positive period have positive period;
* `N` vanishes on the classes carried by a fibre `x ↦ [t, x]`, and it factors through the
  projection `p` and the period homomorphism of the circle `ℝ / ℤ`;
* `N` takes integer values, since the periods of `dt₁` on `H₁(ℝ / ℤ; ℤ)` are integers
  (`AddCircle.exists_homologyPeriodHom_timeForm_eq_intCast_mul`);
* `N` is natural: on the image `f_* c` of a class under a smooth map `f : X → Y_φ` it is the
  period of `f^* dt`. In particular it is preserved by the map of mapping tori induced by a smooth
  semiconjugacy, and the integer-iterate map `Y_(φ^k) → Y_φ` multiplies it by `k`;
* if `M` is compact and `φ` is nondegenerate up to every period, then for distinct points `x i` of
  positive periods `d i` the time periods `N [γ_(x i)] = d i` tend to infinity, so only finitely
  many of these closed orbit classes lie below each bound on `N`.

The opposite convention of circle-valued Morse theory integrates the closed form `α = -dt`, for
which the suspension flow is the flow of `-α♯` in a metric making the suspension vector field dual
to `dt`; its period homomorphism is `-N`
(`TauCeti.SmoothMappingTorus.homologyPeriodHom_neg_timeForm`). The Novikov completions for `N` and
`-N` are exchanged by inverting the exponents, `TauCeti.NovikovSeries.reverseContinuousAlgEquiv`.

## Main definitions

* `TauCeti.SmoothMappingTorus.timePeriodHom φ`: the homomorphism `N(h) = ∫_h dt` on
  `H₁(Y_φ; ℤ)`.

## Main results

* `TauCeti.SmoothMappingTorus.timePeriodHom_closedOrbitHomologyClass`: `N [γ] = d` for the closed
  orbit through a point of period `d`.
* `TauCeti.SmoothMappingTorus.timePeriodHom_singularHomologyMap`: `N (f_* c) = ∫_c f^* dt` for a
  smooth map `f` into `Y_φ`.
* `TauCeti.SmoothMappingTorus.timePeriodHom_singularHomologyMap_mk`: `N` vanishes on fibre classes.
* `TauCeti.SmoothMappingTorus.timePeriodHom_eq_homologyPeriodHom_singularHomologyMap_proj`: `N`
  factors through the projection to the circle.
* `TauCeti.SmoothMappingTorus.exists_timePeriodHom_eq_intCast`: `N` takes integer values.
* `TauCeti.SmoothMappingTorus.timePeriodHom_singularHomologyMap_map`,
  `TauCeti.SmoothMappingTorus.timePeriodHom_singularHomologyMap_iterateMap`: naturality under
  semiconjugacies and the iterate law.
* `TauCeti.SmoothMappingTorus.tendsto_timePeriodHom_closedOrbitHomologyClass`: for distinct
  periodic points of a diffeomorphism of a compact manifold, nondegenerate up to every period, the
  time periods of their closed orbits tend to infinity.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861–888.
* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods).
-/

public section

noncomputable section

open Filter Function TauCeti.HurewiczOne
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] (φ : M ≃ₘ⟮I, I⟯ M)

/-- The **time period homomorphism** `N(h) = ∫_h dt` of the mapping torus `Y_φ`: the periods of the
time form `dt` on the first singular homology group `H₁(Y_φ; ℤ)`. -/
def timePeriodHom : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1 →+ ℝ :=
  homologyPeriodHom (timeForm φ).1

/-- The time period homomorphism is the period homomorphism of the time form. -/
theorem timePeriodHom_def : timePeriodHom φ = homologyPeriodHom (timeForm φ).1 := (rfl)

/-- The periods of the form `α = -dt`, whose negative gradient flow is the suspension flow, are the
negatives `-N` of the time periods. -/
theorem homologyPeriodHom_neg_timeForm :
    homologyPeriodHom (-(timeForm φ).1) = -timePeriodHom φ := by
  rw [← neg_one_smul ℝ (timeForm φ).1, homologyPeriodHom_smul, neg_one_smul, timePeriodHom_def]

variable {φ}

/-- **Naturality of the time period.** The time period of the image `f_* c` of a class under a
smooth map `f : X → Y_φ` is the period of the pulled-back time form `f^* dt` on `c`. -/
theorem timePeriodHom_singularHomologyMap {E₀ H₀ X : Type} [NormedAddCommGroup E₀]
    [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] [TopologicalSpace H₀]
    {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace X] [ChartedSpace H₀ X] [IsManifold I₀ ∞ X]
    [T2Space X]
    {f : X → SmoothMappingTorus φ} (hf : ContMDiff I₀ (𝓘(ℝ).prod I) ∞ f)
    (c : ((singularChains ℤ).obj (TopCat.of X)).homology 1) :
    timePeriodHom φ (ContinuousMap.singularHomologyMap ℤ 1 ⟨f, hf.continuous⟩ c) =
      homologyPeriodHom (SmoothForm.mpullback f hf (timeForm φ)).1 c := by
  rw [timePeriodHom_def, SmoothForm.coe_mpullback]
  exact homologyPeriodHom_singularHomologyMap (hf.of_le (by simp))
    ((timeForm φ).isSmoothForm.of_le (by simp))
    ((SmoothForm.isClosed_def _).1 (isClosed_timeForm φ)) c

variable (φ)

/-- **Fibre classes have time period zero.** The time form vanishes on each fibre
`x ↦ [t, x]`, so `N` vanishes on the image of `H₁(M; ℤ)` under the fibre inclusion. -/
@[simp]
theorem timePeriodHom_singularHomologyMap_mk (t : ℝ)
    (c : ((singularChains ℤ).obj (TopCat.of M)).homology 1) :
    timePeriodHom φ
        (ContinuousMap.singularHomologyMap ℤ 1 ⟨mk φ t, (contMDiff_mk φ t).continuous⟩ c) = 0 := by
  rw [timePeriodHom_singularHomologyMap (contMDiff_mk φ t), mpullback_mk_timeForm]
  simp

/-- **The time period factors through the circle.** `N` is the period of the time form `dt₁` of
`ℝ / ℤ` on the image of a class under the projection `p : Y_φ → ℝ / ℤ`. -/
theorem timePeriodHom_eq_homologyPeriodHom_singularHomologyMap_proj
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    timePeriodHom φ c = homologyPeriodHom (AddCircle.timeForm 1).1
      (ContinuousMap.singularHomologyMap ℤ 1 ⟨proj φ, (contMDiff_proj φ).continuous⟩ c) := by
  rw [homologyPeriodHom_singularHomologyMap ((contMDiff_proj φ).of_le (by simp))
      ((AddCircle.timeForm 1).isSmoothForm.of_le (by simp))
      ((SmoothForm.isClosed_def _).1 (AddCircle.isClosed_timeForm 1)),
    timePeriodHom_def, timeForm_def, SmoothForm.coe_mpullback]

/-- **The time periods are integers.** Every class of `H₁(Y_φ; ℤ)` has integer time period, since
`N` factors through `H₁(ℝ / ℤ; ℤ)`, which is generated by the circuit class of period `1`. -/
theorem exists_timePeriodHom_eq_intCast
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    ∃ n : ℤ, timePeriodHom φ c = n := by
  rw [timePeriodHom_eq_homologyPeriodHom_singularHomologyMap_proj]
  simpa using AddCircle.exists_homologyPeriodHom_timeForm_eq_intCast_mul (p := 1) _

variable {φ} in
/-- **The period of a closed orbit.** The class `[γ] ∈ H₁(Y_φ; ℤ)` of the closed orbit
`[t] ↦ [t, x]` through a point `x` of period `d` has time period `N [γ] = ∫_γ dt = d`: its
projection to the circle `ℝ / ℤ` winds `d` times around it. -/
@[simp]
theorem timePeriodHom_closedOrbitHomologyClass {d : ℕ} {x : M} (hx : IsPeriodicPt φ d x) :
    timePeriodHom φ (closedOrbitHomologyClass hx) = d := by
  have hd : (d : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ) := ⟨d, by simp⟩
  have hcomp :
      (⟨proj φ, (contMDiff_proj φ).continuous⟩ : C(SmoothMappingTorus φ, UnitAddCircle)).comp
        ⟨closedOrbit φ hx, continuous_closedOrbit hx⟩ =
      ⟨AddCircle.coverMap hd, AddCircle.continuous_coverMap hd⟩ := by
    ext θ
    induction θ using QuotientAddGroup.induction_on with
    | H t => simp [closedOrbit_coe, proj_mk]
  rw [timePeriodHom_eq_homologyPeriodHom_singularHomologyMap_proj, closedOrbitHomologyClass_def,
    ← ContinuousMap.singularHomologyMap_comp, hcomp,
    AddCircle.singularHomologyMap_coverMap_fundamentalClass hd d (by simp), map_zsmul,
    AddCircle.homologyPeriodHom_timeForm_fundamentalClass]
  simp

variable {φ} in
/-- The class of a closed orbit of positive period has positive time period. -/
theorem timePeriodHom_closedOrbitHomologyClass_pos {d : ℕ} {x : M} (hx : IsPeriodicPt φ d x)
    (hd : 0 < d) : 0 < timePeriodHom φ (closedOrbitHomologyClass hx) := by
  rw [timePeriodHom_closedOrbitHomologyClass]
  exact_mod_cast hd

section Map

variable {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N]
  (ψ : N ≃ₘ⟮J, J⟯ N) {g : M → N} (h : Semiconj g φ ψ) (hg : ContMDiff I J ∞ g)

/-- **Naturality of the time period.** The map `[t, x] ↦ [t, g x]` of mapping tori induced by a
smooth semiconjugacy `g ∘ φ = ψ ∘ g` preserves time periods. -/
@[simp]
theorem timePeriodHom_singularHomologyMap_map
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology 1) :
    timePeriodHom ψ (ContinuousMap.singularHomologyMap ℤ 1
        ⟨map φ ψ g h, (contMDiff_map φ ψ g h hg).continuous⟩ c) = timePeriodHom φ c := by
  rw [timePeriodHom_singularHomologyMap (contMDiff_map φ ψ g h hg), mpullback_map_timeForm φ ψ h hg,
    timePeriodHom_def]

end Map

/-- **The iterate law.** The integer-iterate map `Y_(φ^k) → Y_φ`, `[t, x] ↦ [k t, x]`, multiplies
time periods by `k`. -/
@[simp]
theorem timePeriodHom_singularHomologyMap_iterateMap (k : ℤ)
    (c : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus (φ ^ k)))).homology 1) :
    timePeriodHom φ (ContinuousMap.singularHomologyMap ℤ 1
        ⟨iterateMap φ k, (contMDiff_iterateMap φ k).continuous⟩ c) =
      k * timePeriodHom (φ ^ k) c := by
  rw [timePeriodHom_singularHomologyMap (contMDiff_iterateMap φ k), mpullback_iterateMap_timeForm,
    Submodule.coe_smul_of_tower, homologyPeriodHom_smul, timePeriodHom_def, AddMonoidHom.smul_apply,
    smul_eq_mul]

section Finiteness

variable {φ} [CompactSpace M] (hφ : ∀ N, IsNondegenerateUpToPeriod I φ N) {ι : Type*}
  {x : ι → M} (hx : Injective x) {d : ι → ℕ} (hxd : ∀ i, IsPeriodicPt φ (d i) (x i))
  (hd : ∀ i, 0 < d i)

include hφ hx hd in
/-- **Finitely many closed orbits below each period.** For a diffeomorphism of a compact manifold
which is nondegenerate up to every period, the time periods `N [γ_(x i)] = d i` of the closed
orbits through distinct points `x i` of positive periods `d i` tend to infinity along the cofinite
filter. -/
theorem tendsto_timePeriodHom_closedOrbitHomologyClass :
    Tendsto (fun i ↦ timePeriodHom φ (closedOrbitHomologyClass (hxd i))) cofinite atTop := by
  simp only [timePeriodHom_closedOrbitHomologyClass]
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop.2 fun N ↦ eventually_cofinite.2 ?_)
  -- The points with a positive period at most `N` form a finite set.
  exact (((hφ N).finite_setOf_isPeriodicPt φ.continuous).preimage hx.injOn).subset
    fun i hi ↦ ⟨d i, hd i, (not_le.1 hi).le, hxd i⟩

end Finiteness

end TauCeti.SmoothMappingTorus
