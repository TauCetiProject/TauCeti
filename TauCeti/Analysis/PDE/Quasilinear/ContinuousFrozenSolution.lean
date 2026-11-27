/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Analysis.PDE.Quasilinear.GlobalHolder
import Mathlib.Dynamics.FixedPoints.Topology
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.Quasilinear.Stability
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure.UniformConvergence
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.ContinuousMap.Bounded.Closure
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Equicontinuity
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.UniformSpace.Cauchy

/-!
# The frozen-coefficient map of a quasilinear problem on `C(closure Ω)`

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded Lipschitz domain and consider the quasilinear Dirichlet problem

`-div (A(x, u) ∇u) = f + div F` in `Ω`, `u = G` on `∂Ω`,

with a Carathéodory coefficient `A`, every `A(·, s)` uniformly elliptic with constants `λ, Λ`,
data `f ∈ Lʳ(Ω)`, `r > 1`, `r > (n + 1)/2`, and `F ∈ L^q(Ω; ℝⁿ⁺¹)`, `q > 2`, `q > n + 1`, and
boundary values `g ∈ H¹(Ω)` whose value `G` is bounded and Lipschitz on `Ω`. The forcing enters as
the functional `ℓ φ = ∫_Ω f φ - ∫_Ω F · ∇φ` on `H¹₀(Ω)`.

For `v ∈ C(closure Ω)`, freezing the coefficient at `v` gives the linear problem
`-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, whose unique weak solution is
`TauCeti.PDE.frozenSolution A g ℓ v`. By the global Hölder estimate it has a representative that
is Hölder continuous up to the boundary, so it defines an element `T v` of `C(closure Ω)`,
realized as the space `closure Ω →ᵇ ℝ` of bounded continuous functions with the uniform norm. This
file constructs the map `T = TauCeti.PDE.continuousFrozenSolution A g ℓ` from `C(closure Ω)` to
itself and proves:

* `T v` is the unique element of `C(closure Ω)` agreeing almost everywhere on `Ω` with the frozen
  solution (`TauCeti.PDE.eq_continuousFrozenSolution_iff`);
* all the `T v` are `α`-Hölder with one constant, for one `α > 0`
  (`TauCeti.PDE.exists_holderWith_continuousFrozenSolution`);
* `T` is continuous (`TauCeti.PDE.continuous_continuousFrozenSolution`);
* `T` has relatively compact range (`TauCeti.PDE.isCompact_closure_range_continuousFrozenSolution`);
* the fixed points of `T` are exactly the continuous representatives on `closure Ω` of the weak
  solutions of the quasilinear problem (`TauCeti.PDE.isFixedPt_continuousFrozenSolution_iff`), and
  there is one, by Schauder's theorem (`TauCeti.PDE.exists_isFixedPt_continuousFrozenSolution`);
* the fixed points of `T` form a compact subset of `C(closure Ω)`
  (`TauCeti.PDE.isCompact_fixedPoints_continuousFrozenSolution`).

So `T` is a compact continuous self-map of the Banach space `C(closure Ω)`, the map of the classical
Schauder approach to quasilinear equations. Its continuity and compactness come from those of the
frozen solutions in `L²(Ω)` (`TauCeti.PDE.continuous_value_frozenSolution`,
`TauCeti.PDE.isCompact_closure_range_value_frozenSolution`): the Hölder representatives form a
uniformly equicontinuous family, so their convergence in measure on `Ω` is uniform
(`MeasureTheory.TendstoInMeasure.tendstoUniformlyOn_of_uniformEquicontinuousOn`), and uniform
convergence on `Ω` is convergence in `C(closure Ω)`.

The same argument makes the continuous solutions stable under perturbation of the data. Let the
coefficients `Aₖ → A` converge for almost every `x` locally uniformly in the second variable, with
common constants `λ, Λ`, let the forcings `ℓₖ → ℓ` converge in `H⁻¹(Ω)`, given by data `fₖ`, `Fₖ`
with norms in `Lʳ(Ω)` and `L^q(Ω)` bounded by one constant, and let the boundary values `gₖ → g`
converge in `H¹(Ω)`, with values bounded by one constant and Lipschitz with one constant. Then:

* the continuous representatives `vₖ ∈ C(closure Ω)` of weak solutions of the problems with data
  `(Aₖ, gₖ, ℓₖ)` have a subsequence converging in `C(closure Ω)` to the continuous representative
  of a weak solution of the problem with data `(A, g, ℓ)` (in the `TauCeti.PDE` namespace,
  `exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq_of_ae_eq`);
* the continuous solutions depend upper semicontinuously on the data: an open subset of
  `C(closure Ω)` containing those of the limit problem contains those of the `k`-th problem for
  all large `k`
  (`TauCeti.PDE.eventually_setOf_exists_forall_energyFormH1_quasilinear_eq_subset`).

The weak solutions converge in `H¹(Ω)` along a subsequence by the stability theorem
`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq`,
so their values converge in `L²(Ω)`. The bounds on the data give one Hölder bound for all the
`vₖ`, by the global Hölder estimate, so this convergence is uniform on `Ω`. In dimension at least
two, convergence in `H¹(Ω)` alone does not control the uniform norm.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 11.3 (quasilinear equations by Schauder's theorem in a space of continuous functions,
  with Hölder estimates uniform in the frozen coefficient) and Theorem 8.29 (the global Hölder
  estimate).
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped BoundedContinuousFunction ENNReal NNReal RealInnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

open scoped Classical in
/-- The function on `ℝⁿ⁺¹` equal to `v` on `closure Ω` and to `0` off it. -/
private def extendClosure (v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  fun x => if hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) then v ⟨x, hx⟩
    else 0

private theorem extendClosure_of_mem
    (v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    extendClosure v x = v ⟨x, hx⟩ :=
  dite_eq_left hx

private theorem continuousOn_extendClosure
    (v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ) :
    ContinuousOn (extendClosure v) (closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert v.continuous using 1
  ext ⟨x, hx⟩
  exact extendClosure_of_mem v hx

private theorem aestronglyMeasurable_extendClosure
    (v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ) :
    AEStronglyMeasurable (extendClosure v) (volume.restrict Omega) :=
  ((continuousOn_extendClosure v).mono subset_closure).aestronglyMeasurable
    Omega.isOpen.measurableSet

private theorem memLp_extendClosure
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ) :
    MemLp (extendClosure v) 2 (volume.restrict Omega) := by
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  refine MemLp.of_bound (aestronglyMeasurable_extendClosure v) ‖v‖
    (Eventually.of_forall fun x => ?_)
  unfold extendClosure
  split_ifs
  · exact v.norm_coe_le_norm _
  · simp

/-- A bounded continuous function on `closure Ω` that agrees almost everywhere on `Ω` with `w`
extends to a function on `ℝⁿ⁺¹` that agrees almost everywhere on `Ω` with `w`. -/
private theorem extendClosure_ae_eq
    {u : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ}
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (h : ∀ᵐ x ∂volume.restrict Omega,
      ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), u ⟨x, hx⟩ = w x) :
    extendClosure u =ᵐ[volume.restrict Omega] w := by
  filter_upwards [h, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
  rw [extendClosure_of_mem u (subset_closure hxΩ), hx]

/-- Two bounded continuous functions on `closure Ω` that agree almost everywhere on `Ω` with the
same function `w` are equal; this is `IsOpen.ext_closure_of_ae_eq` in the form used below. -/
private theorem eq_of_ae_eq_of_ae_eq
    {u u' : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ}
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (h : ∀ᵐ x ∂volume.restrict Omega,
      ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), u ⟨x, hx⟩ = w x)
    (h' : ∀ᵐ x ∂volume.restrict Omega,
      ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), u' ⟨x, hx⟩ = w x) :
    u = u' := by
  refine DFunLike.coe_injective <| Omega.isOpen.ext_closure_of_ae_eq (μ := volume)
    u.continuous u'.continuous ?_
  filter_upwards [(ae_restrict_iff' Omega.isOpen.measurableSet).1 h,
    (ae_restrict_iff' Omega.isOpen.measurableSet).1 h'] with x h₁ h₂ hx
  rw [h₁ hx, h₂ hx]

private theorem holderOnWith_extendClosure
    {u : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ} {C α : ℝ≥0}
    (hu : HolderWith C α u) :
    HolderOnWith C α (extendClosure u) (closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
  fun x hx y hy => by
    rw [extendClosure_of_mem u hx, extendClosure_of_mem u hy]
    exact hu ⟨x, hx⟩ ⟨y, hy⟩

/-- Bounded continuous functions on `closure Ω` that are `α`-Hölder with one constant, `α > 0`,
extend to a family uniformly equicontinuous on `Ω`. -/
private theorem uniformEquicontinuousOn_extendClosure {ι : Type*}
    {u : ι → closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ} {C α : ℝ≥0}
    (hα : 0 < α) (hu : ∀ i, HolderWith C α (u i)) :
    UniformEquicontinuousOn (fun i => extendClosure (u i))
      (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  HolderOnWith.uniformEquicontinuousOn _ hα fun i =>
    (holderOnWith_extendClosure (hu i)).mono subset_closure

/-- Two bounded continuous functions on `closure Ω` whose extensions are within `c` of each other
at each point of `Ω` are within `c` of each other in the uniform distance. -/
private theorem dist_le_of_forall_dist_extendClosure_le
    (u u' : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      dist (extendClosure u x) (extendClosure u' x) ≤ c) :
    dist u u' ≤ c :=
  BoundedContinuousFunction.dist_le_of_forall_mem _ _ hc fun x hx => by
    simpa only [extendClosure_of_mem _ (subset_closure hx)] using h x hx

/-- A sequence of bounded continuous functions on `closure Ω` whose extensions are uniformly Cauchy
on `Ω` is Cauchy for the uniform distance. -/
private theorem cauchySeq_of_uniformCauchySeqOn_extendClosure
    {v : ℕ → closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ}
    (hv : UniformCauchySeqOn (fun k => extendClosure (v k)) atTop
      (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    CauchySeq v := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hv (ε / 2) (half_pos hε)
  exact ⟨N, fun k hk => (dist_le_of_forall_dist_extendClosure_le _ _ (half_pos hε).le
    fun x hx => (hN k hk N le_rfl x hx).le).trans_lt (half_lt_self hε)⟩

variable {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ}

/-- **The frozen-coefficient map on `C(closure Ω)`.** For `v` a bounded continuous function on
`closure Ω`, `continuousFrozenSolution A g ℓ v` is the continuous function on `closure Ω` that
agrees almost everywhere on `Ω` with the weak solution `u` of the linear Dirichlet problem
`-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)` (`TauCeti.PDE.frozenSolution`), when there is one, and `0`
otherwise.

On a bounded Lipschitz domain and for the data of the global Hölder estimate there always is one
(`TauCeti.PDE.eq_continuousFrozenSolution_iff`). -/
def continuousFrozenSolution
    (A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    (v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ) :
    closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ :=
  open scoped Classical in
  if h : ∃ u : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ,
      ∀ᵐ x ∂volume.restrict Omega,
        ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          u ⟨x, hx⟩ = W1p.value (frozenSolution A g ℓ (extendClosure v)) x then
    h.choose
  else 0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
  {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {g : W1p volume Omega 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {K₀ K₁ : ℝ≥0}
  {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {r q : ℝ≥0}

/-- The frozen solutions have representatives that are Hölder on `Ω` with one exponent and one
constant, by the global Hölder estimate applied to the frozen coefficients. -/
private theorem exists_forall_exists_ae_eq_and_holderOnWith
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    ∃ α C : ℝ≥0, 0 < α ∧ ∀ w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      AEStronglyMeasurable w (volume.restrict Omega) →
      ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        W1p.value (frozenSolution A g ℓ w) =ᵐ[volume.restrict Omega] h ∧
          HolderOnWith C α h Omega := by
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  obtain ⟨α, C, hα, -, -, hreg⟩ := hΩ.exists_ae_eq_and_holderOnWith_add_divergence
    (mu := volume) hb (lam := lam) (Lam := Lam) hr (by rwa [hcard]) hq (by rwa [hcard])
  refine ⟨α, _, hα, fun w hw => hreg (UniformlyEllipticOn.apply_of_forall hA w)
    (hw.apply_of_forall_of_continuousAt hAm (hAc.mono fun _ hx => hx.continuousAt)) hf hF
    (frozenSolution_sub_mem_w1p0Submodule hA hAm hAc hb g ℓ hw)
    (fun φ => (forall_energyFormH1_frozenSolution_eq hA hAm hAc hb g ℓ hw φ).trans (hℓ φ))
    hgG hG hG0⟩

/-- Under the hypotheses of the global Hölder estimate, every `T v` agrees almost everywhere on `Ω`
with the frozen solution at `v`, and all the `T v` are Hölder with one exponent and one
constant. -/
private theorem exists_forall_holderWith_and_ae_eq
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    ∃ α C : ℝ≥0, 0 < α ∧ ∀ v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ,
      HolderWith C α (continuousFrozenSolution A g ℓ v) ∧
        ∀ᵐ x ∂volume.restrict Omega,
          ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
            continuousFrozenSolution A g ℓ v ⟨x, hx⟩ =
              W1p.value (frozenSolution A g ℓ (extendClosure v)) x := by
  obtain ⟨α, C, hα, hrep⟩ := exists_forall_exists_ae_eq_and_holderOnWith hΩ hb hr hrn hq hqn hA
    hAm hAc hf hF hℓ hgG hG hG0
  refine ⟨α, C, hα, fun v => ?_⟩
  obtain ⟨h, hvh, hh⟩ := hrep _ (aestronglyMeasurable_extendClosure v)
  obtain ⟨u, hu, hux⟩ := hh.exists_holderWith_boundedContinuousFunction hα hb
  have hspec : ∀ᵐ x ∂volume.restrict Omega,
      ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        u ⟨x, hx⟩ = W1p.value (frozenSolution A g ℓ (extendClosure v)) x := by
    filter_upwards [hvh, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ _
    rw [hx, ← hux x hxΩ]
  have hex : ∃ u : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ,
      ∀ᵐ x ∂volume.restrict Omega,
        ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          u ⟨x, hx⟩ = W1p.value (frozenSolution A g ℓ (extendClosure v)) x := ⟨u, hspec⟩
  have hT : continuousFrozenSolution A g ℓ v = u := by
    rw [continuousFrozenSolution, dite_eq_left hex]
    exact eq_of_ae_eq_of_ae_eq hex.choose_spec hspec
  rw [hT]
  exact ⟨hu, hspec⟩

/-- **The defining property of the frozen-coefficient map on `C(closure Ω)`.** Let `Ω ⊆ ℝⁿ⁺¹` be a
bounded Lipschitz domain, let `r > 1` with `r > (n + 1)/2`, and let `q > 2` with `q > n + 1`.
Let `A` be a Carathéodory coefficient on `Ω` with every `A(·, s)` uniformly elliptic with
constants `λ, Λ`, let `f ∈ Lʳ(Ω)`, `F ∈ L^q(Ω; ℝⁿ⁺¹)` and `ℓ φ = ∫_Ω f φ - ∫_Ω F · ∇φ`,
and let `g ∈ H¹(Ω)` have a value `G` that is bounded and Lipschitz on `Ω`. For
`v ∈ C(closure Ω)` and any `w` agreeing with `v` on `Ω`, a function `u ∈ C(closure Ω)` is
`T v = continuousFrozenSolution A g ℓ v` exactly when it agrees almost everywhere on `Ω` with the
weak solution of `-div (A(x, w) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`. -/
theorem eq_continuousFrozenSolution_iff
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀)
    {v u : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ}
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hw : ∀ x (hx : x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      w x = v ⟨x, subset_closure hx⟩) :
    u = continuousFrozenSolution A g ℓ v ↔
      ∀ᵐ x ∂volume.restrict Omega,
        ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          u ⟨x, hx⟩ = W1p.value (frozenSolution A g ℓ w) x := by
  obtain ⟨α, C, -, hT⟩ := exists_forall_holderWith_and_ae_eq hΩ hb hr hrn hq hqn hA hAm hAc hf
    hF hℓ hgG hG hG0
  -- The frozen solution at `w` is the one at the extension of `v`, as `w` agrees with it on `Ω`.
  have hwv : extendClosure v =ᵐ[volume.restrict Omega] w := by
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    rw [extendClosure_of_mem v (subset_closure hx), hw x hx]
  rw [← frozenSolution_congr_ae hA hAm hAc hb g ℓ (aestronglyMeasurable_extendClosure v) hwv]
  constructor
  · rintro rfl
    exact (hT v).2
  · exact fun hu => eq_of_ae_eq_of_ae_eq hu (hT v).2

/-- **A uniform Hölder bound for the frozen-coefficient map.** Under the hypotheses of
`TauCeti.PDE.eq_continuousFrozenSolution_iff`, there are `α > 0` and `C` such that every
`continuousFrozenSolution A g ℓ v`, `v ∈ C(closure Ω)`, is `α`-Hölder on `closure Ω` with
constant `C`. -/
theorem exists_holderWith_continuousFrozenSolution
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    ∃ α C : ℝ≥0, 0 < α ∧ ∀ v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ,
      HolderWith C α (continuousFrozenSolution A g ℓ v) := by
  obtain ⟨α, C, hα, hT⟩ := exists_forall_holderWith_and_ae_eq hΩ hb hr hrn hq hqn hA hAm hAc hf
    hF hℓ hgG hG hG0
  exact ⟨α, C, hα, fun v => (hT v).1⟩

/-- **The frozen-coefficient map is continuous on `C(closure Ω)`.** Under the hypotheses of
`TauCeti.PDE.eq_continuousFrozenSolution_iff`, `continuousFrozenSolution A g ℓ` is continuous for
the uniform norm on `C(closure Ω)`. -/
theorem continuous_continuousFrozenSolution
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    Continuous (continuousFrozenSolution A g ℓ) := by
  obtain ⟨α, C, hα, hT⟩ := exists_forall_holderWith_and_ae_eq hΩ hb hr hrn hq hqn hA hAm hAc hf
    hF hℓ hgG hG hG0
  rw [continuous_iff_continuousAt]
  intro v
  -- The values of the frozen solutions converge in `L²(Ω)`, by dominated convergence.
  have hL2 : Tendsto (fun w => W1p.value (frozenSolution A g ℓ (extendClosure w))) (𝓝 v)
      (𝓝 (W1p.value (frozenSolution A g ℓ (extendClosure v)))) := by
    simp only [← W1p.valueL_apply]
    refine (W1p.valueL.continuous.tendsto _).comp (tendsto_frozenSolution (A' := fun _ => A)
      (g' := fun _ => g) (ℓ' := fun _ => ℓ) hA hAm hAc (fun _ => hA) (fun _ => hAm)
      (fun _ => hAc) hb (aestronglyMeasurable_extendClosure v)
      (fun w => aestronglyMeasurable_extendClosure w) ?_ tendsto_const_nhds tendsto_const_nhds)
    filter_upwards [hAc, ae_restrict_mem Omega.isOpen.measurableSet] with x hcx hx
    simp only [extendClosure_of_mem _ (subset_closure hx)]
    exact (hcx.tendsto _).comp ((continuous_eval_const _).tendsto v)
  -- So the continuous representatives converge in measure on `Ω`, hence uniformly on `Ω`.
  have hmeas : TendstoInMeasure (volume.restrict Omega)
      (fun w => extendClosure (continuousFrozenSolution A g ℓ w)) (𝓝 v)
      (extendClosure (continuousFrozenSolution A g ℓ v)) :=
    (tendstoInMeasure_of_tendsto_Lp hL2).congr'
      (Eventually.of_forall fun w => (extendClosure_ae_eq (hT w).2).symm)
      (extendClosure_ae_eq (hT v).2).symm
  have hunif := hmeas.tendstoUniformlyOn_of_uniformEquicontinuousOn Omega.isOpen
    (hb.isCompact_closure.totallyBounded.subset subset_closure)
    (uniformEquicontinuousOn_extendClosure hα fun w => (hT w).1)
    (((holderOnWith_extendClosure (hT v).1).mono subset_closure).uniformContinuousOn hα)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif (ε / 2) (half_pos hε)] with w hw
  refine (dist_le_of_forall_dist_extendClosure_le _ _ (half_pos hε).le
    fun x hx => ?_).trans_lt (half_lt_self hε)
  rw [dist_comm]
  exact (hw x hx).le

/-- **The frozen-coefficient map is compact on `C(closure Ω)`.** Under the hypotheses of
`TauCeti.PDE.eq_continuousFrozenSolution_iff`, the range of `continuousFrozenSolution A g ℓ` is
relatively compact in `C(closure Ω)`. -/
theorem isCompact_closure_range_continuousFrozenSolution
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    IsCompact (closure (range (continuousFrozenSolution A g ℓ))) := by
  obtain ⟨α, C, hα, hT⟩ := exists_forall_holderWith_and_ae_eq hΩ hb hr hrn hq hqn hA hAm hAc hf
    hF hℓ hgG hG hG0
  refine (totallyBounded_of_forall_exists_cauchySeq fun u hu => ?_).closure.isCompact_of_isClosed
    isClosed_closure
  choose v hv using hu
  -- The values of the frozen solutions lie in a compact subset of `L²(Ω)`.
  have hψ : ∀ k, W1p.value (frozenSolution A g ℓ (extendClosure (v k))) ∈
      closure (range fun w : Lp ℝ 2
        (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) =>
          W1p.value (frozenSolution A g ℓ w)) := fun k =>
    subset_closure ⟨(memLp_extendClosure hb (v k)).toLp _, by
      dsimp only
      rw [frozenSolution_congr_ae hA hAm hAc hb g ℓ (Lp.aestronglyMeasurable _)
        (memLp_extendClosure hb (v k)).coeFn_toLp]⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_closure_range_value_frozenSolution hA hAm hAc hb g ℓ).tendsto_subseq hψ
  refine ⟨φ, hφ, ?_⟩
  -- Along the subsequence, the continuous representatives converge in measure on `Ω`, so they
  -- are uniformly Cauchy on `Ω`.
  have hmeas : TendstoInMeasure (volume.restrict Omega)
      (fun k => extendClosure (continuousFrozenSolution A g ℓ (v (φ k)))) atTop a :=
    (tendstoInMeasure_of_tendsto_Lp hlim).congr'
      (Eventually.of_forall fun k => (extendClosure_ae_eq (hT _).2).symm) .rfl
  have hcauchy := hmeas.uniformCauchySeqOn_of_uniformEquicontinuousOn Omega.isOpen
    (hb.isCompact_closure.totallyBounded.subset subset_closure)
    (uniformEquicontinuousOn_extendClosure hα fun k => (hT _).1)
  simpa only [comp_def, hv] using cauchySeq_of_uniformCauchySeqOn_extendClosure hcauchy

/-- **The fixed points of the frozen-coefficient map are the solutions.** Under the hypotheses of
`TauCeti.PDE.eq_continuousFrozenSolution_iff`, `v ∈ C(closure Ω)` is a fixed point of
`continuousFrozenSolution A g ℓ` exactly when it agrees almost everywhere on `Ω` with a weak
solution `u ∈ H¹(Ω)` of the quasilinear problem `-div (A(x, u) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`. -/
theorem isFixedPt_continuousFrozenSolution_iff
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀)
    {v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ} :
    IsFixedPt (continuousFrozenSolution A g ℓ) v ↔
      ∃ u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
        (∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ) ∧
        ∀ᵐ x ∂volume.restrict Omega,
          ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
            v ⟨x, hx⟩ = W1p.value u x := by
  obtain ⟨α, C, -, hT⟩ := exists_forall_holderWith_and_ae_eq hΩ hb hr hrn hq hqn hA hAm hAc hf
    hF hℓ hgG hG hG0
  have hv := aestronglyMeasurable_extendClosure v
  constructor
  · intro hfix
    have hspec := (hT v).2
    rw [hfix.eq] at hspec
    refine ⟨frozenSolution A g ℓ (extendClosure v),
      frozenSolution_sub_mem_w1p0Submodule hA hAm hAc hb g ℓ hv, fun φ => ?_, hspec⟩
    -- The value of the frozen solution is `v`, so the frozen coefficient is `A(x, u)`.
    rw [energyFormH1_congr_ae
      ((extendClosure_ae_eq hspec).mono fun x hx => congrArg (A x) hx.symm) .rfl .rfl]
    exact forall_energyFormH1_frozenSolution_eq hA hAm hAc hb g ℓ hv φ
  · rintro ⟨u, hug, hu, hvu⟩
    have hval : extendClosure v =ᵐ[volume.restrict Omega] W1p.value u := extendClosure_ae_eq hvu
    -- `u` solves the problem frozen at `v`, so it is the frozen solution there.
    have hfrozen : u = frozenSolution A g ℓ (extendClosure v) :=
      eq_frozenSolution_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hA hAm hAc hb hv hug
        fun φ => by
          rw [energyFormH1_congr_ae (hval.mono fun x hx => congrArg (A x) hx) .rfl .rfl]
          exact hu φ
    rw [hfrozen] at hvu
    exact eq_of_ae_eq_of_ae_eq (hT v).2 hvu

/-- **Schauder's theorem for the frozen-coefficient map.** Under the hypotheses of
`TauCeti.PDE.eq_continuousFrozenSolution_iff`, `continuousFrozenSolution A g ℓ` has a fixed point
in `C(closure Ω)`; by `TauCeti.PDE.isFixedPt_continuousFrozenSolution_iff` it is the continuous
representative on `closure Ω` of a weak solution of the quasilinear problem. -/
theorem exists_isFixedPt_continuousFrozenSolution
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    ∃ v, IsFixedPt (continuousFrozenSolution A g ℓ) v := by
  have hK := isCompact_closure_range_continuousFrozenSolution hΩ hb hr hrn hq hqn hA hAm hAc hf
    hF hℓ hgG hG hG0
  rw [← image_univ] at hK
  obtain ⟨v, -, hv⟩ := schauderFixedPoint_closedConvex_continuousOn isClosed_univ convex_univ
    univ_nonempty (continuous_continuousFrozenSolution hΩ hb hr hrn hq hqn hA hAm hAc hf hF hℓ
      hgG hG hG0).continuousOn (mapsTo_univ _ _) hK
  exact ⟨v, hv⟩

/-- **The continuous solutions of the quasilinear problem form a compact set.** Under the
hypotheses of `TauCeti.PDE.eq_continuousFrozenSolution_iff`, the fixed points of
`continuousFrozenSolution A g ℓ` form a compact subset of `C(closure Ω)`. By
`TauCeti.PDE.isFixedPt_continuousFrozenSolution_iff` they are the continuous representatives on
`closure Ω` of the weak solutions of `-div (A(x, u) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, and by
`TauCeti.PDE.exists_isFixedPt_continuousFrozenSolution` there is one. -/
theorem isCompact_fixedPoints_continuousFrozenSolution
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hf : MemLp f r (volume.restrict Omega)) (hF : MemLp F q (volume.restrict Omega))
    (hℓ : ∀ φ : W1p0 volume Omega 2,
      ℓ φ = ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hgG : W1p.value g =ᵐ[volume.restrict Omega] G)
    (hG : LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) :
    IsCompact (fixedPoints (continuousFrozenSolution A g ℓ)) :=
  (isCompact_closure_range_continuousFrozenSolution hΩ hb hr hrn hq hqn hA hAm hAc hf hF hℓ hgG
    hG hG0).of_isClosed_subset
    (isClosed_fixedPoints (continuous_continuousFrozenSolution hΩ hb hr hrn hq hqn hA hAm hAc hf
      hF hℓ hgG hG hG0))
    fun v hv => subset_closure ⟨v, hv⟩

/-! ### Stability of the continuous solutions under perturbation of the data -/

/-- The continuous representatives on `closure Ω` of the weak solutions of quasilinear problems
are `α`-Hölder with one exponent, and with a constant depending only on bounds `M` for the norms
of `f` and `F` and on the bound `K₀` and Lipschitz constant `K₁` of the boundary values. This is
the global Hölder estimate, read on `C(closure Ω)`. -/
private theorem exists_forall_holderWith_of_ae_eq_value
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ 0 < C ∧
      ∀ {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
        {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {u g : W1p volume Omega 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {M K₀ K₁ : ℝ≥0}
        {v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ},
        (∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
          (fun x => A x s) lam Lam) →
        (∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega)) →
        (∀ᵐ x ∂volume.restrict Omega, Continuous (A x)) →
        MemLp f r (volume.restrict Omega) → MemLp F q (volume.restrict Omega) →
        eLpNorm f r (volume.restrict Omega) ≤ M → eLpNorm F q (volume.restrict Omega) ≤ M →
        u - g ∈ w1p0Submodule volume Omega 2 →
        (∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u (φ : W1p volume Omega 2) =
            ∫ x in Omega, f x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
              ∫ x in Omega, ⟪F x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume) →
        W1p.value g =ᵐ[volume.restrict Omega] G →
        LipschitzOnWith K₁ G (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
        (∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) →
        (∀ᵐ x ∂volume.restrict Omega,
          ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
            v ⟨x, hx⟩ = W1p.value u x) →
        HolderWith (C * (M / lam + M / lam + K₀ + K₁)).toNNReal α v := by
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  obtain ⟨α, C, hα, -, hC, hreg⟩ :=
    hΩ.exists_ae_eq_and_holderOnWith_quasilinear (mu := volume) hb (lam := lam) (Lam := Lam) hr
      (by rwa [hcard]) hq (by rwa [hcard])
  refine ⟨α, C, hα, hC, fun {A f F u g G M K₀ K₁ v} hA hAm hAc hf hF hfM hFM hug hu hgG hG hG0
    hv => ?_⟩
  obtain ⟨h, huh, hh⟩ := hreg hA hAm hAc hf hF hug hu hgG hG hG0
  -- The Hölder constant of the estimate is monotone in the norms of the data.
  have hlam := (hA 0).pos
  have hf' : (eLpNorm f r (volume.restrict Omega)).toReal / lam ≤ M / lam :=
    (div_le_div_iff_of_pos_right hlam).2 (ENNReal.toReal_le_coe_of_le_coe hfM)
  have hF' : (eLpNorm F q (volume.restrict Omega)).toReal / lam ≤ M / lam :=
    (div_le_div_iff_of_pos_right hlam).2 (ENNReal.toReal_le_coe_of_le_coe hFM)
  have hK := Real.toNNReal_le_toNNReal
    (mul_le_mul_of_nonneg_left (by linarith : (eLpNorm f r (volume.restrict Omega)).toReal / lam +
      (eLpNorm F q (volume.restrict Omega)).toReal / lam + K₀ + K₁ ≤ M / lam + M / lam + K₀ + K₁)
      hC.le)
  -- The Hölder representative extends to `closure Ω`, where it is `v`.
  obtain ⟨w, hw, hwh⟩ := (hh.mono_const hK).exists_holderWith_boundedContinuousFunction hα hb
  have hvw : v = w := eq_of_ae_eq_of_ae_eq hv <| by
    filter_upwards [huh, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ _
    rw [hx, ← hwh x hxΩ]
  rw [hvw]
  exact hw

section Stability

variable {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {fn : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
  {Fn : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {gn : ℕ → W1p volume Omega 2} {Gn : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
  {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)} {M : ℝ≥0}

/-- **Stability of the quasilinear Dirichlet problem in `C(closure Ω)`.** Let `Ω ⊆ ℝⁿ⁺¹` be a
bounded Lipschitz domain, let `r > 1` with `r > (n + 1)/2`, and let `q > 2` with `q > n + 1`. Let
`Aₖ` be Carathéodory coefficients on `Ω`, uniformly elliptic and bounded with common constants
`λ, Λ`, converging for almost every `x ∈ Ω` locally uniformly in the second variable to a
coefficient `A` with the same bounds. Let the forcings `ℓₖ φ = ∫_Ω fₖ φ - ∫_Ω Fₖ · ∇φ` converge,
`ℓₖ → ℓ` in `H⁻¹(Ω)`, with `‖fₖ‖_{Lʳ(Ω)}` and `‖Fₖ‖_{L^q(Ω)}` bounded by one constant `M`, and let
the boundary values converge, `gₖ → g` in `H¹(Ω)`, with values `Gₖ` bounded by one constant `K₀`
and Lipschitz on `Ω` with one constant `K₁`.

If each `uₖ ∈ H¹(Ω)` solves the problem with data `(Aₖ, gₖ, ℓₖ)`,

`-div (Aₖ(x, uₖ) ∇uₖ) = ℓₖ` in `Ω`, `uₖ - gₖ ∈ H¹₀(Ω)`,

and `vₖ ∈ C(closure Ω)` agrees almost everywhere on `Ω` with `uₖ`, then along a subsequence `uₖ`
converges in `H¹(Ω)` to a solution `u` of the problem with data `(A, g, ℓ)` and `vₖ` converges
uniformly on `closure Ω` to a `v ∈ C(closure Ω)` agreeing almost everywhere on `Ω` with `u`. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq_of_ae_eq
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hfn : ∀ k, MemLp (fn k) r (volume.restrict Omega))
    (hFn : ∀ k, MemLp (Fn k) q (volume.restrict Omega))
    (hfM : ∀ k, eLpNorm (fn k) r (volume.restrict Omega) ≤ M)
    (hFM : ∀ k, eLpNorm (Fn k) q (volume.restrict Omega) ≤ M)
    (hℓn : ∀ k (φ : W1p0 volume Omega 2),
      ℓn k φ = ∫ x in Omega, fn k x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪Fn k x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hℓ : Tendsto ℓn atTop (𝓝 ℓ))
    (hgG : ∀ k, W1p.value (gn k) =ᵐ[volume.restrict Omega] Gn k)
    (hG : ∀ k, LipschitzOnWith K₁ (Gn k) (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ k, ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |Gn k x| ≤ K₀)
    (hg : Tendsto gn atTop (𝓝 g)) {un : ℕ → W1p volume Omega 2}
    (hun : ∀ k, un k - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value (un k) x)) 0 0 (un k) φ = ℓn k φ)
    {vn : ℕ → closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ}
    (hvn : ∀ k, ∀ᵐ x ∂volume.restrict Omega,
      ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        vn k ⟨x, hx⟩ = W1p.value (un k) x) :
    ∃ u : W1p volume Omega 2,
      (u - g ∈ w1p0Submodule volume Omega 2 ∧
        ∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ) ∧
      ∃ v : closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ,
        (∀ᵐ x ∂volume.restrict Omega,
          ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
            v ⟨x, hx⟩ = W1p.value u x) ∧
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun j => un (ψ j)) atTop (𝓝 u) ∧
          Tendsto (fun j => vn (ψ j)) atTop (𝓝 v) := by
  have : IsFiniteMeasure (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  -- The `vₖ` are Hölder with one exponent and one constant.
  obtain ⟨α, C, hα, -, hhol⟩ := exists_forall_holderWith_of_ae_eq_value (lam := lam) (Lam := Lam)
    hΩ hb hr hrn hq hqn
  have hT (k : ℕ) := hhol (hAn k) (hAnm k) (hAnc k) (hfn k) (hFn k) (hfM k) (hFM k) (hun k).1
    (fun φ => ((hun k).2 φ).trans (hℓn k φ)) (hgG k) (hG k) (hG0 k) (hvn k)
  -- By the stability theorem in `H¹(Ω)`, a subsequence of the `uₖ` converges to a solution `u`,
  -- so their values converge to that of `u` in `L²(Ω)`, hence in measure.
  obtain ⟨u, hu, ψ, hψ, hlim⟩ :=
    exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq hA hAn hAnm
      hAnc hAlim hb hg hℓ hun
  have hL2 : Tendsto (fun j => W1p.value (un (ψ j))) atTop (𝓝 (W1p.value u)) := by
    simpa only [comp_def, W1p.valueL_apply] using (W1p.valueL.continuous.tendsto u).comp hlim
  have hmeas : TendstoInMeasure (volume.restrict Omega)
      (fun j => extendClosure (vn (ψ j))) atTop (W1p.value u) :=
    (tendstoInMeasure_of_tendsto_Lp hL2).congr'
      (Eventually.of_forall fun j => (extendClosure_ae_eq (hvn _)).symm) .rfl
  -- The `vₖ` are uniformly equicontinuous, so the subsequence converges in `C(closure Ω)`.
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete <|
    cauchySeq_of_uniformCauchySeqOn_extendClosure <|
      hmeas.uniformCauchySeqOn_of_uniformEquicontinuousOn Omega.isOpen
        (hb.isCompact_closure.totallyBounded.subset subset_closure)
        (uniformEquicontinuousOn_extendClosure hα fun j => hT (ψ j))
  -- The uniform limit `v` is also the limit in measure, so it agrees with `u`.
  have hmeas' : TendstoInMeasure (volume.restrict Omega)
      (fun j => extendClosure (vn (ψ j))) atTop (extendClosure v) :=
    tendstoInMeasure_of_tendsto_ae (fun j => aestronglyMeasurable_extendClosure _)
      ((ae_restrict_iff' Omega.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx => by
        simp only [extendClosure_of_mem _ (subset_closure hx)]
        exact ((continuous_eval_const _).tendsto v).comp hv)
  refine ⟨u, hu, v, ?_, ψ, hψ, hlim, hv⟩
  filter_upwards [tendstoInMeasure_ae_unique hmeas' hmeas] with x hx hxc
  rw [← extendClosure_of_mem v hxc, hx]

/-- **Upper semicontinuity in `C(closure Ω)` of the continuous solutions.** Under the
hypotheses of
`exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq_of_ae_eq`, in
the `TauCeti.PDE` namespace, let `U` be an open subset of `C(closure Ω)` containing the continuous
representative on `closure Ω` of every weak solution of the limit problem with data `(A, g, ℓ)`.
Then for all large `k`, `U` contains the continuous representative of every weak solution of the
problem with data `(Aₖ, gₖ, ℓₖ)`. -/
theorem eventually_setOf_exists_forall_energyFormH1_quasilinear_eq_subset
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hr : 1 < r) (hrn : (n + 1 : ℝ) < 2 * r) (hq : 2 < (q : ℝ)) (hqn : (n + 1 : ℝ) < q)
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hfn : ∀ k, MemLp (fn k) r (volume.restrict Omega))
    (hFn : ∀ k, MemLp (Fn k) q (volume.restrict Omega))
    (hfM : ∀ k, eLpNorm (fn k) r (volume.restrict Omega) ≤ M)
    (hFM : ∀ k, eLpNorm (Fn k) q (volume.restrict Omega) ≤ M)
    (hℓn : ∀ k (φ : W1p0 volume Omega 2),
      ℓn k φ = ∫ x in Omega, fn k x * W1p.value (φ : W1p volume Omega 2) x ∂volume -
        ∫ x in Omega, ⟪Fn k x, W1p.gradient (φ : W1p volume Omega 2) x⟫ ∂volume)
    (hℓ : Tendsto ℓn atTop (𝓝 ℓ))
    (hgG : ∀ k, W1p.value (gn k) =ᵐ[volume.restrict Omega] Gn k)
    (hG : ∀ k, LipschitzOnWith K₁ (Gn k) (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hG0 : ∀ k, ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), |Gn k x| ≤ K₀)
    (hg : Tendsto gn atTop (𝓝 g))
    {U : Set (closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) →ᵇ ℝ)} (hU : IsOpen U)
    (hSU : {v | ∃ u : W1p volume Omega 2,
      (u - g ∈ w1p0Submodule volume Omega 2 ∧
        ∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ) ∧
      ∀ᵐ x ∂volume.restrict Omega,
        ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          v ⟨x, hx⟩ = W1p.value u x} ⊆ U) :
    ∀ᶠ k in atTop, {v | ∃ u : W1p volume Omega 2,
      (u - gn k ∈ w1p0Submodule volume Omega 2 ∧
        ∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => An k x (W1p.value u x)) 0 0 u φ = ℓn k φ) ∧
      ∀ᵐ x ∂volume.restrict Omega,
        ∀ hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          v ⟨x, hx⟩ = W1p.value u x} ⊆ U := by
  by_contra h
  -- Otherwise a subsequence of problems has continuous solutions `vⱼ ∉ U`.
  obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop (not_eventually.1 h)
  choose vn hvn hvnU using fun j => not_subset.1 (hψU j)
  simp only [mem_ofPred_eq] at hvn
  choose un hun hvun using hvn
  have hψt := hψ.tendsto_atTop
  obtain ⟨u, hu, v, hvu, _, -, -, hlim⟩ :=
    exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq_of_ae_eq
      (An := fun j => An (ψ j)) (fn := fun j => fn (ψ j)) (Fn := fun j => Fn (ψ j))
      (gn := fun j => gn (ψ j)) (Gn := fun j => Gn (ψ j)) (ℓn := fun j => ℓn (ψ j)) hΩ hb hr hrn
      hq hqn hA (fun j => hAn (ψ j)) (fun j => hAnm (ψ j)) (fun j => hAnc (ψ j))
      (hAlim.mono fun _ hx => hx.comp_tendsto hψt) (fun j => hfn (ψ j)) (fun j => hFn (ψ j))
      (fun j => hfM (ψ j)) (fun j => hFM (ψ j)) (fun j => hℓn (ψ j)) (hℓ.comp hψt)
      (fun j => hgG (ψ j)) (fun j => hG (ψ j)) (fun j => hG0 (ψ j)) (hg.comp hψt) hun hvun
  -- The limit is a continuous solution of the limit problem, so lies in the open set `U`, and so
  -- do the `vⱼ` for large `j`.
  obtain ⟨j, hj⟩ := (hlim.eventually (hU.mem_nhds (hSU ⟨u, hu, hvu⟩))).exists
  exact hvnU _ hj

end Stability

end PDE

end TauCeti
