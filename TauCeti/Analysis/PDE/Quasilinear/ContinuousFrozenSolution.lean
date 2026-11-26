/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Analysis.PDE.Quasilinear.GlobalHolder
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure.UniformConvergence
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.ContinuousMap.Bounded.Closure
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Equicontinuity
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
  there is one, by Schauder's theorem (`TauCeti.PDE.exists_isFixedPt_continuousFrozenSolution`).
  The fixed points form a closed set, since `T` is continuous (`isClosed_fixedPoints`).

So `T` is a compact continuous self-map of the Banach space `C(closure Ω)`, the map of the classical
Schauder approach to quasilinear equations. Its continuity and compactness come from those of the
frozen solutions in `L²(Ω)` (`TauCeti.PDE.continuous_value_frozenSolution`,
`TauCeti.PDE.isCompact_closure_range_value_frozenSolution`): the Hölder representatives form a
uniformly equicontinuous family, so their convergence in measure on `Ω` is uniform
(`MeasureTheory.TendstoInMeasure.tendstoUniformlyOn_of_uniformEquicontinuousOn`), and uniform
convergence on `Ω` is convergence in `C(closure Ω)`.

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
    (HolderOnWith.uniformEquicontinuousOn _ hα fun w =>
      (holderOnWith_extendClosure (hT w).1).mono subset_closure)
    (((holderOnWith_extendClosure (hT v).1).mono subset_closure).uniformContinuousOn hα)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif (ε / 2) (half_pos hε)] with w hw
  refine (BoundedContinuousFunction.dist_le_of_forall_mem _ _ (half_pos hε).le
    fun x hx => ?_).trans_lt (half_lt_self hε)
  rw [dist_comm]
  simpa only [extendClosure_of_mem _ (subset_closure hx)] using (hw x hx).le

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
    (HolderOnWith.uniformEquicontinuousOn _ hα fun k =>
      (holderOnWith_extendClosure (hT _).1).mono subset_closure)
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hcauchy (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  simp only [comp_apply, ← hv]
  refine (BoundedContinuousFunction.dist_le_of_forall_mem _ _ (half_pos hε).le
    fun x hx => ?_).trans_lt (half_lt_self hε)
  simpa only [extendClosure_of_mem _ (subset_closure hx)] using (hN k hk N le_rfl x hx).le

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

end PDE

end TauCeti
