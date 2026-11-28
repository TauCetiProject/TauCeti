/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Analysis.Convex.CCHypersurface.Regular.Basic
import TauCeti.Analysis.Convex.CCHypersurface.Zajicek
import TauCeti.Analysis.Convex.EffectiveDomain

/-!
# Differentiability characterization of `c - c`-regular measures

On a finite-dimensional real inner product space `E`, Zajíček's covering theorem
(`TauCeti.exists_convexOn_subset_not_differentiableAt_iff`) characterizes `c - c`-regularity
(`TauCeti.IsCCRegular`) by almost-everywhere differentiability of convex functions and yields
almost-everywhere differentiability of extended-real convex functions on their effective domains.

## Main statements

* `TauCeti.isCCRegular_iff_forall_convexOn_ae_differentiableAt` — `IsCCRegular μ` iff every convex
  `u : E → ℝ` is differentiable `μ`-almost everywhere;
* `TauCeti.IsCCRegular.ae_eventually_ne_top_and_differentiableAt_toReal` — almost-everywhere
  differentiability of extended-real convex functions on their effective domains;
* `TauCeti.isCCRegular_iff_forall_convex_ae_differentiableAt` — `IsCCRegular μ` iff every
  extended-real function `u : E → EReal` with convex real epigraph has `u.toReal` differentiable
  `μ`-almost everywhere on `{x | u x ≠ ⊤}`.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.25.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

section Differentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- **Differentiability characterization of `c - c`-regularity.** By Zajíček's theorem
(`TauCeti.exists_convexOn_subset_not_differentiableAt_iff`), a measure `μ` on a finite-dimensional
real inner product space `E` is `c - c`-regular iff every convex `u : E → ℝ` is differentiable
`μ`-almost everywhere. -/
theorem isCCRegular_iff_forall_convexOn_ae_differentiableAt {μ : Measure E} :
    IsCCRegular μ ↔ ∀ u : E → ℝ, ConvexOn ℝ univ u → ∀ᵐ x ∂μ, DifferentiableAt ℝ u x :=
  ⟨fun hμ u hu => let ⟨C, hC, hCs, hsub⟩ :=
      exists_convexOn_subset_not_differentiableAt_iff.1 ⟨u, hu, Subset.rfl⟩
    ae_iff.2 (hμ.measure_eq_zero_of_subset_sUnion hC hCs hsub),
   fun h => (isCCRegular_def μ).2 fun s hs =>
    let ⟨u, hu, hsub⟩ := (exists_convexOn_subset_not_differentiableAt_iff (A := s)).2
      ⟨{s}, countable_singleton s, by simpa, by simp⟩
    measure_mono_null hsub (ae_iff.1 (h u hu))⟩

/-- **Almost-everywhere differentiability of extended-real convex functions against a
`c - c`-regular measure.** By Zajíček's covering theorems, for any extended-real `u : E → EReal`
with convex real epigraph and any `c - c`-regular `μ`, at `μ`-a.e. `x` with `u x ≠ ⊤`, `u ≠ ⊤` near
`x` and `u.toReal` is differentiable at `x` (needing no `u x ≠ ⊥` hypothesis, unlike
`TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`). -/
theorem IsCCRegular.ae_eventually_ne_top_and_differentiableAt_toReal {μ : Measure E}
    (hμ : IsCCRegular μ) {u : E → EReal} (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) :
    ∀ᵐ x ∂μ, u x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
  let D : Set E := {x | u x ≠ ⊤}
  obtain ⟨C₁, hC₁, hs₁, hfr⟩ :=
    (convex_setOf_ne_top hconv).exists_countable_isCCHypersurface_cover_frontier
  obtain ⟨C₂, hC₂, hs₂, hnd⟩ :=
    exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal hconv
  have hdiff : D \ interior D ⊆ ⋃₀ C₁ := fun _ hx => hfr ⟨subset_closure hx.1, hx.2⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hμ.measure_eq_zero_of_subset_sUnion hC₁ hs₁
      hdiff),
    measure_eq_zero_iff_ae_notMem.1 (hμ.measure_eq_zero_of_subset_sUnion hC₂ hs₂ hnd)] with
    x hx₁ hx₂ hxD
  have hx_int : x ∈ interior D := by by_contra hni; exact hx₁ ⟨hxD, hni⟩
  exact ⟨mem_interior_iff_mem_nhds.1 hx_int, by by_contra hndiff; exact hx₂ ⟨hx_int, hndiff⟩⟩

/-- **Extended-real differentiability characterization of `c - c`-regularity.** A measure `μ` on a
finite-dimensional real inner product space `E` is `c - c`-regular iff for every extended-real
function `u : E → EReal` with convex real epigraph (with no `⊥` exclusion), `x' ↦ (u x').toReal`
is differentiable `μ`-almost everywhere on `{x | u x ≠ ⊤}`. -/
theorem isCCRegular_iff_forall_convex_ae_differentiableAt {μ : Measure E} :
    IsCCRegular μ ↔
      ∀ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} →
        ∀ᵐ x ∂μ, u x ≠ ⊤ → DifferentiableAt ℝ (fun x' => (u x').toReal) x :=
  ⟨fun hμ _ hconv => (hμ.ae_eventually_ne_top_and_differentiableAt_toReal hconv).mono
      fun _ hx htop => (hx htop).2,
   fun h => isCCRegular_iff_forall_convexOn_ae_differentiableAt.2 fun v hv => by
     simpa [EReal.toReal_coe] using
       h (fun x => (v x : EReal)) (convexOn_iff_convex_epigraph_coe.1 hv)⟩

end Differentiability

end TauCeti
