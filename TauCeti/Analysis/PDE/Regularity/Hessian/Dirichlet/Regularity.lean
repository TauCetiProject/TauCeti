/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.CurvedBoundary.Regularity
public import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Exponent

/-!
# `W^{2,q}` regularity of strong solutions of the Dirichlet problem

Let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary and let

`L u = tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u`

with `A` continuous up to the boundary and elliptic there, and `b`, `c` bounded and measurable.
This file proves Gilbarg–Trudinger's Lemma 9.16 in the form stated there: for `1 < p ≤ q < ∞`, a
solution `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` of `L u = f` with `f ∈ L^q(Ω)` lies in
`W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)` (in the `TauCeti` namespace,
`exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq`).
It adds the boundary condition at the larger exponent to
`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph`, which
places `u` in `W^{2,q}(Ω)`: zero boundary values pass from `W^{1,p}_0(Ω)` to `W^{1,q}_0(Ω)` since
the trace does not depend on the exponent (`TauCeti.W1p.mem_w1p0Submodule_of_value_ae_eq`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace Module
open scoped ENNReal NNReal

namespace TauCeti

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  {Omega : Opens (WithLp 2 (ℝ × E))}
  {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
  {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ} {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
  {f : WithLp 2 (ℝ × E) → ℝ}

/-- **`W^{2,q}` regularity of strong solutions of the Dirichlet problem** (Gilbarg–Trudinger,
Lemma 9.16). Let `1 < p ≤ q < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary.
Let `A` be continuous within `Ω` and elliptic at every point of `closure Ω`, and let `b`, `c` be
measurable and bounded. If `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solves
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `Ω` with `f ∈ L^q(Ω)`, then
`u ∈ W^{2,q}(Ω) ∩ W^{1,q}_0(Ω)`: some `v ∈ W^{2,q}(Ω)` with zero boundary values has the value and
the weak Hessian of `u`. -/
theorem exists_firstOrder_mem_w1p0Submodule_and_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq
    (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2}
    (hu0 : firstOrder 1 u ∈ w1p0Submodule volume Omega p)
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
        ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x)
    (hpq : p ≤ q) (hq_top : q ≠ ⊤)
    (hf : MemLp f q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))) :
    ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega q 2,
      firstOrder 1 v ∈ w1p0Submodule volume Omega q ∧
      (value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
        value 2 u ∧
      (iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
        =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] iteratedGradient 1 u := by
  obtain ⟨v, hv, hvD⟩ :=
    exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph hp hp_top
      (hp.trans_le hpq) hq_top hΩ hbdry hcont hell hb hbβ hc hcγ u hu0 hf heq
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_of_isBounded_of_contDiff one_le_two hΩ hbdry
  refine ⟨v, W1p.mem_w1p0Submodule_of_value_ae_eq hp_top hq_top hpq hL hΩ hu0 ?_, hv, hvD⟩
  rw [value_firstOrder, value_firstOrder]
  exact hv.symm

end TauCeti

end
