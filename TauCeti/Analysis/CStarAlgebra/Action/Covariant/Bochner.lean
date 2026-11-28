/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1

/-!
# Pointwise Bochner formulas and integrand summability for covariant representations

Let `P = (π, U)` be a covariant representation of a C⋆-dynamical system `(G, A, α)` on a Hilbert
space `H`. For a locally compact topological group `G` and a left-invariant Borel measure `μ` finite
on compact sets, inner regular with respect to compact sets on finite-measure sets, and satisfying
`μ.inv ≪ μ` (in particular for both inner regular and regular Haar measures), combining
`TauCeti.CStarAction.CovariantRepresentation.integratedOperatorBochnerL1` with the pointwise Bochner
twisted convolution and involution formulas in
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner` shows that `integratedOperatorBochnerL1`
turns `bochnerConvolution` and `bochnerInvolution` of integrable functions into operator
composition and adjoint.

On any topological group (without separation, measurability, or countability assumptions), a
norm-summable family `f : G → A` yields unconditionally norm-summable and summable Hilbert-space
terms `s ↦ π(f s)(U_s v)`. (For the counting-measure `HasSum` and `tsum` formulas on `R₁` Borel
groups, see `TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1`.)

## Main statements

* `TauCeti.CStarAction.CovariantRepresentation.integratedOperatorBochnerL1_bochnerConvolution` and
  `TauCeti.CStarAction.CovariantRepresentation.integratedOperatorBochnerL1_bochnerInvolution`:
  multiplicativity and star-preservation on integrable functions via `bochnerConvolution` and
  `bochnerInvolution`.
* `TauCeti.CStarAction.CovariantRepresentation.summable_norm_integrand_of_summable_norm` and
  `TauCeti.CStarAction.CovariantRepresentation.summable_integrand_of_summable_norm`: norm and
  vector summability of `s ↦ π(f s)(U_s v)` for any norm-summable `f : G → A`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs **134**,
  American Mathematical Society (2007), Proposition 2.23.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

section BochnerOps

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- Multiplicativity of `integratedOperatorBochnerL1` for Bochner twisted convolution of integrable
functions on a locally compact group with a left-invariant Borel measure `μ` finite on compact sets,
inner regular with respect to compact sets on finite-measure sets, and satisfying `μ.inv ≪ μ` (in
particular for inner regular or regular Haar measures via
`Measure.inv_absolutelyContinuous_of_innerRegular` and
`Measure.inv_absolutelyContinuous_of_regular`). -/
theorem integratedOperatorBochnerL1_bochnerConvolution {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    P.integratedOperatorBochnerL1 μ
      ((α.integrable_bochnerConvolution hinv hf hg).toL1
        (α.bochnerConvolution μ f g)) =
      P.integratedOperatorBochnerL1 μ (hf.toL1 f) *
        P.integratedOperatorBochnerL1 μ (hg.toL1 g) := by
  rw [← α.convolutionL1_toL1_eq_bochnerConvolution hinv hf hg,
    P.integratedOperatorBochnerL1_convolutionL1]

/-- Star-preservation of `integratedOperatorBochnerL1` for Bochner twisted involution of integrable
functions on a locally compact group with a left-invariant Borel measure `μ` finite on compact sets,
inner regular with respect to compact sets on finite-measure sets, and satisfying `μ.inv ≪ μ` (in
particular for inner regular or regular Haar measures). -/
theorem integratedOperatorBochnerL1_bochnerInvolution {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    P.integratedOperatorBochnerL1 μ
      ((α.integrable_bochnerInvolution hinv hf).toL1
        (α.bochnerInvolution f)) =
      star (P.integratedOperatorBochnerL1 μ (hf.toL1 f)) := by
  rw [← α.twistedInvolutionL1_toL1_eq_bochnerInvolution hinv hf,
    P.integratedOperatorBochnerL1_twistedInvolutionL1]

end BochnerOps

/-! ### Integrand summability -/

section Summable

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- On any topological group (without discrete or countability assumptions), if `f : G → A` has
summable norms, then the Hilbert-space terms `s ↦ π(f s)(U_s v)` are norm-summable. -/
theorem summable_norm_integrand_of_summable_norm {f : G → A}
    (hf : Summable fun s => ‖f s‖) (v : H) :
    Summable fun s => ‖P.coefficient (f s) (P.group s v)‖ :=
  (hf.mul_right ‖v‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun s => P.norm_coefficient_group_apply_le (f s) s v

/-- On any topological group, if `f : G → A` has summable norms, then `s ↦ π(f s)(U_s v)` is
unconditionally summable in `H`. -/
theorem summable_integrand_of_summable_norm {f : G → A}
    (hf : Summable fun s => ‖f s‖) (v : H) :
    Summable fun s => P.coefficient (f s) (P.group s v) :=
  (P.summable_norm_integrand_of_summable_norm hf v).of_norm

end Summable

end TauCeti.CStarAction.CovariantRepresentation
