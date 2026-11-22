/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.SemiFredholm
public import TauCeti.Analysis.Sobolev.Strip.Operator
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.ContinuousFamily

/-!
# Fredholm property of first-order operators over the strip along families

Let `D ξ = M (ξ, ∂s ξ, ∂t ξ)` be a first-order operator over the strip `ℝ × [0, 1]` with an
essentially bounded coefficient field `M`, realized as `TauCeti.jetOperator stripMeasure M` on the
Sobolev space `jetClosure S` of a space `S` of test sections, with values in `L²(ℝ × [0, 1], W)`:
for instance `W^{1,2}(ℝ × S¹, V)` for the cylinder, or `W^{1,2}` of the strip with boundary values
in two subspaces. Peetre's argument turns the semi-Fredholm estimate
(`TauCeti.StripSobolev.HasSemiFredholmEstimate`) into finite-dimensional kernel and closed range,
but not into a finite-dimensional cokernel. This file shows that the cokernel is controlled along
families. The operator depends continuously on `M` in `L^∞`
(`TauCeti.StripSobolev.continuousOn_jetOperator`), so for a family of coefficient fields `M x`,
continuous in `L^∞` on a preconnected set `s`, each satisfying a semi-Fredholm estimate,
Fredholmness and the index are constant on `s`
(`TauCeti.StripSobolev.isFredholm_and_index_eq_of_hasSemiFredholmEstimate`). This is the
abstract stability of operators with closed range and finite-dimensional kernel,
`ContinuousOn.isFredholm_of_isPreconnected`, which needs the target `L²(ℝ × [0, 1], W)` to be a
Hilbert space, so `W` is an inner product space.

Semi-Fredholm estimates hold for the linearized Floer operators along cylinders asymptotic to
nondegenerate orbits (`TauCeti.Geometry.Symplectic.Floer.SemiFredholm`). By this file, the
Fredholm property and the index of such an operator follow from those of any operator joined to
it by a path of coefficient fields, continuous in `L^∞`, along which semi-Fredholm estimates hold,
without proving the regularity of weak cokernel elements.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S` on the
  cylinder.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [TopologicalSpace X]
  {S : Submodule ℝ (ℝ × ℝ → V)} [HasL2Jets S] [IsTestSpace S] [HasCompactRestriction S]

/-- **Fredholmness and the index along families of operators over the strip.** Let `M x` be
essentially bounded coefficient fields, depending continuously on `x` in `L^∞` on a preconnected
set `s`, whose first-order operators `D_x ξ = M x (ξ, ∂s ξ, ∂t ξ)` each satisfy a semi-Fredholm
estimate on a space `S` of test sections for which Rellich's theorem holds. If the realization
`D_{x₀} : jetClosure S → L²(ℝ × [0, 1], W)` is Fredholm for one `x₀ ∈ s`, then every `D_x` with
`x ∈ s` is Fredholm, with the same index. -/
theorem isFredholm_and_index_eq_of_hasSemiFredholmEstimate {s : Set X} (hs : IsPreconnected s)
    {M : X → ℝ × ℝ → V × V × V →L[ℝ] W} (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0))
    (hest : ∀ x ∈ s, ∃ C T, HasSemiFredholmEstimate S (M x) C T) {x₀ x : X} (hx₀ : x₀ ∈ s)
    (hx : x ∈ s)
    (h₀ : ((jetOperator stripMeasure (M x₀)).comp (jetClosure S).subtypeL).IsFredholm) :
    ((jetOperator stripMeasure (M x)).comp (jetClosure S).subtypeL).IsFredholm ∧
      ((jetOperator stripMeasure (M x)).comp (jetClosure S).subtypeL).index =
        ((jetOperator stripMeasure (M x₀)).comp (jetClosure S).subtypeL).index := by
  have hT : ContinuousOn
      (fun y ↦ (jetOperator stripMeasure (M y)).comp (jetClosure S).subtypeL) s :=
    (continuousOn_jetOperator hM hcont).clm_comp continuousOn_const
  have hF : ∀ y ∈ s,
      ((jetOperator stripMeasure (M y)).comp (jetClosure S).subtypeL).IsFredholm :=
    fun y hy ↦ hT.isFredholm_of_isPreconnected
      (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
        finiteDimensional_ker_jetOperator_comp_subtypeL (hM z hz) h)
      (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
        isClosed_range_jetOperator_comp_subtypeL (hM z hz) h) hs hx₀ h₀ hy
  exact ⟨hF x hx, ContinuousOn.index_eq_of_isPreconnected hT hF hs hx hx₀⟩

end TauCeti.StripSobolev
