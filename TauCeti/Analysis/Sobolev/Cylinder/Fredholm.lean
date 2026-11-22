/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.SemiFredholm
public import TauCeti.Analysis.Sobolev.Cylinder
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.ContinuousFamily

/-!
# Fredholm property of first-order operators on the cylinder along families

Let `D ξ = M (ξ, ∂s ξ, ∂t ξ)` be a first-order operator on the cylinder `ℝ × S¹` with an essentially
bounded coefficient field `M`, realized as `TauCeti.CylinderSobolev.jetOperator M` on the Sobolev
space `W^{1,2}(ℝ × S¹, V)` with values in `L²(ℝ × S¹, W)`. Peetre's argument turns the
semi-Fredholm estimate (`TauCeti.CylinderSobolev.HasSemiFredholmEstimate`) into finite-dimensional
kernel and closed range, but not into a finite-dimensional cokernel. This file shows that the
cokernel is controlled along families. The operator depends continuously on `M` in `L^∞`
(`TauCeti.CylinderSobolev.continuousOn_jetOperator`), so for a family of coefficient fields `M x`,
continuous in `L^∞` on a preconnected set `s`, each satisfying a semi-Fredholm estimate,
Fredholmness and the index are constant on `s`
(`TauCeti.CylinderSobolev.isFredholm_and_index_eq_of_hasSemiFredholmEstimate`). This is the
abstract stability of operators with closed range and finite-dimensional kernel,
`ContinuousOn.isFredholm_of_isPreconnected`, which needs the target `L²(ℝ × S¹, W)` to be a Hilbert
space, so `W` is an inner product space. It holds for the realization of `D` on any complete
subspace of `L²` jets (`TauCeti.CylinderSobolev.isFredholm_and_index_eq_of_isPreconnected`), and so
also serves the strip with boundary conditions.

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

namespace TauCeti.CylinderSobolev

open StripSobolev (stripMeasure)

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [TopologicalSpace X]

/-- **Fredholmness and the index along families of first-order operators.** Let `M x` be
essentially bounded coefficient fields on the strip, depending continuously on `x` in `L^∞` on a
preconnected set `s`, and let `H` be a complete subspace of `L²` jets, such as the Sobolev space of
the cylinder or of the strip with boundary conditions. If the realizations of the first-order
operators `D_x ξ = M x (ξ, ∂s ξ, ∂t ξ)` on `H` all have finite-dimensional kernel and closed range,
and `D_{x₀}` is Fredholm for one `x₀ ∈ s`, then every `D_x` with `x ∈ s` is Fredholm, with the same
index. -/
theorem isFredholm_and_index_eq_of_isPreconnected
    {H : Submodule ℝ (Lp (V × V × V) 2 stripMeasure)} [CompleteSpace H] {s : Set X}
    (hs : IsPreconnected s) {M : X → ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0))
    (hker : ∀ x ∈ s, FiniteDimensional ℝ ((jetOperator (M x)).comp H.subtypeL).ker)
    (hrange : ∀ x ∈ s, IsClosed (((jetOperator (M x)).comp H.subtypeL).range :
      Set (Lp W 2 stripMeasure)))
    {x₀ x : X} (hx₀ : x₀ ∈ s) (hx : x ∈ s)
    (h₀ : ((jetOperator (M x₀)).comp H.subtypeL).IsFredholm) :
    ((jetOperator (M x)).comp H.subtypeL).IsFredholm ∧
      ((jetOperator (M x)).comp H.subtypeL).index =
        ((jetOperator (M x₀)).comp H.subtypeL).index := by
  have hT : ContinuousOn (fun y ↦ (jetOperator (M y)).comp H.subtypeL) s :=
    (continuousOn_jetOperator hM hcont).clm_comp continuousOn_const
  have hF : ∀ y ∈ s, ((jetOperator (M y)).comp H.subtypeL).IsFredholm := fun y hy ↦
    hT.isFredholm_of_isPreconnected hker hrange hs hx₀ h₀ hy
  exact ⟨hF x hx, ContinuousOn.index_eq_of_isPreconnected hT hF hs hx hx₀⟩

/-- **Fredholmness and the index along families of cylinder operators.** Let `M x` be
essentially bounded coefficient fields, depending continuously on `x` in `L^∞` on a preconnected
set `s`, whose first-order operators `D_x ξ = M x (ξ, ∂s ξ, ∂t ξ)` each satisfy a semi-Fredholm
estimate. If the realization `D_{x₀} : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, W)` is Fredholm for one
`x₀ ∈ s`, then every `D_x` with `x ∈ s` is Fredholm, with the same index. -/
theorem isFredholm_and_index_eq_of_hasSemiFredholmEstimate [FiniteDimensional ℝ V] {s : Set X}
    (hs : IsPreconnected s) {M : X → ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0))
    (hest : ∀ x ∈ s, ∃ C T, HasSemiFredholmEstimate (M x) C T) {x₀ x : X} (hx₀ : x₀ ∈ s)
    (hx : x ∈ s) (h₀ : ((jetOperator (M x₀)).comp (H1 V).subtypeL).IsFredholm) :
    ((jetOperator (M x)).comp (H1 V).subtypeL).IsFredholm ∧
      ((jetOperator (M x)).comp (H1 V).subtypeL).index =
        ((jetOperator (M x₀)).comp (H1 V).subtypeL).index :=
  isFredholm_and_index_eq_of_isPreconnected hs hM hcont
    (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
      finiteDimensional_ker_jetOperator_comp_subtypeL (hM z hz) h)
    (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
      isClosed_range_jetOperator_comp_subtypeL (hM z hz) h) hx₀ hx h₀

end TauCeti.CylinderSobolev
