/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p

/-!
# The kernel of the Neumann Laplacian

A function `u ∈ H¹(Ω)` lies in the kernel of the weak Neumann Laplacian when
`∫_Ω ∇u · ∇v = 0` for every `v ∈ H¹(Ω)`: the test space is all of `H¹(Ω)`, with no boundary
condition, which imposes the natural condition `∂_ν u = 0`. Testing with `v = u` shows that these
are exactly the `u` with vanishing weak gradient, hence exactly the functions that are locally
constant on `Ω`, that is, constant on each connected component of `Ω`. No regularity of `Ω` is
needed. This kernel is the eigenspace of the Neumann eigenvalue `0`.

On a bounded Lipschitz domain the number of components is finite, and the dimension of this
kernel is that number (`TauCeti.W1p.finrank_ker_gradientL_of_isLipschitzDomain`), so the Neumann
eigenvalue `0` has multiplicity the number of components of `Ω`, and is simple for connected `Ω`.

## Main declarations

* `TauCeti.PDE.forall_energyFormH1_one_zero_zero_eq_zero_iff_gradient_eq_zero`: `u` lies in the
  Neumann kernel exactly when its weak gradient vanishes.
* `TauCeti.PDE.forall_energyFormH1_one_zero_zero_eq_zero_iff_exists_isLocallyConstant`: `u` lies
  in the Neumann kernel exactly when it is almost everywhere equal to a function that is locally
  constant on `Ω`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.24 and Problem 47 (the Neumann problem and its kernel).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1.
-/

public section

namespace TauCeti

namespace PDE

open _root_.MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

/-- **The Neumann kernel is the kernel of the weak gradient.** A function `u ∈ H¹(Ω)` satisfies
`∫_Ω ∇u · ∇v = 0` for every `v ∈ H¹(Ω)` exactly when its weak gradient vanishes. -/
theorem forall_energyFormH1_one_zero_zero_eq_zero_iff_gradient_eq_zero (u : W1p mu Omega 2) :
    (∀ v : W1p mu Omega 2, energyFormH1 (fun _ => 1) 0 0 u v = 0) ↔ W1p.gradient u = 0 := by
  simp_rw [energyFormH1_one_zero_zero_eq_inner]
  exact ⟨fun h => inner_self_eq_zero.1 (h u), fun h v => by rw [h, inner_zero_left]⟩

/-- **The Neumann kernel consists of the locally constant functions.** On every open set `Ω`, a
function `u ∈ H¹(Ω)` satisfies `∫_Ω ∇u · ∇v = 0` for every `v ∈ H¹(Ω)` exactly when it agrees
almost everywhere on `Ω` with a function that is locally constant on `Ω`. -/
theorem forall_energyFormH1_one_zero_zero_eq_zero_iff_exists_isLocallyConstant
    (u : W1p mu Omega 2) :
    (∀ v : W1p mu Omega 2, energyFormH1 (fun _ => 1) 0 0 u v = 0) ↔
      ∃ g : EuclideanSpace ℝ ι → ℝ,
        IsLocallyConstant ((Omega : Set (EuclideanSpace ℝ ι)).domRestrict g) ∧
          W1p.value u =ᵐ[mu.restrict Omega] g :=
  (forall_energyFormH1_one_zero_zero_eq_zero_iff_gradient_eq_zero u).trans
    W1p.gradient_eq_zero_iff_exists_isLocallyConstant

end PDE

end TauCeti
