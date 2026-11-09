/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Cylinder
public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Arnold
import TauCeti.Topology.Algebra.Module.CompactQuotient

/-!
# Regular components are cylinders, and compact ones are Liouville tori

Let `σ` be a symplectic form on a `2n`-dimensional boundaryless manifold `M` and let
`F : M → (ι → ℝ)` be `n` smooth, pairwise Poisson-commuting functions whose Hamiltonian vector
fields are complete, with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`.

The Hamiltonian flow action identifies a regular connected component `L` of a common level
with the quotient of `ι → ℝ` by its discrete stabilizer `Λ`
(`TauCeti.SmoothTwoForm.IsSymplectic.quotientHamiltonianFlowStabilizerHomeomorph`). Without any
compactness, `Λ` is a free abelian group of some rank `r ≤ n`, and `L` is homeomorphic to the
cylinder `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`. If `L` is compact, the quotient is compact, so `Λ` spans `ι → ℝ` and
is a full lattice. A lattice basis then identifies `L` with the torus `(ℝ / ℤ)ⁿ`.

Other components of the level need not be regular. The smooth identification and action-angle
coordinates near `L` are not treated here.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus_prod`: a regular component
  of a level whose stabilizer has rank `r` is homeomorphic to `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.span_hamiltonianFlowStabilizer_eq_top`: the stabilizer of a
  point of a compact regular component spans `ι → ℝ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus`: a compact regular
  component of a level is homeomorphic to `(ℝ / ℤ)ⁿ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (the Liouville–Arnold theorem).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Function Set Filter Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {x : M}

/-- **Regular components are cylinders.** Let `F` be a family of `n` Poisson-commuting functions
with complete Hamiltonian vector fields on a `2n`-dimensional symplectic manifold. If the
connected component of `x` in its common level `F⁻¹(F x)` consists of regular points of `F`, and
the stabilizer of `x` in the Hamiltonian flow action has rank `r`, then this component is
homeomorphic to `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`. No compactness is assumed. -/
theorem nonempty_homeomorph_unitAddTorus_prod
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    Nonempty (connectedComponentIn (F ⁻¹' {F x}) x ≃ₜ
      UnitAddTorus (Fin (finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule)) ×
        (Fin (Fintype.card ι -
          finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule) → ℝ)) := by
  have : DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x) :=
    hσ.discreteTopology_hamiltonianFlowStabilizer hF hcomm hc
      (hreg x (mem_connectedComponentIn (by simp)))
  obtain ⟨e⟩ := AddSubgroup.nonempty_quotient_continuousAddEquiv_unitAddTorus_prod
    (hσ.hamiltonianFlowStabilizer hF hcomm hc x)
  rw [finrank_fintype_fun_eq_card] at e
  exact ⟨(hσ.quotientHamiltonianFlowStabilizerHomeomorph hF hcomm hc hdim hreg).symm.trans
    e.toHomeomorph⟩

/-- **The period lattice of a compact regular component has full rank.** If the connected
component of `x` in its common level is compact and consists of regular points, then the stabilizer
of `x` spans `ι → ℝ`. Since it is also discrete
(`TauCeti.SmoothTwoForm.IsSymplectic.discreteTopology_hamiltonianFlowStabilizer`), it is a full
lattice. -/
theorem span_hamiltonianFlowStabilizer_eq_top
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    Submodule.span ℝ (hσ.hamiltonianFlowStabilizer hF hcomm hc x : Set (ι → ℝ)) = ⊤ := by
  have := hσ.compactSpace_quotient_hamiltonianFlowStabilizer hF hcomm hc hdim hreg hK
  exact AddSubgroup.span_eq_top_of_compactSpace_quotient _

include hσ hF hcomm hc in
/-- **Compact regular components are tori** (the topological part of the Liouville–Arnold
theorem). Let `F` be a family of `n` Poisson-commuting functions with complete Hamiltonian vector
fields on a `2n`-dimensional symplectic manifold. If the connected component of `x` in its common
level `F⁻¹(F x)` is compact and consists of regular points of `F`, then it is homeomorphic to the
torus `(ℝ / ℤ)ⁿ`. -/
theorem nonempty_homeomorph_unitAddTorus
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    Nonempty (connectedComponentIn (F ⁻¹' {F x}) x ≃ₜ UnitAddTorus ι) := by
  set Λ := hσ.hamiltonianFlowStabilizer hF hcomm hc x
  have : DiscreteTopology Λ := hσ.discreteTopology_hamiltonianFlowStabilizer hF hcomm hc
    (hreg x (mem_connectedComponentIn (by simp)))
  have : IsZLattice ℝ Λ.toIntSubmodule :=
    ⟨hσ.span_hamiltonianFlowStabilizer_eq_top hF hcomm hc hreg hdim hK⟩
  exact ⟨(hσ.quotientHamiltonianFlowStabilizerHomeomorph hF hcomm hc hdim hreg).symm.trans
    (IsZLattice.basis Λ.toIntSubmodule).quotientLatticeEquiv.toHomeomorph⟩

end IsSymplectic

end SmoothTwoForm

end TauCeti
