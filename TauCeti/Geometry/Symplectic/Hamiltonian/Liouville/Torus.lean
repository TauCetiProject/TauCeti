/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Arnold
import TauCeti.Topology.Algebra.Module.CompactQuotient

/-!
# Compact regular components are Liouville tori

Let `σ` be a symplectic form on a `2n`-dimensional boundaryless manifold `M` and let
`F : M → (ι → ℝ)` be `n` smooth, pairwise Poisson-commuting functions whose Hamiltonian vector
fields are complete, with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`.

The Hamiltonian flow action identifies a regular connected component `L` of a common level
with the quotient of `ι → ℝ` by its discrete stabilizer `Λ`
(`TauCeti.SmoothTwoForm.IsSymplectic.quotientHamiltonianFlowStabilizerHomeomorph`). If `L` is
compact, this quotient is compact, so `Λ` spans `ι → ℝ` and is a full lattice. A lattice basis
then identifies `L` with the torus `(ℝ / ℤ)ⁿ`.

Other components of the level need not be regular. The smooth identification of `L` with
`(ι → ℝ) / Λ` as a Lagrangian embedding is in
`TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Lagrangian`; action-angle coordinates near `L`
are not treated here.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.span_hamiltonianFlowStabilizer_eq_top`: the stabilizer of a
  point of a compact regular component spans `ι → ℝ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.isZLattice_hamiltonianFlowStabilizer` and
  `TauCeti.SmoothTwoForm.IsSymplectic.finrank_hamiltonianFlowStabilizer`: it is a full lattice, of
  rank `n`.
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

/-- **The stabilizer of a point of a compact regular component is a full lattice.** On a manifold
of dimension `2 · |ι|`, if the connected component `L` of `x` in its level is compact and consists
of regular points of `F`, the stabilizer `Λ` of `x` spans `ι → ℝ`, so `(ι → ℝ) / Λ` is a compact
torus. -/
theorem isZLattice_hamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hL : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x))
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)] :
    IsZLattice ℝ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule where
  span_top := by
    rw [AddSubgroup.coe_toIntSubmodule]
    exact hσ.span_hamiltonianFlowStabilizer_eq_top hF hcomm hc hreg hdim hL

/-- **The period lattice of a compact regular component has rank `n`.** On a manifold of dimension
`2 · |ι|`, if the connected component of `x` in its level is compact and consists of regular points
of `F`, the stabilizer of `x` is a free abelian group of rank `|ι|`. -/
theorem finrank_hamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hL : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule = Fintype.card ι := by
  have := hσ.discreteTopology_hamiltonianFlowStabilizer hF hcomm hc
    (hreg x (mem_connectedComponentIn (by simp)))
  have := hσ.isZLattice_hamiltonianFlowStabilizer hF hcomm hc hdim hreg hL
  rw [ZLattice.rank ℝ, finrank_fintype_fun_eq_card]

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
  have := hσ.isZLattice_hamiltonianFlowStabilizer hF hcomm hc hdim hreg hK
  exact ⟨(hσ.quotientHamiltonianFlowStabilizerHomeomorph hF hcomm hc hdim hreg).symm.trans
    (IsZLattice.basis Λ.toIntSubmodule).quotientLatticeEquiv.toHomeomorph⟩

end IsSymplectic

end SmoothTwoForm

end TauCeti
