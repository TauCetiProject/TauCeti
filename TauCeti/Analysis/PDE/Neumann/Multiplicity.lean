/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed
public import TauCeti.Analysis.Sobolev.W1p.ConnectedComponents

/-!
# The multiplicity of the Neumann eigenvalue `0`

Let `Ω ⊆ ℝⁿ` be open and let `-Δ_∅` be the mixed Laplacian with no Dirichlet part
(`TauCeti.PDE.mixedOperator` for the identity coefficient and `Γ = ∅`), the self-adjoint
realization on `L²(Ω)` of `-Δ` with the natural boundary condition `∂_ν u = 0`. Its eigenspace for
the eigenvalue `0` is its kernel, the values of the `u ∈ H¹_∅(Ω)` with vanishing weak gradient
(`TauCeti.PDE.mem_ker_mixedOperator_laplacian_iff`).

When `H¹_∅(Ω) = H¹(Ω)`, as on a bounded Lipschitz domain, this kernel is the image under the value
map of the kernel of the weak gradient on `H¹(Ω)`
(`TauCeti.PDE.ker_mixedOperator_laplacian_empty`). The value map is injective, and on a domain of
finite measure with finitely many connected components the kernel of the weak gradient consists of
the functions constant on each component (`TauCeti.W1p.finrank_ker_gradientL`). So the eigenvalue
`0` of the Neumann Laplacian has multiplicity the number of connected components of `Ω`
(`TauCeti.PDE.finrank_ker_mixedOperator_laplacian_empty`), and it is simple when `Ω` is connected
(`TauCeti.PDE.finrank_ker_mixedOperator_laplacian_empty_eq_one`). A bounded Lipschitz domain has
finitely many components (`Set.IsLipschitzDomain.finite_connectedComponents_of_isBounded`).

Finite measure is needed: on `Ω = ℝⁿ`, where `H¹_∅(Ω) = H¹(Ω)` and `Ω` is connected, a function
with vanishing gradient is constant, and the only square-integrable constant is `0`.

## Main declarations

* `TauCeti.PDE.ker_mixedOperator_laplacian_empty`: when `H¹_∅(Ω) = H¹(Ω)`, the kernel of `-Δ_∅` is
  the space of values of the `u ∈ H¹(Ω)` with `∇u = 0`.
* `TauCeti.PDE.finrank_ker_mixedOperator_laplacian_empty`: the multiplicity of the eigenvalue `0`
  of `-Δ_∅` is the number of connected components of `Ω`.
* `TauCeti.PDE.finrank_ker_mixedOperator_laplacian_empty_eq_one`: for connected `Ω` the eigenvalue
  `0` is simple.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1 (natural
  boundary conditions and the eigenvalue `0` of the Neumann problem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.24 and Problem 47 (the Neumann problem and its kernel).
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory Module TopologicalSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

/-- **The kernel of the Neumann Laplacian.** When `H¹_∅(Ω) = H¹(Ω)`, the kernel of the mixed
Laplacian `-Δ_∅` is the image under the value map `H¹(Ω) → L²(Ω)` of the kernel of the weak
gradient: it consists of the values of the `u ∈ H¹(Ω)` with `∇u = 0`. -/
theorem ker_mixedOperator_laplacian_empty (htop : w1pVanishingOnSubmodule mu Omega 2 ∅ = ⊤) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) ∅).ker =
      (LinearMap.ker (W1p.gradientL : W1p mu Omega 2 →L[ℝ] _).toLinearMap).map
        (W1p.valueL : W1p mu Omega 2 →L[ℝ] _).toLinearMap := by
  ext f
  simp only [mem_ker_mixedOperator_laplacian_iff (Set.empty_disjoint _), Submodule.mem_map,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, W1p.gradientL_apply, W1p.valueL_apply]
  constructor
  · rintro ⟨u, hu, hgrad⟩
    exact ⟨u, hgrad, hu⟩
  · rintro ⟨u, hgrad, hu⟩
    have hmem : u ∈ w1pVanishingOnSubmodule mu Omega 2 ∅ := by
      rw [htop]
      exact ClosedSubmodule.mem_top
    exact ⟨⟨u, hmem⟩, hu, hgrad⟩

/-- **The multiplicity of the Neumann eigenvalue `0` is the number of components.** Let `Ω` be an
open set of finite measure with finitely many connected components, on which
`H¹_∅(Ω) = H¹(Ω)`, as on a bounded Lipschitz domain. Then the kernel of the mixed Laplacian
`-Δ_∅`, its eigenspace for the eigenvalue `0`, has dimension the number of connected components of
`Ω`. -/
theorem finrank_ker_mixedOperator_laplacian_empty
    [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]
    [Finite (ConnectedComponents (Omega : Set (EuclideanSpace ℝ ι)))]
    (htop : w1pVanishingOnSubmodule mu Omega 2 ∅ = ⊤) :
    finrank ℝ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) ∅).ker =
      Nat.card (ConnectedComponents (Omega : Set (EuclideanSpace ℝ ι))) := by
  have hinj : Function.Injective (W1p.valueL : W1p mu Omega 2 →L[ℝ] _).toLinearMap :=
    fun u v h ↦ W1p.ext_value <| by
      rwa [ContinuousLinearMap.coe_coe, W1p.valueL_apply, W1p.valueL_apply] at h
  rw [ker_mixedOperator_laplacian_empty htop, ← W1p.finrank_ker_gradientL (mu := mu) (p := 2)]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

/-- **The Neumann eigenvalue `0` is simple on a connected domain.** Let `Ω` be a nonempty
preconnected open set of finite measure on which `H¹_∅(Ω) = H¹(Ω)`, as on a bounded connected
Lipschitz domain. Then the kernel of the mixed Laplacian `-Δ_∅` is one-dimensional: the eigenvalue
`0` of `-Δ_∅` is simple. -/
theorem finrank_ker_mixedOperator_laplacian_empty_eq_one
    [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]
    (htop : w1pVanishingOnSubmodule mu Omega 2 ∅ = ⊤)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hne : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    finrank ℝ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) ∅).ker = 1 := by
  have : PreconnectedSpace (Omega : Set (EuclideanSpace ℝ ι)) := Subtype.preconnectedSpace hconn
  have : Nonempty (Omega : Set (EuclideanSpace ℝ ι)) := hne.to_subtype
  rw [finrank_ker_mixedOperator_laplacian_empty htop, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩

end PDE

end TauCeti
