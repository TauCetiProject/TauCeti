/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Cylinder.Manifold
public import TauCeti.Geometry.Manifold.RegularValue.Component
public import TauCeti.Geometry.Symplectic.Hamiltonian.LiouvilleArnold.Torus

/-!
# Liouville tori as open submanifolds of regular fibres

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2n`, and let
`F : M → (ι → ℝ)`, `|ι| = n`, be a smooth family of pairwise Poisson-commuting functions. Let `L`
be the connected component of a point `x` in its level `F⁻¹(F x)`, and suppose that `L` consists
of regular points of `F`; other components of the level need not be regular. Then `L` is an open
subset of the regular fibre over `F x` of the restriction of `F` to any open set `U` of regular
points containing it, for instance the open set of all regular points of `F`, and so it carries
the smooth structure of an open submanifold of that regular fibre
(`TauCeti.regularFiberComponent`).

This file shows that the Liouville–Arnold identification of `L` with `ℝⁿ / Λ` is a diffeomorphism
for this smooth structure. When the Hamiltonian vector fields are complete, their flows generate an
action `v • y` of `ι → ℝ` on `M`, the stabilizer `Λ` of `x` is discrete, and the orbit map descends
to a diffeomorphism

`TauCeti.SmoothTwoForm.IsSymplectic.quotientHamiltonianFlowStabilizerDiffeomorph :
  (ι → ℝ) / Λ ≃ L`,  `[v] ↦ v • x`.

It is obtained from the Lagrangian embedding `[v] ↦ v • x` of `(ι → ℝ) / Λ` into `M` with range `L`
(`TauCeti.SmoothTwoForm.IsSymplectic.isLagrangianEmbedding_ofQuotientHamiltonianFlowStabilizer`):
a smooth embedding onto `L` is a diffeomorphism onto this open submanifold of the regular fibre
(`Manifold.IsSmoothEmbedding.regularFiberComponentDiffeomorph`).

Without any compactness, the discrete stabilizer `Λ` has some rank `r ≤ n`, and a real basis of
`ι → ℝ` adapted to `Λ` identifies `(ι → ℝ) / Λ` with the cylinder `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ` as manifolds
(`Module.Basis.orbitRelQuotientCylinderDiffeomorph`). So a regular component of a level of a system
with complete Hamiltonian vector fields is diffeomorphic to such a cylinder
(`TauCeti.SmoothTwoForm.IsSymplectic.nonempty_diffeomorph_regularFiberComponent_unitAddTorus_prod`),
the smooth form of `TauCeti.SmoothTwoForm.IsSymplectic.nonempty_homeomorph_unitAddTorus_prod`.

When `L` is compact no completeness is needed: then `Λ` is a full lattice and `L` is
diffeomorphic to the torus `(ι → ℝ) / Λ`, by a diffeomorphism whose composite with the inclusion
of `L` is a Lagrangian embedding
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_regularFiberComponent_of_isCompact`).
This is the smooth form of the Liouville–Arnold theorem on a single compact regular component of
a level, for the smooth structure that `L` has as a submanifold of `M`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsSymplectic.quotientHamiltonianFlowStabilizerDiffeomorph`: the
  diffeomorphism `(ι → ℝ) / Λ ≃ L`, `[v] ↦ v • x`, for complete Hamiltonian vector fields.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.coe_quotientHamiltonianFlowStabilizerDiffeomorph_apply`: the
  diffeomorphism is the descended orbit map, sending the class of `v` to `v • x`.
* `TauCeti.SmoothTwoForm.IsSymplectic.nonempty_diffeomorph_regularFiberComponent_unitAddTorus_prod`:
  for complete Hamiltonian vector fields, a regular component of a level whose stabilizer has rank
  `r` is diffeomorphic to the cylinder `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_regularFiberComponent_of_isCompact`: a
  compact regular component of a level is diffeomorphic to a torus `(ι → ℝ) / Λ` for a full
  lattice `Λ`, with no completeness hypothesis.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (compact connected regular levels are tori).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4 (the Arnold–Liouville theorem).
-/

public section

noncomputable section

open Function Set Module TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {U : Opens M} (hU : ∀ y : U, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)

/-- The model space of the regular fibres of `F`, of dimension `dim M - |ι|`. -/
local notation "Fib" => Fin (finrank ℝ E - finrank ℝ (ι → ℝ)) → ℝ

include hσ hF hcomm hc

/-- **Liouville tori are diffeomorphic to `ℝⁿ / Λ`.** On a manifold of dimension `2 · |ι|`, let
the connected component `L` of `x` in its level `F⁻¹(F x)` lie in an open set `U` of regular
points of `F`. The orbit map `[v] ↦ v • x` of the Hamiltonian flow action is a diffeomorphism of
the quotient `(ι → ℝ) / Λ` by the stabilizer `Λ` of `x` onto `L`, with its structure of an open
submanifold of the regular fibre over `F x` of the restriction of `F` to `U`
(`TauCeti.regularFiberComponent`). The stabilizer of a regular point is discrete
(`discreteTopology_hamiltonianFlowStabilizer`). -/
def quotientHamiltonianFlowStabilizerDiffeomorph (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M} (hLU : connectedComponentIn (F ⁻¹' {F x}) x ⊆ U)
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)] :
    letI := regularFiberComponentChartedSpace (x := x) (by simp) hF
      BoundarylessManifold.isInteriorPoint hU
    AddAction.orbitRel.Quotient (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
        (ι → ℝ) ≃ₘ⟮𝓘(ℝ, ι → ℝ), 𝓘(ℝ, Fib)⟯
      regularFiberComponent (by simp) hF BoundarylessManifold.isInteriorPoint hU hLU :=
  have hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y :=
    fun y hy ↦ hU ⟨y, hLU hy⟩
  (hσ.isSmoothEmbedding_ofQuotientHamiltonianFlowStabilizer hF hcomm hc hdim
    hreg).regularFiberComponentDiffeomorph _ hF _ hU hLU
      (hσ.range_ofQuotientHamiltonianFlowStabilizer hF hcomm hc hdim hreg)

/-- The diffeomorphism `(ι → ℝ) / Λ ≃ L` is the descended orbit map `[v] ↦ v • x`; with
`ofQuotientHamiltonianFlowStabilizer_mk` it sends the class of `v` to `v • x`. -/
@[simp]
theorem coe_quotientHamiltonianFlowStabilizerDiffeomorph_apply
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hLU : connectedComponentIn (F ⁻¹' {F x}) x ⊆ U)
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)]
    (p : AddAction.orbitRel.Quotient (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
      (ι → ℝ)) :
    letI := regularFiberComponentChartedSpace (x := x) (by simp) hF
      BoundarylessManifold.isInteriorPoint hU
    (((hσ.quotientHamiltonianFlowStabilizerDiffeomorph hF hcomm hc hU hdim hLU p :
      {y : U // F y = F x}) : U) : M) = hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x p :=
  Manifold.IsSmoothEmbedding.coe_regularFiberComponentDiffeomorph_apply _ hF _ hU hLU _ _ p

/-- The inverse of the diffeomorphism `(ι → ℝ) / Λ ≃ L` sends a point `y` of `L` to the class of
any `v` with `v • x = y`. -/
@[simp]
theorem ofQuotientHamiltonianFlowStabilizer_quotientHamiltonianFlowStabilizerDiffeomorph_symm_apply
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hLU : connectedComponentIn (F ⁻¹' {F x}) x ⊆ U)
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)]
    (z : regularFiberComponent (by simp) hF BoundarylessManifold.isInteriorPoint hU hLU) :
    letI := regularFiberComponentChartedSpace (x := x) (by simp) hF
      BoundarylessManifold.isInteriorPoint hU
    hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x
        ((hσ.quotientHamiltonianFlowStabilizerDiffeomorph hF hcomm hc hU hdim hLU).symm z) =
      (((z : {y : U // F y = F x}) : U) : M) :=
  Manifold.IsSmoothEmbedding.apply_regularFiberComponentDiffeomorph_symm_apply _ hF _ hU hLU _ _ z

/-- **Regular components of a level are cylinders `Tʳ × ℝⁿ⁻ʳ`.** On a manifold of dimension
`2n`, `n = |ι|`, let the Hamiltonian vector fields of `F` be complete, and let the connected
component `L` of `x` in its level `F⁻¹(F x)` lie in an open set `U` of regular points of `F`. If the
stabilizer `Λ` of `x` in the Hamiltonian flow action has rank `r`, then `L`, with its structure of
an open submanifold of the regular fibre over `F x` of the restriction of `F` to `U`
(`TauCeti.regularFiberComponent`), is diffeomorphic to the cylinder `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`. No
compactness is assumed. -/
theorem nonempty_diffeomorph_regularFiberComponent_unitAddTorus_prod
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hLU : connectedComponentIn (F ⁻¹' {F x}) x ⊆ U) :
    letI := regularFiberComponentChartedSpace (x := x) (by simp) hF
      BoundarylessManifold.isInteriorPoint hU
    Nonempty (regularFiberComponent (by simp) hF BoundarylessManifold.isInteriorPoint hU hLU
      ≃ₘ⟮𝓘(ℝ, Fib), (ModelWithCorners.pi fun _ : Fin (finrank ℤ
          (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule) ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, Fin (Fintype.card ι -
          finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule) → ℝ)⟯
      UnitAddTorus (Fin (finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule)) ×
        (Fin (Fintype.card ι -
          finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule) → ℝ)) := by
  let := regularFiberComponentChartedSpace (x := x) (by simp) hF
    BoundarylessManifold.isInteriorPoint hU
  have : DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x) :=
    hσ.discreteTopology_hamiltonianFlowStabilizer hF hcomm hc
      (hU ⟨x, hLU (mem_connectedComponentIn (by simp))⟩)
  -- A real basis of `ι → ℝ` whose first `r` vectors span `Λ` over `ℤ`, reindexed so that its
  -- complementary vectors are indexed by `Fin (|ι| - r)`.
  obtain ⟨B, hB⟩ :=
    (hσ.hamiltonianFlowStabilizer hF hcomm hc x).exists_basis_span_range_comp_inl_eq
  let B' := B.reindex (Equiv.sumCongr (Equiv.refl _)
    (finCongr (by rw [finrank_fintype_fun_eq_card])))
  have hL : (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule =
      Submodule.span ℤ (range (B' ∘ Sum.inl)) := by
    have hB' : B' ∘ Sum.inl = B ∘ Sum.inl := by
      funext i
      simp [B']
    rw [hB']
    exact (congrArg AddSubgroup.toIntSubmodule hB).symm
  exact ⟨(hσ.quotientHamiltonianFlowStabilizerDiffeomorph hF hcomm hc hU hdim hLU).symm.trans
    (B'.orbitRelQuotientCylinderDiffeomorph hL ∞)⟩

omit hc

/-- **Compact regular components of a level are tori `ℝⁿ / Λ`** (the smooth part of the
Liouville–Arnold theorem). Let `F` be a family of `n` Poisson-commuting functions on a
`2n`-dimensional symplectic manifold, whose Hamiltonian vector fields need not be complete. If the
connected component `L` of `x` in its level `F⁻¹(F x)` is compact and lies in an open set `U` of
regular points of `F`, then there are a discrete full lattice `Λ ⊆ ι → ℝ` and a diffeomorphism of
the torus `(ι → ℝ) / Λ` onto `L`, with its structure of an open submanifold of the regular fibre
over `F x` of the restriction of `F` to `U` (`TauCeti.regularFiberComponent`), whose composite with
the inclusion of `L` in `M` is a Lagrangian embedding. -/
theorem exists_diffeomorph_regularFiberComponent_of_isCompact
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hLU : connectedComponentIn (F ⁻¹' {F x}) x ⊆ U)
    (hL : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    letI := regularFiberComponentChartedSpace (x := x) (by simp) hF
      BoundarylessManifold.isInteriorPoint hU
    ∃ (Λ : AddSubgroup (ι → ℝ)) (_ : DiscreteTopology Λ)
      (e : AddAction.orbitRel.Quotient Λ.toIntSubmodule (ι → ℝ) ≃ₘ⟮𝓘(ℝ, ι → ℝ), 𝓘(ℝ, Fib)⟯
        regularFiberComponent (by simp) hF BoundarylessManifold.isInteriorPoint hU hLU),
      IsZLattice ℝ Λ.toIntSubmodule ∧
        hσ.isNondegenerate.IsLagrangianEmbedding 𝓘(ℝ, ι → ℝ)
          fun p ↦ (((e p : {y : U // F y = F x}) : U) : M) := by
  obtain ⟨Λ, hΛ, f, hlat, hf, hrange⟩ :=
    hσ.exists_isLagrangianEmbedding_of_isCompact hF hcomm hdim (fun y hy ↦ hU ⟨y, hLU hy⟩) hL
  refine ⟨Λ, hΛ, hf.isSmoothEmbedding.regularFiberComponentDiffeomorph _ hF _ hU hLU hrange,
    hlat, ?_⟩
  simpa using hf

end IsSymplectic

end SmoothTwoForm

end TauCeti
