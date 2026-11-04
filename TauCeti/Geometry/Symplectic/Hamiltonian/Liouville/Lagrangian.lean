/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Torus
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic

import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Liouville tori are smooth Lagrangian embeddings of `ℝⁿ / Λ`

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2n`, and let
`F : M → (ι → ℝ)`, `|ι| = n`, be a smooth family of pairwise Poisson-commuting functions with
complete Hamiltonian vector fields. Their flows generate an action `v • y` of `ι → ℝ` on `M`
(`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`). Let `L` be the connected component
of `x` in its level `F⁻¹(F x)`, and suppose every point of `L` is a regular point of `F`. The
stabilizer `Λ` of `x` is then a discrete subgroup of `ι → ℝ`, and the orbit map `v ↦ v • x`
identifies `(ι → ℝ) ⧸ Λ` with `L` as topological spaces
(`TauCeti.SmoothTwoForm.IsSymplectic.quotientHamiltonianFlowStabilizerHomeomorph`).

This file upgrades that identification to a smooth one. The quotient of `ι → ℝ` by translation
by the discrete subgroup `Λ` is a smooth manifold (`TauCeti.instIsManifoldAddQuotient`), and the
orbit map descends to a map

`TauCeti.SmoothTwoForm.IsSymplectic.ofQuotientHamiltonianFlowStabilizer : (ι → ℝ) / Λ → M`,
`[v] ↦ v • x`,

whose range is `L`. It is a smooth embedding, and its tangent images are Lagrangian: it is a
Lagrangian embedding. The immersion property comes from the derivative of the orbit map,
`w ↦ ∑ i, wᵢ X_{Fᵢ}(v • x)`, which is injective because the Hamiltonian vectors are independent
at regular points; the orbit projection `(ι → ℝ) → (ι → ℝ) / Λ` is a local diffeomorphism, so the
descended map has injective derivative too. The embedding property is the homeomorphism above.
The statements about smoothness take the discreteness of `Λ` as an instance argument, since the
manifold structure of `(ι → ℝ) / Λ` depends on it; at a regular point it is supplied by
`TauCeti.SmoothTwoForm.IsSymplectic.discreteTopology_hamiltonianFlowStabilizer`.

When `L` is moreover compact, as it is for a proper map `F`, the stabilizer spans `ι → ℝ`
(`TauCeti.SmoothTwoForm.IsSymplectic.span_hamiltonianFlowStabilizer_eq_top`): it is a full
lattice, of rank `n`. Then `(ι → ℝ) / Λ` is a compact torus,
and `L` is the image of a Lagrangian embedding of that torus. This is the smooth part of the
Liouville–Arnold theorem on a single compact regular component; no symplectic coordinates near
`L` are constructed here.

## Main definitions

* `TauCeti.SmoothTwoForm.IsSymplectic.ofQuotientHamiltonianFlowStabilizer`: the map
  `(ι → ℝ) / Λ → M`, `[v] ↦ v • x`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.range_ofQuotientHamiltonianFlowStabilizer`: its range is
  the regular component `L`.
* `TauCeti.SmoothTwoForm.IsSymplectic.contMDiff_ofQuotientHamiltonianFlowStabilizer`: it is
  smooth.
* `TauCeti.SmoothTwoForm.IsSymplectic.isSmoothEmbedding_ofQuotientHamiltonianFlowStabilizer`:
  it is a smooth embedding.
* `TauCeti.SmoothTwoForm.IsSymplectic.isLagrangianEmbedding_ofQuotientHamiltonianFlowStabilizer`:
  it is a Lagrangian embedding.
* `TauCeti.SmoothTwoForm.IsSymplectic.isZLattice_hamiltonianFlowStabilizer` and
  `TauCeti.SmoothTwoForm.IsSymplectic.finrank_hamiltonianFlowStabilizer`: the stabilizer of a
  point of a compact regular component is a full lattice of rank `n`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (compact connected regular levels are tori).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4 (the Arnold–Liouville theorem).
-/

public section

noncomputable section

open Function Set Module Topology
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

include hσ hF hcomm hc

/-! ### The orbit map on the quotient by the stabilizer -/

/-- The orbit map `v ↦ v • x` of the Hamiltonian flow action, descended to the quotient of `ι → ℝ`
by translation by the stabilizer `Λ` of `x`; it is Mathlib's `AddAction.ofQuotientStabilizer` read
on this orbit space. On a manifold of dimension `2 · |ι|` (`2 * Fintype.card ι = finrank ℝ E`),
when the connected component `L` of `x` in its level consists of regular points of `F`, it is a
Lagrangian embedding with range `L`
(`isLagrangianEmbedding_ofQuotientHamiltonianFlowStabilizer`,
`range_ofQuotientHamiltonianFlowStabilizer`). -/
def ofQuotientHamiltonianFlowStabilizer (x : M) :
    AddAction.orbitRel.Quotient (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
      (ι → ℝ) → M :=
  Quotient.lift (fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x) fun v w hvw ↦ by
    refine (hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc).2 ?_
    have h : v - w ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x :=
      (Submodule.orbitRel_apply_iff_sub_mem _).1 hvw
    simpa only [neg_sub, neg_add_eq_sub] using neg_mem h

@[simp]
theorem ofQuotientHamiltonianFlowStabilizer_mk (x : M) (v : ι → ℝ) :
    hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x (Quotient.mk _ v) =
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x :=
  (rfl)

/-- The orbit map `v ↦ v • x` factors through the orbit projection of the quotient by the
stabilizer. -/
theorem ofQuotientHamiltonianFlowStabilizer_comp_mk (x : M) :
    hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x ∘
        Quotient.mk (AddAction.orbitRel (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
          (ι → ℝ)) =
      fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul x :=
  (rfl)

/-- The descended orbit map is injective. -/
theorem injective_ofQuotientHamiltonianFlowStabilizer (x : M) :
    Injective (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x) := by
  rintro ⟨v⟩ ⟨w⟩ h
  refine Quotient.sound ((Submodule.orbitRel_apply_iff_sub_mem _).2 ?_)
  have h' : -v + w ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x :=
    (hσ.hamiltonianFlowAction_apply_eq_iff hF hcomm hc).1 h
  -- Membership in `Λ.toIntSubmodule` is membership in `Λ`; the ascription states it for `Λ`.
  exact (by simpa only [neg_add_eq_sub, neg_sub] using neg_mem h' :
    v - w ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc x)

/-- The descended orbit map takes values in the level `F⁻¹(F x)`. -/
theorem apply_ofQuotientHamiltonianFlowStabilizer (x : M)
    (p : AddAction.orbitRel.Quotient (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
      (ι → ℝ)) :
    F (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x p) = F x := by
  induction p using Quotient.ind with
  | _ v => exact hσ.apply_hamiltonianFlowAction hF hcomm hc v x

/-- The descended orbit map takes values in the connected component of `x` in its level. -/
theorem ofQuotientHamiltonianFlowStabilizer_mem_connectedComponentIn (x : M)
    (p : AddAction.orbitRel.Quotient (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
      (ι → ℝ)) :
    hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x p ∈
      connectedComponentIn (F ⁻¹' {F x}) x := by
  induction p using Quotient.ind with
  | _ v => exact hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v

/-- **The range of the descended orbit map is the regular component.** On a manifold of
dimension `2 · |ι|`, if every point of the connected component `L` of `x` in its level is a
regular point of `F`, the range of `[v] ↦ v • x` is `L`. -/
theorem range_ofQuotientHamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) :
    range (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x) =
      connectedComponentIn (F ⁻¹' {F x}) x := by
  rw [← hσ.range_hamiltonianFlowAction_apply hF hcomm hc hdim hreg,
    ← hσ.ofQuotientHamiltonianFlowStabilizer_comp_mk hF hcomm hc x,
    Quotient.mk_surjective.range_comp]

/-- **The descended orbit map is a topological embedding** when the connected component of `x`
in its level consists of regular points of `F`, on a manifold of dimension `2 · |ι|`. -/
theorem isEmbedding_ofQuotientHamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y) :
    IsEmbedding (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x) := by
  -- It is the homeomorphism of `(ι → ℝ) ⧸ Λ` onto the component, read through the identification
  -- of the orbit space of translation by `Λ` with `(ι → ℝ) ⧸ Λ`, followed by the inclusion.
  let e := Submodule.orbitRelQuotientContinuousAddEquiv
    (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
  let g := hσ.quotientHamiltonianFlowStabilizerHomeomorph hF hcomm hc hdim hreg
  have h : hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x = Subtype.val ∘ g ∘ e := by
    funext p
    induction p using Quotient.ind with
    | _ v =>
      exact ((congrArg (fun q ↦ (g q : M))
        (Submodule.orbitRelQuotientContinuousAddEquiv_mk _ v)).trans
          (hσ.coe_quotientHamiltonianFlowStabilizerHomeomorph_mk hF hcomm hc hdim hreg v)).symm
  rw [h]
  exact IsEmbedding.subtypeVal.comp (g.isEmbedding.comp e.toHomeomorph.isEmbedding)

/-! ### Smoothness, immersion and the Lagrangian condition -/

/-- The descended orbit map is smooth, for the quotient manifold structure of `ι → ℝ` modulo the
discrete stabilizer. The stabilizer of a regular point is discrete
(`discreteTopology_hamiltonianFlowStabilizer`). -/
theorem contMDiff_ofQuotientHamiltonianFlowStabilizer (x : M)
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)] :
    ContMDiff 𝓘(ℝ, ι → ℝ) I ∞ (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x) :=
  (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℝ, ι → ℝ)) (n := ∞)).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl |>.1 (hσ.contMDiff_hamiltonianFlowAction_apply hF hcomm hc x)

/-- **The descended orbit map is a smooth embedding.** On a manifold of dimension `2 · |ι|`, if
every point of the connected component `L` of `x` in its level is a regular point of `F`, the map
`[v] ↦ v • x` from `(ι → ℝ) / Λ` is a smooth embedding with range `L`. Its derivative at `[v]` is
injective because that of the orbit map at `v`, `w ↦ ∑ i, wᵢ X_{Fᵢ}(v • x)`, is, and the orbit
projection `(ι → ℝ) → (ι → ℝ) / Λ` is a local diffeomorphism. -/
theorem isSmoothEmbedding_ofQuotientHamiltonianFlowStabilizer
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)] :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ι → ℝ) I ∞
      (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x) := by
  have hf := hσ.contMDiff_ofQuotientHamiltonianFlowStabilizer hF hcomm hc x
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.2 fun p ↦ ?_,
    hσ.isEmbedding_ofQuotientHamiltonianFlowStabilizer hF hcomm hc hdim hreg⟩
  refine (hf.contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ (mem_univ p)
    (by simp)).2 ?_
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective p
  have hq : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞
      (Quotient.mk (AddAction.orbitRel (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule
        (ι → ℝ))) v :=
    TauCeti.isLocalDiffeomorph_addQuotientMk v
  -- The derivative of the orbit map at `v` is the derivative of the descended map composed with
  -- the invertible derivative of the orbit projection; the former is injective at the regular
  -- point `v • x`.
  have hinj := hσ.injective_mfderiv_hamiltonianFlowAction_apply hF hcomm hc (x := x) (v := v)
    (hreg _ (hσ.hamiltonianFlowAction_apply_mem_connectedComponentIn hF hcomm hc x v))
  rw [← hσ.ofQuotientHamiltonianFlowStabilizer_comp_mk hF hcomm hc x,
    mfderiv_comp v (hf.mdifferentiableAt (by simp)) (hq.mdifferentiableAt (by simp))] at hinj
  exact Injective.of_comp_right hinj (hq.mfderivToContinuousLinearEquiv (by simp)).surjective

/-- **Regular components of a level are Lagrangian embeddings of `(ι → ℝ) / Λ`.** On a manifold of
dimension `2 · |ι|`, if every point of the connected component `L` of `x` in its level is a regular
point of `F`, the map `[v] ↦ v • x` from `(ι → ℝ) / Λ` is a Lagrangian embedding with range `L`.
When `L` is compact, `Λ` is a full lattice (`isZLattice_hamiltonianFlowStabilizer`) and
`(ι → ℝ) / Λ` is a torus. -/
theorem isLagrangianEmbedding_ofQuotientHamiltonianFlowStabilizer
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)] :
    hσ.isNondegenerate.IsLagrangianEmbedding 𝓘(ℝ, ι → ℝ)
      (hσ.ofQuotientHamiltonianFlowStabilizer hF hcomm hc x) := by
  have he := hσ.isSmoothEmbedding_ofQuotientHamiltonianFlowStabilizer hF hcomm hc hdim hreg
  refine (IsNondegenerate.isLagrangianEmbedding_iff_of_isSmoothEmbedding he).2 ?_
  exact hσ.isNondegenerate.isLagrangianMap_of_forall_eq
    (hσ.apply_ofQuotientHamiltonianFlowStabilizer hF hcomm hc x)
    (fun p ↦ hreg _ (hσ.ofQuotientHamiltonianFlowStabilizer_mem_connectedComponentIn hF hcomm hc
      x p))
    (fun _ i j ↦ hcomm i j _) (he.isImmersion.mfderiv_injective (by simp))
    (finrank_fintype_fun_eq_card ℝ) hdim

/-! ### Compact components: the period lattice -/

/-- **The stabilizer of a point of a compact regular component is a full lattice.** On a manifold
of dimension `2 · |ι|`, if the connected component `L` of `x` in its level is compact and consists
of regular points of `F`, the stabilizer `Λ` of `x` spans `ι → ℝ`, so `(ι → ℝ) / Λ` is a compact
torus. -/
theorem isZLattice_hamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
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
theorem finrank_hamiltonianFlowStabilizer (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hL : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x))
    [DiscreteTopology (hσ.hamiltonianFlowStabilizer hF hcomm hc x)] :
    finrank ℤ (hσ.hamiltonianFlowStabilizer hF hcomm hc x).toIntSubmodule = Fintype.card ι := by
  have := hσ.isZLattice_hamiltonianFlowStabilizer hF hcomm hc hdim hreg hL
  rw [ZLattice.rank ℝ, finrank_fintype_fun_eq_card]

end IsSymplectic

end SmoothTwoForm

end TauCeti
