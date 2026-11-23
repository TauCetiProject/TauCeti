/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Normed.Operator.Banach
public import TauCeti.LinearAlgebra.LinearMap.Comp
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse

/-!
# Complements of the range cut out by a kernel

Let `L : E →L[R] F` be an operator and `P : F →L[R] Y` a second operator, thought of as an
auxiliary projection whose kernel `W = ker P` is a candidate complement of the range of `L`. The
composite `A = P ∘ L` is bijective exactly when `L` is injective, `P` is onto, and `W` is
complementary to the range of `L` (`LinearMap.bijective_comp_iff`); between Banach spaces this is
the same as invertibility of `A` (`ContinuousLinearMap.isInvertible_comp_iff`).

When `A` is invertible, `K = A⁻¹ P` (`ContinuousLinearMap.leftInverseAlong L P`) is the left
inverse of `L` along `W`: `K L = 1` and `ker K = W`. It is the only continuous left inverse of `L`
vanishing on `W` (`ContinuousLinearMap.eq_leftInverseAlong`), so it depends on `P` only through its
kernel (`ContinuousLinearMap.leftInverseAlong_congr`). As a linear map it is Mathlib's
`LinearMap.linearProjOfIsCompl` (`ContinuousLinearMap.toLinearMap_leftInverseAlong`); the formula
`A⁻¹ P` makes it continuous and lets it vary with `L` and `P`. Moreover `W` is a topological
complement of the range of `L`, and

`Π = 1 - L A⁻¹ P`

is the continuous projection of `F` onto `W` along the range of `L`
(`ContinuousLinearMap.id_sub_comp_leftInverseAlong_eq_projectionL`). For every `S ∈ F` the
vector `f = -A⁻¹ P S` is the unique solution of `L f + S ∈ W`, and `L f + S = Π S`
(`ContinuousLinearMap.apply_add_mem_ker_iff`,
`ContinuousLinearMap.apply_neg_leftInverseAlong_add_eq_projectionL`). Conversely, between Banach
spaces every topological complement `W` of the range of an injective `L` arises this way, from the
projection onto the range along `W` (`ContinuousLinearMap.isInvertible_projectionOntoL_comp`).

This is the leading step of a Lyapunov–Schmidt reduction: an equation `L f + S = 0` with `L` not
onto is solved modulo the fixed complement `W`, leaving the remainder `Π S` in `W`. Neither `Π`
nor `f` depends on the auxiliary map `P` once its kernel `W` is fixed. For a family of operators
`L x` over a parameter space, invertibility of `P ∘ L x` is an open condition
(`ContinuousLinearMap.isOpen_setOf_isInvertible_comp`), and on it `K` and `Π` have the regularity
of the family (`ContinuousAt.leftInverseAlong`, `ContinuousAt.id_sub_comp_leftInverseAlong`,
`ContDiffAt.leftInverseAlong`, `ContDiffAt.id_sub_comp_leftInverseAlong`).

The definition of `ContinuousLinearMap.leftInverseAlong` and its algebraic, complement and
projection lemmas need no norm and live in
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse`. This file adds the Banach-space
results and the dependence on a parameter.

## Main declarations

* `ContinuousLinearMap.isInvertible_comp_iff`: `P ∘ L` is invertible if and only if `L` is
  injective, `P` is onto, and `ker P` is complementary to the range of `L`.
* `ContinuousLinearMap.isInvertible_projectionOntoL_comp`: every topological complement of the
  range of an injective `L` is the kernel of some `P` with `P ∘ L` invertible.
* `ContinuousLinearMap.isOpen_setOf_isInvertible_comp`: invertibility of `P ∘ L x` is an open
  condition on the parameter.
* `ContinuousAt.leftInverseAlong`, `ContinuousAt.id_sub_comp_leftInverseAlong`,
  `ContDiffAt.leftInverseAlong`, `ContDiffAt.id_sub_comp_leftInverseAlong`: regularity in a
  parameter.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* S. N. Chow and J. K. Hale, *Methods of Bifurcation Theory*, Springer, 1982, Chapter 2.
-/

public section

open Function Topology

namespace ContinuousLinearMap

section Banach

variable {𝕜 E F Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {L : E →L[𝕜] F} {P : F →L[𝕜] Y}

/-- Between Banach spaces, `P ∘ L` is invertible exactly when `L` is injective, `P` is onto, and
the kernel of `P` is complementary to the range of `L`. -/
theorem isInvertible_comp_iff [CompleteSpace Y] :
    (P ∘L L).IsInvertible ↔ Injective L ∧ IsCompl L.range P.ker ∧ Surjective P :=
  isInvertible_iff_bijective.trans LinearMap.bijective_comp_iff

/-- Every topological complement `W` of the range of an injective operator `L` between Banach
spaces is the kernel of an auxiliary map `P` with `P ∘ L` invertible, namely the projection onto
the range of `L` along `W`. -/
theorem isInvertible_projectionOntoL_comp [CompleteSpace F] {W : Submodule 𝕜 F}
    (hL : Injective L) (hc : L.range.IsTopCompl W) :
    (L.range.projectionOntoL W hc ∘L L).IsInvertible := by
  have : CompleteSpace L.range := hc.isClosed.completeSpace_coe
  rw [isInvertible_comp_iff, Submodule.ker_projectionOntoL]
  exact ⟨hL, hc.isCompl, Submodule.projectionOntoL_surjective hc⟩

variable {X : Type*}

/-- For a continuous family `L x` of operators out of a Banach space, the parameters at which
`P ∘ L x` is invertible form an open set. -/
theorem isOpen_setOf_isInvertible_comp [TopologicalSpace X] {L : X → E →L[𝕜] F}
    (hL : Continuous L) : IsOpen {x | (P ∘L L x).IsInvertible} :=
  isOpen_setOfPred_isInvertible.preimage (continuous_const.clm_comp hL)

/-- The left inverse along `ker P` depends smoothly on the operators at every pair where
`P ∘ L` is invertible. -/
theorem contDiffAt_leftInverseAlong {n : WithTop ℕ∞} (h : (P ∘L L).IsInvertible) :
    ContDiffAt 𝕜 n (fun p : (E →L[𝕜] F) × (F →L[𝕜] Y) ↦ leftInverseAlong p.1 p.2)
      (L, P) := by
  have hcomp : ContDiff 𝕜 n (fun p : (E →L[𝕜] F) × (F →L[𝕜] Y) ↦ p.2 ∘L p.1) :=
    contDiff_snd.clm_comp contDiff_fst
  simp_rw [leftInverseAlong_def]
  exact (h.contDiffAt_map_inverse.comp (L, P) hcomp.contDiffAt).clm_comp contDiffAt_snd

end Banach

end ContinuousLinearMap

section Family

open ContinuousLinearMap

variable {𝕜 E F Y X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The left inverse along `ker (P x)` of a family `L x` is continuous at every parameter where
both families are continuous and `P x ∘ L x` is invertible. -/
theorem ContinuousAt.leftInverseAlong [TopologicalSpace X] {L : X → E →L[𝕜] F}
    {P : X → F →L[𝕜] Y} {x : X} (hL : ContinuousAt L x) (hP : ContinuousAt P x)
    (h : (P x ∘L L x).IsInvertible) :
    ContinuousAt (fun y ↦ ContinuousLinearMap.leftInverseAlong (L y) (P y)) x :=
  (contDiffAt_leftInverseAlong (n := 0) h).continuousAt.comp (f := fun y ↦ (L y, P y))
    (hL.prodMk hP)

/-- The left inverse along `ker (P x)` of a family `L x` has the regularity of the two families at
every parameter where `P x ∘ L x` is invertible. -/
theorem ContDiffAt.leftInverseAlong [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {L : X → E →L[𝕜] F} {P : X → F →L[𝕜] Y} {x : X} {n : WithTop ℕ∞}
    (hL : ContDiffAt 𝕜 n L x) (hP : ContDiffAt 𝕜 n P x) (h : (P x ∘L L x).IsInvertible) :
    ContDiffAt 𝕜 n (fun y ↦ ContinuousLinearMap.leftInverseAlong (L y) (P y)) x :=
  (contDiffAt_leftInverseAlong h).comp (f := fun y ↦ (L y, P y)) x (hL.prodMk hP)

/-- The projections `1 - L x (P x ∘ L x)⁻¹ P x` onto `ker (P x)` along the range of `L x` are
continuous at every parameter where both families are continuous and `P x ∘ L x` is invertible. -/
theorem ContinuousAt.id_sub_comp_leftInverseAlong [TopologicalSpace X] {L : X → E →L[𝕜] F}
    {P : X → F →L[𝕜] Y} {x : X} (hL : ContinuousAt L x) (hP : ContinuousAt P x)
    (h : (P x ∘L L x).IsInvertible) :
    ContinuousAt
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L
        ContinuousLinearMap.leftInverseAlong (L y) (P y)) x :=
  continuousAt_const.sub (hL.clm_comp (hL.leftInverseAlong hP h))

/-- The projections `1 - L x (P x ∘ L x)⁻¹ P x` onto `ker (P x)` along the range of `L x` have
the regularity of the two families at every parameter where `P x ∘ L x` is invertible. -/
theorem ContDiffAt.id_sub_comp_leftInverseAlong [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {L : X → E →L[𝕜] F} {P : X → F →L[𝕜] Y} {x : X} {n : WithTop ℕ∞}
    (hL : ContDiffAt 𝕜 n L x) (hP : ContDiffAt 𝕜 n P x) (h : (P x ∘L L x).IsInvertible) :
    ContDiffAt 𝕜 n
      (fun y ↦ ContinuousLinearMap.id 𝕜 F - L y ∘L
        ContinuousLinearMap.leftInverseAlong (L y) (P y)) x :=
  contDiffAt_const.sub (hL.clm_comp (hL.leftInverseAlong hP h))

/-- Near a parameter `x` at which the family is continuous and `P ∘ L x` is invertible, the kernel
of `P` stays a topological complement of the range of `L y`. -/
theorem ContinuousAt.eventually_isTopCompl_range_ker [TopologicalSpace X] {L : X → E →L[𝕜] F}
    {P : F →L[𝕜] Y} {x : X} (hL : ContinuousAt L x) (h : (P ∘L L x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, (L y).range.IsTopCompl P.ker := by
  have hopen : ∀ᶠ y in 𝓝 x, (P ∘L L y).IsInvertible :=
    (continuousAt_const.clm_comp hL).eventually_mem
      (isOpen_setOfPred_isInvertible.mem_nhds h)
  exact hopen.mono fun y hy ↦ isTopCompl_range_ker_of_isInvertible_comp hy

end Family
