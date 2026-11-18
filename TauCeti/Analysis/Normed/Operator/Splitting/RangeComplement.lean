/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.LinearAlgebra.LinearMap.Comp

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

## Main declarations

* `ContinuousLinearMap.leftInverseAlong L P`: the operator `(P ∘ L)⁻¹ ∘ P`.
* `ContinuousLinearMap.isInvertible_comp_iff`: `P ∘ L` is invertible if and only if `L` is
  injective, `P` is onto, and `ker P` is complementary to the range of `L`.
* `ContinuousLinearMap.isTopCompl_range_ker_of_isInvertible_comp`: if `P ∘ L` is invertible,
  `ker P` is a topological complement of the range of `L`.
* `ContinuousLinearMap.eq_leftInverseAlong`, `ContinuousLinearMap.leftInverseAlong_congr`: the
  left inverse of `L` vanishing on `ker P` is unique, and depends on `P` only through `ker P`.
* `ContinuousLinearMap.id_sub_comp_leftInverseAlong_eq_projectionL`: `1 - L (P ∘ L)⁻¹ P` is the
  projection onto `ker P` along the range of `L`.
* `ContinuousLinearMap.apply_add_mem_ker_iff`: `L f + S ∈ ker P` exactly for
  `f = -(P ∘ L)⁻¹ P S`.
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

section Ring

variable {R E F Y : Type*} [Ring R]
  [AddCommGroup E] [TopologicalSpace E] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [Module R F]
  [AddCommGroup Y] [TopologicalSpace Y] [Module R Y]
  {L : E →L[R] F} {P : F →L[R] Y}

/-- The left inverse `(P ∘ L)⁻¹ ∘ P` of `L` along the kernel of `P`. It is a left inverse of
`L` with kernel `ker P` whenever `P ∘ L` is invertible
(`ContinuousLinearMap.leftInverseAlong_comp`,
`ContinuousLinearMap.ker_leftInverseAlong`), and otherwise a junk value built from the total
inverse `ContinuousLinearMap.inverse`. -/
noncomputable def leftInverseAlong (L : E →L[R] F) (P : F →L[R] Y) : F →L[R] E :=
  (P ∘L L).inverse ∘L P

/-- The defining formula of the left inverse along `ker P`. -/
theorem leftInverseAlong_def (L : E →L[R] F) (P : F →L[R] Y) :
    leftInverseAlong L P = (P ∘L L).inverse ∘L P :=
  (rfl)

/-- The value of the left inverse along `ker P`. -/
theorem leftInverseAlong_apply (L : E →L[R] F) (P : F →L[R] Y) (f : F) :
    leftInverseAlong L P f = (P ∘L L).inverse (P f) :=
  (rfl)

/-- `(P ∘ L)⁻¹ P` is a left inverse of `L`. -/
theorem leftInverseAlong_comp (h : (P ∘L L).IsInvertible) :
    leftInverseAlong L P ∘L L = .id R E := by
  rw [leftInverseAlong_def, comp_assoc, h.inverse_comp_self]

/-- `(P ∘ L)⁻¹ P` is a left inverse of `L`. -/
@[simp]
theorem leftInverseAlong_apply_apply (h : (P ∘L L).IsInvertible) (x : E) :
    leftInverseAlong L P (L x) = x := by
  simpa [leftInverseAlong_apply] using h.inverse_apply_self x

/-- The left inverse along `ker P` does not change the value of `P` after applying `L`. -/
@[simp]
theorem apply_apply_leftInverseAlong (h : (P ∘L L).IsInvertible) (f : F) :
    P (L (leftInverseAlong L P f)) = P f := by
  simpa [leftInverseAlong_apply] using h.self_apply_inverse (P f)

/-- The kernel of the left inverse along `ker P` is exactly `ker P`. -/
@[simp]
theorem ker_leftInverseAlong (h : (P ∘L L).IsInvertible) :
    (leftInverseAlong L P).ker = P.ker := by
  ext f
  simp only [LinearMap.mem_ker, coe_coe, leftInverseAlong_apply]
  exact ⟨fun hf ↦ by simpa [hf] using (h.self_apply_inverse (P f)).symm,
    fun hf ↦ by rw [hf, map_zero]⟩

/-- `f - L ((P ∘ L)⁻¹ P f)` lies in the kernel of `P`. -/
theorem sub_apply_leftInverseAlong_mem_ker (h : (P ∘L L).IsInvertible) (f : F) :
    f - L (leftInverseAlong L P f) ∈ P.ker := by
  simp [LinearMap.mem_ker, h]

/-- **Uniqueness of the left inverse along a complement.** A left inverse of `L` that vanishes on
`ker P` is `(P ∘ L)⁻¹ P`. -/
theorem eq_leftInverseAlong (h : (P ∘L L).IsInvertible) {K : F →L[R] E}
    (hKL : K ∘L L = .id R E) (hK : P.ker ≤ K.ker) : K = leftInverseAlong L P := by
  ext f
  have hw : K (f - L (leftInverseAlong L P f)) = 0 := hK (sub_apply_leftInverseAlong_mem_ker h f)
  rw [map_sub, sub_eq_zero, ← comp_apply K L, hKL, id_apply] at hw
  exact hw

/-- The left inverse along `ker P` depends on `P` only through its kernel. -/
theorem leftInverseAlong_congr {Y' : Type*} [AddCommGroup Y'] [TopologicalSpace Y'] [Module R Y']
    {P' : F →L[R] Y'} (h : (P ∘L L).IsInvertible) (h' : (P' ∘L L).IsInvertible)
    (hker : P.ker = P'.ker) : leftInverseAlong L P = leftInverseAlong L P' :=
  eq_leftInverseAlong h' (leftInverseAlong_comp h) (by rw [← hker, ker_leftInverseAlong h])

/-- If `P ∘ L` is invertible, the kernel of `P` is a topological complement of the range of
`L`. -/
theorem isTopCompl_range_ker_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    L.range.IsTopCompl P.ker := by
  have hrange : (L ∘L (P ∘L L).inverse).range = L.range := by
    simpa using LinearMap.range_comp_of_range_eq_top (L : E →ₗ[R] F)
      (LinearMap.range_eq_top.mpr h.inverse.surjective)
  have hleft : LeftInverse P (L ∘L (P ∘L L).inverse) := fun y ↦ by
    simpa using h.self_apply_inverse y
  exact hrange ▸ isTopCompl_range_ker_of_leftInverse _ _ hleft

/-- As a linear map, the left inverse along `ker P` is Mathlib's left inverse
`LinearMap.linearProjOfIsCompl` of the injection `L` along the complement `ker P` of its range.
`ContinuousLinearMap.leftInverseAlong` realizes it continuously by the explicit formula
`(P ∘ L)⁻¹ P`. -/
theorem toLinearMap_leftInverseAlong (h : (P ∘L L).IsInvertible) :
    (leftInverseAlong L P : F →ₗ[R] E) =
      LinearMap.linearProjOfIsCompl P.ker (L : E →ₗ[R] F)
        (Injective.of_comp (f := P) h.injective)
        (isTopCompl_range_ker_of_isInvertible_comp h).isCompl := by
  ext f
  have hf := sub_apply_leftInverseAlong_mem_ker h f
  conv_rhs => rw [← sub_add_cancel f (L (leftInverseAlong L P f))]
  rw [map_add, LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ hf, zero_add]
  exact (LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ (leftInverseAlong L P f)).symm

/-- `L (P ∘ L)⁻¹ P` is the projection onto the range of `L` along `ker P`. -/
theorem comp_leftInverseAlong_eq_projectionL (h : (P ∘L L).IsInvertible) :
    L ∘L leftInverseAlong L P =
      L.range.projectionL P.ker (isTopCompl_range_ker_of_isInvertible_comp h) := by
  have hc := isTopCompl_range_ker_of_isInvertible_comp h
  ext f
  have hrange : L.range.projectionL P.ker hc (L (leftInverseAlong L P f)) =
      L (leftInverseAlong L P f) :=
    (Submodule.projectionL_eq_self_iff hc _).mpr ⟨leftInverseAlong L P f, rfl⟩
  have hker : L.range.projectionL P.ker hc (f - L (leftInverseAlong L P f)) = 0 :=
    Submodule.projectionL_apply_eq_zero_of_mem_right hc (sub_apply_leftInverseAlong_mem_ker h f)
  rw [map_sub, hrange, sub_eq_zero] at hker
  exact hker.symm

/-- `L f + S` lies in the kernel of `P` exactly for the correction `f = -(P ∘ L)⁻¹ P S`. In
particular this correction depends on `P` only through its kernel. -/
theorem apply_add_mem_ker_iff (h : (P ∘L L).IsInvertible) {S : F} {x : E} :
    L x + S ∈ P.ker ↔ x = -leftInverseAlong L P S := by
  constructor
  · intro hx
    have hK : leftInverseAlong L P (L x + S) = 0 := by
      have hx' : L x + S ∈ (leftInverseAlong L P).ker := by rwa [ker_leftInverseAlong h]
      exact LinearMap.mem_ker.mp hx'
    rw [map_add, leftInverseAlong_apply_apply h] at hK
    exact eq_neg_of_add_eq_zero_left hK
  · rintro rfl
    simp [LinearMap.mem_ker, h]

variable [IsTopologicalAddGroup F]

/-- **The projection along the range.** If `P ∘ L` is invertible, `1 - L (P ∘ L)⁻¹ P` is the
projection onto `ker P` along the range of `L`. In particular it depends on `P` only through its
kernel. -/
theorem id_sub_comp_leftInverseAlong_eq_projectionL (h : (P ∘L L).IsInvertible) :
    .id R F - L ∘L leftInverseAlong L P =
      P.ker.projectionL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm := by
  rw [comp_leftInverseAlong_eq_projectionL h, Submodule.projectionL_eq_id_sub_projectionL
    (isTopCompl_range_ker_of_isInvertible_comp h)]

/-- **The leading correction.** For `S ∈ F`, the vector `f = -(P ∘ L)⁻¹ P S` satisfies
`L f + S = Π S`, where `Π` is the projection onto `ker P` along the range of `L`. -/
theorem apply_neg_leftInverseAlong_add_eq_projectionL (h : (P ∘L L).IsInvertible) (S : F) :
    L (-leftInverseAlong L P S) + S =
      P.ker.projectionL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm S := by
  rw [← id_sub_comp_leftInverseAlong_eq_projectionL h, map_neg, sub_apply, id_apply, comp_apply]
  abel

end Ring

section Banach

variable {𝕜 E F Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {L : E →L[𝕜] F} {P : F →L[𝕜] Y}

/-- Between Banach spaces, `P ∘ L` is invertible exactly when `L` is injective, `P` is onto, and
the kernel of `P` is complementary to the range of `L`. -/
theorem isInvertible_comp_iff [CompleteSpace Y] :
    (P ∘L L).IsInvertible ↔ Injective L ∧ IsCompl L.range P.ker ∧ Surjective P := by
  refine ⟨fun h ↦ ⟨Injective.of_comp (f := P) h.injective,
    (isTopCompl_range_ker_of_isInvertible_comp h).isCompl,
    Surjective.of_comp (g := L) h.surjective⟩,
    fun hc ↦ ?_⟩
  have hb : Bijective (P ∘L L) :=
    LinearMap.bijective_comp_iff (L := (L : E →ₗ[𝕜] F)).mpr hc
  exact ⟨.ofBijective (P ∘L L) (LinearMap.ker_eq_bot.mpr hb.injective)
    (LinearMap.range_eq_top.mpr hb.surjective), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

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
