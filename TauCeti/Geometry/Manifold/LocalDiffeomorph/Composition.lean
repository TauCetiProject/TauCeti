/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Cancelling local diffeomorphisms from compositions

A continuous map into a manifold is `C^n` if its composite with a `C^n` local diffeomorphism is
`C^n`. This file provides pointwise-within, on-set, and global versions of this cancellation
principle.

Dually, a map out of a manifold is `C^m` at the image of a point at which `p` is a `C^n` local
diffeomorphism, for `m ≤ n`, exactly when its precomposite with `p` is `C^m` at that point. For a
surjective local diffeomorphism, such as the orbit projection of a free properly discontinuous
action, this characterises the `C^m` maps out of its target. The same holds for maps out of a
product `A × B` whose second factor is the target of `p`, precomposed with `Prod.map id p`; this
characterises the `C^m` maps `A × B → N`, such as flows on a quotient manifold. A map out of an
open subset `U` of the target is `C^m` at `p x ∈ U` when, at each `p y ∈ U`, it agrees with a map
that is `C^m` at `x`.

Precomposing a `C^n` local diffeomorphism out of a normed space `E` with a continuous linear
automorphism of `E` gives again a `C^n` local diffeomorphism
(`IsLocalDiffeomorph.comp_continuousLinearEquiv`); for open embeddings this is Mathlib's
`Homeomorph.isOpenEmbedding_comp_iff`. For a linear isometry `R`, both facts are also stated for
`e ∘ R` itself (`Topology.IsOpenEmbedding.comp_linearIsometryEquiv`,
`IsLocalDiffeomorph.comp_linearIsometryEquiv`): the coercion of `R` to a continuous linear
equivalence is not reducibly equal to `R`, so instances built from the general statements would not
apply to `e ∘ R`.

## Main results

* `ContMDiffWithinAt.of_comp_isLocalDiffeomorph`: pointwise-within cancellation.
* `ContMDiffOn.of_comp_isLocalDiffeomorph`: on-set cancellation.
* `ContMDiff.of_comp_isLocalDiffeomorph`: global cancellation.
* `IsLocalDiffeomorphAt.contMDiffAt_comp_iff`: pointwise cancellation on the source side.
* `IsLocalDiffeomorphAt.mdifferentiableAt_comp_iff`, `IsLocalDiffeomorphAt.mfderiv_comp`,
  `IsLocalDiffeomorphAt.isInvertible_mfderiv_comp_iff`: differentiability, chain rule, and
  invertibility of the manifold derivative under precomposition with a local diffeomorphism.
* `IsLocalDiffeomorphAt.ker_mfderiv_comp`: postcomposing with a local diffeomorphism does not
  change the kernel of the differential.
* `IsLocalDiffeomorphAt.contMDiffAt_of_forall_eq`: a sufficient condition for `C^m` maps out of
  an open subset of the target.
* `IsLocalDiffeomorph.contMDiff_comp_iff`: global cancellation on the source side, for a
  surjective local diffeomorphism.
* `IsLocalDiffeomorph.existsUnique_contMDiff_comp_eq`: a `C^m` map constant on the fibres of a
  surjective local diffeomorphism descends to a unique `C^m` map on its target.
* `IsLocalDiffeomorphAt.contMDiffAt_comp_prodMap_iff`,
  `IsLocalDiffeomorph.contMDiff_comp_prodMap_iff`: the same cancellation for maps out of a
  product, along the second factor.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : M → B} {f : N → M}

/-- A continuous map is `C^n` within a set at a point when its composite with a map that is a
`C^n` local diffeomorphism at the image point is `C^n` there. -/
theorem _root_.ContMDiffWithinAt.of_comp_isLocalDiffeomorph {s : Set N} {y : N}
    (hp : IsLocalDiffeomorphAt I J n p (f y)) (hf : ContinuousWithinAt f s y)
    (hpf : ContMDiffWithinAt I' J n (p ∘ f) s y) : ContMDiffWithinAt I' I n f s y := by
  have hcomp : ContMDiffWithinAt I' I n (hp.localInverse ∘ (p ∘ f)) s y :=
    hp.contMDiffAt_localInverse.comp_contMDiffWithinAt y hpf
  have heq : Filter.EventuallyEq (nhdsWithin y s) (hp.localInverse ∘ (p ∘ f)) f := by
    exact hp.localInverse_eventuallyEq_left.comp_tendsto hf
  exact hcomp.congr_of_eventuallyEq heq.symm
    (hp.localInverse_left_inv hp.localInverse_mem_target).symm

/-- A continuous map on a set is `C^n` there when its composite with a `C^n` local diffeomorphism
is `C^n` on that set. -/
theorem _root_.ContMDiffOn.of_comp_isLocalDiffeomorph (hp : IsLocalDiffeomorph I J n p)
    {s : Set N} (hf : ContinuousOn f s) (hpf : ContMDiffOn I' J n (p ∘ f) s) :
    ContMDiffOn I' I n f s :=
  fun y hy ↦ (hpf y hy).of_comp_isLocalDiffeomorph (hp (f y)) (hf y hy)

/-- A continuous map is `C^n` when its composite with a `C^n` local diffeomorphism is `C^n`. -/
theorem _root_.ContMDiff.of_comp_isLocalDiffeomorph (hp : IsLocalDiffeomorph I J n p)
    (hf : Continuous f) (hpf : ContMDiff I' J n (p ∘ f)) : ContMDiff I' I n f := by
  rw [← contMDiffOn_univ]
  exact hpf.contMDiffOn.of_comp_isLocalDiffeomorph hp hf.continuousOn

/-- If `p` is a `C^n` local diffeomorphism at `x` and `m ≤ n`, a map `g` is `C^m` at `p x`
exactly when `g ∘ p` is `C^m` at `x`. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_comp_iff {m : ℕ∞ω} {x : M} {g : B → N}
    (hp : IsLocalDiffeomorphAt I J n p x) (hm : m ≤ n) :
    ContMDiffAt I I' m (g ∘ p) x ↔ ContMDiffAt J I' m g (p x) := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.comp x (hp.contMDiffAt.of_le hm)⟩
  -- near `p x`, the map `g` agrees with `(g ∘ p) ∘ q` for the local inverse `q` of `p`
  have hcomp : ContMDiffAt J I' m ((g ∘ p) ∘ hp.localInverse) (p x) :=
    hg.comp_of_eq (hp.contMDiffAt_localInverse.of_le hm)
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  exact hcomp.congr_of_eventuallyEq (hp.localInverse_eventuallyEq_right.fun_comp g).symm

/-- If `p` is a `C^n` local diffeomorphism at `x` with `n ≠ 0`, a map `g` is differentiable at
`p x` exactly when `g ∘ p` is differentiable at `x`. -/
theorem _root_.IsLocalDiffeomorphAt.mdifferentiableAt_comp_iff {x : M} {g : B → N}
    (hp : IsLocalDiffeomorphAt I J n p x) (hn : n ≠ 0) :
    MDifferentiableAt I I' (g ∘ p) x ↔ MDifferentiableAt J I' g (p x) := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.comp x (hp.mdifferentiableAt hn)⟩
  -- near `p x`, the map `g` agrees with `(g ∘ p) ∘ q` for the local inverse `q` of `p`
  have hcomp : MDifferentiableAt J I' ((g ∘ p) ∘ hp.localInverse) (p x) :=
    hg.comp_of_eq (p x) (hp.mdifferentiableAt_localInverse hn)
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  exact hcomp.congr_of_eventuallyEq (hp.localInverse_eventuallyEq_right.fun_comp g).symm

/-- **Unconditional chain rule on the right for a local diffeomorphism.** Precomposing an arbitrary
map `g` with a `C^n` local diffeomorphism `p` at `x` (`n ≠ 0`) composes its manifold derivative with
`mfderiv p`: where `g` is not differentiable at `p x`, neither is `g ∘ p` at `x`, and both sides
vanish. -/
theorem _root_.IsLocalDiffeomorphAt.mfderiv_comp {x : M}
    (hp : IsLocalDiffeomorphAt I J n p x) (hn : n ≠ 0) (g : B → N) :
    mfderiv I I' (g ∘ p) x = (mfderiv J I' g (p x)).comp (mfderiv I J p x) := by
  by_cases hg : MDifferentiableAt J I' g (p x)
  · exact _root_.mfderiv_comp x hg (hp.mdifferentiableAt hn)
  · have hgp : ¬MDifferentiableAt I I' (g ∘ p) x := (hp.mdifferentiableAt_comp_iff hn).not.mpr hg
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hgp,
      ContinuousLinearMap.zero_comp]

/-- Precomposing an arbitrary map `g` with a `C^n` local diffeomorphism `p` at `x` (`n ≠ 0`)
preserves invertibility of the manifold derivative. -/
theorem _root_.IsLocalDiffeomorphAt.isInvertible_mfderiv_comp_iff {x : M} {g : B → N}
    (hp : IsLocalDiffeomorphAt I J n p x) (hn : n ≠ 0) :
    (mfderiv I I' (g ∘ p) x).IsInvertible ↔ (mfderiv J I' g (p x)).IsInvertible := by
  rw [hp.mfderiv_comp hn, ← hp.mfderivToContinuousLinearEquiv_coe hn,
    ContinuousLinearMap.isInvertible_comp_equiv]

/-- Postcomposing a map differentiable at `y` with a map that is a `C^n` local diffeomorphism at
its image, `n ≠ 0`, does not change the kernel of the differential at `y`. -/
theorem _root_.IsLocalDiffeomorphAt.ker_mfderiv_comp {y : N}
    (hp : IsLocalDiffeomorphAt I J n p (f y)) (hn : n ≠ 0) (hf : MDifferentiableAt I' I f y) :
    (mfderiv I' J (p ∘ f) y).ker = (mfderiv I' I f y).ker := by
  ext v
  rw [_root_.mfderiv_comp y (hp.mdifferentiableAt hn) hf]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [← hp.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.map_eq_zero_iff]

/-- Let `p` be a `C^n` local diffeomorphism at `x`, `m ≤ n`, and `U` an open neighbourhood of `p x`.
A map `g` out of `U` is `C^m` at `p x` when `g (p y) = f y` whenever `p y ∈ U`, for a map `f` that
is `C^m` at `x`: near `p x`, `g` is `f` composed with a local inverse of `p`. This is the analogue
of `IsLocalDiffeomorphAt.contMDiffAt_comp_iff` for maps defined only on an open subset. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_of_forall_eq {m : ℕ∞ω} {x : M}
    (hp : IsLocalDiffeomorphAt I J n p x) (hm : m ≤ n) (U : TopologicalSpace.Opens B)
    (hx : p x ∈ U) {f : M → N} (hf : ContMDiffAt I I' m f x) {g : U → N}
    (hg : ∀ y (hy : p y ∈ U), g ⟨p y, hy⟩ = f y) :
    ContMDiffAt J I' m g ⟨p x, hx⟩ := by
  refine ContMDiffAt.congr_of_eventuallyEq (f := fun y : U ↦ f (hp.localInverse y)) ?_ ?_
  · exact hf.comp_of_eq ((hp.contMDiffAt_localInverse.of_le hm).comp (⟨p x, hx⟩ : U)
        contMDiff_subtypeVal.contMDiffAt)
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  · filter_upwards [hp.localInverse_eventuallyEq_right.comp_tendsto
      continuous_subtypeVal.continuousAt] with ⟨y, hy⟩ hpy
    simp only [Function.comp_apply, id_eq] at hpy
    have hy' : p (hp.localInverse y) ∈ U := by rwa [hpy]
    rw [← hg _ hy']
    exact congrArg g (Subtype.ext hpy.symm)

/-- If `p` is a surjective `C^n` local diffeomorphism and `m ≤ n`, a map `g` out of its target is
`C^m` exactly when `g ∘ p` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_comp_iff {m : ℕ∞ω} {g : B → N}
    (hp : IsLocalDiffeomorph I J n p) (hsurj : Function.Surjective p) (hm : m ≤ n) :
    ContMDiff I I' m (g ∘ p) ↔ ContMDiff J I' m g := by
  refine ⟨fun hg y ↦ ?_, fun hg ↦ hg.comp (hp.contMDiff.of_le hm)⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hp x).contMDiffAt_comp_iff hm).1 (hg x)

/-- **Smooth maps constant on fibres descend along a surjective local diffeomorphism.** If `p` is a
surjective `C^n` local diffeomorphism, `m ≤ n`, and a `C^m` map `g` is constant on the fibres of
`p`, then `g` factors as `g' ∘ p` for a unique map `g'`, and `g'` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.existsUnique_contMDiff_comp_eq {m : ℕ∞ω} {g : M → N}
    (hp : IsLocalDiffeomorph I J n p) (hsurj : Function.Surjective p) (hm : m ≤ n)
    (hg : ContMDiff I I' m g) (hgp : Function.FactorsThrough g p) :
    ∃! g' : B → N, ContMDiff J I' m g' ∧ g' ∘ p = g := by
  have hcomp : (g ∘ Function.surjInv hsurj) ∘ p = g :=
    funext fun x ↦ hgp (Function.surjInv_eq hsurj (p x))
  refine ⟨g ∘ Function.surjInv hsurj,
    ⟨(hp.contMDiff_comp_iff hsurj hm).1 (by rwa [hcomp]), hcomp⟩, fun g' hg' ↦ ?_⟩
  exact hsurj.injective_comp_right (hg'.2.trans hcomp.symm)

section Prod

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- If `p` is a `C^n` local diffeomorphism at `x` and `m ≤ n`, a map `g` out of a product is `C^m`
at `(a, p x)` exactly when `g ∘ Prod.map id p` is `C^m` at `(a, x)`. -/
theorem _root_.IsLocalDiffeomorphAt.contMDiffAt_comp_prodMap_iff {m : ℕ∞ω} {x : M} {a : N}
    {g : N × B → P} (hp : IsLocalDiffeomorphAt I J n p x) (hm : m ≤ n) :
    ContMDiffAt (I'.prod I) I'' m (g ∘ Prod.map id p) (a, x) ↔
      ContMDiffAt (I'.prod J) I'' m g (a, p x) := by
  refine ⟨fun hg ↦ ?_,
    fun hg ↦ hg.comp (a, x) (contMDiffAt_id.prodMap (hp.contMDiffAt.of_le hm))⟩
  -- near `(a, p x)`, the map `g` agrees with `(g ∘ Prod.map id p) ∘ Prod.map id q` for the local
  -- inverse `q` of `p`
  have hcomp : ContMDiffAt (I'.prod J) I'' m
      ((g ∘ Prod.map id p) ∘ Prod.map id hp.localInverse) (a, p x) :=
    hg.comp_of_eq (contMDiffAt_id.prodMap (hp.contMDiffAt_localInverse.of_le hm))
      (by simp [hp.localInverse_left_inv hp.localInverse_mem_target])
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hp.localInverse_eventuallyEq_right.comp_tendsto
    (continuous_snd.tendsto (a, p x))] with ⟨b, y⟩ hy
  simp only [Function.comp_apply, Prod.map_apply, id_eq] at hy ⊢
  rw [hy]

/-- If `p` is a surjective `C^n` local diffeomorphism and `m ≤ n`, a map `g` out of a product with
second factor the target of `p` is `C^m` exactly when `g ∘ Prod.map id p` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_comp_prodMap_iff {m : ℕ∞ω} {g : N × B → P}
    (hp : IsLocalDiffeomorph I J n p) (hsurj : Function.Surjective p) (hm : m ≤ n) :
    ContMDiff (I'.prod I) I'' m (g ∘ Prod.map id p) ↔ ContMDiff (I'.prod J) I'' m g := by
  refine ⟨fun hg y ↦ ?_,
    fun hg ↦ hg.comp (contMDiff_id.prodMap (hp.contMDiff.of_le hm))⟩
  obtain ⟨x, hx⟩ := hsurj y.2
  rw [← Prod.mk.eta (p := y), ← hx]
  exact ((hp x).contMDiffAt_comp_prodMap_iff hm).1 (hg (y.1, x))

end Prod

section ContinuousLinearEquiv

/-- A `C^n` local diffeomorphism out of a normed space `E` remains one when precomposed with a
continuous linear automorphism of `E`. -/
theorem _root_.IsLocalDiffeomorph.comp_continuousLinearEquiv {e : E → M}
    (d : IsLocalDiffeomorph 𝓘(𝕜, E) I n e) (L : E ≃L[𝕜] E) :
    IsLocalDiffeomorph 𝓘(𝕜, E) I n (e ∘ L) := fun v ↦ by
  have hL := (L.toContDiffDiffeomorph n).isLocalDiffeomorph v
  rw [ContinuousLinearEquiv.coe_toContDiffDiffeomorph] at hL
  exact hL.comp (hg := d (L v))

/-- A map out of a normed space `E` which is an open embedding remains one when precomposed with
a linear isometry `R` of `E`, stated for `e ∘ R` itself. -/
theorem _root_.Topology.IsOpenEmbedding.comp_linearIsometryEquiv {X : Type*}
    [TopologicalSpace X] {e : E → X} (h : Topology.IsOpenEmbedding e) (R : E ≃ₗᵢ[𝕜] E) :
    Topology.IsOpenEmbedding (e ∘ R) :=
  R.toHomeomorph.isOpenEmbedding_comp_iff.2 h

/-- The special case of `IsLocalDiffeomorph.comp_continuousLinearEquiv` for a linear isometry `R`,
stated for `e ∘ R` itself rather than for its continuous linear equivalence. -/
theorem _root_.IsLocalDiffeomorph.comp_linearIsometryEquiv {e : E → M}
    (d : IsLocalDiffeomorph 𝓘(𝕜, E) I n e) (R : E ≃ₗᵢ[𝕜] E) :
    IsLocalDiffeomorph 𝓘(𝕜, E) I n (e ∘ R) :=
  d.comp_continuousLinearEquiv R.toContinuousLinearEquiv

end ContinuousLinearEquiv

end TauCeti
