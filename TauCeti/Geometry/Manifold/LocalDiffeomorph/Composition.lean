/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

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
characterises the `C^m` maps `A × B → N`, such as flows on a quotient manifold.

## Main results

* `ContMDiffWithinAt.of_comp_isLocalDiffeomorph`: pointwise-within cancellation.
* `ContMDiffOn.of_comp_isLocalDiffeomorph`: on-set cancellation.
* `ContMDiff.of_comp_isLocalDiffeomorph`: global cancellation.
* `IsLocalDiffeomorphAt.contMDiffAt_comp_iff`: pointwise cancellation on the source side.
* `IsLocalDiffeomorph.contMDiff_comp_iff`: global cancellation on the source side, for a
  surjective local diffeomorphism.
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

/-- If `p` is a surjective `C^n` local diffeomorphism and `m ≤ n`, a map `g` out of its target is
`C^m` exactly when `g ∘ p` is `C^m`. -/
theorem _root_.IsLocalDiffeomorph.contMDiff_comp_iff {m : ℕ∞ω} {g : B → N}
    (hp : IsLocalDiffeomorph I J n p) (hsurj : Function.Surjective p) (hm : m ≤ n) :
    ContMDiff I I' m (g ∘ p) ↔ ContMDiff J I' m g := by
  refine ⟨fun hg y ↦ ?_, fun hg ↦ hg.comp (hp.contMDiff.of_le hm)⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((hp x).contMDiffAt_comp_iff hm).1 (hg x)

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

end TauCeti
