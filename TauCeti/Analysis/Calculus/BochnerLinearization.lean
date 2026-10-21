/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# Finite Bochner linearization

Let a finite group `G` act on a Banach space `E` fixing a point `x`, by maps that are strictly
differentiable at `x`, and let `ρ g` be the derivative at `x` of the action of `g`. Bochner's
averaging trick turns any map `c : E → E` with derivative the identity at `x` (for instance
`y ↦ y - x`) into an *equivariant* one: the average
`A y = |G|⁻¹ • ∑ g, ρ g⁻¹ (c (g • y))`
satisfies `A (h • y) = ρ h (A y)` and still has derivative the identity at `x`. By the inverse
function theorem, `A` restricts to a homeomorphism from a `G`-invariant open neighbourhood of `x`
onto a `ρ`-invariant open set which conjugates the action of `G` to the linear action `ρ`.

No faithfulness is assumed: every element of `G` is kept, including elements that act trivially
near `x`. The chart shows that the derivative representation detects exactly these elements: an
element acts as the identity near `x` if and only if its derivative at `x` is the identity. This
is the linear model of a finite-isotropy orbifold chart, in which the full, possibly ineffective,
isotropy group of a point acts linearly on a neighbourhood of it.

The averaging itself is algebraic and is stated for an arbitrary action of `G` on a type `X` and
an arbitrary continuous linear representation on the target, as `TauCeti.bochnerAverage`.
Averaging divides by the group order, which must be invertible in the scalars.

## Main definitions and results

* `TauCeti.fderivSMulHom`: at a fixed point, the derivatives of the action form a monoid
  homomorphism to continuous linear endomorphisms; for strictly differentiable actions they are
  strict derivatives (`TauCeti.hasStrictFDerivAt_fderivSMulHom`).
* `TauCeti.bochnerAverage`: the Bochner average of a map, with its equivariance
  `TauCeti.bochnerAverage_smul`; equivariant maps are their own average
  (`TauCeti.bochnerAverage_eq_self`).
* `TauCeti.hasStrictFDerivAt_bochnerAverage_id`: averaging a map with derivative the identity at a
  fixed point gives a map with derivative the identity there.
* `TauCeti.bochnerChart`: the resulting equivariant chart, with invariant source
  (`TauCeti.smul_mem_bochnerChart_source_iff`) and target
  (`TauCeti.map_mem_bochnerChart_target_iff`), conjugating the action to `ρ`
  (`TauCeti.bochnerChart_smul`, `TauCeti.bochnerChart_symm_map`), with a `C^n` inverse when the
  average is `C^n` (`TauCeti.contDiffOn_bochnerChart_symm`).
* `TauCeti.forall_mem_bochnerChart_source_smul_eq_iff` and
  `TauCeti.map_eq_one_iff_eventually_smul_eq`: the derivative at `x` of an element is the identity
  exactly when the element acts trivially near `x`.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. 46 (1945),
  372–381.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge, 2007, Chapter 1.
-/

public section

noncomputable section

open MulAction Filter
open scoped Topology

namespace TauCeti

section Derivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [Monoid M] [MulAction M E] {x : E}

/-- The derivatives at a fixed point `x` of the maps `y ↦ g • y` of an action, as a monoid
homomorphism to continuous linear endomorphisms. This is the linear isotropy representation at
`x`; by the chain rule it is multiplicative because `x` is fixed. -/
def fderivSMulHom (hx : x ∈ fixedPoints M E)
    (hd : ∀ g : M, DifferentiableAt 𝕜 (fun y : E ↦ g • y) x) : M →* (E →L[𝕜] E) where
  toFun g := fderiv 𝕜 (fun y : E ↦ g • y) x
  map_one' := by simp only [one_smul]; exact fderiv_fun_id (𝕜 := 𝕜) (x := x)
  map_mul' g h := by
    have hcomp : (fun y : E ↦ (g * h) • y) = (fun y ↦ g • y) ∘ fun y ↦ h • y :=
      funext fun y ↦ mul_smul g h y
    have hg : DifferentiableAt 𝕜 (fun y : E ↦ g • y) (h • x) := by rw [hx h]; exact hd g
    rw [hcomp, fderiv_comp x hg (hd h), hx h, ContinuousLinearMap.mul_def]

/-- The value of `TauCeti.fderivSMulHom` at `g` is the derivative at `x` of `y ↦ g • y`. -/
theorem fderivSMulHom_apply (hx : x ∈ fixedPoints M E)
    (hd : ∀ g : M, DifferentiableAt 𝕜 (fun y : E ↦ g • y) x) (g : M) :
    fderivSMulHom hx hd g = fderiv 𝕜 (fun y : E ↦ g • y) x :=
  (rfl)

/-- If every `y ↦ g • y` is strictly differentiable at the fixed point `x`, its strict derivative
there is given by `TauCeti.fderivSMulHom`. -/
theorem hasStrictFDerivAt_fderivSMulHom (hx : x ∈ fixedPoints M E) {L : M → E →L[𝕜] E}
    (hL : ∀ g : M, HasStrictFDerivAt (fun y : E ↦ g • y) (L g) x) (g : M) :
    HasStrictFDerivAt (fun y : E ↦ g • y)
      (fderivSMulHom hx (fun g ↦ (hL g).differentiableAt) g) x := by
  rw [fderivSMulHom_apply, (hL g).hasFDerivAt.fderiv]
  exact hL g

end Derivative

section Average

variable {𝕜 : Type*} [Semiring 𝕜]
  {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  {G : Type*} [Group G] [Fintype G] [Invertible (Fintype.card G : 𝕜)]
  {X : Type*} [MulAction G X]

/-- The **Bochner average** of a map `c : X → F` with respect to an action of a finite group `G`
on `X` and a continuous linear representation `ρ` of `G` on `F`: the map
`y ↦ |G|⁻¹ • ∑ g, ρ g⁻¹ (c (g • y))`. It is equivariant (`TauCeti.bochnerAverage_smul`), and an
equivariant map is its own average (`TauCeti.bochnerAverage_eq_self`). -/
def bochnerAverage (ρ : G →* (F →L[𝕜] F)) (c : X → F) (y : X) : F :=
  ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • y))

variable (ρ : G →* (F →L[𝕜] F)) (c : X → F)

/-- The defining formula of the Bochner average. -/
theorem bochnerAverage_apply (y : X) :
    bochnerAverage ρ c y = ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • y)) :=
  (rfl)

/-- The Bochner average is equivariant: it intertwines the action on `X` with `ρ`. -/
@[simp]
theorem bochnerAverage_smul (h : G) (y : X) :
    bochnerAverage ρ c (h • y) = ρ h (bochnerAverage ρ c y) := by
  rw [bochnerAverage_apply, bochnerAverage_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g ↦ ?_
  rw [Equiv.coe_mulRight, ← mul_apply_eq_comp, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left, mul_smul]

/-- A map which is already equivariant is its own Bochner average. -/
theorem bochnerAverage_eq_self (hc : ∀ (g : G) (y : X), c (g • y) = ρ g (c y)) :
    bochnerAverage ρ c = c := by
  funext y
  simp only [bochnerAverage_apply, hc, ← mul_apply_eq_comp, ← map_mul,
    inv_mul_cancel, map_one, one_apply_eq_self, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, invOf_mul_self, one_smul]

/-- At a fixed point where `c` vanishes, the Bochner average vanishes. -/
theorem bochnerAverage_apply_eq_zero {x : X} (hx : x ∈ fixedPoints G X) (hc : c x = 0) :
    bochnerAverage ρ c x = 0 := by
  simp [bochnerAverage_apply, hx _, hc]

end Average

section Calculus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [Group G] [Fintype G] [Invertible (Fintype.card G : 𝕜)] [MulAction G E]
  {ρ : G →* (F →L[𝕜] F)} {c : E → F} {x : E}

/-- The derivative of a Bochner average at a fixed point `x`: if every `y ↦ g • y` has strict
derivative `L g` at `x` and `c` has strict derivative `c'` at `x`, then the average has strict
derivative the average `|G|⁻¹ • ∑ g, ρ g⁻¹ ∘ c' ∘ L g` of the transformed
derivatives of `c'`. -/
theorem hasStrictFDerivAt_bochnerAverage {L : G → E →L[𝕜] E} {c' : E →L[𝕜] F}
    (hx : x ∈ fixedPoints G E) (hL : ∀ g : G, HasStrictFDerivAt (fun y : E ↦ g • y) (L g) x)
    (hc : HasStrictFDerivAt c c' x) :
    HasStrictFDerivAt (bochnerAverage ρ c)
      (⅟(Fintype.card G : 𝕜) • ∑ g : G, (ρ g⁻¹).comp (c'.comp (L g))) x := by
  have hfun : bochnerAverage ρ c =
      fun y ↦ ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • y)) :=
    funext (bochnerAverage_apply ρ c)
  rw [hfun]
  refine (HasStrictFDerivAt.fun_sum fun g _ ↦ ?_).const_smul _
  have hcg : HasStrictFDerivAt c c' (g • x) := by rw [hx g]; exact hc
  exact (ρ g⁻¹).hasStrictFDerivAt.comp x (hcg.comp x (hL g))

/-- **Bochner's averaging trick.** Let `ρ g` be the strict derivative at a fixed point `x` of
`y ↦ g • y`. If `c` has strict derivative the identity at `x`, then so does its Bochner average
with respect to `ρ`. -/
theorem hasStrictFDerivAt_bochnerAverage_id {ρ : G →* (E →L[𝕜] E)} {c : E → E}
    (hx : x ∈ fixedPoints G E) (hρ : ∀ g : G, HasStrictFDerivAt (fun y : E ↦ g • y) (ρ g) x)
    (hc : HasStrictFDerivAt c (ContinuousLinearMap.id 𝕜 E) x) :
    HasStrictFDerivAt (bochnerAverage ρ c) (ContinuousLinearMap.id 𝕜 E) x := by
  convert hasStrictFDerivAt_bochnerAverage hx hρ hc using 1
  simp only [ContinuousLinearMap.id_comp]
  simp only [← ContinuousLinearMap.mul_def, ← map_mul, inv_mul_cancel, map_one, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, invOf_mul_self, one_smul,
    ContinuousLinearMap.one_def]

/-- A Bochner average of a `C^n` map along a `C^n` action is `C^n`. -/
theorem contDiffAt_bochnerAverage {n : WithTop ℕ∞} {y : E}
    (hact : ∀ g : G, ContDiffAt 𝕜 n (fun z : E ↦ g • z) y)
    (hc : ∀ g : G, ContDiffAt 𝕜 n c (g • y)) :
    ContDiffAt 𝕜 n (bochnerAverage ρ c) y := by
  have hfun : bochnerAverage ρ c =
      fun z ↦ ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g⁻¹ (c (g • z)) :=
    funext (bochnerAverage_apply ρ c)
  rw [hfun]
  exact (ContDiffAt.sum fun g _ ↦
    (ρ g⁻¹).contDiff.contDiffAt.comp y ((hc g).comp y (hact g))).const_smul _

end Calculus

section Chart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {G : Type*} [Group G] [Fintype G] [Invertible (Fintype.card G : 𝕜)]
  [MulAction G E] [ContinuousConstSMul G E]
  {ρ : G →* (E →L[𝕜] E)} {c : E → E} {x : E}

/-- The **Bochner chart** at a fixed point `x` of a finite group action. Here `ρ g` is the strict
derivative at `x` of `y ↦ g • y` and `c` has strict derivative the identity at `x`. The chart is
the Bochner average of `c` (`TauCeti.coe_bochnerChart`), restricted from the inverse function
theorem's homeomorphism to the largest `G`-invariant subset of its source. Its source contains `x`
(`TauCeti.mem_bochnerChart_source`), its source and target are invariant, and it conjugates the
action to the linear action `ρ` (`TauCeti.bochnerChart_smul`, `TauCeti.bochnerChart_symm_map`). -/
def bochnerChart (hx : x ∈ fixedPoints G E)
    (hρ : ∀ g : G, HasStrictFDerivAt (fun y : E ↦ g • y) (ρ g) x)
    (hc : HasStrictFDerivAt c (ContinuousLinearMap.id 𝕜 E) x) : OpenPartialHomeomorph E E :=
  let e := (hasStrictFDerivAt_bochnerAverage_id hx hρ hc).toOpenPartialHomeomorph
    (f' := .refl 𝕜 E) _
  e.restrOpen (⋂ g : G, (fun y : E ↦ g • y) ⁻¹' e.source)
    (isOpen_iInter_of_finite fun g ↦ e.open_source.preimage (continuous_const_smul g))

variable (hx : x ∈ fixedPoints G E) (hρ : ∀ g : G, HasStrictFDerivAt (fun y : E ↦ g • y) (ρ g) x)
  (hc : HasStrictFDerivAt c (ContinuousLinearMap.id 𝕜 E) x)

/-- As a map, the Bochner chart is the Bochner average. -/
@[simp]
theorem coe_bochnerChart : ⇑(bochnerChart hx hρ hc) = bochnerAverage ρ c :=
  (rfl)

private theorem coe_bochnerChart_symm :
    ⇑(bochnerChart hx hρ hc).symm =
      ((hasStrictFDerivAt_bochnerAverage_id hx hρ hc).toOpenPartialHomeomorph
        (f' := .refl 𝕜 E) _).symm := by
  simp [bochnerChart]

private theorem mem_bochnerChart_source_iff {y : E} :
    y ∈ (bochnerChart hx hρ hc).source ↔
      ∀ g : G, g • y ∈ ((hasStrictFDerivAt_bochnerAverage_id hx hρ hc).toOpenPartialHomeomorph
        (f' := .refl 𝕜 E) _).source := by
  simp only [bochnerChart, OpenPartialHomeomorph.restrOpen_source, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_preimage, and_iff_right_iff_imp]
  intro h
  simpa using h 1

/-- The fixed point `x` lies in the source of its Bochner chart. -/
theorem mem_bochnerChart_source : x ∈ (bochnerChart hx hρ hc).source := by
  rw [mem_bochnerChart_source_iff]
  intro g
  rw [hx g]
  exact HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

/-- The source of the Bochner chart is `G`-invariant. -/
@[simp]
theorem smul_mem_bochnerChart_source_iff (g : G) {y : E} :
    g • y ∈ (bochnerChart hx hρ hc).source ↔ y ∈ (bochnerChart hx hρ hc).source := by
  simp only [mem_bochnerChart_source_iff, smul_smul]
  refine ⟨fun h k ↦ ?_, fun h k ↦ h (k * g)⟩
  simpa using h (k * g⁻¹)

/-- The Bochner chart conjugates the action of `G` to the linear action `ρ`. -/
theorem bochnerChart_smul (g : G) (y : E) :
    bochnerChart hx hρ hc (g • y) = ρ g (bochnerChart hx hρ hc y) := by
  simp

/-- The target of the Bochner chart is invariant under the linear action `ρ`. -/
@[simp]
theorem map_mem_bochnerChart_target_iff (g : G) {z : E} :
    ρ g z ∈ (bochnerChart hx hρ hc).target ↔ z ∈ (bochnerChart hx hρ hc).target := by
  set e := bochnerChart hx hρ hc
  have key : ∀ (k : G) {w : E}, w ∈ e.target → ρ k w ∈ e.target := by
    intro k w hw
    rw [← e.right_inv hw, ← bochnerChart_smul hx hρ hc]
    exact e.map_source ((smul_mem_bochnerChart_source_iff hx hρ hc k).2 (e.map_target hw))
  refine ⟨fun h ↦ ?_, key g⟩
  have h' := key g⁻¹ h
  rwa [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] at h'

/-- The inverse of the Bochner chart conjugates the linear action `ρ` back to the action of `G`. -/
theorem bochnerChart_symm_map (g : G) {z : E} (hz : z ∈ (bochnerChart hx hρ hc).target) :
    (bochnerChart hx hρ hc).symm (ρ g z) = g • (bochnerChart hx hρ hc).symm z := by
  set e := bochnerChart hx hρ hc
  have hy : e.symm z ∈ e.source := e.map_target hz
  rw [← e.right_inv hz, ← bochnerChart_smul hx hρ hc, e.left_inv hy,
    e.left_inv ((smul_mem_bochnerChart_source_iff hx hρ hc g).2 hy)]

/-- If the Bochner average is `C^n` on the source of the Bochner chart, the inverse of the chart is
`C^n` on its target. -/
theorem contDiffOn_bochnerChart_symm {n : WithTop ℕ∞}
    (hcont : ContDiffOn 𝕜 n (bochnerAverage ρ c) (bochnerChart hx hρ hc).source) :
    ContDiffOn 𝕜 n (bochnerChart hx hρ hc).symm (bochnerChart hx hρ hc).target := by
  set e := bochnerChart hx hρ hc
  intro z hz
  have hy : e.symm z ∈ e.source := e.map_target hz
  -- the target of `e` lies in the target of the inverse function theorem's homeomorphism
  have hz₀ : z ∈ ((hasStrictFDerivAt_bochnerAverage_id hx hρ hc).toOpenPartialHomeomorph
      (f' := .refl 𝕜 E) _).target := by
    simp only [e, bochnerChart] at hz
    exact hz.1
  rw [coe_bochnerChart_symm hx hρ hc]
  refine (HasStrictFDerivAt.contDiffAt_toOpenPartialHomeomorph_symm _ hz₀ ?_).contDiffWithinAt
  rw [← coe_bochnerChart_symm hx hρ hc]
  exact hcont.contDiffAt (e.open_source.mem_nhds hy)

/-- **The derivative representation detects the ineffective kernel.** An element of `G` fixes
every point of the source of the Bochner chart exactly when its derivative at `x` is the
identity. -/
theorem forall_mem_bochnerChart_source_smul_eq_iff (g : G) :
    (∀ y ∈ (bochnerChart hx hρ hc).source, g • y = y) ↔ ρ g = 1 := by
  set e := bochnerChart hx hρ hc
  refine ⟨fun h ↦ ?_, fun h y hy ↦ ?_⟩
  · -- `y ↦ g • y` agrees with the identity on a neighbourhood of `x`
    have hev : (fun y : E ↦ g • y) =ᶠ[𝓝 x] id :=
      Filter.mem_of_superset (e.open_source.mem_nhds (mem_bochnerChart_source hx hρ hc)) h
    rw [ContinuousLinearMap.one_def]
    exact (hρ g).hasFDerivAt.unique ((hasFDerivAt_id x).congr_of_eventuallyEq hev)
  refine e.injOn ((smul_mem_bochnerChart_source_iff hx hρ hc g).2 hy) hy ?_
  rw [bochnerChart_smul, h, one_apply_eq_self]

/-- At a fixed point of a finite group action by maps that are strictly differentiable there, an
element acts as the identity near the point exactly when its derivative at the point is the
identity. -/
theorem map_eq_one_iff_eventually_smul_eq (hx : x ∈ fixedPoints G E)
    (hρ : ∀ g : G, HasStrictFDerivAt (fun y : E ↦ g • y) (ρ g) x) (g : G) :
    ρ g = 1 ↔ ∀ᶠ y in 𝓝 x, g • y = y := by
  have hc : HasStrictFDerivAt (fun y : E ↦ y - x) (ContinuousLinearMap.id 𝕜 E) x :=
    (hasStrictFDerivAt_id x).sub_const x
  rw [← forall_mem_bochnerChart_source_smul_eq_iff hx hρ hc]
  refine ⟨fun h ↦ Filter.mem_of_superset
    ((bochnerChart hx hρ hc).open_source.mem_nhds (mem_bochnerChart_source hx hρ hc)) h, ?_⟩
  rw [forall_mem_bochnerChart_source_smul_eq_iff hx hρ hc, ContinuousLinearMap.one_def]
  exact fun h ↦ (hρ g).hasFDerivAt.unique
    ((hasFDerivAt_id x).congr_of_eventuallyEq h)

end Chart

end TauCeti
