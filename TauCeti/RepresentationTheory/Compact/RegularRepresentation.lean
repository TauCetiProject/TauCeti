/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The regular representations of a compact group on `L²(G)`

A compact group `G` acts on `L²(G)` by right translation, `(π g f) x = f (x * g)`, and by left
translation, `(π g f) x = f (g⁻¹ * x)`; the inverse in the latter is what makes it a representation
rather than an antirepresentation. Both translations preserve normalized Haar measure, so both
actions are unitary, and both are *strongly* continuous: for each fixed `f` the orbit map
`g ↦ π g f` is continuous. Continuity of `g ↦ π g` for the operator norm is neither proved nor
needed here; the uses of `L²(G)` that do need it obtain it only after restricting to a
finite-dimensional invariant subspace.

The two actions commute, and `TauCeti.RepresentationTheory.Compact.BiregularRepresentation` bundles
them into a single action of `G × G`.

## Main definitions

* `TauCeti.rightRegularLp`: the right regular representation of `G` on `L²(G)`.
* `TauCeti.leftRegularLp`: the left regular representation of `G` on `L²(G)`.

## Main statements

* `TauCeti.rightRegularLp_apply` and `TauCeti.leftRegularLp_apply`: `π g` is
  `Lp.compMeasurePreserving (· * g)`, respectively `Lp.compMeasurePreserving (g⁻¹ * ·)`, the form
  in which Mathlib and `TauCeti.RepresentationTheory.Compact.Convolution` phrase translation.
* `TauCeti.coeFn_rightRegularLp` and `TauCeti.coeFn_leftRegularLp`: `π g f` is represented by the
  function `x ↦ f (x * g)`, respectively `x ↦ f (g⁻¹ * x)`.
* `TauCeti.rightRegularLp_toLp` and `TauCeti.leftRegularLp_toLp`: on the class of a continuous
  function, `π g` is translation of that function.
* `TauCeti.isUnitary_rightRegularLp` and `TauCeti.isUnitary_leftRegularLp`: both translations
  preserve the `L²` inner product.
* `TauCeti.continuous_rightRegularLp_apply` and `TauCeti.continuous_leftRegularLp_apply`: both
  actions are strongly continuous.

## Implementation notes

Right translation on `Lp` is definitionally Mathlib's `DomMulAct` action of `Gᵐᵒᵖ`, that is,
`DomMulAct.mk (MulOpposite.op g) • f`, so `rightRegularLp`'s identity law is `one_smul` for that
action; its multiplicativity law is proved instead via Mathlib's `compMeasurePreserving_comp_apply`
and right-multiplication associativity, since the two composed `Lp.compMeasurePreservingₗᵢ` do not
unify with the `DomMulAct` action definitionally. Left translation is written with an inverse, so
no such `DomMulAct` action is available for it and its identity law goes through
`Lp.compMeasurePreserving_id_apply` after normalizing `fun x => (1 : G)⁻¹ * x` to the identity.
Strong continuity of both is Mathlib's `Continuous.compMeasurePreservingLp`.

The bodies of both representations are not exposed: `TauCeti.rightRegularLp_apply` and
`TauCeti.leftRegularLp_apply` are the interface through which a downstream file transfers a
statement phrased in raw `Lp.compMeasurePreserving` form to the representation and back.
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (𝕜 G) in
/-- **The right regular representation** of a compact group on `L²(G)`: the element `g` acts by
`f ↦ (x ↦ f (x * g))`, which preserves normalized Haar measure and hence the `L²` norm.

Mathlib's `ContRepresentation` does not require `g ↦ π g` to be continuous for the operator norm,
and no such continuity is proved here; it is an extra hypothesis, established downstream after
restricting to a convolution eigenspace. What is proved in general is the strong continuity
`TauCeti.continuous_rightRegularLp_apply`. -/
noncomputable def rightRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (· * g)
        (measurePreserving_mul_right (haarProb G) g)).toContinuousLinearMap
      -- Right translation on `Lp` *is* the `DomMulAct` action `DomMulAct.mk (op g) • ·` of `Gᵐᵒᵖ`,
      -- definitionally, so the identity law is the `MulAction` law of that action.
      map_one' := ContinuousLinearMap.ext fun x => one_smul (MulOpposite G)ᵈᵐᵃ x
      map_mul' g h := ContinuousLinearMap.ext fun x => by
        have hfun : (fun y : G => y * (g * h)) = (fun y : G => y * h) ∘ (fun y : G => y * g) :=
          funext fun y => (mul_assoc y g h).symm
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply x (measurePreserving_mul_right (haarProb G) h)
          (measurePreserving_mul_right (haarProb G) g) }

/-- **Right translation on `L²(G)`, unfolded to the underlying `Lp.compMeasurePreserving`.** The
body of `rightRegularLp` is not exposed, so this is the lemma that lets a downstream file transfer
a statement phrased in raw `Lp.compMeasurePreserving` form to the representation and back. -/
theorem rightRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    rightRegularLp 𝕜 G g f
      = Lp.compMeasurePreserving (· * g) (measurePreserving_mul_right (haarProb G) g) f :=
  (rfl)

/-- Right translation on `L²(G)` is represented by right translation of functions. -/
theorem coeFn_rightRegularLp (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    rightRegularLp 𝕜 G g f =ᵐ[haarProb G] fun x => f (x * g) := by
  rw [rightRegularLp_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- **On a continuous function, the right regular representation is right translation.** The class
of `F` is sent to the class of `x ↦ F (x * g)`, with no almost-everywhere qualification on the
representatives. -/
@[simp]
theorem rightRegularLp_toLp (F : C(G, 𝕜)) (g : G) :
    rightRegularLp 𝕜 G g (ContinuousMap.toLp 2 (haarProb G) 𝕜 F)
      = ContinuousMap.toLp 2 (haarProb G) 𝕜 (F.comp (.mulRight g)) := by
  rw [rightRegularLp_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F (.mulRight g)
    (measurePreserving_mul_right (haarProb G) g)

variable (𝕜 G) in
/-- **The right regular representation is unitary**, because right translation preserves
normalized Haar measure. -/
theorem isUnitary_rightRegularLp : ContRepresentation.IsUnitary (rightRegularLp 𝕜 G) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro g f
  rw [rightRegularLp_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The right regular representation is strongly continuous:** each orbit map `g ↦ π g f` is
continuous. This is Mathlib's continuity of `Lp.compMeasurePreserving` in both arguments, applied
to the family of right multiplications, which depends continuously on the multiplier because
`(g, x) ↦ x * g` curries. -/
theorem continuous_rightRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun g : G => rightRegularLp 𝕜 G g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulRight (X := G) g :=
    (ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, continuous_snd.mul continuous_fst⟩).continuous
  simp only [rightRegularLp_apply]
  exact continuous_const.compMeasurePreservingLp hg _ (by simp)

variable (𝕜 G) in
/-- **The left regular representation** of a compact group on `L²(G)`: the element `g` acts by
`f ↦ (x ↦ f (g⁻¹ * x))`. The inverse makes this a representation rather than an
antirepresentation.

As for `TauCeti.rightRegularLp`, only strong continuity is asserted; operator-norm continuity is
not needed and generally fails for infinite compact groups. -/
noncomputable def leftRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (g⁻¹ * ·)
        (measurePreserving_mul_left (haarProb G) g⁻¹)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun f => by
        simp only [one_apply_eq_self, LinearIsometry.coe_toContinuousLinearMap,
          Lp.compMeasurePreservingₗᵢ_apply, inv_one, one_mul, ← Function.id_def]
        exact Lp.compMeasurePreserving_id_apply f
      map_mul' g h := ContinuousLinearMap.ext fun f => by
        have hfun : (fun x : G => (g * h)⁻¹ * x) =
            (fun x : G => h⁻¹ * x) ∘ (fun x : G => g⁻¹ * x) := by
          funext x
          simp only [Function.comp_apply, mul_inv_rev, mul_assoc]
        simp only [mul_apply_eq_comp, hfun]
        exact Lp.compMeasurePreserving_comp_apply f
          (measurePreserving_mul_left (haarProb G) h⁻¹)
          (measurePreserving_mul_left (haarProb G) g⁻¹) }

/-- **Left translation on `L²(G)`, unfolded to the underlying `Lp.compMeasurePreserving`.** As for
`TauCeti.rightRegularLp_apply`, the body of `leftRegularLp` is not exposed, so this is the lemma
that moves a statement between the representation and its raw `Lp.compMeasurePreserving` form. -/
theorem leftRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =
      Lp.compMeasurePreserving (g⁻¹ * ·) (measurePreserving_mul_left (haarProb G) g⁻¹) f :=
  (rfl)

/-- Left translation on `L²(G)` is represented by left translation of functions. -/
theorem coeFn_leftRegularLp (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =ᵐ[haarProb G] fun x => f (g⁻¹ * x) := by
  rw [leftRegularLp_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- **On a continuous function, the left regular representation is left translation by the
inverse.** -/
@[simp]
theorem leftRegularLp_toLp (F : C(G, 𝕜)) (g : G) :
    leftRegularLp 𝕜 G g (ContinuousMap.toLp 2 (haarProb G) 𝕜 F) =
      ContinuousMap.toLp 2 (haarProb G) 𝕜 (F.comp (.mulLeft g⁻¹)) := by
  rw [leftRegularLp_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F (.mulLeft g⁻¹)
    (measurePreserving_mul_left (haarProb G) g⁻¹)

variable (𝕜 G) in
/-- **The left regular representation is unitary**, because left translation preserves normalized
Haar measure. -/
theorem isUnitary_leftRegularLp : ContRepresentation.IsUnitary (leftRegularLp 𝕜 G) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro g f
  rw [leftRegularLp_apply]
  exact Lp.norm_compMeasurePreserving f _

/-- **The left regular representation is strongly continuous:** every orbit map `g ↦ g · f` is
continuous. -/
theorem continuous_leftRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun g : G => leftRegularLp 𝕜 G g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulLeft (X := G) g⁻¹ :=
    (ContinuousMap.curry
      ⟨fun p : G × G => p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩).continuous
  simp only [leftRegularLp_apply]
  exact continuous_const.compMeasurePreservingLp hg _ (by simp)

end CompactGroup

end TauCeti
