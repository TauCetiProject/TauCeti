/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# The regular representations of a compact group on `L²(G)`

A compact group `G` acts on `L²(G)` by right translation, `(π g f) x = f (x * g)`, and by left
translation, `(π g f) x = f (g⁻¹ * x)`.  Both translations preserve normalized Haar measure, so both
actions are unitary, and both are *strongly* continuous: for each fixed `f` the orbit map
`g ↦ π g f` is continuous.  Continuity of `g ↦ π g` for the operator norm is neither proved nor
needed here; the uses of `L²(G)` that do need it obtain it only after restricting to a
finite-dimensional invariant subspace.

The two translations commute, so together they make `L²(G)` a representation of `G × G` by
**two-sided translation**, `(π (g, h) f) x = f (g⁻¹ * x * h)`.  That is the action the Peter-Weyl
decomposition of `L²(G)` is equivariant for: each of its isotypic blocks, spanned by the matrix
coefficients of a single irreducible, is a `G × G`-subrepresentation, because translating a matrix
coefficient on either side absorbs the translation into one of its two defining vectors.

## Main definitions

* `TauCeti.rightRegularLp`: the right regular representation of `G` on `L²(G)`.
* `TauCeti.leftRegularLp`: the left regular representation of `G` on `L²(G)`.
* `TauCeti.biregularLp`: the two-sided regular representation of `G × G` on `L²(G)`.

## Main statements

* `TauCeti.rightRegularLp_apply` and `TauCeti.leftRegularLp_apply`: `π g` is
  `Lp.compMeasurePreserving (· * g)`, respectively `Lp.compMeasurePreserving (g⁻¹ * ·)`, the form in
  which Mathlib and `TauCeti.RepresentationTheory.Compact.Convolution` phrase translation.
* `TauCeti.coeFn_rightRegularLp`, `TauCeti.coeFn_leftRegularLp` and `TauCeti.coeFn_biregularLp`:
  `π g f` is represented by the translate of `f`.
* `TauCeti.rightRegularLp_toLp`, `TauCeti.leftRegularLp_toLp` and `TauCeti.biregularLp_toLp`: on the
  class of a continuous function, `π g` is translation of that function.
* `TauCeti.isUnitary_rightRegularLp`, `TauCeti.isUnitary_leftRegularLp` and
  `TauCeti.isUnitary_biregularLp`: translation preserves the `L²` inner product.
* `TauCeti.continuous_rightRegularLp_apply`, `TauCeti.continuous_leftRegularLp_apply` and
  `TauCeti.continuous_biregularLp_apply`: the actions are strongly continuous.
* `TauCeti.commute_leftRegularLp_rightRegularLp`: left and right translation commute, which is what
  makes `TauCeti.biregularLp` a representation of the product group.
* `TauCeti.biregularLp_apply`: the two-sided action is right translation after left translation,
  with `TauCeti.biregularLp_inl` and `TauCeti.biregularLp_inr` recovering the two one-sided
  actions on the two factors of `G × G`.

## Implementation notes

Right translation on `Lp` is definitionally Mathlib's `DomMulAct` action of `Gᵐᵒᵖ`, that is,
`DomMulAct.mk (MulOpposite.op g) • f`, so `rightRegularLp`'s identity law is `one_smul` for that
action; its multiplicativity law is proved instead via Mathlib's `compMeasurePreserving_comp_apply`
and right-multiplication associativity, since the two composed `Lp.compMeasurePreservingₗᵢ` do not
unify with the `DomMulAct` action definitionally. Its strong continuity is Mathlib's
`Continuous.compMeasurePreservingLp`.

Left translation needs the inverse, `f ↦ f ∘ (g⁻¹ * ·)`, since precomposition reverses composition;
so neither of its two monoid-hom laws is an action law of a `DomMulAct` action on the nose, and both
are proved by rewriting the translating map with
`MeasureTheory.Lp.compMeasurePreserving_congr_fun`.

The two-sided representation is *defined* as the product of the two one-sided ones, assembled by
`MonoidHom.noncommCoprod` out of the fact that they commute, rather than as precomposition with
`x ↦ g⁻¹ * x * h`; so its unitarity, strong continuity and translation lemmas all reduce to the
corresponding facts for the two factors, and no separate two-sided measure-preserving lemma is
needed.
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### The right regular representation -/

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

/-! ### The left regular representation -/

variable (𝕜 G) in
/-- **The left regular representation** of a compact group on `L²(G)`: the element `g` acts by
`f ↦ (x ↦ f (g⁻¹ * x))`, which preserves normalized Haar measure and hence the `L²` norm.

The inverse is forced: precomposition reverses composition, so `g ↦ (f ↦ f ∘ (g * ·))` is an
antihomomorphism and it is `g ↦ (f ↦ f ∘ (g⁻¹ * ·))` that is a representation. As for
`TauCeti.rightRegularLp`, continuity of `g ↦ π g` for the operator norm is not claimed; the strong
continuity `TauCeti.continuous_leftRegularLp_apply` is. -/
noncomputable def leftRegularLp : ContRepresentation 𝕜 G (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom
    { toFun g := (Lp.compMeasurePreservingₗᵢ 𝕜 (g⁻¹ * ·)
        (measurePreserving_mul_left (haarProb G) g⁻¹)).toContinuousLinearMap
      map_one' := ContinuousLinearMap.ext fun x =>
        (Lp.compMeasurePreserving_congr_fun (g := id) _ (.id _)
            (funext fun y => by rw [inv_one, one_mul, id]) x).trans
          (Lp.compMeasurePreserving_id_apply x)
      map_mul' g h := ContinuousLinearMap.ext fun x => by
        have hfun : (fun y : G => (g * h)⁻¹ * y)
            = (fun y : G => h⁻¹ * y) ∘ (fun y : G => g⁻¹ * y) :=
          funext fun y => by rw [Function.comp_apply, mul_inv_rev, mul_assoc]
        simp only [mul_apply_eq_comp]
        refine (Lp.compMeasurePreserving_congr_fun _
          ((measurePreserving_mul_left (haarProb G) h⁻¹).comp
            (measurePreserving_mul_left (haarProb G) g⁻¹)) hfun x).trans ?_
        exact Lp.compMeasurePreserving_comp_apply x (measurePreserving_mul_left (haarProb G) h⁻¹)
          (measurePreserving_mul_left (haarProb G) g⁻¹) }

/-- **Left translation on `L²(G)`, unfolded to the underlying `Lp.compMeasurePreserving`.** The
counterpart of `TauCeti.rightRegularLp_apply`; note the inverse. -/
theorem leftRegularLp_apply (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f
      = Lp.compMeasurePreserving (g⁻¹ * ·) (measurePreserving_mul_left (haarProb G) g⁻¹) f :=
  (rfl)

/-- Left translation on `L²(G)` is represented by left translation of functions. -/
theorem coeFn_leftRegularLp (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    leftRegularLp 𝕜 G g f =ᵐ[haarProb G] fun x => f (g⁻¹ * x) := by
  rw [leftRegularLp_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- **On a continuous function, the left regular representation is left translation.** -/
@[simp]
theorem leftRegularLp_toLp (F : C(G, 𝕜)) (g : G) :
    leftRegularLp 𝕜 G g (ContinuousMap.toLp 2 (haarProb G) 𝕜 F)
      = ContinuousMap.toLp 2 (haarProb G) 𝕜 (F.comp (.mulLeft g⁻¹)) := by
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

/-- **The left regular representation is strongly continuous:** each orbit map `g ↦ π g f` is
continuous. The family of left multiplications by `g⁻¹` depends continuously on `g` because
`(g, x) ↦ g * x` curries and inversion is continuous. -/
theorem continuous_leftRegularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun g : G => leftRegularLp 𝕜 G g f := by
  have hg : Continuous fun g : G => ContinuousMap.mulLeft (X := G) g⁻¹ :=
    (ContinuousMap.curry
      ⟨fun p : G × G => p.1 * p.2, continuous_fst.mul continuous_snd⟩).continuous.comp
        continuous_inv
  simp only [leftRegularLp_apply]
  exact continuous_const.compMeasurePreservingLp hg _ (by simp)

/-! ### The two-sided regular representation -/

/-- **Left and right translation commute**: `x ↦ g⁻¹ * x` and `x ↦ x * h` commute on `G`, by
associativity, so precomposition with them commutes on `L²(G)`. This is what makes the two one-sided
regular representations combine into a representation of `G × G`. -/
theorem commute_leftRegularLp_rightRegularLp (g h : G) :
    Commute (leftRegularLp 𝕜 G g) (rightRegularLp 𝕜 G h) := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hfun : (fun y : G => y * h) ∘ (fun y : G => g⁻¹ * y)
      = (fun y : G => g⁻¹ * y) ∘ (fun y : G => y * h) :=
    funext fun y => by
      simp only [Function.comp_apply]
      rw [mul_assoc]
  simp only [mul_apply_eq_comp, leftRegularLp_apply, rightRegularLp_apply]
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_mul_right (haarProb G) h)
      (measurePreserving_mul_left (haarProb G) g⁻¹),
    ← Lp.compMeasurePreserving_comp_apply f (measurePreserving_mul_left (haarProb G) g⁻¹)
      (measurePreserving_mul_right (haarProb G) h)]
  exact Lp.compMeasurePreserving_congr_fun _ _ hfun f

variable (𝕜 G) in
/-- **The two-sided regular representation** of a compact group: `G × G` acts on `L²(G)` by
`(g, h) · f = (x ↦ f (g⁻¹ * x * h))`, the left regular representation on the first factor and the
right regular one on the second.

It is defined as the product of the two one-sided representations, which is a monoid homomorphism
exactly because they commute (`TauCeti.commute_leftRegularLp_rightRegularLp`). This is the action
under which the Peter-Weyl blocks of `L²(G)` are subrepresentations. -/
noncomputable def biregularLp : ContRepresentation 𝕜 (G × G) (Lp 𝕜 2 (haarProb G)) :=
  .ofMonoidHom ((leftRegularLp 𝕜 G).toMonoidHom.noncommCoprod (rightRegularLp 𝕜 G).toMonoidHom
    commute_leftRegularLp_rightRegularLp)

/-- **The two-sided action is right translation after left translation.** -/
theorem biregularLp_apply (a : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biregularLp 𝕜 G a f = rightRegularLp 𝕜 G a.2 (leftRegularLp 𝕜 G a.1 f) :=
  congrArg (fun T : Lp 𝕜 2 (haarProb G) →L[𝕜] Lp 𝕜 2 (haarProb G) => T f)
    (MonoidHom.noncommCoprod_apply' (leftRegularLp 𝕜 G).toMonoidHom
      (rightRegularLp 𝕜 G).toMonoidHom commute_leftRegularLp_rightRegularLp a)

/-- On the first factor of `G × G` the two-sided action is the left regular representation. -/
@[simp]
theorem biregularLp_inl (g : G) (f : Lp 𝕜 2 (haarProb G)) :
    biregularLp 𝕜 G (g, 1) f = leftRegularLp 𝕜 G g f := by
  rw [biregularLp_apply]
  simp

/-- On the second factor of `G × G` the two-sided action is the right regular representation. -/
@[simp]
theorem biregularLp_inr (h : G) (f : Lp 𝕜 2 (haarProb G)) :
    biregularLp 𝕜 G (1, h) f = rightRegularLp 𝕜 G h f := by
  rw [biregularLp_apply]
  simp

/-- **Two-sided translation on `L²(G)` is represented by two-sided translation of functions.** -/
theorem coeFn_biregularLp (a : G × G) (f : Lp 𝕜 2 (haarProb G)) :
    biregularLp 𝕜 G a f =ᵐ[haarProb G] fun x => f (a.1⁻¹ * x * a.2) := by
  have hleft := (measurePreserving_mul_right (haarProb G)
    a.2).quasiMeasurePreserving.ae_eq_comp (coeFn_leftRegularLp (𝕜 := 𝕜) a.1 f)
  have hfun : (fun x : G => f (a.1⁻¹ * x * a.2))
      = (fun y : G => f (a.1⁻¹ * y)) ∘ fun x : G => x * a.2 :=
    funext fun x => by
      simp only [Function.comp_apply]
      rw [mul_assoc]
  rw [biregularLp_apply, hfun]
  exact (coeFn_rightRegularLp a.2 _).trans hleft

/-- **On a continuous function, the two-sided action is two-sided translation.** -/
@[simp]
theorem biregularLp_toLp (F : C(G, 𝕜)) (a : G × G) :
    biregularLp 𝕜 G a (ContinuousMap.toLp 2 (haarProb G) 𝕜 F)
      = ContinuousMap.toLp 2 (haarProb G) 𝕜
        (F.comp ((ContinuousMap.mulLeft a.1⁻¹).comp (ContinuousMap.mulRight a.2))) := by
  rw [biregularLp_apply, leftRegularLp_toLp, rightRegularLp_toLp, ContinuousMap.comp_assoc]

variable (𝕜 G) in
/-- **The two-sided regular representation is unitary**, both translations preserving normalized
Haar measure. -/
theorem isUnitary_biregularLp : ContRepresentation.IsUnitary (biregularLp 𝕜 G) :=
  (ContRepresentation.isUnitary_iff_norm_map _).mpr fun a f => by
    rw [biregularLp_apply, (isUnitary_rightRegularLp 𝕜 G).norm_map,
      (isUnitary_leftRegularLp 𝕜 G).norm_map]

/-- **The two-sided regular representation is strongly continuous:** each orbit map
`(g, h) ↦ (g, h) · f` is continuous. Left translation contributes the strong continuity of
`TauCeti.leftRegularLp`, and right translation the joint continuity of
`Lp.compMeasurePreserving`. -/
theorem continuous_biregularLp_apply (f : Lp 𝕜 2 (haarProb G)) :
    Continuous fun a : G × G => biregularLp 𝕜 G a f := by
  have hf : Continuous fun a : G × G => leftRegularLp 𝕜 G a.1 f :=
    (continuous_leftRegularLp_apply f).comp continuous_fst
  have hg : Continuous fun a : G × G => ContinuousMap.mulRight (X := G) a.2 :=
    (ContinuousMap.curry
      ⟨fun p : G × G => p.2 * p.1, continuous_snd.mul continuous_fst⟩).continuous.comp
        continuous_snd
  simp only [biregularLp_apply, rightRegularLp_apply]
  exact hf.compMeasurePreservingLp hg _ (by simp)

end CompactGroup

end TauCeti
