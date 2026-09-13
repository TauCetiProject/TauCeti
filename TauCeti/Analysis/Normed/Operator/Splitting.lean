/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The kernel of an operator paired with a complementary coordinate

A continuous linear map `A : M →L[R] F` together with a second map `q : M →L[R] G` describes `M`
by "the value of `A`" and "the remaining coordinate `q`" exactly when the pair
`A.prod q : M →L[R] F × G` is invertible. That is the situation the implicit function theorem
creates: there `A` is the derivative of the equation and `q` is a projection onto a complement of
its kernel.

In that situation the second coordinate restricts to an isomorphism from `ker A` onto `G`. This
file constructs its inverse, `ContinuousLinearMap.kerSection`, which sends `v : G` to the unique
`x : M` with `A x = 0` and `q x = v`, and packages it as
`ContinuousLinearMap.kerEquivOfProd : G ≃L[R] ↥A.ker`. The kernel of `A` is therefore described by
a continuous linear parametrization whose parameter space does not depend on the point at which
`A` is taken, which is what lets a moving kernel — a tangent space along a level set — be compared
with a fixed model space.

Invertibility of the pair is recorded through `ContinuousLinearMap.IsInvertible`, so that the
section is a plain definition and the hypothesis appears only in the lemmas about it; the
underlying inverse is Mathlib's total `ContinuousLinearMap.inverse`.

## Main declarations

* `ContinuousLinearMap.kerSection`: the section `G →L[R] M` of `q` with values in `ker A`.
* `ContinuousLinearMap.eq_kerSection`: it is the only map with that defining property.
* `ContinuousLinearMap.range_kerSection`: its range is exactly `ker A`.
* `ContinuousLinearMap.kerEquivOfProd`: the resulting isomorphism `G ≃L[R] ↥A.ker`.
* `ContinuousLinearMap.surjective_of_surjective_prod`: a surjective pair has surjective first
  component.
-/

public section

namespace ContinuousLinearMap

variable {R M F G : Type*} [Semiring R]
  [AddCommMonoid M] [TopologicalSpace M] [Module R M]
  [AddCommMonoid F] [TopologicalSpace F] [Module R F]
  [AddCommMonoid G] [TopologicalSpace G] [Module R G]
  {A : M →L[R] F} {q : M →L[R] G}

/-- The section of `q` with values in the kernel of `A`: it sends `v : G` to the unique `x : M`
with `A x = 0` and `q x = v`.

This is meaningful when the pair `A.prod q` is invertible, which every lemma below assumes;
outside that case Mathlib's `ContinuousLinearMap.inverse` returns `0` and so does this map. -/
noncomputable def kerSection (A : M →L[R] F) (q : M →L[R] G) : G →L[R] M :=
  (A.prod q).inverse ∘L .inr R F G

/-- The defining property of the section: the pair `(A, q)` sends `A.kerSection q v` to `(0, v)`.
Not a `simp` lemma: its two components, `ContinuousLinearMap.apply_kerSection` and
`ContinuousLinearMap.apply_kerSection_right`, are, and together they prove it. -/
theorem prod_apply_kerSection (h : (A.prod q).IsInvertible) (v : G) :
    A.prod q (A.kerSection q v) = (0, v) := by
  obtain ⟨e, he⟩ := h
  simp [kerSection, ← he]

/-- The section takes values in the kernel of `A`. -/
@[simp]
theorem apply_kerSection (h : (A.prod q).IsInvertible) (v : G) : A (A.kerSection q v) = 0 :=
  congrArg Prod.fst (prod_apply_kerSection h v)

/-- The `Submodule.mem` form of `ContinuousLinearMap.apply_kerSection`. -/
theorem kerSection_mem_ker (h : (A.prod q).IsInvertible) (v : G) : A.kerSection q v ∈ A.ker :=
  apply_kerSection h v

/-- The section is a right inverse of `q`. -/
@[simp]
theorem apply_kerSection_right (h : (A.prod q).IsInvertible) (v : G) :
    q (A.kerSection q v) = v :=
  congrArg Prod.snd (prod_apply_kerSection h v)

/-- On the kernel of `A` the section undoes `q`. -/
theorem kerSection_apply_of_mem_ker (h : (A.prod q).IsInvertible) {x : M} (hx : x ∈ A.ker) :
    A.kerSection q (q x) = x := by
  obtain ⟨e, he⟩ := h
  have hx' : A.prod q x = (0, q x) := Prod.ext hx rfl
  have : (A.prod q).inverse (A.prod q x) = x := by
    simp [← he, ContinuousLinearEquiv.symm_apply_apply]
  rwa [hx'] at this

/-- **The section is characterised by its defining property.** Any continuous linear map sent to
`(0, v)` by the pair is `ContinuousLinearMap.kerSection`, so consumers never need to unfold the
definition. -/
theorem eq_kerSection (h : (A.prod q).IsInvertible) {g : G →L[R] M}
    (hg : ∀ v, A.prod q (g v) = (0, v)) : g = A.kerSection q := by
  obtain ⟨e, he⟩ := h
  have hinj : Function.Injective ⇑(A.prod q) := by rw [← he]; exact e.injective
  exact ContinuousLinearMap.ext fun v ↦
    hinj ((hg v).trans (prod_apply_kerSection ⟨e, he⟩ v).symm)

/-- The section is injective, being a right inverse of `q`. -/
theorem kerSection_injective (h : (A.prod q).IsInvertible) :
    Function.Injective (A.kerSection q) := by
  intro v w hvw
  rw [← apply_kerSection_right h v, ← apply_kerSection_right h w, hvw]

/-- **The kernel of `A` is exactly the range of the section.** -/
@[simp]
theorem range_kerSection (h : (A.prod q).IsInvertible) : (A.kerSection q).range = A.ker := by
  refine le_antisymm ?_ fun x hx ↦ ⟨q x, kerSection_apply_of_mem_ker h hx⟩
  rintro _ ⟨v, rfl⟩
  exact kerSection_mem_ker h v

/-- **An invertible pair identifies the kernel of its first component with the codomain of its
second.** The isomorphism is the restriction of `q`; its inverse is
`ContinuousLinearMap.kerSection`. -/
noncomputable def kerEquivOfProd (A : M →L[R] F) (q : M →L[R] G)
    (h : (A.prod q).IsInvertible) : G ≃L[R] ↥A.ker :=
  ContinuousLinearEquiv.equivOfInverse ((A.kerSection q).codRestrict A.ker (kerSection_mem_ker h))
    (q ∘L A.ker.subtypeL) (apply_kerSection_right h) fun x ↦
      Subtype.ext (kerSection_apply_of_mem_ker h x.2)

/-- The isomorphism `G ≃L[R] ↥A.ker` is the section, read in the ambient space. -/
@[simp]
theorem coe_kerEquivOfProd_apply (h : (A.prod q).IsInvertible) (v : G) :
    ((kerEquivOfProd A q h v : ↥A.ker) : M) = A.kerSection q v :=
  (rfl)

/-- Its inverse is the restriction of `q` to the kernel of `A`. -/
@[simp]
theorem kerEquivOfProd_symm_apply (h : (A.prod q).IsInvertible) (x : ↥A.ker) :
    (kerEquivOfProd A q h).symm x = q x :=
  (rfl)

/-- The first component of a surjective pair is surjective: it is the pair followed by the
projection `F × G →L[R] F`. -/
theorem surjective_of_surjective_prod (h : Function.Surjective (A.prod q)) :
    Function.Surjective A := by
  intro y
  obtain ⟨x, hx⟩ := h (y, 0)
  refine ⟨x, ?_⟩
  exact congrArg Prod.fst hx

end ContinuousLinearMap

end
