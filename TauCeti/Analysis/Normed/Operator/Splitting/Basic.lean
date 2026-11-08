/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.LinearAlgebra.Dimension.Submodule

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

The pair `A.prod q` is invertible exactly when `q.prod A` is
(`ContinuousLinearMap.isInvertible_prod_comm`). Read with the roles exchanged, `q.kerSection A` is
therefore the right inverse of `A` taking values in the kernel of `q`.

For a subspace `V` of the target, `q.kerSection (T.coprod V.subtypeL)` is in particular the right
inverse of the stabilized operator `T + inclusion_V` normalized by `q = 0`. Its `V`-component is
the projection onto `V` along the range of `T` as soon as the two are complementary, which a
dimension count detects (`ContinuousLinearMap.isTopCompl_of_isInvertible_prod_coprod`). Where the
dimension of the cokernel jumps, `V` still makes the stabilized operator surjective but is no
longer complementary to the range.

Invertibility of the pair is recorded through `ContinuousLinearMap.IsInvertible`, so that the
section is a plain definition and the hypothesis appears only in the lemmas about it; the
underlying inverse is Mathlib's total `ContinuousLinearMap.inverse`.

## Main declarations

* `ContinuousLinearMap.kerSection`: the section `G →L[R] M` of `q` with values in `ker A`.
* `ContinuousLinearMap.eq_kerSection`: it is the only map with that defining property.
* `ContinuousLinearMap.range_kerSection`: its range is exactly `ker A`.
* `ContinuousLinearMap.kerEquivOfProd`: the resulting isomorphism `G ≃L[R] ↥A.ker`.
* `ContinuousLinearMap.isInvertible_prod_comm`: invertibility of a pair does not depend on the order
  of its components.
* `ContinuousLinearMap.isTopCompl_of_isInvertible_prod_coprod`: a stabilizer whose dimension is
  at most the codimension of the range is a topological complement of the range.
* `ContinuousLinearMap.projectionOntoL_eq_snd_comp_kerSection_coprod`: the projection onto such a
  stabilizer along the range, as a component of the normalized right inverse.
* `ContinuousLinearMap.prod_comp_injective`: projections fixing the range and the kernel of an
  operator `T` give an injective pair `(p ∘ T, q)`.
-/

public section

namespace ContinuousLinearMap

variable {R M F G : Type*} [Semiring R]
  [AddCommMonoid M] [TopologicalSpace M] [Module R M]
  [AddCommMonoid F] [TopologicalSpace F] [Module R F]
  [AddCommMonoid G] [TopologicalSpace G] [Module R G]
  {A : M →L[R] F} {q : M →L[R] G}

/-- Invertibility of a pair does not depend on the order of its two components. -/
theorem isInvertible_prod_comm : (A.prod q).IsInvertible ↔ (q.prod A).IsInvertible := by
  have : q.prod A = (ContinuousLinearEquiv.prodComm R F G : F × G →L[R] G × F) ∘L A.prod q := by
    ext <;> simp
  rw [this, isInvertible_equiv_comp]

/-- The section of `q` with values in the kernel of `A`: it sends `v : G` to the unique `x : M`
with `A x = 0` and `q x = v`.

This is meaningful when the pair `A.prod q` is invertible, which every lemma below assumes;
outside that case Mathlib's `ContinuousLinearMap.inverse` returns `0` and so does this map. -/
noncomputable def kerSection (A : M →L[R] F) (q : M →L[R] G) : G →L[R] M :=
  (A.prod q).inverse ∘L .inr R F G

/-- The kernel section is the inverse of the paired coordinate map on the zero slice. -/
theorem kerSection_def (A : M →L[R] F) (q : M →L[R] G) :
    A.kerSection q = (A.prod q).inverse ∘L .inr R F G :=
  (rfl)

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
@[simp]
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

section Projections

variable {R M F : Type*} [Ring R]
  [AddCommGroup M] [TopologicalSpace M] [Module R M]
  [AddCommGroup F] [TopologicalSpace F] [Module R F]

/-- If `p` fixes the range of `T` and `q` fixes its kernel, then the pair `(p ∘ T, q)` is
injective. With `p` and `q` continuous projections onto the range and the kernel, this pair is
the standard choice of local product coordinates near `T`. -/
theorem prod_comp_injective {T : M →L[R] F} {p : F →L[R] T.range} {q : M →L[R] T.ker}
    (hp : ∀ y : T.range, p y = y) (hq : ∀ v : T.ker, q v = v) :
    Function.Injective ((p ∘L T).prod q) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  simp only [prod_apply, comp_apply, Prod.mk_eq_zero] at hv
  have hT : T v = 0 := by
    have h := hv.1
    rwa [hp ⟨T v, LinearMap.mem_range_self _ v⟩, Submodule.mk_eq_zero] at h
  have h := hv.2
  rw [hq ⟨v, hT⟩] at h
  simpa using congrArg Subtype.val h

end Projections


section CokernelProjection

/-! ### The cokernel projection of a stabilized operator

Let `V` be a subspace of the target with `T.coprod V.subtypeL` surjective, and let `q` be a
coordinate on `M × V` whose pairing with that operator is invertible. Then
`q.kerSection (T.coprod V.subtypeL)` is the right inverse of the stabilized operator normalized by
`q = 0`. Its `V`-component projects onto `V` along the range of `T` as soon as the two subspaces
are complementary, which a dimension count detects. -/

variable {R M F G : Type*} [Ring R]
  [AddCommGroup M] [TopologicalSpace M] [Module R M]
  [AddCommGroup F] [TopologicalSpace F] [Module R F] [ContinuousAdd F]
  [AddCommGroup G] [TopologicalSpace G] [Module R G]
  {T : M →L[R] F} {V : Submodule R F} {q : (M × V) →L[R] G}

/-- The right inverse of a stabilized operator, normalized by `q`, splits each target vector into
a value of `T` and a vector of the stabilizer. -/
@[simp]
theorem apply_fst_kerSection_coprod_add_snd (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible)
    (y : F) :
    T (q.kerSection (T.coprod V.subtypeL) y).1 + (q.kerSection (T.coprod V.subtypeL) y).2 = y := by
  simpa using apply_kerSection_right (isInvertible_prod_comm.mp hinv) y

/-- When the stabilizer `V` is a complement of the range of `T`, the `V`-component of the right
inverse normalized by `q` is the projection onto `V` along the range. -/
@[simp]
theorem snd_kerSection_coprod_apply (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible)
    (hV : IsCompl V T.range) (y : F) :
    (q.kerSection (T.coprod V.subtypeL) y).2 = V.projectionOnto T.range hV y := by
  have hmem : T (q.kerSection (T.coprod V.subtypeL) y).1 ∈ T.range := ⟨_, rfl⟩
  conv_rhs => rw [← apply_fst_kerSection_coprod_add_snd hinv y]
  rw [map_add, Submodule.projectionOnto_apply_of_mem_right hV hmem,
    Submodule.projectionOnto_apply_left, zero_add]

/-- The continuous projection onto an exact stabilizer `V` along the range of `T` is the
`V`-component of the right inverse of `T + inclusion_V` normalized by `q`. Through this formula
the projection inherits the regularity of an operator family; see
`ContinuousLinearMap.continuousAt_snd_comp_kerSection_coprod` and
`ContinuousLinearMap.contDiffAt_snd_comp_kerSection_coprod`. -/
theorem projectionOntoL_eq_snd_comp_kerSection_coprod
    (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible) (hV : V.IsTopCompl T.range) :
    V.projectionOntoL T.range hV = snd R M V ∘L q.kerSection (T.coprod V.subtypeL) := by
  ext y
  simp [snd_kerSection_coprod_apply hinv hV.isCompl]

end CokernelProjection

section CokernelComplement

variable {K M F G : Type*} [DivisionRing K]
  [AddCommGroup M] [TopologicalSpace M] [Module K M]
  [AddCommGroup F] [TopologicalSpace F] [Module K F] [ContinuousAdd F]
  [AddCommGroup G] [TopologicalSpace G] [Module K G]
  {T : M →L[K] F} {V : Submodule K F} {q : (M × V) →L[K] G}

/-- **A stabilizer of the right dimension is an exact cokernel complement.** If the stabilized
operator `T + inclusion_V` paired with `q` is invertible and `V` has dimension at most the
codimension of the range of `T`, then `V` is a topological complement of the range. The
stabilized operator is surjective, so this dimension bound holds exactly when the cokernel of `T`
has the dimension of `V`. -/
theorem isTopCompl_of_isInvertible_prod_coprod [FiniteDimensional K V]
    (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible)
    (hrank : Module.finrank K V ≤ Module.finrank K (F ⧸ T.range)) : V.IsTopCompl T.range := by
  have hcodisj : Codisjoint T.range V := by
    refine codisjoint_iff.mpr (eq_top_iff.mpr fun y _ ↦ ?_)
    rw [← apply_fst_kerSection_coprod_add_snd hinv y]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (Submodule.coe_mem _)
  have hV : IsCompl V T.range :=
    (Submodule.isCompl_of_codisjoint_of_finrank_le hcodisj hrank).symm
  refine (Submodule.IsCompl.isTopCompl_iff_projectionOnto hV).mpr <|
    (snd K M V ∘L q.kerSection (T.coprod V.subtypeL)).continuous.congr fun y ↦ ?_
  simp [snd_kerSection_coprod_apply hinv hV]

end CokernelComplement

end ContinuousLinearMap

end
