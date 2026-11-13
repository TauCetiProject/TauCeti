/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosureOrder

/-!
# The closure order on orbits of vectors

Let `G = Spec H` be an affine group over a field `k` acting on a representation `M`. Two vectors
of `M` are *rationally conjugate* when a rational point of `G` carries one to the other. The
quotient `TauCeti.Comodule.VectorOrbit k H M` is the set of rational orbits of `G` in `M`.

When `k` is algebraically closed, `G` is of finite type and `M` is finite-dimensional, the orbit
of `v` has a geometric image `Oᵥ`: the full topological image of the projective orbit morphism of
the line through `(v, 1)` in the projective completion `P(M × k)` of `M`. Distinct orbits have
distinct images, and even distinct closures. The *closure order* on orbits,

  `O ≤ O'` if and only if `O ⊆ closure O'`,

is therefore a partial order. An orbit lies strictly below another exactly when its vectors lie
in the boundary `closure O' \ O'`, and then it has strictly smaller dimension.

Applied to the adjoint representation of `G` on its Lie algebra, this is the closure order on
adjoint orbits, in particular on nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.rationalConjugacy`: conjugacy under the rational points of `G`.
* `TauCeti.Comodule.VectorOrbit`: the rational orbits of `G` in `M`.
* `TauCeti.Comodule.VectorOrbit.image`: the geometric image of an orbit in `P(M × k)`.
* `TauCeti.Comodule.VectorOrbit.instPartialOrder`: the closure order.
* `TauCeti.Comodule.VectorOrbit.mk_le_mk_iff`, `TauCeti.Comodule.VectorOrbit.mk_lt_mk_iff`:
  the orbit of `w` lies below the orbit of `v` when `w` lies in the closure of the orbit of
  `v`, and strictly below when `w` lies in its boundary.
* `TauCeti.Comodule.VectorOrbit.strictMono_topologicalKrullDim_image`: strictly smaller orbits
  have strictly smaller dimension.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u v w

attribute [local instance] prodTrivial

section Conjugacy

variable (k : Type u) (H : Type v) (M : Type w) [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]

/-- Conjugacy under the rational points of `G = Spec H`: the vectors `v` and `w` are conjugate
when some rational point of `G` carries `v` to `w`. -/
def rationalConjugacy : Setoid M where
  r v w := ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = w
  iseqv :=
    { refl v := ⟨1, by simp⟩
      symm := by
        rintro v _ ⟨g, rfl⟩
        exact ⟨g⁻¹, Representation.inv_self_apply _ g v⟩
      trans := by
        rintro v _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
        exact ⟨g' * g, by simp⟩ }

variable {k H M} in
/-- Unfolding lemma for `TauCeti.Comodule.rationalConjugacy`. -/
theorem rationalConjugacy_iff {v w : M} :
    rationalConjugacy k H M v w ↔ ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = w :=
  Iff.rfl

/-- The rational orbits of `G = Spec H` in `M`: the vectors of `M` up to conjugacy by rational
points of `G`. -/
def VectorOrbit : Type w :=
  Quotient (rationalConjugacy k H M)

namespace VectorOrbit

variable {k H M}

/-- The rational orbit of a vector. -/
def mk (v : M) : VectorOrbit k H M :=
  Quotient.mk _ v

/-- Every rational orbit is the orbit of a vector. -/
theorem mk_surjective : Function.Surjective (mk : M → VectorOrbit k H M) :=
  Quotient.mk_surjective

/-- Induction on rational orbits: it suffices to treat the orbit of each vector. -/
@[elab_as_elim]
theorem ind {p : VectorOrbit k H M → Prop} (h : ∀ v, p (mk v)) (O : VectorOrbit k H M) : p O :=
  Quotient.ind h O

/-- Two vectors have the same rational orbit exactly when a rational point carries one to the
other. -/
theorem mk_eq_mk_iff {v w : M} :
    (mk v : VectorOrbit k H M) = mk w ↔
      ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = w :=
  Quotient.eq

/-- A vector and its translate by a rational point have the same orbit. -/
@[simp]
theorem mk_basePointsRepresentation (g : WithConv (H →ₐ[k] k)) (v : M) :
    (mk (basePointsRepresentation M g v) : VectorOrbit k H M) = mk v :=
  (mk_eq_mk_iff.mpr ⟨g, rfl⟩).symm

/-- Descend a function on vectors that is invariant under the rational points of `G` to a
function on rational orbits. -/
def lift {α : Sort*} (f : M → α)
    (hf : ∀ (g : WithConv (H →ₐ[k] k)) (v : M), f (basePointsRepresentation M g v) = f v) :
    VectorOrbit k H M → α :=
  Quotient.lift f (by
    rintro v _ ⟨g, rfl⟩
    exact (hf g v).symm)

/-- The value of a lifted function on the orbit of `v` is its value on `v`. -/
@[simp]
theorem lift_mk {α : Sort*} (f : M → α)
    (hf : ∀ (g : WithConv (H →ₐ[k] k)) (v : M), f (basePointsRepresentation M g v) = f v)
    (v : M) : lift f hf (mk v : VectorOrbit k H M) = f v :=
  (rfl)

end VectorOrbit

end Conjugacy

namespace VectorOrbit

section Image

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The geometric image of a rational orbit in the projective completion `P(M × k)` of `M`: the
full topological image, including nonclosed points, of the projective orbit morphism of the line
through `(v, 1)`, for any vector `v` of the orbit. -/
noncomputable def image (O : VectorOrbit k H M) :
    Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))) :=
  lift (fun v ↦ Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v)))
    range_projectiveOrbitMap_mk_one_basePointsRepresentation O

/-- The image of the orbit of `v` is the image of the projective orbit morphism of `(v, 1)`. -/
@[simp]
theorem image_mk (v : M) :
    (mk v : VectorOrbit k H M).image =
      Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k) (Module.isUnimodular_mk_one v)) :=
  (rfl)

end Image

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Orbits are determined by their images.** Two vectors have the same geometric orbit image
in `P(M × k)` exactly when they are rationally conjugate. -/
theorem image_injective : Function.Injective (image : VectorOrbit k H M → Set _) := by
  intro O O' h
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  rw [image_mk, image_mk, eq_comm, range_projectiveOrbitMap_eq_iff] at h
  obtain ⟨g, hg⟩ := exists_span_basePointsRepresentation_eq_of_mem_range _ _ _ _ h
  exact mk_eq_mk_iff.mpr ⟨g, basePointsRepresentation_eq_of_span_eq hg⟩

/-- **Orbits are determined by their closures.** Two rational orbits whose geometric images
have the same closure in `P(M × k)` are equal. -/
theorem closure_image_injective :
    Function.Injective fun O : VectorOrbit k H M ↦ closure O.image := by
  intro O O' h
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  simp only [image_mk] at h
  refine image_injective ?_
  rw [image_mk, image_mk]
  refine (range_projectiveOrbitMap_eq_of_mem_closure_of_mem_closure _ _ ?_ ?_).symm
  · exact h ▸ subset_closure (Set.mem_range_self _)
  · exact h.symm ▸ subset_closure (Set.mem_range_self _)

/-- The **closure order** on rational orbits: `O ≤ O'` when `O` lies in the closure of `O'`.
Equivalently, the closure of `O` lies in the closure of `O'`. -/
noncomputable instance instPartialOrder : PartialOrder (VectorOrbit k H M) :=
  PartialOrder.lift _ closure_image_injective

/-- In the closure order, `O ≤ O'` exactly when the closure of `O` lies in that of `O'`. -/
theorem le_iff_closure_image_subset {O O' : VectorOrbit k H M} :
    O ≤ O' ↔ closure O.image ⊆ closure O'.image :=
  Iff.rfl

/-- In the closure order, `O ≤ O'` exactly when `O` lies in the closure of `O'`. -/
theorem le_iff_image_subset_closure {O O' : VectorOrbit k H M} :
    O ≤ O' ↔ O.image ⊆ closure O'.image :=
  isClosed_closure.closure_subset_iff

/-- The orbit of `w` lies below the orbit of `v` exactly when the line through `(w, 1)` lies in
the closure of the orbit of `v`. -/
theorem mk_le_mk_iff {v w : M} :
    (mk w : VectorOrbit k H M) ≤ mk v ↔
      projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
          (Module.isUnimodular_mk_one v))) := by
  rw [le_iff_image_subset_closure, image_mk, image_mk]
  exact range_projectiveOrbitMap_subset_closure_iff _ _ _ _

/-- The orbit of `w` lies strictly below the orbit of `v` exactly when the line through `(w, 1)`
lies in the boundary of the orbit of `v`. -/
theorem mk_lt_mk_iff {v w : M} :
    (mk w : VectorOrbit k H M) < mk v ↔
      projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
        closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
          (Module.isUnimodular_mk_one v))) \
          Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
            (Module.isUnimodular_mk_one v)) := by
  rw [lt_iff_le_and_ne, mk_le_mk_iff, Ne, ← image_injective.eq_iff, image_mk, image_mk,
    range_projectiveOrbitMap_eq_iff, Set.mem_sdiff]

/-- **Strictly smaller orbits have strictly smaller dimension.** -/
theorem strictMono_topologicalKrullDim_image :
    StrictMono fun O : VectorOrbit k H M ↦ topologicalKrullDim O.image := by
  intro O O' h
  induction O using VectorOrbit.ind with | h w
  induction O' using VectorOrbit.ind with | h v
  beta_reduce
  rw [image_mk, image_mk]
  exact Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt _ _ (mk_lt_mk_iff.mp h)

end VectorOrbit

end TauCeti.Comodule
