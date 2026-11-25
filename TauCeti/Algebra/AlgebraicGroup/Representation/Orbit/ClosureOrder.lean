/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosureOrder
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.AlgebraicGeometry.AugmentationPoint.Dense
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import TauCeti.LinearAlgebra.SymmetricAlgebra.Translation
import TauCeti.RingTheory.GradedAlgebra.Homogenization

/-!
# The closure order on orbits of vectors

Let `G = Spec H` be an affine group over a field `k` acting on a finite-dimensional
representation `M`, and let `TauCeti.Comodule.VectorOrbit k H M` be the set of rational orbits of
`G` in `M`. The orbit of `v` has a geometric image `Oᵥ` (`TauCeti.Comodule.VectorOrbit.image`):
the full topological image of the projective orbit morphism of the line through `(v, 1)` in the
projective completion `P(M × k)` of `M`. Both are defined in
`TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic`.

When `k` is algebraically closed and `G` is of finite type, distinct orbits have distinct images,
and even distinct closures. The *closure order* on orbits,

  `O ≤ O'` if and only if `O ⊆ closure O'`,

is therefore a partial order. An orbit lies strictly below another exactly when its vectors lie
in the boundary `closure O' \ O'`, and then it has strictly smaller dimension. Moreover, the
orbit of `w` lies below the orbit of `v` exactly when every polynomial function in `Sym(M*)` that
vanishes on every rational translate of `v` also vanishes at `w`. The converse direction uses
homogeneous basic open sets of `P(M × k)` and restriction of homogeneous polynomials to the affine
chart `M × {1}`.

Applied to the adjoint representation of `G` on its Lie algebra, this is the closure order on
adjoint orbits, in particular on nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.image_injective`,
  `TauCeti.Comodule.VectorOrbit.closure_image_injective`: orbits are determined by their images,
  and even by the closures of their images.
* `TauCeti.Comodule.VectorOrbit.instPartialOrder`: the closure order.
* `TauCeti.Comodule.VectorOrbit.mk_le_mk_iff`, `TauCeti.Comodule.VectorOrbit.mk_lt_mk_iff`:
  the orbit of `w` lies below the orbit of `v` when `w` lies in the closure of the orbit of
  `v`, and strictly below when `w` lies in its boundary.
* `TauCeti.Comodule.VectorOrbit.strictMono_topologicalKrullDim_image`: strictly smaller orbits
  have strictly smaller dimension.
* `lift_eval_eq_zero_of_mk_le_mk_of_forall_lift_eval_basePointsRepresentation_eq_zero` in
  `TauCeti.Comodule.VectorOrbit`: polynomials vanishing on all rational translates of `v` vanish
  at every `w` with `mk w ≤ mk v`.
* `TauCeti.Comodule.VectorOrbit.mk_le_mk_iff_forall_lift_eval_eq_zero`: conversely, the closure
  order is cut out by these polynomials.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

attribute [local instance] prodTrivial

namespace VectorOrbit

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

/-- **Polynomials vanishing on a rational orbit vanish on its closure.** Over an algebraically
closed field, if the rational orbit of `w` lies in the closure of the rational orbit of `v`, and a
polynomial `p ∈ Sym(M*)` vanishes on `g • v` for every rational point `g ∈ G(k)`, then `p` vanishes
at `w`. -/
theorem lift_eval_eq_zero_of_mk_le_mk_of_forall_lift_eval_basePointsRepresentation_eq_zero
    {v w : M} (h : (mk w : VectorOrbit k H M) ≤ mk v)
    {p : SymmetricAlgebra k (Module.Dual k M)}
    (hp : ∀ g : WithConv (H →ₐ[k] k),
      SymmetricAlgebra.lift (Module.Dual.eval k M (basePointsRepresentation M g v)) p = 0) :
    SymmetricAlgebra.lift (Module.Dual.eval k M w) p = 0 := by
  -- Homogenize `p` against the trivial projective coordinate on `M × k`.
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
  obtain ⟨d, P, hP, hPeval⟩ :=
    TauCeti.GradedAlgebra.exists_mem_grade_and_forall_map_eq_of_mem_one 𝒜
      (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k _ (LinearMap.snd k M k))
      (SymmetricAlgebra.map k (LinearMap.fst k M k).dualMap p)
  have heval (u : M) :
      SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (u, 1)) P =
        SymmetricAlgebra.lift (Module.Dual.eval k M u) p := by
    exact (hPeval (SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (u, 1))).toRingHom
      (by simp)).trans (SymmetricAlgebra.lift_eval_map_dualMap k (LinearMap.fst k M k) (u, 1) p)
  have hrange : Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v)) ⊆ (Proj.basicOpen 𝒜 P : Set (Proj 𝒜))ᶜ := by
    rintro _ ⟨x, rfl⟩
    refine (denseRange_kernelPoint (k := k) (A := H)).induction_on
      (p := fun x ↦ projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v) x ∈ (Proj.basicOpen 𝒜 P : Set (Proj 𝒜))ᶜ) x
      ((Proj.basicOpen 𝒜 P).isOpen.isClosed_compl.preimage
        (projectiveOrbitMap (H := H) ((v, 1) : M × k)
          (Module.isUnimodular_mk_one v)).continuous) ?_
    intro g
    rw [Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not]
    have hmem := (mem_projectiveOrbitMap_kernelPoint_iff ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v) (WithConv.toConv g) hP).mpr
    rw [WithConv.ofConv_toConv] at hmem
    exact hmem (by rw [basePointsRepresentation_prodTrivial, heval]; exact hp (WithConv.toConv g))
  have hw_mem : projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ (Proj.basicOpen 𝒜 P : Set (Proj 𝒜))ᶜ :=
    closure_minimal hrange (Proj.basicOpen 𝒜 P).isOpen.isClosed_compl (mk_le_mk_iff.mp h)
  rw [Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not] at hw_mem
  rw [← TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom] at hw_mem
  have h0 := (mem_projectiveOrbitMap_kernelPoint_iff ((w, 1) : M × k)
    (Module.isUnimodular_mk_one w) 1 hP).mp hw_mem
  simpa [heval] using h0

/-- **The closure order is cut out by polynomials.** Over an algebraically closed field, the
rational orbit of `w` lies below the rational orbit of `v` exactly when every polynomial
`p ∈ Sym(M*)` vanishing on all rational translates `g • v` also vanishes at `w`. -/
theorem mk_le_mk_iff_forall_lift_eval_eq_zero {v w : M} :
    (mk w : VectorOrbit k H M) ≤ mk v ↔
      ∀ p : SymmetricAlgebra k (Module.Dual k M),
        (∀ g : WithConv (H →ₐ[k] k),
          SymmetricAlgebra.lift (Module.Dual.eval k M (basePointsRepresentation M g v)) p = 0) →
        SymmetricAlgebra.lift (Module.Dual.eval k M w) p = 0 := by
  refine ⟨fun h _ hp ↦
    lift_eval_eq_zero_of_mk_le_mk_of_forall_lift_eval_basePointsRepresentation_eq_zero h hp,
    fun h ↦ ?_⟩
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
  -- Restriction of polynomial functions on `M × k` to the affine chart `M × {1}`: translate by
  -- the point `(0, 1)`, then restrict along `M → M × k`.
  let D : SymmetricAlgebra k (Module.Dual k (M × k)) →ₐ[k]
      SymmetricAlgebra k (Module.Dual k M) :=
    (SymmetricAlgebra.map k (LinearMap.inl k M k).dualMap).comp
      (SymmetricAlgebra.translation (Module.Dual.eval k (M × k) (0, 1))).toAlgHom
  have hD (u : M) (P : SymmetricAlgebra k (Module.Dual k (M × k))) :
      SymmetricAlgebra.lift (Module.Dual.eval k M u) (D P) =
        SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (u, 1)) P := by
    rw [AlgHom.comp_apply, SymmetricAlgebra.lift_eval_map_dualMap, AlgEquiv.toAlgHom_apply,
      SymmetricAlgebra.lift_translation]
    congr 1
    ext φ
    simpa using (map_add φ (u, 0) (0, 1)).symm
  -- Otherwise a homogeneous basic open set around the line through `(w, 1)` avoids the orbit.
  rw [mk_le_mk_iff]
  by_contra hw
  obtain ⟨_, ⟨f, rfl⟩, hwf, hf⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝒜)
      (U := ⟨_, isClosed_closure.isOpen_compl⟩)
      (TopologicalSpace.Opens.mem_mk.mpr (Set.mem_compl_iff _ _ |>.mpr hw))
  rw [Proj.basicOpen_eq_iSup_proj] at hwf hf
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hwf
  have hP : GradedRing.proj 𝒜 i f ∈ 𝒜 i := by
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  -- Its dehomogenization vanishes on the orbit of `v` but not at `w`.
  have hvanish (g : WithConv (H →ₐ[k] k)) : SymmetricAlgebra.lift
      (Module.Dual.eval k M (basePointsRepresentation M g v)) (D (GradedRing.proj 𝒜 i f)) = 0 := by
    rw [hD, ← basePointsRepresentation_prodTrivial]
    refine (mem_projectiveOrbitMap_kernelPoint_iff ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v) g hP).mp ?_
    by_contra hn
    have hx := (le_iSup _ i).trans hf ((Proj.mem_basicOpen 𝒜 _ _).mpr hn)
    rw [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff] at hx
    exact hx (subset_closure (Set.mem_range_self _))
  have hwP := (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((w, 1) : M × k)
    (Module.isUnimodular_mk_one w) 1 hP).mpr (by simpa [hD] using h _ hvanish)
  rw [TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom] at hwP
  exact (Proj.mem_basicOpen 𝒜 _ _).mp hi hwP

end VectorOrbit

end TauCeti.Comodule
