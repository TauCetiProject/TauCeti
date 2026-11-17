/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosureOrder
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
import TauCeti.Topology.Constructible.Jacobson

/-!
# The closure order on orbits of vectors

Let `G = Spec H` be an affine group over a field `k` acting on a finite-dimensional
representation `M`, and let `TauCeti.Comodule.VectorOrbit k H M` be the set of rational orbits of
`G` in `M`. The orbit of `v` has a geometric image `Oᵥ` (`TauCeti.Comodule.VectorOrbit.image`):
the full topological image of the projective orbit morphism of the line through `(v, 1)` in the
projective completion `P(M × k)` of `M`. Both are defined in
`TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic`.

When `k` is algebraically closed and `G` is of finite type, distinct orbits have disjoint images,
and even distinct closures. The *closure order* on orbits,

  `O ≤ O'` if and only if `O ⊆ closure O'`,

is therefore a partial order. An orbit lies strictly below another exactly when its vectors lie
in the boundary `closure O' \ O'`, and then it has strictly smaller dimension. Moreover, if an
orbit is stable under nonzero scaling (`mk (c • v) = mk v` for all `c : kˣ`), then the zero orbit
lies in its closure (`mk 0 ≤ mk v`).

Applied to the adjoint representation of `G` on its Lie algebra, this is the closure order on
adjoint orbits, in particular on nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.image_injective`,
  `TauCeti.Comodule.VectorOrbit.closure_image_injective`: orbits are determined by their images,
  and even by the closures of their images.
* `TauCeti.Comodule.VectorOrbit.disjoint_image_of_ne`: distinct orbits have disjoint geometric
  images in `P(M × k)`.
* `TauCeti.Comodule.VectorOrbit.instPartialOrder`: the closure order.
* `TauCeti.Comodule.VectorOrbit.mk_le_mk_iff`, `TauCeti.Comodule.VectorOrbit.mk_lt_mk_iff`:
  the orbit of `w` lies below the orbit of `v` when `w` lies in the closure of the orbit of
  `v`, and strictly below when `w` lies in its boundary.
* `TauCeti.Comodule.VectorOrbit.strictMono_topologicalKrullDim_image`: strictly smaller orbits
  have strictly smaller dimension.
* `TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`: a scaling-invariant orbit contains
  the zero orbit in its closure.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry Topology WithConv

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

/-- **Distinct rational orbits have disjoint geometric images.** In `P(M × k)`, if `O₁ ≠ O₂`,
then `O₁.image` and `O₂.image` share no scheme points (including nonclosed points). -/
theorem disjoint_image_of_ne {O₁ O₂ : VectorOrbit k H M} (hne : O₁ ≠ O₂) :
    Disjoint O₁.image O₂.image := by
  induction O₁ using VectorOrbit.ind with | h v₁
  induction O₂ using VectorOrbit.ind with | h v₂
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne'
  rw [image_mk, image_mk] at hne'
  obtain ⟨x, ⟨hx₁, hx₂⟩, hxc⟩ :=
    ((isConstructible_range_projectiveOrbitMap (H := H) ((v₁, 1) : M × k) _).inter
      (isConstructible_range_projectiveOrbitMap (H := H) ((v₂, 1) : M × k) _))
      |>.nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne')
  obtain ⟨g₁, rfl⟩ :=
    (range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints (H := H)
      ((v₁, 1) : M × k) _).ge ⟨hx₁, hxc⟩
  obtain ⟨g₂, hg₂⟩ :=
    (range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints (H := H)
      ((v₂, 1) : M × k) _).ge ⟨hx₂, hxc⟩
  have hspan := (projectiveOrbitMap_kernelPoint_eq_iff_span_eq
    ((v₂, 1) : M × k) _ ((v₁, 1) : M × k) _ g₂ g₁).mp hg₂
  have hspan' : k ∙ basePointsRepresentation (M × k) (g₁⁻¹ * g₂) ((v₂, 1) : M × k) =
      k ∙ ((v₁, 1) : M × k) := by
    simpa only [Submodule.map_span, Set.image_singleton, Representation.inv_self_apply, map_mul,
      mul_apply_eq_comp] using
      congrArg (Submodule.map (basePointsRepresentation (M × k) g₁⁻¹)) hspan
  exact hne (mk_eq_mk_iff.mpr ⟨(g₁⁻¹ * g₂)⁻¹, by
    rw [← basePointsRepresentation_eq_of_span_eq hspan', Representation.inv_self_apply]⟩)

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

/-- **Scaling-invariant orbits contain the zero orbit in their closure.** If every nonzero scalar
multiple of `v` lies in the same rational orbit as `v`, then `mk 0 ≤ mk v` in the closure order. -/
theorem mk_zero_le_mk_of_forall_smul {v : M}
    (hscale : ∀ c : kˣ, (mk ((c : k) • v) : VectorOrbit k H M) = mk v) :
    (mk (0 : M) : VectorOrbit k H M) ≤ mk v := by
  classical
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
  rw [mk_le_mk_iff, mem_closure_iff]
  intro U hU h0U
  obtain ⟨_, ⟨f, rfl⟩, h0f, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open h0U hU
  change _ ∈ (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) at h0f
  rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 f, TopologicalSpace.Opens.coe_iSup]
    at h0f
  obtain ⟨_, ⟨n, rfl⟩, h0n⟩ := Set.mem_sUnion.mp h0f
  let s := GradedRing.proj 𝒜 n f
  have hs : s ∈ 𝒜 n := SetLike.coe_mem _
  have hs_ne : SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (0, 1)) s ≠ 0 := by
    have hiff := mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((0, 1) : M × k)
      (Module.isUnimodular_mk_one 0) 1 hs
    simp only [map_one, one_apply_eq_self] at hiff
    simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at hiff
    exact hiff.not.mp h0n
  let α : Module.Dual k (M × k) →ₗ[k] Polynomial k :=
    { toFun := fun φ ↦ Polynomial.C (φ (0, 1)) + Polynomial.C (φ (v, 0)) * Polynomial.X
      map_add' := fun φ ψ ↦ by simp only [LinearMap.add_apply, map_add]; ring
      map_smul' := fun r φ ↦ by
        simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
          Polynomial.smul_eq_C_mul]; ring }
  set p : Polynomial k := SymmetricAlgebra.lift α s
  have hpeval (t : k) :
      p.eval t = SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (t • v, 1)) s := by
    have hhom : (Polynomial.aeval t).comp (SymmetricAlgebra.lift α) =
        SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (t • v, 1)) := by
      refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun φ ↦ ?_)
      simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply, SymmetricAlgebra.lift_ι_apply, Module.Dual.eval_apply, α,
        LinearMap.coe_mk, AddHom.coe_mk, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (t • v, (1 : k)) = (0, 1) + t • (v, 0) by ext <;> simp, map_add, map_smul,
        smul_eq_mul, mul_comm]
    simpa [p, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using
      AlgHom.congr_fun hhom s
  have hp0 : p ≠ 0 := fun hp ↦ hs_ne (by simpa [hp] using (hpeval 0).symm)
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert (0 : k) p.roots.toFinset)
  have hc0 : c ≠ 0 := fun h ↦ hc (by simp [h])
  have hpc : p.eval c ≠ 0 := fun h ↦
    hc (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp0).mpr h)))
  obtain ⟨g, hg⟩ := mk_eq_mk_iff.mp (hscale (Units.mk0 c hc0)).symm
  refine ⟨_, hfU ?_, Set.mem_range_self (AlgHom.kernelPoint g.ofConv)⟩
  change _ ∈ (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜))
  rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 f, TopologicalSpace.Opens.coe_iSup]
  refine Set.mem_sUnion.mpr ⟨_, ⟨n, rfl⟩,
    (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((v, 1) : M × k)
      (Module.isUnimodular_mk_one v) g hs).not.mpr ?_⟩
  rw [basePointsRepresentation_prodTrivial, hg]
  simpa [Units.val_mk0, ← hpeval c] using hpc

end VectorOrbit

end TauCeti.Comodule
