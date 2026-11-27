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
in the boundary `closure O' \ O'`, and then it has strictly smaller dimension. Moreover, the
orbit of `w` lies below the orbit of `v` exactly when every polynomial function in `Sym(M*)` that
vanishes on every rational translate of `v` also vanishes at `w`. Consequently, any orbit stable
under nonzero scalar multiplication contains the zero orbit in its closure. When an orbit has only
finitely many lower orbits in the closure order, its geometric closure and boundary inside the
affine chart `{t ≠ 0}` of `P(M × k)` decompose as the finite unions of the geometric images of its
lower (respectively strictly lower) orbits, as full sets of scheme points.

Applied to the adjoint representation of `G` on its Lie algebra, this is the closure order on
adjoint orbits, in particular on nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.image_injective`,
  `TauCeti.Comodule.VectorOrbit.closure_image_injective`,
  `TauCeti.Comodule.VectorOrbit.disjoint_image_of_ne`: orbits have pairwise disjoint geometric
  images and distinct closures.
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
* `TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`: a scaling-invariant orbit contains
  the zero orbit in its closure.
* `TauCeti.Comodule.VectorOrbit.setOf_mk_le_eq_union_biUnion_of_forall_le`,
  `TauCeti.Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion`, and
  `TauCeti.Comodule.VectorOrbit.closure_image_sdiff_image_inter_basicOpen_snd_eq_biUnion`:
  rational-vector and finite scheme-point closure and boundary decompositions.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry TopologicalSpace Topology WithConv

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
  have himg : O₁.image ≠ O₂.image := image_injective.ne hne
  induction O₁ using VectorOrbit.ind with | h v₁
  induction O₂ using VectorOrbit.ind with | h v₂
  rw [image_mk, image_mk] at himg ⊢
  exact disjoint_range_projectiveOrbitMap_of_ne _ _ himg

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

/-- **Scaling-invariant orbits contain the zero orbit in their closure.** If every nonzero scalar
multiple of `v` lies in the same rational orbit as `v`, then `mk 0 ≤ mk v` in the closure order. -/
theorem mk_zero_le_mk_of_forall_smul {v : M}
    (hscale : ∀ c : kˣ, (mk ((c : k) • v) : VectorOrbit k H M) = mk v) :
    (mk (0 : M) : VectorOrbit k H M) ≤ mk v := by
  classical
  rw [mk_le_mk_iff_forall_lift_eval_eq_zero]
  intro p hp
  let α : Module.Dual k M →ₗ[k] Polynomial k :=
    { toFun := fun φ ↦ Polynomial.C (φ v) * Polynomial.X
      map_add' := fun φ ψ ↦ by simp [add_mul]
      map_smul' := fun r φ ↦ by simp [Polynomial.smul_eq_C_mul, mul_assoc] }
  set q : Polynomial k := SymmetricAlgebra.lift α p
  have hqeval (t : k) : q.eval t = SymmetricAlgebra.lift (Module.Dual.eval k M (t • v)) p := by
    have hhom : (Polynomial.aeval t).comp (SymmetricAlgebra.lift α) =
        SymmetricAlgebra.lift (Module.Dual.eval k M (t • v)) :=
      SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ by simp [α]; ring
    simpa [q, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using
      AlgHom.congr_fun hhom p
  have hq0 : q = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (insert (0 : k) q.roots.toFinset)
    have hc0 : c ≠ 0 := fun h ↦ hc (by simp [h])
    obtain ⟨g, hg⟩ := mk_eq_mk_iff.mp (hscale (Units.mk0 c hc0)).symm
    rw [Units.val_mk0] at hg
    have hroot : q.eval c = 0 := by
      rw [hqeval c, ← hg]
      exact hp g
    exact hc (Finset.mem_insert_of_mem
      (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hroot)))
  simpa [hq0] using (hqeval 0).symm

/-- **Decomposition of the `k`-rational vectors below an orbit `O`** for any family `S` containing
every orbit below `O`. -/
theorem setOf_mk_le_eq_union_biUnion_of_forall_le {S : Set (VectorOrbit k H M)}
    {O : VectorOrbit k H M} (hS : ∀ ⦃O' : VectorOrbit k H M⦄, O' ≤ O → O' ∈ S) :
    {y : M | (mk y : VectorOrbit k H M) ≤ O} =
      {y : M | mk y = O} ∪
        ⋃ O' ∈ {O' : VectorOrbit k H M | O' ∈ S ∧ O' < O}, {y : M | mk y = O'} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, exists_prop]
  refine ⟨fun hle ↦ ?_, ?_⟩
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨mk y, ⟨hS hle, hlt⟩, rfl⟩
  · rintro (rfl | ⟨_, ⟨-, hlt⟩, rfl⟩)
    · exact le_rfl
    · exact hlt.le

/-- **Scheme-point closure decomposition of an orbit with finitely many lower orbits.** In the
affine chart `U = {t ≠ 0}` of `P(M × k)`, when `{O' | O' ≤ O}` is finite, `closure O.image ∩ U` is
the union of the geometric orbit images `O'.image` for `O' ≤ O`, including nonclosed points. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion {O : VectorOrbit k H M}
    (hf : {O' : VectorOrbit k H M | O' ≤ O}.Finite) :
    closure O.image ∩
        (Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H M | O' ≤ O}, O'.image := by
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
  let U : Set (Proj 𝒜) :=
    (Proj.basicOpen 𝒜 (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _)
  have hlhs_cons : IsConstructible (closure O.image ∩ U) :=
    ((NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl).of_compl.inter
      ((NoetherianSpace.isCompact _).isConstructible (Proj.basicOpen 𝒜 _).isOpen)
  have hrhs_cons : IsConstructible (⋃ O' ∈ {O' : VectorOrbit k H M | O' ≤ O}, O'.image) :=
    IsConstructible.biUnion hf fun O' _ ↦ by
      induction O' using VectorOrbit.ind with | h v
      rw [image_mk]
      exact isConstructible_range_projectiveOrbitMap _ _
  -- Constructible subsets of the Jacobson scheme `Proj 𝒜` are determined by their closed points.
  refine (hlhs_cons.eq_iff_inter_closedPoints_eq hrhs_cons).mpr (Set.Subset.antisymm ?_ ?_)
  · rintro x ⟨⟨hxcl, hxU⟩, hxc⟩
    obtain ⟨⟨v, c⟩, hvc, rfl⟩ :=
      (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) x).mp hxc
    have hc0 : c ≠ 0 := by
      simpa [AlgHom.convOne_def] using (ι_mem_projectiveOrbitMap_kernelPoint_iff (H := H)
        ((v, c) : M × k) hvc 1 (LinearMap.snd k M k)).not.mp hxU
    let y : M := c⁻¹ • v
    have hpt : projectiveOrbitMap (H := H) ((v, c) : M × k) hvc
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) =
        projectiveOrbitMap (H := H) ((y, 1) : M × k) (Module.isUnimodular_mk_one y)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
      have hiff := projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H) ((v, c) : M × k) hvc
        ((y, 1) : M × k) (Module.isUnimodular_mk_one y) 1 1
      simp only [map_one, one_apply_eq_self] at hiff
      rw [TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom] at hiff
      exact hiff.mpr <| Submodule.span_singleton_eq_span_singleton.mpr
        ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), by ext <;> simp [y, Units.smul_def, inv_mul_cancel₀ hc0]⟩
    have hle : (mk y : VectorOrbit k H M) ≤ O := by
      induction O using VectorOrbit.ind with | h e
      rw [image_mk] at hxcl
      rwa [mk_le_mk_iff, ← hpt]
    exact ⟨Set.mem_iUnion₂.mpr ⟨mk y, hle, by rw [hpt, image_mk]; exact Set.mem_range_self _⟩, hxc⟩
  · rintro x ⟨hx, hxc⟩
    obtain ⟨O', hle, hxO'⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨⟨le_iff_image_subset_closure.mp hle hxO', ?_⟩, hxc⟩
    induction O' using VectorOrbit.ind with | h v
    rw [image_mk] at hxO'
    exact range_projectiveOrbitMap_subset_basicOpen_snd v hxO'

/-- **Scheme-point boundary decomposition of an orbit with finitely many lower orbits.** In the
affine chart `U = {t ≠ 0}` of `P(M × k)`, when `{O' | O' ≤ O}` is finite, the boundary
`(closure O.image \ O.image) ∩ U` is the union of `O'.image` over all strictly smaller `O' < O`. -/
theorem closure_image_sdiff_image_inter_basicOpen_snd_eq_biUnion {O : VectorOrbit k H M}
    (hf : {O' : VectorOrbit k H M | O' ≤ O}.Finite) :
    (closure O.image \ O.image) ∩
        (Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H M | O' < O}, O'.image := by
  rw [Set.sdiff_eq, Set.inter_right_comm, ← Set.sdiff_eq,
    closure_image_inter_basicOpen_snd_eq_biUnion hf]
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨fun ⟨⟨O', hle, hxO'⟩, hxO⟩ ↦ ⟨O', lt_of_le_of_ne hle (fun h ↦ hxO (h ▸ hxO')), hxO'⟩,
    fun ⟨O', hlt, hxO'⟩ ↦ ⟨⟨O', hlt.le, hxO'⟩,
      Set.disjoint_left.mp (disjoint_image_of_ne hlt.ne) hxO'⟩⟩

end VectorOrbit

end TauCeti.Comodule
