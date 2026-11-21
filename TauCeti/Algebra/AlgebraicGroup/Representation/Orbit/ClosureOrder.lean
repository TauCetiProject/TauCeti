/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosureOrder
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.AlgebraicGeometry.AugmentationPoint.Dense
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
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

When `k` is algebraically closed and `G` is of finite type, distinct orbits have distinct images,
and even distinct closures. The *closure order* on orbits,

  `O ≤ O'` if and only if `O ⊆ closure O'`,

is therefore a partial order. An orbit lies strictly below another exactly when its vectors lie
in the boundary `closure O' \ O'`, and then it has strictly smaller dimension. Moreover, any
polynomial function in `Sym(M*)` that vanishes on every rational translate of `v` also vanishes at
every vector whose orbit lies below the orbit of `v`.

Over any infinite field, a conical orbit — one closed under nonzero scalar multiplication —
contains the origin in its closure
(`TauCeti.Comodule.mem_closure_projectiveOrbitMap_zero_of_forall_smul`,
`TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`). When an orbit `O` has only finitely
many orbits below it in the closure order, the affine chart `M = {t ≠ 0}` of `P(M × k)` cuts both
`closure O` and the boundary `closure O \ O` into the exact union of the full scheme-point orbit
images below `O` (`TauCeti.Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion_le`
and `TauCeti.Comodule.VectorOrbit.closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt`).

Applied to the adjoint representation of `G` on its Lie algebra, this is the closure order on
adjoint orbits, in particular on nilpotent orbits.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.image_injective`,
  `TauCeti.Comodule.VectorOrbit.disjoint_image_of_ne`,
  `TauCeti.Comodule.VectorOrbit.closure_image_injective`: distinct orbits have disjoint images,
  and are determined by their images and even by the closures of their images.
* `TauCeti.Comodule.VectorOrbit.instPartialOrder`: the closure order.
* `TauCeti.Comodule.VectorOrbit.mk_le_mk_iff`, `TauCeti.Comodule.VectorOrbit.mk_lt_mk_iff`:
  the orbit of `w` lies below the orbit of `v` when `w` lies in the closure of the orbit of
  `v`, and strictly below when `w` lies in its boundary.
* `TauCeti.Comodule.VectorOrbit.strictMono_topologicalKrullDim_image`: strictly smaller orbits
  have strictly smaller dimension.
* `lift_eval_eq_zero_of_mk_le_mk_of_forall_lift_eval_basePointsRepresentation_eq_zero` in
  `TauCeti.Comodule.VectorOrbit`: polynomials vanishing on all rational translates of `v` vanish
  at every `w` with `mk w ≤ mk v`.
* `TauCeti.Comodule.mem_closure_projectiveOrbitMap_zero_of_forall_smul` and
  `TauCeti.Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul`: conical orbits contain `0` in their
  closure.
* `TauCeti.Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion_le` and
  `TauCeti.Comodule.VectorOrbit.closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt`: when the
  lower set of `O` is finite, `closure O` and `closure O \ O` in the affine chart `M` are the
  unions of the full orbit images `O' ≤ O` and `O' < O`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.2.
-/

public section

open AlgebraicGeometry TopologicalSpace

namespace TauCeti.Comodule

universe u

attribute [local instance] prodTrivial

section Conical

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Conical orbits contain zero in their closure.** Over an infinite field `k`, if the rational
orbit of `v` contains every nonzero scalar multiple `t • v`, then the line through `(0, 1)` lies in
the closure of the projective orbit image of `(v, 1)`. Neither algebraic closedness nor finite
generation of `H` is needed. -/
theorem mem_closure_projectiveOrbitMap_zero_of_forall_smul [Infinite k] {v : M}
    (hv : ∀ t : k, t ≠ 0 →
      ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = t • v) :
    projectiveOrbitMap (H := H) ((0, 1) : M × k) (Module.isUnimodular_mk_one (0 : M))
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v))) := by
  classical
  let 𝒜 := SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
  rw [mem_closure_iff]
  intro U hU h0U
  obtain ⟨_, ⟨f, rfl⟩, h0f, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open h0U hU
  -- Pick a homogeneous component `q` of `f` whose basic open still contains the origin point.
  obtain ⟨d, h0q⟩ := ProjectiveSpectrum.exists_mem_basicOpen_proj_of_mem_basicOpen h0f
  have hq_le := ProjectiveSpectrum.basicOpen_proj_le (𝒜 := 𝒜) f d
  set q := GradedRing.proj 𝒜 d f
  have hq_hom : q ∈ 𝒜 d := SetLike.coe_mem _
  -- Restrict `q` to the affine line `t ↦ (t • v, 1)` as a univariate polynomial `P`.
  obtain ⟨P, hP⟩ := _root_.SymmetricAlgebra.exists_polynomial_eval_eq_lift_add_smul q
    (Module.Dual.eval k (M × k) (0, 1)) (Module.Dual.eval k (M × k) (v, 0))
  have heval (t : k) :
      P.eval t = SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (t • v, 1)) q := by
    rw [hP, ← map_smul, ← map_add]
    simp
  have hP0 : P.eval 0 ≠ 0 := by
    rw [heval, zero_smul]
    intro hzero
    apply (ProjectiveSpectrum.mem_basicOpen 𝒜 q _).mp h0q
    have hmem := (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((0, 1) : M × k)
      (Module.isUnimodular_mk_one (0 : M)) 1 hq_hom).mpr (by simpa using hzero)
    simpa [AlgHom.convOne_def] using hmem
  have hPne : P ≠ 0 := fun h ↦ hP0 (by simp [h])
  -- Choose a nonzero scalar `t` that is not a root of `P`.
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (insert (0 : k) P.roots.toFinset)
  have ht0 : t ≠ 0 := fun h ↦ ht (Finset.mem_insert.mpr (Or.inl h))
  have hPt : P.eval t ≠ 0 := fun hzero ↦
    ht (Finset.mem_insert_of_mem
      (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPne).mpr hzero)))
  obtain ⟨g, hg⟩ := hv t ht0
  refine ⟨projectiveOrbitMap (H := H) ((t • v, 1) : M × k) (Module.isUnimodular_mk_one (t • v))
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)), hfU (hq_le ?_), ?_⟩
  · intro hmem
    apply hPt
    rw [heval]
    have h := (mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((t • v, 1) : M × k)
      (Module.isUnimodular_mk_one (t • v)) 1 hq_hom).mp (by simpa [AlgHom.convOne_def] using hmem)
    simpa using h
  · rw [← range_projectiveOrbitMap_mk_one_basePointsRepresentation g v, hg]
    exact Set.mem_range_self _

end Conical

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

/-- **Distinct orbits have disjoint geometric images.** Two distinct rational orbits share no
scheme point, closed or nonclosed, in `P(M × k)`. -/
theorem disjoint_image_of_ne {O O' : VectorOrbit k H M} (h : O ≠ O') :
    Disjoint O.image O'.image := by
  by_contra hdisj
  rw [Set.not_disjoint_iff_nonempty_inter] at hdisj
  obtain ⟨x, ⟨hxO, hxO'⟩, hxc⟩ :=
    (O.isConstructible_image.inter O'.isConstructible_image).nonempty_inter_closedPoints hdisj
  obtain ⟨u, rfl⟩ :=
    exists_projectiveOrbitMap_mk_one_eq_of_mem_basicOpen_snd (H := H)
      (O.image_subset_basicOpen_snd hxO) hxc
  induction O using VectorOrbit.ind with | h v
  induction O' using VectorOrbit.ind with | h w
  rw [image_mk] at hxO hxO'
  have huv : (mk u : VectorOrbit k H M) = mk v := image_injective <| by
    rw [image_mk, image_mk]
    exact (range_projectiveOrbitMap_eq_iff _ _ _ _).mpr hxO
  have huw : (mk u : VectorOrbit k H M) = mk w := image_injective <| by
    rw [image_mk, image_mk]
    exact (range_projectiveOrbitMap_eq_iff _ _ _ _).mpr hxO'
  exact h (huv.symm.trans huw)

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
    have hF : (SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (u, 1))).comp
        (SymmetricAlgebra.map k (LinearMap.fst k M k).dualMap) =
        SymmetricAlgebra.lift (Module.Dual.eval k M u) := by
      ext φ
      simp
    simpa [← hF] using
      hPeval (SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (u, 1))).toRingHom (by simp)
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
  have h1 : (1 : WithConv (H →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k H := by
    ext
    simp [AlgHom.convOne_def]
  rw [← h1] at hw_mem
  have h0 := (mem_projectiveOrbitMap_kernelPoint_iff ((w, 1) : M × k)
    (Module.isUnimodular_mk_one w) 1 hP).mp hw_mem
  simpa [heval] using h0

/-- **Conical orbits lie above zero in the closure order.** If the rational orbit of `v` contains
every nonzero scalar multiple of `v`, then `mk 0 ≤ mk v`. -/
theorem mk_zero_le_mk_of_forall_smul {v : M}
    (hv : ∀ t : k, t ≠ 0 →
      ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation M g v = t • v) :
    (mk (0 : M) : VectorOrbit k H M) ≤ mk v :=
  mk_le_mk_iff.mpr (mem_closure_projectiveOrbitMap_zero_of_forall_smul hv)

/-- **Closure decomposition for orbits with finite lower set.** When only finitely many rational
orbits lie below `O` in the closure order, the closure of `O` inside the affine chart `M = {t ≠ 0}`
of `P(M × k)` is the exact union of the full scheme-point orbit images `O' ≤ O`. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion_le {O : VectorOrbit k H M}
    (hfin : {O' : VectorOrbit k H M | O' ≤ O}.Finite) :
    closure O.image ∩
        (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H M | O' ≤ O}, O'.image := by
  let U : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))) :=
    (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
      (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _)
  have hU_c : Topology.IsConstructible U :=
    (NoetherianSpace.isCompact U).isConstructible (Proj.basicOpen _ _).isOpen
  have hcl_c : Topology.IsConstructible (closure O.image) :=
    ((NoetherianSpace.isCompact (closure O.image)ᶜ).isConstructible
      isClosed_closure.isOpen_compl).of_compl
  have hUnion_c : Topology.IsConstructible
      (⋃ O' ∈ {O' : VectorOrbit k H M | O' ≤ O}, O'.image) :=
    Topology.IsConstructible.biUnion hfin fun O' _ ↦ O'.isConstructible_image
  rw [(hcl_c.inter hU_c).eq_iff_inter_closedPoints_eq hUnion_c]
  induction O using VectorOrbit.ind with | h v
  ext x
  constructor
  · rintro ⟨⟨hxcl, hxU⟩, hxc⟩
    obtain ⟨w, rfl⟩ := exists_projectiveOrbitMap_mk_one_eq_of_mem_basicOpen_snd (H := H) hxU hxc
    rw [image_mk] at hxcl
    exact ⟨Set.mem_biUnion (mk_le_mk_iff.mpr hxcl)
      ((image_mk (k := k) (H := H) w).symm ▸ Set.mem_range_self _), hxc⟩
  · rintro ⟨hx, hxc⟩
    obtain ⟨O', hO'le, hxO'⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨⟨(le_iff_image_subset_closure.mp hO'le) hxO', O'.image_subset_basicOpen_snd hxO'⟩, hxc⟩

/-- **Boundary decomposition for orbits with finite lower set.** When only finitely many rational
orbits lie below `O` in the closure order, the boundary `closure O \ O` inside the affine chart
`M = {t ≠ 0}` of `P(M × k)` is the exact union of the full scheme-point orbit images `O' < O`. -/
theorem closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt {O : VectorOrbit k H M}
    (hfin : {O' : VectorOrbit k H M | O' ≤ O}.Finite) :
    (closure O.image \ O.image) ∩
        (Proj.basicOpen (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H M | O' < O}, O'.image := by
  rw [Set.sdiff_eq, Set.inter_right_comm, ← Set.sdiff_eq,
    closure_image_inter_basicOpen_snd_eq_biUnion_le hfin]
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨⟨O', hO'le, hxO'⟩, hxO⟩
    refine ⟨O', lt_of_le_of_ne hO'le ?_, hxO'⟩
    rintro rfl
    exact hxO hxO'
  · rintro ⟨O', hO'lt, hxO'⟩
    exact ⟨⟨O', le_of_lt hO'lt, hxO'⟩,
      Set.disjoint_right.mp (disjoint_image_of_ne hO'lt.ne') hxO'⟩

end VectorOrbit

end TauCeti.Comodule
