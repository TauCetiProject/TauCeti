/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.Orbit
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedPoints
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocallyClosed
import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
import TauCeti.Topology.Constructible.Jacobson

/-!
# Closures of nilpotent adjoint orbits

Let `G = Spec H` be a finite-type affine group over an algebraically closed field `k` of
characteristic zero, with Lie algebra `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)`. Recall
from `TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder` that rational adjoint
orbits carry a partial order `O' ≤ O ↔ O'.image ⊆ closure O.image`, where `O.image` is the full
topological image (including nonclosed points) of the projective orbit morphism in the projective
completion `P(𝔤 × k)`.

This file proves the fundamental closure properties of nilpotent adjoint orbits, with **no
connectedness hypothesis** on `G`:

* **Closure stability (`TauCeti.isNilpotent_ad_of_mk_le_mk`, `TauCeti.mem_nilpotentOrbits_of_le`)**:
  without even assuming `IsKilling`, if `mk y ≤ mk x` and `ad x` is nilpotent, then `ad y` is
  nilpotent. The proof pulls back the homogeneous trace-power polynomials `x ↦ tr (ad x ^ m)`
  (`TauCeti.tracePowerPolynomial`) along `Prod.fst : 𝔤 × k → 𝔤` to `P(𝔤 × k)` and applies
  `JacobsonSpace.closure_inter_closedPoints_eq_closure`.
* **Minimality of the zero orbit (`TauCeti.mk_zero_le_of_mem_nilpotentOrbits`)**: when `𝔤` has
  nondegenerate Killing form, every nilpotent orbit is a cone (`mk (c • e) = mk e` for `c : kˣ`),
  so the zero orbit `mk 0` lies in its closure (`mk 0 ≤ O`).
* **Finiteness of lower ideals (`TauCeti.finite_lower_nilpotentOrbits`)**: only finitely many
  orbits lie below any nilpotent orbit `O`.
* **Scheme-point decomposition of closures and boundaries**: in the affine chart `U = {t ≠ 0}` of
  `P(𝔤 × k)`, `closure O.image ∩ U = ⋃ O' ≤ O, O'.image` and
  `(closure O.image \ O.image) ∩ U = ⋃ O' < O, O'.image`, as full sets of scheme points
  (including nonclosed points), proved via `Topology.IsConstructible.eq_iff_inter_closedPoints_eq`
  and finiteness of `{O' | O' ≤ O}`.

## Main declarations

* `TauCeti.isNilpotent_ad_of_mk_le_mk` and `TauCeti.mem_nilpotentOrbits_of_le`
* `TauCeti.mk_zero_le_of_mem_nilpotentOrbits`
* `TauCeti.finite_lower_nilpotentOrbits`
* `TauCeti.closure_image_inter_basicOpen_snd_eq_biUnion`
* `TauCeti.closure_diff_image_inter_basicOpen_snd_eq_biUnion`

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.2.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Progress in Math. 228, Birkhäuser,
  2004, §8.
-/

public section

open AlgebraicGeometry LieAlgebra TopologicalSpace Topology WithConv

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

/-! ### Closure stability of the nilpotent locus -/

section ClosureStability

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Closure stability of `ad`-nilpotence.** For any finite-type affine group over an algebraically
closed field of characteristic zero (with no semisimplicity or connectedness hypothesis), if
`mk y ≤ mk x` in the closure order and `ad x` is nilpotent, then `ad y` is nilpotent. -/
theorem isNilpotent_ad_of_mk_le_mk {x y : 𝔤}
    (hle : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤
      Comodule.VectorOrbit.mk x)
    (hx : IsNilpotent (LieAlgebra.ad k 𝔤 x)) :
    IsNilpotent (LieAlgebra.ad k 𝔤 y) := by
  refine LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero.mpr fun m hm ↦ ?_
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k))
  let p := tracePowerPolynomial k 𝔤 𝔤 m
  let π : Module.Dual k 𝔤 →ₗ[k] Module.Dual k (𝔤 × k) := (LinearMap.fst k 𝔤 k).dualMap
  let P : SymmetricAlgebra k (Module.Dual k (𝔤 × k)) := SymmetricAlgebra.map k π p
  have hP_hom : P ∈ 𝒜 m :=
    TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule π
      (tracePowerPolynomial_mem_homogeneousSubmodule (R := k) (L := 𝔤) (M := 𝔤) m)
  have hP_eval : ∀ v : 𝔤,
      SymmetricAlgebra.lift (Module.Dual.eval k (𝔤 × k) (v, (1 : k))) P =
        LinearMap.trace k 𝔤 (LieAlgebra.ad k 𝔤 v ^ m) := by
    intro v
    have hcomp : (SymmetricAlgebra.lift (Module.Dual.eval k (𝔤 × k) (v, (1 : k)))).comp
          (SymmetricAlgebra.map k π) = SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 v) := by
      apply SymmetricAlgebra.algHom_ext
      ext φ
      simp [π]
    have hval := AlgHom.congr_fun hcomp p
    -- `ad k 𝔤 v` is definitionally `LieModule.toEnd k 𝔤 𝔤 v`.
    exact hval.trans (lift_eval_tracePowerPolynomial (R := k) (L := 𝔤) (M := 𝔤) v m)
  -- Consider the closed zero locus `Z = (Proj.basicOpen 𝒜 P)ᶜ` in `P(𝔤 × k)`.
  let Z : Set (Proj 𝒜) := (Proj.basicOpen 𝒜 P : Set (Proj 𝒜))ᶜ
  have hZ : IsClosed Z := (Proj.basicOpen 𝒜 P).isOpen.isClosed_compl
  -- Every closed point of the orbit of `x` lies in `Z`.
  have hclosed : Set.range (Comodule.projectiveOrbitMap (H := H) ((x, 1) : 𝔤 × k)
      (Module.isUnimodular_mk_one x)) ∩ closedPoints (Proj 𝒜) ⊆ Z := by
    rw [← Comodule.range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints]
    rintro _ ⟨g, rfl⟩
    simp only [Z, Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not]
    rw [Comodule.mem_projectiveOrbitMap_kernelPoint_iff _ _ g hP_hom,
      Comodule.basePointsRepresentation_prodTrivial, hP_eval]
    exact LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero.mp
      ((isNilpotent_ad_basePointsRepresentation_iff g x).mpr hx) m hm
  -- Because the orbit image is locally closed in a Jacobson space, its closure lies in `Z`.
  have hsub : closure (Set.range (Comodule.projectiveOrbitMap (H := H) ((x, 1) : 𝔤 × k)
      (Module.isUnimodular_mk_one x))) ⊆ Z := by
    rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure
      (Comodule.isLocallyClosed_range_projectiveOrbitMap _ _)]
    exact hZ.closure_subset_iff.mpr hclosed
  have hyZ : Comodule.projectiveOrbitMap (H := H) ((y, 1) : 𝔤 × k)
      (Module.isUnimodular_mk_one y) (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z :=
    hsub (Comodule.VectorOrbit.mk_le_mk_iff.mp hle)
  have hyP : P ∈ (Comodule.projectiveOrbitMap (H := H) ((y, 1) : 𝔤 × k)
      (Module.isUnimodular_mk_one y)
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))).asHomogeneousIdeal := by
    simpa only [Z, Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not] using hyZ
  have hiff := Comodule.mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((y, 1) : 𝔤 × k)
    (Module.isUnimodular_mk_one y) 1 hP_hom
  simp only [map_one, one_apply_eq_self] at hiff
  simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp, hP_eval] at hiff
  exact hiff.mp hyP

/-- Any orbit lying below a nilpotent orbit in the closure order is again nilpotent. -/
theorem mem_nilpotentOrbits_of_le {O O' : Comodule.VectorOrbit k H 𝔤}
    (hle : O' ≤ O) (hO : O ∈ nilpotentOrbits k H) : O' ∈ nilpotentOrbits k H := by
  induction O using Comodule.VectorOrbit.ind with | h x
  induction O' using Comodule.VectorOrbit.ind with | h y
  rw [mem_nilpotentOrbits_mk_iff] at hO ⊢
  exact isNilpotent_ad_of_mk_le_mk hle hO

end ClosureStability

/-! ### Minimality of the zero orbit and closure decomposition -/

section Decomposition

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **The zero orbit lies in the closure of every nilpotent orbit.** -/
theorem mk_zero_le_of_mem_nilpotentOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) :
    Comodule.VectorOrbit.mk (0 : 𝔤) ≤ O := by
  induction O using Comodule.VectorOrbit.ind with | h e
  rw [mem_nilpotentOrbits_mk_iff] at hO
  exact Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul fun c ↦
    mk_smul_eq_of_isNilpotent_ad hO c

/-- Only finitely many orbits lie below a nilpotent orbit in the closure order. -/
theorem finite_lower_nilpotentOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) :
    {O' : Comodule.VectorOrbit k H 𝔤 | O' ≤ O}.Finite :=
  (finite_nilpotentOrbits k H).subset fun _ hle ↦ mem_nilpotentOrbits_of_le hle hO

/-- **Orbit closure decomposition of a nilpotent orbit.** In the affine chart `U = {t ≠ 0}` of the
projective completion `P(𝔤 × k)`, the closure of a nilpotent orbit `O` is the finite union of the
geometric orbit images of all orbits `O' ≤ O`, as a full set of scheme points (including nonclosed
points). No connectedness hypothesis on `G` is needed. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) :
    closure O.image ∩
        (Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : Comodule.VectorOrbit k H 𝔤 | O' ≤ O}, O'.image := by
  -- Both sides are constructible in the Noetherian Jacobson space `P(𝔤 × k)`, so it suffices to
  -- check that they have the same closed points.
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k))
  let U : Set (Proj 𝒜) :=
    (Proj.basicOpen 𝒜 (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _)
  have hU_open : IsOpen U := (Proj.basicOpen 𝒜 _).isOpen
  have hU_cons : IsConstructible U :=
    IsRetrocompact.isConstructible hU_open fun _ _ _ ↦ NoetherianSpace.isCompact _
  have hcl_cons : IsConstructible (closure O.image) :=
    (IsRetrocompact.isConstructible isClosed_closure.isOpen_compl
      fun _ _ _ ↦ NoetherianSpace.isCompact _).of_compl
  have hlhs_cons : IsConstructible (closure O.image ∩ U) := hcl_cons.inter hU_cons
  have hrhs_cons :
      IsConstructible (⋃ O' ∈ {O' : Comodule.VectorOrbit k H 𝔤 | O' ≤ O}, O'.image) := by
    refine IsConstructible.biUnion (finite_lower_nilpotentOrbits hO) fun O' _ ↦ ?_
    induction O' using Comodule.VectorOrbit.ind with | h v
    rw [Comodule.VectorOrbit.image_mk]
    exact Comodule.isConstructible_range_projectiveOrbitMap _ _
  refine (hlhs_cons.eq_iff_inter_closedPoints_eq hrhs_cons).mpr (Set.Subset.antisymm ?_ ?_)
  · -- Forward inclusion: rescale a closed point `[(v, c)] ∈ U` to `[(c⁻¹ • v, 1)]`.
    rintro x ⟨⟨hxcl, hxU⟩, hxc⟩
    obtain ⟨⟨v, c⟩, hvc, rfl⟩ :=
      (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) x).mp hxc
    have hc0 : c ≠ 0 := by
      have hnot : SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k) ∉
          (Comodule.projectiveOrbitMap (H := H) ((v, c) : 𝔤 × k) hvc
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))).asHomogeneousIdeal := hxU
      have hiff := Comodule.ι_mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((v, c) : 𝔤 × k) hvc
        1 (LinearMap.snd k 𝔤 k)
      simpa [AlgHom.convOne_def] using hiff.not.mp hnot
    let y : 𝔤 := c⁻¹ • v
    have hspan : k ∙ ((v, c) : 𝔤 × k) = k ∙ ((y, 1) : 𝔤 × k) := by
      refine Submodule.span_singleton_eq_span_singleton.mpr ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), ?_⟩
      ext <;> simp [y, Units.smul_def, inv_mul_cancel₀ hc0]
    have hpt : Comodule.projectiveOrbitMap (H := H) ((v, c) : 𝔤 × k) hvc
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) =
        Comodule.projectiveOrbitMap (H := H) ((y, 1) : 𝔤 × k) (Module.isUnimodular_mk_one y)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
      have hiff := Comodule.projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H)
        ((v, c) : 𝔤 × k) hvc ((y, 1) : 𝔤 × k) (Module.isUnimodular_mk_one y) 1 1
      simp only [map_one, one_apply_eq_self] at hiff
      simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at hiff
      exact hiff.mpr hspan
    have hle : (Comodule.VectorOrbit.mk y : Comodule.VectorOrbit k H 𝔤) ≤ O := by
      induction O using Comodule.VectorOrbit.ind with | h e
      rw [Comodule.VectorOrbit.mk_le_mk_iff]
      rw [Comodule.VectorOrbit.image_mk] at hxcl
      rwa [hpt] at hxcl
    refine ⟨?_, hxc⟩
    rw [Set.mem_iUnion₂]
    refine ⟨Comodule.VectorOrbit.mk y, hle, ?_⟩
    rw [hpt, Comodule.VectorOrbit.image_mk]
    exact Set.mem_range_self _
  · -- Reverse inclusion: every `O' ≤ O` lies in both `closure O.image` and the chart `U`.
    rintro x ⟨hx, hxc⟩
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨O', hle, hxO'⟩ := hx
    refine ⟨⟨Comodule.VectorOrbit.le_iff_image_subset_closure.mp hle hxO', ?_⟩, hxc⟩
    induction O' using Comodule.VectorOrbit.ind with | h v
    rw [Comodule.VectorOrbit.image_mk] at hxO'
    exact Comodule.range_projectiveOrbitMap_subset_basicOpen_snd v hxO'

/-- **Boundary decomposition of a nilpotent orbit.** In the affine chart `U = {t ≠ 0}` of
`P(𝔤 × k)`, the boundary `(closure O.image \ O.image) ∩ U` of a nilpotent orbit `O` is the finite
union of the geometric orbit images of all strictly smaller orbits `O' < O`, as a full set of
scheme points. -/
theorem closure_diff_image_inter_basicOpen_snd_eq_biUnion {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) :
    (closure O.image \ O.image) ∩
        (Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : Comodule.VectorOrbit k H 𝔤 | O' < O}, O'.image := by
  rw [Set.sdiff_eq, Set.inter_right_comm, ← Set.sdiff_eq,
    closure_image_inter_basicOpen_snd_eq_biUnion hO]
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨⟨O', hle, hxO'⟩, hxO⟩
    refine ⟨O', lt_of_le_of_ne hle ?_, hxO'⟩
    rintro rfl
    exact hxO hxO'
  · rintro ⟨O', hlt, hxO'⟩
    exact ⟨⟨O', hlt.le, hxO'⟩,
      Set.disjoint_left.mp (Comodule.VectorOrbit.disjoint_image_of_ne hlt.ne) hxO'⟩

end Decomposition

end TauCeti
