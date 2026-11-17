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

For a finite-type affine group `G = Spec H` over an algebraically closed field `k` of
characteristic zero, with Lie algebra `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)`, this file
proves (without connectedness):

* Closure stability of `ad`-nilpotence (`isNilpotent_ad_of_mk_le_mk`, `mem_nilpotentOrbits_of_le`).
* Under `IsKilling k 𝔤`: minimality of the zero orbit (`mk_zero_le_of_mem_nilpotentOrbits`),
  finiteness of lower ideals (`finite_lower_nilpotentOrbits`), and scheme-point closure/boundary
  decompositions in the affine chart `{t ≠ 0}` of `P(𝔤 × k)`
  (`closure_image_inter_basicOpen_snd_eq_biUnion`,
  `closure_diff_image_inter_basicOpen_snd_eq_biUnion`).

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, 1993, §6.2;
  J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Birkhäuser, 2004, §8.
-/

public section

open AlgebraicGeometry LieAlgebra TopologicalSpace Topology WithConv

namespace TauCeti

open Comodule

universe u

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-! ### Closure stability of the nilpotent locus -/

/-- **Closure stability of `ad`-nilpotence.** For any finite-type affine group over an algebraically
closed char-0 field (no semisimplicity or connectedness needed), `mk y ≤ mk x` and nilpotent
`ad x` imply nilpotent `ad y`. -/
theorem isNilpotent_ad_of_mk_le_mk {x y : 𝔤}
    (hle : (VectorOrbit.mk y : VectorOrbit k H 𝔤) ≤ VectorOrbit.mk x)
    (hx : IsNilpotent (ad k 𝔤 x)) :
    IsNilpotent (ad k 𝔤 y) := by
  refine LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero.mpr fun m hm ↦ ?_
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k))
  let π := (LinearMap.fst k 𝔤 k).dualMap
  let P := SymmetricAlgebra.map k π (tracePowerPolynomial k 𝔤 𝔤 m)
  have hP_hom : P ∈ 𝒜 m :=
    TauCeti.SymmetricAlgebra.map_mem_homogeneousSubmodule π
      (tracePowerPolynomial_mem_homogeneousSubmodule (R := k) (L := 𝔤) (M := 𝔤) m)
  have hP_eval (v : 𝔤) :
      SymmetricAlgebra.lift (Module.Dual.eval k (𝔤 × k) (v, (1 : k))) P =
        LinearMap.trace k 𝔤 (ad k 𝔤 v ^ m) := by
    have hcomp : (SymmetricAlgebra.lift (Module.Dual.eval k (𝔤 × k) (v, (1 : k)))).comp
        (SymmetricAlgebra.map k π) = SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 v) :=
      SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ by simp [π]
    exact (AlgHom.congr_fun hcomp _).trans
      (lift_eval_tracePowerPolynomial (R := k) (L := 𝔤) (M := 𝔤) v m)
  let Z : Set (Proj 𝒜) := (Proj.basicOpen 𝒜 P : Set (Proj 𝒜))ᶜ
  have hclosed : Set.range (projectiveOrbitMap (H := H) ((x, 1) : 𝔤 × k)
      (Module.isUnimodular_mk_one x)) ∩ closedPoints (Proj 𝒜) ⊆ Z := by
    rw [← range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints]
    rintro _ ⟨g, rfl⟩
    simp only [Z, Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not]
    rw [mem_projectiveOrbitMap_kernelPoint_iff _ _ g hP_hom,
      basePointsRepresentation_prodTrivial, hP_eval]
    exact LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero.mp
      ((isNilpotent_ad_basePointsRepresentation_iff g x).mpr hx) m hm
  have hyZ : projectiveOrbitMap (H := H) ((y, 1) : 𝔤 × k) (Module.isUnimodular_mk_one y)
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z := by
    have hsub : closure (Set.range (projectiveOrbitMap (H := H) ((x, 1) : 𝔤 × k)
        (Module.isUnimodular_mk_one x))) ⊆ Z := by
      rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure
        (isLocallyClosed_range_projectiveOrbitMap _ _)]
      exact (Proj.basicOpen 𝒜 P).isOpen.isClosed_compl.closure_subset_iff.mpr hclosed
    exact hsub (VectorOrbit.mk_le_mk_iff.mp hle)
  simp only [Z, Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not] at hyZ
  have hiff := mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((y, 1) : 𝔤 × k)
    (Module.isUnimodular_mk_one y) 1 hP_hom
  simp only [map_one, one_apply_eq_self] at hiff
  simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp, hP_eval] at hiff
  exact hiff.mp hyZ

/-- Any orbit lying below a nilpotent orbit in the closure order is again nilpotent. -/
theorem mem_nilpotentOrbits_of_le {O O' : VectorOrbit k H 𝔤}
    (hle : O' ≤ O) (hO : O ∈ nilpotentOrbits k H) : O' ∈ nilpotentOrbits k H := by
  induction O using VectorOrbit.ind with | h x
  induction O' using VectorOrbit.ind with | h y
  rw [mem_nilpotentOrbits_mk_iff] at hO ⊢
  exact isNilpotent_ad_of_mk_le_mk hle hO

/-! ### Minimality of the zero orbit and closure decomposition -/

section Decomposition

variable [IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **The zero orbit lies in the closure of every nilpotent orbit.** -/
theorem mk_zero_le_of_mem_nilpotentOrbits {O : VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) : VectorOrbit.mk (0 : 𝔤) ≤ O := by
  induction O using VectorOrbit.ind with | h e
  exact VectorOrbit.mk_zero_le_mk_of_forall_smul fun c ↦
    mk_smul_eq_of_isNilpotent_ad (mem_nilpotentOrbits_mk_iff.mp hO) c

/-- Only finitely many orbits lie below a nilpotent orbit in the closure order. -/
theorem finite_lower_nilpotentOrbits {O : VectorOrbit k H 𝔤} (hO : O ∈ nilpotentOrbits k H) :
    {O' : VectorOrbit k H 𝔤 | O' ≤ O}.Finite :=
  (finite_nilpotentOrbits k H).subset fun _ hle ↦ mem_nilpotentOrbits_of_le hle hO

/-- **Orbit closure decomposition of a nilpotent orbit.** In the affine chart `U = {t ≠ 0}` of
`P(𝔤 × k)`, the closure of a nilpotent orbit `O` is the finite union of the geometric orbit images
of all orbits `O' ≤ O`, as a full set of scheme points. No connectedness hypothesis is needed. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion {O : VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) :
    closure O.image ∩
        (Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H 𝔤 | O' ≤ O}, O'.image := by
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k))
  let U : Set (Proj 𝒜) :=
    (Proj.basicOpen 𝒜 (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _)
  have hlhs_cons : IsConstructible (closure O.image ∩ U) :=
    (IsRetrocompact.isConstructible isClosed_closure.isOpen_compl
      fun _ _ _ ↦ NoetherianSpace.isCompact _).of_compl.inter
      (IsRetrocompact.isConstructible (Proj.basicOpen 𝒜 _).isOpen
        fun _ _ _ ↦ NoetherianSpace.isCompact _)
  have hrhs_cons : IsConstructible (⋃ O' ∈ {O' : VectorOrbit k H 𝔤 | O' ≤ O}, O'.image) :=
    IsConstructible.biUnion (finite_lower_nilpotentOrbits hO) fun O' _ ↦ by
      induction O' using VectorOrbit.ind with | h v
      rw [VectorOrbit.image_mk]
      exact isConstructible_range_projectiveOrbitMap _ _
  refine (hlhs_cons.eq_iff_inter_closedPoints_eq hrhs_cons).mpr (Set.Subset.antisymm ?_ ?_)
  · rintro x ⟨⟨hxcl, hxU⟩, hxc⟩
    obtain ⟨⟨v, c⟩, hvc, rfl⟩ :=
      (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) x).mp hxc
    have hc0 : c ≠ 0 := by
      have hiff := ι_mem_projectiveOrbitMap_kernelPoint_iff (H := H) ((v, c) : 𝔤 × k) hvc
        1 (LinearMap.snd k 𝔤 k)
      simpa [AlgHom.convOne_def] using hiff.not.mp hxU
    let y : 𝔤 := c⁻¹ • v
    have hspan : k ∙ ((v, c) : 𝔤 × k) = k ∙ ((y, 1) : 𝔤 × k) :=
      Submodule.span_singleton_eq_span_singleton.mpr ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), by
        ext <;> simp [y, Units.smul_def, inv_mul_cancel₀ hc0]⟩
    have hpt : projectiveOrbitMap (H := H) ((v, c) : 𝔤 × k) hvc
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) =
        projectiveOrbitMap (H := H) ((y, 1) : 𝔤 × k) (Module.isUnimodular_mk_one y)
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
      have hiff := projectiveOrbitMap_kernelPoint_eq_iff_span_eq (H := H) ((v, c) : 𝔤 × k) hvc
        ((y, 1) : 𝔤 × k) (Module.isUnimodular_mk_one y) 1 1
      simp only [map_one, one_apply_eq_self] at hiff
      simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at hiff
      exact hiff.mpr hspan
    have hle : (VectorOrbit.mk y : VectorOrbit k H 𝔤) ≤ O := by
      induction O using VectorOrbit.ind with | h e
      rw [VectorOrbit.image_mk] at hxcl
      rwa [VectorOrbit.mk_le_mk_iff, ← hpt]
    refine ⟨Set.mem_iUnion₂.mpr ⟨VectorOrbit.mk y, hle, ?_⟩, hxc⟩
    rw [hpt, VectorOrbit.image_mk]
    exact Set.mem_range_self _
  · rintro x ⟨hx, hxc⟩
    obtain ⟨O', hle, hxO'⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨⟨VectorOrbit.le_iff_image_subset_closure.mp hle hxO', ?_⟩, hxc⟩
    induction O' using VectorOrbit.ind with | h v
    rw [VectorOrbit.image_mk] at hxO'
    exact range_projectiveOrbitMap_subset_basicOpen_snd v hxO'

/-- **Boundary decomposition of a nilpotent orbit.** In the affine chart `U = {t ≠ 0}` of
`P(𝔤 × k)`, the boundary `(closure O.image \ O.image) ∩ U` of a nilpotent orbit `O` is the finite
union of the geometric orbit images of all strictly smaller orbits `O' < O`. -/
theorem closure_diff_image_inter_basicOpen_snd_eq_biUnion {O : VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentOrbits k H) :
    (closure O.image \ O.image) ∩
        (Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : VectorOrbit k H 𝔤 | O' < O}, O'.image := by
  rw [Set.sdiff_eq, Set.inter_right_comm, ← Set.sdiff_eq,
    closure_image_inter_basicOpen_snd_eq_biUnion hO]
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨fun ⟨⟨O', hle, hxO'⟩, hxO⟩ ↦ ⟨O', lt_of_le_of_ne hle (fun h ↦ hxO (h ▸ hxO')), hxO'⟩,
    fun ⟨O', hlt, hxO'⟩ ↦ ⟨⟨O', hlt.le, hxO'⟩,
      Set.disjoint_left.mp (VectorOrbit.disjoint_image_of_ne hlt.ne) hxO'⟩⟩

end Decomposition

end TauCeti
