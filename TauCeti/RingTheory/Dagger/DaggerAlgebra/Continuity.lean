/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.Map
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.Topology.Algebra.Ring.Basic

import TauCeti.RingTheory.Dagger.QuotientCompletion

/-!
# The canonical affinoid topology and automatic continuity for dagger algebras

Let `K` be an ultrametric normed field and `A` a `K`-dagger algebra. Pulling back the quotient
Gauss norm topology of the completion `completion K A` along `toCompletion K A : A → completion K A`
defines a topological `K`-algebra topology `TauCeti.Dagger.affinoidTopology K A` on `A`.

When `K` is nontrivially normed and complete:
1. `toCompletion K A` is a topological embedding (`TauCeti.Dagger.isEmbedding_toCompletion`),
   and `affinoidTopology K A` coincides with the metric topology of the residue norm
   `TauCeti.Dagger.residueNormedCommRing K A` (`TauCeti.Dagger.affinoidTopology_eq_residueNorm`).
   In particular `(A, affinoidTopology K A)` is a Hausdorff Tate ring in which every ideal is
   closed.
2. **Automatic continuity** (`TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom_affinoidTopology`,
   `TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom`,
   `TauCeti.Dagger.IsDaggerAlgebra.exists_norm_map_le`): every `K`-algebra homomorphism `A →ₐ[K] B`
   between dagger algebras is continuous (and bounded for the residue norms), because its induced
   map `completion.map φ` between completely normed affinoid completions is automatically
   continuous.
3. **Presentation-independence** (`TauCeti.Dagger.affinoidTopology_eq_induced_quotient`): for *any*
   surjective overconvergent presentation `π : W_σ ↠ A`, `affinoidTopology K A` is the topology
   transported from the quotient Gauss norm on `W_σ ⧸ ker π`. On `W_σ` itself it is the unit Gauss
   norm topology (`TauCeti.Dagger.affinoidTopology_washnitzerAlgebra`), and on `K` it is the given
   norm topology (`TauCeti.Dagger.affinoidTopology_self`).

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 and Theorem 1.7.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.3.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

namespace completion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The canonical isomorphism `presentationAlgEquiv` is a topological `K`-algebra isomorphism for
the quotient Gauss norms. -/
noncomputable def presentationContinuousAlgEquiv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    completion K A ≃A[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸
        (RingHom.ker π).map (washnitzerAlgebra.toTate σ K) :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A)
    (B := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸
      (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
    (isAffinoidAlgebra_tate.quotient _) (presentationAlgEquiv π hπ)

@[simp]
theorem coe_presentationContinuousAlgEquiv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    ⇑(presentationContinuousAlgEquiv π hπ) = ⇑(presentationAlgEquiv π hπ) :=
  IsAffinoidAlgebra.coe_toContinuousAlgEquiv _ _

@[simp]
theorem toAlgEquiv_presentationContinuousAlgEquiv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    (presentationContinuousAlgEquiv π hπ).toAlgEquiv = presentationAlgEquiv π hπ :=
  IsAffinoidAlgebra.toAlgEquiv_toContinuousAlgEquiv _ _

variable (K) in
/-- `washnitzerAlgEquiv` is a topological `K`-algebra isomorphism for the quotient Gauss norm on
`completion K (washnitzerAlgebra σ K)` and the unit Gauss norm on `T_σ`. -/
noncomputable def washnitzerContinuousAlgEquiv (σ : Type*) [Finite σ] :
    completion K (washnitzerAlgebra σ K) ≃A[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
    (A := completion K (washnitzerAlgebra σ K))
    (B := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)))
    isAffinoidAlgebra_tate (washnitzerAlgEquiv K σ)

@[simp]
theorem coe_washnitzerContinuousAlgEquiv {σ : Type*} [Finite σ] :
    ⇑(washnitzerContinuousAlgEquiv K σ) = ⇑(washnitzerAlgEquiv K σ) :=
  IsAffinoidAlgebra.coe_toContinuousAlgEquiv _ _

@[simp]
theorem toAlgEquiv_washnitzerContinuousAlgEquiv {σ : Type*} [Finite σ] :
    (washnitzerContinuousAlgEquiv K σ).toAlgEquiv = washnitzerAlgEquiv K σ :=
  IsAffinoidAlgebra.toAlgEquiv_toContinuousAlgEquiv _ _

variable (K) in
/-- **Topological `K`-algebra isomorphism between `completion K (washnitzerAlgebra (Fin n) K)` and
Huber's completed Tate algebra** `Huber.restrictedMvPowerSeriesCompletion n K`. -/
noncomputable def restrictedMvPowerSeriesCompletionContinuousAlgEquiv (n : ℕ) :
    completion K (washnitzerAlgebra (Fin n) K) ≃A[K]
      Huber.restrictedMvPowerSeriesCompletion n K :=
  (washnitzerContinuousAlgEquiv K (Fin n)).trans
    { (Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)).symm with
      continuous_toFun := by
        simpa using Huber.continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm
          (n := n) (R := K)
      continuous_invFun := by
        simpa using Huber.continuous_restrictedMvPowerSeriesCompletionGaussEquiv
          (n := n) (R := K) }

@[simp]
theorem toAlgEquiv_restrictedMvPowerSeriesCompletionContinuousAlgEquiv (n : ℕ) :
    (restrictedMvPowerSeriesCompletionContinuousAlgEquiv K n).toAlgEquiv =
      restrictedMvPowerSeriesCompletionAlgEquiv K n := by
  ext x
  rw [restrictedMvPowerSeriesCompletionAlgEquiv_apply]
  exact congrArg (Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)).symm
    (congrFun (coe_washnitzerContinuousAlgEquiv (K := K) (σ := Fin n)) x)

@[simp]
theorem coe_restrictedMvPowerSeriesCompletionContinuousAlgEquiv (n : ℕ) :
    ⇑(restrictedMvPowerSeriesCompletionContinuousAlgEquiv K n) =
      ⇑(restrictedMvPowerSeriesCompletionAlgEquiv K n) :=
  congrArg DFunLike.coe (toAlgEquiv_restrictedMvPowerSeriesCompletionContinuousAlgEquiv n)

end completion

section General

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **The canonical affinoid topology on a dagger algebra**: the topology induced from its
completion `completion K A` along `toCompletion K A`. Over a complete nontrivially normed
ultrametric field it coincides with the topology of the residue norm of every surjective
overconvergent presentation (`TauCeti.Dagger.affinoidTopology_eq_induced_quotient`), and every
`K`-algebra homomorphism of dagger algebras is continuous for it
(`TauCeti.Dagger.IsDaggerAlgebra.continuous_algHom_affinoidTopology`). It is a `def` rather than a
global instance because algebras such as `K` and `washnitzerAlgebra σ K` already carry topologies
from other sources (with which it agrees definitionally or propositionally). -/
@[instance_reducible]
noncomputable def affinoidTopology : TopologicalSpace A :=
  TopologicalSpace.induced (toCompletion K A) inferInstance

/-- The completion map `toCompletion K A` is inducing for `affinoidTopology K A`. -/
theorem isInducing_toCompletion_affinoidTopology :
    letI := affinoidTopology K A
    Topology.IsInducing (toCompletion K A) :=
  letI := affinoidTopology K A
  ⟨rfl⟩

/-- The completion map `toCompletion K A` is continuous for `affinoidTopology K A`. -/
theorem continuous_toCompletion_affinoidTopology :
    letI := affinoidTopology K A
    Continuous (toCompletion K A) :=
  letI := affinoidTopology K A
  (isInducing_toCompletion_affinoidTopology K A).continuous

/-- Equipped with `affinoidTopology K A`, a dagger algebra is a topological ring. -/
theorem isTopologicalRing_affinoidTopology :
    letI := affinoidTopology K A
    IsTopologicalRing A :=
  TauCeti.isTopologicalRing_induced (toCompletion K A)

/-- The structure map `algebraMap K A` is continuous for `affinoidTopology K A`. -/
theorem continuous_algebraMap_affinoidTopology :
    letI := affinoidTopology K A
    Continuous (algebraMap K A) :=
  letI := affinoidTopology K A
  continuous_induced_rng.mpr <| by
    have h : ⇑(toCompletion K A) ∘ ⇑(algebraMap K A) =
        ⇑(Ideal.Quotient.mk _) ∘ ⇑(algebraMap K
          (IsRestricted.subring (R := K) (fun _ : Fin (presentationDim K A) ↦ (1 : ℝ)))) :=
      funext fun c ↦ (toCompletion K A).commutes c
    rw [h]
    exact continuous_quot_mk.comp (continuous_algebraMap K _)

/-- Scalar multiplication by `K` on `A` is jointly continuous for `affinoidTopology K A`. -/
theorem continuousSMul_affinoidTopology :
    letI := affinoidTopology K A
    ContinuousSMul K A :=
  letI := affinoidTopology K A
  letI := isTopologicalRing_affinoidTopology K A
  ⟨by
    simp_rw [Algebra.smul_def]
    exact ((continuous_algebraMap_affinoidTopology K A).comp continuous_fst).mul continuous_snd⟩

end General

section Complete

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : Type*) [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- The affinoid topology on `A` agrees with the metric topology of the residue norm
`residueNormedCommRing K A`. -/
theorem affinoidTopology_eq_residueNorm :
    affinoidTopology K A = (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace := by
  let _ := residueNormedCommRing K A
  exact (isometry_toCompletion K A).isUniformInducing.isInducing.eq_induced.symm

/-- For `affinoidTopology K A`, the completion map `toCompletion K A` is a topological embedding
with dense range. -/
theorem isEmbedding_toCompletion :
    letI := affinoidTopology K A
    Topology.IsEmbedding (toCompletion K A) :=
  letI := affinoidTopology K A
  ⟨isInducing_toCompletion_affinoidTopology K A, toCompletion_injective (K := K) (A := A)⟩

/-- Every dagger algebra over a complete nontrivially normed ultrametric field is Hausdorff in its
canonical affinoid topology (including nonreduced dagger algebras). -/
theorem t2Space_affinoidTopology :
    letI := affinoidTopology K A
    T2Space A :=
  letI := affinoidTopology K A
  (isEmbedding_toCompletion K A).t2Space

/-- Equipped with `affinoidTopology K A`, every `K`-dagger algebra is a Tate ring. -/
theorem isTateRing_affinoidTopology :
    letI := affinoidTopology K A
    letI := isTopologicalRing_affinoidTopology K A
    Huber.IsTateRing A := by
  have htate : @Huber.IsTateRing A _
      (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace
      (let _ := residueNormedCommRing K A; inferInstance) := by
    let _ := residueNormedCommRing K A
    let _ := residueNormedAlgebra K A
    have _ := isUltrametricDist_residueNormedCommRing K A
    exact Huber.IsTateRing.of_normedAlgebra K A
  have h : ∀ (t : TopologicalSpace A) (htr : @IsTopologicalRing A t _),
      t = (residueNormedCommRing K A).toUniformSpace.toTopologicalSpace →
      @Huber.IsTateRing A _ t htr := by
    rintro _ _ rfl
    exact htate
  exact h (affinoidTopology K A) (isTopologicalRing_affinoidTopology K A)
    (affinoidTopology_eq_residueNorm K A)

/-- Every ideal of a dagger algebra is closed in `affinoidTopology K A`. -/
theorem isClosed_ideal_affinoidTopology (J : Ideal A) :
    letI := affinoidTopology K A
    IsClosed (J : Set A) :=
  letI := affinoidTopology K A
  by
    have hpre : (J : Set A) =
        toCompletion K A ⁻¹' (J.map (toCompletion K A) : Set (completion K A)) := by
      ext a
      exact (Ideal.mem_comap.symm.trans
        (by rw [comap_map_toCompletion (K := K) (A := A) J])).symm
    rw [hpre]
    have hcl : IsClosed (J.map (toCompletion K A) : Set (completion K A)) :=
      IsAffinoidAlgebra.isClosed_ideal (K := K) (A := completion K A)
        isAffinoidAlgebra_completion _
    exact hcl.preimage (continuous_toCompletion_affinoidTopology K A)

namespace IsDaggerAlgebra

variable {K A}
variable {B : Type*} [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

variable (K) in
/-- **Automatic continuity for `affinoidTopology`.** Every `K`-algebra homomorphism between
`K`-dagger algebras is continuous for their canonical affinoid topologies. -/
theorem continuous_algHom_affinoidTopology (φ : A →ₐ[K] B) :
    letI := affinoidTopology K A
    letI := affinoidTopology K B
    Continuous φ :=
  letI := affinoidTopology K A
  letI := affinoidTopology K B
  continuous_induced_rng.mpr <| by
    have hcomp : ⇑(toCompletion K B) ∘ ⇑φ = ⇑(completion.map φ) ∘ ⇑(toCompletion K A) :=
      funext fun a ↦ (completion.map_toCompletion φ a).symm
    rw [hcomp]
    exact (completion.continuous_map φ).comp (continuous_toCompletion_affinoidTopology K A)

variable (K) in
/-- **Automatic continuity for the residue norms.** Every `K`-algebra homomorphism between
`K`-dagger algebras is continuous with respect to their residue norms. -/
theorem continuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Continuous φ :=
  letI := residueNormedCommRing K A
  letI := residueNormedCommRing K B
  (isometry_toCompletion K B).isUniformInducing.isInducing.continuous_iff.mpr <| by
    have hcomp : ⇑(toCompletion K B) ∘ ⇑φ = ⇑(completion.map φ) ∘ ⇑(toCompletion K A) :=
      funext fun a ↦ (completion.map_toCompletion φ a).symm
    rw [hcomp]
    exact (completion.continuous_map φ).comp (isometry_toCompletion K A).continuous

variable (K) in
/-- **Boundedness of `K`-algebra homomorphisms for residue norms.** Every `K`-algebra homomorphism
`φ : A →ₐ[K] B` of dagger algebras satisfies `‖φ a‖ ≤ C * ‖a‖` for some `C > 0`. -/
theorem exists_norm_map_le (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedAlgebra K A
    letI := residueNormedCommRing K B
    letI := residueNormedAlgebra K B
    ∃ C > 0, ∀ a : A, ‖φ a‖ ≤ C * ‖a‖ :=
  letI := residueNormedCommRing K A
  letI := residueNormedAlgebra K A
  letI := residueNormedCommRing K B
  letI := residueNormedAlgebra K B
  let L : A →L[K] B := { φ.toLinearMap with cont := continuous_algHom K φ }
  L.isBoundedLinearMap.bound

variable (K) in
/-- Every `K`-algebra isomorphism of dagger algebras is a topological `K`-algebra isomorphism for
their canonical affinoid topologies. -/
noncomputable def toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := affinoidTopology K A
    letI := affinoidTopology K B
    A ≃A[K] B :=
  letI := affinoidTopology K A
  letI := affinoidTopology K B
  { e with
    continuous_toFun := continuous_algHom_affinoidTopology K e.toAlgHom
    continuous_invFun := continuous_algHom_affinoidTopology K e.symm.toAlgHom }

@[simp]
theorem coe_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := affinoidTopology K A
    letI := affinoidTopology K B
    ⇑(toContinuousAlgEquiv K e) = ⇑e := by rfl

@[simp]
theorem toAlgEquiv_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := affinoidTopology K A
    letI := affinoidTopology K B
    (toContinuousAlgEquiv K e).toAlgEquiv = e := by rfl

end IsDaggerAlgebra

section PresentationIndependence

variable {K A}

/-- **Presentation-independence of `affinoidTopology`.** For *any* surjective overconvergent
presentation `π : W_σ ↠ A`, `affinoidTopology K A` agrees with the topology pulled back from the
quotient Gauss norm on `W_σ ⧸ ker π` along the first isomorphism theorem. -/
theorem affinoidTopology_eq_induced_quotient {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    affinoidTopology K A =
      TopologicalSpace.induced (Ideal.quotientKerAlgEquivOfSurjective hπ).symm inferInstance := by
  let I := RingHom.ker π
  let q := Ideal.quotientMapₐ (I.map (washnitzerAlgebra.toTate σ K))
    (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map
  have hsq : ⇑(completion.presentationContinuousAlgEquiv π hπ) ∘ ⇑(toCompletion K A) =
      ⇑q ∘ ⇑(Ideal.quotientKerAlgEquivOfSurjective hπ).symm := by
    funext a
    obtain ⟨f, rfl⟩ := hπ a
    rw [Function.comp_apply, completion.coe_presentationContinuousAlgEquiv,
      completion.presentationAlgEquiv_toCompletion_apply, Function.comp_apply,
      ← Ideal.quotientKerAlgEquivOfSurjective_mk hπ f, AlgEquiv.symm_apply_apply]
    rfl
  have hq_ind : Topology.IsInducing q := I.isometry_quotientMap_toTate.isUniformInducing.isInducing
  calc affinoidTopology K A
      = TopologicalSpace.induced (toCompletion K A)
          (TopologicalSpace.induced (completion.presentationContinuousAlgEquiv π hπ)
            inferInstance) :=
        congrArg (TopologicalSpace.induced (toCompletion K A))
          (completion.presentationContinuousAlgEquiv π hπ).toHomeomorph.isInducing.eq_induced
    _ = TopologicalSpace.induced
          (⇑(completion.presentationContinuousAlgEquiv π hπ) ∘ ⇑(toCompletion K A))
          inferInstance := induced_compose
    _ = TopologicalSpace.induced
          (⇑q ∘ ⇑(Ideal.quotientKerAlgEquivOfSurjective hπ).symm) inferInstance := by
        rw [hsq]
    _ = TopologicalSpace.induced (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
          (TopologicalSpace.induced q inferInstance) := induced_compose.symm
    _ = TopologicalSpace.induced (Ideal.quotientKerAlgEquivOfSurjective hπ).symm inferInstance :=
        congrArg (TopologicalSpace.induced (Ideal.quotientKerAlgEquivOfSurjective hπ).symm)
          hq_ind.eq_induced.symm

/-- On the Monsky–Washnitzer algebra `K⟨X₁, …, Xₙ⟩†`, `affinoidTopology` agrees with the unit Gauss
norm topology. -/
theorem affinoidTopology_washnitzerAlgebra (σ : Type*) [Finite σ] :
    affinoidTopology K (washnitzerAlgebra σ K) =
      (inferInstance : TopologicalSpace (washnitzerAlgebra σ K)) := by
  have hsq : ⇑(completion.washnitzerContinuousAlgEquiv K σ) ∘
      ⇑(toCompletion K (washnitzerAlgebra σ K)) = ⇑(washnitzerAlgebra.toTate σ K) := by
    funext f
    rw [Function.comp_apply, completion.coe_washnitzerContinuousAlgEquiv,
      completion.washnitzerAlgEquiv_toCompletion]
  calc affinoidTopology K (washnitzerAlgebra σ K)
      = TopologicalSpace.induced (toCompletion K (washnitzerAlgebra σ K))
          (TopologicalSpace.induced (completion.washnitzerContinuousAlgEquiv K σ)
            inferInstance) :=
        congrArg (TopologicalSpace.induced (toCompletion K (washnitzerAlgebra σ K)))
          (completion.washnitzerContinuousAlgEquiv K σ).toHomeomorph.isInducing.eq_induced
    _ = TopologicalSpace.induced
          (⇑(completion.washnitzerContinuousAlgEquiv K σ) ∘
            ⇑(toCompletion K (washnitzerAlgebra σ K)))
          inferInstance := induced_compose
    _ = TopologicalSpace.induced (washnitzerAlgebra.toTate σ K) inferInstance := by
        rw [hsq]
    _ = (inferInstance : TopologicalSpace (washnitzerAlgebra σ K)) :=
        washnitzerAlgebra.isometry_toTate.isUniformInducing.isInducing.eq_induced.symm

/-- On the coefficient field `K`, `affinoidTopology K K` agrees with the given norm topology. -/
theorem affinoidTopology_self :
    affinoidTopology K K = (inferInstance : TopologicalSpace K) := by
  have hcont₁ : Continuous (toCompletion K K) := by
    have h : ⇑(toCompletion K K) =
        ⇑(Ideal.Quotient.mk _) ∘ ⇑(algebraMap K
          (IsRestricted.subring (R := K) (fun _ : Fin (presentationDim K K) ↦ (1 : ℝ)))) :=
      funext fun c ↦ (toCompletion K K).commutes c
    rw [h]
    exact continuous_quot_mk.comp (continuous_algebraMap K _)
  let r : completion K K →ₐ[K] K :=
    completion.lift (K := K) (A := K) (C := K) isAffinoidAlgebra_self (AlgHom.id K K)
  have hr : Continuous r :=
    completion.continuous_lift (K := K) (A := K) (C := K) isAffinoidAlgebra_self (AlgHom.id K K)
  have hret : ⇑r ∘ ⇑(toCompletion K K) = id :=
    funext (completion.lift_toCompletion (K := K) (A := K) (C := K)
      isAffinoidAlgebra_self (AlgHom.id K K))
  refine le_antisymm ?_ (continuous_iff_le_induced.mp hcont₁)
  have hcont₂ : @Continuous K K (affinoidTopology K K) inferInstance id := by
    rw [← hret]
    exact @Continuous.comp K (completion K K) K (affinoidTopology K K) inferInstance inferInstance
      _ _ hr (continuous_toCompletion_affinoidTopology K K)
  exact @continuous_id_iff_le K (affinoidTopology K K) inferInstance |>.mp hcont₂

end PresentationIndependence

end Complete

end TauCeti.Dagger
