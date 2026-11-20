/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.NumberTheory.LocalField.Herbrand.FiniteGalois
public import TauCeti.NumberTheory.LocalField.WildInertia

import TauCeti.FieldTheory.Galois.FiberProduct
import TauCeti.NumberTheory.LocalField.Herbrand.Unramified
import TauCeti.Topology.Algebra.Group.Profinite.Limit
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# The absolute upper ramification filtration of a local field

For a finite Galois extension `M/K` of nonarchimedean local fields, Herbrand's theorem in the upper
numbering (`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`) says
that restriction along a Galois subextension `L/K` maps `Gal(M/K)^v` onto `Gal(L/K)^v` for every
`v ≥ -1`. Unlike the lower numbering, the upper numbering therefore forms an inverse system over
all finite Galois subextensions of an algebraic closure `AlgebraicClosure K` of `K`, including
nonabelian ones.

This file defines the **absolute upper ramification group**

`TauCeti.localAbsoluteUpperRamificationGroup K v : Subgroup (Field.absoluteGaloisGroup K)`

at each `v : RamificationIndexDomain = [-1, ∞)` as the intersection, over all finite Galois
intermediate fields `M` of `AlgebraicClosure K / K`, of the preimages of `Gal(M/K)^v` under
`AlgEquiv.restrictNormalHom M`, using the canonical spectral-norm local-field structure induced
from `K` (`TauCeti.LocalFieldsRamification.finiteGaloisUpperRamificationGroup`). By uniqueness of
the extended valuative relation and topology on a finite extension, the same membership condition
holds for any compatible local-field structure on any finite Galois intermediate field.

Compactness of the absolute Galois group turns Herbrand's finite-level surjectivity into
surjectivity from the inverse limit: restriction to every finite Galois subextension `L/K` maps
`G_K^v` onto `Gal(L/K)^v`. More generally, for every normal intermediate field `E` of
`AlgebraicClosure K / K`, restriction maps `G_K^v` onto the subgroup of `Gal(E/K)` cut out by the
upper ramification groups of the finite Galois intermediate fields of `E/K`.

At special values and in the limit, the filtration recovers the classical subgroups of `G_K`:

* at `v = -1` it is the whole absolute Galois group `⊤`;
* at `v = 0` it is the inertia subgroup `TauCeti.inertiaSubgroup K`;
* the topological closure of the union of `G_K^v` over `v > 0` is the wild inertia subgroup
  `TauCeti.wildInertiaSubgroup K`;
* the intersection over all `v` (and already over natural numbers `n : ℕ`) is trivial.

Finally, a continuous ring isomorphism `e : K ≃+* K'` of nonarchimedean local fields intertwines
`G_K^v` and `G_{K'}^v` along any extension `e' : AlgebraicClosure K ≃+* AlgebraicClosure K'`:
`Field.absoluteGaloisGroup.map (e : K →+* K')` (and more generally `Field.absoluteGaloisGroup.map f`
for any bijective continuous `f : K →+* K'`) pulls `G_K^v` back to `G_{K'}^v`, and
`TauCeti.absoluteGaloisGroupMapEquiv e` maps `G_{K'}^v` onto `G_K^v`.

## Main definitions

* `TauCeti.localAbsoluteUpperRamificationGroup K v`: the upper ramification subgroup `G_K^v` of
  `Field.absoluteGaloisGroup K`, for `v ∈ [-1, ∞)`.

## Main results

* `TauCeti.mem_localAbsoluteUpperRamificationGroup_iff`: `σ ∈ G_K^v` exactly when its restriction
  to every finite Galois subextension `L` lies in `Gal(L/K)^v`.
* `TauCeti.isClosed_localAbsoluteUpperRamificationGroup`,
  `TauCeti.isClosed_map_mk'_localAbsoluteUpperRamificationGroup`,
  `TauCeti.localAbsoluteUpperRamificationGroup_normal`,
  `TauCeti.localAbsoluteUpperRamificationGroup_antitone`: each `G_K^v` is closed (along with its
  image in `G_K^ab`) and normal, and the filtration is decreasing.
* `TauCeti.map_restrictNormalHom_localAbsoluteUpperRamificationGroup`,
  `TauCeti.map_restrictNormalHom_localAbsoluteUpperRamificationGroup_finiteGalois`: restriction to a
  finite Galois subextension `L/K` maps `G_K^v` onto `Gal(L/K)^v`.
* `TauCeti.localAbsoluteUpperRamificationGroup_neg_one`,
  `TauCeti.localAbsoluteUpperRamificationGroup_zero`,
  `TauCeti.topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup`,
  `TauCeti.iInf_localAbsoluteUpperRamificationGroup`: the values at `-1` and `0`, the closure of
  the positive-depth union (wild inertia), and the trivial intersection of all depths.
* `TauCeti.map_restrictNormalHom_localAbsoluteUpperRamificationGroup_eq_iInf`: restriction to
  any normal intermediate field `E/K` cuts out the inverse-limit upper filtration of `Gal(E/K)`.
* `TauCeti.mem_localAbsoluteUpperRamificationGroup_iff_of_vle_iff`,
  `TauCeti.comap_absoluteGaloisGroup_mapOfAlgebra_localAbsoluteUpperRamificationGroup`,
  `TauCeti.comap_absoluteGaloisGroup_map_localAbsoluteUpperRamificationGroup`,
  `TauCeti.map_absoluteGaloisGroupMapEquiv_localAbsoluteUpperRamificationGroup`: naturality under
  valuation-preserving and continuous field isomorphisms `K →+* K'` and `K ≃+* K'`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–3, Proposition 14.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, p. 128.
-/

public section
noncomputable section

open ValuativeRel IntermediateField Polynomial

namespace TauCeti

open LocalFieldsRamification

section Basic

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The absolute upper ramification group of a local field.** For real `v ≥ -1`, an absolute
Galois automorphism belongs to `G_K^v` precisely when its restriction to every finite Galois
intermediate field belongs to its upper ramification group, using the canonical extended valuation
(Serre, *Local Fields*, IV §3, Proposition 14). -/
def localAbsoluteUpperRamificationGroup
    (v : RamificationIndexDomain) : Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
    (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
      (AlgEquiv.restrictNormalHom M : Field.absoluteGaloisGroup K →* (M ≃ₐ[K] M))

/-- The absolute upper ramification group is the intersection, over all finite Galois intermediate
fields of `AlgebraicClosure K / K`, of the preimages of the finite upper ramification groups. -/
theorem localAbsoluteUpperRamificationGroup_def (v : RamificationIndexDomain) :
    localAbsoluteUpperRamificationGroup K v =
      ⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
          (AlgEquiv.restrictNormalHom M : Field.absoluteGaloisGroup K →* (M ≃ₐ[K] M)) :=
  (rfl)

variable {K} in
/-- Membership in `localAbsoluteUpperRamificationGroup K v` in terms of
`FiniteGaloisIntermediateField`s equipped with the canonical induced local-field structures. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K} :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      ∀ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        AlgEquiv.restrictNormal σ M ∈
          finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v := by
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  -- `Field.absoluteGaloisGroup K` is semireducible; expose `Gal(AlgebraicClosure K/K)`
  -- so `Subgroup.mem_iInf` applies.
  change σ₀ ∈
      (⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
          (AlgEquiv.restrictNormalHom M) : Subgroup Gal(AlgebraicClosure K/K)) ↔ _
  rw [Subgroup.mem_iInf]
  rfl

variable {K} in
/-- **Restriction to any compatible finite Galois subextension.** For any compatible local-field
structure on a finite Galois intermediate field `L` of `AlgebraicClosure K / K`, an element of
`localAbsoluteUpperRamificationGroup K v` restricts into `upperRamificationGroup K L v`. -/
theorem restrictNormal_mem_upperRamificationGroup
    (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    (hσ : σ ∈ localAbsoluteUpperRamificationGroup K v) :
    AlgEquiv.restrictNormal σ L ∈ upperRamificationGroup K L v := by
  have hM := mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ ⟨L⟩
  rwa [finiteGaloisUpperRamificationGroup_eq K (AlgebraicClosure K) L v] at hM

variable {K} in
/-- **Inverse-limit characterization across arbitrary compatible local-field structures.** An
automorphism `σ ∈ G_K` lies in `localAbsoluteUpperRamificationGroup K v` if and only if, for every
finite Galois subextension `L` of `AlgebraicClosure K / K` and every compatible local-field
structure on `L`, its restriction to `L` lies in `upperRamificationGroup K L v`. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K} :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      ∀ (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
        [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
        [ValuativeExtension K L],
        AlgEquiv.restrictNormal σ L ∈ upperRamificationGroup K L v := by
  refine ⟨fun hσ L _ _ _ _ _ _ ↦ restrictNormal_mem_upperRamificationGroup L hσ, fun h ↦ ?_⟩
  refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  exact h M.toIntermediateField

/-- **Every absolute upper ramification group is normal** in `Field.absoluteGaloisGroup K`. -/
instance localAbsoluteUpperRamificationGroup_normal (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).Normal := by
  rw [localAbsoluteUpperRamificationGroup_def]
  exact Subgroup.normal_iInf_normal fun M ↦
    (instNormalFiniteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap _

/-- **Every absolute upper ramification group is closed** in the Krull topology on
`Field.absoluteGaloisGroup K`. -/
theorem isClosed_localAbsoluteUpperRamificationGroup (v : RamificationIndexDomain) :
    IsClosed (localAbsoluteUpperRamificationGroup K v : Set (Field.absoluteGaloisGroup K)) := by
  -- `Field.absoluteGaloisGroup K` is semireducible; expose `Gal(AlgebraicClosure K/K)`
  -- so `Subgroup.coe_iInf` applies.
  change IsClosed (((⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v).comap
        (AlgEquiv.restrictNormalHom M) : Subgroup Gal(AlgebraicClosure K/K)) :
    Set Gal(AlgebraicClosure K/K)))
  rw [Subgroup.coe_iInf]
  refine isClosed_iInter fun M ↦ ?_
  have : T2Space (M ≃ₐ[K] M) := krullTopology_t2
  have : DiscreteTopology (M ≃ₐ[K] M) := Finite.instDiscreteTopology
  exact (isClosed_discrete _).preimage
    (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField)

/-- **The image of `localAbsoluteUpperRamificationGroup K v` in `G_K^ab` is closed**, as the
continuous image of a closed subgroup of the compact group `G_K`. -/
theorem isClosed_map_mk'_localAbsoluteUpperRamificationGroup (v : RamificationIndexDomain) :
    IsClosed
      (((localAbsoluteUpperRamificationGroup K v).map
          (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure) :
            Subgroup (Field.absoluteGaloisGroupAbelianization K)) :
        Set (Field.absoluteGaloisGroupAbelianization K)) :=
  Subgroup.isClosed_map (isClosed_localAbsoluteUpperRamificationGroup K v).isCompact _
    QuotientGroup.continuous_mk

/-- **The absolute upper ramification filtration is decreasing.** -/
theorem localAbsoluteUpperRamificationGroup_antitone :
    Antitone (localAbsoluteUpperRamificationGroup K) := by
  intro v w hvw σ hσ
  exact mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦
    finiteGaloisUpperRamificationGroup_antitone K (AlgebraicClosure K) M hvw
      (mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ M)

end Basic

/-! ### Finite-level surjectivity -/

section FiniteLevel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Compactness of `G_K` lifts any `τ ∈ Gal(E/K)` whose coset meets the preimage of `Gal(M/K)^v`
at every finite Galois level `M` to an element of `localAbsoluteUpperRamificationGroup K v`. -/
private theorem exists_mem_localAbsoluteUpperRamificationGroup_of_forall_finiteGalois
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
    {v : RamificationIndexDomain} {τ : E ≃ₐ[K] E}
    (hne : ∀ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      ∃ σ : Field.absoluteGaloisGroup K,
        AlgEquiv.restrictNormalHom E σ = τ ∧
          AlgEquiv.restrictNormalHom M.toIntermediateField σ ∈
            finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v) :
    ∃ σ ∈ localAbsoluteUpperRamificationGroup K v, AlgEquiv.restrictNormalHom E σ = τ := by
  let S : FiniteGaloisIntermediateField K (AlgebraicClosure K) →
      Set (Field.absoluteGaloisGroup K) := fun M ↦
    (AlgEquiv.restrictNormalHom E) ⁻¹' {τ} ∩
      (AlgEquiv.restrictNormalHom M.toIntermediateField) ⁻¹'
        (finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v : Set (M ≃ₐ[K] M))
  have hcl (M : FiniteGaloisIntermediateField K (AlgebraicClosure K)) : IsClosed (S M) := by
    have : T2Space (E ≃ₐ[K] E) := krullTopology_t2
    have : T2Space (M ≃ₐ[K] M) := krullTopology_t2
    have : DiscreteTopology (M ≃ₐ[K] M) := Finite.instDiscreteTopology
    exact (isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous E)).inter
      ((isClosed_discrete _).preimage
        (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField))
  have hS_ne (M : FiniteGaloisIntermediateField K (AlgebraicClosure K)) : (S M).Nonempty := by
    obtain ⟨σ, hσE, hσM⟩ := hne M
    exact ⟨σ, hσE, hσM⟩
  have hdir : Directed (· ⊇ ·) S := fun M₁ M₂ ↦
    ⟨M₁ ⊔ M₂,
      fun _ ⟨hE, hN⟩ ↦
        ⟨hE, comap_restrictNormalHom_finiteGaloisUpperRamificationGroup_antitone
          K (AlgebraicClosure K) v le_sup_left hN⟩,
      fun _ ⟨hE, hN⟩ ↦
        ⟨hE, comap_restrictNormalHom_finiteGaloisUpperRamificationGroup_antitone
          K (AlgebraicClosure K) v le_sup_right hN⟩⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hS_ne
    (fun M ↦ (hcl M).isCompact) hcl
  exact ⟨σ, mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦
    (Set.mem_iInter.1 hσ M).2, (Set.mem_iInter.1 hσ ⊥).1⟩

/-- **Absolute upper ramification groups surject onto `finiteGaloisUpperRamificationGroup`.** -/
@[simp]
theorem map_restrictNormalHom_localAbsoluteUpperRamificationGroup_finiteGalois
    (M : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).map
        (AlgEquiv.restrictNormalHom M.toIntermediateField) =
      finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) M v := by
  refine le_antisymm ?_ fun τ hτ ↦ ?_
  · rintro _ ⟨σ, hσ, rfl⟩
    exact mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ M
  · refine exists_mem_localAbsoluteUpperRamificationGroup_of_forall_finiteGalois
      M.toIntermediateField fun M' ↦ ?_
    let N : FiniteGaloisIntermediateField K (AlgebraicClosure K) := M ⊔ M'
    rw [← map_restrictNormalHom_finiteGaloisUpperRamificationGroup K (AlgebraicClosure K)
      (le_sup_left : M ≤ N) v] at hτ
    obtain ⟨ρ, hρN, hρM⟩ := hτ
    obtain ⟨σ, hσN⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) ρ
    refine ⟨σ, ?_, comap_restrictNormalHom_finiteGaloisUpperRamificationGroup_antitone
      K (AlgebraicClosure K) v (le_sup_right : M' ≤ N)
      (by rwa [Subgroup.mem_comap, hσN])⟩
    rw [← hρM, ← hσN, ← IntermediateField.restrictNormalHom_val N.toIntermediateField,
      ← IntermediateField.restrictNormalHom_val M.toIntermediateField,
      AlgHom.restrictNormalHom_restrictNormalHom]
    rfl

/-- **Absolute upper ramification groups surject onto finite upper ramification groups.** For every
compatible local-field structure on a finite Galois intermediate field `L` of
`AlgebraicClosure K / K` and every `v ≥ -1`, restriction maps
`localAbsoluteUpperRamificationGroup K v` onto `upperRamificationGroup K L v`. -/
@[simp]
theorem map_restrictNormalHom_localAbsoluteUpperRamificationGroup
    (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).map (AlgEquiv.restrictNormalHom L) =
      upperRamificationGroup K L v := by
  rw [← finiteGaloisUpperRamificationGroup_eq K (AlgebraicClosure K) L v]
  exact map_restrictNormalHom_localAbsoluteUpperRamificationGroup_finiteGalois ⟨L⟩ v

/-- Every element of a finite upper ramification group `Gal(L/K)^v` lifts to
`localAbsoluteUpperRamificationGroup K v`. -/
theorem exists_mem_localAbsoluteUpperRamificationGroup_restrictNormal_eq
    (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
    {v : RamificationIndexDomain} {τ : L ≃ₐ[K] L} (hτ : τ ∈ upperRamificationGroup K L v) :
    ∃ σ ∈ localAbsoluteUpperRamificationGroup K v, AlgEquiv.restrictNormal σ L = τ := by
  rwa [← map_restrictNormalHom_localAbsoluteUpperRamificationGroup L v] at hτ

end FiniteLevel

/-! ### Special values and limits -/

section SpecialValues

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **At `-1`, the absolute upper ramification group is the whole absolute Galois group.** -/
@[simp]
theorem localAbsoluteUpperRamificationGroup_neg_one :
    localAbsoluteUpperRamificationGroup K ⟨-1, le_rfl⟩ = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  have hv : ((⟨-1, le_rfl⟩ : RamificationIndexDomain) : ℝ) ≤ 0 := neg_nonpos.2 zero_le_one
  have hneg1 : ((⟨-1, le_rfl⟩ : RamificationIndexDomain) : ℝ) = ((-1 : ℤ) : ℝ) := by norm_num
  rw [finiteGaloisUpperRamificationGroup_def,
    upperRamificationGroup_of_coe_le_zero K M hv, hneg1, lowerRamificationGroupReal_intCast,
    lowerRamificationGroup_eq_top_of_le_neg_one K M le_rfl]
  exact Subgroup.mem_top _

/-- **At `0`, the absolute upper ramification group is the inertia subgroup `I_K`.** -/
@[simp]
theorem localAbsoluteUpperRamificationGroup_zero :
    localAbsoluteUpperRamificationGroup K ⟨0, by norm_num⟩ = inertiaSubgroup K := by
  have h0 : (0 : ℝ) = ((0 : ℤ) : ℝ) := Int.cast_zero.symm
  refine le_antisymm (fun σ hσ ↦ ?_) (fun σ hσ ↦ ?_)
  · -- Every element of `K^{ur}` lies in a finite unramified Galois subextension `L`, where
    -- `Gal(L/K)^0 = G_0(L/K)` has order `e(L/K) = 1`.
    refine mem_inertiaSubgroup_iff.2 fun x hx ↦ ?_
    obtain ⟨f, _, hxf⟩ := mem_maximalUnramifiedExtension_iff.1 hx
    let L := unramifiedExtension K (AlgebraicClosure K) f
    let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
    let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
    have : IsUnramified K L := isUnramified_unramifiedExtension
    have hσL := restrictNormal_mem_upperRamificationGroup L hσ
    rw [upperRamificationGroup_eq_bot_of_isUnramified K L le_rfl, Subgroup.mem_bot] at hσL
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, hxf⟩).symm.trans
      (by rw [hσL, AlgEquiv.one_apply]; rfl)
  · refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M ↦ ?_
    let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
    let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
      M.toIntermediateField
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
    rw [finiteGaloisUpperRamificationGroup_def,
      upperRamificationGroup_of_coe_le_zero K M (v := ⟨0, by norm_num⟩) le_rfl,
      Subtype.coe_mk, h0, lowerRamificationGroupReal_intCast]
    exact restrictNormal_mem_lowerRamificationGroup_zero M.toIntermediateField hσ

/-- For nonnegative `v`, `G_K^v` is contained in the inertia subgroup `I_K`. -/
theorem localAbsoluteUpperRamificationGroup_le_inertiaSubgroup
    {v : RamificationIndexDomain} (hv : 0 ≤ (v : ℝ)) :
    localAbsoluteUpperRamificationGroup K v ≤ inertiaSubgroup K := by
  rw [← localAbsoluteUpperRamificationGroup_zero K]
  exact localAbsoluteUpperRamificationGroup_antitone K (Subtype.mk_le_mk.2 hv)

/-- For strictly positive `v`, `G_K^v` is contained in the wild inertia subgroup `P_K`. -/
theorem localAbsoluteUpperRamificationGroup_le_wildInertiaSubgroup
    {v : RamificationIndexDomain} (hv : 0 < (v : ℝ)) :
    localAbsoluteUpperRamificationGroup K v ≤ wildInertiaSubgroup K := by
  intro σ hσ
  refine mem_wildInertiaSubgroup_iff_forall_restrictNormal_mem_finiteGaloisLowerRamificationGroup.2
    fun M ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M.toIntermediateField
  rw [finiteGaloisLowerRamificationGroup_def]
  have hσM := mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ M
  rw [finiteGaloisUpperRamificationGroup_def, upperRamificationGroup_def,
    lowerRamificationGroupReal_def] at hσM
  have hpos : 0 < (inverseHerbrand K M v : ℝ) := by
    have h0 : inverseHerbrand K M ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
      inverseHerbrand_of_coe_le_zero K M le_rfl
    have hlt := inverseHerbrand_strictMono K M (a := ⟨0, by norm_num⟩) (b := v) hv
    rwa [h0] at hlt
  have h0lt : (0 : ℤ) < ⌈(inverseHerbrand K M v : ℝ)⌉ :=
    Int.lt_ceil.2 (by rwa [Int.cast_zero])
  exact lowerRamificationGroup_antitone K M (by omega : (1 : ℤ) ≤ ⌈(inverseHerbrand K M v : ℝ)⌉) hσM

/-- Because the filtration is decreasing, the union of `G_K^v` over `v > 0` is already a subgroup,
equal to their supremum. -/
theorem coe_biSup_pos_localAbsoluteUpperRamificationGroup :
    ((⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v : Subgroup (Field.absoluteGaloisGroup K)) :
      Set (Field.absoluteGaloisGroup K)) =
      ⋃ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        (localAbsoluteUpperRamificationGroup K v : Set (Field.absoluteGaloisGroup K)) := by
  let PosIdx := {v : RamificationIndexDomain // 0 < (v : ℝ)}
  have : Nonempty PosIdx := ⟨⟨⟨1, by norm_num⟩, by norm_num⟩⟩
  have hdir : Directed (· ≤ ·) (fun i : PosIdx ↦ localAbsoluteUpperRamificationGroup K i.1) :=
    fun i j ↦ ⟨⟨min i.1 j.1, lt_min i.2 j.2⟩,
      localAbsoluteUpperRamificationGroup_antitone K (min_le_left _ _),
      localAbsoluteUpperRamificationGroup_antitone K (min_le_right _ _)⟩
  have hsup : (⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v) =
      ⨆ i : PosIdx, localAbsoluteUpperRamificationGroup K i.1 := iSup_subtype'
  rw [hsup, Subgroup.coe_iSup_of_directed hdir]
  ext σ
  simp [PosIdx]

/-- **Wild inertia is the topological closure of the positive-depth upper ramification groups.** -/
@[simp]
theorem topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup :
    (⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v).topologicalClosure =
      wildInertiaSubgroup K := by
  set P' := (⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
    localAbsoluteUpperRamificationGroup K v).topologicalClosure
  refine le_antisymm ?_ ?_
  · refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_wildInertiaSubgroup K)
    exact iSup₂_le fun v hv ↦ localAbsoluteUpperRamificationGroup_le_wildInertiaSubgroup K hv
  · -- Both `P'` and `wildInertiaSubgroup K` are closed in `G_K`; compare their images in every
    -- finite quotient `G_K ⧸ U`.
    rw [← Subgroup.limitSubgroup_map_mk' P' (Subgroup.isClosed_topologicalClosure _)]
    intro σ hσ
    rw [mem_limitSubgroup_iff]
    intro U
    obtain ⟨E, _, _, hEU⟩ := (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K)
      (U : Set (Field.absoluteGaloisGroup K))).1 (U.isOpen.mem_nhds U.one_mem)
    let M : IntermediateField K (AlgebraicClosure K) := E ⊓ separableClosure K (AlgebraicClosure K)
    have : Module.Finite K M :=
      Module.Finite.of_injective (inclusion (inf_le_left : M ≤ E)).toLinearMap
        (inclusion (inf_le_left : M ≤ E)).injective
    have : Algebra.IsSeparable K M := (le_separableClosure_iff K _ M).1 inf_le_right
    have : Normal K M := inferInstance
    have : IsGalois K M := ⟨⟩
    have hMU : ∀ τ : Gal(AlgebraicClosure K/K), τ ∈ M.fixingSubgroup → τ ∈ U.toSubgroup := by
      intro τ hτ
      rw [IntermediateField.fixingSubgroup_inf_separableClosure] at hτ
      exact hEU hτ
    let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M
    let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M
    -- In `M/K`, `G_1(M/K) = Gal(M/K)^{φ_{M/K}(1)}` with `φ_{M/K}(1) > 0`.
    set vM : RamificationIndexDomain := herbrand K M ⟨1, by norm_num⟩
    have hvM : 0 < (vM : ℝ) := by
      have h0 : herbrand K M ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
        herbrand_of_coe_le_zero K M le_rfl
      have hlt := herbrand_strictMono K M (a := ⟨0, by norm_num⟩) (b := ⟨1, by norm_num⟩)
        (by norm_num : (0 : ℝ) < 1)
      rwa [h0] at hlt
    have h1 : (⟨1, by norm_num⟩ : RamificationIndexDomain) = ⟨((1 : ℤ) : ℝ), by norm_num⟩ :=
      Subtype.ext Int.cast_one.symm
    have hσM : AlgEquiv.restrictNormal σ M ∈ upperRamificationGroup K M vM := by
      rw [upperRamificationGroup_herbrand, h1, lowerRamificationGroupReal_intCast]
      exact restrictNormal_mem_lowerRamificationGroup_one M hσ
    obtain ⟨τ, hτ, hτσ⟩ := exists_mem_localAbsoluteUpperRamificationGroup_restrictNormal_eq M hσM
    have hτ_sup : τ ∈ ⨆ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        localAbsoluteUpperRamificationGroup K v := by
      rw [← SetLike.mem_coe, coe_biSup_pos_localAbsoluteUpperRamificationGroup]
      exact Set.mem_iUnion₂.2 ⟨vM, hvM, hτ⟩
    have hτP' : τ ∈ P' := Subgroup.le_topologicalClosure _ hτ_sup
    let τ₀ : Gal(AlgebraicClosure K/K) := τ
    let σ₀ : Gal(AlgebraicClosure K/K) := σ
    have hτσ' : AlgEquiv.restrictNormalHom M τ₀ = AlgEquiv.restrictNormalHom M σ₀ := hτσ
    refine ⟨τ, hτP', QuotientGroup.eq.2 (hMU (τ₀⁻¹ * σ₀) ?_)⟩
    rw [← M.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hτσ', inv_mul_cancel]

/-- Set-level form of `topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup`: the
topological closure of `⋃_{v > 0} G_K^v` is the wild inertia subgroup. -/
theorem closure_biUnion_pos_localAbsoluteUpperRamificationGroup :
    closure (⋃ (v : RamificationIndexDomain) (_ : 0 < (v : ℝ)),
        (localAbsoluteUpperRamificationGroup K v : Set (Field.absoluteGaloisGroup K))) =
      (wildInertiaSubgroup K : Set (Field.absoluteGaloisGroup K)) := by
  rw [← coe_biSup_pos_localAbsoluteUpperRamificationGroup, ← Subgroup.topologicalClosure_coe,
    topologicalClosure_biSup_pos_localAbsoluteUpperRamificationGroup]

/-- **The intersection of the absolute upper ramification groups at natural indices is trivial.** -/
@[simp]
theorem iInf_natCast_localAbsoluteUpperRamificationGroup :
    (⨅ n : ℕ, localAbsoluteUpperRamificationGroup K
      ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  apply (absoluteGaloisGroupRestrictEquiv K).injective
  rw [map_one]
  ext x
  -- Build the finite Galois splitting field of `minpoly K x` inside `AlgebraicClosure K`,
  -- avoiding any separability assumption on `AlgebraicClosure K / K`.
  have hxsep : IsSeparable K (x : AlgebraicClosure K) := mem_separableClosure_iff.1 x.2
  let f : K[X] := minpoly K (x : AlgebraicClosure K)
  let L : IntermediateField K (AlgebraicClosure K) := adjoin K (f.rootSet (AlgebraicClosure K))
  have hsplit : (f.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField K L f := adjoin_rootSet_isSplittingField hsplit
  have : IsGalois K L := IsGalois.of_separable_splitting_field hxsep
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) L
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L
  obtain ⟨N, hN⟩ := exists_forall_upperRamificationGroup_natCast_eq_bot K L
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  have hσN : AlgEquiv.restrictNormal σ₀ L ∈
      upperRamificationGroup K L ⟨N, Nat.cast_mem_ramificationIndexDomain N⟩ :=
    restrictNormal_mem_upperRamificationGroup L (Subgroup.mem_iInf.1 hσ N)
  rw [hN N le_rfl, Subgroup.mem_bot] at hσN
  have hxL : (x : AlgebraicClosure K) ∈ L :=
    subset_adjoin K _ ((Polynomial.mem_rootSet_of_ne (minpoly.ne_zero hxsep.isIntegral)).2
      (minpoly.aeval K _))
  have hfix : σ₀ (x : AlgebraicClosure K) = x :=
    (AlgEquiv.restrictNormal_commutes σ₀ L ⟨x, hxL⟩).symm.trans
      (by rw [hσN, AlgEquiv.one_apply]; rfl)
  exact (coe_absoluteGaloisGroupRestrictEquiv_apply K σ₀ x).trans hfix

/-- **The intersection of all absolute upper ramification groups is trivial.** -/
@[simp]
theorem iInf_localAbsoluteUpperRamificationGroup :
    ⨅ v : RamificationIndexDomain, localAbsoluteUpperRamificationGroup K v = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [← iInf_natCast_localAbsoluteUpperRamificationGroup K, Subgroup.mem_iInf]
  intro n
  exact Subgroup.mem_iInf.1 hσ ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩

end SpecialValues

/-! ### Restriction to normal intermediate extensions -/

section NormalIntermediate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem restrictNormal_restrictNormal_mem_finiteGaloisUpperRamificationGroup_iff
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
    (M : FiniteGaloisIntermediateField K E)
    (L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (hML : lift M.toIntermediateField = L.toIntermediateField)
    {v : RamificationIndexDomain} (σ : Gal(AlgebraicClosure K/K)) :
    AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ E) M.toIntermediateField ∈
        finiteGaloisUpperRamificationGroup K E M v ↔
      AlgEquiv.restrictNormal σ L.toIntermediateField ∈
        finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) L v := by
  let _ := finiteIntermediateFieldValuativeRel K E M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K E M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K E M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K E M.toIntermediateField
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) L.toIntermediateField
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) L.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
    L.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) L.toIntermediateField
  let φ : M.toIntermediateField ≃ₐ[K] L.toIntermediateField :=
    (liftAlgEquiv M.toIntermediateField).trans (IntermediateField.equivOfEq hML)
  rw [finiteGaloisUpperRamificationGroup_def, finiteGaloisUpperRamificationGroup_def,
    ← comap_autCongr_upperRamificationGroup φ v, Subgroup.mem_comap]
  suffices AlgEquiv.autCongr φ
      (AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ E) M.toIntermediateField) =
        AlgEquiv.restrictNormal σ L.toIntermediateField from
    Eq.to_iff (congrArg (· ∈ upperRamificationGroup K L.toIntermediateField v) this)
  refine AlgEquiv.ext fun x ↦ Subtype.ext ?_
  obtain ⟨z, rfl⟩ := φ.surjective x
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply, φ.symm_apply_apply]
  have hφ (w : M.toIntermediateField) :
      (φ w : AlgebraicClosure K) = ((w : E) : AlgebraicClosure K) := rfl
  rw [hφ, AlgEquiv.restrictNormal_apply L.toIntermediateField σ (φ z), hφ,
    AlgEquiv.restrictNormal_apply M.toIntermediateField (AlgEquiv.restrictNormal σ E) z,
    AlgEquiv.restrictNormal_apply E σ (z : E)]

private theorem exists_restrictNormal_eq_and_mem_finiteGaloisUpperRamificationGroup
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
    {v : RamificationIndexDomain} {τ : E ≃ₐ[K] E}
    (hτ : τ ∈ ⨅ M : FiniteGaloisIntermediateField K E,
      (finiteGaloisUpperRamificationGroup K E M v).comap (AlgEquiv.restrictNormalHom M))
    (N : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ∃ σ : Field.absoluteGaloisGroup K,
      AlgEquiv.restrictNormalHom E σ = τ ∧
        AlgEquiv.restrictNormalHom N.toIntermediateField σ ∈
          finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) N v := by
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ
  have : Algebra.IsSeparable K ↥(E ⊓ N.toIntermediateField) :=
    (le_separableClosure_iff K _ _).1
      (inf_le_right.trans (le_separableClosure K _ N.toIntermediateField))
  have : IsGalois K ↥(E ⊓ N.toIntermediateField) := ⟨⟩
  let L₀ : FiniteGaloisIntermediateField K (AlgebraicClosure K) := ⟨E ⊓ N.toIntermediateField⟩
  let eM := IntermediateField.restrictAlgEquiv (inf_le_left : L₀.toIntermediateField ≤ E)
  have : FiniteDimensional K ↥(restrict (inf_le_left : L₀.toIntermediateField ≤ E)) :=
    eM.toLinearEquiv.finiteDimensional
  have : IsGalois K ↥(restrict (inf_le_left : L₀.toIntermediateField ≤ E)) :=
    eM.transfer_galois.1 inferInstance
  let MF : FiniteGaloisIntermediateField K E :=
    ⟨restrict (inf_le_left : L₀.toIntermediateField ≤ E)⟩
  have hσ₀L₀ : AlgEquiv.restrictNormal σ₀ L₀.toIntermediateField ∈
      finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) L₀ v := by
    rw [← restrictNormal_restrictNormal_mem_finiteGaloisUpperRamificationGroup_iff E MF L₀
      (IntermediateField.lift_restrict (inf_le_left : L₀.toIntermediateField ≤ E)) σ₀]
    have hσ₀' : AlgEquiv.restrictNormal σ₀ E = τ := hσ₀
    rw [hσ₀']
    exact Subgroup.mem_iInf.1 hτ MF
  have hL₀N : L₀ ≤ N := (FiniteGaloisIntermediateField.le_iff L₀ N).2 inf_le_right
  rw [← map_restrictNormalHom_finiteGaloisUpperRamificationGroup K (AlgebraicClosure K) hL₀N v]
    at hσ₀L₀
  obtain ⟨ρ, hρN, hρL₀⟩ := hσ₀L₀
  have hval :
      E.val.comp (inclusion (inf_le_left : E ⊓ N.toIntermediateField ≤ E)) =
        L₀.toIntermediateField.val :=
    AlgHom.ext fun _ ↦ rfl
  have hcompat :
      (inclusion (inf_le_left : E ⊓ N.toIntermediateField ≤ E)).restrictNormalHom τ =
        (inclusion
          (inf_le_right : E ⊓ N.toIntermediateField ≤ N.toIntermediateField)).restrictNormalHom
            ρ := by
    rw [hρL₀, ← hσ₀, ← IntermediateField.restrictNormalHom_val E,
      AlgHom.restrictNormalHom_restrictNormalHom, hval,
      IntermediateField.restrictNormalHom_val]
    rfl
  obtain ⟨σ, hσ⟩ := (IntermediateField.mem_range_restrictNormalHom_prod_restrictNormalHom_iff
    E N.toIntermediateField τ ρ).2 hcompat
  rw [MonoidHom.prod_apply, Prod.mk.injEq] at hσ
  exact ⟨σ, hσ.1, hσ.2.symm ▸ hρN⟩

/-- **Quotient upper filtration on any normal intermediate extension.** Let `E` be a normal
intermediate field of `AlgebraicClosure K / K` (possibly infinite or inseparable). Restriction from
`G_K` to `Gal(E/K)` maps `localAbsoluteUpperRamificationGroup K v` onto the intersection of the
preimages of `Gal(M/K)^v` as `M` ranges over the finite Galois intermediate fields of `E/K`. -/
theorem map_restrictNormalHom_localAbsoluteUpperRamificationGroup_eq_iInf
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).map (AlgEquiv.restrictNormalHom E) =
      ⨅ M : FiniteGaloisIntermediateField K E,
        (finiteGaloisUpperRamificationGroup K E M v).comap (AlgEquiv.restrictNormalHom M) := by
  refine le_antisymm ?_ fun τ hτ ↦
    exists_mem_localAbsoluteUpperRamificationGroup_of_forall_finiteGalois E
      (exists_restrictNormal_eq_and_mem_finiteGaloisUpperRamificationGroup E hτ)
  rintro _ ⟨σ, hσ, rfl⟩
  refine Subgroup.mem_iInf.2 fun M ↦ ?_
  let eM := liftAlgEquiv M.toIntermediateField
  have : FiniteDimensional K ↥(lift M.toIntermediateField) :=
    eM.toLinearEquiv.finiteDimensional
  have : IsGalois K ↥(lift M.toIntermediateField) :=
    eM.transfer_galois.1 inferInstance
  let L : FiniteGaloisIntermediateField K (AlgebraicClosure K) := ⟨lift M.toIntermediateField⟩
  exact (restrictNormal_restrictNormal_mem_finiteGaloisUpperRamificationGroup_iff E M L rfl σ).2
    (mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.1 hσ L)

end NormalIntermediate

/-! ### Naturality in the local field -/

section FieldIso

variable {K K' : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

/-- Forward inclusion along a valuation-preserving isomorphism `e : K ≃+* K'` extended to
`e' : AlgebraicClosure K ≃+* AlgebraicClosure K'`. -/
private theorem mem_localAbsoluteUpperRamificationGroup_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    {σ' : Field.absoluteGaloisGroup K'}
    (hσσ' : ∀ y : AlgebraicClosure K,
      e' (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ y) =
        DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' (e' y))
    (hσ : σ ∈ localAbsoluteUpperRamificationGroup K v) :
    σ' ∈ localAbsoluteUpperRamificationGroup K' v := by
  refine mem_localAbsoluteUpperRamificationGroup_iff_forall_finiteGalois.2 fun M' ↦ ?_
  let _ := finiteIntermediateFieldValuativeRel K' (AlgebraicClosure K') M'.toIntermediateField
  let _ := finiteIntermediateFieldTopology K' (AlgebraicClosure K') M'.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K' (AlgebraicClosure K')
    M'.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K' (AlgebraicClosure K')
    M'.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  -- Pull the subfield `M'` back along `e'` to an intermediate field `M` of
  -- `AlgebraicClosure K / K`.
  let M : IntermediateField K (AlgebraicClosure K) :=
    { M'.toIntermediateField.toSubfield.comap e'.toRingHom with
      algebraMap_mem' := fun c ↦ Subfield.mem_comap.2 <| by
        rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he']
        exact M'.toIntermediateField.algebraMap_mem (e c) }
  let eM : M ≃+* M' := e'.restrict M M'.toIntermediateField (fun _ ↦ Iff.rfl)
  have heM (c : K) : eM (algebraMap K M c) = algebraMap K' M' (e c) :=
    Subtype.ext (he' c)
  have hcomp_symm :
      (algebraMap K M).comp e.symm.toRingHom = eM.symm.toRingHom.comp (algebraMap K' M') :=
    RingHom.ext fun c' ↦ by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      exact (eM.symm_apply_eq.2 (by rw [heM, e.apply_symm_apply])).symm
  have : Module.Finite K M := Module.Finite.of_equiv_equiv e.symm eM.symm hcomp_symm
  have : IsGalois K M := IsGalois.of_equiv_equiv (f := e.symm) (g := eM.symm) hcomp_symm
  let _ := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) M
  let _ := finiteIntermediateFieldTopology K (AlgebraicClosure K) M
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) M
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) M
  have hσM := restrictNormal_mem_upperRamificationGroup M hσ
  rw [← comap_algAutCongr_upperRamificationGroup_of_vle_iff e he eM heM v,
    Subgroup.mem_comap] at hσM
  convert hσM using 1
  refine AlgEquiv.ext fun y' ↦ Subtype.ext ?_
  let σ₀ : Gal(AlgebraicClosure K/K) := σ
  let σ'₀ : Gal(AlgebraicClosure K'/K') := σ'
  have hy : (eM (AlgEquiv.restrictNormal σ₀ M (eM.symm y')) : AlgebraicClosure K') =
      e' (σ₀ (eM.symm y' : AlgebraicClosure K)) :=
    congrArg e' (AlgEquiv.restrictNormal_commutes σ₀ M (eM.symm y'))
  have hsymm : (eM.symm y' : AlgebraicClosure K) = e'.symm (y' : AlgebraicClosure K') := rfl
  have happly :
      ((e.algAutCongr eM heM (AlgEquiv.restrictNormal σ₀ M) y' : M') : AlgebraicClosure K') =
        (eM (AlgEquiv.restrictNormal σ₀ M (eM.symm y')) : AlgebraicClosure K') :=
    congrArg Subtype.val (RingEquiv.algAutCongr_apply e eM heM (AlgEquiv.restrictNormal σ₀ M) y')
  refine (AlgEquiv.restrictNormal_commutes σ'₀ M'.toIntermediateField y').trans (Eq.trans ?_
    happly.symm)
  rw [IntermediateField.algebraMap_apply, hy, hsymm, hσσ', e'.apply_symm_apply]

/-- **Naturality of membership in `localAbsoluteUpperRamificationGroup` under valuation-preserving
field isomorphisms.** Let `e : K ≃+* K'` be a valuation-preserving ring isomorphism of
nonarchimedean local fields and `e' : AlgebraicClosure K ≃+* AlgebraicClosure K'` any ring
isomorphism extending `e`. If `σ` and `σ'` are intertwined by `e'`, then
`σ ∈ G_K^v ↔ σ' ∈ G_{K'}^v`. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff_of_vle_iff
    (e : K ≃+* K') (he : ∀ a b : K, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    {σ' : Field.absoluteGaloisGroup K'}
    (hσσ' : ∀ y : AlgebraicClosure K,
      e' (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ y) =
        DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' (e' y)) :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      σ' ∈ localAbsoluteUpperRamificationGroup K' v := by
  have hvle_symm (a' b' : K') : e.symm a' ≤ᵥ e.symm b' ↔ a' ≤ᵥ b' := by
    rw [← he, e.apply_symm_apply, e.apply_symm_apply]
  have he'_symm (c' : K') :
      e'.symm (algebraMap K' (AlgebraicClosure K') c') =
        algebraMap K (AlgebraicClosure K) (e.symm c') :=
    e'.symm_apply_eq.2 (by rw [he', e.apply_symm_apply])
  have hσσ'_symm (y' : AlgebraicClosure K') :
      e'.symm (DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' y') =
        DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ (e'.symm y') :=
    e'.symm_apply_eq.2 (by rw [hσσ', e'.apply_symm_apply])
  exact ⟨mem_localAbsoluteUpperRamificationGroup_of_vle_iff e he e' he' hσσ',
    mem_localAbsoluteUpperRamificationGroup_of_vle_iff e.symm hvle_symm e'.symm he'_symm hσσ'_symm⟩

/-- **Naturality of membership in `localAbsoluteUpperRamificationGroup` under continuous field
isomorphisms.** Let `e : K ≃+* K'` be a continuous ring isomorphism of nonarchimedean local fields
and `e' : AlgebraicClosure K ≃+* AlgebraicClosure K'` any ring isomorphism extending `e`. If `σ`
and `σ'` are intertwined by `e'`, then `σ ∈ G_K^v ↔ σ' ∈ G_{K'}^v`. -/
theorem mem_localAbsoluteUpperRamificationGroup_iff_of_ringEquiv
    (e : K ≃+* K') (he : Continuous e)
    (e' : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he' : ∀ c : K, e' (algebraMap K (AlgebraicClosure K) c) =
      algebraMap K' (AlgebraicClosure K') (e c))
    {v : RamificationIndexDomain} {σ : Field.absoluteGaloisGroup K}
    {σ' : Field.absoluteGaloisGroup K'}
    (hσσ' : ∀ y : AlgebraicClosure K,
      e' (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ y) =
        DFunLike.coe (F := Gal(AlgebraicClosure K'/K')) σ' (e' y)) :
    σ ∈ localAbsoluteUpperRamificationGroup K v ↔
      σ' ∈ localAbsoluteUpperRamificationGroup K' v :=
  mem_localAbsoluteUpperRamificationGroup_iff_of_vle_iff e
    (e.toRingHom.map_vle_map_iff_of_continuous he) e' he' hσσ'

/-- **Pullback along `Field.absoluteGaloisGroup.mapOfAlgebra` preserves the absolute upper
filtration** along any continuous field isomorphism `K →+* K'` and compatible embedding of
algebraic closures. -/
theorem comap_absoluteGaloisGroup_mapOfAlgebra_localAbsoluteUpperRamificationGroup
    [Algebra K K'] [Algebra (AlgebraicClosure K) (AlgebraicClosure K')]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure K')]
    (hbij : Function.Bijective (algebraMap K K')) (hcont : Continuous (algebraMap K K'))
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).comap
        (Field.absoluteGaloisGroup.mapOfAlgebra K K') =
      localAbsoluteUpperRamificationGroup K' v := by
  let e : K ≃+* K' := RingEquiv.ofBijective (algebraMap K K') hbij
  have : Algebra.IsIntegral K K' := Algebra.isIntegral_of_surjective hbij.2
  have : Algebra.IsIntegral K (AlgebraicClosure K') := Algebra.IsIntegral.trans K'
  have : Algebra.IsIntegral (AlgebraicClosure K) (AlgebraicClosure K') :=
    Algebra.IsIntegral.tower_top K
  have hφ : Function.Bijective (algebraMap (AlgebraicClosure K) (AlgebraicClosure K')) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e' : AlgebraicClosure K ≃+* AlgebraicClosure K' := RingEquiv.ofBijective _ hφ
  have he' (c : K) :
      e' (algebraMap K (AlgebraicClosure K) c) = algebraMap K' (AlgebraicClosure K') (e c) :=
    (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) (AlgebraicClosure K') c).symm.trans
      (IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K') c)
  ext g'
  rw [Subgroup.mem_comap]
  exact mem_localAbsoluteUpperRamificationGroup_iff_of_ringEquiv e hcont e' he' fun y ↦
    absoluteGaloisGroup_mapOfAlgebra_commutes K K' g' y

/-- **Pullback along `Field.absoluteGaloisGroup.map` preserves the absolute upper filtration**
for any bijective continuous ring homomorphism `f : K →+* K'`. -/
theorem comap_absoluteGaloisGroup_map_localAbsoluteUpperRamificationGroup
    {f : K →+* K'} (hf : Function.Bijective f) (hcont : Continuous f)
    (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K v).comap (Field.absoluteGaloisGroup.map f) =
      localAbsoluteUpperRamificationGroup K' v := by
  let _ : Algebra K K' := f.toAlgebra
  let _ : Algebra (AlgebraicClosure K) (AlgebraicClosure K') :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure K').toAlgebra
  have : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure K') :=
    .of_algebraMap_eq fun c ↦
      ((IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure K').commutes c).symm
  exact comap_absoluteGaloisGroup_mapOfAlgebra_localAbsoluteUpperRamificationGroup hf hcont v

/-- **Transport along `TauCeti.absoluteGaloisGroupMapEquiv` maps `G_{K'}^v` onto `G_K^v`.** -/
@[simp]
theorem map_absoluteGaloisGroupMapEquiv_localAbsoluteUpperRamificationGroup
    (e : K ≃+* K') (he : Continuous e) (v : RamificationIndexDomain) :
    (localAbsoluteUpperRamificationGroup K' v).map
        (absoluteGaloisGroupMapEquiv e :
          Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) =
      localAbsoluteUpperRamificationGroup K v := by
  have hhom :
      (absoluteGaloisGroupMapEquiv e :
          Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) =
        (Field.absoluteGaloisGroup.map (e : K →+* K') :
          Field.absoluteGaloisGroup K' →* Field.absoluteGaloisGroup K) :=
    MonoidHom.ext (absoluteGaloisGroupMapEquiv_apply e)
  rw [← comap_absoluteGaloisGroup_map_localAbsoluteUpperRamificationGroup
    (f := (e : K →+* K')) e.bijective he v, ← hhom]
  exact Subgroup.map_comap_eq_self_of_surjective (absoluteGaloisGroupMapEquiv e).surjective _

end FieldIso

end TauCeti
