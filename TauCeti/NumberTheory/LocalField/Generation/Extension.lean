/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Generation.Quotient
public import TauCeti.NumberTheory.LocalField.ClassModule
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Lifting
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.ClassIdentification

/-!
# Generating finite local Galois quotients from relation-group maps

Let `U` be an open normal subgroup of a local absolute Galois group, containing the
commutator of wild inertia, and put `V = P_K U`. A generating tuple in `G_K/V` and a
continuous equivariant surjection from its pro-`p` relation group to `Vᵃᵇ(p)`, bijective
on second cohomology, produce a generating tuple of the same length in `G_K/U`.

The coefficient map is an explicit input: its arithmetic construction requires Lyndon's
relation-module identification and local reciprocity. The result here supplies the group
argument once that map is available. The arithmetic extension class generates by local
strict cohomological dimension. The free-presentation lifting theorem then supplies a
surjection onto the arithmetic class-module extension, and `G_K/U` is a quotient of that
extension because the image of wild inertia is an abelian `p`-group.

The conclusion uses tuples, allowing repetitions, and also records their images in the
original tame quotient. Thus the construction retains the chosen quotient generators.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

open ValuativeRel

namespace TauCeti

open ContCohomology freeProfiniteGroup

variable {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharP 𝓀[K] p]

/-- A cohomologically bijective surjection on the pro-`p` relation groups lifts a
generating tuple of `G_K/(P_K U)` to a generating tuple of `G_K/U`.
The number of generators is retained, and their images are the prescribed tuple. -/
theorem exists_generating_tuple_quotient_of_classModuleMap
    (hp : IsUnit (p : K)) (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (hU : ⁅wildInertiaSubgroup K, wildInertiaSubgroup K⁆ ≤ U.toSubgroup)
    {n : ℕ}
    (g : Fin n → Field.absoluteGaloisGroup K ⧸ (wildInertiaSubgroup K ⊔ U.toSubgroup))
    (hg : Dense (Subgroup.closure (Set.range g) :
      Set (Field.absoluteGaloisGroup K ⧸ (wildInertiaSubgroup K ⊔ U.toSubgroup)))) :
    let V := wildInertiaSubgroup K ⊔ U.toSubgroup
    letI : IsClosed (V : Set (Field.absoluteGaloisGroup K)) :=
      V.isClosed_of_isOpen (Subgroup.isOpen_mono le_sup_right U.isOpen)
    letI : DiscreteTopology (Field.absoluteGaloisGroup K ⧸ V) :=
      QuotientGroup.discreteTopology (Subgroup.isOpen_mono le_sup_right U.isOpen)
    letI := presentationClassModuleAction p hg
    letI := continuousSMul_presentationClassModuleAction p hg
    ∀ (f : abelianizationProP p (freeProfiniteGroup (Fin n))
        (lift g : freeProfiniteGroup (Fin n) →*
          Field.absoluteGaloisGroup K ⧸ V).ker →*[Field.absoluteGaloisGroup K ⧸ V]
          abelianizationProP p (Field.absoluteGaloisGroup K) V)
      (hf : Continuous f),
      Function.Surjective f →
      Function.Bijective (explicitCoeff2
        (Field.absoluteGaloisGroup K ⧸ V)
        (Additive (abelianizationProP p (freeProfiniteGroup (Fin n))
          (lift g : freeProfiniteGroup (Fin n) →*
            Field.absoluteGaloisGroup K ⧸ V).ker))
        f.toAdditive (f.continuous_toAdditive hf)) →
      ∃ t : Fin n → Field.absoluteGaloisGroup K ⧸ U.toSubgroup,
        Subgroup.closure (Set.range t) = ⊤ ∧
          ∀ i, QuotientGroup.mapOfLE (le_sup_right :
            U.toSubgroup ≤ wildInertiaSubgroup K ⊔ U.toSubgroup) (t i) = g i := by
  intro V
  have hV : IsOpen (V : Set (Field.absoluteGaloisGroup K)) :=
    Subgroup.isOpen_mono le_sup_right U.isOpen
  let : IsClosed (V : Set (Field.absoluteGaloisGroup K)) := V.isClosed_of_isOpen hV
  let : DiscreteTopology (Field.absoluteGaloisGroup K ⧸ V) :=
    QuotientGroup.discreteTopology hV
  let := presentationClassModuleAction p hg
  let := continuousSMul_presentationClassModuleAction p hg
  intro f hf hs hc
  obtain ⟨hy, hcard⟩ := contCohomologyClass_absoluteGaloisGroup_generates hp hV
  obtain ⟨ψ, hψ, hright⟩ := exists_surjective_presentationClassModuleHom (W := V) hg f hf hs hc
    (by simpa only [abelianizationProPProfiniteExtension_contCohomologyClass p _ V hV] using hy)
    ⟨_, hcard⟩
  let q : abelianizationProPExtensionGroup p (Field.absoluteGaloisGroup K) V →ₜ*
      Field.absoluteGaloisGroup K ⧸ U.toSubgroup :=
    ⟨QuotientGroup.mapOfLE
      (abelianizationProPExtensionKernel_le_of_commutator_wildInertiaSubgroup_le K p U hU),
      QuotientGroup.continuous_mapOfLE _⟩
  let φ := q.comp ψ
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mapOfLE_surjective _).comp hψ
  refine ⟨fun i ↦ φ (of i), ?_, fun i ↦ ?_⟩
  · have hd : Dense ((Subgroup.closure (Set.range (of : Fin n → freeProfiniteGroup (Fin n)))).map
        φ.toMonoidHom : Set (Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) :=
      hφ.denseRange.dense_image φ.continuous (dense_closure_range_of (Fin n))
    rw [MonoidHom.map_closure, _root_.ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass, ← Set.range_comp] at hd
    apply SetLike.coe_injective
    exact (isClosed_discrete _).closure_eq.symm.trans hd.closure_eq
  · have h := DFunLike.congr_fun hright (of i)
    have hcomp : (QuotientGroup.mapOfLE (le_sup_right : U.toSubgroup ≤ V)).comp
        q.toMonoidHom =
          (abelianizationProPExtension p (Field.absoluteGaloisGroup K) V).rightHom := by
      simpa only [q, abelianizationProPExtension_rightHom] using
        QuotientGroup.mapOfLE_comp
          (abelianizationProPExtensionKernel_le_of_commutator_wildInertiaSubgroup_le K p U hU)
          (le_sup_right : U.toSubgroup ≤ V)
    -- Evaluate the bundled map through its monoid-hom projection so the composition
    -- identity applies without depending on simplification of quotient carriers.
    change ((QuotientGroup.mapOfLE (le_sup_right : U.toSubgroup ≤ V)).comp
      q.toMonoidHom) (ψ (of i)) = g i
    rw [hcomp]
    simpa using h

end TauCeti
