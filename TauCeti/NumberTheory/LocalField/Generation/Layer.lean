/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Generation.Quotient
public import TauCeti.NumberTheory.LocalField.Tame.Layer
public import TauCeti.NumberTheory.LocalField.ClassModule
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Extension
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Map

/-!
# Finite local Galois generators from the tame layer's class module

Let `K` be a perfect nonarchimedean local field whose residue prime `p` is invertible in `K`.
Let `U` be an open normal subgroup of `G_K` containing the commutator of wild inertia,
and let `L` be the fixed field of `P_K U`. A generating
tuple of `Gal(L/K)` lifts to a generating tuple of `G_K/U` whenever its pro-`p` relation
group maps continuously and equivariantly onto the arithmetic class module, inducing
a bijection on explicit continuous second cohomology.

The arithmetic coefficients use the separable closure and the canonical embedding of
the tame layer. The conclusion uses the algebraic-closure model of `G_K`, retaining the
prescribed generators under the canonical quotient identification. Thus an arithmetic
relation-module calculation can be used directly without changing coefficient actions
or transporting its second-cohomology hypothesis to a different quotient model.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti

open ContCohomology freeProfiniteGroup _root_.ValuativeRel

variable {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [PerfectField K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharP 𝓀[K] p]

/-- A cohomologically bijective surjection onto the arithmetic class module of the tame
layer lifts its Galois generators to generators of the original finite quotient.
The tuple's images in the tame quotient are retained through `quotientTameLayerEquiv`. -/
theorem exists_generating_tuple_quotient_of_galoisClassModuleMap
    (hp : IsUnit (p : K)) (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (hU : ⁅wildInertiaSubgroup K, wildInertiaSubgroup K⁆ ≤ U.toSubgroup)
    {n : ℕ} (g : Fin n → Gal(tameLayer K U/K))
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    let j := tameLayerEmbedding K U
    letI := presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := galoisClassModuleAction p K (tameLayer K U) j
    letI := continuousSMul_galoisClassModuleAction p K (tameLayer K U) j
    ∀ (f : abelianizationProP p (freeProfiniteGroup (Fin n))
        (lift g : freeProfiniteGroup (Fin n) →* Gal(tameLayer K U/K)).ker →*[
          Gal(tameLayer K U/K)]
        abelianizationProP p (AbsoluteGaloisGroup K)
          (galoisSubgroup K (tameLayer K U) j).toSubgroup)
      (hf : Continuous f),
      Function.Surjective f →
      Function.Bijective (explicitCoeff2 (Gal(tameLayer K U/K))
        (Additive (abelianizationProP p (freeProfiniteGroup (Fin n))
          (lift g : freeProfiniteGroup (Fin n) →* Gal(tameLayer K U/K)).ker))
        f.toAdditive (f.continuous_toAdditive hf)) →
      ∃ t : Fin n → Field.absoluteGaloisGroup K ⧸ U.toSubgroup,
        Subgroup.closure (Set.range t) = ⊤ ∧
          ∀ i, quotientTameLayerEquiv K U
            (QuotientGroup.mapOfLE (by
              simpa only [tameLayerSubgroup_toSubgroup] using
                (le_sup_right : U.toSubgroup ≤ wildInertiaSubgroup K ⊔ U.toSubgroup))
              (t i)) = g i := by
  /- The arithmetic extension class generates by
  `galoisClassModuleExtension_contCohomologyClass_generates`. The extension generators use
  `freeProfiniteGroup.exists_topologicalClosure_closure_range_eq_top_of_bijective_explicitCoeff2`;
  the class-module map induced by `absoluteGaloisGroupRestrictEquiv` then descends them to
  the original finite quotient. -/
  intro j
  have hd : Dense (Subgroup.closure (Set.range g) : Set Gal(tameLayer K U/K)) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  let := presentationClassModuleAction p hd
  let := continuousSMul_presentationClassModuleAction p hd
  let := galoisClassModuleAction p K (tameLayer K U) j
  let := continuousSMul_galoisClassModuleAction p K (tameLayer K U) j
  intro f hf hs hc
  let W := (galoisSubgroup K (tameLayer K U) j).toSubgroup
  let V := wildInertiaSubgroup K ⊔ U.toSubgroup
  let Y := galoisClassModuleExtension p K (tameLayer K U) j
  let a := absoluteGaloisGroupRestrictEquiv K
  have hWV : W ≤ V.comap a.symm.toMulEquiv.toMonoidHom := by
    intro σ hσ
    have h := galoisSubgroup_tameLayerEmbedding_comap K U
    have hm : a (a.symm σ) ∈ W := by
      rw [a.apply_symm_apply]
      exact hσ
    exact (congrArg (a.symm σ ∈ ·) h).to_iff.mp hm
  let c := abelianizationProPExtensionMap p a.symm.toMulEquiv.toMonoidHom
    a.symm.continuous hWV
  let q : abelianizationProPExtensionGroup p (Field.absoluteGaloisGroup K) V →ₜ*
      Field.absoluteGaloisGroup K ⧸ U.toSubgroup :=
    ⟨QuotientGroup.mapOfLE
      (abelianizationProPExtensionKernel_le_of_commutator_wildInertiaSubgroup_le K p U hU),
      QuotientGroup.continuous_mapOfLE _⟩
  -- Relabelling the arithmetic extension changes only its projection, so its total
  -- group is the canonical class-module quotient on which `c` is defined.
  let π : Y.E →ₜ* Field.absoluteGaloisGroup K ⧸ U.toSubgroup := q.comp c
  have hπ : Function.Surjective π :=
    (QuotientGroup.mapOfLE_surjective _).comp
      (abelianizationProPExtensionMap_surjective p _ _ hWV a.symm.surjective)
  have hπmk (σ : AbsoluteGaloisGroup K) : π (QuotientGroup.mk σ) =
      QuotientGroup.mk (a.symm σ) := by
    exact (congrArg q (abelianizationProPExtensionMap_mk p a.symm.toMulEquiv.toMonoidHom
      a.symm.continuous hWV σ)).trans (QuotientGroup.mapOfLE_mk _ _)
  have hright (x : Y.E) : quotientTameLayerEquiv K U
      (QuotientGroup.mapOfLE (by
        simpa only [tameLayerSubgroup_toSubgroup] using
          (le_sup_right : U.toSubgroup ≤ wildInertiaSubgroup K ⊔ U.toSubgroup)) (π x)) =
      Y.toGroupExtension.rightHom x := by
    induction x using QuotientGroup.induction_on with
    | H σ =>
      rw [hπmk, QuotientGroup.mapOfLE_mk]
      exact (quotientTameLayerEquiv_mk K U (a.symm σ)).trans
        (((tameLayerEmbedding_restrictNormalHom K U (a.symm σ)).symm.trans
          (congrArg j.restrictNormalHom (a.apply_symm_apply σ))).trans
          (galoisClassModuleExtension_rightHom_mk p K (tameLayer K U) j σ).symm)
  obtain ⟨hy, hcard⟩ := galoisClassModuleExtension_contCohomologyClass_generates
    (p := p) K (tameLayer K U) hp j
  obtain ⟨y, hyright, hygen⟩ :=
    exists_topologicalClosure_closure_range_eq_top_of_bijective_explicitCoeff2 p hd Y
      isProP_maximalProPQuotient hy ⟨_, hcard⟩ f hf hs hc
  refine ⟨fun i ↦ π (y i), ?_, fun i ↦ (hright (y i)).trans (hyright i)⟩
  have h := hπ.denseRange.topologicalClosure_map_subgroup π.continuous hygen
  rw [MonoidHom.map_closure, ← Set.range_comp] at h
  -- The finite quotient is discrete, so topological generation is algebraic generation.
  have : DiscreteTopology (Field.absoluteGaloisGroup K ⧸ U.toSubgroup) :=
    QuotientGroup.discreteTopology U.isOpen
  apply SetLike.coe_injective
  simpa only [Subgroup.topologicalClosure_coe, (isClosed_discrete _).closure_eq,
    _root_.ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
    Function.comp_def] using
    congrArg (fun S : Subgroup (Field.absoluteGaloisGroup K ⧸ U.toSubgroup) ↦
      (S : Set (Field.absoluteGaloisGroup K ⧸ U.toSubgroup))) h

end TauCeti
