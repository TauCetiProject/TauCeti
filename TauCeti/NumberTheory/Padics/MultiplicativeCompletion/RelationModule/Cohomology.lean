/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.Equivariant
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ProjectiveKernel
import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.CoeffMap

/-!
# Second cohomology of transported arithmetic relation-module maps

The relation-module map transported through Lyndon and local reciprocity induces the same
second-cohomology map as the original integral group-algebra map. In particular, a surjection
with projective kernel gives a bijection on explicit continuous second cohomology. Using
this with the tame-frame relation-module surjection supplies the cohomology input needed to
lift the transported map to a surjection of profinite group extensions.

The two coordinate comparisons are `freeProfiniteGroup.explicitH2EquivRelationModule` and
`explicitH2EquivPadicCompletionUnits`; the transported map is
`relationModuleToAbelianizationProPEquivariant`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti

open Additive CategoryTheory ContCohomology _root_.Rep

-- These two private facts identify the existing comparisons by their coefficient coordinates.
-- Keeping their normalization separate makes the naturality proof use only the generic API.
private theorem relationModuleComparison_eq (p : ℕ) [Fact p.Prime]
    {G ι : Type} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    [Fintype ι] [DecidableEq ι] {g : ι → G} (hg : Subgroup.closure (Set.range g) = ⊤) :
    letI := freeProfiniteGroup.presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    let B : Rep ℤ_[p] G := ofModuleMonoidAlgebra.obj
      (ModuleCat.of (MonoidAlgebra ℤ_[p] G) (MonoidAlgebra.relationModule ℤ_[p] G g))
    ∀ (ψ : Additive (abelianizationProP p (freeProfiniteGroup ι)
        (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* G).ker) ≃+ B)
      (hψ : ∀ t x, ψ (t • x) = B.ρ t (ψ x)),
      ψ = (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg).trans
        (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] G)
          (MonoidAlgebra.relationModule ℤ_[p] G g)).symm →
      freeProfiniteGroup.explicitH2EquivRelationModule p hg =
        explicitH2AddEquivGroupCohomology (.refl G) ψ hψ := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set G) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  let := freeProfiniteGroup.presentationClassModuleAction p hd
  let := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
  dsimp only
  intro ψ hψ heq
  subst ψ
  dsimp only [freeProfiniteGroup.explicitH2EquivRelationModule]

private theorem padicCompletionUnitsComparison_eq (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Normal K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L] (j : L →ₐ[K] SeparableClosure K) :
    letI := galoisClassModuleAction p K L j
    letI := continuousSMul_galoisClassModuleAction p K L j
    let C : Rep ℤ_[p] (L ≃ₐ[K] L) := ofModuleMonoidAlgebra.obj
      (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (Additive ↑(padicCompletionUnits p L)))
    ∀ (χ : Additive (abelianizationProP p (AbsoluteGaloisGroup K)
        (galoisSubgroup K L j).toSubgroup) ≃+ C)
      (hχ : ∀ t x, χ (t • x) = C.ρ t (χ x)),
      χ = (padicCompletionUnitsEquivAbelianizationProP p K L j).symm.toMulEquiv.toAdditive.trans
        (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
          (Additive ↑(padicCompletionUnits p L))).symm →
      explicitH2EquivPadicCompletionUnits p K L j =
        explicitH2AddEquivGroupCohomology (.refl (L ≃ₐ[K] L)) χ hχ := by
  let := galoisClassModuleAction p K L j
  let := continuousSMul_galoisClassModuleAction p K L j
  dsimp only
  intro χ hχ heq
  subst χ
  dsimp only [explicitH2EquivPadicCompletionUnits]

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Normal K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]
  {ι : Type} [Fintype ι] [DecidableEq ι] {g : ι → L ≃ₐ[K] L}
  (hg : Subgroup.closure (Set.range g) = ⊤)
  (β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
    Additive ↑(padicCompletionUnits p L))
  (j : L →ₐ[K] SeparableClosure K)

/-- The explicit second-cohomology map on arithmetic kernels is the original algebraic
relation-module map, in Lyndon and reciprocity coordinates. -/
theorem explicitH2EquivPadicCompletionUnits_explicitCoeff2_relationModule :
    letI := freeProfiniteGroup.presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    let := galoisClassModuleAction p K L j
    letI := continuousSMul_galoisClassModuleAction p K L j
    ∀ x : H2 (L ≃ₐ[K] L) (Additive (abelianizationProP p (freeProfiniteGroup ι)
      (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker)),
    explicitH2EquivPadicCompletionUnits p K L j
        (explicitCoeff2 (L ≃ₐ[K] L) _
          (relationModuleToAbelianizationProPEquivariant p K L hg β j).toAdditive
          ((relationModuleToAbelianizationProPEquivariant p K L hg β j).continuous_toAdditive
            (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j)) x) =
      ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
        (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)))
        (freeProfiniteGroup.explicitH2EquivRelationModule p hg x) := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  let := freeProfiniteGroup.presentationClassModuleAction p hd
  let := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
  let := galoisClassModuleAction p K L j
  let := continuousSMul_galoisClassModuleAction p K L j
  let B : Rep ℤ_[p] (L ≃ₐ[K] L) :=
    ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g))
  let C : Rep ℤ_[p] (L ≃ₐ[K] L) :=
    ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (Additive ↑(padicCompletionUnits p L)))
  let eL := freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
  let eR := padicCompletionUnitsEquivAbelianizationProP p K L j
  let ψ : Additive (abelianizationProP p (freeProfiniteGroup ι)
      (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) ≃+ B :=
    eL.trans (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g)).symm
  let χ : Additive (abelianizationProP p (AbsoluteGaloisGroup K)
      (galoisSubgroup K L j).toSubgroup) ≃+ C :=
    eR.symm.toMulEquiv.toAdditive.trans
      (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
        (Additive ↑(padicCompletionUnits p L))).symm
  have hψ : ∀ t x, ψ (t • x) = B.ρ t (ψ x) := fun t x => by
    -- The group-algebra representation acts by `single t 1` on the unchanged scalar carrier.
    change eL (t • x) = MonoidAlgebra.single t (1 : ℤ_[p]) • eL x
    exact freeProfiniteGroup.abelianizationProPEquivRelationModule_presentation_smul p hg t x
  have hχ : ∀ t x, χ (t • x) = C.ρ t (χ x) := fun t x => by
    -- Inverse reciprocity intertwines the action after reading its carrier additively.
    change ofMul (eR.symm (t • x.toMul)) =
      MonoidAlgebra.single t (1 : ℤ_[p]) • ofMul (eR.symm x.toMul)
    rw [padicCompletionUnits_single_smul, one_smul]
    have h := padicCompletionUnitsEquivAbelianizationProP_galois_smul p K L j t
      (eR.symm x.toMul)
    rw [eR.apply_symm_apply] at h
    exact congrArg ofMul (eR.injective ((eR.apply_symm_apply _).trans h.symm))
  let f := relationModuleToAbelianizationProPEquivariant p K L hg β j
  let hf := f.continuous_toAdditive
    (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j)
  let F : B ⟶ C := ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)
  have hF : ∀ x, χ (f.toAdditive x) = F.hom (ψ x) := by
    intro x
    dsimp only [χ, ψ, F, ofModuleMonoidAlgebra, RestrictScalars.addEquiv,
      MulEquiv.toAdditive]
    simp only [MulDistribMulActionHom.toAdditive_apply, ModuleCat.hom_ofHom]
    -- The representation morphism has underlying map β; scalar restriction keeps its carrier.
    change ofMul (eR.symm (f x.toMul)) = β (eL x)
    rw [relationModuleToAbelianizationProPEquivariant_apply,
      relationModuleToAbelianizationProP_apply]
    exact congrArg ofMul (eR.symm_apply_apply _)
  have hL := relationModuleComparison_eq p hg ψ hψ rfl
  have hR := padicCompletionUnitsComparison_eq p K L j χ hχ rfl
  intro x
  calc
    _ = explicitH2AddEquivGroupCohomology (.refl (L ≃ₐ[K] L)) χ hχ
        (explicitCoeff2 (L ≃ₐ[K] L) _ f.toAdditive hf x) :=
      congrArg (fun e => e (explicitCoeff2 (L ≃ₐ[K] L) _ f.toAdditive hf x)) hR
    _ = groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) F 2
        (explicitH2AddEquivGroupCohomology (.refl (L ≃ₐ[K] L)) ψ hψ x) :=
      explicitH2AddEquivGroupCohomology_explicitCoeff2
        (.refl (L ≃ₐ[K] L)) ψ χ hψ hχ f.toAdditive hf F hF x
    _ = _ := by
      rw [_root_.groupCohomology.functor_map]
      exact congrArg (groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) F 2)
        (congrArg (fun e => e x) hL).symm

/-- A surjective arithmetic relation-module map with projective kernel induces a bijection
on explicit second cohomology after transport through Lyndon and local reciprocity. -/
theorem bijective_explicitCoeff2_relationModuleToAbelianizationProPEquivariant
    (hβ : Function.Surjective β)
    [Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker β)] :
    letI := freeProfiniteGroup.presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    let := galoisClassModuleAction p K L j
    letI := continuousSMul_galoisClassModuleAction p K L j
    Function.Bijective (explicitCoeff2 (L ≃ₐ[K] L) _
      (relationModuleToAbelianizationProPEquivariant p K L hg β j).toAdditive
      ((relationModuleToAbelianizationProPEquivariant p K L hg β j).continuous_toAdditive
        (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j))) := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  let := freeProfiniteGroup.presentationClassModuleAction p hd
  let := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
  let := galoisClassModuleAction p K L j
  let := continuousSMul_galoisClassModuleAction p K L j
  let B : Rep ℤ_[p] (L ≃ₐ[K] L) :=
    ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g))
  let C : Rep ℤ_[p] (L ≃ₐ[K] L) :=
    ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (Additive ↑(padicCompletionUnits p L)))
  let eL := freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
  let eR := padicCompletionUnitsEquivAbelianizationProP p K L j
  let ψ : Additive (abelianizationProP p (freeProfiniteGroup ι)
      (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) ≃+ B :=
    eL.trans (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g)).symm
  let χ : Additive (abelianizationProP p (AbsoluteGaloisGroup K)
      (galoisSubgroup K L j).toSubgroup) ≃+ C :=
    eR.symm.toMulEquiv.toAdditive.trans
      (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
        (Additive ↑(padicCompletionUnits p L))).symm
  have hψ : ∀ t x, ψ (t • x) = B.ρ t (ψ x) := fun t x => by
    -- The group-algebra representation acts by `single t 1` on the unchanged scalar carrier.
    change eL (t • x) = MonoidAlgebra.single t (1 : ℤ_[p]) • eL x
    exact freeProfiniteGroup.abelianizationProPEquivRelationModule_presentation_smul p hg t x
  have hχ : ∀ t x, χ (t • x) = C.ρ t (χ x) := fun t x => by
    -- Inverse reciprocity intertwines the action after reading its carrier additively.
    change ofMul (eR.symm (t • x.toMul)) =
      MonoidAlgebra.single t (1 : ℤ_[p]) • ofMul (eR.symm x.toMul)
    rw [padicCompletionUnits_single_smul, one_smul]
    have h := padicCompletionUnitsEquivAbelianizationProP_galois_smul p K L j t
      (eR.symm x.toMul)
    rw [eR.apply_symm_apply] at h
    exact congrArg ofMul (eR.injective ((eR.apply_symm_apply _).trans h.symm))
  let f := relationModuleToAbelianizationProPEquivariant p K L hg β j
  let hf := f.continuous_toAdditive
    (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j)
  let F : B ⟶ C := ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)
  have hF : ∀ x, χ (f.toAdditive x) = F.hom (ψ x) := by
    intro x
    dsimp only [χ, ψ, F, ofModuleMonoidAlgebra, RestrictScalars.addEquiv,
      MulEquiv.toAdditive]
    simp only [MulDistribMulActionHom.toAdditive_apply, ModuleCat.hom_ofHom]
    -- The representation morphism has underlying map β; scalar restriction keeps its carrier.
    change ofMul (eR.symm (f x.toMul)) = β (eL x)
    rw [relationModuleToAbelianizationProPEquivariant_apply,
      relationModuleToAbelianizationProP_apply]
    exact congrArg ofMul (eR.symm_apply_apply _)
  have := groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ 1
  apply (explicitCoeff2_bijective_iff
    (.refl (L ≃ₐ[K] L)) ψ χ hψ hχ f.toAdditive hf F hF).mpr
  rw [← _root_.groupCohomology.functor_map]
  exact ConcreteCategory.bijective_of_isIso
    ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
      (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)))

end TauCeti
