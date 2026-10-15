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
    letI := galoisClassModuleAction p K L j
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
  intro x
  unfold explicitH2EquivPadicCompletionUnits freeProfiniteGroup.explicitH2EquivRelationModule
  rw [_root_.groupCohomology.functor_map]
  apply explicitH2AddEquivGroupCohomology_explicitCoeff2
  intro m
  change ofMul ((padicCompletionUnitsEquivAbelianizationProP p K L j).symm
      (relationModuleToAbelianizationProPEquivariant p K L hg β j m.toMul)) =
    β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg m)
  rw [relationModuleToAbelianizationProPEquivariant_apply,
    relationModuleToAbelianizationProP_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- A surjective arithmetic relation-module map with projective kernel induces a bijection
on explicit second cohomology after transport through Lyndon and local reciprocity. -/
theorem bijective_explicitCoeff2_relationModuleToAbelianizationProPEquivariant
    (hβ : Function.Surjective β)
    [Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker β)] :
    letI := freeProfiniteGroup.presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := galoisClassModuleAction p K L j
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
  let B := ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
    (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g))
  let C := ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
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
    change eL (t • x) = MonoidAlgebra.single t (1 : ℤ_[p]) • eL x
    exact freeProfiniteGroup.abelianizationProPEquivRelationModule_presentation_smul p hg t x
  have hχ : ∀ t x, χ (t • x) = C.ρ t (χ x) := fun t x => by
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
    simp [χ, ψ, F, ofModuleMonoidAlgebra, RestrictScalars.addEquiv, f,
      relationModuleToAbelianizationProP_apply]
  haveI : IsIso (_root_.groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) F 2) := by
    simpa only [_root_.groupCohomology.functor_map, F] using
      (groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ 1)
  exact explicitCoeff2_bijective_of_isIso
    (.refl (L ≃ₐ[K] L)) ψ χ hψ hχ f.toAdditive hf F hF

end TauCeti
