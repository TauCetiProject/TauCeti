/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.Equivariant
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ProjectiveKernel
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

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
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    let B := ofModuleMonoidAlgebra.obj (ModuleCat.of (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
      (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g))
    let e := freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
    let ψ : Additive (abelianizationProP p (freeProfiniteGroup ι)
        (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) ≃+ B :=
      e.trans (RestrictScalars.addEquiv ℤ_[p] (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L))
        (MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g)).symm
    let c : _root_.groupCohomology.cocycles₂ B :=
      ⟨fun q ↦ ψ ((z : _ → _) q), by
        rw [_root_.groupCohomology.mem_cocycles₂_iff]
        intro a b d
        -- In this representation the action is the group-algebra monomial action.
        change e (z.val (a * b, d)) + e (z.val (a, b)) =
          MonoidAlgebra.single a (1 : ℤ_[p]) • e (z.val (b, d)) + e (z.val (a, b * d))
        simpa only [e, map_add,
          freeProfiniteGroup.abelianizationProPEquivRelationModule_presentation_smul]
          using congrArg e ((mem_Z2_iff.mp z.property).2 a b d)⟩
    simp only [explicitCoeff2_mk]
    rw [freeProfiniteGroup.explicitH2EquivRelationModule_mk p hg z c (fun _ ↦ rfl)]
    have hmap := ConcreteCategory.congr_hom
      (_root_.groupCohomology.H2π_comp_map (MonoidHom.id (L ≃ₐ[K] L))
        (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))) c
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    refine Eq.trans (b := _root_.groupCohomology.H2π _
      (_root_.groupCohomology.mapCocycles₂ (MonoidHom.id (L ≃ₐ[K] L))
        (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β)) c)) ?_ ?_
    · apply explicitH2EquivPadicCompletionUnits_mk
      rintro ⟨a, b⟩
      rw [TauCeti.groupCohomology.mapCocycles₂_apply]
      -- Evaluate the coefficient morphisms on their underlying additive carriers.
      erw [cocyclesMap2_apply]
      simp [ofModuleMonoidAlgebra, c, ψ, e, RestrictScalars.addEquiv]
      rfl
    · convert hmap.symm using 1
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
  have := groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ 1
  let e₁ := freeProfiniteGroup.explicitH2EquivRelationModule p hg
  let e₂ := explicitH2EquivPadicCompletionUnits p K L j
  let f := relationModuleToAbelianizationProPEquivariant p K L hg β j
  let hf := f.continuous_toAdditive
    (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j)
  let b := (_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
    (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))
  have heq : ⇑e₂ ∘ explicitCoeff2 (L ≃ₐ[K] L) _ f.toAdditive hf = ⇑b ∘ ⇑e₁ :=
    funext (explicitH2EquivPadicCompletionUnits_explicitCoeff2_relationModule p K L hg β j)
  apply (Function.Bijective.of_comp_iff' e₂.bijective _).mp
  rw [heq]
  exact (ConcreteCategory.bijective_of_isIso b).comp e₁.bijective

end TauCeti
