/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.Presentation
import TauCeti.NumberTheory.LocalField.ClassModule.Basic
import TauCeti.NumberTheory.LocalField.Generation.Presentation
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.Cohomology
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.ProjectiveKernel

/-!
# Relation-module surjections for arbitrary finite local Galois layers

Let `L/K` be a finite Galois extension of finite extensions of `ℚ_p`, and put
`N = [K : ℚ_p]`. For every generating family of `Gal(L/K)` with at least `N + 2` members, its
relation module over `ℤ_p` surjects onto the completed multiplicative group `A(L)`.
There is no tame-ramification hypothesis and no free presentation supplied as input.

Gaschütz's lemma lifts the prescribed family to topological generators of `G_K`, giving
a compatible surjection from the free profinite group on the same index type. Lyndon's
isomorphism and local reciprocity then give the relation-module surjection.

When the family has exactly `N + 2` members, the map induced by the lifted presentation is
surjective on second cohomology. Its kernel is therefore the regular
`ℤ_p[Gal(L/K)]`-module, giving the exact sequence in NSW (7.4.2)(i).

## Main results

* `TauCeti.exists_relationModule_surjective_of_card_le`: every generating family of size at least
  `[K : ℚ_p] + 2` gives an equivariant surjection from its relation module onto `A(L)`.
* `TauCeti.exists_relationModule_surjective`: for a generating family of size exactly
  `[K : ℚ_p] + 2`, the surjection has kernel `ℤ_p[Gal(L/K)]`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (5.6.6) and the proof of (7.4.2)(i).
-/

public section

namespace TauCeti

/-- For a finite Galois extension `L/K` of finite extensions of `ℚ_p`, the relation module
of every generating family of `Gal(L/K)` with at least `[K : ℚ_p] + 2` members admits a
`ℤ_p[Gal(L/K)]`-linear surjection onto the completed multiplicative group `A(L)`.
No ramification hypothesis or choice of presentation of the absolute Galois group is needed. -/
theorem exists_relationModule_surjective_of_card_le (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [Module.Finite ℚ_[p] L]
    [IsGalois K L] {ι : Type} [Fintype ι] {g : ι → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hι : Module.finrank ℚ_[p] K + 2 ≤ Fintype.card ι) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[
        MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L),
      Function.Surjective β := by
  classical
  have : FiniteDimensional K L := .right ℚ_[p] K L
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  let _ := algebraicExtensionValuativeRel ℚ_[p] L
  let _ := algebraicExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have := algebraicExtension_valuativeExtension ℚ_[p] L
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_presentation_of_card_le p K L hg hι j
  obtain ⟨β, hβ, -⟩ :=
    exists_relationModule_surjective_of_presentation p K L hg j φ hcomp hφ
  exact ⟨β, hβ⟩

noncomputable section

open Additive CategoryTheory ContCohomology freeProfiniteGroup _root_.Rep

section Presentation

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Normal K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]
  {ι : Type} [Fintype ι] [DecidableEq ι] {g : ι → L ≃ₐ[K] L}
  (hg : Subgroup.closure (Set.range g) = ⊤) (j : L →ₐ[K] SeparableClosure K)
  (φ : freeProfiniteGroup ι →ₜ* AbsoluteGaloisGroup K)
  (hφ : ∀ x, j.restrictNormalHom (φ x) = freeProfiniteGroup.lift g x)

include hg j hφ

local instance : CompactSpace
    (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker :=
  isCompact_iff_compactSpace.mp (freeProfiniteGroup.lift g).isClosed_ker.isCompact

private abbrev IsRelationModuleMapOfPresentation
    (β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g
      →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L)) : Prop :=
  ∀ r : (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker,
    padicCompletionUnitsEquivAbelianizationProP p K L j
        (β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
          (ofMul (abelianizationProPMk p _ _ r)))).toMul =
      abelianizationProPMk p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup
        ⟨φ r, by
          rw [galoisSubgroup_toSubgroup, ← j.ker_restrictNormalHom,
            MonoidHom.mem_ker, hφ]
          exact MonoidHom.mem_ker.mp r.2⟩

private theorem explicitCoeff2_contCohomologyClass_of_presentation
    (hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)))
    (β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g
      →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L))
    (hβ_apply : IsRelationModuleMapOfPresentation p K L hg j φ hφ β) :
    letI := freeProfiniteGroup.presentationClassModuleAction p hd
    letI := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
    letI := galoisClassModuleAction p K L j
    letI := continuousSMul_galoisClassModuleAction p K L j
    (explicitCoeff2 (L ≃ₐ[K] L) _
      (relationModuleToAbelianizationProPEquivariant p K L hg β j).toAdditive
      ((relationModuleToAbelianizationProPEquivariant p K L hg β j).continuous_toAdditive
        (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j)))
        (freeProfiniteGroup.presentationProfiniteExtension p hd).contCohomologyClass =
      (galoisClassModuleExtension p K L j).contCohomologyClass := by
  let R := (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker
  let V := (galoisSubgroup K L j).toSubgroup
  have hRV : R ≤ V.comap φ.toMonoidHom := by
    intro r hr
    -- Expose membership in the abbreviations `R` and `V` so the kernel lemmas apply.
    change φ r ∈ (galoisSubgroup K L j).toSubgroup
    rw [galoisSubgroup_toSubgroup, ← j.ker_restrictNormalHom, MonoidHom.mem_ker]
    simpa [R] using (hφ r).trans (MonoidHom.mem_ker.mp hr)
  let _ := freeProfiniteGroup.presentationClassModuleAction p hd
  have := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
  let _ := galoisClassModuleAction p K L j
  have := continuousSMul_galoisClassModuleAction p K L j
  let X := freeProfiniteGroup.presentationProfiniteExtension p hd
  let Y := galoisClassModuleExtension p K L j
  let ψ : X.E →ₜ* Y.E := abelianizationProPExtensionMap p φ.toMonoidHom φ.continuous hRV
  have hright : Y.toGroupExtension.rightHom.comp ψ.toMonoidHom =
      X.toGroupExtension.rightHom := by
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro f
    simp only [MonoidHom.comp_apply]
    calc
      Y.toGroupExtension.rightHom (ψ (QuotientGroup.mk f)) =
          Y.toGroupExtension.rightHom (QuotientGroup.mk (φ f)) := congrArg _
            (abelianizationProPExtensionMap_mk p φ.toMonoidHom φ.continuous hRV f)
      _ = j.restrictNormalHom (φ f) := by
        simp [Y]
      _ = freeProfiniteGroup.lift g f := hφ f
      _ = X.toGroupExtension.rightHom (QuotientGroup.mk f) := by
        simp [X]
  let k := relationModuleToAbelianizationProPEquivariant p K L hg β j
  have hk_map : k.toMonoidHom = abelianizationProPMap p φ.toMonoidHom φ.continuous hRV := by
    apply MonoidHom.ext
    intro x
    obtain ⟨r, rfl⟩ := abelianizationProPMk_surjective p (freeProfiniteGroup ι) R x
    -- Expose the map applications hidden by `k` and `R` so their application lemmas rewrite.
    change relationModuleToAbelianizationProPEquivariant p K L hg β j
        (abelianizationProPMk p (freeProfiniteGroup ι) R r) = _
    rw [relationModuleToAbelianizationProPEquivariant_apply,
      relationModuleToAbelianizationProP_apply, abelianizationProPMap_mk]
    exact hβ_apply r
  have hinl : ψ.toMonoidHom.comp X.toGroupExtension.inl =
      Y.toGroupExtension.inl.comp k.toMonoidHom := by
    rw [hk_map]
    simpa [X, Y, ψ] using
      abelianizationProPExtensionMap_comp_inl p φ.toMonoidHom φ.continuous hRV
  let c := explicitCoeff2 (L ≃ₐ[K] L) _ k.toAdditive
    (k.continuous_toAdditive (continuous_relationModuleToAbelianizationProPEquivariant
      p K L hg β j))
  have hc : c X.contCohomologyClass = Y.contCohomologyClass := by
    rw [← X.contCohomologyClass_map k
      (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j)]
    exact X.contCohomologyClass_map_eq_of_continuous_monoidHom k
      (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j) Y
      ψ.toMonoidHom ψ.continuous hinl hright
  exact hc

omit hg hφ [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [CharZero L] [ValuativeExtension ℚ_[p] L] in
private theorem zmultiples_galoisClassModuleExtension_contCohomologyClass_eq_top :
    letI := galoisClassModuleAction p K L j
    letI := continuousSMul_galoisClassModuleAction p K L j
    AddSubgroup.zmultiples (galoisClassModuleExtension p K L j).contCohomologyClass = ⊤ := by
  have : Module.Finite ℚ_[p] K := .left ℚ_[p] K L
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsAlgebraic ℚ_[p] K := Algebra.IsAlgebraic.of_finite ℚ_[p] K
  let _ := algebraicExtensionValuativeRel ℚ_[p] K
  let _ := algebraicExtensionNormedFieldTopology ℚ_[p] K
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] K
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hpK : IsUnit (p : K) := isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  exact (galoisClassModuleExtension_contCohomologyClass_generates K L hpK j).1

private theorem surjective_explicitCoeff2_of_presentation
    (hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)))
    (β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g
      →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L))
    (hβ_apply : IsRelationModuleMapOfPresentation p K L hg j φ hφ β) :
    letI := freeProfiniteGroup.presentationClassModuleAction p hd
    letI := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
    letI := galoisClassModuleAction p K L j
    letI := continuousSMul_galoisClassModuleAction p K L j
    Function.Surjective (explicitCoeff2 (L ≃ₐ[K] L) _
      (relationModuleToAbelianizationProPEquivariant p K L hg β j).toAdditive
      ((relationModuleToAbelianizationProPEquivariant p K L hg β j).continuous_toAdditive
        (continuous_relationModuleToAbelianizationProPEquivariant p K L hg β j))) := by
  let _ := freeProfiniteGroup.presentationClassModuleAction p hd
  have := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
  let _ := galoisClassModuleAction p K L j
  have := continuousSMul_galoisClassModuleAction p K L j
  let X := freeProfiniteGroup.presentationProfiniteExtension p hd
  let Y := galoisClassModuleExtension p K L j
  let k := relationModuleToAbelianizationProPEquivariant p K L hg β j
  let c := explicitCoeff2 (L ≃ₐ[K] L) _ k.toAdditive
    (k.continuous_toAdditive (continuous_relationModuleToAbelianizationProPEquivariant
      p K L hg β j))
  have hc : c X.contCohomologyClass = Y.contCohomologyClass :=
    explicitCoeff2_contCohomologyClass_of_presentation p K L hg j φ hφ hd β hβ_apply
  have hgen := zmultiples_galoisClassModuleExtension_contCohomologyClass_eq_top p K L j
  have hcs : Function.Surjective c :=
    AddMonoidHom.range_eq_top.mp <| top_unique <|
      hgen ▸ AddSubgroup.zmultiples_le.mpr ⟨X.contCohomologyClass, hc⟩
  simpa only [c, k] using hcs

private theorem surjective_groupCohomology_two_of_presentation
    (hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)))
    (β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g
      →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L))
    (hβ_apply : IsRelationModuleMapOfPresentation p K L hg j φ hφ β) :
    Function.Surjective ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
      (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))) := by
  let _ := freeProfiniteGroup.presentationClassModuleAction p hd
  have := freeProfiniteGroup.continuousSMul_presentationClassModuleAction p hd
  let _ := galoisClassModuleAction p K L j
  have := continuousSMul_galoisClassModuleAction p K L j
  let k := relationModuleToAbelianizationProPEquivariant p K L hg β j
  let c := explicitCoeff2 (L ≃ₐ[K] L) _ k.toAdditive
    (k.continuous_toAdditive (continuous_relationModuleToAbelianizationProPEquivariant
      p K L hg β j))
  have hcs : Function.Surjective c :=
    surjective_explicitCoeff2_of_presentation p K L hg j φ hφ hd β hβ_apply
  let eL := freeProfiniteGroup.explicitH2EquivRelationModule p hg
  let eR := explicitH2EquivPadicCompletionUnits p K L j
  intro y
  obtain ⟨x, hx⟩ := hcs (eR.symm y)
  refine ⟨eL x, ?_⟩
  have hcomm :=
    explicitH2EquivPadicCompletionUnits_explicitCoeff2_relationModule p K L hg β j x
  exact hcomm.symm.trans ((congrArg eR hx).trans (eR.apply_symm_apply y))

omit [DecidableEq ι] in
private theorem exists_relationModule_surjective_h2_surjective_of_presentation
    (hsurj : Function.Surjective φ) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g
        →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L),
      Function.Surjective β ∧
        Function.Surjective ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
          (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))) := by
  classical
  obtain ⟨β, hβ, hβ_apply⟩ :=
    exists_relationModule_surjective_of_presentation p K L hg j φ hφ hsurj
  have hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  exact ⟨β, hβ,
    surjective_groupCohomology_two_of_presentation p K L hg j φ hφ hd β hβ_apply⟩

end Presentation

/-- For a finite Galois extension `L/K` of finite extensions of `ℚ_p`, the relation module
of every generating family of `Gal(L/K)` with exactly `[K : ℚ_p] + 2` members surjects onto
the completed multiplicative group `A(L)`, with kernel isomorphic to the regular
`ℤ_p[Gal(L/K)]`-module. -/
theorem exists_relationModule_surjective (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [Module.Finite ℚ_[p] L]
    [IsGalois K L] {ι : Type} [Fintype ι] {g : ι → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hι : Fintype.card ι = Module.finrank ℚ_[p] K + 2) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[
        MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L),
      Function.Surjective β ∧
        Nonempty (LinearMap.ker β ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
          MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) := by
  classical
  have : FiniteDimensional K L := .right ℚ_[p] K L
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  let _ := algebraicExtensionValuativeRel ℚ_[p] L
  let _ := algebraicExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have := algebraicExtension_valuativeExtension ℚ_[p] L
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_presentation_of_card_le p K L hg
    (hι ▸ le_rfl) j
  obtain ⟨β, hβ, h2⟩ :=
    exists_relationModule_surjective_h2_surjective_of_presentation
      p K L hg j φ hcomp hφ
  exact ⟨β, hβ,
    nonempty_ker_linearEquiv_of_relationModule_surjective_of_h2_surjective p hg hι hβ h2⟩

end

end TauCeti
