/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Reciprocity
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Topology

/-!
# Relation-module maps on arithmetic extension kernels

Let `L/K` be a finite extension of local fields of characteristic zero, `g` a finite generating
family of `Gal(L/K)`, and `R` the kernel of the resulting free profinite presentation. An
algebraic `ℤ_p[Gal(L/K)]`-linear map `β : relationModule → A(L)` defines a continuous
homomorphism `R^ab(p) → V^ab(p)`, where `V` is the subgroup of `G_K` fixing `L`.

The map is exactly `β` read through Lyndon's isomorphism and local reciprocity. It preserves
surjectivity, and for normal `L/K` it is equivariant for the quotient actions. Thus the integral
relation-module surjection can be used as a map of kernels of profinite group extensions.
No compatibility of extension classes is asserted here.

## Main declarations

* `TauCeti.relationModuleToAbelianizationProP`: the continuous transport of a relation-module map.
* `TauCeti.relationModuleToAbelianizationProP_surjective_iff`: surjectivity is preserved and
  reflected.
* `TauCeti.relationModuleToAbelianizationProP_smul`: the transport is equivariant.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

noncomputable section

namespace TauCeti

open Additive

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [CharZero L]
  {ι : Type} [Fintype ι] [DecidableEq ι] {g : ι → L ≃ₐ[K] L}
  (hg : Subgroup.closure (Set.range g) = ⊤)
  (β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
    Additive ↑(padicCompletionUnits p L))
  (j : L →ₐ[K] SeparableClosure K)

/-- Read an algebraic relation-module map as a continuous homomorphism between the abelian
pro-`p` kernels of the free profinite presentation and the arithmetic extension, using Lyndon's
isomorphism and local reciprocity. -/
def relationModuleToAbelianizationProP :
    abelianizationProP p (freeProfiniteGroup ι)
        (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker →ₜ*
      abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup :=
  (padicCompletionUnitsEquivAbelianizationProP p K L j : _ →ₜ* _).comp
    { toFun := fun x ↦ (β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
        (ofMul x))).toMul
      map_one' := by simp
      map_mul' := by intros; simp
      continuous_toFun := continuous_toMul.comp
        ((freeProfiniteGroup.continuous_comp_abelianizationProPEquivRelationModule p hg
          (β.restrictScalars ℤ_[p])).comp continuous_ofMul) }

/-- The transported map is `β` between Lyndon's coordinates and the reciprocity coordinates. -/
@[simp]
theorem relationModuleToAbelianizationProP_apply
    (x : abelianizationProP p (freeProfiniteGroup ι)
      (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) :
    relationModuleToAbelianizationProP p K L hg β j x =
      padicCompletionUnitsEquivAbelianizationProP p K L j
        (β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg (ofMul x))).toMul :=
  (rfl)

/-- A relation-module map is surjective exactly when its continuous transport to the arithmetic
extension kernel is surjective. -/
@[simp]
theorem relationModuleToAbelianizationProP_surjective_iff :
    Function.Surjective (relationModuleToAbelianizationProP p K L hg β j) ↔
      Function.Surjective β := by
  let e := freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
  let a := padicCompletionUnitsEquivAbelianizationProP p K L j
  have hright : Function.Surjective (fun x ↦ e (ofMul x)) :=
    e.surjective.comp Additive.ofMul.surjective
  have hleft : Function.Bijective (fun x : Additive ↑(padicCompletionUnits p L) ↦ a x.toMul) :=
    a.bijective.comp Additive.toMul.bijective
  have hmap : ⇑(relationModuleToAbelianizationProP p K L hg β j) =
      (fun x : Additive ↑(padicCompletionUnits p L) ↦ a x.toMul) ∘ β ∘
        (fun x ↦ e (ofMul x)) :=
    funext (relationModuleToAbelianizationProP_apply p K L hg β j)
  rw [hmap]
  exact (Function.Surjective.of_comp_iff' hleft _).trans
    (Function.Surjective.of_comp_iff β hright)

variable [Normal K L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]

/-- The transported relation-module map intertwines the quotient conjugation actions whenever
`f ∈ F` and `s ∈ G_K` induce the same automorphism of `L`. -/
theorem relationModuleToAbelianizationProP_smul
    (f : freeProfiniteGroup ι) (s : AbsoluteGaloisGroup K)
    (hfs : freeProfiniteGroup.lift g f = j.restrictNormalHom s)
    (x : abelianizationProP p (freeProfiniteGroup ι)
      (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) :
    relationModuleToAbelianizationProP p K L hg β j
        ((f : freeProfiniteGroup ι ⧸
          (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) • x) =
      (s : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L j).toSubgroup) •
        relationModuleToAbelianizationProP p K L hg β j x := by
  rw [relationModuleToAbelianizationProP_apply, relationModuleToAbelianizationProP_apply,
    ofMul_smul, freeProfiniteGroup.abelianizationProPEquivRelationModule_smul,
    β.map_smul, hfs]
  have hβ := padicCompletionUnits_single_smul p L K (j.restrictNormalHom s) 1
    (β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg (ofMul x))).toMul
  simp only [ofMul_toMul, one_smul] at hβ
  rw [hβ, toMul_ofMul]
  exact padicCompletionUnitsEquivAbelianizationProP_smul p K L j s
    (β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg (ofMul x))).toMul

end TauCeti
