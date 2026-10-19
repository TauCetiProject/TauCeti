/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ClassModule
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Extension

/-!
# Equivariant relation-module maps over a common Galois quotient

An algebraic relation-module map to the completed multiplicative group of a finite normal
extension of `p`-adic fields gives a continuous homomorphism between the free and arithmetic
pro-`p` class-module kernels via `relationModuleToAbelianizationProP`. Here that homomorphism
is bundled as equivariant for `Gal(L/K)`.
The source uses the action of the presented group on its relation group, and the target uses
the arithmetic conjugation action transported through the Galois correspondence.

Thus the map has the coefficient-map type required to lift a surjection between kernels to
a surjection of profinite extensions. Continuity and surjectivity agree with the existing
transport through Lyndon's isomorphism and local reciprocity; no condition on extension
classes is imposed or proved here.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public noncomputable section

namespace TauCeti

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

/-- A relation-module map, transported through Lyndon and reciprocity, as an equivariant
homomorphism for the common quotient `Gal(L/K)` of the free and arithmetic extensions. -/
def relationModuleToAbelianizationProPEquivariant :
    letI := freeProfiniteGroup.presentationClassModuleAction p (g := g)
      (by rw [hg, Subgroup.coe_top]; exact dense_univ)
    letI := galoisClassModuleAction p K L j
    abelianizationProP p (freeProfiniteGroup ι)
        (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker →*[L ≃ₐ[K] L]
      abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup := by
  have hd : Dense (Subgroup.closure (Set.range g) : Set (L ≃ₐ[K] L)) := by
    rw [hg, Subgroup.coe_top]
    exact dense_univ
  letI := freeProfiniteGroup.presentationClassModuleAction p hd
  letI := galoisClassModuleAction p K L j
  refine { (relationModuleToAbelianizationProP p K L hg β j).toMonoidHom with
    map_smul' := ?_ }
  intro t x
  simp only [MonoidHom.id_apply]
  obtain ⟨f, rfl⟩ := freeProfiniteGroup.lift_surjective hd t
  obtain ⟨q, hq⟩ := (quotientGaloisSubgroupEquiv K L j).surjective (freeProfiniteGroup.lift g f)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  rw [quotientGaloisSubgroupEquiv_mk] at hq
  rw [freeProfiniteGroup.presentationClassModuleAction_lift_smul, ← hq,
    galoisClassModuleAction_restrict_smul]
  exact relationModuleToAbelianizationProP_smul p K L hg β j f s hq.symm x

/-- The equivariant transport has the same underlying map as the continuous transport. -/
@[simp]
theorem relationModuleToAbelianizationProPEquivariant_apply
    (x : abelianizationProP p (freeProfiniteGroup ι)
      (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker) :
    relationModuleToAbelianizationProPEquivariant p K L hg β j x =
      relationModuleToAbelianizationProP p K L hg β j x :=
  (rfl)

/-- The equivariant kernel transport is continuous. -/
theorem continuous_relationModuleToAbelianizationProPEquivariant :
    Continuous (relationModuleToAbelianizationProPEquivariant p K L hg β j) :=
  (relationModuleToAbelianizationProP p K L hg β j).continuous.congr
    (fun x ↦ (relationModuleToAbelianizationProPEquivariant_apply p K L hg β j x).symm)

/-- The equivariant kernel transport is surjective exactly when the algebraic
relation-module map is surjective. -/
@[simp]
theorem relationModuleToAbelianizationProPEquivariant_surjective_iff :
    Function.Surjective (relationModuleToAbelianizationProPEquivariant p K L hg β j) ↔
      Function.Surjective β := by
  have hmap : ⇑(relationModuleToAbelianizationProPEquivariant p K L hg β j) =
      ⇑(relationModuleToAbelianizationProP p K L hg β j) :=
    funext (relationModuleToAbelianizationProPEquivariant_apply p K L hg β j)
  rw [hmap]
  exact relationModuleToAbelianizationProP_surjective_iff p K L hg β j

end TauCeti
