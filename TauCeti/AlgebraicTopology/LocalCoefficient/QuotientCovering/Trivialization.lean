/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Exact

/-!
# Trivializing an associated local system on its covering space

Let `p : E ⟶ B` be a quotient covering by `G`, and let `A` be a representation of `G`.
The pullback to `E` of the associated local system is canonically constant:
`IsQuotientCoveringMap.associatedLocalSystemPullbackIso` identifies its fibre at `e` with
`A` using the sheet `e` itself. No connectedness or simple connectivity is needed.

The sheet coordinates are compatible with transport and with coefficient maps. Changing
from a sheet `e` to `g • e` multiplies the coordinates by `A.ρ g`, not by `A.ρ g⁻¹`.
Equivalently, the tensor class using the new sheet has old coordinates `A.ρ g⁻¹ a`.
These formulas fix the equivariance convention when identifying local-system-valued
cochains downstairs with equivariant cochains upstairs, without taking any duals of `A`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (A : Rep.{u} k G)

/-- Transport keeps the coefficient unchanged when the chosen sheet is transported too. -/
@[reassoc]
lemma associatedLocalSystemFiberIso_inv_map {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemFiberIso k A e).inv ≫ (hG.associatedLocalSystem k A).map γ =
      (hG.associatedLocalSystemFiberIso k A (hG.isCoveringMap.monodromy γ e)).inv := by
  ext a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [associatedLocalSystemFiberIso_inv_apply, associatedLocalSystem_map_coinvariantsTensorMk,
    associatedLocalSystemFiberIso_inv_apply]
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- In coordinates given by a sheet and its transported sheet, transport is the identity. -/
@[reassoc]
lemma associatedLocalSystemFiberIso_map_hom {x y : FundamentalGroupoid B} (γ : x ⟶ y)
    (e : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystem k A).map γ ≫
        (hG.associatedLocalSystemFiberIso k A (hG.isCoveringMap.monodromy γ e)).hom =
      (hG.associatedLocalSystemFiberIso k A e).hom := by
  apply (cancel_epi (hG.associatedLocalSystemFiberIso k A e).inv).1
  simp [← Category.assoc, associatedLocalSystemFiberIso_inv_map]

/-- Transition between two choices of sheet is the inverse action of the unique group
element carrying the first sheet to the second. -/
lemma associatedLocalSystemFiberIso_inv_comp_hom {x : FundamentalGroupoid B}
    (e e' : p ⁻¹' {x.as}) :
    (hG.associatedLocalSystemFiberIso k A e').inv ≫
        (hG.associatedLocalSystemFiberIso k A e).hom =
      ModuleCat.ofHom (A.ρ (hG.fiberEquivGroup e e')⁻¹) := by
  ext a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [associatedLocalSystemFiberIso_inv_apply,
    associatedLocalSystemFiberIso_hom_coinvariantsTensorMk]
  simp

/-- Changing the coordinate sheet from `e` to `g • e` acts on coordinates by `A.ρ g`.
The local-system fibre itself is unchanged. -/
@[simp]
lemma associatedLocalSystemFiberIso_hom_smul {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (g : G) :
    letI := hG.mulActionFiber x.as
    (hG.associatedLocalSystemFiberIso k A (g • e)).hom =
      (hG.associatedLocalSystemFiberIso k A e).hom ≫ ModuleCat.ofHom (A.ρ g) := by
  let := hG.mulActionFiber x.as
  have hg : hG.fiberEquivGroup (g • e) e = g⁻¹ := by
    apply (hG.fiberEquivGroup_eq_iff _ _ _).2
    simp
  apply (cancel_epi (hG.associatedLocalSystemFiberIso k A e).inv).1
  rw [associatedLocalSystemFiberIso_inv_comp_hom, hg]
  simp

/-- The inverse coordinate map at `g • e` inserts the inverse translate of the coefficient
in the old sheet. -/
@[simp]
lemma associatedLocalSystemFiberIso_inv_smul {x : FundamentalGroupoid B}
    (e : p ⁻¹' {x.as}) (g : G) :
    letI := hG.mulActionFiber x.as
    (hG.associatedLocalSystemFiberIso k A (g • e)).inv =
      ModuleCat.ofHom (A.ρ g⁻¹) ≫ (hG.associatedLocalSystemFiberIso k A e).inv := by
  let := hG.mulActionFiber x.as
  have hg : hG.fiberEquivGroup e (g • e) = g := by
    apply (hG.fiberEquivGroup_eq_iff _ _ _).2
    rfl
  apply (cancel_mono (hG.associatedLocalSystemFiberIso k A e).hom).1
  rw [associatedLocalSystemFiberIso_inv_comp_hom, hg]
  simp

/-- The associated local system becomes canonically constant on the covering space. At
`e : E`, its fibre is identified with `A` using `e` as the chosen sheet. -/
def associatedLocalSystemPullbackIso :
    (LocalCoefficientSystem.pullback p.hom).obj (hG.associatedLocalSystem k A) ≅
      (LocalCoefficientSystem.constantFunctor E).obj (ModuleCat.of k A) :=
  NatIso.ofComponents (fun e ↦ hG.associatedLocalSystemFiberIso k A ⟨e.as, rfl⟩) (by
    intro x y γ
    simp only [LocalCoefficientSystem.pullback_obj_map,
      LocalCoefficientSystem.constantFunctor_obj_map]
    have h := hG.associatedLocalSystemFiberIso_map_hom k A
      ((FundamentalGroupoid.map p.hom).map γ) ⟨x.as, rfl⟩
    have he : hG.isCoveringMap.monodromy ((FundamentalGroupoid.map p.hom).map γ)
        ⟨x.as, rfl⟩ = ⟨y.as, rfl⟩ := hG.isCoveringMap.monodromy_map γ
    rwa [he] at h)

/-- The trivialization uses the sheet at which the pullback fibre is evaluated. -/
@[simp]
lemma associatedLocalSystemPullbackIso_hom_app (e : FundamentalGroupoid E) :
    (hG.associatedLocalSystemPullbackIso k A).hom.app e =
      (hG.associatedLocalSystemFiberIso k A ⟨e.as, rfl⟩).hom :=
  (rfl)

/-- The inverse trivialization inserts the chosen sheet. -/
@[simp]
lemma associatedLocalSystemPullbackIso_inv_app (e : FundamentalGroupoid E) :
    (hG.associatedLocalSystemPullbackIso k A).inv.app e =
      (hG.associatedLocalSystemFiberIso k A ⟨e.as, rfl⟩).inv :=
  (rfl)

/-- The canonical trivialization on the cover is natural in the coefficient representation. -/
@[reassoc]
lemma associatedLocalSystemPullbackIso_hom_naturality {A A' : Rep.{u} k G} (f : A ⟶ A') :
    (LocalCoefficientSystem.pullback p.hom).map (hG.associatedLocalSystemMap k f) ≫
        (hG.associatedLocalSystemPullbackIso k A').hom =
      (hG.associatedLocalSystemPullbackIso k A).hom ≫
        (LocalCoefficientSystem.constantFunctor E).map
          ((forget₂ (Rep k G) (ModuleCat k)).map f) := by
  ext e : 2
  exact hG.associatedLocalSystemFiberIso_hom_naturality k f ⟨e.as, rfl⟩

end IsQuotientCoveringMap
