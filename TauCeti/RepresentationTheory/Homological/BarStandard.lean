/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.Resolution

/-!
# Naturality of the bar-standard comparison along a group homomorphism

Mathlib's chain isomorphism `Rep.barComplex.isoStandardComplex`, constructed in
`Mathlib.RepresentationTheory.Homological.Resolution` from `Rep.diagonalSuccIsoFree`, identifies
the inhomogeneous bar resolution `Rep.barComplex k G` with the homogeneous standard resolution
`Rep.standardComplex k G`. In degree `m` its forward map sends `g • [g₁ | ⋯ | gₘ]` to
`g • (1, g₁, g₁g₂, …, g₁⋯gₘ)`, while its inverse sends `(g₀, …, gₘ)` to
`g₀ • [g₀⁻¹g₁ | ⋯ | gₘ₋₁⁻¹gₘ]`.

This file computes that inverse formula on basis elements (`diagonalSuccIsoFree_hom_hom_single`)
and proves that both directions of `Rep.barComplex.isoStandardComplex` intertwine the relabelling
chain maps `TauCeti.Rep.barComplex.resChainMap` and `MonoidHom.standardComplexMap` along any group
homomorphism `φ : G →* H`. No injectivity or projectivity-preservation assumption on `φ` is needed.

## Main results

* `TauCeti.Rep.diagonalSuccIsoFree_hom_hom_single`: the homogeneous-to-inhomogeneous comparison
  sends `(g₀, …, gₘ)` with coefficient `r` to `g₀ • [g₀⁻¹g₁ | ⋯ | gₘ₋₁⁻¹gₘ]` with coefficient `r`.
* `MonoidHom.barComplex_isoStandardComplex_hom_naturality` and
  `MonoidHom.barComplex_isoStandardComplex_inv_naturality`: the isomorphism between bar and
  standard complexes commutes with change of groups along any group homomorphism.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §5 and Chapter III, §8.
-/

public section

noncomputable section

open CategoryTheory Finsupp

namespace TauCeti.Rep

open _root_.Rep

universe u

/-- The homogeneous-to-inhomogeneous comparison `(Rep.diagonalSuccIsoFree k G m).hom` sends the
standard basis element `(y₀, …, yₘ)` with coefficient `r` to the bar basis element
`(y₀⁻¹y₁, …, yₘ₋₁⁻¹yₘ)` with group coefficient `r • y₀`. -/
theorem diagonalSuccIsoFree_hom_hom_single {k G : Type u} [CommRing k] [Group G]
    (m : ℕ) (y : Fin (m + 1) → G) (r : k) :
    (diagonalSuccIsoFree k G m).hom.hom (MonoidAlgebra.single y r) =
      single (fun i : Fin m ↦ (y i.castSucc)⁻¹ * y i.succ)
        (MonoidAlgebra.single (y 0) r) := by
  have hinv := diagonalSuccIsoFree_inv_hom_single (k := k) (G := G) m
    (fun i : Fin m ↦ (y i.castSucc)⁻¹ * y i.succ) (y 0) r
  rw [Fin.partialProd_left_inv y] at hinv
  have h := congrArg (diagonalSuccIsoFree k G m).hom.hom hinv
  rw [← Representation.IntertwiningMap.comp_apply, ← Rep.hom_comp, Iso.inv_hom_id,
    Rep.hom_id, Representation.IntertwiningMap.id_apply] at h
  exact h.symm

namespace barComplex

/-- In degree `n` the forward bar-to-standard isomorphism is `(Rep.diagonalSuccIsoFree k G n).inv`.
-/
@[simp]
theorem isoStandardComplex_hom_f (k G : Type u) [CommRing k] [Group G] (n : ℕ) :
    (_root_.Rep.barComplex.isoStandardComplex k G).hom.f n =
      (diagonalSuccIsoFree k G n).inv :=
  (rfl)

/-- In degree `n` the inverse standard-to-bar isomorphism is `(Rep.diagonalSuccIsoFree k G n).hom`.
-/
@[simp]
theorem isoStandardComplex_inv_f (k G : Type u) [CommRing k] [Group G] (n : ℕ) :
    (_root_.Rep.barComplex.isoStandardComplex k G).inv.f n =
      (diagonalSuccIsoFree k G n).hom :=
  (rfl)

end barComplex

end TauCeti.Rep

namespace MonoidHom

universe u

/-- Applying a monoid homomorphism entrywise commutes with `Fin.partialProd`. -/
theorem comp_partialProd {G : Type*} {H : Type*} [Monoid G] [Monoid H]
    (φ : G →* H) {n : ℕ} (x : Fin n → G) :
    φ ∘ Fin.partialProd x = Fin.partialProd (φ ∘ x) := by
  funext i
  induction i using Fin.inductionOn with
  | zero => simp
  | succ j hj =>
    simp only [Function.comp_apply] at hj ⊢
    rw [Fin.partialProd_succ, map_mul, hj, Fin.partialProd_succ, Function.comp_apply]

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- **Mathlib's bar-to-standard comparison is natural in the group.** Relabelling inhomogeneous bar
chains before passing to homogeneous coordinates agrees with passing to homogeneous coordinates and
then relabelling standard tuples. -/
@[reassoc]
theorem barComplex_isoStandardComplex_hom_naturality (φ : G →* H) :
    TauCeti.Rep.barComplex.resChainMap (k := k) φ ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (Rep.barComplex.isoStandardComplex k H).hom =
      (Rep.barComplex.isoStandardComplex k G).hom ≫ φ.standardComplexMap := by
  apply HomologicalComplex.hom_ext
  intro n
  refine Rep.free_ext _ _ _ _ _ fun x ↦ ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    TauCeti.Rep.barComplex.isoStandardComplex_hom_f, TauCeti.Rep.barComplex.resChainMap_f,
    standardComplexMap_f]
  -- `(standardComplex k G).X n` and `Rep.ofMulAction k G (Fin (n + 1) → G)` have the same
  -- underlying module; compare the underlying linear maps once so representation-level lemmas
  -- apply without carrier-transport mismatches.
  change ((Rep.diagonalSuccIsoFree k H n).inv).hom.toLinearMap
      (((TauCeti.Rep.barComplex.resHom (k := k) φ n).hom.toLinearMap)
        (single x (MonoidAlgebra.single 1 1))) =
    (φ.standardComplexHom n).hom.toLinearMap
      (((Rep.diagonalSuccIsoFree k G n).inv).hom.toLinearMap
        (single x (MonoidAlgebra.single 1 1)))
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  rw [TauCeti.Rep.barComplex.resHom_single, map_one,
    TauCeti.Rep.diagonalSuccIsoFree_inv_hom_single, TauCeti.Rep.diagonalSuccIsoFree_inv_hom_single,
    one_smul, one_smul, MulActionHom.toRepRes_hom_single]
  exact congrArg (fun y ↦ MonoidAlgebra.single y (1 : k)) (φ.comp_partialProd x).symm

/-- **The inverse standard-to-bar comparison is natural in the group.** Relabelling standard tuples
before passing to inhomogeneous bar coordinates agrees with passing to inhomogeneous bar
coordinates and then relabelling bar chains. -/
@[reassoc]
theorem barComplex_isoStandardComplex_inv_naturality (φ : G →* H) :
    φ.standardComplexMap (k := k) ≫
        ((Rep.resFunctor φ).mapHomologicalComplex _).map
          (Rep.barComplex.isoStandardComplex k H).inv =
      (Rep.barComplex.isoStandardComplex k G).inv ≫
        TauCeti.Rep.barComplex.resChainMap φ := by
  apply (cancel_epi (Rep.barComplex.isoStandardComplex k G).hom).mp
  apply (cancel_mono
    (((Rep.resFunctor φ).mapHomologicalComplex _).map
      (Rep.barComplex.isoStandardComplex k H).hom)).mp
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id, Iso.hom_inv_id_assoc]
  exact (φ.barComplex_isoStandardComplex_hom_naturality).symm

end MonoidHom
