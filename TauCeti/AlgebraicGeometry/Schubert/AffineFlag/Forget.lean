/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Schubert.AffineFlag.BaseChange
public import TauCeti.AlgebraicGeometry.Grassmannian.Proper

import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.CategoryTheory.Limits.MorphismProperty

/-!
# Forgetful morphisms and properness of affine-base flag schemes

Let `M` be a module over a commutative ring `R` and `q : Fin n → ℕ` a list of quotient ranks.
For a monotone map `e : Fin m → Fin n`, a flag `N 0 ≤ ⋯ ≤ N (n - 1)` of submodules of
`A ⊗[R] M` with quotients of ranks `q` gives the flag `N (e 0) ≤ ⋯ ≤ N (e (m - 1))` with
quotients of ranks `q ∘ e`. This file constructs the corresponding morphism of flag schemes
`TauCeti.AlgebraicGeometry.flagSchemeForget`, which forgets the steps not in the image of `e`
(and repeats a step when `e` is not injective). On the ambient products of Grassmannians it is
the reindexing of the factors (`TauCeti.AlgebraicGeometry.flagGrassmannianProductMap`), and the
incidence equations of the flags of ranks `q ∘ e` pull back into those of the flags of ranks `q`
(`TauCeti.AlgebraicGeometry.comap_flagIncidence_le`). The forgetful morphisms are compatible with
composition and with extension of the base ring.

When `M` is a finite `R`-module, the flag scheme is a closed subscheme of a finite product of
proper Grassmannians over `Spec R`, so it is proper over `Spec R`
(`TauCeti.AlgebraicGeometry.isProper_flagScheme_hom`), and then every forgetful morphism is
proper.

## Main definitions

* `TauCeti.AlgebraicGeometry.flagGrassmannianProductMap`: the reindexing morphism of the ambient
  products of Grassmannians along a map `e : Fin m → Fin n`.
* `TauCeti.AlgebraicGeometry.flagSchemeForget`: the morphism of flag schemes along a monotone
  `e`, retaining the steps indexed by `e`.

## Main results

* `TauCeti.AlgebraicGeometry.comap_flagIncidence_le`: forgetting steps preserves the incidence
  equations.
* `TauCeti.AlgebraicGeometry.flagSchemeHomEquiv_comp_flagSchemeForget`: on points the forgetful
  morphism restricts a flag to the steps indexed by `e`.
* `TauCeti.AlgebraicGeometry.flagSchemeForget_comp`,
  `TauCeti.AlgebraicGeometry.flagBaseChangeHom_flagSchemeForget`: compatibility with composition
  and with base change.
* `TauCeti.AlgebraicGeometry.isProper_flagScheme_hom`: the flag scheme of a finite module is
  proper over the base.

## References

* M. Brion, *Lectures on the geometry of flag varieties*, §1.2.
-/

public section

universe u

open CategoryTheory Limits _root_.AlgebraicGeometry Module.Grassmannian TensorProduct
open scoped Module.Grassmannian

namespace TauCeti.AlgebraicGeometry

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
  {m n : ℕ} (q : Fin n → ℕ)

/-! ### Reindexing the ambient products -/

/-- The morphism of ambient products of Grassmannians along `e : Fin m → Fin n`, whose `i`th
component is the projection onto the factor `e i`. -/
noncomputable def flagGrassmannianProductMap (e : Fin m → Fin n) :
    flagGrassmannianProduct R M q ⟶ flagGrassmannianProduct R M (q ∘ e) :=
  flagGrassmannianProductLift R M (q ∘ e) (fun i ↦ flagGrassmannianProductπ R M q (e i))
    (fun i ↦ flagGrassmannianProductπ_toSpec R M q (e i))

/-- The `i`th projection after reindexing along `e` is the projection onto the factor `e i`. -/
@[reassoc (attr := simp)]
theorem flagGrassmannianProductMap_π (e : Fin m → Fin n) (i : Fin m) :
    (flagGrassmannianProductMap R M q e).left ≫ flagGrassmannianProductπ R M (q ∘ e) i =
      flagGrassmannianProductπ R M q (e i) :=
  flagGrassmannianProductLift_π R M (q ∘ e) _ _ i

/-- Reindexing along the identity is the identity. -/
@[simp]
theorem flagGrassmannianProductMap_id : flagGrassmannianProductMap R M q id = 𝟙 _ :=
  flagGrassmannianProduct_hom_ext R M q fun i ↦
    (flagGrassmannianProductMap_π R M q id i).trans (Category.id_comp _).symm

/-- Reindexing is compatible with composition. -/
@[reassoc (attr := simp)]
theorem flagGrassmannianProductMap_comp {l : ℕ} (e : Fin m → Fin n) (e' : Fin l → Fin m) :
    flagGrassmannianProductMap R M q e ≫ flagGrassmannianProductMap R M (q ∘ e) e' =
      flagGrassmannianProductMap R M q (e ∘ e') :=
  -- The ranks `(q ∘ e) ∘ e'` and `q ∘ (e ∘ e')` agree only by unfolding `Function.comp`, which
  -- `simp` does not do, so the projection lemma for `e ∘ e'` is applied directly.
  flagGrassmannianProduct_hom_ext R M _ fun i ↦
    (by simp : _ = flagGrassmannianProductπ R M q (e (e' i))).trans
      (flagGrassmannianProductMap_π R M q (e ∘ e') i).symm

variable {R M q}
variable {A : Type u} [CommRing A] [Algebra R A]

/-- On affine points, reindexing the ambient product reindexes the family of Grassmannian
points. -/
@[simp]
theorem flagGrassmannianProductHomEquiv_comp_flagGrassmannianProductMap (e : Fin m → Fin n)
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagGrassmannianProduct R M q)
    (i : Fin m) :
    flagGrassmannianProductHomEquiv (g ≫ flagGrassmannianProductMap R M q e) i =
      flagGrassmannianProductHomEquiv g (e i) := by
  apply toSchemeHom_injective
  simp

/-- **Forgetting steps preserves the incidence equations.** Along a monotone `e`, the incidence
ideal of flags of ranks `q ∘ e` pulls back into the incidence ideal of flags of ranks `q`: the
condition `N (e i) ≤ N (e j)` for `i < j` is either one of the conditions defining flags of
ranks `q`, or trivial when `e i = e j`. -/
theorem comap_flagIncidence_le {e : Fin m → Fin n} (he : Monotone e) :
    (flagIncidence R M (q ∘ e)).comap (flagGrassmannianProductMap R M q e).left ≤
      flagIncidence R M q := by
  have key (S : Type u) [CommRing S] [Algebra R S]
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶
        flagGrassmannianProduct R M q) :
      (flagIncidence R M (q ∘ e)).comap (g ≫ flagGrassmannianProductMap R M q e).left ≤
        (flagIncidence R M q).comap g.left := by
    rw [comap_flagIncidence, comap_flagIncidence]
    refine fun U ↦ Ideal.map_mono (Ideal.map_mono ?_)
    simp only [flagGrassmannianProductHomEquiv_comp_flagGrassmannianProductMap]
    refine iSup₂_le fun i j ↦ iSup_le fun hij ↦ ?_
    rcases (he hij.le).lt_or_eq with h | h
    · exact le_iSup₂_of_le (e i) (e j) (le_iSup_of_le h le_rfl)
    · have hle (a b : Fin n) (hab : a = b) : (flagGrassmannianProductHomEquiv g a).toSubmodule ≤
          (flagGrassmannianProductHomEquiv g b).toSubmodule := by
        subst hab
        exact le_rfl
      exact ((incidenceLocus_eq_bot_iff _ _).2 (hle _ _ h)).le.trans bot_le
  refine Scheme.IdealSheafData.le_of_comap_Spec_isLocalRing fun S _ _ φ ↦ ?_
  let _ : Algebra R S := (Spec.preimage (φ ≫ (flagGrassmannianProduct R M q).hom)).hom.toAlgebra
  rw [← Scheme.IdealSheafData.comap_comp]
  exact key S (Over.homMk φ (Spec.map_preimage _).symm)

/-! ### Forgetful morphisms of flag schemes -/

variable (R M q)

/-- The morphism of flag schemes along a monotone `e : Fin m → Fin n`, sending a flag `N` of
quotient ranks `q` to the flag `N ∘ e` of quotient ranks `q ∘ e`. -/
noncomputable def flagSchemeForget {e : Fin m → Fin n} (he : Monotone e) :
    flagScheme R M q ⟶ flagScheme R M (q ∘ e) :=
  Over.homMk (IsClosedImmersion.lift (flagSchemeι R M (q ∘ e)).left
    ((flagSchemeι R M q).left ≫ (flagGrassmannianProductMap R M q e).left) (by
      rw [ker_flagSchemeι, Scheme.Hom.ker_comp, ker_flagSchemeι,
        Scheme.IdealSheafData.le_map_iff_comap_le]
      exact comap_flagIncidence_le he)) (by
    rw [← Over.w (flagSchemeι R M (q ∘ e)), IsClosedImmersion.lift_fac_assoc, Category.assoc,
      Over.w, Over.w])

/-- The forgetful morphism is the reindexing of the ambient products. -/
@[reassoc (attr := simp)]
theorem flagSchemeForget_flagSchemeι {e : Fin m → Fin n} (he : Monotone e) :
    flagSchemeForget R M q he ≫ flagSchemeι R M (q ∘ e) =
      flagSchemeι R M q ≫ flagGrassmannianProductMap R M q e := by
  ext1
  exact IsClosedImmersion.lift_fac _ _ _

/-- The `i`th step of the forgotten flag is the step `e i` of the original flag. -/
@[reassoc (attr := simp)]
theorem flagSchemeForget_π {e : Fin m → Fin n} (he : Monotone e) (i : Fin m) :
    (flagSchemeForget R M q he).left ≫ flagSchemeπ R M (q ∘ e) i = flagSchemeπ R M q (e i) := by
  simp [← flagSchemeι_comp_flagGrassmannianProductπ, ← Over.comp_left_assoc]

/-- Forgetting along the identity is the identity. -/
@[simp]
theorem flagSchemeForget_id : flagSchemeForget R M q monotone_id = 𝟙 _ := by
  ext1
  exact flagScheme_hom_ext (by simp) fun i ↦
    (flagSchemeForget_π R M q monotone_id i).trans (Category.id_comp _).symm

/-- Forgetful morphisms are compatible with composition. -/
@[reassoc (attr := simp)]
theorem flagSchemeForget_comp {l : ℕ} {e : Fin m → Fin n} (he : Monotone e) {e' : Fin l → Fin m}
    (he' : Monotone e') :
    flagSchemeForget R M q he ≫ flagSchemeForget R M (q ∘ e) he' =
      flagSchemeForget R M q (he.comp he') := by
  ext1
  -- The ranks `(q ∘ e) ∘ e'` and `q ∘ (e ∘ e')` agree only by unfolding `Function.comp`, which
  -- `simp` does not do, so the projection lemma for `e ∘ e'` is applied directly.
  exact flagScheme_hom_ext (by simp) fun i ↦ (by simp : _ = flagSchemeπ R M q (e (e' i))).trans
    (flagSchemeForget_π R M q (he.comp he') i).symm

variable {R M q}

/-- **The forgetful morphism on points.** On affine points, the forgetful morphism along `e`
restricts a flag `N` to the flag `N ∘ e`. -/
@[simp]
theorem flagSchemeHomEquiv_comp_flagSchemeForget {e : Fin m → Fin n} (he : Monotone e)
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagScheme R M q)
    (i : Fin m) :
    (flagSchemeHomEquiv (g ≫ flagSchemeForget R M q he)).val i =
      (flagSchemeHomEquiv g).val (e i) := by
  apply toSchemeHom_injective
  simp

/-- Forgetful morphisms commute with extension of the base ring. -/
@[reassoc]
theorem flagBaseChangeHom_flagSchemeForget (R' : Type u) [CommRing R'] [Algebra R R']
    {e : Fin m → Fin n} (he : Monotone e) :
    flagBaseChangeHom R R' M q ≫ (flagSchemeForget R M q he).left =
      (flagSchemeForget R' (R' ⊗[R] M) q he).left ≫ flagBaseChangeHom R R' M (q ∘ e) :=
  flagScheme_hom_ext (by simp) fun i ↦ by simp

/-! ### Properness -/

variable (R M q)

/-- The product of the Grassmannians of a finite module is proper over the base. -/
instance isProper_flagGrassmannianProduct_hom [Module.Finite R M] :
    IsProper (flagGrassmannianProduct R M q).hom := by
  rw [flagGrassmannianProduct_def]
  -- Instance search cannot unify the class `@IsProper` with a `MorphismProperty Scheme`
  -- metavariable, so the closure instance is supplied by name.
  have := Over.isClosedUnderFiniteProducts @IsProper (X := Spec (.of R))
  exact (MorphismProperty.overObj @IsProper).prop_product fun i ↦
    inferInstanceAs (IsProper (toSpec R M (q i)))

/-- **The flag scheme of a finite module is proper** over the base: it is a closed subscheme of
a finite product of proper Grassmannians. -/
instance isProper_flagScheme_hom [Module.Finite R M] : IsProper (flagScheme R M q).hom := by
  rw [← Over.w (flagSchemeι R M q)]
  infer_instance

/-- The forgetful morphisms of flag schemes of a finite module are proper. -/
instance isProper_flagSchemeForget_left [Module.Finite R M] {e : Fin m → Fin n}
    (he : Monotone e) : IsProper (flagSchemeForget R M q he).left := by
  have : IsProper ((flagSchemeForget R M q he).left ≫ (flagScheme R M (q ∘ e)).hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ (flagScheme R M (q ∘ e)).hom

end TauCeti.AlgebraicGeometry
