/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.RingTheory.Grassmannian.Incidence

import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.PointIdeals
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Flag incidence over an affine base

For an `R`-module `M` and a list of quotient ranks `q`, take the product over
`Spec R` of the Grassmannians of quotients of `M` of ranks `q i`. On an affine
test scheme `Spec A`, its points are families of submodules `N i` of `A ⊗[R] M`
with finite projective quotients of the prescribed ranks. The flag incidence ideal
is the sum of the content ideals of `N i → (A ⊗[R] M) ⧸ N j` for `i < j`. Thus its
closed subscheme classifies nested families over arbitrary test algebras.

The ambient product has a lift and projectionwise extensionality for arbitrary
test schemes over `Spec R`, in addition to its affine-point classification.

For finite projective `M` of constant rank `d`, the submodule ranks of such
flags are `d - q i`. Using quotient ranks lets the construction work for any
ambient module and includes the empty list. See M. Brion, *Lectures on the
geometry of flag varieties*, §1.2, for the incidence model over the complex numbers.
-/

public section

universe u

open CategoryTheory Limits _root_.AlgebraicGeometry TensorProduct
open scoped Module.Grassmannian

namespace TauCeti.AlgebraicGeometry

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
  {n : ℕ} (q : Fin n → ℕ)

private noncomputable def flagFactors (i : Fin n) : Over (Spec (.of R)) :=
  Over.mk (Module.Grassmannian.toSpec R M (q i))

/-- The product of the Grassmannians of the specified quotient ranks over `Spec R`. -/
noncomputable def flagGrassmannianProduct : Over (Spec (.of R)) :=
  ∏ᶜ flagFactors R M q

/-- The projection of the ambient product onto the Grassmannian of the `i`th quotient. -/
noncomputable def flagGrassmannianProductπ (i : Fin n) :
    (flagGrassmannianProduct R M q).left ⟶ Module.Grassmannian.scheme R M (q i) :=
  (Pi.π (flagFactors R M q) i).left

@[reassoc (attr := simp)]
theorem flagGrassmannianProductπ_toSpec (i : Fin n) :
    flagGrassmannianProductπ R M q i ≫ Module.Grassmannian.toSpec R M (q i) =
      (flagGrassmannianProduct R M q).hom :=
  Over.w (Pi.π (flagFactors R M q) i)

/-- A family of morphisms to the Grassmannians over `Spec R` induces a morphism to
their product, for any test scheme over `Spec R`. -/
noncomputable def flagGrassmannianProductLift {X : Over (Spec (.of R))}
    (f : ∀ i, X.left ⟶ Module.Grassmannian.scheme R M (q i))
    (hf : ∀ i, f i ≫ Module.Grassmannian.toSpec R M (q i) = X.hom) :
    X ⟶ flagGrassmannianProduct R M q :=
  Pi.lift fun i ↦ Over.homMk (f i) (hf i)

/-- The lift to the ambient product has the prescribed Grassmannian projections. -/
@[reassoc (attr := simp)]
theorem flagGrassmannianProductLift_π {X : Over (Spec (.of R))}
    (f : ∀ i, X.left ⟶ Module.Grassmannian.scheme R M (q i))
    (hf : ∀ i, f i ≫ Module.Grassmannian.toSpec R M (q i) = X.hom) (i : Fin n) :
    (flagGrassmannianProductLift R M q f hf).left ≫ flagGrassmannianProductπ R M q i =
      f i :=
  congrArg Over.Hom.left (Pi.lift_comp_π (f := flagFactors R M q)
    (fun j ↦ Over.homMk (f j) (hf j)) i)

/-- Morphisms over `Spec R` to the ambient product are determined by their
Grassmannian projections. This also applies to the empty family. -/
theorem flagGrassmannianProduct_hom_ext {X : Over (Spec (.of R))}
    {f g : X ⟶ flagGrassmannianProduct R M q}
    (h : ∀ i, f.left ≫ flagGrassmannianProductπ R M q i =
      g.left ≫ flagGrassmannianProductπ R M q i) : f = g := by
  apply Pi.hom_ext (f := flagFactors R M q)
  intro i
  exact Over.OverMorphism.ext (h i)

variable {R M q}
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

open Module.Grassmannian

private noncomputable abbrev affineOver (A : Type u) [CommRing A] [Algebra R A] :
    Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

private noncomputable def productPointFamily
    (g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q) (i : Fin n) : G(q i, A ⊗[R] M; A) :=
  (schemeHomEquiv R M (q i) A).symm
    ⟨g.left ≫ flagGrassmannianProductπ R M q i, by simp [Over.w g, affineOver]⟩

private theorem toSchemeHom_productPointFamily
    (g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q) (i : Fin n) :
    toSchemeHom (productPointFamily g i) = g.left ≫ flagGrassmannianProductπ R M q i :=
  toSchemeHom_schemeHomEquiv_symm_apply _

private noncomputable def productPoint (N : ∀ i, G(q i, A ⊗[R] M; A)) :
    affineOver (R := R) A ⟶ flagGrassmannianProduct R M q :=
  flagGrassmannianProductLift R M q (fun i ↦ toSchemeHom (N i))
    (fun i ↦ toSchemeHom_toSpec (N i))

@[reassoc]
private theorem productPoint_left_π (N : ∀ i, G(q i, A ⊗[R] M; A)) (i : Fin n) :
    (productPoint N).left ≫ flagGrassmannianProductπ R M q i = toSchemeHom (N i) :=
  flagGrassmannianProductLift_π R M q _ _ i

private theorem productPointFamily_productPoint (N : ∀ i, G(q i, A ⊗[R] M; A)) (i : Fin n) :
    productPointFamily (productPoint N) i = N i :=
  toSchemeHom_injective ((toSchemeHom_productPointFamily _ _).trans (productPoint_left_π _ _))

private theorem productPoint_productPointFamily
    (g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q) :
    productPoint (productPointFamily g) = g := by
  apply flagGrassmannianProduct_hom_ext R M q
  intro i
  exact (productPoint_left_π _ _).trans (toSchemeHom_productPointFamily _ _)

/-- An affine point of the ambient product is a family of Grassmannian points. -/
noncomputable def flagGrassmannianProductHomEquiv :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagGrassmannianProduct R M q) ≃
      (∀ i, G(q i, A ⊗[R] M; A)) where
  toFun := productPointFamily
  invFun := productPoint
  left_inv := productPoint_productPointFamily
  right_inv N := funext (productPointFamily_productPoint N)

/-- Each step of the family corresponding to an ambient point is classified by a projection. -/
@[simp]
theorem toSchemeHom_flagGrassmannianProductHomEquiv_apply
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagGrassmannianProduct R M q)
    (i : Fin n) :
    toSchemeHom (flagGrassmannianProductHomEquiv g i) =
      g.left ≫ flagGrassmannianProductπ R M q i :=
  toSchemeHom_productPointFamily g i

/-- The ambient point of a family projects to the morphisms classifying the individual steps. -/
@[reassoc (attr := simp)]
theorem flagGrassmannianProductHomEquiv_symm_apply_π
    (N : ∀ i, G(q i, A ⊗[R] M; A)) (i : Fin n) :
    (flagGrassmannianProductHomEquiv.symm N).left ≫ flagGrassmannianProductπ R M q i =
      toSchemeHom (N i) :=
  productPoint_left_π N i

private theorem productPointFamily_map (f : A →ₐ[R] B)
    {g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q}
    {g' : affineOver (R := R) B ⟶ flagGrassmannianProduct R M q}
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g.left = g'.left) (i : Fin n) :
    productPointFamily g' i = map f (productPointFamily g i) := by
  apply toSchemeHom_injective
  rw [toSchemeHom_productPointFamily, toSchemeHom_map, toSchemeHom_productPointFamily,
    ← Category.assoc, ← AlgHom.toRingHom_eq_coe, h]

private noncomputable def flagPointIdeal
    (g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q) : Ideal A :=
  ⨆ (i : Fin n) (j : Fin n) (_ : i < j),
    (productPointFamily g i).incidenceLocus (productPointFamily g j)

private theorem flagPointIdeal_eq_bot_iff
    (g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q) :
    flagPointIdeal g = ⊥ ↔ ∀ ⦃i j⦄, i < j →
      (productPointFamily g i).toSubmodule ≤ (productPointFamily g j).toSubmodule := by
  simp [flagPointIdeal, iSup_eq_bot]

private theorem flagPointIdeal_map (f : A →ₐ[R] B)
    {g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q}
    {g' : affineOver (R := R) B ⟶ flagGrassmannianProduct R M q}
    (h : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g.left = g'.left) :
    flagPointIdeal g' = Ideal.map f (flagPointIdeal g) := by
  simp only [flagPointIdeal, productPointFamily_map f h, incidenceLocus_map, Ideal.map_iSup]

variable (R M q)

/-- The ideal sheaf of the flag incidence in the product of the Grassmannians:
over an affine point it is generated by the coefficients of the maps
from the `i`th submodule to the `j`th quotient for every `i < j`. -/
noncomputable def flagIncidence : (flagGrassmannianProduct R M q).left.IdealSheafData :=
  (flagGrassmannianProduct R M q).hom.idealSheafOfAffinePoints
    (fun g ↦ flagPointIdeal (Over.homMk g.val g.property))
    (fun f _ _ h ↦ flagPointIdeal_map f h)

/-- The scheme of flags of the specified quotient ranks in the base changes of `M`. -/
noncomputable def flagScheme : Over (Spec (.of R)) :=
  Over.mk ((flagIncidence R M q).subschemeι ≫ (flagGrassmannianProduct R M q).hom)

/-- The closed immersion of the flag scheme into the product of its Grassmannians. -/
noncomputable def flagSchemeι : flagScheme R M q ⟶ flagGrassmannianProduct R M q :=
  Over.homMk (flagIncidence R M q).subschemeι rfl

/-- The ideal of the closed immersion of the flag scheme is the incidence ideal. -/
theorem ker_flagSchemeι : (flagSchemeι R M q).left.ker = flagIncidence R M q :=
  Scheme.IdealSheafData.ker_subschemeι _

instance : IsClosedImmersion (flagSchemeι R M q).left :=
  inferInstanceAs (IsClosedImmersion (flagIncidence R M q).subschemeι)

/-- The morphism remembering the `i`th step of a flag. -/
noncomputable def flagSchemeπ (i : Fin n) :
    (flagScheme R M q).left ⟶ Module.Grassmannian.scheme R M (q i) :=
  (flagSchemeι R M q).left ≫ flagGrassmannianProductπ R M q i

/-- The flag projection is the corresponding ambient projection after the closed immersion. -/
@[reassoc (attr := simp)]
theorem flagSchemeι_comp_flagGrassmannianProductπ (i : Fin n) :
    (flagSchemeι R M q).left ≫ flagGrassmannianProductπ R M q i = flagSchemeπ R M q i :=
  (rfl)

@[reassoc (attr := simp)]
theorem flagSchemeπ_toSpec (i : Fin n) :
    flagSchemeπ R M q i ≫ Module.Grassmannian.toSpec R M (q i) = (flagScheme R M q).hom := by
  rw [flagSchemeπ, Category.assoc, flagGrassmannianProductπ_toSpec, Over.w]

variable {R M q}

/-- The pullback of the flag incidence ideal to an affine point of the ambient product is the
sum of the incidence ideals of its ordered pairs of steps. -/
theorem comap_flagIncidence
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagGrassmannianProduct R M q) :
    (flagIncidence R M q).comap g.left = Scheme.IdealSheafData.ofIdealTop
      ((⨆ (i : Fin n) (j : Fin n) (_ : i < j),
        (flagGrassmannianProductHomEquiv g i).incidenceLocus
          (flagGrassmannianProductHomEquiv g j)).map (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  exact Scheme.Hom.comap_idealSheafOfAffinePoints (flagGrassmannianProduct R M q).hom
    (fun p ↦ flagPointIdeal (Over.homMk p.val p.property))
    (fun f _ _ h ↦ flagPointIdeal_map f h) ⟨g.left, Over.w g⟩

private theorem flagIncidence_le_ker_iff
    (g : affineOver (R := R) A ⟶ flagGrassmannianProduct R M q) :
    flagIncidence R M q ≤ g.left.ker ↔ ∀ ⦃i j⦄, i < j →
      (productPointFamily g i).toSubmodule ≤ (productPointFamily g j).toSubmodule := by
  rw [flagIncidence, Scheme.Hom.idealSheafOfAffinePoints_le_ker_iff
    _ _ (fun f _ _ h ↦ flagPointIdeal_map f h) ⟨g.left, Over.w g⟩]
  simpa only [Over.homMk_eta] using flagPointIdeal_eq_bot_iff g

/-- A morphism into the flag scheme is determined by its structure map to the base
and its projections to the Grassmannians. -/
theorem flagScheme_hom_ext {T : Scheme} {f g : T ⟶ (flagScheme R M q).left}
    (hbase : f ≫ (flagScheme R M q).hom = g ≫ (flagScheme R M q).hom)
    (hπ : ∀ i, f ≫ flagSchemeπ R M q i = g ≫ flagSchemeπ R M q i) : f = g := by
  let f' : Over.mk (f ≫ (flagScheme R M q).hom) ⟶ flagScheme R M q := Over.homMk f rfl
  let g' : Over.mk (f ≫ (flagScheme R M q).hom) ⟶ flagScheme R M q := Over.homMk g hbase.symm
  apply (cancel_mono (flagSchemeι R M q).left).1
  have h : f' ≫ flagSchemeι R M q = g' ≫ flagSchemeι R M q := by
    apply flagGrassmannianProduct_hom_ext R M q
    intro i
    exact (Category.assoc _ _ _).trans ((hπ i).trans (Category.assoc _ _ _).symm)
  exact congrArg Over.Hom.left h

private theorem flagIncidence_le_ker_of_point
    (N : {N : ∀ i, G(q i, A ⊗[R] M; A) // ∀ ⦃i j⦄, i < j →
      (N i).toSubmodule ≤ (N j).toSubmodule}) :
    flagIncidence R M q ≤ (productPoint N.val).left.ker := by
  rw [flagIncidence_le_ker_iff]
  simpa only [productPointFamily_productPoint] using N.property

private theorem flagPoint_nested (g : affineOver (R := R) A ⟶ flagScheme R M q) :
    ∀ ⦃i j⦄, i < j →
      (productPointFamily (g ≫ flagSchemeι R M q) i).toSubmodule ≤
        (productPointFamily (g ≫ flagSchemeι R M q) j).toSubmodule := by
  rw [← flagIncidence_le_ker_iff, Over.comp_left, ← ker_flagSchemeι]
  exact Scheme.Hom.le_ker_comp _ _

private noncomputable def flagPointLift
    (N : {N : ∀ i, G(q i, A ⊗[R] M; A) // ∀ ⦃i j⦄, i < j →
      (N i).toSubmodule ≤ (N j).toSubmodule}) :
    affineOver (R := R) A ⟶ flagScheme R M q :=
  Over.homMk (IsClosedImmersion.lift (flagSchemeι R M q).left (productPoint N.val).left
    ((ker_flagSchemeι R M q).trans_le (flagIncidence_le_ker_of_point N))) (by
      rw [← Over.w (flagSchemeι R M q), IsClosedImmersion.lift_fac_assoc,
        Over.w (productPoint N.val)])

private theorem flagPointLift_comp
    (N : {N : ∀ i, G(q i, A ⊗[R] M; A) // ∀ ⦃i j⦄, i < j →
      (N i).toSubmodule ≤ (N j).toSubmodule}) :
    flagPointLift N ≫ flagSchemeι R M q = productPoint N.val := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac (flagSchemeι R M q).left (productPoint N.val).left _

/-- Affine points of the flag scheme are nested families of submodules of `A ⊗[R] M` with
finite projective quotients of the specified ranks. -/
noncomputable def flagSchemeHomEquiv :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagScheme R M q) ≃
      {N : ∀ i, G(q i, A ⊗[R] M; A) // ∀ ⦃i j⦄, i < j →
        (N i).toSubmodule ≤ (N j).toSubmodule} where
  toFun g := ⟨productPointFamily (g ≫ flagSchemeι R M q), flagPoint_nested g⟩
  invFun := flagPointLift
  left_inv g := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (flagSchemeι R M q).left).1
    rw [← Over.comp_left, ← Over.comp_left, flagPointLift_comp, productPoint_productPointFamily]
  right_inv N := by
    apply Subtype.ext
    funext i
    exact (congrArg (fun g ↦ productPointFamily g i) (flagPointLift_comp N)).trans
      (productPointFamily_productPoint N.val i)

/-- The `i`th Grassmannian point of a flag is classified by its `i`th projection. -/
@[simp]
theorem toSchemeHom_flagSchemeHomEquiv_apply
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagScheme R M q)
    (i : Fin n) :
    toSchemeHom ((flagSchemeHomEquiv g).val i) = g.left ≫ flagSchemeπ R M q i := by
  exact (toSchemeHom_productPointFamily (g ≫ flagSchemeι R M q) i).trans (Category.assoc _ _ _)

/-- The map to the flag scheme associated to a nested family classifies each of its steps
under the corresponding Grassmannian projection. -/
@[reassoc (attr := simp)]
theorem flagSchemeHomEquiv_symm_apply_π
    (N : {N : ∀ i, G(q i, A ⊗[R] M; A) // ∀ ⦃i j⦄, i < j →
      (N i).toSubmodule ≤ (N j).toSubmodule}) (i : Fin n) :
    (flagSchemeHomEquiv.symm N).left ≫ flagSchemeπ R M q i = toSchemeHom (N.val i) := by
  rw [← toSchemeHom_flagSchemeHomEquiv_apply, Equiv.apply_symm_apply]

/-- Precomposition by an affine algebra map base changes each submodule in the flag. -/
theorem flagSchemeHomEquiv_apply_of_comp (f : A →ₐ[R] B)
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ flagScheme R M q)
    (g' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ flagScheme R M q)
    (h : Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ g.left = g'.left) (i : Fin n) :
    (flagSchemeHomEquiv g').val i = map f ((flagSchemeHomEquiv g).val i) := by
  apply toSchemeHom_injective
  rw [toSchemeHom_flagSchemeHomEquiv_apply, toSchemeHom_map,
    toSchemeHom_flagSchemeHomEquiv_apply, ← Category.assoc, h]

private theorem flagIncidence_eq_bot_of_subsingleton [Subsingleton (Fin n)] :
    flagIncidence R M q = ⊥ := by
  refine Scheme.IdealSheafData.eq_bot_of_le_ker_Spec_isLocalRing fun S _ _ g ↦ ?_
  let φ := Spec.preimage (g ≫ (flagGrassmannianProduct R M q).hom)
  let _ : Algebra R S := φ.hom.toAlgebra
  have hg : g ≫ (flagGrassmannianProduct R M q).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := (Spec.map_preimage _).symm
  let g' : affineOver (R := R) S ⟶ flagGrassmannianProduct R M q := Over.homMk g hg
  exact (flagIncidence_le_ker_iff g').2 fun {i j} hij ↦
    (hij.ne (Subsingleton.elim i j)).elim

private theorem isIso_flagSchemeι_left [Subsingleton (Fin n)] :
    IsIso (flagSchemeι R M q).left :=
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    ((ker_flagSchemeι R M q).trans flagIncidence_eq_bot_of_subsingleton)

variable (R M)

private noncomputable def flagGrassmannianProductIsTerminal (q : Fin 0 → ℕ) :
    IsTerminal (flagGrassmannianProduct R M q) :=
  IsTerminal.ofUniqueHom (fun _ ↦ Pi.lift fun i ↦ i.elim0)
    (fun _ g ↦ Pi.hom_ext (f := flagFactors R M q) g _ fun i ↦ i.elim0)

/-- For the empty list of ranks, the flag scheme is isomorphic to the base via its
structure morphism. -/
instance isIso_flagScheme_hom_empty (q : Fin 0 → ℕ) : IsIso (flagScheme R M q).hom := by
  let e := (flagGrassmannianProductIsTerminal R M q).uniqueUpToIso (Over.mkIdTerminal)
  have he : e.hom.left = (flagGrassmannianProduct R M q).hom := by
    rw [← Category.comp_id e.hom.left]
    exact Over.w e.hom
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsIso (flagSchemeι R M q).left := isIso_flagSchemeι_left
  rw [← Over.w (flagSchemeι R M q), ← he]
  infer_instance

/-- For a single rank, the flag scheme is isomorphic to its Grassmannian via the
projection. -/
instance isIso_flagSchemeπ_singleton (q : Fin 1 → ℕ) : IsIso (flagSchemeπ R M q 0) := by
  let e := productUniqueIso (flagFactors R M q)
  have he : e.hom.left = flagGrassmannianProductπ R M q 0 :=
    congrArg Over.Hom.left (productUniqueIso_hom (flagFactors R M q))
  have he' : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hι : IsIso (flagSchemeι R M q).left := isIso_flagSchemeι_left
  have hc : IsIso ((flagSchemeι R M q).left ≫ flagGrassmannianProductπ R M q 0) :=
    he ▸ IsIso.comp_isIso' hι he'
  exact hc

end TauCeti.AlgebraicGeometry
