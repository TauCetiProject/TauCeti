/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# The category of finite isocrystals

Let `L` be a field with a field automorphism `σ : L ≃ₐ[E] L` fixing a coefficient ring `E`.
A *finite isocrystal* over `(L, σ)` is a finite-dimensional `L`-vector space `V` together with a
bijective `σ`-semilinear map `Φ : V → V`, its Frobenius. A morphism of finite isocrystals is an
`L`-linear map `f` with `f ∘ Φ = Φ' ∘ f`.

The motivating case is a nonarchimedean local field `E` with residue field `𝔽_q`, `L` the
completion of its maximal unramified extension and `σ` the arithmetic `q`-Frobenius; in equal
characteristic, `L = k((π))` with `σ` acting on coefficients. Finite isocrystals are the input of
the Dieudonné–Manin classification and, through the functor to vector bundles, of the
classification of vector bundles on the Fargues–Fontaine curve.

Since `σ` fixes `E`, multiplying an intertwining map by a scalar from `E` gives an intertwining
map again, while multiplying by an arbitrary scalar from `L` does not. So the morphism spaces are
`E`-modules and the category is `E`-linear; arbitrary `L`-scalars are not part of the structure.

## Main definitions

* `TauCeti.FiniteIsocrystal σ`: the category of finite isocrystals over `(L, σ)`.
* `TauCeti.FiniteIsocrystal.isoMk`: an isomorphism from an intertwining linear equivalence.
* `TauCeti.FiniteIsocrystal.pi`: the isocrystal on a finite product, with coordinatewise
  Frobenius, and `TauCeti.FiniteIsocrystal.isBilimitBicone`, which shows that it is a biproduct.
* `TauCeti.FiniteIsocrystal.biproductIsoPi`: the chosen biproduct of a finite family is isomorphic
  to `TauCeti.FiniteIsocrystal.pi`.
* `TauCeti.FiniteIsocrystal.endRingHom`: the embedding of the endomorphism `E`-algebra into the
  `L`-linear endomorphisms; its range consists of the Frobenius-intertwining endomorphisms.

## Main results

* `TauCeti.FiniteIsocrystal.isIso_iff_bijective`: a morphism is an isomorphism iff its
  underlying linear map is bijective.
* `TauCeti.FiniteIsocrystal.isZero_iff_subsingleton`: the zero objects are the isocrystals on the
  zero space.
* The category is `E`-linear and has finite biproducts, and the forgetful functor to
  `ModuleCat L` is faithful, additive and reflects isomorphisms.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3, Definition 8.2.5.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), Definition 4.1.1.
-/

public section

open CategoryTheory Limits

universe w u

namespace TauCeti

variable {E L : Type*} [CommRing E] [Field L] [Algebra E L]

/-- A finite isocrystal over a field `L` with an automorphism `σ` fixing `E`: a finite-dimensional
`L`-vector space with a bijective `σ`-semilinear Frobenius. -/
structure FiniteIsocrystal (σ : L ≃ₐ[E] L) where
  /-- The underlying `L`-vector space. -/
  toModuleCat : ModuleCat.{u} L
  /-- The underlying vector space is finite-dimensional. -/
  [finite : Module.Finite L toModuleCat]
  /-- The Frobenius, a `σ`-semilinear map. -/
  frobenius : toModuleCat →ₛₗ[(σ : L →+* L)] toModuleCat
  /-- The Frobenius is bijective. -/
  frobenius_bijective : Function.Bijective frobenius

namespace FiniteIsocrystal

variable {σ : L ≃ₐ[E] L}

instance : CoeSort (FiniteIsocrystal.{u} σ) (Type u) := ⟨fun D => D.toModuleCat⟩

attribute [instance] finite

/-- Bundle a finite-dimensional vector space with a bijective `σ`-semilinear Frobenius. -/
abbrev of (σ : L ≃ₐ[E] L) (V : Type u) [AddCommGroup V] [Module L V] [Module.Finite L V]
    (Φ : V →ₛₗ[(σ : L →+* L)] V) (hΦ : Function.Bijective Φ) : FiniteIsocrystal σ where
  toModuleCat := ModuleCat.of L V
  finite := ‹Module.Finite L V›
  frobenius := Φ
  frobenius_bijective := hΦ

theorem frobenius_injective (D : FiniteIsocrystal.{u} σ) : Function.Injective D.frobenius :=
  D.frobenius_bijective.injective

theorem frobenius_surjective (D : FiniteIsocrystal.{u} σ) : Function.Surjective D.frobenius :=
  D.frobenius_bijective.surjective

/-- The Frobenius commutes with scalars from `E`, since `σ` fixes them. -/
theorem frobenius_algebraMap_smul (D : FiniteIsocrystal.{u} σ) (c : E) (x : D) :
    D.frobenius (algebraMap E L c • x) = algebraMap E L c • D.frobenius x := by
  simp

/-- On a nonzero space the Frobenius is nonzero: the zero semilinear map on a nonzero space is
not the Frobenius of an isocrystal. -/
theorem frobenius_ne_zero (D : FiniteIsocrystal.{u} σ) [Nontrivial D] : D.frobenius ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : D)
  exact hx (D.frobenius_injective (by simp [h]))

/-! ### Morphisms -/

/-- A morphism of finite isocrystals: a linear map intertwining the Frobenii. -/
@[ext]
structure Hom (D D' : FiniteIsocrystal.{u} σ) where
  /-- The underlying linear map. -/
  hom : D →ₗ[L] D'
  /-- The linear map intertwines the Frobenii. -/
  hom_frobenius : ∀ x, hom (D.frobenius x) = D'.frobenius (hom x)

attribute [simp] Hom.hom_frobenius

instance {D D' : FiniteIsocrystal.{u} σ} : FunLike (Hom D D') D D' where
  coe f := f.hom
  coe_injective _ _ h := Hom.ext (DFunLike.coe_injective h)

instance : Category (FiniteIsocrystal.{u} σ) where
  Hom := Hom
  id D := ⟨LinearMap.id, fun _ => rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun x => by simp⟩

instance : ConcreteCategory (FiniteIsocrystal.{u} σ) Hom where
  hom f := f
  ofHom f := f

variable {D D' D'' : FiniteIsocrystal.{u} σ}

@[simp]
theorem Hom.coe_hom_apply (f : D ⟶ D') (x : D) : f x = f.hom x := (rfl)

/-- Bundle a linear map intertwining the Frobenii as a morphism of finite isocrystals. -/
abbrev ofHom (f : D →ₗ[L] D') (hf : ∀ x, f (D.frobenius x) = D'.frobenius (f x)) : D ⟶ D' :=
  ⟨f, hf⟩

@[simp]
theorem hom_ofHom (f : D →ₗ[L] D') (hf : ∀ x, f (D.frobenius x) = D'.frobenius (f x)) :
    (ofHom f hf).hom = f := (rfl)

@[simp]
theorem ofHom_hom (f : D ⟶ D') : ofHom f.hom f.hom_frobenius = f := (rfl)

/-- Morphisms of finite isocrystals are determined by their underlying linear maps. -/
@[ext]
theorem hom_ext {f g : D ⟶ D'} (h : f.hom = g.hom) : f = g := Hom.ext h

theorem hom_injective : Function.Injective (Hom.hom : (D ⟶ D') → (D →ₗ[L] D')) :=
  fun _ _ => hom_ext

@[simp]
theorem hom_id (D : FiniteIsocrystal.{u} σ) : (𝟙 D : D ⟶ D).hom = LinearMap.id := (rfl)

@[simp]
theorem hom_comp (f : D ⟶ D') (g : D' ⟶ D'') : (f ≫ g).hom = g.hom.comp f.hom := (rfl)

/-- The forgetful functor to `L`-vector spaces. -/
instance : HasForget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L) where
  forget₂ :=
    { obj D := D.toModuleCat
      map f := ModuleCat.ofHom f.hom }

@[simp]
theorem forget₂_obj (D : FiniteIsocrystal.{u} σ) :
    (forget₂ (FiniteIsocrystal σ) (ModuleCat L)).obj D = D.toModuleCat := (rfl)

@[simp]
theorem forget₂_map (f : D ⟶ D') :
    ((forget₂ (FiniteIsocrystal σ) (ModuleCat L)).map f).hom = f.hom := (rfl)

instance : (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)).Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

/-! ### Isomorphisms -/

/-- A linear equivalence intertwining the Frobenii is an isomorphism of finite isocrystals. -/
def isoMk (e : D ≃ₗ[L] D') (he : ∀ x, e (D.frobenius x) = D'.frobenius (e x)) : D ≅ D' where
  hom := ofHom e.toLinearMap he
  inv := ofHom e.symm.toLinearMap fun y => e.injective (by simp [he])
  hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply)

@[simp]
theorem isoMk_hom_hom (e : D ≃ₗ[L] D') (he : ∀ x, e (D.frobenius x) = D'.frobenius (e x)) :
    (isoMk e he).hom.hom = e.toLinearMap := (rfl)

@[simp]
theorem isoMk_inv_hom (e : D ≃ₗ[L] D') (he : ∀ x, e (D.frobenius x) = D'.frobenius (e x)) :
    (isoMk e he).inv.hom = e.symm.toLinearMap := (rfl)

/-- A morphism of finite isocrystals is an isomorphism iff its underlying linear map is
bijective: the inverse linear map automatically intertwines the Frobenii. -/
theorem isIso_iff_bijective (f : D ⟶ D') : IsIso f ↔ Function.Bijective f.hom := by
  refine ⟨fun _ => ConcreteCategory.bijective_of_isIso f, fun hf => ?_⟩
  exact (isoMk (LinearEquiv.ofBijective f.hom hf) f.hom_frobenius).isIso_hom

instance : (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)).ReflectsIsomorphisms where
  reflects f _ := by
    rw [isIso_iff_bijective]
    exact (ConcreteCategory.isIso_iff_bijective
      ((forget₂ (FiniteIsocrystal σ) (ModuleCat L)).map f)).mp inferInstance

/-! ### The `E`-linear structure -/

instance : Zero (D ⟶ D') := ⟨ofHom 0 fun _ => by simp⟩

instance : Add (D ⟶ D') := ⟨fun f g => ofHom (f.hom + g.hom) fun _ => by simp⟩

instance : Neg (D ⟶ D') := ⟨fun f => ofHom (-f.hom) fun _ => by simp⟩

instance : Sub (D ⟶ D') := ⟨fun f g => ofHom (f.hom - g.hom) fun _ => by simp⟩

instance : SMul ℕ (D ⟶ D') := ⟨fun n f => ofHom (n • f.hom) fun _ => by simp⟩

instance : SMul ℤ (D ⟶ D') := ⟨fun n f => ofHom (n • f.hom) fun _ => by simp⟩

/-- Scalars from `E` act on morphisms through `algebraMap E L`. -/
instance : SMul E (D ⟶ D') :=
  ⟨fun c f => ofHom (algebraMap E L c • f.hom) fun _ => by simp⟩

@[simp] theorem hom_zero : (0 : D ⟶ D').hom = 0 := (rfl)

@[simp] theorem hom_add (f g : D ⟶ D') : (f + g).hom = f.hom + g.hom := (rfl)

@[simp] theorem hom_neg (f : D ⟶ D') : (-f).hom = -f.hom := (rfl)

@[simp] theorem hom_sub (f g : D ⟶ D') : (f - g).hom = f.hom - g.hom := (rfl)

@[simp] theorem hom_nsmul (n : ℕ) (f : D ⟶ D') : (n • f).hom = n • f.hom := (rfl)

@[simp] theorem hom_zsmul (n : ℤ) (f : D ⟶ D') : (n • f).hom = n • f.hom := (rfl)

@[simp]
theorem hom_smul (c : E) (f : D ⟶ D') : (c • f).hom = algebraMap E L c • f.hom := (rfl)

instance : AddCommGroup (D ⟶ D') :=
  Function.Injective.addCommGroup Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Preadditive (FiniteIsocrystal.{u} σ) where
  add_comp _ _ _ _ _ _ := hom_ext (LinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _ := hom_ext (LinearMap.add_comp _ _ _)

instance : (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)).Additive where

@[simp]
theorem hom_sum {ι : Type*} (s : Finset ι) (f : ι → (D ⟶ D')) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  have := congrArg ModuleCat.Hom.hom
    (map_sum (forget₂ (FiniteIsocrystal σ) (ModuleCat L)).mapAddHom f s)
  simpa only [Functor.mapAddHom_apply, forget₂_map, ModuleCat.hom_sum] using this

instance : Module E (D ⟶ D') where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]
  zero_smul _ := by ext; simp

instance : Linear E (FiniteIsocrystal.{u} σ) where
  smul_comp _ _ _ _ _ _ := by ext; simp
  comp_smul _ _ _ _ _ _ := by ext; simp

/-! ### Zero objects -/

/-- A finite isocrystal is a zero object iff its underlying space is zero. -/
theorem isZero_iff_subsingleton (D : FiniteIsocrystal.{u} σ) : IsZero D ↔ Subsingleton D := by
  rw [IsZero.iff_id_eq_zero]
  refine ⟨fun h => ⟨fun x y => ?_⟩, fun _ => hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)⟩
  have h' : ∀ z : D, z = 0 := fun z => by simpa using congrArg (fun f : D ⟶ D => f.hom z) h
  rw [h' x, h' y]

/-! ### Finite biproducts -/

section Pi

variable {ι : Type w} (D : ι → FiniteIsocrystal.{max w u} σ)

/-- The coordinatewise Frobenius on a product of finite isocrystals. -/
def piFrobenius : (∀ i, D i) →ₛₗ[(σ : L →+* L)] (∀ i, D i) where
  toFun x i := (D i).frobenius (x i)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smulₛₗ _ _ _

@[simp]
theorem piFrobenius_apply (x : ∀ i, D i) (i : ι) : piFrobenius D x i = (D i).frobenius (x i) :=
  (rfl)

theorem piFrobenius_bijective : Function.Bijective (piFrobenius D) :=
  Function.Bijective.piMap fun i => (D i).frobenius_bijective

variable [Finite ι]

/-- The direct sum of a finite family of finite isocrystals: the product of the underlying spaces
with the coordinatewise Frobenius. -/
abbrev pi : FiniteIsocrystal.{max w u} σ :=
  of σ (∀ i, D i) (piFrobenius D) (piFrobenius_bijective D)

/-- The projection from the direct sum onto a summand. -/
def piπ (i : ι) : pi D ⟶ D i := ofHom (LinearMap.proj i) fun _ => rfl

/-- The inclusion of a summand into the direct sum. -/
def piι [DecidableEq ι] (i : ι) : D i ⟶ pi D :=
  ofHom (LinearMap.single L (fun j => D j) i) fun x => by
    ext j
    obtain rfl | hj := eq_or_ne j i <;> simp [*]

@[simp]
theorem piπ_hom (i : ι) : (piπ D i).hom = LinearMap.proj (φ := fun j => D j) i := (rfl)

@[simp]
theorem piι_hom [DecidableEq ι] (i : ι) : (piι D i).hom = LinearMap.single L (fun j => D j) i :=
  (rfl)

/-- The bicone exhibiting `pi D` as the direct sum of the family `D`. -/
@[expose]
def bicone [DecidableEq ι] : Bicone D where
  pt := pi D
  π := piπ D
  ι := piι D
  ι_π i j := by
    obtain rfl | hij := eq_or_ne i j
    · ext x
      simp
    · ext x
      simp [hij]

@[simp] theorem bicone_pt [DecidableEq ι] : (bicone D).pt = pi D := (rfl)

@[simp] theorem bicone_π [DecidableEq ι] (i : ι) : (bicone D).π i = piπ D i := (rfl)

@[simp] theorem bicone_ι [DecidableEq ι] (i : ι) : (bicone D).ι i = piι D i := (rfl)

/-- The projections and inclusions of `pi D` sum to the identity. -/
theorem sum_piπ_comp_piι [Fintype ι] [DecidableEq ι] : ∑ i, piπ D i ≫ piι D i = 𝟙 (pi D) :=
  hom_ext <| LinearMap.ext fun x => by simpa using Finset.univ_sum_single x

/-- The direct sum `pi D` is a biproduct of the finite family `D`. -/
def isBilimitBicone [Fintype ι] [DecidableEq ι] : (bicone D).IsBilimit :=
  isBilimitOfTotal _ (sum_piπ_comp_piι D)

end Pi

instance : HasFiniteBiproducts (FiniteIsocrystal.{u} σ) :=
  ⟨fun _ => ⟨fun D => .mk ⟨bicone.{0} D, isBilimitBicone.{0} D⟩⟩⟩

section BiproductIsoPi

variable {J : Type} [Fintype J] [DecidableEq J] (D : J → FiniteIsocrystal.{u} σ)

/-- The chosen biproduct of a finite family of finite isocrystals is isomorphic to `pi D`. -/
noncomputable def biproductIsoPi : ⨁ D ≅ pi D :=
  (biproduct.uniqueUpToIso D (isBilimitBicone.{0} D)).symm

@[reassoc (attr := simp)]
theorem ι_comp_biproductIsoPi_hom (j : J) :
    biproduct.ι D j ≫ (biproductIsoPi D).hom = piι D j := by
  rw [biproductIsoPi, Iso.symm_hom, biproduct.uniqueUpToIso_inv]
  -- `biproduct.desc (bicone D).ι` has target `(bicone D).pt`, which is `pi D` only up to the
  -- definitional equality `bicone_pt`, so `rw [biproduct.ι_desc]` and `simp` cannot apply here;
  -- `exact` closes the goal using that definitional equality.
  exact (biproduct.ι_desc _ j).trans (bicone_ι D j)

@[reassoc (attr := simp)]
theorem biproductIsoPi_inv_comp_π (j : J) :
    (biproductIsoPi D).inv ≫ biproduct.π D j = piπ D j := by
  rw [biproductIsoPi, Iso.symm_inv, biproduct.uniqueUpToIso_hom]
  -- As in `ι_comp_biproductIsoPi_hom`, `exact` uses the definitional equality `bicone_pt`,
  -- here for the source of `biproduct.lift (bicone D).π`.
  exact (biproduct.lift_π _ j).trans (bicone_π D j)

@[reassoc (attr := simp)]
theorem piι_comp_biproductIsoPi_inv (j : J) :
    piι D j ≫ (biproductIsoPi D).inv = biproduct.ι D j := by
  rw [← ι_comp_biproductIsoPi_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem biproductIsoPi_hom_comp_piπ (j : J) :
    (biproductIsoPi D).hom ≫ piπ D j = biproduct.π D j := by
  rw [← biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]

end BiproductIsoPi

/-! ### Endomorphisms -/

/-- The embedding of the endomorphism ring of a finite isocrystal into the `L`-linear
endomorphisms of its underlying vector space. Its image is the subring of endomorphisms commuting
with the Frobenius (`mem_range_endRingHom`). -/
def endRingHom (D : FiniteIsocrystal.{u} σ) : End D →+* Module.End L D :=
  (ModuleCat.endRingEquiv ((forget₂ (FiniteIsocrystal σ) (ModuleCat L)).obj D)).toRingHom.comp
    ((forget₂ (FiniteIsocrystal σ) (ModuleCat L)).mapEndRingHom D)

@[simp]
theorem endRingHom_apply (D : FiniteIsocrystal.{u} σ) (f : End D) :
    D.endRingHom f = f.asHom.hom := by
  simp [endRingHom]

theorem endRingHom_injective (D : FiniteIsocrystal.{u} σ) : Function.Injective D.endRingHom :=
  fun _ _ h => End.ext (hom_ext (by simpa using h))

/-- The endomorphisms of a finite isocrystal are exactly the linear endomorphisms commuting with
the Frobenius. -/
theorem mem_range_endRingHom (D : FiniteIsocrystal.{u} σ) (f : Module.End L D) :
    f ∈ D.endRingHom.range ↔ ∀ x, f (D.frobenius x) = D.frobenius (f x) :=
  ⟨by rintro ⟨g, rfl⟩; simp, fun hf => ⟨.of (ofHom f hf), by simp⟩⟩

/-- The `E`-algebra structure on the endomorphism ring is multiplication by the scalars of `E`,
viewed in `L`. -/
theorem endRingHom_algebraMap (D : FiniteIsocrystal.{u} σ) (c : E) :
    D.endRingHom (algebraMap E (End D) c) = algebraMap L (Module.End L D) (algebraMap E L c) := by
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

end FiniteIsocrystal

end TauCeti
