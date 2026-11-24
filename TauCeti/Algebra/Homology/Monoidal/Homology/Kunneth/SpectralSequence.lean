/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Monoidal.Tor
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.CartanEilenberg
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Projective
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.FirstDifferential
public import TauCeti.CategoryTheory.Monoidal.Tor

/-!
# The Künneth spectral sequence

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, indexed by `ℕ`, and let
`Q` be the Cartan–Eilenberg resolution of `L` (`ChainComplex.cartanEilenbergResolution`). The
**Künneth spectral sequence** `HomologicalComplex.kunnethSpectralSequence K L` is the spectral
sequence of the column filtration of the Künneth bicomplex
`HomologicalComplex.kunnethBicomplex K L`, whose column `p` is `K ⊗ Q.X p`. When every term of `K`
is flat, its total complex computes `K ⊗ L`
(`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). This file computes its first two
pages, without any flatness assumption.

Pages are numbered as in `HomologicalComplex₂.columnFiltrationSpectralSequence`: the first page
(`E¹`) is `page 2` and the second page (`E²`) is `page 3`, and the object at column `p` and degree
`q` sits at `(-q - 2p, p)`.

* **First page.** The rows `Q.X p` have projective terms and projective homology, so the Künneth
  map `⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(Q.X p) ⟶ H_q(K ⊗ Q.X p)` is an isomorphism
  (`HomologicalComplex.isIso_homologyKunneth_of_projective_right`). This identifies the first page
  at column `p`, degree `q` with `⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(Q.X p)`
  (`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`).
* **First differential.** By naturality of the Künneth map, the first differential is `(-1)^q`
  times the map induced by the maps `Hⱼ(Q.d (p + 1) p)`
  (`HomologicalComplex.kunnethSpectralSequence_page_two_d`).
* **Second page.** For each `j`, the complex `p ↦ Hⱼ(Q.X p)` is the projective resolution
  `ChainComplex.cartanEilenbergResolution.homologyResolution L j` of `Hⱼ(L)`, so the row of the
  first page in degree `q` is, up to the sign `(-1)^q` of its differential, the direct sum over
  `i + j = q` of the complexes `Hᵢ(K) ⊗ Hⱼ(Q.X •)` computing `Tor (Hᵢ(K)) (Hⱼ(L))`. Hence the
  second page at column `p`, degree `q` is `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`
  (`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`), with `Tor` derived in the second
  variable as in Mathlib's `CategoryTheory.Tor`. As for `HomologicalComplex.homologyTor`, this sum
  is the graded object `GradedObject.mapBifunctorMapObj (Tor _ p) (fun x ↦ x.1 + x.2)`. On
  classes of cycles of the first page, the isomorphism is described by
  `HomologicalComplex.homologyπ_kunnethSpectralSequenceSecondPageXIso_hom`, and on each summand by
  `HomologicalComplex.homologyMap_ι_kunnethTorSumComplexHomologyIso_hom`. A morphism of Künneth
  spectral sequences whose first page is induced by a chain map of the complexes
  `HomologicalComplex.kunnethTorSumComplex` is, on the second page, the map induced on their
  homology (`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality_of_firstPage`).
* **Naturality in the first variable.** Morphisms `Hᵢ(K) ⟶ Hᵢ(K')` of coefficients, for instance
  the maps `Hᵢ(f)` induced by a chain map `f : K ⟶ K'`, induce morphisms of complexes
  `HomologicalComplex.kunnethTorComplexMap` and `HomologicalComplex.kunnethTorSumComplexMap`,
  through which the identifications above are natural
  (`HomologicalComplex.kunnethColumnHomologyKunneth_naturality_left`,
  `HomologicalComplex.tensorObjIsoKunnethTorSumComplexX_hom_naturality`,
  `HomologicalComplex.kunnethTorSumComplexHomologyIso_hom_naturality`). They are used to describe
  the morphisms of Künneth spectral sequences in
  `TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Naturality`.
* **Naturality in the second variable.** Morphisms `φ j` of the projective resolutions
  `ChainComplex.cartanEilenbergResolution.homologyResolution L j` of `Hⱼ(L)` induce morphisms of
  complexes `HomologicalComplex.kunnethTorComplexMapRight` and
  `HomologicalComplex.kunnethTorSumComplexMapRight`, through which the identifications above are
  natural (`HomologicalComplex.tensorObjIsoKunnethTorSumComplexX_hom_naturality_right`). The
  Künneth maps of the columns are natural for morphisms of the rows of the Cartan–Eilenberg
  resolutions (`HomologicalComplex.kunnethColumnHomologyKunneth_naturality_right`). When each `φ j`
  lies over a map `Hⱼ(L) ⟶ Hⱼ(L')`, the identification with `Tor` turns them into the maps induced
  on `Tor` in the second variable
  (`HomologicalComplex.kunnethTorSumComplexHomologyIso_hom_naturality_right`), as computed by
  `ProjectiveResolution.isoLeftDerivedObj_inv_naturality`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 5.6.4 (the Künneth spectral sequence) and Section 5.7 (Cartan–Eilenberg resolutions).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.20 (the algebraic Künneth spectral sequence).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory ChainComplex cartanEilenbergResolution

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The Künneth map of `K` and the row `p` of the Cartan–Eilenberg resolution `Q` of `L`, with
target the homology of the column `p` of the Künneth bicomplex, which is `K ⊗ Q.X p`. -/
def kunnethColumnHomologyKunneth (p k : ℕ) :
    GradedObject.Monoidal.tensorObj (fun i ↦ K.homology i)
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) k ⟶
      ((kunnethBicomplex K L).X p).homology k :=
  homologyKunneth K ((cartanEilenbergResolution L).X p) k

/-- `kunnethColumnHomologyKunneth K L p k` is the Künneth map of `K` and `Q.X p`. -/
lemma kunnethColumnHomologyKunneth_eq (p k : ℕ) :
    kunnethColumnHomologyKunneth K L p k =
      homologyKunneth K ((cartanEilenbergResolution L).X p) k :=
  (rfl)

/-- The Künneth map `kunnethColumnHomologyKunneth` is an isomorphism, because the rows of the
Cartan–Eilenberg resolution have projective terms and projective homology. -/
instance isIso_kunnethColumnHomologyKunneth (p k : ℕ) :
    IsIso (kunnethColumnHomologyKunneth K L p k) :=
  isIso_homologyKunneth_of_projective_right _ _ k

/-- Naturality of `kunnethColumnHomologyKunneth` with respect to the horizontal differentials of
the Künneth bicomplex. -/
@[reassoc]
lemma kunnethColumnHomologyKunneth_naturality (p k : ℕ) :
    kunnethColumnHomologyKunneth K L (p + 1) k ≫
        homologyMap ((kunnethBicomplex K L).d (p + 1) p) k =
      GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
        (fun j ↦ homologyMap ((cartanEilenbergResolution L).d (p + 1) p) j) k ≫
        kunnethColumnHomologyKunneth K L p k := by
  have h := homologyKunneth_naturality (𝟙 K) ((cartanEilenbergResolution L).d (p + 1) p) k
  simp only [homologyMap_id] at h
  -- `𝟙` of a graded object is the family of identities, `K ◁ f` is `tensorHom (𝟙 K) f`, and the
  -- columns and horizontal differentials of the Künneth bicomplex are `K ⊗ Q.X p` and `K ◁ Q.d`,
  -- all by definition
  exact h.symm

/-- **The Künneth spectral sequence**: the spectral sequence of the column filtration of the
Künneth bicomplex `HomologicalComplex.kunnethBicomplex K L`, whose column `p` is `K ⊗ Q.X p` for
the Cartan–Eilenberg resolution `Q` of `L`. Its first page is the graded tensor product of the
homology of `K` with the homology of the rows of `Q`
(`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`), and its second page is
`⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))` (`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`).
When every term of `K` is flat it converges to the homology of `K ⊗ L`
(`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). -/
abbrev kunnethSpectralSequence :=
  (kunnethBicomplex K L).columnFiltrationSpectralSequence

/-- **The first page of the Künneth spectral sequence.** Its object at column `p`, degree `k`
is `⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, through the Künneth map of `K` and `Q.X p`, which is an
isomorphism because `Q.X p` has projective terms and projective homology. -/
def kunnethSpectralSequenceFirstPageXIso (p k : ℕ) :
    ((kunnethSpectralSequence K L).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      GradedObject.Monoidal.tensorObj (fun i ↦ K.homology i)
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) k :=
  (kunnethBicomplex K L).columnFiltrationSpectralSequenceFirstPageXIso p k ≪≫
    (asIso (kunnethColumnHomologyKunneth K L p k)).symm

/-- The identification of the first page of the Künneth spectral sequence is that of the first
page of the column filtration with the homology of the columns
(`HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso`), followed by the inverse of
the Künneth map. -/
lemma kunnethSpectralSequenceFirstPageXIso_eq (p k : ℕ) :
    kunnethSpectralSequenceFirstPageXIso K L p k =
      (kunnethBicomplex K L).columnFiltrationSpectralSequenceFirstPageXIso p k ≪≫
        (asIso (kunnethColumnHomologyKunneth K L p k)).symm :=
  (rfl)

/-- **The first differential of the Künneth spectral sequence.** Under the identifications
`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`, the differential of the first page from
column `p + 1` to column `p` in degree `k` is `(-1)^k` times the map
`⨁ Hᵢ(K) ⊗ Hⱼ(Q.X (p + 1)) ⟶ ⨁ Hᵢ(K) ⊗ Hⱼ(Q.X p)` induced by the maps `Hⱼ(Q.d (p + 1) p)`. -/
theorem kunnethSpectralSequence_page_two_d (p k : ℕ) :
    (kunnethSpectralSequenceFirstPageXIso K L (p + 1) k).inv ≫
      ((kunnethSpectralSequence K L).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (kunnethSpectralSequenceFirstPageXIso K L p k).hom =
    ((-1 : ℤ) ^ k) • GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
      (fun j ↦ homologyMap ((cartanEilenbergResolution L).d (p + 1) p) j) k := by
  simp only [kunnethSpectralSequenceFirstPageXIso_eq, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  rw [reassoc_of% ((kunnethBicomplex K L).columnFiltrationSpectralSequence_page_two_d p k),
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, kunnethColumnHomologyKunneth_naturality_assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-! ### The second page -/

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The complex `p ↦ Hᵢ(K) ⊗ Hⱼ(Q.X p)`: the projective resolution
`ChainComplex.cartanEilenbergResolution.homologyResolution L j` of `Hⱼ(L)`, tensored on the left
with `Hᵢ(K)`. Its homology is `Tor (Hᵢ(K)) (Hⱼ(L))`. -/
abbrev kunnethTorComplex (i j : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (((tensoringLeft _).obj (K.homology i)).mapHomologicalComplex _).obj
    (homologyResolution L j).complex

/-- The direct sum over `i + j = q` of the complexes `kunnethTorComplex K L i j`. Under the
identifications `HomologicalComplex.kunnethFirstPageXIsoTorSum`, it is the row of the first page
of the Künneth spectral sequence in degree `q`, up to the sign `(-1)^q` of its differential. -/
abbrev kunnethTorSumComplex (q : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ⨁ fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2

/-- In degree `p`, the complex `kunnethTorComplex K L i j` is `Hᵢ(K) ⊗ Hⱼ(Q.X p)`. -/
def kunnethTorComplexXIso (i j p : ℕ) :
    (kunnethTorComplex K L i j).X p ≅
      K.homology i ⊗ ((cartanEilenbergResolution L).X p).homology j :=
  -- the term of `homologyResolution L j` in degree `p` is `Hⱼ(Q.X p)` by definition
  Iso.refl _

/-- The differential of `kunnethTorComplex K L i j` is `Hᵢ(K)` tensored with the map induced on
`Hⱼ` by the differential of the Cartan–Eilenberg resolution. -/
@[reassoc]
lemma kunnethTorComplexXIso_inv_d (i j p : ℕ) :
    (kunnethTorComplexXIso K L i j (p + 1)).inv ≫ (kunnethTorComplex K L i j).d (p + 1) p =
      K.homology i ◁ homologyMap ((cartanEilenbergResolution L).d (p + 1) p) j ≫
        (kunnethTorComplexXIso K L i j p).inv := by
  -- both identifications are identities, and the differential of `homologyResolution L j` is by
  -- definition the map induced on `Hⱼ` by the differential of `Q`
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The terms of `kunnethTorSumComplex K L q` are the graded tensor products
`⨁_{i + j = q} Hᵢ(K) ⊗ Hⱼ(Q.X p)`. -/
def tensorObjIsoKunnethTorSumComplexX (q p : ℕ) :
    GradedObject.Monoidal.tensorObj (fun i ↦ K.homology i)
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) q ≅
      (kunnethTorSumComplex K L q).X p :=
  GradedObject.Monoidal.tensorObjIsoBiproduct _ _ q ≪≫
    -- the summands `(kunnethTorComplex K L i j).X p` and `(eval _ _ p).obj (kunnethTorComplex K L
    -- i j)` agree by definition
    biproduct.mapIso (g := (HomologicalComplex.eval _ _ p).obj ∘
        fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2)
      (fun x ↦ (kunnethTorComplexXIso K L x.val.1 x.val.2 p).symm) ≪≫
    ((HomologicalComplex.eval _ _ p).mapBiproduct _).symm

/-- On the summand `Hᵢ(K) ⊗ Hⱼ(Q.X p)`, the identification
`HomologicalComplex.tensorObjIsoKunnethTorSumComplexX` is the inclusion of the summand
`kunnethTorComplex K L i j` of `kunnethTorSumComplex K L q`, in degree `p`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom (q p i j : ℕ) (h : i + j = q) :
    GradedObject.Monoidal.ιTensorObj (fun i ↦ K.homology i)
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) i j q h ≫
      (tensorObjIsoKunnethTorSumComplexX K L q p).hom =
    (kunnethTorComplexXIso K L i j p).inv ≫
      (biproduct.ι (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2)
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩).f p := by
  simp only [tensorObjIsoKunnethTorSumComplexX, Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom,
    GradedObject.Monoidal.ι_tensorObjIsoBiproduct_hom_assoc]
  rw [biproduct.ι_map_assoc, Functor.mapBiproduct_inv, biproduct.ι_desc, eval_map]

/-- Under the identifications `HomologicalComplex.tensorObjIsoKunnethTorSumComplexX`, the
differential of `kunnethTorSumComplex K L q` is induced by the maps `homologyMap (Q.d (p + 1) p) j`.
-/
@[reassoc]
lemma tensorObjIsoKunnethTorSumComplexX_hom_d (q p : ℕ) :
    (tensorObjIsoKunnethTorSumComplexX K L q (p + 1)).hom ≫
      (kunnethTorSumComplex K L q).d (p + 1) p =
      GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
          (fun j ↦ homologyMap ((cartanEilenbergResolution L).d (p + 1) p) j) q ≫
        (tensorObjIsoKunnethTorSumComplexX K L q p).hom := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
  simp only [ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom_assoc, Hom.comm,
    GradedObject.Monoidal.ι_tensorHom_assoc]
  rw [ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom, kunnethTorComplexXIso_inv_d_assoc,
    Pi.id_apply,
    id_tensorHom]

/-- The homology of `kunnethTorComplex K L i j` in degree `p` is `Torₚ(Hᵢ(K), Hⱼ(L))`, computed by
the projective resolution `ChainComplex.cartanEilenbergResolution.homologyResolution L j`. -/
def kunnethTorComplexHomologyIso (i j p : ℕ) :
    (HomologicalComplex.homologyFunctor _ _ p).obj (kunnethTorComplex K L i j) ≅
      ((Tor (ModuleCat.{u} R) p).obj (K.homology i)).obj (L.homology j) :=
  -- `Tor` is by definition the left derived functor of the tensor product in the second variable
  ((homologyResolution L j).isoLeftDerivedObj ((tensoringLeft _).obj (K.homology i)) p).symm

/-- The identification `HomologicalComplex.kunnethTorComplexHomologyIso` is the computation of a
left derived functor by a projective resolution (`ProjectiveResolution.isoLeftDerivedObj`). -/
lemma kunnethTorComplexHomologyIso_hom (i j p : ℕ) :
    (kunnethTorComplexHomologyIso K L i j p).hom =
      ((homologyResolution L j).isoLeftDerivedObj ((tensoringLeft _).obj (K.homology i)) p).inv :=
  (rfl)

/-- The homology of `kunnethTorSumComplex K L q` in degree `p` is
`⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`. -/
def kunnethTorSumComplexHomologyIso (q p : ℕ) :
    (kunnethTorSumComplex K L q).homology p ≅
      GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
        (fun i ↦ K.homology i) (fun j ↦ L.homology j) q :=
  (HomologicalComplex.homologyFunctor _ _ p).mapBiproduct _ ≪≫
    biproduct.mapIso (fun x ↦ kunnethTorComplexHomologyIso K L x.val.1 x.val.2 p) ≪≫
    (GradedObject.mapBifunctorMapObjIsoBiproduct (Tor (ModuleCat.{u} R) p)
      (fun i ↦ K.homology i) (fun j ↦ L.homology j) q).symm

/-- On the summand `kunnethTorComplex K L i j`, the identification
`HomologicalComplex.kunnethTorSumComplexHomologyIso` is
`HomologicalComplex.kunnethTorComplexHomologyIso`, followed by the inclusion of the summand. -/
@[reassoc (attr := simp)]
lemma homologyMap_ι_kunnethTorSumComplexHomologyIso_hom (q p i j : ℕ) (h : i + j = q) :
    homologyMap (biproduct.ι (fun x : Finset.antidiagonal q ↦
        kunnethTorComplex K L x.val.1 x.val.2) ⟨(i, j), Finset.mem_antidiagonal.2 h⟩) p ≫
      (kunnethTorSumComplexHomologyIso K L q p).hom =
    (kunnethTorComplexHomologyIso K L i j p).hom ≫
      GradedObject.ιMapBifunctorMapObj (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
        (fun i ↦ K.homology i) (fun j ↦ L.homology j) i j q h := by
  have hι : homologyMap (biproduct.ι (fun x : Finset.antidiagonal q ↦
        kunnethTorComplex K L x.val.1 x.val.2) ⟨(i, j), Finset.mem_antidiagonal.2 h⟩) p ≫
      ((HomologicalComplex.homologyFunctor _ _ p).mapBiproduct _).hom =
        biproduct.ι ((HomologicalComplex.homologyFunctor _ _ p).obj ∘
          fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2)
          ⟨(i, j), Finset.mem_antidiagonal.2 h⟩ := by
    rw [← Iso.eq_comp_inv, Functor.mapBiproduct_inv, biproduct.ι_desc, homologyFunctor_map]
  simp only [kunnethTorSumComplexHomologyIso, Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom,
    reassoc_of% hι, biproduct.ι_map_assoc]
  rw [GradedObject.ι_mapBifunctorMapObjIsoBiproduct_inv (Tor (ModuleCat.{u} R) p)
    (fun i ↦ K.homology i) (fun j ↦ L.homology j)]

/-- The identification of the first page of the Künneth spectral sequence at column `p`,
degree `q`, with the term of `kunnethTorSumComplex K L q` in degree `p`. -/
def kunnethFirstPageXIsoTorSum (p q : ℕ) :
    ((kunnethSpectralSequence K L).page 2).X (-(q : ℤ) - 2 * p, p) ≅
      (kunnethTorSumComplex K L q).X p :=
  kunnethSpectralSequenceFirstPageXIso K L p q ≪≫ tensorObjIsoKunnethTorSumComplexX K L q p

/-- The identification `kunnethFirstPageXIsoTorSum` is the identification of the first page with
the graded tensor object, followed by `tensorObjIsoKunnethTorSumComplexX`. -/
lemma kunnethFirstPageXIsoTorSum_eq (p q : ℕ) :
    kunnethFirstPageXIsoTorSum K L p q =
      kunnethSpectralSequenceFirstPageXIso K L p q ≪≫ tensorObjIsoKunnethTorSumComplexX K L q p :=
  (rfl)

/-- Under the identifications `HomologicalComplex.kunnethFirstPageXIsoTorSum`, the first
differential of the Künneth spectral sequence in degree `q` is `(-1)^q` times the differential of
`kunnethTorSumComplex K L q`. -/
@[reassoc]
lemma kunnethSpectralSequence_page_two_d_kunnethFirstPageXIsoTorSum (p q : ℕ) :
    ((kunnethSpectralSequence K L).page 2).d
        (-(q : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(q : ℤ) - 2 * p, p) ≫
      (kunnethFirstPageXIsoTorSum K L p q).hom =
    ((-1 : ℤ) ^ q) • ((kunnethFirstPageXIsoTorSum K L (p + 1) q).hom ≫
      (kunnethTorSumComplex K L q).d (p + 1) p) := by
  have h := kunnethSpectralSequence_page_two_d K L p q
  rw [Iso.inv_comp_eq] at h
  simp only [kunnethFirstPageXIsoTorSum_eq, Iso.trans_hom, Category.assoc,
    tensorObjIsoKunnethTorSumComplexX_hom_d]
  rw [reassoc_of% h, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- The third component of the comparison of the first page around column `p` with
`kunnethTorSumComplex K L q`: zero for `p = 0`, where the first page vanishes, and otherwise
`(-1)^q` times the identification `HomologicalComplex.kunnethFirstPageXIsoTorSum` at `p - 1`. -/
private def kunnethSecondPageτ₃ (q : ℕ) : (p : ℕ) →
    (((kunnethSpectralSequence K L).page 2).X (-(q : ℤ) - 2 * p + 2, (p : ℤ) - 1) ⟶
      (kunnethTorSumComplex K L q).X (p - 1))
  | 0 => 0
  | s + 1 => (((-1 : ℤˣ) ^ q) • (((kunnethSpectralSequence K L).page 2).XIsoOfEq
      (Prod.ext (by omega) (by omega)) ≪≫ kunnethFirstPageXIsoTorSum K L s q ≪≫
      (kunnethTorSumComplex K L q).XIsoOfEq (by omega))).hom

/-- The third component `kunnethSecondPageτ₃` is a monomorphism: its source is zero for `p = 0`,
and it is an isomorphism otherwise. -/
private instance (q p : ℕ) : Mono (kunnethSecondPageτ₃ K L q p) := by
  cases p with
  | zero =>
    refine ⟨fun _ _ _ ↦ IsZero.eq_of_tgt ?_ _ _⟩
    exact (kunnethBicomplex K L).flip.isZero_rowFiltrationSpectralSequence_page_two_X_of_neg _ _
      (by omega)
  | succ s => exact inferInstanceAs (Mono (((-1 : ℤˣ) ^ q) • _ : _ ≅ _).hom)

/-- The differential of `kunnethTorSumComplex K L q` leaving degree `p`, transported to the first
page, is the differential of the first page followed by `kunnethSecondPageτ₃`. -/
private lemma kunnethFirstPageXIsoTorSum_hom_d (p q : ℕ) :
    (kunnethFirstPageXIsoTorSum K L p q).hom ≫ (kunnethTorSumComplex K L q).d p (p - 1) =
      ((kunnethSpectralSequence K L).page 2).d (-(q : ℤ) - 2 * p, p)
        (-(q : ℤ) - 2 * p + 2, (p : ℤ) - 1) ≫ kunnethSecondPageτ₃ K L q p := by
  cases p with
  | zero =>
    rw [(kunnethTorSumComplex K L q).shape _ _ (by simp), comp_zero]
    simp only [kunnethSecondPageτ₃, comp_zero]
  | succ s =>
    simp only [kunnethSecondPageτ₃, Preadditive.smul_iso_hom, Units.smul_def, Iso.trans_hom,
      Preadditive.comp_zsmul, d_comp_XIsoOfEq_hom_assoc]
    rw [kunnethSpectralSequence_page_two_d_kunnethFirstPageXIsoTorSum_assoc]
    simp [smul_smul, ← mul_pow]

/-- A cycle of the first page of the Künneth spectral sequence at column `p`, degree `q` is sent by
`HomologicalComplex.kunnethFirstPageXIsoTorSum` to a cycle of `kunnethTorSumComplex K L q`. -/
@[reassoc (attr := simp)]
lemma iCycles_kunnethFirstPageXIsoTorSum_hom_d (p q : ℕ) :
    ((kunnethSpectralSequence K L).page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
      (kunnethFirstPageXIsoTorSum K L p q).hom ≫ (kunnethTorSumComplex K L q).d p (p - 1) = 0 := by
  rw [kunnethFirstPageXIsoTorSum_hom_d, iCycles_d_assoc, zero_comp]

/-- The comparison of the first page of the Künneth spectral sequence around column `p`, in
degree `q`, with `kunnethTorSumComplex K L q` around degree `p`. Its components are, up to the
sign `(-1)^q` on the outer terms, the identifications
`HomologicalComplex.kunnethFirstPageXIsoTorSum`. -/
private def kunnethSecondPageShortComplexHom (p q : ℕ) :
    ((kunnethSpectralSequence K L).page 2).sc'
        (-(q : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(q : ℤ) - 2 * p, p)
        (-(q : ℤ) - 2 * p + 2, (p : ℤ) - 1) ⟶
      (kunnethTorSumComplex K L q).sc' (p + 1) p (p - 1) where
  τ₁ := (((-1 : ℤˣ) ^ q) • kunnethFirstPageXIsoTorSum K L (p + 1) q).hom
  τ₂ := (kunnethFirstPageXIsoTorSum K L p q).hom
  τ₃ := kunnethSecondPageτ₃ K L q p
  comm₁₂ := by
    dsimp only [shortComplexFunctor'_obj_f]
    rw [kunnethSpectralSequence_page_two_d_kunnethFirstPageXIsoTorSum]
    simp [Units.smul_def]
  comm₂₃ := by
    dsimp only [shortComplexFunctor'_obj_g]
    exact kunnethFirstPageXIsoTorSum_hom_d K L p q

/-- The second component of `kunnethSecondPageShortComplexHom` is
`HomologicalComplex.kunnethFirstPageXIsoTorSum`. -/
private lemma kunnethSecondPageShortComplexHom_τ₂ (p q : ℕ) :
    (kunnethSecondPageShortComplexHom K L p q).τ₂ = (kunnethFirstPageXIsoTorSum K L p q).hom :=
  (rfl)

/-- The comparison `kunnethSecondPageShortComplexHom` induces an isomorphism on homology: its first
two components are isomorphisms and its third is a monomorphism. -/
private instance (p q : ℕ) : ShortComplex.QuasiIso (kunnethSecondPageShortComplexHom K L p q) := by
  have : IsIso (kunnethSecondPageShortComplexHom K L p q).τ₁ :=
    inferInstanceAs (IsIso (((-1 : ℤˣ) ^ q) • _ : _ ≅ _).hom)
  have : IsIso (kunnethSecondPageShortComplexHom K L p q).τ₂ :=
    inferInstanceAs (IsIso (kunnethFirstPageXIsoTorSum K L p q).hom)
  have : Mono (kunnethSecondPageShortComplexHom K L p q).τ₃ :=
    inferInstanceAs (Mono (kunnethSecondPageτ₃ K L q p))
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono _

/-- **The second page of the Künneth spectral sequence.** The object at column `p`, degree `q`
of the second page (numbered `3`) of the Künneth spectral sequence is
`⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`. -/
def kunnethSpectralSequenceSecondPageXIso (p q : ℕ) :
    ((kunnethSpectralSequence K L).page 3).X (-(q : ℤ) - 2 * p, p) ≅
      GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
        (fun i ↦ K.homology i) (fun j ↦ L.homology j) q :=
  ((kunnethSpectralSequence K L).iso 2 3 (-(q : ℤ) - 2 * p, p)).symm ≪≫
    ((kunnethSpectralSequence K L).page 2 le_rfl).homologyIsoSc'
      (-(q : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(q : ℤ) - 2 * p, p)
      (-(q : ℤ) - 2 * p + 2, (p : ℤ) - 1)
      ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
      ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega))) ≪≫
    asIso (ShortComplex.homologyMap (kunnethSecondPageShortComplexHom K L p q)) ≪≫
    ((kunnethTorSumComplex K L q).homologyIsoSc' (p + 1) p (p - 1) (by simp)
      (by cases p <;> simp)).symm ≪≫
    kunnethTorSumComplexHomologyIso K L q p

/-- **The second-page isomorphism on classes of cycles.** The class on the second page of a cycle
`z` of the first page at column `p`, degree `q`, is sent by
`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso` to the image under
`HomologicalComplex.kunnethTorSumComplexHomologyIso` of the class of the cycle
`(kunnethFirstPageXIsoTorSum K L p q).hom z` of `kunnethTorSumComplex K L q`. -/
lemma homologyπ_kunnethSpectralSequenceSecondPageXIso_hom (p q : ℕ) :
    ((kunnethSpectralSequence K L).page 2).homologyπ (-(q : ℤ) - 2 * p, p) ≫
        ((kunnethSpectralSequence K L).iso 2 3 (-(q : ℤ) - 2 * p, p)).hom ≫
        (kunnethSpectralSequenceSecondPageXIso K L p q).hom =
      (kunnethTorSumComplex K L q).liftCycles
          (((kunnethSpectralSequence K L).page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
            (kunnethFirstPageXIsoTorSum K L p q).hom) (p - 1) (by cases p <;> simp)
          (by rw [Category.assoc, iCycles_kunnethFirstPageXIsoTorSum_hom_d]) ≫
        (kunnethTorSumComplex K L q).homologyπ p ≫
          (kunnethTorSumComplexHomologyIso K L q p).hom := by
  have h : (((kunnethSpectralSequence K L).page 2).cyclesIsoSc'
        (-(q : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(q : ℤ) - 2 * p, p)
        (-(q : ℤ) - 2 * p + 2, (p : ℤ) - 1)
        ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
        ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega)))).hom ≫
      ShortComplex.cyclesMap (kunnethSecondPageShortComplexHom K L p q) ≫
      ((kunnethTorSumComplex K L q).cyclesIsoSc' (p + 1) p (p - 1) (by simp)
        (by cases p <;> simp)).inv =
      (kunnethTorSumComplex K L q).liftCycles
        (((kunnethSpectralSequence K L).page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
          (kunnethFirstPageXIsoTorSum K L p q).hom) (p - 1) (by cases p <;> simp)
        (by rw [Category.assoc, iCycles_kunnethFirstPageXIsoTorSum_hom_d]) := by
    rw [← cancel_mono ((kunnethTorSumComplex K L q).iCycles p)]
    simp [kunnethSecondPageShortComplexHom_τ₂]
  simp only [kunnethSpectralSequenceSecondPageXIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [Iso.hom_inv_id_assoc]
  simp only [π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    π_homologyIsoSc'_inv_assoc, reassoc_of% h]

/-- **Morphisms of Künneth spectral sequences on the second page, from the first page.** Let
`F` be a morphism of Künneth spectral sequences whose first-page component at column `p`,
degree `q` corresponds, under the identifications
`HomologicalComplex.kunnethFirstPageXIsoTorSum`, to the component in degree `p` of a chain map
`T : kunnethTorSumComplex K L q ⟶ kunnethTorSumComplex K' L' q`. Then, under the identifications
`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`, its second-page component is the map
induced on homology by `T`, transported by `HomologicalComplex.kunnethTorSumComplexHomologyIso`. -/
@[reassoc]
theorem kunnethSpectralSequenceSecondPageXIso_hom_naturality_of_firstPage
    {K' L' : ChainComplex (ModuleCat.{u} R) ℕ}
    (F : kunnethSpectralSequence K L ⟶ kunnethSpectralSequence K' L') (p q : ℕ)
    (T : kunnethTorSumComplex K L q ⟶ kunnethTorSumComplex K' L' q)
    (hF : (F.hom 2).f (-(q : ℤ) - 2 * p, p) ≫ (kunnethFirstPageXIsoTorSum K' L' p q).hom =
      (kunnethFirstPageXIsoTorSum K L p q).hom ≫ T.f p) :
    (F.hom 3).f (-(q : ℤ) - 2 * p, p) ≫ (kunnethSpectralSequenceSecondPageXIso K' L' p q).hom =
      (kunnethSpectralSequenceSecondPageXIso K L p q).hom ≫
        (kunnethTorSumComplexHomologyIso K L q p).inv ≫ homologyMap T p ≫
          (kunnethTorSumComplexHomologyIso K' L' q p).hom := by
  -- the square of cycles: the first-page component of `F`, on cycles, followed by the lift to the
  -- cycles of `kunnethTorSumComplex K' L' q`, is the lift to the cycles of
  -- `kunnethTorSumComplex K L q` followed by the map induced by `T`
  have hcycles : cyclesMap (F.hom 2) (-(q : ℤ) - 2 * p, p) ≫
      (kunnethTorSumComplex K' L' q).liftCycles
        (((kunnethSpectralSequence K' L').page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
          (kunnethFirstPageXIsoTorSum K' L' p q).hom) (p - 1) (by cases p <;> simp)
        (by rw [Category.assoc, iCycles_kunnethFirstPageXIsoTorSum_hom_d]) =
      (kunnethTorSumComplex K L q).liftCycles
        (((kunnethSpectralSequence K L).page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
          (kunnethFirstPageXIsoTorSum K L p q).hom) (p - 1) (by cases p <;> simp)
        (by rw [Category.assoc, iCycles_kunnethFirstPageXIsoTorSum_hom_d]) ≫ cyclesMap T p := by
    rw [comp_liftCycles, liftCycles_comp_cyclesMap]
    congr 1
    rw [cyclesMap_i_assoc, hF, Category.assoc]
  rw [← cancel_epi (((kunnethSpectralSequence K L).page 2).homologyπ (-(q : ℤ) - 2 * p, p) ≫
    ((kunnethSpectralSequence K L).iso 2 3 (-(q : ℤ) - 2 * p, p)).hom)]
  rw [Category.assoc, Category.assoc,
    reassoc_of% (homologyπ_kunnethSpectralSequenceSecondPageXIso_hom K L p q),
    ← F.comm_assoc 2 3, homologyπ_naturality_assoc,
    homologyπ_kunnethSpectralSequenceSecondPageXIso_hom, reassoc_of% hcycles,
    Iso.hom_inv_id_assoc, homologyπ_naturality_assoc]

/-! ### Naturality in the first variable -/

section Naturality

variable {K} {K' : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ K')

/-- Naturality of `kunnethColumnHomologyKunneth` in the first variable, with respect to the
morphism of Künneth bicomplexes `HomologicalComplex.kunnethBicomplexMapLeft f L`. -/
@[reassoc]
lemma kunnethColumnHomologyKunneth_naturality_left (p k : ℕ) :
    GradedObject.Monoidal.whiskerRight (fun i ↦ homologyMap f i)
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) k ≫
        kunnethColumnHomologyKunneth K' L p k =
      kunnethColumnHomologyKunneth K L p k ≫
        homologyMap ((kunnethBicomplexMapLeft f L).f p) k := by
  have h := homologyKunneth_naturality f (𝟙 ((cartanEilenbergResolution L).X p)) k
  have e₁ : (fun j ↦ homologyMap (𝟙 ((cartanEilenbergResolution L).X p)) j) =
      𝟙 (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) :=
    funext fun j ↦ homologyMap_id _ j
  -- `HomologicalComplex.tensorHom` is the tensor product of morphisms of the monoidal structure
  -- on complexes by definition
  have e₂ : HomologicalComplex.tensorHom f (𝟙 ((cartanEilenbergResolution L).X p)) =
      f ▷ (cartanEilenbergResolution L).X p := by
    exact MonoidalCategory.tensorHom_id f ((cartanEilenbergResolution L).X p)
  rw [e₁, e₂] at h
  rw [kunnethColumnHomologyKunneth_eq, kunnethColumnHomologyKunneth_eq, kunnethBicomplexMapLeft_f]
  -- the columns of the Künneth bicomplexes are `K ⊗ Q.X p` by definition
  exact h

end Naturality

end HomologicalComplex

namespace HomologicalComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R]

variable {K K' K'' : ChainComplex (ModuleCat.{u} R) ℕ} (L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The morphism of complexes `kunnethTorComplex K L i j ⟶ kunnethTorComplex K' L i j` induced by
a morphism `u : Hᵢ(K) ⟶ Hᵢ(K')` of coefficients: in degree `p`, it is `u ▷ Hⱼ(Q.X p)`
(`HomologicalComplex.kunnethTorComplexXIso_inv_kunnethTorComplexMap_f`). -/
def kunnethTorComplexMap {i : ℕ} (u : K.homology i ⟶ K'.homology i) (j : ℕ) :
    kunnethTorComplex K L i j ⟶ kunnethTorComplex K' L i j :=
  (NatTrans.mapHomologicalComplex ((tensoringLeft _).map u) _).app
    (homologyResolution L j).complex

/-- The identity of `Hᵢ(K)` induces the identity of `kunnethTorComplex K L i j`. -/
@[simp]
lemma kunnethTorComplexMap_id (i j : ℕ) :
    kunnethTorComplexMap L (𝟙 (K.homology i)) j = 𝟙 _ := by
  rw [kunnethTorComplexMap, CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id,
    NatTrans.id_app]

/-- `HomologicalComplex.kunnethTorComplexMap` is compatible with composition. -/
@[simp]
lemma kunnethTorComplexMap_comp {i : ℕ} (u : K.homology i ⟶ K'.homology i)
    (u' : K'.homology i ⟶ K''.homology i) (j : ℕ) :
    kunnethTorComplexMap L (u ≫ u') j =
      kunnethTorComplexMap L u j ≫ kunnethTorComplexMap L u' j := by
  simp only [kunnethTorComplexMap, CategoryTheory.Functor.map_comp,
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- In degree `p`, the morphism `HomologicalComplex.kunnethTorComplexMap L u j` is
`u ▷ Hⱼ(Q.X p)`. -/
@[reassoc]
lemma kunnethTorComplexXIso_inv_kunnethTorComplexMap_f {i : ℕ} (u : K.homology i ⟶ K'.homology i)
    (j p : ℕ) :
    (kunnethTorComplexXIso K L i j p).inv ≫ (kunnethTorComplexMap L u j).f p =
      u ▷ ((cartanEilenbergResolution L).X p).homology j ≫
        (kunnethTorComplexXIso K' L i j p).inv := by
  -- both identifications are identities, and the component of `kunnethTorComplexMap L u j` in
  -- degree `p` is `u ▷ Hⱼ(Q.X p)` by definition
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The identifications `HomologicalComplex.kunnethTorComplexHomologyIso` with `Tor` are natural in
the coefficients: the map induced on homology by `HomologicalComplex.kunnethTorComplexMap L u j`
is the map `Torₚ(u, Hⱼ(L))`. -/
@[reassoc]
lemma kunnethTorComplexHomologyIso_hom_naturality {i : ℕ} (u : K.homology i ⟶ K'.homology i)
    (j p : ℕ) :
    homologyMap (kunnethTorComplexMap L u j) p ≫ (kunnethTorComplexHomologyIso K' L i j p).hom =
      (kunnethTorComplexHomologyIso K L i j p).hom ≫
        ((Tor (ModuleCat.{u} R) p).map u).app (L.homology j) := by
  have h := ProjectiveResolution.Tor_map_app_comp_isoLeftDerivedObj_hom u
    (homologyResolution L j) p
  rw [kunnethTorComplexHomologyIso_hom, kunnethTorComplexHomologyIso_hom, kunnethTorComplexMap]
  -- the objects `Torₚ(A, Y)` and `Lₚ(A ⊗ -)(Y)`, and `homology` and the homology functor, agree by
  -- definition, so the square is inverted as a term rather than by rewriting
  exact (Iso.eq_inv_comp _).2 ((Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).2 h.symm))

/-- The morphism of complexes `kunnethTorSumComplex K L q ⟶ kunnethTorSumComplex K' L q` induced by
a morphism `u` of graded coefficient objects `(Hᵢ(K))ᵢ ⟶ (Hᵢ(K'))ᵢ`: the direct sum of the
morphisms `HomologicalComplex.kunnethTorComplexMap L (u i) j`. -/
def kunnethTorSumComplexMap (u : (fun i ↦ K.homology i) ⟶ (fun i ↦ K'.homology i)) (q : ℕ) :
    kunnethTorSumComplex K L q ⟶ kunnethTorSumComplex K' L q :=
  biproduct.map fun x ↦ kunnethTorComplexMap L (u x.val.1) x.val.2

/-- On the summand `kunnethTorComplex K L i j`, the morphism
`HomologicalComplex.kunnethTorSumComplexMap L u q` is
`HomologicalComplex.kunnethTorComplexMap L (u i) j`. -/
@[reassoc (attr := simp)]
lemma ι_kunnethTorSumComplexMap (u : (fun i ↦ K.homology i) ⟶ (fun i ↦ K'.homology i)) (q : ℕ)
    (x : Finset.antidiagonal q) :
    biproduct.ι (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2) x ≫
        kunnethTorSumComplexMap L u q =
      kunnethTorComplexMap L (u x.val.1) x.val.2 ≫
        biproduct.ι (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K' L x.val.1 x.val.2) x := by
  rw [kunnethTorSumComplexMap, biproduct.ι_map]

/-- The identity of the coefficients induces the identity of `kunnethTorSumComplex K L q`. -/
@[simp]
lemma kunnethTorSumComplexMap_id (q : ℕ) :
    kunnethTorSumComplexMap L (𝟙 (fun i ↦ K.homology i)) q = 𝟙 _ :=
  biproduct.hom_ext' _ _ fun x ↦ by
    rw [ι_kunnethTorSumComplexMap, Pi.id_apply, kunnethTorComplexMap_id, Category.id_comp,
      Category.comp_id]

/-- `HomologicalComplex.kunnethTorSumComplexMap` is compatible with composition. -/
@[simp]
lemma kunnethTorSumComplexMap_comp (u : (fun i ↦ K.homology i) ⟶ (fun i ↦ K'.homology i))
    (u' : (fun i ↦ K'.homology i) ⟶ (fun i ↦ K''.homology i)) (q : ℕ) :
    kunnethTorSumComplexMap L (u ≫ u') q =
      kunnethTorSumComplexMap L u q ≫ kunnethTorSumComplexMap L u' q :=
  biproduct.hom_ext' _ _ fun x ↦ by
    rw [ι_kunnethTorSumComplexMap, ι_kunnethTorSumComplexMap_assoc, Pi.comp_apply,
      kunnethTorComplexMap_comp, Category.assoc, ι_kunnethTorSumComplexMap]

/-- The identifications `HomologicalComplex.tensorObjIsoKunnethTorSumComplexX` are natural in the
coefficients. -/
@[reassoc]
lemma tensorObjIsoKunnethTorSumComplexX_hom_naturality
    (u : (fun i ↦ K.homology i) ⟶ (fun i ↦ K'.homology i)) (q p : ℕ) :
    GradedObject.Monoidal.whiskerRight u
        (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) q ≫
      (tensorObjIsoKunnethTorSumComplexX K' L q p).hom =
    (tensorObjIsoKunnethTorSumComplexX K L q p).hom ≫ (kunnethTorSumComplexMap L u q).f p := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc,
    ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom_assoc,
    ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom, ← comp_f, ι_kunnethTorSumComplexMap]
  rw [comp_f, kunnethTorComplexXIso_inv_kunnethTorComplexMap_f_assoc]
  -- the identity of the graded object `j ↦ Hⱼ(Q.X p)` is the identity of `Hⱼ(Q.X p)` in degree
  -- `j` by definition
  exact congrArg (· ≫ _) (MonoidalCategory.tensorHom_id _ _)

/-- The identifications `HomologicalComplex.kunnethTorSumComplexHomologyIso` with
`⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))` are natural in the coefficients: the map induced on homology by
`HomologicalComplex.kunnethTorSumComplexMap L u q` is induced by the maps `Torₚ(u i, Hⱼ(L))`. -/
@[reassoc]
lemma kunnethTorSumComplexHomologyIso_hom_naturality
    (u : (fun i ↦ K.homology i) ⟶ (fun i ↦ K'.homology i)) (q p : ℕ) :
    homologyMap (kunnethTorSumComplexMap L u q) p ≫
        (kunnethTorSumComplexHomologyIso K' L q p).hom =
      (kunnethTorSumComplexHomologyIso K L q p).hom ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
          u (𝟙 fun j ↦ L.homology j) q := by
  rw [← cancel_epi ((HomologicalComplex.homologyFunctor _ _ p).mapBiproduct
    (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2)).inv]
  refine biproduct.hom_ext' _ _ fun ⟨⟨i, j⟩, h⟩ ↦ ?_
  have h' : i + j = q := Finset.mem_antidiagonal.1 h
  simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, homologyFunctor_map]
  rw [← homologyMap_comp_assoc, ι_kunnethTorSumComplexMap, homologyMap_comp_assoc,
    homologyMap_ι_kunnethTorSumComplexHomologyIso_hom (h := h'),
    homologyMap_ι_kunnethTorSumComplexHomologyIso_hom_assoc (h := h'),
    kunnethTorComplexHomologyIso_hom_naturality_assoc, GradedObject.ι_mapBifunctorMapMap]
  simp only [Pi.id_apply]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end HomologicalComplex

/-! ### Naturality in the second variable -/

namespace HomologicalComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)
  {L L' L'' : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Naturality of `kunnethColumnHomologyKunneth` in the second variable, with respect to a
morphism `ψ : Q.X p ⟶ Q'.X p` of the rows `p` of the Cartan–Eilenberg resolutions of `L` and
`L'`. -/
@[reassoc]
lemma kunnethColumnHomologyKunneth_naturality_right (p k : ℕ)
    (ψ : (cartanEilenbergResolution L).X p ⟶ (cartanEilenbergResolution L').X p) :
    GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i) (fun j ↦ homologyMap ψ j) k ≫
        kunnethColumnHomologyKunneth K L' p k =
      kunnethColumnHomologyKunneth K L p k ≫ homologyMap (K ◁ ψ) k := by
  have h := homologyKunneth_naturality (𝟙 K) ψ k
  have e₁ : (fun i ↦ homologyMap (𝟙 K) i) = 𝟙 (fun i ↦ K.homology i) :=
    funext fun i ↦ homologyMap_id _ i
  -- `HomologicalComplex.tensorHom` is the tensor product of morphisms of the monoidal structure
  -- on complexes by definition
  have e₂ : HomologicalComplex.tensorHom (𝟙 K) ψ = K ◁ ψ := by
    exact MonoidalCategory.id_tensorHom K ψ
  rw [e₁, e₂] at h
  rw [kunnethColumnHomologyKunneth_eq, kunnethColumnHomologyKunneth_eq]
  -- the columns of the Künneth bicomplexes are `K ⊗ Q.X p` by definition
  exact h

/-- The morphism of complexes `kunnethTorComplex K L i j ⟶ kunnethTorComplex K L' i j` induced by
a morphism `φ` of the complexes of the projective resolutions `homologyResolution L j` and
`homologyResolution L' j`: `Hᵢ(K) ⊗ φ`. -/
def kunnethTorComplexMapRight (i : ℕ) {j : ℕ}
    (φ : (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex) :
    kunnethTorComplex K L i j ⟶ kunnethTorComplex K L' i j :=
  (((tensoringLeft _).obj (K.homology i)).mapHomologicalComplex _).map φ

/-- The identity of the resolution induces the identity of `kunnethTorComplex K L i j`. -/
@[simp]
lemma kunnethTorComplexMapRight_id (i j : ℕ) :
    kunnethTorComplexMapRight K i (𝟙 (homologyResolution L j).complex) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- `HomologicalComplex.kunnethTorComplexMapRight` is compatible with composition. -/
@[simp]
lemma kunnethTorComplexMapRight_comp (i : ℕ) {j : ℕ}
    (φ : (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex)
    (φ' : (homologyResolution L' j).complex ⟶ (homologyResolution L'' j).complex) :
    kunnethTorComplexMapRight K i (φ ≫ φ') =
      kunnethTorComplexMapRight K i φ ≫ kunnethTorComplexMapRight K i φ' :=
  CategoryTheory.Functor.map_comp _ _ _

/-- In degree `p`, the morphism `HomologicalComplex.kunnethTorComplexMapRight K i φ` is
`Hᵢ(K) ◁ φ.f p`. -/
@[reassoc]
lemma kunnethTorComplexXIso_inv_kunnethTorComplexMapRight_f (i : ℕ) {j : ℕ}
    (φ : (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex) (p : ℕ) :
    (kunnethTorComplexXIso K L i j p).inv ≫ (kunnethTorComplexMapRight K i φ).f p =
      K.homology i ◁ φ.f p ≫ (kunnethTorComplexXIso K L' i j p).inv := by
  -- both identifications are identities, and the component of `kunnethTorComplexMapRight K i φ`
  -- in degree `p` is `Hᵢ(K) ◁ φ.f p` by definition
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The identifications `HomologicalComplex.kunnethTorComplexHomologyIso` with `Tor` are natural in
the second variable: if `φ` lies over `v : Hⱼ(L) ⟶ Hⱼ(L')`, the map induced on homology by
`HomologicalComplex.kunnethTorComplexMapRight K i φ` is the map `Torₚ(Hᵢ(K), v)`. -/
@[reassoc]
lemma kunnethTorComplexHomologyIso_hom_naturality_right (i : ℕ) {j : ℕ}
    (φ : (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex)
    (v : L.homology j ⟶ L'.homology j)
    (hφ : φ.f 0 ≫ (homologyResolution L' j).π.f 0 = (homologyResolution L j).π.f 0 ≫ v)
    (p : ℕ) :
    homologyMap (kunnethTorComplexMapRight K i φ) p ≫
        (kunnethTorComplexHomologyIso K L' i j p).hom =
      (kunnethTorComplexHomologyIso K L i j p).hom ≫
        ((Tor (ModuleCat.{u} R) p).obj (K.homology i)).map v := by
  rw [kunnethTorComplexHomologyIso_hom, kunnethTorComplexHomologyIso_hom,
    kunnethTorComplexMapRight]
  -- `(Tor _ p).obj A` is `Lₚ(A ⊗ -)` and `homologyMap` is the action of the homology functor on
  -- morphisms, both by definition
  exact (ProjectiveResolution.isoLeftDerivedObj_inv_naturality v _ _ φ hφ _ p).symm

/-- The morphism of complexes `kunnethTorSumComplex K L q ⟶ kunnethTorSumComplex K L' q` induced by
a family `φ` of morphisms of the complexes of the projective resolutions `homologyResolution L j`
and `homologyResolution L' j`: the direct sum of the morphisms
`HomologicalComplex.kunnethTorComplexMapRight K i (φ j)`. -/
def kunnethTorSumComplexMapRight
    (φ : ∀ j, (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex) (q : ℕ) :
    kunnethTorSumComplex K L q ⟶ kunnethTorSumComplex K L' q :=
  biproduct.map fun x ↦ kunnethTorComplexMapRight K x.val.1 (φ x.val.2)

/-- On the summand `kunnethTorComplex K L i j`, the morphism
`HomologicalComplex.kunnethTorSumComplexMapRight K φ q` is
`HomologicalComplex.kunnethTorComplexMapRight K i (φ j)`. -/
@[reassoc (attr := simp)]
lemma ι_kunnethTorSumComplexMapRight
    (φ : ∀ j, (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex) (q : ℕ)
    (x : Finset.antidiagonal q) :
    biproduct.ι (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2) x ≫
        kunnethTorSumComplexMapRight K φ q =
      kunnethTorComplexMapRight K x.val.1 (φ x.val.2) ≫
        biproduct.ι (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L' x.val.1 x.val.2) x := by
  rw [kunnethTorSumComplexMapRight, biproduct.ι_map]

/-- The identities of the resolutions induce the identity of `kunnethTorSumComplex K L q`. -/
@[simp]
lemma kunnethTorSumComplexMapRight_id (q : ℕ) :
    kunnethTorSumComplexMapRight K (L := L) (fun j ↦ 𝟙 _) q = 𝟙 _ :=
  biproduct.hom_ext' _ _ fun x ↦ by
    rw [ι_kunnethTorSumComplexMapRight, kunnethTorComplexMapRight_id, Category.id_comp,
      Category.comp_id]

/-- `HomologicalComplex.kunnethTorSumComplexMapRight` is compatible with composition. -/
@[simp]
lemma kunnethTorSumComplexMapRight_comp
    (φ : ∀ j, (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex)
    (φ' : ∀ j, (homologyResolution L' j).complex ⟶ (homologyResolution L'' j).complex)
    (q : ℕ) :
    kunnethTorSumComplexMapRight K (fun j ↦ φ j ≫ φ' j) q =
      kunnethTorSumComplexMapRight K φ q ≫ kunnethTorSumComplexMapRight K φ' q :=
  biproduct.hom_ext' _ _ fun x ↦ by
    rw [ι_kunnethTorSumComplexMapRight, ι_kunnethTorSumComplexMapRight_assoc,
      kunnethTorComplexMapRight_comp, Category.assoc, ι_kunnethTorSumComplexMapRight]

/-- The identifications `HomologicalComplex.tensorObjIsoKunnethTorSumComplexX` are natural in the
second variable: for a family `φ` of morphisms of the resolutions whose components in degree `p`
are the maps `v j : Hⱼ(Q.X p) ⟶ Hⱼ(Q'.X p)`. -/
@[reassoc]
lemma tensorObjIsoKunnethTorSumComplexX_hom_naturality_right
    (φ : ∀ j, (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex) (q p : ℕ)
    (v : (fun j ↦ ((cartanEilenbergResolution L).X p).homology j) ⟶
      (fun j ↦ ((cartanEilenbergResolution L').X p).homology j))
    (hv : ∀ j, (φ j).f p = v j) :
    GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i) v q ≫
      (tensorObjIsoKunnethTorSumComplexX K L' q p).hom =
    (tensorObjIsoKunnethTorSumComplexX K L q p).hom ≫
      (kunnethTorSumComplexMapRight K φ q).f p := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc,
    ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom_assoc,
    ιTensorObj_tensorObjIsoKunnethTorSumComplexX_hom, ← comp_f, ι_kunnethTorSumComplexMapRight]
  rw [comp_f, kunnethTorComplexXIso_inv_kunnethTorComplexMapRight_f_assoc, hv]
  -- the identity of the graded object `i ↦ Hᵢ(K)` is the identity of `Hᵢ(K)` in degree `i` by
  -- definition
  exact congrArg (· ≫ _) (MonoidalCategory.id_tensorHom _ _)

/-- The identifications `HomologicalComplex.kunnethTorSumComplexHomologyIso` with
`⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))` are natural in the second variable: if each `φ j` lies over
`v j : Hⱼ(L) ⟶ Hⱼ(L')`, the map induced on homology by
`HomologicalComplex.kunnethTorSumComplexMapRight K φ q` is induced by the maps
`Torₚ(Hᵢ(K), v j)`. -/
@[reassoc]
lemma kunnethTorSumComplexHomologyIso_hom_naturality_right
    (φ : ∀ j, (homologyResolution L j).complex ⟶ (homologyResolution L' j).complex)
    (v : (fun j ↦ L.homology j) ⟶ (fun j ↦ L'.homology j))
    (hφ : ∀ j, (φ j).f 0 ≫ (homologyResolution L' j).π.f 0 =
      (homologyResolution L j).π.f 0 ≫ v j) (q p : ℕ) :
    homologyMap (kunnethTorSumComplexMapRight K φ q) p ≫
        (kunnethTorSumComplexHomologyIso K L' q p).hom =
      (kunnethTorSumComplexHomologyIso K L q p).hom ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
          (𝟙 fun i ↦ K.homology i) v q := by
  rw [← cancel_epi ((HomologicalComplex.homologyFunctor _ _ p).mapBiproduct
    (fun x : Finset.antidiagonal q ↦ kunnethTorComplex K L x.val.1 x.val.2)).inv]
  refine biproduct.hom_ext' _ _ fun ⟨⟨i, j⟩, h⟩ ↦ ?_
  have h' : i + j = q := Finset.mem_antidiagonal.1 h
  simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, homologyFunctor_map]
  rw [← homologyMap_comp_assoc, ι_kunnethTorSumComplexMapRight, homologyMap_comp_assoc,
    homologyMap_ι_kunnethTorSumComplexHomologyIso_hom (h := h'),
    homologyMap_ι_kunnethTorSumComplexHomologyIso_hom_assoc (h := h'),
    kunnethTorComplexHomologyIso_hom_naturality_right_assoc K i (φ j) (v j) (hφ j),
    GradedObject.ι_mapBifunctorMapMap]
  simp only [Pi.id_apply]
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

end HomologicalComplex
