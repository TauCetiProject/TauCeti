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
  `HomologicalComplex.homologyMap_ι_kunnethTorSumComplexHomologyIso_hom`.

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

end HomologicalComplex
