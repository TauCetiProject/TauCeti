/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.HomotopyCofiber

/-!
# Cartan–Eilenberg resolutions of chain complexes

Let `K` be a chain complex indexed by `ℕ` in an abelian category with enough projectives. This
file constructs a bicomplex `Q = ChainComplex.cartanEilenbergResolution K`, a chain complex of
chain complexes, with an augmentation `ChainComplex.cartanEilenbergResolutionπ K : Q.X 0 ⟶ K`,
such that

* every term `(Q.X p).X q` is projective, and so is every homology object `(Q.X p).homology q`
  of every row;
* for every `q`, the column `p ↦ (Q.X p).X q` is a projective resolution of `K.X q`
  (`ChainComplex.cartanEilenbergResolution.columnResolution`);
* for every `q`, the complex `p ↦ (Q.X p).homology q` of homology objects of the rows is a
  projective resolution of `K.homology q`
  (`ChainComplex.cartanEilenbergResolution.homologyResolution`).

These are the properties of a Cartan–Eilenberg resolution (Weibel, Definition 5.7.1) that the
Künneth spectral sequence uses: tensoring `Q` with a complex `L` gives a bicomplex whose rows
satisfy the Künneth formula, because they have projective terms and projective homology, and
whose homology in the resolution direction is then computed by the resolutions of the homology
objects of `K`, giving `Tor`.

## Construction

For a complex `M`, the cover `ChainComplex.cartanEilenbergResolution.cover M` is the direct sum of
two complexes. The first is the mapping cone of the identity of the complex with zero differentials
whose term in degree `q` is a projective object `Projective.over (M.X (q + 1))`; it is a sum of
disks, which is contractible. The second has zero differentials, and its term in degree `q` is a
projective object `Projective.over (M.cycles q)` mapping onto the cycles of `M`. The map
`ChainComplex.cartanEilenbergResolution.coverπ M : cover M ⟶ M` is an epimorphism in each degree,
and it is surjective on homology because already the second summand is. Hence the long exact
homology sequence of `0 ⟶ ker ⟶ cover M ⟶ M ⟶ 0` breaks into short exact sequences. Iterating
on the kernels gives `Q`, whose differentials are the composites
`cover (ker) ⟶ ker ⟶ cover M`. The columns and the homology of the rows are then spliced from
short exact sequences, which makes them resolutions
(`CategoryTheory.ProjectiveResolution.splice`).

## Lifting chain maps

A chain map `g : K ⟶ K'` lifts to a morphism of Cartan–Eilenberg resolutions
`ChainComplex.cartanEilenbergResolutionMap g` lying over `g`
(`ChainComplex.cartanEilenbergResolutionMap_π`). On the covers it is built from lifts through the
projective covers: of the terms, for the disk parts
(`ChainComplex.cartanEilenbergResolution.diskMap`, a map of mapping cones), and of the cycles, for
the sphere parts
(`ChainComplex.cartanEilenbergResolution.sphereMap`). These give the lift
`ChainComplex.cartanEilenbergResolution.coverMap` to the covers and, by induction, the maps
`ChainComplex.cartanEilenbergResolution.kernelsMap` of the successive kernels. The lift depends on
these choices, so it is not functorial on the nose, and no identity or composition lemmas are
stated for it.

A morphism `ψ` of Cartan–Eilenberg resolutions induces morphisms of the resolutions of the
homology `ChainComplex.cartanEilenbergResolution.homologyResolutionMap ψ j`, functorially in `ψ`,
lying over `Hⱼ(g)` when `ψ` lies over `g`
(`ChainComplex.cartanEilenbergResolution.homologyResolutionMap_f_zero_comp_π_f_zero`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.7.
* H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press, 1956,
  Chapter XVII, §1.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ChainComplex

variable [EnoughProjectives C]

namespace cartanEilenbergResolution

open HomologicalComplex

variable (M : ChainComplex C ℕ)

/-- The complex with zero differentials whose term in degree `q` is a projective object mapping
onto `M.X (q + 1)`. -/
abbrev diskBase : ChainComplex C ℕ :=
  HomologicalComplex.graded _ fun q => Projective.over (M.X (q + 1))

/-- The chain map from `diskBase M` to `M` given in degree `q` by
`Projective.over (M.X (q + 1)) ⟶ M.X (q + 1) ⟶ M.X q`. -/
def diskBaseHom : diskBase M ⟶ M where
  f q := Projective.π _ ≫ M.d (q + 1) q

/-- The null-homotopy of `diskBaseHom M` which is `Projective.π (M.X (q + 1))` in degree `q`. -/
def diskBaseHomotopy : Homotopy (𝟙 _ ≫ diskBaseHom M) 0 where
  hom i j := if h : i + 1 = j then Projective.π _ ≫ eqToHom (congrArg M.X h) else 0
  zero _ _ hij := dite_eq_right hij
  comm j := by
    rw [prevD_eq _ (ComplexShape.down_mk (j + 1) j rfl)]
    simp [dNext, diskBaseHom]

/-- The disk part of the cover of `M`: the mapping cone of the identity of `diskBase M`. -/
abbrev disk : ChainComplex C ℕ := homotopyCofiber (𝟙 (diskBase M))

/-- The map from the disk part of the cover to `M`. -/
def diskπ : disk M ⟶ M := homotopyCofiber.desc _ (diskBaseHom M) (diskBaseHomotopy M)

/-- The sphere part of the cover of `M`: projective objects mapping onto the cycles of `M`, with
zero differentials. -/
abbrev sphere : ChainComplex C ℕ :=
  HomologicalComplex.graded _ fun q => Projective.over (M.cycles q)

/-- The map from the sphere part of the cover to `M`, through the cycles. -/
abbrev sphereπ : sphere M ⟶ M := M.fromGraded fun q => Projective.π (M.cycles q)

/-- The cover of `M`: the direct sum of a contractible complex of projectives and a complex of
projectives with zero differentials. -/
abbrev cover : ChainComplex C ℕ := disk M ⊞ sphere M

/-- The map from the cover onto `M`. -/
def coverπ : cover M ⟶ M := biprod.desc (diskπ M) (sphereπ M)

instance (q : ℕ) : Projective ((disk M).X q) := by
  by_cases h : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
  · exact Projective.of_iso (homotopyCofiber.XIsoBiprod (𝟙 (diskBase M)) q _ h).symm inferInstance
  · exact Projective.of_iso (homotopyCofiber.XIso (𝟙 (diskBase M)) q h).symm inferInstance

instance (q : ℕ) : Projective ((cover M).X q) :=
  Projective.of_iso (biprodXIso _ _ q).symm inferInstance

instance (q : ℕ) : Projective ((cover M).homology q) := by
  have hD : IsZero ((disk M).homology q) :=
    ((homotopyCofiber.acyclic_id _ fun j => ⟨j + 1, rfl⟩) q).isZero_homology
  have : Projective ((sphere M).homology q) :=
    projective_homology_of_d_eq_zero _ _ rfl rfl
  have : Projective ((disk M).homology q) := Projective.of_iso hD.isoZero.symm inferInstance
  have := preservesBinaryBiproduct_of_preservesBiproduct
    (homologyFunctor C (ComplexShape.down ℕ) q) (disk M) (sphere M)
  have : Projective ((homologyFunctor C (ComplexShape.down ℕ) q).obj (disk M) ⊞
      (homologyFunctor C (ComplexShape.down ℕ) q).obj (sphere M)) :=
    inferInstanceAs (Projective ((disk M).homology q ⊞ (sphere M).homology q))
  exact Projective.of_iso
    ((homologyFunctor C (ComplexShape.down ℕ) q).mapBiprod (disk M) (sphere M)).symm this

instance (q : ℕ) : Epi ((coverπ M).f q) := by
  cases q with
  | zero =>
    have h : (biprod.inr : sphere M ⟶ cover M).f 0 ≫ (coverπ M).f 0 =
        Projective.π _ ≫ M.iCycles 0 := by
      simp [coverπ, ← comp_f]
    have : IsIso (M.iCycles 0) := M.isIso_iCycles 0 0 (by simp) (by simp)
    exact epi_of_epi_fac h
  | succ q =>
    have h : (homotopyCofiber.inlX (𝟙 (diskBase M)) q (q + 1) (ComplexShape.down_mk _ _ rfl) ≫
        (biprod.inl : disk M ⟶ cover M).f (q + 1)) ≫ (coverπ M).f (q + 1) =
        Projective.π (M.X (q + 1)) := by
      rw [Category.assoc, ← comp_f, coverπ, biprod.inl_desc, diskπ,
        homotopyCofiber.inlX_desc_f]
      simp [diskBaseHomotopy]
    exact epi_of_epi_fac h

instance (q : ℕ) : Epi (homologyMap (coverπ M) q) := by
  have h : homologyMap (biprod.inr : sphere M ⟶ cover M) q ≫ homologyMap (coverπ M) q =
      homologyMap (sphereπ M) q := by
    rw [← homologyMap_comp, coverπ, biprod.inr_desc]
  have := epi_homologyMap_fromGraded (K := M) (fun q => Projective.π (M.cycles q)) q
  exact epi_of_epi_fac h

/-- The short exact sequence `0 ⟶ ker ⟶ cover M ⟶ M ⟶ 0`. -/
lemma shortExact_cover :
    (ShortComplex.mk (kernel.ι (coverπ M)) (coverπ M) (kernel.condition _)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  epi_g := epi_of_epi_f _ inferInstance

/-- The homology sequence of `0 ⟶ ker ⟶ cover M ⟶ M ⟶ 0` is short exact in every degree. -/
lemma shortExact_cover_homology (q : ℕ) :
    (ShortComplex.mk (homologyMap (kernel.ι (coverπ M)) q) (homologyMap (coverπ M) q)
      (by rw [← homologyMap_comp, kernel.condition, homologyMap_zero])).ShortExact where
  exact := (shortExact_cover M).homology_exact₂ q
  mono_f := ((shortExact_cover M).homology_exact₁ (q + 1) q rfl).mono_g
    (((shortExact_cover M).homology_exact₃ (q + 1) q rfl).epi_f_iff.1
      (inferInstanceAs (Epi (homologyMap (coverπ M) (q + 1)))))
  epi_g := inferInstanceAs (Epi (homologyMap (coverπ M) q))

/-- The successive kernels: `kernels K 0 = K`, and `kernels K (p + 1)` is the kernel of the cover
of `kernels K p`. -/
-- The body is exposed so that `kernels K 0` is `K`, the object resolved by the column and
-- homology resolutions.
@[expose]
def kernels (K : ChainComplex C ℕ) : ℕ → ChainComplex C ℕ
  | 0 => K
  | p + 1 => kernel (coverπ (kernels K p))

/-- The inclusion of the `(p + 1)`-st successive kernel into the cover of the `p`-th one. -/
def kernelsι (K : ChainComplex C ℕ) (p : ℕ) : kernels K (p + 1) ⟶ cover (kernels K p) :=
  kernel.ι (coverπ (kernels K p))

@[reassoc (attr := simp)]
lemma kernelsι_coverπ (K : ChainComplex C ℕ) (p : ℕ) :
    kernelsι K p ≫ coverπ (kernels K p) = 0 :=
  kernel.condition _

end cartanEilenbergResolution

open cartanEilenbergResolution HomologicalComplex

variable (K : ChainComplex C ℕ)

/-- **The Cartan–Eilenberg resolution of a chain complex.** Its row `p` is the cover of the
`p`-th successive kernel, and its differential `p + 1 ⟶ p` maps the cover of the `(p + 1)`-st
kernel onto that kernel, which sits inside the cover of the `p`-th kernel.

Weibel's Definition 5.7.1 also asks that the boundaries and the cycles of the rows form projective
resolutions of the boundaries and cycles of `K`. Those conditions hold for this construction too,
since each short exact sequence `0 ⟶ ker ⟶ cover M ⟶ M ⟶ 0` is exact on boundaries and cycles
and the cover has projective boundaries and cycles, but they are not proved in this file. -/
-- The body is exposed so that its rows are the covers of the kernels, which the column and
-- homology resolutions see.
@[expose]
def cartanEilenbergResolution : ChainComplex (ChainComplex C ℕ) ℕ :=
  ChainComplex.of (fun p => cover (kernels K p))
    (fun p => coverπ (kernels K (p + 1)) ≫ kernelsι K p)
    (fun p => by simp)

namespace cartanEilenbergResolution

/-- The row `p` of the Cartan–Eilenberg resolution is the cover of the `p`-th kernel. -/
lemma X_eq (p : ℕ) : (cartanEilenbergResolution K).X p = cover (kernels K p) := (rfl)

/-- The map from the row `p` of the Cartan–Eilenberg resolution onto the `p`-th kernel. -/
def rowπ (p : ℕ) : (cartanEilenbergResolution K).X p ⟶ kernels K p := coverπ (kernels K p)

/-- The inclusion of the `(p + 1)`-st kernel into the row `p` of the Cartan–Eilenberg
resolution. -/
def rowι (p : ℕ) : kernels K (p + 1) ⟶ (cartanEilenbergResolution K).X p := kernelsι K p

@[reassoc (attr := simp)]
lemma rowι_rowπ (p : ℕ) : rowι K p ≫ rowπ K p = 0 := kernelsι_coverπ K p

/-- The short exact sequence `0 ⟶ kernels K (p + 1) ⟶ Q.X p ⟶ kernels K p ⟶ 0`. -/
lemma shortExact_row (p : ℕ) : (ShortComplex.mk _ _ (rowι_rowπ K p)).ShortExact :=
  shortExact_cover (kernels K p)

/-- The short exact sequences `0 ⟶ kernels K (p + 1) ⟶ Q.X p ⟶ kernels K p ⟶ 0` stay short
exact on homology. -/
lemma shortExact_row_homology (p q : ℕ) :
    (ShortComplex.mk (homologyMap (rowι K p) q) (homologyMap (rowπ K p) q)
      (by rw [← homologyMap_comp, rowι_rowπ, homologyMap_zero])).ShortExact :=
  shortExact_cover_homology (kernels K p) q

/-- The differential of the Cartan–Eilenberg resolution maps the row `p + 1` onto the `(p + 1)`-st
kernel, which sits inside the row `p`. -/
@[simp]
lemma d_succ (p : ℕ) : (cartanEilenbergResolution K).d (p + 1) p = rowπ K (p + 1) ≫ rowι K p := by
  simp [cartanEilenbergResolution, rowπ, rowι]

end cartanEilenbergResolution

/-- The augmentation of the Cartan–Eilenberg resolution. -/
def cartanEilenbergResolutionπ : (cartanEilenbergResolution K).X 0 ⟶ K := rowπ K 0

namespace cartanEilenbergResolution

/-- The augmentation of the Cartan–Eilenberg resolution is the map from the row `0` onto
`kernels K 0 = K`. -/
lemma cartanEilenbergResolutionπ_eq : cartanEilenbergResolutionπ K = rowπ K 0 := (rfl)

/-- The augmentation vanishes on the first kernel. -/
@[reassoc (attr := simp)]
lemma rowι_π : rowι K 0 ≫ cartanEilenbergResolutionπ K = 0 := rowι_rowπ K 0

/-- The augmentation vanishes on the image of the differential. Not a simp lemma: `d_succ` and
`rowι_π` prove it. -/
@[reassoc]
lemma d_comp_π : (cartanEilenbergResolution K).d 1 0 ≫ cartanEilenbergResolutionπ K = 0 := by
  rw [d_succ K 0, Category.assoc, rowι_π, comp_zero]

instance (p q : ℕ) : Projective (((cartanEilenbergResolution K).X p).X q) :=
  inferInstanceAs (Projective ((cover (kernels K p)).X q))

instance (p q : ℕ) : Projective (((cartanEilenbergResolution K).X p).homology q) :=
  inferInstanceAs (Projective ((cover (kernels K p)).homology q))

instance (p q : ℕ) : Projective ((((HomologicalComplex.eval C _ q).mapHomologicalComplex _).obj
    (cartanEilenbergResolution K)).X p) :=
  inferInstanceAs (Projective ((cover (kernels K p)).X q))

instance (p q : ℕ) : Projective
    ((((HomologicalComplex.homologyFunctor C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K)).X p) :=
  inferInstanceAs (Projective ((cover (kernels K p)).homology q))

/-- The column of the Cartan–Eilenberg resolution in degree `q` is a projective resolution of
`K.X q`. -/
-- The body is exposed so that the complex of the resolution is the column itself.
@[expose]
def columnResolution (q : ℕ) : ProjectiveResolution (K.X q) :=
  ProjectiveResolution.splice
    (K := ((HomologicalComplex.eval C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K))
    (A := fun p => (kernels K p).X q)
    (fun p => (rowι K p).f q) (fun p => (rowπ K p).f q)
    (fun p => (comp_f (rowι K p) (rowπ K p) q).symm.trans (by rw [rowι_rowπ, zero_f]))
    (fun p => (shortExact_iff_degreewise_shortExact _).1 (shortExact_row K p) q)
    (fun p => (congrArg (fun f => f.f q) (d_succ K p)).trans (comp_f _ _ q))

@[simp]
lemma columnResolution_complex (q : ℕ) : (columnResolution K q).complex =
    ((HomologicalComplex.eval C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K) := (rfl)

@[simp]
lemma columnResolution_π_f_zero (q : ℕ) :
    (columnResolution K q).π.f 0 = (cartanEilenbergResolutionπ K).f q :=
  ProjectiveResolution.splice_π_f_zero _ _ _ _ _

/-- The homology in degree `q` of the rows of the Cartan–Eilenberg resolution is a projective
resolution of `K.homology q`. -/
-- The body is exposed so that the complex of the resolution is the row homology itself.
@[expose]
def homologyResolution (q : ℕ) : ProjectiveResolution (K.homology q) :=
  ProjectiveResolution.splice
    (K := ((HomologicalComplex.homologyFunctor C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K))
    (A := fun p => (kernels K p).homology q)
    (fun p => homologyMap (rowι K p) q)
    (fun p => homologyMap (rowπ K p) q)
    (fun p => (homologyMap_comp _ _ q).symm.trans (by rw [rowι_rowπ, homologyMap_zero]))
    (fun p => shortExact_row_homology K p q)
    (fun p => (congrArg (fun f => homologyMap f q) (d_succ K p)).trans (homologyMap_comp _ _ q))

@[simp]
lemma homologyResolution_complex (q : ℕ) : (homologyResolution K q).complex =
    ((HomologicalComplex.homologyFunctor C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K) := (rfl)

@[simp]
lemma homologyResolution_π_f_zero (q : ℕ) :
    (homologyResolution K q).π.f 0 = homologyMap (cartanEilenbergResolutionπ K) q :=
  ProjectiveResolution.splice_π_f_zero _ _ _ _ _

/-! ### Lifting chain maps to Cartan–Eilenberg resolutions -/

section Map

variable {M M' : ChainComplex C ℕ} (h : M ⟶ M')

/-- A lift of a chain map `h : M ⟶ M'` to the complexes `diskBase M ⟶ diskBase M'`, through the
projective covers of the terms of `M` and `M'`. -/
def diskBaseMap : diskBase M ⟶ diskBase M' :=
  HomologicalComplex.gradedMap _ fun q =>
    Projective.factorThru (Projective.π (M.X (q + 1)) ≫ h.f (q + 1)) (Projective.π (M'.X (q + 1)))

@[reassoc (attr := simp)]
lemma diskBaseMap_f_π (q : ℕ) :
    (diskBaseMap h).f q ≫ Projective.π (M'.X (q + 1)) =
      Projective.π (M.X (q + 1)) ≫ h.f (q + 1) := by
  rw [diskBaseMap, HomologicalComplex.gradedMap_f]
  exact Projective.factorThru_comp _ _

/-- The chain map `diskBaseHom M` is `Projective.π (M.X (q + 1)) ≫ M.d (q + 1) q` in degree `q`. -/
lemma diskBaseHom_f (q : ℕ) : (diskBaseHom M).f q = Projective.π _ ≫ M.d (q + 1) q := (rfl)

/-- The lift of `h` to the complexes `diskBase` is compatible with the maps `diskBaseHom` to `M`
and `M'`. -/
@[reassoc]
lemma diskBaseMap_diskBaseHom : diskBaseMap h ≫ diskBaseHom M' = diskBaseHom M ≫ h := by
  ext q
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, diskBaseHom_f, diskBaseHom_f,
    diskBaseMap_f_π_assoc, Category.assoc, h.comm]

/-- A lift of a chain map `h : M ⟶ M'` to the disk parts of the covers. -/
def diskMap : disk M ⟶ disk M' :=
  homotopyCofiber.mapArrowHom _ _ (fun j => ⟨j + 1, rfl⟩)
    (Arrow.homMk (diskBaseMap h) (diskBaseMap h)
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The lift of `h` to the disk parts of the covers lies over `h`. -/
@[reassoc (attr := simp)]
lemma diskMap_diskπ : diskMap h ≫ diskπ M' = diskπ M ≫ h := by
  ext i
  rcases i with _ | i
  · refine homotopyCofiber.ext_from_X' (𝟙 (diskBase M)) 0 (by simp) ?_
    simpa [diskMap, diskπ] using HomologicalComplex.congr_hom (diskBaseMap_diskBaseHom h) 0
  · refine homotopyCofiber.ext_from_X (𝟙 (diskBase M)) i (i + 1) rfl ?_ ?_
    · simp [diskMap, diskπ, diskBaseHomotopy]
    · simpa [diskMap, diskπ] using
        HomologicalComplex.congr_hom (diskBaseMap_diskBaseHom h) (i + 1)

/-- A lift of a chain map `h : M ⟶ M'` to the sphere parts of the covers, through the projective
covers of the cycles. -/
def sphereMap : sphere M ⟶ sphere M' :=
  HomologicalComplex.gradedMap _ fun q =>
    Projective.factorThru (Projective.π (M.cycles q) ≫ HomologicalComplex.cyclesMap h q)
      (Projective.π (M'.cycles q))

/-- The lift of `h` to the sphere parts of the covers lifts the map induced on cycles. -/
@[reassoc (attr := simp)]
lemma sphereMap_f_π (q : ℕ) :
    (sphereMap h).f q ≫ Projective.π (M'.cycles q) =
      Projective.π (M.cycles q) ≫ HomologicalComplex.cyclesMap h q := by
  rw [sphereMap, HomologicalComplex.gradedMap_f]
  exact Projective.factorThru_comp _ _

/-- The lift of `h` to the sphere parts of the covers lies over `h`. -/
@[reassoc (attr := simp)]
lemma sphereMap_sphereπ : sphereMap h ≫ sphereπ M' = sphereπ M ≫ h := by
  rw [sphereMap]
  exact HomologicalComplex.gradedMap_fromGraded _ _ _ h fun q => Projective.factorThru_comp _ _

/-- A lift of a chain map `h : M ⟶ M'` to the covers. It depends on the choice of the lifts
through the projective covers. -/
def coverMap : cover M ⟶ cover M' := biprod.map (diskMap h) (sphereMap h)

/-- The lift of `h` to the covers lies over `h`. -/
@[reassoc (attr := simp)]
lemma coverMap_coverπ : coverMap h ≫ coverπ M' = coverπ M ≫ h := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [coverMap, coverπ]

variable {K K' : ChainComplex C ℕ} (g : K ⟶ K')

/-- The lifts of a chain map `g : K ⟶ K'` to the successive kernels: `g` on `kernels K 0 = K`,
and on `kernels K (p + 1)` the map of kernels induced by the lift of the map on `kernels K p` to
the covers. -/
def kernelsMap : (p : ℕ) → kernels K p ⟶ kernels K' p
  | 0 => g
  | p + 1 => kernel.map _ _ (coverMap (kernelsMap p)) (kernelsMap p) (coverMap_coverπ _).symm

@[simp]
lemma kernelsMap_zero : kernelsMap g 0 = g := (rfl)

/-- The lifts to the successive kernels commute with their inclusions into the covers. -/
@[reassoc (attr := simp)]
lemma kernelsMap_succ_kernelsι (p : ℕ) :
    kernelsMap g (p + 1) ≫ kernelsι K' p = kernelsι K p ≫ coverMap (kernelsMap g p) :=
  kernel.lift_ι _ _ _

end Map

end cartanEilenbergResolution

open cartanEilenbergResolution in
/-- **A lift of a chain map to the Cartan–Eilenberg resolutions.** A chain map `g : K ⟶ K'` lifts
to a morphism of the Cartan–Eilenberg resolutions, which on the row `p` is the lift
`cartanEilenbergResolution.coverMap` to the covers of the map of the successive kernels. It lies
over `g` (`ChainComplex.cartanEilenbergResolutionMap_π`). The lift depends on the choice of lifts
through projective covers, so it is not functorial on the nose. -/
def cartanEilenbergResolutionMap {K K' : ChainComplex C ℕ} (g : K ⟶ K') :
    cartanEilenbergResolution K ⟶ cartanEilenbergResolution K' :=
  ChainComplex.ofHom (fun p => coverMap (kernelsMap g p)) fun p => by
    -- the differential is the projection of the row `p + 1` onto the `(p + 1)`-st kernel followed
    -- by its inclusion into the row `p`
    rw [d_succ, d_succ]
    -- `rowπ` and `rowι` are `coverπ` and `kernelsι` by definition, and the rows of the
    -- resolutions are the covers of the kernels; the lemmas relating them to the lift are stated
    -- below in terms of `cartanEilenbergResolutionMap` itself, so they are not available here
    change coverMap _ ≫ coverπ _ ≫ kernelsι K' p = (coverπ _ ≫ kernelsι K p) ≫ coverMap _
    rw [coverMap_coverπ_assoc, kernelsMap_succ_kernelsι, Category.assoc]

namespace cartanEilenbergResolution

variable {K K' : ChainComplex C ℕ} (g : K ⟶ K')

/-- The lift of `g` to the Cartan–Eilenberg resolutions is, on the row `p`, the lift to the covers
of the map of the successive kernels. -/
lemma cartanEilenbergResolutionMap_f (p : ℕ) :
    (cartanEilenbergResolutionMap g).f p = coverMap (kernelsMap g p) := (rfl)

/-- The lift of `g` to the Cartan–Eilenberg resolutions commutes with the projections of the rows
onto the successive kernels. -/
@[reassoc (attr := simp)]
lemma cartanEilenbergResolutionMap_f_rowπ (p : ℕ) :
    (cartanEilenbergResolutionMap g).f p ≫ rowπ K' p = rowπ K p ≫ kernelsMap g p :=
  -- the row `p` is the cover of the `p`-th kernel by definition
  coverMap_coverπ (kernelsMap g p)

/-- The lift of `g` to the Cartan–Eilenberg resolutions commutes with the inclusions of the
successive kernels into the rows. -/
@[reassoc (attr := simp)]
lemma kernelsMap_succ_rowι (p : ℕ) :
    kernelsMap g (p + 1) ≫ rowι K' p = rowι K p ≫ (cartanEilenbergResolutionMap g).f p :=
  -- `rowι` is `kernelsι` and the row `p` is the cover of the `p`-th kernel by definition
  kernelsMap_succ_kernelsι g p

end cartanEilenbergResolution

open cartanEilenbergResolution in
/-- The lift of `g` to the Cartan–Eilenberg resolutions lies over `g`. -/
@[reassoc (attr := simp)]
lemma cartanEilenbergResolutionMap_π {K K' : ChainComplex C ℕ} (g : K ⟶ K') :
    (cartanEilenbergResolutionMap g).f 0 ≫ cartanEilenbergResolutionπ K' =
      cartanEilenbergResolutionπ K ≫ g :=
  -- the augmentation is the projection onto `kernels K 0 = K`
  cartanEilenbergResolutionMap_f_rowπ g 0

namespace cartanEilenbergResolution

variable {K K' K'' : ChainComplex C ℕ}

/-- The morphism `homologyResolution K j ⟶ homologyResolution K' j` of the complexes of the
projective resolutions of `Hⱼ(K)` and `Hⱼ(K')` induced by a morphism `ψ` of Cartan–Eilenberg
resolutions: in degree `p` it is `Hⱼ(ψ.f p)`. When `ψ` lies over `g : K ⟶ K'`, it lies over
`Hⱼ(g)` (`ChainComplex.cartanEilenbergResolution.homologyResolutionMap_f_zero_comp_π_f_zero`). -/
def homologyResolutionMap (ψ : cartanEilenbergResolution K ⟶ cartanEilenbergResolution K')
    (j : ℕ) : (homologyResolution K j).complex ⟶ (homologyResolution K' j).complex :=
  ((HomologicalComplex.homologyFunctor C _ j).mapHomologicalComplex _).map ψ

/-- In degree `p`, the morphism `homologyResolutionMap ψ j` is `Hⱼ(ψ.f p)`. -/
@[simp]
lemma homologyResolutionMap_f (ψ : cartanEilenbergResolution K ⟶ cartanEilenbergResolution K')
    (j p : ℕ) : (homologyResolutionMap ψ j).f p = homologyMap (ψ.f p) j :=
  (rfl)

/-- The identity of a Cartan–Eilenberg resolution induces the identity of the resolutions of the
homology. -/
@[simp]
lemma homologyResolutionMap_id (j : ℕ) :
    homologyResolutionMap (𝟙 (cartanEilenbergResolution K)) j = 𝟙 _ := by
  rw [homologyResolutionMap, CategoryTheory.Functor.map_id]
  -- the complex of `homologyResolution K j` is the row homology by definition
  rfl

/-- `homologyResolutionMap` is compatible with composition. -/
@[simp]
lemma homologyResolutionMap_comp
    (ψ : cartanEilenbergResolution K ⟶ cartanEilenbergResolution K')
    (ψ' : cartanEilenbergResolution K' ⟶ cartanEilenbergResolution K'') (j : ℕ) :
    homologyResolutionMap (ψ ≫ ψ') j = homologyResolutionMap ψ j ≫ homologyResolutionMap ψ' j := by
  rw [homologyResolutionMap, CategoryTheory.Functor.map_comp]
  -- the complexes of `homologyResolution` are the row homology by definition
  rfl

/-- If `ψ` lies over `g`, then `homologyResolutionMap ψ j` lies over `Hⱼ(g)`: it is a morphism of
the projective resolutions `homologyResolution K j` and `homologyResolution K' j` over `Hⱼ(g)`,
as in `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`. -/
@[reassoc]
lemma homologyResolutionMap_f_zero_comp_π_f_zero
    (ψ : cartanEilenbergResolution K ⟶ cartanEilenbergResolution K') (g : K ⟶ K')
    (hψ : ψ.f 0 ≫ cartanEilenbergResolutionπ K' = cartanEilenbergResolutionπ K ≫ g) (j : ℕ) :
    (homologyResolutionMap ψ j).f 0 ≫ (homologyResolution K' j).π.f 0 =
      (homologyResolution K j).π.f 0 ≫ homologyMap g j := by
  rw [homologyResolutionMap_f, homologyResolution_π_f_zero, homologyResolution_π_f_zero]
  -- the terms of `homologyResolution` are the row homology only by definition, so the composites
  -- are combined as terms rather than by rewriting
  exact (homologyMap_comp _ _ j).symm.trans
    ((congrArg (homologyMap · j) hψ).trans (homologyMap_comp _ _ j))

end cartanEilenbergResolution

end ChainComplex
