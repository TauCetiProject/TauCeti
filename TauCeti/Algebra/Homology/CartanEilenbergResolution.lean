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
(`CategoryTheory.ProjectiveResolution.ofShortExact`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.7.
* H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press, 1956,
  Chapter XVII, §1.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory

/-- An exact sequence `A₁ ⟶ X₂ ⟶ A₂` stays exact after precomposing its first map with an
epimorphism `X₁ ⟶ A₁` and postcomposing its second map with a monomorphism `A₂ ⟶ X₃`. -/
lemma ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono {X₁ A₁ X₂ A₂ X₃ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} (zero : f ≫ g = 0) (e : X₁ ⟶ A₁) (i : A₁ ⟶ X₂) (g' : X₂ ⟶ A₂) (m : A₂ ⟶ X₃)
    [Epi e] [Mono m] (hf : f = e ≫ i) (hg : g = g' ≫ m) (w : i ≫ g' = 0)
    (h : (ShortComplex.mk i g' w).Exact) : (ShortComplex.mk f g zero).Exact := by
  subst hf hg
  have h₁ : (ShortComplex.mk (e ≫ i) g' (by simp [w])).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (e ≫ i) g' (by simp [w])) (S₂ := ShortComplex.mk i g' w)
      { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 h
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (e ≫ i) g' (by simp [w]))
    (S₂ := ShortComplex.mk (e ≫ i) (g' ≫ m) zero) { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m }).1 h₁

namespace ProjectiveResolution

variable {X : ChainComplex C ℕ} [∀ p, Projective (X.X p)] {A : ℕ → C}
  (ι : ∀ p, A (p + 1) ⟶ X.X p) (ε : ∀ p, X.X p ⟶ A p) (w : ∀ p, ι p ≫ ε p = 0)
  (hS : ∀ p, (ShortComplex.mk _ _ (w p)).ShortExact) (hd : ∀ p, X.d (p + 1) p = ε (p + 1) ≫ ι p)

/-- **Splicing short exact sequences into a resolution.** Let `X` be a complex of projectives
whose differentials factor as `X.X (p + 1) ⟶ A (p + 1) ⟶ X.X p` through short exact sequences
`0 ⟶ A (p + 1) ⟶ X.X p ⟶ A p ⟶ 0`. Then `X` is a projective resolution of `A 0`, with
augmentation `X.X 0 ⟶ A 0`. -/
def ofShortExact : ProjectiveResolution (A 0) where
  complex := X
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε 0, by rw [hd, Category.assoc, w, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp; rfl)
          (by simp; rfl)]
      have : Epi (ε 1) := (hS 1).epi_g
      have : Epi (ε 0) := (hS 0).epi_g
      have hg : ((ChainComplex.toSingle₀Equiv X (A 0)).symm
          ⟨ε 0, by rw [hd, Category.assoc, w, comp_zero]⟩).f 0 =
          ε 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (A 0)).inv := by
        simp
      refine ⟨ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono _ (ε 1) (ι 0) (ε 0)
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (A 0)).inv
        (by simp [hd]) hg (w 0) (hS 0).exact, ?_⟩
      have := epi_comp (ε 0) (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (A 0)).inv
      rw [← hg] at this
      exact this
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      have : Epi (ε (n + 2)) := (hS (n + 2)).epi_g
      have : Mono (ι n) := (hS n).mono_f
      exact ShortComplex.exact_of_eq_epi_comp_of_eq_comp_mono _ (ε (n + 2)) (ι (n + 1))
        (ε (n + 1)) (ι n) (hd _) (hd _) (w (n + 1)) (hS (n + 1)).exact⟩

@[simp]
lemma ofShortExact_complex : (ofShortExact ι ε w hS hd).complex = X := rfl

@[simp]
lemma ofShortExact_π_f_zero : (ofShortExact ι ε w hS hd).π.f 0 = ε 0 := by
  simp [ofShortExact]

end ProjectiveResolution

end CategoryTheory

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
    rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl)]
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
  dsimp [disk, homotopyCofiber, homotopyCofiber.X]
  split_ifs <;> infer_instance

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
kernel onto that kernel, which sits inside the cover of the `p`-th kernel. -/
def cartanEilenbergResolution : ChainComplex (ChainComplex C ℕ) ℕ :=
  ChainComplex.of (fun p => cover (kernels K p))
    (fun p => coverπ (kernels K (p + 1)) ≫ kernelsι K p)
    (fun p => by simp)

namespace cartanEilenbergResolution

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

lemma d_succ (p : ℕ) : (cartanEilenbergResolution K).d (p + 1) p = rowπ K (p + 1) ≫ rowι K p := by
  simp [cartanEilenbergResolution, rowπ, rowι]

end cartanEilenbergResolution

/-- The augmentation of the Cartan–Eilenberg resolution. -/
def cartanEilenbergResolutionπ : (cartanEilenbergResolution K).X 0 ⟶ K := rowπ K 0

namespace cartanEilenbergResolution

@[reassoc (attr := simp)]
lemma d_comp_π : (cartanEilenbergResolution K).d 1 0 ≫ cartanEilenbergResolutionπ K = 0 := by
  rw [d_succ K 0, Category.assoc,
    show rowι K 0 ≫ cartanEilenbergResolutionπ K = 0 from rowι_rowπ K 0, comp_zero]

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
def columnResolution (q : ℕ) : ProjectiveResolution (K.X q) :=
  ProjectiveResolution.ofShortExact
    (X := ((HomologicalComplex.eval C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K))
    (A := fun p => (kernels K p).X q)
    (fun p => (rowι K p).f q) (fun p => (rowπ K p).f q)
    (fun p => (comp_f (rowι K p) (rowπ K p) q).symm.trans (by rw [rowι_rowπ, zero_f]))
    (fun p => (shortExact_iff_degreewise_shortExact _).1 (shortExact_row K p) q)
    (fun p => by rw [Functor.mapHomologicalComplex_obj_d, d_succ]; rfl)

@[simp]
lemma columnResolution_complex (q : ℕ) : (columnResolution K q).complex =
    ((HomologicalComplex.eval C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K) := rfl

@[simp]
lemma columnResolution_π_f_zero (q : ℕ) :
    (columnResolution K q).π.f 0 = (cartanEilenbergResolutionπ K).f q :=
  ProjectiveResolution.ofShortExact_π_f_zero _ _ _ _ _

/-- The homology in degree `q` of the rows of the Cartan–Eilenberg resolution is a projective
resolution of `K.homology q`. -/
def homologyResolution (q : ℕ) : ProjectiveResolution (K.homology q) :=
  ProjectiveResolution.ofShortExact
    (X := ((HomologicalComplex.homologyFunctor C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K))
    (A := fun p => (kernels K p).homology q)
    (fun p => homologyMap (rowι K p) q)
    (fun p => homologyMap (rowπ K p) q)
    (fun p => (homologyMap_comp _ _ q).symm.trans (by rw [rowι_rowπ, homologyMap_zero]))
    (fun p => shortExact_row_homology K p q)
    (fun p => by
      rw [Functor.mapHomologicalComplex_obj_d, d_succ, homologyFunctor_map, homologyMap_comp]
      rfl)

@[simp]
lemma homologyResolution_complex (q : ℕ) : (homologyResolution K q).complex =
    ((HomologicalComplex.homologyFunctor C _ q).mapHomologicalComplex _).obj
      (cartanEilenbergResolution K) := rfl

@[simp]
lemma homologyResolution_π_f_zero (q : ℕ) :
    (homologyResolution K q).π.f 0 = homologyMap (cartanEilenbergResolutionπ K) q :=
  ProjectiveResolution.ofShortExact_π_f_zero _ _ _ _ _

end cartanEilenbergResolution

end ChainComplex
