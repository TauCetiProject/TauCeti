/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
import TauCeti.Algebra.Homology.HomologicalComplex.Subobject

/-!
# The spectral sequence of the filtration of a complex by its brutal truncations

Let `K` be a cochain complex in an abelian category, read as a chain complex with `C_n = K^{-n}`.
Its brutal (stupid) truncations `σ^{≥ -p} K`, which keep the terms `C_n` with `n ≤ p` and replace
the others by `0`, form an increasing filtration `F_p` of `K`
(`CochainComplex.stupidFiltration`, `CochainComplex.monotone_stupidFiltration`): the filtration of
a chain complex by its skeleta. Its graded piece `F_p/F_{p-1}` is the single term `C_p` placed in
degree `p`, so the homological spectral sequence of the filtration
(`CochainComplex.homologicalFiltrationSpectralSequence`) is computed by hand:

* the first page is `E¹_{p,0} = C_p` (`CochainComplex.stupidFiltrationFirstPageXIso`) and vanishes
  off the row `q = 0` (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`, on every
  page);
* the first differential `d¹ : E¹_{p,0} ⟶ E¹_{p-1,0}` is the boundary `∂ : C_p ⟶ C_{p-1}`
  (`CochainComplex.stupidFiltrationSpectralSequence_first_page_d`), the connecting map of
  `F_{p-1}/F_{p-2} ⟶ F_p/F_{p-2} ⟶ F_p/F_{p-1}`;
* hence the second page is the homology, `E²_{p,0} = H_p(C)`
  (`CochainComplex.stupidFiltrationSecondPageXIso`), and the spectral sequence degenerates there:
  `E^r_{p,0} = H_p(C)` for every `r ≥ 2` (`CochainComplex.stupidFiltrationPageXIso`), since the
  later differentials leave the row `q = 0`.

These are the values that the classical indexing of the spectral sequence of a filtered complex
must produce on the skeletal filtration, the filtration of the cellular and Morse chain complexes
by the dimension of the cells. A reindexing error in the bidegree `(1 - 2p - q, p - 1)` of
`CochainComplex.homologicalFiltrationSpectralSequence` would move `C_p` off the row `q = 0` or
change the bidegree of `d¹`.

The connecting map is computed with `ShortComplex.ShortExact.δ_eq`: an element `x` of `C_p` lifts
to `F_p/F_{p-2}`, its differential there is the image of `∂x ∈ C_{p-1} = F_{p-1}/F_{p-2}`.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Section 5.4.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, Section 2.2.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- The **filtration of a cochain complex by its brutal truncations**: `F_p` is the subcomplex
`σ^{≥ -p} K`, made of the terms of `K` in the degrees `≥ -p`. Read as a chain complex with
`C_n = K^{-n}`, it is the subcomplex of the terms `C_n` with `n ≤ p`, the skeletal filtration. -/
noncomputable def stupidFiltration (p : ℤ) : Subobject K :=
  Subobject.mk (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (-p)))

variable {K} in
/-- In the degrees `≥ -p`, the subcomplex `F_p` of the brutal filtration is all of `K`. -/
lemma isIso_stupidFiltration_arrow_f {p i : ℤ} (hi : -p ≤ i) :
    IsIso ((K.stupidFiltration p).arrow.f i) := by
  rw [stupidFiltration, ← Subobject.underlyingIso_hom_comp_eq_mk, HomologicalComplex.comp_f]
  have := K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE (-p)) (i := (i + p).toNat)
    (i' := i) (by simp; omega)
  have : IsIso ((Subobject.underlyingIso
      (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (-p)))).hom.f i) :=
    (HomologicalComplex.eval C _ i).map_isIso _
  infer_instance

variable {K} in
/-- In the degrees `< -p`, the subcomplex `F_p` of the brutal filtration vanishes. -/
lemma isZero_stupidFiltration_X {p i : ℤ} (hi : i < -p) :
    IsZero ((K.stupidFiltration p : CochainComplex C ℤ).X i) := by
  rw [stupidFiltration]
  exact (K.isZero_stupidTrunc_embeddingUpIntGE_X (-p) hi).of_iso
    ((HomologicalComplex.eval C _ i).mapIso (Subobject.underlyingIso _))

/-- The brutal truncations form an increasing filtration: `F_p ⊆ F_{p+1}`. -/
lemma monotone_stupidFiltration : Monotone K.stupidFiltration :=
  monotone_int_of_le_succ fun p ↦ Subobject.le_of_factors
    ((Subobject.factors_iff_forall_exists_comp_arrow_f_eq _ _).2 fun i ↦ by
      by_cases hi : i < -p
      · exact ⟨0, (isZero_stupidFiltration_X hi).eq_of_src _ _⟩
      · have := isIso_stupidFiltration_arrow_f (K := K) (p := p + 1) (i := i) (by omega)
        exact ⟨(K.stupidFiltration p).arrow.f i ≫ inv ((K.stupidFiltration (p + 1)).arrow.f i),
          by simp⟩)

/-- The graded piece `F_p/F_{p-1}` of the filtration by brutal truncations. -/
private noncomputable abbrev stupidGr (p : ℤ) : CochainComplex C ℤ :=
  cokernel (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
    (K.monotone_stupidFiltration (by omega)))

variable {K} in
/-- The graded piece `F_p/F_{p-1}` vanishes outside the degree `-p`. -/
private lemma isZero_stupidGr_X {p i : ℤ} (hi : i ≠ -p) : IsZero ((K.stupidGr p).X i) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact IsZero.of_epi ((cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1))
      (K.stupidFiltration p) (K.monotone_stupidFiltration (by omega)))).f i)
      (isZero_stupidFiltration_X hi)
  · have h₁ := isIso_stupidFiltration_arrow_f (K := K) (p := p) (i := i) (by omega)
    have h₂ := isIso_stupidFiltration_arrow_f (K := K) (p := p - 1) (i := i) (by omega)
    have : IsIso ((Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
        (K.monotone_stupidFiltration (by omega))).f i) := by
      have w := congrArg (fun φ ↦ φ.f i) (Subobject.ofLE_arrow
        (K.monotone_stupidFiltration (show p - 1 ≤ p by omega)))
      simp only [HomologicalComplex.comp_f] at w
      exact IsIso.of_isIso_fac_right w
    -- The projection onto the cokernel vanishes in the degree `i`, where it is an epimorphism.
    refine IsZero.of_epi_eq_zero ((cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1))
      (K.stupidFiltration p) (K.monotone_stupidFiltration (by omega)))).f i) ?_
    rw [← cancel_epi ((Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
      (K.monotone_stupidFiltration (by omega))).f i), ← HomologicalComplex.comp_f,
      cokernel.condition, HomologicalComplex.zero_f, comp_zero]

variable {K} in
/-- In the degree `-p`, the projection of `F_p` onto the graded piece `F_p/F_{p-1}` is an
isomorphism, since `F_{p-1}` vanishes there. -/
private lemma isIso_stupidGr_π_f {p n : ℤ} (hn : n = -p) :
    IsIso ((cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
      (K.monotone_stupidFiltration (by omega)))).f n) := by
  have hS := (TauCeti.cokernelSequence_shortExact (Subobject.ofLE (K.stupidFiltration (p - 1))
    (K.stupidFiltration p) (K.monotone_stupidFiltration (by omega)))).map_of_exact
      (HomologicalComplex.eval C _ n)
  have : Mono ((cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
      (K.monotone_stupidFiltration (by omega)))).f n) :=
    hS.exact.mono_g ((isZero_stupidFiltration_X (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

variable {K} in
/-- In the degrees `≥ -p`, the term of `F_p` is the term of `K`. -/
private noncomputable def stupidFiltrationXIso {p n : ℤ} (hn : -p ≤ n) :
    K.X n ≅ (K.stupidFiltration p : CochainComplex C ℤ).X n :=
  haveI := isIso_stupidFiltration_arrow_f (K := K) hn
  (asIso ((K.stupidFiltration p).arrow.f n)).symm

variable {K} in
/-- The identification of the terms of `F_p` with those of `K` inverts the inclusion. -/
@[reassoc (attr := simp)]
private lemma stupidFiltrationXIso_hom_arrow_f {p n : ℤ} (hn : -p ≤ n) :
    (stupidFiltrationXIso hn).hom ≫ (K.stupidFiltration p).arrow.f n = 𝟙 _ := by
  simp [stupidFiltrationXIso]

variable {K} in
/-- The identifications of the terms of `F_{p-1}` and of `F_p` with those of `K` are compatible
with the inclusion `F_{p-1} ⊆ F_p`. -/
@[reassoc]
private lemma stupidFiltrationXIso_hom_ofLE_f {p n : ℤ} (hn : -(p - 1) ≤ n) :
    (stupidFiltrationXIso hn).hom ≫ (Subobject.ofLE (K.stupidFiltration (p - 1))
      (K.stupidFiltration p) (K.monotone_stupidFiltration (by omega))).f n =
        (stupidFiltrationXIso (K := K) (p := p) (by omega)).hom := by
  have := isIso_stupidFiltration_arrow_f (K := K) (p := p) (i := n) (by omega)
  rw [← cancel_mono ((K.stupidFiltration p).arrow.f n), Category.assoc,
    ← HomologicalComplex.comp_f, Subobject.ofLE_arrow, stupidFiltrationXIso_hom_arrow_f,
    stupidFiltrationXIso_hom_arrow_f]

variable {K} in
/-- The identifications of the terms of `F_p` with those of `K` are compatible with the
differentials. -/
@[reassoc]
private lemma stupidFiltrationXIso_hom_d {p n m : ℤ} (hn : -p ≤ n) (hm : -p ≤ m) :
    (stupidFiltrationXIso hn).hom ≫ (K.stupidFiltration p : CochainComplex C ℤ).d n m =
      K.d n m ≫ (stupidFiltrationXIso hm).hom := by
  have := isIso_stupidFiltration_arrow_f (K := K) hm
  rw [← cancel_mono ((K.stupidFiltration p).arrow.f m), Category.assoc, Category.assoc,
    ← HomologicalComplex.Hom.comm, stupidFiltrationXIso_hom_arrow_f_assoc,
    stupidFiltrationXIso_hom_arrow_f, Category.comp_id]

variable {K} in
/-- The term of `K` in the degree `-p` is the term of the graded piece `F_p/F_{p-1}` there. -/
private noncomputable def stupidGrXIso {p n : ℤ} (hn : n = -p) : K.X n ≅ (K.stupidGr p).X n :=
  haveI := isIso_stupidGr_π_f (K := K) hn
  stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega) ≪≫
    asIso ((cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
      (K.monotone_stupidFiltration (by omega)))).f n)

variable {K} in
/-- The identification of `K^{-p}` with the graded piece `F_p/F_{p-1}` there is the inverse of the
inclusion followed by the projection. -/
private lemma stupidGrXIso_hom {p n : ℤ} (hn : n = -p) :
    (stupidGrXIso hn).hom = (stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega)).hom ≫
      (cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
        (K.monotone_stupidFiltration (by omega)))).f n :=
  (rfl)

variable {K} in
/-- The differentials of the graded piece `F_p/F_{p-1}` leaving the degree `-p` vanish. -/
private lemma stupidGr_d_eq_zero {p n m : ℤ} (hn : n = -p) (hm : n ≠ m) :
    (K.stupidGr p).d n m = 0 :=
  (isZero_stupidGr_X (by omega)).eq_of_tgt _ _

variable {K} in
/-- The differentials of the graded piece `F_p/F_{p-1}` entering the degree `-p` vanish. -/
private lemma stupidGr_d_eq_zero' {p n m : ℤ} (hn : n = -p) (hm : n ≠ m) :
    (K.stupidGr p).d m n = 0 :=
  (isZero_stupidGr_X (by omega)).eq_of_src _ _

variable {K} in
/-- The homology of the graded piece `F_p/F_{p-1}` in the degree `-p` is the term of `K` there. -/
private noncomputable def stupidGrHomologyIso {p n : ℤ} (hn : n = -p) :
    K.X n ≅ (K.stupidGr p).homology n :=
  stupidGrXIso hn ≪≫
    ((K.stupidGr p).iCyclesIso n (n + 1) (by simp) (stupidGr_d_eq_zero hn (by omega))).symm ≪≫
    (K.stupidGr p).isoHomologyπ (n - 1) n (by simp) (stupidGr_d_eq_zero' hn (by omega))

variable {K} in
/-- The identification of `K^{-p}` with the homology of `F_p/F_{p-1}` takes an element to the
class of the corresponding cycle. -/
private lemma stupidGrHomologyIso_hom {p n : ℤ} (hn : n = -p) :
    (stupidGrHomologyIso hn).hom = (K.stupidGr p).liftCycles (stupidGrXIso hn).hom (n + 1)
      (by simp) (by rw [stupidGr_d_eq_zero (m := n + 1) hn (by omega), comp_zero]) ≫
        (K.stupidGr p).homologyπ n := by
  rw [← cancel_mono ((K.stupidGr p).isoHomologyπ (n - 1) n (by simp)
    (stupidGr_d_eq_zero' hn (by omega))).inv]
  simp [stupidGrHomologyIso, ← cancel_mono ((K.stupidGr p).iCycles n)]

variable {K} in
/-- The connecting map of the short exact sequence `F_{p-1}/F_{p-2} ⟶ F_p/F_{p-2} ⟶ F_p/F_{p-1}`
from the degree `-p` to the degree `-p + 1` is the differential of `K`, under the identifications
of the homology of the graded pieces with the terms of `K`. -/
private lemma stupidGrHomologyIso_hom_δ {p n m : ℤ} (hn : n = -p) (hm : m = n + 1) :
    (stupidGrHomologyIso (K := K) hn).hom ≫
      (TauCeti.cokernelCompSequence_shortExact
        (Subobject.ofLE (K.stupidFiltration (p - 1 - 1)) (K.stupidFiltration (p - 1))
          (K.monotone_stupidFiltration (by omega)))
        (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
          (K.monotone_stupidFiltration (by omega)))).δ n m (by simp; omega) =
      K.d n m ≫ (stupidGrHomologyIso (K := K) (p := p - 1) (n := m) (by omega)).hom := by
  subst hm
  have hS := TauCeti.cokernelCompSequence_shortExact
    (Subobject.ofLE (K.stupidFiltration (p - 1 - 1)) (K.stupidFiltration (p - 1))
      (K.monotone_stupidFiltration (by omega)))
    (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
      (K.monotone_stupidFiltration (by omega)))
  -- The class of `x ∈ K^{-p}` lifts to `F_p/F_{p-2}`, and its differential `dx` lies in
  -- `F_{p-1}/F_{p-2}`.
  rw [stupidGrHomologyIso_hom, stupidGrHomologyIso_hom, Category.assoc,
    hS.δ_eq n (n + 1) (by simp) (stupidGrXIso hn).hom
      ((isZero_stupidGr_X (K := K) (p := p) (i := n + 1) (by omega)).eq_of_tgt _ _)
      ((stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega)).hom ≫ (cokernel.π
        (Subobject.ofLE (K.stupidFiltration (p - 1 - 1)) (K.stupidFiltration (p - 1))
          (K.monotone_stupidFiltration (by omega)) ≫
            Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
              (K.monotone_stupidFiltration (by omega)))).f n)
      (by
        rw [Category.assoc, ← HomologicalComplex.comp_f]
        simp [cokernel.map, stupidGrXIso_hom])
      (K.d n (n + 1) ≫ (stupidGrXIso (K := K) (p := p - 1) (n := n + 1) (by omega)).hom)
      (by
        rw [stupidGrXIso_hom, Category.assoc, Category.assoc, ← HomologicalComplex.comp_f]
        simp only [cokernel.map, cokernel.π_desc, HomologicalComplex.comp_f,
          stupidFiltrationXIso_hom_ofLE_f_assoc, TauCeti.cokernelCompSequence_X₂, Category.assoc,
          HomologicalComplex.Hom.comm]
        rw [stupidFiltrationXIso_hom_d_assoc (K := K) (p := p) (by omega) (by omega)])
      (n + 1 + 1) (by simp),
    HomologicalComplex.comp_liftCycles_assoc]

/-- **The first page of the spectral sequence of the brutal filtration.** For the filtration
`F_p = σ^{≥ -p} K` of `K`, read as a chain complex with `C_n = K^{-n}`, the object `E¹_{p,0}` is
the term `C_p = K^{-p}`. -/
noncomputable def stupidFiltrationFirstPageXIso (p q : ℤ) (hq : q = 0) :
    ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page 1).X (p, q) ≅ K.X (-(p + q)) :=
  homologicalFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (stupidGrHomologyIso (K := K) (p := p) (n := -(p + q)) (by omega)).symm

/-- **The first page of the spectral sequence of the brutal filtration is concentrated on the row
`q = 0`.** -/
lemma isZero_stupidFiltrationSpectralSequence_page_X (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hq : q ≠ 0) :
    IsZero (((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page r).X (p, q)) := by
  set E := homologicalFiltrationSpectralSequence K.stupidFiltration K.monotone_stupidFiltration
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k + 1 := ⟨(r - 1).toNat, by omega⟩
  induction k with
  | zero =>
    refine IsZero.of_iso ?_ ((E.pageXIsoOfEq (p, q) _ 1 (by simp)) ≪≫
      homologicalFiltrationSpectralSequenceFirstPageXIso _ _ p q)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_stupidGr_X (by omega))
  | succ k ih =>
    exact IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ (ih (by omega)))
      (E.iso (k + 1) ((k + 1 : ℕ) + 1) (p, q) (by push_cast; ring)).symm

/-- **The first differential of the spectral sequence of the brutal filtration is the
differential of `K`.** Under the identifications `E¹_{p,0} ≅ C_p = K^{-p}`
(`CochainComplex.stupidFiltrationFirstPageXIso`), the differential `d¹ : E¹_{p,0} ⟶ E¹_{p-1,0}` is
the differential `K^{-p} ⟶ K^{-p+1}`, the boundary `∂ : C_p ⟶ C_{p-1}`. -/
lemma stupidFiltrationSpectralSequence_first_page_d (p p' q : ℤ) (hp : p' = p - 1) (hq : q = 0) :
    ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page 1).d (p, q) (p', q) =
        (K.stupidFiltrationFirstPageXIso p q hq).hom ≫ K.d (-(p + q)) (-(p' + q)) ≫
          (K.stupidFiltrationFirstPageXIso p' q hq).inv := by
  subst hp
  rw [homologicalFiltrationSpectralSequence_first_page_d_eq]
  simp only [stupidFiltrationFirstPageXIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Category.assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  rw [Category.assoc, Iso.eq_inv_comp]
  exact stupidGrHomologyIso_hom_δ (K := K) (by omega) (by omega)

/-- The first page of the spectral sequence of the brutal filtration, along the row `q = 0`, is
the complex `K` itself: the short complex `E¹_{p+1,0} ⟶ E¹_{p,0} ⟶ E¹_{p-1,0}` is
`K^{-p-1} ⟶ K^{-p} ⟶ K^{-p+1}`. -/
private noncomputable def stupidFiltrationFirstPageScIso (p q : ℤ) (hq : q = 0) :
    ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page 1).sc' (p + 1, q) (p, q) (p - 1, q) ≅
        K.sc' (-(p + 1 + q)) (-(p + q)) (-(p - 1 + q)) :=
  ShortComplex.isoMk (K.stupidFiltrationFirstPageXIso (p + 1) q hq)
    (K.stupidFiltrationFirstPageXIso p q hq) (K.stupidFiltrationFirstPageXIso (p - 1) q hq)
    (by
      simp [stupidFiltrationSpectralSequence_first_page_d K (p + 1) p q (by omega) hq])
    (by simp [stupidFiltrationSpectralSequence_first_page_d K p (p - 1) q rfl hq])

/-- **The second page of the spectral sequence of the brutal filtration is the homology of the
complex.** For the filtration `F_p = σ^{≥ -p} K` of `K`, read as a chain complex with
`C_n = K^{-n}`, the object `E²_{p,0}` is `H_p(C) = H^{-p}(K)`. Off the row `q = 0` the second page
vanishes (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`). -/
noncomputable def stupidFiltrationSecondPageXIso (p q : ℤ) (hq : q = 0) :
    ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page 2).X (p, q) ≅ K.homology (-(p + q)) :=
  ((homologicalFiltrationSpectralSequence K.stupidFiltration
    K.monotone_stupidFiltration).iso 1 2 (p, q)).symm ≪≫
    HomologicalComplex.homologyIsoSc' _ (p + 1, q) (p, q) (p - 1, q)
      ((ComplexShape.up' _).prev_eq' (by simp)) ((ComplexShape.up' _).next_eq' (by simp; omega)) ≪≫
    ShortComplex.homologyMapIso (K.stupidFiltrationFirstPageScIso p q hq) ≪≫
    (K.homologyIsoSc' (-(p + 1 + q)) (-(p + q)) (-(p - 1 + q)) (by simp; omega)
      (by simp; omega)).symm

/-- On every page `r ≥ 2`, the object at `(p, q)` of the spectral sequence of the brutal
filtration is the object at `(p, q)` of the page `r + 1`: the differentials of the page `r`
entering and leaving `(p, q)` connect the rows `q` and `q ± (r - 1)`, one of which vanishes. -/
private noncomputable def stupidFiltrationPageXIsoSucc (r : ℤ) (hr : 2 ≤ r) (p q : ℤ)
    (hq : q = 0) :
    ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page (r + 1)).X (p, q) ≅
      ((homologicalFiltrationSpectralSequence K.stupidFiltration
        K.monotone_stupidFiltration).page r).X (p, q) :=
  ((homologicalFiltrationSpectralSequence K.stupidFiltration
    K.monotone_stupidFiltration).iso r (r + 1) (p, q)).symm ≪≫
    (HomologicalComplex.isoHomologyπ _ (p + r, q - r + 1) (p, q)
      ((ComplexShape.up' _).prev_eq' (by simp))
      ((K.isZero_stupidFiltrationSpectralSequence_page_X r (by omega) _ _ (by omega)).eq_of_src
        _ _)).symm ≪≫
    HomologicalComplex.iCyclesIso _ (p, q) (p - r, q + r - 1)
      ((ComplexShape.up' _).next_eq' (by simp; omega))
      ((K.isZero_stupidFiltrationSpectralSequence_page_X r (by omega) _ _ (by omega)).eq_of_tgt
        _ _)

/-- The object `E^{k+2}_{p,0}` of the spectral sequence of the brutal filtration is the homology
`H^{-p}(K)`, by induction on `k`. -/
private noncomputable def stupidFiltrationPageXIsoAux (p q : ℤ) (hq : q = 0) :
    (k : ℕ) → ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page ((k : ℤ) + 2)).X (p, q) ≅ K.homology (-(p + q))
  | 0 => (homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).pageXIsoOfEq (p, q) _ 2 (by simp) ≪≫
        K.stupidFiltrationSecondPageXIso p q hq
  | k + 1 => (homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).pageXIsoOfEq (p, q) _ ((k : ℤ) + 2 + 1) (by push_cast; ring) ≪≫
        K.stupidFiltrationPageXIsoSucc (k + 2) (by omega) p q hq ≪≫
          stupidFiltrationPageXIsoAux p q hq k

/-- **The spectral sequence of the brutal filtration degenerates at the second page.** On every
page `r ≥ 2`, the object `E^r_{p,0}` is the homology `H_p(C) = H^{-p}(K)`; off the row `q = 0`
every page vanishes (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`). -/
noncomputable def stupidFiltrationPageXIso (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) (hq : q = 0) :
    ((homologicalFiltrationSpectralSequence K.stupidFiltration
      K.monotone_stupidFiltration).page r).X (p, q) ≅ K.homology (-(p + q)) :=
  (homologicalFiltrationSpectralSequence K.stupidFiltration
    K.monotone_stupidFiltration).pageXIsoOfEq (p, q) r (((r - 2).toNat : ℤ) + 2) (by omega) ≪≫
      K.stupidFiltrationPageXIsoAux p q hq (r - 2).toNat

end CochainComplex
