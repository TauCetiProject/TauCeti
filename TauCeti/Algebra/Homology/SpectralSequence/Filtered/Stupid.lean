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
(`CochainComplex.stupidFiltrationSpectralSequence`) is computed by hand:

* the first page is `E¹_{p,0} = C_p`
  (`CochainComplex.stupidFiltrationSpectralSequenceFirstPageXIso`) and every page vanishes off the
  row `q = 0`
  (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`);
* the first differential `d¹ : E¹_{p,0} ⟶ E¹_{p-1,0}` is the boundary `∂ : C_p ⟶ C_{p-1}`
  (`CochainComplex.stupidFiltrationSpectralSequence_first_page_d_eq`), the connecting map of
  `F_{p-1}/F_{p-2} ⟶ F_p/F_{p-2} ⟶ F_p/F_{p-1}`;
* hence the second page is the homology, `E²_{p,0} = H_p(C)`
  (`CochainComplex.stupidFiltrationSpectralSequenceSecondPageXIso`), and the spectral sequence
  degenerates there: the differentials of the pages `r ≥ 2` leave the row `q = 0`, so they vanish
  (`CochainComplex.stupidFiltrationSpectralSequence_page_d_eq_zero`) and
  `E^r_{p,0} = H_p(C)` for every `r ≥ 2`
  (`CochainComplex.stupidFiltrationSpectralSequencePageXIso`).

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

/-- The subcomplex `F_p` of the brutal filtration is the image of Mathlib's brutal truncation
`σ^{≥ -p} K ⟶ K`. -/
lemma stupidFiltration_eq (p : ℤ) :
    K.stupidFiltration p = Subobject.mk (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (-p))) :=
  (rfl)

variable {K} in
/-- In the degrees `≥ -p`, the subcomplex `F_p` of the brutal filtration is all of `K`. -/
lemma isIso_stupidFiltration_arrow_f {p i : ℤ} (hi : -p ≤ i) :
    IsIso ((K.stupidFiltration p).arrow.f i) := by
  rw [stupidFiltration_eq, ← Subobject.underlyingIso_hom_comp_eq_mk, HomologicalComplex.comp_f]
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
  rw [stupidFiltration_eq]
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

/-- The homological spectral sequence of the filtration of `K` by its brutal truncations,
`CochainComplex.homologicalFiltrationSpectralSequence` for `CochainComplex.stupidFiltration`. -/
noncomputable abbrev stupidFiltrationSpectralSequence :
    SpectralSequence C (fun r ↦ ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) 1 :=
  homologicalFiltrationSpectralSequence K.stupidFiltration K.monotone_stupidFiltration

/-- The inclusion `F_{p-1} ⟶ F_p` of the filtration by brutal truncations. -/
private noncomputable abbrev stupidFiltrationι (p : ℤ) :
    (K.stupidFiltration (p - 1) : CochainComplex C ℤ) ⟶ K.stupidFiltration p :=
  Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
    (K.monotone_stupidFiltration (by omega))

/-- The graded piece `F_p/F_{p-1}` of the filtration by brutal truncations. -/
private noncomputable abbrev stupidGr (p : ℤ) : CochainComplex C ℤ :=
  cokernel (K.stupidFiltrationι p)

/-- The projection `F_p ⟶ F_p/F_{p-1}` onto the graded piece. -/
private noncomputable abbrev stupidGrπ (p : ℤ) :
    (K.stupidFiltration p : CochainComplex C ℤ) ⟶ K.stupidGr p :=
  cokernel.π (K.stupidFiltrationι p)

variable {K} in
/-- The graded piece `F_p/F_{p-1}` vanishes outside the degree `-p`. -/
private lemma isZero_stupidGr_X {p i : ℤ} (hi : i ≠ -p) : IsZero ((K.stupidGr p).X i) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact IsZero.of_epi ((K.stupidGrπ p).f i) (isZero_stupidFiltration_X hi)
  · have h₁ := isIso_stupidFiltration_arrow_f (K := K) (p := p) (i := i) (by omega)
    have h₂ := isIso_stupidFiltration_arrow_f (K := K) (p := p - 1) (i := i) (by omega)
    have : IsIso ((K.stupidFiltrationι p).f i) := by
      have w := congrArg (fun φ ↦ φ.f i) (Subobject.ofLE_arrow
        (K.monotone_stupidFiltration (show p - 1 ≤ p by omega)))
      simp only [HomologicalComplex.comp_f] at w
      exact IsIso.of_isIso_fac_right w
    -- The projection onto the cokernel vanishes in the degree `i`, where it is an epimorphism.
    refine IsZero.of_epi_eq_zero ((K.stupidGrπ p).f i) ?_
    rw [← cancel_epi ((K.stupidFiltrationι p).f i), ← HomologicalComplex.comp_f,
      cokernel.condition, HomologicalComplex.zero_f, comp_zero]

variable {K} in
/-- In the degree `-p`, the projection of `F_p` onto the graded piece `F_p/F_{p-1}` is an
isomorphism, since `F_{p-1}` vanishes there. -/
private lemma isIso_stupidGrπ_f {p n : ℤ} (hn : n = -p) : IsIso ((K.stupidGrπ p).f n) := by
  have hS := (TauCeti.cokernelSequence_shortExact (K.stupidFiltrationι p)).map_of_exact
    (HomologicalComplex.eval C _ n)
  have : Mono ((K.stupidGrπ p).f n) :=
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
private lemma stupidFiltrationXIso_hom_ι_f {p n : ℤ} (hn : -(p - 1) ≤ n) :
    (stupidFiltrationXIso hn).hom ≫ (K.stupidFiltrationι p).f n =
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
  haveI := isIso_stupidGrπ_f (K := K) hn
  stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega) ≪≫ asIso ((K.stupidGrπ p).f n)

variable {K} in
/-- The identification of `K^{-p}` with the graded piece `F_p/F_{p-1}` there is the inverse of the
inclusion followed by the projection. -/
private lemma stupidGrXIso_hom {p n : ℤ} (hn : n = -p) :
    (stupidGrXIso hn).hom =
      (stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega)).hom ≫ (K.stupidGrπ p).f n :=
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
/-- An element `x ∈ K^{-p}`, viewed in `F_p`, lifts to `F_p/F_{p-2}` the corresponding element
of the graded piece `F_p/F_{p-1}`. -/
private lemma stupidGr_lift_comp_g_f {p n : ℤ} (hn : n = -p) :
    ((stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega)).hom ≫
      (cokernel.π (K.stupidFiltrationι (p - 1) ≫ K.stupidFiltrationι p)).f n) ≫
        (TauCeti.cokernelCompSequence (K.stupidFiltrationι (p - 1))
          (K.stupidFiltrationι p)).g.f n = (stupidGrXIso hn).hom := by
  rw [Category.assoc, ← HomologicalComplex.comp_f]
  simp [cokernel.map, stupidGrXIso_hom]

variable {K} in
/-- The differential in `F_p/F_{p-2}` of the lift of `x ∈ K^{-p}` is the image of
`∂x ∈ K^{-p+1} = F_{p-1}/F_{p-2}`. -/
private lemma stupidGr_d_comp_f_f {p n m : ℤ} (hn : n = -p) (hm : m = n + 1) :
    (K.d n m ≫ (stupidGrXIso (K := K) (p := p - 1) (n := m) (by omega)).hom) ≫
      (TauCeti.cokernelCompSequence (K.stupidFiltrationι (p - 1))
        (K.stupidFiltrationι p)).f.f m =
      ((stupidFiltrationXIso (K := K) (p := p) (n := n) (by omega)).hom ≫
        (cokernel.π (K.stupidFiltrationι (p - 1) ≫ K.stupidFiltrationι p)).f n) ≫
          (cokernel (K.stupidFiltrationι (p - 1) ≫ K.stupidFiltrationι p)).d n m := by
  rw [stupidGrXIso_hom, Category.assoc, Category.assoc, ← HomologicalComplex.comp_f]
  simp only [cokernel.map, cokernel.π_desc, HomologicalComplex.comp_f,
    stupidFiltrationXIso_hom_ι_f_assoc, Category.assoc, HomologicalComplex.Hom.comm]
  rw [stupidFiltrationXIso_hom_d_assoc (K := K) (p := p) (by omega) (by omega)]

variable {K} in
/-- The connecting map of the short exact sequence `F_{p-1}/F_{p-2} ⟶ F_p/F_{p-2} ⟶ F_p/F_{p-1}`
from the degree `-p` to the degree `-p + 1` is the differential of `K`, under the identifications
of the homology of the graded pieces with the terms of `K`. -/
private lemma stupidGr_δ_eq {p n m : ℤ} (hn : n = -p) (hm : m = n + 1) :
    (TauCeti.cokernelCompSequence_shortExact (K.stupidFiltrationι (p - 1))
        (K.stupidFiltrationι p)).δ n m (by simp; omega) =
      (stupidGrHomologyIso (K := K) hn).inv ≫ K.d n m ≫
        (stupidGrHomologyIso (K := K) (p := p - 1) (n := m) (by omega)).hom := by
  subst hm
  rw [Iso.eq_inv_comp, stupidGrHomologyIso_hom, stupidGrHomologyIso_hom, Category.assoc,
    (TauCeti.cokernelCompSequence_shortExact _ _).δ_eq n (n + 1) (by simp) _
      ((isZero_stupidGr_X (K := K) (p := p) (i := n + 1) (by omega)).eq_of_tgt _ _) _
      (stupidGr_lift_comp_g_f hn) _ (stupidGr_d_comp_f_f hn rfl) (n + 1 + 1) (by simp),
    HomologicalComplex.comp_liftCycles_assoc]

/-- **The first page of the spectral sequence of the brutal filtration.** For the filtration
`F_p = σ^{≥ -p} K` of `K`, read as a chain complex with `C_n = K^{-n}`, the object `E¹_{p,0}` is
the term `C_p = K^{-p}`. -/
noncomputable def stupidFiltrationSpectralSequenceFirstPageXIso (p q : ℤ) (hq : q = 0) :
    (K.stupidFiltrationSpectralSequence.page 1).X (p, q) ≅ K.X (-(p + q)) :=
  homologicalFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (stupidGrHomologyIso (K := K) (p := p) (n := -(p + q)) (by omega)).symm

/-- `CochainComplex.stupidFiltrationSpectralSequenceFirstPageXIso` sends an element of
`K^{-p} = F_p^{-p}` to the class of its image in the graded piece `F_p/F_{p-1}`, under the
identification `CochainComplex.homologicalFiltrationSpectralSequenceFirstPageXIso` of `E¹_{p,q}`
with the homology of the graded piece. Since the inclusion `F_p^{-p} ⟶ K^{-p}` is an isomorphism
(`CochainComplex.isIso_stupidFiltration_arrow_f`), this characterizes the identification. -/
@[reassoc]
lemma stupidFiltration_arrow_f_stupidFiltrationSpectralSequenceFirstPageXIso_inv (p q : ℤ)
    (hq : q = 0) :
    (K.stupidFiltration p).arrow.f (-(p + q)) ≫
        (K.stupidFiltrationSpectralSequenceFirstPageXIso p q hq).inv =
      (cokernel (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
          (K.monotone_stupidFiltration (by omega)))).liftCycles
        ((cokernel.π (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
          (K.monotone_stupidFiltration (by omega)))).f (-(p + q))) (-(p + q) + 1) (by simp)
        (by rw [stupidGr_d_eq_zero (K := K) (p := p) (n := -(p + q)) (by omega) (by omega),
          comp_zero]) ≫
        (cokernel (Subobject.ofLE (K.stupidFiltration (p - 1)) (K.stupidFiltration p)
          (K.monotone_stupidFiltration (by omega)))).homologyπ (-(p + q)) ≫
        (homologicalFiltrationSpectralSequenceFirstPageXIso _ _ p q).inv := by
  have := isIso_stupidFiltration_arrow_f (K := K) (p := p) (i := -(p + q)) (by omega)
  simp [stupidFiltrationSpectralSequenceFirstPageXIso, stupidGrHomologyIso_hom, stupidGrXIso_hom,
    stupidFiltrationXIso, HomologicalComplex.comp_liftCycles_assoc]

/-- **Every page `r ≥ 1` of the spectral sequence of the brutal filtration vanishes off the row
`q = 0`.** -/
lemma isZero_stupidFiltrationSpectralSequence_page_X (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hq : q ≠ 0) : IsZero ((K.stupidFiltrationSpectralSequence.page r).X (p, q)) :=
  K.stupidFiltrationSpectralSequence.isZero_page_X_of_le le_rfl
    ((ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_stupidGr_X (by omega))).of_iso
      (homologicalFiltrationSpectralSequenceFirstPageXIso _ _ p q)) r hr

/-- **The spectral sequence of the brutal filtration degenerates at the second page.** On every
page `r ≥ 2` the differentials vanish, since they join the row `q = 0` to the rows `±(r - 1)`, on
which the pages vanish (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`). -/
lemma stupidFiltrationSpectralSequence_page_d_eq_zero (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    (K.stupidFiltrationSpectralSequence.page r).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)).Rel pq pq'
  · refine K.stupidFiltrationSpectralSequence.page_d_eq_zero_of_le le_rfl ?_ r (by omega)
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := pq'
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at hrel
    by_cases hq : q = 0
    · exact Or.inr (K.isZero_stupidFiltrationSpectralSequence_page_X 1 le_rfl _ _ (by omega))
    · exact Or.inl (K.isZero_stupidFiltrationSpectralSequence_page_X 1 le_rfl _ _ hq)
  · exact (K.stupidFiltrationSpectralSequence.page r).shape _ _ hrel

/-- **The first differential of the spectral sequence of the brutal filtration is the
differential of `K`.** Under the identifications `E¹_{p,0} ≅ C_p = K^{-p}`
(`CochainComplex.stupidFiltrationSpectralSequenceFirstPageXIso`), the differential
`d¹ : E¹_{p,0} ⟶ E¹_{p-1,0}` is the differential `K^{-p} ⟶ K^{-p+1}`, the boundary
`∂ : C_p ⟶ C_{p-1}`. -/
lemma stupidFiltrationSpectralSequence_first_page_d_eq (p p' q : ℤ) (hp : p' = p - 1)
    (hq : q = 0) :
    (K.stupidFiltrationSpectralSequence.page 1).d (p, q) (p', q) =
      (K.stupidFiltrationSpectralSequenceFirstPageXIso p q hq).hom ≫ K.d (-(p + q)) (-(p' + q)) ≫
        (K.stupidFiltrationSpectralSequenceFirstPageXIso p' q hq).inv := by
  subst hp
  rw [homologicalFiltrationSpectralSequence_first_page_d_eq,
    stupidGr_δ_eq (K := K) (p := p) (n := -(p + q)) (m := -(p - 1 + q)) (by omega) (by omega)]
  simp [stupidFiltrationSpectralSequenceFirstPageXIso]

/-- The first page of the spectral sequence of the brutal filtration, along the row `q = 0`, is
the complex `K` itself: the short complex `E¹_{p+1,0} ⟶ E¹_{p,0} ⟶ E¹_{p-1,0}` is
`K^{-p-1} ⟶ K^{-p} ⟶ K^{-p+1}`. -/
private noncomputable def stupidFiltrationSpectralSequenceFirstPageScIso (p q : ℤ) (hq : q = 0) :
    (K.stupidFiltrationSpectralSequence.page 1).sc' (p + 1, q) (p, q) (p - 1, q) ≅
      K.sc' (-(p + 1 + q)) (-(p + q)) (-(p - 1 + q)) :=
  ShortComplex.isoMk (K.stupidFiltrationSpectralSequenceFirstPageXIso (p + 1) q hq)
    (K.stupidFiltrationSpectralSequenceFirstPageXIso p q hq)
    (K.stupidFiltrationSpectralSequenceFirstPageXIso (p - 1) q hq)
    (by simp [K.stupidFiltrationSpectralSequence_first_page_d_eq (p + 1) p q (by omega) hq])
    (by simp [K.stupidFiltrationSpectralSequence_first_page_d_eq p (p - 1) q rfl hq])

/-- **The second page of the spectral sequence of the brutal filtration is the homology of the
complex.** For the filtration `F_p = σ^{≥ -p} K` of `K`, read as a chain complex with
`C_n = K^{-n}`, the object `E²_{p,0}` is `H_p(C) = H^{-p}(K)`. Off the row `q = 0` the second page
vanishes (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`). -/
noncomputable def stupidFiltrationSpectralSequenceSecondPageXIso (p q : ℤ) (hq : q = 0) :
    (K.stupidFiltrationSpectralSequence.page 2).X (p, q) ≅ K.homology (-(p + q)) :=
  (K.stupidFiltrationSpectralSequence.iso 1 2 (p, q)).symm ≪≫
    HomologicalComplex.homologyIsoSc' _ (p + 1, q) (p, q) (p - 1, q)
      ((ComplexShape.up' _).prev_eq' (by simp)) ((ComplexShape.up' _).next_eq' (by simp; omega)) ≪≫
    ShortComplex.homologyMapIso (K.stupidFiltrationSpectralSequenceFirstPageScIso p q hq) ≪≫
    (K.homologyIsoSc' (-(p + 1 + q)) (-(p + q)) (-(p - 1 + q)) (by simp; omega)
      (by simp; omega)).symm

/-- The identification `E²_{p,0} ≅ H^{-p}(K)` sends the class of a cycle `x` of the first page,
through `E¹_{p,0} ≅ K^{-p}`, to the class of the corresponding cycle of `K`. -/
@[reassoc]
lemma homologyπ_stupidFiltrationSpectralSequenceSecondPageXIso_hom (p q : ℤ) (hq : q = 0) :
    (K.stupidFiltrationSpectralSequence.page 1).homologyπ (p, q) ≫
      (K.stupidFiltrationSpectralSequence.iso 1 2 (p, q)).hom ≫
        (K.stupidFiltrationSpectralSequenceSecondPageXIso p q hq).hom =
      K.liftCycles ((K.stupidFiltrationSpectralSequence.page 1).iCycles (p, q) ≫
          (K.stupidFiltrationSpectralSequenceFirstPageXIso p q hq).hom) (-(p - 1 + q))
        (by simp; omega) (by
          rw [Category.assoc, ← cancel_mono
            (K.stupidFiltrationSpectralSequenceFirstPageXIso (p - 1) q hq).inv]
          simpa [K.stupidFiltrationSpectralSequence_first_page_d_eq p (p - 1) q rfl hq] using
            (K.stupidFiltrationSpectralSequence.page 1).iCycles_d (p, q) (p - 1, q)) ≫
        K.homologyπ (-(p + q)) := by
  simp only [stupidFiltrationSpectralSequenceSecondPageXIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyMapIso_hom, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (K.iCycles _)]
  simp [stupidFiltrationSpectralSequenceFirstPageScIso]

/-- **The pages `r ≥ 2` of the spectral sequence of the brutal filtration are the homology.** On
every page `r ≥ 2`, the object `E^r_{p,0}` is the homology `H_p(C) = H^{-p}(K)`: its neighbours
vanish (`CochainComplex.isZero_stupidFiltrationSpectralSequence_page_X`), so it survives from the
second page (`CategoryTheory.SpectralSequence.pageXIsoOfStabilizesAt`). -/
noncomputable def stupidFiltrationSpectralSequencePageXIso (r : ℤ) (hr : 2 ≤ r) (p q : ℤ)
    (hq : q = 0) :
    (K.stupidFiltrationSpectralSequence.page r).X (p, q) ≅ K.homology (-(p + q)) :=
  (K.stupidFiltrationSpectralSequence.pageXIsoOfStabilizesAt
    (K.stupidFiltrationSpectralSequence.stabilizesAt_of_forall_isZero (s := 2) (by norm_num)
      fun s hs pq' hpq' ↦ K.isZero_stupidFiltrationSpectralSequence_page_X 2 (by norm_num) _ _ (by
        obtain ⟨p', q'⟩ := pq'
        simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at hpq'
        omega)) r hr).symm ≪≫
    K.stupidFiltrationSpectralSequenceSecondPageXIso p q hq

/-- On the second page, `CochainComplex.stupidFiltrationSpectralSequencePageXIso` is
`CochainComplex.stupidFiltrationSpectralSequenceSecondPageXIso`. -/
@[simp]
lemma stupidFiltrationSpectralSequencePageXIso_two (p q : ℤ) (hq : q = 0) :
    K.stupidFiltrationSpectralSequencePageXIso 2 le_rfl p q hq =
      K.stupidFiltrationSpectralSequenceSecondPageXIso p q hq := by
  simp [stupidFiltrationSpectralSequencePageXIso]

/-- From the page `r ≥ 2` to the page `r + 1`,
`CochainComplex.stupidFiltrationSpectralSequencePageXIso` identifies the object at `(p, 0)` with
its homology on the page `r`, which is the object itself since both differentials there vanish
(`CochainComplex.stupidFiltrationSpectralSequence_page_d_eq_zero`). -/
lemma stupidFiltrationSpectralSequencePageXIso_add_one (r : ℤ) (hr : 2 ≤ r) (p q : ℤ)
    (hq : q = 0) :
    K.stupidFiltrationSpectralSequencePageXIso (r + 1) (by omega) p q hq =
      (K.stupidFiltrationSpectralSequence.iso r (r + 1) (p, q)).symm ≪≫
        ((K.stupidFiltrationSpectralSequence.page r).isoHomologyπ _ (p, q) rfl
          (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)).symm ≪≫
        (K.stupidFiltrationSpectralSequence.page r).iCyclesIso (p, q) _ rfl
          (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _) ≪≫
        K.stupidFiltrationSpectralSequencePageXIso r hr p q hq := by
  have hstep :
      (K.stupidFiltrationSpectralSequence.pageXStepIso (p, q) r (by omega)
          (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)
          (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)).inv =
        (K.stupidFiltrationSpectralSequence.iso r (r + 1) (p, q)).inv ≫
          ((K.stupidFiltrationSpectralSequence.page r).isoHomologyπ _ (p, q) rfl
            (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)).inv ≫
          ((K.stupidFiltrationSpectralSequence.page r).iCyclesIso (p, q) _ rfl
            (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)).hom := by
    rw [← cancel_epi (K.stupidFiltrationSpectralSequence.pageXStepIso (p, q) r (by omega)
      (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)
      (K.stupidFiltrationSpectralSequence_page_d_eq_zero r hr _ _)).hom, Iso.hom_inv_id]
    simp [SpectralSequence.pageXStepIso_hom, HomologicalComplex.XIsoHomologyOfDEqZero_hom]
  ext
  simp [stupidFiltrationSpectralSequencePageXIso,
    SpectralSequence.pageXIsoOfStabilizesAt_add_one _ r hr, hstep]

end CochainComplex
