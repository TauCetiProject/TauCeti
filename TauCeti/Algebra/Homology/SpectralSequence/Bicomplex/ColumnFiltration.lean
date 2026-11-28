/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotalComplex.AcyclicAssembly
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject

/-!
# The column filtration of a cochain bicomplex

The decreasing column filtration on the direct-sum total complex is given by the totals of
the brutal truncations in the outer cochain direction. Its associated graded complex in
filtration degree `p` is the column `K.X p` shifted by `-p`. The first classical page of the
resulting spectral sequence thus consists of column cohomology.

See the Stacks Project, Tag 012X and Lemma 25.1 (Tag 0130).
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace HomologicalComplex₂

section Filtration

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]

/-- The total of the columns of index at least `p` includes into the total of the bicomplex. -/
noncomputable abbrev totalColumnFiltrationι (p : ℤ) :
    total (K.stupidTrunc (embeddingUpIntGE p)) (.up ℤ) ⟶ K.total (.up ℤ) :=
  total.map (K.ιStupidTrunc (embeddingUpIntGE p)) (.up ℤ)

private lemma mono_totalColumnFiltrationι_succ (p : ℤ) :
    Mono (K.totalColumnFiltrationι (p + 1)) :=
  (totalShortComplex_shortExact (.up ℤ) (CochainComplex.stupidTruncShortComplex K p)
    (fun i j ↦ (CochainComplex.stupidTruncShortComplexSplitting K p i).map
      (eval C (.up ℤ) j))).mono_f

/-- The inclusion defining the column filtration is monic. -/
instance mono_totalColumnFiltrationι (p : ℤ) : Mono (K.totalColumnFiltrationι p) := by
  have hp : p - 1 + 1 = p := by omega
  rw [← hp]
  exact K.mono_totalColumnFiltrationι_succ (p - 1)

/-- The column filtration of the direct-sum total complex, indexed decreasingly by `ℤ`. -/
noncomputable def totalColumnFiltration (p : ℤ) : Subobject (K.total (.up ℤ)) :=
  Subobject.mk (K.totalColumnFiltrationι p)

/-- The step in column degree `p` is represented by the total of the brutal truncation. -/
lemma totalColumnFiltration_eq_mk (p : ℤ) :
    K.totalColumnFiltration p = Subobject.mk (K.totalColumnFiltrationι p) := (rfl)

/-- The column filtration decreases as the column index increases. -/
lemma antitone_totalColumnFiltration : Antitone K.totalColumnFiltration := by
  intro p q h
  apply Subobject.mk_le_mk_of_comm (total.map (CochainComplex.stupidTruncGEMap K h) (.up ℤ))
  rw [← total.map_comp, CochainComplex.stupidTruncGEMap_comp_ιStupidTrunc]

variable {K} {L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} [L.HasTotal (.up ℤ)]

/-- A map of bicomplexes is filtered for the column filtrations on their total complexes. -/
lemma totalColumnFiltration_factors (f : K ⟶ L) (p : ℤ) :
    (L.totalColumnFiltration p).Factors ((K.totalColumnFiltration p).arrow ≫
      total.map f (.up ℤ)) := by
  rw [K.totalColumnFiltration_eq_mk, L.totalColumnFiltration_eq_mk]
  let S := Subobject.underlyingIso (K.totalColumnFiltrationι p)
  let T := Subobject.underlyingIso (L.totalColumnFiltrationι p)
  let g := total.map (stupidTruncMap f (embeddingUpIntGE p)) (.up ℤ)
  have hg : g ≫ L.totalColumnFiltrationι p =
      K.totalColumnFiltrationι p ≫ total.map f (.up ℤ) := by
    simp [g, ← total.map_comp]
  have he : (S.hom ≫ g ≫ T.inv) ≫ (Subobject.mk (L.totalColumnFiltrationι p)).arrow =
      (Subobject.mk (K.totalColumnFiltrationι p)).arrow ≫ total.map f (.up ℤ) := by
    simp only [Category.assoc, T, Subobject.underlyingIso_arrow, hg, S,
      Subobject.underlyingIso_hom_comp_eq_mk_assoc]
  rw [← he]
  exact Subobject.factors_comp_arrow _

variable (K)

/-- The diagram of column-filtration stages, with the increasing index `-p` at column `p`.
The bottom and top stages are zero and the whole total complex, respectively. -/
noncomputable abbrev totalColumnFiltrationFunctor : EInt ⥤ CochainComplex C ℤ :=
  CochainComplex.filtrationFunctor (fun t ↦ K.totalColumnFiltration (-t))
    (fun _ _ h ↦ K.antitone_totalColumnFiltration (neg_le_neg h))

/-- At the finite index `-p`, the column filtration is the total of the columns at least `p`. -/
noncomputable def totalColumnFiltrationStageIso (p : ℤ) :
    K.totalColumnFiltrationFunctor.obj ((-p : ℤ) : EInt) ≅
      total (K.stupidTrunc (embeddingUpIntGE p)) (.up ℤ) :=
  CochainComplex.filtrationFunctorObjIsoOfEqMk _ _ (K.totalColumnFiltrationι p)
    (by simpa only [neg_neg] using K.totalColumnFiltration_eq_mk p)

/-- The stage identification intertwines the maps to the full total complex. -/
@[reassoc (attr := simp)]
lemma totalColumnFiltrationStageIso_hom_comp_ι (p : ℤ) :
    (K.totalColumnFiltrationStageIso p).hom ≫ K.totalColumnFiltrationι p =
      CochainComplex.filtrationFunctorArrow _ _ ((-p : ℤ) : EInt) :=
  CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp _ _ _ _

/-- The comparison between the two ways of truncating to columns at least `q`, for `p ≤ q`. -/
private noncomputable def totalColumnTruncationIso {p q : ℤ} (h : p ≤ q) :
    total ((K.stupidTrunc (embeddingUpIntGE p)).stupidTrunc (embeddingUpIntGE q)) (.up ℤ) ≅
      total (K.stupidTrunc (embeddingUpIntGE q)) (.up ℤ) :=
  haveI := CochainComplex.isIso_stupidTruncMap_ιStupidTruncGE K h
  total.mapIso (asIso (stupidTruncMap (K.ιStupidTrunc (embeddingUpIntGE p))
    (embeddingUpIntGE q))) (.up ℤ)

private lemma totalColumnTruncationIso_inv_comp_ι {p q : ℤ} (h : p ≤ q) :
    (K.totalColumnTruncationIso h).inv ≫
      total.map ((K.stupidTrunc (embeddingUpIntGE p)).ιStupidTrunc
        (embeddingUpIntGE q)) (.up ℤ) =
      total.map (CochainComplex.stupidTruncGEMap K h) (.up ℤ) := by
  have := CochainComplex.isIso_stupidTruncMap_ιStupidTruncGE K h
  rw [totalColumnTruncationIso, total.mapIso_inv, asIso_inv, ← total.map_comp]
  congr 1
  apply (cancel_mono (K.ιStupidTrunc (embeddingUpIntGE p))).1
  rw [Category.assoc, ← ιStupidTrunc_naturality, IsIso.inv_hom_id_assoc,
    CochainComplex.stupidTruncGEMap_comp_ιStupidTrunc]

private noncomputable abbrev totalColumnGradedShortComplex (p : ℤ) :=
  totalShortComplex (.up ℤ)
    (CochainComplex.stupidTruncShortComplex (K.stupidTrunc (embeddingUpIntGE p)) p)

private noncomputable def totalColumnGradedCokernelIso (p : ℤ) :
    cokernel (K.totalColumnFiltrationFunctor.map
      (TauCeti.eIntHomOfLE (show -(p + 1) ≤ -p by omega))) ≅
      (K.totalColumnGradedShortComplex p).X₃ := by
  let T := K.stupidTrunc (embeddingUpIntGE p)
  let S := K.totalColumnGradedShortComplex p
  let e := K.totalColumnFiltrationStageIso (p + 1) ≪≫
    (K.totalColumnTruncationIso (show p ≤ p + 1 by omega)).symm
  let t := K.totalColumnFiltrationStageIso p
  have w : K.totalColumnFiltrationFunctor.map (TauCeti.eIntHomOfLE
      (show -(p + 1) ≤ -p by omega)) ≫ t.hom = e.hom ≫ S.f := by
    apply (cancel_mono (K.totalColumnFiltrationι p)).1
    simp only [Category.assoc, t, totalColumnFiltrationStageIso_hom_comp_ι,
      e, Iso.trans_hom, Iso.symm_hom]
    have hf : S.f = total.map (T.ιStupidTrunc (embeddingUpIntGE (p + 1))) (.up ℤ) := rfl
    rw [hf, ← Category.assoc (K.totalColumnTruncationIso _).inv,
      K.totalColumnTruncationIso_inv_comp_ι, ← total.map_comp,
      CochainComplex.stupidTruncGEMap_comp_ιStupidTrunc]
    simpa only [totalColumnFiltrationStageIso_hom_comp_ι] using
      CochainComplex.filtrationFunctor_map_comp_arrow _ _
        (TauCeti.eIntHomOfLE (show -(p + 1) ≤ -p by omega))
  have hS : S.ShortExact :=
    totalShortComplex_shortExact (.up ℤ) (CochainComplex.stupidTruncShortComplex T p)
      (fun i j ↦ (CochainComplex.stupidTruncShortComplexSplitting T p i).map (eval C (.up ℤ) j))
  exact cokernel.mapIso _ S.f e t w ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

private noncomputable def totalColumnGradedShortComplexX₃Iso (p : ℤ) :
    (K.totalColumnGradedShortComplex p).X₃ ≅ (K.X p)⟦-p⟧ := by
  let T := K.stupidTrunc (embeddingUpIntGE p)
  let Q : HomologicalComplex₂ C (.up ℤ) (.up ℤ) := T.stupidTrunc (embeddingUpIntLE p)
  have : IsIso ((T.πStupidTrunc (embeddingUpIntLE p)).f p) :=
    T.isIso_πStupidTrunc_f _ (i := 0) (by simp)
  have : IsIso ((K.ιStupidTrunc (embeddingUpIntGE p)).f p) :=
    K.isIso_ιStupidTrunc_f _ (i := 0) (by simp)
  let e : Q.X p ≅ K.X p :=
    (asIso ((T.πStupidTrunc (embeddingUpIntLE p)).f p)).symm ≪≫
      asIso ((K.ιStupidTrunc (embeddingUpIntGE p)).f p)
  have hQ : ∀ i, i ≠ p → IsZero (Q.X i) := fun i hi ↦
    CochainComplex.isZero_stupidTrunc_embeddingUpIntLE_X_of_isZero T p p
      (fun _ hj ↦ CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X K p hj) (lt_or_gt_of_ne hi)
  exact (Q.shiftIsoTotalOfIsZero p hQ).symm ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-p)).mapIso e

/-- The graded piece of the column filtration in degree `p` is the column `p` shifted by
`-p`. The quotient is induced by projecting the truncated bicomplex onto its first column. -/
noncomputable def totalColumnFiltrationGradedIso (p : ℤ) :
    cokernel (K.totalColumnFiltrationFunctor.map
      (TauCeti.eIntHomOfLE (show -(p + 1) ≤ -p by omega))) ≅ (K.X p)⟦-p⟧ :=
  K.totalColumnGradedCokernelIso p ≪≫ K.totalColumnGradedShortComplexX₃Iso p

/-- The projection from the total of the columns at least `p` onto its column `p` quotient. -/
noncomputable def totalColumnFiltrationGradedπ (p : ℤ) :
    total (K.stupidTrunc (embeddingUpIntGE p)) (.up ℤ) ⟶ (K.X p)⟦-p⟧ :=
  (K.totalColumnGradedShortComplex p).g ≫ (K.totalColumnGradedShortComplexX₃Iso p).hom

/-- The projection onto the shifted column agrees with the original truncation identification
on the summand for that column. -/
@[reassoc]
lemma ιTotal_totalColumnFiltrationGradedπ_f_self (p n : ℤ) :
    ιTotal (K.stupidTrunc (embeddingUpIntGE p)) (.up ℤ) p (n + -p) n (by simp) ≫
      (K.totalColumnFiltrationGradedπ p).f n =
      ((K.ιStupidTrunc (embeddingUpIntGE p)).f p).f (n + -p) := by
  let T := K.stupidTrunc (embeddingUpIntGE p)
  let Q : HomologicalComplex₂ C (.up ℤ) (.up ℤ) := T.stupidTrunc (embeddingUpIntLE p)
  have hQ : ∀ i, i ≠ p → IsZero (Q.X i) := fun i hi ↦
    CochainComplex.isZero_stupidTrunc_embeddingUpIntLE_X_of_isZero T p p
      (fun _ hj ↦ CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X K p hj) (lt_or_gt_of_ne hi)
  let e := Q.shiftIsoTotalOfIsZero p hQ
  have hshift : e.hom.f n ≫ e.inv.f n = 𝟙 _ := by
    rw [← comp_f, Iso.hom_inv_id, id_f]
  have : IsIso ((T.πStupidTrunc (embeddingUpIntLE p)).f p) :=
    T.isIso_πStupidTrunc_f _ (i := 0) (by simp)
  have hπ : ((T.πStupidTrunc (embeddingUpIntLE p)).f p).f (n + -p) ≫
      (inv ((T.πStupidTrunc (embeddingUpIntLE p)).f p)).f (n + -p) = 𝟙 _ := by
    rw [← comp_f, IsIso.hom_inv_id, id_f]
  simp only [totalColumnFiltrationGradedπ, comp_f, ιTotal_map_assoc,
    totalColumnGradedShortComplexX₃Iso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    CochainComplex.shiftFunctor_map_f', asIso_hom, asIso_inv]
  rw [← shiftIsoTotalOfIsZero_hom_f Q p hQ]
  dsimp only [e, Q, T] at hshift hπ
  rw [reassoc_of% hshift, reassoc_of% hπ]

/-- The projection onto the shifted column vanishes on summands from other columns. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalColumnFiltrationGradedπ_f_of_ne (p i j n : ℤ)
    (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (i, j) = n) (hi : i ≠ p) :
    ιTotal (K.stupidTrunc (embeddingUpIntGE p)) (.up ℤ) i j n h ≫
      (K.totalColumnFiltrationGradedπ p).f n = 0 := by
  let T := K.stupidTrunc (embeddingUpIntGE p)
  simp only [totalColumnFiltrationGradedπ, comp_f, ιTotal_map_assoc]
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact ((eval C (.up ℤ) j).map_isZero
      (CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X K p hi)).eq_of_src _ _
  · rw [CochainComplex.πStupidTruncLE_f_of_lt T p hi, zero_f, zero_comp]

/-- The associated graded identification intertwines the cokernel projection with the projection
onto the shifted column. -/
@[reassoc (attr := simp)]
lemma cokernel_π_totalColumnFiltrationGradedIso_hom (p : ℤ) :
    cokernel.π _ ≫ (K.totalColumnFiltrationGradedIso p).hom =
      (K.totalColumnFiltrationStageIso p).hom ≫ K.totalColumnFiltrationGradedπ p := by
  unfold totalColumnFiltrationGradedIso totalColumnFiltrationGradedπ totalColumnGradedCokernelIso
  simp only [Iso.trans_hom, cokernel.mapIso_hom, Category.assoc, cokernel.map,
    cokernel.π_desc_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

/-- The column spectral sequence of the direct-sum total, in Mathlib's native indexing. -/
noncomputable abbrev totalColumnSpectralSequence :=
  CochainComplex.spectralSequence K.totalColumnFiltrationFunctor

/-- Classical `E₁^{p,q}` of the column spectral sequence is the `q`-th cohomology of column `p`.
The classical position `(p, q)` is represented by `(2 * p + q + 1, -p - 1)` on native page `2`. -/
noncomputable def totalColumnSpectralSequenceFirstPageXIso (p q : ℤ) :
    (K.totalColumnSpectralSequence.page 2).X (2 * p + q + 1, -p - 1) ≅ (K.X p).homology q := by
  have hmono {a b : EInt} (f : a ⟶ b) : Mono (K.totalColumnFiltrationFunctor.map f) := by
    exact CochainComplex.instMonoIntMapEIntFiltrationFunctor
      (fun t ↦ K.totalColumnFiltration (-t)) _ f
  let e := CochainComplex.spectralSequenceFirstPageXIsoCokernel K.totalColumnFiltrationFunctor
    (2 * p + q + 1, -p - 1) (-(p + 1)) (-p) (by dsimp; omega) (by dsimp; omega)
    (p + q) (by dsimp; omega)
  exact e ≪≫ homologyMapIso (K.totalColumnFiltrationGradedIso p) (p + q) ≪≫
    (CochainComplex.ShiftSequence.shiftIso C (-p) (p + q) q (by omega)).app (K.X p)

end Filtration

end HomologicalComplex₂
