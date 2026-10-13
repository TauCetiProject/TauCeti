/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import TauCeti.Algebra.Homology.Embedding.DownNatSucc
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Basic
public import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Total complexes of first-quadrant bicomplexes

A bicomplex indexed by `ℕ × ℕ` with homological differentials has only finitely many terms
`(K.X p).X q` with `p + q = n`, so its total complex exists in any preadditive category with finite
coproducts. Its differential is `d₁ + (-1)ᵖ d₂` on the summand `(K.X p).X q`, by Mathlib's sign
convention `TotalComplexShape (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)`.

An augmentation `ε : K.X 0 ⟶ E` of the column `0` by a chain complex `E`, that is a chain map
vanishing on the image of the horizontal differential `K.d 1 0`, induces a chain map
`HomologicalComplex₂.totalAugmentation` from the total complex to `E`. For the bicomplex whose
only column is `E`, in degree `0`, this map is an isomorphism.

When `C` is abelian, a map of first-quadrant bicomplexes which is a quasi-isomorphism on every row
`⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q` induces a quasi-isomorphism of total complexes. Applied to a map
to the bicomplex with the single column `E`, this says that exactness of the augmented rows
`⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q ⟶ E.X q ⟶ 0` makes the augmentation of the total complex a
quasi-isomorphism, as for the Čech complex of a cover or an acyclic resolution. The converse fails
in general. The proof filters the total complex by rows: row `0` is a subcomplex, the quotient is
the total complex of the remaining rows placed one degree higher, and an induction on the degree
compares the homology sequences of these short exact sequences.

## Main definitions and results

* `HomologicalComplex₂.hasTotal_down_nat`: first-quadrant bicomplexes have total complexes.
* `HomologicalComplex₂.totalAugmentation`: the chain map from the total complex induced by an
  augmentation of the column `0`.
* `HomologicalComplex₂.isIso_totalAugmentation_single`: the total complex of a bicomplex with a
  single column is that column.
* `HomologicalComplex₂.quasiIso_total_map_of_rows`: a map of bicomplexes which is a
  quasi-isomorphism on every row induces a quasi-isomorphism of total complexes.
* `HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`: exact augmented rows make the
  augmentation of the total complex a quasi-isomorphism.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 2.7, for the acyclic assembly lemma, of which the statement on rows is the relative form.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A first-quadrant bicomplex has a total complex as soon as finite coproducts exist. -/
instance hasTotal_down_nat [HasFiniteCoproducts C]
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := fun n ↦
  have : Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) :=
    inferInstanceAs (Finite ((fun i : ℕ × ℕ ↦ i.1 + i.2) ⁻¹' {n}))
  inferInstance

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [K.HasTotal (ComplexShape.down ℕ)] {E : ChainComplex C ℕ} (ε : K.X 0 ⟶ E) (hε : K.d 1 0 ≫ ε = 0)

/-- The components of `totalAugmentation`: `ε` on the column `0` and zero on the other columns. -/
private def totalAugmentationAux (n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p, q) = n) :
    (K.X p).X q ⟶ E.X n :=
  match p, h with
  | 0, h => ε.f q ≫ (E.XIsoOfEq (by simpa using h)).hom
  | _ + 1, _ => 0

/-- The chain map from the total complex of a first-quadrant bicomplex `K` to a chain complex `E`
induced by an augmentation `ε : K.X 0 ⟶ E` of the column `0` vanishing on the image of the
horizontal differential: it is `ε` on the summands `(K.X 0).X q` and zero on the other columns. -/
def totalAugmentation : K.total (ComplexShape.down ℕ) ⟶ E where
  f n := K.totalDesc (totalAugmentationAux K ε n)
  comm' := by
    rintro _ n rfl
    refine total.hom_ext _ fun p q h ↦ ?_
    rw [ι_totalDesc_assoc, total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc,
      ι_D₂_assoc]
    -- On the column `0` this is the commutation of `ε` with the vertical differentials, and on
    -- the column `1` it is `K.d 1 0 ≫ ε = 0`; the other terms land in columns `p ≥ 1`.
    rcases p with _ | p
    · obtain rfl : q = n + 1 := by simpa using h
      rw [d₁_eq_zero _ _ _ _ _ (by simp), zero_comp, zero_add,
        d₂_eq K _ 0 (ComplexShape.down_mk _ _ rfl) n (by simp)]
      simp [totalAugmentationAux]
    · have h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, q) = n := by
        simp at h ⊢
        omega
      rw [d₁_eq K _ (ComplexShape.down_mk _ _ rfl) q n h']
      have h₂ : K.d₂ (ComplexShape.down ℕ) (p + 1) q n ≫
          K.totalDesc (K.totalAugmentationAux ε n) = 0 := by
        rcases q with _ | q
        · rw [d₂_eq_zero _ _ _ _ _ (by simp), zero_comp]
        · rw [d₂_eq K _ (p + 1) (ComplexShape.down_mk _ _ rfl) n
            (by simp at h ⊢; omega)]
          simp [totalAugmentationAux]
      rw [h₂, add_zero]
      rcases p with _ | p
      · simp [totalAugmentationAux, ← HomologicalComplex.comp_f_assoc, hε]
      · simp [totalAugmentationAux]

/-- On the summand `(K.X 0).X q`, the augmentation of the total complex is the component of `ε` in
degree `q`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalAugmentation_f_zero (q : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫ (K.totalAugmentation ε hε).f q =
      ε.f q := by
  simp [totalAugmentation, totalAugmentationAux]

/-- The augmentation of the total complex vanishes on the columns `p + 1`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalAugmentation_f_succ (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p + 1, q) = n) :
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫ (K.totalAugmentation ε hε).f n = 0 := by
  simp [totalAugmentation, totalAugmentationAux]

/-- Composing the augmentation of the total complex with a chain map `g` gives the augmentation
induced by `ε ≫ g`. -/
lemma totalAugmentation_comp {E' : ChainComplex C ℕ} (g : E ⟶ E') :
    K.totalAugmentation ε hε ≫ g =
      K.totalAugmentation (ε ≫ g) (by rw [← Category.assoc, hε, zero_comp]) := by
  ext n p q h
  rcases p with _ | p
  · obtain rfl : q = n := by simpa using h
    simp
  · simp

section Single

variable [HasZeroObject C] [HasFiniteCoproducts C] (E : ChainComplex C ℕ)

omit [HasFiniteCoproducts C] in
/-- The identity of `E` is an augmentation of the bicomplex with the single column `E`. -/
lemma single_d_comp_singleObjXSelf_hom :
    ((HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E).d 1 0 ≫
      (HomologicalComplex.singleObjXSelf _ 0 E).hom = 0 := by
  rw [HomologicalComplex.single_obj_d, zero_comp]

/-- The total complex of the bicomplex with the single column `E` in degree `0` is `E`: its
augmentation by the identity of `E` is an isomorphism. -/
lemma isIso_totalAugmentation_single :
    IsIso (totalAugmentation ((HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E)
      (HomologicalComplex.singleObjXSelf _ 0 E).hom (single_d_comp_singleObjXSelf_hom E)) := by
  -- The inverse in degree `n` is the inclusion of `E.X n` as the summand of the column `0`.
  have (n : ℕ) : IsIso ((totalAugmentation _ _ (single_d_comp_singleObjXSelf_hom E)).f n) := by
    refine ⟨(HomologicalComplex.singleObjXSelf _ 0 E).inv.f n ≫
      HomologicalComplex₂.ιTotal ((HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E)
        _ 0 n n (by simp), ?_, ?_⟩
    · refine total.hom_ext _ fun p q h ↦ ?_
      rcases p with _ | p
      · obtain rfl : q = n := by simpa using h
        rw [ιTotal_totalAugmentation_f_zero_assoc, Category.comp_id,
          ← HomologicalComplex.comp_f_assoc, Iso.hom_inv_id, HomologicalComplex.id_f,
          Category.id_comp]
      · exact ((HomologicalComplex.eval C _ q).map_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp))).eq_of_src _ _
    · rw [Category.assoc, ιTotal_totalAugmentation_f_zero, ← HomologicalComplex.comp_f,
        Iso.inv_hom_id, HomologicalComplex.id_f]
  exact HomologicalComplex.Hom.isIso_of_components _

variable {E}

omit [K.HasTotal (ComplexShape.down ℕ)] [HasFiniteCoproducts C] in
/-- The column `0` of a map `φ` from `K` to the bicomplex with the single column `E` is an
augmentation of `K`: it vanishes on the image of the horizontal differential `K.d 1 0`. -/
lemma d_comp_f_zero_singleObjXSelf_hom
    (φ : K ⟶ (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E) :
    K.d 1 0 ≫ φ.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 E).hom = 0 := by
  rw [← Category.assoc, ← φ.comm, HomologicalComplex.single_obj_d, comp_zero, zero_comp]

/-- A map `φ` from `K` to the bicomplex with the single column `E` induces, on total complexes,
the augmentation of `K` by the column `0` of `φ`. -/
lemma total_map_totalAugmentation_single
    (φ : K ⟶ (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E) :
    total.map φ (ComplexShape.down ℕ) ≫
        totalAugmentation ((HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E)
          (HomologicalComplex.singleObjXSelf _ 0 E).hom (single_d_comp_singleObjXSelf_hom E) =
      K.totalAugmentation (φ.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 E).hom)
        (d_comp_f_zero_singleObjXSelf_hom K φ) := by
  ext n p q h
  -- `simp` would rewrite `singleObjXSelf` to an identity whose source is `E` rather than the
  -- column `0`, after which the lemmas on `totalAugmentation` no longer match.
  rcases p with _ | p
  · obtain rfl : q = n := by simpa using h
    rw [HomologicalComplex.comp_f, ιTotal_map_assoc, ιTotal_totalAugmentation_f_zero,
      ιTotal_totalAugmentation_f_zero, HomologicalComplex.comp_f]
  · rw [HomologicalComplex.comp_f, ιTotal_map_assoc, ιTotal_totalAugmentation_f_succ, comp_zero,
      ιTotal_totalAugmentation_f_succ]

end Single

end HomologicalComplex₂

/-! ### Rows and quasi-isomorphisms

Let `φ : K ⟶ L` be a map of first-quadrant bicomplexes in an abelian category which is a
quasi-isomorphism on every row. Row `0` is a subcomplex of the total complex, and the quotient is
the total complex of the rows `≥ 1`, reindexed and placed one degree higher. The short exact
sequence `row 0 ⟶ Tot K ⟶ Tot K⁺[1]` is split in each degree and natural in `φ`, and the
reindexed bicomplex `K⁺` again satisfies the hypothesis. Comparing the homology sequences shows,
by induction on `Q`, that `Tot φ` is an isomorphism in homology below `Q` and an epimorphism in
degree `Q`: the epimorphism in degree `Q + 1` on the quotient term is what the five lemma needs
in degree `Q`. -/

namespace HomologicalComplex₂

open HomologicalComplex
open ComplexShape (embeddingDownNatSucc embeddingDownNatSucc_f)

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The identification of the shift of a complex in degree `n + 1`. -/
private noncomputable abbrev extendSuccXIso (M : HomologicalComplex C (ComplexShape.down ℕ))
    (n : ℕ) : (M.extend embeddingDownNatSucc).X (n + 1) ≅ M.X n :=
  M.extendXIso embeddingDownNatSucc (embeddingDownNatSucc_f n)

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- The rows `≥ 1` of `K`, reindexed so that row `q + 1` of `K` is row `q`. The summands are
`(K.X p).X (q + 1)` up to reducible unfolding, which lets rewriting identify them with those of
`K`. -/
private abbrev rowsSucc : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  X p :=
    { X q := (K.X p).X (q + 1)
      d q q' := (K.X p).d (q + 1) (q' + 1)
      shape q q' h := (K.X p).shape _ _ (by simp at h ⊢; omega) }
  d p p' := { f q := (K.d p p').f (q + 1) }
  shape p p' h := by ext q; exact HomologicalComplex.congr_hom (K.shape _ _ h) (q + 1)
  d_comp_d' p p' p'' _ _ := by
    ext q; exact HomologicalComplex.congr_hom (K.d_comp_d p p' p'') (q + 1)

/-- The inclusion of row `0` into the total complex. -/
private noncomputable def rowZeroι :
    ((eval C (ComplexShape.down ℕ) 0).mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      K.total (ComplexShape.down ℕ) where
  f n := K.ιTotal (ComplexShape.down ℕ) n 0 n (by simp)
  comm' := by
    rintro _ n rfl
    rw [total_d, Preadditive.comp_add, ι_D₁, ι_D₂, d₂_eq_zero _ _ _ _ _ (by simp), add_zero,
      d₁_eq K _ (ComplexShape.down_mk _ _ rfl) 0 n (by simp)]
    simp

@[simp]
private lemma rowZeroι_f (n : ℕ) :
    (rowZeroι K).f n = K.ιTotal (ComplexShape.down ℕ) n 0 n (by simp) :=
  rfl

/-- The projection of the total complex in degree `n + 1` onto the total complex of `rowsSucc K`
in degree `n`, killing row `0`. -/
private noncomputable def dropRowZeroX (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X (n + 1) ⟶ ((rowsSucc K).total (ComplexShape.down ℕ)).X n :=
  K.totalDesc fun p q h ↦ match q, h with
    | 0, _ => 0
    | q + 1, h => (rowsSucc K).ιTotal (ComplexShape.down ℕ) p q n (by simp at h ⊢; omega)

@[reassoc (attr := simp)]
private lemma ιTotal_dropRowZeroX_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p 0 (n + 1) h ≫ dropRowZeroX K n = 0 := by
  simp [dropRowZeroX]

@[reassoc (attr := simp)]
private lemma ιTotal_dropRowZeroX_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p (q + 1) (n + 1) h ≫ dropRowZeroX K n =
      (rowsSucc K).ιTotal (ComplexShape.down ℕ) p q n (by simp at h ⊢; omega) := by
  simp only [dropRowZeroX, ι_totalDesc]

private lemma ιTotalOrZero_dropRowZeroX_succ (p q n : ℕ) :
    K.ιTotalOrZero (ComplexShape.down ℕ) p (q + 1) (n + 1) ≫ dropRowZeroX K n =
      (rowsSucc K).ιTotalOrZero (ComplexShape.down ℕ) p q n := by
  by_cases h : p + q = n
  · rw [K.ιTotalOrZero_eq _ _ _ _ (by simp; omega), ιTotal_dropRowZeroX_succ,
      ιTotalOrZero_eq _ _ _ _ _ (by simpa using h)]
  · rw [K.ιTotalOrZero_eq_zero _ _ _ _ (by simp; omega), zero_comp,
      ιTotalOrZero_eq_zero _ _ _ _ _ (by simpa using h)]

private lemma ιTotalOrZero_dropRowZeroX_zero (p n : ℕ) :
    K.ιTotalOrZero (ComplexShape.down ℕ) p 0 (n + 1) ≫ dropRowZeroX K n = 0 := by
  by_cases h : p = n + 1
  · rw [K.ιTotalOrZero_eq _ _ _ _ (by simpa using h), ιTotal_dropRowZeroX_zero]
  · rw [K.ιTotalOrZero_eq_zero _ _ _ _ (by simpa using h), zero_comp]

private lemma d₁_dropRowZeroX_succ (p q n : ℕ) :
    K.d₁ (ComplexShape.down ℕ) p (q + 1) (n + 1) ≫ dropRowZeroX K n =
      (rowsSucc K).d₁ (ComplexShape.down ℕ) p q n := by
  rcases p with _ | p
  · rw [d₁_eq_zero _ _ _ _ _ (by simp), d₁_eq_zero _ _ _ _ _ (by simp), zero_comp]
  · rw [d₁_eq' K _ (ComplexShape.down_mk _ _ rfl), d₁_eq' _ _ (ComplexShape.down_mk _ _ rfl),
      Linear.units_smul_comp, Category.assoc, ιTotalOrZero_dropRowZeroX_succ]
    -- Both signs `ε₁` are `1`, and the horizontal differentials of `rowsSucc K` are those of `K`
    -- by definition.
    rfl

private lemma d₁_dropRowZeroX_zero (p n : ℕ) :
    K.d₁ (ComplexShape.down ℕ) p 0 (n + 1) ≫ dropRowZeroX K n = 0 := by
  rcases p with _ | p
  · rw [d₁_eq_zero _ _ _ _ _ (by simp), zero_comp]
  · rw [d₁_eq' K _ (ComplexShape.down_mk _ _ rfl), Linear.units_smul_comp, Category.assoc,
      ιTotalOrZero_dropRowZeroX_zero, comp_zero, smul_zero]

private lemma d₂_dropRowZeroX_succ (p q n : ℕ) :
    K.d₂ (ComplexShape.down ℕ) p (q + 1) (n + 1) ≫ dropRowZeroX K n =
      (rowsSucc K).d₂ (ComplexShape.down ℕ) p q n := by
  rcases q with _ | q
  · rw [d₂_eq_zero (rowsSucc K) _ _ _ _ (by simp), d₂_eq' K _ _ (ComplexShape.down_mk _ _ rfl),
      Linear.units_smul_comp, Category.assoc, ιTotalOrZero_dropRowZeroX_zero, comp_zero,
      smul_zero]
  · rw [d₂_eq' K _ _ (ComplexShape.down_mk _ _ rfl), d₂_eq' _ _ _ (ComplexShape.down_mk _ _ rfl),
      Linear.units_smul_comp, Category.assoc, ιTotalOrZero_dropRowZeroX_succ]
    simp

/-- The projection killing row `0`, as a chain map out of the total complex restricted to the
degrees `≥ 1`. -/
private noncomputable def dropRowZeroAux :
    (K.total (ComplexShape.down ℕ)).restriction embeddingDownNatSucc ⟶
      (rowsSucc K).total (ComplexShape.down ℕ) where
  f n := dropRowZeroX K n
  comm' := by
    rintro _ n rfl
    refine total.hom_ext _ fun p q h ↦ ?_
    -- The differential of the restriction is that of the total complex in the shifted degrees.
    dsimp only [HomologicalComplex.restriction]
    simp only [embeddingDownNatSucc_f] at h ⊢
    rcases q with _ | q
    · simp only [ιTotal_dropRowZeroX_zero_assoc, zero_comp, total_d, Preadditive.add_comp,
        Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc, d₁_dropRowZeroX_zero,
        d₂_eq_zero _ _ _ _ _ (by simp : ¬ (ComplexShape.down ℕ).Rel 0 _), add_zero]
    · simp only [ιTotal_dropRowZeroX_succ_assoc, total_d, Preadditive.add_comp,
        Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc, ι_D₁, ι_D₂, d₁_dropRowZeroX_succ,
        d₂_dropRowZeroX_succ]

-- Every predecessor of a degree in the image of `embeddingDownNatSucc` is again in the image.
private lemma hasLift_dropRowZeroAux : embeddingDownNatSucc.HasLift (dropRowZeroAux K) :=
  fun j hj ↦ (hj.2 (j + 1) (ComplexShape.down_mk _ _ rfl)).elim

/-- The projection of the total complex onto the total complex of the rows `≥ 1`, placed one
degree higher. -/
private noncomputable def dropRowZero :
    K.total (ComplexShape.down ℕ) ⟶
      ((rowsSucc K).total (ComplexShape.down ℕ)).extend embeddingDownNatSucc :=
  embeddingDownNatSucc.liftExtend (dropRowZeroAux K) (hasLift_dropRowZeroAux K)

private lemma dropRowZero_f_succ (n : ℕ) :
    (dropRowZero K).f (n + 1) =
      dropRowZeroX K n ≫ (extendSuccXIso ((rowsSucc K).total (ComplexShape.down ℕ)) n).inv := by
  rw [dropRowZero, embeddingDownNatSucc.liftExtend_f _ _ (embeddingDownNatSucc_f n)]
  -- The restriction isomorphism is an `eqToHom` between definitionally equal objects.
  exact Category.id_comp _

@[reassoc (attr := simp)]
private lemma rowZeroι_dropRowZero : rowZeroι K ≫ dropRowZero K = 0 := by
  ext (_ | n)
  · exact (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_tgt _ _
  · simp [dropRowZero_f_succ]

/-- The short complex `row 0 ⟶ Tot K ⟶ Tot (rowsSucc K)[1]`. It is an abbreviation so that its
objects are reducibly those of `K`. -/
private noncomputable abbrev rowZeroShortComplex :
    ShortComplex (HomologicalComplex C (ComplexShape.down ℕ)) :=
  ShortComplex.mk (rowZeroι K) (dropRowZero K) (rowZeroι_dropRowZero K)

/-- The retraction of the total complex onto row `0` in degree `n`. -/
private noncomputable def rowZeroπX (n : ℕ) : (K.total (ComplexShape.down ℕ)).X n ⟶ (K.X n).X 0 :=
  K.totalDesc fun p q h ↦ match q, h with
    | 0, h => (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom
    | _ + 1, _ => 0

@[reassoc (attr := simp)]
private lemma ιTotal_rowZeroπX_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p 0 n h ≫ rowZeroπX K n =
      (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom := by
  simp [rowZeroπX]

@[reassoc (attr := simp)]
private lemma ιTotal_rowZeroπX_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.down ℕ) p (q + 1) n h ≫ rowZeroπX K n = 0 := by
  simp [rowZeroπX]

/-- The section of `dropRowZeroX K n`. -/
private noncomputable def dropRowZeroSectionX (n : ℕ) :
    ((rowsSucc K).total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X (n + 1) :=
  (rowsSucc K).totalDesc fun p q h ↦ K.ιTotal (ComplexShape.down ℕ) p (q + 1) (n + 1)
    (by simp at h ⊢; omega)

@[reassoc (attr := simp)]
private lemma ιTotal_dropRowZeroSectionX (p q n : ℕ) (h) :
    (rowsSucc K).ιTotal (ComplexShape.down ℕ) p q n h ≫ dropRowZeroSectionX K n =
      K.ιTotal (ComplexShape.down ℕ) p (q + 1) (n + 1) (by simp at h ⊢; omega) := by
  simp [dropRowZeroSectionX]

@[reassoc (attr := simp)]
private lemma dropRowZeroSectionX_dropRowZeroX (n : ℕ) :
    dropRowZeroSectionX K n ≫ dropRowZeroX K n = 𝟙 _ := by
  ext p q h
  simp

/-- The short complex `rowZeroShortComplex K` in degree `n`, as a short complex in `C`. -/
private noncomputable abbrev rowZeroShortComplexX (n : ℕ) : ShortComplex C :=
  ShortComplex.mk ((rowZeroι K).f n) ((dropRowZero K).f n)
    (by rw [← HomologicalComplex.comp_f, rowZeroι_dropRowZero, HomologicalComplex.zero_f])

/-- The splitting of `rowZeroShortComplex K` in degree `n`: the retraction onto row `0` and, in
positive degrees, the inclusion of the rows `≥ 1`. -/
private noncomputable def rowZeroShortComplexXSplitting (n : ℕ) :
    (rowZeroShortComplexX K n).Splitting :=
  match n with
  | 0 =>
    { r := rowZeroπX K 0
      s := 0
      f_r := by simp
      s_g := (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_src _ _
      id := by
        refine total.hom_ext _ fun p q h ↦ ?_
        obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by simp at h; omega
        simp }
  | n + 1 =>
    { r := rowZeroπX K (n + 1)
      s := (extendSuccXIso ((rowsSucc K).total (ComplexShape.down ℕ)) n).hom ≫
        dropRowZeroSectionX K n
      f_r := by simp
      s_g := by simp [dropRowZero_f_succ]
      id := by
        refine total.hom_ext _ fun p q h ↦ ?_
        rcases q with _ | q
        · obtain rfl : p = n + 1 := by simpa using h
          simp [dropRowZero_f_succ]
        · simp [dropRowZero_f_succ] }

private lemma rowZeroShortComplex_shortExact : (rowZeroShortComplex K).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun n ↦ (rowZeroShortComplexXSplitting K n).shortExact

variable {K} {L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (φ : K ⟶ L)

/-- The map of the bicomplexes of rows `≥ 1` induced by `φ`. -/
private abbrev rowsSuccMap : rowsSucc K ⟶ rowsSucc L where
  f p := { f q := (φ.f p).f (q + 1) }

@[reassoc]
private lemma dropRowZeroX_naturality (n : ℕ) :
    dropRowZeroX K n ≫ (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)).f n =
      (total.map φ (ComplexShape.down ℕ)).f (n + 1) ≫ dropRowZeroX L n := by
  refine total.hom_ext _ fun p q h ↦ ?_
  rcases q with _ | q
  · simp
  · simp only [ιTotal_dropRowZeroX_succ_assoc, ιTotal_map, ιTotal_map_assoc,
      ιTotal_dropRowZeroX_succ]

/-- The map of short complexes induced by `φ`. -/
private noncomputable def rowZeroShortComplexMap :
    rowZeroShortComplex K ⟶ rowZeroShortComplex L where
  τ₁ := ((eval C (ComplexShape.down ℕ) 0).mapHomologicalComplex _).map φ
  τ₂ := total.map φ (ComplexShape.down ℕ)
  τ₃ := extendMap (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)) embeddingDownNatSucc
  comm₁₂ := by
    ext n
    simp
  comm₂₃ := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    rcases n with _ | n
    · exact (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_tgt _ _
    · simp only [HomologicalComplex.comp_f, dropRowZero_f_succ,
        extendMap_f _ embeddingDownNatSucc (embeddingDownNatSucc_f n), Category.assoc,
        Iso.inv_hom_id_assoc]
      rw [dropRowZeroX_naturality_assoc]

open HomologySequence in
/-- If `φ` is a quasi-isomorphism on every row, then `Tot φ` is an isomorphism in homology below
`Q` and an epimorphism in degree `Q`. -/
private lemma total_map_aux (Q : ℕ) :
    ∀ {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (φ : K ⟶ L),
      (∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) →
        (∀ m < Q, IsIso (homologyMap (total.map φ (ComplexShape.down ℕ)) m)) ∧
          Epi (homologyMap (total.map φ (ComplexShape.down ℕ)) Q) := by
  induction Q with
  | zero =>
    intro K L φ hφ
    have : QuasiIso (rowZeroShortComplexMap φ).τ₁ := hφ 0
    refine ⟨fun m hm ↦ (Nat.not_lt_zero m hm).elim, ?_⟩
    exact epi_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
      (rowZeroShortComplex_shortExact L) 0 inferInstance
      ((extend_exactAt _ _ 0 fun _ ↦ by simp).isZero_homology.epi _) (fun k hk ↦ by simp at hk)
  | succ Q ih =>
    intro K L φ hφ
    have : QuasiIso (rowZeroShortComplexMap φ).τ₁ := hφ 0
    -- The rows of `rowsSucc K` are the rows `≥ 1` of `K`.
    obtain ⟨ih₁, ih₂⟩ := ih (rowsSuccMap φ) fun q ↦ hφ (q + 1)
    have hepi (m : ℕ) (hm : m ≤ Q) :
        Epi (homologyMap (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)) m) := by
      rcases hm.lt_or_eq with hm | rfl
      · have := ih₁ m hm
        infer_instance
      · exact ih₂
    refine ⟨fun m hm ↦ ?_, ?_⟩
    · refine isIso_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
        (rowZeroShortComplex_shortExact L) m ?_ inferInstance ?_ fun _ _ ↦ inferInstance
      · rintro i rfl
        exact (epi_homologyMap_extendMap_iff _ (embeddingDownNatSucc_f m)).2 (hepi m (by omega))
      · rcases m with _ | m
        · exact isIso_homologyMap_extendMap_of_forall_ne _ fun _ ↦ by simp
        · have := ih₁ m (by omega)
          rw [← quasiIsoAt_iff_isIso_homologyMap] at this ⊢
          exact (quasiIsoAt_extendMap_iff _ embeddingDownNatSucc (embeddingDownNatSucc_f m)).2 this
    · exact epi_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
        (rowZeroShortComplex_shortExact L) (Q + 1) inferInstance
        ((epi_homologyMap_extendMap_iff _ (embeddingDownNatSucc_f Q)).2 ih₂) fun _ _ ↦ inferInstance

/-- **A map of first-quadrant bicomplexes which is a quasi-isomorphism on every row induces a
quasi-isomorphism of total complexes.** Here the row `q` of a bicomplex `K` is the complex
`⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q` formed by the horizontal differentials. -/
theorem quasiIso_total_map_of_rows
    (hφ : ∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) :
    QuasiIso (total.map φ (ComplexShape.down ℕ)) := by
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (total_map_aux (m + 1) φ hφ).1 m (Nat.lt_succ_self m)

variable {E : ChainComplex C ℕ}

/-- **Exact augmented rows give a quasi-isomorphism from the total complex.** Let `φ` be a map
from a first-quadrant bicomplex `K` to the bicomplex with the single column `E`, that is an
augmentation `K.X 0 ⟶ E` vanishing on the image of `K.d 1 0`. If on every row `q` the map
`⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q` to `E.X q` is a quasi-isomorphism, equivalently the augmented
row `⋯ ⟶ (K.X 0).X q ⟶ E.X q ⟶ 0` is exact, then the induced augmentation of the total complex
is a quasi-isomorphism. -/
theorem quasiIso_totalAugmentation_of_rows
    (φ : K ⟶ (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj E)
    (hφ : ∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) :
    QuasiIso (K.totalAugmentation (φ.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 E).hom)
      (d_comp_f_zero_singleObjXSelf_hom K φ)) := by
  have := quasiIso_total_map_of_rows φ hφ
  have := isIso_totalAugmentation_single E
  rw [← total_map_totalAugmentation_single]
  infer_instance

end HomologicalComplex₂
