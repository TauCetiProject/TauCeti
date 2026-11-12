/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.GlueMorphisms

/-!
# Fibre products of adic spaces are local on the source

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of adic spaces, and let `j i : U i ⟶ X` be open
immersions of adic spaces whose images cover `X`. If every fibre product `U i ×_S Y` exists in the
category `(Adic)` of adic spaces, then so does `X ×_S Y`
(`TauCeti.AdicSpace.hasPullback_of_cover`). This is the reduction step of the existence of fibre
products of adic spaces (Huber 1994, Proposition 3.7; Huber 1996, Proposition 1.2.2) to the case
of an affinoid source, as for schemes (Mathlib's
`AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover`).

## Construction

Write `P i = U i ×_S Y`, with projections `p i : P i ⟶ X` (through `j i`) and `q i : P i ⟶ Y`.
Morphisms from an adic space into `P i` are determined by their composites with `p i` and `q i`,
since `j i` is a monomorphism. The overlap `V i k` is the pullback of the open immersion `j k`
along `p i`, an open subspace of `P i`, and the transition morphism `V i k ⟶ V k i` is induced by
the universal property of `P k`. The gluing axioms are checked after composing with `p` and `q`,
so the `P i` glue along the `V i k` to a pre-adic space, which is an adic space because every
`P i` is (`TauCeti.PreAdicSpace.GlueData.isAdic_glued_iff`). The projections glue to morphisms to
`X` and `Y`.

The universal property is tested against adic spaces `W` only, as the fibre product is taken in
`(Adic)`: since `W` is sheafy, morphisms out of `W` glue along open covers
(`TauCeti.PreAdicSpace.glueMorphisms`). Given `a : W ⟶ X` and `b : W ⟶ Y` over `S`, the
restriction of `W` to `a⁻¹(j i (U i))` maps to `P i`, and these local morphisms agree on overlaps
because they factor through the overlaps `V i k` of the glue data. Uniqueness holds because the
chart `P i` of the glued space is the preimage of `j i (U i)` under the first projection, so any
morphism into the glued space restricts over `a⁻¹(j i (U i))` to a morphism into `P i`.

## Main results

* `TauCeti.AdicSpace.hasPullback_of_cover`: fibre products of adic spaces exist once they exist
  over the members of an open cover of the source.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Proposition 1.2.2.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.6, Theorem 8.56.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace TauCeti.AdicSpace

universe u

open PreAdicSpace (IsOpenImmersion isAdic)

variable {X Y S : AdicSpace.{u}} (f : X ⟶ S) (g : Y ⟶ S) {ι : Type u} {U : ι → AdicSpace.{u}}
  (j : ∀ i, U i ⟶ X) [∀ i, HasPullback (j i ≫ f) g]

namespace PullbackCover

/-- The fibre product `U i ×_S Y`, as a pre-adic space. -/
private noncomputable abbrev P (i : ι) : PreAdicSpace.{u} := (pullback (j i ≫ f) g).obj

/-- The projection `U i ×_S Y ⟶ X`. -/
private noncomputable def p (i : ι) : P f g j i ⟶ X.obj :=
  (pullback.fst (j i ≫ f) g).hom ≫ (j i).hom

/-- The projection `U i ×_S Y ⟶ Y`. -/
private noncomputable def q (i : ι) : P f g j i ⟶ Y.obj :=
  (pullback.snd (j i ≫ f) g).hom

private theorem p_eq (i : ι) : p f g j i = (pullback.fst (j i ≫ f) g).hom ≫ (j i).hom := rfl

private theorem p_comp (i : ι) : p f g j i ≫ f.hom = q f g j i ≫ g.hom := by
  simpa only [p_eq, q, Category.assoc, ObjectProperty.FullSubcategory.comp_hom] using
    congrArg InducedCategory.Hom.hom (pullback.condition (f := j i ≫ f) (g := g))

/-- The morphism from an adic space into `U i ×_S Y` with given components. -/
private noncomputable def liftP {i : ι} {T : PreAdicSpace.{u}} (hT : isAdic T)
    (a : T ⟶ (U i).obj) (b : T ⟶ Y.obj) (h : a ≫ (j i).hom ≫ f.hom = b ≫ g.hom) :
    T ⟶ P f g j i :=
  (pullback.lift (W := (⟨T, hT⟩ : AdicSpace.{u})) (f := j i ≫ f) (g := g)
    (ObjectProperty.homMk a) (ObjectProperty.homMk b) (by ext1; simpa using h)).hom

@[reassoc (attr := simp)]
private theorem liftP_fst {i : ι} {T : PreAdicSpace.{u}} (hT : isAdic T)
    (a : T ⟶ (U i).obj) (b : T ⟶ Y.obj) (h : a ≫ (j i).hom ≫ f.hom = b ≫ g.hom) :
    liftP f g j hT a b h ≫ (pullback.fst (j i ≫ f) g).hom = a := by
  simpa only [liftP, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom] using
    congrArg InducedCategory.Hom.hom (pullback.lift_fst (f := j i ≫ f) (g := g)
    (W := (⟨T, hT⟩ : AdicSpace.{u})) (ObjectProperty.homMk a) (ObjectProperty.homMk b)
    (by ext1; simpa using h))

@[reassoc (attr := simp)]
private theorem liftP_p {i : ι} {T : PreAdicSpace.{u}} (hT : isAdic T)
    (a : T ⟶ (U i).obj) (b : T ⟶ Y.obj) (h : a ≫ (j i).hom ≫ f.hom = b ≫ g.hom) :
    liftP f g j hT a b h ≫ p f g j i = a ≫ (j i).hom := by
  simp [p_eq]

@[reassoc (attr := simp)]
private theorem liftP_q {i : ι} {T : PreAdicSpace.{u}} (hT : isAdic T)
    (a : T ⟶ (U i).obj) (b : T ⟶ Y.obj) (h : a ≫ (j i).hom ≫ f.hom = b ≫ g.hom) :
    liftP f g j hT a b h ≫ q f g j i = b := by
  simpa only [liftP, q, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom] using
    congrArg InducedCategory.Hom.hom (pullback.lift_snd (f := j i ≫ f)
    (g := g) (W := (⟨T, hT⟩ : AdicSpace.{u})) (ObjectProperty.homMk a) (ObjectProperty.homMk b)
    (by ext1; simpa using h))

variable [∀ i, IsOpenImmersion (j i).hom]

/-- Morphisms from an adic space into `U i ×_S Y` are determined by their composites with the
projections to `X` and `Y`, since `j i` is a monomorphism. -/
private theorem P_hom_ext {i : ι} {T : PreAdicSpace.{u}} (hT : isAdic T) {a b : T ⟶ P f g j i}
    (hp : a ≫ p f g j i = b ≫ p f g j i) (hq : a ≫ q f g j i = b ≫ q f g j i) : a = b := by
  have h₁ : a ≫ (pullback.fst (j i ≫ f) g).hom = b ≫ (pullback.fst (j i ≫ f) g).hom :=
    (cancel_mono (j i).hom).1 (by simpa [p] using hp)
  exact congrArg InducedCategory.Hom.hom
    (pullback.hom_ext (W := (⟨T, hT⟩ : AdicSpace.{u})) (k := ObjectProperty.homMk a)
      (l := ObjectProperty.homMk b) (by ext1; simpa using h₁) (by ext1; simpa [q] using hq))

/-- The overlap `V i k`: the open subspace of `U i ×_S Y` lying over `j k (U k)`. -/
private noncomputable abbrev V (i k : ι) : PreAdicSpace.{u} := pullback (p f g j i) (j k).hom

/-- The inclusion of the overlap `V i k` into `U i ×_S Y`. -/
private noncomputable def fV (i k : ι) : V f g j i k ⟶ P f g j i := pullback.fst _ _

private theorem fV_eq (i k : ι) : fV f g j i k = pullback.fst _ _ := rfl

private instance (i k : ι) : IsOpenImmersion (fV f g j i k) := by
  rw [fV_eq]; infer_instance

/-- The overlap `V i k` lies over `j k (U k)`. -/
@[reassoc]
private theorem fV_p (i k : ι) :
    fV f g j i k ≫ p f g j i = pullback.snd (p f g j i) (j k).hom ≫ (j k).hom :=
  pullback.condition

private theorem isAdic_V (i k : ι) : isAdic (V f g j i k) :=
  PreAdicSpace.isAdic_of_isOpenImmersion (pullback (j i ≫ f) g).property (fV f g j i k)

/-- The transition morphism `V i k ⟶ V k i`. -/
private noncomputable def tV (i k : ι) : V f g j i k ⟶ V f g j k i :=
  pullback.lift
    (liftP f g j (isAdic_V f g j i k) (pullback.snd _ _) (pullback.fst _ _ ≫ q f g j i) (by
      rw [← pullback.condition_assoc, Category.assoc, p_comp]))
    (pullback.fst _ _ ≫ (pullback.fst (j i ≫ f) g).hom) (by
      rw [liftP_p, ← fV_p, fV_eq, Category.assoc, ← p_eq])

@[reassoc (attr := simp)]
private theorem tV_fV_p (i k : ι) :
    tV f g j i k ≫ fV f g j k i ≫ p f g j k = fV f g j i k ≫ p f g j i := by
  simp [tV, fV_eq, ← p_eq, pullback.condition]

@[reassoc (attr := simp)]
private theorem tV_fV_q (i k : ι) :
    tV f g j i k ≫ fV f g j k i ≫ q f g j k = fV f g j i k ≫ q f g j i := by
  simp [tV, fV_eq]

/-- The transition morphism on triple overlaps, required by the gluing axioms. -/
private noncomputable def t' (i k l : ι) :
    pullback (fV f g j i k) (fV f g j i l) ⟶ pullback (fV f g j k l) (fV f g j k i) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ tV f g j i k ≫ fV f g j k i)
      (pullback.snd _ _ ≫ pullback.snd _ _) (by
        rw [Category.assoc, Category.assoc, tV_fV_p, pullback.condition_assoc, fV_p,
          Category.assoc]))
    (pullback.fst _ _ ≫ tV f g j i k) (by simp [fV_eq])

@[reassoc (attr := simp)]
private theorem t'_snd (i k l : ι) :
    t' f g j i k l ≫ pullback.snd _ _ = pullback.fst _ _ ≫ tV f g j i k := by
  simp [t']

@[reassoc (attr := simp)]
private theorem t'_fst_fV (i k l : ι) :
    t' f g j i k l ≫ pullback.fst _ _ ≫ fV f g j k l =
      pullback.fst _ _ ≫ tV f g j i k ≫ fV f g j k i := by
  simp only [t', pullback.lift_fst_assoc]
  exact pullback.lift_fst _ _ _

private instance (i : ι) : IsIso (fV f g j i i) := by
  rw [fV_eq]
  exact pullback_snd_iso_of_left_factors_mono (pullback.fst (j i ≫ f) g).hom (j i).hom

/-- The glue data of the fibre products `U i ×_S Y` along the overlaps `V i k`. -/
private noncomputable def glueData : PreAdicSpace.GlueData.{u} where
  J := ι
  U := P f g j
  V ik := V f g j ik.1 ik.2
  f := fV f g j
  f_mono _ _ := inferInstance
  f_hasPullback _ _ _ := inferInstance
  f_id _ := inferInstance
  t := tV f g j
  t_id i := by
    rw [← cancel_mono (fV f g j i i)]
    exact P_hom_ext f g j (isAdic_V f g j i i) (by simp) (by simp)
  t' := t' f g j
  t_fac := t'_snd f g j
  cocycle i k l := by
    rw [← cancel_mono (pullback.fst (fV f g j i k) (fV f g j i l) ≫ fV f g j i k)]
    refine P_hom_ext f g j (PreAdicSpace.isAdic_of_isOpenImmersion (isAdic_V f g j i k)
      (pullback.fst (fV f g j i k) (fV f g j i l))) ?_ ?_ <;> simp
  f_open _ _ := inferInstance

/-- The glued space. -/
private noncomputable abbrev G : PreAdicSpace.{u} := (glueData f g j).toGlueData.glued

/-- The chart `U i ×_S Y ⟶ G` of the glued space. -/
private noncomputable def ιP (i : ι) : P f g j i ⟶ G f g j := (glueData f g j).toGlueData.ι i

private theorem ιP_eq (i : ι) :
    ιP f g j i = Multicoequalizer.π (glueData f g j).toGlueData.diagram i := rfl

private instance (i : ι) : IsOpenImmersion (ιP f g j i) :=
  (glueData f g j).ι_isOpenImmersion i

@[reassoc]
private theorem glue_condition (i k : ι) :
    tV f g j i k ≫ fV f g j k i ≫ ιP f g j k = fV f g j i k ≫ ιP f g j i :=
  (glueData f g j).toGlueData.glue_condition i k

private theorem ιP_jointly_surjective (z : G f g j) :
    ∃ (i : ι) (y : P f g j i), (ιP f g j i).base y = z :=
  (glueData f g j).ι_jointly_surjective z

/-- The first projection of the glued space, glued from the `p i`. -/
private noncomputable def πX : G f g j ⟶ X.obj :=
  Multicoequalizer.desc (glueData f g j).toGlueData.diagram _ (p f g j) fun ik ↦
    (tV_fV_p f g j ik.1 ik.2).symm

/-- The second projection of the glued space, glued from the `q i`. -/
private noncomputable def πY : G f g j ⟶ Y.obj :=
  Multicoequalizer.desc (glueData f g j).toGlueData.diagram _ (q f g j) fun ik ↦
    (tV_fV_q f g j ik.1 ik.2).symm

@[reassoc (attr := simp)]
private theorem ιP_πX (i : ι) : ιP f g j i ≫ πX f g j = p f g j i := by
  rw [ιP_eq]
  exact Multicoequalizer.π_desc _ _ _ _ _

@[reassoc (attr := simp)]
private theorem ιP_πY (i : ι) : ιP f g j i ≫ πY f g j = q f g j i := by
  rw [ιP_eq]
  exact Multicoequalizer.π_desc _ _ _ _ _

private theorem πX_comp : πX f g j ≫ f.hom = πY f g j ≫ g.hom :=
  Multicoequalizer.hom_ext _ _ _ fun (i : ι) ↦ by
    rw [← ιP_eq f g j i]
    exact (ιP_πX_assoc f g j i f.hom).trans
      ((p_comp f g j i).trans (ιP_πY_assoc f g j i g.hom).symm)

/-- Morphisms from an adic space into `U i ×_S Y` and `U k ×_S Y` with the same projections to
`X` and `Y` have the same image in the glued space: they factor through the overlap `V i k`. -/
private theorem comp_ιP_eq {i k : ι} {T : PreAdicSpace.{u}} (hT : isAdic T)
    (m : T ⟶ P f g j i) (m' : T ⟶ P f g j k)
    (hp : m ≫ p f g j i = m' ≫ p f g j k) (hq : m ≫ q f g j i = m' ≫ q f g j k) :
    m ≫ ιP f g j i = m' ≫ ιP f g j k := by
  let n : T ⟶ V f g j i k :=
    pullback.lift m (m' ≫ (pullback.fst (j k ≫ f) g).hom) (by rw [hp, p_eq, Category.assoc])
  have hn : n ≫ fV f g j i k = m := pullback.lift_fst _ _ _
  have hn' : n ≫ tV f g j i k ≫ fV f g j k i = m' :=
    P_hom_ext f g j hT (by rw [Category.assoc, Category.assoc, tV_fV_p, ← hp, ← hn,
      Category.assoc]) (by rw [Category.assoc, Category.assoc, tV_fV_q, ← hq, ← hn,
      Category.assoc])
  rw [← hn, ← hn']
  simp only [Category.assoc, glue_condition]

/-- The chart `U i ×_S Y` of the glued space contains every point lying over `j i (U i)`. -/
private theorem mem_range_ιP {i : ι} (z : G f g j)
    (hz : (πX f g j).base z ∈ Set.range (j i).hom.base) : z ∈ Set.range (ιP f g j i).base := by
  obtain ⟨k, y, rfl⟩ := ιP_jointly_surjective f g j z
  have hy : (p f g j k).base y ∈ Set.range (j i).hom.base := by
    rw [← ιP_πX]
    exact hz
  obtain ⟨v, rfl⟩ : y ∈ Set.range (fV f g j k i).base := by
    rw [fV_eq, PreAdicSpace.IsOpenImmersion.range_pullback_fst_of_right]
    exact hy
  refine ⟨(fV f g j i k).base ((tV f g j k i).base v), ?_⟩
  exact ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.base) (glue_condition f g j k i)) v

/-- The open of a pre-adic space `W` lying over `j i (U i)` under `a : W ⟶ X`. -/
private def O {W : PreAdicSpace.{u}} (a : W ⟶ X.obj) (i : ι) : Opens W :=
  (Opens.map a.base).obj ⟨_, (j i).hom.isOpenEmbedding.isOpenMap.isOpen_range⟩

private theorem iSup_O (hj : ∀ x : X.obj, ∃ (i : ι) (y : (U i).obj), (j i).hom.base y = x)
    {W : PreAdicSpace.{u}} (a : W ⟶ X.obj) : ⨆ i, O j a i = ⊤ :=
  top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr (let ⟨i, y, hy⟩ := hj (a.base x); ⟨i, y, hy⟩)

private theorem range_O {W : PreAdicSpace.{u}} (a : W ⟶ X.obj) (i : ι) :
    Set.range (W.ofRestrict (O j a i).isOpenEmbedding ≫ a).base ⊆ Set.range (j i).hom.base := by
  rintro _ ⟨y, rfl⟩
  exact y.2

variable {f g j}

/-- Morphisms from an adic space into the glued space are determined by their composites with the
two projections. -/
private theorem G_hom_ext (hj : ∀ x : X.obj, ∃ (i : ι) (y : (U i).obj), (j i).hom.base y = x)
    {W : PreAdicSpace.{u}} (hW : isAdic W) {l l' : W ⟶ G f g j}
    (hX : l ≫ πX f g j = l' ≫ πX f g j) (hY : l ≫ πY f g j = l' ≫ πY f g j) : l = l' := by
  let O := O j (l ≫ πX f g j)
  refine PreAdicSpace.hom_ext_of_ofRestrict hW.isSheafy O (iSup_O j hj _) fun i ↦ ?_
  have hR (l₀ : W ⟶ G f g j) (h₀ : l₀ ≫ πX f g j = l ≫ πX f g j) :
      Set.range (W.ofRestrict (O i).isOpenEmbedding ≫ l₀).base ⊆
        Set.range (ιP f g j i).base := by
    rintro _ ⟨y, rfl⟩
    have hy := range_O j (l ≫ πX f g j) i ⟨y, rfl⟩
    have e := congrArg (fun φ ↦ (W.ofRestrict (O i).isOpenEmbedding ≫ φ).base y) h₀
    exact mem_range_ιP f g j _ (e.symm ▸ hy)
  have hWi : isAdic (W.restrict (O i).isOpenEmbedding) := PreAdicSpace.isAdic_restrict _ hW
  obtain ⟨m, hm⟩ : ∃ m, m ≫ ιP f g j i = W.ofRestrict (O i).isOpenEmbedding ≫ l :=
    ⟨_, PreAdicSpace.IsOpenImmersion.lift_fac _ _ (hR l rfl)⟩
  obtain ⟨m', hm'⟩ : ∃ m', m' ≫ ιP f g j i = W.ofRestrict (O i).isOpenEmbedding ≫ l' :=
    ⟨_, PreAdicSpace.IsOpenImmersion.lift_fac _ _ (hR l' hX.symm)⟩
  have hmm : m = m' := P_hom_ext f g j hWi
    (by rw [← ιP_πX, reassoc_of% hm, reassoc_of% hm', hX])
    (by rw [← ιP_πY, reassoc_of% hm, reassoc_of% hm', hY])
  rw [← hm, ← hm', hmm]

section Lift

variable (hj : ∀ x : X.obj, ∃ (i : ι) (y : (U i).obj), (j i).hom.base y = x)
  {W : PreAdicSpace.{u}} (hW : isAdic W) (a : W ⟶ X.obj) (b : W ⟶ Y.obj)
  (h : a ≫ f.hom = b ≫ g.hom)

/-- Over the open `a⁻¹(j i (U i))`, a cone from an adic space `W` maps to `U i ×_S Y`. -/
private noncomputable def liftO (i : ι) : W.restrict (O j a i).isOpenEmbedding ⟶ P f g j i :=
  liftP f g j (PreAdicSpace.isAdic_restrict _ hW)
    (PreAdicSpace.IsOpenImmersion.lift (j i).hom _ (range_O j a i))
    (W.ofRestrict (O j a i).isOpenEmbedding ≫ b) (by
      rw [PreAdicSpace.IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, h])

@[reassoc]
private theorem liftO_p (i : ι) :
    liftO hW a b h i ≫ p f g j i = W.ofRestrict (O j a i).isOpenEmbedding ≫ a := by
  simp [liftO]

@[reassoc]
private theorem liftO_q (i : ι) :
    liftO hW a b h i ≫ q f g j i = W.ofRestrict (O j a i).isOpenEmbedding ≫ b := by
  simp [liftO]

include hW in
/-- The local morphisms `liftO` agree on the overlaps. -/
private theorem liftO_compatible (i k : ι) :
    pullback.fst (W.ofRestrict (O j a i).isOpenEmbedding)
        (W.ofRestrict (O j a k).isOpenEmbedding) ≫ liftO hW a b h i ≫ ιP f g j i =
      pullback.snd _ _ ≫ liftO hW a b h k ≫ ιP f g j k := by
  rw [← Category.assoc, ← Category.assoc]
  exact comp_ιP_eq f g j (PreAdicSpace.isAdic_of_isOpenImmersion
      (PreAdicSpace.isAdic_restrict _ hW) (pullback.fst (W.ofRestrict (O j a i).isOpenEmbedding)
        (W.ofRestrict (O j a k).isOpenEmbedding))) _ _
    (by rw [Category.assoc, Category.assoc, liftO_p, liftO_p, pullback.condition_assoc])
    (by rw [Category.assoc, Category.assoc, liftO_q, liftO_q, pullback.condition_assoc])

/-- The morphism from an adic space into the glued space induced by a cone over `f` and `g`,
glued from the local morphisms `liftO`. -/
private noncomputable def lift : W ⟶ G f g j :=
  PreAdicSpace.glueMorphisms hW.isSheafy (O j a) (iSup_O j hj a)
    (fun i ↦ liftO hW a b h i ≫ ιP f g j i) (liftO_compatible hW a b h)

private theorem lift_πX : lift hj hW a b h ≫ πX f g j = a :=
  PreAdicSpace.hom_ext_of_ofRestrict hW.isSheafy (O j a) (iSup_O j hj a) fun i ↦ by
    rw [lift, PreAdicSpace.ofRestrict_glueMorphisms_assoc, Category.assoc, ιP_πX, liftO_p]

private theorem lift_πY : lift hj hW a b h ≫ πY f g j = b :=
  PreAdicSpace.hom_ext_of_ofRestrict hW.isSheafy (O j a) (iSup_O j hj a) fun i ↦ by
    rw [lift, PreAdicSpace.ofRestrict_glueMorphisms_assoc, Category.assoc, ιP_πY, liftO_q]

end Lift

variable (f g j) in
/-- The glued space, as an adic space. -/
private noncomputable abbrev Gadic : AdicSpace.{u} :=
  ⟨G f g j, (glueData f g j).isAdic_glued_iff.mpr fun (i : ι) ↦ (pullback (j i ≫ f) g).property⟩

/-- The glued space with its two projections is a fibre product in `(Adic)`. -/
private noncomputable def isLimit
    (hj : ∀ x : X.obj, ∃ (i : ι) (y : (U i).obj), (j i).hom.base y = x) :
    IsLimit (PullbackCone.mk (W := Gadic f g j) (ObjectProperty.homMk (πX f g j))
      (ObjectProperty.homMk (πY f g j)) (by ext1; exact πX_comp f g j) : PullbackCone f g) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ ObjectProperty.homMk (lift hj s.pt.property s.fst.hom s.snd.hom
      (congrArg InducedCategory.Hom.hom s.condition)))
    (fun s ↦ by ext1; exact lift_πX hj s.pt.property s.fst.hom s.snd.hom _)
    (fun s ↦ by ext1; exact lift_πY hj s.pt.property s.fst.hom s.snd.hom _)
    (fun s m h₁ h₂ ↦ by
      ext1
      exact G_hom_ext (l := m.hom) hj s.pt.property
        ((congrArg InducedCategory.Hom.hom h₁).trans
          (lift_πX hj s.pt.property s.fst.hom s.snd.hom _).symm)
        ((congrArg InducedCategory.Hom.hom h₂).trans
          (lift_πY hj s.pt.property s.fst.hom s.snd.hom _).symm))

end PullbackCover

variable [∀ i, IsOpenImmersion (j i).hom]

/-- **Fibre products of adic spaces are local on the source.** Let `f : X ⟶ S` and `g : Y ⟶ S`
be morphisms of adic spaces and `j i : U i ⟶ X` open immersions whose images cover `X`. If every
fibre product `U i ×_S Y` exists in the category `(Adic)` of adic spaces, then so does `X ×_S Y`:
the `U i ×_S Y` glue along their open subspaces lying over `j k (U k)`. -/
theorem hasPullback_of_cover
    (hj : ∀ x : X.obj, ∃ (i : ι) (y : (U i).obj), (j i).hom.base y = x) : HasPullback f g :=
  ⟨⟨⟨_, PullbackCover.isLimit hj⟩⟩⟩

end TauCeti.AdicSpace
