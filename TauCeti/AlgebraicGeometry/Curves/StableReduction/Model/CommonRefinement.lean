/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Closure

/-!
# Common refinements of models

For a separated generic fibre over the fraction field of a discrete valuation ring, the common
refinement of two models is the scheme-theoretic closure of the generic diagonal in the fibre
product of their total spaces. Its projections respect the prescribed generic-fibre
identifications, and it is the categorical product of the models.

If both models are proper, their generic fibre is separated and the common refinement is proper.
This gives the common-domination step in comparing regular proper models; no regularity or
resolution is asserted here.

The construction uses `Model.isPullback_genericι` to identify the generic fibre of the fibre
product and `Model.closure` for flatness and the generic-fibre identification of the closure.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 10, comparison of models.
* The Stacks Project, Section 55.8, Models, and Lemma 38.32.1 (Tag 0ATU), common refinements
  of compactifications.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

private def genericDiagonal (M N : Model R K C toK) :
    C ⟶ (genericFiber R K (pullback.fst M.toBase N.toBase ≫ M.toBase)).left :=
  pullback.lift (pullback.lift M.genericι N.genericι (by simp)) toK (by simp)

@[reassoc]
private lemma genericDiagonal_ι (M N : Model R K C toK) :
    genericDiagonal M N ≫ genericFiberι R K (pullback.fst M.toBase N.toBase ≫ M.toBase) =
      pullback.lift M.genericι N.genericι (by simp) :=
  pullback.lift_fst _ _ _

private lemma genericDiagonal_hom (M N : Model R K C toK) :
    genericDiagonal M N ≫ (genericFiber R K
      (pullback.fst M.toBase N.toBase ≫ M.toBase)).hom = toK :=
  pullback.lift_snd _ _ _

private instance (M N : Model R K C toK) [IsSeparated toK] :
    IsClosedImmersion (genericDiagonal M N) := by
  let p := pullback.fst M.toBase N.toBase
  let q := pullback.snd M.toBase N.toBase
  let i := genericFiberι R K (p ≫ M.toBase)
  let k := (genericFiber R K (p ≫ M.toBase)).hom
  have hp := isPullback_genericFiber R K (p ≫ M.toBase)
  have hq : IsPullback i k (q ≫ N.toBase) (Spec.algebraMap R K) := by
    simpa only [q, ← pullback.condition] using hp
  let a := M.isPullback_genericι.lift (i ≫ p) k (by rw [Category.assoc, hp.w])
  let b := N.isPullback_genericι.lift (i ≫ q) k (by rw [Category.assoc, hq.w])
  have hb : IsPullback i b q N.genericι := hq.of_bot' N.isPullback_genericι
  -- The generic fibre of the product is the product of the two generic fibres over `Spec K`.
  have hab : IsPullback a b toK toK :=
    (IsPullback.of_hasPullback M.toBase N.toBase).paste_twist_right
      M.isPullback_genericι N.genericι toK N.genericι_toBase i b hb
      (by simp [a, p]) (by simp [a, b])
  have hdiag : genericDiagonal M N ≫ hab.isoPullback.hom = pullback.diagonal toK := by
    have := M.isOpenImmersion_genericι
    have := N.isOpenImmersion_genericι
    apply pullback.hom_ext
    · rw [Category.assoc, hab.isoPullback_hom_fst, ← cancel_mono M.genericι]
      simp [a, i, p, genericDiagonal_ι_assoc]
    · rw [Category.assoc, hab.isoPullback_hom_snd, ← cancel_mono N.genericι]
      simp [b, i, q, p, genericDiagonal_ι_assoc]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ hab.isoPullback.hom,
    hdiag]
  infer_instance

section

variable [IsSeparated toK]

/-- The common refinement of two models: the closure of the generic diagonal in the fibre
product over the discrete valuation ring. -/
def commonRefinement (M N : Model R K C toK) : Model R K C toK :=
  closure (genericDiagonal M N) (genericDiagonal_hom M N)

/-- The closed immersion of the common refinement into the fibre product of total spaces. -/
def commonRefinementι (M N : Model R K C toK) :
    (commonRefinement M N).total ⟶ pullback M.toBase N.toBase :=
  closureι (genericDiagonal M N) (genericDiagonal_hom M N)

instance (M N : Model R K C toK) :
    IsClosedImmersion (commonRefinementι M N) :=
  inferInstanceAs (IsClosedImmersion (closureι (genericDiagonal M N) (genericDiagonal_hom M N)))

/-- The common refinement of two proper models is proper over the discrete valuation ring. -/
instance (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinement M N).IsProper :=
  isProper_closure (genericDiagonal M N) (genericDiagonal_hom M N)

/-- The inclusion followed by the first projection lies over the DVR. -/
@[reassoc (attr := simp)]
lemma commonRefinementι_fst_toBase (M N : Model R K C toK) :
    commonRefinementι M N ≫ pullback.fst M.toBase N.toBase ≫ M.toBase =
      (commonRefinement M N).toBase :=
  closureι_toBase _ _

/-- The inclusion followed by the second projection lies over the DVR. -/
@[reassoc (attr := simp)]
lemma commonRefinementι_snd_toBase (M N : Model R K C toK) :
    commonRefinementι M N ≫ pullback.snd M.toBase N.toBase ≫ N.toBase =
      (commonRefinement M N).toBase := by
  rw [← pullback.condition, commonRefinementι_fst_toBase]

/-- On the generic fibre the inclusion is the pair of the chosen generic-fibre inclusions. -/
@[reassoc (attr := simp)]
lemma genericι_commonRefinementι (M N : Model R K C toK) :
    (commonRefinement M N).genericι ≫ commonRefinementι M N =
      pullback.lift M.genericι N.genericι (by simp) :=
  (genericι_closureι _ _).trans (genericDiagonal_ι M N)

/-- The projection of the common refinement to the first model, fixing the generic fibre. -/
def commonRefinementFst (M N : Model R K C toK) :
    commonRefinement M N ⟶ M :=
  { hom := commonRefinementι M N ≫ pullback.fst M.toBase N.toBase
    overBase := by simp
    genericFiber := baseChangeHom_genericFiberIso_hom_left _ (by simp) (by simp) }

/-- The projection of the common refinement to the second model, fixing the generic fibre. -/
def commonRefinementSnd (M N : Model R K C toK) :
    commonRefinement M N ⟶ N :=
  { hom := commonRefinementι M N ≫ pullback.snd M.toBase N.toBase
    overBase := by simp
    genericFiber := baseChangeHom_genericFiberIso_hom_left _ (by simp) (by simp) }

/-- The underlying map of the first projection. -/
@[simp]
lemma commonRefinementFst_hom (M N : Model R K C toK) :
    (commonRefinementFst M N).hom =
      commonRefinementι M N ≫ pullback.fst M.toBase N.toBase :=
  (rfl)

/-- The underlying map of the second projection. -/
@[simp]
lemma commonRefinementSnd_hom (M N : Model R K C toK) :
    (commonRefinementSnd M N).hom =
      commonRefinementι M N ≫ pullback.snd M.toBase N.toBase :=
  (rfl)

/-- The ideal sheaf of the common refinement is the kernel of the generic-fibre pair. -/
@[simp]
lemma ker_commonRefinementι (M N : Model R K C toK) :
    (commonRefinementι M N).ker = (pullback.lift M.genericι N.genericι (by simp)).ker :=
  (ker_closureι _ _).trans (congrArg Scheme.Hom.ker (genericDiagonal_ι M N))

private lemma ker_commonRefinementι_le {M N P : Model R K C toK}
    (f : P ⟶ M) (g : P ⟶ N) :
    (commonRefinementι M N).ker ≤
      (pullback.lift f.hom g.hom (by simp)).ker := by
  have h : P.genericι ≫ pullback.lift (f := M.toBase) (g := N.toBase) f.hom g.hom (by simp) =
      pullback.lift M.genericι N.genericι (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [ker_commonRefinementι, ← h, P.genericι.ker_comp_of_isSchemeTheoreticallyDominant]

/-- The universal morphism to the common refinement from any model mapping to both factors. -/
def commonRefinementLift {M N P : Model R K C toK}
    (f : P ⟶ M) (g : P ⟶ N) : P ⟶ commonRefinement M N := by
  let k := IsClosedImmersion.lift (commonRefinementι M N)
    (pullback.lift f.hom g.hom (by simp)) (ker_commonRefinementι_le f g)
  have hk : k ≫ commonRefinementι M N = pullback.lift f.hom g.hom (by simp) :=
    IsClosedImmersion.lift_fac _ _ _
  have hb : k ≫ (commonRefinement M N).toBase = P.toBase := by
    rw [← commonRefinementι_fst_toBase, ← Category.assoc, hk]
    simp
  refine ⟨k, hb, baseChangeHom_genericFiberIso_hom_left _ hb ?_⟩
  rw [← cancel_mono (commonRefinementι M N), Category.assoc, hk,
    genericι_commonRefinementι]
  apply pullback.hom_ext <;> simp

/-- In the fibre product of total spaces, the universal morphism is the given pair of maps. -/
@[reassoc (attr := simp)]
lemma commonRefinementLift_hom_commonRefinementι {M N P : Model R K C toK}
    (f : P ⟶ M) (g : P ⟶ N) :
    (commonRefinementLift f g).hom ≫ commonRefinementι M N =
      pullback.lift f.hom g.hom (by simp) :=
  IsClosedImmersion.lift_fac _ _ _

/-- The universal map followed by the first projection is the given first map. -/
@[reassoc (attr := simp)]
lemma commonRefinementLift_fst {M N P : Model R K C toK}
    (f : P ⟶ M) (g : P ⟶ N) :
    commonRefinementLift f g ≫ commonRefinementFst M N = f :=
  Hom.ext (by simp)

/-- The universal map followed by the second projection is the given second map. -/
@[reassoc (attr := simp)]
lemma commonRefinementLift_snd {M N P : Model R K C toK}
    (f : P ⟶ M) (g : P ⟶ N) :
    commonRefinementLift f g ≫ commonRefinementSnd M N = g :=
  Hom.ext (by simp)

/-- The closure in the fibre product is a categorical product in the category of all models. -/
def isLimitCommonRefinement (M N : Model R K C toK) :
    IsLimit (BinaryFan.mk (commonRefinementFst M N) (commonRefinementSnd M N)) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ commonRefinementLift f g)
    (fun f g ↦ commonRefinementLift_fst f g)
    (fun f g ↦ commonRefinementLift_snd f g)
    (fun f g m hm₁ hm₂ ↦ by
      apply Hom.ext
      rw [← cancel_mono (commonRefinementι M N)]
      apply pullback.hom_ext
      · simpa using congrArg Hom.hom (hm₁.trans (commonRefinementLift_fst f g).symm)
      · simpa using congrArg Hom.hom (hm₂.trans (commonRefinementLift_snd f g).symm))

/-- Models of a separated generic fibre have binary products given by common refinements. -/
instance : HasBinaryProducts (Model R K C toK) :=
  haveI {M N : Model R K C toK} : HasLimit (pair M N) :=
    ⟨⟨_, isLimitCommonRefinement M N⟩⟩
  hasBinaryProducts_of_hasLimit_pair _

end

/-- Any two proper models admit a common proper model with morphisms to both. -/
theorem exists_isProper_nonempty_hom (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    ∃ (P : Model R K C toK) (_ : P.IsProper), Nonempty (P ⟶ M) ∧ Nonempty (P ⟶ N) := by
  have : IsSeparated toK := MorphismProperty.of_isPullback M.isPullback_genericι inferInstance
  exact ⟨commonRefinement M N, inferInstance, ⟨commonRefinementFst M N⟩,
    ⟨commonRefinementSnd M N⟩⟩

end TauCeti.Model
