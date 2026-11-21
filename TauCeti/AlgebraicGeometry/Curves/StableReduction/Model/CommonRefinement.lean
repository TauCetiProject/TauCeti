/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Closure
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Uniqueness
import TauCeti.AlgebraicGeometry.Compactification.Refinement

/-!
# Common refinements of proper models

Two proper models of the same scheme over the fraction field of a discrete valuation ring
have a common proper model. It is the scheme-theoretic closure of the identified generic fibre
in the fibre product of their total spaces. Its projections respect the prescribed generic-fibre
identifications, not just the isomorphism classes of the generic fibres.

This construction is the common-domination step in comparing regular models: resolving this
closure would give a common regular model. No regularity or resolution is asserted here.
The closure is also universal among models mapping to both given models.

The construction uses `Compactification.toPullback` for the immersion into the fibre product
and `Model.closure` for flatness and the generic-fibre identification.

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

private abbrev compactification (M : Model R K C toK) [M.IsProper] :
    Compactification (toK ≫ Spec.algebraMap R K) :=
  have := M.isOpenImmersion_genericι
  Compactification.ofHom M.genericι M.toBase M.genericι_toBase

private def genericPair (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    C ⟶ pullback M.toBase N.toBase :=
  Compactification.toPullback (compactification M) (compactification N)

-- Identify the opaque compactification construction by its projection equations.
private lemma genericPair_eq_lift (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    genericPair M N = pullback.lift M.genericι N.genericι (by simp) := by
  apply pullback.hom_ext
  · exact (Compactification.toPullback_fst _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (Compactification.toPullback_snd _ _).trans (pullback.lift_snd _ _ _).symm

private def genericDiagonal (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    C ⟶ (genericFiber R K (pullback.fst M.toBase N.toBase ≫ M.toBase)).left :=
  pullback.lift (genericPair M N) toK
    ((Compactification.toPullback_fst_assoc (compactification M) (compactification N)
      M.toBase).trans M.genericι_toBase)

@[reassoc (attr := simp)]
private lemma genericDiagonal_ι (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    genericDiagonal M N ≫ genericFiberι R K (pullback.fst M.toBase N.toBase ≫ M.toBase) =
      genericPair M N :=
  pullback.lift_fst _ _ _

private lemma genericDiagonal_hom (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    genericDiagonal M N ≫ (genericFiber R K
      (pullback.fst M.toBase N.toBase ≫ M.toBase)).hom = toK :=
  pullback.lift_snd _ _ _

private instance (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    IsClosedImmersion (genericDiagonal M N) := by
  have hproper : AlgebraicGeometry.IsProper toK :=
    MorphismProperty.of_isPullback M.isPullback_genericι inferInstance
  have : IsSeparated (genericFiber R K
      (pullback.fst M.toBase N.toBase ≫ M.toBase)).hom := by
    rw [genericFiber_hom]
    infer_instance
  have : IsImmersion (genericPair M N) :=
    inferInstanceAs (IsImmersion (Compactification.toPullback
      (compactification M) (compactification N)))
  have : IsImmersion (genericDiagonal M N ≫
      genericFiberι R K (pullback.fst M.toBase N.toBase ≫ M.toBase)) := by
    rw [genericDiagonal_ι]
    infer_instance
  have := IsImmersion.of_comp (genericDiagonal M N)
    (genericFiberι R K (pullback.fst M.toBase N.toBase ≫ M.toBase))
  have : AlgebraicGeometry.IsProper (genericDiagonal M N ≫ (genericFiber R K
      (pullback.fst M.toBase N.toBase ≫ M.toBase)).hom) := by
    rw [genericDiagonal_hom]
    exact hproper
  have := AlgebraicGeometry.IsProper.of_comp (genericDiagonal M N) (genericFiber R K
    (pullback.fst M.toBase N.toBase ≫ M.toBase)).hom
  exact IsClosedImmersion.of_isPreimmersion _
    (genericDiagonal M N).isClosedMap.isClosed_range

/-- The common refinement of two proper models: the closure of their identified generic fibre
in the fibre product over the discrete valuation ring. -/
def commonRefinement (M N : Model R K C toK) [M.IsProper] [N.IsProper] : Model R K C toK :=
  closure (genericDiagonal M N) (genericDiagonal_hom M N)

/-- The closed immersion of the common refinement into the fibre product of total spaces. -/
def commonRefinementι (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinement M N).total ⟶ pullback M.toBase N.toBase :=
  closureι (genericDiagonal M N) (genericDiagonal_hom M N)

instance (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    IsClosedImmersion (commonRefinementι M N) :=
  inferInstanceAs (IsClosedImmersion (closureι (genericDiagonal M N) (genericDiagonal_hom M N)))

/-- The common refinement is proper over the discrete valuation ring. -/
instance (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinement M N).IsProper :=
  isProper_closure (genericDiagonal M N) (genericDiagonal_hom M N)

/-- The inclusion into the fibre product lies over the DVR. -/
@[reassoc (attr := simp)]
lemma commonRefinementι_toBase (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    commonRefinementι M N ≫ pullback.fst M.toBase N.toBase ≫ M.toBase =
      (commonRefinement M N).toBase :=
  closureι_toBase _ _

/-- On the generic fibre the inclusion is the pair of the chosen generic-fibre inclusions. -/
@[reassoc (attr := simp)]
lemma genericι_commonRefinementι (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinement M N).genericι ≫ commonRefinementι M N =
      pullback.lift M.genericι N.genericι (by simp) := by
  exact (genericι_closureι _ _).trans ((genericDiagonal_ι M N).trans (genericPair_eq_lift M N))

/-- The projection of the common refinement to the first model, fixing the generic fibre. -/
def commonRefinementFst (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    commonRefinement M N ⟶ M :=
  { hom := commonRefinementι M N ≫ pullback.fst M.toBase N.toBase
    overBase := by simp
    genericFiber := baseChangeHom_genericFiberIso_hom_left _ (by simp) (by simp) }

/-- The projection of the common refinement to the second model, fixing the generic fibre. -/
def commonRefinementSnd (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    commonRefinement M N ⟶ N :=
  { hom := commonRefinementι M N ≫ pullback.snd M.toBase N.toBase
    overBase := by rw [Category.assoc, ← pullback.condition]; simp
    genericFiber := baseChangeHom_genericFiberIso_hom_left _
      (by rw [Category.assoc, ← pullback.condition]; simp) (by simp) }

/-- The underlying map of the first projection. -/
@[simp]
lemma commonRefinementFst_hom (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinementFst M N).hom =
      commonRefinementι M N ≫ pullback.fst M.toBase N.toBase :=
  (rfl)

/-- The underlying map of the second projection. -/
@[simp]
lemma commonRefinementSnd_hom (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinementSnd M N).hom =
      commonRefinementι M N ≫ pullback.snd M.toBase N.toBase :=
  (rfl)

private lemma ker_commonRefinementι (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    (commonRefinementι M N).ker = (genericPair M N).ker := by
  exact (ker_closureι _ _).trans (congrArg Scheme.Hom.ker (genericDiagonal_ι M N))

private lemma ker_commonRefinementι_le {M N P : Model R K C toK} [M.IsProper] [N.IsProper]
    (f : P ⟶ M) (g : P ⟶ N) :
    (commonRefinementι M N).ker ≤
      (pullback.lift f.hom g.hom (by simp)).ker := by
  have h : P.genericι ≫ pullback.lift f.hom g.hom (by simp) = genericPair M N := by
    rw [genericPair_eq_lift]
    apply pullback.hom_ext <;> simp
  rw [ker_commonRefinementι, ← h, P.genericι.ker_comp_of_isSchemeTheoreticallyDominant]

/-- The universal morphism to the common refinement from any model mapping to both factors.
The source model need not be proper. -/
def commonRefinementLift {M N P : Model R K C toK} [M.IsProper] [N.IsProper]
    (f : P ⟶ M) (g : P ⟶ N) : P ⟶ commonRefinement M N := by
  let k := IsClosedImmersion.lift (commonRefinementι M N)
    (pullback.lift f.hom g.hom (by simp)) (ker_commonRefinementι_le f g)
  have hk : k ≫ commonRefinementι M N = pullback.lift f.hom g.hom (by simp) :=
    IsClosedImmersion.lift_fac _ _ _
  have hb : k ≫ (commonRefinement M N).toBase = P.toBase := by
    rw [← commonRefinementι_toBase, ← Category.assoc, hk]
    simp
  refine ⟨k, hb, baseChangeHom_genericFiberIso_hom_left _ hb ?_⟩
  rw [← cancel_mono (commonRefinementι M N), Category.assoc, hk,
    genericι_commonRefinementι]
  apply pullback.hom_ext <;> simp

/-- The universal map followed by the first projection is the given first map. -/
@[reassoc (attr := simp)]
lemma commonRefinementLift_fst {M N P : Model R K C toK} [M.IsProper] [N.IsProper]
    (f : P ⟶ M) (g : P ⟶ N) :
    commonRefinementLift f g ≫ commonRefinementFst M N = f :=
  Subsingleton.elim _ _

/-- The universal map followed by the second projection is the given second map. -/
@[reassoc (attr := simp)]
lemma commonRefinementLift_snd {M N P : Model R K C toK} [M.IsProper] [N.IsProper]
    (f : P ⟶ M) (g : P ⟶ N) :
    commonRefinementLift f g ≫ commonRefinementSnd M N = g :=
  Subsingleton.elim _ _

/-- The closure in the fibre product is a categorical product in the category of all models. -/
def isLimitCommonRefinement (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    IsLimit (BinaryFan.mk (commonRefinementFst M N) (commonRefinementSnd M N)) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ commonRefinementLift f g)
    (fun f g ↦ commonRefinementLift_fst f g)
    (fun f g ↦ commonRefinementLift_snd f g)
    (fun {P} _ _ _ _ _ ↦
      (subsingleton_hom (M := P) (N := commonRefinement M N)).elim _ _)

/-- Any two proper models admit a common proper model with morphisms to both. -/
theorem exists_commonRefinement (M N : Model R K C toK) [M.IsProper] [N.IsProper] :
    ∃ (P : Model R K C toK) (_ : P.IsProper), Nonempty (P ⟶ M) ∧ Nonempty (P ⟶ N) :=
  ⟨commonRefinement M N, inferInstance, ⟨commonRefinementFst M N⟩,
    ⟨commonRefinementSnd M N⟩⟩

end TauCeti.Model
