/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Reduced
import TauCeti.AlgebraicGeometry.RationalPoint.Dense

/-!
# Zariski closures of subgroups of rational points

Over a perfect field, the Zariski closure of a subgroup of rational points of a group scheme
has a canonical reduced closed subgroup scheme structure.
For an abelian variety, this construction applies to the prime-to-characteristic torsion
subgroup and makes it possible to compare torsion inside the closure with ambient torsion.
The affine counterpart is `TauCeti.HopfIdeal.vanishingIdeal`.

## References

* J. S. Milne, *Algebraic Groups* (2022), Corollary 1.46 and Definition 1.48.
* J. S. Milne, *Abelian Varieties* (2022), §12, the lemma on density of prime-to-characteristic
  torsion.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonoidalCategory TopologicalSpace
open scoped MonObj

namespace TauCeti.ClosedSubgroupScheme

open GroupScheme

universe u

variable {K : Type u} [Field K] {G : Grp (Over (Spec (.of K)))}

private instance : IsReduced (𝟙_ (Over (Spec (.of K)))).left :=
  inferInstanceAs (IsReduced (Spec (.of K)))

private instance : Subsingleton (𝟙_ (Over (Spec (.of K)))).left :=
  inferInstanceAs (Subsingleton (Spec (.of K)))

private abbrev pointValue {X : Over (Spec (.of K))} (p : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    X.left :=
  p.left (IsLocalRing.closedPoint K)

private theorem pointValue_comp {X Y : Over (Spec (.of K))}
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ X) (f : X ⟶ Y) :
    pointValue (p ≫ f) = f.left (pointValue p) :=
  (rfl)

private abbrev pointClosure (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) : Closeds G.X.left :=
  ⟨closure (pointValue '' (H : Set _)), isClosed_closure⟩

private abbrev closureIdeal (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    G.X.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (pointClosure H)

private abbrev closureOver (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    Over (Spec (.of K)) :=
  Over.mk ((closureIdeal H).subschemeι ≫ G.X.hom)

private abbrev closureInclusion (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    closureOver H ⟶ G.X :=
  Over.homMk (closureIdeal H).subschemeι (by rfl)

private instance (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    IsClosedImmersion (closureInclusion H).left :=
  inferInstanceAs (IsClosedImmersion (closureIdeal H).subschemeι)

private instance (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    IsReduced (closureOver H).left :=
  inferInstanceAs (IsReduced (closureIdeal H).subscheme)

private theorem ker_closureInclusion (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    (closureInclusion H).left.ker = closureIdeal H :=
  (closureIdeal H).ker_subschemeι

private theorem range_closureInclusion (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    Set.range (closureInclusion H).left = (pointClosure H : Set G.X.left) := by
  exact (closureIdeal H).range_subschemeι.trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal (pointClosure H))

private theorem point_mem_closure {H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)}
    {p : 𝟙_ (Over (Spec (.of K))) ⟶ G.X} (hp : p ∈ H) :
    pointValue p ∈ pointClosure H :=
  subset_closure ⟨p, hp, rfl⟩

private theorem exists_point_lift (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X))
    {p : 𝟙_ (Over (Spec (.of K))) ⟶ G.X}
    (hp : pointValue p ∈ pointClosure H) :
    ∃ q, q ≫ closureInclusion H = p := by
  have hker : (closureInclusion H).left.ker ≤ p.left.ker := by
    rw [ker_closureInclusion]
    refine Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset _ ?_
    rintro _ ⟨x, rfl⟩
    exact Subsingleton.elim (IsLocalRing.closedPoint K : (𝟙_ (Over (Spec (.of K)))).left) x ▸ hp
  exact ⟨closedImmersionOverLift (closureInclusion H) p hker,
    closedImmersionOverLift_comp (closureInclusion H) p hker⟩

private theorem dense_liftedPoints (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X)) :
    Dense (pointValue '' {q | q ≫ closureInclusion H ∈ H}) := by
  let i := (closureInclusion H).left
  have himage : i '' (pointValue '' {q | q ≫ closureInclusion H ∈ H}) =
      pointValue '' (H : Set _) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q ≫ closureInclusion H, hq, pointValue_comp _ _⟩
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨q, rfl⟩ := exists_point_lift H (point_mem_closure hp)
      exact ⟨_, ⟨q, hp, rfl⟩, (pointValue_comp _ _).symm⟩
  rw [dense_iff_closure_eq,
    (IsClosedImmersion.isClosedEmbedding i).isEmbedding.closure_eq_preimage_closure_image,
    himage]
  apply Set.eq_univ_of_forall
  intro x
  have hx := Set.mem_range_self (f := i) x
  rw [range_closureInclusion H] at hx
  exact hx

variable (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ G.X))

private theorem ker_closureInclusion_le_one : (closureInclusion H).left.ker ≤ η[G.X].left.ker := by
  rw [ker_closureInclusion]
  apply Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x (IsLocalRing.closedPoint K), MonObj.one_eq_one]
  exact point_mem_closure (H := H) H.one_mem

private theorem ker_closureInclusion_le_inv :
    (closureInclusion H).left.ker ≤ (closureInclusion H ≫ ι[G.X]).left.ker := by
  rw [ker_closureInclusion]
  apply Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset
  rintro _ ⟨x, rfl⟩
  exact (dense_liftedPoints H).induction
    (by
      rintro _ ⟨q, hq, rfl⟩
      rw [← pointValue_comp, ← Category.assoc, ← Hom.inv_def]
      exact point_mem_closure (H.inv_mem hq))
    ((pointClosure H).isClosed.preimage (closureInclusion H ≫ ι[G.X]).left.continuous) x

variable [PerfectField K]

private theorem ker_closureInclusion_le_mul :
    (closureInclusion H).left.ker ≤
      ((closureInclusion H ⊗ₘ closureInclusion H) ≫ μ[G.X]).left.ker := by
  rw [ker_closureInclusion]
  have : IsReduced (closureOver H ⊗ closureOver H).left := by
    rw [Over.tensorObj_left]
    infer_instance
  apply Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset
  rintro _ ⟨x, rfl⟩
  have hd := Over.dense_image_lift_of_dense (dense_liftedPoints H) (dense_liftedPoints H)
  exact hd.induction
    (by
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      rw [← pointValue_comp, lift_map_assoc, ← Hom.mul_def]
      exact point_mem_closure (H.mul_mem ha hb))
    ((pointClosure H).isClosed.preimage
      ((closureInclusion H ⊗ₘ closureInclusion H) ≫ μ[G.X]).left.continuous) x

private abbrev closureGrpObj : GrpObj (closureOver H) :=
  grpObjOfClosedImmersion (closureInclusion H) (ker_closureInclusion_le_one H)
    (ker_closureInclusion_le_mul H) (ker_closureInclusion_le_inv H)

private def closureGrp : Grp (Over (Spec (.of K))) :=
  letI := closureGrpObj H
  Grp.mk (closureOver H)

private def closureHom : closureGrp H ⟶ G :=
  letI := closureGrpObj H
  haveI : IsMonHom (closureInclusion H) := isMonHom_grpObjOfClosedImmersion (closureInclusion H)
    (ker_closureInclusion_le_one H) (ker_closureInclusion_le_mul H) (ker_closureInclusion_le_inv H)
  Grp.ofHom (closureInclusion H)

private instance : IsClosedImmersion (closureHom H).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (closureInclusion H).left)

/-- The reduced closed subgroup scheme whose support is the Zariski closure of a subgroup of
rational points. -/
def ofPointSubgroup : ClosedSubgroupScheme G :=
  ClosedSubgroupScheme.mk (closureHom H)

private def closureIso : ((ofPointSubgroup H).val : Grp (Over (Spec (.of K)))) ≅ closureGrp H :=
  ClosedSubgroupScheme.mkIso (closureHom H)

private def closureSchemeIso : ((ofPointSubgroup H).val : Grp (Over (Spec (.of K)))).X.left ≅
    (closureOver H).left :=
  ((Grp.forget _) ⋙ Over.forget _).mapIso (closureIso H)

private theorem closureSchemeIso_inv_comp_arrow :
    (closureSchemeIso H).inv ≫ (ofPointSubgroup H).val.arrow.hom.hom.left =
      (closureInclusion H).left :=
  congrArg (fun f ↦ f.hom.hom.left) (ClosedSubgroupScheme.mkIso_inv_comp_arrow (closureHom H))

/-- The image of the closure subgroup scheme in the ambient scheme is the closure of the
underlying points of the given subgroup. -/
@[simp]
theorem range_ofPointSubgroup_arrow :
    Set.range (ofPointSubgroup H).val.arrow.hom.hom.left =
      closure ((fun p : 𝟙_ (Over (Spec (.of K))) ⟶ G.X ↦ p.left (IsLocalRing.closedPoint K)) ''
        (H : Set _)) := by
  let i := (ofPointSubgroup H).val.arrow.hom.hom.left
  let e := closureSchemeIso H
  calc
    Set.range i = Set.range (i ∘ e.inv) := (e.inv.surjective.range_comp i).symm
    _ = Set.range (closureInclusion H).left :=
      congrArg (fun f : (closureOver H).left ⟶ G.X.left ↦ Set.range f)
        (closureSchemeIso_inv_comp_arrow H)
    _ = _ := range_closureInclusion H

/-- The Zariski closure of a point subgroup has reduced underlying scheme. -/
instance isReduced_ofPointSubgroup :
    IsReduced (((ofPointSubgroup H).val : Grp (Over (Spec (.of K)))).X.left) := by
  let e := closureSchemeIso H
  have : IsIso e.hom := inferInstance
  exact isReduced_of_isOpenImmersion e.hom

/-- The closure subgroup scheme is locally of finite type over the field. -/
instance locallyOfFiniteType_ofPointSubgroup [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (((ofPointSubgroup H).val : Grp (Over (Spec (.of K)))).X.hom) := by
  rw [← Over.w (ofPointSubgroup H).val.arrow.hom.hom]
  infer_instance

/-- The Zariski closure of a point subgroup is smooth over the field. -/
instance smooth_ofPointSubgroup [LocallyOfFiniteType G.X.hom] :
    Smooth (((ofPointSubgroup H).val : Grp (Over (Spec (.of K)))).X.hom) :=
  GroupScheme.smooth_of_isReduced _

/-- The closure subgroup of a proper group scheme is proper over the field. -/
instance isProper_ofPointSubgroup [IsProper G.X.hom] :
    IsProper (((ofPointSubgroup H).val : Grp (Over (Spec (.of K)))).X.hom) := by
  rw [← Over.w (ofPointSubgroup H).val.arrow.hom.hom]
  infer_instance

/-- A rational point factors through the closure subgroup if and only if its underlying point
lies in the Zariski closure. -/
theorem exists_comp_ofPointSubgroup_arrow_iff {p : 𝟙_ (Over (Spec (.of K))) ⟶ G.X} :
    (∃ q, q ≫ (ofPointSubgroup H).val.arrow.hom.hom = p) ↔
      p.left (IsLocalRing.closedPoint K) ∈
        closure ((fun a : 𝟙_ (Over (Spec (.of K))) ⟶ G.X ↦ a.left (IsLocalRing.closedPoint K)) ''
          (H : Set _)) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact range_ofPointSubgroup_arrow H ▸ ⟨pointValue q, (pointValue_comp _ _).symm⟩
  · intro hp
    obtain ⟨q, hq⟩ := exists_point_lift H hp
    refine ⟨q ≫ (closureIso H).inv.hom.hom, ?_⟩
    have h := congrArg (fun f ↦ f.hom.hom)
      (ClosedSubgroupScheme.mkIso_inv_comp_arrow (closureHom H))
    rw [Grp.comp_hom_hom] at h
    exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) h).trans hq)

/-- The closure subgroup is the least closed subgroup scheme whose support contains the
underlying points of the given subgroup. The competing subgroup scheme can have nilpotents. -/
theorem ofPointSubgroup_le_iff (P : ClosedSubgroupScheme G) :
    (ofPointSubgroup H).val ≤ P.val ↔ ∀ p ∈ H,
      p.left (IsLocalRing.closedPoint K) ∈ Set.range P.val.arrow.hom.hom.left := by
  constructor
  · intro h p hp
    let g := Subobject.ofLE _ _ h
    obtain ⟨q, hq⟩ := (exists_comp_ofPointSubgroup_arrow_iff H).2 (point_mem_closure hp)
    refine ⟨pointValue (q ≫ g.hom.hom), ?_⟩
    have hg := congrArg (fun f ↦ f.hom.hom) (Subobject.ofLE_arrow h)
    rw [Grp.comp_hom_hom] at hg
    rw [← pointValue_comp, Category.assoc, hg, hq]
  · intro h
    let i := P.val.arrow.hom.hom
    have hi : (pointClosure H : Set G.X.left) ⊆ Set.range i.left :=
      closure_minimal (by rintro _ ⟨p, hp, rfl⟩; exact h p hp)
        (IsClosedImmersion.isClosedEmbedding i.left).isClosed_range
    have hker : i.left.ker ≤ (closureInclusion H).left.ker := by
      rw [ker_closureInclusion]
      refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp ?_
      apply SetLike.coe_subset_coe.mp
      rwa [Scheme.Hom.support_ker,
        (IsClosedImmersion.isClosedEmbedding i.left).isClosed_range.closure_eq]
    let f := closedImmersionOverLift i (closureHom H).hom.hom hker
    have hf : f ≫ i = (closureHom H).hom.hom := closedImmersionOverLift_comp _ _ _
    have : Mono i := Over.mono_of_mono_left i
    have : IsMonHom f := by
      constructor <;> rw [← cancel_mono i] <;>
        simp only [Category.assoc, IsMonHom.one_hom, IsMonHom.mul_hom,
          tensorHom_comp_tensorHom_assoc, hf]
    rw [ofPointSubgroup, coe_mk]
    exact Subobject.mk_le_of_comm (Grp.homMk (A := closureGrp H) f) (by ext1; exact hf)

end TauCeti.ClosedSubgroupScheme
