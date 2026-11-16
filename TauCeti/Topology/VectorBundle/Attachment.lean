/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Attach
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import TauCeti.Analysis.Normed.Module.Ball.Radial.Push
import TauCeti.Topology.ContinuousMap.Sigma
import TauCeti.Topology.Homotopy.Sigma
import TauCeti.Topology.VectorBundle.Smul

/-!
# Attaching disc bundles

Let `E → B` be a real vector bundle whose fibre norm is continuous on the total space, with unit
disc bundle `D(E)` and unit sphere bundle `S(E)` (`TauCeti.discBundle`, `TauCeti.sphereBundle`).
Say that a space `Z` is obtained from a closed subset `X` by attaching `D(E)` along `S(E)` through
a map of pairs `f : (D(E), S(E)) ⟶ (Z, X)` when `f` is a closed embedding of `D(E)` into `Z`
whose image meets `X` exactly in the image of `S(E)`, and `X` together with the image of `f` is
all of `Z`. Then `f` induces isomorphisms on relative singular homology and cohomology, with
arbitrary coefficients, in every degree (`TauCeti.isIso_singularHomologyMap_of_attach_discBundle`
and `TauCeti.isIso_singularCohomologyMap_of_attach_discBundle`). Together with the comparison of
the disc-sphere pair with the Thom pair (`TauCeti.isIso_singularHomologyMap_discSpherePairMap` and
`TauCeti.isIso_singularCohomologyMap_discSpherePairMap`), the relative homology and cohomology of
`(Z, X)` are those of the Thom pair `(E, E₀)`.

The same holds for finitely many disc bundles attached at once, along closed embeddings with
pairwise disjoint images, the bundles having possibly different bases and ranks: the relative
homology of `(Z, X)` is the coproduct of the relative homologies of the disc-sphere pairs
(`TauCeti.isColimitCofanSingularHomologyOfAttachDiscBundle`), and its relative cohomology is their
product (`TauCeti.isLimitFanSingularCohomologyOfAttachDiscBundle`), the structure maps being
induced by the attaching maps.

This is how attachments of disc bundles are seen by homology. For instance, crossing a critical
level of a Morse–Bott function attaches, up to homotopy, the negative disc bundle of each critical
submanifold on the level to the sublevel below it. The critical submanifolds on one level may have
different dimensions and indices, so their negative normal bundles have different bases and
ranks; with `X` the lower sublevel and `Z` its union with the attached disc bundles, the relative
homology of the attachment is the sum over the critical submanifolds of the relative homologies of
their disc-sphere pairs, which are those of the Thom pairs of the negative normal bundles. The rank
zero case is included: there `S(E)` is empty, `D(E)` is `E` and `Z` is the disjoint union of `X`
and a copy of the base.

The proofs apply the comparison for attachments along a subspace with a deformation neighbourhood
(`TopPair.isIso_singularHomologyMap_of_attach`, `TopPair.isIso_singularCohomologyMap_of_attach`).
Its neighbourhood of `S(E)` in `D(E)` is the set `D½` of vectors of norm greater than `1/2`, and
its deformation is the radial push `TauCeti.radialPush 2⁻¹`, applied in every fibre of `D(E)`: it
pushes every vector of norm at least `1/2` out to the unit sphere and doubles the smaller ones, it
fixes `S(E)` and keeps `D½` in place. For several disc bundles the attaching maps glue to a closed
embedding of the disjoint union of the disc bundles (`ContinuousMap.isClosedEmbedding_sigma`), the
radial push runs on every summand, and additivity of relative homology
(`TopPair.isColimitCofanSingularHomology`) and cohomology
(`TopPair.isLimitFanSingularCohomology`) splits the disjoint union of the disc-sphere pairs.

## Main results

* `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`: attaching a disc bundle along its
  sphere bundle induces isomorphisms `Hₙ(D(E), S(E)) ≅ Hₙ(Z, X)`.
* `TauCeti.isIso_singularCohomologyMap_of_attach_discBundle`: the same in cohomology,
  `Hⁿ(Z, X) ≅ Hⁿ(D(E), S(E))`.
* `TauCeti.isColimitCofanSingularHomologyOfAttachDiscBundle`: attaching finitely many disc bundles
  `D(Eₐ)` along their sphere bundles with disjoint images gives `Hₙ(Z, X) ≅ ∐ₐ Hₙ(D(Eₐ), S(Eₐ))`.
* `TauCeti.isLimitFanSingularCohomologyOfAttachDiscBundle`: the same in cohomology,
  `Hⁿ(Z, X) ≅ ∏ₐ Hⁿ(D(Eₐ), S(Eₐ))`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.22 and its proof (good pairs and excision).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261, for the
  attachment of the negative disc bundles of several critical submanifolds on one level.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Set Topology
open scoped unitInterval

universe w v u

namespace TauCeti

/-! ### The radial push in the fibres of a disc bundle -/

section Collar

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, NormedAddCommGroup (E b)]

variable (F E) in
/-- The vectors of the disc bundle of norm greater than `1/2`. -/
private def outerCollar : Set (discBundle F E) :=
  {v | 2⁻¹ < ‖(v : TotalSpace F E).2‖}

private lemma mem_outerCollar {v : discBundle F E} :
    v ∈ outerCollar F E ↔ 2⁻¹ < ‖(v : TotalSpace F E).2‖ :=
  Iff.rfl

variable [TopologicalSpace (TotalSpace F E)]

/-- The subspace of the disc-sphere pair, as the range of its embedding, consists of the vectors of
the sphere bundle. -/
private lemma mem_range_discSpherePair_map {v : discBundle F E} :
    v ∈ range (discSpherePair F E).map ↔ (v : TotalSpace F E) ∈ sphereBundle F E := by
  rw [TopPair.range_ofInclusion_map]
  exact mem_preimage

private lemma range_discSpherePair_map_subset_outerCollar :
    range (discSpherePair F E).map ⊆ outerCollar F E := fun v hv ↦
  mem_outerCollar.2 (by rw [mem_sphereBundle.1 (mem_range_discSpherePair_map.1 hv)]; norm_num)

private lemma isOpen_outerCollar (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsOpen (outerCollar F E) :=
  isOpen_lt continuous_const (hnorm.comp continuous_subtype_val)

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)

/-- The radial push `TauCeti.radialPush 2⁻¹` in every fibre of the disc bundle: at time one it
pushes every vector of norm at least `1/2` out to the unit sphere and doubles the smaller ones. -/
private def discCollar : C(I × discBundle F E, discBundle F E) where
  toFun p := ⟨TotalSpace.mk' F p.2.1.proj (radialPush 2⁻¹ p.1 p.2.1.2),
    mem_discBundle.2 (norm_radialPush_le_one p.1 (mem_discBundle.1 p.2.2))⟩
  continuous_toFun := by
    have hv : Continuous fun p : I × discBundle F E ↦ (p.2 : TotalSpace F E) :=
      continuous_subtype_val.comp continuous_snd
    have ht : Continuous fun p : I × discBundle F E ↦ (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    -- The radial push rescales each vector by a factor in `[0, 3]`, continuous off the zero
    -- section.
    refine Continuous.subtype_mk ((hv.smul_totalSpace_of_norm_le (C := 3) (fun p ↦ ?_)
      fun p hp ↦ ?_).congr fun p ↦ by rw [radialPush_eq_smul]) _
    · have hm : 0 ≤ min 1 (2⁻¹ / ‖(p.2 : TotalSpace F E).2‖) :=
        le_min zero_le_one (by positivity)
      have hm' := min_le_left 1 (2⁻¹ / ‖(p.2 : TotalSpace F E).2‖)
      rw [Real.norm_of_nonneg (by nlinarith [p.1.2.1, p.1.2.2])]
      norm_num
      nlinarith [p.1.2.1, p.1.2.2]
    · exact (continuousAt_const.sub ht.continuousAt).add (ht.continuousAt.mul
        (continuousAt_const.mul (continuousAt_const.min (continuousAt_const.div
          (hnorm.comp hv).continuousAt (norm_ne_zero_iff.2 hp)))))

private lemma coe_discCollar (t : I) (v : discBundle F E) :
    (discCollar hnorm (t, v) : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (radialPush 2⁻¹ t v.1.2) :=
  rfl

/-- The collar deformation keeps the outer collar in place at every time. -/
private lemma discCollar_mem_outerCollar (t : I) {v : discBundle F E} (hv : v ∈ outerCollar F E) :
    discCollar hnorm (t, v) ∈ outerCollar F E :=
  hv.trans_le (norm_le_norm_radialPush (by norm_num) (by norm_num) t (mem_discBundle.1 v.2))

/-- At time one the collar deformation pushes the outer collar onto the sphere bundle. -/
private lemma discCollar_one_mem_range {v : discBundle F E} (hv : v ∈ outerCollar F E) :
    discCollar hnorm (1, v) ∈ range (discSpherePair F E).map := by
  rw [mem_range_discSpherePair_map, coe_discCollar, mem_sphereBundle]
  exact norm_radialPush_one (by norm_num) hv.le

/-- The collar deformation fixes the sphere bundle at every time. -/
private lemma discCollar_of_mem_range (t : I) {v : discBundle F E}
    (hv : v ∈ range (discSpherePair F E).map) : discCollar hnorm (t, v) = v := by
  apply Subtype.ext
  rw [coe_discCollar, radialPush_of_norm_eq_one (by norm_num) (by norm_num) t
    (mem_sphereBundle.1 (mem_range_discSpherePair_map.1 hv))]

/-- At time zero the collar deformation is the identity. -/
private lemma discCollar_zero (v : discBundle F E) : discCollar hnorm (0, v) = v := by
  apply Subtype.ext
  rw [coe_discCollar, radialPush_zero]

end Collar

/-! ### Attaching a disc bundle -/

section Attach

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, NormedAddCommGroup (E b)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : discSpherePair F E ⟶ TopPair.ofSubset (X := TopCat.of Z) X}

/-- **Attaching a disc bundle induces isomorphisms on relative homology.** Let `E → B` be a real
vector bundle whose fibre norm is continuous on the total space, and let
`f : (D(E), S(E)) ⟶ (Z, X)` be a map of pairs with `X` closed in `Z`. Suppose that `f` is a closed
embedding of `D(E)` into `Z` sending a point into `X` only if it lies in `S(E)`, and that `X`
together with the image of `f` is all of `Z`: the space `Z` is obtained from `X` by attaching
`D(E)` along `S(E)`. Then `f` induces isomorphisms `Hₙ(D(E), S(E)) ≅ Hₙ(Z, X)` on relative singular
homology, with coefficients in any abelian category with coproducts, in every degree. -/
theorem isIso_singularHomologyMap_of_attach_discBundle
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (hf : IsClosedEmbedding (TopPair.Hom.fst f))
    (hfX : ∀ v : discBundle F E,
      TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
    (hfcover : X ∪ range (TopPair.Hom.fst f) = univ) :
    IsIso (TopPair.singularHomologyMap f R n) :=
  TopPair.isIso_singularHomologyMap_of_attach R n f hX hf
    (fun v hv ↦ mem_range_discSpherePair_map.2 (hfX v hv)) hfcover (isOpen_outerCollar hnorm)
    range_discSpherePair_map_subset_outerCollar (discCollar hnorm) (discCollar_zero hnorm)
    (fun t _ ↦ discCollar_of_mem_range hnorm t) (fun t _ ↦ discCollar_mem_outerCollar hnorm t)
    (fun _ ↦ discCollar_one_mem_range hnorm)

/-- **Attaching a disc bundle induces isomorphisms on relative cohomology.** Under the hypotheses
of `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`, the map of pairs
`f : (D(E), S(E)) ⟶ (Z, X)` induces isomorphisms `Hⁿ(Z, X) ≅ Hⁿ(D(E), S(E))` on relative singular
cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_of_attach_discBundle
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (k : Type*) [Ring k] [Linear k C] (M : C)
    (hf : IsClosedEmbedding (TopPair.Hom.fst f))
    (hfX : ∀ v : discBundle F E,
      TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
    (hfcover : X ∪ range (TopPair.Hom.fst f) = univ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) :=
  TopPair.isIso_singularCohomologyMap_of_attach R k M n f hX hf
    (fun v hv ↦ mem_range_discSpherePair_map.2 (hfX v hv)) hfcover (isOpen_outerCollar hnorm)
    range_discSpherePair_map_subset_outerCollar (discCollar hnorm) (discCollar_zero hnorm)
    (fun t _ ↦ discCollar_of_mem_range hnorm t) (fun t _ ↦ discCollar_mem_outerCollar hnorm t)
    (fun _ ↦ discCollar_one_mem_range hnorm)

end Attach

/-! ### Attaching several disc bundles -/

section Several

variable {ι : Type w} {B : ι → Type w} {F : ι → Type*} {E : ∀ a, B a → Type w}
  [∀ a b, NormedAddCommGroup (E a b)] [∀ a, TopologicalSpace (TotalSpace (F a) (E a))]
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  (f : ∀ a, discSpherePair (F a) (E a) ⟶ TopPair.ofSubset (X := TopCat.of Z) X)

/-- If `X` and the images of the `f a` cover `Z`, so do `X` and the image of the map out of the
disjoint union of the disc-sphere pairs which is `f a` on the summand of `a`. -/
private lemma union_range_sigmaCofanIsColimit_desc
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    X ∪ range (TopPair.Hom.fst
      (Cofan.IsColimit.desc (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f)) =
      univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  obtain hz | hz := (hfcover.symm ▸ mem_univ z : z ∈ X ∪ ⋃ a, range (TopPair.Hom.fst (f a)))
  · exact Or.inl hz
  · obtain ⟨a, v, rfl⟩ := mem_iUnion.1 hz
    exact Or.inr ⟨⟨a, v⟩, TopPair.sigmaCofanIsColimit_desc_fst_apply _ f _⟩

/-- The map out of the disjoint union of the disc-sphere pairs which is `f a` on the summand of `a`
is a closed embedding when the `f a` are, with pairwise disjoint images. -/
private lemma isClosedEmbedding_fst_sigmaCofanIsColimit_desc [Finite ι]
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a)))) :
    IsClosedEmbedding (TopPair.Hom.fst (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f)) := by
  rw [TopPair.sigmaCofanIsColimit_desc_fst]
  exact ContinuousMap.isClosedEmbedding_sigma hf hdisj

/-- The map out of the disjoint union of the disc-sphere pairs which is `f a` on the summand of `a`
sends a point into `X` only if it lies in the disjoint union of the sphere bundles, when each `f a`
sends a point into `X` only if it lies in the sphere bundle of `Eₐ`. -/
private lemma mem_range_sigma_map_of_fst_sigmaCofanIsColimit_desc_mem
    (hfX : ∀ a, ∀ v : discBundle (F a) (E a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (x : Σ a, discBundle (F a) (E a))
    (hx : TopPair.Hom.fst (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f) x ∈ X) :
    x ∈ range (TopPair.sigma fun a ↦ discSpherePair (F a) (E a)).map :=
  (TopPair.mem_range_sigma_map _).2 (mem_range_discSpherePair_map.2
    (hfX _ _ (TopPair.sigmaCofanIsColimit_desc_fst_apply _ f x ▸ hx)))

/-- The vectors of the disjoint union of the disc bundles of norm greater than `1/2`. -/
private def sigmaOuterCollar : Set (Σ a, discBundle (F a) (E a)) :=
  {x | x.2 ∈ outerCollar (F x.1) (E x.1)}

private lemma range_sigma_map_subset_sigmaOuterCollar :
    range (TopPair.sigma fun a ↦ discSpherePair (F a) (E a)).map ⊆ sigmaOuterCollar :=
  fun _ hx ↦ range_discSpherePair_map_subset_outerCollar ((TopPair.mem_range_sigma_map _).1 hx)

private lemma isOpen_sigmaOuterCollar
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) :
    IsOpen (sigmaOuterCollar (F := F) (E := E)) :=
  isOpen_sigma_iff.2 fun a ↦ isOpen_outerCollar (hnorm a)

variable [∀ a, TopologicalSpace (B a)] [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℝ (F a)]
  [∀ a b, NormedSpace ℝ (E a b)] [∀ a, FiberBundle (F a) (E a)] [∀ a, VectorBundle ℝ (F a) (E a)]

/-- The radial push `TauCeti.radialPush 2⁻¹` in every fibre of every summand of the disjoint union
of the disc bundles: the homotopies `discCollar` of the summands, followed by their inclusions,
glued along the disjoint union. -/
private def sigmaDiscCollar (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) :
    C(I × Σ a, discBundle (F a) (E a), Σ a, discBundle (F a) (E a)) :=
  (ContinuousMap.Homotopy.sigma fun a ↦
    (ContinuousMap.Homotopy.refl ⟨Sigma.mk a, continuous_sigmaMk⟩).comp
      (ContinuousMap.Homotopy.ofApplyZero (f := .id _) (discCollar (hnorm a))
        (discCollar_zero (hnorm a)))).toContinuousMap

section

variable (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖)

/-- On the summand of `a`, the collar deformation of the disjoint union is that of `D(Eₐ)`. -/
private lemma sigmaDiscCollar_apply (t : I) (x : Σ a, discBundle (F a) (E a)) :
    sigmaDiscCollar hnorm (t, x) = ⟨x.1, discCollar (hnorm x.1) (t, x.2)⟩ :=
  ContinuousMap.Homotopy.sigma_apply (X := fun a ↦ discBundle (F a) (E a)) _ t x.1 x.2

private lemma sigmaDiscCollar_zero (x : Σ a, discBundle (F a) (E a)) :
    sigmaDiscCollar hnorm (0, x) = x := by
  rw [sigmaDiscCollar_apply, discCollar_zero]

private lemma sigmaDiscCollar_of_mem_range (t : I) {x : Σ a, discBundle (F a) (E a)}
    (hx : x ∈ range (TopPair.sigma fun a ↦ discSpherePair (F a) (E a)).map) :
    sigmaDiscCollar hnorm (t, x) = x := by
  rw [sigmaDiscCollar_apply,
    discCollar_of_mem_range (hnorm x.1) t ((TopPair.mem_range_sigma_map _).1 hx)]

private lemma sigmaDiscCollar_mem_sigmaOuterCollar (t : I) {x : Σ a, discBundle (F a) (E a)}
    (hx : x ∈ sigmaOuterCollar) : sigmaDiscCollar hnorm (t, x) ∈ sigmaOuterCollar := by
  rw [sigmaDiscCollar_apply]
  exact discCollar_mem_outerCollar (hnorm x.1) t hx

private lemma sigmaDiscCollar_one_mem_range {x : Σ a, discBundle (F a) (E a)}
    (hx : x ∈ sigmaOuterCollar) :
    sigmaDiscCollar hnorm (1, x) ∈
      range (TopPair.sigma fun a ↦ discSpherePair (F a) (E a)).map := by
  rw [sigmaDiscCollar_apply]
  exact (TopPair.mem_range_sigma_map _).2 (discCollar_one_mem_range (hnorm x.1) hx)

end

variable [Finite ι]

/-- The hypotheses of an attachment of several disc bundles make the attachment of their disjoint
union an attachment along a subspace with a deformation neighbourhood, so that its relative homology
is that of the disjoint union of the disc-sphere pairs. -/
private lemma isIso_singularHomologyMap_sigmaCofanIsColimit_desc
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : discBundle (F a) (E a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsIso (TopPair.singularHomologyMap
      (Cofan.IsColimit.desc (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f)
      R n) :=
  TopPair.isIso_singularHomologyMap_of_attach R n _ hX
    (isClosedEmbedding_fst_sigmaCofanIsColimit_desc f hf hdisj)
    (mem_range_sigma_map_of_fst_sigmaCofanIsColimit_desc_mem f hfX)
    (union_range_sigmaCofanIsColimit_desc f hfcover) (isOpen_sigmaOuterCollar hnorm)
    range_sigma_map_subset_sigmaOuterCollar (sigmaDiscCollar hnorm) (sigmaDiscCollar_zero hnorm)
    (fun t _ ↦ sigmaDiscCollar_of_mem_range hnorm t)
    (fun t _ ↦ sigmaDiscCollar_mem_sigmaOuterCollar hnorm t)
    (fun _ ↦ sigmaDiscCollar_one_mem_range hnorm)

/-- The cohomology form of `isIso_singularHomologyMap_sigmaCofanIsColimit_desc`. -/
private lemma isIso_singularCohomologyMap_sigmaCofanIsColimit_desc
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : discBundle (F a) (E a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (Cofan.IsColimit.desc (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f)
      n) :=
  TopPair.isIso_singularCohomologyMap_of_attach R k M n _ hX
    (isClosedEmbedding_fst_sigmaCofanIsColimit_desc f hf hdisj)
    (mem_range_sigma_map_of_fst_sigmaCofanIsColimit_desc_mem f hfX)
    (union_range_sigmaCofanIsColimit_desc f hfcover) (isOpen_sigmaOuterCollar hnorm)
    range_sigma_map_subset_sigmaOuterCollar (sigmaDiscCollar hnorm) (sigmaDiscCollar_zero hnorm)
    (fun t _ ↦ sigmaDiscCollar_of_mem_range hnorm t)
    (fun t _ ↦ sigmaDiscCollar_mem_sigmaOuterCollar hnorm t)
    (fun _ ↦ sigmaDiscCollar_one_mem_range hnorm)

/-- **Attaching several disc bundles: relative homology is the coproduct.** Let `Eₐ → Bₐ`, for `a`
in a finite type, be real vector bundles whose fibre norms are continuous on the total spaces, with
possibly different bases and ranks, and let `f a : (D(Eₐ), S(Eₐ)) ⟶ (Z, X)` be maps of pairs with
`X` closed in `Z`. Suppose that each `f a` is a closed embedding of `D(Eₐ)` into `Z` sending a point
into `X` only if it lies in `S(Eₐ)`, that the images of the `f a` are pairwise disjoint, and that
`X` together with these images is all of `Z`: the space `Z` is obtained from `X` by attaching the
disc bundles `D(Eₐ)` along their sphere bundles. Then, in every degree and with coefficients in any
abelian category with coproducts, `Hₙ(Z, X)` is the coproduct of the `Hₙ(D(Eₐ), S(Eₐ))`, with the
maps induced by the `f a` as the coproduct inclusions. -/
def isColimitCofanSingularHomologyOfAttachDiscBundle
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : discBundle (F a) (E a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsColimit (Cofan.mk ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n)
      fun a ↦ TopPair.singularHomologyMap (f a) R n) :=
  have := isIso_singularHomologyMap_sigmaCofanIsColimit_desc f hnorm hX R n hf hfX hdisj hfcover
  -- Finite coproducts are exact in an abelian category, which has finite biproducts.
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  IsColimit.ofIsoColimit
    (TopPair.isColimitCofanSingularHomology (fun a ↦ discSpherePair (F a) (E a)) C R n)
    (Cofan.ext (asIso (TopPair.singularHomologyMap (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f) R n)) fun a ↦ by
      rw [cofan_mk_inj, cofan_mk_inj, asIso_hom, ← TopPair.singularHomologyMap_comp]
      exact congrArg (TopPair.singularHomologyMap · R n) (Cofan.IsColimit.fac _ f a))

/-- **Attaching several disc bundles: relative cohomology is the product.** Under the hypotheses of
`TauCeti.isColimitCofanSingularHomologyOfAttachDiscBundle`, in every degree and with arbitrary
coefficients, `Hⁿ(Z, X)` is the product of the `Hⁿ(D(Eₐ), S(Eₐ))`, with the maps induced by the
`f a` as the product projections. -/
def isLimitFanSingularCohomologyOfAttachDiscBundle
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : discBundle (F a) (E a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsLimit (Fan.mk ((TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n)
      fun a ↦ TopPair.singularCohomologyMap (f a) n) := by
  have := isIso_singularCohomologyMap_sigmaCofanIsColimit_desc f hnorm hX R k M n hf hfX hdisj
    hfcover
  refine IsLimit.ofIsoLimit
    (TopPair.isLimitFanSingularCohomology (fun a ↦ discSpherePair (F a) (E a)) C R k M n)
    (Fan.ext (asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ discSpherePair (F a) (E a)) f) n)).symm fun a ↦ ?_)
  rw [fan_mk_proj, fan_mk_proj, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
    ← TopPair.singularCohomologyMap_comp]
  exact congrArg (TopPair.singularCohomologyMap · n) (Cofan.IsColimit.fac _ f a)

end Several

end TauCeti
