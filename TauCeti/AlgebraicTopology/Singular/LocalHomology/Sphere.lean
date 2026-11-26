/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# The fundamental class of a sphere in relative homology

Let `Sⁿ = TopCat.diskBoundary (n + 1)` be the boundary sphere of the `(n + 1)`-disk and `B` a
subset of it. The standard generator of the reduced homology `H_redₙ(Sⁿ)`
(`TauCeti.reducedSingularHomologyTopCatSphereIso`) has an image in the relative homology
`Hₙ(Sⁿ, B)`, `TauCeti.diskBoundaryFundamentalClass R B`. For `B = Sⁿ ∖ {x}` this is a class in
the local homology of `Sⁿ` at `x`, and for `B` the complement of finitely many points it is the
class whose image under a map `Sⁿ ⟶ Y` computes local degrees.

## Main results

* `TauCeti.diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap`: the image of the
  class under the map of pairs induced by `g : Sⁿ ⟶ Y` is the image of the generator under `g`.
* `TauCeti.diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap_id`: the classes are
  compatible with enlarging `B`.
* `TauCeti.diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap_diskBoundaryNeg`: the
  antipodal map acts on the class by `(-1) ^ (n + 1)`.
* `TauCeti.isIso_diskBoundaryFundamentalClass_compl_singleton`: in positive degrees the class
  generates the local homology `Hₙ(Sⁿ, Sⁿ ∖ {x})`, since `Sⁿ ∖ {x}` is contractible.
* `TauCeti.singularHomologyToLocalHomology_singularHomologyTopCatSphereGenerator`: for `n ≥ 1`, the
  standard generator of `Hₙ(Sⁿ; k)` maps to this class in the local homology at each point.
* `TauCeti.isFundamentalClass_singularHomologyTopCatSphereGenerator`: consequently the standard
  generator of `Hₙ(Sⁿ; k)`, `n ≥ 1`, is a fundamental class of `Sⁿ` in the sense of
  `TauCeti.IsFundamentalClass`, for every ring `k`.
* `TauCeti.exists_isFundamentalClass_sphere`: so the unit sphere of every real normed space of
  finite dimension at least `2` has a fundamental class.

Coefficients are an object `R` of an abelian category with coproducts, except in the last three
results, which are about `k`-modules.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) {n : ℕ}

/-- The fundamental class of the boundary sphere `Sⁿ` of the `(n + 1)`-disk read in `Hₙ(Sⁿ, B)`:
the image of the standard generator `TauCeti.reducedSingularHomologyTopCatSphereIso` of the
reduced homology `H_redₙ(Sⁿ)` under the quotient map to the relative homology. -/
def diskBoundaryFundamentalClass (B : Set (TopCat.diskBoundary.{w} (n + 1))) :
    R ⟶ (TopPair.ofSubset B).singularHomology R n :=
  (reducedSingularHomologyTopCatSphereIso R n).inv ≫
    (reducedSingularHomologyι R n).app (TopCat.diskBoundary.{w} (n + 1)) ≫
      (TopPair.ofSubset B).singularHomologyπ R n

lemma diskBoundaryFundamentalClass_def (B : Set (TopCat.diskBoundary.{w} (n + 1))) :
    diskBoundaryFundamentalClass R B =
      (reducedSingularHomologyTopCatSphereIso R n).inv ≫
        (reducedSingularHomologyι R n).app (TopCat.diskBoundary.{w} (n + 1)) ≫
          (TopPair.ofSubset B).singularHomologyπ R n :=
  (rfl)

/-- The image of `diskBoundaryFundamentalClass R B` under the map of pairs induced by `g` is the
image of the standard generator under `g`, read in `Hₙ(Y, B')`. -/
@[reassoc]
lemma diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap
    {B : Set (TopCat.diskBoundary.{w} (n + 1))} {Y : TopCat.{w}} {B' : Set Y}
    (g : TopCat.diskBoundary.{w} (n + 1) ⟶ Y) (h : MapsTo g B B') :
    diskBoundaryFundamentalClass R B ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g h) R n =
      (reducedSingularHomologyTopCatSphereIso R n).inv ≫
        (reducedSingularHomologyι R n).app (TopCat.diskBoundary.{w} (n + 1)) ≫
          SSet.homologyMap (TopCat.toSSet.map g) R n ≫
            (TopPair.ofSubset B').singularHomologyπ R n := by
  have hπ := SSetPair.homologyπ_naturality (TopPair.toSSetPair.map (TopPair.ofSubsetMap g h)) R n
  rw [TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst] at hπ
  -- Ambient singular homology appears both as the target of `reducedSingularHomologyι` and as the
  -- source of `singularHomologyπ`; the two presentations agree only up to unfolding, so the
  -- rewrite across them uses `erw`.
  rw [diskBoundaryFundamentalClass, Category.assoc]
  erw [Category.assoc, ← hπ]
  rfl

/-- The fundamental classes of `Sⁿ` in `Hₙ(Sⁿ, B)` and `Hₙ(Sⁿ, B')` correspond under the map
induced by an inclusion `B ⊆ B'`. -/
@[reassoc (attr := simp)]
lemma diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap_id
    {B B' : Set (TopCat.diskBoundary.{w} (n + 1))}
    (h : MapsTo (𝟙 (TopCat.diskBoundary.{w} (n + 1))) B B') :
    diskBoundaryFundamentalClass R B ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) h) R n =
      diskBoundaryFundamentalClass R B' := by
  refine (diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap R _ _).trans ?_
  rw [CategoryTheory.Functor.map_id, SSet.homologyMap_id]
  -- The identity sits between the two presentations of ambient singular homology.
  erw [Category.id_comp]
  rfl

/-- The antipodal map acts by `(-1) ^ (n + 1)` on the fundamental class of `Sⁿ` in `Hₙ(Sⁿ, B)`,
for `B` invariant under it. -/
@[reassoc (attr := simp)]
lemma diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap_diskBoundaryNeg
    {B : Set (TopCat.diskBoundary.{w} (n + 1))} (h : MapsTo (diskBoundaryNeg.{w} (n + 1)) B B) :
    diskBoundaryFundamentalClass R B ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap _ h) R n =
      ((-1 : ℤ) ^ (n + 1)) • diskBoundaryFundamentalClass R B := by
  have hι := (reducedSingularHomologyι R n).naturality (diskBoundaryNeg.{w} (n + 1))
  rw [reducedSingularHomologyFunctor_map_diskBoundaryNeg, Preadditive.zsmul_comp,
    Category.id_comp] at hι
  have hF : ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
      (diskBoundaryNeg.{w} (n + 1)) =
      SSet.homologyMap (TopCat.toSSet.map (diskBoundaryNeg.{w} (n + 1))) R n := rfl
  rw [diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap]
  -- As in `diskBoundaryFundamentalClass_comp_singularHomologyMap_ofSubsetMap`, the rewrite
  -- crosses the two presentations of ambient singular homology.
  erw [← Category.assoc ((reducedSingularHomologyι R n).app _), ← hι.trans (congrArg _ hF),
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rfl

/-- In positive degrees, the fundamental class of `Sⁿ` generates the local homology
`Hₙ(Sⁿ, Sⁿ ∖ {x})`, since `Sⁿ ∖ {x}` is contractible. -/
theorem isIso_diskBoundaryFundamentalClass_compl_singleton (k : ℕ)
    (x : TopCat.diskBoundary.{w} (k + 1 + 1)) :
    IsIso (diskBoundaryFundamentalClass R {x}ᶜ) := by
  let e : (TopCat.diskBoundary.{w} (k + 1 + 1) : Type w) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (k + 1 + 1))) 1 := Homeomorph.ulift
  have : ContractibleSpace (TopPair.ofSubset ({x}ᶜ :
      Set (TopCat.diskBoundary.{w} (k + 1 + 1)))).snd :=
    (e.subtype (q := (· ∈ ({x.down}ᶜ : Set _))) fun v ↦
      not_congr ⟨fun h ↦ congrArg ULift.down h, fun h ↦ ULift.ext h⟩).contractibleSpace_iff.2
      (contractibleSpace_sphere_compl_singleton _)
  have : IsIso ((reducedSingularHomologyι R (k + 1)).app
      (TopCat.diskBoundary.{w} (k + 1 + 1))) := by
    rw [reducedSingularHomologyι_succ_app]
    infer_instance
  have : IsIso ((TopPair.ofSubset ({x}ᶜ :
      Set (TopCat.diskBoundary.{w} (k + 1 + 1)))).singularHomologyπ R (k + 1)) :=
    TopPair.isIso_singularHomologyπ_of_contractibleSpace _ R k
  -- The three factors are invertible, but their objects agree only up to unfolding.
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ‹_› ‹_›)

/-- For `n ≥ 1`, the image of the standard generator of `Hₙ(Sⁿ; k)` in the local homology
`Hₙ(Sⁿ, Sⁿ ∖ {x}; k)` is the fundamental class `diskBoundaryFundamentalClass` applied to `1`. Here
`TopCat.sphere n` is `TopCat.diskBoundary (n + 1)`, and the generator, stated in
`singularHomologyFunctor`, is applied to maps out of `SSet.homology`; the two presentations of
singular homology agree only after unfolding, which this lemma records once. -/
lemma singularHomologyToLocalHomology_singularHomologyTopCatSphereGenerator (k : Type w) [Ring k]
    (d : ℕ) (x : TopCat.sphere.{w} (d + 1)) :
    singularHomologyToLocalHomology (ModuleCat.of k k) x (d + 1)
        (singularHomologyTopCatSphereGenerator k d) =
      (diskBoundaryFundamentalClass (ModuleCat.of k k)
        ({x}ᶜ : Set (TopCat.diskBoundary.{w} (d + 1 + 1)))).hom 1 := by
  refine (singularHomologyToLocalHomology_eq_singularHomologyπ _ x _).trans ?_
  rw [singularHomologyTopCatSphereGenerator_def, diskBoundaryFundamentalClass_def]
  rfl

/-- **The standard generator of `Hₙ(Sⁿ; k)` is a fundamental class.** For every ring `k` and
`n ≥ 1`, the image of the standard generator `TauCeti.singularHomologyTopCatSphereGenerator` of
`Hₙ(Sⁿ; k)` in the local homology `Hₙ(Sⁿ, Sⁿ ∖ {x}; k)` generates it, at every point `x`. -/
theorem isFundamentalClass_singularHomologyTopCatSphereGenerator (k : Type w) [Ring k] (d : ℕ) :
    IsFundamentalClass (M := TopCat.sphere.{w} (d + 1)) (N := ModuleCat.of k k) (n := d + 1)
      (singularHomologyTopCatSphereGenerator k d) := by
  refine (isFundamentalClass_iff _).2 fun x ↦ ?_
  -- The goal carries the topology of the lifted metric sphere, found while elaborating the
  -- statement, rather than that of `TopCat.sphere (d + 1)`, so it is transported along the
  -- lemma by `congrArg` instead of `rw`.
  refine (congrArg (k ∙ · = ⊤)
    (singularHomologyToLocalHomology_singularHomologyTopCatSphereGenerator k d x)).mpr ?_
  have h := isIso_diskBoundaryFundamentalClass_compl_singleton (ModuleCat.of k k) d x
  -- `h` is stated for `{x}ᶜ` as a subset of `TopCat.diskBoundary (d + 1 + 1)`, so it is passed to
  -- `asIso` explicitly rather than found by instance search.
  exact (@asIso _ _ _ _ _ h).toLinearEquiv.span_singleton_apply_eq_top_iff.2
    Ideal.span_singleton_one

/-- **The unit sphere of a finite-dimensional real normed space has a fundamental class.** For a
real normed space `E` of dimension `d + 2`, the image of the standard generator of `Hd₊₁(Sᵈ⁺¹; k)`
under a homeomorphism from the standard sphere is a fundamental class of the unit sphere of `E`,
for every ring `k`. -/
theorem exists_isFundamentalClass_sphere {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (hd : Module.finrank ℝ E = d + 2) (k : Type w) [Ring k] :
    ∃ μ : ((TopCat.toSSet.obj (TopCat.of (sphere (0 : E) 1))).homology (ModuleCat.of k k)
      (d + 1) : ModuleCat.{w} k), IsFundamentalClass μ :=
  ⟨_, (isFundamentalClass_singularHomologyTopCatSphereGenerator k d).map_homeomorph
    (Homeomorph.ulift.trans (sphereHomeomorphOfFinrankEq (by rw [finrank_euclideanSpace_fin, hd])))⟩

end TauCeti
