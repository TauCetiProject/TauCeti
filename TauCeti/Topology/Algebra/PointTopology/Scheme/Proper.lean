/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Projective.Basic
public import TauCeti.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Maps.Proper.LocalAtTarget

/-!
# Proper morphisms induce proper maps of points

Let `K` be an algebraically closed topological field whose projective spaces have compact
`K`-points, for instance `K = ℂ`. Give the `K`-points of a scheme over `Spec K`, the morphisms
from `Spec K` over `Spec K`, the chart topology `TauCeti.SchemePointTopology.topology`. A proper
morphism `f : X ⟶ Y` of `K`-schemes, with `Y` locally Noetherian, induces a proper map
`X(K) → Y(K)` in the sense of Mathlib's `IsProperMap`. This covers every `Y` locally of finite type
over `K` (`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`). In particular a proper
`K`-scheme has
compact `K`-points; for a separated `K`-scheme these points are also Hausdorff
(`TauCeti.SchemePointTopology.t2Space_of_isSeparated`). Neither `X` nor `Y` need be separated,
reduced or quasi-compact.

Properness of a continuous map is local on its target, so it suffices to show it over the image
of every affine open chart `Spec A ⟶ Y`, where `A` is a Noetherian `K`-algebra. The
points of the base change `X ×_Y Spec A` are the points of `X` over that image. Chow's lemma
(`TauCeti.AlgebraicGeometry.exists_projectiveModification`) gives a surjective morphism
`p : P ⟶ X ×_Y Spec A` from a scheme `P` projective over `A`, whose `K`-points are proper over
those of `Spec A` (`TauCeti.SchemePointTopology.isProperMap_map_of_isProjectiveOver`). Since `K`
is algebraically closed and `p` is surjective and locally of finite type, every `K`-point of
`X ×_Y Spec A` lifts to `P` (`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_iff_mem_range`), and a
continuous map whose composite with a continuous surjection is proper is itself proper.

## Main results

All results assume that `K` is algebraically closed and that the `K`-points of every
projective space `ℙⁿ_K` are compact; both hold for `K = ℂ`.

* `TauCeti.SchemePointTopology.isProperMap_map_of_isProper_of_finite_irreducibleComponents`:
  a proper scheme with finitely many irreducible components over a `K`-algebra `A` has a proper
  map of `K`-points to `Spec A`.
* `TauCeti.SchemePointTopology.isProperMap_map_of_isProper_of_isNoetherianRing`: a proper scheme
  over a Noetherian `K`-algebra `A` has a proper map of `K`-points to `Spec A`.
* `TauCeti.SchemePointTopology.isProperMap_map_of_isProper`: a proper morphism of `K`-schemes
  whose target is locally Noetherian induces a proper map of `K`-points.
* `TauCeti.SchemePointTopology.compactSpace_of_isProper`: the `K`-points of a proper `K`-scheme
  are compact.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII, Propositions
  3.1(viii) and 3.2(v), pp. 244–247.
* J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2.
* The Stacks Project, Section 30.18, *Chow's Lemma* (tag 0200).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace
  TauCeti.SymmetricAlgebra

namespace TauCeti.SchemePointTopology

attribute [local instance] topology

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  [∀ n : ℕ, CompactSpace (Points (R := K) (projToSpec K (Option (Fin n) → K)))]

/-- **A proper scheme with finitely many irreducible components over a `K`-algebra is proper
on `K`-points.** If `g : Z ⟶ Spec A` is proper and `Z` has finitely many irreducible components,
then `g` induces a proper map of `K`-points `Z(K) → (Spec A)(K)`. -/
theorem isProperMap_map_of_isProper_of_finite_irreducibleComponents {A : Type u} [CommRing A]
    [Algebra K A] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of A)) [IsProper g]
    (hZ : (irreducibleComponents Z).Finite) :
    IsProperMap (map (R := K) g (fX := g ≫ Spec.algebraMap K A) rfl) := by
  obtain ⟨P, _, p, -, _, _, hP⟩ :=
    TauCeti.AlgebraicGeometry.exists_projectiveModification_of_finite_irreducibleComponents g hZ
  have hp : p ≫ g ≫ Spec.algebraMap K A = (P ↘ Spec (.of A)) ≫ Spec.algebraMap K A := by
    rw [hP, Category.assoc]
  have : LocallyOfFiniteType (p ≫ g) := by
    rw [← hP]
    infer_instance
  have : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p g
  have hcomp : map (R := K) g (fX := g ≫ Spec.algebraMap K A) rfl ∘ map p hp =
      map (R := K) (P ↘ Spec (.of A)) rfl := by
    funext x
    rw [Function.comp_apply, map_map]
    congr 1
    exact hP.symm
  refine isProperMap_of_comp_of_surj (continuous_map p hp) (continuous_map g rfl) ?_
    (map_surjective_of_surjective p hp)
  rw [hcomp]
  exact isProperMap_map_of_isProjectiveOver

/-- **A proper scheme over a Noetherian `K`-algebra is proper on `K`-points.** If `g : Z ⟶ Spec A`
is proper, where `A` is a Noetherian `K`-algebra, then `g` induces a proper map of `K`-points
`Z(K) → (Spec A)(K)`. -/
theorem isProperMap_map_of_isProper_of_isNoetherianRing {A : Type u} [CommRing A]
    [Algebra K A] [IsNoetherianRing A] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of A)) [IsProper g] :
    IsProperMap (map (R := K) g (fX := g ≫ Spec.algebraMap K A) rfl) := by
  have : IsNoetherian Z := TauCeti.AlgebraicGeometry.isNoetherian_of_finiteType g
  exact isProperMap_map_of_isProper_of_finite_irreducibleComponents g
    NoetherianSpace.finite_irreducibleComponents

variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of K)} {fY : Y ⟶ Spec (.of K)}

/-- Over an affine open chart `i : Spec A ⟶ Y`, a proper morphism `f : X ⟶ Y` restricts to a
proper map of `K`-points over the image of the chart. -/
private theorem isProperMap_restrictPreimage_range_map (f : X ⟶ Y) (hf : f ≫ fY = fX) [IsProper f]
    [IsLocallyNoetherian Y] (A : CommAlgCat.{u} K) (i : Spec (.of A) ⟶ Y)
    (hi : i ≫ fY = Spec.algebraMap K A) [IsOpenImmersion i] :
    IsProperMap ((Set.range (map (R := K) i hi)).restrictPreimage (map f hf)) := by
  -- The chart algebra is Noetherian since `Y` is locally Noetherian.
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_of_isOpenImmersion i
  have : IsNoetherianRing A := isLocallyNoetherian_Spec.mp this
  -- The base change of `f` along the chart computes the points of `X` over the chart.
  have hfst : pullback.fst f i ≫ fX = pullback.snd f i ≫ Spec.algebraMap K A := by
    rw [← hf, ← hi, pullback.condition_assoc]
  refine (isProperMap_map_of_isProper_of_isNoetherianRing (K := K) (pullback.snd f i))
    |>.restrictPreimage_range_of_isEmbedding
      (isOpenEmbedding_of_isOpenImmersion (pullback.fst f i) hfst).isEmbedding
      (isOpenEmbedding_of_isOpenImmersion i hi).isEmbedding ?_ ?_
  · funext x
    exact Subtype.ext (by simp [pullback.condition])
  · ext x
    rw [Set.mem_preimage, mem_range_map_iff_closedPoint, mem_range_map_iff_closedPoint]
    simp only [Scheme.Hom.mem_opensRange, ← Set.mem_range]
    rw [Scheme.Pullback.range_fst]
    simp only [Set.mem_preimage, map_val]
    exact (congrArg (fun y : Y ↦ y ∈ Set.range i)
      (Scheme.Hom.comp_apply x.val f (IsLocalRing.closedPoint K))).symm.to_iff

/-- **Proper morphisms induce proper maps of points.** Let `K` be an algebraically closed
topological field, such as `ℂ`, whose projective spaces have compact `K`-points. A proper morphism
`f : X ⟶ Y` of `K`-schemes, where `Y` is locally Noetherian (for instance locally of finite type
over `K`), induces a proper map of `K`-points `X(K) → Y(K)`. -/
theorem isProperMap_map_of_isProper (f : X ⟶ Y) (hf : f ≫ fY = fX) [IsProper f]
    [IsLocallyNoetherian Y] : IsProperMap (map (R := K) f hf) := by
  refine (continuous_map f hf).isProperMap_of_locally fun y ↦ ?_
  obtain ⟨A, i, hi, _, hy⟩ := exists_mem_range_chartPoint fY y
  rw [chartPoint_eq_map_comp_homEquivAlgHom_symm, Set.range_comp,
    Spec.homEquivAlgHom.symm.surjective.range_eq, Set.image_univ] at hy
  exact ⟨⟨_, (isOpenEmbedding_of_isOpenImmersion i hi).isOpen_range⟩, hy,
    isProperMap_restrictPreimage_range_map f hf A i hi⟩

/-- **The `K`-points of a proper `K`-scheme are compact.** Over an algebraically closed topological
field `K`, such as `ℂ`, whose projective spaces have compact `K`-points, a scheme proper over `K`
has compact `K`-points. -/
instance compactSpace_of_isProper [IsProper fX] : CompactSpace (Points (R := K) fX) :=
  -- The base `Spec K` has a single `K`-point, so properness over it is compactness.
  (isProperMap_map_of_isProper (K := K) fX (Category.comp_id fX)).compactSpace
    (Y := Points (R := K) (𝟙 (Spec (.of K))))

end TauCeti.SchemePointTopology
