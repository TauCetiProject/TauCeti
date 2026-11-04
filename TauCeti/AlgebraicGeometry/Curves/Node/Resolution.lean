/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Node
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import TauCeti.RingTheory.GradedAlgebra.FiniteType
import TauCeti.AlgebraicGeometry.Blowup.AwayFromCenter
import TauCeti.AlgebraicGeometry.Gluing.Extension
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Resolving the node `xy = πⁿ` by repeated blowups

Let `R` be a discrete valuation ring with uniformizer `π`. The node `A = R[x, y] ⧸ (xy - πⁿ)` is
the local model of a node of thickness `n` in a family of curves over `R`; its total space is
regular exactly when `n ≤ 1` (`TauCeti.NodeAlgebra.isRegularRing_pow_iff`). Blowing up the origin
`(π, x, y)` of `xy = πⁿ⁺²` gives a scheme covered by the `π`-chart `xy = πⁿ` and two regular
coordinate charts `xt = π` (`TauCeti/AlgebraicGeometry/Blowup/Node.lean`), and the coordinate
charts meet the `π`-chart exactly where one of its coordinates is invertible. So the only part of
the blowup that can still be singular is the closed subset `V(x, y)` of the `π`-chart, and
blowing it up again lowers the thickness by two once more.

This file carries out the induction. For every `n`, the node `xy = πⁿ` has a resolution: a proper
morphism `Y ⟶ Spec A` from a regular scheme, which is an isomorphism away from `V(x, y)` and whose
composite to `Spec R` is still a nodal relative curve. When `n ≥ 1`, `V(x, y)` is the single
closed point `(π, x, y)`, the node of the special fibre, so the resolution changes nothing else.
For `n ≤ 1` the resolution is the identity. For `n + 2`, it is the blowup at the origin with a
resolution of its `π`-chart `xy = πⁿ` glued in along the complement of `V(x, y)`
(`AlgebraicGeometry.Scheme.Hom.exists_isPullback_isIso_morphismRestrict`); the coordinate
charts are already regular.

## Main results

* `TauCeti.NodeAlgebra.exists_resolution`: for a uniformizer `π` of a discrete valuation ring `R`
  and every `n`, there is a proper morphism `Y ⟶ Spec R[x, y] ⧸ (xy - πⁿ)` from a regular scheme,
  an isomorphism over `D(x) ∪ D(y)`, with `Y` at worst nodal of relative dimension one over `R`.

## References

* [The Stacks Project, Example 55.14.1](https://stacks.math.columbia.edu/tag/0CDC)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry reesAlgebra

namespace TauCeti.NodeAlgebra

universe u

variable {R : Type u} [CommRing R] {π : R}

/-- The node `xy = a` has a proper resolution by a regular scheme which is nodal over `R` and an
isomorphism over the open `D(x) ∪ D(y)`. -/
private def HasResolution (a : R) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of (NodeAlgebra R a))), IsProper f ∧
    IsIso (f ∣_ (⨆ i, PrimeSpectrum.basicOpen (coord a i) : (Spec (.of (NodeAlgebra R a))).Opens)) ∧
    IsRegular Y ∧
    AtWorstNodalOfRelativeDimensionOne (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)))

/-- A regular node is its own resolution. -/
private theorem hasResolution_of_isRegularRing {a : R} [IsRegularRing (NodeAlgebra R a)] :
    HasResolution a :=
  ⟨_, 𝟙 _, inferInstance, inferInstance, inferInstance, by
    rw [Category.id_comp]
    exact atWorstNodalOfRelativeDimensionOne a⟩

/-- A scheme `Y'` covered by an open immersion `ι` from a regular scheme and by the inverse image of
an open `V` over which `f' : Y' ⟶ B` is an isomorphism is regular as soon as `B` has regular local
rings at the points of `V` and `Y'` is locally Noetherian. -/
private theorem isRegular_of_isIso_morphismRestrict {Y Y' B : Scheme.{u}} [IsRegular Y]
    [IsLocallyNoetherian Y'] (ι : Y ⟶ Y') [IsOpenImmersion ι] (f' : Y' ⟶ B) (V : B.Opens)
    [IsIso (f' ∣_ V)] (hcov : ι.opensRange ⊔ f' ⁻¹ᵁ V = ⊤)
    (hV : ∀ b ∈ V, IsRegularLocalRing (B.presheaf.stalk b)) : IsRegular Y' := by
  refine ⟨fun p ↦ ?_⟩
  rcases TopologicalSpace.Opens.mem_sup.mp (hcov.ge (by trivial : p ∈ (⊤ : Y'.Opens))) with
    ⟨y, rfl⟩ | hp
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion ι y).mpr inferInstance
  -- Over `V`, the local ring of `Y'` at `p` is that of `f' ⁻¹ᵁ V ≅ V`, hence that of `B` at `f' p`.
  let p' : (f' ⁻¹ᵁ V).toScheme := ⟨p, hp⟩
  have e : V.ι ((f' ∣_ V) p') = f' p := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  have hB := hV (f' p) hp
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (f' ⁻¹ᵁ V).ι p').mpr
    ((isRegularLocalRing_stalk_iff_of_isOpenImmersion (f' ∣_ V) p').mp
      ((isRegularLocalRing_stalk_iff_of_isOpenImmersion V.ι _).mp (e ▸ hB)))

/-- **The induction step.** If the node `xy = a` has a resolution, so does `xy = π²a`: glue the
resolution of the `π`-chart `xy = a` of the blowup of `xy = π²a` at its origin into the blowup,
along the union of the two regular coordinate charts. -/
private theorem hasResolution_pow_two_mul [IsDomain R] [IsDiscreteValuationRing R]
    (hπ : Irreducible π) {a : R} (h : HasResolution a) : HasResolution (π ^ 2 * a) := by
  obtain ⟨Y, f, hfp, hfi, hY, hfn⟩ := h
  have hπ0 : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  -- `j` is the `π`-chart of the blowup, and `V` the union of its two coordinate charts.
  set j := blowupBaseChartι a hπ0
  set V := ⨆ i, (blowupCoordChartι a i hπ0).opensRange
  have hjV : j ⁻¹ᵁ V =
      (⨆ i, PrimeSpectrum.basicOpen (coord a i) : (Spec (.of (NodeAlgebra R a))).Opens) := by
    simp only [V, j, Scheme.Hom.preimage_iSup,
      blowupBaseChartι_preimage_opensRange_blowupCoordChartι]
  have : IsIso (f ∣_ j ⁻¹ᵁ V) := by
    rw [hjV]
    exact hfi
  obtain ⟨Y', ι, f', _, hpb, hiso, hcov⟩ := j.exists_isPullback_isIso_morphismRestrict V f
  set b := Proj.toSpecZero (grade (originIdeal π (π ^ 2 * a))) ≫
    Spec.map (gradeZeroEquiv (originIdeal π (π ^ 2 * a))).toCommRingCatIso.hom
  -- Instance search does not find `ContainsIdentities` through `IsMultiplicative` here.
  have : MorphismProperty.ContainsIdentities @IsProper :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : IsProper f' := IsZariskiLocalAtTarget.of_isPullback_of_isIso_morphismRestrict
    (P := @IsProper) hpb hiso
    (opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι a hπ0) hfp
  -- The Rees algebra of the finitely generated ideal `(π, x, y)` is of finite type, so the
  -- blowup `Proj` is proper over its degree-zero part.
  have : Algebra.FiniteType (NodeAlgebra R (π ^ 2 * a))
      (_root_.reesAlgebra (originIdeal π (π ^ 2 * a))) :=
    ⟨(_root_.reesAlgebra _).fg_top.mpr (reesAlgebra.fg
      (by rw [originIdeal_def]; exact Submodule.fg_span (Set.toFinite _)))⟩
  have : IsNoetherianRing (NodeAlgebra R (π ^ 2 * a)) := Algebra.FiniteType.isNoetherianRing R _
  have : IsRegularRing (NodeAlgebra R π) := by
    have h1 := (isRegularRing_pow_iff hπ 1).mpr le_rfl
    rwa [pow_one] at h1
  have : IsProper b :=
    MorphismProperty.comp_mem (W := @IsProper) _ _ inferInstance (MorphismProperty.of_isIso _ _)
  have : IsProper (f' ≫ b) := inferInstance
  refine ⟨Y', f' ≫ b, this, ?_, ?_, ?_⟩
  · -- Over `D(x) ∪ D(y)` the blowup is an isomorphism with image in `V`, over which so is `f'`.
    rw [morphismRestrict_comp]
    have hb : IsIso (b ∣_ (⨆ i, PrimeSpectrum.basicOpen (coord (π ^ 2 * a) i) :
        (Spec (.of (NodeAlgebra R (π ^ 2 * a)))).Opens)) := by
      refine isIso_morphismRestrict_toSpecZero_reesAlgebra_of_disjoint_zeroLocus
        (Set.disjoint_left.mpr fun p hp hz ↦ ?_)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
      exact hi (hz (coord_mem_originIdeal π _ i))
    have hf' : IsIso (f' ∣_ b ⁻¹ᵁ (⨆ i, PrimeSpectrum.basicOpen (coord (π ^ 2 * a) i) :
        (Spec (.of (NodeAlgebra R (π ^ 2 * a)))).Opens)) := by
      refine (MorphismProperty.isomorphisms.iff _).mp
        (IsZariskiLocalAtTarget.restrict_of_le (MorphismProperty.isomorphisms Scheme)
          ((MorphismProperty.isomorphisms.iff _).mpr hiso) ?_)
      intro x hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨i, preimage_basicOpen_coord_le_opensRange_blowupCoordChartι a i hπ0 hi⟩
    exact IsIso.comp_isIso' hf' hb
  · -- `Y'` is covered by `Y` and by the regular coordinate charts.
    have := LocallyOfFiniteType.isLocallyNoetherian (f' ≫ b)
    refine isRegular_of_isIso_morphismRestrict ι f' V hcov fun x hx ↦ ?_
    obtain ⟨i, q, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ q).mpr inferInstance
  · -- On `Y` the composite is the resolution of `xy = a`, and over `V` it is the blowup.
    have hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) = blowupToSpec π a := by
      rw [blowupToSpec_def, Category.assoc]
    rw [Category.assoc, hb]
    refine IsZariskiLocalAtSource.of_iSup_eq_top (fun t ↦ cond t ι.opensRange (f' ⁻¹ᵁ V))
      (by rwa [iSup_bool_eq]) fun t ↦ ?_
    cases t
    · dsimp only [Bool.cond_false]
      rw [← morphismRestrict_ι_assoc,
        MorphismProperty.cancel_left_of_respectsIso (P := @AtWorstNodalOfRelativeDimensionOne)]
      exact IsZariskiLocalAtSource.comp (atWorstNodalOfRelativeDimensionOne_blowup a hπ0) _
    · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @AtWorstNodalOfRelativeDimensionOne)
        ι.isoOpensRange.hom]
      dsimp only [Bool.cond_true]
      rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, ← hpb.w_assoc, blowupBaseChartι_blowupToSpec]
      exact hfn

/-- The node `xy = πⁿ` has a resolution for every `n`, by induction on `n` in steps of two. -/
private theorem hasResolution_pow [IsDomain R] [IsDiscreteValuationRing R] (hπ : Irreducible π) :
    ∀ n : ℕ, HasResolution (π ^ n)
  | 0 => have := (isRegularRing_pow_iff hπ 0).mpr zero_le_one; hasResolution_of_isRegularRing
  | 1 => have := (isRegularRing_pow_iff hπ 1).mpr le_rfl; hasResolution_of_isRegularRing
  | n + 2 => by
    rw [pow_add, mul_comm]
    exact hasResolution_pow_two_mul hπ (hasResolution_pow hπ n)

/-- **Resolution of the node `xy = πⁿ`.** Let `π` be a uniformizer of a discrete valuation ring
`R`. For every `n` there is a proper morphism `f : Y ⟶ Spec R[x, y] ⧸ (xy - πⁿ)` such that

* `f` is an isomorphism over the open `D(x) ∪ D(y)`, the complement of `V(x, y)`; for `n ≥ 1`
  this closed subset is the single point `(π, x, y)`, the node of the special fibre;
* `Y` is a regular scheme;
* `Y` is at worst nodal of relative dimension one over `Spec R`. -/
theorem exists_resolution [IsDomain R] [IsDiscreteValuationRing R] (hπ : Irreducible π) (n : ℕ) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of (NodeAlgebra R (π ^ n)))), IsProper f ∧
      IsIso (f ∣_ (⨆ i, PrimeSpectrum.basicOpen (coord (π ^ n) i) :
        (Spec (.of (NodeAlgebra R (π ^ n)))).Opens)) ∧ IsRegular Y ∧
      AtWorstNodalOfRelativeDimensionOne (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R _))) :=
  hasResolution_pow hπ n

end TauCeti.NodeAlgebra
