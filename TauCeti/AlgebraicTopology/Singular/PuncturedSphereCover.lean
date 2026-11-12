/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
import TauCeti.AlgebraicTopology.Sphere.Zero

/-!
# Open covers of a twice-punctured sphere

Let `A` and `B` be path-connected open subsets of the `2`-sphere whose union is the sphere with
two points removed. Then `A ∩ B` has at most two path components
(`TauCeti.enatCard_zerothHomotopy_inter_le_two`).

This is the bound behind the classical fact that a crosscut cuts a plane domain into at most two
pieces. There `A` is the domain, `B` is the complement of the closed crosscut on the Riemann sphere,
and the two removed points are the endpoints of the crosscut.

The proof is homological. The sphere with two points removed is the complement of an embedded
`S⁰`, so its first reduced homology is one copy of the coefficients
(`TauCeti.reducedSingularHomologySphereComplRangeSphereIso`, Hatcher, Proposition 2B.1(b)).
Since `A` and `B` are path-connected, the reduced Mayer–Vietoris connecting morphism
`H₁(A ∪ B) ⟶ H_red₀(A ∩ B)` is an epimorphism (`TopCat.epi_reducedMayerVietorisδ`). With rational
coefficients, the rank of `H_red₀(A ∩ B)` is the number of path components of `A ∩ B` minus one
(`TauCeti.rank_reducedSingularHomologyFunctor_zero`), so there are at most two of them.

## Main results

* `TauCeti.enatCard_zerothHomotopy_inter_le_two`: two path-connected open subsets of `S²` covering
  `S²` minus two points meet in at most two path components.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (the Mayer–Vietoris sequence) and
  Proposition 2B.1.
-/

public section

open CategoryTheory Limits AlgebraicTopology Topology Set TopCat Metric Module

universe w

namespace TauCeti

/-- **Two path-connected open sets covering a twice-punctured sphere meet in at most two path
components.** Let `A` and `B` be path-connected open subsets of the unit sphere of a
three-dimensional real normed space, and suppose that `A ∪ B` is the sphere with two distinct
points removed. Then `A ∩ B` has at most two path components. -/
theorem enatCard_zerothHomotopy_inter_le_two {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hF : finrank ℝ F = 3) {A B : Set (sphere (0 : F) 1)} (hA : IsOpen A)
    (hB : IsOpen B) (hAc : IsPathConnected A) (hBc : IsPathConnected B)
    {p q : sphere (0 : F) 1} (hpq : p ≠ q) (hAB : A ∪ B = {p, q}ᶜ) :
    ENat.card (ZerothHomotopy ↥(A ∩ B)) ≤ 2 := by
  classical
  let K := ULift.{w} ℚ
  let M := ModuleCat.of K K
  obtain ⟨h, hc, hi, hrange⟩ := exists_continuous_injective_range_sphere_eq_pair hpq
  -- The Mayer–Vietoris sequence is stated for an open cover of a space, here the complement `E`
  -- of `{p, q}`, by the preimages `U` and `V` of `A` and `B`.
  let E : Set (sphere (0 : F) 1) := (range h)ᶜ
  have hABE : A ∪ B = E := by simp only [E, hAB, hrange]
  have hAE : A ⊆ E := hABE ▸ subset_union_left
  have hBE : B ⊆ E := hABE ▸ subset_union_right
  let U : Set (of ↥E) := Subtype.val ⁻¹' A
  let V : Set (of ↥E) := Subtype.val ⁻¹' B
  have hU : IsOpen U := hA.preimage continuous_subtype_val
  have hV : IsOpen V := hB.preimage continuous_subtype_val
  have hUV : U ∪ V = univ := eq_univ_of_forall fun z ↦ hABE.ge z.2
  have : PathConnectedSpace ↥U := isPathConnected_iff_pathConnectedSpace.1 (hAc.preimage_coe hAE)
  have : PathConnectedSpace ↥V := isPathConnected_iff_pathConnectedSpace.1 (hBc.preimage_coe hBE)
  have : Epi (reducedMayerVietorisδ M hU hV hUV 0) := epi_reducedMayerVietorisδ M hU hV hUV
    (isZero_reducedSingularHomologyFunctor_zero M (of ↥U))
    (isZero_reducedSingularHomologyFunctor_zero M (of ↥V))
  -- The first homology of `E` is one copy of the coefficients.
  let e : (toSSet.obj (of ↥E)).homology M 1 ≅ M :=
    ((reducedSingularHomologySuccIso M 0).app (of ↥E)).symm ≪≫
      reducedSingularHomologySphereComplRangeSphereIso M (i := 1) (by simp [hF]) hc hi
  -- `U ∩ V` is `Subtype.val ⁻¹' (A ∩ B)` by `Set.preimage_inter`, which holds by definition.
  let i : of ↥(U ∩ V) ≅ of ↥(A ∩ B) := isoOfHomeo
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (inter_subset_left.trans (hAE.trans Subtype.range_coe.ge)))
  let f : M ⟶ (reducedSingularHomologyFunctor M 0).obj (of ↥(A ∩ B)) :=
    e.inv ≫ reducedMayerVietorisδ M hU hV hUV 0 ≫ (reducedSingularHomologyFunctor M 0).map i.hom
  have hf : Function.Surjective f := (ModuleCat.epi_iff_surjective f).1 inferInstance
  have hrank := (LinearMap.rank_le_of_surjective f.hom hf).trans_eq (Module.rank_self K)
  -- With rational coefficients, the rank counts the path components other than that of a point.
  by_contra h3
  have h3 : 3 ≤ ENat.card (ZerothHomotopy ↥(A ∩ B)) := Order.add_one_le_of_lt (not_le.1 h3)
  obtain ⟨c⟩ := (ENat.one_le_card_iff_nonempty _).1 ((by norm_num : (1 : ℕ∞) ≤ 3).trans h3)
  obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective c
  rw [rank_reducedSingularHomologyFunctor_zero z, Cardinal.le_one_iff_subsingleton] at hrank
  obtain ⟨c, hc, -⟩ := ENat.exists_ne_ne_of_three_le h3 (.mk z) (.mk z)
  obtain ⟨d, hdz, hdc⟩ := ENat.exists_ne_ne_of_three_le h3 (.mk z) c
  exact hdc (congrArg Subtype.val (Subsingleton.elim (⟨d, hdz⟩ : {c // c ≠ _}) ⟨c, hc⟩))

end TauCeti
