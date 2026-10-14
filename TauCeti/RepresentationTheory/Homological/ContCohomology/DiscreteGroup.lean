/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DimensionShifting.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import TauCeti.RepresentationTheory.Rep.TensorShortExact
import TauCeti.RepresentationTheory.Coinduced

/-!
# Continuous cohomology of a finite discrete group in every degree

Let `G` be a finite group with the discrete topology and `M` a discrete `G`-module. In every
degree `n` the canonical continuous cohomology `Hⁿ(G, M)` is isomorphic to Mathlib's discrete
group cohomology of the representation `Rep.ofDistribMulAction ℤ G M`
(`TauCeti.ContCohomology.nonempty_continuousCohomology_addEquiv_groupCohomology`).

In degrees `0` and `1` this is the composite of the explicit low-degree comparisons on both sides.
The higher degrees follow by dimension shifting, run in parallel in the two theories along the
same short exact sequence

```text
0 → M → Coind_1^G M → Coind_1^G M ⧸ M → 0.
```

Its middle term is acyclic in positive degrees for continuous cohomology
(`TauCeti.ContCohomology.dimensionShiftIso`) and, being the representation `coindBot ℤ G M`
coinduced from the trivial subgroup, for group cohomology (`groupCohomology.isZero_coindBot_succ`).
So the two connecting maps identify `Hⁿ⁺²(G, M)` with `Hⁿ⁺¹(G, Coind_1^G M ⧸ M)` in both
theories, and induction on the degree, over all coefficient modules at once, finishes.

This is what lets a vanishing statement about the cohomology of the finite layers of a profinite
group, proved in Mathlib's `groupCohomology` (for instance by Tate's theorem), be read in the
finite-quotient colimit description of continuous cohomology.

## Main results

* `TauCeti.ContCohomology.nonempty_continuousCohomology_addEquiv_groupCohomology`: an additive
  equivalence `Hⁿ(G, M) ≃+ groupCohomology (Rep.ofDistribMulAction ℤ G M) n` exists for every `n`.

## Implementation notes

The isomorphism is assembled from the connecting maps of the two long exact sequences and from
the low-degree comparisons; its naturality is not proved here, so it is stated as the existence of
an additive equivalence, which is the form vanishing and finiteness statements consume.
Finiteness of `G` enters only through the acyclicity of `Coind_1^G M` in continuous cohomology,
which is proved for compact groups.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.2.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §7 (dimension shifting).
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.ContCohomology

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]

/-- An action of a discrete group on a discrete module is continuous. -/
local instance continuousSMul_of_discreteTopology : ContinuousSMul G M :=
  ⟨continuous_of_discreteTopology⟩

/-! ### The dimension-shifting sequence in `Rep ℤ G` -/

section ShortComplex

/-- The projection `Coind_⊥^G M → Coind_1^G M ⧸ M` from the representation coinduced from the
trivial subgroup onto the cokernel of the unit of coinduction. Every function on the discrete group
`G` is continuous, so it reads a function `G → M` as an element of `Coind_1^G M`. -/
private def coindBotToCoindQuotient :
    Rep.coindBot ℤ G M ⟶ Rep.ofDistribMulAction ℤ G (CoindQuotient G ⊥ M) :=
  Rep.ofHom
    { toLinearMap := (CoindQuotient.mk G ⊥ M).toIntLinearMap ∘ₗ AddMonoidHom.toIntLinearMap
        { toFun := fun f : Rep.coindBot ℤ G M =>
            DiscreteCoind.ofContinuousMap G M ⟨f.1, continuous_of_discreteTopology⟩
          map_zero' := DiscreteCoind.ext fun _ => by simp
          map_add' := fun _ _ => DiscreteCoind.ext fun _ => by simp }
      isIntertwining' := fun g => LinearMap.ext fun f =>
        (congrArg (CoindQuotient.mk G ⊥ M) (DiscreteCoind.ext fun x => by
          simpa using Representation.coind_apply_coe_apply _ _ f g x)).trans
          (CoindQuotient.mk_smul g _) }

/-- The projection reads a function `f : G → M` as the class of `f` in `Coind_1^G M ⧸ M`. -/
private theorem coindBotToCoindQuotient_hom_apply (f : Rep.coindBot ℤ G M) :
    (coindBotToCoindQuotient G M).hom f =
      CoindQuotient.mk G ⊥ M
        (DiscreteCoind.ofContinuousMap G M ⟨f.1, continuous_of_discreteTopology⟩) :=
  (rfl)

/-- **The dimension-shifting sequence** `0 → M → Coind_⊥^G M → Coind_1^G M ⧸ M → 0` in `Rep ℤ G`,
for a discrete group `G`: the canonical embedding into the representation coinduced from the
trivial subgroup, followed by the projection onto the cokernel of the unit of coinduction, the
module on which continuous dimension shifting runs. -/
private def coindBotShortComplex : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (Rep.coindBotUnit (Rep.ofDistribMulAction ℤ G M)) (coindBotToCoindQuotient G M)
    (by
      ext (a : M)
      refine (coindBotToCoindQuotient_hom_apply G M _).trans
        ((CoindQuotient.mk_eq_zero_iff (G := G) (U := ⊥) (M := M)).2
          ⟨a, DiscreteCoind.ext fun x => ?_⟩)
      simp only [AddMonoidHom.coe_mk, MonoidHom.coe_id, DistribMulActionHom.toFun_eq_coe,
        ZeroHom.coe_mk, DiscreteCoind.unit_apply, Representation.IntertwiningMap.coe_toLinearMap,
        DiscreteCoind.ofContinuousMap_apply, ContinuousMap.coe_mk]
      exact (Rep.coindBotUnit_hom_apply_coe (Rep.ofDistribMulAction ℤ G M) a x).symm)

/-- The dimension-shifting sequence is short exact. -/
private theorem coindBotShortComplex_shortExact : (coindBotShortComplex G M).ShortExact where
  exact := by
    rw [Rep.exact_iff_function_exact]
    intro (f : Rep.coindBot ℤ G M)
    refine (Eq.congr_left (coindBotToCoindQuotient_hom_apply G M f)).trans <|
      (CoindQuotient.mk_eq_zero_iff (G := G) (U := ⊥) (M := M)).trans
        (exists_congr fun m => ⟨fun h => Subtype.ext (funext fun x => ?_), fun h => ?_⟩)
    · have hx : x • m = f.1 x := by simpa using DFunLike.congr_fun h x
      exact (Rep.coindBotUnit_hom_apply_coe (Rep.ofDistribMulAction ℤ G M) m x).trans hx
    · refine DiscreteCoind.ext fun x => ?_
      simp only [AddMonoidHom.coe_mk, MonoidHom.coe_id, DistribMulActionHom.toFun_eq_coe,
        ZeroHom.coe_mk, DiscreteCoind.unit_apply, DiscreteCoind.ofContinuousMap_apply,
        ContinuousMap.coe_mk]
      exact (Rep.coindBotUnit_hom_apply_coe (Rep.ofDistribMulAction ℤ G M) m x).symm.trans
        (congrFun (congrArg Subtype.val h) x)
  mono_f := Rep.coindBotUnit_mono _
  epi_g := (Rep.epi_iff_surjective _).2 fun q => by
    obtain ⟨F, rfl⟩ := CoindQuotient.mk_surjective (G := G) (U := ⊥) (M := M) q
    refine ⟨(Rep.coindBotEquivPi ℤ G M).symm F, (coindBotToCoindQuotient_hom_apply G M _).trans
      (congrArg (CoindQuotient.mk G ⊥ M) (DiscreteCoind.ext fun x => ?_))⟩
    rw [DiscreteCoind.ofContinuousMap_apply, ContinuousMap.coe_mk,
      Rep.coindBotEquivPi_symm_apply_coe]

/-- **Dimension shifting in group cohomology along the continuous dimension-shifting module**:
`Hⁿ⁺¹(G, Coind_1^G M ⧸ M) ≅ Hⁿ⁺²(G, M)`, the connecting map of `coindBotShortComplex`, whose middle
term has no cohomology in positive degrees. -/
private def groupCohomologyDimensionShiftIso (n : ℕ) :
    groupCohomology (Rep.ofDistribMulAction ℤ G (CoindQuotient G ⊥ M)) (n + 1) ≅
      groupCohomology (Rep.ofDistribMulAction ℤ G M) (n + 2) :=
  (groupCohomology.map_cochainsFunctor_shortExact
    (coindBotShortComplex_shortExact G M)).δIso (n + 1) (n + 2) rfl
    (groupCohomology.isZero_coindBot_succ _ n) (groupCohomology.isZero_coindBot_succ _ (n + 1))

end ShortComplex

/-! ### The comparison in every degree -/

section Comparison

variable [Finite G]

/-- **The continuous cohomology of a finite discrete group is its group cohomology**, in every
degree: for a finite group `G` with the discrete topology and a discrete `G`-module `M`,
`Hⁿ(G, M)` is additively isomorphic to Mathlib's `groupCohomology` of
`Rep.ofDistribMulAction ℤ G M`. -/
theorem nonempty_continuousCohomology_addEquiv_groupCohomology (n : ℕ) :
    Nonempty (continuousCohomology n (ofDiscreteModule ℤ G M) ≃+
      groupCohomology (Rep.ofDistribMulAction ℤ G M) n) := by
  have : CompactSpace G := Finite.compactSpace
  induction n using Nat.twoStepInduction generalizing M with
  | zero =>
    exact ⟨(explicitH0IsoContinuousCohomology G M).toContinuousLinearEquiv.toAddEquiv.symm.trans
      (explicitH0IsoGroupCohomology G M)⟩
  | one =>
    exact ⟨(explicitH1AddEquivContinuousCohomology G M).symm.trans
      (explicitH1IsoGroupCohomology G M)⟩
  | more n _ ih =>
    -- shift both sides down to `Hⁿ⁺¹(G, Coind_1^G M ⧸ M)`
    obtain ⟨e⟩ := ih (CoindQuotient G ⊥ M)
    exact ⟨(dimensionShiftIso G M (n + 1) n.succ_pos).toContinuousLinearEquiv.toAddEquiv.trans
      (e.trans (groupCohomologyDimensionShiftIso G M n).toLinearEquiv.toAddEquiv)⟩

end Comparison

end TauCeti.ContCohomology
