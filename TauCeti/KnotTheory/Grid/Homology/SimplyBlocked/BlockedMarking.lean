/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.Cone
public import TauCeti.KnotTheory.Grid.Homology.PartiallyBlocked

/-!
# Changing the blocked marking of a knot grid

Over `𝔽₂`, the homology obtained by blocking a single `O`-marking does not depend,
as a vector space, on which marking is blocked. The comparison uses the chosen
`X`-marking homotopy between the two variable actions, rather than a dimension
count. It factors through the mapping cones of these injective variable actions.

`IsKnot.partiallyBlockedHomologyChangeBlockedColumnEquiv` compares the two quotient
models. `IsKnot.simplyBlockedHomologyChangeBlockedColumnEquiv` transports this
comparison to the actual categorical simply blocked homologies. These are ungraded
comparisons; no assertion about the Maslov or Alexander degrees is made here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.6:
variable actions on a component are chain homotopic, and blocking any one of its
markings gives the simply blocked theory.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ}

local notation "F" => ZMod 2
local notation "P" => MvPolynomial (Fin n) F
local notation "M" => GridChainMinus F n

private noncomputable def variableMap (i : Fin n) : M →ₗ[F] M :=
  DistribSMul.toLinearMap F M (MvPolynomial.X i : P)

private theorem variableMap_apply (i : Fin n) (c : M) :
    variableMap i c = (MvPolynomial.X i : P) • c := (rfl)

private theorem range_variableMap (i : Fin n) :
    LinearMap.range (variableMap i) = (blockedChains F {i}).restrictScalars F := by
  ext c
  rw [Submodule.restrictScalars_mem, ← simplyBlockedSpecialization_eq_zero_iff,
    exact_X_smul_simplyBlockedSpecialization F i]
  rfl

variable (G : GridDiagram n)

local notation "d" => LinearMap.restrictScalars F (GridDiagram.unblockedDifferential G F)
local notation "hd" => restrictScalars_unblockedDifferential_comp_self_eq_zero G

private theorem variableMap_comp (i : Fin n) :
    variableMap i ∘ₗ d = d ∘ₗ variableMap i := by
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, variableMap_apply, LinearMap.restrictScalars_apply, map_smul]

private theorem variableMap_injective (i : Fin n) : Function.Injective (variableMap i) :=
  X_smul_gridChainMinus_injective F i

private noncomputable def singletonQuotientHomologyEquiv (i : Fin n) :
    (d).quotientHomology hd (LinearMap.range (variableMap i))
        (LinearMap.range_le_comap_of_commute d (variableMap i) (variableMap_comp G i)) ≃ₗ[F]
      G.partiallyBlockedHomology {i} :=
  LinearMap.quotientHomologyEquivOfSurjective hd
    (LinearMap.range_le_comap_of_commute d (variableMap i) (variableMap_comp G i))
    ((d).mapQ_comp_mapQ_eq_zero hd _ (G.blockedChains_le_comap_unblockedDifferential {i}))
    ((blockedChains F {i}).restrictScalars F).mkQ
    (Submodule.mkQ_surjective _)
    ((Submodule.ker_mkQ _).trans (range_variableMap i).symm)
    (by apply LinearMap.ext; intro c; rfl)

private theorem singletonQuotientHomologyEquiv_mk (i : Fin n) (c : M)
    (hc : d c ∈ LinearMap.range (variableMap i)) :
    singletonQuotientHomologyEquiv G i
        (LinearMap.quotientHomologyClass hd
          (LinearMap.range_le_comap_of_commute d (variableMap i) (variableMap_comp G i)) c hc) =
      LinearMap.quotientHomologyClass hd
        (G.blockedChains_le_comap_unblockedDifferential {i}) c
        ((range_variableMap i).le hc) := by
  unfold singletonQuotientHomologyEquiv
  rw [LinearMap.quotientHomologyClass_def,
    LinearMap.quotientHomologyEquivOfSurjective_mk (hm := hc)]
  simp only [LinearMap.quotientHomologyClass_def, Submodule.mkQ_apply]

namespace IsKnot

variable {G} (hG : G.IsKnot) (i j : Fin n)

private theorem variableMap_homotopy :
    variableMap i - variableMap j =
      d ∘ₗ (hG.XSmulHomotopy F i j).restrictScalars F +
        (hG.XSmulHomotopy F i j).restrictScalars F ∘ₗ d := by
  have hh := hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp F i j
  apply LinearMap.ext
  intro c
  have hc : G.unblockedDifferential F (hG.XSmulHomotopy F i j c) +
      hG.XSmulHomotopy F i j (G.unblockedDifferential F c) =
        (MvPolynomial.X i + MvPolynomial.X j : P) • c := congr($hh c)
  have hneg : -(MvPolynomial.X j : P) = MvPolynomial.X j := CharTwo.neg_eq _
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.restrictScalars_apply, variableMap_apply, sub_eq_add_neg, ← neg_smul, hneg,
    add_smul] using hc.symm

/-- Changing the single blocked column of a knot grid gives isomorphic partially blocked
homologies. The comparison is induced by the specified `XSmulHomotopy`. -/
noncomputable def partiallyBlockedHomologyChangeBlockedColumnEquiv :
    G.partiallyBlockedHomology {i} ≃ₗ[F] G.partiallyBlockedHomology {j} :=
  (singletonQuotientHomologyEquiv G i).symm.trans
    ((LinearMap.quotientHomologyEquivOfHomotopy d hd
      (variableMap i) (variableMap_comp G i) (variableMap j)
      ((hG.XSmulHomotopy F i j).restrictScalars F) (variableMap_comp G j)
      (variableMap_homotopy hG i j) (variableMap_injective i) (variableMap_injective j)).trans
        (singletonQuotientHomologyEquiv G j))

private theorem differential_eq_zero_of_differential_eq_X_smul (c a : M)
    (hc : G.unblockedDifferential F c = (MvPolynomial.X i : P) • a) :
    G.unblockedDifferential F a = 0 := by
  apply X_smul_gridChainMinus_injective F i
  dsimp only
  rw [← map_smul, ← hc, smul_zero]
  exact congr($(G.unblockedDifferential_comp_self_eq_zero F) c)

private theorem differential_changeBlockedColumn (c a : M)
    (hc : G.unblockedDifferential F c = (MvPolynomial.X i : P) • a) :
    G.unblockedDifferential F (c + hG.XSmulHomotopy F i j a) = (MvPolynomial.X j : P) • a := by
  have hda := differential_eq_zero_of_differential_eq_X_smul (i := i) c a hc
  have hh : G.unblockedDifferential F (hG.XSmulHomotopy F i j a) =
      (MvPolynomial.X i + MvPolynomial.X j : P) • a := by
    have h := congr($(hG.unblockedDifferential_comp_XSmulHomotopy_add_XSmulHomotopy_comp F i j) a)
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, hda, map_zero, add_zero,
      LinearMap.smul_apply, LinearMap.id_apply] using h
  rw [map_add, hc, hh, add_smul, ← add_assoc, ← add_smul,
    CharTwo.add_self_eq_zero, zero_smul, zero_add]

/-- On representatives, if `∂c = V_i a`, changing the blocked column from `i` to `j`
sends the class of `c` to the class of `c + H a`, for the chosen variable homotopy `H`. -/
theorem partiallyBlockedHomologyChangeBlockedColumnEquiv_mk (c a : M)
    (hc : G.unblockedDifferential F c = (MvPolynomial.X i : P) • a) :
    hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j
        (LinearMap.quotientHomologyClass hd
          (G.blockedChains_le_comap_unblockedDifferential {i}) c
          (by rw [LinearMap.restrictScalars_apply, hc]
              exact X_smul_mem_blockedChains (Finset.mem_singleton_self i) a)) =
      LinearMap.quotientHomologyClass hd
        (G.blockedChains_le_comap_unblockedDifferential {j}) (c + hG.XSmulHomotopy F i j a)
        (by rw [LinearMap.restrictScalars_apply, differential_changeBlockedColumn hG i j c a hc]
            exact X_smul_mem_blockedChains (Finset.mem_singleton_self j) a) := by
  have hda := differential_eq_zero_of_differential_eq_X_smul (i := i) c a hc
  let z : LinearMap.ker (LinearMap.mappingCone d d (variableMap i)) := ⟨(a, c), by
    simp only [LinearMap.mem_ker, LinearMap.mappingCone_apply, variableMap_apply,
      LinearMap.restrictScalars_apply, hda, neg_zero, hc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, Prod.mk_zero_zero]⟩
  have h := LinearMap.quotientHomologyEquivOfHomotopy_quotientHomologyClass d hd
    (variableMap i) (variableMap_comp G i) (variableMap j)
    ((hG.XSmulHomotopy F i j).restrictScalars F) (variableMap_comp G j)
    (variableMap_homotopy hG i j) (variableMap_injective i) (variableMap_injective j) z
  have hsrc := singletonQuotientHomologyEquiv_mk G i c
    (by rw [LinearMap.restrictScalars_apply, hc]; exact ⟨a, rfl⟩)
  rw [← hsrc]
  unfold partiallyBlockedHomologyChangeBlockedColumnEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, h,
    singletonQuotientHomologyEquiv_mk]
  rfl

/-- Simply blocked homology of a knot grid is independent, as an `𝔽₂`-vector space, of the
blocked marking. Both carriers use their actual restricted coefficient actions. -/
noncomputable def simplyBlockedHomologyChangeBlockedColumnEquiv :
    (ModuleCat.restrictScalars (C : F →+* MvPolynomial {c : Fin n // c ≠ i} F)).obj
        (hG.simplyBlockedHomology F i) ≃ₗ[F]
      (ModuleCat.restrictScalars (C : F →+* MvPolynomial {c : Fin n // c ≠ j} F)).obj
        (hG.simplyBlockedHomology F j) :=
  (hG.partiallyBlockedHomologySingletonEquiv i).symm.trans
    ((hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j).trans
      (hG.partiallyBlockedHomologySingletonEquiv j))

/-- On classes in the quotient model, the categorical comparison is the same change of
blocked marking. Together with the representative formula for the quotient comparison, this
characterizes its action without unfolding the homology equivalences. -/
@[simp]
theorem simplyBlockedHomologyChangeBlockedColumnEquiv_apply
    (x : G.partiallyBlockedHomology {i}) :
    hG.simplyBlockedHomologyChangeBlockedColumnEquiv i j
        (hG.partiallyBlockedHomologySingletonEquiv i x) =
      hG.partiallyBlockedHomologySingletonEquiv j
        (hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j x) := by
  unfold simplyBlockedHomologyChangeBlockedColumnEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply]

/-- The inverse categorical comparison is the inverse quotient comparison on represented
classes. -/
@[simp]
theorem simplyBlockedHomologyChangeBlockedColumnEquiv_symm_apply
    (x : G.partiallyBlockedHomology {j}) :
    (hG.simplyBlockedHomologyChangeBlockedColumnEquiv i j).symm
        (hG.partiallyBlockedHomologySingletonEquiv j x) =
      hG.partiallyBlockedHomologySingletonEquiv i
        ((hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j).symm x) := by
  apply (hG.simplyBlockedHomologyChangeBlockedColumnEquiv i j).injective
  simp only [LinearEquiv.apply_symm_apply,
    simplyBlockedHomologyChangeBlockedColumnEquiv_apply]

end IsKnot

end TauCeti.GridDiagram
