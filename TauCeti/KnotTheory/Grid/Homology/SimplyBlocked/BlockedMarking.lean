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
as a vector space, on which marking is blocked. The comparison uses the chosen null-homotopy
`IsKnot.XSmulHomotopy` of `V_i + V_j`, rather than a dimension count. It factors through the
mapping cones of these injective variable actions. Since that homotopy is a choice, the
comparison is not asserted to be canonical, to be the identity when `i = j`, or to preserve
gradings.

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
  simp only [LinearMap.mem_range, Set.mem_range, variableMap_apply]

variable (G : GridDiagram n)

local notation "d" => LinearMap.restrictScalars F (GridDiagram.unblockedDifferential G F)
local notation "hd" => restrictScalars_unblockedDifferential_comp_self_eq_zero G

private theorem variableMap_comp (i : Fin n) :
    variableMap i ∘ₗ d = d ∘ₗ variableMap i := by
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, variableMap_apply, LinearMap.restrictScalars_apply, map_smul]

private theorem variableMap_injective (i : Fin n) : Function.Injective (variableMap i) :=
  fun _ _ hxy => X_smul_gridChainMinus_injective F i (by simpa only [variableMap_apply] using hxy)

private noncomputable def singletonQuotientHomologyEquiv (i : Fin n) :
    (d).quotientHomology hd (LinearMap.range (variableMap i))
        (LinearMap.range_le_comap_range_of_comp_eq (variableMap i) (variableMap_comp G i)) ≃ₗ[F]
      G.partiallyBlockedHomology {i} :=
  LinearMap.quotientHomologyEquivOfSurjective hd
    (LinearMap.range_le_comap_range_of_comp_eq (variableMap i) (variableMap_comp G i))
    ((d).mapQ_comp_mapQ_eq_zero hd _ (G.blockedChains_le_comap_unblockedDifferential {i}))
    ((blockedChains F {i}).restrictScalars F).mkQ
    (Submodule.mkQ_surjective _)
    ((Submodule.ker_mkQ _).trans (range_variableMap i).symm)
    (((blockedChains F {i}).restrictScalars F).mapQ_mkQ _ d).symm

private theorem singletonQuotientHomologyEquiv_quotientHomologyClass (i : Fin n) (c : M)
    (hc : d c ∈ LinearMap.range (variableMap i)) :
    singletonQuotientHomologyEquiv G i
        (LinearMap.quotientHomologyClass hd
          (LinearMap.range_le_comap_range_of_comp_eq (variableMap i) (variableMap_comp G i))
          c hc) =
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
homologies. The comparison is induced by the chosen null-homotopy `XSmulHomotopy`. -/
noncomputable def partiallyBlockedHomologyChangeBlockedColumnEquiv :
    G.partiallyBlockedHomology {i} ≃ₗ[F] G.partiallyBlockedHomology {j} :=
  (singletonQuotientHomologyEquiv G i).symm.trans
    ((LinearMap.quotientHomologyEquivOfHomotopy d hd d hd
      (variableMap i) (variableMap_comp G i) (variableMap j)
      ((hG.XSmulHomotopy F i j).restrictScalars F) (variableMap_comp G j)
      (variableMap_homotopy hG i j) (variableMap_injective i) (variableMap_injective j)).trans
        (singletonQuotientHomologyEquiv G j))

/-- On representatives, if `∂c = V_i a`, changing the blocked column from `i` to `j`
sends the class of `c` to the class of `c + H a`, for the chosen variable homotopy `H`. -/
theorem partiallyBlockedHomologyChangeBlockedColumnEquiv_quotientHomologyClass (c a : M)
    (hc : G.unblockedDifferential F c = (MvPolynomial.X i : P) • a) :
    hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j
        (LinearMap.quotientHomologyClass hd
          (G.blockedChains_le_comap_unblockedDifferential {i}) c
          (by rw [LinearMap.restrictScalars_apply, hc]
              exact X_smul_mem_blockedChains (Finset.mem_singleton_self i) a)) =
      LinearMap.quotientHomologyClass hd
        (G.blockedChains_le_comap_unblockedDifferential {j}) (c + hG.XSmulHomotopy F i j a)
        (by rw [LinearMap.restrictScalars_apply,
              hG.unblockedDifferential_add_XSmulHomotopy_left F i j c a hc]
            exact X_smul_mem_blockedChains (Finset.mem_singleton_self j) a) := by
  have hc' : d c = variableMap i a := by
    rw [LinearMap.restrictScalars_apply, hc, variableMap_apply]
  have h := LinearMap.quotientHomologyEquivOfHomotopy_quotientHomologyClass d hd d hd
    (variableMap i) (variableMap_comp G i) (variableMap j)
    ((hG.XSmulHomotopy F i j).restrictScalars F) (variableMap_comp G j)
    (variableMap_homotopy hG i j) (variableMap_injective i) (variableMap_injective j) c a hc'
  rw [← singletonQuotientHomologyEquiv_quotientHomologyClass G i c
    (LinearMap.mem_range.mpr ⟨a, hc'.symm⟩)]
  unfold partiallyBlockedHomologyChangeBlockedColumnEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, h,
    singletonQuotientHomologyEquiv_quotientHomologyClass]
  congr 1
  rw [LinearMap.restrictScalars_apply, ZModModule.sub_eq_add]

/-- On representatives, if `∂c = V_j a`, the inverse change of blocked column sends the class
of `c` to the class of `c + H a`, for the chosen variable homotopy `H`. -/
theorem partiallyBlockedHomologyChangeBlockedColumnEquiv_symm_quotientHomologyClass (c a : M)
    (hc : G.unblockedDifferential F c = (MvPolynomial.X j : P) • a) :
    (hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j).symm
        (LinearMap.quotientHomologyClass hd
          (G.blockedChains_le_comap_unblockedDifferential {j}) c
          (by rw [LinearMap.restrictScalars_apply, hc]
              exact X_smul_mem_blockedChains (Finset.mem_singleton_self j) a)) =
      LinearMap.quotientHomologyClass hd
        (G.blockedChains_le_comap_unblockedDifferential {i}) (c + hG.XSmulHomotopy F i j a)
        (by rw [LinearMap.restrictScalars_apply,
              hG.unblockedDifferential_add_XSmulHomotopy_right F i j c a hc]
            exact X_smul_mem_blockedChains (Finset.mem_singleton_self i) a) := by
  rw [LinearEquiv.symm_apply_eq,
    partiallyBlockedHomologyChangeBlockedColumnEquiv_quotientHomologyClass hG i j _ a
      (hG.unblockedDifferential_add_XSmulHomotopy_right F i j c a hc)]
  congr 1
  rw [add_assoc, ZModModule.add_self, add_zero]

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
theorem simplyBlockedHomologyChangeBlockedColumnEquiv_partiallyBlockedHomologySingletonEquiv
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
theorem simplyBlockedHomologyChangeBlockedColumnEquiv_symm_partiallyBlockedHomologySingletonEquiv
    (x : G.partiallyBlockedHomology {j}) :
    (hG.simplyBlockedHomologyChangeBlockedColumnEquiv i j).symm
        (hG.partiallyBlockedHomologySingletonEquiv j x) =
      hG.partiallyBlockedHomologySingletonEquiv i
        ((hG.partiallyBlockedHomologyChangeBlockedColumnEquiv i j).symm x) := by
  rw [LinearEquiv.symm_apply_eq,
    simplyBlockedHomologyChangeBlockedColumnEquiv_partiallyBlockedHomologySingletonEquiv,
    LinearEquiv.apply_symm_apply]

/-- On a simply blocked cycle with unblocked lift `c`, where `∂c = V_i a`, the categorical
comparison gives the class of the lift `c + H a`, for the chosen variable homotopy `H`. -/
theorem simplyBlockedHomologyChangeBlockedColumnEquiv_oneVariableSpecializationHomologyClass
    (c a : M) (hc : G.unblockedDifferential F c = (MvPolynomial.X i : P) • a) :
    hG.simplyBlockedHomologyChangeBlockedColumnEquiv i j
        (G.oneVariableSpecializationHomologyClass F i
          ⟨(G.simplyBlockedChainEquiv F i).symm (simplyBlockedSpecialization F i c),
            (G.mem_ker_simplyBlockedComplex_d_iff F i _).mpr (by
              rw [LinearEquiv.apply_symm_apply,
                ← simplyBlockedSpecialization_unblockedDifferential, hc]
              exact (exact_X_smul_simplyBlockedSpecialization F i).apply_apply_eq_zero a)⟩) =
      G.oneVariableSpecializationHomologyClass F j
        ⟨(G.simplyBlockedChainEquiv F j).symm
            (simplyBlockedSpecialization F j (c + hG.XSmulHomotopy F i j a)),
          (G.mem_ker_simplyBlockedComplex_d_iff F j _).mpr (by
            rw [LinearEquiv.apply_symm_apply, ← simplyBlockedSpecialization_unblockedDifferential,
              hG.unblockedDifferential_add_XSmulHomotopy_left F i j c a hc]
            exact (exact_X_smul_simplyBlockedSpecialization F j).apply_apply_eq_zero a)⟩ := by
  have hsrc := hG.partiallyBlockedHomologySingletonEquiv_mk i c (by
    rw [hc]; exact X_smul_mem_blockedChains (Finset.mem_singleton_self i) a)
  have htgt := hG.partiallyBlockedHomologySingletonEquiv_mk j (c + hG.XSmulHomotopy F i j a) (by
    rw [hG.unblockedDifferential_add_XSmulHomotopy_left F i j c a hc]
    exact X_smul_mem_blockedChains (Finset.mem_singleton_self j) a)
  rw [← hsrc, ← htgt,
    simplyBlockedHomologyChangeBlockedColumnEquiv_partiallyBlockedHomologySingletonEquiv]
  congr 1
  simpa only [LinearMap.quotientHomologyClass_def] using
    partiallyBlockedHomologyChangeBlockedColumnEquiv_quotientHomologyClass hG i j c a hc

/-- On a simply blocked cycle with unblocked lift `c`, where `∂c = V_j a`, the inverse
categorical comparison gives the class of the lift `c + H a`, for the chosen variable
homotopy `H`. -/
theorem simplyBlockedHomologyChangeBlockedColumnEquiv_symm_oneVariableSpecializationHomologyClass
    (c a : M) (hc : G.unblockedDifferential F c = (MvPolynomial.X j : P) • a) :
    (hG.simplyBlockedHomologyChangeBlockedColumnEquiv i j).symm
        (G.oneVariableSpecializationHomologyClass F j
          ⟨(G.simplyBlockedChainEquiv F j).symm (simplyBlockedSpecialization F j c),
            (G.mem_ker_simplyBlockedComplex_d_iff F j _).mpr (by
              rw [LinearEquiv.apply_symm_apply,
                ← simplyBlockedSpecialization_unblockedDifferential, hc]
              exact (exact_X_smul_simplyBlockedSpecialization F j).apply_apply_eq_zero a)⟩) =
      G.oneVariableSpecializationHomologyClass F i
        ⟨(G.simplyBlockedChainEquiv F i).symm
            (simplyBlockedSpecialization F i (c + hG.XSmulHomotopy F i j a)),
          (G.mem_ker_simplyBlockedComplex_d_iff F i _).mpr (by
            rw [LinearEquiv.apply_symm_apply, ← simplyBlockedSpecialization_unblockedDifferential,
              hG.unblockedDifferential_add_XSmulHomotopy_right F i j c a hc]
            exact (exact_X_smul_simplyBlockedSpecialization F i).apply_apply_eq_zero a)⟩ := by
  have hsrc := hG.partiallyBlockedHomologySingletonEquiv_mk j c (by
    rw [hc]; exact X_smul_mem_blockedChains (Finset.mem_singleton_self j) a)
  have htgt := hG.partiallyBlockedHomologySingletonEquiv_mk i (c + hG.XSmulHomotopy F i j a) (by
    rw [hG.unblockedDifferential_add_XSmulHomotopy_right F i j c a hc]
    exact X_smul_mem_blockedChains (Finset.mem_singleton_self i) a)
  rw [← hsrc, ← htgt,
    simplyBlockedHomologyChangeBlockedColumnEquiv_symm_partiallyBlockedHomologySingletonEquiv]
  congr 1
  simpa only [LinearMap.quotientHomologyClass_def] using
    partiallyBlockedHomologyChangeBlockedColumnEquiv_symm_quotientHomologyClass hG i j c a hc

end IsKnot

end TauCeti.GridDiagram
