/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
public import TauCeti.NumberTheory.LocalField.IntegerRing.Padic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Deep units are finite free p-adic modules

For a finite compatible extension `K/ℚ_[p]` and a depth `i` satisfying
`absoluteRamificationIndex K p < (p - 1) * i`, the logarithm transports the natural
`ℤ_[p]`-module structure of `𝓂[K]^i` to the deep units, written additively. Choosing an integral
basis of this ideal gives a continuous linear equivalence with `ℤ_[p]^[K : ℚ_[p]]`.

The module structure is a named definition, independent of the choice of basis. The coordinate
map is characterized by the logarithm and the chosen basis, and its inverse by the exponential.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Propositions (5.5) and (5.7).
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField Module NormedSpace

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p] {i : ℕ}

/-- The p-adic module structure on deep units, written additively, transported through the
logarithm from the ideal `𝓂[K]^i`. It depends on the depth, but not on a choice of basis. -/
abbrev deepUnitPadicIntModule (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    Module ℤ_[p] (Additive (unitFiltration K i)) :=
  letI := integerIdealPadicIntModule K p (𝓂[K] ^ i)
  (MulEquiv.toAdditiveLeft (deepUnitExpLogEquiv K hi).toMulEquiv).module ℤ_[p]

variable {K p}

/-- P-adic scalar multiplication on deep units is characterized by multiplication of their
logarithms in `K`. -/
@[simp]
theorem log_padicInt_smul_deepUnit (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (c : ℤ_[p]) (u : Additive (unitFiltration K i)) :
    letI := deepUnitPadicIntModule K p hi
    log (((c • u).toMul : Kˣ) : K) = algebraMap ℚ_[p] K (c : ℚ_[p]) *
      log ((u.toMul : Kˣ) : K) := by
  let _ := integerIdealPadicIntModule K p (𝓂[K] ^ i)
  let _ := deepUnitPadicIntModule K p hi
  let e := MulEquiv.toAdditiveLeft (deepUnitExpLogEquiv K hi).toMulEquiv
  have h := congrArg (fun x : (𝓂[K] ^ i : Ideal 𝒪[K]) => (x : K))
    ((e.linearEquiv ℤ_[p]).map_smul c u)
  -- The additive type tags only repackage the existing logarithm equivalence.
  change (((deepUnitExpLogEquiv K hi (c • u).toMul).toAdd : 𝒪[K]) : K) =
    (((c • (deepUnitExpLogEquiv K hi u.toMul).toAdd : (𝓂[K] ^ i : Ideal 𝒪[K])) : 𝒪[K]) : K) at h
  simpa only [coe_deepUnitExpLogEquiv_apply, coe_padicInt_smul_integerIdeal] using h

variable {ι : Type*} [Fintype ι]

/-- The logarithmic p-adic coordinates on deep units attached to a basis of `𝓂[K]^i` over
`𝒪[ℚ_[p]]`. This is an equivalence of topological `ℤ_[p]`-modules. -/
def deepUnitEquivPiPadicInt (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (b : Basis ι 𝒪[ℚ_[p]] (𝓂[K] ^ i : Ideal 𝒪[K])) :
    letI := deepUnitPadicIntModule K p hi
    Additive (unitFiltration K i) ≃L[ℤ_[p]] (ι → ℤ_[p]) := by
  letI := integerIdealPadicIntModule K p (𝓂[K] ^ i)
  letI := deepUnitPadicIntModule K p hi
  let e := deepUnitExpLogEquiv K hi
  let a := MulEquiv.toAdditiveLeft e.toMulEquiv
  let f := integerIdealEquivPiPadicInt (𝓂[K] ^ i) b
  exact { (a.linearEquiv ℤ_[p]).trans f.toLinearEquiv with
    continuous_toFun := f.continuous.comp
      (continuous_toAdd.comp (e.continuous.comp continuous_toMul))
    continuous_invFun := continuous_ofMul.comp
      (e.continuous_symm.comp (continuous_ofAdd.comp f.symm.continuous)) }

/-- The coordinates of a deep unit are the integral basis coordinates of its logarithm,
identified with p-adic integers. -/
@[simp]
theorem deepUnitEquivPiPadicInt_apply (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (b : Basis ι 𝒪[ℚ_[p]] (𝓂[K] ^ i : Ideal 𝒪[K]))
    (u : Additive (unitFiltration K i)) :
    letI := deepUnitPadicIntModule K p hi
    deepUnitEquivPiPadicInt hi b u = fun j => Padic.integerRingEquiv p
      (b.equivFun (deepUnitExpLogEquiv K hi u.toMul).toAdd j) := by
  let _ := deepUnitPadicIntModule K p hi
  exact integerIdealEquivPiPadicInt_apply (𝓂[K] ^ i) b _

/-- Reconstructing a deep unit from its coordinates exponentiates the linear combination of
the chosen ideal basis vectors. -/
@[simp]
theorem coe_deepUnitEquivPiPadicInt_symm_apply
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (b : Basis ι 𝒪[ℚ_[p]] (𝓂[K] ^ i : Ideal 𝒪[K])) (c : ι → ℤ_[p]) :
    letI := deepUnitPadicIntModule K p hi
    ((((deepUnitEquivPiPadicInt hi b).symm c).toMul : Kˣ) : K) =
      exp (∑ j, algebraMap ℚ_[p] K (c j : ℚ_[p]) * (b j : K)) := by
  let _ := integerIdealPadicIntModule K p (𝓂[K] ^ i)
  let _ := deepUnitPadicIntModule K p hi
  -- Forgetting the linear and continuity fields leaves the composition of coordinates and exp.
  change (((deepUnitExpLogEquiv K hi).symm (Multiplicative.ofAdd
    ((integerIdealEquivPiPadicInt (𝓂[K] ^ i) b).symm c)) : Kˣ) : K) = _
  rw [coe_deepUnitExpLogEquiv_symm_apply, integerIdealEquivPiPadicInt_symm_apply]
  simp only [toAdd_ofAdd]
  apply congrArg exp
  have hsum : (((∑ j, c j • b j : (𝓂[K] ^ i : Ideal 𝒪[K])) : 𝒪[K]) : K) =
      ∑ j, (((c j • b j : (𝓂[K] ^ i : Ideal 𝒪[K])) : 𝒪[K]) : K) :=
    map_sum ((Subring.subtype 𝒪[K]).toAddMonoidHom.comp
      (𝓂[K] ^ i : Ideal 𝒪[K]).subtype.toAddMonoidHom) _ _
  rw [hsum]
  exact Finset.sum_congr rfl fun j _ => coe_padicInt_smul_integerIdeal _ (c j) (b j)

variable (K p) in
/-- Deep units in a finite extension `K/ℚ_[p]` are topologically free p-adic modules of rank
`[K : ℚ_[p]]`, at every depth strictly beyond the exponential convergence threshold. -/
theorem nonempty_deepUnitEquivPiPadicInt
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    letI := deepUnitPadicIntModule K p hi
    Nonempty (Additive (unitFiltration K i) ≃L[ℤ_[p]]
      (Fin (Module.finrank ℚ_[p] K) → ℤ_[p])) := by
  let _ := deepUnitPadicIntModule K p hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hI : (𝓂[K] ^ i : Ideal 𝒪[K]) ≠ ⊥ := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hπ.ne_zero
  let b := Module.finBasisOfFinrankEq 𝒪[ℚ_[p]] 𝒪[K] (finrank_integerRing ℚ_[p] K)
  exact ⟨deepUnitEquivPiPadicInt hi ((𝓂[K] ^ i).selfBasis b hI)⟩

/-- Deep units with their logarithmic p-adic module structure have continuous scalar
multiplication for the original unit-group topology. -/
theorem continuousSMul_deepUnitPadicInt
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    letI := deepUnitPadicIntModule K p hi
    ContinuousSMul ℤ_[p] (Additive (unitFiltration K i)) := by
  let _ := deepUnitPadicIntModule K p hi
  obtain ⟨e⟩ := nonempty_deepUnitEquivPiPadicInt K p hi
  exact e.toHomeomorph.isInducing.continuousSMul continuous_id (fun {c x} => e.map_smul c x)

end TauCeti
