/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# p-adic coordinates on integer-ring ideals

For a finite compatible extension `K/ℚ_[p]`, any nonzero ideal of `𝒪[K]` is a free
`ℤ_[p]`-module of rank `[K : ℚ_[p]]`. Its basis coordinates are homeomorphisms for the
subspace topology on the ideal and the product topology on the coordinates. These coordinates
identify the additive lattices that occur as logarithms of deep units.

The scalar structure is a named definition: it transports the existing action of
`𝒪[ℚ_[p]]` through `Padic.integerRingEquiv`, without adding global module instances.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§5–6.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField Module

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- The `ℤ_[p]`-module structure on an ideal of `𝒪[K]`, obtained from its
`𝒪[ℚ_[p]]`-module structure via the canonical identification of these scalar rings. -/
abbrev integerIdealPadicIntModule (I : Ideal 𝒪[K]) : Module ℤ_[p] I :=
  Module.compHom I (Padic.integerRingEquiv p).symm.toRingHom

variable {K p}

/-- Scalar multiplication by a p-adic integer on an integer-ring ideal agrees with
multiplication by its image in the local field. -/
@[simp]
theorem coe_padicInt_smul_integerIdeal (I : Ideal 𝒪[K]) (c : ℤ_[p]) (x : I) :
    letI := integerIdealPadicIntModule K p I
    (((c • x : I) : 𝒪[K]) : K) = algebraMap ℚ_[p] K (c : ℚ_[p]) * (x : K) := by
  let _ := integerIdealPadicIntModule K p I
  -- The named module restricts scalars; expose that action before using the coercion lemmas.
  change ((((Padic.integerRingEquiv p).symm c • x : I) : 𝒪[K]) : K) = _
  rw [Submodule.coe_smul_of_tower, Algebra.smul_def, Subring.coe_mul,
    coe_algebraMap_integerRing, Padic.coe_integerRingEquiv_symm_apply]

/-- P-adic scalar multiplication is continuous on an integer-ring ideal with its subspace
topology. -/
theorem continuousSMul_integerIdealPadicInt (I : Ideal 𝒪[K]) :
    letI := integerIdealPadicIntModule K p I
    ContinuousSMul ℤ_[p] I := by
  let _ := integerIdealPadicIntModule K p I
  have hc : Continuous fun z : ℤ_[p] × I =>
      algebraMap ℚ_[p] K (z.1 : ℚ_[p]) * (z.2 : K) :=
    ((continuous_algebraMap_of_valuativeExtension ℚ_[p] K).comp
      (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  have hs : Continuous fun z : ℤ_[p] × I => (((z.1 • z.2 : I) : 𝒪[K]) : K) :=
    hc.congr fun z => (coe_padicInt_smul_integerIdeal I z.1 z.2).symm
  exact ⟨(hs.subtype_mk _).subtype_mk _⟩

variable {ι : Type*} [Fintype ι]

/-- The p-adic basis coordinates of an ideal of the integer ring. A basis over
`𝒪[ℚ_[p]]` becomes a basis over `ℤ_[p]` through `Padic.integerRingEquiv`. -/
def integerIdealEquivPiPadicInt (I : Ideal 𝒪[K]) (b : Basis ι 𝒪[ℚ_[p]] I) :
    letI := integerIdealPadicIntModule K p I
    I ≃L[ℤ_[p]] (ι → ℤ_[p]) := by
  letI := integerIdealPadicIntModule K p I
  letI := continuousSMul_integerIdealPadicInt (p := p) I
  let b' := b.mapCoeffs (Padic.integerRingEquiv p) (by
    intro c x
    -- Both actions are identified by the scalar-ring equivalence.
    change (Padic.integerRingEquiv p).symm (Padic.integerRingEquiv p c) • x = c • x
    rw [RingEquiv.symm_apply_apply])
  have hc : Continuous b'.equivFun.symm := by
    have hs : (b'.equivFun.symm : (ι → ℤ_[p]) → I) = fun c => ∑ j, c j • b' j :=
      funext (Basis.equivFun_symm_apply b')
    rw [hs]
    fun_prop
  exact { b'.equivFun with
    continuous_toFun := hc.continuous_symm_of_equiv_compact_to_t2 (f := b'.equivFun.symm.toEquiv)
    continuous_invFun := hc }

/-- The inverse coordinate map is the linear combination of the chosen basis vectors with
p-adic integer coefficients. -/
@[simp]
theorem integerIdealEquivPiPadicInt_symm_apply (I : Ideal 𝒪[K])
    (b : Basis ι 𝒪[ℚ_[p]] I) (c : ι → ℤ_[p]) :
    letI := integerIdealPadicIntModule K p I
    (integerIdealEquivPiPadicInt I b).symm c = ∑ j, c j • b j := by
  let _ := integerIdealPadicIntModule K p I
  -- Forgetting the continuity fields exposes the basis equivalence defining this map.
  change (b.mapCoeffs (Padic.integerRingEquiv p) _).equivFun.symm c = _
  simp only [Basis.equivFun_symm_apply, Basis.mapCoeffs_apply]

/-- The coordinates are the chosen integral basis coordinates, with each scalar identified
with a p-adic integer. -/
@[simp]
theorem integerIdealEquivPiPadicInt_apply (I : Ideal 𝒪[K])
    (b : Basis ι 𝒪[ℚ_[p]] I) (x : I) :
    letI := integerIdealPadicIntModule K p I
    integerIdealEquivPiPadicInt I b x = fun j => Padic.integerRingEquiv p (b.equivFun x j) := by
  let _ := integerIdealPadicIntModule K p I
  apply (integerIdealEquivPiPadicInt I b).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply, integerIdealEquivPiPadicInt_symm_apply]
  -- Scalar restriction turns p-adic coefficients back into the original integral coefficients.
  change x = ∑ j, (Padic.integerRingEquiv p).symm
    (Padic.integerRingEquiv p (b.equivFun x j)) • b j
  simpa only [RingEquiv.symm_apply_apply, Basis.equivFun_apply] using (b.sum_repr x).symm

variable (K p) in
/-- Every nonzero integer-ring ideal in a finite extension of `ℚ_[p]` has p-adic coordinates
with exactly `[K : ℚ_[p]]` entries, continuously and linearly. -/
theorem nonempty_integerIdealEquivPiPadicInt (I : Ideal 𝒪[K]) (hI : I ≠ ⊥) :
    letI := integerIdealPadicIntModule K p I
    Nonempty (I ≃L[ℤ_[p]] (Fin (Module.finrank ℚ_[p] K) → ℤ_[p])) := by
  let _ := integerIdealPadicIntModule K p I
  let b := Module.finBasisOfFinrankEq 𝒪[ℚ_[p]] 𝒪[K] (finrank_integerRing ℚ_[p] K)
  exact ⟨integerIdealEquivPiPadicInt I (I.selfBasis b hI)⟩

end TauCeti
