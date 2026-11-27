/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.GaloisAction
public import TauCeti.RingTheory.Perfectoid.Cyclotomic.GaloisAction
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.Topology.Algebra.Valued.Integer

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The Galois action on the tilt of `ℂ_p` and on `A_inf`

Let `G_p` be the absolute Galois group of `ℚ_p`, realised as
`PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p`, act on `ℂ_p` by the continuous extensions of its elements.
These are isometries, so `G_p` acts on the valuation ring
`O_C = 𝒪[ℂ_p]` of the norm (`Valued.integer.isInvariantSubring`), and then by instances on the tilt
`O♭ = PreTilt O_C p` (`PreTilt.instMulSemiringAction`), on its fraction field `C♭ = Frac(O♭)`, on
`A_inf = W(O♭)` and on `W(C♭)`, commuting with the Witt-vector Frobenius; Fontaine's map
`θ : A_inf → O_C` is `G_p`-equivariant (`WittVector.fontaineTheta_smul`). Since `p` is
topologically nilpotent in `ℂ_p`, the results of
`TauCeti.RingTheory.Perfectoid.Cyclotomic.GaloisAction` apply to `C = ℂ_p`: there is a compatible
system `ε ∈ O♭` of `p`-power roots of unity, and for `μ = [ε] - 1` and `τ = [ε ^ (1 / p)] - 1`,
`g(τ)` is a unit multiple of `τ` and `μ²` divides `g(μ) - χ(g) μ`.

There the cyclotomic character is that of the action on `O_C`. This file shows that it is the
cyclotomic character `χ : G_p → ℤ_pˣ` of `PadicAlgCl p`, both being read off from the action on
the roots of unity of `p`-power order, which lie in `PadicAlgCl p` and in `O_C`.

The valuation ring `O_C` here is `𝒪[ℂ_p]` for the valuation `NormedField.valuation` of the norm, as
in the general results on perfectoid fields; Mathlib's own valuation on `ℂ_p` has the same integer
ring, but not definitionally.

## Main results

* `PadicComplex.fact_isTopologicallyNilpotent_natCast`: `p` is topologically nilpotent in `ℂ_p`.
* `PadicComplex.cyclotomicCharacter_integer`: the cyclotomic character of the action of `g ∈ G_p`
  on `O_C` is the cyclotomic character `χ(g)`.
* `PadicComplex.mu_sq_dvd_smul_mu_sub`: `μ²` divides `g(μ) - χ(g) μ` in `A_inf`.

## References

* J.-M. Fontaine, *Le corps des périodes `p`-adiques*, Astérisque 223 (1994).
-/

public section

open TauCeti.Perfectoid
open scoped NormedField Valued

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- `p` is topologically nilpotent in `ℂ_p`, as `‖p‖ < 1`; so `p` is not a unit of the valuation
ring `𝒪[ℂ_p]` (`Valued.integer.fact_not_isUnit_natCast`), and `𝒪[ℂ_p]` is `p`-adically complete. -/
instance fact_isTopologicallyNilpotent_natCast : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_p_lt_one p)⟩

-- `𝒪[ℂ_[p]]` below is the valuation ring of the valuation `NormedField.valuation` of the norm, as
-- in the results on perfectoid fields; without this, `Valued.integer` would use Mathlib's
-- valuation `PadicComplex.valued` on `ℂ_p`.
attribute [local instance high] NormedField.toValued

/-- The cyclotomic character of the action of `g ∈ Gal(PadicAlgCl p / ℚ_p)` on the valuation ring
of `ℂ_p` is the cyclotomic character `χ(g)` of `PadicAlgCl p`. -/
theorem cyclotomicCharacter_integer (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    cyclotomicCharacter 𝒪[ℂ_[p]] p
        (MulSemiringAction.toRingEquiv (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) 𝒪[ℂ_[p]] g) =
      cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv := by
  -- both characters agree with that of the action on `ℂ_p`, by naturality along the injective
  -- equivariant maps `O_C → ℂ_p` and `PadicAlgCl p → ℂ_p`
  refine (TauCeti.cyclotomicCharacter_eq_of_injective p (f := (𝒪[ℂ_[p]]).subtype)
    Subtype.val_injective (h := MulSemiringAction.toRingEquiv _ ℂ_[p] g) (fun _ _ _ ↦ rfl)
    fun h i ↦ ?_).symm.trans (TauCeti.cyclotomicCharacter_eq_of_injective p
      (f := UniformSpace.Completion.coeRingHom) (UniformSpace.Completion.coe_injective _)
      (fun _ t _ ↦ UniformSpace.Completion.algEquiv_smul_coe g t)
      fun _ i ↦ HasEnoughRootsOfUnity.exists_isPrimitiveRoot _ _)
  -- a primitive root of unity of `ℂ_p` has norm one, so it lies in the valuation ring
  obtain ⟨ζ, hζ⟩ := h i
  have hpi : p ^ i ≠ 0 := pow_ne_zero i (Fact.out : p.Prime).ne_zero
  have hζ1 : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hpi).mp (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  exact ⟨⟨ζ, Valued.integer.mem_iff.mpr hζ1.le⟩,
    hζ.of_map_of_injective (f := (𝒪[ℂ_[p]]).subtype) Subtype.val_injective⟩

/-- **`μ²` divides `g(μ) - χ(g) μ` in `A_inf`** for every `g ∈ Gal(PadicAlgCl p / ℚ_p)`, where `χ`
is the cyclotomic character and `μ = [ε] - 1` for a compatible system `ε` of `p`-power roots of
unity in the tilt of `𝒪[ℂ_p]`. -/
theorem mu_sq_dvd_smul_mu_sub (ε : PreTilt 𝒪[ℂ_[p]] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[ℂ_[p]] p) p).symm ε)) p)
    (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    mu p ε ^ 2 ∣ g • mu p ε - TauCeti.WittVector.padicIntHom p (PreTilt 𝒪[ℂ_[p]] p)
      (cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv) * mu p ε := by
  rw [← cyclotomicCharacter_integer]
  exact PreTilt.mu_sq_dvd_smul_mu_sub ε hε g

end PadicComplex
