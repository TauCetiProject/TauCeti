/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic

/-!
# Finiteness of `H¹` with roots-of-unity coefficients over a local field

Let `K` be a nonarchimedean local field. For `ℓ` invertible in `K` the group `Kˣ ⧸ (Kˣ)ˡ` of power
classes is finite (`TauCeti.finiteIndex_range_powMonoidHom`), so by the Kummer isomorphism
`TauCeti.kummerIso` so is `H¹(G_K, μ_ℓ)`. When `K` contains a primitive `n`th root of unity, every
trivial `G_K`-module of prime order `ℓ ∣ n` is a copy of `μ_ℓ`, and its `H¹` is finite. This is the
input from Kummer theory to the finiteness of the Galois cohomology of a finite module over a
local field.

## Main results

* `TauCeti.finite_H1_of_isPrimitiveRoot_of_natCard_dvd`: `H¹(G_K, M)` is finite for every trivial
  discrete module `M` of prime order dividing `n`, when `K` contains a primitive `n`th root of
  unity.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.2, proof of Proposition 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. VII, §1.
-/

public section

namespace TauCeti

open ContCohomology

/-- **`H¹` of a trivial module of prime order over a local field.** Let `K` be a nonarchimedean
local field containing a primitive `n`th root of unity, and `H` a topological group isomorphic to
`G_K`. Then `H¹(H, M)` is finite for every discrete `H`-module `M` of prime order dividing `n` on
which `H` acts trivially. -/
theorem finite_H1_of_isPrimitiveRoot_of_natCard_dvd (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {H : Type*} [Group H] [TopologicalSpace H]
    (φ : AbsoluteGaloisGroup K ≃ₜ* H) (M : Type*) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction H M] [ContinuousSMul H M] (hM : (Nat.card M).Prime)
    (hMn : Nat.card M ∣ n) (htriv : ∀ (h : H) (m : M), h • m = m) :
    Finite (H1 H M) := by
  have : NeZero (Nat.card M) := ⟨hM.ne_zero⟩
  have : IsAddCyclic M := isAddCyclic_of_prime_card rfl (hp := ⟨hM⟩)
  -- `ζ ^ (n / ℓ)` is a primitive `ℓ`th root of unity in `K`, for `ℓ = Nat.card M`
  have hζℓ : IsPrimitiveRoot (ζ ^ (n / Nat.card M)) (Nat.card M) := by
    have h := hζ.pow_of_dvd
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hMn) hM.pos).ne'
      (Nat.div_dvd_of_dvd hMn)
    rwa [Nat.div_div_self hMn (NeZero.ne n)] at h
  -- `Kˣ ⧸ (Kˣ)ˡ` is finite, since `ℓ` is invertible in `K`
  have := hζℓ.neZero'
  have : (powerSubgroup Kˣ (Nat.card M)).FiniteIndex := by
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact finiteIndex_range_powMonoidHom (NeZero.ne ((Nat.card M : ℕ) : K))
  have : Finite (powerClassQuotient Kˣ (Nat.card M)) := Subgroup.finite_quotient_of_finiteIndex
  exact finite_H1_of_isPrimitiveRoot hζℓ φ M rfl htriv

end TauCeti
