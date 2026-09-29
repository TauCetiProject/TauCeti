/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ZMod.Four
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Character
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit

/-!
# Cup squares of classes of `H¹(G, 𝔽₂)` that lift to `ℤ/4`

Let `G` be a topological group and `φ : G →ₜ* ℤ/4` a continuous character. Its reduction modulo
`2` is the continuous character `φ.zmodFourReduction : G → 𝔽₂`, and the class of that character in
`H¹(G, 𝔽₂)` under the identification `TauCeti.cohomFpLinearEquivContinuousZModDual` of
`H¹(G, 𝔽₂)` with the continuous `𝔽₂`-dual of `G` is `φ.zmodFourReductionClass`; it is represented
by the homogeneous cocycle `(g₀, g₁) ↦ φ(g₀⁻¹ g₁) mod 2` (`TauCeti.characterCocycle`). The cup
square of this class vanishes: the carry `ZMod.carryFour = ⌊·/2⌋ : ℤ/4 → 𝔽₂` satisfies
`⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)` (`ZMod.carryFour_add`), so the cup square
`(g₀, g₁, g₂) ↦ (φ(g₀⁻¹ g₁) mod 2)(φ(g₁⁻¹ g₂) mod 2)` is the coboundary of the homogeneous
one-cochain `(g₀, g₁) ↦ ⌊φ(g₀⁻¹ g₁)/2⌋`. This is the vanishing half of the classical identification
of the cup square on `H¹(G, 𝔽₂)` with the Bockstein of `0 → 𝔽₂ → ℤ/4 → 𝔽₂ → 0`, which kills exactly
the classes that lift to `ℤ/4`; only the vanishing on lifted classes is proved here. The class is
nonzero as soon as `φ` takes an odd value.

Together with the nonvanishing of the cup square of the generator of `H¹(ℤ/2, 𝔽₂)`, this is what
distinguishes `ℤ/2` from the cyclic groups `ℤ/2ᵏ`, `k ≥ 2`, whose mod-`2` character lifts to
`ℤ/4`: the cup pairing on `H¹(ℤ/2ᵏ, 𝔽₂)` vanishes for `k ≥ 2`.

## Main declarations

* `ContinuousMonoidHom.zmodFourReduction`: the reduction modulo `2` of a continuous character
  `φ : G →ₜ* ℤ/4`, a continuous character `G → 𝔽₂`.
* `ContinuousMonoidHom.zmodFourReductionClass`: the class in `H¹(G, 𝔽₂)` of that reduction;
  `ContinuousMonoidHom.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass` recovers the
  reduction as its character.
* `ContinuousMonoidHom.zmodFourReductionClass_ne_zero`: the class is nonzero when `φ` takes an
  odd value.
* `ContinuousMonoidHom.cupFp_zmodFourReductionClass_self_eq_zero`: **the cup square of the class
  vanishes**.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology TopRep

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod 2`, so that the cochain
-- computations below take place in the additive group the cohomology API expects, as in
-- `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CyclicTwo`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (φ : G →ₜ* Multiplicative (ZMod 4))

/-! ### The reduction modulo `2` and its class -/

omit [IsTopologicalGroup G] in
/-- **The reduction modulo `2` of a continuous character `φ : G →ₜ* ℤ/4`**: the continuous
character `g ↦ φ g mod 2` of `G` with values in `𝔽₂`, as an element of the continuous `𝔽₂`-dual of
`G`. -/
def _root_.ContinuousMonoidHom.zmodFourReduction : continuousZModDual 2 G :=
  Additive.ofMul
    ((⟨(ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative,
      continuous_of_discreteTopology⟩ : Multiplicative (ZMod 4) →ₜ* Multiplicative (ZMod 2)).comp φ)

omit [IsTopologicalGroup G] in
/-- The reduction of `φ` takes the value `φ g mod 2` at `g`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.zmodFourReduction_apply (g : G) :
    Multiplicative.toAdd (Additive.toMul φ.zmodFourReduction g) =
      ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ g)) := by
  rw [_root_.ContinuousMonoidHom.zmodFourReduction]
  rfl

/-- **The class in `H¹(G, 𝔽₂)` of the reduction modulo `2` of a continuous character
`φ : G →ₜ* ℤ/4`**: the class attached to the character `φ.zmodFourReduction` by the identification
`TauCeti.cohomFpLinearEquivContinuousZModDual` of `H¹(G, 𝔽₂)` with the continuous `𝔽₂`-dual of
`G`. -/
noncomputable def _root_.ContinuousMonoidHom.zmodFourReductionClass : cohomFp 2 G 1 :=
  (cohomFpLinearEquivContinuousZModDual 2 G).symm φ.zmodFourReduction

/-- **The character of the class of the reduction of `φ` is the reduction of `φ`.** -/
@[simp]
theorem _root_.ContinuousMonoidHom.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass :
    cohomFpLinearEquivContinuousZModDual 2 G φ.zmodFourReductionClass = φ.zmodFourReduction :=
  (cohomFpLinearEquivContinuousZModDual 2 G).apply_symm_apply _

/-- **The class of the reduction of `φ` is nonzero when `φ` takes an odd value**: its character
takes the value `φ g mod 2 ≠ 0` at `g`. -/
theorem _root_.ContinuousMonoidHom.zmodFourReductionClass_ne_zero {g : G}
    (hg : ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ g)) ≠ 0) :
    φ.zmodFourReductionClass ≠ 0 := by
  intro hzero
  have h := φ.zmodFourReduction_apply g
  rw [← φ.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass, hzero, map_zero] at h
  exact hg (by simpa using h.symm)

/-! ### The cup square -/

/-- The homogeneous one-cochain `(g₀, g₁) ↦ ⌊φ (g₀⁻¹ g₁) / 2⌋` of `G` with trivial `𝔽₂`
coefficients, the carry of `φ`. -/
private noncomputable def carryFourCochain : (homogeneousCochains (trivialFp 2 G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦
      (trivialFpEquiv 2 G).symm (ZMod.carryFour (Multiplicative.toAdd (φ (q.1⁻¹ * q.2)))), by
      have hc : Continuous fun q : G × G ↦ q.1⁻¹ * q.2 := by fun_prop
      exact (continuous_of_discreteTopology (α := Multiplicative (ZMod 4))
        (f := fun z ↦ (trivialFpEquiv 2 G).symm (ZMod.carryFour (Multiplicative.toAdd z)))).comp
          (φ.continuous.comp hc)⟩, fun g ↦ by
    ext h k
    simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
      ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of `carryFourCochain φ` at `(g₀, g₁)` is `⌊φ (g₀⁻¹ g₁) / 2⌋`, lifted into the
coefficient object. -/
-- Not a `simp` lemma: the carrier of the homogeneous cochains is the iterated function space
-- `C(G, C(G, X.V))` only after unfolding the coinduction, which `simp` does not do when matching
-- the left-hand side; use it with `rw`.
private theorem carryFourCochain_apply (g₀ g₁ : G) :
    (carryFourCochain φ).val g₀ g₁ =
      (trivialFpEquiv 2 G).symm (ZMod.carryFour (Multiplicative.toAdd (φ (g₀⁻¹ * g₁)))) :=
  (rfl)

/-- **The cup square of a class of `H¹(G, 𝔽₂)` that lifts to `ℤ/4` vanishes.** The cup square of
the cocycle `(g₀, g₁) ↦ φ (g₀⁻¹ g₁) mod 2` is the coboundary of the homogeneous one-cochain
`(g₀, g₁) ↦ ⌊φ (g₀⁻¹ g₁) / 2⌋`, by the carry identity `ZMod.carryFour_add`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.cupFp_zmodFourReductionClass_self_eq_zero :
    cupFp 2 G φ.zmodFourReductionClass φ.zmodFourReductionClass = 0 := by
  rw [_root_.ContinuousMonoidHom.zmodFourReductionClass,
    cohomFpLinearEquivContinuousZModDual_symm_apply, cupFp_π,
    (homogeneousCochains (trivialFp 2 G)).homologyπ_eq_zero_iff 2 (m := 1)
      (CochainComplex.prev_nat_succ 1)]
  refine ⟨carryFourCochain φ, ?_⟩
  apply (homogeneousCochains (trivialFp 2 G)).iCycles_injective (n := 1 + 1)
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_characterCocycle]
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply]
  rw [TopPairing.cupCochain_one_one_apply]
  rw [carryFourCochain_apply, carryFourCochain_apply, carryFourCochain_apply]
  rw [characterCochain_apply, characterCochain_apply]
  rw [fpPairing_bil_apply]
  simp only [LinearEquiv.apply_symm_apply, _root_.ContinuousMonoidHom.zmodFourReduction_apply]
  rw [← map_sub (trivialFpEquiv 2 G).symm, ← map_sub (trivialFpEquiv 2 G).symm]
  have hmul : g₀⁻¹ * g₂ = (g₀⁻¹ * g₁) * (g₁⁻¹ * g₂) := by group
  refine congrArg (trivialFpEquiv 2 G).symm ?_
  -- The identity `carryFour_add` differs from the coboundary equation by a sign, which is
  -- invisible in `𝔽₂`.
  rw [hmul, map_mul φ (g₀⁻¹ * g₁) (g₁⁻¹ * g₂), toAdd_mul,
    ← ZMod.neg_eq_self_mod_two (ZMod.castHom _ (ZMod 2) _ * _), ZMod.carryFour_add]
  abel

end TauCeti
