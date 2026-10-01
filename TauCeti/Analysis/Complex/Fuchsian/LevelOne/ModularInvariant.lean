/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Descent
public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
public import TauCeti.Analysis.Complex.Fuchsian.Ramification
public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.Analysis.Complex.UpperHalfPlane.LocalMultiplicity

/-!
# The modular invariant on the level-one quotient

The normalized modular invariant `j = E₄³ / Δ` is holomorphic on the upper half-plane and
invariant under the effective level-one group, the image of `PSL(2, ℤ)` in `PSL(2, ℝ)`. It
therefore descends through the orbit projection to a holomorphic function
`TauCeti.ModularGroup.jQuotient` on the coarse level-one quotient.

The local multiplicities of the descended function are determined by those of `j` and the
stabilizer orders: pulling back to the upper half-plane multiplies the local multiplicity at the
orbit of `z` by the order of the stabilizer of `z`. At the elliptic point `ρ` the stabilizer has
order `3` and `j` vanishes to order `3`; at `i` the stabilizer has order `2` and `j - 1728`
vanishes to order `2`. So the descended function is unramified at both elliptic orbits, and at
every other orbit its local multiplicity equals that of `j` upstairs.

The descent uses the ordinary orbit quotient, without choosing representatives. Everything here
concerns the uncompactified quotient; the behaviour of `j` at the cusp is not treated.

## Main results

* `TauCeti.ModularForm.localMultiplicity_j_ρ` and `TauCeti.ModularForm.localMultiplicity_j_I`:
  the ramification indices `3` and `2` of `j` at `ρ` and `i`.
* `TauCeti.ModularGroup.jQuotient`: the descent of `j` to the coarse level-one quotient, with
  `TauCeti.ModularGroup.jQuotient_mk` and `TauCeti.ModularGroup.mdifferentiable_jQuotient`.
* `TauCeti.ModularGroup.localMultiplicity_j_eq_card_stabilizer_mul_localMultiplicity_jQuotient`:
  the local multiplicity of `j` at `z` is the stabilizer order of `z` times that of `jQuotient` at
  the orbit of `z`.
* `TauCeti.ModularGroup.localMultiplicity_jQuotient_ρ` and
  `TauCeti.ModularGroup.localMultiplicity_jQuotient_I`: the descended function is unramified at
  both elliptic orbits.
* `TauCeti.ModularGroup.localMultiplicity_jQuotient_eq_localMultiplicity_j_of_stabilizer_eq_bot`:
  away from the elliptic orbits the local multiplicities upstairs and downstairs agree.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3–2.4.
* Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer,
  1973, Chapter VII.
-/

public noncomputable section

open MulAction TauCeti.ModularForm TauCeti.RiemannSurface UpperHalfPlane

open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

/-- The modular invariant has ramification index `3` at the elliptic point `ρ`. -/
theorem localMultiplicity_j_ρ : localMultiplicity j ρ = 3 := by
  rw [UpperHalfPlane.localMultiplicity_eq_toNat_analyticOrderAt_comp_ofComplex (g := j)
    fun w ↦ by rw [j_ρ, sub_zero], analyticOrderAt_j_comp_ofComplex_ρ, ENat.toNat_ofNat]

/-- The modular invariant has ramification index `2` at the elliptic point `i`. -/
theorem localMultiplicity_j_I : localMultiplicity j I = 2 := by
  rw [UpperHalfPlane.localMultiplicity_eq_toNat_analyticOrderAt_comp_ofComplex (g := j - 1728)
    fun w ↦ by rw [j_I, Pi.sub_apply, Pi.ofNat_apply], coe_I,
    analyticOrderAt_j_sub_1728_comp_ofComplex_I, ENat.toNat_ofNat]

end TauCeti.ModularForm

namespace TauCeti.ModularGroup

/-- The modular invariant is invariant under the effective level-one group. -/
@[simp]
theorem j_smul_psl2zToPSL2RRange (g : psl2zToPSL2R.range) (z : ℍ) : j (g • z) = j z := by
  obtain ⟨_, p, rfl⟩ := g
  induction p using QuotientGroup.induction_on with
  | H a =>
    rw [Subgroup.smul_def, psl2zToPSL2R_smul, pslMk_smul]
    simp

/-- **The modular invariant on the coarse level-one quotient**: the function on the orbit space of
the effective level-one group whose pullback along the orbit projection is the modular
invariant `j`. -/
def jQuotient : orbitRel.Quotient psl2zToPSL2R.range ℍ → ℂ :=
  Quotient.lift j fun z w h ↦ by
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
    exact j_smul_psl2zToPSL2RRange g w

/-- The descended modular invariant takes the value `j z` at the orbit of `z`. -/
@[simp]
theorem jQuotient_mk (z : ℍ) : jQuotient (Quotient.mk _ z) = j z :=
  (rfl)

/-- The pullback of the descended modular invariant along the orbit projection is `j`. -/
theorem jQuotient_comp_quotientMk : jQuotient ∘ Quotient.mk _ = j :=
  funext jQuotient_mk

/-- The modular invariant on the coarse level-one quotient is holomorphic, including at the two
elliptic orbits. -/
theorem mdifferentiable_jQuotient : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jQuotient :=
  (psl2zToPSL2R.range.mdifferentiable_iff_comp_quotientMk).mpr j_mdifferentiable

/-- **The ramification formula for `j`.** The local multiplicity of `j` at `z` is the order of the
stabilizer of `z` in the effective level-one group times the local multiplicity of its descent at
the orbit of `z`. -/
theorem localMultiplicity_j_eq_card_stabilizer_mul_localMultiplicity_jQuotient (z : ℍ) :
    localMultiplicity j z = Nat.card (stabilizer psl2zToPSL2R.range z) *
      localMultiplicity jQuotient (Quotient.mk _ z) := by
  rw [← jQuotient_comp_quotientMk]
  exact psl2zToPSL2R.range.localMultiplicity_comp_quotientMk
    (.of_forall fun q ↦ mdifferentiable_jQuotient q)

/-- The descended modular invariant is unramified at the orbit of `ρ`. -/
@[simp]
theorem localMultiplicity_jQuotient_ρ : localMultiplicity jQuotient (Quotient.mk _ ρ) = 1 := by
  have h := localMultiplicity_j_eq_card_stabilizer_mul_localMultiplicity_jQuotient ρ
  rw [localMultiplicity_j_ρ, card_stabilizer_psl2zToPSL2RRange_ρ] at h
  omega

/-- The descended modular invariant is unramified at the orbit of `i`. -/
@[simp]
theorem localMultiplicity_jQuotient_I : localMultiplicity jQuotient (Quotient.mk _ I) = 1 := by
  have h := localMultiplicity_j_eq_card_stabilizer_mul_localMultiplicity_jQuotient I
  rw [localMultiplicity_j_I, card_stabilizer_psl2zToPSL2RRange_I] at h
  omega

/-- At an orbit with trivial stabilizer, the descended modular invariant has the same local
multiplicity as `j`. By `stabilizer_psl2zToPSL2RRange_eq_bot_iff` these are exactly the orbits
other than those of `i` and `ρ`. -/
theorem localMultiplicity_jQuotient_eq_localMultiplicity_j_of_stabilizer_eq_bot {z : ℍ}
    (hz : stabilizer psl2zToPSL2R.range z = ⊥) :
    localMultiplicity jQuotient (Quotient.mk _ z) = localMultiplicity j z := by
  rw [localMultiplicity_j_eq_card_stabilizer_mul_localMultiplicity_jQuotient,
    Subgroup.card_eq_one.mpr hz, one_mul]

end TauCeti.ModularGroup
