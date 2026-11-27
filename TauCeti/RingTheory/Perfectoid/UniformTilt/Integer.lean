/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Field
public import TauCeti.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.ValuedField
import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta

/-!
# The valuation ring of the tilt of a field

Let `K` be a complete nontrivially normed field with an ultrametric norm in which the prime `p`
is topologically nilpotent, with valuation ring `O_K = 𝒪[K]` and tilt `K♭ = tiltField p K`. The
valuation ring `𝒪[K♭]` of `K♭`, its closed unit ball, is Mathlib's tilt
`PreTilt O_K p = lim_{x ↦ x ^ p} O_K ⧸ p` of `O_K`: an element of `𝒪[K♭]` is a compatible system
of `p`-power roots in `O_K`, and reducing every coordinate modulo `p` gives an element of
`PreTilt O_K p` (`TauCeti.Perfectoid.uniformTilt.plusEquivPreTilt`). Under this identification
Mathlib's untilt `PreTilt.untilt` is the sharp map `x ↦ x♯` of `K♭`, so the norm of `K♭` is
`‖x‖ = ‖x♯‖`.

## Main definitions

* `TauCeti.Perfectoid.tiltField.integerEquivPreTilt p K`: the ring isomorphism
  `𝒪[K♭] ≃+* PreTilt O_K p` between the valuation ring of the tilt and Mathlib's tilt of `O_K`.

## Main results

* `TauCeti.Perfectoid.tiltField.untilt_integerEquivPreTilt`,
  `TauCeti.Perfectoid.tiltField.coeff_zero_integerEquivPreTilt_symm`: under this isomorphism the
  untilt is the sharp map `x ↦ x♯` of `K♭`.

## References

* P. Scholze, *Perfectoid spaces*, Lemma 3.4.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1.
-/

public section

open scoped NormedField Valued
open TauCeti.Huber

namespace TauCeti.Perfectoid.tiltField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (IsTopologicallyNilpotent (p : K))]

/-- The ring homomorphism `O_K♭ → K♭`: the integral tilt `PreTilt O_K p` is the subring of
`uniformTilt p K` of compatible systems of `p`-power roots in `O_K`. -/
private noncomputable def preTiltToTilt : PreTilt 𝒪[K] p →+* tiltField p K :=
  (WithAbs.equiv (uniformTilt.sharpAbsoluteValue p K)).symm.toRingHom.comp
    ((uniformTilt.plusSubring p (isRingOfIntegralElements_integer K)).subtype.comp
      (uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_integer K)).symm.toRingHom)

variable {p K} in
private theorem preTiltToTilt_apply (x : PreTilt 𝒪[K] p) :
    preTiltToTilt p K x = WithAbs.toAbs _
      ((uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_integer K)).symm x :
        uniformTilt p K) :=
  (rfl)

variable {p K} in
/-- `preTiltToTilt` is injective. -/
private theorem preTiltToTilt_injective : Function.Injective (preTiltToTilt p K) :=
  fun x y h ↦ by simpa [preTiltToTilt_apply] using h

variable {p K} in
/-- `preTiltToTilt` takes values in the closed unit ball. -/
private theorem preTiltToTilt_mem_integer (x : PreTilt 𝒪[K] p) :
    preTiltToTilt p K x ∈ 𝒪[tiltField p K] := by
  rw [mem_integer_iff, preTiltToTilt_apply, norm_toAbs, ← Valued.integer.mem_iff]
  exact uniformTilt.mem_plusSubring_iff.mp (Subtype.property _) 0

variable {p K} in
/-- Every element of the closed unit ball is a value of `preTiltToTilt`: its coordinates are a
compatible system of `p`-power roots in `O_K`. -/
private theorem exists_preTiltToTilt_eq {y : tiltField p K} (hy : y ∈ 𝒪[tiltField p K]) :
    ∃ x, preTiltToTilt p K x = y := by
  have hmem :
      WithAbs.equiv _ y ∈ uniformTilt.plusSubring p (isRingOfIntegralElements_integer K) := by
    rw [uniformTilt.mem_plusSubring_iff_coeff_zero, Valued.integer.mem_iff, ← norm_def]
    exact mem_integer_iff.mp hy
  refine ⟨uniformTilt.plusEquivPreTilt p _ ⟨_, hmem⟩, ?_⟩
  simp only [preTiltToTilt_apply, RingEquiv.symm_apply_apply, WithAbs.equiv_apply,
    WithAbs.toAbs_ofAbs]

/-- The ring homomorphism `preTiltToTilt` is an isomorphism onto the closed unit ball. -/
private noncomputable def preTiltEquivInteger : PreTilt 𝒪[K] p ≃+* 𝒪[tiltField p K] :=
  RingEquiv.ofBijective
    ((preTiltToTilt p K).codRestrict 𝒪[tiltField p K] preTiltToTilt_mem_integer)
    ⟨fun _ _ h ↦ preTiltToTilt_injective (congrArg Subtype.val h),
      fun y ↦ (exists_preTiltToTilt_eq y.property).imp fun _ hx ↦ Subtype.ext hx⟩

/-- **The valuation ring of the tilt is the tilt of the valuation ring.** The closed unit ball
`𝒪[K♭]` of the tilt `K♭ = tiltField p K` is isomorphic to Mathlib's tilt
`PreTilt O_K p = lim_{x ↦ x ^ p} O_K ⧸ p`, by reducing every coordinate modulo `p`; under this
isomorphism the untilt is the sharp map (`tiltField.untilt_integerEquivPreTilt`), so
`‖x‖ = ‖x♯‖`. -/
noncomputable def integerEquivPreTilt : 𝒪[tiltField p K] ≃+* PreTilt 𝒪[K] p :=
  (preTiltEquivInteger p K).symm

variable {p K}

private theorem preTiltToTilt_integerEquivPreTilt (y : 𝒪[tiltField p K]) :
    preTiltToTilt p K (integerEquivPreTilt p K y) = y :=
  congrArg Subtype.val ((preTiltEquivInteger p K).apply_symm_apply y)

/-- **The untilt is the sharp map.** For `y` in the valuation ring of the tilt `K♭`, the untilt of
the corresponding element of `PreTilt O_K p` is the zeroth coordinate `y♯` of `y`. In particular
`‖y‖ = ‖(integerEquivPreTilt p K y)♯‖` (`tiltField.norm_def`). -/
@[simp]
theorem untilt_integerEquivPreTilt (y : 𝒪[tiltField p K]) :
    ((integerEquivPreTilt p K y).untilt : K) =
      uniformTilt.coeff p K 0 (WithAbs.ofAbs (y : tiltField p K)) := by
  conv_rhs => rw [← preTiltToTilt_integerEquivPreTilt y, preTiltToTilt_apply]
  rw [← uniformTilt.plusSharp_plusEquivPreTilt_symm (isRingOfIntegralElements_integer K),
    uniformTilt.coe_plusSharp]

/-- **The sharp map is the untilt.** For `x ∈ PreTilt O_K p`, the sharp of the corresponding
element of the tilt `K♭` is the untilt `x♯`. -/
@[simp]
theorem coeff_zero_integerEquivPreTilt_symm (x : PreTilt 𝒪[K] p) :
    uniformTilt.coeff p K 0 (WithAbs.ofAbs ((integerEquivPreTilt p K).symm x : tiltField p K)) =
      (x.untilt : K) := by
  rw [← untilt_integerEquivPreTilt, RingEquiv.apply_symm_apply]

end TauCeti.Perfectoid.tiltField
