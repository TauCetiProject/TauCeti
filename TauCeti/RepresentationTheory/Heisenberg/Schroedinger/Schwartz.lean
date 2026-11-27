/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.Heisenberg.Schroedinger.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.UnitaryAddChar

/-!
# The Schrödinger representation on the Schwartz space

Let `X` be a finite-dimensional real normed space, `B : X × Y → C` a pairing whose partial maps
`B · y` are continuous, and `ψ` a continuous unitary character of `C`. The Schrödinger operators
`ρψ(t, (x, y)) φ (u) = ψ (t + B u y + ½ B x y) φ (u + x)` of `LinearMap.schroedinger` preserve the
Schwartz space `𝓢(X, V)` and act on it by continuous linear maps, giving a continuous
representation of the Heisenberg group (`LinearMap.schroedingerSchwartz`). This is the smooth
Schrödinger model at an archimedean place: for `ℝ`, and for `ℂ` viewed as a real field.

Translation preserves Schwartz functions, and so does multiplication by the modulation
`u ↦ ψ (B u y)`: it is a continuous unitary character of `X`, hence of the form
`u ↦ exp (ℓ u * i)` with `ℓ` linear, a function of temperate growth
(`AddChar.hasTemperateGrowth`).

## Main definitions

* `LinearMap.schroedingerSchwartz`: the Schrödinger representation on `𝓢(X, V)`, as a continuous
  representation.

## Main results

* `LinearMap.schroedingerSchwartz_apply`: its operators are those of `LinearMap.schroedinger`.

## References

* S. Kudla, *Notes on the local theta correspondence* (1996), I.2, Lemma 2.2.
* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), I.§4.
-/

public section

noncomputable section

open Multiplicative TauCeti SchwartzMap

attribute [local instance] trivialMulDistribMulAction

namespace LinearMap

variable {R X Y C : Type*} [CommSemiring R] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup C]
  [Module R C] [TopologicalSpace C] {B : X →ₗ[R] Y →ₗ[R] C} {ψ : AddChar C ℂ}

/-- The modulation `u ↦ ψ (B u y)` by a continuous unitary character has temperate growth. -/
private theorem hasTemperateGrowth_modulation (hψ : Continuous ψ) (hψ1 : ∀ c, ‖ψ c‖ = 1)
    (hB : ∀ y, Continuous fun u ↦ B u y) (y : Y) :
    (fun u ↦ ψ (B u y)).HasTemperateGrowth :=
  AddChar.hasTemperateGrowth (ψ.compAddMonoidHom (B.flip y).toAddMonoidHom) (hψ.comp (hB y))
    fun _ ↦ hψ1 _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [Invertible (2 : R)]

variable (B ψ V) in
/-- The Schrödinger operator of `p` on `𝓢(X, V)`: translation by `x` followed by modulation. -/
private def schroedingerSchwartzCLM
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension) :
    𝓢(X, V) →L[ℂ] 𝓢(X, V) :=
  ψ (p.left.toAdd + ⅟(2 : R) • B p.right.toAdd.1 p.right.toAdd.2) •
    (smulLeftCLM V fun u ↦ ψ (B u p.right.toAdd.2)) ∘L compSubConstCLM ℂ (-p.right.toAdd.1)

private theorem coe_schroedingerSchwartzCLM_apply (hψ : Continuous ψ) (hψ1 : ∀ c, ‖ψ c‖ = 1)
    (hB : ∀ y, Continuous fun u ↦ B u y)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (φ : 𝓢(X, V)) :
    ⇑(schroedingerSchwartzCLM B ψ V p φ) = B.schroedinger ψ V p φ := funext fun u ↦ by
  simp only [schroedingerSchwartzCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    smul_apply, smulLeftCLM_apply_apply (hasTemperateGrowth_modulation hψ hψ1 hB _),
    compSubConstCLM_apply, sub_neg_eq_add, smul_smul, ← AddChar.map_add_eq_mul, schroedinger_apply]
  congr 2
  abel

variable (B ψ V) in
/-- **The Schrödinger representation on the Schwartz space** `𝓢(X, V)` of a finite-dimensional
real space, for a continuous unitary character `ψ` and a pairing with continuous partial maps
`B · y`: `ρψ(t, (x, y)) φ (u) = ψ (t + B u y + ½ B x y) φ (u + x)`, by continuous linear maps. -/
def schroedingerSchwartz (hψ : Continuous ψ) (hψ1 : ∀ c, ‖ψ c‖ = 1)
    (hB : ∀ y, Continuous fun u ↦ B u y) :
    ContRepresentation ℂ
      (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension
      𝓢(X, V) :=
  .ofMonoidHom
    { toFun := schroedingerSchwartzCLM B ψ V
      map_one' := ContinuousLinearMap.ext fun φ ↦ SchwartzMap.ext fun u ↦ by
        simp [coe_schroedingerSchwartzCLM_apply hψ hψ1 hB]
      map_mul' p q := ContinuousLinearMap.ext fun φ ↦ SchwartzMap.ext fun u ↦ by
        simp [coe_schroedingerSchwartzCLM_apply hψ hψ1 hB] }

/-- The operators of the Schwartz-space Schrödinger representation are those of
`LinearMap.schroedinger`. -/
@[simp]
theorem schroedingerSchwartz_apply (hψ : Continuous ψ) (hψ1 : ∀ c, ‖ψ c‖ = 1)
    (hB : ∀ y, Continuous fun u ↦ B u y)
    (p : (⅟(2 : R) • (B.polarizedForm - B.polarizedForm.flip)).bilinearFactorSet.Extension)
    (φ : 𝓢(X, V)) :
    ⇑(B.schroedingerSchwartz ψ V hψ hψ1 hB p φ) = B.schroedinger ψ V p φ :=
  coe_schroedingerSchwartzCLM_apply hψ hψ1 hB p φ

end LinearMap
