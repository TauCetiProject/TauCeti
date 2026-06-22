/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Topology.Homotopy.AmbientIsotopic

/-!
# The group of ambient isotopies of a space

An `TauCeti.AmbientIsotopy Y` is a homotopy of `Y` from the identity whose level-preserving
total map `I × Y → I × Y` is a homeomorphism: a continuous path of self-homeomorphisms of `Y`
based at the identity. The three closure operations on ambient isotopies built in
`TauCeti.Topology.Homotopy.Isotopy` (the constant `AmbientIsotopy.refl`, the pointwise
composition `AmbientIsotopy.trans` running `Φ_t` then `Ψ_t` at each time `t`, and the pointwise
inverse `AmbientIsotopy.symm`) are exactly the pointwise multiplication, unit, and inverse of a
group: they assemble `AmbientIsotopy Y` into a group, the pointwise group structure on the
path space of the homeomorphism group based at the identity.

Evaluating at time `1` is a group homomorphism `AmbientIsotopy Y →* (Y ≃ₜ Y)` whose image is
exactly the self-homeomorphisms ambient isotopic to the identity, characterised through the
`TauCeti.AmbientIsotopic` relation of `TauCeti.Topology.Homotopy.AmbientIsotopic`. This is the
algebraic counterpart, for the
point-set ambient-isotopy notion, of the diffeomorphism group the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3) builds in the smooth category.

## Main definitions

* `TauCeti.AmbientIsotopy.instGroup`: the group structure on `AmbientIsotopy Y`, with `refl`
  the unit, `Φ * Ψ := Ψ.trans Φ` the (time-`1`-contravariant) product, and `symm` the inverse.
* `TauCeti.AmbientIsotopy.finalMonoidHom`: the time-`1` homomorphism `AmbientIsotopy Y →* (Y ≃ₜ Y)`.

## Main results

* `TauCeti.AmbientIsotopy.trans_assoc`, `refl_trans`, `trans_refl`, `trans_symm`, `symm_trans`:
  the group laws phrased on the closure operations themselves.
* `TauCeti.AmbientIsotopy.ambientIsotopic_id_iff_mem_finalMonoidHom_range`: a self-homeomorphism
  is in the range of the time-`1` homomorphism exactly when it is ambient isotopic to the identity.
-/

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {Y : Type*} [TopologicalSpace Y]

namespace AmbientIsotopy

/-- Two ambient isotopies are equal when their underlying maps agree pointwise; the
homeomorphism and basepoint conditions are propositions, fixed by proof irrelevance. -/
@[ext]
theorem ext {Φ Ψ : AmbientIsotopy Y} (h : ∀ p, Φ.toContinuousMap p = Ψ.toContinuousMap p) :
    Φ = Ψ := by
  obtain ⟨f, _, _⟩ := Φ
  obtain ⟨g, _, _⟩ := Ψ
  have hfg : f = g := ContinuousMap.ext h
  cases hfg
  rfl

/-- Pointwise composition of ambient isotopies is associative. -/
theorem trans_assoc (Φ Ψ Χ : AmbientIsotopy Y) :
    (Φ.trans Ψ).trans Χ = Φ.trans (Ψ.trans Χ) := by
  ext p; rfl

/-- The constant ambient isotopy is a left unit for pointwise composition. -/
theorem refl_trans (Φ : AmbientIsotopy Y) : (refl Y).trans Φ = Φ := by
  ext p; rfl

/-- The constant ambient isotopy is a right unit for pointwise composition. -/
theorem trans_refl (Φ : AmbientIsotopy Y) : Φ.trans (refl Y) = Φ := by
  ext p; rfl

/-- An ambient isotopy followed pointwise by its inverse is the constant ambient isotopy. -/
theorem trans_symm (Φ : AmbientIsotopy Y) : Φ.trans Φ.symm = refl Y := by
  ext p
  rw [trans_apply, symm_apply, ← totalHomeomorph_apply, Φ.totalHomeomorph.symm_apply_apply]
  rfl

/-- The inverse of an ambient isotopy followed pointwise by the isotopy is the constant ambient
isotopy. -/
theorem symm_trans (Φ : AmbientIsotopy Y) : Φ.symm.trans Φ = refl Y := by
  ext p
  rw [trans_apply, symm_apply]
  have hfst : (Φ.totalHomeomorph.symm p).1 = p.1 := Φ.totalHomeomorph_symm_fst p
  have happ := Φ.totalHomeomorph.apply_symm_apply p
  rw [totalHomeomorph_apply] at happ
  have hpair : (p.1, (Φ.totalHomeomorph.symm p).2) = Φ.totalHomeomorph.symm p :=
    Prod.ext hfst.symm rfl
  rw [show ((p.1, (Φ.totalHomeomorph.symm p).2) : I × Y) = Φ.totalHomeomorph.symm p from hpair]
  exact (Prod.ext_iff.mp happ).2

/-- The ambient isotopies of `Y` form a group under pointwise composition `Φ * Ψ := Ψ.trans Φ`,
with the constant ambient isotopy as unit and `symm` as inverse. The product is written so that
the time-`1` map (`finalMonoidHom`) is a homomorphism into `Y ≃ₜ Y` with its usual
function-composition multiplication. -/
noncomputable instance instGroup : Group (AmbientIsotopy Y) where
  mul Φ Ψ := Ψ.trans Φ
  one := refl Y
  inv Φ := Φ.symm
  mul_assoc Φ Ψ Χ := (trans_assoc Χ Ψ Φ).symm
  one_mul Φ := trans_refl Φ
  mul_one Φ := refl_trans Φ
  inv_mul_cancel Φ := trans_symm Φ

theorem one_def : (1 : AmbientIsotopy Y) = refl Y := rfl

theorem mul_def (Φ Ψ : AmbientIsotopy Y) : Φ * Ψ = Ψ.trans Φ := rfl

theorem inv_def (Φ : AmbientIsotopy Y) : Φ⁻¹ = Φ.symm := rfl

@[simp]
theorem mul_apply (Φ Ψ : AmbientIsotopy Y) (p : I × Y) :
    (Φ * Ψ).toContinuousMap p = Φ.toContinuousMap (p.1, Ψ.toContinuousMap p) :=
  Ψ.trans_apply Φ p

@[simp]
theorem one_apply (p : I × Y) : (1 : AmbientIsotopy Y).toContinuousMap p = p.2 := rfl

@[simp]
theorem inv_apply (Φ : AmbientIsotopy Y) (p : I × Y) :
    (Φ⁻¹).toContinuousMap p = (Φ.totalHomeomorph.symm p).2 := rfl

/-- The time-`1` homeomorphism of the unit ambient isotopy is the identity. -/
@[simp]
theorem finalHomeomorph_one : (1 : AmbientIsotopy Y).finalHomeomorph = 1 := by
  apply Homeomorph.ext
  intro y
  rw [one_def, finalHomeomorph_apply, final_refl]
  exact (Homeomorph.one_apply y).symm

/-- The time-`1` homeomorphism of a pointwise product is the product (in `Y ≃ₜ Y`) of the
time-`1` homeomorphisms, in the opposite order. -/
@[simp]
theorem finalHomeomorph_mul (Φ Ψ : AmbientIsotopy Y) :
    (Φ * Ψ).finalHomeomorph = Φ.finalHomeomorph * Ψ.finalHomeomorph := by
  apply Homeomorph.ext
  intro y
  simp only [Homeomorph.mul_apply, finalHomeomorph_apply, mul_def]
  exact Ψ.final_trans Φ y

/-- Evaluation at time `1`, as a group homomorphism from the ambient isotopies of `Y` to the
self-homeomorphisms of `Y`. -/
noncomputable def finalMonoidHom : AmbientIsotopy Y →* (Y ≃ₜ Y) where
  toFun Φ := Φ.finalHomeomorph
  map_one' := finalHomeomorph_one
  map_mul' := finalHomeomorph_mul

@[simp]
theorem finalMonoidHom_apply (Φ : AmbientIsotopy Y) :
    finalMonoidHom Φ = Φ.finalHomeomorph := rfl

/-- A self-homeomorphism of `Y` lies in the image of the time-`1` homomorphism exactly when it is
ambient isotopic to the identity: the image of `finalMonoidHom` is the set of self-homeomorphisms
ambient isotopic to the identity. -/
theorem ambientIsotopic_id_iff_mem_finalMonoidHom_range (e : Y ≃ₜ Y) :
    AmbientIsotopic (.id Y) (e : C(Y, Y)) ↔ e ∈ (finalMonoidHom (Y := Y)).range := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨Φ, hΦ⟩
    refine ⟨Φ, Homeomorph.ext fun y => ?_⟩
    have := congrArg (fun f : C(Y, Y) => f y) hΦ
    simpa using this
  · rintro ⟨Φ, hΦ⟩
    refine ⟨Φ, ContinuousMap.ext fun y => ?_⟩
    have := congrArg (fun h : Y ≃ₜ Y => h y) hΦ
    simpa using this

end AmbientIsotopy

end TauCeti
