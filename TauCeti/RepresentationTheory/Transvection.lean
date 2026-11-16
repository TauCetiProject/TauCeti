/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Representations by transvections

An additive character, written as `χ : G →* Multiplicative k`, gives the representation
`σ (x, y) = (x + y * (χ σ).toAdd, y)`. For a nontrivial character its invariant space is the
first coordinate line and has dimension one. This supplies the character-independent linear
algebra for tame monodromy.
-/

public section

noncomputable section

namespace MonoidHom

variable {k G : Type*}

section CommSemiring

variable [CommSemiring k] [Monoid G] (χ : G →* Multiplicative k)

/-- The two-dimensional transvection representation attached to an additive character. -/
def transvectionRepresentation : Representation k G (k × k) where
  toFun σ := LinearMap.transvection (LinearMap.snd _ _ _) ((χ σ).toAdd, 0)
  map_one' := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [LinearMap.transvection.apply]
  map_mul' σ τ := by
    rw [Module.End.mul_eq_comp, LinearMap.transvection.comp_of_left_eq (by simp)]
    congr 1
    simp

/-- The coordinate formula for the representation attached to a character. -/
@[simp]
theorem transvectionRepresentation_apply (σ : G) (v : k × k) :
    transvectionRepresentation χ σ v = (v.1 + v.2 * (χ σ).toAdd, v.2) := by
  rcases v with ⟨x, y⟩
  simp [transvectionRepresentation, LinearMap.transvection.apply, smul_eq_mul]

/-- The transvection representation is trivial exactly when its character is trivial. -/
@[simp]
theorem transvectionRepresentation_eq_one_iff : transvectionRepresentation χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    ext σ
    have hv := congrArg (fun ρ : Representation k G (k × k) ↦ (ρ σ (0, 1)).1) h
    simpa using hv
  · rintro rfl
    apply MonoidHom.ext
    intro σ
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp

end CommSemiring

section CommRing

variable [CommRing k] [NoZeroDivisors k] [Group G] (χ : G →* Multiplicative k)

/-- For a nontrivial character, fixed vectors have vanishing second coordinate. -/
theorem mem_invariants_transvectionRepresentation_iff (hχ : χ ≠ 1) (v : k × k) :
    v ∈ (transvectionRepresentation χ).invariants ↔ v.2 = 0 := by
  constructor
  · intro hv
    obtain ⟨σ, hσ⟩ := DFunLike.ne_iff.mp hχ
    have hnonzero : (χ σ).toAdd ≠ 0 := by simpa using hσ
    have h := congrArg Prod.fst (hv σ)
    simp only [transvectionRepresentation_apply] at h
    exact (mul_eq_zero.mp (add_eq_left.mp h)).resolve_right hnonzero
  · intro hv σ
    apply Prod.ext <;> simp [hv]

/-- The invariant space for a nontrivial character is the first coordinate line. -/
@[simp]
theorem invariants_transvectionRepresentation (hχ : χ ≠ 1) :
    (transvectionRepresentation χ).invariants = LinearMap.ker (LinearMap.snd k k k) := by
  ext v
  simp [mem_invariants_transvectionRepresentation_iff χ hχ]

end CommRing

section Field

variable [Field k] [Group G] (χ : G →* Multiplicative k)

/-- A nontrivial character gives a one-dimensional invariant space. -/
theorem finrank_invariants_transvectionRepresentation (hχ : χ ≠ 1) :
    Module.finrank k (transvectionRepresentation χ).invariants = 1 := by
  rw [invariants_transvectionRepresentation χ hχ, LinearMap.ker_snd,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_self]

end Field

end MonoidHom
