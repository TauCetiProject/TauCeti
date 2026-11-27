/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.DiscreteValuationRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.DiscreteValuationRing.Inversion

/-!
# Examples of the local Hecke ring of `GL_n`

* The local Hecke pair and the commutative local Hecke ring of `GL_n` over a nonarchimedean local
  field `L`, for the valuation ring `𝒪[L]`, come from the general results for discrete valuation
  rings with finite residue field.
* Coset counts: for `n = 2` and residue field `𝔽₃` (for instance `L = ℚ₃`), `K η₁ K` and
  `K η₂ K` are unions of `4` and `1` left cosets. For `n = 3` and residue field `𝔽₂`, `K η₁ K`
  and `K η₂ K` are unions of `7` left cosets each, the points and the lines of the Fano plane.
* At `j = 0` the double coset is `K` itself.
* In rank one, `η₁ = π` and `[K π⁻¹ K]` is the inverse of `[K π K]`: the inversion formula gives
  `T^{(1)} [K η₁⁻¹ K] = T^{(0)} = 1`.
-/

public section

open HeckeRing.GLn HeckeCosetModule TauCeti IsLocalRing ValuativeRel
open scoped HeckeCosetModule

-- The local Hecke pair over a nonarchimedean local field.
example (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (n : ℕ) :
    IsHeckeTriple (⊤ : Submonoid (GL (Fin n) L)) (integralGL 𝒪[L] L (Fin n))
      (integralGL 𝒪[L] L (Fin n)) :=
  inferInstance

-- Its Hecke ring is commutative.
example (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (n : ℕ) (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) L)) (integralGL 𝒪[L] L (Fin n)) ℤ) :
    f * g = g * f :=
  mul_comm_integralGLHeckeRing 𝒪[L] L n ℤ f g

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {ϖ : R} {π : Kˣ}

-- `n = 2`, `q = 3`: `T^{(1)}` has `q + 1 = 4` cosets.
example (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) (hq : Nat.card (ResidueField R) = 3) :
    (minusculeCoset R π 2 1).degree = 4 := by
  rw [degree_minusculeCoset hϖ hπ (by norm_num), hq]
  simp [gaussianBinomial_succ_succ]

-- `n = 2`, `q = 3`: `T^{(2)}` is a single coset.
example (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) (hq : Nat.card (ResidueField R) = 3) :
    (minusculeCoset R π 2 2).degree = 1 := by
  rw [degree_minusculeCoset hϖ hπ le_rfl, hq, gaussianBinomial_self]

-- `n = 3`, `q = 2`: `T^{(1)}` and `T^{(2)}` have `7` cosets each.
example (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) (hq : Nat.card (ResidueField R) = 2) :
    (minusculeCoset R π 3 1).degree = 7 ∧ (minusculeCoset R π 3 2).degree = 7 := by
  rw [degree_minusculeCoset hϖ hπ (by norm_num), degree_minusculeCoset hϖ hπ (by norm_num), hq]
  simp [gaussianBinomial_succ_succ]

-- At `j = 0` the double coset is `K` itself, a single coset.
example (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) (n : ℕ) :
    (minusculeCoset R π n 0).degree = 1 := by
  rw [degree_minusculeCoset hϖ hπ (Nat.zero_le n), gaussianBinomial_zero_right]

-- In rank one the inversion formula says that `[K π⁻¹ K]` is inverse to `[K π K]`.
example (π : Kˣ) :
    single ℤ (minusculeCoset R π 1 1) 1 *
        single ℤ (HeckeCoset.mk (integralGL R K (Fin 1)) (integralGL R K (Fin 1))
          ⟨(minusculeDiag π 1 1)⁻¹, Submonoid.mem_top _⟩) 1 =
      single ℤ (minusculeCoset R π 1 0) 1 :=
  single_minusculeCoset_self_mul_single_inv ℤ π le_rfl
