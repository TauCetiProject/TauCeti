/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Quotients by powers of a global function

For a sheaf of modules `M` and a global function `f`, `scalarPowerQuotient` is the cokernel
`M/fⁿM`. Its reduction maps are defined for any pair of exponents `m ≤ n`, commute with the
quotient projections, and satisfy the identity and composition laws. The corresponding
morphism of cokernel sequences multiplies the left coefficient by `f ^ (n - m)`.
These constructions do not require regularity of `f` or sheaf cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤))

/-- The sheaf quotient `M/fⁿM`, computed as the cokernel of multiplication by `fⁿ`. -/
abbrev scalarPowerQuotient (n : ℕ) : X.Modules :=
  cokernel (M.globalSectionsSmul (f ^ n))

/-- The canonical reduction `M/fⁿM → M/fᵐM` for `m ≤ n`. -/
def scalarPowerQuotientTransition {m n : ℕ} (h : m ≤ n) :
    M.scalarPowerQuotient f n ⟶ M.scalarPowerQuotient f m :=
  cokernel.desc _ (cokernel.π (M.globalSectionsSmul (f ^ m))) (by
    rw [← Nat.add_sub_of_le h, pow_add, globalSectionsSmul_mul, Category.assoc,
      cokernel.condition, comp_zero])

/-- Reduction commutes with the quotient projections. -/
@[reassoc (attr := simp)]
lemma π_comp_scalarPowerQuotientTransition {m n : ℕ} (h : m ≤ n) :
    cokernel.π (M.globalSectionsSmul (f ^ n)) ≫
        M.scalarPowerQuotientTransition f h =
      cokernel.π (M.globalSectionsSmul (f ^ m)) :=
  cokernel.π_desc _ _ _

/-- Reduction of quotient sheaves is an epimorphism. -/
instance epi_scalarPowerQuotientTransition {m n : ℕ} (h : m ≤ n) :
    Epi (M.scalarPowerQuotientTransition f h) :=
  epi_of_epi_fac (M.π_comp_scalarPowerQuotientTransition f h)

/-- Reduction without changing the exponent is the identity. -/
@[simp]
lemma scalarPowerQuotientTransition_id (n : ℕ) :
    M.scalarPowerQuotientTransition f (le_refl n) = 𝟙 (M.scalarPowerQuotient f n) := by
  apply (cancel_epi (cokernel.π (M.globalSectionsSmul (f ^ n)))).mp
  simp

/-- Reducing quotient exponents in two steps agrees with direct reduction. -/
@[reassoc (attr := simp)]
lemma scalarPowerQuotientTransition_comp {l m n : ℕ} (hmn : m ≤ n) (hlm : l ≤ m) :
    M.scalarPowerQuotientTransition f hmn ≫ M.scalarPowerQuotientTransition f hlm =
      M.scalarPowerQuotientTransition f (hlm.trans hmn) := by
  apply (cancel_epi (cokernel.π (M.globalSectionsSmul (f ^ n)))).mp
  simp

/-- Reduction of quotient sheaves is induced by multiplication by `f ^ (n - m)` on the left
coefficient and the identity on the middle coefficient. -/
def scalarPowerQuotientSequenceMap {m n : ℕ} (h : m ≤ n) :
    ShortComplex.cokernelSequence (M.globalSectionsSmul (f ^ n)) ⟶
      ShortComplex.cokernelSequence (M.globalSectionsSmul (f ^ m)) where
  τ₁ := M.globalSectionsSmul (f ^ (n - m))
  τ₂ := 𝟙 M
  τ₃ := M.scalarPowerQuotientTransition f h
  comm₁₂ := by
    dsimp only [ShortComplex.cokernelSequence]
    rw [Category.comp_id, ← globalSectionsSmul_mul, ← pow_add, Nat.add_sub_of_le h]
  comm₂₃ := by
    dsimp only [ShortComplex.cokernelSequence]
    rw [Category.id_comp, π_comp_scalarPowerQuotientTransition]

/-- The left component of the coefficient-sequence map is scalar multiplication. -/
@[simp]
lemma scalarPowerQuotientSequenceMap_τ₁ {m n : ℕ} (h : m ≤ n) :
    (M.scalarPowerQuotientSequenceMap f h).τ₁ = M.globalSectionsSmul (f ^ (n - m)) := by
  rfl

/-- The middle component of the coefficient-sequence map is the identity. -/
@[simp]
lemma scalarPowerQuotientSequenceMap_τ₂ {m n : ℕ} (h : m ≤ n) :
    (M.scalarPowerQuotientSequenceMap f h).τ₂ = 𝟙 M := by
  rfl

/-- The right component of the coefficient-sequence map is reduction of quotients. -/
@[simp]
lemma scalarPowerQuotientSequenceMap_τ₃ {m n : ℕ} (h : m ≤ n) :
    (M.scalarPowerQuotientSequenceMap f h).τ₃ = M.scalarPowerQuotientTransition f h := by
  rfl

end AlgebraicGeometry.Scheme.Modules
