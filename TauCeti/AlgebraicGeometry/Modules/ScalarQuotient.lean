/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Quotients by global functions

For a sheaf of modules `M` and a global function `f`, `scalarQuotient` is the cokernel `M/fM`.
Divisibility `f ∣ g` gives reduction maps `M/gM → M/fM`, which commute with the quotient
projections and satisfy the identity and composition laws. A factorization `g = f * c`
gives a morphism of cokernel sequences multiplying the left coefficient by `c`.
The power quotients `M/fⁿM` and their reductions are specializations of these constructions.
These constructions do not require regularity of the functions or sheaf cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- The sheaf quotient `M/fM`, computed as the cokernel of multiplication by `f`. -/
abbrev scalarQuotient (f : Γ(X, ⊤)) : X.Modules :=
  cokernel (M.globalSectionsSmul f)

/-- The canonical reduction `M/gM → M/fM` when `f ∣ g`. -/
def scalarQuotientTransition {f g : Γ(X, ⊤)} (h : f ∣ g) :
    M.scalarQuotient g ⟶ M.scalarQuotient f :=
  cokernel.desc _ (cokernel.π (M.globalSectionsSmul f)) (by
    obtain ⟨c, rfl⟩ := h
    rw [globalSectionsSmul_mul, Category.assoc, cokernel.condition, comp_zero])

/-- Reduction commutes with the quotient projections. -/
@[reassoc (attr := simp)]
lemma π_comp_scalarQuotientTransition {f g : Γ(X, ⊤)} (h : f ∣ g) :
    cokernel.π (M.globalSectionsSmul g) ≫ M.scalarQuotientTransition h =
      cokernel.π (M.globalSectionsSmul f) :=
  cokernel.π_desc _ _ _

/-- Reduction of quotient sheaves is an epimorphism. -/
instance epi_scalarQuotientTransition {f g : Γ(X, ⊤)} (h : f ∣ g) :
    Epi (M.scalarQuotientTransition h) :=
  epi_of_epi_fac (M.π_comp_scalarQuotientTransition h)

/-- Reduction without changing the scalar is the identity. -/
@[simp]
lemma scalarQuotientTransition_id (f : Γ(X, ⊤)) :
    M.scalarQuotientTransition (dvd_refl f) = 𝟙 (M.scalarQuotient f) := by
  apply (cancel_epi (cokernel.π (M.globalSectionsSmul f))).mp
  simp

/-- Reducing scalar quotients in two steps agrees with direct reduction. -/
@[reassoc (attr := simp)]
lemma scalarQuotientTransition_comp {f g k : Γ(X, ⊤)} (hgk : g ∣ k) (hfg : f ∣ g) :
    M.scalarQuotientTransition hgk ≫ M.scalarQuotientTransition hfg =
      M.scalarQuotientTransition (hfg.trans hgk) := by
  apply (cancel_epi (cokernel.π (M.globalSectionsSmul k))).mp
  simp

/-- A scalar factorization induces a map of cokernel sequences, with multiplication by `c`
on the left coefficient and the identity on the middle coefficient. -/
def scalarQuotientSequenceMap {f g c : Γ(X, ⊤)} (h : g = f * c) :
    ShortComplex.cokernelSequence (M.globalSectionsSmul g) ⟶
      ShortComplex.cokernelSequence (M.globalSectionsSmul f) where
  τ₁ := M.globalSectionsSmul c
  τ₂ := 𝟙 M
  τ₃ := M.scalarQuotientTransition ⟨c, h⟩
  comm₁₂ := by
    dsimp only [ShortComplex.cokernelSequence]
    rw [Category.comp_id, ← globalSectionsSmul_mul, h]
  comm₂₃ := by
    dsimp only [ShortComplex.cokernelSequence]
    rw [Category.id_comp, π_comp_scalarQuotientTransition]

/-- The left component of the coefficient-sequence map is scalar multiplication. -/
@[simp]
lemma scalarQuotientSequenceMap_τ₁ {f g c : Γ(X, ⊤)} (h : g = f * c) :
    (M.scalarQuotientSequenceMap h).τ₁ = M.globalSectionsSmul c := by
  rfl

/-- The middle component of the coefficient-sequence map is the identity. -/
@[simp]
lemma scalarQuotientSequenceMap_τ₂ {f g c : Γ(X, ⊤)} (h : g = f * c) :
    (M.scalarQuotientSequenceMap h).τ₂ = 𝟙 M := by
  rfl

/-- The right component of the coefficient-sequence map is reduction of quotients. -/
@[simp]
lemma scalarQuotientSequenceMap_τ₃ {f g c : Γ(X, ⊤)} (h : g = f * c) :
    (M.scalarQuotientSequenceMap h).τ₃ = M.scalarQuotientTransition ⟨c, h⟩ := by
  rfl

/-- The sheaf quotient `M/fⁿM`. -/
abbrev scalarPowerQuotient (f : Γ(X, ⊤)) (n : ℕ) : X.Modules :=
  M.scalarQuotient (f ^ n)

/-- The canonical reduction `M/fⁿM → M/fᵐM` for `m ≤ n`. -/
abbrev scalarPowerQuotientTransition (f : Γ(X, ⊤)) {m n : ℕ} (h : m ≤ n) :
    M.scalarPowerQuotient f n ⟶ M.scalarPowerQuotient f m :=
  M.scalarQuotientTransition (pow_dvd_pow f h)

end AlgebraicGeometry.Scheme.Modules
