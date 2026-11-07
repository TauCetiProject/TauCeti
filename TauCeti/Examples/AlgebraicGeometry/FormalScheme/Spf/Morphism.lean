/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.RingTheory.AdicRing.Quotient
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Examples of morphisms of formal spectra

Evaluation at distinct scalars gives distinct formal-spectrum morphisms, including over
nonreduced coefficient rings. The global-section formula retains the coordinate being
evaluated. The examples also exercise composition, the empty formal spectrum and reduction
from a nondiscrete ring of `p`-adic integers to its residue ring.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open TauCeti TauCeti.FormalScheme TauCeti.FormalScheme.Spf

universe u

noncomputable section

namespace TauCeti.Examples.FormalScheme.Spf.Morphism

section Evaluation

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- The polynomial ring has the discrete topology in the evaluation examples. -/
local instance polynomialTopology : TopologicalSpace (Polynomial R) := ⊥
local instance : DiscreteTopology (Polynomial R) := ⟨rfl⟩

/-- Distinct evaluations give distinct morphisms, even for nonreduced coefficient rings. -/
theorem map_evaluation_ne {a b : R} (hab : a ≠ b) :
    map (Polynomial.evalRingHom a) continuous_of_discreteTopology ≠
      map (Polynomial.evalRingHom b) continuous_of_discreteTopology := by
  intro h
  have hring := map_injective h
  exact hab (by simpa using DFunLike.congr_fun hring Polynomial.X)

-- Conjugating the global-section map recovers the full evaluation homomorphism.
example (a : R) :
    have := (IsAdicRing.ideal_spec R).2.2
    have := (IsAdicRing.ideal_spec (Polynomial R)).2.2
    (globalSectionsIso (IsAdicRing.ideal_spec (Polynomial R)).2.1).inv ≫
      (map (Polynomial.evalRingHom a) continuous_of_discreteTopology).c.app (op ⊤) ≫
        (globalSectionsIso (IsAdicRing.ideal_spec R).2.1).hom =
      CommRingCat.ofHom (Polynomial.evalRingHom a) := by
  intro _ _
  erw [map_globalSections, Iso.inv_hom_id_assoc]

end Evaluation

section Nonreduced

/-- The discrete topology on the nonreduced coefficient ring. -/
local instance zmodFourTopology : TopologicalSpace (ZMod 4) := ⊥
local instance : DiscreteTopology (ZMod 4) := ⟨rfl⟩

/-- The discrete topology on its polynomial ring. -/
local instance zmodFourPolynomialTopology : TopologicalSpace (Polynomial (ZMod 4)) := ⊥
local instance : DiscreteTopology (Polynomial (ZMod 4)) := ⟨rfl⟩

-- The maps retain nilpotent information: evaluation at zero differs from evaluation at two.
example :
    map (Polynomial.evalRingHom (0 : ZMod 4)) continuous_of_discreteTopology ≠
      map (Polynomial.evalRingHom (2 : ZMod 4)) continuous_of_discreteTopology :=
  map_evaluation_ne (by decide)

end Nonreduced

section Composition

variable {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]

-- Composition is contravariant, as for ordinary spectra.
example (φ : B →+* A) (hφ : Continuous φ) (ψ : C →+* B) (hψ : Continuous ψ) :
    map (φ.comp ψ) (hφ.comp hψ) = map φ hφ ≫ map ψ hψ :=
  map_comp φ hφ ψ hψ

example : map (RingHom.id A) continuous_id = 𝟙 (Spf A) := map_id

end Composition

section Zero

/-- The discrete topology on the zero ring. -/
local instance zmodOneTopology : TopologicalSpace (ZMod 1) := ⊥
local instance : DiscreteTopology (ZMod 1) := ⟨rfl⟩

example : map (RingHom.id (ZMod 1)) continuous_id = 𝟙 (Spf (ZMod 1)) := map_id

end Zero

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

-- A continuous map from a nondiscrete adic ring also gives a local morphism.
example (J : Ideal ℤ_[p]) :
    Spf (ℤ_[p] ⧸ J) ⟶ Spf ℤ_[p] :=
  map (Ideal.Quotient.mk J) (QuotientRing.isOpenQuotientMap_mk J).continuous

end Padic

end TauCeti.Examples.FormalScheme.Spf.Morphism
