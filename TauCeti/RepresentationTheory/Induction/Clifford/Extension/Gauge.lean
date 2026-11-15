/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Gauge
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Commutant
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Splitting

/-!
# Neutral gauges for the Clifford extension

For a representation `A` of a normal subgroup, changing a section of its canonical
Clifford extension by units of `CategoryTheory.End A` conjugates the commutant
automorphisms and transforms the factors by the noncommutative gauge formula.
An ordinary inertia action extending the specified normal-subgroup action exists exactly
when a normalized gauge makes those factors trivial.

The factors and automorphisms belong to the actual commutant, which can be a noncommutative
division algebra for a simple representation over a nonsplitting field. No scalar-Schur,
simplicity, semisimplicity, characteristic, or finite-group hypothesis is needed here.
The criterion combines the general section gauge calculus with the existing correspondence
between ordinary inertia actions and splittings of the canonical Clifford extension.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension TauCeti.GroupExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)

/-- A change of Clifford section conjugates each commutant automorphism by its gauge unit. -/
theorem commutantAction_gauge (s : (groupExtension A).Section)
    (b : Quotient A → (End A)ˣ) (q : Quotient A) (f : End A) :
    commutantAction (s.gauge b q) f =
      (b q : End A) * commutantAction (s q) f * (↑(b q)⁻¹ : End A) := by
  rw [GroupExtension.Section.gauge_apply, groupExtension_inl, map_mul, AlgEquiv.mul_apply]
  simp

/-- The factor transformation uses the original commutant automorphism on the second
unit. In particular no action law for the original section is assumed. -/
theorem factorSetFun_clifford_gauge (s : (groupExtension A).Section)
    (b : Quotient A → (End A)ˣ) (q r : Quotient A) :
    factorSetFun (s.gauge b) (q, r) =
      b q * Units.map (commutantAction (s q)).toMonoidHom (b r) *
        factorSetFun s (q, r) * (b (q * r))⁻¹ := by
  rw [GroupExtension.Section.factorSetFun_gauge, commutantAction_units]

/-- A neutral gauge makes the commutant automorphisms multiplicative. -/
theorem commutantAction_gauge_mul (s : (groupExtension A).Section)
    (b : Quotient A → (End A)ˣ)
    (hb : ∀ q r, b q * Units.map (commutantAction (s q)).toMonoidHom (b r) *
      factorSetFun s (q, r) * (b (q * r))⁻¹ = 1) (q r : Quotient A) :
    commutantAction (s.gauge b (q * r)) =
      commutantAction (s.gauge b q) * commutantAction (s.gauge b r) := by
  have hs := (s.gauge b).factorSetFun_eq_one_iff.mp (fun q r => by
    rw [factorSetFun_clifford_gauge, hb])
  rw [hs, map_mul]

/-- The specified normal-subgroup action extends to its inertia group exactly when a
normalized commutant-unit gauge neutralizes the factors of a normalized Clifford section.
The extended action has the same underlying vector space and the same `N`-action. -/
theorem exists_inertiaExtension_iff_exists_gauge (s : (groupExtension A).Section)
    (hs : s 1 = 1) :
    (∃ ρ : Representation k (inertia A) A,
      ρ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) ↔
      ∃ b : Quotient A → (End A)ˣ, b 1 = 1 ∧
        ∀ q r, b q * Units.map (commutantAction (s q)).toMonoidHom (b r) *
          factorSetFun s (q, r) * (b (q * r))⁻¹ = 1 := by
  rw [← nonempty_splitting_iff, s.nonempty_splitting_iff_exists_gauge hs]
  simp only [commutantAction_units]

end FDRep
