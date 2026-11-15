/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.ModuleResolution
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.RingTheory.GlobalDimension

/-!
# Global dimension and uniform Ext-Euler bounds

Over a left Noetherian ring, global dimension at most `n` is equivalent to vanishing of
`Ext` in degrees at least `n + 1` between finitely generated modules. Thus the uniform
bound used for Euler pairings agrees with the usual homological dimension, rather than
merely bounding Ext within a smaller test category.

For a finite-dimensional algebra over a field, such a global-dimension bound also supplies
Euler-admissibility. Finite-dimensionality and eventual vanishing remain separate inputs:
the former comes from the finite projective resolution and finite Hom spaces, while the
latter has the single bound `n + 1` for every pair.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7 and Chapter 4.
* Stacks Project, Lemma 10.109.12 (065T), for detection of global dimension on finite modules.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u uk

variable {R : Type u} [Ring R] [Small.{v} R]

/-- A bound on global dimension bounds Ext on any two selected classes of modules.
No finiteness or Noetherianity assumption is needed for this implication. -/
theorem isExtBoundedOn_of_globalDimension_le {n : ℕ}
    (h : globalDimension.{v} R ≤ n) (P Q : ObjectProperty (ModuleCat.{v} R)) :
    IsExtBoundedOn.{v} P Q (n + 1) where
  isExtBoundedBy {X Y} _ _ := by
    have := (globalDimension_le_iff_hasProjectiveDimensionLE R n).1 h X
    exact ⟨fun _ hi ↦ HasProjectiveDimensionLT.subsingleton X (n + 1) _ hi Y⟩

/-- For a left Noetherian ring, a uniform Ext bound on finite modules is exactly a bound
on the global dimension. In particular the target is allowed to be finite as well as the source. -/
theorem globalDimension_le_iff_isExtBoundedOn_isFG [IsNoetherianRing R]
    (n : ℕ) :
    globalDimension.{v} R ≤ n ↔
      IsExtBoundedOn.{v} (ModuleCat.isFG R) (ModuleCat.isFG R) (n + 1) := by
  refine ⟨fun h ↦ isExtBoundedOn_of_globalDimension_le h _ _, fun h ↦ ?_⟩
  apply ((globalDimension_le_tfae.{v} R n).out 2 1).1
  intro M hM
  have : Module.Finite R M := hM
  apply M.hasProjectiveDimensionLT_of_subsingleton_ext_finite (n + 1)
  intro L hL
  exact (h.isExtBoundedBy ((ModuleCat.isFG_iff M).2 hM)
    ((ModuleCat.isFG_iff L).2 hL)).subsingleton le_rfl

variable {k : Type uk} [Field k] [Algebra k R] [Module.Finite k R]

omit [Small.{v} R] in
/-- Finite global dimension of a finite-dimensional algebra makes every pair of finite
modules Euler-admissible. This supplies the witness for the module Ext-Euler pairing. -/
theorem isEulerAdmissibleOn_isFG_of_globalDimension_le {n : ℕ}
    (h : globalDimension.{u} R ≤ n) :
    IsEulerAdmissibleOn.{u} k (ModuleCat.isFG R) (ModuleCat.isFG R) := by
  have : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  apply isEulerAdmissibleOn_isFG k
  apply finiteModules_le_admitsFiniteResolution_of_finite_projectiveDimension
  exact fun M _ ↦ ⟨n, (globalDimension_le_iff_hasProjectiveDimensionLE R n).1 h M⟩

end TauCeti
