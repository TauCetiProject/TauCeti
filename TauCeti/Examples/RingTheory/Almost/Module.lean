/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Module
import TauCeti.RingTheory.Almost.ValuationRing

/-!
# Examples of almost modules

These examples test the category `TauCeti.Almost.Module S` of almost modules and the
almostification functor `toAlmost S`:

* `V ⧸ m` almostifies to zero for every setup; for a valuation ring with non-finitely-generated
  maximal ideal `m` so does the residue field, while `V ⧸ (ε)` does not for `ε ∈ m`;
* for the classical setup `(ℤ, ℤ)`, `ℤ^a` is not zero, multiplication by `2` on `ℤ` does not
  become an isomorphism, and `toAlmost` is an equivalence;
* for the zero setup every almost module is zero;
* the inclusion `m ⊆ V` becomes an isomorphism, `toAlmost` is exact and `V`-linear, and the
  factorisation of `toAlmost` through itself is the identity.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4.
-/

open CategoryTheory Limits IsLocalRing TauCeti.Almost TauCeti.Almost.BasicSetup
  TauCeti.Almost.Module

variable {V : Type*} [CommRing V]

/-! ### Zero and nonzero almost modules -/

-- `V ⧸ m` almostifies to zero for every setup.
example (S : BasicSetup V) : IsZero ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal))) :=
  (isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_quotient

section ValuationRing

variable [IsDomain V] [ValuationRing V] (h : ¬ (maximalIdeal V).FG)

-- For a valuation ring, the residue field almostifies to zero.
example : IsZero ((toAlmost (ofValuationRing h)).obj (ModuleCat.of V (ResidueField V))) :=
  (isZero_toAlmost_obj_iff _ _).mpr (ofValuationRing_isAlmostZero_residueField h)

-- For `ε ∈ m`, `V ⧸ (ε)` does not almostify to zero.
example {ε : V} (hε : ε ∈ maximalIdeal V) :
    ¬ IsZero ((toAlmost (ofValuationRing h)).obj (ModuleCat.of V (V ⧸ Ideal.span {ε}))) := by
  rw [isZero_toAlmost_obj_iff, ofValuationRing_isAlmostZero_quotient_span_singleton_iff]
  exact (mem_maximalIdeal ε).mp hε

end ValuationRing

-- For the classical setup, `ℤ^a` is not zero.
example : ¬ IsZero ((toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  rw [isZero_toAlmost_obj_iff, isAlmostZero_classical_iff]
  intro h
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

-- For the zero setup, every almost module is zero.
example (X : Module (zero V)) : IsZero X :=
  isZero_of_ideal_eq_bot _ zero_ideal X

/-! ### Almost isomorphisms -/

-- The inclusion `m ⊆ V` becomes an isomorphism `m^a ≅ V^a`.
example (S : BasicSetup V) : IsIso ((toAlmost S).map (ModuleCat.ofHom S.ideal.subtype)) :=
  inferInstance

-- For the classical setup, multiplication by `2` on `ℤ` does not become an isomorphism.
example : ¬ IsIso ((toAlmost (classical ℤ)).map
    (ModuleCat.ofHom ((2 : ℤ) • LinearMap.id (R := ℤ) (M := ℤ)))) := by
  rw [isIso_toAlmost_map_iff, ModuleCat.hom_ofHom, isAlmostIso_classical_iff]
  rintro ⟨-, hs⟩
  obtain ⟨x, hx⟩ := hs 1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hx
  omega

-- For the classical setup, `toAlmost` is an equivalence.
example : (toAlmost (classical V)).IsEquivalence :=
  inferInstance

example : (classicalEquiv (V := V)).functor = toAlmost (classical V) :=
  classicalEquiv_functor

/-! ### Structure of the category -/

noncomputable example (S : BasicSetup V) : Abelian (Module S) :=
  inferInstance

example (S : BasicSetup V) :
    PreservesFiniteLimits (toAlmost S) ∧ PreservesFiniteColimits (toAlmost S) :=
  ⟨inferInstance, inferInstance⟩

-- `toAlmost` is `V`-linear.
example (S : BasicSetup V) {M N : ModuleCat V} (ε : V) (f : M ⟶ N) :
    (toAlmost S).map (ε • f) = ε • (toAlmost S).map f :=
  (toAlmost S).map_smul ε f

-- `toAlmost` kills almost zero modules, and its factorisation through itself is the identity.
noncomputable example (S : BasicSetup V) :
    𝟭 (Module S) ≅ lift S (toAlmost S) fun M hM ↦ (isZero_toAlmost_obj_iff S M).mpr hM :=
  liftUniq S _ _ (𝟭 _) (Functor.rightUnitor _)
