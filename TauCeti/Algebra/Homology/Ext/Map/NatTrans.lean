/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Natural transformations of exact functors and composites of Ext classes

For a natural transformation `τ : Φ ⟶ Ψ` of exact functors between abelian categories, Mathlib's
`CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp` says that `Φ x` followed by
`τ` equals `τ` followed by `Ψ x`. This file records the same naturality with a further class
composed on the right (`CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_comp`), the form in
which it is used to move `τ` across a Yoneda product.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/Lib/Cohomology/Etale/Basic.lean` (declaration `New.Variety.mapExactFunctor_naturality`) and
  `src/Lib/Cohomology/Hodge/CupProduct.lean` (its use in the proofs of `New.Variety.cup_map` and
  `New.Variety.Comparison.pull_cup`); Apache 2.0, Copyright 2026 Anthropic, PBC. The lemma is
  adapted from these and stated for arbitrary abelian categories.
-/

public section

open CategoryTheory Limits

universe t t'

namespace CategoryTheory.Abelian.Ext

variable {𝒜 𝒟 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasExt.{t} 𝒜] [Category* 𝒟] [Abelian 𝒟]
  [HasExt.{t'} 𝒟]

/-- Naturality of the action of exact functors on Ext, with a class composed on the right: for
`τ : Φ ⟶ Ψ`, the class `Φ x` followed by `τ` and `z` is `τ` followed by `Ψ x` and `z`. -/
lemma mapExactFunctor_comp_mk₀_comp {Φ Ψ : 𝒜 ⥤ 𝒟} [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (τ : Φ ⟶ Ψ) {X Y : 𝒜} {W : 𝒟} {a c n : ℕ}
    (x : Ext.{t} X Y a) (z : Ext.{t'} (Ψ.obj Y) W c) (h : a + c = n) :
    (x.mapExactFunctor Φ).comp ((mk₀ (τ.app Y)).comp z (zero_add c)) h =
      (mk₀ (τ.app X)).comp ((x.mapExactFunctor Ψ).comp z h) (zero_add n) := by
  rw [← comp_assoc_of_second_deg_zero, mapExactFunctor_comp_mk₀_natTransApp,
    comp_assoc _ _ _ (zero_add a) h (by lia)]

end CategoryTheory.Abelian.Ext
