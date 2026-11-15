/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Linear forms on the top of a local endomorphism ring

Let `C` be an `R`-linear category and `X` an object with local endomorphism ring, so that the
non-isomorphisms `X ⟶ X` form the radical `rad(X, X)`. Let `Q` be an injective `R`-module
receiving a nonzero map from every `R ⧸ 𝔪`, so that `Q` separates points. Then there is an
`R`-linear form on `End(X)` vanishing on `rad(X, X)` but not at the identity: a functional on the
top `End(X) / rad(X, X)`.

The same holds after passing to the quotient `C/I` by an ideal not containing `𝟙 X`, as such an
ideal contains no isomorphism and so lies in the radical at `X`. This is the form in which the
dual of the top of a local endomorphism ring produces almost-split classes in Auslander–Reiten
theory, where `I` is an ideal of projectively or injectively trivial morphisms.

## Main results

* `TauCeti.MorphismIdeal.exists_linearMap_quotient_end`: on `(C/I)(X, X)`, a linear form into
  `Q` that is nonzero at the identity and vanishes on the classes of the non-isomorphisms.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section V.1.
-/

public section

namespace TauCeti.MorphismIdeal

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [CommRing R] [Linear R C]
  {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.Injective R Q] [Small.{w} R]

/-- **A linear form on the top of a local endomorphism ring.** If `End X` is local and the ideal
`I` does not contain `𝟙 X`, there is a linear form on `(C/I)(X, X)` with values in `Q` that is
nonzero at the identity and vanishes on the classes of the non-isomorphisms, whenever `Q` is
injective and receives a nonzero map from every `R ⧸ 𝔪`. -/
theorem exists_linearMap_quotient_end
    (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] Q)) (I : MorphismIdeal C)
    (X : C) [IsLocalRing (End X)] (hX : 𝟙 X ∉ I.hom X X) :
    ∃ ψ : (I.quotientFunctor.obj X ⟶ I.quotientFunctor.obj X) →ₗ[R] Q,
      ψ (I.quotientFunctor.map (𝟙 X)) ≠ 0 ∧
        ∀ c : X ⟶ X, ¬ IsIso c → ψ (I.quotientFunctor.map c) = 0 := by
  obtain ⟨ψ, hψ1, hψ⟩ := exists_apply_ne_zero_of_notMem hQ
    (N := jacobsonRadicalSubmodule R X X) (m := 𝟙 X) (by
      rw [mem_jacobsonRadicalSubmodule, mem_jacobsonRadical_iff_not_isIso, not_not]
      infer_instance)
  -- A morphism of `I` is not an isomorphism, so `ψ` descends to `(C/I)(X, X)`.
  refine ⟨(I.homSubmodule R X X).liftQ ψ (fun c hc ↦ LinearMap.mem_ker.mpr (hψ c (by
      simpa using I.not_isIso_of_mem hX ((MorphismIdeal.mem_homSubmodule R I c).mp hc)))) ∘ₗ
    (I.homLinearEquiv R X X).symm.toLinearMap, ?_, fun c hc ↦ ?_⟩
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      MorphismIdeal.homLinearEquiv_symm_quotientFunctor_map, Submodule.liftQ_apply]
    exact hψ1
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      MorphismIdeal.homLinearEquiv_symm_quotientFunctor_map, Submodule.liftQ_apply]
    exact hψ c (by simpa using hc)

end TauCeti.MorphismIdeal
