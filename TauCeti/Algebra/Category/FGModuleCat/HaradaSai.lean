/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.HaradaSai
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.Preadditive.Radical.Chain

/-!
# The nilpotency index of the radical of `mod A`

Let `A` be a left Artinian ring, for instance an Artin algebra, and suppose that every finitely
generated indecomposable `A`-module has length at most `b`. Then the `(2 ^ b - 1)`-th power of the
radical of the category `FGModuleCat A` of finitely generated `A`-modules vanishes
(`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`).

The motivating case is a representation-finite algebra `A`, whose finitely generated
indecomposable modules have bounded length (`TauCeti.IsRepresentationFinite.exists_length_le`), so
that the radical of `mod A` is nilpotent with an explicit bound on the exponent. The theorem itself
assumes only the length bound, not representation-finiteness.

The category `FGModuleCat A` is Krull-Schmidt (`FGModuleCat.isKrullSchmidt_of_isArtinianRing`), so
its powers of the radical are detected by chains of non-isomorphisms between objects with local
endomorphism rings (`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_iff`). These objects are
indecomposable modules, and the composite of `2 ^ b - 1` such non-isomorphisms vanishes by the
Harada–Sai lemma (`TauCeti.composableArrows_hom_eq_zero_of_length_le`).

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Corollary VI.1.3 and the discussion after it.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Lemma IV.5.2.
* M. Harada and Y. Sai, *On categories of indecomposable modules. I*, Osaka J. Math. 7 (1970),
  323–344.
-/

public section

namespace TauCeti

open CategoryTheory

universe w v

/-- **The radical of `mod A` is nilpotent of index at most `2 ^ b - 1`** when every finitely
generated indecomposable module over the left Artinian ring `A` has length at most `b`: the
`(2 ^ b - 1)`-th power of the radical of `FGModuleCat A` vanishes. -/
theorem jacobsonRadicalIdeal_pow_eq_bot_of_length_le {A : Type v} [Ring A] [IsArtinianRing A]
    {b : ℕ} (h : ∀ X : FGModuleCat.{w} A, Indecomposable X.obj → Module.length A X.obj ≤ b) :
    jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ (2 ^ b - 1) = ⊥ := by
  refine (jacobsonRadicalIdeal_pow_eq_bot_iff _).mpr fun G hG hl ↦ ?_
  -- Read the chain in `ModuleCat A`, where its objects are indecomposable modules.
  let ι := ObjectProperty.ι (ModuleCat.isFG.{w} A)
  have hind (i : Fin (2 ^ b - 1 + 1)) : Indecomposable (G.obj i).obj :=
    (FGModuleCat.indecomposable_obj_iff _).mpr indecomposable_of_isLocalRing_end
  refine ι.map_injective ?_
  rw [Functor.map_zero]
  exact composableArrows_hom_eq_zero_of_length_le (G ⋙ ι) hind (fun i ↦ h _ (hind i))
    (fun i hi hiso ↦ hl i hi ((isIso_iff_of_reflects_iso _ ι).mp hiso)) le_rfl

end TauCeti
