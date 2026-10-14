/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Algebra.Module.CharacterModule
public import TauCeti.Data.ZMod.Units
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Characters for the cyclotomic input to global class field theory

Let `q > 1` and `N > 0`, and put `m = q ^ N - 1`. The class of `q` in `(ZMod m)ˣ` has exact
order `N` (`TauCeti.ZMod.orderOf_unitOfCoprime_pow_sub_one`). Consequently there is an additive
character of `(ZMod m)ˣ` taking `q` to `1 / N` in `ℚ / ℤ`. Composing this character with the
action on a primitive `m`-th root of unity gives a character of a cyclotomic Galois group with the
same prescribed value.

These are the finite-group ingredients in the cyclotomic construction used to produce an idele
class of invariant `1 / N`: at a finite place with residue cardinality `q`, arithmetic Frobenius
acts on the `m`-th roots of unity as the `q`-th power. The global carry class attached to the
resulting character therefore has local invariant `1 / N` at a uniformizer of that place.

## Main results

* `CharacterModule.exists_apply_unitOfCoprime_pow_sub_one`: a character of
  `(ZMod (q ^ N - 1))ˣ` takes `q` to `1 / N`; it is obtained from the general
  `TauCeti.CharacterModule.exists_apply_eq_inv_addOrderOf`.
* `IsPrimitiveRoot.exists_character_autToPow_apply`: the corresponding character on a
  cyclotomic Galois group.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3.
-/

public section

noncomputable section

namespace TauCeti

namespace CharacterModule

/-- If `q > 1` and `N > 0`, there is a character of `(ZMod (q ^ N - 1))ˣ` taking the class of
`q` to `1 / N`. -/
theorem exists_apply_unitOfCoprime_pow_sub_one (q N : ℕ) (hq : 1 < q) (hN : N ≠ 0) :
    ∃ χ : CharacterModule (Additive (ZMod (q ^ N - 1))ˣ),
      χ (.ofMul (ZMod.unitOfCoprime q (Nat.coprime_pow_sub_one q N hq hN))) =
        ((1 / N : ℚ) : AddCircle (1 : ℚ)) := by
  let u := ZMod.unitOfCoprime q (Nat.coprime_pow_sub_one q N hq hN)
  have horder : addOrderOf (Additive.ofMul u) = N := by
    rw [addOrderOf_ofMul_eq_orderOf, ZMod.orderOf_unitOfCoprime_pow_sub_one q N hq hN]
  obtain ⟨χ, hχ⟩ :=
    exists_apply_eq_inv_addOrderOf (Additive.ofMul u) (horder.trans_ne hN)
  exact ⟨χ, by simpa only [horder] using hχ⟩

end CharacterModule

end TauCeti

namespace IsPrimitiveRoot

/-- **The prescribed cyclotomic character.** Let `ζ` be a primitive `(q ^ N - 1)`-th root of
unity in an extension `E/K`. There is a character of `Aut(E/K)` taking every automorphism acting
on `ζ` by the `q`-th power to `1 / N`.

At a finite place of residue cardinality `q`, this hypothesis is precisely the arithmetic
Frobenius action on roots of unity. -/
theorem exists_character_autToPow_apply {K E : Type*} [CommRing K] [CommRing E] [IsDomain E]
    [Algebra K E]
    {q N : ℕ} (hq : 1 < q) (hN : N ≠ 0) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (q ^ N - 1)) :
    ∃ χ : Additive (E ≃ₐ[K] E) →+ AddCircle (1 : ℚ),
      ∀ σ : E ≃ₐ[K] E,
        ζ ^ q = σ ζ →
          χ (.ofMul σ) = ((1 / N : ℚ) : AddCircle (1 : ℚ)) := by
  let _ : NeZero (q ^ N - 1) := ⟨by
    have : 1 < q ^ N := one_lt_pow₀ hq hN
    omega⟩
  obtain ⟨χ, hχ⟩ := TauCeti.CharacterModule.exists_apply_unitOfCoprime_pow_sub_one q N hq hN
  refine ⟨χ.comp (hζ.autToPow K).toAdditive, fun σ hσ ↦ ?_⟩
  -- `χ : CharacterModule _` is a semireducible definition for an `→+`, so
  -- `AddMonoidHom.comp_apply` cannot rewrite the composite (the term is ill-typed at instance
  -- transparency); evaluate it definitionally instead.
  change χ (.ofMul (hζ.autToPow K σ)) = _
  have haut : hζ.autToPow K σ =
      ZMod.unitOfCoprime q (Nat.coprime_pow_sub_one q N hq hN) :=
    Units.ext ((hζ.coe_autToPow_eq_natCast hσ.symm).trans (ZMod.coe_unitOfCoprime _ _).symm)
  rw [haut, hχ]

end IsPrimitiveRoot
