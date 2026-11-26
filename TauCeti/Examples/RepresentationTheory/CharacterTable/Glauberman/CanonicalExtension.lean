/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.CanonicalExtension.Basic

/-!
# Checks for Glauberman's canonical extension

These examples check `TauCeti.IsCanonicalExtension` in two small cases. The general trivial-action
case, where the canonical extension of `χ` is `x ↦ χ x.left`, is
`TauCeti.isCanonicalExtension_one_left`.

* `S₃ = C₃ ⋊ C₂`, as the affine group `TauCeti.AffineGroup (ZMod 3)`, with `C₂ = (ZMod 3)ˣ` acting
  on `C₃` by negation: the sign character also extends the trivial character of `C₃`, but the
  canonical extension of `1` is `1`, and the sign is not canonical.
* Trivial action of `C₂` on `C₃`, with `χ` the linear character sending the generator to `ζ`: the
  canonical extension takes the value `1` on `C₂`, and its values generate `ℚ(ζ) = ℚ(χ)`.
-/

public section

open SemidirectProduct

namespace TauCeti.Examples.RepresentationTheory.CanonicalExtension

open scoped IntermediateField

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- **`S₃ = C₃ ⋊ C₂`**, as the affine group `TauCeti.AffineGroup (ZMod 3)`, in which the unit `-1`
acts on `C₃` by negation: the sign character, `1` or `-1` according to whether the linear part
`x.right` is `1`, extends the trivial character of `C₃`, but it is not the canonical extension of
`1`, which is `1`: the sign has determinant `-1` on `C₂`. -/
example :
    ((fun x : AffineGroup (ZMod 3) => if x.right = 1 then (1 : k) else -1) ∘ inl =
      fun _ => (1 : k)) ∧
      IsCanonicalExtension (affineAction (ZMod 3)) (fun _ => (1 : k)) (fun _ => 1) ∧
      ¬ IsCanonicalExtension (affineAction (ZMod 3)) (fun _ => (1 : k))
        fun x => if x.right = 1 then 1 else -1 := by
  refine ⟨funext fun _ => by simp, isCanonicalExtension_one, fun h => ?_⟩
  have hcop : (Nat.card (Multiplicative (ZMod 3))).Coprime (Nat.card (ZMod 3)ˣ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide
  have hne : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
  have h1 := congrFun (h.eq_one hcop) (inr (-1))
  norm_num [hne] at h1

/-- **Trivial action, values**: for the trivial action of `C₂` on `C₃` and a linear character `χ`
of `C₃` sending the generator to `ζ`, the canonical extension `ψ` of `χ` takes the value `1` on
`C₂`, and `ℚ(ψ) = ℚ(ζ) = ℚ(χ)`. -/
example (χ : Multiplicative (ZMod 3) →* ℂˣ) (ζ : ℂ) (hζ : χ (.ofAdd 1) = ζ)
    {ψ : Multiplicative (ZMod 3) ⋊[(1 : Multiplicative (ZMod 2) →* MulAut _)]
      Multiplicative (ZMod 2) → ℂ}
    (hψ : IsCanonicalExtension 1 (fun g => (χ g : ℂ)) ψ) :
    (∀ s, ψ (inr s) = 1) ∧ IntermediateField.adjoin ℚ (Set.range ψ) = ℚ⟮ζ⟯ ∧
      IntermediateField.adjoin ℚ (Set.range fun g => (χ g : ℂ)) = ℚ⟮ζ⟯ := by
  have hcop :
      (Nat.card (Multiplicative (ZMod 3))).Coprime (Nat.card (Multiplicative (ZMod 2))) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide
  have hχ : (fun g => (χ g : ℂ)) ∈ irreducibleCharacters ℂ (Multiplicative (ZMod 3)) :=
    χ.coe_mem_irreducibleCharacters
  -- The canonical extension is `χ × 1`, read through the first coordinate.
  have hψ' : ψ = fun x => (χ x.left : ℂ) :=
    (existsUnique_canonicalExtension hcop hχ fun _ _ => by simp).unique hψ
      (isCanonicalExtension_one_left hχ)
  have hrange : Set.range ψ = Set.range fun g => (χ g : ℂ) := by
    rw [hψ']
    exact Function.Surjective.range_comp (fun g => ⟨inl g, rfl⟩) fun g => (χ g : ℂ)
  have hadj : IntermediateField.adjoin ℚ (Set.range fun g => (χ g : ℂ)) = ℚ⟮ζ⟯ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_)
      (IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.subset_adjoin _ _ ⟨_, hζ⟩))
    rintro _ ⟨g, rfl⟩
    have hg : g = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd g).val := by
      rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
    beta_reduce
    rw [hg, map_pow, Units.val_pow_eq_pow_val, hζ]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  refine ⟨fun s => ?_, hrange ▸ hadj, hadj⟩
  rw [hψ']
  simp

end TauCeti.Examples.RepresentationTheory.CanonicalExtension
