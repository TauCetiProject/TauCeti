/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.CanonicalExtension

/-!
# Checks for Glauberman's canonical extension

These examples check `TauCeti.IsCanonicalExtension` in three small cases.

* Trivial action: `Γ ⋊[1] S` is `Γ × S`, and the canonical extension of `χ` is `χ × 1_S`,
  `x ↦ χ x.left`.
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

variable {k : Type*} [Field k]

/-- **Trivial action**: for the trivial action, `Γ ⋊[1] S ≅ Γ × S`, and the canonical extension of
an irreducible character `χ` of `Γ` is `χ × 1_S`, read through the first coordinate. -/
example {Γ S : Type*} [Group Γ] [Group S] {χ : Γ → k} (hχ : χ ∈ irreducibleCharacters k Γ) :
    IsCanonicalExtension (1 : S →* MulAut Γ) χ fun x => χ x.left := by
  obtain ⟨n, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  let π : Γ ⋊[(1 : S →* MulAut Γ)] S →* Γ := (MonoidHom.fst Γ S).comp mulEquivProd.toMonoidHom
  have hπ : Function.Surjective π := fun g => ⟨inl g, rfl⟩
  refine isCanonicalExtension_iff.2
    ⟨π.comp_mem_irreducibleCharacters hπ hχ, rfl, n, ρ.comp π, rfl, fun s => ?_⟩
  have hπs : π (inr s) = 1 := by simp [π]
  rw [MonoidHom.comp_apply, hπs, map_one, map_one]

variable [IsAlgClosed k] [CharZero k]

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
  let φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 3)) := 1
  have hcop :
      (Nat.card (Multiplicative (ZMod 3))).Coprime (Nat.card (Multiplicative (ZMod 2))) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide
  have hχ : (fun g => (χ g : ℂ)) ∈ irreducibleCharacters ℂ (Multiplicative (ZMod 3)) :=
    χ.coe_mem_irreducibleCharacters
  -- The canonical extension is `χ × 1`, read through the first coordinate.
  have hext : IsCanonicalExtension φ (fun g => (χ g : ℂ)) fun x => (χ x.left : ℂ) := by
    obtain ⟨n, ρ, -, hρ⟩ := mem_irreducibleCharacters_iff.1 hχ
    let π : Multiplicative (ZMod 3) ⋊[φ] Multiplicative (ZMod 2) →* Multiplicative (ZMod 3) :=
      (MonoidHom.fst _ _).comp mulEquivProd.toMonoidHom
    have hπ : Function.Surjective π := fun g => ⟨inl g, rfl⟩
    refine isCanonicalExtension_iff.2 ⟨π.comp_mem_irreducibleCharacters hπ hχ, rfl, n, ρ.comp π,
      by rw [Representation.character_comp, hρ]; rfl, fun s => ?_⟩
    have hπs : π (inr s) = 1 := rfl
    rw [MonoidHom.comp_apply, hπs, map_one, map_one]
  have hψ' : ψ = fun x => (χ x.left : ℂ) :=
    (existsUnique_canonicalExtension hcop hχ fun _ _ => rfl).unique hψ hext
  have hrange : Set.range ψ = Set.range fun g => (χ g : ℂ) := by
    rw [hψ']
    exact Set.ext fun z => ⟨fun ⟨x, hx⟩ => ⟨x.left, hx⟩, fun ⟨g, hg⟩ => ⟨inl g, hg⟩⟩
  have hadj : IntermediateField.adjoin ℚ (Set.range fun g => (χ g : ℂ)) = ℚ⟮ζ⟯ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_)
      (IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.subset_adjoin _ _ ⟨_, hζ⟩))
    rintro _ ⟨g, rfl⟩
    have hg : g = Multiplicative.ofAdd 1 ^ (Multiplicative.toAdd g).val := by
      rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
    simp only
    rw [hg, map_pow, Units.val_pow_eq_pow_val, hζ]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  refine ⟨fun s => ?_, hrange ▸ hadj, hadj⟩
  rw [hψ']
  simp

end TauCeti.Examples.RepresentationTheory.CanonicalExtension
