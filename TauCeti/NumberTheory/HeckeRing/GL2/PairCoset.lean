/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Handedness

/-!
# The double coset a pair of right-coset representatives lands in

Composing two Hecke operators indexed by double cosets `Γ₁ δ₁ Γ₂ = ⊔ᵥ Γ₁ aᵥ` and
`Γ₂ δ₂ Γ₃ = ⊔_w Γ₂ b_w` — whether they act on functions on `ℍ` by slash sums or on modular
symbols — produces a double sum over the products `aᵥ b_w`. Rewriting that double sum as
`∑_D m(D₁, D₂; D) • T_D` is a piece of set-level bookkeeping with no operator in it: group the
pairs `(v, w)` by the double coset `Γ₁ (aᵥ b_w) Γ₃` their product lies in, and count how often
the pairs over one double coset `D` meet each of its right cosets. This file supplies that
bookkeeping once, for both consumers.

`pairCoset D₁ D₂` is the grouping map, from pairs of right-coset indices to `HeckeCoset Δ Γ₁ Γ₃`,
characterised by `pairCoset_eq_iff`. The count is
`card_pairs_pairCoset_rightCoset_eq_multiplicity`: among the pairs over `D`, the number whose
product spans a given right coset `Γ₁ x` of `D` is Shimura's multiplicity in its right-coset
indexed form `DoubleCoset.multiplicity Γ₃ Γ₂ Γ₁ δ₂⁻¹ δ₁⁻¹ δ₃⁻¹`, independently of `x`. Its two
ingredients are `DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`, which reconciles the
handedness, and `DoubleCoset.card_pairs_mem_rightCoset_congr`, which supplies the uniformity in
`x`.

Between images `Γᵢ.map (mapGL ℚ)` of subgroups of `SL(2, ℤ)`, the double cosets met by the
products of two integral representatives are again integral
(`mem_intEntries_of_mem_image_pairCoset`), which is what operators indexed by integral double
cosets need at each output coset of the composition law.

## Main results

* `HeckeRing.GL2.pairCoset`: the double coset `Γ₁ (aᵥ b_w) Γ₃` that a pair of right-coset
  representatives lands in — the map the double sum is fibred over.
* `HeckeRing.GL2.pairCoset_eq_iff`: a pair lies in the fibre over `D` exactly when the product
  of its two representatives lies in `D`'s double coset.
* `HeckeRing.GL2.PairCosetFiber`: among the pairs lying over `D`, those whose product spans the
  right coset `Γ₁ x` — the type the multiplicity counts.
* `HeckeRing.GL2.card_pairs_pairCoset_rightCoset_eq_multiplicity`: each right coset of a double
  coset `D` is met by `m(D₁, D₂; D)` of the pairs, whichever right coset of `D` is chosen.
* `HeckeRing.GL2.mem_intEntries_of_mem_image_pairCoset`: between images of subgroups of
  `SL(2, ℤ)`, every double coset met by the products of two integral representatives is integral.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: the displayed computation preceding Proposition 3.37.
-/

public section

open Matrix Matrix.SpecialLinearGroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ Γ₃ : Subgroup (GL (Fin 2) ℚ)}

attribute [local instance] Fintype.ofFinite

section PairCoset

variable [IsHeckeTriple Δ Γ₁ Γ₂] [IsHeckeTriple Δ Γ₂ Γ₃]
  (D₁ : HeckeCoset Δ Γ₁ Γ₂) (D₂ : HeckeCoset Δ Γ₂ Γ₃)

/-- **The product `aᵥ b_w` of a right-coset representative of `D₁` and one of `D₂`, as an element
of `Δ`.** Each factor lies in the double coset of an element of `Δ`, hence in `Δ` itself by
`IsHeckeTriple.mem_of_mem_doubleCoset`, and a submonoid is closed under multiplication.

Membership in `Δ` is the point of the definition: it is what lets the product name an element of
`HeckeCoset Δ Γ₁ Γ₃`, which is how the double sum of a composite is partitioned. -/
private noncomputable def pairRep (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) : Δ :=
  ⟨rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2, mul_mem
    (IsHeckeTriple.mem_of_mem_doubleCoset (D₁.out).2 (rightCosetRep_mem_doubleCoset D₁ p.1))
    (IsHeckeTriple.mem_of_mem_doubleCoset (D₂.out).2 (rightCosetRep_mem_doubleCoset D₂ p.2))⟩

/-- The underlying matrix of `pairRep` is the product of the two right-coset
representatives. -/
private lemma coe_pairRep (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) :
    (pairRep D₁ D₂ p : GL (Fin 2) ℚ) = rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2 := (rfl)

/-- **The double coset `Γ₁ (aᵥ b_w) Γ₃` a pair of representatives lands in.** This is the map the
double sum of a composite of two Hecke operators is fibred over. -/
noncomputable def pairCoset (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) : HeckeCoset Δ Γ₁ Γ₃ :=
  HeckeCoset.mk Γ₁ Γ₃ (pairRep D₁ D₂ p)

/-- `pairCoset` is the double coset of `pairRep`; `pairCoset_eq_iff` characterises it by
membership. -/
private lemma pairCoset_def (p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
    DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹) :
    pairCoset D₁ D₂ p = HeckeCoset.mk Γ₁ Γ₃ (pairRep D₁ D₂ p) := (rfl)

variable {D₁ D₂}
variable {D : HeckeCoset Δ Γ₁ Γ₃} {p : DecompQuotient Γ₂ Γ₁ (D₁.out : GL (Fin 2) ℚ)⁻¹ ×
  DecompQuotient Γ₃ Γ₂ (D₂.out : GL (Fin 2) ℚ)⁻¹}

/-- **`pairCoset` is characterised by membership**: a pair lies in the fibre over `D` exactly
when the product of its two representatives lies in the double coset of `D`. -/
@[simp] lemma pairCoset_eq_iff : pairCoset D₁ D₂ p = D ↔
    rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2 ∈
      doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃ := by
  constructor
  · intro h
    have hD := HeckeCoset.eq_iff.mp
      ((pairCoset_def D₁ D₂ p).symm.trans (h.trans (HeckeCoset.mk_rep D).symm))
    rw [HeckeCoset.rep_def, coe_pairRep] at hD
    exact hD ▸ mem_doubleCoset_self Γ₁ Γ₃ _
  · intro h
    rw [pairCoset_def, ← HeckeCoset.mk_rep D]
    refine HeckeCoset.eq_iff.mpr ?_
    rw [HeckeCoset.rep_def, coe_pairRep]
    exact doubleCoset_eq_of_mem h

/-- A pair whose product lies in one right coset `Γ₁ x` of a double coset is in the fibre of
`pairCoset` over that double coset: a right coset is contained in the double coset it
generates, and `x` generates `D`. -/
private lemma pairCoset_eq_of_mem_rightCoset {x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃)
    (hp : rightCosetRep D₁ p.1 * rightCosetRep D₂ p.2 ∈
      MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))) :
    pairCoset D₁ D₂ p = D := by
  refine pairCoset_eq_iff.mpr ?_
  rw [← doubleCoset_eq_of_mem hx]
  exact mem_doubleCoset.mpr ⟨_, (mem_rightCoset_iff x).mp hp, 1, one_mem _, by group⟩

/-- **The pairs over `D` whose product spans the right coset `Γ₁ x`.** Among the index pairs
whose product lies in the double coset `D`, those whose product generates the same right coset
of `Γ₁` as `x` does. `card_pairs_pairCoset_rightCoset_eq_multiplicity` counts this type; its
nonemptiness is what identifies the support of the Hecke structure constants downstream. -/
abbrev PairCosetFiber (D₁ : HeckeCoset Δ Γ₁ Γ₂) (D₂ : HeckeCoset Δ Γ₂ Γ₃)
    (D : HeckeCoset Δ Γ₁ Γ₃) (x : GL (Fin 2) ℚ) : Type :=
  {i : {q // pairCoset D₁ D₂ q = D} //
    MulOpposite.op (rightCosetRep D₁ i.1.1 * rightCosetRep D₂ i.1.2) •
        (Γ₁ : Set (GL (Fin 2) ℚ)) = MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))}

/-- **Each right coset of a double coset `D` is met by Shimura's multiplicity `m(D₁, D₂; D)`
many pairs**, whichever `x ∈ D` names that right coset: among the pairs lying over `D`, the
number whose product spans the right coset `Γ₁ x` does not depend on `x`. -/
lemma card_pairs_pairCoset_rightCoset_eq_multiplicity {x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₃) :
    Nat.card (PairCosetFiber D₁ D₂ D x) =
      DoubleCoset.multiplicity Γ₃ Γ₂ Γ₁ (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹
        (D.out : GL (Fin 2) ℚ)⁻¹ := by
  have hiff (y : GL (Fin 2) ℚ) :
      (MulOpposite.op y • (Γ₁ : Set (GL (Fin 2) ℚ)) =
          MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ))) ↔
        y ∈ MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    rw [rightCoset_eq_iff, mem_rightCoset_iff]
    exact ⟨fun h ↦ by simpa using inv_mem h, fun h ↦ by simpa using inv_mem h⟩
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtype (p := fun q ↦ pairCoset D₁ D₂ q = D)
      (q := fun q ↦ MulOpposite.op (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) •
        (Γ₁ : Set (GL (Fin 2) ℚ)) = MulOpposite.op x • (Γ₁ : Set (GL (Fin 2) ℚ)))
      fun {q} hq ↦ pairCoset_eq_of_mem_rightCoset hx ((hiff _).mp hq)),
    ← card_pairs_mem_rightCoset_eq_multiplicity Γ₁ Γ₂ Γ₃ (D₁.out : GL (Fin 2) ℚ)
      (D₂.out : GL (Fin 2) ℚ) (D.out : GL (Fin 2) ℚ)]
  simp only [hiff, rightCosetRep_def, Set.coe_ofPred]
  exact card_pairs_mem_rightCoset_congr Γ₁ Γ₂ Γ₃ (D₁.out : GL (Fin 2) ℚ)
    (D₂.out : GL (Fin 2) ℚ) hx

end PairCoset

section Integral

variable (Γ₁ Γ₂ Γ₃ : Subgroup SL(2, ℤ))
  [IsHeckeTriple Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ))]
  [IsHeckeTriple Δ (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ))]
  (D₁ : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
  (D₂ : HeckeCoset Δ (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)))
  (hD₁ : (D₁.out : GL (Fin 2) ℚ) ∈ intEntries 2) (hD₂ : (D₂.out : GL (Fin 2) ℚ) ∈ intEntries 2)

include hD₁ hD₂ in
open Classical in
/-- **Every double coset met by the products of the representatives is integral.** Between images
`Γᵢ' = Γᵢ.map (mapGL ℚ)` of subgroups of `SL(2, ℤ)`, if `D₁.out` and `D₂.out` are integral then so
is `D.out` for every `D` in the image of `pairCoset D₁ D₂`: such a `D` is the double coset of a
product `aᵥ b_u` of two integral representatives, and
`HeckeRing.GLn.mem_intEntries_of_mem_doubleCoset` applies. This supplies the integrality proof that
operators indexed by integral double cosets ask for at each output coset of the composition law;
nothing is assumed of the other elements of `Δ`. -/
theorem mem_intEntries_of_mem_image_pairCoset
    {D : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ))}
    (hD : D ∈ Finset.univ.image (pairCoset D₁ D₂)) : (D.out : GL (Fin 2) ℚ) ∈ intEntries 2 := by
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hD
  -- `D.out` lies in its own double coset, which is that of the product of the representatives
  have hmem : ((pairCoset D₁ D₂ q).out : GL (Fin 2) ℚ) ∈
      doubleCoset (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) (Γ₁.map (mapGL ℚ))
        (Γ₃.map (mapGL ℚ)) := by
    rw [doubleCoset_eq_of_mem (pairCoset_eq_iff.mp rfl)]
    exact mem_doubleCoset_self _ _ _
  exact mem_intEntries_of_mem_doubleCoset 2
    (mul_mem (rightCosetRep_mem D₁ hD₁ (map_mapGL_le_intEntries 2 Γ₂) q.1)
      (rightCosetRep_mem D₂ hD₂ (map_mapGL_le_intEntries 2 Γ₃) q.2)) hmem

end Integral

end HeckeRing.GL2

end
