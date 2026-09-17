/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Normalizer
public import TauCeti.NumberTheory.HeckeRing.Multiplication

import Mathlib.Tactic.Group

/-!
# Hecke double cosets at a normalizing element

`GroupTheory/DoubleCoset/Normalizer.lean` collapses a double coset `ΓgΓ` to the single right
coset `Γg` when `g` normalizes `Γ`. This file draws the Hecke-ring consequences, for a Hecke
triple `(Δ, Γ, Γ)` and an `x : Δ` normalizing `Γ`:

* the underlying set of `HeckeCoset.mk Γ Γ x` is `Γx`, and so is the double coset of its chosen
  representative — the shape in which the slash sum of a double coset consumes a decomposition;
* the chosen representative again normalizes `Γ`, so the decomposition quotient
  `Γ ⧸ (Γ ∩ xΓx⁻¹)` is a subsingleton;
* consequently the basis elements multiply with no structure constant to count,
  `[ΓxΓ] · [ΓyΓ] = [Γ(xy)Γ]`, as soon as **one** of the two factors normalizes `Γ` — the other
  is an arbitrary element of `Δ`. Both handednesses are proved, and neither follows from the
  other: `multiplicity Γ₁ Γ₂ Γ₃ g h d` quotients by `Γ₃` on the right only, so it is not
  symmetric in its two arguments.

The last statement is what lets a submonoid of the normalizer of `Γ` act on the Hecke ring
through its basis elements, and, because the right factor is unconstrained, lets that action be
computed against an arbitrary basis element rather than only against another normalizing one.
For `Γ₁(N) ⊴ Γ₀(N)` it is the diamond direction of the `Γ₁(N)` Hecke ring, in
`HeckeRing/GL2/Gamma1/DiamondCosets.lean`.

## Main results

* `DoubleCoset.subsingleton_decompQuotient_of_mem_normalizer`: the decomposition quotient at a
  normalizing element is a subsingleton.
* `HeckeCoset.toSet_mk_eq_rightCoset_of_mem_normalizer` and
  `HeckeCoset.doubleCoset_out_mk_eq_rightCoset_of_mem_normalizer`: the double coset of a
  normalizing element is the single right coset `Γx`, at `x` itself and at the chosen
  representative.
* `DoubleCoset.multiplicity_le_one_of_mem_normalizer_right`: the mirror of
  `multiplicity_le_one_of_subsingleton`, bounding via the *second* decomposition quotient. It
  asks only that the second element normalize `Γ`; the subsingleton hypothesis its counterpart
  takes is implied here.
* `HeckeCosetModule.single_mul_single_of_mem_normalizer` and
  `HeckeCosetModule.single_mul_single_of_mem_normalizer_right`: the basis element of a
  normalizing element times the basis element of an arbitrary one is the basis element of their
  product, with the normalizing factor on either side.
* `HeckeCosetModule.commute_single_of_mem_normalizer`: consequently a commutation question in
  the Hecke ring is discharged by the single coset identity `Γ(xy)Γ = Γ(yx)Γ`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1.
-/

public section

open DoubleCoset MulOpposite

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ : Subgroup G} {g : G}

/-- **The decomposition quotient at a normalizing element is a subsingleton**: the stabilizer
`Γ ∩ gΓg⁻¹` is all of `Γ`. This is `subsingleton_decompQuotient_of_mem` with membership in `Γ`
weakened to membership in its normalizer. -/
lemma subsingleton_decompQuotient_of_mem_normalizer
    (hg : g ∈ Subgroup.normalizer (Γ : Set G)) : Subsingleton (DecompQuotient Γ Γ g) :=
  subsingleton_decompQuotient (Subgroup.conjAct_pointwise_smul_eq_self hg).ge

/-- **A second factor that normalizes `Γ` forces multiplicity at most one.**

The mirror of `multiplicity_le_one_of_subsingleton`, which bounds via the *first* decomposition
quotient. `multiplicity` is not symmetric — it quotients by `Γ₃` on the right only — so this is
a separate statement rather than that one applied backwards, and normalisation is what replaces
the subsingleton hypothesis the first-quotient version takes: here it is implied, by
`subsingleton_decompQuotient_of_mem_normalizer`. -/
lemma multiplicity_le_one_of_mem_normalizer_right {Γ : Subgroup G} {g h d : G}
    (hh : h ∈ Subgroup.normalizer (Γ : Set G)) :
    multiplicity Γ Γ Γ g h d ≤ 1 := by
  have hs : Subsingleton (DecompQuotient Γ Γ h) :=
    subsingleton_decompQuotient_of_mem_normalizer hh
  rw [multiplicity_def]
  have hfib : Subsingleton {p : DecompQuotient Γ Γ g × DecompQuotient Γ Γ h |
      ((p.1.out : G) * g * ((p.2.out : G) * h) : G ⧸ Γ) = (d : G ⧸ Γ)} := by
    constructor
    rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩
    simp only [Set.mem_ofPred_eq] at hp₁ hp₂
    obtain rfl : j₁ = j₂ := hs.elim j₁ j₂
    obtain rfl : i₁ = i₂ := by
      refine mk_out_mul_injective Γ Γ g ?_
      have hq := hp₁.trans hp₂.symm
      rw [QuotientGroup.eq] at hq ⊢
      -- `hq` says the goal's element is `Γ`-conjugate by the whole trailing word `τ h`, with
      -- `τ = j₁.out ∈ Γ`. That word normalizes `Γ` — `τ` does because `Γ ≤ normalizer Γ`, and
      -- `h` by hypothesis — so conjugation by it may simply be undone.
      have hw : (j₁.out : G) * h ∈ Subgroup.normalizer (Γ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.le_normalizer j₁.out.2) hh
      refine (Subgroup.mem_normalizer_iff''.mp hw _).mpr ?_
      have hrw : ((j₁.out : G) * h)⁻¹ * (((i₁.out : G) * g)⁻¹ * ((i₂.out : G) * g)) *
            ((j₁.out : G) * h) =
          ((i₁.out : G) * g * ((j₁.out : G) * h))⁻¹ *
            ((i₂.out : G) * g * ((j₁.out : G) * h)) := by group
      rw [hrw]
      exact hq
    rfl
  exact Finite.card_le_one_iff_subsingleton.mpr hfib

end DoubleCoset

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G} {x y : Δ}

/-- **The double coset of a normalizing element is a single right coset**, `ΓxΓ = Γx`. -/
lemma toSet_mk_eq_rightCoset_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    (mk Γ Γ x).toSet = op (x : G) • (Γ : Set G) :=
  (toSet_mk x).trans (DoubleCoset.doubleCoset_eq_rightCoset_of_mem_normalizer hx)

/-- The same collapse read at the chosen representative of `HeckeCoset.mk Γ Γ x`, which is the
shape a decomposition of a double coset into right cosets is stated in. -/
lemma doubleCoset_out_mk_eq_rightCoset_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    DoubleCoset.doubleCoset (((mk Γ Γ x).out : Δ) : G) Γ Γ = op (x : G) • (Γ : Set G) :=
  (eq_iff.mp (Quotient.out_eq (mk Γ Γ x))).trans
    (DoubleCoset.doubleCoset_eq_rightCoset_of_mem_normalizer hx)

/-- The chosen representative of `HeckeCoset.mk Γ Γ x` lies in the right coset `Γx`. -/
lemma rep_mk_mem_rightCoset_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    (((mk Γ Γ x).rep : Δ) : G) ∈ op (x : G) • (Γ : Set G) :=
  toSet_mk_eq_rightCoset_of_mem_normalizer hx ▸ (mk Γ Γ x).rep_mem

/-- The chosen representative of `HeckeCoset.mk Γ Γ x` again normalizes `Γ`: it lies in `ΓxΓ`,
all of whose elements do. -/
lemma rep_mk_mem_normalizer_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    (((mk Γ Γ x).rep : Δ) : G) ∈ Subgroup.normalizer (Γ : Set G) :=
  DoubleCoset.mem_normalizer_of_mem_doubleCoset hx (toSet_mk x ▸ (mk Γ Γ x).rep_mem)

/-- **Every value of `HeckeCoset.mulMap` at a normalizing left factor is the double coset of
the product**, `Γ · xy · Γ` — so there is no structure constant to compute.

Only the **left** factor need normalize `Γ`. The right one is an arbitrary element of `Δ`,
which is what lets this compute a product against an arbitrary basis element rather than only
against another normalizing one. -/
lemma mulMap_rep_mk_eq_of_mem_normalizer [IsHeckeTriple Δ Γ Γ]
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G))
    (p : DecompQuotient Γ Γ (((mk Γ Γ x).rep : Δ) : G) ×
      DecompQuotient Γ Γ (((mk Γ Γ y).rep : Δ) : G)) :
    mulMap Γ Γ Γ (mk Γ Γ x).rep (mk Γ Γ y).rep p = mk Γ Γ (x * y) := by
  -- Name the representatives as `a x` (with `a ∈ Γ`) and `c y d` (with `c, d ∈ Γ`), so the
  -- identity below is between short words in eight atoms. The intervening `Γ` factors are then
  -- pushed across `x`, which is legitimate exactly because `x` normalizes `Γ`, leaving `Γ xy Γ`.
  obtain ⟨a, ha, hA⟩ : ∃ a ∈ Γ, (((mk Γ Γ x).rep : Δ) : G) = a * (x : G) :=
    ⟨_, (mem_rightCoset_iff _).mp (rep_mk_mem_rightCoset_of_mem_normalizer hx),
      (inv_mul_cancel_right _ _).symm⟩
  obtain ⟨c, hc', d, hd', hB⟩ :
      ∃ c ∈ Γ, ∃ d ∈ Γ, (((mk Γ Γ y).rep : Δ) : G) = c * (y : G) * d :=
    DoubleCoset.mem_doubleCoset.mp (toSet_mk y ▸ (mk Γ Γ y).rep_mem)
  -- the intervening `Γ` factor, conjugated across `x`
  have hc : (x : G) * ((p.2.out : G) * c) * (x : G)⁻¹ ∈ Γ :=
    (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mul_mem _ p.2.out.2 hc')
  -- the word identity, in eight free atoms: quantifying over `u` and `v` keeps `group` away
  -- from the coset representatives, whose types are large
  have key₀ : ∀ u v : G, u * (a * (x : G)) * (v * (c * (y : G) * d)) =
      u * a * ((x : G) * (v * c) * (x : G)⁻¹) * ((x : G) * (y : G)) * d := fun u v ↦ by group
  have key := key₀ (p.1.out : G) (p.2.out : G)
  rw [← hA, ← hB] at key
  exact mulMap_eq_of_eq_mul_mul (d := x * y)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ p.1.out.2 ha) hc) hd' key

/-- **Every value of `HeckeCoset.mulMap` at a normalizing right factor is the double coset of
the product** — the mirror of `mulMap_rep_mk_eq_of_mem_normalizer`, with the normalisation
hypothesis on the right factor instead of the left. -/
lemma mulMap_rep_mk_eq_of_mem_normalizer_right [IsHeckeTriple Δ Γ Γ]
    (hy : (y : G) ∈ Subgroup.normalizer (Γ : Set G))
    (p : DecompQuotient Γ Γ (((mk Γ Γ x).rep : Δ) : G) ×
      DecompQuotient Γ Γ (((mk Γ Γ y).rep : Δ) : G)) :
    mulMap Γ Γ Γ (mk Γ Γ x).rep (mk Γ Γ y).rep p = mk Γ Γ (x * y) := by
  obtain ⟨a, ha, b, hb, hA⟩ :
      ∃ a ∈ Γ, ∃ b ∈ Γ, (((mk Γ Γ x).rep : Δ) : G) = a * (x : G) * b :=
    DoubleCoset.mem_doubleCoset.mp (toSet_mk x ▸ (mk Γ Γ x).rep_mem)
  obtain ⟨c, hc, hB⟩ : ∃ c ∈ Γ, (((mk Γ Γ y).rep : Δ) : G) = c * (y : G) :=
    ⟨_, (mem_rightCoset_iff _).mp (rep_mk_mem_rightCoset_of_mem_normalizer hy),
      (inv_mul_cancel_right _ _).symm⟩
  -- Here the left representative is the arbitrary `a x b` and the right one is `c y`, so the
  -- intervening `Γ` factor is conjugated across `y` rather than across `x`.
  have hd : (y : G)⁻¹ * (b * ((p.2.out : G) * c)) * (y : G) ∈ Γ :=
    (Subgroup.mem_normalizer_iff''.mp hy _).mp
      (Subgroup.mul_mem _ hb (Subgroup.mul_mem _ p.2.out.2 hc))
  have key₀ : ∀ u v : G, u * (a * (x : G) * b) * (v * (c * (y : G))) =
      u * a * ((x : G) * (y : G)) * ((y : G)⁻¹ * (b * (v * c)) * (y : G)) := fun u v ↦ by group
  have key := key₀ (p.1.out : G) (p.2.out : G)
  rw [← hA, ← hB] at key
  exact mulMap_eq_of_eq_mul_mul (d := x * y)
    (Subgroup.mul_mem _ p.1.out.2 ha) hd key

end HeckeCoset

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G} {x y : Δ}

/-- **A normalizing basis element multiplies any other**, `[ΓxΓ] · [ΓyΓ] = [Γ(xy)Γ]`, over any
coefficient semiring, when `x` normalizes `Γ`. `y` is arbitrary.

There is no structure constant to compute: `x` normalizes `Γ`, so its decomposition quotient is
a subsingleton and `multiplicity ≤ 1` follows, and every pair of representatives multiplies into
the same double coset. Both facts need only `x`. -/
theorem single_mul_single_of_mem_normalizer [IsHeckeTriple Δ Γ Γ] (R : Type*) [Semiring R]
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    single R (HeckeCoset.mk Γ Γ x) 1 * single R (HeckeCoset.mk Γ Γ y) 1 =
      single R (HeckeCoset.mk Γ Γ (x * y)) 1 := by
  classical
  rw [mul_def]
  refine mul_single_single_of_mulMap_eq R _ _ _
    (HeckeCoset.mulMap_rep_mk_eq_of_mem_normalizer hx) ?_
  exact DoubleCoset.multiplicity_le_one_of_subsingleton
    (DoubleCoset.subsingleton_decompQuotient_of_mem_normalizer
      (HeckeCoset.rep_mk_mem_normalizer_of_mem_normalizer hx))

/-- **A normalizing basis element multiplies any other from the right**, `[ΓxΓ] · [ΓyΓ] =
[Γ(xy)Γ]`, when `y` normalizes `Γ`. `x` is arbitrary.

The mirror of `single_mul_single_of_mem_normalizer`. It is a separate proof rather than that
one applied backwards: `multiplicity Γ₁ Γ₂ Γ₃ g h d` quotients by `Γ₃` on the right only, so
the two sides are not interchangeable, and the bound used here is
`multiplicity_le_one_of_mem_normalizer_right`. -/
theorem single_mul_single_of_mem_normalizer_right [IsHeckeTriple Δ Γ Γ] (R : Type*) [Semiring R]
    (hy : (y : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    single R (HeckeCoset.mk Γ Γ x) 1 * single R (HeckeCoset.mk Γ Γ y) 1 =
      single R (HeckeCoset.mk Γ Γ (x * y)) 1 := by
  classical
  rw [mul_def]
  refine mul_single_single_of_mulMap_eq R _ _ _
    (HeckeCoset.mulMap_rep_mk_eq_of_mem_normalizer_right hy) ?_
  exact DoubleCoset.multiplicity_le_one_of_mem_normalizer_right
    (HeckeCoset.rep_mk_mem_normalizer_of_mem_normalizer hy)

/-- **A normalizing basis element commutes with another whenever the double cosets of their two
products agree**, `Γ(xy)Γ = Γ(yx)Γ`.

This is what having both handednesses buys: the left-handed lemma computes `[ΓxΓ] · [ΓyΓ]` and
the right-handed one computes `[ΓyΓ] · [ΓxΓ]`, both as basis elements, so a commutation
question in the Hecke ring is discharged by the single coset identity `Γ(xy)Γ = Γ(yx)Γ`. Neither
lemma alone suffices, since each constrains a different side.

Only this direction is claimed, and only `x` need normalize `Γ`; `y` is arbitrary. -/
theorem commute_single_of_mem_normalizer [IsHeckeTriple Δ Γ Γ] (R : Type*) [Semiring R]
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G))
    (hxy : HeckeCoset.mk Γ Γ (x * y) = HeckeCoset.mk Γ Γ (y * x)) :
    Commute (single R (HeckeCoset.mk Γ Γ x) 1) (single R (HeckeCoset.mk Γ Γ y) 1) := by
  rw [Commute, SemiconjBy, single_mul_single_of_mem_normalizer R hx,
    single_mul_single_of_mem_normalizer_right R hx, hxy]

end HeckeCosetModule

end
