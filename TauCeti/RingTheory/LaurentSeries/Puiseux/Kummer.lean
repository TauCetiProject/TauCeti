/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Twist
public import TauCeti.RingTheory.LaurentSeries.Level.Kummer
public import TauCeti.RingTheory.RootsOfUnity.TateModule

/-!
# The Kummer action of compatible roots of unity on Puiseux series

A point `ζ = (ζₙ)ₙ` of the Tate module `lim_n μₙ(K)` of the roots of unity of `K`, the compatible
families `ζₘ ^ (m / n) = ζₙ` for `n ∣ m`, acts on the Puiseux field by the `K⸨X⸩`-algebra
automorphism `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)`. Concretely the automorphism multiplies the
coefficient of `t ^ q` by `ζ_{q.den} ^ q.num`: it is the twist of rational Hahn series by the
character `TauCeti.PrimeToPTateModule.ratChar`, which preserves supports and is trivial on integer
exponents.

On the level-`n` subfield `K⸨t ^ (1 / n)⸩` this automorphism restricts to the Kummer automorphism
`t ^ (1 / n) ↦ ζₙ t ^ (1 / n)`, so the action assembles the finite-level Kummer actions of
`TauCeti.puiseuxField.levelKummer` compatibly with the transition maps. The action is faithful.
If every `ζₙ` is a primitive `n`-th root of unity, the series fixed by `ζ ^ n` are exactly those of
level `n`; in particular the series fixed by `ζ` are the Laurent series in `t`. When `K` is
algebraically closed of characteristic zero, these automorphisms are the candidates for the whole
absolute Galois group of `K⸨X⸩` acting on the Puiseux field; that identification is not proved
here.

The Tate module `lim_n μₙ(K)` is `TauCeti.PrimeToPTateModule 1 K`: every positive integer is prime
to `1`, so it is the inverse limit of all the finite groups `μₙ(K)` along the power maps, with the
inverse-limit topology of these discrete groups.

## Main definitions

* `TauCeti.puiseuxField.kummer K`: the action of `lim_n μₙ(K)` on the Puiseux field by
  `K⸨X⸩`-algebra automorphisms, `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)`.

## Main results

* `TauCeti.puiseuxField.coeff_kummer`: the automorphism attached to `ζ` multiplies the
  coefficient of `t ^ q` by the value of the character of `ζ` at `q`.
* `TauCeti.puiseuxField.coeff_kummer_intCast_div`: it multiplies the coefficient of `t ^ (k / n)`
  by `ζₙ ^ k`.
* `TauCeti.puiseuxField.kummer_coe_level`: on the level-`n` subfield it is the Kummer automorphism
  `TauCeti.puiseuxField.levelKummer` attached to `ζₙ`.
* `TauCeti.puiseuxField.kummer_injective`: the action is faithful.
* `TauCeti.puiseuxField.fixedField_zpowers_kummer_pow`: if every `ζₙ` is primitive, the fixed field
  of `ζ ^ n` is the level-`n` subfield.
* `TauCeti.puiseuxField.fixedField_zpowers_kummer`: if every `ζₙ` is primitive, the fixed field of
  `ζ` is `K⸨X⸩`.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries

namespace TauCeti.puiseuxField

open PrimeToPTateModule

variable (K : Type*) [Field K]

/-- Twisting by the character of a point of the Tate module preserves Puiseux series, since it
preserves supports. -/
private theorem twistEquiv_ratChar_mem (ζ : PrimeToPTateModule 1 K) {x : HahnSeries ℚ K}
    (hx : x ∈ puiseuxField K) : twistEquiv (ratChar K ζ) x ∈ puiseuxField K := by
  rw [mem_puiseuxField_iff_exists_den_dvd, support_twistEquiv]
  exact mem_puiseuxField_iff_exists_den_dvd.mp hx

/-- The twist by the character of `ζ`, as a `K⸨X⸩`-algebra endomorphism of the Puiseux field. It
fixes `K⸨X⸩` because the character is trivial on integer exponents. -/
private noncomputable def kummerAlgHom (ζ : PrimeToPTateModule 1 K) :
    puiseuxField K →ₐ[K⸨X⸩] puiseuxField K where
  toFun x := ⟨twistEquiv (ratChar K ζ) x, twistEquiv_ratChar_mem K ζ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' f := Subtype.ext <| HahnSeries.ext <| funext fun q ↦ by
    simp only [coeff_twistEquiv]
    rw [coe_algebraMap_laurentSeries]
    by_cases hq : q.den = 1
    · rw [← Rat.coe_int_num_of_den_eq_one hq, ratChar_ofAdd_intCast, Units.val_one, one_mul]
    · rw [coeff_ramifiedEmbedding_of_not_den_dvd 1 f (by simpa using hq), mul_zero]

variable {K} in
private theorem coe_kummerAlgHom_apply (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) :
    (kummerAlgHom K ζ x : HahnSeries ℚ K) = twistEquiv (ratChar K ζ) x :=
  rfl

/-- The **Kummer action** of the Tate module `lim_n μₙ(K)` on the Puiseux field: the point
`ζ = (ζₙ)ₙ` acts by the `K⸨X⸩`-algebra automorphism `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)`, which
multiplies the coefficient of `t ^ q` by `ζ_{q.den} ^ q.num`. -/
noncomputable def kummer : PrimeToPTateModule 1 K →* Gal(puiseuxField K/K⸨X⸩) :=
  (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp
    ({ toFun := kummerAlgHom K
       map_one' := AlgHom.ext fun x ↦ Subtype.ext <| HahnSeries.ext <| funext fun q ↦ by
         rw [coe_kummerAlgHom_apply, coeff_twistEquiv, map_one, MonoidHom.one_apply,
           Units.val_one, one_mul, AlgHom.one_apply]
       map_mul' ζ η := AlgHom.ext fun x ↦ Subtype.ext <| HahnSeries.ext <| funext fun q ↦ by
         rw [coe_kummerAlgHom_apply, AlgHom.mul_apply, coe_kummerAlgHom_apply, coeff_twistEquiv,
           coeff_twistEquiv, coe_kummerAlgHom_apply, coeff_twistEquiv, map_mul,
           MonoidHom.mul_apply, Units.val_mul, mul_assoc] } :
      PrimeToPTateModule 1 K →* (puiseuxField K →ₐ[K⸨X⸩] puiseuxField K)).toHomUnits

variable {K}

/-- As a Hahn series, the image of `x` under the automorphism attached to `ζ` is the twist of `x`
by the character of `ζ`. -/
theorem coe_kummer_apply (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) :
    (kummer K ζ x : HahnSeries ℚ K) = twistEquiv (ratChar K ζ) x :=
  (rfl)

/-- The automorphism attached to `ζ` multiplies the coefficient of `t ^ q` by the value of the
character of `ζ` at `q`, that is, by `ζ_{q.den} ^ q.num`. -/
@[simp]
theorem coeff_kummer (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) (q : ℚ) :
    (kummer K ζ x : HahnSeries ℚ K).coeff q =
      (ratChar K ζ (.ofAdd q) : K) * (x : HahnSeries ℚ K).coeff q := by
  rw [coe_kummer_apply, coeff_twistEquiv]

/-- The automorphism attached to `ζ` multiplies the coefficient of `t ^ (k / n)` by `ζₙ ^ k`. -/
theorem coeff_kummer_intCast_div (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) (n : ℕ+)
    (k : ℤ) :
    (kummer K ζ x : HahnSeries ℚ K).coeff ((k : ℚ) / n) =
      ((proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Kˣ) : K) ^ k *
        (x : HahnSeries ℚ K).coeff ((k : ℚ) / n) := by
  rw [coeff_kummer, ratChar_ofAdd_eq_zpow ζ ⟨n, n.ne_zero, Nat.coprime_one_right _⟩
    (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.ne_zero)).symm, Units.val_zpow_eq_zpow_val]

/-- The automorphism attached to `ζ` sends the monomial `a t ^ q` to `ζ_{q.den} ^ q.num a t ^ q`,
where `ζ_{q.den} ^ q.num` is the value of the character of `ζ` at `q`. -/
@[simp]
theorem kummer_single (ζ : PrimeToPTateModule 1 K) (q : ℚ) (a : K) :
    kummer K ζ (single K q a) = single K q ((ratChar K ζ (.ofAdd q) : K) * a) := by
  apply Subtype.ext
  rw [coe_kummer_apply, coe_single, coe_single, twistEquiv_apply, twist_single,
    MonoidHom.comp_apply, Units.coeHom_apply]

/-- **Compatibility with the finite levels.** On the level-`n` subfield `K⸨t ^ (1 / n)⸩`, the
automorphism attached to `ζ` is the Kummer automorphism `t ^ (1 / n) ↦ ζₙ t ^ (1 / n)`. -/
theorem kummer_coe_level (ζ : PrimeToPTateModule 1 K) {n : ℕ+} (x : level K n) :
    kummer K ζ (x : puiseuxField K) = levelKummer K n
      (proj (⟨n, n.ne_zero, Nat.coprime_one_right _⟩ : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) ζ) x := by
  refine Subtype.ext <| HahnSeries.ext <| funext fun q ↦ ?_
  by_cases hq : q.den ∣ n
  · obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hq
    rw [coeff_kummer_intCast_div, coeff_levelKummer]
  -- Away from the exponents `k / n`, both level-`n` series have vanishing coefficients.
  obtain ⟨f, hf⟩ : ∃ f, levelEmbedding K n f = x := (mem_level_iff K n x).mp x.2
  obtain ⟨g, hg⟩ : ∃ g, levelEmbedding K n g = levelKummer K n
      (proj (⟨n, n.ne_zero, Nat.coprime_one_right _⟩ : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) ζ) x :=
    (mem_level_iff K n _).mp (SetLike.coe_mem _)
  rw [coeff_kummer, ← hf, ← hg, coe_levelEmbedding, coe_levelEmbedding,
    coeff_ramifiedEmbedding_of_not_den_dvd n f hq, coeff_ramifiedEmbedding_of_not_den_dvd n g hq,
    mul_zero]

/-- **Faithfulness.** Distinct points of the Tate module act by distinct automorphisms of the
Puiseux field: the automorphism attached to `ζ` sends `t ^ (1 / n)` to `ζₙ t ^ (1 / n)`. -/
theorem kummer_injective : Function.Injective (kummer K) := by
  refine (injective_iff_map_eq_one _).2 fun ζ hζ ↦ ratChar_injective (E := K) ?_
  ext q
  have h := congrArg (fun x : puiseuxField K ↦ (x : HahnSeries ℚ K).coeff q)
    (AlgEquiv.ext_iff.mp hζ (single K q 1))
  simpa using h

/-- **Fixed fields.** If every component `ζₙ` of `ζ` is a primitive `n`-th root of unity, then the
Puiseux series fixed by `ζ ^ n` are exactly those of level `n`. -/
theorem fixedField_zpowers_kummer_pow {ζ : PrimeToPTateModule 1 K}
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj m ζ : Kˣ) m) (n : ℕ+) :
    IntermediateField.fixedField (Subgroup.zpowers (kummer K ζ ^ (n : ℕ))) = level K n := by
  set N : {m : ℕ // m ≠ 0 ∧ m.Coprime 1} := ⟨n, n.ne_zero, Nat.coprime_one_right _⟩
  apply le_antisymm
  · -- A fixed series has only exponents `q` with `ζ_{q.den} ^ (n * q.num) = 1`, so `q.den ∣ n`.
    intro x hx
    have hfix := (IntermediateField.mem_fixedField_iff _ x).mp hx _
      (Subgroup.mem_zpowers (kummer K ζ ^ (n : ℕ)))
    rw [mem_level_iff, mem_range_levelEmbedding_iff, mem_range_ramifiedEmbedding_iff]
    intro q hq
    have hcoeff := congrArg (fun y : puiseuxField K ↦ (y : HahnSeries ℚ K).coeff q) hfix
    simp only [← map_pow, coeff_kummer] at hcoeff
    have hχ : ratChar K ζ (.ofAdd ((n : ℕ) * q)) = 1 := by
      rw [← nsmul_eq_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, ← map_pow]
      exact Units.val_eq_one.mp (mul_eq_right₀ (mem_support _ _ |>.mp hq) |>.mp hcoeff)
    rw [ratChar_ofAdd_eq_one_iff hζ, Rat.den_eq_one_iff] at hχ
    exact (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mpr ⟨((n : ℕ) * q).num, by
      rw [hχ, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr n.ne_zero)]⟩
  · -- On level `n`, every power of `ζ ^ n` acts through `ζₙ ^ n = 1`.
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    rintro _ ⟨m, rfl⟩
    have h1 : proj N ((ζ ^ (n : ℕ)) ^ m) = 1 := by
      have hN : proj N ζ ^ (n : ℕ) = 1 := Subtype.ext <| by
        simpa using (mem_rootsOfUnity _ _).mp (proj N ζ).2
      rw [map_zpow, map_pow, hN, one_zpow]
    simp only
    rw [← map_pow, ← map_zpow, kummer_coe_level _ (⟨x, hx⟩ : level K n), h1, map_one,
      AlgEquiv.one_apply]

/-- If every component `ζₙ` of `ζ` is a primitive `n`-th root of unity, then the Puiseux series
fixed by `ζ` are exactly the Laurent series in `t`. -/
theorem fixedField_zpowers_kummer {ζ : PrimeToPTateModule 1 K}
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj m ζ : Kˣ) m) :
    IntermediateField.fixedField (Subgroup.zpowers (kummer K ζ)) = ⊥ := by
  simpa [level_one] using fixedField_zpowers_kummer_pow hζ 1

end TauCeti.puiseuxField
