/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CompletedGenericField.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom

import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Ideal.Maps

/-!
# Maps of completed generic fields and Frobenius lifts

Let `π ∈ A` and `π' ∈ B` generate prime ideals and let `f : A →+* B` be a ring homomorphism with
`f⁻¹ (π') = (π)`. Then `f` extends to the localizations at these primes and, being local there,
to their completions: this gives a local homomorphism of completed generic rings
`completedGenericIntegersMap f hf`, the unique local homomorphism extending `f`. When `f π` stays
nonzero in the completion of `B`, the map is injective and extends to the completed generic
fields; when `f π` is associated to `π'`, the extension preserves the normalized valuations. If
moreover `A ⧸ (π) → B ⧸ (π')` is surjective, then the map of completed generic rings is
bijective.

The main example is a Frobenius lift. If `φ` is an endomorphism of `A` congruent modulo `π` to
`a ↦ a ^ q` with `q ≠ 0`, then `φ⁻¹ (π) = (π)` automatically
(`Ideal.comap_eq_self_of_forall_sub_pow_mem`), and its extension to the completed generic ring
is again congruent modulo `π` to `x ↦ x ^ q`, so it induces the `q`-power map on the residue field
`Frac (A ⧸ π)`. If moreover `φ π` is associated to `π`, as for a lift of an isometric Frobenius of
the coefficients, then `φ` extends to an isometric endomorphism of the completed generic field.
This applies, for instance, to the affine line `A = W(k)[t]` with `π = p` and the Frobenius lift
`t ↦ t ^ p` over the Witt-vector Frobenius, whose completed generic field is the generic field of
the affine line.

## Main definitions and results

* `completedGenericIntegersMap`: the local homomorphism of completed generic rings induced by `f`,
  with `completedGenericIntegersMap_algebraMap`, its uniqueness
  `completedGenericIntegersMap_unique`, and the functoriality laws
  `completedGenericIntegersMap_id` and `completedGenericIntegersMap_comp`.
* `completedGenericIntegersMap_injective`: injectivity when the image of `f π` is nonzero.
* `completedGenericIntegersMap_surjective` and `completedGenericIntegersMap_bijective`:
  surjectivity and bijectivity when `f π` is associated to `π'` and `A ⧸ (π) → B ⧸ (π')` is
  surjective.
* `completedGenericFieldMap`: the induced homomorphism of completed generic fields, with
  `valuation_completedGenericFieldMap` (it preserves valuations when `f π` is associated to `π'`).
* `completedGenericIntegersMap_sub_pow_mem` and `residue_completedGenericIntegersMap`: the
  extension of a `q`-Frobenius lift is a `q`-Frobenius lift.

## References

* [N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*](https://arxiv.org/abs/1910.03871v3),
  §3.1.
* [M. D'Addezio, *Parabolicity conjecture of F-isocrystals*](https://arxiv.org/abs/2012.12879v4),
  §4.2.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] {π : A} {π' : B} {π'' : C}
  [(Ideal.span {π}).IsPrime] [(Ideal.span {π'}).IsPrime] [(Ideal.span {π''}).IsPrime]

/-- Elements of `A` congruent modulo `π` have the same residue in the generic local ring. -/
private theorem residue_algebraMap_eq_of_sub_mem {a₁ a₂ : A} (h : a₁ - a₂ ∈ Ideal.span {π}) :
    residue (genericLocalRing π) (algebraMap A _ a₁) =
      residue (genericLocalRing π) (algebraMap A _ a₂) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ h

/-- An element of `A` outside `(π)` has nonzero residue in the generic local ring. -/
private theorem residue_algebraMap_ne_zero (s : (Ideal.span {π}).primeCompl) :
    residue (genericLocalRing π) (algebraMap A _ s) ≠ 0 := fun h ↦
  (mem_maximalIdeal _).mp ((residue_eq_zero_iff _).mp h) (IsLocalization.map_units _ s)

section Integers

variable (f : A →+* B) (hf : (Ideal.span {π'}).comap f = Ideal.span {π})

/-- The map of generic local rings induced by `f`, as a `ℤ`-algebra homomorphism for the
`ℤ`-algebra structures of the localizations. -/
private noncomputable def localRingHomₐ : genericLocalRing π →ₐ[ℤ] genericLocalRing π' :=
  { Localization.localRingHom _ _ f hf.symm with commutes' := fun r ↦ by simp }

private theorem le_comap_maximalIdeal_localRingHomₐ :
    maximalIdeal (genericLocalRing π) ≤
      (maximalIdeal (genericLocalRing π')).comap (localRingHomₐ f hf) :=
  (IsLocalRing.maximalIdeal_comap (Localization.localRingHom _ _ f hf.symm)).ge

/-- A ring homomorphism `f : A →+* B` with `f⁻¹ (π') = (π)` induces a homomorphism of completed
generic rings: it extends `f` to the localizations at `(π)` and `(π')`, then to their completions
along the maximal ideals. -/
noncomputable def completedGenericIntegersMap :
    completedGenericIntegers π →+* completedGenericIntegers π' :=
  (_root_.AdicCompletion.mapₐ (localRingHomₐ f hf)
    (le_comap_maximalIdeal_localRingHomₐ f hf)).toRingHom

/-- The map of completed generic rings extends the map of generic local rings. -/
@[simp]
theorem completedGenericIntegersMap_algebraMap_genericLocalRing (x : genericLocalRing π) :
    completedGenericIntegersMap f hf (algebraMap (genericLocalRing π) _ x) =
      algebraMap (genericLocalRing π') _ (Localization.localRingHom _ _ f hf.symm x) := by
  simp [completedGenericIntegersMap, localRingHomₐ, _root_.AdicCompletion.algebraMap_apply]

/-- The map of completed generic rings extends `f`. -/
@[simp]
theorem completedGenericIntegersMap_algebraMap (a : A) :
    completedGenericIntegersMap f hf (algebraMap A _ a) = algebraMap B _ (f a) := by
  rw [IsScalarTower.algebraMap_apply A (genericLocalRing π),
    completedGenericIntegersMap_algebraMap_genericLocalRing, Localization.localRingHom_to_map,
    ← IsScalarTower.algebraMap_apply]

/-- The map of completed generic rings is local. -/
instance : IsLocalHom (completedGenericIntegersMap f hf) := by
  refine ((local_hom_tfae _).out 4 1).mp ?_
  rw [maximalIdeal_completedGenericIntegers, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
    completedGenericIntegersMap_algebraMap, maximalIdeal_completedGenericIntegers]
  have hfπ : f π ∈ Ideal.span {π'} := by
    rw [← Ideal.mem_comap, hf]
    exact Ideal.mem_span_singleton_self π
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hfπ
  rw [← hb, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **Uniqueness of the extension.** A local homomorphism of completed generic rings extending `f`
is `completedGenericIntegersMap f hf`. -/
theorem completedGenericIntegersMap_unique
    (g : completedGenericIntegers π →+* completedGenericIntegers π') [IsLocalHom g]
    (hg : ∀ a, g (algebraMap A _ a) = algebraMap B _ (f a)) :
    g = completedGenericIntegersMap f hf := by
  have := isAdicComplete_completedGenericIntegers π'
  have hle (h : completedGenericIntegers π →+* completedGenericIntegers π') [IsLocalHom h] :
      (maximalIdeal (genericLocalRing π)).map (algebraMap _ (completedGenericIntegers π)) ≤
        (Ideal.span {algebraMap B (completedGenericIntegers π') π'}).comap h := by
    rw [← maximalIdeal_completedGenericIntegers, IsLocalRing.maximalIdeal_comap]
    exact IsLocalRing.map_maximalIdeal_le _
  refine _root_.AdicCompletion.ringHom_ext (fg_maximalIdeal_genericLocalRing π) (hle g)
    (hle _) (IsLocalization.ringHom_ext (Ideal.span {π}).primeCompl (RingHom.ext fun a ↦ ?_))
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hg,
    completedGenericIntegersMap_algebraMap]

/-- The identity of `A` induces the identity of the completed generic ring. -/
@[simp]
theorem completedGenericIntegersMap_id :
    completedGenericIntegersMap (RingHom.id A) (Ideal.comap_id _) =
      RingHom.id (completedGenericIntegers π) :=
  (completedGenericIntegersMap_unique _ _ _ fun _ ↦ by rw [RingHom.id_apply, RingHom.id_apply]).symm

/-- The map of completed generic rings induced by a composite is the composite of the induced
maps. -/
theorem completedGenericIntegersMap_comp (g : B →+* C)
    (hg : (Ideal.span {π''}).comap g = Ideal.span {π'}) :
    completedGenericIntegersMap (g.comp f) (by rw [← Ideal.comap_comap, hg, hf]) =
      (completedGenericIntegersMap g hg).comp (completedGenericIntegersMap f hf) :=
  (completedGenericIntegersMap_unique _ _ _ fun a ↦ by simp).symm

/-- If `f` induces a surjection `A ⧸ (π) → B ⧸ (π')`, then every element of the completed generic
ring of `B` is congruent modulo its maximal ideal to the image of an element of the completed
generic ring of `A`. -/
private theorem exists_sub_completedGenericIntegersMap_mem
    (hsurj : Function.Surjective (Ideal.quotientMap (Ideal.span {π'}) f hf.ge))
    (t : completedGenericIntegers π') :
    ∃ x, t - completedGenericIntegersMap f hf x ∈ maximalIdeal (completedGenericIntegers π') := by
  -- `t` is congruent to the image of `b / s` with `b, s ∈ B` and `s ∉ (π')`
  obtain ⟨y, hy⟩ := _root_.AdicCompletion.exists_sub_algebraMap_mem_map_pow
    (fg_maximalIdeal_genericLocalRing π') 1 t
  rw [pow_one, ← _root_.AdicCompletion.maximalIdeal_eq_map_of_fg
    (fg_maximalIdeal_genericLocalRing π')] at hy
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Ideal.span {π'}).primeCompl y
  have hlift (b : B) : ∃ a, f a - b ∈ Ideal.span {π'} := by
    obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨a, Ideal.Quotient.eq.mp (by simpa using ha)⟩
  -- lift `b` and `s` modulo `π'` to `f a` and `f c`
  obtain ⟨a, ha⟩ := hlift b
  obtain ⟨c, hc⟩ := hlift s
  have hc' : c ∈ (Ideal.span {π}).primeCompl := fun h ↦
    s.property (by simpa using sub_mem (Ideal.mem_comap.mp (hf.ge h)) hc)
  refine ⟨algebraMap _ _ (IsLocalization.mk' (genericLocalRing π) a ⟨c, hc'⟩), ?_⟩
  rw [completedGenericIntegersMap_algebraMap_genericLocalRing, ← sub_add_sub_cancel _
    (algebraMap _ _ (IsLocalization.mk' (genericLocalRing π') b s)), ← map_sub]
  refine add_mem hy (map_nonunit _ _ ?_)
  -- the two fractions have the same residue
  have hy₁ := congrArg (Localization.localRingHom _ _ f hf.symm)
    (IsLocalization.mk'_spec (genericLocalRing π) a ⟨c, hc'⟩)
  rw [map_mul, Localization.localRingHom_to_map, Localization.localRingHom_to_map] at hy₁
  have hy₂ := IsLocalization.mk'_spec (genericLocalRing π') b s
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  apply mul_right_cancel₀ (residue_algebraMap_ne_zero s)
  rw [← map_mul, hy₂, ← residue_algebraMap_eq_of_sub_mem hc, ← map_mul, hy₁,
    residue_algebraMap_eq_of_sub_mem ha]

/-- **Surjectivity criterion.** If `f π` is associated to `π'` and `f` induces a surjection
`A ⧸ (π) → B ⧸ (π')`, then the map of completed generic rings is surjective. -/
theorem completedGenericIntegersMap_surjective (hfπ : Associated (f π) π')
    (hsurj : Function.Surjective (Ideal.quotientMap (Ideal.span {π'}) f hf.ge)) :
    Function.Surjective (completedGenericIntegersMap f hf) := by
  have := isAdicComplete_completedGenericIntegers π
  have := isAdicComplete_completedGenericIntegers π'
  obtain ⟨u, hu⟩ := hfπ
  have hu' : algebraMap B (completedGenericIntegers π') π' =
      algebraMap B _ (f π) * algebraMap B _ u := by
    rw [← map_mul, hu]
  have hmap : (Ideal.span {algebraMap A (completedGenericIntegers π) π}).map
      (completedGenericIntegersMap f hf) = Ideal.span {algebraMap B _ π'} := by
    rw [Ideal.map_span, Set.image_singleton, completedGenericIntegersMap_algebraMap, hu',
      Ideal.span_singleton_mul_right_unit (u.isUnit.map _)]
  have : IsHausdorff ((Ideal.span {algebraMap A (completedGenericIntegers π) π}).map
      (completedGenericIntegersMap f hf)) (completedGenericIntegers π') := hmap ▸ inferInstance
  refine surjective_of_mk_map_comp_surjective
    (I := Ideal.span {algebraMap A (completedGenericIntegers π) π}) _ fun t ↦ ?_
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨x, hx⟩ := exists_sub_completedGenericIntegersMap_mem f hf hsurj t
  refine ⟨x, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, hmap, ← maximalIdeal_completedGenericIntegers,
    ← neg_mem_iff, neg_sub]
  exact hx

end Integers

section Field

open scoped WithZero

variable [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B)
  (hf : (Ideal.span {π'}).comap f = Ideal.span {π})

/-- The map of completed generic rings is injective as soon as the image of `f π` in the
completed generic ring of `B` is nonzero. -/
theorem completedGenericIntegersMap_injective (hπ : π ∈ nonZeroDivisors A)
    (hπ' : π' ∈ nonZeroDivisors B)
    (hfπ : algebraMap B (completedGenericIntegers π') (f π) ≠ 0) :
    Function.Injective (completedGenericIntegersMap f hf) := by
  let := isRegularLocalRing_completedGenericIntegers π hπ
  let := isDiscreteValuationRing_completedGenericIntegers π hπ
  let := isRegularLocalRing_completedGenericIntegers π' hπ'
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ by_contra fun hx0 ↦ ?_
  -- write `x = u * π ^ n` with `u` a unit
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0
    (irreducible_completedGenericIntegers π hπ)
  rw [map_mul, map_pow, completedGenericIntegersMap_algebraMap] at hx
  exact mul_ne_zero ((u.map (completedGenericIntegersMap f hf).toMonoidHom).ne_zero)
    (pow_ne_zero n hfπ) hx

omit [(Ideal.span {π}).IsPrime] [IsNoetherianRing A] in
/-- If `f π` is associated to `π'`, its image in the completed generic ring of `B` is nonzero. -/
theorem algebraMap_apply_ne_zero_of_associated (hπ' : π' ∈ nonZeroDivisors B)
    (hfπ : Associated (f π) π') :
    algebraMap B (completedGenericIntegers π') (f π) ≠ 0 := by
  let := isRegularLocalRing_completedGenericIntegers π' hπ'
  exact (Associated.ne_zero_iff (hfπ.map (algebraMap B _))).mpr
    (irreducible_completedGenericIntegers π' hπ').ne_zero

/-- **Bijectivity criterion.** If `f π` is associated to `π'` and `f` induces a surjection
`A ⧸ (π) → B ⧸ (π')`, then the map of completed generic rings is bijective. -/
theorem completedGenericIntegersMap_bijective (hπ : π ∈ nonZeroDivisors A)
    (hπ' : π' ∈ nonZeroDivisors B) (hfπ : Associated (f π) π')
    (hsurj : Function.Surjective (Ideal.quotientMap (Ideal.span {π'}) f hf.ge)) :
    Function.Bijective (completedGenericIntegersMap f hf) :=
  ⟨completedGenericIntegersMap_injective f hf hπ hπ'
      (algebraMap_apply_ne_zero_of_associated f hπ' hfπ),
    completedGenericIntegersMap_surjective f hf hfπ hsurj⟩

variable (hπ : π ∈ nonZeroDivisors A) (hπ' : π' ∈ nonZeroDivisors B)

/-- An injective map of completed generic rings induces a homomorphism of completed generic
fields. -/
noncomputable def completedGenericFieldMap
    (hinj : Function.Injective (completedGenericIntegersMap f hf)) :
    completedGenericField π hπ →+* completedGenericField π' hπ' :=
  let := isRegularLocalRing_completedGenericIntegers π' hπ'
  IsFractionRing.map hinj

variable (hinj : Function.Injective (completedGenericIntegersMap f hf))

/-- The map of completed generic fields extends the map of completed generic rings. -/
@[simp]
theorem completedGenericFieldMap_algebraMap (x : completedGenericIntegers π) :
    completedGenericFieldMap f hf hπ hπ' hinj (algebraMap _ _ x) =
      algebraMap _ _ (completedGenericIntegersMap f hf x) := by
  let := isRegularLocalRing_completedGenericIntegers π' hπ'
  exact IsLocalization.map_eq (S := completedGenericField π hπ) (Q := completedGenericField π' hπ')
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) x

/-- The map of completed generic fields extends `f`. -/
@[simp]
theorem completedGenericFieldMap_algebraMap_apply (a : A) :
    completedGenericFieldMap f hf hπ hπ' hinj (algebraMap A _ a) = algebraMap B _ (f a) := by
  rw [IsScalarTower.algebraMap_apply A (completedGenericIntegers π),
    completedGenericFieldMap_algebraMap, completedGenericIntegersMap_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- On the image of the completed generic ring, the map of completed generic fields preserves
valuations when `f π` is associated to `π'`. -/
private theorem valuation_completedGenericFieldMap_algebraMap (hfπ : Associated (f π) π')
    (x : completedGenericIntegers π) :
    Valued.v (completedGenericFieldMap f hf hπ hπ' hinj (algebraMap _ _ x)) =
      Valued.v (algebraMap _ (completedGenericField π hπ) x) := by
  let := isRegularLocalRing_completedGenericIntegers π hπ
  let := isDiscreteValuationRing_completedGenericIntegers π hπ
  let := isRegularLocalRing_completedGenericIntegers π' hπ'
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0
    (irreducible_completedGenericIntegers π hπ)
  obtain ⟨c, hc⟩ := hfπ
  have hc' : algebraMap B (completedGenericIntegers π') π' =
      algebraMap B _ (f π) * algebraMap B _ c := by
    rw [← map_mul, hc]
  -- the image of `π` has valuation one, since it differs from `π'` by a unit
  have hfπv : Valued.v (algebraMap _ (completedGenericField π' hπ')
      (algebraMap B (completedGenericIntegers π') (f π))) = WithZero.exp (-1 : ℤ) := by
    have h := valuation_completedGenericField_algebraMap π' hπ'
    rwa [IsScalarTower.algebraMap_apply B (completedGenericIntegers π'), hc', map_mul, map_mul,
      (completedGenericField_integers π' hπ').one_of_isUnit (c.isUnit.map _), mul_one] at h
  simp only [completedGenericFieldMap_algebraMap, map_mul, map_pow,
    completedGenericIntegersMap_algebraMap]
  rw [(completedGenericField_integers π' hπ').one_of_isUnit (u.isUnit.map _),
    (completedGenericField_integers π hπ).one_of_isUnit u.isUnit, hfπv,
    ← IsScalarTower.algebraMap_apply, valuation_completedGenericField_algebraMap]

/-- If `f π` is associated to `π'`, the map of completed generic fields preserves the normalized
valuations, so it is an isometric embedding for these valuations. -/
theorem valuation_completedGenericFieldMap (hfπ : Associated (f π) π')
    (x : completedGenericField π hπ) :
    Valued.v (completedGenericFieldMap f hf hπ hπ' hinj x) = Valued.v x := by
  let := isRegularLocalRing_completedGenericIntegers π hπ
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := completedGenericIntegers π) x
  rw [map_div₀, map_div₀, map_div₀,
    valuation_completedGenericFieldMap_algebraMap f hf hπ hπ' hinj hfπ,
    valuation_completedGenericFieldMap_algebraMap f hf hπ hπ' hinj hfπ]

end Field

section Frobenius

variable {q : ℕ} (φ : A →+* A) (hφ : ∀ a, φ a - a ^ q ∈ Ideal.span {π})

variable (hf : (Ideal.span {π}).comap φ = Ideal.span {π})

include hφ in
/-- The extension of `φ` to the generic local ring is congruent to `x ↦ x ^ q` modulo the maximal
ideal. -/
private theorem localRingHom_sub_pow_mem (x : genericLocalRing π) :
    Localization.localRingHom _ _ φ hf.symm x - x ^ q ∈ maximalIdeal (genericLocalRing π) := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Ideal.span {π}).primeCompl x
  have hy := IsLocalization.mk'_spec (genericLocalRing π) a s
  have hφy := congrArg (Localization.localRingHom _ _ φ hf.symm) hy
  rw [map_mul, Localization.localRingHom_to_map, Localization.localRingHom_to_map] at hφy
  -- in the residue field, `φ` acts on `a` and on `s` as the `q`-th power
  have hres (b : A) : residue (genericLocalRing π) (algebraMap A _ (φ b)) =
      residue (genericLocalRing π) (algebraMap A _ b) ^ q := by
    rw [residue_algebraMap_eq_of_sub_mem (hφ b), map_pow, map_pow]
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  apply mul_right_cancel₀ (pow_ne_zero q (residue_algebraMap_ne_zero s))
  rw [← hres s, ← map_mul, hφy, hres a, hres s, ← hy, map_mul, mul_pow, map_pow]

include hφ in
/-- **The extension of a Frobenius lift is a Frobenius lift.** If `φ` is congruent modulo `π` to
`a ↦ a ^ q`, then its extension to the completed generic ring is congruent modulo `π` to
`x ↦ x ^ q`. -/
theorem completedGenericIntegersMap_sub_pow_mem (x : completedGenericIntegers π) :
    completedGenericIntegersMap φ hf x - x ^ q ∈
      Ideal.span {algebraMap A (completedGenericIntegers π) π} := by
  rw [← maximalIdeal_completedGenericIntegers, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
  -- reduce to the image of an element of the generic local ring, which has the same residue
  obtain ⟨y, hy⟩ := _root_.AdicCompletion.exists_sub_algebraMap_mem_map_pow
    (fg_maximalIdeal_genericLocalRing π) 1 x
  rw [pow_one, ← _root_.AdicCompletion.maximalIdeal_eq_map_of_fg
    (fg_maximalIdeal_genericLocalRing π), ← residue_eq_zero_iff, map_sub, sub_eq_zero] at hy
  have hg : residue _ (completedGenericIntegersMap φ hf x) =
      residue _ (completedGenericIntegersMap φ hf (algebraMap _ _ y)) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff]
    exact map_nonunit _ _ ((residue_eq_zero_iff _).mp (by rw [map_sub, hy, sub_self]))
  rw [hg, map_pow, hy, completedGenericIntegersMap_algebraMap_genericLocalRing, ← map_pow,
    ← map_pow, ← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff]
  exact map_nonunit _ _ (localRingHom_sub_pow_mem φ hφ hf y)

include hφ in
/-- The extension of a `q`-Frobenius lift induces the `q`-power map on the residue field of the
completed generic ring. -/
theorem residue_completedGenericIntegersMap (x : completedGenericIntegers π) :
    residue _ (completedGenericIntegersMap φ hf x) = residue _ x ^ q := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    maximalIdeal_completedGenericIntegers]
  exact completedGenericIntegersMap_sub_pow_mem φ hφ hf x

end Frobenius

end TauCeti.AdicCompletion
