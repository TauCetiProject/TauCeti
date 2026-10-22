/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Map
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing

/-!
# Functoriality of Novikov rings

Let `N : H →+ ℝ` and `N' : H' →+ ℝ` be period homomorphisms and `φ : H →+ H'` a homomorphism of
exponent groups rescaling periods by a positive constant, `N' (φ h) = c * N h` with `c > 0`. The
pushforward `TauCeti.NovikovSeries.map ρ φ hφ` of `TauCeti.RingTheory.NovikovSeries.Map` sums the
coefficients of a Novikov series along the fibres of `φ` after applying the coefficient map `ρ`.

When `ρ` is multiplicative, so is the pushforward: the coefficient of `map (a * b)` at `h'` and that
of `map a * map b` are both the finite sum of `ρ (a.coeff u) * ρ (b.coeff v)` over the pairs of
support exponents with `φ u + φ v = h'` (`TauCeti.NovikovSeries.finite_setOf_map_add_eq`). For a
unital ring homomorphism `ρ : R →+* S` this gives the unital ring homomorphism
`P_(ρ,φ) : Nov(R, H, N) →+* Nov(S, H', N')`, which sends the monomial `r e^g` to `ρ r e^(φ g)`
(`TauCeti.NovikovSeries.map_single`). It satisfies the identity and composition laws, and for an
algebra homomorphism `ρ` it is an algebra homomorphism. No finiteness of the kernel of `φ` and no
injectivity of the period maps is needed.

The pushforward moves the period neighbourhood `U_C` into `U'_(c * C)`, so it is continuous for the
period topologies. Since `c > 0`, it preserves nonnegative and strictly positive supports, and it
restricts to a ring homomorphism of the nonnegative subrings which maps the positive ideal into the
positive ideal. Applied to the inclusion of a finite-index subgroup of exponents, these maps
compare the Novikov rings of a finite cyclic covering and of its base.

## Main definitions

* `TauCeti.NovikovSeries.mapRingHom`: the pushforward `P_(ρ,φ)` along a ring homomorphism of
  coefficients, as a ring homomorphism.
* `TauCeti.NovikovSeries.mapAlgHom`: the pushforward along an algebra homomorphism of
  coefficients, as an algebra homomorphism.
* `TauCeti.NovikovSeries.mapNonnegSubring`: the restriction of `mapRingHom` to the nonnegative
  subrings.

## Main results

* `TauCeti.NovikovSeries.map_mul`: the pushforward along a multiplicative coefficient map is
  multiplicative.
* `TauCeti.NovikovSeries.mapRingHom_id` and `TauCeti.NovikovSeries.mapRingHom_comp`: the
  identity and composition laws.
* `TauCeti.NovikovSeries.map_mem_periodFiltration`: the pushforward sends `U_C` into `U'_(c * C)`.
* `TauCeti.NovikovSeries.continuous_map` and `TauCeti.NovikovSeries.continuous_mapRingHom`: the
  pushforward is continuous for the period topologies.
* `TauCeti.NovikovSeries.mapNonnegSubring_mem_posIdeal`: the pushforward maps the positive ideal
  into the positive ideal.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace NovikovSeries

variable {R S T H H' H'' : Type*}

section Mul

variable [AddZeroClass H] [AddZeroClass H'] {N : H →+ ℝ} {N' : H' →+ ℝ}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {F : Type*} [FunLike F R S]
  [NonUnitalRingHomClass F R S] (ρ : F) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)

/-- The coefficient of `map ρ φ hφ (a * b)` at `h'` is the sum of `ρ (a.coeff u) * ρ (b.coeff v)`
over the pairs of support exponents with `φ u + φ v = h'`. -/
private theorem coeff_map_mul_eq_sum (a b : NovikovSeries R H N) (h' : H') :
    (map (ρ : R →+ S) φ hφ (a * b)).coeff h' =
      ∑ p ∈ (finite_setOf_map_add_eq a b hφ h').toFinset, ρ (a.coeff p.1) * ρ (b.coeff p.2) := by
  classical
  set T := (finite_setOf_map_add_eq a b hφ h').toFinset
  have hT (p : H × H) : p ∈ T ↔ φ p.1 + φ p.2 = h' ∧ a.coeff p.1 ≠ 0 ∧ b.coeff p.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  -- Group the pairs `(u, v)` by their sum `u + v`, the exponent of the product.
  rw [coeff_map_eq_sum _ φ hφ _ (T.image fun p => p.1 + p.2) ?_ ?_,
    ← sum_fiberwise_of_maps_to (s := T) (g := fun p : H × H => p.1 + p.2)
      fun p hp => mem_image_of_mem _ hp]
  · refine sum_congr rfl fun h hh => ?_
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.1 hh
    rw [coeff_mul_eq_sum (s := T.filter fun p => p.1 + p.2 = p₀.1 + p₀.2)
      (fun p hp => (mem_filter.1 hp).2) fun u v huv hu hv => mem_filter.2
        ⟨(hT _).2 ⟨by rw [← map_add, huv, map_add]; exact ((hT p₀).1 hp₀).1, hu, hv⟩, huv⟩,
      AddMonoidHom.coe_ofClass, map_sum]
    exact sum_congr rfl fun p _ => map_mul ρ _ _
  · rintro h ⟨hh, rfl : φ h = h'⟩
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_add_eq_of_coeff_mul_ne_zero (mem_support.1 hh)
    exact mem_image.2 ⟨(u, v), (hT _).2 ⟨(map_add φ u v).symm, hu, hv⟩, rfl⟩
  · intro h hh
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hh
    rw [map_add]
    exact ((hT p).1 hp).1

/-- The coefficient of `map ρ φ hφ a * map ρ φ hφ b` at `h'` is the sum of
`ρ (a.coeff u) * ρ (b.coeff v)` over the pairs of support exponents with `φ u + φ v = h'`. -/
private theorem coeff_mul_map_eq_sum (a b : NovikovSeries R H N)
    (h' : H') :
    (map (ρ : R →+ S) φ hφ a * map (ρ : R →+ S) φ hφ b).coeff h' =
      ∑ p ∈ (finite_setOf_map_add_eq a b hφ h').toFinset, ρ (a.coeff p.1) * ρ (b.coeff p.2) := by
  classical
  set T := (finite_setOf_map_add_eq a b hφ h').toFinset
  have hT (p : H × H) : p ∈ T ↔ φ p.1 + φ p.2 = h' ∧ a.coeff p.1 ≠ 0 ∧ b.coeff p.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  -- Group the pairs `(u, v)` by their image `(φ u, φ v)`, a pair of exponents of the factors.
  rw [coeff_mul_eq_sum (s := T.image fun p => (φ p.1, φ p.2)) ?_ ?_,
    ← sum_fiberwise_of_maps_to (s := T) (g := fun p : H × H => (φ p.1, φ p.2))
      fun p hp => mem_image_of_mem _ hp]
  · refine sum_congr rfl fun q hq => ?_
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.1 hq
    obtain ⟨hp₀h', ha₀, hb₀⟩ := (hT p₀).1 hp₀
    -- Each factor's coefficient is a sum over one coordinate of the fibre through `p₀`.
    rw [coeff_map_eq_sum _ φ hφ a ((T.image Prod.fst).filter fun u => φ u = φ p₀.1)
        (fun u hu => mem_filter.2 ⟨mem_image.2 ⟨(u, p₀.2),
          (hT _).2 ⟨by rw [hu.2]; exact hp₀h', mem_support.1 hu.1, hb₀⟩, rfl⟩, hu.2⟩)
        fun u hu => (mem_filter.1 hu).2,
      coeff_map_eq_sum _ φ hφ b ((T.image Prod.snd).filter fun v => φ v = φ p₀.2)
        (fun v hv => mem_filter.2 ⟨mem_image.2 ⟨(p₀.1, v),
          (hT _).2 ⟨by rw [hv.2]; exact hp₀h', ha₀, mem_support.1 hv.1⟩, rfl⟩, hv.2⟩)
        fun v hv => (mem_filter.1 hv).2,
      sum_mul_sum, ← sum_product']
    refine sum_congr (Finset.ext fun p => ?_) fun _ _ => by simp only [AddMonoidHom.coe_ofClass]
    simp only [mem_product, mem_filter, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨p₁, hp₁, h₁⟩, hu⟩, ⟨p₂, hp₂, h₂⟩, hv⟩
      exact ⟨(hT _).2 ⟨by rw [hu, hv]; exact hp₀h', h₁ ▸ ((hT p₁).1 hp₁).2.1,
        h₂ ▸ ((hT p₂).1 hp₂).2.2⟩, hu, hv⟩
    · rintro ⟨hp, hu, hv⟩
      exact ⟨⟨⟨p, hp, rfl⟩, hu⟩, ⟨p, hp, rfl⟩, hv⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    exact ((hT p).1 hp).1
  · intro u' v' huv hu hv
    obtain ⟨u, hua, rfl⟩ := support_map_subset _ φ hφ a (mem_support.2 hu)
    obtain ⟨v, hvb, rfl⟩ := support_map_subset _ φ hφ b (mem_support.2 hv)
    exact mem_image.2 ⟨(u, v), (hT _).2 ⟨huv, mem_support.1 hua, mem_support.1 hvb⟩, rfl⟩

/-- The pushforward along a multiplicative coefficient map is multiplicative. -/
theorem map_mul (a b : NovikovSeries R H N) :
    map (ρ : R →+ S) φ hφ (a * b) = map (ρ : R →+ S) φ hφ a * map (ρ : R →+ S) φ hφ b := by
  classical
  ext h'
  rw [coeff_map_mul_eq_sum, coeff_mul_map_eq_sum]

end Mul

section RingHom

variable [AddMonoid H] [AddMonoid H'] [AddMonoid H''] {N : H →+ ℝ} {N' : H' →+ ℝ}
  {N'' : H'' →+ ℝ} [Semiring R] [Semiring S] [Semiring T]

/-- The pushforward `P_(ρ,φ)` of Novikov series along a ring homomorphism `ρ` of coefficients and
an exponent homomorphism `φ` rescaling periods by a positive constant, as a ring homomorphism: the
coefficient at `h'` is the sum of the images under `ρ` of the coefficients at the exponents `h`
with `φ h = h'`. -/
def mapRingHom (ρ : R →+* S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) :
    NovikovSeries R H N →+* NovikovSeries S H' N' where
  __ := map (ρ : R →+ S) φ hφ
  map_one' := by
    rw [AddMonoidHom.toFun_eq_coe, one_def, map_single]
    simp
  map_mul' := map_mul ρ φ hφ

variable (ρ : R →+* S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)

@[simp]
theorem mapRingHom_apply (a : NovikovSeries R H N) :
    mapRingHom ρ φ hφ a = map (ρ : R →+ S) φ hφ a :=
  (rfl)

/-- The pushforward ring homomorphism along the identity coefficient and exponent maps is the
identity. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom (RingHom.id R) (AddMonoidHom.id H) exists_period_rescale_id =
      RingHom.id (NovikovSeries R H N) := by
  ext a h
  exact coeff_map_id_right _ a h

/-- The composite of pushforward ring homomorphisms is the pushforward ring homomorphism along the
composite coefficient and exponent maps. -/
theorem mapRingHom_comp (ρ' : S →+* T) (φ' : H' →+ H'')
    (hφ' : ∃ c > 0, ∀ h, N'' (φ' h) = c * N' h) :
    (mapRingHom ρ' φ' hφ').comp (mapRingHom ρ φ hφ) =
      mapRingHom (ρ'.comp ρ) (φ'.comp φ) (exists_period_rescale_comp hφ hφ') :=
  RingHom.ext <| map_map (ρ : R →+ S) φ hφ (ρ' : S →+ T) φ' hφ'

end RingHom

section AlgHom

variable [AddMonoid H] [AddMonoid H'] {N : H →+ ℝ} {N' : H' →+ ℝ} {A : Type*} [CommSemiring A]
  [Semiring R] [Semiring S] [Algebra A R] [Algebra A S]

/-- The pushforward of Novikov series along an `A`-algebra homomorphism `ρ` of coefficients and an
exponent homomorphism `φ` rescaling periods by a positive constant, as an `A`-algebra
homomorphism. For `ρ = AlgHom.id A R` this is the pushforward of `A`-algebras of Novikov series
with fixed coefficient ring. -/
def mapAlgHom (ρ : R →ₐ[A] S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) :
    NovikovSeries R H N →ₐ[A] NovikovSeries S H' N' where
  __ := mapRingHom (ρ : R →+* S) φ hφ
  commutes' s := by
    rw [RingHom.toFun_eq_coe, mapRingHom_apply, algebraMap_apply, algebraMap_apply, map_single]
    simp

@[simp]
theorem mapAlgHom_apply (ρ : R →ₐ[A] S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (a : NovikovSeries R H N) :
    mapAlgHom ρ φ hφ a = map ((ρ : R →+* S) : R →+ S) φ hφ a :=
  (rfl)

end AlgHom

section Topology

variable [AddZeroClass H] [AddZeroClass H'] {N : H →+ ℝ} {N' : H' →+ ℝ} [AddCommGroup R]
  [AddCommGroup S] (ρ : R →+ S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)

/-- If `φ` rescales periods by `c ≥ 0`, the pushforward sends the period neighbourhood `U_C` into
`U'_(c * C)`. -/
theorem map_mem_periodFiltration {c C : ℝ} (hc : 0 ≤ c) (hcφ : ∀ h, N' (φ h) = c * N h)
    {a : NovikovSeries R H N} (ha : a ∈ periodFiltration R N C) :
    map ρ φ hφ a ∈ periodFiltration S N' (c * C) :=
  mem_periodFiltration.2 fun _ hh' =>
    coeff_map_eq_zero_of_lt ρ φ hφ hc hcφ (mem_periodFiltration.1 ha) hh'

/-- The pushforward of Novikov series is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_map : Continuous (map ρ φ hφ) := by
  obtain ⟨c, hc, hcφ⟩ := hφ
  refine continuous_of_continuousAt_zero (map ρ φ _) ?_
  rw [ContinuousAt, map_zero]
  refine (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ => ⟨C / c, trivial,
    fun a ha => ?_⟩
  simpa [mul_div_cancel₀ C hc.ne'] using map_mem_periodFiltration ρ φ _ hc.le hcφ ha

end Topology

section TopologyRing

variable [AddMonoid H] [AddMonoid H'] {N : H →+ ℝ} {N' : H' →+ ℝ} [Ring R] [Ring S]
  (ρ : R →+* S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)

/-- The pushforward ring homomorphism is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_mapRingHom : Continuous (mapRingHom ρ φ hφ) :=
  continuous_map (ρ : R →+ S) φ hφ

/-- The pushforward sends series supported in nonnegative periods to series supported in
nonnegative periods. -/
theorem map_mem_nonnegSubring {a : NovikovSeries R H N} (ha : a ∈ nonnegSubring R N) :
    map (ρ : R →+ S) φ hφ a ∈ nonnegSubring S N' := by
  obtain ⟨c, hc, hcφ⟩ := hφ
  simpa using map_mem_periodFiltration (ρ : R →+ S) φ _ hc.le hcφ (C := 0)
    (mem_periodFiltration.2 (mem_nonnegSubring.1 ha))

/-- The restriction of the pushforward ring homomorphism to the nonnegative subrings. -/
def mapNonnegSubring : nonnegSubring R N →+* nonnegSubring S N' :=
  (mapRingHom ρ φ hφ).restrict _ _ fun _ ha => map_mem_nonnegSubring ρ φ hφ ha

@[simp]
theorem coe_mapNonnegSubring (a : nonnegSubring R N) :
    (mapNonnegSubring ρ φ hφ a : NovikovSeries S H' N') = map (ρ : R →+ S) φ hφ a :=
  (rfl)

/-- The pushforward maps the ideal of series supported in strictly positive periods into the
corresponding ideal. -/
theorem mapNonnegSubring_mem_posIdeal {a : nonnegSubring R N} (ha : a ∈ posIdeal R N) :
    mapNonnegSubring ρ φ hφ a ∈ posIdeal S N' := by
  obtain ⟨c, hc, hcφ⟩ := hφ
  obtain ⟨C, hC, haC⟩ := exists_pos_mem_periodFiltration_iff.2 (mem_posIdeal.1 ha)
  rw [mem_posIdeal, coe_mapNonnegSubring]
  exact exists_pos_mem_periodFiltration_iff.1
    ⟨c * C, mul_pos hc hC, map_mem_periodFiltration (ρ : R →+ S) φ _ hc.le hcφ haC⟩

end TopologyRing

end NovikovSeries

end TauCeti
