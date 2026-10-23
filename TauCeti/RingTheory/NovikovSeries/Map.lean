/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finsupp.Basic
public import TauCeti.GroupTheory.Coset.Fiber
public import TauCeti.RingTheory.NovikovSeries.Basic

/-!
# Pushforward and restriction of Novikov series

Let `N : H →+ ℝ` and `N' : H' →+ ℝ` be period homomorphisms and `φ : H →+ H'` a homomorphism of
exponent groups that rescales periods by a positive constant: `N' (φ h) = c * N h` for some
`c > 0`. For instance, the inclusion of a subgroup `K ≤ H`, with the restricted period map
`N.comp K.subtype`, rescales periods by `c = 1`. For a finite cyclic covering, the exponent
group of the cover is such a finite-index subgroup of the exponent group of the base.

Together with an additive map `ρ : R →+ S` of coefficients, `φ` pushes a Novikov series forward
by summing coefficients along the fibres of `φ`:

`(map ρ φ hφ a).coeff h' = ∑ᶠ h ∈ φ ⁻¹' {h'}, ρ (a.coeff h)`.

Since `φ` rescales periods, only finitely many nonzero coefficients of `a` lie in a fibre, and
the result is again a Novikov series. No finiteness of the kernel of `φ` is needed. The
pushforward is additive and satisfies the identity and composition laws, which include its
naturality in the coefficient map. It extends the pushforward
`Finsupp.mapDomain φ ∘ Finsupp.mapRange ρ` of the group ring, and sends series vanishing below
the period cutoff `C` to series vanishing below `c * C`.

When `φ` has finite kernel, a Novikov series on `H'` also restricts along `φ` by precomposing its
coefficients (`TauCeti.NovikovSeries.comap`), sending series vanishing below `c * C` to series
vanishing below `C`. Restricting a pushforward along an injective `φ` gives back the series with
`ρ` applied to its coefficients.

## Main definitions

* `TauCeti.NovikovSeries.map`: the pushforward of Novikov series along a coefficient map and a
  period-rescaling exponent homomorphism.
* `TauCeti.NovikovSeries.comap`: the restriction of Novikov series along a period-rescaling
  exponent homomorphism with finite kernel.

## Main results

* `TauCeti.NovikovSeries.finite_support_inter_preimage_singleton`: a fibre of a period-rescaling
  homomorphism meets the support of a Novikov series in a finite set.
* `TauCeti.NovikovSeries.finite_setOf_map_add_eq`: only finitely many pairs of support exponents
  of two Novikov series have images under a period-rescaling homomorphism adding up to a given
  exponent.
* `TauCeti.NovikovSeries.exists_period_rescale_id` and
  `TauCeti.NovikovSeries.exists_period_rescale_comp`: the identity rescales periods by `1`, and
  composites rescale them by the product of the factors.
* `TauCeti.NovikovSeries.coeff_map_eq_sum`: a coefficient of a pushforward as a sum over any
  finite set of exponents in the fibre containing the nonzero coefficients there.
* `TauCeti.NovikovSeries.map_id` and `TauCeti.NovikovSeries.map_map`: the identity and composition
  laws of the pushforward.
* `TauCeti.NovikovSeries.map_ofFinsupp`: the pushforward of a finitely supported series is the
  group-ring pushforward.
* `TauCeti.NovikovSeries.map_single`: the pushforward of the monomial `r e^g` is the monomial
  `ρ r e^(φ g)`.
* `TauCeti.NovikovSeries.coeff_map_eq_zero_of_lt` and
  `TauCeti.NovikovSeries.coeff_comap_eq_zero_of_lt`: the pushforward moves the period cutoff `C`
  to `c * C`, and the restriction moves `c * C` back to `C`.
* `TauCeti.NovikovSeries.comap_comap` and `TauCeti.NovikovSeries.comap_map_of_injective`: the
  composition law of restriction, and restriction of a pushforward along an injective
  homomorphism.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

variable {R S T H H' H'' : Type*}

section Map

variable [AddZeroClass H] [AddZeroClass H'] [AddZeroClass H''] {N : H →+ ℝ} {N' : H' →+ ℝ}
  {N'' : H'' →+ ℝ}

/-- If `φ` rescales periods by a positive constant, only finitely many exponents in a fibre of
`φ` carry a nonzero coefficient of a Novikov series. -/
theorem finite_support_inter_preimage_singleton [Zero R] (a : NovikovSeries R H N)
    {φ : H →+ H'} (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (h' : H') :
    (a.support ∩ φ ⁻¹' {h'}).Finite := by
  obtain ⟨c, hc, hφ⟩ := hφ
  refine (a.finite_le (N' h' / c)).subset ?_
  rintro h ⟨hh, rfl⟩
  exact ⟨mem_support.1 hh, (le_div_iff₀' hc).2 (hφ h).ge⟩

/-- If `φ` rescales periods by a positive constant, then for two Novikov series only finitely many
pairs of support exponents have images under `φ` adding up to a given exponent. -/
theorem finite_setOf_map_add_eq [Zero R] [Zero S] (a : NovikovSeries R H N)
    (b : NovikovSeries S H N) {φ : H →+ H'} (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (h' : H') :
    {p : H × H | φ p.1 + φ p.2 = h' ∧ a.coeff p.1 ≠ 0 ∧ b.coeff p.2 ≠ 0}.Finite := by
  obtain ⟨c, hc, hcφ⟩ := hφ
  refine (finite_setOf_period_add_lt a b (N' h' / c + 1)).subset fun p hp => ⟨?_, hp.2⟩
  rw [← hp.1, ← map_add, hcφ, mul_div_cancel_left₀ _ hc.ne']
  exact lt_add_one _

/-- The identity rescales periods by `1`. -/
theorem exists_period_rescale_id : ∃ c > 0, ∀ h, N (AddMonoidHom.id H h) = c * N h :=
  ⟨1, one_pos, fun h => (one_mul (N h)).symm⟩

/-- If `φ` rescales periods by `c` and `φ'` by `c'`, then `φ'.comp φ` rescales them by `c' * c`. -/
theorem exists_period_rescale_comp {φ : H →+ H'} {φ' : H' →+ H''}
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (hφ' : ∃ c > 0, ∀ h, N'' (φ' h) = c * N' h) :
    ∃ c > 0, ∀ h, N'' (φ'.comp φ h) = c * N h := by
  obtain ⟨c, hc, hφ⟩ := hφ
  obtain ⟨c', hc', hφ'⟩ := hφ'
  exact ⟨c' * c, mul_pos hc' hc, fun h => by rw [AddMonoidHom.comp_apply, hφ', hφ, mul_assoc]⟩

/-- If an additive equivalence rescales periods by a positive factor `c`, its inverse rescales
them by `c⁻¹`. -/
theorem period_rescale_symm {e : H ≃+ H'} {c : ℝ} (hc : 0 < c)
    (hcN : ∀ h, N' (e h) = c * N h) (h' : H') :
    N (e.symm h') = c⁻¹ * N' h' := by
  have h := hcN (e.symm h')
  rw [e.apply_symm_apply] at h
  rw [h, inv_mul_cancel_left₀ hc.ne']

/-- The inverse of an additive equivalence that rescales periods positively also rescales
periods positively. -/
theorem exists_period_rescale_symm {e : H ≃+ H'}
    (he : ∃ c > 0, ∀ h, N' (e h) = c * N h) :
    ∃ c > 0, ∀ h', N (e.symm h') = c * N' h' := by
  obtain ⟨c, hc, hcN⟩ := he
  exact ⟨c⁻¹, inv_pos.mpr hc, period_rescale_symm hc hcN⟩

/-- Successive additive equivalences rescaling periods positively have a composite that also
rescales periods positively. -/
theorem exists_period_rescale_trans {e : H ≃+ H'} {e' : H' ≃+ H''}
    (he : ∃ c > 0, ∀ h, N' (e h) = c * N h)
    (he' : ∃ c > 0, ∀ h, N'' (e' h) = c * N' h) :
    ∃ c > 0, ∀ h, N'' ((e.trans e') h) = c * N h := by
  simpa only [AddEquiv.trans_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom] using
    exists_period_rescale_comp (φ := e.toAddMonoidHom) (φ' := e'.toAddMonoidHom)
      (by simpa only [AddEquiv.coe_toAddMonoidHom] using he)
      (by simpa only [AddEquiv.coe_toAddMonoidHom] using he')

variable [AddMonoid R] [AddCommMonoid S] [AddCommMonoid T]

/-- The pushforward of a Novikov series along a coefficient map `ρ` and an exponent homomorphism
`φ` rescaling periods by a positive constant: the coefficient at `h'` is the sum of the images
under `ρ` of the coefficients at the exponents `h` with `φ h = h'`. -/
def map (ρ : R →+ S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) :
    NovikovSeries R H N →+ NovikovSeries S H' N' where
  toFun a :=
    { coeff h' := ∑ᶠ h ∈ φ ⁻¹' {h'}, ρ (a.coeff h)
      finite_lt C := by
        obtain ⟨c, hc, hcφ⟩ := hφ
        refine ((a.finite_lt (C / c)).image φ).subset ?_
        rintro h' ⟨hh', hC⟩
        obtain ⟨h, rfl : φ h = h', hh⟩ := exists_ne_zero_of_finsum_mem_ne_zero hh'
        exact ⟨h, ⟨fun ha => hh (by rw [ha, map_zero]), (lt_div_iff₀' hc).2 (hcφ h ▸ hC)⟩, rfl⟩ }
  map_zero' := by
    ext h'
    exact finsum_mem_eq_zero_of_forall_eq_zero fun h _ => by rw [coeff_zero, map_zero]
  map_add' a b := by
    ext h'
    refine (finsum_mem_congr rfl fun h _ => map_add ρ _ _).trans (finsum_mem_add_distrib'
      ((a.finite_support_inter_preimage_singleton hφ h').subset fun h hh => ?_)
      ((b.finite_support_inter_preimage_singleton hφ h').subset fun h hh => ?_)) <;>
    exact ⟨mem_support.2 fun hab => hh.2 (by simp [hab]), hh.1⟩

variable (ρ : R →+ S) (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)

/-- The coefficient of a pushforward at `h'` is the sum of the images under `ρ` of the
coefficients at the exponents in the fibre of `φ` over `h'`. -/
theorem coeff_map (a : NovikovSeries R H N) (h' : H') :
    (map ρ φ hφ a).coeff h' = ∑ᶠ h ∈ φ ⁻¹' {h'}, ρ (a.coeff h) := by
  rfl

/-- A coefficient of a pushforward is the sum over any finite set of exponents in the fibre
containing the exponents of nonzero coefficient there. -/
theorem coeff_map_eq_sum (a : NovikovSeries R H N) {h' : H'} (s : Finset H)
    (hs : a.support ∩ φ ⁻¹' {h'} ⊆ s) (hsφ : ∀ h ∈ s, φ h = h') :
    (map ρ φ hφ a).coeff h' = ∑ h ∈ s, ρ (a.coeff h) := by
  rw [coeff_map]
  exact finsum_mem_eq_sum_of_subset _
    (fun h hh => hs ⟨mem_support.2 fun ha => hh.2 (by simp [ha]), hh.1⟩) hsφ

/-- Every exponent of nonzero coefficient of a pushforward is the image of an exponent of nonzero
coefficient. -/
theorem support_map_subset (a : NovikovSeries R H N) : (map ρ φ hφ a).support ⊆ φ '' a.support := by
  intro h' hh'
  rw [mem_support, coeff_map] at hh'
  obtain ⟨h, hφh, hh⟩ := exists_ne_zero_of_finsum_mem_ne_zero hh'
  exact ⟨h, mem_support.2 fun ha => hh (by rw [ha, map_zero]), hφh⟩

/-- A pushforward has zero coefficient outside the range of the exponent homomorphism. -/
theorem coeff_map_eq_zero_of_notMem_range (a : NovikovSeries R H N) {h' : H'}
    (hh' : h' ∉ range φ) : (map ρ φ hφ a).coeff h' = 0 := by
  by_contra hne
  obtain ⟨h, -, rfl⟩ := support_map_subset ρ φ hφ a (mem_support.2 hne)
  exact hh' ⟨h, rfl⟩

/-- If `h` is the only exponent of nonzero coefficient in its fibre, the pushforward moves the
coefficient at `h` to `φ h`. -/
theorem coeff_map_of_support_inter_subset_singleton (a : NovikovSeries R H N) {h : H}
    (hs : a.support ∩ φ ⁻¹' {φ h} ⊆ {h}) : (map ρ φ hφ a).coeff (φ h) = ρ (a.coeff h) := by
  rw [coeff_map_eq_sum ρ φ hφ a {h} (fun g hg => Finset.mem_singleton.2 (hs hg))
    fun g hg => by rw [Finset.mem_singleton.1 hg], Finset.sum_singleton]

/-- Along an injective exponent homomorphism, the pushforward moves each coefficient to the image
exponent. -/
@[simp]
theorem coeff_map_of_injective (hinj : Injective φ) (a : NovikovSeries R H N) (h : H) :
    (map ρ φ hφ a).coeff (φ h) = ρ (a.coeff h) :=
  coeff_map_of_support_inter_subset_singleton ρ φ hφ a fun _ hg => hinj hg.2

/-- The pushforward along the identity of exponents applies the coefficient map to each
coefficient. -/
@[simp]
theorem coeff_map_id_right (a : NovikovSeries R H N) (h : H) :
    (map ρ (AddMonoidHom.id H) exists_period_rescale_id a).coeff h = ρ (a.coeff h) :=
  coeff_map_of_injective ρ _ _ injective_id a h

/-- The pushforward sends a series vanishing below the period cutoff `C` to a series vanishing
below `c * C`, where `c` is the period rescaling factor of `φ`. -/
theorem coeff_map_eq_zero_of_lt {c C : ℝ} (hc : 0 ≤ c) (hcφ : ∀ h, N' (φ h) = c * N h)
    {a : NovikovSeries R H N} (ha : ∀ h, N h < C → a.coeff h = 0) {h' : H'}
    (hh' : N' h' < c * C) : (map ρ φ hφ a).coeff h' = 0 := by
  by_contra hne
  obtain ⟨h, hh, rfl⟩ := support_map_subset ρ φ hφ a (mem_support.2 hne)
  rw [hcφ] at hh'
  exact mem_support.1 hh (ha h (lt_of_not_ge fun hCh => hh'.not_ge
    (mul_le_mul_of_nonneg_left hCh hc)))

/-- Pushing forward along the identity coefficient map and the identity exponent homomorphism is
the identity. -/
@[simp]
theorem map_id {M : Type*} [AddCommMonoid M] :
    map (AddMonoidHom.id M) (AddMonoidHom.id H) exists_period_rescale_id =
      AddMonoidHom.id (NovikovSeries M H N) := by
  ext a h
  exact coeff_map_id_right _ a h

/-- The pushforward along composite coefficient and exponent maps is the composite of the
pushforwards. -/
@[simp]
theorem map_map (ρ' : S →+ T) (φ' : H' →+ H'') (hφ' : ∃ c > 0, ∀ h, N'' (φ' h) = c * N' h)
    (a : NovikovSeries R H N) :
    map ρ' φ' hφ' (map ρ φ hφ a) =
      map (ρ'.comp ρ) (φ'.comp φ) (exists_period_rescale_comp hφ hφ') a := by
  classical
  ext h''
  have hφφ' := exists_period_rescale_comp hφ hφ'
  set t := (a.finite_support_inter_preimage_singleton hφφ' h'').toFinset
  have ht : ∀ h, h ∈ t ↔ a.coeff h ≠ 0 ∧ φ' (φ h) = h'' := fun h => by
    simp [t, mem_support]
  rw [coeff_map_eq_sum ρ' φ' hφ' _ (t.image φ) ?_ ?_,
    coeff_map_eq_sum (ρ'.comp ρ) (φ'.comp φ) hφφ' a t
      (fun h hh => (ht h).2 ⟨mem_support.1 hh.1, hh.2⟩) fun h hh => ((ht h).1 hh).2,
    ← Finset.sum_fiberwise_of_maps_to (g := φ) fun h hh => Finset.mem_image_of_mem φ hh]
  · refine Finset.sum_congr rfl fun h' hh' => ?_
    rw [coeff_map_eq_sum ρ φ hφ a (t.filter fun h => φ h = h') ?_ fun h hh =>
      (Finset.mem_filter.1 hh).2, map_sum]
    · simp only [AddMonoidHom.comp_apply]
    · rintro h ⟨hh, hφh⟩
      obtain ⟨g, hg, hgh'⟩ := Finset.mem_image.1 hh'
      refine Finset.mem_filter.2 ⟨(ht h).2 ⟨mem_support.1 hh, ?_⟩, hφh⟩
      rw [(hφh : φ h = h'), ← hgh']
      exact ((ht g).1 hg).2
  · rintro h' ⟨hh', rfl⟩
    obtain ⟨h, hh, rfl⟩ := support_map_subset ρ φ hφ a hh'
    exact Finset.mem_image_of_mem φ ((ht h).2 ⟨mem_support.1 hh, rfl⟩)
  · intro h' hh'
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hh'
    exact ((ht h).1 hh).2

/-- The pushforward of a finitely supported series is the pushforward of the group ring, along
`ρ` on coefficients and along `φ` on exponents. -/
@[simp]
theorem map_ofFinsupp (f : H →₀ R) :
    map ρ φ hφ (ofFinsupp f) =
      ofFinsupp (Finsupp.mapDomain φ (Finsupp.mapRange ρ ρ.map_zero f)) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, Finsupp.mapRange_add, Finsupp.mapDomain_add]
  | single h r =>
    ext h'
    rw [Finsupp.mapRange_single, Finsupp.mapDomain_single, coeff_ofFinsupp]
    have hs : (ofFinsupp (N := N) (Finsupp.single h r)).support ⊆ {h} := by
      rw [support_ofFinsupp, ← Finset.coe_singleton, Finset.coe_subset]
      exact Finsupp.support_single_subset
    by_cases hh : φ h = h'
    · subst hh
      rw [coeff_map_of_support_inter_subset_singleton ρ φ hφ _ (inter_subset_left.trans hs),
        coeff_ofFinsupp, Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hh), coeff_map_eq_sum ρ φ hφ _ ∅ ?_ (by simp),
        Finset.sum_empty]
      rintro g ⟨hg, hφg⟩
      exact absurd (by rw [← mem_singleton_iff.1 (hs hg)]; exact hφg) hh

/-- The pushforward of the monomial `r e^g` is the monomial `ρ r e^(φ g)`. -/
@[simp]
theorem map_single (g : H) (r : R) : map ρ φ hφ (single g r) = single (φ g) (ρ r) := by
  rw [← ofFinsupp_single, map_ofFinsupp, Finsupp.mapRange_single, Finsupp.mapDomain_single,
    ofFinsupp_single]

end Map

section Comap

variable [AddGroup H] {N : H →+ ℝ} [AddMonoid R]

section Restriction

variable [AddZeroClass H'] {N' : H' →+ ℝ}

/-- The restriction of a Novikov series along an exponent homomorphism `φ` with finite kernel
rescaling periods by a positive constant: the coefficient at `h` is the coefficient at `φ h`. -/
def comap (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (hker : (φ.ker : Set H).Finite) : NovikovSeries R H' N' →+ NovikovSeries R H N where
  toFun b :=
    { coeff h := b.coeff (φ h)
      finite_lt C := by
        obtain ⟨c, hc, hcφ⟩ := hφ
        have := hker.to_subtype
        exact ((b.finite_lt (c * C)).preimage' fun h' _ => finite_coe_iff.1 (φ.finite_fiber h')
          ).subset fun h hh => ⟨hh.1, (hcφ h).symm ▸ mul_lt_mul_of_pos_left hh.2 hc⟩ }
  map_zero' := rfl
  map_add' _ _ := rfl

variable (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (hker : (φ.ker : Set H).Finite)

/-- The coefficient of a restriction at `h` is the coefficient of the series at `φ h`. -/
@[simp]
theorem coeff_comap (b : NovikovSeries R H' N') (h : H) :
    (comap φ hφ hker b).coeff h = b.coeff (φ h) := by
  rfl

/-- The exponents of nonzero coefficient of a restriction are the preimages of those of the
series. -/
@[simp]
theorem support_comap (b : NovikovSeries R H' N') :
    (comap φ hφ hker b).support = φ ⁻¹' b.support := by
  ext
  simp

/-- The restriction sends a series vanishing below the period cutoff `c * C` to a series
vanishing below `C`, where `c > 0` is the period rescaling factor of `φ`. -/
theorem coeff_comap_eq_zero_of_lt {c C : ℝ} (hc : 0 < c) (hcφ : ∀ h, N' (φ h) = c * N h)
    {b : NovikovSeries R H' N'} (hb : ∀ h', N' h' < c * C → b.coeff h' = 0) {h : H}
    (hh : N h < C) : (comap φ hφ hker b).coeff h = 0 :=
  hb _ ((hcφ h).symm ▸ mul_lt_mul_of_pos_left hh hc)

/-- Restricting along the identity exponent homomorphism is the identity. -/
@[simp]
theorem comap_id :
    comap (AddMonoidHom.id H) exists_period_rescale_id (by simp [AddMonoidHom.ker_id]) =
      AddMonoidHom.id (NovikovSeries R H N) := by
  ext
  simp

/-- Restricting a pushforward along an injective exponent homomorphism gives back the series with
the coefficient map applied to its coefficients. -/
theorem comap_map_of_injective [AddCommMonoid S] (ρ : R →+ S) (hinj : Injective φ)
    (a : NovikovSeries R H N) :
    comap φ hφ hker (map ρ φ hφ a) = map ρ (AddMonoidHom.id H) exists_period_rescale_id a := by
  ext h
  rw [coeff_comap, coeff_map_of_injective _ _ _ hinj, coeff_map_id_right]

end Restriction

section Composition

variable [AddGroup H'] [AddZeroClass H''] {N' : H' →+ ℝ} {N'' : H'' →+ ℝ}
variable (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (hker : (φ.ker : Set H).Finite)

/-- The restriction along a composite exponent homomorphism is the composite of the
restrictions. -/
@[simp]
theorem comap_comap (φ' : H' →+ H'') (hφ' : ∃ c > 0, ∀ h, N'' (φ' h) = c * N' h)
    (hker' : (φ'.ker : Set H').Finite) (b : NovikovSeries R H'' N'') :
    comap φ hφ hker (comap φ' hφ' hker' b) =
      comap (φ'.comp φ) (exists_period_rescale_comp hφ hφ') (φ'.finite_ker_comp φ hker' hker)
        b := by
  ext
  simp

end Composition

end Comap

end NovikovSeries

end TauCeti
