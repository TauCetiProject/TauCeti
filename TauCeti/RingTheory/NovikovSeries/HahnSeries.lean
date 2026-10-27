/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import TauCeti.Order.WellFoundedSet
public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import TauCeti.RingTheory.NovikovSeries.Topology

/-!
# Novikov series as Hahn series over the group ring of the period kernel

Let `N : H →+ ℝ` be a period homomorphism. The Novikov series `Nov(R, H, N)` are defined by their
coefficient functions, with no order on `H` and no choice of complement to the period kernel.
This file compares them with Hahn series once such a choice is made.

A *splitting of the period kernel* (`TauCeti.NovikovSeries.PeriodKernelSplitting`) identifies `H`
with a product `K × Γ`, where `Γ` is a linearly ordered group embedded in `ℝ` by a strictly
monotone period map, such that `N` is the period of the `Γ`-component. Then `K` is the kernel of
`N` (`TauCeti.NovikovSeries.PeriodKernelSplitting.period_eq_zero_iff`). A Novikov series `a`
has only finitely many nonzero coefficients of a given period, so for each `γ : Γ` its
coefficients at the exponents `(k, γ)` form an element of the group ring `R[K]`. The support of
the resulting family is finite below every period, hence well-founded, and we obtain an injective
ring homomorphism

`TauCeti.NovikovSeries.toHahnSeries S : Nov(R, H, N) →+* HahnSeries Γ R[K]`.

Ties in the period are retained: the finitely many exponents of a common period are recorded in
one coefficient of `R[K]`, so `N` need not be injective, and the kernel `K` may be infinite.
The image of `toHahnSeries S` consists exactly of the *locally finite* Hahn series, those with
finitely many nonzero coefficients below each period
(`TauCeti.NovikovSeries.mem_range_toHahnSeries_iff`); we package it as the subsemiring
`TauCeti.NovikovSeries.locallyFiniteHahnSeries S` and obtain the ring isomorphism
`TauCeti.NovikovSeries.hahnSeriesEquiv S`. Well-founded support alone is weaker than local
finiteness as soon as the period group `Γ` is not discrete.

Under the comparison, the period neighbourhood `U_C` consists of the series whose Hahn
coefficients vanish below the period `C`, and convergence in the period topology is eventual
agreement of Hahn coefficients below each period.

The splitting and the ordered group `Γ` are data: the comparison is not the definition of the
Novikov ring, and it depends on the splitting. A section `σ` of `N` over its image gives a
splitting with `K = ker N` and `Γ = range N`
(`TauCeti.NovikovSeries.PeriodKernelSplitting.ofSection`).

## Main definitions

* `TauCeti.NovikovSeries.PeriodKernelSplitting N K Γ`: an identification `H ≃+ K × Γ` under which
  `N` becomes a strictly monotone period map on `Γ`.
* `TauCeti.NovikovSeries.PeriodKernelSplitting.ofSection`: the splitting of `H` as
  `ker N × range N` given by a section of `N` over its image.
* `TauCeti.NovikovSeries.toHahnSeries S`: the comparison ring homomorphism to Hahn series over
  `R[K]`.
* `TauCeti.NovikovSeries.locallyFiniteHahnSeries S`: the locally finite Hahn series.
* `TauCeti.NovikovSeries.hahnSeriesEquiv S`: the ring isomorphism of Novikov series with the
  locally finite Hahn series.

## Main results

* `TauCeti.NovikovSeries.coeff_coeff_toHahnSeries`: the coefficient of `toHahnSeries S a` at `γ`
  has coefficient `a.coeff (S.equiv.symm (k, γ))` at `k`.
* `TauCeti.NovikovSeries.support_toHahnSeries`: the Hahn support is the image of the Novikov
  support.
* `TauCeti.NovikovSeries.toHahnSeries_single`: monomials go to monomials.
* `TauCeti.NovikovSeries.toHahnSeries_injective` and
  `TauCeti.NovikovSeries.mem_range_toHahnSeries_iff`: the comparison is injective, with image the
  locally finite Hahn series.
* `TauCeti.NovikovSeries.mem_periodFiltration_iff_coeff_toHahnSeries` and
  `TauCeti.NovikovSeries.tendsto_nhds_iff_coeff_toHahnSeries`: the period filtration and the
  period topology in terms of Hahn coefficients.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti

namespace NovikovSeries

variable {R H K Γ : Type*}

/-- A splitting of the period kernel of `N : H →+ ℝ`: an additive identification of `H` with
`K × Γ`, where `Γ` is linearly ordered with a strictly monotone period map to `ℝ`, under which
`N` is the period of the `Γ`-component. The group `K` is then the kernel of `N`. -/
structure PeriodKernelSplitting [AddZeroClass H] (N : H →+ ℝ) (K Γ : Type*) [AddZeroClass K]
    [AddZeroClass Γ] [LinearOrder Γ] where
  /-- The identification of the exponents with pairs of a kernel element and a period class. -/
  equiv : H ≃+ K × Γ
  /-- The period of an element of `Γ`. -/
  period : Γ →+ ℝ
  /-- The order of `Γ` is the order of the periods. -/
  strictMono_period : StrictMono period
  /-- `N` is the period of the `Γ`-component. -/
  period_snd_equiv (h : H) : period (equiv h).2 = N h

namespace PeriodKernelSplitting

variable [AddZeroClass H] {N : H →+ ℝ} [AddZeroClass K] [AddZeroClass Γ] [LinearOrder Γ]
  (S : PeriodKernelSplitting N K Γ)

/-- The exponent corresponding to `(k, γ)` has period `S.period γ`. -/
@[simp]
theorem period_symm_apply (k : K) (γ : Γ) : N (S.equiv.symm (k, γ)) = S.period γ := by
  rw [← S.period_snd_equiv, AddEquiv.apply_symm_apply]

/-- `K` is the period kernel: an exponent has period zero exactly when its `Γ`-component is
zero. -/
theorem period_eq_zero_iff {h : H} : N h = 0 ↔ (S.equiv h).2 = 0 := by
  rw [← S.period_snd_equiv, ← map_zero S.period, S.strictMono_period.injective.eq_iff]

end PeriodKernelSplitting

namespace PeriodKernelSplitting

variable [AddCommGroup H] {N : H →+ ℝ}

/-- The splitting of the period kernel given by a section `σ` of `N` over its image: an exponent
`h` corresponds to the pair of `h - σ (N h)`, in the kernel, and of its period `N h`. -/
def ofSection (σ : N.range →+ H) (hσ : ∀ γ, N (σ γ) = γ) :
    PeriodKernelSplitting N N.ker N.range where
  equiv :=
    { toFun h := (⟨h - σ (N.rangeRestrict h), by simp [hσ]⟩, N.rangeRestrict h)
      invFun p := p.1 + σ p.2
      left_inv h := by simp
      right_inv p := by
        have hp : N.rangeRestrict (p.1 + σ p.2) = p.2 :=
          Subtype.ext (by simp [hσ, AddMonoidHom.mem_ker.1 p.1.2])
        exact Prod.ext (Subtype.ext (by simp [hp])) hp
      map_add' h h' := by
        ext
        · simp only [map_add, Prod.fst_add, AddSubgroup.coe_add]
          abel
        · simp only [map_add, Prod.snd_add] }
  period := N.range.subtype
  strictMono_period _ _ := id
  period_snd_equiv _ := AddMonoidHom.coe_rangeRestrict N _

@[simp]
theorem ofSection_equiv_apply (σ : N.range →+ H) (hσ : ∀ γ, N (σ γ) = γ) (h : H) :
    (ofSection σ hσ).equiv h =
      (⟨h - σ (N.rangeRestrict h), by simp [hσ]⟩, N.rangeRestrict h) :=
  (rfl)

@[simp]
theorem ofSection_equiv_symm_apply (σ : N.range →+ H) (hσ : ∀ γ, N (σ γ) = γ)
    (p : N.ker × N.range) : (ofSection σ hσ).equiv.symm p = p.1 + σ p.2 :=
  (rfl)

@[simp]
theorem ofSection_period (σ : N.range →+ H) (hσ : ∀ γ, N (σ γ) = γ) :
    (ofSection σ hσ).period = N.range.subtype :=
  (rfl)

end PeriodKernelSplitting

section Semiring

variable [Semiring R] [AddMonoid H] {N : H →+ ℝ} [AddMonoid K] [AddCommMonoid Γ] [LinearOrder Γ]
  (S : PeriodKernelSplitting N K Γ)

/-- The coefficients of `a` at the exponents with `Γ`-component `γ`, as an element of `R[K]`.
These exponents all have period `S.period γ`, so only finitely many coefficients are nonzero. -/
private def kernelCoeff (a : NovikovSeries R H N) (γ : Γ) : AddMonoidAlgebra R K :=
  .ofCoeff <| Finsupp.ofSupportFinite (fun k => a.coeff (S.equiv.symm (k, γ))) <|
    ((a.finite_le (S.period γ)).preimage
      (S.equiv.symm.injective.comp (Prod.mk_left_injective γ)).injOn).subset
      fun k hk => ⟨hk, (S.period_symm_apply k γ).le⟩

private theorem coeff_kernelCoeff (a : NovikovSeries R H N) (γ : Γ) (k : K) :
    (kernelCoeff S a γ).coeff k = a.coeff (S.equiv.symm (k, γ)) :=
  rfl

private theorem kernelCoeff_ne_zero_iff {a : NovikovSeries R H N} {γ : Γ} :
    kernelCoeff S a γ ≠ 0 ↔ ∃ h ∈ a.support, (S.equiv h).2 = γ := by
  refine ⟨fun hγ => ?_, fun ⟨h, hh, hγ⟩ hγ' => ?_⟩
  · by_contra hcon
    refine hγ (AddMonoidAlgebra.ext (Finsupp.ext fun k => ?_))
    by_contra hk
    exact hcon ⟨_, mem_support.2 hk, by simp⟩
  · subst hγ
    have := congrArg (fun x => x.coeff (S.equiv h).1) hγ'
    simp only [coeff_kernelCoeff, Prod.mk.eta, AddEquiv.symm_apply_apply,
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact mem_support.1 hh this

/-- The Hahn series of a Novikov series, before it is bundled as a ring homomorphism. Its support
is finite below each period, hence partially well-ordered. -/
private def toHahnSeriesFun (a : NovikovSeries R H N) : HahnSeries Γ (AddMonoidAlgebra R K) where
  coeff := kernelCoeff S a
  isPWO_support' := by
    refine Set.IsPWO.of_finite_inter_Iic fun γ₀ _ => ?_
    refine ((a.finite_le (S.period γ₀)).image fun h => (S.equiv h).2).subset ?_
    rintro γ ⟨hγ, hle⟩
    obtain ⟨h, hh, rfl⟩ := (kernelCoeff_ne_zero_iff S).1 hγ
    exact ⟨h, ⟨mem_support.1 hh, by
      rw [← S.period_snd_equiv]
      exact S.strictMono_period.monotone hle⟩, rfl⟩

private theorem toHahnSeriesFun_single (h : H) (r : R) :
    toHahnSeriesFun S (single h r : NovikovSeries R H N) =
      HahnSeries.single (S.equiv h).2 (AddMonoidAlgebra.single (S.equiv h).1 r) := by
  classical
  ext γ k
  simp only [toHahnSeriesFun, coeff_kernelCoeff, HahnSeries.coeff_single]
  by_cases hγ : γ = (S.equiv h).2
  · by_cases hk : k = (S.equiv h).1
    · subst hγ hk
      simp
    · rw [ite_eq_left hγ, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
        ite_eq_right (Ne.symm hk), coeff_single_of_ne]
      rintro rfl
      simp at hk
  · rw [ite_eq_right hγ, coeff_single_of_ne, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    rintro rfl
    simp at hγ

variable [IsOrderedCancelAddMonoid Γ]

/-- The comparison is multiplicative. A pair of exponents of `H` adding up to `(k, γ)` is a pair
of `Γ`-components adding up to `γ`, which enters the Hahn product, together with a pair of
`K`-components adding up to `k`, which enters the group-ring product of the coefficients. -/
private theorem toHahnSeriesFun_mul (a b : NovikovSeries R H N) :
    toHahnSeriesFun S (a * b) = toHahnSeriesFun S a * toHahnSeriesFun S b := by
  classical
  ext γ k
  set A := toHahnSeriesFun S a
  set B := toHahnSeriesFun S b
  -- The group-ring coefficient of a product, as a sum over pairs of support exponents.
  have hprod (x y : AddMonoidAlgebra R K) : (x * y).coeff k =
      ∑ p ∈ x.coeff.support ×ˢ y.coeff.support with p.1 + p.2 = k, x.coeff p.1 * y.coeff p.2 := by
    rw [AddMonoidAlgebra.coeff_mul, Finset.sum_filter, Finset.sum_product]
    simp only [Finsupp.sum]
  -- Index the pairs of exponents of `H` by a pair of `Γ`-components and a pair of
  -- `K`-components.
  set D := Finset.antidiagonal A.isPWO_support B.isPWO_support γ
  let F : Γ × Γ → Finset (K × K) := fun ij =>
    {p ∈ (A.coeff ij.1).coeff.support ×ˢ (B.coeff ij.2).coeff.support | p.1 + p.2 = k}
  let g : (Σ _ : Γ × Γ, K × K) → H × H := fun t =>
    (S.equiv.symm (t.2.1, t.1.1), S.equiv.symm (t.2.2, t.1.2))
  have hg : Set.InjOn g (D.sigma F) := by
    rintro ⟨⟨i, j⟩, ⟨p, q⟩⟩ - ⟨⟨i', j'⟩, ⟨p', q'⟩⟩ - hgt
    simp only [g, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hgt
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hgt
    rfl
  calc (a * b).coeff (S.equiv.symm (k, γ))
      = ∑ p ∈ (D.sigma F).image g, a.coeff p.1 * b.coeff p.2 := by
        refine coeff_mul_eq_sum (fun p hp => ?_) fun u v huv hu hv => ?_
        · obtain ⟨⟨⟨i, j⟩, ⟨p, q⟩⟩, ht, rfl⟩ := Finset.mem_image.1 hp
          simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_filter, F, D] at ht
          rw [← map_add, Prod.mk_add_mk, ht.2.2, ht.1.2.2]
        · have he : S.equiv u + S.equiv v = (k, γ) := by
            rw [← map_add, huv, AddEquiv.apply_symm_apply]
          refine Finset.mem_image.2 ⟨⟨((S.equiv u).2, (S.equiv v).2),
            ((S.equiv u).1, (S.equiv v).1)⟩, ?_, by simp [g]⟩
          simp only [Finset.mem_sigma, Finset.mem_antidiagonal, HahnSeries.mem_support,
            Finset.mem_filter, Finset.mem_product, Finsupp.mem_support_iff, F, D]
          refine ⟨⟨fun hA => ?_, fun hB => ?_, congrArg Prod.snd he⟩, ⟨?_, ?_⟩,
            congrArg Prod.fst he⟩
          · have := congrArg (fun x => x.coeff (S.equiv u).1) hA
            exact hu (by simpa [A, toHahnSeriesFun, coeff_kernelCoeff] using this)
          · have := congrArg (fun x => x.coeff (S.equiv v).1) hB
            exact hv (by simpa [B, toHahnSeriesFun, coeff_kernelCoeff] using this)
          · simpa [A, toHahnSeriesFun, coeff_kernelCoeff] using hu
          · simpa [B, toHahnSeriesFun, coeff_kernelCoeff] using hv
    _ = ∑ t ∈ D.sigma F, a.coeff (g t).1 * b.coeff (g t).2 := Finset.sum_image hg
    _ = ∑ ij ∈ D, ∑ p ∈ F ij, (A.coeff ij.1).coeff p.1 * (B.coeff ij.2).coeff p.2 :=
        Finset.sum_sigma _ _ _
    _ = ((A * B).coeff γ).coeff k := by
        rw [HahnSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
        exact Finset.sum_congr rfl fun ij _ => (hprod _ _).symm

variable (R) in
/-- The comparison of Novikov series with Hahn series over the group ring of the period kernel,
for a splitting `S` of the period kernel. The coefficient at `γ : Γ` collects the coefficients
of the exponents with `Γ`-component `γ`. -/
def toHahnSeries : NovikovSeries R H N →+* HahnSeries Γ (AddMonoidAlgebra R K) where
  toFun := toHahnSeriesFun S
  map_one' := by
    rw [← single_zero_one, toHahnSeriesFun_single, map_zero, Prod.fst_zero, Prod.snd_zero,
      ← AddMonoidAlgebra.one_def, HahnSeries.single_zero_one]
  map_mul' := toHahnSeriesFun_mul S
  map_zero' := by
    ext
    simp [toHahnSeriesFun, coeff_kernelCoeff]
  map_add' a b := by
    ext
    simp [toHahnSeriesFun, coeff_kernelCoeff]

/-- The coefficient formula of the comparison: the coefficient of `toHahnSeries R S a` at `γ` has
coefficient `a.coeff (S.equiv.symm (k, γ))` at `k`. -/
@[simp]
theorem coeff_coeff_toHahnSeries (a : NovikovSeries R H N) (γ : Γ) (k : K) :
    ((toHahnSeries R S a).coeff γ).coeff k = a.coeff (S.equiv.symm (k, γ)) :=
  (rfl)

/-- A coefficient of a Novikov series, read off its Hahn series. -/
theorem coeff_eq_coeff_coeff_toHahnSeries (a : NovikovSeries R H N) (h : H) :
    a.coeff h = ((toHahnSeries R S a).coeff (S.equiv h).2).coeff (S.equiv h).1 := by
  simp

/-- The Hahn support of a Novikov series is the image of its support under the projection to
`Γ`. -/
theorem support_toHahnSeries (a : NovikovSeries R H N) :
    (toHahnSeries R S a).support = (fun h => (S.equiv h).2) '' a.support :=
  Set.ext fun _ => kernelCoeff_ne_zero_iff S

/-- The comparison sends the monomial `r e^h` to the Hahn monomial with coefficient the group-ring
monomial `r e^k`, where `S.equiv h = (k, γ)`. -/
@[simp]
theorem toHahnSeries_single (h : H) (r : R) :
    toHahnSeries R S (single h r : NovikovSeries R H N) =
      HahnSeries.single (S.equiv h).2 (AddMonoidAlgebra.single (S.equiv h).1 r) :=
  toHahnSeriesFun_single S h r

/-- The comparison is injective: a Novikov series is determined by its Hahn coefficients. -/
theorem toHahnSeries_injective : Injective (toHahnSeries R S) := fun a b hab => by
  ext h
  rw [coeff_eq_coeff_coeff_toHahnSeries S a, coeff_eq_coeff_coeff_toHahnSeries S b, hab]

/-- The image of the comparison consists exactly of the locally finite Hahn series: those with
only finitely many nonzero coefficients below each period. -/
theorem mem_range_toHahnSeries_iff {f : HahnSeries Γ (AddMonoidAlgebra R K)} :
    f ∈ Set.range (toHahnSeries R S) ↔
      ∀ C : ℝ, {γ | f.coeff γ ≠ 0 ∧ S.period γ < C}.Finite := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨a, rfl⟩ C
    refine ((a.finite_lt C).image fun h => (S.equiv h).2).subset ?_
    rintro γ ⟨hγ, hlt⟩
    obtain ⟨h, hh, rfl⟩ := (support_toHahnSeries S a).subset hγ
    exact ⟨h, ⟨mem_support.1 hh, by rwa [← S.period_snd_equiv]⟩, rfl⟩
  -- A locally finite Hahn series has finitely many nonzero coefficients, each a finite sum,
  -- below each period.
  refine ⟨⟨fun h => ((f.coeff (S.equiv h).2).coeff (S.equiv h).1), fun C => ?_⟩, ?_⟩
  · refine ((hf C).biUnion fun γ _ =>
      (f.coeff γ).coeff.support.finite_toSet.image fun k => S.equiv.symm (k, γ)).subset ?_
    rintro h ⟨hh, hlt⟩
    refine Set.mem_biUnion (x := (S.equiv h).2) ⟨fun hf' => hh ?_, ?_⟩
      ⟨(S.equiv h).1, Finsupp.mem_support_iff.2 hh, by simp⟩
    · simp [hf']
    · rwa [S.period_snd_equiv]
  · ext γ k
    simp

variable (R K) in
/-- The locally finite Hahn series over the group ring `R[K]` of the period kernel: those with
only finitely many nonzero coefficients below each period. They form a subsemiring, the image of
the comparison `toHahnSeries R S`. -/
def locallyFiniteHahnSeries : Subsemiring (HahnSeries Γ (AddMonoidAlgebra R K)) :=
  (toHahnSeries R S).rangeS.copy {f | ∀ C : ℝ, {γ | f.coeff γ ≠ 0 ∧ S.period γ < C}.Finite} <|
    Set.ext fun _ => (mem_range_toHahnSeries_iff S).symm

theorem mem_locallyFiniteHahnSeries_iff {f : HahnSeries Γ (AddMonoidAlgebra R K)} :
    f ∈ locallyFiniteHahnSeries R K S ↔
      ∀ C : ℝ, {γ | f.coeff γ ≠ 0 ∧ S.period γ < C}.Finite :=
  Iff.rfl

theorem toHahnSeries_mem_locallyFiniteHahnSeries (a : NovikovSeries R H N) :
    toHahnSeries R S a ∈ locallyFiniteHahnSeries R K S :=
  (mem_range_toHahnSeries_iff S).1 ⟨a, rfl⟩

variable (R) in
/-- The Novikov series are isomorphic, as a ring, to the locally finite Hahn series over the group
ring of the period kernel, through the comparison `toHahnSeries R S`. -/
def hahnSeriesEquiv : NovikovSeries R H N ≃+* locallyFiniteHahnSeries R K S :=
  RingEquiv.ofBijective
    ((toHahnSeries R S).codRestrict _ (toHahnSeries_mem_locallyFiniteHahnSeries S))
    ⟨fun _ _ hab => toHahnSeries_injective S (congrArg Subtype.val hab), fun f => by
      obtain ⟨a, ha⟩ := (mem_range_toHahnSeries_iff S).2 f.2
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp]
theorem coe_hahnSeriesEquiv_apply (a : NovikovSeries R H N) :
    (hahnSeriesEquiv R S a : HahnSeries Γ (AddMonoidAlgebra R K)) = toHahnSeries R S a :=
  (rfl)

@[simp]
theorem toHahnSeries_hahnSeriesEquiv_symm_apply (f : locallyFiniteHahnSeries R K S) :
    toHahnSeries R S ((hahnSeriesEquiv R S).symm f) = f := by
  rw [← coe_hahnSeriesEquiv_apply, RingEquiv.apply_symm_apply]

end Semiring

section Ring

variable [Ring R] [AddMonoid H] {N : H →+ ℝ} [AddMonoid K] [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] (S : PeriodKernelSplitting N K Γ)

/-- The period neighbourhood `U_C` consists of the Novikov series whose Hahn coefficients vanish
below the period `C`. -/
theorem mem_periodFiltration_iff_coeff_toHahnSeries {a : NovikovSeries R H N} {C : ℝ} :
    a ∈ periodFiltration R N C ↔ ∀ γ, S.period γ < C → (toHahnSeries R S a).coeff γ = 0 := by
  rw [mem_periodFiltration]
  refine ⟨fun ha γ hγ => ?_, fun ha h hh => ?_⟩
  · ext k
    simpa using ha _ (by rwa [S.period_symm_apply])
  · rw [coeff_eq_coeff_coeff_toHahnSeries S, ha _ (by rwa [S.period_snd_equiv]),
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- Convergence in the period topology is eventual agreement of Hahn coefficients below each
period. -/
theorem tendsto_nhds_iff_coeff_toHahnSeries {ι : Type*} {l : Filter ι}
    {f : ι → NovikovSeries R H N} {a : NovikovSeries R H N} :
    Tendsto f l (𝓝 a) ↔ ∀ C : ℝ, ∀ᶠ i in l, ∀ γ, S.period γ < C →
      (toHahnSeries R S (f i)).coeff γ = (toHahnSeries R S a).coeff γ := by
  simp only [(hasBasis_nhds a).tendsto_right_iff, mem_periodFiltration_iff_coeff_toHahnSeries S,
    map_sub, HahnSeries.coeff_sub, sub_eq_zero, Set.mem_ofPred_eq, forall_const]

end Ring

end NovikovSeries

end TauCeti
