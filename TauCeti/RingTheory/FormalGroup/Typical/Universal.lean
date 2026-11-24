/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hazewinkel.LeadingDifference
public import TauCeti.RingTheory.FormalGroup.LeadingDifference
public import TauCeti.RingTheory.FormalGroup.Typical.Lazard
import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial

/-!
# Hazewinkel's law is the universal `p`-typical formal group law

Let `p` be a prime. Hazewinkel's integral formal group law `F_v`
(`TauCeti.hazewinkelIntegralFormalGroup p v`) over `ℤ[v₁, v₂, …]` is `p`-typical
(`TauCeti.isPTypical_hazewinkelIntegralFormalGroup`). This file proves that it is the universal
`p`-typical law over `ℤ_(p)`-algebras: if every prime `q ≠ p` is invertible in a commutative ring
`R`, then every commutative `p`-typical formal group law over `R` is `F_v` for a unique family
`v : ℕ+ → R` (`FormalGroup.IsPTypical.existsUnique_eq_hazewinkelIntegralFormalGroup`). Equivalently,
commutative `p`-typical laws over `R` correspond bijectively to ring homomorphisms
`ℤ[v₁, v₂, …] →+* R` (`TauCeti.hazewinkelLift`), which are the ring homomorphisms out of
`V = ℤ_(p)[v₁, v₂, …]`. This is the universal property of the ring `V` in Hazewinkel's generators
(Ravenel, Theorem A2.1.25).

Uniqueness holds over every commutative ring (`TauCeti.hazewinkelIntegralFormalGroup_injective`).
Existence is proved first when `R` embeds in a `ℚ`-algebra `K`
(`FormalGroup.IsPTypical.exists_eq_hazewinkelIntegralFormalGroup_of_injective`). Over `K` the law
is Hazewinkel's for a unique `w : ℕ+ → K`, by the rational classification of `p`-typical laws
(`FormalGroup.IsPTypical.existsUnique_eq_hazewinkelFormalGroup`), and `wₙ` lies in `R` by induction
on `n`. If `w₁, …, w_(n - 1)` come from `u₁, …, u_(n - 1)` in `R`, the law agrees below degree `pⁿ`
with `F_u` for `u = (u₁, …, u_(n - 1), 0, 0, …)`, so its degree-`pⁿ` difference from `F_u` is
`c C_(pⁿ)` for some `c ∈ R` by Lazard's symmetric 2-cocycle lemma. Over `K` the same difference is
`-wₙ C_(pⁿ)` (`TauCeti.homogeneousComponent_hazewinkelFormalGroup_sub`), so `wₙ` is the image of
`-c`. For a general `ℤ_(p)`-algebra, the law is classified by a ring homomorphism out of the ring of
Quillen's universal `p`-typical law (`TauCeti.LazardRing.typicalLocalizedLift`), a subring of a
localization of the Lazard ring, which is a domain of characteristic zero and so embeds in its
field of fractions.

## Main results

* `FormalGroup.IsPTypical.exists_eq_hazewinkelIntegralFormalGroup_of_injective`: a `p`-typical law
  over a ring embedding in a `ℚ`-algebra is Hazewinkel's.
* `FormalGroup.IsPTypical.existsUnique_eq_hazewinkelIntegralFormalGroup`: over a ring in which
  every prime `q ≠ p` is invertible, a `p`-typical law is `F_v` for a unique `v`.
* `FormalGroup.isPTypical_iff_exists_eq_hazewinkelIntegralFormalGroup`: over such a ring, the
  `p`-typical laws are exactly Hazewinkel's.
* `TauCeti.hazewinkelLift`: the bijection between `p`-typical laws over such a ring `R` and ring
  homomorphisms `ℤ[v₁, v₂, …] →+* R`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986),
  Theorem A2.1.25.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §§2–5, and
  Chapter III, §16.
-/

public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]

/-- The inductive step: if a law over `R` becomes Hazewinkel's law `F_w` over a `ℚ`-algebra `K`
containing `R`, and `w₁, …, w_(n - 1)` lie in `R`, then so does `wₙ`. -/
private theorem exists_eq_of_map_eq_hazewinkelFormalGroup {K : Type*} [CommRing K] [Algebra ℚ K]
    {ι : R →+* K} (hι : Function.Injective ι) {F : FormalGroup R} [F.IsComm] {w : ℕ+ → K}
    (hw : F.map ι = TauCeti.hazewinkelFormalGroup p w) {u : ℕ+ → R} (n : ℕ+)
    (hu : ∀ i < n, w i = ι (u i)) : ∃ x, ι x = w n := by
  set u' : ℕ+ → R := fun i ↦ if i < n then u i else 0
  have hu' : ∀ i < n, w i = ι (u' i) := fun i hi ↦ by simp [u', hi, hu]
  have hmap : (TauCeti.hazewinkelIntegralFormalGroup p u').map ι =
      TauCeti.hazewinkelFormalGroup p (ι ∘ u') := by
    rw [TauCeti.map_hazewinkelIntegralFormalGroup,
      TauCeti.hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  -- `F` and `F_u'` agree below degree `pⁿ`, so their degree-`pⁿ` difference is `c C_(pⁿ)`
  have hord : ((p ^ (n : ℕ) : ℕ) : ℕ∞) ≤ (F.toPowerSeries -
      (TauCeti.hazewinkelIntegralFormalGroup p u').toPowerSeries).order := by
    refine nat_le_order fun d hd ↦ hι ?_
    rw [map_sub, map_sub, ← coeff_map, ← coeff_map, ← map_toPowerSeries, ← map_toPowerSeries, hw,
      hmap, map_zero, sub_eq_zero]
    refine TauCeti.coeff_hazewinkelFormalGroup_congr (N := (n : ℕ) - 1)
      (fun i hi ↦ hu' i ?_) (by rwa [Nat.sub_add_cancel n.pos])
    rw [← PNat.coe_lt_coe]
    have := n.pos
    omega
  obtain ⟨c, hc⟩ := F.exists_homogeneousComponent_sub_eq_smul_lazardCocycle _ hord
  -- over `K` the same difference is `-wₙ C_(pⁿ)`
  have hrat := TauCeti.homogeneousComponent_hazewinkelFormalGroup_sub hp.out (w := ι ∘ u') n hu'
  rw [← hw, ← hmap, map_toPowerSeries, map_toPowerSeries, ← map_sub] at hrat
  have hcoeff (e : Fin 2 →₀ ℕ) :
      (ι c + w n) * (TauCeti.lazardCocycle (p ^ (n : ℕ)) K).coeff e = 0 := by
    have h₁ := congrArg (fun x ↦ ι (coeff e x)) hc
    have h₂ := congrArg (coeff e) hrat
    have hC : (TauCeti.lazardCocycle (p ^ (n : ℕ)) K).coeff e =
        ι ((TauCeti.lazardCocycle (p ^ (n : ℕ)) R).coeff e) := by
      rw [← TauCeti.map_lazardCocycle ι, MvPolynomial.coeff_map]
    simp only [coeff_homogeneousComponent, MvPolynomial.coeff_coe, coeff_map] at h₁ h₂
    rw [hC]
    split_ifs at h₁ h₂ <;>
    · simp only [map_zero, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
        map_mul, Function.comp_apply, hC] at h₁ h₂
      simp only [u', lt_irrefl, ite_false, map_zero] at h₂
      linear_combination h₂ - h₁
  have h0 : (ι c + w n) • TauCeti.lazardCocycle (p ^ (n : ℕ)) K = 0 := by
    ext e
    rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, hcoeff]
    rfl
  rw [TauCeti.smul_lazardCocycle_eq_zero_iff
    (hp.out.two_le.trans (Nat.le_self_pow n.ne_zero p))] at h0
  exact ⟨-c, by rw [map_neg, neg_eq_iff_add_eq_zero, h0]⟩

/-- **`p`-typical laws over a ring embedding in a `ℚ`-algebra are Hazewinkel's.** If `R` embeds in
a `ℚ`-algebra, every commutative `p`-typical formal group law over `R` is
`TauCeti.hazewinkelIntegralFormalGroup p v` for some `v : ℕ+ → R`. -/
theorem IsPTypical.exists_eq_hazewinkelIntegralFormalGroup_of_injective {K : Type*} [CommRing K]
    [Algebra ℚ K] {ι : R →+* K} (hι : Function.Injective ι) {F : FormalGroup R} [F.IsComm]
    (hF : F.IsPTypical p) : ∃ v : ℕ+ → R, F = TauCeti.hazewinkelIntegralFormalGroup p v := by
  obtain ⟨w, hw⟩ := ((hF.map ι).existsUnique_eq_hazewinkelFormalGroup hp.out).exists
  -- every `wₙ` lies in the image of `ι`, by strong induction on `n`
  have key (n : ℕ+) : ∃ x, ι x = w n := by
    induction n using PNat.strongInductionOn with
    | _ n ih =>
      choose u hu using ih
      exact exists_eq_of_map_eq_hazewinkelFormalGroup hι hw
        (u := fun i ↦ if h : i < n then u i h else 0) n fun i hi ↦ by simp [hi, hu]
  choose v hv using key
  refine ⟨v, map_injective hι ?_⟩
  simp only [hw, TauCeti.map_hazewinkelIntegralFormalGroup,
    TauCeti.hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  congr 1
  funext n
  exact (hv n).symm

/-- **`p`-typical laws over `ℤ_(p)`-algebras are Hazewinkel's.** If every prime `q ≠ p` is
invertible in `R`, every commutative `p`-typical formal group law over `R` is
`TauCeti.hazewinkelIntegralFormalGroup p v` for some `v : ℕ+ → R`. -/
theorem IsPTypical.exists_eq_hazewinkelIntegralFormalGroup
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {F : FormalGroup R} [F.IsComm]
    (hF : F.IsPTypical p) : ∃ v : ℕ+ → R, F = TauCeti.hazewinkelIntegralFormalGroup p v := by
  -- `F` is classified by a ring homomorphism out of the ring of Quillen's universal `p`-typical
  -- law, a subring of the localization `S` of the Lazard ring, which embeds in a field of
  -- characteristic zero
  let S := Localization (TauCeti.LazardRing.coprimeSubmonoid p)
  have hM : TauCeti.LazardRing.coprimeSubmonoid p ≤ nonZeroDivisors TauCeti.LazardRing :=
    fun m hm ↦ by
      obtain ⟨k, hk, -, rfl⟩ := TauCeti.LazardRing.mem_coprimeSubmonoid_iff.mp hm
      exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hk)
  have : IsDomain S := IsLocalization.isDomain_localization hM
  have : CharZero S := charZero_of_injective_algebraMap (IsLocalization.injective S hM)
  have : CharZero (FractionRing S) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S))
  have hunit' (q : ℕ) (hq : q.Prime) (hqp : ¬q ∣ p) : IsUnit (q : R) :=
    hunit q hq fun h ↦ hqp (h ▸ dvd_rfl)
  obtain ⟨v, hv⟩ := (TauCeti.LazardRing.isPTypical_typicalFormalGroup p S)
    |>.exists_eq_hazewinkelIntegralFormalGroup_of_injective
      (ι := (algebraMap S (FractionRing S)).comp
        (TauCeti.LazardRing.typicalIdempotent p S).range.subtype)
      ((IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective)
  refine ⟨TauCeti.LazardRing.typicalLocalizedLift p S hunit' ⟨F, inferInstance, hF⟩ ∘ v, ?_⟩
  rw [← TauCeti.map_hazewinkelIntegralFormalGroup, ← hv,
    TauCeti.LazardRing.map_typicalLocalizedLift]

/-- **Hazewinkel's law is the universal `p`-typical law over `ℤ_(p)`-algebras.** If every prime
`q ≠ p` is invertible in `R`, every commutative `p`-typical formal group law over `R` is
`TauCeti.hazewinkelIntegralFormalGroup p v` for a unique `v : ℕ+ → R`. -/
theorem IsPTypical.existsUnique_eq_hazewinkelIntegralFormalGroup
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {F : FormalGroup R} [F.IsComm]
    (hF : F.IsPTypical p) : ∃! v : ℕ+ → R, F = TauCeti.hazewinkelIntegralFormalGroup p v :=
  let ⟨v, hv⟩ := hF.exists_eq_hazewinkelIntegralFormalGroup hunit
  ⟨v, hv, fun _ hw ↦ TauCeti.hazewinkelIntegralFormalGroup_injective p (hw.symm.trans hv)⟩

/-- If every prime `q ≠ p` is invertible in `R`, the commutative `p`-typical formal group laws over
`R` are exactly Hazewinkel's laws `TauCeti.hazewinkelIntegralFormalGroup p v`. -/
theorem isPTypical_iff_exists_eq_hazewinkelIntegralFormalGroup
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (F : FormalGroup R) [F.IsComm] :
    F.IsPTypical p ↔ ∃ v : ℕ+ → R, F = TauCeti.hazewinkelIntegralFormalGroup p v :=
  ⟨fun hF ↦ hF.exists_eq_hazewinkelIntegralFormalGroup hunit,
    fun ⟨v, hv⟩ ↦
      (isPTypical_congr hv p).mpr (TauCeti.isPTypical_hazewinkelIntegralFormalGroup p v)⟩

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
  (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- **Universal property of `ℤ[v₁, v₂, …]` for `p`-typical laws.** If every prime `q ≠ p` is
invertible in `R`, commutative `p`-typical formal group laws over `R` correspond bijectively to ring
homomorphisms `ℤ[v₁, v₂, …] →+* R`, the inverse sending `f` to the base change of
`universalHazewinkelIntegralFormalGroup p` along `f`. -/
def hazewinkelLift :
    {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p} ≃ (MvPolynomial ℕ+ ℤ →+* R) :=
  (Equiv.ofBijective
    (fun f ↦ ⟨(universalHazewinkelIntegralFormalGroup p).map f, inferInstance,
      (isPTypical_universalHazewinkelIntegralFormalGroup p).map f⟩)
    ⟨fun f g h ↦ by
      have h' := hazewinkelIntegralFormalGroup_injective p <| by
        simpa only [map_universalHazewinkelIntegralFormalGroup] using congrArg Subtype.val h
      exact MvPolynomial.ringHom_ext (fun r ↦ by simp) fun i ↦ congrFun h' i,
    fun F ↦ by
      have := F.property.1
      obtain ⟨v, hv⟩ := F.property.2.exists_eq_hazewinkelIntegralFormalGroup hunit
      exact ⟨MvPolynomial.eval₂Hom (Int.castRingHom R) v,
        Subtype.ext ((hazewinkelIntegralFormalGroup_def p v).symm.trans hv.symm)⟩⟩).symm

/-- The `p`-typical law classified by `f` is Hazewinkel's law at the images `f(vᵢ)` of the
generators, the base change of `universalHazewinkelIntegralFormalGroup p` along `f`. -/
@[simp]
theorem coe_hazewinkelLift_symm (f : MvPolynomial ℕ+ ℤ →+* R) :
    ((hazewinkelLift p hunit).symm f).val = hazewinkelIntegralFormalGroup p (f ∘ MvPolynomial.X) :=
  map_universalHazewinkelIntegralFormalGroup p f

/-- Hazewinkel's law at the images of the generators under the classifying map of `F` is `F`. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_hazewinkelLift_comp_X
    (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p}) :
    hazewinkelIntegralFormalGroup p (hazewinkelLift p hunit F ∘ MvPolynomial.X) = F.val := by
  rw [← coe_hazewinkelLift_symm p hunit, Equiv.symm_apply_apply]

/-- Hazewinkel's law at `v` is classified by evaluation at `v`. -/
@[simp]
theorem hazewinkelLift_hazewinkelIntegralFormalGroup (v : ℕ+ → R) :
    hazewinkelLift p hunit ⟨hazewinkelIntegralFormalGroup p v, inferInstance,
      isPTypical_hazewinkelIntegralFormalGroup p v⟩ =
      MvPolynomial.eval₂Hom (Int.castRingHom R) v :=
  (hazewinkelLift p hunit).eq_symm_apply.mp <| Subtype.ext <| by
    rw [coe_hazewinkelLift_symm]
    exact congrArg _ (funext fun i ↦ by simp)

end TauCeti
