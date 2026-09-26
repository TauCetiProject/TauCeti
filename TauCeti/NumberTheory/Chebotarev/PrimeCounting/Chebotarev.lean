/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt
import TauCeti.Algebra.Group.Conj
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.Chebotarev.AuxiliaryPrime
import TauCeti.NumberTheory.Chebotarev.Crossing.CrossingConstant
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Cyclotomic
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FixedFieldContraction
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Partition
import TauCeti.NumberTheory.Chebotarev.PrimeCounting.Tower
import TauCeti.NumberTheory.Chebotarev.TaggedFixedField
import TauCeti.Topology.Algebra.Order.LiminfLimsup

/-!
# The Chebotarev density theorem, for Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`, and let `C` be a
conjugacy class of `G`. This file proves the prime-number-theorem form of Chebotarev's theorem,

```text
ψ_C(x) = (#C / #G) x + o(x),
```

where `ψ_C = frobeniusPsi K L C` sums `log N𝔭` over the prime powers `𝔭 ^ j` of `K` with `𝔭`
unramified in `L` and `Frob(𝔭) ^ j ∈ C`.

The proof is the weighted form of the cyclotomic crossing behind
`NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet`; in particular, the tagged-class
crossing follows the proof of `NumberField.Chebotarev.hasDirichletDensity_abelianFrobenius`.

* For abelian `G` and `σ ∈ G` of order `f`, pick an auxiliary prime `q` with `f ^ r ∣ q - 1`
  and cross with `M = L(μ_q)`, so that `Gal(M/K) ≃ G × (ZMod q)ˣ`. For each tag `τ` with
  `f ∣ orderOf τ`, the field `E_τ` fixed by `(σ, τ)` has `M` as a `q`-th cyclotomic extension,
  so the cyclotomic weighted theorem over `E_τ` and the contraction across the cyclic fixed field
  give `ψ_{(σ, τ)}(x) = x / #Gal(M/K) + o(x)` over `K`. The tagged classes are distinct classes
  over the class of `σ`, so their `ψ` functions add up to at most `ψ_σ`: for a fixed `q`, the
  limit in `x` gives `liminf ψ_σ(x) / x ≥ (1 - 2 ^ (-r)) ^ #f.primeFactors / #G`, and only then
  does `r` grow, giving `liminf ψ_σ(x) / x ≥ 1 / #G`.
* The `ψ` functions of all classes add up to `ψ_K(x) = x + o(x)` up to `O(log x)`, so these
  lower bounds saturate the total and each of them is the limit.
* For a general class `C ∋ σ`, the extension `L / L ^ ⟨σ⟩` is cyclic, and the contraction across
  the cyclic fixed field carries the abelian result down to `C`.

## Main results

* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_mul_comm`: for abelian `G` and `σ ∈ G`,
  `ψ_σ(x) = x / #G + o(x)`.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic`: for every conjugacy class `C` of `G`,
  `ψ_C(x) = (#C / #G) x + o(x)`.
* `NumberField.Chebotarev.tendsto_frobeniusPsi`: the same, as `ψ_C(x) / x → #C / #G`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
* H. W. Lenstra Jr. and P. Stevenhagen, "Chebotarëv and his density theorem",
  *Math. Intelligencer* 18 (1996), 26–37, for the cyclotomic crossing.
-/

open Asymptotics Filter NumberField TauCeti TauCeti.NumberField.Chebotarev
open scoped NumberField Topology

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- **One auxiliary prime.** In an abelian extension, the Frobenius `ψ` of `σ` eventually exceeds
-- `δ x` for every `δ` below `(1 - 2 ^ (-r)) ^ #(orderOf σ).primeFactors / #G`, for every `r ≥ 1`.
private theorem eventually_lt_frobeniusPsi_div_of_mul_comm
    (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (σ : L ≃ₐ[K] L) {r : ℕ} (hr : 0 < r) {δ : ℝ}
    (hδ : δ < (1 - (2 : ℝ) ^ (-(r : ℤ))) ^ (orderOf σ).primeFactors.card /
      (Nat.card (L ≃ₐ[K] L) : ℝ)) :
    ∀ᶠ x in atTop, δ < frobeniusPsi K L (ConjClasses.mk σ) x / x := by
  classical
  set f := orderOf σ
  -- Cross with `M = L(μ_q)` for a prime `q` with `f ^ r ∣ q - 1` and `|disc L| < q`; then
  -- `Gal(M/K) ≃ Gal(L/K) × (ZMod q)ˣ`.
  obtain ⟨q, hq, hqN, -, hfq, -, -, -⟩ := exists_auxiliaryPrime K L (f ^ r) (discr L).natAbs
    (pow_ne_zero _ (orderOf_pos σ).ne')
  have : Fact q.Prime := ⟨hq⟩
  have hcop : (discr L).natAbs.Coprime q :=
    (Nat.coprime_of_lt_prime (Int.natAbs_ne_zero.mpr (discr_ne_zero L)) hqN hq).symm
  let M := CyclotomicField q L
  have hζ := IsCyclotomicExtension.zeta_spec q L M
  have : IsGalois K M := IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension K L M q
  set e := IsCyclotomicExtension.galEquivProd K L M q hcop hζ
  have hcard : Nat.card (M ≃ₐ[K] M) = Nat.card (L ≃ₐ[K] L) * Nat.card (ZMod q)ˣ := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have hcomm (ρ ρ' : M ≃ₐ[K] M) : ρ * ρ' = ρ' * ρ :=
    e.injective (by rw [map_mul, map_mul, Prod.mul_def, Prod.mul_def, hab, mul_comm (e ρ).2])
  -- Each tagged class has the weighted asymptotic of one element of `Gal(M/K)`: for a tag `τ`,
  -- the field fixed by `(σ, τ)` has `M` as a `q`-th cyclotomic extension, so the cyclotomic
  -- weighted theorem and the fixed-field contraction apply, and `(σ, τ)` is central, so its class
  -- is a singleton.
  have hψ (τ : (ZMod q)ˣ) (hτ : τ ∈ taggedElements f) :
      Tendsto (fun x ↦ frobeniusPsi K M (ConjClasses.mk (e.symm (σ, τ))) x / x) atTop
        (𝓝 (1 / ((Nat.card (L ≃ₐ[K] L) : ℝ) * Nat.card (ZMod q)ˣ))) := by
    have := TauCeti.fixedField_zpowers_isCyclotomicExtension K L M q hcop hζ σ τ
      (mem_taggedElements_iff.mp hτ)
    have h := frobeniusPsi_asymptotic_of_fixedField _ _ ConjClasses.mem_carrier_mk <|
      AlgEquiv.card_algEquiv_fixedField_zpowers (e.symm (σ, τ)) ▸
        frobeniusPsi_asymptotic_of_isCyclotomicExtension _ M q
          (e.symm (σ, τ)).toFixedFieldAlgEquiv
    rw [Nat.card_coe_set_eq, ConjClasses.ncard_carrier_mk_of_mem_center
      (Subgroup.mem_center_iff.mpr fun ρ ↦ hcomm ρ _), hcard, Nat.cast_one, Nat.cast_mul] at h
    exact (isLittleO_sub_mul_iff_tendsto_div (eventually_ne_atTop 0)).mp h
  -- Summed over the tags, the limits add up to the crossing constant.
  have hsum : Tendsto (fun x ↦ ∑ τ ∈ taggedElements f,
      frobeniusPsi K M (ConjClasses.mk (e.symm (σ, τ))) x / x) atTop
        (𝓝 (crossingConstant K L (H := (ZMod q)ˣ) f)) := by
    rw [crossingConstant_def, div_eq_mul_one_div, ← nsmul_eq_mul, ← Finset.sum_const]
    exact tendsto_finsetSum _ hψ
  have hf : f ^ r ∣ Nat.card (ZMod q)ˣ := by
    rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
  -- Distinct tags give distinct classes of `Gal(M/K)`, all over the class of `σ`.
  have hinj : Set.InjOn (fun τ : (ZMod q)ˣ ↦ ConjClasses.mk (e.symm (σ, τ)))
      (taggedElements (H := (ZMod q)ˣ) f : Set (ZMod q)ˣ) := fun τ _ υ _ h ↦ by
    have hconj := (hζ.autToPow K).map_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp h)
    apply isConj_iff_eq.mp
    simpa only [e, IsCyclotomicExtension.autToPow_galEquivProd_symm] using hconj
  have hover : ∀ D ∈ (taggedElements f).image fun τ : (ZMod q)ˣ ↦ ConjClasses.mk (e.symm (σ, τ)),
      ConjClasses.map (AlgEquiv.restrictNormalHom L) D = ConjClasses.mk σ := by
    simp only [Finset.mem_image]
    rintro _ ⟨τ, -, rfl⟩
    rw [ConjClasses.map_mk, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
      IsCyclotomicExtension.restrictNormal_galEquivProd_symm]
  filter_upwards [(tendsto_order.1 hsum).1 δ (hδ.trans_le (le_crossingConstant K L f r hr hf)),
    eventually_gt_atTop 0] with x hx hx0
  refine hx.trans_le ?_
  rw [← Finset.sum_div, ← Finset.sum_image (f := fun D ↦ frobeniusPsi K M D x) hinj]
  gcongr
  exact sum_frobeniusPsi_le_frobeniusPsi _ _ hover x

-- Letting the level of the auxiliary prime grow: in an abelian extension, the Frobenius `ψ` of
-- `σ` eventually exceeds `δ x` for every `δ < 1 / #G`.
private theorem eventually_lt_frobeniusPsi_div_one_div_card_of_mul_comm
    (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (σ : L ≃ₐ[K] L) {δ : ℝ}
    (hδ : δ < 1 / (Nat.card (L ≃ₐ[K] L) : ℝ)) :
    ∀ᶠ x in atTop, δ < frobeniusPsi K L (ConjClasses.mk σ) x / x := by
  -- The bound of one auxiliary prime tends to `1 / #G` as its level grows.
  have h2 : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ (-(r : ℤ))) atTop (𝓝 0) := by
    simpa [zpow_neg, zpow_natCast, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub h2).pow
    (orderOf σ).primeFactors.card).div_const (Nat.card (L ≃ₐ[K] L) : ℝ)
  rw [sub_zero, one_pow] at hlim
  obtain ⟨r, hr, hδr⟩ := ((eventually_gt_atTop 0).and (hlim.eventually (lt_mem_nhds hδ))).exists
  exact eventually_lt_frobeniusPsi_div_of_mul_comm hab σ hr hδr

public section

/-- **Weighted Chebotarev for abelian extensions.** If `Gal(L/K)` is abelian, then for every
`σ ∈ Gal(L/K)` the Frobenius `ψ` function of `σ` satisfies `ψ_σ(x) = x / #Gal(L/K) + o(x)`. -/
theorem frobeniusPsi_asymptotic_of_mul_comm (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (σ : L ≃ₐ[K] L) :
    (fun x : ℝ ↦ frobeniusPsi K L (ConjClasses.mk σ) x -
      (1 / Nat.card (L ≃ₐ[K] L) : ℝ) * x) =o[atTop] fun x : ℝ ↦ x := by
  classical
  rw [isLittleO_sub_mul_iff_tendsto_div (eventually_ne_atTop 0)]
  -- In an abelian group the conjugacy classes are the elements.
  have hmk : Function.Bijective (ConjClasses.mk : (L ≃ₐ[K] L) → ConjClasses (L ≃ₐ[K] L)) := by
    refine ⟨fun ρ ρ' h ↦ ?_, ConjClasses.mk_surjective⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
    rw [← hc, hab c, mul_inv_cancel_right]
  -- The Frobenius `ψ` functions of all classes add up to `ψ_K(x) = x + o(x)`, up to `O(log x)`.
  have htotal : Tendsto (fun x ↦ ∑ ρ : L ≃ₐ[K] L, frobeniusPsi K L (ConjClasses.mk ρ) x / x)
      atTop (𝓝 (∑ _ρ : L ≃ₐ[K] L, 1 / (Nat.card (L ≃ₐ[K] L) : ℝ))) := by
    have h : (fun x ↦ ∑ C : ConjClasses (L ≃ₐ[K] L), frobeniusPsi K L C x - 1 * x)
        =o[atTop] fun x : ℝ ↦ x :=
      ((primePsi_univ_asymptotic K).sub
        ((primePsi_univ_sub_sum_frobeniusPsi_isBigO_log K L).trans_isLittleO
          Real.isLittleO_log_id_atTop)).congr_left fun x ↦ by ring
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      mul_one_div_cancel (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
    refine ((isLittleO_sub_mul_iff_tendsto_div (eventually_ne_atTop 0)).mp h).congr fun x ↦ ?_
    rw [← Finset.sum_div, Fintype.sum_bijective _ hmk
      (fun ρ ↦ frobeniusPsi K L (ConjClasses.mk ρ) x) (fun C ↦ frobeniusPsi K L C x) fun _ ↦ rfl]
  -- Every class has lower asymptotic density `1 / #G`, and these bounds saturate the total.
  exact tendsto_of_forall_eventually_lt_of_eventually_sum_lt (s := Finset.univ)
    (f := fun ρ x ↦ frobeniusPsi K L (ConjClasses.mk ρ) x / x)
    (fun ρ _ _ hb ↦ eventually_lt_frobeniusPsi_div_one_div_card_of_mul_comm hab ρ hb)
    (tendsto_order.1 htotal).2 (Finset.mem_univ σ)

variable (K L) in
/-- **The Chebotarev density theorem, for Chebyshev's `ψ`.** For a finite Galois extension `L / K`
of number fields and a conjugacy class `C` of `Gal(L/K)`, the Frobenius `ψ` function of `C`
satisfies `ψ_C(x) = (#C / #Gal(L/K)) x + o(x)`. -/
theorem frobeniusPsi_asymptotic (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x : ℝ ↦ frobeniusPsi K L C x -
      (Nat.card C.carrier / Nat.card (L ≃ₐ[K] L) : ℝ) * x) =o[atTop] fun x : ℝ ↦ x := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  refine frobeniusPsi_asymptotic_of_fixedField _ σ ConjClasses.mem_carrier_mk ?_
  -- `Gal(L / L ^ ⟨σ⟩)` is generated by `σ`, so it is cyclic and hence abelian.
  have : IsCyclic (L ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨_, AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top σ⟩
  exact AlgEquiv.card_algEquiv_fixedField_zpowers σ ▸ frobeniusPsi_asymptotic_of_mul_comm
    IsCyclic.commGroup.mul_comm σ.toFixedFieldAlgEquiv

variable (K L) in
/-- **The Chebotarev density theorem, for Chebyshev's `ψ`, as a limit.** For a finite Galois
extension `L / K` of number fields and a conjugacy class `C` of `Gal(L/K)`,
`ψ_C(x) / x → #C / #Gal(L/K)`. -/
theorem tendsto_frobeniusPsi (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto (fun x : ℝ ↦ frobeniusPsi K L C x / x) atTop
      (𝓝 ((Nat.card C.carrier : ℝ) / (Nat.card (L ≃ₐ[K] L) : ℝ))) :=
  (isLittleO_sub_mul_iff_tendsto_div (eventually_ne_atTop 0)).mp (frobeniusPsi_asymptotic K L C)

end

end NumberField.Chebotarev
