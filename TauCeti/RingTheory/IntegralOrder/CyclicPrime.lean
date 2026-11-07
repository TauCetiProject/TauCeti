/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.CyclicPrime
public import TauCeti.RingTheory.IntegralOrder.Maximal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# The maximal order of the rational group algebra of a group of prime order

Let `p` be a prime and `G` a group of order `p`, so that `G` is cyclic. Let `K` be a `p`-th
cyclotomic field and `χ : G →* K` a nontrivial character; it sends every `g ≠ 1` to a primitive
`p`-th root of unity. The map `x ↦ (ε(x), χ(x))`, where `ε` is the augmentation, is the isomorphism
of `ℚ`-algebras `TauCeti.groupAlgebraEquivProd : ℚ[G] ≃ ℚ × K` sending the averaging idempotent
`e₁ = p⁻¹ ∑_g g` to `(1, 0)`.

Under this isomorphism the integral closure of `ℤ` in `ℚ[G]` corresponds to `ℤ × 𝓞_K`, and
`𝓞_K = ℤ[ζ]` for a primitive `p`-th root of unity `ζ`. Every integral element is therefore
`P(g) + k e₁` for an integer polynomial `P` and an integer `k`, so the integral closure is the ring
`ℤ[G][e₁]` obtained by adjoining `e₁` to the group ring `ℤ[G]`. Since this integral closure is an
order and `ℚ[G]` is commutative, it is the unique maximal `ℤ`-order of `ℚ[G]`. The element `k e₁`
lies in `ℤ[G]` exactly when `p ∣ k`, so `ℤ[G]` has index `p` in the maximal order, and `ℤ[G]`
consists of the elements whose two components `(a, b) ∈ ℤ × 𝓞_K` are congruent modulo `ζ - 1`.

## Main results

* `TauCeti.IntegralOrder.mem_integralClosure_iff_groupAlgebraEquivProd_mem`: the integral closure
  of `ℤ` in `ℚ[G]` corresponds to `ℤ × 𝓞_K`.
* `TauCeti.IntegralOrder.mem_integralClosure_iff_exists_add_zsmul_average`: the integral elements
  of `ℚ[G]` are the elements `y + k e₁` with `y ∈ ℤ[G]` and `k ∈ ℤ`.
* `TauCeti.IntegralOrder.integralClosure_eq_adjoin_average`: the integral closure is `ℤ[G][e₁]`.
* `TauCeti.IntegralOrder.isMaximalOrder_iff_eq_adjoin_average`: `ℤ[G][e₁]` is the unique maximal
  `ℤ`-order of `ℚ[G]`.
* `TauCeti.IntegralOrder.relIndex_groupRingSubalgebra_integralClosure`: the group ring `ℤ[G]` has
  index `p` in the maximal order.
* `TauCeti.IntegralOrder.mem_groupRingSubalgebra_iff_groupAlgebraEquivProd`: `ℤ[G]` corresponds to
  the pairs `(a, b) ∈ ℤ × 𝓞_K` with `a ≡ b` modulo `ζ - 1`.

## References

* H. Johnston, *Notes on Galois modules*, Example 13.9.
-/

public section

open Module Polynomial MonoidAlgebra NumberField

namespace TauCeti.IntegralOrder

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [CommGroup G]

section Character

variable {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K] {χ : G →* K}
  (hG : Nat.card G = p) (hχ : χ ≠ 1)

/-- **The integral closure of `ℤ` in `ℚ[G]` corresponds to `ℤ × 𝓞_K`.** An element of `ℚ[G]` is
integral over `ℤ` exactly when its augmentation is an integer and its image under `χ` is an
algebraic integer of `K`. -/
theorem mem_integralClosure_iff_groupAlgebraEquivProd_mem {x : MonoidAlgebra ℚ G} :
    x ∈ integralClosure ℤ (MonoidAlgebra ℚ G) ↔
      groupAlgebraEquivProd K hG hχ x ∈ (⊥ : Subalgebra ℤ ℚ).prod (integralClosure ℤ K) := by
  rw [mem_integralClosure_iff,
    ← isIntegral_algEquiv ((groupAlgebraEquivProd K hG hχ).restrictScalars ℤ),
    AlgEquiv.coe_restrictScalars, IsIntegral.pair_iff, Subalgebra.mem_prod,
    mem_integralClosure_iff, Algebra.mem_bot, IsIntegrallyClosed.isIntegral_iff, Set.mem_range]

include hG hχ in
/-- Every integral element of `ℚ[G]` is `y + k e₁` with `y ∈ ℤ[G]` and `k ∈ ℤ`: its `χ`-component
lies in `𝓞_K = ℤ[χ g]`, the image of `ℤ[G]`, and `e₁ ↦ (1, 0)` corrects the augmentation. -/
private theorem exists_add_zsmul_average_eq [Fintype G] {x : MonoidAlgebra ℚ G}
    (hx : x ∈ integralClosure ℤ (MonoidAlgebra ℚ G)) :
    ∃ y ∈ groupRingSubalgebra ℤ ℚ G, ∃ k : ℤ, y + k • GroupAlgebra.average ℚ G = x := by
  set φ := groupAlgebraEquivProd K hG hχ
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hχ
  have hζ := χ.isPrimitiveRoot_apply_of_card_eq_prime hG hg
  rw [mem_integralClosure_iff_groupAlgebraEquivProd_mem hG hχ, Subalgebra.mem_prod,
    mem_integralClosure_iff] at hx
  obtain ⟨⟨a, ha⟩, hb⟩ := hx
  obtain ⟨⟨b, hb⟩, hbx⟩ :=
    (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1 hb
  have hle : Algebra.adjoin ℤ {χ g} ≤
      (groupRingSubalgebra ℤ ℚ G).map ((lift ℚ K G χ).restrictScalars ℤ) :=
    Algebra.adjoin_le <| Set.singleton_subset_iff.2
      ⟨single g 1, single_one_mem_groupRingSubalgebra g, by simp⟩
  obtain ⟨y, hy, hyb⟩ := hle hb
  -- the augmentation of `y ∈ ℤ[G]` is an integer `m`
  have hyint := (groupRing_isOrder ℤ ℚ G).le_integralClosure hy
  rw [mem_integralClosure_iff_groupAlgebraEquivProd_mem hG hχ, Subalgebra.mem_prod] at hyint
  obtain ⟨⟨m, hm⟩, -⟩ := hyint
  refine ⟨y, hy, a - m, φ.injective ?_⟩
  rw [map_add, map_zsmul, groupAlgebraEquivProd_average]
  ext
  · simp [φ, ← ha, ← hm]
  · simpa [φ, groupAlgebraEquivProd_apply] using hyb.trans hbx

end Character

/-- **The integral elements of `ℚ[G]`.** For a group `G` of prime order, the elements of `ℚ[G]`
integral over `ℤ` are exactly the elements `y + k e₁` with `y ∈ ℤ[G]`, `k ∈ ℤ`, and
`e₁ = #G⁻¹ ∑_g g` the averaging idempotent. -/
theorem mem_integralClosure_iff_exists_add_zsmul_average [Fintype G] (hG : Nat.card G = p)
    {x : MonoidAlgebra ℚ G} :
    x ∈ integralClosure ℤ (MonoidAlgebra ℚ G) ↔
      ∃ y ∈ groupRingSubalgebra ℤ ℚ G, ∃ k : ℤ, y + k • GroupAlgebra.average ℚ G = x := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have := isCyclic_of_prime_card hG
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (hG ▸ hp.out.one_lt)
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨φ, hφ⟩ := IsCyclic.exists_apply_ne_one (G' := (CyclotomicField p ℚ)ˣ)
    ⟨_, by rw [hG]; exact (IsCyclotomicExtension.zeta_spec p ℚ _).isUnit_unit hp.out.ne_zero⟩ ha
  set χ := (Units.coeHom (CyclotomicField p ℚ)).comp φ
  have hχ : χ ≠ 1 := fun h => hφ (Units.ext (DFunLike.congr_fun h a))
  refine ⟨exists_add_zsmul_average_eq hG hχ, ?_⟩
  rintro ⟨y, hy, k, rfl⟩
  have he : GroupAlgebra.average ℚ G ∈ integralClosure ℤ (MonoidAlgebra ℚ G) := by
    rw [mem_integralClosure_iff_groupAlgebraEquivProd_mem hG hχ, groupAlgebraEquivProd_average]
    exact Subalgebra.mem_prod.2 ⟨one_mem _, zero_mem _⟩
  exact add_mem ((groupRing_isOrder ℤ ℚ G).le_integralClosure hy) (zsmul_mem he k)

/-- **The integral closure of `ℤ` in `ℚ[G]` is `ℤ[G][e₁]`.** For a group `G` of prime order, it is
the subring generated by the group ring `ℤ[G]` and the averaging idempotent `e₁ = #G⁻¹ ∑_g g`. -/
theorem integralClosure_eq_adjoin_average [Fintype G] (hG : Nat.card G = p) :
    integralClosure ℤ (MonoidAlgebra ℚ G) = Algebra.adjoin ℤ
      (insert (GroupAlgebra.average ℚ G) (groupRingSubalgebra ℤ ℚ G : Set _)) := by
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨y, hy, k, rfl⟩ := (mem_integralClosure_iff_exists_add_zsmul_average hG).1 hx
    exact add_mem (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy))
      (zsmul_mem (Algebra.subset_adjoin (Set.mem_insert _ _)) k)
  · rintro x (rfl | hx)
    · exact (mem_integralClosure_iff_exists_add_zsmul_average hG).2 ⟨0, zero_mem _, 1, by simp⟩
    · exact (groupRing_isOrder ℤ ℚ G).le_integralClosure hx

/-- For a group `G` of prime order, the integral closure of `ℤ` in `ℚ[G]` is a `ℤ`-order: it is
spanned over `ℤ` by the group elements and the averaging idempotent. -/
theorem integralClosure_isOrder_of_card_eq_prime [Finite G] (hG : Nat.card G = p) :
    IsOrder ℚ (integralClosure ℤ (MonoidAlgebra ℚ G)) := by
  have := Fintype.ofFinite G
  have hle : Subalgebra.toSubmodule (integralClosure ℤ (MonoidAlgebra ℚ G)) ≤
      Submodule.span ℤ
        (insert (GroupAlgebra.average ℚ G) (Set.range fun g : G => single g (1 : ℚ))) := by
    intro x hx
    obtain ⟨y, hy, k, rfl⟩ := (mem_integralClosure_iff_exists_add_zsmul_average hG).1 hx
    rw [← Subalgebra.mem_toSubmodule, toSubmodule_groupRingSubalgebra] at hy
    exact add_mem (Submodule.span_mono (Set.subset_insert _ _) hy)
      (zsmul_mem (Submodule.subset_span (Set.mem_insert _ _)) k)
  have : Module.Finite ℤ (integralClosure ℤ (MonoidAlgebra ℚ G)) :=
    Module.Finite.iff_fg.2 ((Submodule.fg_span ((Set.finite_range _).insert _)).of_le hle)
  exact (groupRing_isOrder ℤ ℚ G).of_le (groupRing_isOrder ℤ ℚ G).le_integralClosure

/-- **The maximal order of `ℚ[G]` for `G` of prime order.** The ring `ℤ[G][e₁]` obtained by
adjoining the averaging idempotent `e₁ = #G⁻¹ ∑_g g` to the group ring is the unique maximal
`ℤ`-order of `ℚ[G]`. -/
theorem isMaximalOrder_iff_eq_adjoin_average [Fintype G] (hG : Nat.card G = p)
    {Λ : Subalgebra ℤ (MonoidAlgebra ℚ G)} :
    IsMaximalOrder ℚ Λ ↔ Λ = Algebra.adjoin ℤ
      (insert (GroupAlgebra.average ℚ G) (groupRingSubalgebra ℤ ℚ G : Set _)) := by
  rw [isMaximalOrder_iff_eq_integralClosure (integralClosure_isOrder_of_card_eq_prime hG),
    integralClosure_eq_adjoin_average hG]

/-- **The index of `ℤ[G]` in the maximal order.** For a group `G` of prime order `p`, the group ring
`ℤ[G]` has index `p` in the maximal order of `ℚ[G]`, the integral closure of `ℤ`; the quotient is
cyclic, generated by the class of the averaging idempotent `e₁`. -/
theorem relIndex_groupRingSubalgebra_integralClosure [Finite G] (hG : Nat.card G = p) :
    (Subalgebra.toSubmodule (groupRingSubalgebra ℤ ℚ G)).toAddSubgroup.relIndex
      (Subalgebra.toSubmodule (integralClosure ℤ (MonoidAlgebra ℚ G))).toAddSubgroup = p := by
  have := Fintype.ofFinite G
  set A := (Subalgebra.toSubmodule (integralClosure ℤ (MonoidAlgebra ℚ G))).toAddSubgroup
  set B := (Subalgebra.toSubmodule (groupRingSubalgebra ℤ ℚ G)).toAddSubgroup
  have he : GroupAlgebra.average ℚ G ∈ A :=
    (mem_integralClosure_iff_exists_add_zsmul_average hG).2 ⟨0, zero_mem _, 1, by simp⟩
  -- `k ↦ k e₁` maps `ℤ` onto `A / B`, with kernel `p ℤ`
  let f : ℤ →+ A ⧸ B.addSubgroupOf A := (QuotientAddGroup.mk' _).comp (zmultiplesHom A ⟨_, he⟩)
  have hf : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩⟩
    obtain ⟨y, hy, k, rfl⟩ := (mem_integralClosure_iff_exists_add_zsmul_average hG).1 hx
    refine ⟨k, QuotientAddGroup.eq.2 ?_⟩
    simpa [AddSubgroup.mem_addSubgroupOf, B] using hy
  have hker : f.ker = AddSubgroup.zmultiples (p : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, Int.mem_zmultiples_iff]
    simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, zmultiplesHom_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul, B,
      Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule,
      zsmul_average_mem_groupRingSubalgebra_iff]
    rw [← Nat.card_eq_fintype_card, hG]
  rw [AddSubgroup.relIndex, AddSubgroup.index,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker,
    ← AddSubgroup.index, Int.index_zmultiples, Int.natAbs_natCast]

section Congruence

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] {χ : G →* K}
  (hG : Nat.card G = p) (hχ : χ ≠ 1) {ζ : K} (hζ : IsPrimitiveRoot ζ p)

include hG in
/-- The components of an element of `ℤ[G]` under `ℚ[G] ≃ ℚ × K` are congruent modulo `ζ - 1`:
this holds for a group element `h ↦ (1, ζ ^ i)`, and is preserved by `ℤ`-linear combinations. -/
private theorem exists_dvd_sub_of_mem_groupRingSubalgebra {y : MonoidAlgebra ℚ G}
    (hy : y ∈ groupRingSubalgebra ℤ ℚ G) :
    ∃ (a : ℤ) (b : 𝓞 K), groupAlgebraEquivProd K hG hχ y = ((a : ℚ), (b : K)) ∧
      hζ.toInteger - 1 ∣ (a : 𝓞 K) - b := by
  rw [← Subalgebra.mem_toSubmodule, toSubmodule_groupRingSubalgebra] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (χ.apply_pow_eq_one_of_card_eq hG h)
    refine ⟨1, hζ.toInteger ^ i, by
      simp only [← hi, groupAlgebraEquivProd_single, Int.cast_one, Prod.mk.injEq, true_and,
        map_pow, ← RingOfIntegers.coe_eq_algebraMap]
      exact congrArg (· ^ i) hζ.coe_toInteger.symm, ?_⟩
    rw [Int.cast_one, ← dvd_neg, neg_sub]
    simpa using sub_dvd_pow_sub_pow hζ.toInteger 1 i
  | zero => exact ⟨0, 0, by ext <;> simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, hab, hd⟩ := hy
    obtain ⟨c, d, hcd, hd'⟩ := hz
    refine ⟨a + c, b + d, by simp [hab, hcd], ?_⟩
    convert dvd_add hd hd' using 1
    push_cast
    ring
  | smul n y _ hy =>
    obtain ⟨a, b, hab, hd⟩ := hy
    refine ⟨n * a, n * b, by ext <;> simp [hab], ?_⟩
    convert dvd_mul_of_dvd_right hd (n : 𝓞 K) using 1
    push_cast
    ring

/-- **The group ring inside `ℤ × 𝓞_K`.** Under the isomorphism `ℚ[G] ≃ ℚ × K`, the group ring
`ℤ[G]` corresponds to the pairs `(a, b) ∈ ℤ × 𝓞_K` with `a ≡ b` modulo `ζ - 1`, for any primitive
`p`-th root of unity `ζ ∈ K`. -/
theorem mem_groupRingSubalgebra_iff_groupAlgebraEquivProd [Finite G] {x : MonoidAlgebra ℚ G} :
    x ∈ groupRingSubalgebra ℤ ℚ G ↔ ∃ (a : ℤ) (b : 𝓞 K),
      groupAlgebraEquivProd K hG hχ x = ((a : ℚ), (b : K)) ∧ hζ.toInteger - 1 ∣ (a : 𝓞 K) - b := by
  have := Fintype.ofFinite G
  refine ⟨exists_dvd_sub_of_mem_groupRingSubalgebra hG hχ hζ, fun ⟨a, b, hab, hd⟩ => ?_⟩
  -- `x = y + k e₁` with `y ∈ ℤ[G]`, and the congruences for `x` and `y` give `ζ - 1 ∣ k`
  have hx : x ∈ integralClosure ℤ (MonoidAlgebra ℚ G) := by
    rw [mem_integralClosure_iff_groupAlgebraEquivProd_mem hG hχ, hab, Subalgebra.mem_prod]
    exact ⟨Subalgebra.algebraMap_mem _ a,
      (mem_integralClosure_iff _ _).2 (RingOfIntegers.isIntegral_coe b)⟩
  obtain ⟨y, hy, k, rfl⟩ := (mem_integralClosure_iff_exists_add_zsmul_average hG).1 hx
  obtain ⟨c, d, hcd, hd'⟩ := exists_dvd_sub_of_mem_groupRingSubalgebra hG hχ hζ hy
  rw [map_add, map_zsmul, groupAlgebraEquivProd_average, hcd] at hab
  simp only [Prod.smul_mk, zsmul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero,
    Prod.mk.injEq] at hab
  have hac : a = c + k := by exact_mod_cast hab.1.symm
  have hbd : b = d := RingOfIntegers.ext hab.2.symm
  have hk : hζ.toInteger - 1 ∣ (k : 𝓞 K) := by
    convert dvd_sub hd hd' using 1
    rw [hac, hbd]
    push_cast
    ring
  rw [IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ, ← hG,
    Nat.card_eq_fintype_card, ← zsmul_average_mem_groupRingSubalgebra_iff] at hk
  exact add_mem hy hk

end Congruence

end TauCeti.IntegralOrder
