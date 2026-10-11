/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete

/-!
# A standard fundamental domain for the rational adeles

The half-open real interval `[0, 1)` times the integral finite adeles meets each additive
coset of the diagonal copy of `ℚ` exactly once. Thus every rational adele has a unique rational
translate in this standard fundamental domain, and the translates cover the full adele ring.

We use Mathlib's unique real place of `ℚ` and its completion isomorphism with `ℝ`, together with
`FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers` for the finite part.
The half-open endpoint convention makes the representative unique.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section

open IsDedekindDomain HeightOneSpectrum NumberField
open scoped NumberField.AdeleRing

namespace NumberField.AdeleRing

/-- The real component of a rational adele, using the unique infinite place of `ℚ`. -/
noncomputable def ratRealComponent : 𝔸[ℚ] →+* ℝ :=
  (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).comp
    ((Pi.evalRingHom (fun w : InfinitePlace ℚ ↦ w.Completion) Rat.infinitePlace).comp
      (RingHom.fst _ _))

/-- The real component is the real completion embedding at the unique infinite place. -/
theorem ratRealComponent_apply (a : 𝔸[ℚ]) :
    ratRealComponent a =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (a.1 Rat.infinitePlace) :=
  (rfl)

end NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

/-- The standard fundamental domain for the additive rational adele quotient: the real
component lies in `[0, 1)` and every finite component is integral. -/
noncomputable def ratFundamentalDomain : Set 𝔸[ℚ] :=
  {a | AdeleRing.ratRealComponent a ∈ Set.Ico 0 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ), a.2 v ∈ v.adicCompletionIntegers ℚ}

/-- Membership in the standard rational adele fundamental domain. -/
@[simp]
theorem mem_ratFundamentalDomain_iff (a : 𝔸[ℚ]) :
    a ∈ ratFundamentalDomain ↔ AdeleRing.ratRealComponent a ∈ Set.Ico 0 1 ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), a.2 v ∈ v.adicCompletionIntegers ℚ :=
  (Iff.rfl)

private theorem exists_sub_algebraMap_mem_ratFundamentalDomain (a : 𝔸[ℚ]) :
    ∃ q : ℚ, a - algebraMap ℚ 𝔸[ℚ] q ∈ ratFundamentalDomain := by
  obtain ⟨q, hq⟩ :=
    FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers a.2
  let n : ℤ := toIcoDiv (show 0 < (1 : ℝ) by norm_num) 0
    (AdeleRing.ratRealComponent a - (q : ℝ))
  refine ⟨q + (n : ℚ), ?_, ?_⟩
  · simp only [map_sub, RingHom.map_rat_algebraMap, eq_ratCast, Rat.cast_add,
      Rat.cast_intCast, sub_add_eq_sub_sub]
    simpa only [zsmul_eq_mul, mul_one, zero_add] using
      sub_toIcoDiv_zsmul_mem_Ico (show 0 < (1 : ℝ) by norm_num) 0
        (AdeleRing.ratRealComponent a - (q : ℝ))
  · intro v
    have hn : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) ∈
        v.adicCompletionIntegers ℚ := by
      rw [← Rat.ringOfIntegersEquiv_symm_apply_coe n]
      exact v.coe_mem_adicCompletionIntegers (Rat.ringOfIntegersEquiv.symm n)
    -- `AdeleRing` is a product synonym; expose its finite component to use the local ring API.
    change a.2 v - algebraMap ℚ (v.adicCompletion ℚ) (q + (n : ℚ)) ∈
      v.adicCompletionIntegers ℚ
    simpa only [map_add, sub_add_eq_sub_sub] using sub_mem (hq v) hn

private theorem sub_algebraMap_mem_ratFundamentalDomain_unique (a : 𝔸[ℚ]) {q r : ℚ}
    (hq : a - algebraMap ℚ 𝔸[ℚ] q ∈ ratFundamentalDomain)
    (hr : a - algebraMap ℚ 𝔸[ℚ] r ∈ ratFundamentalDomain) : q = r := by
  obtain ⟨hqinf, hqfin⟩ := hq
  obtain ⟨hrinf, hrfin⟩ := hr
  have hinf : |((q - r : ℚ) : ℝ)| < 1 := by
    simp only [map_sub, RingHom.map_rat_algebraMap, eq_ratCast,
      Set.mem_Ico] at hqinf hrinf
    rw [Rat.cast_sub, abs_lt]
    constructor <;> linarith [hqinf.1, hqinf.2, hrinf.1, hrinf.2]
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_norm_lt_one_of_mem_integralAdeles
  · intro w
    -- The completion's field coercion uses `WithAbs`, whereas rational casts use its ring API.
    change ‖(WithAbs.toAbs w.1 (q - r) : w.Completion)‖ < 1
    rw [InfinitePlace.Completion.norm_coe]
    simpa using hinf
  · refine FiniteAdeleRing.mem_integralAdeles.mpr fun v ↦ ?_
    have hv := sub_mem (hrfin v) (hqfin v)
    -- Expose the finite components of the product synonym before the local additive calculation.
    change (a.2 v - algebraMap ℚ (v.adicCompletion ℚ) r) -
      (a.2 v - algebraMap ℚ (v.adicCompletion ℚ) q) ∈ v.adicCompletionIntegers ℚ at hv
    change algebraMap ℚ (v.adicCompletion ℚ) (q - r) ∈ v.adicCompletionIntegers ℚ
    convert hv using 1
    rw [map_sub]
    abel

/-- Each rational adele has a unique rational translate in the standard fundamental domain. -/
theorem existsUnique_sub_algebraMap_mem_ratFundamentalDomain (a : 𝔸[ℚ]) :
    ∃! q : ℚ, a - algebraMap ℚ 𝔸[ℚ] q ∈ ratFundamentalDomain := by
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_mem_ratFundamentalDomain a
  exact ⟨q, hq, fun r hr ↦ sub_algebraMap_mem_ratFundamentalDomain_unique a hr hq⟩

/-- The rational translates of the standard fundamental domain cover the full rational adele
ring. -/
theorem iUnion_ratFundamentalDomain_add_algebraMap :
    (⋃ q : ℚ, (fun a : 𝔸[ℚ] ↦ a + algebraMap ℚ 𝔸[ℚ] q) '' ratFundamentalDomain) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨q, hq, -⟩ := existsUnique_sub_algebraMap_mem_ratFundamentalDomain a
  exact Set.mem_iUnion.mpr ⟨q, a - algebraMap ℚ 𝔸[ℚ] q, hq, sub_add_cancel _ _⟩

end TauCeti.GlobalNumberFields
