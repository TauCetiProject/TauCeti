/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.MulIndicator

/-!
# The finite idele for a Weil lattice

Suppose an integral relative different generator `x` is associated to its conjugate, and the
primes dividing `x` divide either `β` or its conjugate, which are coprime. Put `x⁻¹` at
the primes dividing `β` and `1` elsewhere. The resulting finite idele and its conjugate
multiply to `x⁻¹` up to local integer units. A multiple of `x` clears its denominators.

The normalization follows `New.Parameters.α` and
`New.Parameters.v_alpha_mul_star_mul_relDifferentGen` in `New/Derivatives/Field/WeilData.lean`
of lsernau/grh-lean (commit `72fead1`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
open scoped NumberField.AdeleRing

namespace TauCeti

open GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E]

open Classical in
/-- An inverse diagonal component selected by ideal membership is transported to the
corresponding component selected by membership of the conjugate integer. -/
private theorem finiteAdeleEquiv_mulIndicator_inv_apply (σ : E ≃+* E) (β : 𝓞 E) (x : E)
    (v : HeightOneSpectrum (𝓞 E)) :
    finiteAdeleEquiv E E σ
        (mulIndicator {w | β ∈ w.asIdeal} (algebraMap E 𝔸ᶠ[E] x⁻¹)) v =
      if RingOfIntegers.mapRingEquiv σ β ∈ v.asIdeal then
        (algebraMap E 𝔸ᶠ[E] (σ x)⁻¹) v else 1 := by
  rw [finiteAdeleEquiv_apply, mulIndicator_apply]
  split_ifs with h h' h'
  · simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.adicCompletionExtension_coe]
    exact congrArg (fun y : E ↦ (y : v.adicCompletion E)) (map_inv₀ σ x)
  · simp only [Set.mem_ofPred_eq, HeightOneSpectrum.under_asIdeal, Ideal.under,
      Ideal.mem_comap] at h
    exact (h' h).elim
  · exfalso
    apply h
    simp only [Set.mem_ofPred_eq, HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap]
    exact h'
  · exact map_one _

/-- Compute the valuation of the product with the conjugate at one place. -/
private theorem valued_mulIndicator_mul_conj_mul_eq_one (σ : E ≃+* E) {β x : 𝓞 E}
    (hβ : IsCoprime β (RingOfIntegers.mapRingEquiv σ β))
    (hassoc : Associated (RingOfIntegers.mapRingEquiv σ x) x)
    (hxE : (x : E) ≠ 0) (v : HeightOneSpectrum (𝓞 E))
    (hsupport : x ∈ v.asIdeal → β * RingOfIntegers.mapRingEquiv σ β ∈ v.asIdeal) :
    let a := mulIndicator {w | β ∈ w.asIdeal} (algebraMap E 𝔸ᶠ[E] (x : E)⁻¹)
    Valued.v ((a * finiteAdeleEquiv E E σ a * algebraMap (𝓞 E) 𝔸ᶠ[E] x) v) = 1 := by
  classical
  let b := RingOfIntegers.mapRingEquiv σ β
  intro a
  dsimp only [a]
  rw [FiniteAdeleRing.mul_apply, FiniteAdeleRing.mul_apply, mulIndicator_apply,
    finiteAdeleEquiv_mulIndicator_inv_apply, IsScalarTower.algebraMap_apply (𝓞 E) E]
  simp only [FiniteAdeleRing.algebraMap_apply]
  have hval : v.valuation E (x : E) ≠ 0 := (Valuation.ne_zero_iff _).2 hxE
  have hconj : v.valuation E (σ (x : E)) = v.valuation E (x : E) := by
    obtain ⟨u, hu⟩ := hassoc
    have he := congrArg (algebraMap (𝓞 E) E) hu
    rw [map_mul] at he
    -- The algebra map from the ring of integers to its field is its coercion.
    change ((RingOfIntegers.mapRingEquiv σ x : 𝓞 E) : E) * (u : 𝓞 E) = (x : E) at he
    rw [RingOfIntegers.mapRingEquiv_apply] at he
    have huval := (v.valuation_eq_one_iff_notMem (K := E) (r := (u : 𝓞 E))).mpr
      (fun hm ↦ v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm u.isUnit))
    calc
      _ = v.valuation E (σ (x : E) * (u : 𝓞 E)) := by rw [map_mul, huval, mul_one]
      _ = _ := congrArg (v.valuation E) he
  have hnot : ¬ (β ∈ v.asIdeal ∧ b ∈ v.asIdeal) := by
    rintro ⟨h₁, h₂⟩
    obtain ⟨a, c, hac⟩ := hβ
    exact v.isPrime.ne_top (v.asIdeal.eq_top_of_isUnit_mem
      (hac ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h₁) (v.asIdeal.mul_mem_left c h₂))
      isUnit_one)
  have hunit (h₁ : β ∉ v.asIdeal) (h₂ : b ∉ v.asIdeal) :
      v.valuation E (x : E) = 1 :=
    v.valuation_eq_one_iff_notMem.mpr fun hxv ↦ (v.isPrime.mem_or_mem (hsupport hxv)).elim h₁ h₂
  by_cases h₁ : β ∈ v.asIdeal <;> by_cases h₂ : b ∈ v.asIdeal
  · exact (hnot ⟨h₁, h₂⟩).elim
  · simp [b, h₁, h₂, map_inv₀, hval]
  · simp [b, h₁, h₂, map_inv₀, hconj, hval]
  · simp [b, h₁, h₂, hunit h₁ h₂]

open Classical in
/-- Construct the finite idele with component `x⁻¹` at the primes containing `β` and `1` at
all other primes. Its inverse is integral, any integral multiple `n` of `x` clears its
denominators, and its product with its conjugate and `x` has valuation one at every place.
Here `Valued.v` is multiplicative, so valuation one means an integer unit. -/
theorem _root_.RingEquiv.exists_weilFiniteIdele (σ : E ≃+* E) {β x n : 𝓞 E}
    (hβ : IsCoprime β (RingOfIntegers.mapRingEquiv σ β))
    (hassoc : Associated (RingOfIntegers.mapRingEquiv σ x) x)
    (hsupport : β * RingOfIntegers.mapRingEquiv σ β ∈ (Ideal.span {x}).radical) (hn : x ∣ n) :
    ∃ α : 𝔸ᶠ[E]ˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), (α : 𝔸ᶠ[E]) v =
        if β ∈ v.asIdeal then ((x : E)⁻¹ : v.adicCompletion E) else 1) ∧
      (↑(α⁻¹) : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E ∧
      algebraMap (𝓞 E) 𝔸ᶠ[E] n * (α : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E ∧
      ∀ v : HeightOneSpectrum (𝓞 E),
        Valued.v (((α : 𝔸ᶠ[E]) * finiteAdeleEquiv E E σ ↑α * algebraMap (𝓞 E) 𝔸ᶠ[E] x) v) =
          1 := by
  let S : Set (HeightOneSpectrum (𝓞 E)) := {v | β ∈ v.asIdeal}
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hsupport
  have hβ₀ : β ≠ 0 := by
    intro h
    subst β
    simpa using hβ.ne_zero_or_ne_zero
  have hx : x ≠ 0 := by
    rintro rfl
    have hb₀ : RingOfIntegers.mapRingEquiv σ β ≠ 0 := fun h ↦
      hβ₀ ((RingOfIntegers.mapRingEquiv σ).injective (h.trans (map_zero _).symm))
    apply pow_ne_zero k (mul_ne_zero hβ₀ hb₀)
    rwa [Ideal.span_singleton_zero, Ideal.mem_bot] at hk
  have hxE : (x : E) ≠ 0 := by exact_mod_cast hx
  let μ := (Units.map (mulIndicator (K := E) S)).comp (unitEmbedding (𝓞 E) E)
  let α := μ (Units.mk0 (x : E) hxE)⁻¹
  have hα : (α : 𝔸ᶠ[E]) = mulIndicator S (algebraMap E 𝔸ᶠ[E] (x : E)⁻¹) := (rfl)
  have hαinv : (↑(α⁻¹) : 𝔸ᶠ[E]) = mulIndicator S (algebraMap E 𝔸ᶠ[E] (x : E)) := by
    simp [α, μ]
  refine ⟨α, fun v ↦ ?_, ?_, ?_, ?_⟩
  · rw [hα, mulIndicator_apply]
    -- Use the algebra map to the completion to transport inversion inside the selected component.
    change (if β ∈ v.asIdeal then algebraMap E (v.adicCompletion E) (x : E)⁻¹ else 1) = _
    rw [map_inv₀]
    rfl
  · rw [hαinv, mulIndicator_mem_integralAdeles]
    exact fun v _ ↦ v.coe_mem_adicCompletionIntegers (K := E) x
  · obtain ⟨c, rfl⟩ := hn
    rw [hα, mem_integralAdeles]
    intro v
    rw [FiniteAdeleRing.mul_apply, mulIndicator_apply]
    -- Express diagonal components using the same two algebra maps into the completion.
    change (algebraMap E (v.adicCompletion E) ((x * c : 𝓞 E) : E) *
      (if v ∈ S then algebraMap E (v.adicCompletion E) (x : E)⁻¹ else 1)) ∈ _
    split_ifs
    · have he : algebraMap (𝓞 E) E (x * c) * (x : E)⁻¹ = (c : E) := by
        rw [map_mul (algebraMap (𝓞 E) E), mul_comm (x : E), mul_assoc,
          mul_inv_cancel₀ hxE, mul_one]
      rw [← map_mul, he]
      exact v.coe_mem_adicCompletionIntegers (K := E) c
    · rw [mul_one]
      exact v.coe_mem_adicCompletionIntegers (K := E) (x * c)
  · intro v
    rw [hα]
    exact valued_mulIndicator_mul_conj_mul_eq_one σ hβ hassoc hxE v fun hv ↦
      v.isPrime.mem_of_pow_mem k ((Ideal.span_le.mpr (by simpa using hv)) hk)

end TauCeti
