/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Map

/-!
# Surjectivity of Novikov pushforward

A surjective homomorphism of exponents rescaling periods by a positive constant induces a
surjective pushforward of Novikov series, provided the coefficient map is surjective too.
In particular, quotienting exponents does not require a finite kernel. To lift a series one
chooses one representative of each exponent, rather than pulling back along the quotient:
the latter can have infinite support at a single period.
-/

public section

namespace TauCeti.NovikovSeries

open Function Set

variable {R S H H' : Type*} [AddMonoid R] [AddCommMonoid S]
  [AddZeroClass H] [AddZeroClass H'] {N : H →+ ℝ} {N' : H' →+ ℝ}

/-- Pushforward along surjective coefficient and exponent maps is surjective. The exponent
map may have infinite kernel and the period maps need not be injective or discrete. -/
theorem map_surjective (ρ : R →+ S) (φ : H →+ H')
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (hρ : Surjective ρ) (hφs : Surjective φ) : Surjective (map ρ φ hφ) := by
  classical
  obtain ⟨c, hc, hcφ⟩ := hφ
  obtain ⟨σ, hσ⟩ := hφs.hasRightInverse
  obtain ⟨τ, hτ⟩ := hρ.hasRightInverse
  intro b
  let f : H' → R := fun h => if b.coeff h = 0 then 0 else τ (b.coeff h)
  have hf (h : H') : ρ (f h) = b.coeff h := by
    simp only [f]
    split_ifs with h
    · simp [h]
    · exact hτ _
  have hf₀ (h : H') (hh : b.coeff h = 0) : f h = 0 := by simp [f, hh]
  let a : NovikovSeries R H N :=
    { coeff := extend σ f 0
      finite_lt C := by
        refine ((b.finite_lt (c * C)).image σ).subset ?_
        rintro h ⟨hh, hC⟩
        by_cases hσh : ∃ h', σ h' = h
        · obtain ⟨h', rfl⟩ := hσh
          rw [hσ.injective.extend_apply] at hh
          refine ⟨h', ⟨fun hb => hh (hf₀ h' hb), ?_⟩, rfl⟩
          have hp := hcφ (σ h')
          rw [hσ h'] at hp
          exact hp.trans_lt (mul_lt_mul_of_pos_left hC hc)
        · exact (hh (extend_apply' f (fun _ => 0) h hσh)).elim }
  have ha (h : H) : a.coeff h = extend σ f 0 h := rfl
  refine ⟨a, ?_⟩
  ext h'
  rw [← hσ h', coeff_map_of_support_inter_subset_singleton ρ φ _ a ?_]
  · rw [ha, hσ.injective.extend_apply, hf, hσ h']
  · rintro h ⟨hh, heq⟩
    by_cases hσh : ∃ k, σ k = h
    · obtain ⟨k, rfl⟩ := hσh
      simp only [mem_preimage, mem_singleton_iff] at heq
      rw [hσ k, hσ h'] at heq
      exact congrArg σ heq
    · exact (mem_support.1 hh ((ha h).trans
        (extend_apply' f (fun _ => 0) h hσh))).elim

end TauCeti.NovikovSeries
