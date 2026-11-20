/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion

/-!
# The first exponent of a coset theta series

For an integral lattice `L`, a dual vector `γ`, and a positive multiple `N` of the level, the
first nonzero exponent of the expansion of `θ_{γ+L}` in `q_N = exp (2π i τ / N)` is `N/2` times
the least squared norm in `γ + L`. This identifies the exponent from an actual minimum, not
merely from its residue class modulo `N`. The result holds also for odd integral lattices:
`L ≤ L^∨` places every vector of `γ + L` in `L^∨`, so the level quantizes the squared norms of
the whole coset.

The proof uses `ZLattice.qExpansion_thetaCoset_coeff`, which identifies the coefficients with
shell cardinalities, and `PowerSeries.coeff_order`, which picks out the first nonzero coefficient.
-/

public section

open UpperHalfPlane (qExpansion)

namespace ZLattice.IsIntegral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} {γ : E}

/-- The first exponent of a coset theta series in `q_N` is finite, and dividing it by `N/2`
gives the least squared norm in the coset. Here `N` is any positive multiple of the level. -/
theorem exists_qExpansion_thetaCoset_order_eq_of_level_dvd (hL : IsIntegral L) (hγ : γ ∈ dual L)
    {N : ℕ} (hN : 0 < N) (hdvd : level L ∣ N) :
    ∃ m : ℕ, (qExpansion N (thetaCoset L γ)).order = m ∧
      IsLeast (Set.range fun v : L ↦ ‖γ + (v : E)‖ ^ 2) (2 * m / N) := by
  have := hL.discreteTopology
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnorm (v : E) (hv : v ∈ L) : ∃ k : ℤ, (N : ℝ) * ‖γ + v‖ ^ 2 = 2 * k :=
    level_dvd_iff.mp hdvd _ (add_mem hγ (isIntegral_iff_le_dual.mp hL hv))
  -- Every squared norm in the coset is indexed by a natural exponent.
  have hexp (v : L) : ∃ k : ℕ, ‖γ + (v : E)‖ ^ 2 = 2 * k / N := by
    obtain ⟨k, hk⟩ := hnorm v v.property
    have hk0 : (0 : ℝ) ≤ 2 * k := hk ▸ by positivity
    have hk' : 0 ≤ k := by exact_mod_cast (by linarith : (0 : ℝ) ≤ k)
    lift k to ℕ using hk'
    exact ⟨k, (eq_div_iff hN'.ne').2 (by simpa [mul_comm] using hk)⟩
  let p := qExpansion N (thetaCoset L γ)
  -- Nonzero coefficients are exactly the norms actually represented in the coset.
  have hcoeff (k : ℕ) : p.coeff k ≠ 0 ↔
      (2 * k / N : ℝ) ∈ Set.range (fun v : L ↦ ‖γ + (v : E)‖ ^ 2) := by
    dsimp only [p]
    simp [qExpansion_thetaCoset_coeff hN' hnorm, cosetRepresentationNumber_eq_zero_iff,
      Set.Nonempty, mem_cosetShell]
  obtain ⟨k, hk⟩ := hexp 0
  have hp : p ≠ 0 := fun h ↦ (hcoeff k).2 ⟨0, hk⟩ (by simp [h])
  refine ⟨p.order.toNat, (PowerSeries.coe_toNat_order hp).symm, ?_, ?_⟩
  · exact (hcoeff _).1 (PowerSeries.coeff_order hp)
  rintro _ ⟨v, rfl⟩
  obtain ⟨j, hj⟩ := hexp v
  have hj' := PowerSeries.order_le j ((hcoeff j).2 ⟨v, hj⟩)
  have hmj : p.order.toNat ≤ j := by
    exact_mod_cast ((PowerSeries.coe_toNat_order hp).trans_le hj')
  calc
    (2 * (p.order.toNat : ℝ) / N) ≤ 2 * j / N := by gcongr
    _ = ‖γ + (v : E)‖ ^ 2 := hj.symm

/-- At the positive level of an integral lattice, the first nonzero exponent of the coset theta
series is `level L / 2` times the squared norm of a shortest vector in `γ + L`. -/
theorem order_qExpansion_level_thetaCoset (hL : IsIntegral L) (hγ : γ ∈ dual L)
    (hN : 0 < level L) :
    ∃ m : ℕ, (qExpansion (level L) (thetaCoset L γ)).order = m ∧
      IsLeast (Set.range fun v : L ↦ ‖γ + (v : E)‖ ^ 2) (2 * m / level L) :=
  hL.exists_qExpansion_thetaCoset_order_eq_of_level_dvd hγ hN dvd_rfl

end ZLattice.IsIntegral
