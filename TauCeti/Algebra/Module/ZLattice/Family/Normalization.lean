/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Gauge
public import TauCeti.Algebra.Module.ZLattice.Family.Lift

/-!
# Independence of the lift in cyclic translation normalization

Suppose a period family `P` is invariant under a base map `r`. Replacing a vector lift `β`
of a torus-valued translation by `β + P μ` changes its orbit-sum period `λ` to `λ + m • μ`.
Thus the class of `λ` modulo `mΛ` is independent of the lift. Over a preconnected base, the
comparison applies to any two continuous lifts, not just to a prescribed period change.

When `m` is invertible in the scalar field, the centered lift `β - (1/m) • P λ` is unchanged
by this replacement. Consequently its weighted cyclic correction is literally independent of
the lift. This correction conjugates the original
translation to `(1/m) • P λ`; the normalized torus translation is also independent of the
representative `λ`. These are comparisons on the actual varying period quotient, without
replacing the family by a constant torus. They supply the change-of-lift law needed when
constructing logarithmic gauges.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Chapter V, section on logarithmic transformations.
-/

public section

namespace TauCeti

section Algebra

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E) (r : Y → Y)

/-- Adding an invariant period to a lift adds `m` times that period to its orbit sum. -/
theorem birkhoffSum_add_period (hP : ∀ y, P (r y) = P y) (β : Y → E)
    (μ : Λ) (m : ℕ) (y : Y) :
    birkhoffSum r (fun y ↦ β y + P y μ) m y =
      birkhoffSum r β m y + P y (m • μ) := by
  have hadd := birkhoffSum_add_apply r β (fun y ↦ P y μ) m y
  simp only [Pi.add_def] at hadd
  rw [hadd]
  rw [birkhoffSum_apply_of_comp_eq (φ := fun y ↦ P y μ)
    (funext fun y ↦ congrArg (fun p ↦ p μ) (hP y))]
  simp

/-- For injective periods, the orbit-sum lattice vector changes by `m • μ` when the lift
changes by the period `μ`. Only one base point is needed to identify lattice vectors. -/
theorem eq_add_nsmul_of_birkhoffSum_eq_period (hP : ∀ y, P (r y) = P y)
    {β β' : Y → E} {l l' μ : Λ} {m : ℕ}
    (hβ : ∀ y, β' y = β y + P y μ)
    (hsum : ∀ y, birkhoffSum r β m y = P y l)
    (hsum' : ∀ y, birkhoffSum r β' m y = P y l')
    (y : Y) (hinj : Function.Injective (P y)) :
    l' = l + m • μ := by
  apply hinj
  rw [← hsum', funext hβ, birkhoffSum_add_period P r hP, hsum, map_add]

variable {𝕜 : Type*} [DivisionRing 𝕜] [Module 𝕜 E]

/-- Subtracting the normalized period removes the entire ambiguity in the vector lift,
not merely its ambiguity modulo periods. -/
theorem sub_inv_natCast_smul_period_add_nsmul {m : ℕ} (hm : (m : 𝕜) ≠ 0)
    (β : Y → E) (l μ : Λ) :
    (fun y ↦ (β y + P y μ) - (m : 𝕜)⁻¹ • P y (l + m • μ)) =
      (fun y ↦ β y - (m : 𝕜)⁻¹ • P y l) := by
  ext y
  simp only [map_add, map_nsmul, smul_add]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ hm]
  abel

/-- Normalized translations from representatives differing by `mΛ` are the same map on
the torus family. This comparison retains the varying periods. -/
theorem torusFamilyGauge_inv_natCast_smul_period_add_nsmul {m : ℕ}
    (hm : (m : 𝕜) ≠ 0) (l μ : Λ) :
    torusFamilyGauge P (fun y ↦ (m : 𝕜)⁻¹ • P y (l + m • μ)) =
      torusFamilyGauge P (fun y ↦ (m : 𝕜)⁻¹ • P y l) := by
  apply (torusFamilyGauge_eq_iff P _ _).2
  intro y
  simp only [map_add, map_nsmul, smul_add, add_sub_cancel_left]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ hm]
  exact LinearMap.mem_range_self (P y) μ

/-- The correction of the centered lift conjugates a cyclic translation to its normalized
period. Unlike the correction of an uncentered lift, this choice is independent of adding
periods to the lift. The base map has order dividing `m`, not necessarily exact order `m`. -/
theorem torusFamilyGauge_cyclicCorrection_centered_conj_mk
    (hP : ∀ y, P (r y) = P y) (β : Y → E) {m : ℕ} (l : Λ)
    (hperiod : r^[m] = id) (hm : (m : 𝕜) ≠ 0)
    (hsum : ∀ y, birkhoffSum r β m y = P y l)
    (F : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Y × E) → AddAction.orbitRel.Quotient Λ (Y × E))
    (hF : ∀ y v, F (Quotient.mk _ (y, v)) = Quotient.mk _ (r y, v + β y))
    (y : Y) (v : E) :
    let c := cyclicCorrection 𝕜 r (fun y ↦ β y - (m : 𝕜)⁻¹ • P y l) m
    torusFamilyGauge P c (F ((torusFamilyGauge P c).symm (Quotient.mk _ (y, v)))) =
      Quotient.mk _ (r y, v + (m : 𝕜)⁻¹ • P y l) := by
  let f := fun y ↦ β y - (m : 𝕜)⁻¹ • P y l
  have hsumf : birkhoffSum r f m y = m • (0 : E) := by
    have hsub := birkhoffSum_sub_apply r β (fun y ↦ (m : 𝕜)⁻¹ • P y l) m y
    simp only [Pi.sub_def] at hsub
    rw [hsub, hsum]
    rw [birkhoffSum_apply_of_comp_eq (funext fun y ↦ by simp [hP y])]
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_inv_smul₀ hm]
    simp
  have hc := add_cyclicCorrection_apply_sub (𝕜 := 𝕜) r f
    (congrFun hperiod y) hm hsumf
  have hnorm : β y + cyclicCorrection 𝕜 r f m (r y) - cyclicCorrection 𝕜 r f m y =
      (m : 𝕜)⁻¹ • P y l := by
    calc
      _ = (f y + cyclicCorrection 𝕜 r f m (r y) - cyclicCorrection 𝕜 r f m y) +
          (m : 𝕜)⁻¹ • P y l := by dsimp only [f]; abel
      _ = _ := by rw [hc, zero_add]
  exact (torusFamilyGauge_conj_mk P (cyclicCorrection 𝕜 r f m) β r F hF y v).trans
    (by rw [hnorm])

end Algebra

section ContinuousLifts

variable {Y Λ E : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] [Nonempty Y]
  [T2Space Y] [LocallyCompactSpace Y] [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Function.Injective (P y))
  (r : Y → Y) (hP : ∀ y, P (r y) = P y)

include hcont hinj hP

/-- Any two continuous lifts of the same torus-valued translation give orbit-sum lattice
vectors differing by `mΛ`. In particular their classes modulo `mΛ` agree. -/
theorem exists_eq_add_period_and_eq_add_nsmul_of_mk_eq_mk
    {β β' : Y → E} (hβ : Continuous β) (hβ' : Continuous β')
    (heq : ∀ y, letI := periodAddAction P
      Quotient.mk (AddAction.orbitRel Λ (Y × E)) (y, β' y) = Quotient.mk _ (y, β y))
    {m : ℕ} {l l' : Λ} (hsum : ∀ y, birkhoffSum r β m y = P y l)
    (hsum' : ∀ y, birkhoffSum r β' m y = P y l') :
    ∃ μ : Λ, (∀ y, β' y = β y + P y μ) ∧ l' = l + m • μ := by
  obtain ⟨μ, hμ⟩ := exists_eq_add_period_of_mk_eq_mk P hcont hinj continuous_id hβ hβ' heq
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact ⟨μ, hμ, eq_add_nsmul_of_birkhoffSum_eq_period P r hP hμ hsum hsum' y (hinj y)⟩

/-- The centered cyclic correction is literally the same for any two continuous lifts of
a translation with their orbit-sum periods. Hence the normalizing gauge, and its restriction
to every overlap, are independent of the lift. No choice of a representative modulo `mΛ`
is asserted to be canonical. -/
theorem cyclicCorrection_sub_period_eq_of_mk_eq_mk
    {𝕜 : Type*} [DivisionRing 𝕜] [Module 𝕜 E]
    {β β' : Y → E} (hβ : Continuous β) (hβ' : Continuous β')
    (heq : ∀ y, letI := periodAddAction P
      Quotient.mk (AddAction.orbitRel Λ (Y × E)) (y, β' y) = Quotient.mk _ (y, β y))
    {m : ℕ} (hm : (m : 𝕜) ≠ 0) {l l' : Λ}
    (hsum : ∀ y, birkhoffSum r β m y = P y l)
    (hsum' : ∀ y, birkhoffSum r β' m y = P y l') :
    cyclicCorrection 𝕜 r (fun y ↦ β' y - (m : 𝕜)⁻¹ • P y l') m =
      cyclicCorrection 𝕜 r (fun y ↦ β y - (m : 𝕜)⁻¹ • P y l) m := by
  obtain ⟨μ, hμ, hl⟩ := exists_eq_add_period_and_eq_add_nsmul_of_mk_eq_mk
    P hcont hinj r hP hβ hβ' heq hsum hsum'
  rw [funext hμ, hl, sub_inv_natCast_smul_period_add_nsmul P hm]

end ContinuousLifts

end TauCeti
