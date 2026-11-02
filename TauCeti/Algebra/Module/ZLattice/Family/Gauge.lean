/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Geometry.Manifold.ContMDiff.CyclicCorrection

/-!
# Translation gauges and cyclic normalization on a family of tori

A vector-valued section `c : Y → E` changes fibre coordinates on the period quotient by
`[y, v] ↦ [y, v + c y]`. The equivalence `torusFamilyGauge` has inverse given by `-c`, preserves
the projection, and depends only on `c` modulo periods. For a `C^n` family and section it is the
`C^n` diffeomorphism `torusFamilyGaugeDiffeomorph`; over the complex numbers this includes
biholomorphic coordinate changes.

If a map of the family is represented by `[y, v] ↦ [r y, v + β y]`, conjugating by this gauge
replaces `β` by `β + c ∘ r - c`. When `r` is cyclic of period dividing `m` and the orbit sum of
`β` is the period `P y λ`, finite cyclic averaging therefore conjugates the map to
`[y, v] ↦ [r y, v + (1/m) • P y λ]`. The period family remains varying throughout. The theorem
takes a vector lift and its orbit-sum equation as input; it does not assert existence of a lift
for an arbitrary torus-valued section.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Chapter V, section on logarithmic transformations.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section Algebra

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E)

/-- Changing fibre coordinates by a vector-valued section, `[y, v] ↦ [y, v + c y]`.
Its inverse is the coordinate change by `-c`. -/
def torusFamilyGauge (c : Y → E) :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × E) ≃ AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction P
  letI := torusFamilyTranslationAddAction P
  { toFun := fun x ↦ c (torusFamilyProjection P x) +ᵥ x
    invFun := fun x ↦ -c (torusFamilyProjection P x) +ᵥ x
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

/-- A translation gauge acts by fibrewise translation at the point's base. -/
theorem torusFamilyGauge_apply (c : Y → E)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    letI := torusFamilyTranslationAddAction P
    torusFamilyGauge P c x = c (torusFamilyProjection P x) +ᵥ x := (rfl)

/-- On representatives a translation gauge adds the section to the vector coordinate. -/
@[simp] theorem torusFamilyGauge_mk (c : Y → E) (y : Y) (v : E) :
    torusFamilyGauge P c (Quotient.mk _ (y, v)) = Quotient.mk _ (y, v + c y) := by
  simp [torusFamilyGauge_apply, add_comm]

/-- Translation gauges preserve the family projection. -/
@[simp] theorem torusFamilyProjection_gauge (c : Y → E)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyProjection P (torusFamilyGauge P c x) = torusFamilyProjection P x := by
  let _ := torusFamilyTranslationAddAction P
  simp [torusFamilyGauge_apply]

/-- The inverse coordinate change subtracts the section. -/
@[simp] theorem torusFamilyGauge_symm (c : Y → E) :
    (torusFamilyGauge P c).symm = torusFamilyGauge P (-c) := by
  let _ := torusFamilyTranslationAddAction P
  apply Equiv.ext
  intro x
  apply (torusFamilyGauge P c).injective
  simp [torusFamilyGauge_apply]

/-- The zero section gives the identity coordinate change. -/
@[simp] theorem torusFamilyGauge_zero : torusFamilyGauge P 0 = Equiv.refl _ := by
  let _ := torusFamilyTranslationAddAction P
  ext x
  simp [torusFamilyGauge_apply]

/-- Successive translation gauges add their sections. -/
@[simp] theorem torusFamilyGauge_trans (c d : Y → E) :
    (torusFamilyGauge P c).trans (torusFamilyGauge P d) = torusFamilyGauge P (c + d) := by
  let _ := torusFamilyTranslationAddAction P
  ext x
  simp [Equiv.trans_apply, torusFamilyGauge_apply, ← add_vadd, add_comm]

/-- Two translation gauges agree exactly when their sections differ pointwise by periods. -/
theorem torusFamilyGauge_eq_iff (c d : Y → E) :
    torusFamilyGauge P c = torusFamilyGauge P d ↔
      ∀ y, c y - d y ∈ LinearMap.range (P y) := by
  let _ := periodAddAction P
  constructor
  · intro h y
    have hzero := Equiv.congr_fun h (Quotient.mk _ (y, (0 : E)))
    simpa only [torusFamilyGauge_mk, zero_add, Quotient.eq, AddAction.orbitRel_apply,
      mem_orbit_periodAddAction_iff, true_and] using hzero
  · intro h
    apply Equiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h p =>
      obtain ⟨y, v⟩ := p
      simp only [torusFamilyGauge_mk, Quotient.eq, AddAction.orbitRel_apply,
        mem_orbit_periodAddAction_iff, true_and]
      simpa only [add_sub_add_left_eq_sub] using h y

/-- Conjugating a lifted translation by a gauge replaces its section by `β + c ∘ r - c`.
The map `F` is on the actual period quotient, and `hF` specifies its vector lift. -/
theorem torusFamilyGauge_conj_mk (c β : Y → E) (r : Y → Y)
    (F : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Y × E) → AddAction.orbitRel.Quotient Λ (Y × E))
    (hF : ∀ y v, F (Quotient.mk _ (y, v)) = Quotient.mk _ (r y, v + β y))
    (y : Y) (v : E) :
    torusFamilyGauge P c (F ((torusFamilyGauge P c).symm (Quotient.mk _ (y, v)))) =
      Quotient.mk _ (r y, v + (β y + c (r y) - c y)) := by
  rw [torusFamilyGauge_symm, torusFamilyGauge_mk, hF, torusFamilyGauge_mk]
  congr 2
  simp only [Pi.neg_apply]
  abel

end Algebra

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EY : Type*} [NormedAddCommGroup EY]
  [NormedSpace 𝕜 EY] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-- A `C^n` vector-valued section gives a `C^n` change of coordinates on the torus family.
For holomorphic periods and section this is a biholomorphism. -/
noncomputable def torusFamilyGaugeDiffeomorph (c : Y → E)
    (hc : ContMDiff I 𝓘(𝕜, E) n c) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    Diffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E))
      (AddAction.orbitRel.Quotient Λ (Y × E)) (AddAction.orbitRel.Quotient Λ (Y × E)) n :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  letI := torusFamilyTranslationAddAction P
  haveI := contMDiffVAdd_torusFamilyTranslationAddAction P hinj hP
  { toEquiv := torusFamilyGauge P c
    contMDiff_toFun := (hc.comp (contMDiff_torusFamilyProjection P hinj hP)).vadd contMDiff_id
    contMDiff_invFun := (hc.neg.comp (contMDiff_torusFamilyProjection P hinj hP)).vadd
      contMDiff_id }

/-- The differentiable gauge has the underlying equivalence `torusFamilyGauge`. -/
@[simp] theorem torusFamilyGaugeDiffeomorph_toEquiv (c : Y → E)
    (hc : ContMDiff I 𝓘(𝕜, E) n c) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyGaugeDiffeomorph P hinj hP c hc).toEquiv = torusFamilyGauge P c := (rfl)

/-- The inverse differentiable gauge subtracts its section. -/
@[simp] theorem torusFamilyGaugeDiffeomorph_symm (c : Y → E)
    (hc : ContMDiff I 𝓘(𝕜, E) n c) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    (torusFamilyGaugeDiffeomorph P hinj hP c hc).symm =
      torusFamilyGaugeDiffeomorph P hinj hP (-c) hc.neg := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  apply Diffeomorph.toEquiv_injective
  simp only [Diffeomorph.symm_toEquiv, torusFamilyGaugeDiffeomorph_toEquiv,
    torusFamilyGauge_symm]

/-- A cyclic lifted translation whose orbit sum is the period `P y λ` is conjugate, by a
`C^n` fibre coordinate change, to translation by `(1/m) • P y λ` over the same base map.
In particular holomorphic input gives a biholomorphic normalization, without making the period
family constant. This asserts order dividing `m` for the base map, not exact order. -/
theorem exists_torusFamilyGaugeDiffeomorph_cyclic_normalization
    (r : Y → Y) (β : Y → E) {m : ℕ} (l : Λ)
    (hr : ContMDiff I I n r) (hβ : ContMDiff I 𝓘(𝕜, E) n β)
    (hperiod : r^[m] = id) (hm : (m : 𝕜) ≠ 0)
    (hsum : ∀ y, birkhoffSum r β m y = P y l)
    (F : letI := periodAddAction P
      AddAction.orbitRel.Quotient Λ (Y × E) → AddAction.orbitRel.Quotient Λ (Y × E))
    (hF : ∀ y v, F (Quotient.mk _ (y, v)) = Quotient.mk _ (r y, v + β y)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ∃ c : Y → E, ∃ hc : ContMDiff I 𝓘(𝕜, E) n c, ∀ y v,
      torusFamilyGaugeDiffeomorph P hinj hP c hc
          (F ((torusFamilyGaugeDiffeomorph P hinj hP c hc).symm (Quotient.mk _ (y, v)))) =
        Quotient.mk _ (r y, v + (m : 𝕜)⁻¹ • P y l) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  refine ⟨cyclicCorrection 𝕜 r β m, contMDiff_cyclicCorrection hr hβ m, ?_⟩
  intro y v
  have hnorm := add_cyclicCorrection_apply_sub (𝕜 := 𝕜) r β (congrFun hperiod y) hm
    (a := (m : 𝕜)⁻¹ • P y l) (by
      rw [hsum, ← Nat.cast_smul_eq_nsmul 𝕜, smul_inv_smul₀ hm])
  have he := torusFamilyGauge_conj_mk P (cyclicCorrection 𝕜 r β m) β r F hF y v
  rw [hnorm] at he
  simpa only [← Diffeomorph.coe_toEquiv, Diffeomorph.symm_toEquiv,
    torusFamilyGaugeDiffeomorph_toEquiv] using he

end Regularity

end TauCeti
