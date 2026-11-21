/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
import TauCeti.Analysis.InnerProductSpace.Complex
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.NormalForm
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# The Wirtinger inequality and Kähler calibrations in every degree

On a finite-dimensional real inner product space `V` equipped with an orthogonal almost complex
structure `J`, the **Wirtinger inequality** states that the normalized `r`-th Kähler power
`ωʳ / r!` (power index `r`, form degree `2 * r`) has comass at most one in every power index `r`,
and comass equal to one whenever `2 * r ≤ finrank ℝ V`
(`AlmostComplexStructure.norm_kahlerPowerForm`).

Its calibrated frames are precisely the real-orthonormal `2r`-frames sharing the same oriented
exterior product as a `J`-adapted orthonormal frame `(u₀, J u₀, …, u_{r-1}, J u_{r-1})`
(`AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff`). The proof restricts `ω` to the
span `P` of an orthonormal `2r`-frame, applies the real normal form and Pfaffian divided-power
identity (`TauCeti.exists_orthonormalBasis_twoVector_normalForm`) to the skew-adjoint contraction
`x ↦ P.starProjection (J x)`, and reads off `ωʳ / r! (v) = ± ∏ j, μ j` with `0 ≤ μ j ≤ 1`: a unit
weight `μ j = 1` makes its corresponding two-plane `(w_{2j}, w_{2j+1})` `J`-invariant
(`w_{2j+1} = J w_{2j}`), and overall equality `ωʳ / r! (v) = 1` forces every weight `μ j` to be `1`
(so `J` preserves `P`).

Specializing `J` to multiplication by `i` (`AlmostComplexStructure.ofComplexModule E`) yields the
all-degree Wirtinger inequality (`TauCeti.norm_kahlerPowerForm_le`, `TauCeti.norm_kahlerPowerForm`)
and calibrated-frame classification (`TauCeti.isCalibratedFrame_kahlerPowerForm_iff`) on any
finite-dimensional Hermitian vector space `E` in terms of `TauCeti.complexToRealFamily`.

## Main results

* `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm_le`,
  `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm`, and
  `TauCeti.AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff`: the Wirtinger inequality
  and equality classification for an orthogonal almost complex structure for every power index `r`
  (form degree `2 * r`).
* `TauCeti.norm_kahlerPowerForm_le`, `TauCeti.norm_kahlerPowerForm`, and
  `TauCeti.isCalibratedFrame_kahlerPowerForm_iff`: the Wirtinger inequality and calibrated-frame
  classification on any finite-dimensional Hermitian vector space in every power index `r` (form
  degree `2 * r`).

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), Theorem II.6.11
  and Lemma II.6.13.
* H. Federer, *Geometric Measure Theory*, Springer (1969), §1.8.2.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998),
  705–747.
-/

public section

noncomputable section

open Module exteriorPower
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

namespace AlmostComplexStructure

section Wirtinger

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem apply_eq_of_norm_starProjection_eq_one {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {P : Submodule ℝ V} {u w : P}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hproj : P.starProjection (J u.val) = w.val) :
    w.val = J u.val := by
  have hnorm : ‖P.starProjection (J u.val)‖ = ‖J u.val‖ := by
    rw [hproj, Submodule.norm_coe, hw, J.norm_apply hJ, Submodule.norm_coe, hu]
  rw [← hproj]
  exact P.starProjection_eq_self_iff.2 ((P.mem_iff_norm_starProjection _).2 hnorm)

/-- Core normal-form decomposition of `J.kahlerPowerForm r` restricted to the span of an
orthonormal `2r`-frame `v`: yields a companion orthonormal frame `w` of the same span, weights
`0 ≤ μ j ≤ 1`, and a sign `ε ∈ {1, -1}` with `v₁ ∧ ⋯ ∧ v_{2r} = ε • (w₁ ∧ ⋯ ∧ w_{2r})`,
`ωʳ / r! (v) = ε * ∏ j, μ j`, and `μ j = 1 → w_{2j+1} = J w_{2j}`. -/
private theorem exists_normalForm_eval_of_orthonormal {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {r : ℕ} {v : Fin (2 * r) → V} (hv : Orthonormal ℝ v) :
    ∃ (w : Fin (2 * r) → V) (μ : Fin r → ℝ) (ε : ℝ),
      Orthonormal ℝ w ∧
      (∀ j, 0 ≤ μ j ∧ μ j ≤ 1) ∧
      |ε| = 1 ∧
      ιMulti ℝ (2 * r) v = ε • ιMulti ℝ (2 * r) w ∧
      J.kahlerPowerForm r v = ε * ∏ j, μ j ∧
      (∀ j : Fin r, μ j = 1 →
        w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) := by
  let P : Submodule ℝ V := Submodule.span ℝ (Set.range v)
  have hP_dim : finrank ℝ P = 2 * r := by simpa using finrank_span_eq_card hv.linearIndependent
  let vP : Fin (2 * r) → P := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  let FP : ⋀[ℝ]^2 P := (alternatingFormEquiv P 2).symm
    ((alternatingFormEquiv V 2 J.kahlerForm).compContinuousLinearMap P.subtypeL)
  obtain ⟨b, μ, hμ0, hcontr0, _, _, hpow⟩ := exists_orthonormalBasis_twoVector_normalForm hP_dim FP
  have hproj (x : P) : (twoVectorContraction FP x : V) = P.starProjection (J x.val) := by
    rw [coe_twoVectorContraction_alternatingFormEquiv_symm_compContinuousLinearMap_subtypeL
      P J.kahlerForm x, twoVectorContraction_kahlerForm hJ]
  have hμ1 (j : Fin r) : μ j ≤ 1 := by
    have hnorm := congrArg norm (hcontr0 j)
    rw [norm_smul, Real.norm_of_nonneg (hμ0 j), b.orthonormal.1, mul_one, ← Submodule.norm_coe,
      hproj] at hnorm
    calc μ j = ‖P.starProjection (J (b ⟨2 * (j : ℕ), by omega⟩ : V))‖ := hnorm.symm
      _ ≤ ‖J (b ⟨2 * (j : ℕ), by omega⟩ : V)‖ := P.norm_starProjection_apply_le _
      _ = 1 := by rw [J.norm_apply hJ, Submodule.norm_coe, b.orthonormal.1]
  set ε : ℝ := b.toBasis.det vP
  have hdetP : ιMulti ℝ (2 * r) vP = ε • ιMulti ℝ (2 * r) b :=
    b.toBasis.exteriorPower_ιMulti_eq_det_smul vP
  have hw : Orthonormal ℝ (fun i ↦ (b i : V)) := b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  have hι : ιMulti ℝ (2 * r) v = ε • ιMulti ℝ (2 * r) (fun i ↦ (b i : V)) := by
    simpa only [map_smul, exteriorPower.map_apply_ιMulti, Function.comp_def,
      Submodule.coe_subtype] using congrArg (exteriorPower.map (2 * r) P.subtype) hdetP
  have hε : |ε| = 1 := by
    have hn := congrArg norm hι
    rw [hv.norm_ιMulti, norm_smul, Real.norm_eq_abs, hw.norm_ιMulti, mul_one] at hn
    exact hn.symm
  refine ⟨fun i ↦ (b i : V), μ, ε, hw, fun j ↦ ⟨hμ0 j, hμ1 j⟩, hε, hι, ?_, fun j hμj ↦ ?_⟩
  · have hcomp : P.subtypeL ∘ vP = v := funext fun _ ↦ Submodule.subtypeL_apply _ _
    have heval := DFunLike.congr_fun
      (kahlerPowerForm_compContinuousLinearMap J P.subtypeL FP
        (LinearEquiv.apply_symm_apply _ _).symm r) vP
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hcomp,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, alternatingFormEquiv_apply,
      ← real_inner_smul_left, hpow, hdetP,
      real_inner_smul_left (F := ⋀[ℝ]^(2 * r) P),
      real_inner_smul_right (F := ⋀[ℝ]^(2 * r) P),
      real_inner_self_eq_norm_sq, b.orthonormal.norm_ιMulti] at heval
    rw [heval]
    ring
  · exact apply_eq_of_norm_starProjection_eq_one hJ (b.orthonormal.1 _) (b.orthonormal.1 _)
      (by simpa [hproj, hμj] using congrArg Subtype.val (hcontr0 j))

/-- **The Wirtinger comass bound** for an orthogonal almost complex structure: `‖ωʳ / r!‖ ≤ 1`
for every power index `r` (form degree `2 * r`, including form degrees exceeding `finrank ℝ V`).
-/
theorem norm_kahlerPowerForm_le {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (r : ℕ) :
    ‖J.kahlerPowerForm r‖ ≤ 1 := by
  refine (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).2 fun v hv ↦ ?_
  obtain ⟨_, μ, ε, _, hμ, hε, _, heval, _⟩ := exists_normalForm_eval_of_orthonormal hJ hv
  rw [heval, Real.norm_eq_abs, abs_mul, hε, one_mul,
    abs_of_nonneg (Finset.prod_nonneg fun j _ ↦ (hμ j).1)]
  exact Finset.prod_le_one₀ (fun j _ ↦ (hμ j).1) (fun j _ ↦ (hμ j).2)

/-- **The Wirtinger inequality in every degree** for an orthogonal almost complex structure: when
`2 * r ≤ finrank ℝ V`, the normalized Kähler power `ωʳ / r!` (power index `r`, form degree `2 * r`)
has comass equal to one. -/
theorem norm_kahlerPowerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {r : ℕ} (hr : 2 * r ≤ finrank ℝ V) :
    ‖J.kahlerPowerForm r‖ = 1 := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  have hdim : finrank ℝ V = 2 * n := by omega
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) n hdim
  let ι : Fin (2 * r) → Fin (2 * n) := fun i ↦ ⟨(i : ℕ), by have := i.isLt; omega⟩
  let w : Fin (2 * r) → V := b ∘ ι
  have hw : Orthonormal ℝ w :=
    b.orthonormal.comp ι (fun i j hij ↦ Fin.ext (by simpa [ι] using congrArg Fin.val hij))
  have hadapt (j : Fin r) : w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩) := by
    simpa [w, ι] using hb ⟨(j : ℕ), by omega⟩
  have hcal : (J.kahlerPowerForm r).IsCalibratedFrame w :=
    ContinuousAlternatingMap.isCalibratedFrame_iff.2
      ⟨hw, kahlerPowerForm_apply_of_adapted hw hadapt⟩
  exact le_antisymm (norm_kahlerPowerForm_le hJ r) hcal.one_le_norm

/-- **Equality case of the Wirtinger inequality** for an orthogonal almost complex structure: a
`2r`-frame `v` is calibrated by `ωʳ / r!` precisely when `v` is real-orthonormal and shares its
exterior product with a `J`-adapted orthonormal frame `(w₀, J w₀, …, w_{2r-2}, J w_{2r-2})`. -/
theorem isCalibratedFrame_kahlerPowerForm_iff {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {r : ℕ} (v : Fin (2 * r) → V) :
    (J.kahlerPowerForm r).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧ ∃ w : Fin (2 * r) → V, Orthonormal ℝ w ∧
        (∀ j : Fin r, w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) ∧
        ιMulti ℝ (2 * r) v = ιMulti ℝ (2 * r) w := by
  constructor
  · rw [ContinuousAlternatingMap.isCalibratedFrame_iff]
    rintro ⟨hv, hval⟩
    obtain ⟨w, μ, ε, hw, hμ, hε, hι, heval, hμ_eq⟩ := exists_normalForm_eval_of_orthonormal hJ hv
    have hprod_nonneg : 0 ≤ ∏ j, μ j := Finset.prod_nonneg fun j _ ↦ (hμ j).1
    have hε1 : ε = 1 := by
      rcases (abs_eq zero_le_one).mp hε with h1 | hneg
      · exact h1
      · rw [heval, hneg, neg_one_mul] at hval
        linarith
    have hprod1 : ∏ j, μ j = 1 := by rw [hε1, one_mul] at heval; linarith
    have hall1 : ∀ j, μ j = 1 := fun j ↦ by
      have h1 : 1 ≤ μ j := by
        simpa [hprod1] using Finset.prod_le_prod_of_subset_of_le_one₀
          (Finset.singleton_subset_iff.2 (Finset.mem_univ j))
          (fun k _ ↦ (hμ k).1) (fun k _ _ ↦ (hμ k).2)
      exact le_antisymm (hμ j).2 h1
    exact ⟨hv, w, hw, fun j ↦ hμ_eq j (hall1 j), by simpa [hε1] using hι⟩
  · rintro ⟨hv, w, hw, hadapt, hι⟩
    exact (ContinuousAlternatingMap.isCalibratedFrame_iff.2
      ⟨hw, kahlerPowerForm_apply_of_adapted hw hadapt⟩).of_ιMulti_eq hv hι

end Wirtinger

end AlmostComplexStructure

section HermitianWirtinger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- The normalized `r`-th Kähler power `ωʳ / r!` (power index `r`, form degree `2 * r`) has comass
at most one for every power index `r`. -/
theorem norm_kahlerPowerForm_le (r : ℕ) : ‖kahlerPowerForm E r‖ ≤ 1 :=
  AlmostComplexStructure.norm_kahlerPowerForm_le
    AlmostComplexStructure.real_inner_ofComplexModule_apply_ofComplexModule_apply r

/-- **The Wirtinger inequality in every degree**: on a finite-dimensional Hermitian vector space
`E`, for every power index `r ≤ finrank ℂ E`, the normalized Kähler power `ωʳ / r!` (form degree
`2 * r`) has comass one. -/
theorem norm_kahlerPowerForm {r : ℕ} (hr : r ≤ finrank ℂ E) : ‖kahlerPowerForm E r‖ = 1 := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  refine AlmostComplexStructure.norm_kahlerPowerForm
    AlmostComplexStructure.real_inner_ofComplexModule_apply_ofComplexModule_apply ?_
  rw [finrank_real_eq_two_mul_finrank_complex]
  omega

/-- **Equality case of the Wirtinger inequality in every degree**: a `2r`-frame `v` in a
finite-dimensional Hermitian vector space `E` is calibrated by `ωʳ / r!` precisely when `v` is
real-orthonormal and shares its exterior product with `TauCeti.complexToRealFamily u` for some
complex-orthonormal family `u : Fin r → E`. -/
theorem isCalibratedFrame_kahlerPowerForm_iff {r : ℕ} (v : Fin (2 * r) → E) :
    (kahlerPowerForm E r).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧ ∃ u : Fin r → E, Orthonormal ℂ u ∧
        ιMulti ℝ (2 * r) v = ιMulti ℝ (2 * r) (complexToRealFamily u) := by
  rw [kahlerPowerForm, AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff
    AlmostComplexStructure.real_inner_ofComplexModule_apply_ofComplexModule_apply v]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨w, hw, hadapt, hι⟩
    let u : Fin r → E := fun j ↦ w ⟨2 * (j : ℕ), by omega⟩
    have hu : Orthonormal ℂ u := by
      refine ⟨fun j ↦ hw.1 _, fun j k hjk ↦ ?_⟩
      have hre : (inner ℂ (u j) (u k)).re = 0 := by
        rw [← RCLike.re_to_complex, ← TauCeti.inner_real_eq_re_inner ℂ]
        have hne : (⟨2 * (j : ℕ), by omega⟩ : Fin (2 * r)) ≠ ⟨2 * (k : ℕ), by omega⟩ := by
          rw [← complexRealIndexEquiv_zero, ← complexRealIndexEquiv_zero]
          exact (complexRealIndexEquiv r).injective.ne (by simp [hjk])
        exact hw.2 hne
      have him : (inner ℂ (u j) (u k)).im = 0 := by
        have hω : (inner ℂ (u j) (u k)).im = ⟪Complex.I • u j, u k⟫_ℝ := by
          simpa [kahlerTwoForm_apply] using kahlerTwoForm_apply_eq_inner (u j) (u k)
        have hI : Complex.I • u j = w ⟨2 * (j : ℕ) + 1, by omega⟩ := by
          simpa only [AlmostComplexStructure.ofComplexModule_apply] using (hadapt j).symm
        have hne : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * r)) ≠ ⟨2 * (k : ℕ), by omega⟩ := by
          rw [← complexRealIndexEquiv_one, ← complexRealIndexEquiv_zero]
          exact (complexRealIndexEquiv r).injective.ne (by simp)
        rw [hω, hI]
        exact hw.2 hne
      exact Complex.ext hre him
    have hw_eq : complexToRealFamily u = w := by
      ext i
      obtain ⟨⟨j, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
      fin_cases k
      · simp [u, complexRealIndexEquiv_zero]
      · simpa [u, complexRealIndexEquiv_one] using (hadapt j).symm
    exact ⟨u, hu, by rwa [hw_eq]⟩
  · rintro ⟨u, hu, hι⟩
    exact ⟨complexToRealFamily u, orthonormal_complexToRealFamily hu,
      complexToRealFamily_odd_eq_ofComplexModule u, hι⟩

end HermitianWirtinger

end TauCeti
