/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Equicontinuity
import TauCeti.Analysis.CStarAlgebra.GNS.Basic
import TauCeti.Analysis.CStarAlgebra.Ideal
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Jordan
import TauCeti.Analysis.CStarAlgebra.Representation.Multiplier
import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Quasicentral approximate units for closed two-sided ideals

Every closed two-sided ideal `I` of a (possibly nonunital) C⋆-algebra `A` admits a positive
contractive approximate unit that is *quasicentral* in `A`, meaning `e * a - a * e → 0` in norm
for every `a : A`. This is Arveson's quasicentral approximate unit theorem.

The proof has three steps:

1. **Weak asymptotic centrality.** Along any increasing approximate unit `l` of `I`, every positive
   functional `ω` on `A⁺¹` satisfies `ω (e * a - a * e) → 0`. In the GNS representation of `ω`, the
   restriction to `I` converges strongly along `l` to the orthogonal projection `P` onto its
   essential subspace (`NonUnitalStarAlgHom.tendsto_nonUnitalMultiplierExtension_apply`), and
   because `I` is a two-sided ideal, `P` commutes with the action of every `a : A`. By the Jordan
   decomposition (`ContinuousLinearMap.exists_positiveContinuousLinearMap_sub_add_I_smul_sub`),
   the same holds for every continuous linear functional `φ : A →L[ℂ] ℂ`.
2. **Convexification.** Given a lower bound `u ∈ I` with `0 ≤ u` and `‖u‖ < 1`, finite subsets
   `G ⊆ I` and `F ⊆ A`, and `δ > 0`, the set `K` of elements `e ∈ I` above `u` with `‖e‖ < 1`
   approximating the unit on `G` within `δ` is convex and belongs to the strict-ball approximate
   unit filter of `I`. Applying Hahn–Banach separation to `0` and the closure of the commutator
   image of `K` in `F → A` shows that `0` lies in that closure, yielding an element `e ∈ K` with
   `‖e * a - a * e‖ < δ` for every `a ∈ F`.
3. **Filter and sequential forms.** Taking the intersection over all such finite constraints builds
   a proper quasicentral approximate unit filter `TwoSidedIdeal.quasicentralApproximateUnit I`
   (`TwoSidedIdeal.exists_quasicentral_approximateUnit`). When `A` is separable, iterating the
   finite approximation step along dense sequences in `I` and `A` produces a monotone sequential
   quasicentral approximate unit (`TwoSidedIdeal.exists_seq_monotone_quasicentral_approximateUnit`).

## Main results

* `TwoSidedIdeal.exists_mem_le_norm_lt_one_mul_sub_lt`: Arveson's finite approximation lemma with
  an arbitrary lower bound `u ∈ I` (`0 ≤ u`, `‖u‖ < 1`).
* `TwoSidedIdeal.quasicentralApproximateUnit`: canonical coarsest quasicentral approximate unit
  filter of a two-sided ideal, characterized by `TwoSidedIdeal.le_quasicentralApproximateUnit_iff`
  and proved proper (`TwoSidedIdeal.neBot_quasicentralApproximateUnit`) when the ideal is closed.
* `TwoSidedIdeal.exists_quasicentral_approximateUnit`: Arveson's quasicentral approximate unit
  theorem.
* `TwoSidedIdeal.exists_seq_monotone_quasicentral_approximateUnit`: monotone sequential
  quasicentral approximate unit when `A` is separable.

## References

* W. Arveson, *Notes on extensions of C⋆-algebras*, Duke Math. J. 44 (1977), 329–355, Theorem 1.
* B. Blackadar, *Operator Algebras*, Section II.4.3 (Theorem II.4.3.2).
-/

public section

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder MultiplierAlgebra

namespace TwoSidedIdeal

section WeakCentrality

variable {A : Type*} [NonUnitalCStarAlgebra A]

private theorem starProjection_essentialSubspace_comm (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A⁺¹ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    let S := I.toNonUnitalStarSubalgebra
    let πS : S →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
      π.comp ((Unitization.inrNonUnitalStarAlgHom ℂ A).comp
        (NonUnitalStarSubalgebraClass.subtype S))
    πS.essentialSubspace.starProjection * π (a : A⁺¹) =
      π (a : A⁺¹) * πS.essentialSubspace.starProjection := by
  let S := I.toNonUnitalStarSubalgebra
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  let ιS : S →⋆ₙₐ[ℂ] A⁺¹ :=
    (Unitization.inrNonUnitalStarAlgHom ℂ A).comp (NonUnitalStarSubalgebraClass.subtype S)
  let πS : S →⋆ₙₐ[ℂ] (H →L[ℂ] H) := π.comp ιS
  let P : H →L[ℂ] H := πS.essentialSubspace.starProjection
  have hP_mul (y : S) : P * πS y = πS y := by
    simpa [P, πS.nonUnitalMultiplierExtension_one] using
      πS.nonUnitalMultiplierExtension_mul_eq_fst 1 y
  refine πS.ext_of_orthogonal_essentialSubspace (fun x => ?_) (fun η hη => ?_)
  · let ax : S :=
      ⟨a * (x : A), I.mem_toNonUnitalStarSubalgebra.2
        (I.mul_mem_left a x (I.mem_toNonUnitalStarSubalgebra.1 x.2))⟩
    have hmul : π (a : A⁺¹) * πS x = πS ax := by
      simp only [πS, ιS, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype,
        Unitization.inrNonUnitalStarAlgHom_apply, ← map_mul, ← Unitization.inr_mul, ax]
    rw [mul_assoc, hmul, hP_mul, mul_assoc, hP_mul, hmul]
  · have hPη : P η = 0 := by
      simpa [P, πS.nonUnitalMultiplierExtension_one] using
        πS.nonUnitalMultiplierExtension_apply_eq_zero 1 hη
    have haη : π (a : A⁺¹) η ∈ πS.essentialSubspaceᗮ := by
      rw [πS.mem_orthogonal_essentialSubspace_iff]
      intro x
      let xa : S :=
        ⟨(x : A) * a, I.mem_toNonUnitalStarSubalgebra.2
          (I.mul_mem_right x a (I.mem_toNonUnitalStarSubalgebra.1 x.2))⟩
      have hmul : πS x (π (a : A⁺¹) η) = πS xa η := by
        rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def]
        simp only [πS, ιS, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype,
          Unitization.inrNonUnitalStarAlgHom_apply, ← map_mul, ← Unitization.inr_mul, xa]
      rw [hmul]
      exact πS.apply_eq_zero_of_mem_orthogonal_essentialSubspace hη xa
    have hPaη : P (π (a : A⁺¹) η) = 0 := by
      simpa [P, πS.nonUnitalMultiplierExtension_one] using
        πS.nonUnitalMultiplierExtension_apply_eq_zero 1 haη
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, P] at hPaη hPη ⊢
    rw [hPaη, hPη, map_zero]

variable [PartialOrder A]

private theorem tendsto_pos_apply_mul_sub_mul (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (ω : A⁺¹ →P[ℂ] ℂ) {l : Filter I.toNonUnitalStarSubalgebra}
    (hl : let _ := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra I.toNonUnitalStarSubalgebra
      l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I.toNonUnitalStarSubalgebra =>
      ω (((e : A) * a - a * (e : A) : A) : A⁺¹)) l (𝓝 0) := by
  let S := I.toNonUnitalStarSubalgebra
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  let f : A⁺¹ →ₚ[ℂ] ℂ := ω.toPositiveLinearMap
  let H := f.GNS
  let ξ : H := f.gnsVector
  let π : A⁺¹ →⋆ₙₐ[ℂ] (H →L[ℂ] H) := f.gnsNonUnitalStarAlgHom
  let ιS : S →⋆ₙₐ[ℂ] A⁺¹ :=
    (Unitization.inrNonUnitalStarAlgHom ℂ A).comp (NonUnitalStarSubalgebraClass.subtype S)
  let πS : S →⋆ₙₐ[ℂ] (H →L[ℂ] H) := π.comp ιS
  let P : H →L[ℂ] H := πS.essentialSubspace.starProjection
  have hlim (η : H) : Tendsto (fun e : S => πS e η) l (𝓝 (P η)) := by
    simpa [P, πS.nonUnitalMultiplierExtension_one] using
      πS.tendsto_nonUnitalMultiplierExtension_apply hl 1 η
  have hcomm : P * π (a : A⁺¹) = π (a : A⁺¹) * P :=
    starProjection_essentialSubspace_comm I π a
  have hleft : Tendsto (fun e : S => ω (((e : A) * a : A) : A⁺¹)) l
      (𝓝 (inner ℂ ξ (P (π (a : A⁺¹) ξ)))) := by
    have ht : Tendsto (fun e : S => inner ℂ ξ (πS e (π (a : A⁺¹) ξ))) l
        (𝓝 (inner ℂ ξ (P (π (a : A⁺¹) ξ)))) :=
      ((continuous_inner.comp (continuous_const.prodMk continuous_id)).tendsto _).comp
        (hlim (π (a : A⁺¹) ξ))
    refine ht.congr fun e => ?_
    have hmul : πS e (π (a : A⁺¹) ξ) = π (((e : A) * a : A) : A⁺¹) ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def]
      simp only [πS, ιS, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype,
        Unitization.inrNonUnitalStarAlgHom_apply, ← map_mul, ← Unitization.inr_mul]
    rw [hmul, f.gnsNonUnitalStarAlgHom_apply_gnsVector, f.inner_gnsVector_coe]
    exact congrArg (fun g : A⁺¹ → ℂ => g _) ω.coe_toPositiveLinearMap
  have hright : Tendsto (fun e : S => ω ((a * (e : A) : A) : A⁺¹)) l
      (𝓝 (inner ℂ ξ (π (a : A⁺¹) (P ξ)))) := by
    have ht : Tendsto (fun e : S => inner ℂ ξ (π (a : A⁺¹) (πS e ξ))) l
        (𝓝 (inner ℂ ξ (π (a : A⁺¹) (P ξ)))) :=
      ((continuous_inner.comp (continuous_const.prodMk (π (a : A⁺¹)).continuous)).tendsto _).comp
        (hlim ξ)
    refine ht.congr fun e => ?_
    have hmul : π (a : A⁺¹) (πS e ξ) = π ((a * (e : A) : A) : A⁺¹) ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def]
      simp only [πS, ιS, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype,
        Unitization.inrNonUnitalStarAlgHom_apply, ← map_mul, ← Unitization.inr_mul]
    rw [hmul, f.gnsNonUnitalStarAlgHom_apply_gnsVector, f.inner_gnsVector_coe]
    exact congrArg (fun g : A⁺¹ → ℂ => g _) ω.coe_toPositiveLinearMap
  have hEq : inner ℂ ξ (P (π (a : A⁺¹) ξ)) = inner ℂ ξ (π (a : A⁺¹) (P ξ)) :=
    congrArg (inner ℂ ξ) (congrArg (fun T : H →L[ℂ] H => T ξ) hcomm)
  rw [hEq] at hleft
  simpa [Unitization.inr_sub, map_sub, sub_self] using hleft.sub hright

private theorem tendsto_clm_apply_mul_sub_mul (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (φ : A →L[ℂ] ℂ) {l : Filter I.toNonUnitalStarSubalgebra}
    (hl : let _ := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra I.toNonUnitalStarSubalgebra
      l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I.toNonUnitalStarSubalgebra => φ ((e : A) * a - a * (e : A))) l (𝓝 0) := by
  let ι : A →ₗᵢ[ℂ] A⁺¹ :=
    { Unitization.inrHom (R := ℂ) (S := ℂ) (A := A) with
      norm_map' := fun x => Unitization.norm_inr (𝕜 := ℂ) x }
  obtain ⟨ψ, hψ_ext, -⟩ := ι.exists_extension_norm_eq φ
  obtain ⟨ψ₁, ψ₂, ψ₃, ψ₄, hdecomp, -, -⟩ :=
    ψ.exists_positiveContinuousLinearMap_sub_add_I_smul_sub
  have h1 := tendsto_pos_apply_mul_sub_mul I ψ₁ hl a
  have h2 := tendsto_pos_apply_mul_sub_mul I ψ₂ hl a
  have h3 := tendsto_pos_apply_mul_sub_mul I ψ₃ hl a
  have h4 := tendsto_pos_apply_mul_sub_mul I ψ₄ hl a
  have hcomb : Tendsto (fun e : I.toNonUnitalStarSubalgebra =>
      ((ψ₁ (((e : A) * a - a * (e : A) : A) : A⁺¹) -
        ψ₂ (((e : A) * a - a * (e : A) : A) : A⁺¹)) +
      Complex.I * (ψ₃ (((e : A) * a - a * (e : A) : A) : A⁺¹) -
        ψ₄ (((e : A) * a - a * (e : A) : A) : A⁺¹)))) l (𝓝 0) := by
    simpa using (h1.sub h2).add ((h3.sub h4).const_mul Complex.I)
  refine hcomb.congr fun e => ?_
  have hext : ψ (((e : A) * a - a * (e : A) : A) : A⁺¹) = φ ((e : A) * a - a * (e : A)) :=
    congrArg (fun f : A →L[ℂ] ℂ => f ((e : A) * a - a * (e : A))) hψ_ext
  have hval :=
    congrArg (fun f : A⁺¹ →L[ℂ] ℂ => f (((e : A) * a - a * (e : A) : A) : A⁺¹)) hdecomp
  rw [hext] at hval
  simpa using hval

end WeakCentrality

section FiniteApprox

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

private theorem zero_mem_closure_commutator_image (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    {l : Filter I.toNonUnitalStarSubalgebra}
    (hl : let _ := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra I.toNonUnitalStarSubalgebra
      l.IsIncreasingApproximateUnit)
    {K : Set I.toNonUnitalStarSubalgebra} (hK_mem : K ∈ l) (hK_conv : Convex ℝ K) (F : Finset A) :
    (0 : F → A) ∈ closure
      ((fun e : I.toNonUnitalStarSubalgebra => fun a : F => (e : A) * (a : A) - (a : A) * (e : A))
        '' K) := by
  classical
  let S := I.toNonUnitalStarSubalgebra
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  have : l.NeBot := hl.neBot
  let T : S →L[ℂ] (F → A) :=
    { toFun := fun e a => (e : A) * (a : A) - (a : A) * (e : A)
      map_add' := fun e₁ e₂ => by
        ext a
        simp only [NonUnitalStarSubalgebra.coe_add, Pi.add_apply]
        noncomm_ring
      map_smul' := fun c e => by
        ext a
        simp only [NonUnitalStarSubalgebra.coe_smul, Pi.smul_apply, RingHom.id_apply,
          smul_mul_assoc, mul_smul_comm, smul_sub]
      cont := continuous_pi fun a =>
        (continuous_subtype_val.mul continuous_const).sub
          (continuous_const.mul continuous_subtype_val) }
  by_contra hnotmem
  have hTK_conv : Convex ℝ (T '' K) :=
    hK_conv.linear_image (T.toLinearMap.restrictScalars ℝ)
  obtain ⟨f, r, hfr0, hfrK⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hTK_conv.closure isClosed_closure hnotmem
  have hr_pos : 0 < r := by simpa using hfr0
  have hfT : Tendsto (fun e : S => f (T e)) l (𝓝 0) := by
    have hterm (a : F) :
        Tendsto (fun e : S =>
          (f.comp (ContinuousLinearMap.single ℂ (fun _ : F => A) a))
            ((e : A) * (a : A) - (a : A) * (e : A))) l (𝓝 0) :=
      tendsto_clm_apply_mul_sub_mul I
        (f.comp (ContinuousLinearMap.single ℂ (fun _ : F => A) a)) hl (a : A)
    have hsum : Tendsto (fun e : S =>
        ∑ a : F, (f.comp (ContinuousLinearMap.single ℂ (fun _ : F => A) a))
          ((e : A) * (a : A) - (a : A) * (e : A))) l (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun a _ => hterm a
    refine hsum.congr fun e => ?_
    have hTe : T e = ∑ a : F, Pi.single a (T e a) := (Finset.univ_sum_single (T e)).symm
    conv_rhs => rw [hTe, map_sum]
    rfl
  have hre : Tendsto (fun e : S => (f (T e)).re) l (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp hfT
  obtain ⟨e, heK, he_lt⟩ :=
    (Filter.eventually_and.2 ⟨hK_mem, hre.eventually (Iio_mem_nhds hr_pos)⟩).exists
  exact he_lt.not_gt (hfrK (T e) (subset_closure ⟨e, heK, rfl⟩))

variable [StarOrderedRing A]

private theorem convex_quasicentralApproxSet (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (uS : I.toNonUnitalStarSubalgebra) (G : Finset A) (δ : ℝ) :
    Convex ℝ {e : I.toNonUnitalStarSubalgebra | uS ≤ e ∧ ‖e‖ < 1 ∧
      ∀ x ∈ G, ‖(e : A) * x - x‖ < δ ∧ ‖x * (e : A) - x‖ < δ} := by
  intro e₁ he₁ e₂ he₂ s t hs ht hst
  refine ⟨?_, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · rw [← Subtype.coe_le_coe]
    simp only [NonUnitalStarSubalgebra.coe_add, NonUnitalStarSubalgebra.coe_smul]
    calc
      (uS : A) = (s + t) • (uS : A) := by rw [hst, one_smul]
      _ = s • (uS : A) + t • (uS : A) := add_smul s t (uS : A)
      _ ≤ s • (e₁ : A) + t • (e₂ : A) :=
        add_le_add (smul_le_smul_of_nonneg_left he₁.1 hs) (smul_le_smul_of_nonneg_left he₂.1 ht)
  · have hb : s • e₁ + t • e₂ ∈ Metric.ball (0 : I.toNonUnitalStarSubalgebra) 1 :=
      convex_ball (0 : I.toNonUnitalStarSubalgebra) 1
        (by simpa [Metric.mem_ball] using he₁.2.1)
        (by simpa [Metric.mem_ball] using he₂.2.1) hs ht hst
    simpa [Metric.mem_ball] using hb
  · have hcomb : (s • (e₁ : A) + t • (e₂ : A)) * x - x =
        s • ((e₁ : A) * x - x) + t • ((e₂ : A) * x - x) := by
      calc
        (s • (e₁ : A) + t • (e₂ : A)) * x - x
          = s • ((e₁ : A) * x) + t • ((e₂ : A) * x) - (s • x + t • x) := by
              rw [add_mul, smul_mul_assoc, smul_mul_assoc, ← add_smul, hst, one_smul]
        _ = s • ((e₁ : A) * x - x) + t • ((e₂ : A) * x - x) := by
              rw [smul_sub, smul_sub]; abel
    have hb : s • ((e₁ : A) * x - x) + t • ((e₂ : A) * x - x) ∈ Metric.ball (0 : A) δ :=
      convex_ball (0 : A) δ (by simpa [Metric.mem_ball] using (he₁.2.2 x hx).1)
        (by simpa [Metric.mem_ball] using (he₂.2.2 x hx).1) hs ht hst
    simpa [Metric.mem_ball, hcomb] using hb
  · have hcomb : x * (s • (e₁ : A) + t • (e₂ : A)) - x =
        s • (x * (e₁ : A) - x) + t • (x * (e₂ : A) - x) := by
      calc
        x * (s • (e₁ : A) + t • (e₂ : A)) - x
          = s • (x * (e₁ : A)) + t • (x * (e₂ : A)) - (s • x + t • x) := by
              rw [mul_add, mul_smul_comm, mul_smul_comm, ← add_smul, hst, one_smul]
        _ = s • (x * (e₁ : A) - x) + t • (x * (e₂ : A) - x) := by
              rw [smul_sub, smul_sub]; abel
    have hb : s • (x * (e₁ : A) - x) + t • (x * (e₂ : A) - x) ∈ Metric.ball (0 : A) δ :=
      convex_ball (0 : A) δ (by simpa [Metric.mem_ball] using (he₁.2.2 x hx).2)
        (by simpa [Metric.mem_ball] using (he₂.2.2 x hx).2) hs ht hst
    simpa [Metric.mem_ball, hcomb] using hb

/-- **Arveson's finite quasicentral approximation lemma.** Given a closed two-sided ideal `I` of a
C⋆-algebra `A`, a positive strict contraction `u ∈ I`, finite subsets `G ⊆ I` and `F ⊆ A`, and
`δ > 0`, there is a strict contraction `e ∈ I` above `u` (hence `0 ≤ e`) that acts as an
approximate unit within `δ` on `G` and commutes within `δ` with every element of `F`. -/
theorem exists_mem_le_norm_lt_one_mul_sub_lt (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    {u : A} (huI : u ∈ I) (hu₀ : 0 ≤ u) (hu₁ : ‖u‖ < 1)
    (G : Finset A) (hG : ∀ x ∈ G, x ∈ I) (F : Finset A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e ∈ I, u ≤ e ∧ ‖e‖ < 1 ∧
      (∀ x ∈ G, ‖e * x - x‖ < δ ∧ ‖x * e - x‖ < δ) ∧
      (∀ a ∈ F, ‖e * a - a * e‖ < δ) := by
  let S := I.toNonUnitalStarSubalgebra
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  have _ : StarOrderedRing S := Subtype.starOrderedRing S
  -- Refine `CStarAlgebra.approximateUnit S` to the open unit ball so every element has `‖e‖ < 1`.
  let l₀ : Filter S := (CStarAlgebra.isBasis_nonneg_sections S).filter ⊓ 𝓟 (Metric.ball (0 : S) 1)
  have hl₀_basis : l₀.HasBasis (fun x : S => 0 ≤ x ∧ ‖x‖ < 1)
      (fun x => {y : S | x ≤ y} ∩ Metric.ball (0 : S) 1) :=
    (CStarAlgebra.isBasis_nonneg_sections S).hasBasis.inf_principal (Metric.ball (0 : S) 1)
  have hl₀_le : l₀ ≤ CStarAlgebra.approximateUnit S :=
    inf_le_inf_left _ (principal_mono.2 Metric.ball_subset_closedBall)
  have hl₀ : l₀.IsIncreasingApproximateUnit :=
    { tendsto_mul_left := fun x =>
        ((CStarAlgebra.increasingApproximateUnit S).tendsto_mul_left x).mono_left hl₀_le
      tendsto_mul_right := fun x =>
        ((CStarAlgebra.increasingApproximateUnit S).tendsto_mul_right x).mono_left hl₀_le
      eventually_nonneg :=
        (CStarAlgebra.increasingApproximateUnit S).eventually_nonneg.filter_mono hl₀_le
      eventually_norm :=
        (CStarAlgebra.increasingApproximateUnit S).eventually_norm.filter_mono hl₀_le
      neBot := hl₀_basis.neBot_iff.2 fun {x} hx =>
        ⟨x, le_rfl, by simpa [Metric.mem_ball] using hx.2⟩ }
  let uS : S := ⟨u, I.mem_toNonUnitalStarSubalgebra.2 huI⟩
  let K : Set S :=
    {e : S | uS ≤ e ∧ ‖e‖ < 1 ∧
      ∀ x ∈ G, ‖(e : A) * x - x‖ < δ ∧ ‖x * (e : A) - x‖ < δ}
  have hK_mem : K ∈ l₀ := by
    have hsec : ∀ᶠ e : S in l₀, uS ≤ e ∧ ‖e‖ < 1 :=
      Filter.mem_of_superset (hl₀_basis.mem_of_mem (i := uS) ⟨hu₀, hu₁⟩) fun _ ⟨hle, hball⟩ =>
        ⟨hle, by simpa [Metric.mem_ball] using hball⟩
    have hG_ev : ∀ᶠ e : S in l₀, ∀ x ∈ G, ‖(e : A) * x - x‖ < δ ∧ ‖x * (e : A) - x‖ < δ := by
      rw [Filter.eventually_all_finset]
      intro x hx
      let xS : S := ⟨x, I.mem_toNonUnitalStarSubalgebra.2 (hG x hx)⟩
      have hR : ∀ᶠ e : S in l₀, ‖(e : A) * x - x‖ < δ := by
        filter_upwards [Metric.tendsto_nhds.1 (hl₀.tendsto_mul_right xS) δ hδ] with e he
        simpa [dist_eq_norm, xS] using he
      have hL : ∀ᶠ e : S in l₀, ‖x * (e : A) - x‖ < δ := by
        filter_upwards [Metric.tendsto_nhds.1 (hl₀.tendsto_mul_left xS) δ hδ] with e he
        simpa [dist_eq_norm, xS] using he
      exact hR.and hL
    filter_upwards [hsec, hG_ev] with e he hG'
    exact ⟨he.1, he.2, hG'⟩
  have hzero :=
    zero_mem_closure_commutator_image I hl₀ hK_mem (convex_quasicentralApproxSet I uS G δ) F
  obtain ⟨v, ⟨e, heK, rfl⟩, hv⟩ := Metric.mem_closure_iff.1 hzero δ hδ
  have hcomm_norm : ‖fun a : F => (e : A) * (a : A) - (a : A) * (e : A)‖ < δ := by
    simpa [dist_eq_norm] using hv
  exact ⟨(e : A), I.mem_toNonUnitalStarSubalgebra.1 e.2, heK.1, heK.2.1, heK.2.2, fun a ha =>
    (norm_le_pi_norm (fun b : F => (e : A) * (b : A) - (b : A) * (e : A)) ⟨a, ha⟩).trans_lt
      hcomm_norm⟩

end FiniteApprox

section FilterDef

variable {A : Type*} [NonUnitalSeminormedRing A] [PartialOrder A]

/-- The canonical coarsest quasicentral positive contractive approximate unit filter of a
two-sided ideal `I` in a normed ring `A`. It is characterized by
`TwoSidedIdeal.le_quasicentralApproximateUnit_iff`, and for a closed two-sided ideal of a
C⋆-algebra it is proper (`TwoSidedIdeal.neBot_quasicentralApproximateUnit`). -/
noncomputable def quasicentralApproximateUnit (I : TwoSidedIdeal A) : Filter A :=
  (⨅ u ∈ {u : A | u ∈ I ∧ 0 ≤ u ∧ ‖u‖ < 1}, 𝓟 {e : A | u ≤ e}) ⊓
    𝓟 (I : Set A) ⊓
    𝓟 {e : A | ‖e‖ ≤ 1} ⊓
    (⨅ x ∈ I, Filter.comap (fun e => e * x) (𝓝 x)) ⊓
    (⨅ x ∈ I, Filter.comap (fun e => x * e) (𝓝 x)) ⊓
    (⨅ a : A, Filter.comap (fun e => e * a - a * e) (𝓝 0))

/-- Universal property of `I.quasicentralApproximateUnit`: a filter `l` refines it if and only if
elements along `l` eventually dominate every positive strict contraction in `I`, eventually lie in
the closed unit ball of `I`, form a two-sided approximate unit on `I`, and asymptotically commute
with every element of `A`. -/
theorem le_quasicentralApproximateUnit_iff (I : TwoSidedIdeal A) {l : Filter A} :
    l ≤ I.quasicentralApproximateUnit ↔
      (∀ u ∈ I, 0 ≤ u → ‖u‖ < 1 → ∀ᶠ e in l, u ≤ e) ∧
      (∀ᶠ e in l, e ∈ I) ∧
      (∀ᶠ e in l, ‖e‖ ≤ 1) ∧
      (∀ x ∈ I, Tendsto (fun e => e * x) l (𝓝 x)) ∧
      (∀ x ∈ I, Tendsto (fun e => x * e) l (𝓝 x)) ∧
      (∀ a : A, Tendsto (fun e => e * a - a * e) l (𝓝 0)) := by
  simp only [quasicentralApproximateUnit, le_inf_iff, le_iInf_iff, le_principal_iff,
    ← tendsto_iff_comap, mem_ofPred_eq, and_imp]
  constructor
  · rintro ⟨⟨⟨⟨⟨hle, hmem⟩, hnorm⟩, hR⟩, hL⟩, hcomm⟩
    exact ⟨hle, hmem, hnorm, hR, hL, hcomm⟩
  · rintro ⟨hle, hmem, hnorm, hR, hL, hcomm⟩
    exact ⟨⟨⟨⟨⟨hle, hmem⟩, hnorm⟩, hR⟩, hL⟩, hcomm⟩

/-- Elements along `I.quasicentralApproximateUnit` eventually dominate any positive strict
contraction `u ∈ I`. -/
theorem eventually_le_quasicentralApproximateUnit (I : TwoSidedIdeal A)
    {u : A} (huI : u ∈ I) (hu₀ : 0 ≤ u) (hu₁ : ‖u‖ < 1) :
    ∀ᶠ e in I.quasicentralApproximateUnit, u ≤ e :=
  (I.le_quasicentralApproximateUnit_iff.1 le_rfl).1 u huI hu₀ hu₁

/-- Elements along `I.quasicentralApproximateUnit` eventually belong to `I`. -/
theorem eventually_mem_quasicentralApproximateUnit (I : TwoSidedIdeal A) :
    ∀ᶠ e in I.quasicentralApproximateUnit, e ∈ I :=
  (I.le_quasicentralApproximateUnit_iff.1 le_rfl).2.1

/-- Elements along `I.quasicentralApproximateUnit` are eventually nonnegative. -/
theorem eventually_nonneg_quasicentralApproximateUnit (I : TwoSidedIdeal A) :
    ∀ᶠ e in I.quasicentralApproximateUnit, 0 ≤ e :=
  I.eventually_le_quasicentralApproximateUnit I.zero_mem le_rfl (by simp)

/-- Elements along `I.quasicentralApproximateUnit` eventually have norm at most `1`. -/
theorem eventually_norm_le_one_quasicentralApproximateUnit (I : TwoSidedIdeal A) :
    ∀ᶠ e in I.quasicentralApproximateUnit, ‖e‖ ≤ 1 :=
  (I.le_quasicentralApproximateUnit_iff.1 le_rfl).2.2.1

/-- Along `I.quasicentralApproximateUnit`, `e * x → x` for every `x ∈ I`. -/
theorem tendsto_mul_right_quasicentralApproximateUnit (I : TwoSidedIdeal A) {x : A} (hx : x ∈ I) :
    Tendsto (fun e => e * x) I.quasicentralApproximateUnit (𝓝 x) :=
  (I.le_quasicentralApproximateUnit_iff.1 le_rfl).2.2.2.1 x hx

/-- Along `I.quasicentralApproximateUnit`, `x * e → x` for every `x ∈ I`. -/
theorem tendsto_mul_left_quasicentralApproximateUnit (I : TwoSidedIdeal A) {x : A} (hx : x ∈ I) :
    Tendsto (fun e => x * e) I.quasicentralApproximateUnit (𝓝 x) :=
  (I.le_quasicentralApproximateUnit_iff.1 le_rfl).2.2.2.2.1 x hx

/-- Along `I.quasicentralApproximateUnit`, `e * a - a * e → 0` for every `a : A`. -/
theorem tendsto_mul_sub_mul_quasicentralApproximateUnit (I : TwoSidedIdeal A) (a : A) :
    Tendsto (fun e => e * a - a * e) I.quasicentralApproximateUnit (𝓝 0) :=
  (I.le_quasicentralApproximateUnit_iff.1 le_rfl).2.2.2.2.2 a

end FilterDef

section FilterNeBot

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private def quasicentralBasisSet (I : TwoSidedIdeal A)
    (p : {u : A // u ∈ I ∧ 0 ≤ u ∧ ‖u‖ < 1} × {G : Finset A // ∀ x ∈ G, x ∈ I} ×
      Finset A × {δ : ℝ // 0 < δ}) : Set A :=
  {e : A | e ∈ I ∧ p.1.1 ≤ e ∧ ‖e‖ < 1 ∧
    (∀ x ∈ p.2.1.1, ‖e * x - x‖ < p.2.2.2.1 ∧ ‖x * e - x‖ < p.2.2.2.1) ∧
    (∀ a ∈ p.2.2.1, ‖e * a - a * e‖ < p.2.2.2.1)}

private theorem isBasis_quasicentralBasisSet (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    Filter.IsBasis (fun _ => True) (quasicentralBasisSet I) := by
  classical
  let S := I.toNonUnitalStarSubalgebra
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  have _ : StarOrderedRing S := Subtype.starOrderedRing S
  refine ⟨⟨(⟨0, I.zero_mem, le_rfl, by simp⟩, ⟨∅, by simp⟩, ∅, ⟨1, zero_lt_one⟩), trivial⟩, ?_⟩
  intro p q _ _
  let u₁ : S := ⟨p.1.1, I.mem_toNonUnitalStarSubalgebra.2 p.1.2.1⟩
  let u₂ : S := ⟨q.1.1, I.mem_toNonUnitalStarSubalgebra.2 q.1.2.1⟩
  obtain ⟨u₃, ⟨hu₃₀, hu₃_ball⟩, hu₁₃, hu₂₃⟩ := CStarAlgebra.directedOn_nonneg_ball (A := S)
    u₁ ⟨p.1.2.2.1, by simpa [Metric.mem_ball] using p.1.2.2.2⟩
    u₂ ⟨q.1.2.2.1, by simpa [Metric.mem_ball] using q.1.2.2.2⟩
  refine ⟨(⟨(u₃ : A), I.mem_toNonUnitalStarSubalgebra.1 u₃.2, hu₃₀,
      by simpa [Metric.mem_ball] using hu₃_ball⟩,
     ⟨p.2.1.1 ∪ q.2.1.1, fun x hx =>
        (Finset.mem_union.1 hx).elim (p.2.1.2 x) (q.2.1.2 x)⟩,
     p.2.2.1 ∪ q.2.2.1,
     ⟨min p.2.2.2.1 q.2.2.2.1, lt_min p.2.2.2.2 q.2.2.2.2⟩), trivial, fun e he => ⟨?_, ?_⟩⟩
  · refine ⟨he.1, (Subtype.coe_le_coe.2 hu₁₃).trans he.2.1, he.2.2.1,
      fun x hx => ?_, fun a ha => ?_⟩
    · have h := he.2.2.2.1 x (Finset.mem_union_left _ hx)
      exact ⟨h.1.trans_le (min_le_left _ _), h.2.trans_le (min_le_left _ _)⟩
    · exact (he.2.2.2.2 a (Finset.mem_union_left _ ha)).trans_le (min_le_left _ _)
  · refine ⟨he.1, (Subtype.coe_le_coe.2 hu₂₃).trans he.2.1, he.2.2.1,
      fun x hx => ?_, fun a ha => ?_⟩
    · have h := he.2.2.2.1 x (Finset.mem_union_right _ hx)
      exact ⟨h.1.trans_le (min_le_right _ _), h.2.trans_le (min_le_right _ _)⟩
    · exact (he.2.2.2.2 a (Finset.mem_union_right _ ha)).trans_le (min_le_right _ _)

/-- For every closed two-sided ideal `I`, `I.quasicentralApproximateUnit` is a proper filter. -/
instance neBot_quasicentralApproximateUnit (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    I.quasicentralApproximateUnit.NeBot := by
  have hB := isBasis_quasicentralBasisSet I
  have hlB_neBot : hB.filter.NeBot :=
    hB.hasBasis.neBot_iff.2 fun {p} _ =>
      I.exists_mem_le_norm_lt_one_mul_sub_lt p.1.2.1 p.1.2.2.1 p.1.2.2.2
        p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2.2
  have hlB_le : hB.filter ≤ I.quasicentralApproximateUnit := by
    rw [I.le_quasicentralApproximateUnit_iff]
    refine ⟨fun u huI hu₀ hu₁ => ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun a => ?_⟩
    · exact Filter.mem_of_superset
        (hB.hasBasis.mem_of_mem
          (i := (⟨u, huI, hu₀, hu₁⟩, ⟨∅, by simp⟩, ∅, ⟨1, zero_lt_one⟩)) trivial)
        fun _ he => he.2.1
    · exact Filter.mem_of_superset
        (hB.hasBasis.mem_of_mem
          (i := (⟨0, I.zero_mem, le_rfl, by simp⟩, ⟨∅, by simp⟩, ∅, ⟨1, zero_lt_one⟩)) trivial)
        fun _ he => he.1
    · exact Filter.mem_of_superset
        (hB.hasBasis.mem_of_mem
          (i := (⟨0, I.zero_mem, le_rfl, by simp⟩, ⟨∅, by simp⟩, ∅, ⟨1, zero_lt_one⟩)) trivial)
        fun _ he => he.2.2.1.le
    · rw [Metric.tendsto_nhds]
      intro ε hε
      exact Filter.mem_of_superset
        (hB.hasBasis.mem_of_mem
          (i := (⟨0, I.zero_mem, le_rfl, by simp⟩, ⟨{x}, by simpa using hx⟩, ∅, ⟨ε, hε⟩)) trivial)
        fun _ he => by simpa [dist_eq_norm] using (he.2.2.2.1 x (Finset.mem_singleton_self x)).1
    · rw [Metric.tendsto_nhds]
      intro ε hε
      exact Filter.mem_of_superset
        (hB.hasBasis.mem_of_mem
          (i := (⟨0, I.zero_mem, le_rfl, by simp⟩, ⟨{x}, by simpa using hx⟩, ∅, ⟨ε, hε⟩)) trivial)
        fun _ he => by simpa [dist_eq_norm] using (he.2.2.2.1 x (Finset.mem_singleton_self x)).2
    · rw [Metric.tendsto_nhds]
      intro ε hε
      exact Filter.mem_of_superset
        (hB.hasBasis.mem_of_mem
          (i := (⟨0, I.zero_mem, le_rfl, by simp⟩, ⟨∅, by simp⟩, {a}, ⟨ε, hε⟩)) trivial)
        fun _ he => by simpa [dist_eq_norm] using he.2.2.2.2 a (Finset.mem_singleton_self a)
  exact hlB_neBot.mono hlB_le

/-- **Arveson's quasicentral approximate unit theorem.** Every closed two-sided ideal of a
(possibly nonunital) C⋆-algebra has a positive contractive approximate unit that is quasicentral
in `A`. -/
theorem exists_quasicentral_approximateUnit (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ I ∧ 0 ≤ e ∧ ‖e‖ ≤ 1) ∧
      (∀ a ∈ I, Tendsto (fun e => e * a) l (𝓝 a)) ∧
      (∀ a ∈ I, Tendsto (fun e => a * e) l (𝓝 a)) ∧
      (∀ a : A, Tendsto (fun e => e * a - a * e) l (𝓝 0)) :=
  ⟨I.quasicentralApproximateUnit, I.neBot_quasicentralApproximateUnit,
    I.eventually_mem_quasicentralApproximateUnit.and
      (I.eventually_nonneg_quasicentralApproximateUnit.and
        I.eventually_norm_le_one_quasicentralApproximateUnit),
    fun _ h => I.tendsto_mul_right_quasicentralApproximateUnit h,
    fun _ h => I.tendsto_mul_left_quasicentralApproximateUnit h,
    I.tendsto_mul_sub_mul_quasicentralApproximateUnit⟩

end FilterNeBot

section Sequential

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Sequential monotone quasicentral approximate units.** For a closed two-sided ideal `I` of a
separable C⋆-algebra `A`, there is a monotone increasing sequence of positive strict contractions
in `I` forming a quasicentral approximate unit for `I` in `A`. -/
theorem exists_seq_monotone_quasicentral_approximateUnit [TopologicalSpace.SeparableSpace A]
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    ∃ u : ℕ → A, Monotone u ∧ (∀ n, u n ∈ I ∧ 0 ≤ u n ∧ ‖u n‖ < 1) ∧
      (∀ x ∈ I, Tendsto (fun n => u n * x) atTop (𝓝 x)) ∧
      (∀ x ∈ I, Tendsto (fun n => x * u n) atTop (𝓝 x)) ∧
      (∀ a : A, Tendsto (fun n => u n * a - a * u n) atTop (𝓝 0)) := by
  classical
  have : Nonempty I := ⟨⟨0, I.zero_mem⟩⟩
  obtain ⟨dA, hdA⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨dI, hdI⟩ := TopologicalSpace.exists_dense_seq I
  -- Step 1: Recursively build a monotone sequence of positive strict contractions in `I` that
  -- approximates the unit on `dI 0, ..., dI n` and commutes with `dA 0, ..., dA n` within
  -- `1 / (n + 1)` at stage `n + 1`.
  let State := {e : A // e ∈ I ∧ 0 ≤ e ∧ ‖e‖ < 1}
  let step : ∀ (n : ℕ) (prev : State),
      {e : State // prev.1 ≤ e.1 ∧
        (∀ k < n + 1, ‖e.1 * (dI k : A) - (dI k : A)‖ < 1 / (n + 1 : ℝ) ∧
          ‖(dI k : A) * e.1 - (dI k : A)‖ < 1 / (n + 1 : ℝ)) ∧
        (∀ k < n + 1, ‖e.1 * dA k - dA k * e.1‖ < 1 / (n + 1 : ℝ))} := by
    intro n prev
    let G : Finset A := (Finset.range (n + 1)).image (fun k => (dI k : A))
    let F : Finset A := (Finset.range (n + 1)).image dA
    have hG : ∀ x ∈ G, x ∈ I := fun x hx => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      exact (dI k).2
    have hex := I.exists_mem_le_norm_lt_one_mul_sub_lt prev.2.1 prev.2.2.1 prev.2.2.2
      G hG F (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ))
    let e := Classical.choose hex
    have he := Classical.choose_spec hex
    exact ⟨⟨e, he.1, prev.2.2.1.trans he.2.1, he.2.2.1⟩, he.2.1,
      fun k hk => he.2.2.2.1 (dI k : A) (Finset.mem_image_of_mem _ (Finset.mem_range.2 hk)),
      fun k hk => he.2.2.2.2 (dA k) (Finset.mem_image_of_mem _ (Finset.mem_range.2 hk))⟩
  let seq : ℕ → State :=
    Nat.rec ⟨0, I.zero_mem, le_rfl, by simp⟩ (fun n prev => (step n prev).1)
  let u : ℕ → A := fun n => (seq n).1
  have hu_prop (n : ℕ) : u n ∈ I ∧ 0 ≤ u n ∧ ‖u n‖ < 1 := (seq n).2
  have hu_mono : Monotone u :=
    monotone_nat_of_le_succ fun n => (step n (seq n)).2.1
  have hu_step_I (n k : ℕ) (hk : k < n + 1) :
      ‖u (n + 1) * (dI k : A) - (dI k : A)‖ < 1 / (n + 1 : ℝ) ∧
        ‖(dI k : A) * u (n + 1) - (dI k : A)‖ < 1 / (n + 1 : ℝ) :=
    (step n (seq n)).2.2.1 k hk
  have hu_step_A (n k : ℕ) (hk : k < n + 1) :
      ‖u (n + 1) * dA k - dA k * u (n + 1)‖ < 1 / (n + 1 : ℝ) :=
    (step n (seq n)).2.2.2 k hk
  -- Step 2: Convergence on the dense sequences `dI` and `dA`, then extend to `I` and `A` by
  -- equicontinuity since `‖u n‖ ≤ 1`.
  have hrate : ∀ {g : ℕ → A} {y : A} {k : ℕ},
      (∀ m, k < m + 1 → ‖g (m + 1) - y‖ < 1 / (m + 1 : ℝ)) →
      Tendsto g atTop (𝓝 y) := by
    intro g y k hg
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨max (k + 1) (N + 1), fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hkm : k < m + 1 := by omega
    have hNm : N + 1 ≤ m + 1 := by omega
    rw [dist_eq_norm]
    exact (hg m hkm).trans_le <|
      (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hNm)).trans hN.le
  have hclosed_right : IsClosed {x : I | Tendsto (fun n => u n * (x : A)) atTop (𝓝 (x : A))} :=
    (Metric.equicontinuous_of_continuity_modulus id tendsto_id
      (fun n (x : I) => u n * (x : A)) fun x y n => by
        rw [dist_eq_norm, ← mul_sub, Subtype.dist_eq, dist_eq_norm]
        exact (norm_mul_le _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hu_prop n).2.2.le)).isClosed_setOfPred_tendsto
      continuous_subtype_val
  have hclosed_left : IsClosed {x : I | Tendsto (fun n => (x : A) * u n) atTop (𝓝 (x : A))} :=
    (Metric.equicontinuous_of_continuity_modulus id tendsto_id
      (fun n (x : I) => (x : A) * u n) fun x y n => by
        rw [dist_eq_norm, ← sub_mul, Subtype.dist_eq, dist_eq_norm]
        exact (norm_mul_le _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (hu_prop n).2.2.le)).isClosed_setOfPred_tendsto
      continuous_subtype_val
  have hmod : Tendsto (fun t : ℝ => 2 * t) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (2 : ℝ)
  have hclosed_comm :
      IsClosed {a : A | Tendsto (fun n => u n * a - a * u n) atTop (𝓝 0)} :=
    (Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => 2 * t) hmod
      (fun n (a : A) => u n * a - a * u n) fun a b n => by
        have hsub : (u n * a - a * u n) - (u n * b - b * u n) =
            u n * (a - b) - (a - b) * u n := by noncomm_ring
        rw [dist_eq_norm, dist_eq_norm, hsub]
        calc
          ‖u n * (a - b) - (a - b) * u n‖
              ≤ ‖u n * (a - b)‖ + ‖(a - b) * u n‖ := norm_sub_le _ _
          _ ≤ 1 * ‖a - b‖ + ‖a - b‖ * 1 := add_le_add
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hu_prop n).2.2.le
                (norm_nonneg _)))
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hu_prop n).2.2.le
                (norm_nonneg _)))
          _ = 2 * ‖a - b‖ := by ring).isClosed_setOfPred_tendsto continuous_const
  refine ⟨u, hu_mono, hu_prop, fun x hx => ?_, fun x hx => ?_, fun a => ?_⟩
  · have hcl : (univ : Set I) ⊆ {y : I | Tendsto (fun n => u n * (y : A)) atTop (𝓝 (y : A))} :=
      hdI.closure_eq ▸ closure_minimal (by rintro _ ⟨k, rfl⟩; exact hrate fun m hk =>
        (hu_step_I m k hk).1) hclosed_right
    exact hcl (a := ⟨x, hx⟩) trivial
  · have hcl : (univ : Set I) ⊆ {y : I | Tendsto (fun n => (y : A) * u n) atTop (𝓝 (y : A))} :=
      hdI.closure_eq ▸ closure_minimal (by rintro _ ⟨k, rfl⟩; exact hrate fun m hk =>
        (hu_step_I m k hk).2) hclosed_left
    exact hcl (a := ⟨x, hx⟩) trivial
  · have hcl : (univ : Set A) ⊆ {b : A | Tendsto (fun n => u n * b - b * u n) atTop (𝓝 0)} :=
      hdA.closure_eq ▸ closure_minimal
        (by rintro _ ⟨k, rfl⟩; exact hrate fun m hk => by simpa using hu_step_A m k hk)
        hclosed_comm
    exact hcl (a := a) trivial

end Sequential

end TwoSidedIdeal
