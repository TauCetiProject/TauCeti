/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.ShiftedResolventTransform
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.LocallyConstant.Preconnected
import TauCeti.Topology.Order.Interval

/-!
# The spectral flow of a path of operators on a compactly embedded common domain

Let `ι : D →L H` be a compact operator from a Banach space `D` into a Hilbert space `H`, and let
`A : ℝ → (D →L H)` be a continuous path of operators which are symmetric through `ι`,
`⟪A t x, ι y⟫ = ⟪ι x, A t y⟫`, each with some invertible shift `c₀ ι - A t`. This is how a path
of unbounded operators with a common domain `range ι` and compact resolvent is given by bounded
operators on that domain, such as the asymptotic operators `J₀ ∂ₜ + S(t)` of the Floer equation
with `D = H¹` and `H = L²`. This file defines the **spectral flow** of such a path,
`TauCeti.domainSpectralFlow ι A a b`, the net number of eigenvalues of `A t` crossing `0` upwards
as `t` runs from `a` to `b`.

**Local definition.** At a real shift `c ≠ 0` for which `c ι - A u` is invertible, the shifted
resolvent transform `τ_c (A u) = c A u (c ι - A u)⁻¹`
(`ContinuousLinearMap.shiftedResolventTransform`) is a bounded self-adjoint Fredholm operator
which sends an eigenvector `ι x` of `A u` with eigenvalue `μ` to an eigenvector with eigenvalue
`c μ / (c - μ)`, an increasing function of `μ` near `0` vanishing exactly at `0`. Along an interval
`[s, t]` on which a single shift `c` is *admissible*, the spectral flow is therefore that of the
bounded path `τ_c ∘ A` (`TauCeti.spectralFlow`), and it does not depend on the admissible shift
(`TauCeti.spectralFlow_shiftedResolventTransform_eq`).

**Gluing.** A single shift need not be admissible along the whole path, but admissible shifts
exist near every time, uniformly on compact intervals
(`ContinuousLinearMap.exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub`). A
*spectral flow potential* (`TauCeti.IsDomainSpectralFlowPotential`) is an integer function `F` on
`[a, b]` whose increment over every subinterval `[s, t]` with an admissible shift `c ≠ 0` is the
spectral flow of `τ_c ∘ A` from `s` to `t`. Potentials exist
(`TauCeti.exists_isDomainSpectralFlowPotential`): a single admissible shift on an interval gives
a potential there, and potentials on adjacent intervals glue, since the bounded spectral flow is
additive. Any two potentials have the same increment over `[a, b]`
(`TauCeti.IsDomainSpectralFlowPotential.sub_eq_sub`), since their difference is locally constant.
The spectral flow `TauCeti.domainSpectralFlow ι A a b` is the increment `F b - F a` of any
potential (`TauCeti.domainSpectralFlow_eq_sub`). For `b < a` every function is vacuously a
potential, and the spectral flow is a junk value. The construction follows the spectral flow
potentials `TauCeti.IsSpectralFlowPotential` of the bounded spectral flow in
`TauCeti.Analysis.Fredholm.Spectral.Flow`.

**Properties.**

* Over an interval with a single admissible shift `c ≠ 0`, it is the spectral flow of the shifted
  resolvent transforms at `c`
  (`TauCeti.domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform`).
* It is additive under concatenation (`TauCeti.domainSpectralFlow_add_adjacent_intervals`),
  unchanged by a continuous change of parameter `φ` with `φ a ≤ φ b`
  (`TauCeti.domainSpectralFlow_comp_of_mapsTo`), and changes sign when `φ b ≤ φ a`
  (`TauCeti.domainSpectralFlow_comp_of_mapsTo_of_ge`), in particular under reversal
  (`TauCeti.domainSpectralFlow_comp_neg`).
* A path of invertible operators `A t : D → H` has no spectral flow
  (`TauCeti.domainSpectralFlow_eq_zero_of_forall_isInvertible`): every transform is invertible.
* Paths with the same potentials, possibly on different spaces, have the same spectral flow
  (`TauCeti.domainSpectralFlow_eq_of_isDomainSpectralFlowPotential_iff`). In particular it is
  unchanged by changes of trivialization (`TauCeti.domainSpectralFlow_comp_comp_symm`, in
  `TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Conjugation`).
* It extends the bounded spectral flow: on a finite-dimensional space, with `D = H` and `ι = 1`,
  every path of self-adjoint operators qualifies, and its spectral flow is
  `TauCeti.spectralFlow A a b` (`TauCeti.domainSpectralFlow_one`). Then `τ_c A` is the image
  of `A` under the fractional linear function `x ↦ x / (1 - x / c)`
  (`ContinuousLinearMap.shiftedResolventTransform_one_eq_mul_ringInverse`), which preserves the
  spectral flow (`TauCeti.spectralFlow_mul_ringInverse_one_add_smul`).

This is the spectral flow in the index formula `ind (∂ₛ - A) = -SF(A)` for the linearized Floer
operator, which is Fredholm on a compactly embedded common domain
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`); that formula is not proved
here.

## Main definitions

* `TauCeti.IsDomainSpectralFlowPotential ι A a b F`: `F` integrates the spectral flows of the
  shifted resolvent transforms over intervals with admissible shifts.
* `TauCeti.domainSpectralFlow ι A a b`: the spectral flow of the path `A` from `a` to `b`.

## Main results

* `TauCeti.exists_isDomainSpectralFlowPotential`,
  `TauCeti.IsDomainSpectralFlowPotential.sub_eq_sub`: existence and uniqueness of potentials.
* `TauCeti.domainSpectralFlow_eq_sub`: the spectral flow is the increment of any potential.
* `TauCeti.domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform`: the spectral flow over
  an interval with a single admissible shift.
* `TauCeti.domainSpectralFlow_eq_of_isDomainSpectralFlowPotential_iff`: paths with the same
  potentials have the same spectral flow.
* `TauCeti.domainSpectralFlow_add_adjacent_intervals`: concatenation.
* `TauCeti.IsDomainSpectralFlowPotential.comp_of_mapsTo`: potentials of reparametrized paths.
* `TauCeti.domainSpectralFlow_comp_of_mapsTo`, `TauCeti.domainSpectralFlow_comp_of_mapsTo_of_ge`,
  `TauCeti.domainSpectralFlow_comp_neg`: reparametrization and reversal.
* `TauCeti.domainSpectralFlow_eq_zero_of_forall_isInvertible`: paths of invertible operators.
* `TauCeti.domainSpectralFlow_one`: comparison with the bounded spectral flow in finite
  dimensions.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4.
* B. Booss-Bavnbek, M. Lesch and J. Phillips, *Unbounded Fredholm operators and spectral flow*,
  Canad. J. Math. **57** (2005), 225--250.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Potentials -/

/-- `F` is a **spectral flow potential** of the path `A` of operators on the common domain `D`,
embedded in `H` by `ι`, on `[a, b]`: over every subinterval `[s, t]` of `[a, b]` along which a
nonzero real shift `c` is admissible, that is, `c ι - A u` is invertible for every `u ∈ [s, t]`,
the increment of `F` is the spectral flow of the shifted resolvent transforms at `c`. -/
def IsDomainSpectralFlowPotential (ι : D →L[𝕜] H) (A : ℝ → D →L[𝕜] H) (a b : ℝ) (F : ℝ → ℤ) :
    Prop :=
  ∀ ⦃s t c : ℝ⦄, a ≤ s → s ≤ t → t ≤ b → c ≠ 0 →
    (∀ u ∈ Icc s t, ((c : 𝕜) • ι - A u).IsInvertible) →
      F t - F s = spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) s t

variable {ι : D →L[𝕜] H} {A : ℝ → D →L[𝕜] H}

/-- Unfolds `TauCeti.IsDomainSpectralFlowPotential`. -/
theorem isDomainSpectralFlowPotential_iff {a b : ℝ} {F : ℝ → ℤ} :
    IsDomainSpectralFlowPotential ι A a b F ↔ ∀ ⦃s t c : ℝ⦄, a ≤ s → s ≤ t → t ≤ b → c ≠ 0 →
      (∀ u ∈ Icc s t, ((c : 𝕜) • ι - A u).IsInvertible) →
        F t - F s = spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) s t :=
  Iff.rfl

/-- A spectral flow potential on `[a, b]` is a spectral flow potential on every subinterval. -/
theorem IsDomainSpectralFlowPotential.mono {a b a' b' : ℝ} {F : ℝ → ℤ}
    (hF : IsDomainSpectralFlowPotential ι A a b F) (ha : a ≤ a') (hb : b' ≤ b) :
    IsDomainSpectralFlowPotential ι A a' b' F :=
  fun _ _ _ hs hst ht hc hinv ↦ hF (ha.trans hs) hst (ht.trans hb) hc hinv

section Regular

variable [CompleteSpace D] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

omit [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Along an interval with an admissible shift `c ≠ 0`, the shifted resolvent transforms at `c`
of a continuous path of operators symmetric through a compact `ι` form a continuous path of
self-adjoint Fredholm operators. -/
private theorem regular_shiftedResolventTransform {s : Set ℝ} {c : ℝ}
    (hι : IsCompactOperator ι) (hA : ContinuousOn A s)
    (hsymm : ∀ t ∈ s, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫) (hc : c ≠ 0)
    (hinv : ∀ u ∈ s, ((c : 𝕜) • ι - A u).IsInvertible) :
    ContinuousOn (fun u ↦ ι.shiftedResolventTransform (A u) c) s ∧
      (∀ u ∈ s, IsSelfAdjoint (ι.shiftedResolventTransform (A u) c)) ∧
      ∀ u ∈ s, (ι.shiftedResolventTransform (A u) c).IsFredholm :=
  ⟨hA.shiftedResolventTransform hinv,
    fun u hu ↦ ι.isSelfAdjoint_shiftedResolventTransform (hsymm u hu),
    fun u hu ↦ ι.isFredholm_shiftedResolventTransform hι hc (hinv u hu)⟩

variable (hι : IsCompactOperator ι)
include hι

/-- Along an interval with an admissible shift `c ≠ 0`, the spectral flow of the shifted resolvent
transforms at `c` is additive. -/
private theorem spectralFlow_shiftedResolventTransform_add {s m t c : ℝ} (hsm : s ≤ m)
    (hmt : m ≤ t) (hA : ContinuousOn A (Icc s t))
    (hsymm : ∀ u ∈ Icc s t, ∀ x y, ⟪A u x, ι y⟫ = ⟪ι x, A u y⟫) (hc : c ≠ 0)
    (hinv : ∀ u ∈ Icc s t, ((c : 𝕜) • ι - A u).IsInvertible) :
    spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) s t =
      spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) s m +
        spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) m t := by
  obtain ⟨hτ, hsa, hF⟩ := regular_shiftedResolventTransform hι hA hsymm hc hinv
  exact spectralFlow_add_adjacent_intervals hsm hmt hτ hsa hF

/-- **A single admissible shift gives a potential.** If a shift `c₀ ≠ 0` is admissible on all of
`[p, q]`, the spectral flow of the shifted resolvent transforms at `c₀` from `p` is a potential on
`[p, q]`. -/
private theorem isDomainSpectralFlowPotential_spectralFlow {p q c₀ : ℝ}
    (hA : ContinuousOn A (Icc p q)) (hsymm : ∀ t ∈ Icc p q, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (hc₀ : c₀ ≠ 0) (hinv₀ : ∀ u ∈ Icc p q, ((c₀ : 𝕜) • ι - A u).IsInvertible) :
    IsDomainSpectralFlowPotential ι A p q
      (fun x ↦ spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c₀) p x) := by
  intro s t c hps hst htq hc hinv
  have hsub : Icc p t ⊆ Icc p q := Icc_subset_Icc le_rfl htq
  have hsub' : Icc s t ⊆ Icc p q := Icc_subset_Icc hps htq
  dsimp only
  rw [spectralFlow_shiftedResolventTransform_add hι hps hst (hA.mono hsub)
    (fun u hu ↦ hsymm u (hsub hu)) hc₀ (fun u hu ↦ hinv₀ u (hsub hu)), add_sub_cancel_left]
  exact spectralFlow_shiftedResolventTransform_eq hst hι (hA.mono hsub')
    (fun u hu ↦ hsymm u (hsub' hu)) hc hc₀ hinv (fun u hu ↦ hinv₀ u (hsub' hu))

/-- **Gluing potentials.** Potentials `F` on `[a, m]` and `G` on `[m, b]` glue to a potential on
`[a, b]`: `F` up to `m`, and `G` shifted to agree with `F` at `m` after it. -/
private theorem IsDomainSpectralFlowPotential.glue {a m b : ℝ} {F G : ℝ → ℤ}
    (hA : ContinuousOn A (Icc a b)) (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (hF : IsDomainSpectralFlowPotential ι A a m F) (hG : IsDomainSpectralFlowPotential ι A m b G) :
    IsDomainSpectralFlowPotential ι A a b
      (fun x ↦ if x ≤ m then F x else G x - G m + F m) := by
  intro s t c has hst htb hc hinv
  by_cases htm : t ≤ m
  · simp only [htm, hst.trans htm, ↓reduceIte]
    exact hF has hst htm hc hinv
  by_cases hsm : s ≤ m
  · -- The interval `[s, t]` straddles `m`.
    simp only [htm, hsm, ↓reduceIte]
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    rw [spectralFlow_shiftedResolventTransform_add hι hsm (not_le.1 htm).le (hA.mono hsub)
      (fun u hu ↦ hsymm u (hsub hu)) hc hinv,
      ← hF has hsm le_rfl hc fun u hu ↦ hinv u ⟨hu.1, hu.2.trans (not_le.1 htm).le⟩,
      ← hG le_rfl (not_le.1 htm).le htb hc fun u hu ↦ hinv u ⟨hsm.trans hu.1, hu.2⟩]
    ring
  · simp only [htm, hsm, ↓reduceIte]
    rw [← hG (not_le.1 hsm).le hst htb hc hinv]
    ring

omit [CompleteSpace H] [NormedAlgebra ℝ (H →L[𝕜] H)]
  [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Uniformly local nonzero admissible shifts on `[a, b]`. -/
private theorem exists_pos_forall_exists_ne_zero_isInvertible {a b : ℝ}
    (hA : ContinuousOn A (Icc a b)) (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∃ c : ℝ, c ≠ 0 ∧ ∀ u ∈ Icc a b, dist u t < δ →
      ((c : 𝕜) • ι - A u).IsInvertible := by
  obtain ⟨δ, hδ, h⟩ := ι.exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub hι
    isCompact_Icc hA h₀ zero_lt_one
  exact ⟨δ, hδ, fun t ht ↦ let ⟨c, hc, hinv⟩ := h t ht; ⟨c, hc.1.ne', hinv⟩⟩

/-- **Existence of spectral flow potentials** for a continuous path of operators symmetric through
a compact `ι`, each with some invertible shift. -/
theorem exists_isDomainSpectralFlowPotential {a b : ℝ} (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    ∃ F, IsDomainSpectralFlowPotential ι A a b F := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨0, fun s t _ has hst htb ↦ absurd (has.trans (hst.trans htb)) (not_le.2 hba)⟩
  obtain ⟨δ, hδ, hloc⟩ := exists_pos_forall_exists_ne_zero_isInvertible hι hA h₀
  -- The intervals `[a, m n]`, with `m n = min b (a + n δ / 2)`, carry potentials.
  set m : ℕ → ℝ := fun n ↦ min b (a + n * (δ / 2)) with hm
  have ham (n : ℕ) : a ≤ m n := le_min hab (le_add_of_nonneg_right (by positivity))
  have key (n : ℕ) : ∃ F, IsDomainSpectralFlowPotential ι A a (m n) F := by
    induction n with
    | zero =>
      refine ⟨0, fun s t c has hst htm _ _ ↦ ?_⟩
      have hta : t ≤ a := htm.trans (min_le_right _ _ |>.trans (by simp))
      obtain rfl : s = t := le_antisymm hst (hta.trans has)
      simp
    | succ n ih =>
      obtain ⟨F, hF⟩ := ih
      have hmn : m n ≤ m (n + 1) := min_le_min le_rfl (by push_cast; linarith)
      have hmb : m (n + 1) ≤ b := min_le_left _ _
      -- On `[m n, m (n + 1)]`, of length at most `δ / 2`, one shift is admissible.
      obtain ⟨c, hc, hinv⟩ := hloc (m n) ⟨ham n, hmn.trans hmb⟩
      have hsub : Icc (m n) (m (n + 1)) ⊆ Icc a b := Icc_subset_Icc (ham n) hmb
      have hinv' : ∀ u ∈ Icc (m n) (m (n + 1)), ((c : 𝕜) • ι - A u).IsInvertible := by
        intro u hu
        refine hinv u (hsub hu) ?_
        have hlen : m (n + 1) ≤ m n + δ / 2 := by
          simp only [hm]
          push_cast
          rcases le_total b (a + n * (δ / 2)) with h | h
          · rw [min_eq_left h]
            exact (min_le_left _ _).trans (by linarith)
          · rw [min_eq_right h]
            exact (min_le_right _ _).trans (by linarith)
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
        linarith [hu.2]
      have hG := isDomainSpectralFlowPotential_spectralFlow hι (hA.mono hsub)
        (fun u hu ↦ hsymm u (hsub hu)) hc hinv'
      exact ⟨_, hF.glue hι (hA.mono (Icc_subset_Icc le_rfl hmb))
        (fun u hu ↦ hsymm u (Icc_subset_Icc le_rfl hmb hu)) hG⟩
  -- Eventually `m n = b`.
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (δ / 2))
  have hmn : m n = b := min_eq_left (by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith)
  simpa [hmn] using key n

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **Uniqueness of spectral flow potentials**: any two potentials have the same increment over
`[a, b]`. Their difference is locally constant, since near every time some shift is admissible. -/
theorem IsDomainSpectralFlowPotential.sub_eq_sub {a b : ℝ} {F G : ℝ → ℤ}
    (hFp : IsDomainSpectralFlowPotential ι A a b F)
    (hGp : IsDomainSpectralFlowPotential ι A a b G) (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) : F b - F a = G b - G a := by
  obtain ⟨δ, hδ, hloc⟩ := exists_pos_forall_exists_ne_zero_isInvertible hι hA h₀
  have := isPreconnected_Icc.apply_eq_of_eventually_eq (f := fun x ↦ F x - G x) (fun t₀ ht₀ ↦ by
    obtain ⟨c, hc, hinv⟩ := hloc t₀ ht₀
    filter_upwards [inter_mem_nhdsWithin (Icc a b) (ball_mem_nhds t₀ hδ)] with u ⟨hu, huδ⟩
    -- Compare `F` and `G` over the interval between `t₀` and `u`.
    have hinv' : ∀ v ∈ uIcc t₀ u, ((c : 𝕜) • ι - A v).IsInvertible := fun v hv ↦
      have hv' := ordConnected_Icc.uIcc_subset_ball_inter ht₀ ⟨huδ, hu⟩ hv
      hinv v hv'.2 hv'.1
    rcases le_total t₀ u with h | h
    · rw [uIcc_of_le h] at hinv'
      have h₁ := hFp ht₀.1 h hu.2 hc hinv'
      have h₂ := hGp ht₀.1 h hu.2 hc hinv'
      linarith
    · rw [uIcc_of_ge h] at hinv'
      have h₁ := hFp hu.1 h ht₀.2 hc hinv'
      have h₂ := hGp hu.1 h ht₀.2 hc hinv'
      linarith) ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  linarith

end Regular

/-! ### Spectral flow -/

open scoped Classical in
/-- The **spectral flow** of the path `A` of operators on the common domain `D`, embedded in `H`
by `ι`, from `a` to `b`: the increment `F b - F a` of a spectral flow potential `F` of `A` on
`[a, b]`. For `a ≤ b`, a compact `ι` and a continuous path of operators symmetric through `ι`,
each with some invertible shift, potentials exist and all give the same value
(`TauCeti.domainSpectralFlow_eq_sub`); it is the net number of eigenvalues crossing `0` upwards.
Otherwise it is a junk value: in particular, for `b < a` every function is vacuously a potential,
so the value is arbitrary. -/
noncomputable def domainSpectralFlow (ι : D →L[𝕜] H) (A : ℝ → D →L[𝕜] H) (a b : ℝ) : ℤ :=
  if h : ∃ F, IsDomainSpectralFlowPotential ι A a b F then h.choose b - h.choose a else 0

/-- The spectral flow from `a` to `b` only depends on the path on `[a, b]`. -/
theorem domainSpectralFlow_congr {B : ℝ → D →L[𝕜] H} {a b : ℝ} (h : EqOn A B (Icc a b)) :
    domainSpectralFlow ι A a b = domainSpectralFlow ι B a b := by
  have key {A B : ℝ → D →L[𝕜] H} (h : EqOn A B (Icc a b)) (F : ℝ → ℤ)
      (hF : IsDomainSpectralFlowPotential ι A a b F) : IsDomainSpectralFlowPotential ι B a b F := by
    intro s t c has hst htb hc hinv
    have hEq : EqOn A B (Icc s t) := h.mono (Icc_subset_Icc has htb)
    rw [hF has hst htb hc fun u hu ↦ hEq hu ▸ hinv u hu]
    exact spectralFlow_congr fun u hu ↦ by simp only [hEq hu]
  have hpot : IsDomainSpectralFlowPotential ι A a b = IsDomainSpectralFlowPotential ι B a b :=
    funext fun F ↦ propext ⟨key h F, key h.symm F⟩
  unfold domainSpectralFlow
  rw [hpot]

/-- **Comparison of spectral flows.** Two paths on common domains, possibly embedded in different
Hilbert spaces, with the same spectral flow potentials on `[a, b]` have the same spectral flow. No
regularity of either path is assumed. -/
theorem domainSpectralFlow_eq_of_isDomainSpectralFlowPotential_iff {D' K : Type*}
    [NormedAddCommGroup D'] [NormedSpace 𝕜 D'] [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] [NormedAlgebra ℝ (K →L[𝕜] K)]
    [IsometricContinuousFunctionalCalculus ℝ (K →L[𝕜] K) IsSelfAdjoint] {ι' : D' →L[𝕜] K}
    {B : ℝ → D' →L[𝕜] K} {a b : ℝ}
    (h : ∀ F, IsDomainSpectralFlowPotential ι' B a b F ↔ IsDomainSpectralFlowPotential ι A a b F) :
    domainSpectralFlow ι' B a b = domainSpectralFlow ι A a b := by
  have hpot : IsDomainSpectralFlowPotential ι' B a b = IsDomainSpectralFlowPotential ι A a b :=
    funext fun F ↦ propext (h F)
  unfold domainSpectralFlow
  rw [hpot]

/-- The spectral flow over a single time vanishes. -/
@[simp]
theorem domainSpectralFlow_self (ι : D →L[𝕜] H) (A : ℝ → D →L[𝕜] H) (a : ℝ) :
    domainSpectralFlow ι A a a = 0 := by
  unfold domainSpectralFlow
  split_ifs <;> simp

variable [CompleteSpace D] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] (hι : IsCompactOperator ι)
include hι

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- The spectral flow is the increment of any spectral flow potential. -/
theorem domainSpectralFlow_eq_sub {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) {F : ℝ → ℤ}
    (hFp : IsDomainSpectralFlowPotential ι A a b F) : domainSpectralFlow ι A a b = F b - F a := by
  have h : ∃ F, IsDomainSpectralFlowPotential ι A a b F := ⟨F, hFp⟩
  simp only [domainSpectralFlow, h, ↓reduceDIte]
  exact h.choose_spec.sub_eq_sub hι hFp hab hA h₀

/-- **The spectral flow over an interval with a single admissible shift** `c ≠ 0` is the spectral
flow of the shifted resolvent transforms at `c`. -/
theorem domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform {a b c : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (hc : c ≠ 0) (hinv : ∀ t ∈ Icc a b, ((c : 𝕜) • ι - A t).IsInvertible) :
    domainSpectralFlow ι A a b =
      spectralFlow (fun t ↦ ι.shiftedResolventTransform (A t) c) a b := by
  rw [domainSpectralFlow_eq_sub hι hab hA (fun t ht ↦ ⟨c, hinv t ht⟩)
    (isDomainSpectralFlowPotential_spectralFlow hι hA hsymm hc hinv), spectralFlow_self, sub_zero]

/-- **Concatenation.** The spectral flow from `a` to `d` is the spectral flow from `a` to `b` plus
the spectral flow from `b` to `d`. -/
theorem domainSpectralFlow_add_adjacent_intervals {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d)
    (hA : ContinuousOn A (Icc a d)) (hsymm : ∀ t ∈ Icc a d, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a d, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι A a d = domainSpectralFlow ι A a b + domainSpectralFlow ι A b d := by
  obtain ⟨F, hFp⟩ := exists_isDomainSpectralFlowPotential hι hA hsymm h₀
  have h₁ : Icc a b ⊆ Icc a d := Icc_subset_Icc le_rfl hbd
  have h₂ : Icc b d ⊆ Icc a d := Icc_subset_Icc hab le_rfl
  rw [domainSpectralFlow_eq_sub hι (hab.trans hbd) hA h₀ hFp,
    domainSpectralFlow_eq_sub hι hab (hA.mono h₁) (fun t ht ↦ h₀ t (h₁ ht)) (hFp.mono le_rfl hbd),
    domainSpectralFlow_eq_sub hι hbd (hA.mono h₂) (fun t ht ↦ h₀ t (h₂ ht)) (hFp.mono hab le_rfl)]
  ring

/-- **A path of invertible operators has no spectral flow**: if every `A t : D → H` with
`t ∈ [a, b]` is invertible, no eigenvalue crosses `0`. Every shifted resolvent transform is then
invertible. -/
theorem domainSpectralFlow_eq_zero_of_forall_isInvertible {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (hinvA : ∀ t ∈ Icc a b, (A t).IsInvertible) : domainSpectralFlow ι A a b = 0 := by
  have h₀ (t : ℝ) (ht : t ∈ Icc a b) : ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible :=
    ⟨0, by simpa [ContinuousLinearMap.isInvertible_neg_iff] using hinvA t ht⟩
  -- Every transform `c A (c ι - A)⁻¹` is invertible, so the zero function is a potential.
  have hp : IsDomainSpectralFlowPotential ι A a b 0 := by
    intro s t c has hst htb hc hinv
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    obtain ⟨hτ, hsa, -⟩ := regular_shiftedResolventTransform hι (hA.mono hsub)
      (fun u hu ↦ hsymm u (hsub hu)) hc hinv
    rw [spectralFlow_eq_zero_of_forall_zero_notMem_spectrum hst hτ hsa fun u hu ↦ ?_]
    · simp
    rw [spectrum.zero_notMem_iff, ← ContinuousLinearMap.isInvertible_iff_isUnit,
      ContinuousLinearMap.shiftedResolventTransform_def,
      ContinuousLinearMap.isInvertible_smul_iff (RCLike.ofReal_ne_zero.2 hc)]
    exact (hinvA u (hsub hu)).comp (hinv u hu).inverse
  simp [domainSpectralFlow_eq_sub hι hab hA h₀ hp]

/-! ### Reparametrization -/

section Reparametrization

variable {φ : ℝ → ℝ} {a b p q : ℝ}

/-- A potential `F` of `A` on `[p, q]` gives the potential `F ∘ φ` of `A ∘ φ` on `[a, b]`. Over a
subinterval `[s, t]` with an admissible shift `c`, the shift is admissible along `φ '' [s, t]`,
an interval containing `φ s` and `φ t` on which the transforms form a regular path, so the
spectral flow of the reparametrized transforms is that of the transforms from `φ s` to `φ t`. -/
theorem IsDomainSpectralFlowPotential.comp_of_mapsTo {F : ℝ → ℤ}
    (hFp : IsDomainSpectralFlowPotential ι A p q F) (hφ : ContinuousOn φ (Icc a b))
    (hmaps : MapsTo φ (Icc a b) (Icc p q)) (hA : ContinuousOn A (Icc p q))
    (hsymm : ∀ t ∈ Icc p q, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫) :
    IsDomainSpectralFlowPotential ι (A ∘ φ) a b (F ∘ φ) := by
  intro s t c has hst htb hc hinv
  simp only [Function.comp_apply] at hinv ⊢
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hφst : ContinuousOn φ (Icc s t) := hφ.mono hsub
  -- The image `φ '' [s, t]` is a closed interval `[m, M]` inside `[p, q]`.
  set m := sInf (φ '' Icc s t)
  set M := sSup (φ '' Icc s t)
  have himg : φ '' Icc s t = Icc m M := hφst.image_Icc hst
  have hmapsI : MapsTo φ (Icc s t) (Icc m M) := himg ▸ mapsTo_image φ (Icc s t)
  have hIpq : Icc m M ⊆ Icc p q := himg ▸ (image_subset_iff.2 (hmaps.mono_left hsub))
  have hinvI : ∀ v ∈ Icc m M, ((c : 𝕜) • ι - A v).IsInvertible := by
    rw [← himg]
    rintro _ ⟨u, hu, rfl⟩
    exact hinv u hu
  obtain ⟨hτ, hsa, hF⟩ := regular_shiftedResolventTransform hι (hA.mono hIpq)
    (fun u hu ↦ hsymm u (hIpq hu)) hc hinvI
  have hs := hmapsI ⟨le_rfl, hst⟩
  have ht := hmapsI ⟨hst, le_rfl⟩
  rcases le_total (φ s) (φ t) with h | h
  · have hcomp := spectralFlow_comp_of_mapsTo (A := fun v ↦ ι.shiftedResolventTransform (A v) c)
      hst hφst hmapsI h hτ hsa hF
    simp only [Function.comp_def] at hcomp
    rw [hcomp]
    exact hFp (hIpq hs).1 h (hIpq ht).2 hc fun v hv ↦ hinvI v ⟨hs.1.trans hv.1, hv.2.trans ht.2⟩
  · have hcomp := spectralFlow_comp_of_mapsTo_of_ge
      (A := fun v ↦ ι.shiftedResolventTransform (A v) c) hst hφst hmapsI h hτ hsa hF
    simp only [Function.comp_def] at hcomp
    rw [hcomp, ← hFp (hIpq ht).1 h (hIpq hs).2 hc fun v hv ↦
      hinvI v ⟨ht.1.trans hv.1, hv.2.trans hs.2⟩]
    ring

/-- The spectral flow of the reparametrized path `A ∘ φ` from `a` to `b` is the increment
`F (φ b) - F (φ a)` of a potential `F` of `A` on `[p, q]`. -/
private theorem domainSpectralFlow_comp_eq_sub (hab : a ≤ b) {F : ℝ → ℤ}
    (hFp : IsDomainSpectralFlowPotential ι A p q F) (hφ : ContinuousOn φ (Icc a b))
    (hmaps : MapsTo φ (Icc a b) (Icc p q)) (hA : ContinuousOn A (Icc p q))
    (hsymm : ∀ t ∈ Icc p q, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc p q, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι (A ∘ φ) a b = F (φ b) - F (φ a) :=
  domainSpectralFlow_eq_sub hι hab (hA.comp hφ hmaps) (fun t ht ↦ h₀ (φ t) (hmaps ht))
    (hFp.comp_of_mapsTo hι hφ hmaps hA hsymm)

/-- **Reparametrization.** For `φ` continuous on `[a, b]` with `φ a ≤ φ b`, mapping `[a, b]` into
an interval `[p, q]` along which `A` is a continuous path of operators symmetric through `ι`, each
with some invertible shift, the spectral flow of `A ∘ φ` from `a` to `b` is the spectral flow of
`A` from `φ a` to `φ b`. The map `φ` need not be monotone. -/
theorem domainSpectralFlow_comp_of_mapsTo (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hmaps : MapsTo φ (Icc a b) (Icc p q)) (hφab : φ a ≤ φ b) (hA : ContinuousOn A (Icc p q))
    (hsymm : ∀ t ∈ Icc p q, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc p q, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι (A ∘ φ) a b = domainSpectralFlow ι A (φ a) (φ b) := by
  obtain ⟨F, hFp⟩ := exists_isDomainSpectralFlowPotential hι hA hsymm h₀
  have ha := hmaps ⟨le_rfl, hab⟩
  have hb := hmaps ⟨hab, le_rfl⟩
  have hsub : Icc (φ a) (φ b) ⊆ Icc p q := Icc_subset_Icc ha.1 hb.2
  rw [domainSpectralFlow_comp_eq_sub hι hab hFp hφ hmaps hA hsymm h₀,
    domainSpectralFlow_eq_sub hι hφab (hA.mono hsub) (fun t ht ↦ h₀ t (hsub ht))
      (hFp.mono ha.1 hb.2)]

/-- **Reparametrization reversing the direction.** For `φ` continuous on `[a, b]` with
`φ b ≤ φ a`, mapping `[a, b]` into an interval `[p, q]` along which `A` is a continuous path of
operators symmetric through `ι`, each with some invertible shift, the spectral flow of `A ∘ φ`
from `a` to `b` is minus the spectral flow of `A` from `φ b` to `φ a`. -/
theorem domainSpectralFlow_comp_of_mapsTo_of_ge (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hmaps : MapsTo φ (Icc a b) (Icc p q)) (hφba : φ b ≤ φ a) (hA : ContinuousOn A (Icc p q))
    (hsymm : ∀ t ∈ Icc p q, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc p q, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι (A ∘ φ) a b = -domainSpectralFlow ι A (φ b) (φ a) := by
  obtain ⟨F, hFp⟩ := exists_isDomainSpectralFlowPotential hι hA hsymm h₀
  have ha := hmaps ⟨le_rfl, hab⟩
  have hb := hmaps ⟨hab, le_rfl⟩
  have hsub : Icc (φ b) (φ a) ⊆ Icc p q := Icc_subset_Icc hb.1 ha.2
  rw [domainSpectralFlow_comp_eq_sub hι hab hFp hφ hmaps hA hsymm h₀,
    domainSpectralFlow_eq_sub hι hφba (hA.mono hsub) (fun t ht ↦ h₀ t (hsub ht))
      (hFp.mono hb.1 ha.2), neg_sub]

end Reparametrization

/-- **Reversal.** Running the path backwards changes the sign of the spectral flow. -/
theorem domainSpectralFlow_comp_neg {a b : ℝ} (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, ∀ x y, ⟪A t x, ι y⟫ = ⟪ι x, A t y⟫)
    (h₀ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) :
    domainSpectralFlow ι (fun t ↦ A (-t)) (-b) (-a) = -domainSpectralFlow ι A a b := by
  have h := domainSpectralFlow_comp_of_mapsTo_of_ge (A := A) (φ := Neg.neg) hι (neg_le_neg hab)
    continuous_neg.continuousOn (fun _ ht ↦ ⟨le_neg.2 ht.2, neg_le.2 ht.1⟩) (by simpa using hab)
    hA hsymm h₀
  rw [neg_neg, neg_neg] at h
  exact h

omit hι

/-! ### Comparison with the bounded spectral flow -/

/-- **The spectral flow extends the bounded spectral flow.** On a finite-dimensional space `H`,
take `D = H` with `ι = 1`. Every continuous path of self-adjoint operators qualifies, and its
spectral flow as a path on the common domain `H` is its spectral flow
`TauCeti.spectralFlow A a b` as a path of bounded operators. -/
theorem domainSpectralFlow_one [FiniteDimensional 𝕜 H] {A : ℝ → H →L[𝕜] H} {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) :
    domainSpectralFlow 1 A a b = spectralFlow A a b := by
  -- A shift `c` above every `‖A t‖` is admissible on all of `[a, b]`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  set c : ℝ := max C 0 + 1
  have hc : 0 < c := by positivity
  have hunit (t : ℝ) (ht : t ∈ Icc a b) : IsUnit ((c : 𝕜) • (1 : H →L[𝕜] H) - A t) := by
    have hnot : (c : 𝕜) ∉ spectrum 𝕜 (A t) := fun hmem ↦ by
      have := spectrum.norm_le_norm_of_mem hmem
      rw [RCLike.norm_ofReal, abs_of_pos hc] at this
      linarith [hC t ht, le_max_left C 0]
    rwa [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one] at hnot
  have hinv (t : ℝ) (ht : t ∈ Icc a b) : ((c : 𝕜) • (1 : H →L[𝕜] H) - A t).IsInvertible :=
    ContinuousLinearMap.isInvertible_iff_isUnit.2 (hunit t ht)
  have hsymm (t : ℝ) (ht : t ∈ Icc a b) (x y : H) : ⟪A t x, (1 : H →L[𝕜] H) y⟫ =
      ⟪(1 : H →L[𝕜] H) x, A t y⟫ := (hsa t ht).isSymmetric x y
  have hι : IsCompactOperator (1 : H →L[𝕜] H) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := 𝕜)).2 inferInstance
  rw [domainSpectralFlow_eq_spectralFlow_shiftedResolventTransform hι hab hA hsymm hc.ne' hinv]
  -- The transform is `A (1 - A / c)⁻¹`, the image of `A` under `x ↦ x / (1 - x / c)`.
  rw [spectralFlow_congr fun t ht ↦
    ContinuousLinearMap.shiftedResolventTransform_one_eq_mul_ringInverse hc.ne' (hinv t ht)]
  exact spectralFlow_mul_ringInverse_one_add_smul hab hA hsa
    (fun t _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    fun t ht ↦ ContinuousLinearMap.isUnit_one_add_neg_inv_smul hc.ne' (hinv t ht)

end TauCeti
