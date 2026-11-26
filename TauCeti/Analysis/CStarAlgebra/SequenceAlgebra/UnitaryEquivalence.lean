/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import TauCeti.Analysis.CStarAlgebra.SequenceAlgebra.Lifting
import Mathlib.Topology.DenseEmbedding
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Order.Filter.Ultrafilter

/-!
# Exact unitary implementation in C⋆-sequence algebras and ultrapowers

Norm sequence algebras and ultrapowers convert approximate unitary equivalence into exact unitary
conjugacy:

* **Diagonal transfer** (`TauCeti.ApproximatelyUnitarilyEquivalent.cstarFilterQuotient_diag_iff`,
  `TauCeti.ApproximatelyUnitarilyEquivalent.of_unitary_cstarFilterQuotient_diag`): without
  separability, `φ ψ : A →⋆ₙₐ[ℂ] B` are approximately unitarily equivalent if and only if
  `diag B l ∘ φ` and `diag B l ∘ ψ` are in `CStarFilterQuotient B l` (`[l.NeBot]`).
* **Exact implementation**
  (`TauCeti.ApproximatelyUnitarilyEquivalent.iff_exists_unitary_cstarFilterQuotient`, specialized to
  `CStarSequenceAlgebra B` and `CStarUltrapower B ω`): for separable `A` and `l ≤ atTop` on `ℕ`,
  approximate unitary equivalence into `CStarFilterQuotient B l` is exact unitary conjugacy.

## References

* E. Kirchberg, N. C. Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra `𝒪₂`*,
  J. Reine Angew. Math. 525 (2000), Lemma 1.12 (`arXiv:funct-an/9712002`).
* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Proposition 6.2.4.
-/

public section

open Filter Topology
open scoped ENNReal CStarAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

section DiagonalTransfer

variable {ι : Type*} {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B] [Nontrivial B]

/-- Postcomposing `φ ψ : A →⋆ₙₐ[ℂ] B` with the diagonal embedding into `CStarFilterQuotient B l`
preserves approximate unitary equivalence. -/
theorem comp_cstarFilterQuotient_diag (l : Filter ι) {φ ψ : A →⋆ₙₐ[ℂ] B}
    (h : ApproximatelyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent
      ((CStarFilterQuotient.diag B l).comp φ) ((CStarFilterQuotient.diag B l).comp ψ) :=
  h.postcomp (CStarFilterQuotient.diag B l)

/-- For any nontrivial filter `l`, approximate unitary equivalence of `diag B l ∘ φ` and
`diag B l ∘ ψ` in `CStarFilterQuotient B l` is equivalent to approximate unitary equivalence of `φ`
and `ψ` in `B` (without separability). -/
theorem cstarFilterQuotient_diag_iff {l : Filter ι} [l.NeBot] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent
        ((CStarFilterQuotient.diag B l).comp φ) ((CStarFilterQuotient.diag B l).comp ψ) ↔
      ApproximatelyUnitarilyEquivalent φ ψ := by
  refine ⟨fun h ↦ (approximatelyUnitarilyEquivalent_def φ ψ).mpr fun F ε hε ↦ ?_,
    comp_cstarFilterQuotient_diag l⟩
  obtain ⟨U, hU⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp h F ε hε
  obtain ⟨u, hu⟩ := CStarFilterQuotient.exists_unitary_family_mk_eq l U
  have hev : ∀ a ∈ F, ∀ᶠ i in l, ‖(u i : B) * φ a * star (u i : B) - ψ a‖ < ε := fun a ha ↦ by
    let z : lp (fun _ : ι ↦ B) ∞ :=
      (lp.unitaryEquiv.symm u : lp _ ∞) * lp.constNonUnitalStarAlgHom ℂ ι B (φ a) *
        star (lp.unitaryEquiv.symm u : lp _ ∞) - lp.constNonUnitalStarAlgHom ℂ ι B (ψ a)
    have hmk : CStarFilterQuotient.mk B l z =
        (U : CStarFilterQuotient B l) * CStarFilterQuotient.diag B l (φ a) *
          star (U : CStarFilterQuotient B l) - CStarFilterQuotient.diag B l (ψ a) := by
      simp [z, map_star, hu, CStarFilterQuotient.diag_eq_mk_const]
    refine (CStarFilterQuotient.eventually_norm_lt_of_norm_mk_lt z (hmk ▸ hU a ha)).mono fun i hi ↦
      by simpa only [z, lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply,
        lp.star_apply, lp.coe_unitaryEquiv_symm_apply, lp.constNonUnitalStarAlgHom_apply] using hi
  obtain ⟨i, hi⟩ := (F.eventually_all.mpr hev).exists
  exact ⟨u i, hi⟩

/-- Exact unitary conjugacy of `diag B l ∘ φ` and `diag B l ∘ ψ` in `CStarFilterQuotient B l`
implies approximate unitary equivalence of `φ` and `ψ` (without separability). -/
theorem of_unitary_cstarFilterQuotient_diag {l : Filter ι} [l.NeBot] {φ ψ : A →⋆ₙₐ[ℂ] B}
    (U : unitary (CStarFilterQuotient B l))
    (hU : ∀ a, (U : CStarFilterQuotient B l) * CStarFilterQuotient.diag B l (φ a) *
      star (U : CStarFilterQuotient B l) = CStarFilterQuotient.diag B l (ψ a)) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  (cstarFilterQuotient_diag_iff (l := l)).mp <| .of_unitary U fun a ↦
    (congrArg (fun x ↦ (U : CStarFilterQuotient B l) * x * star (U : CStarFilterQuotient B l))
      (NonUnitalStarAlgHom.comp_apply (CStarFilterQuotient.diag B l) φ a)).trans
      ((hU a).trans (NonUnitalStarAlgHom.comp_apply (CStarFilterQuotient.diag B l) ψ a).symm)

end DiagonalTransfer

section ExactImplementation

/-- Diagonal selection along a filter `l ≤ atTop` on `ℕ`: given bounded sequences `x j`, `y j` and
unitary families `u k : ℕ → unitary B` whose quotient classes conjugate `x j` within `1 / (k + 1)`
of `y j` for `j < k`, a single unitary sequence `v : ℕ → unitary B` conjugates every `x j`
asymptotically to `y j` along `l`. -/
private theorem exists_unitary_seq_tendsto_of_approx {B : Type*} [CStarAlgebra B] [Nontrivial B]
    {l : Filter ℕ} (hl : l ≤ atTop) (x y : ℕ → lp (fun _ : ℕ ↦ B) ∞)
    (u : ℕ → ℕ → unitary B)
    (hu : ∀ k : ℕ, ∀ j < k,
      ‖CStarFilterQuotient.mk B l (lp.unitaryEquiv.symm (u k)) *
          CStarFilterQuotient.mk B l (x j) *
          star (CStarFilterQuotient.mk B l (lp.unitaryEquiv.symm (u k))) -
        CStarFilterQuotient.mk B l (y j)‖ < 1 / ((k : ℝ) + 1)) :
    ∃ v : ℕ → unitary B,
      ∀ j : ℕ, Tendsto (fun n ↦ ‖(v n : B) * x j n * star (v n : B) - y j n‖) l (𝓝 0) := by
  let err (w : ℕ → unitary B) (j n : ℕ) : ℝ := ‖(w n : B) * x j n * star (w n : B) - y j n‖
  let P (k n : ℕ) : Prop := ∀ j < k, err (u k) j n < 1 / ((k : ℝ) + 1)
  have hPl (k : ℕ) : ∀ᶠ n in l, P k n := by
    have hall : ∀ j ∈ Finset.range k, ∀ᶠ n in l, err (u k) j n < 1 / ((k : ℝ) + 1) := fun j hj ↦ by
      let z : lp (fun _ : ℕ ↦ B) ∞ :=
        (lp.unitaryEquiv.symm (u k) : lp _ ∞) * x j *
          star (lp.unitaryEquiv.symm (u k) : lp _ ∞) - y j
      have hz : ‖CStarFilterQuotient.mk B l z‖ < 1 / ((k : ℝ) + 1) := by
        simpa only [z, map_sub, map_mul, map_star] using hu k j (Finset.mem_range.mp hj)
      refine (CStarFilterQuotient.eventually_norm_lt_of_norm_mk_lt z hz).mono fun n hn ↦ ?_
      simpa only [z, err, lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply,
        lp.star_apply, lp.coe_unitaryEquiv_symm_apply] using hn
    simpa only [P, Finset.mem_range] using (Finset.range k).eventually_all.mpr hall
  -- Diagonalize over `k` along `l ≤ atTop`.
  obtain ⟨κ, hκ_tend, hκ_P⟩ := TauCeti.exists_tendsto_atTop_of_forall_eventually hPl hl
  refine ⟨fun n ↦ u (κ n) n, fun j ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_⟩
  obtain ⟨K, hKε, hjK⟩ : ∃ K : ℕ, 1 / ((K : ℝ) + 1) < ε ∧ j < K :=
    (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)).and
      (eventually_gt_atTop j)).exists
  filter_upwards [(hκ_tend.eventually_ge_atTop K), hκ_P] with n hK_le hnP
  have herr_lt : err (u (κ n)) j n < 1 / ((κ n : ℝ) + 1) := hnP j (hjK.trans_le hK_le)
  have hmono : 1 / ((κ n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hK_le 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact (herr_lt.trans_le hmono).trans hKε

variable {A B : Type*} [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [Nontrivial B]

/-- **Kirchberg–Phillips exact unitary implementation.** For separable `A`, nonzero unital `B`, and
any filter `l ≤ atTop` on `ℕ`, two `⋆`-homomorphisms into `CStarFilterQuotient B l` are
approximately unitarily equivalent if and only if they are unitarily equivalent. -/
theorem iff_exists_unitary_cstarFilterQuotient {l : Filter ℕ} (hl : l ≤ atTop)
    {Φ Ψ : A →⋆ₙₐ[ℂ] CStarFilterQuotient B l} :
    ApproximatelyUnitarilyEquivalent Φ Ψ ↔
      ∃ U : unitary (CStarFilterQuotient B l),
        ∀ a, (U : CStarFilterQuotient B l) * Φ a * star (U : CStarFilterQuotient B l) = Ψ a := by
  refine ⟨fun h ↦ ?_, fun ⟨U, hU⟩ ↦ .of_unitary U hU⟩
  have hdef := (approximatelyUnitarilyEquivalent_def Φ Ψ).mp h
  classical
  let d := TopologicalSpace.denseSeq A
  choose x hx using fun j ↦ CStarFilterQuotient.mk_surjective l (Φ (d j))
  choose y hy using fun j ↦ CStarFilterQuotient.mk_surjective l (Ψ (d j))
  choose U_seq hU_seq using fun k : ℕ ↦
    hdef ((Finset.range k).image d) (1 / ((k : ℝ) + 1)) (by positivity)
  choose u hu using fun k ↦ CStarFilterQuotient.exists_unitary_family_mk_eq l (U_seq k)
  obtain ⟨v, hv⟩ := exists_unitary_seq_tendsto_of_approx hl x y u fun k j hjk ↦ by
    rw [hu k, hx j, hy j]
    exact hU_seq k (d j) (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjk, rfl⟩)
  let U : unitary (CStarFilterQuotient B l) :=
    Unitary.map (StarMonoidHom.ofClass (CStarFilterQuotient.unitalMk B l)) (lp.unitaryEquiv.symm v)
  have hU_val : (U : CStarFilterQuotient B l) =
      CStarFilterQuotient.mk B l (lp.unitaryEquiv.symm v) := by simp [U]
  have hd (j : ℕ) :
      (U : CStarFilterQuotient B l) * Φ (d j) * star (U : CStarFilterQuotient B l) = Ψ (d j) := by
    rw [hU_val, ← hx j, ← hy j, ← map_star, ← map_mul, ← map_mul,
      CStarFilterQuotient.mk_eq_mk_iff]
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply,
      lp.coe_unitaryEquiv_symm_apply] using hv j
  have hcont : Continuous fun a ↦
      (U : CStarFilterQuotient B l) * Φ a * star (U : CStarFilterQuotient B l) :=
    (continuous_const.mul (map_continuous Φ)).mul continuous_const
  exact ⟨U, isClosed_property (TopologicalSpace.denseRange_denseSeq A)
    (isClosed_eq hcont (map_continuous Ψ)) hd⟩

/-- In `CStarSequenceAlgebra B`, approximate unitary equivalence from a separable C⋆-algebra `A` is
equivalent to exact unitary conjugacy. -/
theorem iff_exists_unitary_cstarSequenceAlgebra {Φ Ψ : A →⋆ₙₐ[ℂ] CStarSequenceAlgebra B} :
    ApproximatelyUnitarilyEquivalent Φ Ψ ↔
      ∃ U : unitary (CStarSequenceAlgebra B),
        ∀ a, (U : CStarSequenceAlgebra B) * Φ a * star (U : CStarSequenceAlgebra B) = Ψ a :=
  iff_exists_unitary_cstarFilterQuotient le_rfl

/-- In `CStarUltrapower B ω` for a free ultrafilter `ω` on `ℕ`, approximate unitary equivalence from
a separable C⋆-algebra `A` is equivalent to exact unitary conjugacy. -/
theorem iff_exists_unitary_cstarUltrapower {ω : Ultrafilter ℕ} (hω : ∀ n, ω ≠ pure n)
    {Φ Ψ : A →⋆ₙₐ[ℂ] CStarUltrapower B ω} :
    ApproximatelyUnitarilyEquivalent Φ Ψ ↔
      ∃ U : unitary (CStarUltrapower B ω),
        ∀ a, (U : CStarUltrapower B ω) * Φ a * star (U : CStarUltrapower B ω) = Ψ a :=
  iff_exists_unitary_cstarFilterQuotient (Ultrafilter.le_atTop_iff_forall_ne_pure.mpr hω)

/-- For separable `A` and nontrivial `l ≤ atTop`, `φ ψ : A →⋆ₙₐ[ℂ] B` are approximately unitarily
equivalent if and only if `diag B l ∘ φ` and `diag B l ∘ ψ` are unitarily conjugate. -/
theorem iff_exists_unitary_cstarFilterQuotient_diag {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ∃ U : unitary (CStarFilterQuotient B l),
        ∀ a, (U : CStarFilterQuotient B l) * CStarFilterQuotient.diag B l (φ a) *
          star (U : CStarFilterQuotient B l) = CStarFilterQuotient.diag B l (ψ a) := by
  rw [← cstarFilterQuotient_diag_iff (l := l), iff_exists_unitary_cstarFilterQuotient hl]
  simp only [NonUnitalStarAlgHom.comp_apply]

/-- Specialization of `iff_exists_unitary_cstarFilterQuotient_diag` to `CStarSequenceAlgebra B`. -/
theorem iff_exists_unitary_cstarSequenceAlgebra_diag {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ∃ U : unitary (CStarSequenceAlgebra B),
        ∀ a, (U : CStarSequenceAlgebra B) * CStarFilterQuotient.diag B atTop (φ a) *
          star (U : CStarSequenceAlgebra B) = CStarFilterQuotient.diag B atTop (ψ a) :=
  iff_exists_unitary_cstarFilterQuotient_diag le_rfl

/-- Specialization of `iff_exists_unitary_cstarFilterQuotient_diag` to `CStarUltrapower B ω`. -/
theorem iff_exists_unitary_cstarUltrapower_diag {ω : Ultrafilter ℕ} (hω : ∀ n, ω ≠ pure n)
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ∃ U : unitary (CStarUltrapower B ω),
        ∀ a, (U : CStarUltrapower B ω) * CStarFilterQuotient.diag B (ω : Filter ℕ) (φ a) *
          star (U : CStarUltrapower B ω) = CStarFilterQuotient.diag B (ω : Filter ℕ) (ψ a) :=
  iff_exists_unitary_cstarFilterQuotient_diag (Ultrafilter.le_atTop_iff_forall_ne_pure.mpr hω)

end ExactImplementation

end TauCeti.ApproximatelyUnitarilyEquivalent
