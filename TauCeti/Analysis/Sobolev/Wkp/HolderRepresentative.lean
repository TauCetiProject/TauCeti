/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical

/-!
# Hölder derivatives from Hölder representatives

Let `Ω` be an open subset of a finite-dimensional real inner product space `F`, and suppose that
for every `k`, each `u ∈ W^{k+1,p}(Ω)` agrees almost everywhere on `Ω` with an `α`-Hölder function
on `closure Ω`, depending linearly and boundedly on `u` (a Morrey embedding of every order). Then
for every `j`, each `u ∈ W^{j+1,p}(Ω)` agrees almost everywhere on `Ω` with a function `g` that is
`Cʲ` on `Ω`, whose derivatives of every order `i ≤ j` are bounded and `α`-Hölder on `Ω`, with
bounds linear in the norm of `u`. No boundedness or boundary regularity of `Ω` is assumed beyond
the existence of the embeddings; the Lipschitz-domain case is
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_isLipschitzDomainWith_image`.
On the whole space the representative lies in the Banach space `C_b^{j,α}(F)` of
`TauCeti.CkHolderSpace`, and depends linearly and boundedly on `u`
(`TauCeti.Wkp.toCkHolderSpaceL`).

## Method

The induction on `j` is that of the interior statement
`TauCeti.Wkp.exists_contDiffOn_ae_eq_of_forall_zeroAtInfty`: for `u ∈ W^{j+2,p}(Ω)`, the weak
derivatives of `u` along an orthonormal basis lie in `W^{j+1,p}(Ω)`, and depend boundedly on `u`
(`TauCeti.Wkp.lineDerivL`), so by induction they have representatives with the required bounds.
They assemble into a continuous weak derivative of the Hölder representative of `u`, which is
therefore its classical derivative.

## Main declarations

* `TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL`: Hölder
  bounds for all derivatives of a representative, from Hölder representatives at every order.
* `TauCeti.Wkp.toCkHolderSpaceL`: on the whole space, the resulting embedding
  `W^{j+1,p}(F) → C_b^{j,α}(F)` as a continuous linear map, characterised by
  `TauCeti.Wkp.toCkHolderSpaceL_eq_iff`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part II.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Theorem B.1.11.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

namespace Wkp

/-- A Hölder representative on `closure Ω`, depending boundedly on `u`, gives a function on `F`
equal almost everywhere on `Ω` to `u`, bounded and Hölder on `Ω` with constants `‖T‖ ‖u‖`. -/
private theorem exists_holderOnWith_of_holderSpaceL {Ω : Opens F} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {α : ℝ≥0} {k : ℕ} (T : Wkp volume Ω p k →L[ℝ] HolderSpace α (closure (Ω : Set F)) ℝ)
    (hT : ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value k u x)
    (u : Wkp volume Ω p k) :
    ∃ g : F → ℝ, (value k u : F → ℝ) =ᵐ[volume.restrict Ω] g ∧
      (∀ x ∈ Ω, ‖g x‖ ≤ ‖T‖ * ‖u‖) ∧ HolderOnWith (‖T‖₊ * ‖u‖₊) α g Ω := by
  classical
  let g : F → ℝ := fun x => if hx : x ∈ closure (Ω : Set F) then T u ⟨x, hx⟩ else 0
  have hg : ∀ x (hx : x ∈ Ω), g x = T u ⟨x, subset_closure hx⟩ := fun x hx => by
    simp [g, subset_closure hx]
  refine ⟨g, ?_, fun x hx => ?_, HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
  · rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [hT u] with x hx hxΩ
    rw [hg x hxΩ, hx hxΩ]
  · rw [hg x hx]
    exact (HolderSpace.norm_apply_le _ _).trans (T.le_opNorm u)
  · rw [hg x hx, hg y hy]
    refine ((T u).holderWith_nnnorm.dist_le _ _).trans ?_
    rw [Subtype.dist_eq]
    gcongr
    exact_mod_cast T.le_opNNNorm u

/-- **Hölder derivatives from Hölder representatives at every order.** Let `Ω` be an open subset
of `F` and `0 < α`. Suppose that for every `k`, each `u ∈ W^{k+1,p}(Ω)` agrees almost everywhere
on `Ω` with an `α`-Hölder function on `closure Ω`, depending linearly and boundedly on `u`. Then
for every `j` there is a constant `K` such that each `u ∈ W^{j+1,p}(Ω)` agrees almost everywhere on
`Ω` with a function `g` that is `Cʲ` on `Ω`, and whose derivatives of order `i ≤ j` are bounded by
`K ‖u‖` and `α`-Hölder with constant `K ‖u‖` on `Ω`. -/
theorem exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL {Ω : Opens F}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {α : ℝ≥0} (hα : 0 < α)
    (hM : ∀ k : ℕ, ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace α (closure (Ω : Set F)) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value (k + 1) u x) :
    ∀ j : ℕ, ∃ K : ℝ≥0, ∀ u : Wkp volume Ω p (j + 1), ∃ g : F → ℝ, ContDiffOn ℝ j g Ω ∧
      (value (j + 1) u : F → ℝ) =ᵐ[volume.restrict Ω] g ∧ ∀ i ≤ j,
        (∀ x ∈ Ω, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
          HolderOnWith (K * ‖u‖₊) α (iteratedFDeriv ℝ i g) Ω
  | 0 => by
    obtain ⟨T, hT⟩ := hM 0
    refine ⟨‖T‖₊, fun u => ?_⟩
    obtain ⟨g, hug, hgb, hgH⟩ := exists_holderOnWith_of_holderSpaceL T hT u
    refine ⟨g, ?_, hug, fun i hi => ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      exact hgH.continuousOn hα
    · obtain rfl := Nat.le_zero.1 hi
      refine ⟨fun x hx => ?_, holderOnWith_iteratedFDeriv_zero_iff.2 hgH⟩
      rw [norm_iteratedFDeriv_zero]
      exact hgb x hx
  | j + 1 => by
    obtain ⟨T, hT⟩ := hM (j + 1)
    obtain ⟨K, hK⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL hα hM j
    let b := stdOrthonormalBasis ℝ F
    -- The weak derivative along `b l`, and the map recording it in the derivative.
    let D : Fin (finrank ℝ F) → Wkp volume Ω p (j + 2) →L[ℝ] Wkp volume Ω p (j + 1) :=
      fun l => lineDerivL (b l) (j + 1)
    let A : Fin (finrank ℝ F) → ℝ →L[ℝ] (F →L[ℝ] ℝ) :=
      fun l => (ContinuousLinearMap.id ℝ ℝ).smulRight (innerSL ℝ (b l))
    have hA : ∀ l, ‖A l‖ = 1 := fun l => by
      simp [A, ContinuousLinearMap.norm_smulRight_apply, b.orthonormal.1 l]
    let c : ℝ≥0 := ∑ l, K * ‖D l‖₊
    refine ⟨max ‖T‖₊ c, fun u => ?_⟩
    obtain ⟨g, hug, hgb, hgH⟩ := exists_holderOnWith_of_holderSpaceL T hT u
    have hgc : ContinuousOn g Ω := hgH.continuousOn hα
    -- Representatives of the derivatives of `u` along `b`, with the bounds of order `j`.
    choose G hG hdG hGb using fun l => hK (D l u)
    have hdG' : ∀ l, HasWeakLineDerivOn volume Ω g (G l) (b l) := fun l =>
      ((hasWeakLineDerivOn_lineDerivL (b l) (j + 1) u).congr_ae hug).congr_ae_deriv (hdG l)
    obtain ⟨hD, hgD⟩ := contDiffOn_sum_innerSL_and_hasWeakFDerivOn hG
      (hgc.locallyIntegrableOn Ω.isOpen.measurableSet) hdG'
    -- The higher derivatives of `g` are those of the `G l`.
    have hit : ∀ i ≤ j, ∀ y ∈ Ω, iteratedFDeriv ℝ i (fderiv ℝ g) y =
        ∑ l, (A l).compContinuousMultilinearMap (iteratedFDeriv ℝ i (G l) y) := by
      intro i hi y hy
      have hfd : fderiv ℝ g =ᶠ[𝓝 y] fun x => ∑ l, G l x • innerSL ℝ (b l) :=
        eventually_of_mem (Ω.isOpen.mem_nhds hy) fun x hx =>
          hgD.fderiv_eq_of_continuousOn hgc hD.continuousOn hx
      have hGy : ∀ l, ContDiffAt ℝ i (G l) y := fun l =>
        ((hG l).contDiffAt (Ω.isOpen.mem_nhds hy)).of_le (by exact_mod_cast hi)
      rw [(hfd.iteratedFDeriv ℝ i).eq_of_nhds,
        iteratedFDeriv_fun_sum_apply fun l _ => (hGy l).smul_const _]
      exact Finset.sum_congr rfl fun l _ => iteratedFDeriv_smul_const_apply (hGy l)
    have hGn : ∀ i ≤ j, ∀ l, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ i (G l) x‖ ≤ K * ‖D l‖ * ‖u‖ :=
      fun i hi l x hx => ((hGb l i hi).1 x hx).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((D l).le_opNorm u) K.coe_nonneg)
    refine ⟨g, by exact_mod_cast contDiffOn_succ_of_forall_hasWeakLineDerivOn hgc hG hdG', hug,
      fun i hi => ?_⟩
    rcases i with _ | i
    · refine ⟨fun x hx => ?_, holderOnWith_iteratedFDeriv_zero_iff.2 (hgH.mono_const ?_)⟩
      · rw [norm_iteratedFDeriv_zero]
        exact (hgb x hx).trans (mul_le_mul_of_nonneg_right
          (by exact_mod_cast le_max_left _ _) (norm_nonneg u))
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le
    have hi : i ≤ j := Nat.le_of_succ_le_succ hi
    refine ⟨fun x hx => ?_, holderOnWith_iteratedFDeriv_succ_iff.2 <|
      HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
    · calc ‖iteratedFDeriv ℝ (i + 1) g x‖ ≤ ∑ l, ‖iteratedFDeriv ℝ i (G l) x‖ :=
            norm_iteratedFDeriv_succ_le_sum_of_forall_hasWeakLineDerivOn hgc hG hdG'
              (by exact_mod_cast hi) hx
        _ ≤ ∑ l, K * ‖D l‖ * ‖u‖ := Finset.sum_le_sum fun l _ => hGn i hi l x hx
        _ = c * ‖u‖ := by simp only [c, NNReal.coe_sum, NNReal.coe_mul, coe_nnNorm, Finset.sum_mul]
        _ ≤ max ‖T‖₊ c * ‖u‖ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast le_max_right _ _) (norm_nonneg u)
    · rw [hit i hi x hx, hit i hi y hy, dist_eq_norm, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ l, ‖(A l).compContinuousMultilinearMap (iteratedFDeriv ℝ i (G l) x) -
            (A l).compContinuousMultilinearMap (iteratedFDeriv ℝ i (G l) y)‖
          ≤ ∑ l, ‖A l‖ * (K * ‖D l‖ * ‖u‖ * dist x y ^ (α : ℝ)) :=
            Finset.sum_le_sum fun l _ => ((A l).norm_compContinuousMultilinearMap_sub_le _ _).trans
              (mul_le_mul_of_nonneg_left (by
                rw [← dist_eq_norm]
                refine ((hGb l i hi).2.dist_le hx hy).trans ?_
                rw [NNReal.coe_mul, coe_nnNorm, mul_assoc (K : ℝ) ‖D l‖]
                gcongr
                exact (D l).le_opNorm u) (norm_nonneg _))
        _ = c * ‖u‖ * dist x y ^ (α : ℝ) := by
          simp only [c, hA, one_mul, NNReal.coe_sum, NNReal.coe_mul, coe_nnNorm, Finset.sum_mul]
        _ ≤ ↑(max ‖T‖₊ c * ‖u‖₊) * dist x y ^ (α : ℝ) := by
          push_cast
          gcongr
          exact le_max_right _ _

section WholeSpace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {α : ℝ≥0} (hα : 0 < α)
  (hM : ∀ k : ℕ, ∃ T : Wkp volume (⊤ : Opens F) p (k + 1) →L[ℝ]
      HolderSpace α (closure ((⊤ : Opens F) : Set F)) ℝ,
    ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ (⊤ : Opens F), T u ⟨x, subset_closure hx⟩ = value (k + 1) u x)
include hα hM

/-- On the whole space, the representative of
`exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL` lies in `C_b^{j,α}(F)`,
with norm at most `(j + 2) K ‖u‖`. -/
private theorem exists_ckHolderSpace (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : Wkp volume (⊤ : Opens F) p (j + 1), ∃ f : CkHolderSpace j α F ℝ,
      (value (j + 1) u : F → ℝ) =ᵐ[volume] f ∧ ‖f‖ ≤ (j + 2) * K * ‖u‖ := by
  obtain ⟨K, hK⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL hα hM j
  refine ⟨K, fun u ↦ ?_⟩
  obtain ⟨g, hg, hug, hbd⟩ := hK u
  simp only [Opens.coe_top, Measure.restrict_univ, contDiffOn_univ] at hg hug
  replace hbd : ∀ i ≤ j, (∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
      HolderWith (K * ‖u‖₊) α (iteratedFDeriv ℝ i g) := fun i hi ↦
    ⟨fun x ↦ (hbd i hi).1 x (by simp), holderOnWith_univ.1 (by simpa using (hbd i hi).2)⟩
  let f : CkHolderSpace j α F ℝ := CkHolderSpace.ofContDiff g hg
    (fun i hi ↦ ⟨_, (hbd i hi).1⟩) ⟨_, (hbd j le_rfl).2⟩
  have hf : ⇑f = g := CkHolderSpace.coe_ofContDiff g hg _ _
  refine ⟨f, hf ▸ hug, ?_⟩
  refine (CkHolderSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderWith (M := K * ‖u‖)
    (K := K * ‖u‖₊) (fun i hi x ↦ hf ▸ (hbd i hi).1 x) (hf ▸ (hbd j le_rfl).2)).trans_eq ?_
  push_cast
  ring

/-- The representative of `u` in `C_b^{j,α}(F)`, chosen by `exists_ckHolderSpace`. -/
private def ckHolderRepresentative (j : ℕ) (u : Wkp volume (⊤ : Opens F) p (j + 1)) :
    CkHolderSpace j α F ℝ :=
  ((exists_ckHolderSpace hα hM j).choose_spec u).choose

private theorem value_ae_eq_ckHolderRepresentative (j : ℕ)
    (u : Wkp volume (⊤ : Opens F) p (j + 1)) :
    (value (j + 1) u : F → ℝ) =ᵐ[volume] ckHolderRepresentative hα hM j u :=
  ((exists_ckHolderSpace hα hM j).choose_spec u).choose_spec.1

private theorem norm_ckHolderRepresentative_le (j : ℕ)
    (u : Wkp volume (⊤ : Opens F) p (j + 1)) :
    ‖ckHolderRepresentative hα hM j u‖ ≤ (j + 2) * (exists_ckHolderSpace hα hM j).choose * ‖u‖ :=
  ((exists_ckHolderSpace hα hM j).choose_spec u).choose_spec.2

/-- The representative of `u` is the only element of `C_b^{j,α}(F)` agreeing almost everywhere
with `u`. -/
private theorem ckHolderRepresentative_eq_of_ae_eq (j : ℕ)
    {u : Wkp volume (⊤ : Opens F) p (j + 1)} {f : CkHolderSpace j α F ℝ}
    (h : (value (j + 1) u : F → ℝ) =ᵐ[volume] f) : ckHolderRepresentative hα hM j u = f :=
  CkHolderSpace.ext <| congrFun <| (Continuous.ae_eq_iff_eq volume
    (CkHolderSpace.contDiff _).continuous (CkHolderSpace.contDiff _).continuous).1 <|
      (value_ae_eq_ckHolderRepresentative hα hM j u).symm.trans h

/-- **The embedding `W^{j+1,p}(F) → C_b^{j,α}(F)` from Hölder representatives.** Suppose that for
every `k`, each `u ∈ W^{k+1,p}(F)` agrees almost everywhere with an `α`-Hölder function, depending
linearly and boundedly on `u`. Then every `u ∈ W^{j+1,p}(F)` has a representative that is `Cʲ` with
bounded derivatives through order `j` and an `α`-Hölder `j`-th derivative. It depends linearly and
boundedly on `u`, and is the only element of `C_b^{j,α}(F)` agreeing almost everywhere with `u`
(`TauCeti.Wkp.toCkHolderSpaceL_eq_iff`). -/
def toCkHolderSpaceL (j : ℕ) : Wkp volume (⊤ : Opens F) p (j + 1) →L[ℝ] CkHolderSpace j α F ℝ :=
  LinearMap.mkContinuous
    { toFun := ckHolderRepresentative hα hM j
      map_add' u v := ckHolderRepresentative_eq_of_ae_eq hα hM j <| by
        have h₃ := value_add_ae (j + 1) u v
        simp only [Opens.coe_top, Measure.restrict_univ] at h₃
        filter_upwards [value_ae_eq_ckHolderRepresentative hα hM j u,
          value_ae_eq_ckHolderRepresentative hα hM j v, h₃] with x h₁ h₂ h₃
        rw [h₃, CkHolderSpace.coe_add, Pi.add_apply, Pi.add_apply, h₁, h₂]
      map_smul' c u := ckHolderRepresentative_eq_of_ae_eq hα hM j <| by
        have h₂ := value_smul_ae (j + 1) c u
        simp only [Opens.coe_top, Measure.restrict_univ] at h₂
        filter_upwards [value_ae_eq_ckHolderRepresentative hα hM j u, h₂] with x h₁ h₂
        rw [h₂, RingHom.id_apply, CkHolderSpace.coe_smul, Pi.smul_apply, Pi.smul_apply, h₁] }
    ((j + 2) * (exists_ckHolderSpace hα hM j).choose) (norm_ckHolderRepresentative_le hα hM j)

/-- The embedding `W^{j+1,p}(F) → C_b^{j,α}(F)` gives a representative of `u`. -/
theorem value_ae_eq_toCkHolderSpaceL (j : ℕ) (u : Wkp volume (⊤ : Opens F) p (j + 1)) :
    (value (j + 1) u : F → ℝ) =ᵐ[volume] toCkHolderSpaceL hα hM j u :=
  value_ae_eq_ckHolderRepresentative hα hM j u

/-- `toCkHolderSpaceL hα hM j u` is the only element of `C_b^{j,α}(F)` representing `u`. -/
theorem toCkHolderSpaceL_eq_iff (j : ℕ) {u : Wkp volume (⊤ : Opens F) p (j + 1)}
    {f : CkHolderSpace j α F ℝ} :
    toCkHolderSpaceL hα hM j u = f ↔ (value (j + 1) u : F → ℝ) =ᵐ[volume] f :=
  ⟨fun h ↦ h ▸ value_ae_eq_toCkHolderSpaceL hα hM j u,
    ckHolderRepresentative_eq_of_ae_eq hα hM j⟩

end WholeSpace

end Wkp

end TauCeti
