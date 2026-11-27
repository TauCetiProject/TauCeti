/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# The `W^{k,p}` size of a function on a subset of a real normed space

`TauCeti.eLpNormWkp p U k f` is the extended `W^{k,p}(U)` norm of `f : E → F`, for real normed
spaces `E` and `F`: the `Lᵖ(U)` norm of `f` plus, recursively, the `W^{k-1,p}(U)` size of its weak
derivative on `interior U`, minimized over all weak derivatives. It is `∞` when no weak derivative
exists, or when one of the norms is infinite. Its derivatives are taken on the interior and its
norms on `U` itself, matching `TauCeti.MemWkpLoc`. On an open set in a finite-dimensional Borel
space, weak derivatives are unique almost everywhere, so the minimum is attained by every weak
derivative.

This is the quantity in which interior estimates of elliptic equations are stated. The file
supplies its unfolding, its value through a given weak derivative on an open set or on a set
that agrees almost everywhere with its interior, such as a half-disc, the `Lᵖ` and
`W^{k,p}_loc` membership of a function of finite norm and, conversely, the finiteness of the
norm of a `W^{k,p}_loc` function on relatively compact subsets, the extraction of a weak
derivative from a finite successor-order norm, the almost-everywhere vanishing of a function of
zero norm, monotonicity in the set and in the derivative order, invariance under
almost-everywhere change and linear isometric equivalences of the codomain
(`LinearIsometryEquiv.eLpNormWkp_comp`), the triangle inequality (also over finite sums and for
pairs) and the
operator-norm bound under a continuous linear map of the codomain. An upper bound of the form
`a + c ‖f‖_{W^{k+1,p}(U)}` (for finite `c`, with `‖f‖_{W^{k+1,p}(U)}` finite when `c = 0`) may be
checked through each weak derivative of `f` separately. A chain bound
`TauCeti.WeakDerivChainLe p S T C m f g` between the iterated weak derivatives of `f` and `g`,
with a finite nonzero constant `C`, gives the norm bound `‖f‖_{W^{m,p}(S)} ≤ C ‖g‖_{W^{m,p}(T)}`
when `f` has the iterated weak derivatives, for instance when `MemWkpLoc q S m f`
(`TauCeti.WeakDerivChainLe.eLpNormWkp_le`).

## Implementation notes

As with `MemWkpLocAux` in `TauCeti.Analysis.Sobolev.Local.Basic`, when `E : Type u` and
`F : Type v` live in separate universes, `E →L[ℝ] F` lives in `Type (max u v)`. The private
helper `eLpNormWkpAux` fixes the codomain universe to `max u v` so the recursion on `k` is
well-typed while `TauCeti.eLpNormWkp` accepts any `F : Type v`. Inductive proofs reuse
`TauCeti.nat_induction_clm_ulift` and `TauCeti.nat_induction_clm_ulift₂` by lifting `F` to
`ULift.{u} F` via `LinearIsometryEquiv.eLpNormWkp_comp` (packaged by
`TauCeti.eLpNormWkp_ulift_induction`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

universe u v w v' w'

variable {E : Type u} {F : Type v} {G : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p : ℝ≥0∞} {U V : Set E} {k : ℕ} {f g : E → F}

private def eLpNormWkpAux (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type (max u v)} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (volume.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (volume.restrict U) +
      ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
        eLpNormWkpAux p U k D

/-- The extended `W^{k,p}(U)` norm: the `Lᵖ(U)` norm of `f` plus the smallest `W^{k-1,p}(U)` norm
of a weak derivative of `f` on `interior U`. It is `∞` when no weak derivative exists. -/
def eLpNormWkp (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → ℝ≥0∞
  | 0, _, _, _, f => eLpNorm f p (volume.restrict U)
  | k + 1, F, _, _, f => eLpNorm f p (volume.restrict U) +
      ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
        eLpNormWkpAux.{u, v} p U k D

private theorem eLpNormWkpAux_max {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} : eLpNormWkpAux.{u, v} p U k f = eLpNormWkpAux.{u, max u v} p U k f := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    unfold eLpNormWkpAux
    congr 1
    exact iInf_congr fun _ => iInf_congr fun _ => ih

private theorem eLpNormWkpAux_eq {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} : eLpNormWkpAux.{u, v} p U k f = eLpNormWkp.{u, max u v} p U k f := by
  cases k with
  | zero => rfl
  | succ k =>
    unfold eLpNormWkpAux eLpNormWkp
    congr 1
    exact iInf_congr fun _ => iInf_congr fun _ => eLpNormWkpAux_max

/-- At order zero the `W^{k,p}` norm is the `Lᵖ` norm. -/
@[simp]
theorem eLpNormWkp_zero : eLpNormWkp p U 0 f = eLpNorm f p (volume.restrict U) := by
  rw [eLpNormWkp]

/-- The successor-order unfolding of the `W^{k,p}` norm. -/
theorem eLpNormWkp_succ : eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) +
    ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
      eLpNormWkp p U k D := by
  rw [eLpNormWkp]
  congr 1
  exact iInf_congr fun _ => iInf_congr fun _ => eLpNormWkpAux_eq

/-- The `Lᵖ` norm is bounded by every `W^{k,p}` norm. -/
theorem eLpNorm_le_eLpNormWkp : eLpNorm f p (volume.restrict U) ≤ eLpNormWkp p U k f := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_self_add

/-- A function of finite `W^{k,p}` norm is `Lᵖ` on the set. -/
theorem memLp_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f ≠ ∞) :
    MemLp f p (volume.restrict U) :=
  memLp_iff.2 (eLpNorm_le_eLpNormWkp.trans_lt (lt_top_iff_ne_top.2 hf))

/-- A function of zero `W^{k,p}` norm vanishes almost everywhere on the set. -/
theorem ae_eq_zero_of_eLpNormWkp_eq_zero (hp : p ≠ 0) (hf : eLpNormWkp p U k f = 0) :
    f =ᵐ[volume.restrict U] 0 :=
  (eLpNorm_eq_zero_iff hp).1 (le_antisymm (hf ▸ eLpNorm_le_eLpNormWkp) zero_le)

/-- Any weak derivative bounds the successor-order norm. -/
theorem eLpNormWkp_succ_le {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f ≤ eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  rw [eLpNormWkp_succ]
  gcongr
  exact iInf₂_le D hD

private theorem eLpNormWkp_comp_le_step {F' : Type v'} {G' : Type w'}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {f' : E → F'} (e' : F' ≃ₗᵢ[ℝ] G')
    (ih : ∀ {f'' : E → E →L[ℝ] F'} (e'' : (E →L[ℝ] F') ≃ₗᵢ[ℝ] (E →L[ℝ] G')),
      eLpNormWkp p U k (fun z => e'' (f'' z)) ≤ eLpNormWkp p U k f'') :
    eLpNormWkp p U (k + 1) (fun z => e' (f' z)) ≤ eLpNormWkp p U (k + 1) f' := by
  rw [eLpNormWkp_succ, eLpNormWkp_succ, e'.eLpNorm_comp]
  refine add_le_add le_rfl (le_iInf₂ fun D hD => ?_)
  let ePost : (E →L[ℝ] F') ≃ₗᵢ[ℝ] (E →L[ℝ] G') :=
    LinearIsometryEquiv.ofLinearIsometry (e'.toLinearIsometry.postcomp (E := E))
      (e'.symm.toLinearIsometry.postcomp (E := E)).toLinearMap
      (by ext B x; simp [LinearIsometry.postcomp]) (by ext A x; simp [LinearIsometry.postcomp])
  exact iInf₂_le_of_le (fun z => ePost (D z))
    (e'.toContinuousLinearEquiv.comp_hasWeakFDerivOn hD) (ih ePost)

private theorem eLpNormWkp_comp_le (e : F ≃ₗᵢ[ℝ] G) :
    eLpNormWkp p U k (fun z => e (f z)) ≤ eLpNormWkp p U k f := by
  -- Bootstraps the universe transfer used by `nat_induction_clm_ulift` and `_₂`.
  have aux : ∀ (k : ℕ) {F' : Type (max u v)} {G' : Type (max u w)}
      [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G'] [NormedSpace ℝ G']
      {f' : E → F'} (e' : F' ≃ₗᵢ[ℝ] G'),
      eLpNormWkp p U k (fun z => e' (f' z)) ≤ eLpNormWkp p U k f' := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ _ f' e'; exact (e'.eLpNorm_comp _ _ _).le
    | succ k ih => exact fun e' => eLpNormWkp_comp_le_step e' (fun e'' => ih e'')
  cases k with
  | zero => exact (e.eLpNorm_comp _ _ _).le
  | succ k => exact eLpNormWkp_comp_le_step e (fun e'' => aux k e'')

/-- Postcomposing with a linear isometric equivalence preserves the `W^{k,p}` norm. -/
@[simp]
theorem _root_.LinearIsometryEquiv.eLpNormWkp_comp (e : F ≃ₗᵢ[ℝ] G) :
    eLpNormWkp p U k (fun z => e (f z)) = eLpNormWkp p U k f :=
  le_antisymm (eLpNormWkp_comp_le e)
    (by simpa using eLpNormWkp_comp_le e.symm (f := fun z => e (f z)))

omit [MeasureSpace E] in
/-- Universe-lifting induction for `TauCeti.eLpNormWkp`: proves a universe-uniform predicate
`P k (ULift.{u} F) ((LinearIsometryEquiv.ulift ℝ F).symm ∘ f)` from a base case at `k = 0` and an
inductive step from `E →L[ℝ] F` at `k` to `F` at `k + 1`. -/
private theorem eLpNormWkp_ulift_induction
    (P : ℕ → ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace ℝ F], (E → F) → Prop)
    (h0 : ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F), P 0 F g)
    (hsucc : ∀ (k : ℕ) (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace ℝ F],
      (∀ D : E → E →L[ℝ] F, P k (E →L[ℝ] F) D) → ∀ g : E → F, P (k + 1) F g)
    (f : E → F) :
    P k (ULift.{u} F) (fun z => (LinearIsometryEquiv.ulift ℝ F).symm (f z)) :=
  nat_induction_clm_ulift ℝ E (fun k F _ _ => ∀ g : E → F, P k F g)
    (fun _ _ _ g => h0 _ g) (fun k F _ _ ih g => hsucc k F ih g) k F _

/-- The `W^{k,p}` norm increases with the set. -/
theorem eLpNormWkp_mono_set (hVU : V ⊆ U) : eLpNormWkp p V k f ≤ eLpNormWkp p U k f := by
  simpa using eLpNormWkp_ulift_induction
    (fun k _ _ _ g => eLpNormWkp p V k g ≤ eLpNormWkp p U k g)
    (fun _ _ _ _ => eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl))
    (fun _ _ _ _ ih g => by
      rw [eLpNormWkp_succ, eLpNormWkp_succ]
      gcongr ?_ + ?_
      · exact eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)
      · exact le_iInf₂ fun D hD => iInf₂_le_of_le D (hD.mono (interior_mono hVU)) (ih D))
    f

/-- The `W^{k,p}(U)` norm increases with the derivative order. -/
theorem eLpNormWkp_mono_order {l : ℕ} (hlk : l ≤ k) :
    eLpNormWkp p U l f ≤ eLpNormWkp p U k f := by
  simpa using eLpNormWkp_ulift_induction
    (fun l _ _ _ g => ∀ (k : ℕ), l ≤ k → eLpNormWkp p U l g ≤ eLpNormWkp p U k g)
    (fun _ _ _ _ _ _ => eLpNorm_le_eLpNormWkp.trans_eq' eLpNormWkp_zero.symm)
    (fun _ _ _ _ ih g k hlk => by
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [eLpNormWkp_succ, eLpNormWkp_succ]
      gcongr
      exact ih _ k (by omega))
    f k hlk

/-- Almost-everywhere equality on `U` preserves the `W^{k,p}(U)` norm. -/
theorem eLpNormWkp_congr_ae (hfg : f =ᵐ[volume.restrict U] g) :
    eLpNormWkp p U k f = eLpNormWkp p U k g := by
  cases k with
  | zero => exact eLpNorm_congr_ae hfg
  | succ k =>
    have hint : f =ᵐ[volume.restrict (Opens.interior U)] g :=
      ae_mono (Measure.restrict_mono_set volume interior_subset) hfg
    rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNorm_congr_ae hfg]
    congr 1
    refine le_antisymm (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
      (le_iInf₂ fun D hD => iInf₂_le_of_le D ?_ le_rfl)
    · exact hD.congr_ae (Filter.EventuallyEq.symm hint)
    · exact hD.congr_ae hint

/-- On a set that agrees almost everywhere with its interior, every weak derivative on the
interior realizes the successor-order norm. This applies to open sets and to the half-discs
`Ω ∩ {0 ≤ im}` (`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). -/
theorem eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior [FiniteDimensional ℝ E] [BorelSpace E]
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  refine le_antisymm (eLpNormWkp_succ_le hD) ?_
  rw [eLpNormWkp_succ]
  gcongr
  refine le_iInf₂ fun D' hD' => (eLpNormWkp_congr_ae ?_).le
  rw [Measure.restrict_congr_set hU]
  exact hD.ae_eq hD'

/-- On an open set, every weak derivative realizes the successor-order norm. -/
theorem eLpNormWkp_succ_eq_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    eLpNormWkp p Ω (k + 1) f = eLpNorm f p (volume.restrict Ω) + eLpNormWkp p Ω k D :=
  eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior (by rw [Opens.interior_coe])
    (by rwa [Opens.interior_coe])

/-- On an open set, the order-`k` norm of a weak derivative is at most the order-`k + 1` norm of
the function. At `k = 0` this bounds `‖D‖_{Lᵖ(Ω)}` by `‖f‖_{W^{1,p}(Ω)}`. -/
theorem eLpNormWkp_le_eLpNormWkp_succ_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    eLpNormWkp p Ω k D ≤ eLpNormWkp p Ω (k + 1) f := by
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD]
  exact le_add_self

/-- A finite successor-order norm provides a weak derivative on the interior of finite norm of
the previous order. -/
theorem exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf : eLpNormWkp p U (k + 1) f ≠ ∞) :
    ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior U) f D ∧ eLpNormWkp p U k D ≠ ∞ := by
  rw [eLpNormWkp_succ, ENNReal.add_ne_top] at hf
  obtain ⟨D, hD, hlt⟩ : ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn volume (Opens.interior U) f D ∧ eLpNormWkp p U k D < ∞ := by
    simpa [iInf_lt_iff, lt_top_iff_ne_top] using hf.2
  exact ⟨D, hD, hlt.ne⟩

/-- Let `c ≠ ∞`, and if `c = 0` let `f` have finite `W^{k+1,p}(U)` norm. To bound `b` by
`a + c ‖f‖_{W^{k+1,p}(U)}` it suffices to bound it by `a + c (‖f‖_{Lᵖ(U)} + ‖D‖_{W^{k,p}(U)})`
for every weak derivative `D` of `f` on `interior U` of finite `W^{k,p}(U)` norm. -/
theorem le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn {a b c : ℝ≥0∞}
    (hc : c ≠ ∞) (hf : c = 0 → eLpNormWkp p U (k + 1) f ≠ ∞)
    (H : ∀ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D →
      eLpNormWkp p U k D ≠ ∞ →
        b ≤ a + c * (eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D)) :
    b ≤ a + c * eLpNormWkp p U (k + 1) f := by
  rcases eq_or_ne c 0 with rfl | hc0
  · obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top (hf rfl)
    simpa using H D hD hDk
  calc b
      ≤ ⨅ (D : E → E →L[ℝ] F) (_ : HasWeakFDerivOn volume (Opens.interior U) f D),
          a + c * (eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D) :=
        le_iInf₂ fun D hD => by
          by_cases hDk : eLpNormWkp p U k D = ∞
          · rw [hDk, add_top, ENNReal.mul_top hc0, add_top]
            exact le_top
          · exact H D hD hDk
    _ = a + c * eLpNormWkp p U (k + 1) f := by
        rw [eLpNormWkp_succ]
        simp only [ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hc]

/-- A function of finite `W^{k,p}` norm lies in the local Sobolev class `W^{k,p}_loc`. -/
theorem memWkpLoc_of_eLpNormWkp_ne_top (hf : eLpNormWkp p U k f ≠ ∞) : MemWkpLoc p U k f :=
  memWkpLoc_ulift_induction (fun k _ _ _ g => eLpNormWkp p U k g ≠ ∞)
    (fun _ _ _ _ hg => (memLp_of_eLpNormWkp_ne_top hg).memLpLoc)
    (fun _ _ _ _ _ hg => by
      obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hg
      exact ⟨(memLp_of_eLpNormWkp_ne_top hg).memLpLoc, D, hD, hDk⟩)
    (by
      change eLpNormWkp p U k (fun z => (LinearIsometryEquiv.ulift ℝ F).symm (f z)) ≠ ∞
      simpa using hf)

/-- On an open set, a finite successor-order norm is realized by a weak derivative of finite norm
of the previous order. -/
theorem exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top [FiniteDimensional ℝ E] [BorelSpace E]
    {Ω : Opens E} (hf : eLpNormWkp p Ω (k + 1) f ≠ ∞) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ eLpNormWkp p Ω k D ≠ ∞ ∧
      eLpNormWkp p Ω (k + 1) f = eLpNorm f p (volume.restrict Ω) + eLpNormWkp p Ω k D := by
  obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
  rw [Opens.interior_coe] at hD
  exact ⟨D, hD, hDk, eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD⟩

/-- On a set that agrees almost everywhere with its interior, for instance a half-disc
`Ω ∩ {0 ≤ im}`, a finite successor-order norm is realized by a weak derivative on the interior of
finite norm of the previous order. -/
theorem exists_hasWeakFDerivOn_interior_eLpNormWkp_succ_eq_of_ne_top
    [FiniteDimensional ℝ E] [BorelSpace E]
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) (hf : eLpNormWkp p U (k + 1) f ≠ ∞) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      eLpNormWkp p U k D ≠ ∞ ∧
      eLpNormWkp p U (k + 1) f = eLpNorm f p (volume.restrict U) + eLpNormWkp p U k D := by
  obtain ⟨D, hD, hDk⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hf
  exact ⟨D, hD, hDk, eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior hU hD⟩

/-- A local Sobolev function has finite `W^{k,p}` norm on every compact subset of its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_isCompact (hf : MemWkpLoc p U k f) {K : Set E}
    (hKU : K ⊆ U) (hK : IsCompact K) : eLpNormWkp p K k f ≠ ∞ := by
  simpa using eLpNormWkp_ulift_induction
    (fun k _ _ _ g => MemWkpLoc p U k g → eLpNormWkp p K k g ≠ ∞)
    (fun _ _ _ _ hg => (memLpLoc_iff.1 hg.memLpLoc K hKU hK).eLpNorm_ne_top)
    (fun _ _ _ _ ih g hg => by
      obtain ⟨D, hD, hDk⟩ := hg.exists_weakFDeriv
      refine ne_top_of_le_ne_top ?_ (eLpNormWkp_succ_le (hD.mono (interior_mono hKU)))
      exact ENNReal.add_ne_top.2 ⟨(memLpLoc_iff.1 hg.memLpLoc K hKU hK).eLpNorm_ne_top, ih D hDk⟩)
    f ((LinearIsometryEquiv.ulift ℝ F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff.2 hf)

/-- A local Sobolev function has finite `W^{k,p}` norm on every set whose closure is compact and
contained in its domain. -/
theorem MemWkpLoc.eLpNormWkp_ne_top_of_closure_subset (hf : MemWkpLoc p U k f)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U) : eLpNormWkp p V k f ≠ ∞ :=
  ne_top_of_le_ne_top (hf.eLpNormWkp_ne_top_of_isCompact hVU hV)
    (eLpNormWkp_mono_set subset_closure)

/-- A local estimate `‖v‖_{Lᵗ(V)} ≤ C ‖v‖_{W^{k,r}(W)}` on every `V` with compact closure in an
open `W` makes every `u ∈ W^{k,r}_loc(Ω, F)` locally `Lᵗ`. -/
theorem MemWkpLoc.memLpLoc_of_forall_exists_eLpNorm_le [LocallyCompactSpace E]
    {Ω : Opens E} {r t : ℝ≥0∞} (hf : MemWkpLoc r Ω k f)
    (hest : ∀ {V : Set E} {W : Opens E}, IsCompact (closure V) → closure V ⊆ W →
      ∃ C : ℝ≥0, ∀ v : E → F, eLpNorm v t (volume.restrict V) ≤ C * eLpNormWkp r W k v) :
    MemLpLoc t Ω f := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨C, hC⟩ := hest (W := W) (by rwa [hKc]) (by rwa [hKc])
  exact memLp_iff.2 ((hC f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.2 (hf.eLpNormWkp_ne_top_of_closure_subset hWc hWΩ))))

/-- The zero function has zero `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_zero_fun [CompleteSpace F] : eLpNormWkp p U k (0 : E → F) = 0 := by
  have h :
      eLpNormWkp p U k (fun z => (LinearIsometryEquiv.ulift ℝ F).symm ((0 : E → F) z)) = 0 :=
    eLpNormWkp_ulift_induction (k := k)
      (fun k F _ _ g => CompleteSpace F → g = 0 → eLpNormWkp p U k g = 0)
      (fun _ _ _ _ _ hg => by simp [hg])
      (fun _ _ _ _ ih g _ hg => by
        subst hg
        refine le_antisymm ((eLpNormWkp_succ_le hasWeakFDerivOn_zero).trans ?_) zero_le
        simp [ih 0 inferInstance rfl])
      (0 : E → F) (completeSpace_ulift_iff.2 inferInstance) (by ext; simp)
  exact (LinearIsometryEquiv.eLpNormWkp_comp (LinearIsometryEquiv.ulift ℝ F).symm).symm.trans h

/-- The triangle inequality for the `W^{k,p}` norm. -/
theorem eLpNormWkp_add_le [OpensMeasurableSpace E] (hp : 1 ≤ p) :
    eLpNormWkp p U k (f + g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
  have hadd : (fun z => (LinearIsometryEquiv.ulift ℝ F).symm ((f + g) z)) =
      (fun z => (LinearIsometryEquiv.ulift ℝ F).symm (f z)) +
        (fun z => (LinearIsometryEquiv.ulift ℝ F).symm (g z)) := by ext; simp
  have h := eLpNormWkp_ulift_induction (k := k)
    (fun k F _ _ h => ∀ a b : E → F, h = a + b →
      eLpNormWkp p U k h ≤ eLpNormWkp p U k a + eLpNormWkp p U k b)
    (fun _ _ _ _ a b hab => by simpa [hab] using eLpNorm_add_le hp)
    (fun _ _ _ _ ih _ a b hab => by
      subst hab
      rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNormWkp_succ, add_add_add_comm]
      gcongr ?_ + ?_
      · exact eLpNorm_add_le hp
      · exact ENNReal.le_iInf_add_iInf fun D D' => ENNReal.le_iInf_add_iInf fun hD hD' =>
          iInf₂_le_of_le (D + D') (hD.add hD') (ih (D + D') D D' rfl))
    (f + g) _ _ hadd
  simpa only [LinearIsometryEquiv.eLpNormWkp_comp] using h

/-- The triangle inequality for the `W^{k,p}` norm over a finite sum. -/
theorem eLpNormWkp_sum_le [OpensMeasurableSpace E] [CompleteSpace F] {ι : Type*}
    {s : Finset ι} {u : ι → E → F} (hp : 1 ≤ p) :
    eLpNormWkp p U k (∑ i ∈ s, u i) ≤ ∑ i ∈ s, eLpNormWkp p U k (u i) :=
  Finset.le_sum_of_subadditive (fun u : E → F ↦ eLpNormWkp p U k u) eLpNormWkp_zero_fun.le
    (fun _ _ ↦ eLpNormWkp_add_le hp) s u

/-- A continuous linear map of the codomain scales the `W^{k,p}` norm by at most its operator
norm. -/
theorem _root_.ContinuousLinearMap.eLpNormWkp_comp_le [OpensMeasurableSpace E] [CompleteSpace G]
    (A : F →L[ℝ] G) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ ‖A‖ₑ * eLpNormWkp p U k f := by
  have hlift := nat_induction_clm_ulift₂ ℝ E
    (fun k F _ _ G _ _ => CompleteSpace G → ∀ (f : E → F) (A : F →L[ℝ] G),
      eLpNormWkp p U k (fun z => A (f z)) ≤ ‖A‖ₑ * eLpNormWkp p U k f)
    (fun _ _ _ _ _ _ _ _ A => A.eLpNorm_comp_le)
    (fun _ F' _ _ G' _ _ ih _ f A => by
      by_cases hA : A = 0
      · subst hA
        have h0 : (fun z => (0 : F' →L[ℝ] G') (f z)) = (0 : E → G') := by ext; simp
        rw [h0, eLpNormWkp_zero_fun]
        exact zero_le
      have hA₀ : ‖A‖ₑ ≠ 0 := by
        rw [eNorm_eq_nnNorm]; exact ENNReal.coe_ne_zero.2 (nnNorm_ne_zero_iff.2 hA)
      have hA_top : ‖A‖ₑ ≠ ⊤ := eNorm_ne_top
      rw [eLpNormWkp_succ, eLpNormWkp_succ, mul_add]
      gcongr ?_ + ?_
      · exact A.eLpNorm_comp_le
      · rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
        refine le_iInf fun D => ?_
        rw [ENNReal.mul_iInf_of_ne hA₀ hA_top]
        refine le_iInf fun hD => iInf₂_le_of_le _ (hD.clm_comp A) ?_
        refine (ih inferInstance D (ContinuousLinearMap.compL ℝ E _ _ A)).trans ?_
        gcongr
        exact eNorm_le_iff_norm_le.2
          (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => A.opNorm_comp_le B))
    k F G (completeSpace_ulift_iff.2 inferInstance)
  let eF : F ≃ₗᵢ[ℝ] ULift.{u} F := (LinearIsometryEquiv.ulift ℝ F).symm
  let eG : G ≃ₗᵢ[ℝ] ULift.{u} G := (LinearIsometryEquiv.ulift ℝ G).symm
  let A' : ULift.{u} F →L[ℝ] ULift.{u} G :=
    eG.toLinearIsometry.toContinuousLinearMap.comp
      (A.comp eF.symm.toLinearIsometry.toContinuousLinearMap)
  have hnorm : ‖A'‖ₑ ≤ ‖A‖ₑ := by
    refine eNorm_le_iff_norm_le.2 ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
    simpa [A'] using A.le_opNorm (eF.symm x)
  have hA := hlift (fun z => eF (f z)) A'
  have heq : (fun z => A' (eF (f z))) = fun z => eG (A (f z)) := by ext; simp [A']
  rw [heq, eG.eLpNormWkp_comp, eF.eLpNormWkp_comp] at hA
  exact hA.trans (mul_le_mul_of_nonneg_right hnorm zero_le)

/-- A continuous linear map of norm at most one does not increase the `W^{k,p}` norm. -/
theorem eLpNormWkp_clm_comp_le_of_norm_le_one [OpensMeasurableSpace E] [CompleteSpace G]
    (A : F →L[ℝ] G) (hA : ‖A‖ ≤ 1) :
    eLpNormWkp p U k (fun z => A (f z)) ≤ eLpNormWkp p U k f :=
  A.eLpNormWkp_comp_le.trans (mul_le_of_le_one_left zero_le (by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 hA))

/-- The `W^{k,p}` norm of a pair of functions is at most the sum of the norms of its
components. -/
theorem eLpNormWkp_prodMk_le [OpensMeasurableSpace E] [CompleteSpace F] [CompleteSpace G]
    (hp : 1 ≤ p) {v : E → G} :
    eLpNormWkp p U k (fun z => (f z, v z)) ≤ eLpNormWkp p U k f + eLpNormWkp p U k v := by
  have h : (fun z => (f z, v z)) = (fun z => ContinuousLinearMap.inl ℝ F G (f z)) +
      fun z => ContinuousLinearMap.inr ℝ F G (v z) := by
    ext1 z
    simp
  rw [h]
  exact (eLpNormWkp_add_le hp).trans (add_le_add
    (eLpNormWkp_clm_comp_le_of_norm_le_one _ (ContinuousLinearMap.norm_inl_le_one ℝ F G))
    (eLpNormWkp_clm_comp_le_of_norm_le_one _ (ContinuousLinearMap.norm_inr_le_one ℝ F G)))

/-- Evaluating a field of linear maps at a vector `v` with `‖v‖ ≤ 1` does not increase the
`W^{k,p}` norm. -/
theorem eLpNormWkp_apply_le_of_norm_le_one [OpensMeasurableSpace E] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace F]
    (f : E → E' →L[ℝ] F) {v : E'} (hv : ‖v‖ ≤ 1) :
    eLpNormWkp p U k (fun z => f z v) ≤ eLpNormWkp p U k f :=
  eLpNormWkp_clm_comp_le_of_norm_le_one (ContinuousLinearMap.apply ℝ F v)
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => by
      simpa using (A.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg A) hv))

/-- On an open set, a partial derivative `z ↦ D z v`, `‖v‖ ≤ 1`, of a weak derivative `D` of `f`
has `W^{k,p}` norm at most the `W^{k+1,p}` norm of `f`. -/
theorem eLpNormWkp_apply_le_eLpNormWkp_succ_of_hasWeakFDerivOn [FiniteDimensional ℝ E]
    [BorelSpace E] [CompleteSpace F] {Ω : Opens E} {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn volume Ω f D) {v : E} (hv : ‖v‖ ≤ 1) :
    eLpNormWkp p Ω k (fun z => D z v) ≤ eLpNormWkp p Ω (k + 1) f :=
  (eLpNormWkp_apply_le_of_norm_le_one D hv).trans
    (eLpNormWkp_le_eLpNormWkp_succ_of_hasWeakFDerivOn hD)

/-- Negation preserves the `W^{k,p}` norm. -/
@[simp]
theorem eLpNormWkp_neg : eLpNormWkp p U k (-f) = eLpNormWkp p U k f := by
  have h := eLpNormWkp_ulift_induction (k := k)
    (fun k F _ _ g => eLpNormWkp p U k (-g) = eLpNormWkp p U k g)
    (fun _ _ _ g => by simp [eLpNorm_neg])
    (fun _ _ _ _ ih g => by
      rw [eLpNormWkp_succ, eLpNormWkp_succ, eLpNorm_neg]
      congr 1
      refine le_antisymm (le_iInf₂ fun D hD => iInf₂_le_of_le (-D) hD.neg ?_)
        (le_iInf₂ fun D hD => iInf₂_le_of_le (-D) (by simpa using hD.neg) ?_)
      all_goals exact (ih D).le)
    f
  rw [← (LinearIsometryEquiv.ulift ℝ F).symm.eLpNormWkp_comp (f := -f),
    show (fun z => (LinearIsometryEquiv.ulift ℝ F).symm ((-f) z)) =
      -fun z => (LinearIsometryEquiv.ulift ℝ F).symm (f z) from by ext; simp]
  simpa using h

/-- The triangle inequality for the `W^{k,p}` norm of a difference. -/
theorem eLpNormWkp_sub_le [OpensMeasurableSpace E] (hp : 1 ≤ p) :
    eLpNormWkp p U k (f - g) ≤ eLpNormWkp p U k f + eLpNormWkp p U k g := by
  rw [sub_eq_add_neg]
  exact (eLpNormWkp_add_le hp).trans_eq (by rw [eLpNormWkp_neg])

/-- **A chain bound bounds the `W^{m,p}` norm.** Let `C` be finite and nonzero. If the iterated
weak derivatives of `f` on the interior of `S` are bounded in `Lᵖ(S)` by `C` times those of `g` on
the interior of `T` in `Lᵖ(T)`, in the sense of `TauCeti.WeakDerivChainLe`, then
`‖f‖_{W^{m,p}(S)} ≤ C ‖g‖_{W^{m,p}(T)}`. The
derivatives of `f` must exist, which `MemWkpLoc q S m f` provides for any exponent `q`; those of
`g` need not, the right side being `∞` otherwise. -/
theorem WeakDerivChainLe.eLpNormWkp_le {S T : Set E} {C : ℝ≥0∞} (hC : C ≠ ∞) (hC0 : C ≠ 0)
    {m : ℕ} (h : WeakDerivChainLe p S T C m f g) {q : ℝ≥0∞} (hf : MemWkpLoc q S m f) :
    eLpNormWkp p S m f ≤ C * eLpNormWkp p T m g := by
  have aux : ∀ (m : ℕ) {F' : Type (max u v)} [NormedAddCommGroup F'] [NormedSpace ℝ F']
      {f' g' : E → F'}, WeakDerivChainLe p S T C m f' g' → MemWkpLoc q S m f' →
      eLpNormWkp p S m f' ≤ C * eLpNormWkp p T m g' := by
    intro m
    induction m with
    | zero => intro _ _ _ _ _ h' _; simpa using h'.eLpNorm_le
    | succ m ih =>
      intro _ _ _ _ _ h' hf'
      obtain ⟨-, Df, hDf, hDfm⟩ := memWkpLoc_succ_iff.1 hf'
      simpa using le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn (a := 0) hC
        (fun h0 => absurd h0 hC0) fun Dg hDg _ => by
          rw [zero_add, mul_add]
          exact (eLpNormWkp_succ_le hDf).trans
            (add_le_add h'.eLpNorm_le (ih (h'.weakFDeriv hDf hDg) hDfm))
  cases m with
  | zero => simpa using h.eLpNorm_le
  | succ m =>
    obtain ⟨-, Df, hDf, hDfm⟩ := memWkpLoc_succ_iff.1 hf
    simpa using le_add_mul_eLpNormWkp_succ_of_forall_hasWeakFDerivOn (a := 0) hC
      (fun h0 => absurd h0 hC0) fun Dg hDg _ => by
        rw [zero_add, mul_add]
        exact (eLpNormWkp_succ_le hDf).trans
          (add_le_add h.eLpNorm_le (aux m (h.weakFDeriv hDf hDg) hDfm))

/-- **The `W^{k+1,p}` norm through partial derivatives.** If `D` is a weak derivative of `f` on the
interior of `U`, the `W^{k+1,p}(U)` norm of `f` is at most its `Lᵖ(U)` norm plus the
`W^{k,p}(U)` norms of the partial derivatives `z ↦ D z 1` and `z ↦ D z I`, weighted by the norms
of the maps `L₁`, `L₂` that reassemble `D` from them
(`ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM`). This is the norm form of
`TauCeti.memWkpLoc_succ_iff_apply_one_apply_I`. -/
theorem eLpNormWkp_succ_le_eLpNorm_add_apply_one_add_apply_I [CompleteSpace F] (hp : 1 ≤ p)
    {U : Set ℂ} {f : ℂ → F} {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior U) f D) :
    eLpNormWkp p U (k + 1) f ≤ eLpNorm f p (volume.restrict U) +
      (‖ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ F Complex.reCLM‖ₑ *
          eLpNormWkp p U k (fun z => D z 1) +
        ‖ContinuousLinearMap.smulRightL ℝ ℝ ℝ ℂ F Complex.imCLM‖ₑ *
          eLpNormWkp p U k (fun z => D z Complex.I)) := by
  refine (eLpNormWkp_succ_le hD).trans ?_
  gcongr
  conv_lhs => rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D]
  exact (eLpNormWkp_add_le hp).trans (add_le_add (ContinuousLinearMap.eLpNormWkp_comp_le _)
    (ContinuousLinearMap.eLpNormWkp_comp_le _))

end TauCeti
