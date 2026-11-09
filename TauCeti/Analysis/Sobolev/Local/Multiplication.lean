/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.MixedMultiplication
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates

/-!
# Mixed-exponent products of local Sobolev maps on planar domains

Let `p > 2`, `1 ≤ q ≤ p` and let `B : F × G → H` be continuous bilinear with `G`
finite-dimensional. This file proves the first two orders of the mixed-exponent product
theorem for the local classes `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` on an open planar
domain `Ω`.

* Order zero: for `f ∈ Lᵖ_loc` and `g ∈ W^{1,q}_loc`, the product `B(f, g)` is in `L^q_loc`.
  This combines Hölder's inequality with the local gain of integrability `W^{1,q} ⊂ Lʳ`,
  where `1/p + 1/r = 1/q`, and it uses `p > 2`.
* Order one: for `f ∈ W^{1,p}_loc` continuous on `Ω` and `g ∈ W^{1,q}_loc` with `1 < q`, the
  product `B(f, g)` is in `W^{1,q}_loc`, with weak derivative `B(Df, g) + B(f, Dg)`.
  At `q = p` this is the algebra property of `W^{1,p}_loc`.

Both come with local bounds that are uniform in the bilinear map. Continuity of the first factor
is an explicit hypothesis of the order-one statements; it is automatic for `p > 2` by Morrey's
embedding, which is not used here.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_of_holderTriple`: the local gain of integrability.
* `TauCeti.exists_eLpNorm_bilin_le` and `TauCeti.MemLpLoc.bilin_memWkpLoc`: the order-zero
  bound and membership.
* `TauCeti.HasWeakFDerivOn.bilin_of_continuousOn`: the weak Leibniz rule for the order-one
  product.
* `TauCeti.exists_eLpNorm_bilin_add_eLpNorm_deriv_le` and `TauCeti.MemWkpLoc.bilin`: the
  order-one bound and membership.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Module
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- A real function with a weak derivative on `W`, both in `L^q(W)`, defines an element of
`W^{1,q}(W)` whose norm is at most the sum of the two `L^q` norms. -/
private theorem exists_w1p_of_hasWeakFDerivOn {s : ℝ≥0∞} [Fact (1 ≤ s)] {W : Opens ℂ}
    {u : ℂ → ℝ} {D : ℂ → ℂ →L[ℝ] ℝ} (h : HasWeakFDerivOn volume W u D)
    (hu : MemLp u s (volume.restrict W)) (hD : MemLp D s (volume.restrict W)) :
    ∃ w : W1p volume W s, W1p.value w =ᵐ[volume.restrict W] u ∧
      ‖w‖ₑ ≤ eLpNorm u s (volume.restrict W) + eLpNorm D s (volume.restrict W) := by
  let e := (InnerProductSpace.toDual ℝ ℂ).symm
  have hgm : AEStronglyMeasurable (fun x => e (D x)) (volume.restrict W) :=
    e.continuous.comp_aestronglyMeasurable hD.aestronglyMeasurable
  have hnorm : ∀ x, ‖e (D x)‖ = ‖D x‖ := fun x => e.norm_map (D x)
  have hg : MemLp (fun x => e (D x)) s (volume.restrict W) :=
    hD.of_le hgm (Filter.Eventually.of_forall fun x => (hnorm x).le)
  have hderiv : (fun x => innerSL ℝ (hg.toLp _ x)) =ᵐ[volume.restrict W] D := by
    filter_upwards [hg.coeFn_toLp] with x hx
    ext v
    rw [hx, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
  have hw : HasWeakFDerivOn volume W (hu.toLp u) (fun x => innerSL ℝ (hg.toLp _ x)) :=
    (h.congr_ae hu.coeFn_toLp.symm).congr_ae_deriv hderiv.symm
  refine ⟨W1p.mk _ _ hw, by rw [W1p.value_mk]; exact hu.coeFn_toLp, ?_⟩
  calc
    ‖W1p.mk _ _ hw‖ₑ ≤ ‖W1p.value (W1p.mk _ _ hw)‖ₑ + ‖W1p.gradient (W1p.mk _ _ hw)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
        ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (W1p.norm_le_norm_value_add_norm_gradient _)
    _ = eLpNorm u s (volume.restrict W) + eLpNorm D s (volume.restrict W) := by
      rw [W1p.value_mk, W1p.gradient_mk, Lp.enorm_def, Lp.enorm_def,
        eLpNorm_congr_ae hu.coeFn_toLp, eLpNorm_congr_ae hg.coeFn_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae hgm hD.aestronglyMeasurable (Filter.Eventually.of_forall hnorm)

/-- A scalar `W^{1,q}(W)` bound into `Lʳ(V)` extends, coordinate by coordinate, to weakly
differentiable maps with finite-dimensional values. -/
private theorem exists_eLpNorm_le_of_w1p_bound [Fact (1 ≤ (q : ℝ≥0∞))] {r : ℝ≥0∞}
    (hr : 1 ≤ r) {W : Opens ℂ} {V : Set ℂ} (hVW : V ⊆ W)
    (hbound : ∃ C : ℝ≥0, ∀ u : W1p volume W q,
      eLpNorm (W1p.value u) r (volume.restrict V) ≤ C * ‖u‖ₑ) :
    ∃ C : ℝ≥0, ∀ (g : ℂ → G) (Dg : ℂ → ℂ →L[ℝ] G), HasWeakFDerivOn volume W g Dg →
      MemLp g q (volume.restrict W) → MemLp Dg q (volume.restrict W) →
      eLpNorm g r (volume.restrict V) ≤
        C * (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)) := by
  obtain ⟨C, hC⟩ := hbound
  let b := Module.finBasis ℝ G
  let c : Fin (finrank ℝ G) → G →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  refine ⟨∑ i, ‖b i‖₊ * C * ‖c i‖₊, fun g Dg hg hgq hDq => ?_⟩
  set X := eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)
  have hVm := Measure.restrict_mono_set volume hVW
  have key (i : Fin (finrank ℝ G)) :
      eLpNorm (fun x => c i (g x)) r (volume.restrict V) ≤ C * ‖c i‖ₑ * X := by
    have hci := (hasWeakFDerivOn_iff_coordinates b).1 hg i
    obtain ⟨w, hw, hwn⟩ := exists_w1p_of_hasWeakFDerivOn hci
      (hgq.continuousLinearMap_comp (c i))
      (hDq.continuousLinearMap_comp (ContinuousLinearMap.compL ℝ ℂ G ℝ (c i)))
    calc
      eLpNorm (fun x => c i (g x)) r (volume.restrict V)
          = eLpNorm (W1p.value w) r (volume.restrict V) :=
        eLpNorm_congr_ae (hw.filter_mono (ae_mono hVm)).symm
      _ ≤ C * ‖w‖ₑ := hC w
      _ ≤ C * (‖c i‖ₑ * eLpNorm g q (volume.restrict W) +
          ‖c i‖ₑ * eLpNorm Dg q (volume.restrict W)) := by
        gcongr
        refine hwn.trans (add_le_add ?_ ?_)
        · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _
            ((c i).continuous.comp_aestronglyMeasurable hgq.aestronglyMeasurable)
            (Filter.Eventually.of_forall fun x => (c i).le_opENorm (g x))
        · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _
            ((ContinuousLinearMap.compL ℝ ℂ G ℝ (c i)).continuous.comp_aestronglyMeasurable
              hDq.aestronglyMeasurable)
            (Filter.Eventually.of_forall fun x => (c i).opENorm_comp_le (Dg x))
      _ = C * ‖c i‖ₑ * X := by rw [← mul_add, mul_assoc]
  have hsum : g = ∑ i, fun x => c i (g x) • b i := by
    funext x
    rw [Finset.sum_apply]
    exact (b.sum_repr (g x)).symm
  calc
    eLpNorm g r (volume.restrict V)
        ≤ ∑ i, eLpNorm (fun x => c i (g x) • b i) r (volume.restrict V) := by
      conv_lhs => rw [hsum]
      exact eLpNorm_sum_le hr
    _ ≤ ∑ i, ‖b i‖ₑ * (C * ‖c i‖ₑ * X) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ ?_
        (Filter.Eventually.of_forall fun x => ?_)).trans (by gcongr; exact key i)
      · exact (((c i).continuous.comp_aestronglyMeasurable
          (hgq.aestronglyMeasurable.mono_measure hVm)).smul_const (b i))
      · rw [enorm_smul, mul_comm]
    _ = ↑(∑ i, ‖b i‖₊ * C * ‖c i‖₊) * X := by
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [enorm_eq_nnnorm]
      ring

/-- The local `W^{1,q} ⊂ Lʳ` bound at the exponent with `1/p + 1/r = 1/q`, on a compact set
inside an open set. -/
private theorem exists_eLpNorm_le_of_holderTriple (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {r : ℝ≥0∞} [hpr : ENNReal.HolderTriple p r q] {K : Set ℂ}
    (hK : IsCompact K) {W : Opens ℂ} (hKW : K ⊆ W) :
    ∃ C : ℝ≥0, ∀ (g : ℂ → G) (Dg : ℂ → ℂ →L[ℝ] G), HasWeakFDerivOn volume W g Dg →
      MemLp g q (volume.restrict W) → MemLp Dg q (volume.restrict W) →
      eLpNorm g r (volume.restrict K) ≤
        C * (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)) := by
  have hp' : (finrank ℝ ℂ : ℝ≥0) < p := by
    rw [Complex.finrank_real_complex]
    exact_mod_cast hp
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨r', hr', hhr', S, hS⟩ := W1p.exists_mixed_valueEmbedding (μ := volume) (Ω := W) hp'
    hqp (V := K) (by rwa [hKc]) (by rwa [hKc])
  have hrr : r = r' := ENNReal.HolderTriple.unique_of_ne_zero (p : ℝ≥0∞) r r'
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  subst hrr
  let _ : Fact (1 ≤ r) := ⟨hr'⟩
  refine exists_eLpNorm_le_of_w1p_bound hr' hKW ⟨‖S‖₊, fun u => ?_⟩
  rw [← eLpNorm_congr_ae (hS u), ← Lp.enorm_def]
  simpa only [enorm_eq_nnnorm] using S.le_opENorm u

omit [FiniteDimensional ℝ G] in
/-- An open set between a compact subset of `Ω` and `Ω`, with compact closure in `Ω`. -/
private theorem exists_opens_between {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ W : Opens ℂ, K ⊆ W ∧ closure (W : Set ℂ) ⊆ Ω ∧ IsCompact (closure (W : Set ℂ)) := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨W, hWo⟩, hKW, hWΩ, hWc⟩

omit [NormedSpace ℝ F] [FiniteDimensional ℝ G] in
/-- Local `Lᵖ` membership on `Ω` gives `Lᵖ` membership on an open set with compact closure
in `Ω`. -/
private theorem MemLpLoc.memLp_of_closure {s : ℝ≥0∞} {f : ℂ → F} (hf : MemLpLoc s Ω f)
    {W : Set ℂ} (hWΩ : closure W ⊆ Ω) (hWc : IsCompact (closure W)) :
    MemLp f s (volume.restrict W) :=
  (memLpLoc_iff.1 hf _ hWΩ hWc).mono_measure (Measure.restrict_mono_set volume subset_closure)

/-- **Local gain of integrability.** For `p > 2` and `1 ≤ q ≤ p`, a map in `W^{1,q}_loc` with
finite-dimensional values is in `Lʳ_loc` for `1/p + 1/r = 1/q`. At `q = p` this is `r = ∞`. -/
theorem MemWkpLoc.memLpLoc_of_holderTriple (hp : 2 < p) (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))]
    {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : ℂ → G} (hg : MemWkpLoc q Ω 1 g) :
    MemLpLoc r Ω g := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := exists_opens_between hK hKΩ
  obtain ⟨Dg, hDg, hDq⟩ := hg.exists_weakFDeriv_of_isOpen
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_holderTriple (G := G) (r := r) hp hqp hK hKW
  have hgW := hg.memLpLoc.memLp_of_closure hWΩ hWc
  have hDW := (memWkpLoc_zero_iff.1 hDq).memLp_of_closure hWΩ hWc
  exact (hC g Dg (hDg.mono (subset_closure.trans hWΩ)) hgW hDW).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨hgW.eLpNorm_lt_top, hDW.eLpNorm_lt_top⟩))

/-- The exponent `r` with `1/p + 1/r = 1/q`, for `q ≤ p`. -/
private theorem holderTriple_inv_sub (hqp : q ≤ p) :
    ENNReal.HolderTriple p ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 (by exact_mod_cast hqp))]⟩

/-- **Local bound for order-zero mixed products.** For `p > 2`, `1 ≤ q ≤ p`, a compact `K`
and an open `W ⊇ K`, one constant bounds `‖B(f, g)‖_{L^q(K)}` by
`‖B‖ ‖f‖_{Lᵖ(K)} (‖g‖_{L^q(W)} + ‖Dg‖_{L^q(W)})` for every bilinear map `B`, every `f`
and every weakly differentiable `g` on `W`. -/
theorem exists_eLpNorm_bilin_le (hp : 2 < p) (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))]
    {K : Set ℂ} (hK : IsCompact K) {W : Opens ℂ} (hKW : K ⊆ W) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G) (Dg : ℂ → ℂ →L[ℝ] G),
      AEStronglyMeasurable f (volume.restrict K) → HasWeakFDerivOn volume W g Dg →
      MemLp g q (volume.restrict W) → MemLp Dg q (volume.restrict W) →
      eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) ≤
        C * ‖B‖ₑ * eLpNorm f p (volume.restrict K) *
          (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)) := by
  let _ := holderTriple_inv_sub hqp
  obtain ⟨C, hC⟩ := exists_eLpNorm_le_of_holderTriple (G := G)
    (r := ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹) hp hqp hK hKW
  refine ⟨C, fun B f g Dg hf hg hgq hDq => ?_⟩
  calc
    _ ≤ ‖B‖ₑ * eLpNorm f p (volume.restrict K) *
        eLpNorm g ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹ (volume.restrict K) :=
      eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm B hf
        (hgq.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hKW))
    _ ≤ ‖B‖ₑ * eLpNorm f p (volume.restrict K) *
        (C * (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W))) :=
      mul_le_mul_right (hC g Dg hg hgq hDq) _
    _ = _ := by ring

/-- **Order-zero mixed products.** For `p > 2` and `1 ≤ q ≤ p`, the product of a locally `Lᵖ`
map with a `W^{1,q}_loc` map with finite-dimensional values is locally `L^q`. -/
theorem MemLpLoc.bilin_memWkpLoc (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {f : ℂ → F} {g : ℂ → G} (hf : MemLpLoc p Ω f)
    (hg : MemWkpLoc q Ω 1 g) : MemLpLoc q Ω (fun z => B (f z) (g z)) := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := exists_opens_between hK hKΩ
  obtain ⟨Dg, hDg, hDq⟩ := hg.exists_weakFDeriv_of_isOpen
  obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le (F := F) (G := G) (H := H) hp hqp hK hKW
  have hgW := hg.memLpLoc.memLp_of_closure hWΩ hWc
  have hDW := (memWkpLoc_zero_iff.1 hDq).memLp_of_closure hWΩ hWc
  have hfK := memLpLoc_iff.1 hf K hKΩ hK
  exact (hC B f g Dg hfK.aestronglyMeasurable (hDg.mono (subset_closure.trans hWΩ)) hgW
    hDW).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      enorm_lt_top) hfK.eLpNorm_lt_top)
      (ENNReal.add_lt_top.2 ⟨hgW.eLpNorm_lt_top, hDW.eLpNorm_lt_top⟩))

/-- **The weak Leibniz rule for order-one mixed products.** For `p > 2` and `1 < q ≤ p`, let
`f` be continuous on `Ω` with weak derivative `Df ∈ Lᵖ_loc`, and let `g ∈ L^q_loc` have weak
derivative `Dg ∈ L^q_loc`. Then `B(f, g)` has weak derivative `B(Df, g) + B(f, Dg)`.
The local gain of integrability of `g` pairs it with `Df`. -/
theorem HasWeakFDerivOn.bilin_of_continuousOn [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {Df : ℂ → ℂ →L[ℝ] F} {g : ℂ → G}
    {Dg : ℂ → ℂ →L[ℝ] G} (hf : HasWeakFDerivOn volume Ω f Df) (hfc : ContinuousOn f Ω)
    (hDf : MemLpLoc p Ω Df) (hg : HasWeakFDerivOn volume Ω g Dg) (hgq : MemLpLoc q Ω g)
    (hDg : MemLpLoc q Ω Dg) :
    HasWeakFDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) := by
  have hq1 : (1 : ℝ≥0∞) < q := by exact_mod_cast hq
  have hp1 : (1 : ℝ≥0∞) < p := hq1.trans_le (by exact_mod_cast hqp)
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨hq1.le⟩
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨hp1.le⟩
  -- Exponents: `f` in `L^{q'}`, `Df` in `Lᵖ`, `g` in `L^b` with `b = max q p'`, `Dg` in `L^q`.
  set a := (q : ℝ≥0∞).conjExponent
  set p' := (p : ℝ≥0∞).conjExponent
  set b := max (q : ℝ≥0∞) p'
  have ha : a ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one a q).2 hq1.ne'
  have hp' : p' ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p' p).2 hp1.ne'
  have hb : b ≠ ⊤ := max_ne_top ENNReal.coe_ne_top hp'
  let _ : Fact (1 ≤ a) := ⟨ENNReal.HolderConjugate.one_le a q⟩
  let _ : Fact (1 ≤ b) := ⟨hq1.le.trans (le_max_left _ _)⟩
  have haq : a⁻¹ + (q : ℝ≥0∞)⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one a q
  have hpp : (p : ℝ≥0∞)⁻¹ + p'⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one _ _
  have hbq : b⁻¹ ≤ (q : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 (le_max_left _ _)
  have hbp : b⁻¹ ≤ p'⁻¹ := ENNReal.inv_le_inv.2 (le_max_right _ _)
  -- `g` lies in `L^b_loc` because `q ≤ b ≤ r` with `1/p + 1/r = 1/q`.
  let r := ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹
  let _ := holderTriple_inv_sub hqp
  have hgr : MemLpLoc r Ω g := MemWkpLoc.memLpLoc_of_holderTriple hp hqp
    (memWkpLoc_succ_iff_of_isOpen.2 ⟨hgq, Dg, hg, memWkpLoc_zero_iff.2 hDg⟩)
  have hbr : b ≤ r := by
    refine max_le (ENNReal.inv_le_inv.1 ?_) (ENNReal.inv_le_inv.1 ?_)
    · rw [inv_inv]
      exact tsub_le_self
    · rw [inv_inv, ← ENNReal.HolderConjugate.one_sub_inv (p : ℝ≥0∞) p']
      exact tsub_le_tsub_right (ENNReal.inv_le_one.2 hq1.le) _
  have hgb : MemLpLoc b Ω g := memLpLoc_iff.2 fun K hKΩ hK =>
    let _ : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    (memLpLoc_iff.1 hgr K hKΩ hK).mono_exponent hbr
  exact hf.bilin_of_memLp_mixed B ha ENNReal.coe_ne_top hb ENNReal.coe_ne_top
    ((add_le_add le_rfl hbq).trans haq.le) ((add_le_add le_rfl hbp).trans hpp.le) haq.le hg
    (fun K hK hKΩ => memLpLoc_iff.1 hfc.memLpLoc K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDf K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hgb K hKΩ hK) (fun K hK hKΩ => memLpLoc_iff.1 hDg K hKΩ hK)

/-- **Local bound for order-one mixed products.** For `p > 2`, `1 ≤ q ≤ p`, a compact `K` and
an open `W ⊇ K`, one constant bounds the `L^q(K)` norms of `B(f, g)` and of
`B(Df, g) + B(f, Dg)` by `‖B‖ (‖f‖_{L^∞(K)} + ‖Df‖_{Lᵖ(K)}) (‖g‖_{L^q(W)} + ‖Dg‖_{L^q(W)})`.
At `q = p` this is the local bound for the algebra property of `W^{1,p}_loc`. -/
theorem exists_eLpNorm_bilin_add_eLpNorm_deriv_le (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {K : Set ℂ} (hK : IsCompact K) {W : Opens ℂ} (hKW : K ⊆ W) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (Df : ℂ → ℂ →L[ℝ] F) (g : ℂ → G)
      (Dg : ℂ → ℂ →L[ℝ] G),
      AEStronglyMeasurable f (volume.restrict K) → AEStronglyMeasurable Df (volume.restrict K) →
      HasWeakFDerivOn volume W g Dg →
      MemLp g q (volume.restrict W) → MemLp Dg q (volume.restrict W) →
      eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) +
          eLpNorm (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) q
            (volume.restrict K) ≤
        C * ‖B‖ₑ * (eLpNorm f ∞ (volume.restrict K) + eLpNorm Df p (volume.restrict K)) *
          (eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)) := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le (F := ℂ →L[ℝ] F) (G := G) (H := ℂ →L[ℝ] H)
    hp hqp hK hKW
  refine ⟨2 + C, fun B f Df g Dg hf hDf hg hgq hDq => ?_⟩
  have hKm := Measure.restrict_mono_set volume hKW
  set X := eLpNorm g q (volume.restrict W) + eLpNorm Dg q (volume.restrict W)
  set M := eLpNorm f ∞ (volume.restrict K)
  set N := eLpNorm Df p (volume.restrict K)
  have hgK : eLpNorm g q (volume.restrict K) ≤ X :=
    (eLpNorm_mono_measure g hKm).trans le_self_add
  have hDgK : eLpNorm Dg q (volume.restrict K) ≤ X :=
    (eLpNorm_mono_measure Dg hKm).trans le_add_self
  have h₀ : eLpNorm (fun z => B (f z) (g z)) q (volume.restrict K) ≤ ‖B‖ₑ * M * X :=
    (eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm (p := ∞) B hf
      (hgq.aestronglyMeasurable.mono_measure hKm)).trans (by gcongr)
  have h₁ : eLpNorm (fun z => B.precompL ℂ (Df z) (g z)) q (volume.restrict K) ≤
      C * ‖B‖ₑ * N * X :=
    (hC (B.precompL ℂ) Df g Dg hDf hg hgq hDq).trans (by
      gcongr
      exact enorm_le_iff_norm_le.2 (ContinuousLinearMap.norm_precompL_le ℂ B))
  have h₂ : eLpNorm (fun z => B.precompR ℂ (f z) (Dg z)) q (volume.restrict K) ≤
      ‖B‖ₑ * M * X :=
    (eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm (p := ∞) (B.precompR ℂ) hf
      (hDq.aestronglyMeasurable.mono_measure hKm)).trans (by
      gcongr
      exact enorm_le_iff_norm_le.2 (ContinuousLinearMap.norm_precompR_le ℂ B))
  have hadd := eLpNorm_add_le (μ := volume.restrict K)
    (f := fun z => B.precompL ℂ (Df z) (g z)) (g := fun z => B.precompR ℂ (f z) (Dg z))
    (Fact.out : (1 : ℝ≥0∞) ≤ q)
  calc
    _ ≤ ‖B‖ₑ * M * X + (C * ‖B‖ₑ * N * X + ‖B‖ₑ * M * X) :=
      add_le_add h₀ (hadd.trans (add_le_add h₁ h₂))
    _ = ‖B‖ₑ * (2 * M + C * N) * X := by ring
    _ ≤ ‖B‖ₑ * ((2 + C) * (M + N)) * X := by
      gcongr
      calc
        2 * M + C * N ≤ (2 + C) * M + (2 + C) * N := by gcongr <;> simp
        _ = (2 + C) * (M + N) := by ring
    _ = ↑(2 + C) * ‖B‖ₑ * (M + N) * X := by push_cast; ring

/-- **Order-one mixed products.** For `p > 2` and `1 < q ≤ p`, the product of a continuous
`W^{1,p}_loc` map with a `W^{1,q}_loc` map with finite-dimensional values is in
`W^{1,q}_loc`. At `q = p` this is the algebra property of `W^{1,p}_loc` under continuous bilinear
maps. -/
theorem MemWkpLoc.bilin [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f) (hfc : ContinuousOn f Ω)
    (hg : MemWkpLoc q Ω 1 g) : MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  obtain ⟨Df, hDf, hDfp⟩ := hf.exists_weakFDeriv_of_isOpen
  obtain ⟨Dg, hDg, hDgq⟩ := hg.exists_weakFDeriv_of_isOpen
  have hfi : MemLpLoc ∞ Ω f := hfc.memLpLoc
  have hgq := hg.memLpLoc
  rw [memWkpLoc_zero_iff] at hDfp hDgq
  have hD := hDf.bilin_of_continuousOn B hp hq hqp hfc hDfp hDg hgq hDgq
  refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, _, hD,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
  · exact B.memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK) (memLpLoc_iff.1 hgq K hKΩ hK)
  · exact (memLpLoc_iff.1 (MemLpLoc.bilin_memWkpLoc (B.precompL ℂ) hp hqp hDfp hg) K hKΩ
      hK).add ((B.precompR ℂ).memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK)
        (memLpLoc_iff.1 hDgq K hKΩ hK))

end TauCeti
