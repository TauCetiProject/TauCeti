/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.MixedMultiplication
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Local.Mollification
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Data.ENNReal.Holder
import TauCeti.Data.ENNReal.Inv

/-!
# Mixed-exponent products of local Sobolev maps on planar domains

Let `p > 2`, `1 ≤ q ≤ p` and let `B : F × G → H` be continuous bilinear with `G`
finite-dimensional. This file proves the first two orders of the mixed-exponent product
theorem for the local classes `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` on an open planar
domain `Ω`.

* Order zero: for `f ∈ Lᵖ_loc` and `g ∈ W^{1,q}_loc`, the product `B(f, g)` is in `L^q_loc`.
  This combines Hölder's inequality with the local gain of integrability `W^{1,q} ⊂ Lʳ`,
  where `1/p + 1/r = 1/q`, and it uses `p > 2`.
* Order one: for `f ∈ W^{1,p}_loc ∩ L^∞_loc` and `g ∈ W^{1,q}_loc` with `1 < q`, the product
  `B(f, g)` is in `W^{1,q}_loc`, with weak derivative `B(Df, g) + B(f, Dg)`.
  At `q = p` this is the algebra property of `W^{1,p}_loc`. When `F` is finite-dimensional, the
  local boundedness of `f` follows from the local gain of integrability at `q = p`.
* Extended-exponent weak Leibniz rule: when both `F` and `G` are finite-dimensional, mollifying
  `f` locally proves the weak Leibniz rule `HasWeakFDerivOn.bilin` for all `2 < p ≤ ∞` and
  `1 ≤ q ≤ ∞`, including both the `p = ∞` and `q = 1` endpoints (using `W^{1,1}_loc ⊂ L²_loc`
  on planar domains).

Both order-zero and finite-exponent order-one results rest on local bounds that are uniform in the
bilinear map.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_of_holderTriple`: the local gain of integrability.
* `TauCeti.MemLpLoc.bilin_of_memWkpLoc`: order-zero membership.
* `TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`: the weak Leibniz rule for finite exponents
  `1 < q ≤ p`.
* `TauCeti.MemWkpLoc.bilin_of_memLpLoc_top` and `TauCeti.MemWkpLoc.bilin`: order-one membership.
* `TauCeti.HasWeakFDerivOn.bilin`: the weak Leibniz rule for all `2 < p ≤ ∞` and `1 ≤ q ≤ ∞` with
  finite-dimensional factors `F, G`.
* `TauCeti.HasWeakFDerivOn.ae_bilin_add_bilin_eq_zero_of_eq_const`: differentiating a constant
  bilinear product `B(f, g) = c` weakly on `Ω`.
* `TauCeti.HasWeakFDerivOn.ae_apply_add_apply_eq_zero_of_comp_self_eq_const`: differentiating
  `J ∘ J = c` weakly on `Ω` for `J ∈ W^{1,p}_loc` (`2 < p ≤ ∞`).

The local bounds behind them, `TauCeti.W1p.exists_eLpNorm_le_of_holderTriple`,
`TauCeti.W1p.exists_eLpNorm_bilin_le` and `TauCeti.W1p.exists_eLpNorm_bilin_add_eLpNorm_deriv_le`,
hold in any finite-dimensional space with `dim E < p` and live in
`TauCeti.Analysis.Sobolev.W1p.MixedMultiplication`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open Filter LineDeriv MeasureTheory Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- **Local gain of integrability.** For `p > 2` and `1 ≤ q ≤ p`, a map in `W^{1,q}_loc` with
finite-dimensional values is in `Lʳ_loc` for `1/p + 1/r = 1/q`. At `q = p` this is `r = ∞`. -/
theorem MemWkpLoc.memLpLoc_of_holderTriple (hp : 2 < p) (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))]
    {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : ℂ → G} (hg : MemWkpLoc q Ω 1 g) :
    MemLpLoc r Ω g := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨Dg, hDg, hDq⟩ := hg.exists_weakFDeriv_of_isOpen
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_le_of_holderTriple (μ := volume) (Ω := ⟨W, hWo⟩)
    (G := G) (r := r) (by simpa using hp) hqp hK hKW
  have hgW := hg.memLpLoc.memLp_of_closure_subset hWc hWΩ
  have hDW := (memWkpLoc_zero_iff.1 hDq).memLp_of_closure_subset hWc hWΩ
  exact (hC g Dg (hDg.mono (subset_closure.trans hWΩ)) hgW hDW).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨hgW.eLpNorm_lt_top, hDW.eLpNorm_lt_top⟩))

/-- **Order-zero mixed products.** For `p > 2` and `1 ≤ q ≤ p`, the product of a locally `Lᵖ`
map with a `W^{1,q}_loc` map with finite-dimensional values is locally `L^q`. -/
theorem MemLpLoc.bilin_of_memWkpLoc (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {f : ℂ → F} {g : ℂ → G} (hf : MemLpLoc p Ω f)
    (hg : MemWkpLoc q Ω 1 g) : MemLpLoc q Ω (fun z => B (f z) (g z)) := by
  let _ := ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q) (by exact_mod_cast hqp)
  have hgr : MemLpLoc ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹ Ω g :=
    hg.memLpLoc_of_holderTriple hp hqp
  exact memLpLoc_iff.2 fun K hKΩ hK =>
    B.memLp_of_bilin q (memLpLoc_iff.1 hf K hKΩ hK) (memLpLoc_iff.1 hgr K hKΩ hK)

/-- **The weak Leibniz rule for order-one mixed products.** For `p > 2` and `1 < q ≤ p`, let
`f ∈ L^{q'}_loc` have weak derivative `Df ∈ Lᵖ_loc`, where `q'` is the conjugate exponent of `q`,
and let `g ∈ L^q_loc` have weak derivative `Dg ∈ L^q_loc`. Then `B(f, g)` has weak derivative
`B(Df, g) + B(f, Dg)`. -/
theorem HasWeakFDerivOn.bilin_of_memLpLoc [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {Df : ℂ → ℂ →L[ℝ] F} {g : ℂ → G}
    {Dg : ℂ → ℂ →L[ℝ] G} (hf : HasWeakFDerivOn volume Ω f Df)
    (hfi : MemLpLoc (q : ℝ≥0∞).conjExponent Ω f)
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
  let _ := ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q) (by exact_mod_cast hqp)
  have hgr : MemLpLoc r Ω g := MemWkpLoc.memLpLoc_of_holderTriple hp hqp
    (memWkpLoc_succ_iff_of_isOpen.2 ⟨hgq, Dg, hg, memWkpLoc_zero_iff.2 hDg⟩)
  have hbr : b ≤ r := by
    refine max_le (ENNReal.inv_le_inv.1 ?_) (ENNReal.inv_le_inv.1 ?_)
    · rw [inv_inv]
      exact tsub_le_self
    · rw [inv_inv, ← ENNReal.HolderConjugate.one_sub_inv (p : ℝ≥0∞) p']
      exact tsub_le_tsub_right (ENNReal.inv_le_one.2 hq1.le) _
  have hgb : MemLpLoc b Ω g := hgr.mono_exponent hbr
  exact hf.bilin_of_memLp B ha ENNReal.coe_ne_top hb ENNReal.coe_ne_top
    ((add_le_add le_rfl hbq).trans haq.le) ((add_le_add le_rfl hbp).trans hpp.le) haq.le hg
    (fun K hK hKΩ => memLpLoc_iff.1 hfi K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDf K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hgb K hKΩ hK) (fun K hK hKΩ => memLpLoc_iff.1 hDg K hKΩ hK)

/-- **Order-one mixed products.** For `p > 2` and `1 < q ≤ p`, the product of a locally bounded
`W^{1,p}_loc` map with a `W^{1,q}_loc` map with finite-dimensional values is in
`W^{1,q}_loc`. At `q = p` this is the algebra property of `W^{1,p}_loc` under continuous bilinear
maps. -/
theorem MemWkpLoc.bilin_of_memLpLoc_top [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f)
    (hfi : MemLpLoc ∞ Ω f) (hg : MemWkpLoc q Ω 1 g) :
    MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  obtain ⟨Df, hDf, hDfp⟩ := hf.exists_weakFDeriv_of_isOpen
  obtain ⟨Dg, hDg, hDgq⟩ := hg.exists_weakFDeriv_of_isOpen
  have hgq := hg.memLpLoc
  rw [memWkpLoc_zero_iff] at hDfp hDgq
  have hD := hDf.bilin_of_memLpLoc B hp hq hqp (hfi.mono_exponent le_top) hDfp hDg hgq hDgq
  refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, _, hD,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
  · exact B.memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK) (memLpLoc_iff.1 hgq K hKΩ hK)
  · exact (memLpLoc_iff.1 (MemLpLoc.bilin_of_memWkpLoc (B.precompL ℂ) hp hqp hDfp hg) K hKΩ
      hK).add ((B.precompR ℂ).memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK)
        (memLpLoc_iff.1 hDgq K hKΩ hK))

/-- **Order-one mixed products with finite-dimensional factors.** For `p > 2` and
`1 < q ≤ p`, the product of a `W^{1,p}_loc` map with a `W^{1,q}_loc` map, both with
finite-dimensional values, is in `W^{1,q}_loc`. The first factor is locally bounded by the local
gain of integrability at `q = p`. -/
theorem MemWkpLoc.bilin [FiniteDimensional ℝ F] [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f)
    (hg : MemWkpLoc q Ω 1 g) : MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  exact hf.bilin_of_memLpLoc_top B hp hq hqp (hf.memLpLoc_of_holderTriple hp le_rfl) hg

/-- **The weak Leibniz rule for mixed-exponent local Sobolev maps.** For `2 < p ≤ ∞` and
`1 ≤ q ≤ ∞`, if `f ∈ W^{1,p}_loc(Ω; F)` has weak derivative `Df` and `g ∈ W^{1,q}_loc(Ω; G)` has
weak derivative `Dg` with `F` and `G` finite-dimensional and `H` complete, then for any continuous
bilinear map `B : F →L[ℝ] G →L[ℝ] H`, the product `B(f, g)` has weak derivative
`B(Df, g) + B(f, Dg)` on `Ω`. This includes both the `p = ∞` and `q = 1` endpoints. -/
theorem HasWeakFDerivOn.bilin [FiniteDimensional ℝ F] [CompleteSpace H]
    (B : F →L[ℝ] G →L[ℝ] H) {p q : ℝ≥0∞} (hp : 2 < p) (hq : 1 ≤ q)
    {f : ℂ → F} {Df : ℂ → ℂ →L[ℝ] F} {g : ℂ → G} {Dg : ℂ → ℂ →L[ℝ] G}
    (hf : MemWkpLoc p Ω 1 f) (hDf : HasWeakFDerivOn volume Ω f Df)
    (hg : MemWkpLoc q Ω 1 g) (hDg : HasWeakFDerivOn volume Ω g Dg) :
    HasWeakFDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℝ F
  have hloc := Ω.isOpen.isLocallyClosed
  have hp1 : 1 < p := ENNReal.one_lt_two.trans hp
  have : p.HolderConjugate p.conjExponent := .conjExponent hp1.le
  have hfi : MemLpLoc ∞ Ω f := hf.memLpLoc_top hp
  have hDfp : MemLpLoc p Ω Df := hf.memLpLoc_of_hasWeakFDerivOn hDf
  have hg1 : MemWkpLoc (1 : ℝ≥0) Ω 1 g := hg.mono_exponent (by simpa using hq)
  have hDg1 : MemLpLoc (1 : ℝ≥0) Ω Dg := hg1.memLpLoc_of_hasWeakFDerivOn hDg
  have hg2 : MemLpLoc (2 : ℝ≥0) Ω g :=
    hg1.memLpLoc_of_inv_sub_inv_le le_rfl one_le_two (by norm_num)
  have hp'_le_two : p.conjExponent ≤ 2 := by
    rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv p p.conjExponent]
    exact ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 (zero_lt_one.trans hp1).ne')
      (ENNReal.inv_add_inv_lt_one_of_two_lt hp le_rfl).le
  have hgp' : MemLpLoc p.conjExponent Ω g := hg2.mono_exponent (by simpa using hp'_le_two)
  have hfg_loc : LocallyIntegrableOn (fun z => B (f z) (g z)) Ω :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).1 <| memLpLoc_iff.2 fun K hKΩ hK =>
      B.memLp_of_bilin 1 (memLpLoc_iff.1 hfi K hKΩ hK) (memLpLoc_iff.1 hg1.memLpLoc K hKΩ hK)
  refine hasWeakFDerivOn_iff.2 fun u => ?_
  have hDfg_loc : LocallyIntegrableOn (fun z => B (Df z u) (g z)) Ω :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).1 <| memLpLoc_iff.2 fun K hKΩ hK =>
      B.memLp_of_bilin 1
        (memLpLoc_iff.1 (hDfp.clm_comp (ContinuousLinearMap.apply ℝ F u)) K hKΩ hK)
        (memLpLoc_iff.1 hgp' K hKΩ hK)
  have hfDg_loc : LocallyIntegrableOn (fun z => B (f z) (Dg z u)) Ω :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).1 <| memLpLoc_iff.2 fun K hKΩ hK =>
      B.memLp_of_bilin 1 (memLpLoc_iff.1 hfi K hKΩ hK)
        (memLpLoc_iff.1 (hDg1.clm_comp (ContinuousLinearMap.apply ℝ G u)) K hKΩ hK)
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨inferInstance, hfg_loc, hDfg_loc.add hfDg_loc, fun ψ => ?_⟩
  have hDgu := hDg.hasWeakLineDerivOn u
  have hg_loc : LocallyIntegrableOn g Ω := hDgu.locallyIntegrableOn
  have hDgu_loc : LocallyIntegrableOn (fun z => Dg z u) Ω := hDgu.locallyIntegrableOn_deriv
  -- Smooth-factor Leibniz identity obtained by expanding `F_sm` in a finite basis of `F`.
  let b := Module.finBasis ℝ F
  let ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  have hsmooth {F_sm : ℂ → F} (hF : ContDiff ℝ ∞ F_sm) :
      (∫ z, (∂_{u} ψ : 𝓓(Ω, ℝ)) z • B (F_sm z) (g z)) +
          (∫ z, (ψ : ℂ → ℝ) z • B (fderiv ℝ F_sm z u) (g z)) =
        -∫ z, (ψ : ℂ → ℝ) z • B (F_sm z) (Dg z u) := by
    have hF1 : ContDiff ℝ 1 F_sm := hF.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤))
    have hDFu_c : Continuous fun z => fderiv ℝ F_sm z u :=
      (ContinuousLinearMap.apply ℝ F u).continuous.comp (hF1.continuous_fderiv one_ne_zero)
    have hi1 (i : Fin (finrank ℝ F)) :
        Integrable (fun z => (∂_{u} ψ : 𝓓(Ω, ℝ)) z • B (ℓ i (F_sm z) • b i) (g z)) volume := by
      have hloc1 : LocallyIntegrableOn (fun z => ℓ i (F_sm z) • B (b i) (g z)) Ω :=
        (memLpLoc_one_iff_locallyIntegrableOn hloc).1 <|
          (hg1.memLpLoc.clm_comp (B (b i))).continuousOn_smul
            ((ℓ i).continuous.comp hF.continuous).continuousOn
      simpa only [map_smul, smul_apply] using (∂_{u} ψ).integrable_smul hloc1
    have hi2 (i : Fin (finrank ℝ F)) :
        Integrable (fun z => (ψ : ℂ → ℝ) z • B (ℓ i (fderiv ℝ F_sm z u) • b i) (g z)) volume := by
      have hloc2 : LocallyIntegrableOn (fun z => ℓ i (fderiv ℝ F_sm z u) • B (b i) (g z)) Ω :=
        (memLpLoc_one_iff_locallyIntegrableOn hloc).1 <|
          (hg1.memLpLoc.clm_comp (B (b i))).continuousOn_smul
            ((ℓ i).continuous.comp hDFu_c).continuousOn
      simpa only [map_smul, smul_apply] using ψ.integrable_smul hloc2
    have hi3 (i : Fin (finrank ℝ F)) :
        Integrable (fun z => (ψ : ℂ → ℝ) z • B (ℓ i (F_sm z) • b i) (Dg z u)) volume := by
      have hloc3 : LocallyIntegrableOn (fun z => ℓ i (F_sm z) • B (b i) (Dg z u)) Ω :=
        (memLpLoc_one_iff_locallyIntegrableOn hloc).1 <|
          ((hDg1.clm_comp (ContinuousLinearMap.apply ℝ G u)).clm_comp (B (b i))).continuousOn_smul
            ((ℓ i).continuous.comp hF.continuous).continuousOn
      simpa only [map_smul, smul_apply] using ψ.integrable_smul hloc3
    have hterm (i : Fin (finrank ℝ F)) :
        (∫ z, (∂_{u} ψ : 𝓓(Ω, ℝ)) z • B (ℓ i (F_sm z) • b i) (g z)) +
            (∫ z, (ψ : ℂ → ℝ) z • B (ℓ i (fderiv ℝ F_sm z u) • b i) (g z)) =
          -∫ z, (ψ : ℂ → ℝ) z • B (ℓ i (F_sm z) • b i) (Dg z u) := by
      let ψi : 𝓓(Ω, ℝ) :=
        TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) ((ℓ i).contDiff.comp hF) ψ
      have hibp := congrArg (B (b i)) (hDgu.integral_lineDeriv_smul_eq_neg_integral_smul ψi)
      have hψi_l : Integrable (fun z => lineDeriv ℝ (ψi : ℂ → ℝ) z u • g z) volume := by
        simpa only [← TestFunction.lineDerivOp_apply] using (∂_{u} ψi).integrable_smul hg_loc
      rw [← (B (b i)).integral_comp_comm hψi_l, map_neg,
        ← (B (b i)).integral_comp_comm (ψi.integrable_smul hDgu_loc)] at hibp
      rw [← integral_add (hi1 i) (hi2 i)]
      refine (integral_congr_ae (.of_forall fun z => ?_)).trans
        (hibp.trans (congrArg Neg.neg (integral_congr_ae (.of_forall fun z => ?_))))
      · have hd1 : HasFDerivAt (fun w => ℓ i (F_sm w)) ((ℓ i).comp (fderiv ℝ F_sm z)) z :=
          (ℓ i).hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
        have hd2 : HasFDerivAt (ψ : ℂ → ℝ) (fderiv ℝ (ψ : ℂ → ℝ) z) z :=
          (ψ.contDiff.differentiable (by simp) z).hasFDerivAt
        have hψi_coe : (ψi : ℂ → ℝ) = (fun w => ℓ i (F_sm w)) * (ψ : ℂ → ℝ) := by
          ext w; simp [ψi, mul_comm]
        have hld : lineDeriv ℝ (ψi : ℂ → ℝ) z u =
            (∂_{u} ψ : 𝓓(Ω, ℝ)) z * ℓ i (F_sm z) + (ψ : ℂ → ℝ) z * ℓ i (fderiv ℝ F_sm z u) := by
          rw [hψi_coe, ((hd1.mul hd2).hasLineDerivAt u).lineDeriv]
          simp [TestFunction.lineDerivOp_apply_eq_fderiv ψ u z, mul_comm, add_comm]
        rw [hld, add_smul, map_add, map_smul, map_smul, map_smul, map_smul,
          smul_apply, smul_apply, smul_smul, smul_smul]
      · simp [ψi, map_smul, smul_smul]
    have hsum_eq := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ => hterm i
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum_eq
    have hrep (x : F) (y : G) : ∑ i, B (ℓ i x • b i) y = B x y := by
      have hx : ∑ i, ℓ i x • b i = x := by simp [ℓ]
      conv_rhs => rw [← hx, map_sum, sum_apply]
    rw [← integral_finsetSum _ fun i _ => hi1 i, ← integral_finsetSum _ fun i _ => hi2 i,
      ← integral_finsetSum _ fun i _ => hi3 i] at hsum_eq
    simpa only [← Finset.smul_sum, hrep] using hsum_eq
  -- Pass from the mollified sequence `fn n` to `f`.
  obtain ⟨fn, hfn, hlim_f, hlim_Df⟩ :=
    exists_contDiff_tendsto_integral_smul_bilin_of_hasWeakFDerivOn B hp1.le hfi hDf hDfp
      ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hlim := tendsto_nhds_unique
    ((hlim_f (∂_{u} ψ) (ψ.tsupport_lineDerivOp_subset u) hg_loc).add
      (hlim_Df u ψ Subset.rfl hgp'))
    ((hlim_f ψ Subset.rfl hDgu_loc).neg.congr fun n => (hsmooth (hfn n)).symm)
  have hψu : (fun z => lineDeriv ℝ (ψ : ℂ → ℝ) z u • B (f z) (g z)) =
      fun z => (∂_{u} ψ : 𝓓(Ω, ℝ)) z • B (f z) (g z) :=
    funext fun z => by rw [TestFunction.lineDerivOp_apply]
  have hadd_int : ∫ z, (ψ : ℂ → ℝ) z • (B (Df z u) (g z) + B (f z) (Dg z u)) =
      (∫ z, (ψ : ℂ → ℝ) z • B (Df z u) (g z)) + ∫ z, (ψ : ℂ → ℝ) z • B (f z) (Dg z u) := by
    rw [← integral_add (ψ.integrable_smul hDfg_loc) (ψ.integrable_smul hfDg_loc)]
    exact integral_congr_ae (.of_forall fun z => smul_add _ _ _)
  simp only [add_apply, ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  rw [hψu, hadd_int]
  exact eq_neg_of_add_eq_zero_left (by rw [← add_assoc, hlim, neg_add_cancel])

/-- Differentiating a constant bilinear product `B(f, g) = c` weakly on `Ω` for `f ∈ W^{1,p}_loc`
(`2 < p ≤ ∞`) and `g ∈ W^{1,q}_loc` (`1 ≤ q ≤ ∞`) gives `B (Df · v) g + B f (Dg · v) = 0` for
all `v ∈ ℂ` almost everywhere on `Ω`. -/
theorem HasWeakFDerivOn.ae_bilin_add_bilin_eq_zero_of_eq_const
    [FiniteDimensional ℝ F] [CompleteSpace H]
    (B : F →L[ℝ] G →L[ℝ] H) {p q : ℝ≥0∞} (hp : 2 < p) (hq : 1 ≤ q)
    {f : ℂ → F} {Df : ℂ → ℂ →L[ℝ] F} {g : ℂ → G} {Dg : ℂ → ℂ →L[ℝ] G} {c : H}
    (hf : MemWkpLoc p Ω 1 f) (hDf : HasWeakFDerivOn volume Ω f Df)
    (hg : MemWkpLoc q Ω 1 g) (hDg : HasWeakFDerivOn volume Ω g Dg)
    (hconst : ∀ᵐ z ∂volume.restrict Ω, B (f z) (g z) = c) :
    ∀ᵐ z ∂volume.restrict Ω, ∀ v : ℂ, B (Df z v) (g z) + B (f z) (Dg z v) = 0 := by
  have hprod := hDf.bilin B hp hq hf hg hDg
  have h0 : HasWeakFDerivOn volume Ω (fun _ : ℂ => c) 0 :=
    hasWeakFDerivOn_iff.2 fun u => by
      simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := u) c
  filter_upwards [(hprod.congr_ae hconst).ae_eq h0] with z hz v
  simpa using congr($hz v)

section Operator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p : ℝ≥0∞} {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- Differentiating `J ∘ J = c` weakly on `Ω` for a constant operator `c` gives
`(DJ · v) ∘ J + J ∘ (DJ · v) = 0` for all `v ∈ ℂ` almost everywhere on `Ω`, for all
`2 < p ≤ ∞`. -/
theorem HasWeakFDerivOn.ae_apply_add_apply_eq_zero_of_comp_self_eq_const
    {c : V →L[ℝ] V} (hDJ : HasWeakFDerivOn volume Ω J DJ) (hp : 2 < p) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = c) :
    ∀ᵐ z ∂volume.restrict Ω, ∀ (v : ℂ) (w : V), DJ z v (J z w) + J z (DJ z v w) = 0 := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  filter_upwards [hDJ.ae_bilin_add_bilin_eq_zero_of_eq_const (ContinuousLinearMap.compL ℝ V V V)
    hp (ENNReal.one_lt_two.trans hp).le hJ hJ hDJ hJsq] with z hz v w
  simpa using congr($(hz v) w)

end Operator

end TauCeti
