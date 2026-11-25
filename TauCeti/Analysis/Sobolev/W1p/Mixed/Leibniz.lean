/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Mixed.Multiplication
public import TauCeti.MeasureTheory.Function.MemLpLoc
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Data.ENNReal.Holder

/-!
# The weak Leibniz rule for mixed-exponent products on Euclidean domains

Let `Ω` be an open subset of a real inner product space `E` of finite dimension `n`, let
`n < p < ∞`, `1 ≤ q ≤ p`, and let `B : F × G → H` be continuous bilinear with `G`
finite-dimensional. This file proves the first two orders of the mixed-exponent product theorem
for functions that are locally integrable on `Ω`, in the sense of `TauCeti.MemLpLoc`, together
with their weak derivatives. Throughout, `g, Dg ∈ L^q_loc(Ω)`, where `Dg` is a weak derivative
of `g`.

* Order zero: for `f ∈ Lᵖ_loc(Ω)`, the product `B(f, g)` is in `L^q_loc(Ω)`.
* Order one, the Leibniz rule: for `1 < q` and `f ∈ L^{q'}_loc(Ω)` with weak derivative
  `Df ∈ Lᵖ_loc(Ω)`, where `q'` is the conjugate exponent of `q`, the product `B(f, g)` has weak
  derivative `B(Df, g) + B(f, Dg)`.
* Order one, membership: for `f ∈ L^∞_loc(Ω)` and `Df ∈ Lᵖ_loc(Ω)`, both `B(f, g)` and
  `B(Df, g) + B(f, Dg)` are in `L^q_loc(Ω)`. When `F` is finite-dimensional and `f, Df ∈ Lᵖ_loc(Ω)`
  with `Df` a weak derivative of `f`, the factor `f` is locally bounded by the gain of
  integrability below at `q = p`.

The input is the local gain of integrability `W^{1,q}_loc ⊆ Lʳ_loc` for `1/p + 1/r = 1/q`
(`TauCeti.HasWeakFDerivOn.memLpLoc_of_holderTriple`), which uses `p > n` and is the local form of
`TauCeti.W1p.exists_eLpNorm_le_of_holderTriple`. At `q = p` it gives `r = ∞`: a `W^{1,p}_loc`
map with finite-dimensional values is locally bounded. The Leibniz rule itself is
`TauCeti.HasWeakFDerivOn.bilin_of_memLp`, applied at exponents supplied by this gain.

For planar domains, `TauCeti.Analysis.Sobolev.Local.Multiplication` restates these results
for the local Sobolev classes `TauCeti.MemWkpLoc` (`TauCeti.MemLpLoc.bilin_of_memWkpLoc` and
`TauCeti.MemWkpLoc.bilin`), with their higher-order consequences in
`TauCeti.Analysis.Sobolev.Local.Multiplication.Higher`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.memLpLoc_of_holderTriple`: the local gain of integrability.
* `TauCeti.MemLpLoc.bilin_of_hasWeakFDerivOn`: order-zero mixed products.
* `TauCeti.HasWeakFDerivOn.bilin_of_finrank_lt`: the weak Leibniz rule for order-one mixed
  products.
* `TauCeti.HasWeakFDerivOn.memLpLoc_bilin_of_memLpLoc_top`: order-one membership of the product
  and of its candidate weak derivative, for a locally bounded factor.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Module
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {p q : ℝ≥0}

/-- **Local gain of integrability.** For `dim E < p` and `1 ≤ q ≤ p`, a weakly differentiable
map on `Ω` with finite-dimensional values which, with its weak derivative, is locally `L^q` on
`Ω` is locally `Lʳ` on `Ω` for `1/p + 1/r = 1/q`. At `q = p` this is `r = ∞`. -/
theorem HasWeakFDerivOn.memLpLoc_of_holderTriple (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : E → G}
    {Dg : E → E →L[ℝ] G} (hg : HasWeakFDerivOn μ Ω g Dg) (hgq : MemLpLoc q Ω g μ)
    (hDg : MemLpLoc q Ω Dg μ) : MemLpLoc r Ω g μ := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_le_of_holderTriple (μ := μ) (Ω := ⟨W, hWo⟩)
    (G := G) (r := r) hp hqp hK hKW
  have hgW := hgq.memLp_restrict_of_isCompact_closure hWc hWΩ
  have hDW := hDg.memLp_restrict_of_isCompact_closure hWc hWΩ
  exact (hC g Dg (hg.mono (subset_closure.trans hWΩ)) hgW hDW).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.add_lt_top.2 ⟨hgW.eLpNorm_lt_top, hDW.eLpNorm_lt_top⟩))

/-- **Order-zero mixed products.** For `dim E < p` and `1 ≤ q ≤ p`, the product of a locally
`Lᵖ` map with a weakly differentiable map with finite-dimensional values which, with its weak
derivative, is locally `L^q` is locally `L^q`. -/
theorem MemLpLoc.bilin_of_hasWeakFDerivOn (B : F →L[ℝ] G →L[ℝ] H)
    (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))] {f : E → F}
    {g : E → G} {Dg : E → E →L[ℝ] G} (hf : MemLpLoc p Ω f μ)
    (hg : HasWeakFDerivOn μ Ω g Dg) (hgq : MemLpLoc q Ω g μ) (hDg : MemLpLoc q Ω Dg μ) :
    MemLpLoc q Ω (fun x => B (f x) (g x)) μ := by
  let _ := ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q) (by exact_mod_cast hqp)
  have hgr : MemLpLoc ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹ Ω g μ :=
    hg.memLpLoc_of_holderTriple hp hqp hgq hDg
  exact memLpLoc_iff.2 fun K hKΩ hK =>
    B.memLp_of_bilin q (memLpLoc_iff.1 hf K hKΩ hK) (memLpLoc_iff.1 hgr K hKΩ hK)

/-- **The weak Leibniz rule for order-one mixed products.** For `dim E < p` and `1 < q ≤ p`, let
`f ∈ L^{q'}_loc(Ω)`, where `q'` is the conjugate exponent of `q`, have weak derivative
`Df ∈ Lᵖ_loc(Ω)`, and let `g ∈ L^q_loc(Ω)` with finite-dimensional values have weak derivative
`Dg ∈ L^q_loc(Ω)`. Then `B(f, g)` has weak derivative `B(Df, g) + B(f, Dg)` on `Ω`. -/
theorem HasWeakFDerivOn.bilin_of_finrank_lt [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : (finrank ℝ E : ℝ≥0) < p) (hq : 1 < q) (hqp : q ≤ p) {f : E → F}
    {Df : E → E →L[ℝ] F} {g : E → G} {Dg : E → E →L[ℝ] G} (hf : HasWeakFDerivOn μ Ω f Df)
    (hfi : MemLpLoc (q : ℝ≥0∞).conjExponent Ω f μ) (hDf : MemLpLoc p Ω Df μ)
    (hg : HasWeakFDerivOn μ Ω g Dg) (hgq : MemLpLoc q Ω g μ) (hDg : MemLpLoc q Ω Dg μ) :
    HasWeakFDerivOn μ Ω (fun x => B (f x) (g x))
      (fun x => B.precompL E (Df x) (g x) + B.precompR E (f x) (Dg x)) := by
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
  have hgr : MemLpLoc r Ω g μ := hg.memLpLoc_of_holderTriple hp hqp hgq hDg
  have hbr : b ≤ r := by
    refine max_le (ENNReal.inv_le_inv.1 ?_) (ENNReal.inv_le_inv.1 ?_)
    · rw [inv_inv]
      exact tsub_le_self
    · rw [inv_inv, ← ENNReal.HolderConjugate.one_sub_inv (p : ℝ≥0∞) p']
      exact tsub_le_tsub_right (ENNReal.inv_le_one.2 hq1.le) _
  have hgb : MemLpLoc b Ω g μ := hgr.mono_exponent hbr
  exact hf.bilin_of_memLp B ha ENNReal.coe_ne_top hb ENNReal.coe_ne_top
    ((add_le_add le_rfl hbq).trans haq.le) ((add_le_add le_rfl hbp).trans hpp.le) haq.le hg
    (fun K hK hKΩ => memLpLoc_iff.1 hfi K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDf K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hgb K hKΩ hK) (fun K hK hKΩ => memLpLoc_iff.1 hDg K hKΩ hK)

/-- **Order-one mixed products with a locally bounded factor.** For `dim E < p` and
`1 ≤ q ≤ p`, let `f ∈ L^∞_loc(Ω)`, let `Df ∈ Lᵖ_loc(Ω)`, and let `g` with finite-dimensional
values have weak derivative `Dg` on `Ω` with `g, Dg ∈ L^q_loc(Ω)`. Then the product `B(f, g)`
and the candidate weak derivative `B(Df, g) + B(f, Dg)` are in `L^q_loc(Ω)`. When `Df` is a weak
derivative of `f` and `1 < q`, `TauCeti.HasWeakFDerivOn.bilin_of_finrank_lt` shows that the
second function is the weak derivative of the first. -/
theorem HasWeakFDerivOn.memLpLoc_bilin_of_memLpLoc_top (B : F →L[ℝ] G →L[ℝ] H)
    (hp : (finrank ℝ E : ℝ≥0) < p) (hq : 1 ≤ q) (hqp : q ≤ p) {f : E → F}
    {Df : E → E →L[ℝ] F} {g : E → G} {Dg : E → E →L[ℝ] G} (hfi : MemLpLoc ∞ Ω f μ)
    (hDf : MemLpLoc p Ω Df μ) (hg : HasWeakFDerivOn μ Ω g Dg) (hgq : MemLpLoc q Ω g μ)
    (hDg : MemLpLoc q Ω Dg μ) :
    MemLpLoc q Ω (fun x => B (f x) (g x)) μ ∧
      MemLpLoc q Ω (fun x => B.precompL E (Df x) (g x) + B.precompR E (f x) (Dg x)) μ := by
  let _ : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  refine ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, memLpLoc_iff.2 fun K hKΩ hK => ?_⟩
  · exact B.memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK) (memLpLoc_iff.1 hgq K hKΩ hK)
  · exact (memLpLoc_iff.1 (hDf.bilin_of_hasWeakFDerivOn (B.precompL E) hp hqp hg hgq hDg) K
      hKΩ hK).add ((B.precompR E).memLp_of_bilin q (memLpLoc_iff.1 hfi K hKΩ hK)
        (memLpLoc_iff.1 hDg K hKΩ hK))

end TauCeti
