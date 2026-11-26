/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.Mixed.Leibniz
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

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

These are the case `E = ℂ` of the results for `TauCeti.MemLpLoc` on domains in a
finite-dimensional real inner product space `E` with `dim E < p`, in
`TauCeti.Analysis.Sobolev.W1p.Mixed.Leibniz`; the weak Leibniz rule for the order-one product is
`TauCeti.HasWeakFDerivOn.bilin_of_finrank_lt` there.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_of_holderTriple`: the local gain of integrability.
* `TauCeti.MemLpLoc.bilin_of_memWkpLoc`: order-zero membership.
* `TauCeti.MemWkpLoc.bilin_of_memLpLoc_top` and `TauCeti.MemWkpLoc.bilin`: order-one membership.

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

/-- **Local gain of integrability.** For `p > 2` and `1 ≤ q ≤ p`, a map in `W^{1,q}_loc` with
finite-dimensional values is in `Lʳ_loc` for `1/p + 1/r = 1/q`. At `q = p` this is `r = ∞`. -/
theorem MemWkpLoc.memLpLoc_of_holderTriple (hp : 2 < p) (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))]
    {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : ℂ → G} (hg : MemWkpLoc q Ω 1 g) :
    MemLpLoc r Ω g := by
  obtain ⟨Dg, hDg, hDq⟩ := hg.exists_weakFDeriv_of_isOpen
  exact hDg.memLpLoc_of_holderTriple (by simpa using hp) hqp hg.memLpLoc
    (memWkpLoc_zero_iff.1 hDq)

/-- **Order-zero mixed products.** For `p > 2` and `1 ≤ q ≤ p`, the product of a locally `Lᵖ`
map with a `W^{1,q}_loc` map with finite-dimensional values is locally `L^q`. -/
theorem MemLpLoc.bilin_of_memWkpLoc (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {f : ℂ → F} {g : ℂ → G} (hf : MemLpLoc p Ω f)
    (hg : MemWkpLoc q Ω 1 g) : MemLpLoc q Ω (fun z => B (f z) (g z)) := by
  obtain ⟨Dg, hDg, hDq⟩ := hg.exists_weakFDeriv_of_isOpen
  exact hf.bilin_of_hasWeakFDerivOn B (by simpa using hp) hqp hDg hg.memLpLoc
    (memWkpLoc_zero_iff.1 hDq)

/-- **Order-one mixed products.** For `p > 2` and `1 < q ≤ p`, the product of a locally bounded
`W^{1,p}_loc` map with a `W^{1,q}_loc` map with finite-dimensional values is in
`W^{1,q}_loc`. At `q = p` this is the algebra property of `W^{1,p}_loc` under continuous bilinear
maps. -/
theorem MemWkpLoc.bilin_of_memLpLoc_top [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f)
    (hfi : MemLpLoc ∞ Ω f) (hg : MemWkpLoc q Ω 1 g) :
    MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  have hp' : (finrank ℝ ℂ : ℝ≥0) < p := by simpa using hp
  obtain ⟨Df, hDf, hDfp⟩ := hf.exists_weakFDeriv_of_isOpen
  obtain ⟨Dg, hDg, hDgq⟩ := hg.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDfp hDgq
  obtain ⟨h0, h1⟩ := hDg.memLpLoc_bilin_of_memLpLoc_top B hp' hq.le hqp hfi hDfp hg.memLpLoc hDgq
  exact memWkpLoc_succ_iff_of_isOpen.2 ⟨h0, _, hDf.bilin_of_finrank_lt B hp' hq hqp
    (hfi.mono_exponent le_top) hDfp hDg hg.memLpLoc hDgq, memWkpLoc_zero_iff.2 h1⟩

/-- **Order-one mixed products with finite-dimensional factors.** For `p > 2` and
`1 < q ≤ p`, the product of a `W^{1,p}_loc` map with a `W^{1,q}_loc` map, both with
finite-dimensional values, is in `W^{1,q}_loc`. The first factor is locally bounded by the local
gain of integrability at `q = p`. -/
theorem MemWkpLoc.bilin [FiniteDimensional ℝ F] [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω 1 f)
    (hg : MemWkpLoc q Ω 1 g) : MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  exact hf.bilin_of_memLpLoc_top B hp hq hqp (hf.memLpLoc_of_holderTriple hp le_rfl) hg

end TauCeti
