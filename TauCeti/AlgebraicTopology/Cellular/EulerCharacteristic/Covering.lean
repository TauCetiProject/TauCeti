/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Covering
import TauCeti.Topology.CWComplex.Comparison
import TauCeti.Topology.Covering.Pullback

/-!
# Multiplicativity of the Euler characteristic for finite covers

Let `p : E → B` be a covering map with finite fibres and let `C` be a finite CW complex in `B`.
Lifting the characteristic maps of `C` through `p` makes `p ⁻¹' C` a finite CW complex whose
`n`-cells are the pairs of an `n`-cell of `C` and a point over its centre
(`TauCeti.cwComplexPreimage`). When every fibre over `C` has `d` points, `p ⁻¹' C` therefore has
`d` times as many cells as `C` in every dimension, and its Euler characteristic is `d` times that
of `C`:

```text
χ(p⁻¹(C)) = d · χ(C).
```

Over a disconnected base the number of sheets need not be constant; the cell count
`TauCeti.nat_card_cell_preimage` is stated cellwise, through the number of points over the centre
of each cell, and the alternating count of cells of `p ⁻¹' C` is the corresponding alternating sum
(`TauCeti.cwEulerChar_preimage`).

The base of a finite cover need not carry a CW structure: when `B` only has finite CW type, the
cover pulls back along a homotopy equivalence with a finite CW complex to a `d`-sheeted cover of
that complex, and the total space of the pullback is homotopy equivalent to `E`
(`IsCoveringMap.pullbackHomotopyEquiv`). Hence `χ(E) = d · χ(B)` for every `d`-sheeted cover of a
space of finite CW type.

## Main results

* `TauCeti.cwEulerChar_preimage`: the alternating count of the cells of the lifted complex, summed
  cell by cell over the fibres of the centres.
* `TauCeti.cwEulerChar_preimage_of_card_fiber`: `χ(p⁻¹(C)) = d · χ(C)` for the alternating cell
  counts, when every fibre over `C` has `d` points.
* `TauCeti.eulerChar_preimage_of_card_fiber`: the same for the Euler characteristics of the spaces.
* `TauCeti.eulerChar_eq_mul_of_isCoveringMap`: **finite-cover multiplicativity**, `χ(E) = d · χ(B)`
  for a `d`-sheeted cover of a space `B` of finite CW type.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44, and the exercise of that section on
  the Euler characteristic of an `n`-sheeted covering space.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section CWComplex

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] [T2Space B] {p : E → B}
  (C : Set B) [CWComplex C] [RelCWComplex.Finite C]
  (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))

include hp hfin

/-- The alternating count of the cells of the lift of `C` along `p` is the alternating sum, over the
cells of `C`, of the number of points over their centres. -/
theorem cwEulerChar_preimage :
    letI := cwComplexPreimage C hp
    cwEulerChar (p ⁻¹' C) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ∑ᶠ i : cell C n, (Nat.card ↥(p ⁻¹' {map n i 0}) : ℤ) := by
  let := cwComplexPreimage C hp
  rw [cwEulerChar_def]
  refine finsum_congr fun n ↦ ?_
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  rw [nat_card_cell_preimage C hp hfin, Nat.cast_finsum]

/-- **The cells of a `d`-sheeted cover.** If every fibre of `p` over `C` has `d` points, the
alternating count of the cells of the lift of `C` along `p` is `d` times that of `C`. -/
theorem cwEulerChar_preimage_of_card_fiber {d : ℕ} (hd : ∀ b ∈ C, Nat.card ↥(p ⁻¹' {b}) = d) :
    letI := cwComplexPreimage C hp
    cwEulerChar (p ⁻¹' C) = d * cwEulerChar C := by
  let := cwComplexPreimage C hp
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅))
  have hN' (n : ℕ) (hn : N ≤ n) : IsEmpty (cell (p ⁻¹' C) n) :=
    (cellPreimageEquiv C hp n).isEmpty_congr.2 ⟨fun c ↦ (hN n hn).false c.1⟩
  rw [cwEulerChar_eq_sum_range _ hN', cwEulerChar_eq_sum_range _ hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [nat_card_cell_preimage_of_card_fiber C hp hfin hd, Nat.cast_mul]
  ring

/-- If every fibre of `p` over the finite CW complex `C` has `d` points, then
`χ(p⁻¹(C)) = d · χ(C)`. -/
theorem eulerChar_preimage_of_card_fiber {d : ℕ} (hd : ∀ b ∈ C, Nat.card ↥(p ⁻¹' {b}) = d) :
    letI := cwComplexPreimage C hp
    haveI := finite_cwComplexPreimage C hp hfin
    haveI := hp.t2Space
    eulerChar ↥(p ⁻¹' C) = d * eulerChar ↥C := by
  let := cwComplexPreimage C hp
  have := finite_cwComplexPreimage C hp hfin
  have := hp.t2Space
  rw [eulerChar_cwComplex, eulerChar_cwComplex, cwEulerChar_preimage_of_card_fiber C hp hfin hd]

/-- Finite-cover multiplicativity over a finite CW complex, the case of
`eulerChar_eq_mul_of_isCoveringMap` with a CW structure on the base itself. -/
private theorem eulerChar_eq_mul_of_isCoveringMap_of_cwComplex [CWComplex (univ : Set B)]
    [RelCWComplex.Finite (univ : Set B)] [FiniteCWType B] {d : ℕ}
    (hd : ∀ b, Nat.card ↥(p ⁻¹' {b}) = d) :
    haveI := hp.finiteCWType hfin
    eulerChar E = d * eulerChar B := by
  have := hp.finiteCWType hfin
  let := cwComplexPreimage univ hp
  have := finite_cwComplexPreimage univ hp hfin
  have := hp.t2Space
  have h := eulerChar_preimage_of_card_fiber univ hp hfin fun b _ ↦ hd b
  rwa [(Homeomorph.Set.univ B).symm.eulerChar_eq,
    ((Homeomorph.setCongr (preimage_univ (f := p))).trans
      (Homeomorph.Set.univ E)).eulerChar_eq.symm]

end CWComplex

section FiniteCWType

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))

include hp hfin

/-- **Finite-cover multiplicativity of the Euler characteristic.** If `B` has finite CW type and
`p : E → B` is a covering map all of whose fibres have `d` points, then `χ(E) = d · χ(B)`.
The space `E` has finite CW type by `IsCoveringMap.finiteCWType`, which the statement installs. -/
theorem eulerChar_eq_mul_of_isCoveringMap [FiniteCWType B] {d : ℕ}
    (hd : ∀ b, Nat.card ↥(p ⁻¹' {b}) = d) :
    haveI := hp.finiteCWType hfin
    eulerChar E = d * eulerChar B := by
  have := hp.finiteCWType hfin
  obtain ⟨Z, _, _, _, _, ⟨e⟩⟩ := FiniteCWType.exists_homotopyEquiv_univ B
  have := e.symm.finiteCWType
  have hq := hp.pullback_fst e.symm.toFun.continuous
  have hqfin (z : Z) :
      Finite ↥((Function.Pullback.fst : Function.Pullback e.symm p → Z) ⁻¹' {z}) :=
    .of_equiv _ (Function.Pullback.fstPreimageEquiv z).symm
  have h := eulerChar_eq_mul_of_isCoveringMap_of_cwComplex hq hqfin fun z ↦
    (Nat.card_congr (Function.Pullback.fstPreimageEquiv z)).trans (hd _)
  have := hq.finiteCWType hqfin
  rw [← (hp.pullbackHomotopyEquiv e.symm).eulerChar_eq, h, e.eulerChar_eq]

end FiniteCWType

end TauCeti
