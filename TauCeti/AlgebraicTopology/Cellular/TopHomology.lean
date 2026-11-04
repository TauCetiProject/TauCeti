/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Basic
public import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Freeness of cellular homology in a degree without cells above it

Let `(C, D)` be a relative CW complex with no `(n + 1)`-cells, and let `M` be a free module over
a principal ideal ring `k` without zero divisors, such as `ℤ`. The cellular chain complex then
vanishes in degree `n + 1`, so its homology in degree `n` is the module of `n`-cycles, the kernel of
the cellular differential on the free module of `n`-chains. Every submodule of a free module over
such a ring is free, with no restriction on the rank (`Submodule.free_of_isPrincipalIdealRing`), so
`Hₙ(C, D; M)` is free (`TauCeti.free_singularHomology_complexBasePair_of_isEmpty_cell`). The
number of cells is arbitrary, in particular it may be countably infinite.

In particular the top relative homology of a CW pair of dimension at most `n` is free. With
integral coefficients this says that `Hₙ(C, D; ℤ)` is free abelian. It does not make the degree
`n` integral cohomology torsion-free: by the universal coefficient theorem that cohomology also
contains `Ext(Hₙ₋₁(C, D; ℤ), ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34 and cellular homology.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {k : Type w} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (M : ModuleCat.{w} k)
  [Module.Free k M]

/-- **Cellular homology below an empty degree is free.** If a relative CW complex has no
`(n + 1)`-cells, its cellular homology in degree `n`, with coefficients in a free module over a
principal ideal ring without zero divisors, is free. -/
theorem free_cellularHomology_of_isEmpty_cell (n : ℕ) [IsEmpty (cell C (n + 1))] :
    Module.Free k ((cellularChainComplex C M).homology n : ModuleCat k) := by
  set K := cellularChainComplex C M
  -- There are no `(n + 1)`-chains, so the homology in degree `n` is the module of `n`-cycles.
  have hd : K.d (n + 1) n = 0 := by
    refine IsZero.eq_of_src ?_ _ _
    rw [cellularChainComplex_X]
    exact isZero_cellularChainGroup C (n + 1) M
  have : Module.Free k (K.X n : ModuleCat k) := by
    rw [cellularChainComplex_X]
    infer_instance
  -- The cycles are a submodule of the free module of `n`-chains.
  have := Module.Free.of_injective_of_projective_of_isPrincipalIdealRing (K.iCycles n).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact .of_equiv (K.isoHomologyπ (n + 1) n (by simp) hd).toLinearEquiv

/-- **Relative homology below an empty degree is free.** If a relative CW complex `(C, D)` has no
`(n + 1)`-cells, then `Hₙ(C, D; M)` is free for every free module `M` over a principal ideal ring
without zero divisors. In particular the top relative homology of a CW pair of dimension at most
`n` is free. -/
theorem free_singularHomology_complexBasePair_of_isEmpty_cell (n : ℕ)
    [IsEmpty (cell C (n + 1))] :
    Module.Free k ((complexBasePair C).singularHomology M n : ModuleCat k) :=
  have := free_cellularHomology_of_isEmpty_cell C M n
  .of_equiv (cellularSingularHomologyIso C M n).toLinearEquiv

end TauCeti
