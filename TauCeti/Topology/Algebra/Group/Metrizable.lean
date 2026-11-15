/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Metrizability of topological groups with countably generated identity neighbourhoods

By the Birkhoff–Kakutani theorem, a topological group whose neighbourhood filter at the identity is
countably generated is pseudometrizable, and metrizable when it is `T₀` (hence Hausdorff).
Indeed, the right uniformity `IsTopologicalGroup.rightUniformSpace` induces the topology of `G` and
its uniformity filter `comap (fun p ↦ p.2 * p.1⁻¹) (𝓝 1)` is countably generated whenever `𝓝 1` is,
which directly witnesses `TopologicalSpace.PseudoMetrizableSpace`. Because `PseudoMetrizableSpace`
is defined in terms of a countably generated uniformity without mentioning real numbers, this
requires no metric or order imports.

In combination with Mathlib's Lindelöf-to-second-countable instance on pseudometrizable spaces,
every Lindelöf (in particular, σ-compact) topological group with countably generated identity
neighbourhoods is second countable.

As with `UniformSpace.metrizableSpace`, these declarations are theorems rather than global instances
in order to avoid a typeclass cycle with `PseudoMetrizableSpace.firstCountableTopology`.

## Main results

* `IsTopologicalGroup.pseudoMetrizableSpace` / `IsTopologicalAddGroup.pseudoMetrizableSpace`:
  a topological group with countably generated `𝓝 1` is pseudometrizable.
* `IsTopologicalGroup.metrizableSpace` / `IsTopologicalAddGroup.metrizableSpace`:
  a `T₀` topological group with countably generated `𝓝 1` is metrizable.
* `IsTopologicalGroup.secondCountableTopology` / `IsTopologicalAddGroup.secondCountableTopology`:
  a Lindelöf topological group with countably generated `𝓝 1` has second-countable topology.

## References

* G. Birkhoff, *A note on topological groups*, Compositio Math. **3** (1936), 427–430.
* S. Kakutani, *Über die Metrisation der topologischen Gruppen*, Proc. Imp. Acad. Tokyo **12**
  (1936), 82–84.
* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis*, Vol. I, 2nd ed., Springer (1979),
  Theorem 8.3.
-/

public section

open Filter TopologicalSpace
open scoped Topology Uniformity

/-- **Birkhoff–Kakutani theorem** (pseudometrizable form): a topological group whose identity has
a countably generated neighbourhood filter is pseudometrizable. -/
@[to_additive /-- **Birkhoff–Kakutani theorem** (pseudometrizable form): a topological additive
group whose zero has a countably generated neighbourhood filter is pseudometrizable. -/]
theorem IsTopologicalGroup.pseudoMetrizableSpace (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [(𝓝 (1 : G)).IsCountablyGenerated] :
    PseudoMetrizableSpace G := by
  let _ : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : (𝓤 G).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one']
    infer_instance
  infer_instance

/-- **Birkhoff–Kakutani theorem**: a `T₀` topological group whose identity has a countably
generated neighbourhood filter is metrizable. -/
@[to_additive /-- **Birkhoff–Kakutani theorem**: a `T₀` topological additive group whose zero has
a countably generated neighbourhood filter is metrizable. -/]
theorem IsTopologicalGroup.metrizableSpace (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T0Space G] [(𝓝 (1 : G)).IsCountablyGenerated] :
    MetrizableSpace G := by
  have : PseudoMetrizableSpace G := IsTopologicalGroup.pseudoMetrizableSpace G
  infer_instance

/-- A Lindelöf (in particular, σ-compact) topological group whose identity has a countably
generated neighbourhood filter is second countable. -/
@[to_additive /-- A Lindelöf (in particular, σ-compact) topological additive group whose zero has
a countably generated neighbourhood filter is second countable. -/]
theorem IsTopologicalGroup.secondCountableTopology (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LindelofSpace G] [(𝓝 (1 : G)).IsCountablyGenerated] :
    SecondCountableTopology G := by
  have : PseudoMetrizableSpace G := IsTopologicalGroup.pseudoMetrizableSpace G
  infer_instance

end
