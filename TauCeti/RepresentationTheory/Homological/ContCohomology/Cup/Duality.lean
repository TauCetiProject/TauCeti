/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.Topology.Algebra.GroupAction.InternalHom

/-!
# Evaluation cups for finite discrete modules

For a finite discrete `G`-module `M` and a discrete module `N`, evaluation is an equivariant
biadditive pairing from `InternalHom G M N` and `M` to `N`. The three low-degree cup shapes of
total degree two give pairings from `Hⁱ(G, InternalHom G M N)` and `H²⁻ⁱ(G, M)` to `H²(G, N)`.
These are the underlying cohomological pairings used in duality statements.

The cochain formulas below fix the order of the two inputs: the internal hom is always the first
factor, so in degree `(1,1)` the evaluation is `a(g) (g • b(h))`.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

omit [Finite M] in
/-- Evaluation on `H⁰(G, InternalHom G M N) × H²(G, M)`. -/
noncomputable def explicitDualityPairing02 :
    H0 G (InternalHom G M N) →+ H2 G M →+ H2 G N :=
  explicitCup02 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- Evaluation on `H¹(G, InternalHom G M N) × H¹(G, M)`. -/
noncomputable def explicitDualityPairing11 :
    H1 G (InternalHom G M N) →+ H1 G M →+ H2 G N :=
  explicitCup11 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- Evaluation on `H²(G, InternalHom G M N) × H⁰(G, M)`. -/
noncomputable def explicitDualityPairing20 :
    H2 G (InternalHom G M N) →+ H0 G M →+ H2 G N :=
  explicitCup20 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

omit [Finite M] in
/-- On cocycles, the `(0,2)` evaluation cup evaluates the invariant homomorphism pointwise. -/
@[simp]
theorem explicitDualityPairing02_mk (a : H0 G (InternalHom G M N)) (b : Z2 G M) :
    explicitDualityPairing02 G M N a (b : H2 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G (a : InternalHom G M N) ((b : G × G → M) q),
        cup02_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b.2⟩ :
        Z2 G N) : H2 G N) := by
  exact explicitCup02_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

/-- On cocycles, the `(1,1)` evaluation cup applies the first cocycle to the translate of the
second. -/
@[simp]
theorem explicitDualityPairing11_mk (a : Z1 G (InternalHom G M N)) (b : Z1 G M) :
    explicitDualityPairing11 G M N (a : H1 G (InternalHom G M N)) (b : H1 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G → InternalHom G M N) q.1)
          (q.1 • (b : G → M) q.2),
        cup11_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b.2⟩ :
        Z2 G N) : H2 G N) := by
  exact explicitCup11_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

/-- On cocycles, the `(2,0)` evaluation cup evaluates at an invariant element of `M`. -/
@[simp]
theorem explicitDualityPairing20_mk (a : Z2 G (InternalHom G M N)) (b : H0 G M) :
    explicitDualityPairing20 G M N (a : H2 G (InternalHom G M N)) b =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G × G → InternalHom G M N) q)
          ((q.1 * q.2) • (b : M)),
        cup20_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b⟩ :
        Z2 G N) : H2 G N) := by
  exact explicitCup20_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end TauCeti.ContCohomology
