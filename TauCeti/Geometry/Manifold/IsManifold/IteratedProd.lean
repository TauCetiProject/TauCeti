/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Prod

/-!
# Iterated products of a manifold

For a type `M` and `n : ℕ`, `TauCeti.IteratedProd M n` is the product of `n + 1` copies of `M`,
nested to the left: `IteratedProd M 0 = M` and `IteratedProd M (n + 1) = IteratedProd M n × M`.
For instance the torus `Tⁿ⁺¹` is `IteratedProd S¹ n`.

When `M` is a manifold modelled on a normed space `E` with the model `𝓘(𝕜, E)`, its iterated
products are manifolds modelled on the iterated products of `E`, with the model
`𝓘(𝕜, IteratedProdModel E n)`: at each step the charts are the product charts with values in the
normed space `IteratedProdModel E n × E` (`TauCeti.chartedSpaceProd`), which form a `C^k` atlas
(`TauCeti.isManifold_chartedSpaceProd`). These are the charts in which constructions stated for a
binary product `M × N` with the model `𝓘(𝕜, E × E')`, such as the Morse complex of a separated sum,
apply to each step of the iteration.

The model space is a separate type `TauCeti.IteratedProdModel E n`, with the same underlying type
as `IteratedProd E n`: it carries the product norm and the normed space structure, while
`IteratedProd M n` carries only the product topology. Using one type for both would give a normed
space `E` two topologies on `IteratedProd E n`, the product topology and that of the product norm,
which agree but not by definition when `n` is a variable.

## Main definitions

* `TauCeti.IteratedProd M n`: the product of `n + 1` copies of `M`.
* `TauCeti.IteratedProdModel E n`: the product of `n + 1` copies of a normed space `E`, as a normed
  space.

## Main results

* `TauCeti.IteratedProd.instChartedSpace` and `TauCeti.IteratedProd.instIsManifold`: the iterated
  products of a `C^k` manifold modelled on `E` form a `C^k` manifold modelled on
  `IteratedProdModel E n`.
* `TauCeti.IteratedProd.instCompactSpace` and `TauCeti.IteratedProd.instT2Space`: the iterated
  products of a compact Hausdorff space are compact Hausdorff spaces.
-/

public section

open scoped Manifold

namespace TauCeti

universe u

/-- The product of `n + 1` copies of a type `M`, nested to the left:
`M × ⋯ × M = (⋯ (M × M) × ⋯) × M`. -/
@[expose]
def IteratedProd (M : Type u) : ℕ → Type u
  | 0 => M
  | n + 1 => IteratedProd M n × M

/-- The product of `n + 1` copies of a normed space `E`, nested to the left, with the product norm:
the model space of the iterated products `TauCeti.IteratedProd M n` of a manifold `M` modelled on
`E`. -/
@[expose]
def IteratedProdModel (E : Type u) : ℕ → Type u
  | 0 => E
  | n + 1 => IteratedProdModel E n × E

/-! ### The model space -/

namespace IteratedProdModel

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The product norm on the iterated product of a normed group. -/
noncomputable instance instNormedAddCommGroup : (n : ℕ) → NormedAddCommGroup (IteratedProdModel E n)
  | 0 => inferInstanceAs (NormedAddCommGroup E)
  | n + 1 => letI := instNormedAddCommGroup n
      inferInstanceAs (NormedAddCommGroup (IteratedProdModel E n × E))

/-- The iterated product of a normed space is a normed space. -/
noncomputable instance instNormedSpace : (n : ℕ) → NormedSpace 𝕜 (IteratedProdModel E n)
  | 0 => inferInstanceAs (NormedSpace 𝕜 E)
  | n + 1 => letI := instNormedSpace n
      inferInstanceAs (NormedSpace 𝕜 (IteratedProdModel E n × E))

/-- The iterated product of a finite-dimensional space is finite-dimensional. -/
instance instFiniteDimensional [FiniteDimensional 𝕜 E] :
    (n : ℕ) → FiniteDimensional 𝕜 (IteratedProdModel E n)
  | 0 => inferInstanceAs (FiniteDimensional 𝕜 E)
  | n + 1 => letI := instFiniteDimensional n
      inferInstanceAs (FiniteDimensional 𝕜 (IteratedProdModel E n × E))

end IteratedProdModel

/-! ### The iterated products of a manifold -/

namespace IteratedProd

variable {M : Type*} [TopologicalSpace M]

/-- The product topology on an iterated product. -/
instance instTopologicalSpace : (n : ℕ) → TopologicalSpace (IteratedProd M n)
  | 0 => inferInstanceAs (TopologicalSpace M)
  | n + 1 => letI := instTopologicalSpace n
      inferInstanceAs (TopologicalSpace (IteratedProd M n × M))

/-- The iterated products of a compact space are compact. -/
instance instCompactSpace [CompactSpace M] : (n : ℕ) → CompactSpace (IteratedProd M n)
  | 0 => inferInstanceAs (CompactSpace M)
  | n + 1 => letI := instCompactSpace n
      inferInstanceAs (CompactSpace (IteratedProd M n × M))

/-- The iterated products of a Hausdorff space are Hausdorff. -/
instance instT2Space [T2Space M] : (n : ℕ) → T2Space (IteratedProd M n)
  | 0 => inferInstanceAs (T2Space M)
  | n + 1 => letI := instT2Space n
      inferInstanceAs (T2Space (IteratedProd M n × M))

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [ChartedSpace E M]

/-- The charts of an iterated product: at each step, the product charts with values in the normed
space `IteratedProdModel E n × E` (`TauCeti.chartedSpaceProd`). -/
noncomputable instance instChartedSpace :
    (n : ℕ) → ChartedSpace (IteratedProdModel E n) (IteratedProd M n)
  | 0 => inferInstanceAs (ChartedSpace E M)
  | n + 1 => letI := instChartedSpace n
      chartedSpaceProd (IteratedProdModel E n) E (IteratedProd M n) M

/-- The iterated products of a `C^k` manifold modelled on `E` are `C^k` manifolds modelled on the
iterated products of `E`. -/
instance instIsManifold {k : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) k M] :
    (n : ℕ) → IsManifold 𝓘(𝕜, IteratedProdModel E n) k (IteratedProd M n)
  | 0 => inferInstanceAs (IsManifold 𝓘(𝕜, E) k M)
  | n + 1 => letI : IsManifold 𝓘(𝕜, IteratedProdModel E n) k (IteratedProd M n) :=
        instIsManifold n
      isManifold_chartedSpaceProd (E := IteratedProdModel E n) (E' := E) (M := IteratedProd M n)
        (N := M)

end IteratedProd

end TauCeti
