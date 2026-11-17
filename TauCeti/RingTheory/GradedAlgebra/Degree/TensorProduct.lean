/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Decomposition
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.GradedAlgebra.Degree.Filtration

/-!
# Total-degree tensor filtrations of nonnegatively graded algebras

For two nonnegatively graded `R`-algebras `A` and `B`, the total-degree tensor filtration
`AlgFiltration.tensorProduct` of their `GradedAlgebra.degreeFiltration`s agrees with the bidegree
`DirectSum.degreeTail` associated to the internal tensor decomposition `A i ⊗ B j` of `A ⊗[R] B`.
Consequently, a tensor lies in filtration order `k` precisely when all of its bidegree projections
`TensorProduct.map (GradedAlgebra.proj 𝒜 i) (GradedAlgebra.proj ℬ j)` of total degree below `k`
vanish. The underlying module-level bidegree decomposition API lives in
`TauCeti.LinearAlgebra.TensorProduct.Decomposition`. No flatness, freeness, or commutativity of `A`
or `B` is assumed.

## Main results

* `TauCeti.GradedAlgebra.tensorProduct_degreeFiltration_ideal_restrictScalars`: restricting scalars
  on the total-degree tensor ideal recovers the bidegree `DirectSum.degreeTail`.
* `TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff`: membership in the
  total-degree tensor ideal is the vanishing of all bidegree projections below the cutoff.
-/

public section

open scoped TensorProduct

namespace TauCeti.GradedAlgebra

variable {R A B ι κ : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [AddMonoid ι] [AddMonoid κ] [DecidableEq ι] [DecidableEq κ]
  (𝒜 : ι → Submodule R A) (ℬ : κ → Submodule R B)
  [_root_.GradedAlgebra 𝒜] [_root_.GradedAlgebra ℬ]
  (dA : ι →+ ℤ) (hnegA : ∀ i, dA i < 0 → 𝒜 i = ⊥)
  (dB : κ →+ ℤ) (hnegB : ∀ j, dB j < 0 → ℬ j = ⊥)

/-- Restricting scalars on the total-degree tensor ideal of two degree filtrations recovers the
bidegree `DirectSum.degreeTail`. -/
theorem tensorProduct_degreeFiltration_ideal_restrictScalars (k : ℕ) :
    (((degreeFiltration 𝒜 dA hnegA).tensorProduct R
        (degreeFiltration ℬ dB hnegB)).ideal k).restrictScalars R =
      TauCeti.DirectSum.degreeTail
        (fun p : ι × κ => Submodule.map₂ (TensorProduct.mk R A B) (𝒜 p.1) (ℬ p.2))
        (fun p => dA p.1 + dB p.2) k := by
  ext t
  simp only [Submodule.restrictScalars_mem, AlgFiltration.mem_tensorProduct_ideal_iff,
    degreeFiltration_ideal, degreeIdeal_restrictScalars,
    TauCeti.DirectSum.tensorFiltrationTail_degreeTail_eq 𝒜 dA hnegA ℬ dB hnegB k]

/-- Membership in the total-degree tensor ideal of two degree filtrations is the vanishing of all
bidegree projections of total degree below `k`. -/
theorem mem_tensorProduct_degreeFiltration_ideal_iff {k : ℕ} {t : A ⊗[R] B} :
    t ∈ ((degreeFiltration 𝒜 dA hnegA).tensorProduct R
        (degreeFiltration ℬ dB hnegB)).ideal k ↔
    ∀ i j, dA i + dB j < k →
      TensorProduct.map (_root_.GradedAlgebra.proj 𝒜 i) (_root_.GradedAlgebra.proj ℬ j) t = 0 := by
  let _ := TauCeti.tensorProductDecomposition 𝒜 ℬ
  rw [← Submodule.restrictScalars_mem R,
    tensorProduct_degreeFiltration_ideal_restrictScalars 𝒜 ℬ dA hnegA dB hnegB k,
    TauCeti.DirectSum.mem_degreeTail_iff]
  simp only [Prod.forall, proj_eq_homogeneousComponent, TauCeti.coe_decompose_tensorProduct]

end TauCeti.GradedAlgebra
