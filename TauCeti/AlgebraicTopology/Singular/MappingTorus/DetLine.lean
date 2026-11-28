/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.LinearAlgebra.Determinant.Exact

/-!
# The determinant line of the homology of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus, and write `A = 𝟙 - φ_*` for the
Wang endomorphism of the homology of the fibre with coefficients in a field `k`. For every
monodromy the Wang sequence breaks into the short exact sequences
(`TauCeti.MappingTorus.wangKernelShortComplex_shortExact`)

`0 ⟶ Hₙ₊₁(F) ⧸ range A ⟶ Hₙ₊₁(T_φ) ⟶ ker A ⟶ 0`,

with `A` acting on `Hₙ₊₁(F)` in the first term and on `Hₙ(F)` in the last; the first map is
induced by the fibre inclusion and the second is the Wang connecting morphism. When the homology
of the fibre is finite-dimensional in degrees `n` and `n + 1`, this identifies determinant lines
(`TauCeti.MappingTorus.wangDetLineEquiv`):

`det (Hₙ₊₁(F) ⧸ range A) ⊗ det (ker A) ≃ det Hₙ₊₁(T_φ)`.

No complement of `ker A` or of `range A` is chosen, and `A` need not be invertible: when `φ_*` has
eigenvalue one, `ker A` is the `1`-eigenspace of `φ_*` and the cokernel of `A` has the same
dimension, and both keep their full determinant lines. The isomorphism sends
`(ι₁ ∧ ⋯ ∧ ιₐ) ⊗ (δ y₁ ∧ ⋯ ∧ δ y_c)` to
`i_* x₁ ∧ ⋯ ∧ i_* xₐ ∧ y₁ ∧ ⋯ ∧ y_c`, where `ιⱼ` is the class of `xⱼ ∈ Hₙ₊₁(F)` modulo `range A`,
`i_*` is the map induced by the fibre inclusion and `δ` the Wang connecting morphism
(`TauCeti.MappingTorus.coe_wangDetLineEquiv_tmul`).

This is the determinant comparison through which an orientation of the homology of a mapping
torus is read off the monodromy: for a path-connected fibre with `det (𝟙 - φ_*) ≠ 0` on `H₁(F)`,
such as a surface whose mapping torus has first Betti number one, the cokernel of `A` on `H₁(F)`
vanishes, `A` is zero on `H₀(F)`, and `det H₁(T_φ)` is identified with `det H₀(F)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48 (the Wang sequence).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomologicalComplex Module TensorProduct

universe w

namespace TauCeti.MappingTorus

variable {k : Type w} [Field k] {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F) (n : ℕ)
  [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))]
  [FiniteDimensional k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
    (ModuleCat.of k k)).obj (TopCat.of F)).homology n)]

/-- **The Wang determinant line isomorphism.** If the homology of the fibre is
finite-dimensional over a field in degrees `n` and `n + 1`, the Wang short exact sequence
`0 ⟶ Hₙ₊₁(F) ⧸ range (𝟙 - φ_*) ⟶ Hₙ₊₁(T_φ) ⟶ ker (𝟙 - φ_*) ⟶ 0` identifies
`det (Hₙ₊₁(F) ⧸ range (𝟙 - φ_*)) ⊗ det (ker (𝟙 - φ_*))` with `det Hₙ₊₁(T_φ)`, with `𝟙 - φ_*`
acting on `Hₙ₊₁(F)` and on `Hₙ(F)` respectively. -/
def wangDetLineEquiv :
    detLine k (((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1)) ⧸ LinearMap.range
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom)) ⊗[k]
      detLine k (LinearMap.ker
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom)) ≃ₗ[k]
      detLine k ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) :=
  detLineShortExactEquiv
    (U := ((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1)) ⧸ LinearMap.range
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom))
    (V := (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
      (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1))
    (W := LinearMap.ker
      (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom))
    (wangKernelShortComplex_shortExact φ n).moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (wangKernelShortComplex_shortExact φ n).exact)
    (wangKernelShortComplex_shortExact φ n).moduleCat_surjective_g

/-- **The value of the Wang determinant line isomorphism.** For classes `x₁, …, xₐ` of `Hₙ₊₁(F)`
and `y₁, …, y_c` of `Hₙ₊₁(T_φ)`, with `a` and `c` the dimensions of the cokernel and the kernel of
`𝟙 - φ_*`, `TauCeti.MappingTorus.wangDetLineEquiv` sends `(ι₁ ∧ ⋯ ∧ ιₐ) ⊗ (δ y₁ ∧ ⋯ ∧ δ y_c)` to
`i_* x₁ ∧ ⋯ ∧ i_* xₐ ∧ y₁ ∧ ⋯ ∧ y_c` in the exterior algebra of `Hₙ₊₁(T_φ)`. Here `ιⱼ` is the class
of `xⱼ` modulo the range of `𝟙 - φ_*`, `i_*` is induced by the fibre inclusion and `δ` is the Wang
connecting morphism, with values in the kernel of `𝟙 - φ_*` on `Hₙ(F)`. -/
@[simp]
theorem coe_wangDetLineEquiv_tmul
    (x : Fin (finrank k (((((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1)) ⧸ LinearMap.range
          (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) (n + 1)).hom))) →
      (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of F)).homology (n + 1))
    (y : Fin (finrank k (LinearMap.ker
        (LinearMap.id - (homologyMap (monodromyChainMap φ (ModuleCat.of k k)) n).hom))) →
      (((singularChainComplexFunctor (ModuleCat.{w} k)).obj
        (ModuleCat.of k k)).obj (TopCat.of (MappingTorus φ))).homology (n + 1)) :
    (wangDetLineEquiv (k := k) φ n (exteriorPower.ιMulti k _ (Submodule.Quotient.mk ∘ x) ⊗ₜ
        exteriorPower.ιMulti k _ ((wangKernelShortComplex φ n).g.hom ∘ y)) :
          ExteriorAlgebra k _) =
      ExteriorAlgebra.ιMulti k _
        (Fin.append ((homologyMap (fibreInclusionChainMap φ (ModuleCat.of k k)) (n + 1)).hom ∘ x)
          y) := by
  -- The objects of the Wang short complex carry the module structures of the explicit types
  -- only up to unfolding, and its first map sends the class of `x` to `i_* x` by definition
  -- (`TauCeti.MappingTorus.wangKernelShortComplex_f_mk`), so the general value applies by
  -- `exact` rather than by rewriting.
  rw [wangDetLineEquiv]
  exact coe_detLineShortExactEquiv_tmul _ _ _ (Submodule.Quotient.mk ∘ x) y

end TauCeti.MappingTorus
