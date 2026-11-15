/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Cap products with a homology class and the cup pairing over a field

Let `X` be a space, `k` a field and `μ ∈ Hₙ(X; k)` a homology class. For `p + q = n`, capping
with `μ` is a linear map `Hᵖ(X; k) → H_q(X; k)`, `α ↦ μ ⌢ α` (`TopCat.singularCapLinearMap`,
defined over any commutative ring in `TauCeti.AlgebraicTopology.Cohomology.Cap.Basic`), and
evaluating cup products on `μ` is the bilinear cup pairing `Hᵖ(X; k) × H^q(X; k) → k`,
`(α, β) ↦ ⟨α ⌣ β, μ⟩` (`TopCat.singularCupPairing`, from
`TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker`). Over a field, the Kronecker pairing
identifies `H^q(X; k)` with the dual of `H_q(X; k)`, and `⟨β, μ ⌢ α⟩ = ⟨α ⌣ β, μ⟩`. Hence capping
with `μ` is injective in degree `p` exactly when the cup pairing is left-separating
(`TopCat.injective_singularCapLinearMap_iff`), and, by graded commutativity, capping with `μ` is
injective in degree `q` exactly when it is right-separating
(`TopCat.separatingRight_singularCupPairing_iff`). In a middle degree `p` with `p + p = n` the
cup pairing is reflexive, so it is nondegenerate exactly when capping with `μ` is injective on
`Hᵖ(X; k)` (`TopCat.nondegenerate_singularCupPairing_iff`). No finiteness is needed for this.

If `2 ≠ 0` in `k`, graded commutativity of the cup product makes the cup pairing alternating in
an odd middle degree `p` with `p + p = n` (`TopCat.isAlt_singularCupPairing`, from
`TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker`). If moreover capping with `μ` is injective
on `Hᵖ(X; k)`, the pairing is a nondegenerate alternating form and `finrank k Hᵖ(X; k)` is even
(`TopCat.even_finrank_singularCohomology_of_injective_singularCapLinearMap`), and so is
`finrank k Hₚ(X; k)`
(`TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`); when `Hᵖ(X; k)` is
infinite-dimensional its `finrank` is `0`. The hypothesis on
`2` cannot be dropped: over `𝔽₂`, the real projective plane has `H¹` of dimension one and capping
with its mod two fundamental class is bijective. When capping with `μ` is bijective, the Betti
numbers in the complementary degrees `p` and `q` agree
(`TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap` and
`TopCat.finrank_singularCohomology_eq_of_bijective_singularCapLinearMap`).

All cohomology and homology here has coefficients in the tensor unit `𝟙_ (ModuleCat k)`, that is
`k` itself, and both products are taken along the unitors of `𝟙_ (ModuleCat k)`, as in
`TopCat.singularCap_comp_singularKronecker`.

## Main declarations

* `TopCat.singularCapLinearMap_eq_zero_iff` and `TopCat.injective_singularCapLinearMap_iff`:
  capping with `μ` kills `α` exactly when `α` lies in the left kernel of the cup pairing.
* `TopCat.separatingRight_singularCupPairing_iff` and
  `TopCat.nondegenerate_singularCupPairing_iff`: the right kernel and, in a middle degree,
  nondegeneracy.
* `TopCat.even_finrank_singularCohomology_of_injective_singularCapLinearMap`,
  `TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`,
  `TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap` and
  `TopCat.finrank_singularCohomology_eq_of_bijective_singularCapLinearMap`: the Betti number
  consequences.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Theorem 3.11, and Section 3.3, Proposition 3.38.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module AlgebraicTopology

universe w

namespace TopCat

variable (X : TopCat.{w}) (k : Type w) [Field k]

/-- **Capping with `μ` kills exactly the left kernel of the cup pairing**: over a field,
`μ ⌢ α = 0` if and only if `⟨α ⌣ β, μ⟩ = 0` for every class `β` of the complementary degree. -/
theorem singularCapLinearMap_eq_zero_iff {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCapLinearMap k h μ α = 0 ↔ ∀ β, X.singularCupPairing k h μ α β = 0 := by
  simp_rw [singularCupPairing_eq_singularKronecker_singularCapLinearMap]
  rw [← forall_dual_apply_eq_zero_iff k]
  -- Every linear form on `H_q(X; k)` is the Kronecker pairing with a class of degree `q`.
  refine ⟨fun H β ↦ H _, fun H φ ↦ ?_⟩
  have := H ((X.singularCohomologyDualEquiv q).symm φ)
  rwa [singularKronecker_singularCohomologyDualEquiv_symm, ModuleCat.hom_ofHom] at this

/-- **Injectivity of capping with a homology class over a field**: capping with `μ ∈ Hₙ(X; k)` is
injective on `Hᵖ(X; k)` if and only if the cup pairing `(α, β) ↦ ⟨α ⌣ β, μ⟩` with
`H^q(X; k)`, `p + q = n`, is left-separating. No finiteness is assumed. -/
theorem injective_singularCapLinearMap_iff {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    Function.Injective (X.singularCapLinearMap k h μ) ↔
      (X.singularCupPairing k h μ).SeparatingLeft := by
  rw [injective_iff_map_eq_zero]
  exact forall_congr' fun α ↦ imp_congr_left (X.singularCapLinearMap_eq_zero_iff k h μ α)

/-- **The right kernel of the cup pairing over a field**: the cup pairing on `μ ∈ Hₙ(X; k)` of
`Hᵖ(X; k)` with `H^q(X; k)`, `p + q = n`, is right-separating if and only if capping with `μ` is
injective on `H^q(X; k)`. No finiteness is assumed. -/
theorem separatingRight_singularCupPairing_iff {p q n : ℕ} (h : p + q = n) (h' : q + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing k h μ).SeparatingRight ↔
      Function.Injective (X.singularCapLinearMap k h' μ) := by
  rw [X.injective_singularCapLinearMap_iff k h' μ]
  refine forall_congr' fun β ↦ imp_congr_left (forall_congr' fun α ↦ ?_)
  rw [X.singularCupPairing_gradedComm k h h' μ α β,
    ((isUnit_neg_one (α := k)).pow (p * q)).mul_right_eq_zero]

/-- **Nondegeneracy of the cup pairing in a middle degree over a field**: for `p + p = n`, the cup
pairing on `μ ∈ Hₙ(X; k)` is nondegenerate on `Hᵖ(X; k)` if and only if capping with `μ` is
injective on `Hᵖ(X; k)`. No finiteness is assumed. -/
theorem nondegenerate_singularCupPairing_iff {p n : ℕ} (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing k h μ).Nondegenerate ↔
      Function.Injective (X.singularCapLinearMap k h μ) := by
  rw [(X.isRefl_singularCupPairing k h μ).nondegenerate_iff_separatingLeft,
    X.injective_singularCapLinearMap_iff k h μ]

/-- **Middle odd degree cohomology has even dimension under duality**: if `2 ≠ 0` in `k`,
`p` is odd, `p + p = n` and capping with `μ ∈ Hₙ(X; k)` is injective on `Hᵖ(X; k)`, then the cup
pairing on `μ` is a nondegenerate alternating form on `Hᵖ(X; k)`, so its `finrank` is even. No
finiteness is assumed: an infinite-dimensional `Hᵖ(X; k)` has `finrank` zero. The hypothesis on
`2` is needed: the real projective plane over `𝔽₂` has `H¹` of dimension one. -/
theorem even_finrank_singularCohomology_of_injective_singularCapLinearMap (h2 : (2 : k) ≠ 0)
    {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (hinj : Function.Injective (X.singularCapLinearMap k h μ)) :
    Even (finrank k
      (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)) := by
  by_cases hfin : Module.Finite k
      (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
  swap
  · rw [finrank_of_not_finite hfin]
    exact .zero
  exact LinearMap.BilinForm.IsAlt.even_finrank
    (X.isAlt_singularCupPairing k (IsRegular.of_ne_zero h2).left hp h μ)
    ((X.nondegenerate_singularCupPairing_iff k h μ).2 hinj)

/-- **Middle odd degree homology has even dimension under duality**: if `2 ≠ 0` in `k`, `p` is
odd, `p + p = n` and capping with `μ ∈ Hₙ(X; k)` is injective on `Hᵖ(X; k)`, then `Hₚ(X; k)` has
even `finrank`. -/
theorem even_finrank_singularHomology_of_injective_singularCapLinearMap (h2 : (2 : k) ≠ 0)
    {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (hinj : Function.Injective (X.singularCapLinearMap k h μ)) :
    Even (finrank k
      (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X)) := by
  convert X.even_finrank_singularCohomology_of_injective_singularCapLinearMap k h2 hp h μ hinj
    using 1
  exact (X.finrank_singularCohomology p).symm

/-- **Complementary Betti numbers agree under duality**: if capping with `μ ∈ Hₙ(X; k)` is a
bijection `Hᵖ(X; k) → H_q(X; k)` with `p + q = n`, then `H_q(X; k)` and `Hₚ(X; k)` have the same
`finrank`. -/
theorem finrank_singularHomology_eq_of_bijective_singularCapLinearMap {p q n : ℕ}
    (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (hbij : Function.Bijective (X.singularCapLinearMap k h μ)) :
    finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj X) =
      finrank k
        (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X) := by
  rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq]
  exact X.finrank_singularCohomology p

/-- **Complementary cohomological Betti numbers agree under duality**: if capping with
`μ ∈ Hₙ(X; k)` is a bijection `Hᵖ(X; k) → H_q(X; k)` with `p + q = n`, then `H^q(X; k)` and
`Hᵖ(X; k)` have the same `finrank`. -/
theorem finrank_singularCohomology_eq_of_bijective_singularCapLinearMap {p q n : ℕ}
    (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (hbij : Function.Bijective (X.singularCapLinearMap k h μ)) :
    finrank k (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) =
      finrank k (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) := by
  exact (X.finrank_singularCohomology q).trans
    ((X.finrank_singularHomology_eq_of_bijective_singularCapLinearMap k h μ hbij).trans
      (X.finrank_singularCohomology p).symm)

end TopCat
