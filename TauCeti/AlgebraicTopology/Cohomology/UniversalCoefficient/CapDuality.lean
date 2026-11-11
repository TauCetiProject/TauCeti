/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Cap products with a homology class and the cup pairing over a field

Let `X` be a space, `k` a field and `μ ∈ Hₙ(X; k)` a homology class. For `p + q = n`, capping
with `μ` is a linear map `Hᵖ(X; k) → H_q(X; k)`, `α ↦ μ ⌢ α` (`TopCat.singularCapLinearMap`),
and evaluating cup products on `μ` is the bilinear cup pairing `Hᵖ(X; k) × H^q(X; k) → k`,
`(α, β) ↦ ⟨α ⌣ β, μ⟩` (`TopCat.singularCupPairing`). The Kronecker pairing identifies `H^q(X; k)`
with the dual of `H_q(X; k)`, and `⟨β, μ ⌢ α⟩ = ⟨α ⌣ β, μ⟩`. Hence capping with `μ` is injective
in degree `p` exactly when the cup pairing has trivial left kernel
(`TopCat.injective_singularCapLinearMap_iff`). No finiteness is needed for this.

If `2 ≠ 0` in `k`, graded commutativity of the cup product makes the square of an odd degree
class vanish (`TopCat.singularCup_self_eq_zero_of_odd`), so in the middle degree `p` of an odd
`p + p = n` the cup pairing is alternating. If moreover `Hᵖ(X; k)` is finite-dimensional and
capping with `μ` is injective on it, the pairing is a nondegenerate alternating form and `Hᵖ(X; k)`
has even dimension
(`TopCat.even_finrank_singularCohomology_of_injective_singularCapLinearMap`). The hypothesis on
`2` cannot be dropped: over `𝔽₂`, the real projective plane has `H¹` of dimension one and capping
with its mod two fundamental class is bijective. When capping with `μ` is bijective, the Betti
numbers in the complementary degrees `p` and `q` agree
(`TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap`).

All cohomology and homology here has coefficients in the tensor unit `𝟙_ (ModuleCat k)`, that is
`k` itself, and both products are taken along the unitors of `𝟙_ (ModuleCat k)`, as in
`TopCat.singularCap_comp_singularKronecker`.

## Main declarations

* `TopCat.singularCapLinearMap`: capping with `μ`, `α ↦ μ ⌢ α`.
* `TopCat.singularCupPairing`: the cup pairing `(α, β) ↦ ⟨α ⌣ β, μ⟩`.
* `TopCat.singularCapLinearMap_eq_zero_iff` and `TopCat.injective_singularCapLinearMap_iff`:
  capping with `μ` kills `α` exactly when `α` lies in the left kernel of the cup pairing.
* `TopCat.singularCup_self_eq_zero_of_odd`: `α ⌣ α = 0` in odd degree when `2 ≠ 0` in `k`.
* `TopCat.even_finrank_singularCohomology_of_injective_singularCapLinearMap` and
  `TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap`: the Betti number
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

variable {k : Type w} [Field k] (X : TopCat.{w})

/-- **Capping with a homology class**: for `μ ∈ Hₙ(X; k)` and `p + q = n`, the `k`-linear map
`Hᵖ(X; k) → H_q(X; k)`, `α ↦ μ ⌢ α`, with the cap product taken along the unitors of
`𝟙_ (ModuleCat k)`. -/
def singularCapLinearMap {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p →ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj X where
  toFun α := (X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom
    p q n h α).hom μ
  map_add' α β := by simp
  map_smul' c α := by simp

/-- `TopCat.singularCapLinearMap h μ α` is the cap product `μ ⌢ α`. -/
@[simp]
theorem singularCapLinearMap_apply {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCapLinearMap h μ α =
      (X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom
        p q n h α).hom μ :=
  (rfl)

/-- **The cup pairing on a homology class**: for `μ ∈ Hₙ(X; k)` and `p + q = n`, the bilinear form
`(α, β) ↦ ⟨α ⌣ β, μ⟩` on `Hᵖ(X; k) × H^q(X; k)`, with the cup product taken along the unitors of
`𝟙_ (ModuleCat k)`. -/
def singularCupPairing {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p →ₗ[k]
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k] k :=
  LinearMap.mk₂ k
    (fun α β ↦ (X.singularKronecker k n (X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h α β)).hom μ)
    (fun α α' β ↦ by simp) (fun c α β ↦ by simp) (fun α β β' ↦ by simp) (fun c α β ↦ by simp)

/-- The cup pairing of `α` and `β` on `μ` is the Kronecker pairing `⟨α ⌣ β, μ⟩`. -/
@[simp]
theorem singularCupPairing_apply {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCupPairing h μ α β =
      (X.singularKronecker k n (X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h α β)).hom μ :=
  (rfl)

/-- The cup pairing of `α` and `β` on `μ` is the Kronecker pairing `⟨β, μ ⌢ α⟩` of `β` with the
cap product of `μ` and `α`. -/
theorem singularCupPairing_eq_singularKronecker_singularCapLinearMap {p q n : ℕ}
    (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCupPairing h μ α β =
      (X.singularKronecker k q β).hom (X.singularCapLinearMap h μ α) := by
  rw [singularCupPairing_apply, singularCapLinearMap_apply,
    ← singularCap_comp_singularKronecker]
  rfl

/-- **Capping with `μ` kills exactly the left kernel of the cup pairing**: over a field,
`μ ⌢ α = 0` if and only if `⟨α ⌣ β, μ⟩ = 0` for every class `β` of the complementary degree. -/
theorem singularCapLinearMap_eq_zero_iff {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCapLinearMap h μ α = 0 ↔ ∀ β, X.singularCupPairing h μ α β = 0 := by
  simp_rw [singularCupPairing_eq_singularKronecker_singularCapLinearMap]
  rw [← forall_dual_apply_eq_zero_iff k]
  -- Every linear form on `H_q(X; k)` is the Kronecker pairing with a class of degree `q`.
  refine ⟨fun H β ↦ H _, fun H φ ↦ ?_⟩
  have := H ((X.singularCohomologyDualEquiv q).symm φ)
  rwa [singularKronecker_singularCohomologyDualEquiv_symm, ModuleCat.hom_ofHom] at this

/-- **Injectivity of capping with a homology class over a field**: capping with `μ ∈ Hₙ(X; k)` is
injective on `Hᵖ(X; k)` if and only if the cup pairing `(α, β) ↦ ⟨α ⌣ β, μ⟩` with
`H^q(X; k)`, `p + q = n`, has trivial left kernel. No finiteness is assumed. -/
theorem injective_singularCapLinearMap_iff {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    Function.Injective (X.singularCapLinearMap h μ) ↔
      ∀ α, (∀ β, X.singularCupPairing h μ α β = 0) → α = 0 := by
  rw [injective_iff_map_eq_zero]
  exact forall_congr' fun α ↦ imp_congr_left (X.singularCapLinearMap_eq_zero_iff h μ α)

/-- **Cup squares of odd classes vanish** when `2 ≠ 0` in the field `k`: by graded commutativity,
`α ⌣ α = -(α ⌣ α)` for `α` of odd degree. -/
theorem singularCup_self_eq_zero_of_odd (h2 : (2 : k) ≠ 0) {p n : ℕ} (hp : Odd p)
    (h : p + p = n) (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom
      p p n h α α = 0 := by
  have hμ : (β_ (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k))).hom ≫
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom = (λ_ (𝟙_ (ModuleCat.{w} k))).hom := by
    simp [unitors_inv_equal]
  have hcomm := X.singularCup_gradedComm_tensorUnit k hμ h α α
  rw [(hp.mul hp).neg_one_pow, neg_one_smul] at hcomm
  have h2' : (2 : k) • X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom p p n h α α = 0 := by
    rw [two_smul]
    nth_rw 1 [hcomm]
    exact neg_add_cancel _
  exact (smul_eq_zero.1 h2').resolve_left h2

/-- In odd degree `p` with `p + p = n`, the cup pairing on `μ` is alternating when `2 ≠ 0`
in `k`. -/
theorem isAlt_singularCupPairing (h2 : (2 : k) ≠ 0) {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing h μ).IsAlt := fun α ↦ by
  rw [singularCupPairing_apply, X.singularCup_self_eq_zero_of_odd h2 hp h α, map_zero]
  rfl

/-- **Middle odd degree cohomology has even dimension under duality**: if `2 ≠ 0` in `k`,
`p` is odd, `p + p = n`, `Hᵖ(X; k)` is finite-dimensional and capping with `μ ∈ Hₙ(X; k)` is
injective on it, then the cup pairing on `μ` is a nondegenerate alternating form on `Hᵖ(X; k)`,
so its dimension is even. The hypothesis on `2` is needed: the real projective plane over `𝔽₂`
has `H¹` of dimension one. -/
theorem even_finrank_singularCohomology_of_injective_singularCapLinearMap (h2 : (2 : k) ≠ 0)
    {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    [FiniteDimensional k (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)]
    (hinj : Function.Injective (X.singularCapLinearMap h μ)) :
    Even (finrank k
      (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)) := by
  refine (X.isAlt_singularCupPairing h2 hp h μ).even_finrank_of_injective ?_ (finrank_self k)
  rw [injective_iff_map_eq_zero]
  exact fun α hα ↦ (X.injective_singularCapLinearMap_iff h μ).1 hinj α fun β ↦ by
    rw [hα, LinearMap.zero_apply]

/-- **Complementary Betti numbers agree under duality**: if capping with `μ ∈ Hₙ(X; k)` is a
bijection `Hᵖ(X; k) → H_q(X; k)` with `p + q = n`, then `H_q(X; k)` and `Hₚ(X; k)` have the same
`finrank`. -/
theorem finrank_singularHomology_eq_of_bijective_singularCapLinearMap {p q n : ℕ}
    (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (hbij : Function.Bijective (X.singularCapLinearMap h μ)) :
    finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj X) =
      finrank k
        (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X) := by
  rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq]
  exact X.finrank_singularCohomology p

end TopCat
