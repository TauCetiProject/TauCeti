/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
public import TauCeti.LinearAlgebra.QuadraticForm.Dual

/-!
# The indices of inertia of the intersection form of `Sᵈ⁺¹ × Y`

Let `k` be a linearly ordered field, such as `ℝ`, and write `Hⁿ(Z)` for the singular cohomology
of `Z` with coefficients in `k`. For a homology class `z ∈ Hₙ(X; k)` and `p + p = n`, the cup
pairing `(x, y) ↦ ⟨x ⌣ y, z⟩` is a bilinear form on `Hᵖ(X)` (`TopCat.singularCupPairing` with
`q = p`). For a closed oriented four-manifold `X`, `p = 2` and `z` its fundamental class, this is
the real intersection form, and its positive index of inertia is `b₂⁺(X)`.

This file computes both indices of inertia of this form on a product `X = Sᵈ⁺¹ × Y` with a compact
manifold `Y` of dimension below `2 (p + d + 1)`, in degree `p + d + 1` even. Write a class `x` as
`(b, c) = pr₂^* b + pr₁^* θ ⌣ pr₂^* c` in the slant decomposition
`Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y) ≅ Hᵖ⁺ᵈ⁺¹(Y) × Hᵖ(Y)` (`TopCat.singularCohomologySphereProdSlantEquiv`), where
`θ ∈ Hᵈ⁺¹(Sᵈ⁺¹)` is dual to the standard generator. The cup square of `x` is
`2 pr₁^* θ ⌣ pr₂^* (b ⌣ c)` (`TopCat.singularCup_self_eq_two_smul_of_compactSpace`), so the
quadratic form of the cup pairing is

`⟨x ⌣ x, z⟩ = 2 ψ_z(b, c)`,  `ψ_z(b, c) = ⟨pr₁^* θ ⌣ pr₂^* (b ⌣ c), z⟩`

(`TopCat.singularCupPairing_apply_self_sphere`), with `ψ_z` the pairing of `Hᵖ⁺ᵈ⁺¹(Y)` with
`Hᵖ(Y)` given by `TopCat.sphereProdCupPairing`. This is twice the quadratic form of a pairing, so
when `Hᵖ⁺ᵈ⁺¹(Y)` and `Hᵖ(Y)` are finite dimensional both of its indices of inertia are the rank of
`ψ_z` (`TauCeti.sigPos_dualProd_comp_prodMap`):

* `TopCat.sigPos_singularCupPairing_sphere`, `TopCat.sigNeg_singularCupPairing_sphere`:
  both indices of inertia of the cup pairing against `z` are the rank of `ψ_z`;
* `TopCat.sigPos_singularCupPairing_sphere_of_injective_flip`,
  `TopCat.sigNeg_singularCupPairing_sphere_of_injective_flip`: if every nonzero `c ∈ Hᵖ(Y)` pairs
  nontrivially with some `b` under `ψ_z`, both indices are `dim Hᵖ(Y)`.

When `z = [Sᵈ⁺¹] × y` is the homology cross product of the standard generator of `Hᵈ⁺¹(Sᵈ⁺¹; k)`
with a class `y` of `Y`, read with coefficients `k`, the pairing `ψ_z` is the cup pairing
`(b, c) ↦ ⟨b ⌣ c, y⟩` of `Y`, with no sign (`TopCat.sphereProdCupPairing_singularHomologyCross`).
This follows from `⟨pr₁^* θ ⌣ pr₂^* β, [Sᵈ⁺¹] × y⟩ = ⟨θ, [Sᵈ⁺¹]⟩ ⟨β, y⟩ = ⟨β, y⟩`
(`TopCat.singularKronecker_singularCup_fst_snd_singularHomologyCross`). So both indices of
inertia against `[Sᵈ⁺¹] × y` are the rank of this pairing of `Y`, and they are `dim Hᵖ(Y)` when
it is nondegenerate on `Hᵖ(Y)`
(`TopCat.sigPos_singularCupPairing_sphere_singularHomologyCross_of_injective_flip`,
`TopCat.sigNeg_singularCupPairing_sphere_singularHomologyCross_of_injective_flip`).

For a closed oriented three-manifold `Y`, `d = 0`, `p = 1`, `k = ℝ` and `y = [Y]`, the pairing of
`Y` is the Poincaré duality pairing `(b, c) ↦ ⟨b ⌣ c, [Y]⟩` of `H²(Y; ℝ)` with `H¹(Y; ℝ)`. It is
then perfect, and once `[S¹] × [Y]` is known to be a fundamental class of `S¹ × Y` the theorems say
`b₂⁺(S¹ × Y) = b₂⁻(S¹ × Y) = b₁(Y)`. Poincaré duality on `Y` is not proved here, so the
nondegeneracy of the pairing of `Y` is a hypothesis; nor is it proved here that `[S¹] × [Y]` is a
fundamental class of `S¹ × Y`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2 (cup products) and Section 3.3 (Poincaré duality).
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Module

universe w

namespace TopCat

variable {k : Type w}

section CommRing

variable [CommRing k]

/-- **The pairing of `Hᵖ⁺ᵈ⁺¹(Y)` with `Hᵖ(Y)` cut out by a class of `Sᵈ⁺¹ × Y`**: for a homology
class `z` of `Sᵈ⁺¹ × Y` of degree `2 (p + d + 1)`, the pairing
`(b, c) ↦ ⟨pr₁^* θ ⌣ pr₂^* (b ⌣ c), z⟩`, where `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; k)` is dual to the standard
generator. When `Y` is a compact manifold of dimension below `2 (p + d + 1)` and `p + d + 1` is
even, twice its value at the slant components `(b, c)` of a class `x` is `⟨x ⌣ x, z⟩`
(`TopCat.singularCupPairing_apply_self_sphere`). -/
def sphereProdCupPairing (Y : TopCat.{w}) (d p : ℕ)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ Y)) :
    Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)) →ₗ[k]
      Dual k (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :=
  (Y.singularCup k (λ_ _).inv (λ_ _).hom (p + (d + 1)) p (p + p + (d + 1)) (by omega)).compr₂
    ((sphere.{w} (d + 1) ⊗ Y).singularCupPairing k (by omega) z
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
          (TauCeti.singularCohomologyTopCatSphereGenerator k d)) ∘ₗ
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (p + p + (d + 1))).hom)

@[simp]
lemma sphereProdCupPairing_apply (Y : TopCat.{w}) (d p : ℕ)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ Y))
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))
    (c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    sphereProdCupPairing Y d p z b c =
      (sphere.{w} (d + 1) ⊗ Y).singularCupPairing k (by omega) z
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
          (TauCeti.singularCohomologyTopCatSphereGenerator k d))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (p + p + (d + 1))
          (Y.singularCup k (λ_ _).inv (λ_ _).hom (p + (d + 1)) p (p + p + (d + 1)) (by omega)
            b c)) :=
  (rfl)

/-- **`ψ_z` on a cross product with the sphere generator is the cup pairing of `Y`**: let
`z = [Sᵈ⁺¹] × y` be the homology cross product of the standard generator `[Sᵈ⁺¹]` of
`Hᵈ⁺¹(Sᵈ⁺¹; k)` with a class `y` of `Y`, read with coefficients `k` instead of `k ⊗ k`. Then
`ψ_z(b, c) = ⟨b ⌣ c, y⟩`, with no sign. For `y` the fundamental class of a closed oriented
three-manifold `Y`, `d = 0` and `p = 1`, this is the Poincaré duality pairing of `H²(Y)` with
`H¹(Y)`. -/
@[simp]
theorem sphereProdCupPairing_singularHomologyCross (Y : TopCat.{w}) (d p : ℕ)
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj Y) :
    sphereProdCupPairing Y d p
        (((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ Y)
          (singularHomologyCross (sphere.{w} (d + 1)) Y (𝟙_ (ModuleCat.{w} k))
            (𝟙_ (ModuleCat.{w} k)) (d + 1) (p + p + (d + 1)) (p + p + (d + 1) + (d + 1))
            (by omega) (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ y))) =
      Y.singularCupPairing k (p := p + (d + 1)) (q := p) (by omega) y := by
  ext b c
  rw [sphereProdCupPairing_apply, singularCupPairing_apply,
    singularKronecker_singularCup_fst_snd_singularHomologyCross,
    TauCeti.singularKronecker_singularCohomologyTopCatSphereGenerator, one_mul,
    singularCupPairing_apply]

variable {M E : Type w} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] [CompactSpace M]

/-- **The quadratic form of the cup pairing on `Sᵈ⁺¹ × Y`**: if `Y` is a compact manifold of
dimension below `2 (p + d + 1)` and `p + d + 1` is even, then for every class `x` of
`Sᵈ⁺¹ × Y` of degree `p + d + 1`, with slant components `(b, c)` at any point `x₀`,
`⟨x ⌣ x, z⟩ = 2 ψ_z(b, c)`. -/
theorem singularCupPairing_apply_self_sphere
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] {d n p : ℕ} (x₀ : sphere.{w} (d + 1))
    (hn : finrank ℝ E = n) (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ TopCat.of M))
    (x : (sphere.{w} (d + 1) ⊗ TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1))) :
    (sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (by omega) z x x =
      2 * sphereProdCupPairing (TopCat.of M) d p z
        (singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) _ x₀ p x).1
        (singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) _ x₀ p x).2 := by
  rw [singularCupPairing_apply, singularCup_self_eq_two_smul_of_compactSpace x₀ hn hnp hp x,
    singularCohomologySphereProdSlantEquiv_symm_apply]
  simp [sphereProdCupPairing_apply, singularCupPairing_apply]

end CommRing

section Signature

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] {M E : Type w} [TopologicalSpace M]
  [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [CompactSpace M]

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- The quadratic form of the cup pairing on `Sᵈ⁺¹ × Y` is equivalent to twice the quadratic form
`(b, c) ↦ ψ_z(b, c)` of the pairing `ψ_z`. -/
private theorem equivalent_toQuadraticMap_singularCupPairing_sphere {d n p : ℕ}
    (hn : finrank ℝ E = n) (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ TopCat.of M)) :
    (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) z)).Equivalent
      ((2 : k) • (QuadraticForm.dualProd k _).comp
        ((sphereProdCupPairing (TopCat.of M) d p z).prodMap LinearMap.id)) := by
  obtain ⟨x₀⟩ : Nonempty (sphere.{w} (d + 1)) := inferInstance
  let e := singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) (TopCat.of M) x₀ p
  refine ⟨{ toLinearEquiv := e, map_app' := fun x ↦ ?_ }⟩
  simp [singularCupPairing_apply_self_sphere x₀ hn hnp hp z x, e]

/-- **The positive index of inertia of the cup pairing on `Sᵈ⁺¹ × Y`**: if `Y` is a compact
manifold of dimension below `2 (p + d + 1)`, `p + d + 1` is even and `Hᵖ⁺ᵈ⁺¹(Y)` and `Hᵖ(Y)` are
finite dimensional, the cup pairing `(x, y) ↦ ⟨x ⌣ y, z⟩` on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y)` has positive
index of inertia the rank of the pairing `ψ_z` of `Hᵖ⁺ᵈ⁺¹(Y)` with `Hᵖ(Y)`. -/
theorem sigPos_singularCupPairing_sphere {d n p : ℕ} (hn : finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) p)]
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ TopCat.of M)) :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) z)) =
      finrank k (LinearMap.range (sphereProdCupPairing (TopCat.of M) d p z)) := by
  rw [(equivalent_toQuadraticMap_singularCupPairing_sphere hn hnp hp z).sigPos_eq,
    QuadraticForm.sigPos_smul_of_pos _ two_pos, TauCeti.sigPos_dualProd_comp_prodMap]

/-- **The negative index of inertia of the cup pairing on `Sᵈ⁺¹ × Y`**: under the hypotheses of
`TopCat.sigPos_singularCupPairing_sphere`, the cup pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y)` has
negative index of inertia the rank of the pairing `ψ_z`. -/
theorem sigNeg_singularCupPairing_sphere {d n p : ℕ} (hn : finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) p)]
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ TopCat.of M)) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) z)) =
      finrank k (LinearMap.range (sphereProdCupPairing (TopCat.of M) d p z)) := by
  rw [(equivalent_toQuadraticMap_singularCupPairing_sphere hn hnp hp z).sigNeg_eq,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos, TauCeti.sigNeg_dualProd_comp_prodMap]

/-- **Positive index `dim Hᵖ(Y)` for a nondegenerate pairing**: under the hypotheses of
`TopCat.sigPos_singularCupPairing_sphere`, if every nonzero `c ∈ Hᵖ(Y)` pairs nontrivially
with some `b ∈ Hᵖ⁺ᵈ⁺¹(Y)` under `ψ_z`, as Poincaré duality gives for the fundamental class `z` of
`S¹ × Y` with `Y` a closed oriented three-manifold, `d = 0` and `p = 1`, then the cup pairing on
`Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y)` has positive index of inertia `dim Hᵖ(Y)`; for `S¹ × Y` this is
`b₂⁺(S¹ × Y) = b₁(Y)`. -/
theorem sigPos_singularCupPairing_sphere_of_injective_flip {d n p : ℕ} (hn : finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) p)]
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ TopCat.of M))
    (hz : Function.Injective (sphereProdCupPairing (TopCat.of M) d p z).flip) :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) z)) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) p) := by
  rw [sigPos_singularCupPairing_sphere hn hnp hp z, ← LinearMap.finrank_range_flip,
    LinearMap.finrank_range_of_inj hz]

/-- **Negative index `dim Hᵖ(Y)` for a nondegenerate pairing**: under the hypotheses of
`TopCat.sigPos_singularCupPairing_sphere_of_injective_flip`, the cup pairing on
`Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y)` has negative index of inertia `dim Hᵖ(Y)`. -/
theorem sigNeg_singularCupPairing_sphere_of_injective_flip {d n p : ℕ} (hn : finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) p)]
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ TopCat.of M))
    (hz : Function.Injective (sphereProdCupPairing (TopCat.of M) d p z).flip) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) z)) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) p) := by
  rw [sigNeg_singularCupPairing_sphere hn hnp hp z, ← LinearMap.finrank_range_flip,
    LinearMap.finrank_range_of_inj hz]

/-- **Positive index `dim Hᵖ(Y)` against `[Sᵈ⁺¹] × y`**: under the hypotheses of
`TopCat.sigPos_singularCupPairing_sphere`, if every nonzero `c ∈ Hᵖ(Y)` has some
`b ∈ Hᵖ⁺ᵈ⁺¹(Y)` with `⟨b ⌣ c, y⟩ ≠ 0`, then the cup pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y)` against
`[Sᵈ⁺¹] × y` has positive index of inertia `dim Hᵖ(Y)`. For `y = [Y]` the fundamental class of a
closed oriented three-manifold, `d = 0` and `p = 1`, the hypothesis is Poincaré duality on `Y`, and
the conclusion is `b₂⁺(S¹ × Y) = b₁(Y)` once `[S¹] × [Y]` is known to be a fundamental class of
`S¹ × Y`, which is not proved here. -/
theorem sigPos_singularCupPairing_sphere_singularHomologyCross_of_injective_flip {d n p : ℕ}
    (hn : finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) p)]
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (TopCat.of M))
    (hy : Function.Injective
      ((TopCat.of M).singularCupPairing k (p := p + (d + 1)) (q := p) (by omega) y).flip) :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega)
        (((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ TopCat.of M)
          (singularHomologyCross (sphere.{w} (d + 1)) (TopCat.of M) (𝟙_ (ModuleCat.{w} k))
            (𝟙_ (ModuleCat.{w} k)) (d + 1) (p + p + (d + 1)) (p + p + (d + 1) + (d + 1))
            (by omega) (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ y))))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) p) := by
  rw [sigPos_singularCupPairing_sphere_of_injective_flip hn hnp hp _
    (by rwa [sphereProdCupPairing_singularHomologyCross])]

/-- **Negative index `dim Hᵖ(Y)` against `[Sᵈ⁺¹] × y`**: under the hypotheses of
`TopCat.sigPos_singularCupPairing_sphere_singularHomologyCross_of_injective_flip`, the cup pairing
on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y)` against `[Sᵈ⁺¹] × y` has negative index of inertia `dim Hᵖ(Y)`. -/
theorem sigNeg_singularCupPairing_sphere_singularHomologyCross_of_injective_flip {d n p : ℕ}
    (hn : finrank ℝ E = n)
    (hnp : n < p + p + (d + 1) + (d + 1)) (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) p)]
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1))).obj
      (𝟙_ (ModuleCat.{w} k))).obj (TopCat.of M))
    (hy : Function.Injective
      ((TopCat.of M).singularCupPairing k (p := p + (d + 1)) (q := p) (by omega) y).flip) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((sphere.{w} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega)
        (((singularHomologyFunctor (ModuleCat.{w} k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ TopCat.of M)
          (singularHomologyCross (sphere.{w} (d + 1)) (TopCat.of M) (𝟙_ (ModuleCat.{w} k))
            (𝟙_ (ModuleCat.{w} k)) (d + 1) (p + p + (d + 1)) (p + p + (d + 1) + (d + 1))
            (by omega) (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ y))))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) p) := by
  rw [sigNeg_singularCupPairing_sphere_of_injective_flip hn hnp hp _
    (by rwa [sphereProdCupPairing_singularHomologyCross])]

end Signature

end TopCat
