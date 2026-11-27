/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity

/-!
# Capping a cross product with the sphere by a class pulled back from the second factor

Let `k` be a commutative ring and write `Hⁿ(Z)` and `Hₙ(Z)` for the singular cohomology and
homology of `Z` with coefficients in `k`. Let `γ ∈ H_{d+1}(Sᵈ⁺¹)` be the standard generator
(`TauCeti.singularHomologyTopCatSphereGenerator`) and `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹)` the dual class. On the
product `Sᵈ⁺¹ × Y`, the slant product by `γ` reads off the component of a class along
`pr₁^* θ ⌣ pr₂^* H^*(Y)` in the decomposition `TopCat.singularCohomologySphereProdSlantEquiv`.

This file shows that the slant product by `γ` is linear over the cohomology of `Y`, up to the
Koszul sign: for `ψ ∈ Hʲ(Y)` and `φ ∈ H^(q+d+1)(Sᵈ⁺¹ × Y; M)` with coefficients in any `k`-module
`M`,

`(pr₂^* ψ ⌣ φ) / γ = (-1)^((d + 1) j) ψ ⌣ (φ / γ)`

(`TopCat.singularSlant_singularCup_singularCohomologyMap_snd_sphere`). Writing
`φ = pr₂^* β + pr₁^* θ ⌣ pr₂^* c`, the class `pr₂^* ψ ⌣ pr₂^* β` is pulled back from `Y` and has
no slant product by `γ`, while `pr₂^* ψ` moves past `pr₁^* θ` at the cost of the sign
`(-1)^((d + 1) j)`.

By the evaluation law of the slant product, `⟨φ, γ × y⟩ = ⟨φ / γ, y⟩`, and by the adjunction
`⟨φ, z ⌢ α⟩ = ⟨α ⌣ φ, z⟩` of cap and cup products, both sides of the identity

`(γ × y) ⌢ pr₂^* ψ = (-1)^((d + 1) j) γ × (y ⌢ ψ)`

then have the same Kronecker pairing with every class `φ` with coefficients in any `k`-module.
Pairings with classes with injective coefficients separate homology classes
(`TopCat.singularKronecker_bijective`), so the identity holds over every commutative ring `k` and
for every `y ∈ H_{j+q}(Y)`
(`TopCat.singularCapLinearMap_singularHomologyCross_singularCohomologyMap_snd_sphere`). The cross
product `γ × y` is read with coefficients `k` through `k ⊗ k ≅ k`.

For `d = 0`, a closed oriented three-manifold `Y` with fundamental class `y = [Y]` and a class
`ψ ∈ H²(Y)`, the sign is `+1`: the Poincaré dual of `pr₂^* ψ` against `[S¹] × [Y]` is the cross
product `[S¹] × PD_Y(ψ)` of the circle with the Poincaré dual of `ψ` in `Y`.

## Main results

* `TopCat.singularSlant_singularCup_singularCohomologyMap_snd_sphere`:
  `(pr₂^* ψ ⌣ φ) / γ = (-1)^((d + 1) j) ψ ⌣ (φ / γ)`.
* `TopCat.singularCapLinearMap_singularHomologyCross_singularCohomologyMap_snd_sphere`:
  `(γ × y) ⌢ pr₂^* ψ = (-1)^((d + 1) j) γ × (y ⌢ ψ)`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 5, Section 6 (the slant and
  cap products of cross products).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products) and Section 3.B (cross products).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

/-- **Slanting by the sphere generator is linear over the cohomology of the second factor**: for
the standard generator `γ` of `H_{d+1}(Sᵈ⁺¹; k)`, a class `ψ ∈ Hʲ(Y; k)` and a class
`φ ∈ H^(q+d+1)(Sᵈ⁺¹ × Y; M)` with coefficients in any `k`-module `M`,
`(pr₂^* ψ ⌣ φ) / γ = (-1)^((d + 1) j) ψ ⌣ (φ / γ)`, with `ψ` acting through `k ⊗ M ≅ M`. -/
theorem singularSlant_singularCup_singularCohomologyMap_snd_sphere (M : ModuleCat.{w} k)
    (Y : TopCat.{w}) {d j q : ℕ}
    (ψ : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j)
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (q + (d + 1))) :
    singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) (j + q)
        (j + q + (d + 1)) (add_comm (d + 1) (j + q))
        (TauCeti.singularHomologyTopCatSphereGenerator k d)
        ((sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ _).inv (λ_ M).hom j (q + (d + 1))
          (j + q + (d + 1)) (by omega)
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) j ψ) φ) =
      ((-1 : ℤ) ^ ((d + 1) * j)) •
        Y.singularCup k (λ_ _).inv (λ_ M).hom j q (j + q) rfl ψ
          (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) q
            (q + (d + 1)) (add_comm (d + 1) q)
            (TauCeti.singularHomologyTopCatSphereGenerator k d) φ) := by
  obtain ⟨x₀⟩ : Nonempty (sphere.{w} (d + 1)) := inferInstance
  -- write `φ = pr₂^* β + pr₁^* θ ⌣ pr₂^* c`, with `c = φ / γ`
  conv_lhs => rw [← singularCohomologyMap_snd_add_singularCup_sphere M Y x₀ φ]
  set c := singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) q
    (q + (d + 1)) (add_comm (d + 1) q) (TauCeti.singularHomologyTopCatSphereGenerator k d) φ
  set θ := TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
    (TauCeti.singularCohomologyTopCatSphereGenerator k d)
  -- `pr₂^* ψ ⌣ pr₁^* θ ⌣ pr₂^* c = (-1)^((d + 1) j) pr₁^* θ ⌣ pr₂^* ψ ⌣ pr₂^* c`, by associativity
  -- and graded commutativity of `pr₂^* ψ` and `pr₁^* θ`
  have hcomm : (sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ _).inv (λ_ M).hom j (q + (d + 1))
      (j + q + (d + 1)) (by omega)
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) j ψ)
      ((sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ _).inv (λ_ M).hom (d + 1) q (q + (d + 1))
        (add_comm (d + 1) q) θ
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) q c)) =
      ((-1 : ℤ) ^ ((d + 1) * j)) •
        (sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ _).inv (λ_ M).hom (d + 1) (j + q)
          (j + q + (d + 1)) (add_comm (d + 1) (j + q)) θ
          ((sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ _).inv (λ_ M).hom j q (j + q) rfl
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) j ψ)
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) q c)) := by
    rw [← (sphere.{w} (d + 1) ⊗ Y).singularCup_assoc k (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv)
        (u₂₃ := (λ_ _).inv) (u' := (λ_ _).inv) (μ₁₂ := (λ_ _).hom) (μ := (λ_ M).hom)
        (μ₂₃ := (λ_ M).hom) (μ' := (λ_ M).hom) (by monoidal) (by monoidal)
        (rfl : j + (d + 1) = j + (d + 1)) (by omega) (add_comm (d + 1) q) (by omega),
      (sphere.{w} (d + 1) ⊗ Y).singularCup_gradedComm_tensorUnit k (μ := (λ_ _).hom)
        (IsCommMonObj.mul_comm _) (add_comm (d + 1) j),
      map_zsmul, LinearMap.smul_apply,
      (sphere.{w} (d + 1) ⊗ Y).singularCup_assoc k (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv)
        (u₂₃ := (λ_ _).inv) (u' := (λ_ _).inv) (μ₁₂ := (λ_ _).hom) (μ := (λ_ M).hom)
        (μ₂₃ := (λ_ M).hom) (μ' := (λ_ M).hom) (by monoidal) (by monoidal)
        (add_comm (d + 1) j) (by omega) rfl (by omega)]
  rw [map_add, hcomm, singularCup_naturality, singularCup_naturality, ← map_zsmul, ← map_zsmul,
    singularSlant_singularCohomologyMap_snd_add_singularCup M _ Y _ d.succ_ne_zero,
    TauCeti.singularKronecker_singularCohomologyTopCatSphereGenerator, one_smul]

/-- **Capping a cross product with the sphere by a class of the second factor**: over a
commutative ring `k`, for the standard generator `γ` of `H_{d+1}(Sᵈ⁺¹; k)`, a class
`y ∈ H_{j+q}(Y; k)` and a class `ψ ∈ Hʲ(Y; k)`,
`(γ × y) ⌢ pr₂^* ψ = (-1)^((d + 1) j) γ × (y ⌢ ψ)`, where the cross products are read with
coefficients `k` through `k ⊗ k ≅ k`. For `d = 0`, `j = 2` and the fundamental class of a closed
oriented three-manifold `Y`, this says that the Poincaré dual of `pr₂^* ψ` against `[S¹] × [Y]` is
`[S¹] × PD_Y(ψ)`. -/
theorem singularCapLinearMap_singularHomologyCross_singularCohomologyMap_snd_sphere
    (Y : TopCat.{w}) {d j q m n : ℕ} (hn : d + 1 + (j + q) = n) (hm : d + 1 + q = m)
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj (𝟙_ (ModuleCat.{w} k))).obj Y)
    (ψ : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j) :
    (sphere.{w} (d + 1) ⊗ Y).singularCapLinearMap k (p := j) (q := m) (by omega)
        (((singularHomologyFunctor (ModuleCat.{w} k) n).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ Y)
          (singularHomologyCross (sphere.{w} (d + 1)) Y (𝟙_ (ModuleCat.{w} k))
            (𝟙_ (ModuleCat.{w} k)) (d + 1) (j + q) n hn
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ y)))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) j ψ) =
      ((-1 : ℤ) ^ ((d + 1) * j)) •
        ((singularHomologyFunctor (ModuleCat.{w} k) m).map
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (sphere.{w} (d + 1) ⊗ Y)
          (singularHomologyCross (sphere.{w} (d + 1)) Y (𝟙_ (ModuleCat.{w} k))
            (𝟙_ (ModuleCat.{w} k)) (d + 1) q m hm
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ
              Y.singularCapLinearMap k (rfl : j + q = j + q) y ψ)) := by
  obtain rfl : m = q + (d + 1) := by omega
  obtain rfl : n = j + q + (d + 1) := by omega
  -- Classes of `H_{q+d+1}(Sᵈ⁺¹ × Y; k)` are separated by their Kronecker pairings with classes
  -- with injective coefficients: the inclusion into an injective module is such a pairing.
  let ι := Injective.ι (((singularHomologyFunctor (ModuleCat.{w} k) (q + (d + 1))).obj
    (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (d + 1) ⊗ Y))
  apply (ModuleCat.mono_iff_injective ι).1 inferInstance
  obtain ⟨φ, hφ⟩ := ((sphere.{w} (d + 1) ⊗ Y).singularKronecker_bijective k
    (R := 𝟙_ (ModuleCat.{w} k)) (q + (d + 1))).2 ι
  -- both sides pair with `φ` to `(-1)^((d + 1) j) ⟨φ / γ, y ⌢ ψ⟩`
  rw [← hφ, map_zsmul, singularCapLinearMap_apply, singularCapLinearMap_apply,
    ← ConcreteCategory.comp_apply, singularCap_comp_singularKronecker,
    ← singularKronecker_singularSlant, ← singularKronecker_singularSlant,
    singularSlant_singularCup_singularCohomologyMap_snd_sphere, map_zsmul,
    ← singularCap_comp_singularKronecker]
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply]

end TopCat
