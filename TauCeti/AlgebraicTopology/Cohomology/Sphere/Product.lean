/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Prod
public import TauCeti.AlgebraicTopology.Cohomology.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.Slant
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.Disk

/-!
# The cohomology of `Sᵈ⁺¹ × Y`

Let `k` be a commutative ring and `M` a `k`-module, and write `Hⁿ(Z; M)` for the singular
cohomology of `Z` with coefficients in `M`, computed from the singular chains with coefficients in
`k`. For spaces `X` and `Y`, slant products by the homology of `X` turn classes on `X × Y` into
classes on `Y` (`TopCat.singularSlant`); here they are taken along the multiplication
`k ⊗ k ≅ k`, so that they act on `Hⁿ(X × Y; M)`.

**Classes pulled back from `Y`** (in `TauCeti.AlgebraicTopology.Cohomology.Slant`). Let `X` be
path-connected with projective homology `Hₚ(X; k)`, and `x₀ ∈ X`. Slanting by the class of the
point `x₀` recovers a class pulled back from `Y`, `pr₂^* b / [x₀] = b`
(`TopCat.singularSlant_singularHomology₀Section_singularCohomologyMap_snd`), and pulled-back
classes have no slant products by classes of positive degree. Conversely a class `φ` whose slant
products by all classes of positive degree vanish is `pr₂^* (φ / [x₀])`
(`TopCat.singularCohomologyMap_snd_singularSlant_of_forall_ne_zero`), because slant products by
the homology of `X` detect the cohomology of `X × Y`
(`TopCat.eq_zero_of_forall_singularSlant_eq_zero_of_isIso`). So the image of
`pr₂^* : Hⁿ(Y; M) → Hⁿ(X × Y; M)` is cut out by the vanishing of these slant products
(`TopCat.mem_range_singularCohomologyMap_snd_iff`).

**Spheres.** For `X = Sᵈ⁺¹` the only homology of positive degree is `Hᵈ⁺¹(Sᵈ⁺¹; k) = k γ`, where
`γ` is the standard generator (`TauCeti.singularHomologyTopCatSphereGenerator`,
`TauCeti.exists_eq_smul_singularHomologyTopCatSphereGenerator`). Let `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; k)` be the
dual class (`TauCeti.singularCohomologyTopCatSphereGenerator`), with `⟨θ, γ⟩ = 1`
(`TauCeti.singularKronecker_singularCohomologyTopCatSphereGenerator`). Slanting
`pr₂^* b + pr₁^* θ ⌣ pr₂^* c` by `[x₀]` gives `b`
(`TopCat.singularSlant_singularHomology₀Section_singularCohomologyMap_snd_add_singularCup`), and
slanting it by `γ` gives `c` (`TopCat.singularSlant_singularCohomologyMap_snd_add_singularCup`).
Then:

* a class `φ ∈ Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` is pulled back from `Y` if and only if `φ / γ = 0`
  (`TopCat.mem_range_singularCohomologyMap_snd_sphere_iff`), and it is zero if moreover
  `φ / [x₀] = 0` (`TopCat.eq_zero_of_singularSlant_sphere_eq_zero`);
* every such class decomposes as `φ = pr₂^* (φ / [x₀]) + pr₁^* θ ⌣ pr₂^* (φ / γ)`
  (`TopCat.singularCohomologyMap_snd_add_singularCup_sphere`), and the two slant products give
  a `k`-linear equivalence `Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M) ≃ Hⁿ⁺ᵈ⁺¹(Y; M) × Hⁿ(Y; M)` whose inverse is
  `(b, c) ↦ pr₂^* b + pr₁^* θ ⌣ pr₂^* c` (`TopCat.singularCohomologySphereProdSlantEquiv`). This
  is the analogue, for an arbitrary coefficient module `M`, of the equivalence
  `TopCat.singularCohomologySphereProdEquiv` with coefficients in `k`.

**Cup products.** With coefficients `M = k`, the decomposition turns the cup product into a
multiplication table. The generator satisfies `θ ⌣ θ = 0`
(`TopCat.singularCup_singularCohomologyTopCatSphereGenerator_self`), so by the interchange law for
cross products (`TopCat.singularCup_singularCohomologyMap_snd_add_singularCup`), for
`b ∈ Hᵖ⁺ᵈ⁺¹(Y)` and `c ∈ Hᵖ(Y)`,
`(b, c) ⌣ (b', c') = (b ⌣ b', c ⌣ b' + (-1)^((d + 1)(p + d + 1)) b ⌣ c')`
(`TopCat.singularCohomologySphereProdSlantEquiv_singularCup`). On `H²(S¹ × Y)` the cup product
therefore pairs the summand pulled back from `Y` with the summand `θ ⌣ pr₂^* H¹(Y)`, which is
isotropic. When `Y` is a compact manifold whose dimension is below the degree of `b ⌣ b'`, the
component `b ⌣ b'` vanishes
(`TopCat.singularCohomologySphereProdSlantEquiv_singularCup_of_compactSpace`); for a closed
three-manifold `Y` the cup product on `H²(S¹ × Y)` is thus off-diagonal in the decomposition.

For the circle `S¹` (`d = 0`), with `k = M = ℤ` and `n = 1` this is the integral decomposition
`H²(S¹ × Y; ℤ) = pr₂^* H²(Y; ℤ) ⊕ (θ ⌣ pr₂^* H¹(Y; ℤ))` of the second cohomology of a product
with a circle, torsion included; `θ` generates `H¹(S¹; ℤ)`. Under `S¹ ≅ ℝ / ℤ`, `θ` corresponds
to `±[ds]` for the angular form `ds`, with the sign fixed by orientations; that identification is
not made here. Its cross quotient `H¹(Y; ℤ)` is torsion-free, which the following makes precise for
any coefficient change. A map `g : M ⟶ M'` of coefficient modules which is injective induces an
injective map `H¹(Y; M) → H¹(Y; M')`, because `H₀(Y; k)` is free and so
`H¹(Y; M) = Hom(H₁(Y; k), M)`
(`TopCat.injective_homologyMap_linearYonedaObjMap_one`). Since slant
products commute with coefficient changes (`TopCat.singularSlant_linearYonedaObjMap`), a class
`φ ∈ H¹⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` whose image in `H¹⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M')` is pulled back from `Y` is itself
pulled back from `Y` (`TopCat.mem_range_singularCohomologyMap_snd_sphere_one_add_of_injective`, the
case `n = 1` of `TopCat.mem_range_singularCohomologyMap_snd_sphere_of_injective`, which asks for
`g` to be injective on `Hⁿ(Y; -)`). For `d = 0` and `ℤ → ℝ`: an integral class of `H²(S¹ × Y)`
whose real class is pulled back from `Y` is pulled back from `Y` integrally.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B, the Künneth formulas.
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (slant products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

section Sphere

variable {M}

/-- **Classes of `Sᵈ⁺¹ × Y` pulled back from `Y`**: a class `φ ∈ Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` is pulled
back from `Y` if and only if its slant product `φ / γ` by the standard generator `γ` of
`Hᵈ⁺¹(Sᵈ⁺¹; k)` vanishes. -/
theorem mem_range_singularCohomologyMap_snd_sphere_iff (Y : TopCat.{w}) {d n : ℕ}
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
      (n + (d + 1))) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd (sphere.{w} (d + 1)) Y)
        (n + (d + 1))).hom ↔
      singularSlant k M (sphere.{w} (d + 1)) Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n
        (n + (d + 1)) (add_comm (d + 1) n)
        (TauCeti.singularHomologyTopCatSphereGenerator k d) φ = 0 := by
  rw [mem_range_singularCohomologyMap_snd_iff]
  refine ⟨fun hφ ↦ hφ _ _ _ _ d.succ_ne_zero, fun hφ p q h x hp ↦ ?_⟩
  obtain _ | p := p
  · exact absurd rfl hp
  obtain rfl | hpd := eq_or_ne p d
  · obtain rfl : q = n := by omega
    obtain ⟨r, rfl⟩ := TauCeti.exists_eq_smul_singularHomologyTopCatSphereGenerator k p x
    rw [map_smul, LinearMap.smul_apply, hφ, smul_zero]
  · -- the homology of the sphere vanishes in the other positive degrees
    have := ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularHomologyFunctor_topCatSphere_of_ne
        (𝟙_ (ModuleCat.{w} k)) (n := d + 1) (q := p) (by omega))
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

/-- **Classes of `Sᵈ⁺¹ × Y` are detected by two slant products**: for `x₀ ∈ Sᵈ⁺¹` and the
standard generator `γ` of `Hᵈ⁺¹(Sᵈ⁺¹; k)`, a class `φ ∈ Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` with
`φ / [x₀] = 0` and `φ / γ = 0` is zero. -/
theorem eq_zero_of_singularSlant_sphere_eq_zero (Y : TopCat.{w}) {d : ℕ}
    (x₀ : sphere.{w} (d + 1)) {n : ℕ}
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
      (n + (d + 1)))
    (h₀ : singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + (d + 1)) (n + (d + 1))
      (zero_add _) (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ = 0)
    (h₁ : singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n (n + (d + 1))
      (add_comm (d + 1) n) (TauCeti.singularHomologyTopCatSphereGenerator k d) φ = 0) :
    φ = 0 := by
  obtain ⟨b, rfl⟩ := (mem_range_singularCohomologyMap_snd_sphere_iff Y φ).2 h₁
  rw [singularSlant_singularHomology₀Section_singularCohomologyMap_snd] at h₀
  rw [h₀, map_zero]

variable (M)

/-- **The decomposition of the cohomology of `Sᵈ⁺¹ × Y`**: for `x₀ ∈ Sᵈ⁺¹`, the standard
generator `γ` of `Hᵈ⁺¹(Sᵈ⁺¹; k)` and the dual class `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; k)`, `⟨θ, γ⟩ = 1`, every
`φ ∈ Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` is `pr₂^* (φ / [x₀]) + pr₁^* θ ⌣ pr₂^* (φ / γ)`. -/
theorem singularCohomologyMap_snd_add_singularCup_sphere (Y : TopCat.{w}) {d : ℕ}
    (x₀ : sphere.{w} (d + 1)) {n : ℕ}
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
      (n + (d + 1))) :
    TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (n + (d + 1))
        (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + (d + 1)) (n + (d + 1))
          (zero_add _) (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ) +
      (sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        (d + 1) n (n + (d + 1)) (add_comm (d + 1) n)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
          (TauCeti.singularCohomologyTopCatSphereGenerator k d))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n
          (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n (n + (d + 1))
            (add_comm (d + 1) n) (TauCeti.singularHomologyTopCatSphereGenerator k d) φ)) = φ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_singularSlant_sphere_eq_zero Y x₀ _ ?_ ?_
  · rw [map_sub, singularSlant_singularHomology₀Section_singularCohomologyMap_snd_add_singularCup
      M _ Y x₀ _ d.succ_ne_zero, sub_self]
  · rw [map_sub, singularSlant_singularCohomologyMap_snd_add_singularCup M _ Y _ d.succ_ne_zero,
      TauCeti.singularKronecker_singularCohomologyTopCatSphereGenerator, one_smul, sub_self]

/-- **The cohomology of `Sᵈ⁺¹ × Y`**: for `x₀ ∈ Sᵈ⁺¹`, the slant products by the class of `x₀`
and by the standard generator `γ` of `Hᵈ⁺¹(Sᵈ⁺¹; k)` give a `k`-linear equivalence
`Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M) ≃ Hⁿ⁺ᵈ⁺¹(Y; M) × Hⁿ(Y; M)`. Its inverse sends `(b, c)` to
`pr₂^* b + pr₁^* θ ⌣ pr₂^* c`, where `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; k)` is dual to `γ`
(`TopCat.singularCohomologyMap_snd_add_singularCup_sphere`). -/
def singularCohomologySphereProdSlantEquiv (Y : TopCat.{w}) {d : ℕ} (x₀ : sphere.{w} (d + 1))
    (n : ℕ) :
    (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
        (n + (d + 1)) ≃ₗ[k]
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n where
  toFun φ :=
    (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + (d + 1)) (n + (d + 1))
        (zero_add _) (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ,
      singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n (n + (d + 1))
        (add_comm (d + 1) n) (TauCeti.singularHomologyTopCatSphereGenerator k d) φ)
  map_add' φ ψ := by simp
  map_smul' r φ := by simp
  invFun bc :=
    TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (n + (d + 1)) bc.1 +
      (sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        (d + 1) n (n + (d + 1)) (add_comm (d + 1) n)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
          (TauCeti.singularCohomologyTopCatSphereGenerator k d))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n bc.2)
  left_inv φ := singularCohomologyMap_snd_add_singularCup_sphere M Y x₀ φ
  right_inv bc := Prod.ext
    (singularSlant_singularHomology₀Section_singularCohomologyMap_snd_add_singularCup M _ Y x₀ _
      d.succ_ne_zero _ _ _)
    ((singularSlant_singularCohomologyMap_snd_add_singularCup M _ Y _ d.succ_ne_zero _ _ _
      _).trans (by rw [TauCeti.singularKronecker_singularCohomologyTopCatSphereGenerator,
        one_smul]))

/-- The decomposition of `Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` records the slant products by the class of `x₀`
and by the standard generator of `Hᵈ⁺¹(Sᵈ⁺¹; k)`. -/
@[simp]
lemma singularCohomologySphereProdSlantEquiv_apply (Y : TopCat.{w}) {d : ℕ}
    (x₀ : sphere.{w} (d + 1)) (n : ℕ)
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
      (n + (d + 1))) :
    singularCohomologySphereProdSlantEquiv M Y x₀ n φ =
      (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + (d + 1)) (n + (d + 1))
          (zero_add _) (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ,
        singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n (n + (d + 1))
          (add_comm (d + 1) n) (TauCeti.singularHomologyTopCatSphereGenerator k d) φ) :=
  (rfl)

/-- The inverse of the decomposition of `Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` sends `(b, c)` to
`pr₂^* b + pr₁^* θ ⌣ pr₂^* c`. -/
@[simp]
lemma singularCohomologySphereProdSlantEquiv_symm_apply (Y : TopCat.{w}) {d : ℕ}
    (x₀ : sphere.{w} (d + 1)) (n : ℕ)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    (singularCohomologySphereProdSlantEquiv M Y x₀ n).symm bc =
      TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (n + (d + 1)) bc.1 +
        (sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n (n + (d + 1)) (add_comm (d + 1) n)
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
            (TauCeti.singularCohomologyTopCatSphereGenerator k d))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n bc.2) :=
  (rfl)

end Sphere

section Coefficients

variable {M}

/-- **Pulled-back classes of `Sᵈ⁺¹ × Y` under a change of coefficients**: let `g : M ⟶ M'` induce
an injective map `Hⁿ(Y; M) → Hⁿ(Y; M')`. If the image of `φ ∈ Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` in
`Hⁿ⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M')` is pulled back from `Y`, then so is `φ`. -/
theorem mem_range_singularCohomologyMap_snd_sphere_of_injective (Y : TopCat.{w}) {d n : ℕ}
    {M' : ModuleCat.{w} k} (g : M ⟶ M')
    (hg : Function.Injective (homologyMap (((toSSet.obj Y).chainComplex
      (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n))
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
      (n + (d + 1)))
    (hφ : homologyMap (((toSSet.obj (sphere.{w} (d + 1) ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) (n + (d + 1)) φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd (sphere.{w} (d + 1)) Y)
        (n + (d + 1))).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd (sphere.{w} (d + 1)) Y)
        (n + (d + 1))).hom := by
  rw [mem_range_singularCohomologyMap_snd_sphere_iff, singularSlant_linearYonedaObjMap] at hφ
  rw [mem_range_singularCohomologyMap_snd_sphere_iff]
  exact hg (hφ.trans (map_zero _).symm)

/-- **Classes of `Sᵈ⁺¹ × Y` pulled back after an injective change of coefficients**: if
`g : M ⟶ M'` is injective and the image of `φ ∈ H¹⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M)` in `H¹⁺ᵈ⁺¹(Sᵈ⁺¹ × Y; M')` is
pulled back from `Y`, then so is `φ`. For `d = 0` and `ℤ → ℝ`: an integral class of `H²(S¹ × Y)`
whose real class is pulled back from `Y` is pulled back from `Y` integrally, because the cross
quotient `H¹(Y; ℤ)` is torsion-free. -/
theorem mem_range_singularCohomologyMap_snd_sphere_one_add_of_injective (Y : TopCat.{w})
    {d : ℕ} {M' : ModuleCat.{w} k} (g : M ⟶ M') (hg : Function.Injective g)
    (φ : (sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M
      (1 + (d + 1)))
    (hφ : homologyMap (((toSSet.obj (sphere.{w} (d + 1) ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) (1 + (d + 1)) φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd (sphere.{w} (d + 1)) Y)
        (1 + (d + 1))).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd (sphere.{w} (d + 1)) Y)
        (1 + (d + 1))).hom := by
  have : Module.Free k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Free k k)
  exact mem_range_singularCohomologyMap_snd_sphere_of_injective (n := 1) Y g
    (Y.injective_homologyMap_linearYonedaObjMap_one g hg) φ hφ

end Coefficients

section Cup

/-- **The cup product on `Sᵈ⁺¹ × Y` in the slant decomposition**: with coefficients in a
commutative ring `k`, write classes of `Sᵈ⁺¹ × Y` as `(b, c) = pr₂^* b + pr₁^* θ ⌣ pr₂^* c` through
`TopCat.singularCohomologySphereProdSlantEquiv`. Then for `b ∈ Hᵖ⁺ᵈ⁺¹(Y)`, `c ∈ Hᵖ(Y)`,
`b' ∈ H^(q+d+1)(Y)` and `c' ∈ H^q(Y)`,

`(b, c) ⌣ (b', c') = (b ⌣ b', c ⌣ b' + (-1)^((d + 1)(p + d + 1)) b ⌣ c')`.

For `d = 0` and `p = q = 1` this is the cup product `H²(S¹ × Y) × H²(S¹ × Y) → H⁴(S¹ × Y)`: the
summands `pr₂^* H²(Y)` and `pr₁^* θ ⌣ pr₂^* H¹(Y)` are paired by `(b, c') ↦ b ⌣ c' ∈ H³(Y)`, the
second summand is isotropic, and the first is isotropic whenever `H⁴(Y) = 0`, for instance when
`Y` is a closed three-manifold (`TauCeti.isZero_singularCohomology_of_compactSpace`). -/
theorem singularCohomologySphereProdSlantEquiv_singularCup {d : ℕ}
    (x₀ : TopCat.sphere.{w} (d + 1)) (p q : ℕ)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (p + (d + 1)) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (bc' : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (q + (d + 1)) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) Y x₀ (p + q + (d + 1))
        ((TopCat.sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ _).inv (λ_ _).hom (p + (d + 1))
          (q + (d + 1)) (p + q + (d + 1) + (d + 1)) (by omega)
          ((singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) Y x₀ p).symm bc)
          ((singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) Y x₀ q).symm bc')) =
      (Y.singularCup k (λ_ _).inv (λ_ _).hom (p + (d + 1)) (q + (d + 1))
          (p + q + (d + 1) + (d + 1)) (by omega) bc.1 bc'.1,
        Y.singularCup k (λ_ _).inv (λ_ _).hom p (q + (d + 1)) (p + q + (d + 1)) (by omega)
            bc.2 bc'.1 +
          ((-1 : ℤ) ^ ((d + 1) * (p + (d + 1)))) •
            Y.singularCup k (λ_ _).inv (λ_ _).hom (p + (d + 1)) q (p + q + (d + 1)) (by omega)
              bc.1 bc'.2) := by
  rw [← LinearEquiv.eq_symm_apply, singularCohomologySphereProdSlantEquiv_symm_apply,
    singularCohomologySphereProdSlantEquiv_symm_apply,
    singularCohomologySphereProdSlantEquiv_symm_apply]
  exact singularCup_singularCohomologyMap_snd_add_singularCup (add_comm (d + 1) p)
    (add_comm (d + 1) q) _ (add_comm (d + 1) _) _
    (singularCup_singularCohomologyTopCatSphereGenerator_self d) _ _ _ _

/-- **The cup product on `Sᵈ⁺¹ × Y` for a compact manifold `Y`**: if `Y` is a compact manifold of
dimension `n` and the cup product lands above degree `n`, its component pulled back from
`Y` vanishes, so in the slant decomposition
`(b, c) ⌣ (b', c') = (0, c ⌣ b' + (-1)^((d + 1)(p + d + 1)) b ⌣ c')`. Here `k` is a commutative
ring over which every module has projective dimension at most one, such as `ℤ` or a field. For a
closed three-manifold `Y`, `d = 0` and `p = q = 1`, this says that the cup product
`H²(S¹ × Y) × H²(S¹ × Y) → H⁴(S¹ × Y) ≅ H³(Y)` is off-diagonal: it vanishes on each of the
summands `pr₂^* H²(Y)` and `θ ⌣ pr₂^* H¹(Y)` and pairs them by `(b, c') ↦ b ⌣ c'`. -/
theorem singularCohomologySphereProdSlantEquiv_singularCup_of_compactSpace
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] {M E : Type w} [TopologicalSpace M]
    [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] [CompactSpace M] {d : ℕ} (x₀ : TopCat.sphere.{w} (d + 1)) {n p q : ℕ}
    (hn : Module.finrank ℝ E = n) (hpq : n < p + q + (d + 1) + (d + 1))
    (bc : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        (p + (d + 1)) ×
      (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (bc' : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        (q + (d + 1)) ×
      (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) (TopCat.of M) x₀
        (p + q + (d + 1))
        ((TopCat.sphere.{w} (d + 1) ⊗ TopCat.of M).singularCup k (λ_ _).inv (λ_ _).hom
          (p + (d + 1)) (q + (d + 1)) (p + q + (d + 1) + (d + 1)) (by omega)
          ((singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) _ x₀ p).symm bc)
          ((singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) _ x₀ q).symm bc')) =
      (0, (TopCat.of M).singularCup k (λ_ _).inv (λ_ _).hom p (q + (d + 1)) (p + q + (d + 1))
            (by omega) bc.2 bc'.1 +
          ((-1 : ℤ) ^ ((d + 1) * (p + (d + 1)))) •
            (TopCat.of M).singularCup k (λ_ _).inv (λ_ _).hom (p + (d + 1)) q (p + q + (d + 1))
              (by omega) bc.1 bc'.2) := by
  have : Module.Projective k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Projective k k)
  have := ModuleCat.subsingleton_of_isZero (TauCeti.isZero_singularCohomology_of_compactSpace
    (M := M) (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) hn hpq)
  rw [singularCohomologySphereProdSlantEquiv_singularCup]
  exact Prod.ext (Subsingleton.elim _ _) rfl

end Cup

end TopCat
