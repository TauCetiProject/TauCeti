/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Slant
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# Pulled-back classes on a product under a change of coefficients

Let `X` be a path-connected space whose singular homology `Hₚ(X; k)` is projective in every
degree, over a commutative ring `k`, for instance a sphere or a torus over `ℤ`. For every space
`Y`, a class `φ ∈ Hⁿ(X × Y; M)` is pulled back along the projection `pr₂ : X × Y ⟶ Y` exactly when
its slant products `φ / x ∈ H^q(Y; M)` by the classes `x ∈ Hₚ(X; k)` with `p ≠ 0` vanish
(`TopCat.mem_range_singularCohomologyMap_snd_iff`). These slant products lie in degrees `q < n`,
and they commute with a change of coefficients `g : M ⟶ M'`
(`TopCat.singularSlant_linearYonedaObjMap`). Hence, if `g` is injective on `H^q(Y; -)` for
`q < n`, a class whose image under `g` is pulled back from `Y` is itself pulled back from `Y`
(`TopCat.mem_range_singularCohomologyMap_snd_of_injective`).

An injective map `g` of coefficient modules is injective on `H^q(Y; -)` when `Hⱼ(Y; k)` is
projective for `j < q`
(`TopCat.injective_homologyMap_linearYonedaObjMap_of_projective_homology_lt`).
As `H₀(Y; k)` is free, this holds for `q ≤ 1` and every space `Y`. So the descent holds for
injective `g` whenever `Hⱼ(Y; k)` is projective for `j + 2 ≤ n`
(`TopCat.mem_range_singularCohomologyMap_snd_of_projective_homology`), in particular in degrees
`n ≤ 2` for every space `Y` (`TopCat.mem_range_singularCohomologyMap_snd_of_le_two`). For
`g : ℤ ⟶ ℝ` and `n = 2`: an integral class on `X × Y` whose real image is pulled back from `Y` is
the pullback of an integral class of `Y`, torsion included. The bound `n ≤ 2` is sharp: for a
nonzero torsion class `t ∈ H²(Y; ℤ)` and the generator `u ∈ H¹(S¹; ℤ)`, the cross product
`u × t ∈ H³(S¹ × Y; ℤ)` has real image zero but slant product `t` by the fundamental class of
`S¹`, so it is not pulled back from `Y`. For spheres the slant products by positive-degree classes
lie in a single degree, which gives the sharper
`TopCat.mem_range_singularCohomologyMap_snd_sphere_of_injective`.

Applied to the coefficient map `r • 𝟙 : M ⟶ M`, which acts on cohomology as multiplication by `r`
(`ChainComplex.linearYonedaObjMap_smul`), the descent says that in degrees `n ≤ 2` a class
`φ` with `r • φ` pulled back from `Y` is pulled back from `Y`, as soon as `r` is `M`-regular
(`TopCat.mem_range_singularCohomologyMap_snd_of_smul_mem`). Hence if `ψ` is pulled back from
`Y` and the image of `ψ + r • φ` under an injective coefficient map is pulled back from `Y`, so
is `φ` (`TopCat.mem_range_singularCohomologyMap_snd_of_add_smul_mem_of_injective`). On `S¹ × Y`, a
`Spinᶜ` structure `s₀ ⊗ E` twisted by a Hermitian line `E` from a reference `s₀` pulled back from
`Y` has determinant class `l = l₀ + 2 c₁(E)` with `l₀` pulled back from `Y`. If the real class of
`l` is pulled back from `Y`, then the integral class `c₁(E)` is pulled back from `Y`, two-torsion
included.

## Main results

* `TopCat.mem_range_singularCohomologyMap_snd_of_injective`: descent along a coefficient map
  that is injective on `H^q(Y; -)` for `q < n`.
* `TopCat.mem_range_singularCohomologyMap_snd_of_projective_homology`: descent along an injective
  coefficient map when `Hⱼ(Y; k)` is projective for `j + 2 ≤ n`.
* `TopCat.mem_range_singularCohomologyMap_snd_of_le_two`: descent along an injective coefficient
  map in degrees `n ≤ 2`, for every space `Y`.
* `TopCat.mem_range_singularCohomologyMap_snd_of_smul_mem`: in degrees `n ≤ 2`, a class whose
  multiple by an `M`-regular scalar is pulled back is itself pulled back.
* `TopCat.mem_range_singularCohomologyMap_snd_of_add_smul_mem_of_injective`: if `ψ` is pulled back
  and the image of `ψ + r • φ` under an injective coefficient map is pulled back, then `φ` is
  pulled back.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B (the Künneth formula), Section 3.1 (universal coefficients).
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k] (X Y : TopCat.{w}) [PathConnectedSpace X]
  [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
    (𝟙_ (ModuleCat.{w} k))).obj X)]
  {M M' : ModuleCat.{w} k}

/-- **Pulled-back classes descend along a change of coefficients**: let `X` be path-connected with
projective singular homology `Hₚ(X; k)`, and let `g : M ⟶ M'` induce injective maps
`H^q(Y; M) → H^q(Y; M')` for `q < n`. If the image of `φ ∈ Hⁿ(X × Y; M)` in `Hⁿ(X × Y; M')` is
pulled back from `Y`, then so is `φ`: the slant products of `φ` by classes of positive degree lie
in degrees `q < n`, and they vanish because their images under `g` do. -/
theorem mem_range_singularCohomologyMap_snd_of_injective {n : ℕ} (g : M ⟶ M')
    (hg : ∀ q < n, Function.Injective (homologyMap (((toSSet.obj Y).chainComplex
      (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) q))
    (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n)
    (hφ : homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd X Y) n).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd X Y) n).hom := by
  rw [mem_range_singularCohomologyMap_snd_iff] at hφ ⊢
  intro p q h x hp
  have hgx := hφ p q h x hp
  rw [singularSlant_linearYonedaObjMap] at hgx
  exact hg q (by omega) (hgx.trans (map_zero _).symm)

/-- **Pulled-back classes descend along injective coefficient maps**: let `X` be path-connected
with projective singular homology `Hₚ(X; k)`, let `g : M ⟶ M'` be injective, and let `Hⱼ(Y; k)`
be projective for `j + 2 ≤ n`. If the image of `φ ∈ Hⁿ(X × Y; M)` in `Hⁿ(X × Y; M')` is pulled
back from `Y`, then so is `φ`. -/
theorem mem_range_singularCohomologyMap_snd_of_projective_homology {n : ℕ} (g : M ⟶ M')
    (hg : Function.Injective g)
    (hY : ∀ j, j + 2 ≤ n → Projective (((singularHomologyFunctor (ModuleCat.{w} k) j).obj
      (𝟙_ (ModuleCat.{w} k))).obj Y))
    (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n)
    (hφ : homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd X Y) n).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd X Y) n).hom := by
  have : Module.Free k (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Module.Free k k)
  exact mem_range_singularCohomologyMap_snd_of_injective X Y g (fun q hq ↦
    Y.injective_homologyMap_linearYonedaObjMap_of_projective_homology_lt g hg q fun j hj ↦
      hY j (by omega)) φ hφ

/-- **Pulled-back classes of degree at most two descend along injective coefficient maps**: let
`X` be path-connected with projective singular homology `Hₚ(X; k)`, for instance `X = S¹`, and let
`g : M ⟶ M'` be injective. If `n ≤ 2` and the image of `φ ∈ Hⁿ(X × Y; M)` in `Hⁿ(X × Y; M')` is
pulled back from `Y`, then so is `φ`, for every space `Y`. For `g : ℤ ⟶ ℝ` and `n = 2`: an
integral class on `X × Y` whose real image is pulled back from `Y` is the pullback of an integral
class of `Y`. In degree `3` torsion classes of `H²(Y; ℤ)` give counterexamples. -/
theorem mem_range_singularCohomologyMap_snd_of_le_two {n : ℕ} (hn : n ≤ 2) (g : M ⟶ M')
    (hg : Function.Injective g)
    (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n)
    (hφ : homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd X Y) n).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd X Y) n).hom :=
  mem_range_singularCohomologyMap_snd_of_projective_homology X Y g hg (fun j hj ↦ by
    -- only `H₀(Y; k)` is involved, and it is free
    obtain rfl : j = 0 := by omega
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis k _)) φ hφ

/-- **Classes of degree at most two whose multiples are pulled back**: let `X` be path-connected
with projective singular homology `Hₚ(X; k)`, and let `r` be `M`-regular, that is,
`r • · : M → M` injective. If `n ≤ 2` and `r • φ` is pulled back from `Y` for
`φ ∈ Hⁿ(X × Y; M)`, then so is `φ`. For `X = S¹`, `M = ℤ` and `r = 2`: an integral class of
`H²(S¹ × Y)` whose double is pulled back from `Y` is itself pulled back, two-torsion included,
because the cross quotient `H¹(Y; ℤ)` has no two-torsion. -/
theorem mem_range_singularCohomologyMap_snd_of_smul_mem {n : ℕ} (hn : n ≤ 2) {r : k}
    (hr : IsSMulRegular M r)
    {φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n}
    (hφ : r • φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k))
      (k := k) (M := M) (CartesianMonoidalCategory.snd X Y) n).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd X Y) n).hom := by
  refine mem_range_singularCohomologyMap_snd_of_le_two X Y hn (r • 𝟙 M) hr φ ?_
  -- the coefficient map `r • 𝟙` acts on cohomology as multiplication by `r`
  rwa [ChainComplex.linearYonedaObjMap_smul, ChainComplex.linearYonedaObjMap_id,
    HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id]

/-- **A class is pulled back if a pulled-back class plus a multiple of it is pulled back after a
change of coefficients**: let `X` be path-connected with projective singular homology
`Hₚ(X; k)`, let `r` be `M`-regular, let `g : M ⟶ M'` be injective, and let `n ≤ 2`. If
`ψ ∈ Hⁿ(X × Y; M)` is pulled back from `Y`, and the image of `ψ + r • φ` in `Hⁿ(X × Y; M')` is
pulled back from `Y`, then `φ` is pulled back from `Y`. For `X = S¹`, `g : ℤ ⟶ ℝ` and `r = 2`:
if the real determinant class `l = l₀ + 2 c₁(E)` of a `Spinᶜ` structure `s₀ ⊗ E` on `S¹ × Y`,
with `l₀` pulled back from `Y`, is pulled back from `Y`, then the integral class `c₁(E)` is
pulled back from `Y`, two-torsion included. -/
theorem mem_range_singularCohomologyMap_snd_of_add_smul_mem_of_injective {n : ℕ} (hn : n ≤ 2)
    {r : k} (hr : IsSMulRegular M r) (g : M ⟶ M') (hg : Function.Injective g)
    {ψ φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n}
    (hψ : ψ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k))
      (k := k) (M := M) (CartesianMonoidalCategory.snd X Y) n).hom)
    (h : homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n (ψ + r • φ) ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd X Y) n).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd X Y) n).hom :=
  mem_range_singularCohomologyMap_snd_of_smul_mem X Y hn hr (by
    simpa using Submodule.sub_mem _ (mem_range_singularCohomologyMap_snd_of_le_two X Y hn g hg _ h)
      hψ)

end TopCat
