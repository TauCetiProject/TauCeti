/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Slant
public import TauCeti.AlgebraicTopology.Cohomology.Sphere
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.Disk

/-!
# Classes pulled back from a factor, and the cohomology of `S¹ × Y`

Let `k` be a commutative ring and `M` a `k`-module, and write `Hⁿ(Z; M)` for the singular
cohomology of `Z` with coefficients in `M`, computed from the singular chains with coefficients in
`k`. For spaces `X` and `Y`, slant products by the homology of `X` turn classes on `X × Y` into
classes on `Y` (`TopCat.singularSlant`); here they are taken along the multiplication
`k ⊗ k ≅ k`, so that they act on `Hⁿ(X × Y; M)`.

**Classes pulled back from `Y`.** Let `X` be path-connected with projective homology `Hₚ(X; k)`,
and `x₀ ∈ X`. Slanting by the class of the point `x₀` recovers a class pulled back from `Y`,
`pr₂^* b / [x₀] = b` (`TopCat.singularSlant_singularHomology₀Section_singularCohomologyMap_snd`),
and pulled-back classes have no slant products by classes of positive degree. Conversely a class
`φ` whose slant products by all classes of positive degree vanish is `pr₂^* (φ / [x₀])`
(`TopCat.singularCohomologyMap_snd_singularSlant_of_forall_ne_zero`), because slant products by
the homology of `X` detect the cohomology of `X × Y`
(`TopCat.eq_zero_of_forall_singularSlant_eq_zero_of_isIso`). So the image of
`pr₂^* : Hⁿ(Y; M) → Hⁿ(X × Y; M)` is cut out by the vanishing of these slant products
(`TopCat.mem_range_singularCohomologyMap_snd_iff`).

**The circle.** For `X = S¹` the only homology of positive degree is `H₁(S¹; k) = k γ`, where `γ`
is the standard generator (`TauCeti.reducedSingularHomologyTopCatSphereIso`). Let
`θ ∈ H¹(S¹; k)` be the dual class, `⟨θ, γ⟩ = 1`
(`TauCeti.singularCohomologyTopCatSphereEquiv`). Then:

* a class `φ ∈ Hⁿ⁺¹(S¹ × Y; M)` is pulled back from `Y` if and only if `φ / γ = 0`
  (`TopCat.mem_range_singularCohomologyMap_snd_sphere_iff`);
* every such class decomposes as `φ = pr₂^* (φ / [x₀]) + pr₁^* θ ⌣ pr₂^* (φ / γ)`
  (`TopCat.singularCohomologyMap_snd_add_singularCup_sphere`), and the two slant products give
  a `k`-linear equivalence
  `Hⁿ⁺¹(S¹ × Y; M) ≃ Hⁿ⁺¹(Y; M) × Hⁿ(Y; M)` whose inverse is `(b, c) ↦ pr₂^* b + pr₁^* θ ⌣ pr₂^* c`
  (`TopCat.singularCohomologySphereOneProdEquiv`).

With `k = M = ℤ` and `n = 1` this is the integral decomposition
`H²(S¹ × Y; ℤ) = pr₂^* H²(Y; ℤ) ⊕ (θ ⌣ pr₂^* H¹(Y; ℤ))` of the second cohomology of a product
with a circle, torsion included; `θ` generates `H¹(S¹; ℤ)`, the class of the angular form `ds` on
`ℝ / ℤ`. Its cross quotient `H¹(Y; ℤ)` is torsion-free, which the following makes precise for
any coefficient change. A map `g : M ⟶ M'` of coefficient modules which is injective induces an
injective map `H¹(Y; M) → H¹(Y; M')`, because `H₀(Y; k)` is free and so
`H¹(Y; M) = Hom(H₁(Y; k), M)`
(`TopCat.injective_homologyMap_linearYonedaObjMap_of_projective_homology_lt`). Since slant
products commute with coefficient changes (`TopCat.singularSlant_coefficient_naturality`), a class
`φ ∈ H²(S¹ × Y; M)` whose image in `H²(S¹ × Y; M')` is pulled back from `Y` is itself pulled back
from `Y` (`TopCat.mem_range_singularCohomologyMap_snd_sphere_two_of_injective`). For
`ℤ → ℝ`: an integral class of `S¹ × Y` whose real class is pulled back from `Y` is pulled back from
`Y` integrally.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B, the Künneth formulas.
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (slant products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TauCeti

/-- On a path-connected space, every class of `H₀(X; k)` is a multiple of the class of a point,
the multiple being its augmentation. -/
theorem eq_smul_singularHomology₀Section {k : Type w} [CommRing k] {X : TopCat.{w}}
    [PathConnectedSpace X] (x₀ : X)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    x = (X.singularHomology₀ε (𝟙_ (ModuleCat.{w} k)) x : k) •
      singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k) := by
  rw [← map_smul, smul_eq_mul, mul_one, ← ConcreteCategory.comp_apply,
    singularHomology₀ε_singularHomology₀Section, ConcreteCategory.id_apply]

end TauCeti

namespace TopCat

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

section PullbackFromFactor

/-- **Slanting a class pulled back from `Y` by a point of `X` returns it**:
`pr₂^* b / [x] = b`, for the class `[x] ∈ H₀(X; k)` of a point and the slant product along the
multiplication `k ⊗ k ≅ k`. -/
theorem singularSlant_singularHomology₀Section_singularCohomologyMap_snd (X Y : TopCat.{w})
    (x : X) (q : ℕ) (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M q) :
    singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 q q (zero_add q)
        (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x (1 : k))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b) = b := by
  -- the class of `x` is that of the singular `0`-cycle `x` with coefficient `1`
  have hx : TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x (1 : k) =
      ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ 0
        (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).liftCycles
          ((toSSet.obj X).ιChainComplex (toSSetObj₀Equiv.symm x)) 0 (by simp) (by simp)
          (1 : k)) := by
    rw [TauCeti.singularHomology₀Section_def, SSet.ιHomology₀_def]
    -- `ConcreteCategory.comp_apply` does not match here: the target of `homologyπ` is the
    -- singular homology object only after unfolding `singularHomologyFunctor`
    rfl
  rw [hx]
  exact singularSlant_homologyπ_singularCohomologyMap_snd_eq_self M X Y _ q _
    (toSSetObj₀Equiv.symm x) (1 : k)
    (by rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]) (fun s ↦ by simp) b

variable {M}

/-- **A class with no slant products in positive degree is pulled back**: let `X` be
path-connected with projective homology and `x₀ ∈ X`. If `φ ∈ Hⁿ(X × Y; M)` has `φ / x = 0` for
every class `x ∈ Hₚ(X; k)` with `p ≠ 0`, then `φ = pr₂^* (φ / [x₀])`. -/
theorem singularCohomologyMap_snd_singularSlant_of_forall_ne_zero (X Y : TopCat.{w})
    [PathConnectedSpace X]
    [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)]
    (x₀ : X) {n : ℕ} (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n)
    (hφ : ∀ p q (h : p + q = n)
      (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X),
      p ≠ 0 → singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h x φ = 0) :
    TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n
        (singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 n n (zero_add n)
          (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ) = φ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_singularSlant_eq_zero_of_isIso M X Y (λ_ _).hom _ fun p q h x ↦ ?_
  rw [map_sub]
  rcases p with _ | p
  · -- `x` is a multiple of the class of `x₀`
    obtain rfl : q = n := by omega
    rw [TauCeti.eq_smul_singularHomology₀Section x₀ x, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, singularSlant_singularHomology₀Section_singularCohomologyMap_snd,
      sub_self]
  · rw [hφ _ _ _ _ (Nat.succ_ne_zero p), singularSlant_singularCohomologyMap_snd_eq_zero _ _ _ _ _
      _ _ _ (Nat.succ_ne_zero p), sub_zero]

/-- **Classes pulled back from the second factor**: for `X` path-connected with projective
homology, a class `φ ∈ Hⁿ(X × Y; M)` is pulled back from `Y` if and only if its slant products by
all classes of `Hₚ(X; k)` with `p ≠ 0` vanish. -/
theorem mem_range_singularCohomologyMap_snd_iff (X Y : TopCat.{w}) [PathConnectedSpace X]
    [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)]
    {n : ℕ} (φ : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd X Y) n).hom ↔
      ∀ p q (h : p + q = n)
        (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X),
        p ≠ 0 → singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h x φ = 0 := by
  refine ⟨?_, fun hφ ↦ ?_⟩
  · rintro ⟨b, rfl⟩ p q h x hp
    exact singularSlant_singularCohomologyMap_snd_eq_zero M X Y _ p q n h hp x b
  · obtain ⟨x₀⟩ : Nonempty X := inferInstance
    exact ⟨_, singularCohomologyMap_snd_singularSlant_of_forall_ne_zero X Y x₀ φ hφ⟩

variable (M)

/-- **The slant product of a cup product of pulled-back classes**: for `a ∈ Hᵖ(X; k)` and
`b ∈ H^q(Y; M)`, the slant product of `pr₁^* a ⌣ pr₂^* b ∈ Hⁿ(X × Y; M)` along `k ⊗ k ≅ k` is the
slant product of the cross product `a × b`, which `TopCat.singularSlant_singularCross_leftUnitor`
and `TopCat.singularSlant_singularCross_of_ne` compute. -/
theorem singularSlant_singularCup_singularCohomologyMap_fst_snd (X Y : TopCat.{w})
    {p q n : ℕ} (h : p + q = n)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M q) {p' q' : ℕ} (h' : p' + q' = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p').obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom p' q' n h' x
        ((X ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom p q n h
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst X Y) p a)
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b)) =
      singularSlant k M X Y (𝟙 _) p' q' n h' x
        (TauCeti.singularCross k X Y (λ_ M).hom p q n h a b) := by
  -- the cup product along `k ≅ k ⊗ k` is the cross product with its chain coefficients changed
  -- along that isomorphism, and slanting along `k ⊗ k ≅ k` undoes the change
  have hcup := singularCup_comp k (X ⊗ Y) (λ_ (𝟙_ (ModuleCat.{w} k))).inv (𝟙 _)
    (λ_ M).hom p q n h (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst X Y) p a)
    (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b)
  rw [Category.comp_id] at hcup
  rw [hcup, ← TauCeti.singularCross_eq_singularCup, ← singularSlant_comp, Iso.hom_inv_id]

end PullbackFromFactor

section Circle

/-- Every class of `H₁(S¹; k)` is a multiple of the standard generator. -/
theorem exists_eq_smul_singularHomology_sphere_one
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) 1).obj (𝟙_ (ModuleCat.{w} k))).obj
      (TopCat.sphere.{w} 1)) :
    ∃ r : k, x = r • (TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app
      (TopCat.sphere 1)
        ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
          (1 : k)) := by
  let E := ((TauCeti.reducedSingularHomologySuccIso (𝟙_ (ModuleCat.{w} k)) 0).app
      (TopCat.sphere.{w} 1)).symm ≪≫
    TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1
  refine ⟨E.hom x, ?_⟩
  have h1 : E.inv (E.hom x) = x := by simp
  have h2 : E.hom x = (E.hom x : k) • (1 : k) := by rw [smul_eq_mul, mul_one]
  rw [h2, map_smul] at h1
  refine h1.symm.trans (congrArg (E.hom x • ·) ?_)
  simp [E]

variable {M}

/-- **Classes of `S¹ × Y` pulled back from `Y`**: a class `φ ∈ Hⁿ⁺¹(S¹ × Y; M)` is pulled back
from `Y` if and only if its slant product `φ / γ` by the standard generator `γ` of `H₁(S¹; k)`
vanishes. -/
theorem mem_range_singularCohomologyMap_snd_sphere_iff (Y : TopCat.{w}) {n : ℕ}
    (φ : (TopCat.sphere.{w} 1 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1)) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd (TopCat.sphere.{w} 1) Y) (n + 1)).hom ↔
      singularSlant k M (TopCat.sphere.{w} 1) Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 1 n (n + 1)
        (add_comm 1 n)
        ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app (TopCat.sphere 1)
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
            (1 : k))) φ = 0 := by
  have : PathConnectedSpace (TopCat.sphere.{w} 1) :=
    TauCeti.TopCat.pathConnectedSpace_diskBoundary (by norm_num)
  rw [mem_range_singularCohomologyMap_snd_iff]
  refine ⟨fun hφ ↦ hφ _ _ _ _ one_ne_zero, fun hφ p q h x hp ↦ ?_⟩
  obtain _ | _ | p := p
  · exact absurd rfl hp
  · obtain rfl : q = n := by omega
    obtain ⟨r, rfl⟩ := exists_eq_smul_singularHomology_sphere_one x
    rw [map_smul, LinearMap.smul_apply, hφ, smul_zero]
  · have := ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularHomologyFunctor_topCatSphere_of_ne
        (𝟙_ (ModuleCat.{w} k)) (n := 1) (q := p + 1) (by omega))
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

variable (M)

/-- **The decomposition of the cohomology of `S¹ × Y`**: for `x₀ ∈ S¹`, the standard generator
`γ` of `H₁(S¹; k)` and the dual class `θ ∈ H¹(S¹; k)`, `⟨θ, γ⟩ = 1`, every
`φ ∈ Hⁿ⁺¹(S¹ × Y; M)` is `pr₂^* (φ / [x₀]) + pr₁^* θ ⌣ pr₂^* (φ / γ)`. -/
theorem singularCohomologyMap_snd_add_singularCup_sphere (Y : TopCat.{w})
    (x₀ : TopCat.sphere.{w} 1) {n : ℕ}
    (φ : (TopCat.sphere.{w} 1 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1)) :
    TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (n + 1)
        (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + 1) (n + 1) (zero_add _)
          (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ) +
      (TopCat.sphere.{w} 1 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 1 n
        (n + 1) (add_comm 1 n)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) 1
          ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm
            (1 : k)))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n
          (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 1 n (n + 1) (add_comm 1 n)
            ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app (TopCat.sphere 1)
              ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
                (1 : k))) φ)) = φ := by
  have : PathConnectedSpace (TopCat.sphere.{w} 1) :=
    TauCeti.TopCat.pathConnectedSpace_diskBoundary (by norm_num)
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_singularSlant_eq_zero_of_isIso M _ Y (λ_ _).hom _ fun p q h x ↦ ?_
  rw [map_sub, map_add, singularSlant_singularCup_singularCohomologyMap_fst_snd]
  match p, h, x with
  | 0, h, x =>
    -- `x` is a multiple of the class of `x₀`, and `θ` has degree one
    obtain rfl : q = n + 1 := by omega
    rw [singularSlant_singularCross_of_ne _ _ _ _ _ _ zero_ne_one,
      TauCeti.eq_smul_singularHomology₀Section x₀ x]
    simp only [map_smul, LinearMap.smul_apply]
    rw [singularSlant_singularHomology₀Section_singularCohomologyMap_snd, add_zero, sub_self]
  | 1, h, x =>
    -- `x` is a multiple of `γ`, and `⟨θ, γ⟩ = 1`
    obtain rfl : q = n := by omega
    obtain ⟨r, rfl⟩ := exists_eq_smul_singularHomology_sphere_one x
    have hθ : (TopCat.sphere.{w} 1).singularKronecker k 1
        ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm (1 : k))
        ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app (TopCat.sphere 1)
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
            (1 : k))) = 1 :=
      TauCeti.singularKronecker_singularCohomologyTopCatSphereEquiv_symm k _ 0 1
    simp only [map_smul, LinearMap.smul_apply]
    rw [singularSlant_singularCohomologyMap_snd_eq_zero _ _ _ _ _ _ _ _ one_ne_zero,
      singularSlant_singularCross_leftUnitor, hθ]
    simp
  | p + 2, h, x =>
    have := ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularHomologyFunctor_topCatSphere_of_ne
        (𝟙_ (ModuleCat.{w} k)) (n := 1) (q := p + 1) (by omega))
    rw [Subsingleton.elim x 0]
    simp

/-- **The cohomology of `S¹ × Y`**: for `x₀ ∈ S¹`, the slant products by the class of `x₀` and by
the standard generator `γ` of `H₁(S¹; k)` give a `k`-linear equivalence
`Hⁿ⁺¹(S¹ × Y; M) ≃ Hⁿ⁺¹(Y; M) × Hⁿ(Y; M)`. Its inverse sends `(b, c)` to
`pr₂^* b + pr₁^* θ ⌣ pr₂^* c`, where `θ ∈ H¹(S¹; k)` is dual to `γ`
(`TopCat.singularCohomologyMap_snd_add_singularCup_sphere`). -/
def singularCohomologySphereOneProdEquiv (Y : TopCat.{w}) (x₀ : TopCat.sphere.{w} 1) (n : ℕ) :
    (TopCat.sphere.{w} 1 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1) ≃ₗ[k]
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1) ×
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n where
  toFun φ :=
    (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + 1) (n + 1) (zero_add _)
        (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ,
      singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 1 n (n + 1) (add_comm 1 n)
        ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app (TopCat.sphere 1)
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
            (1 : k))) φ)
  map_add' φ ψ := by simp
  map_smul' r φ := by simp
  invFun bc :=
    TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (n + 1) bc.1 +
      (TopCat.sphere.{w} 1 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 1 n
        (n + 1) (add_comm 1 n)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) 1
          ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm
            (1 : k)))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n bc.2)
  left_inv φ := singularCohomologyMap_snd_add_singularCup_sphere M Y x₀ φ
  right_inv bc := by
    have hθ : (TopCat.sphere.{w} 1).singularKronecker k 1
        ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm (1 : k))
        ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app (TopCat.sphere 1)
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
            (1 : k))) = 1 :=
      TauCeti.singularKronecker_singularCohomologyTopCatSphereEquiv_symm k _ 0 1
    simp only [map_add, singularSlant_singularCup_singularCohomologyMap_fst_snd,
      singularSlant_singularHomology₀Section_singularCohomologyMap_snd,
      singularSlant_singularCross_of_ne _ _ _ _ _ _ zero_ne_one,
      singularSlant_singularCohomologyMap_snd_eq_zero _ _ _ _ _ _ _ _ one_ne_zero,
      singularSlant_singularCross_leftUnitor, hθ]
    simp

/-- The decomposition of `Hⁿ⁺¹(S¹ × Y; M)` records the slant products by the class of `x₀` and by
the standard generator of `H₁(S¹; k)`. -/
@[simp]
lemma singularCohomologySphereOneProdEquiv_apply (Y : TopCat.{w}) (x₀ : TopCat.sphere.{w} 1)
    (n : ℕ)
    (φ : (TopCat.sphere.{w} 1 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1)) :
    singularCohomologySphereOneProdEquiv M Y x₀ n φ =
      (singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (n + 1) (n + 1) (zero_add _)
          (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ,
        singularSlant k M _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 1 n (n + 1) (add_comm 1 n)
          ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) 1).app (TopCat.sphere 1)
            ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) 1).inv
              (1 : k))) φ) :=
  (rfl)

/-- The inverse of the decomposition of `Hⁿ⁺¹(S¹ × Y; M)` sends `(b, c)` to
`pr₂^* b + pr₁^* θ ⌣ pr₂^* c`. -/
@[simp]
lemma singularCohomologySphereOneProdEquiv_symm_apply (Y : TopCat.{w})
    (x₀ : TopCat.sphere.{w} 1) (n : ℕ)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    (singularCohomologySphereOneProdEquiv M Y x₀ n).symm bc =
      TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (n + 1) bc.1 +
        (TopCat.sphere.{w} 1 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 1 n
          (n + 1) (add_comm 1 n)
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) 1
            ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm
              (1 : k)))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n bc.2) :=
  (rfl)

end Circle

section Coefficients

variable {M}

/-- **Pulled-back classes of `S¹ × Y` under a change of coefficients**: let `g : M ⟶ M'` induce
an injective map `Hⁿ(Y; M) → Hⁿ(Y; M')`. If the image of `φ ∈ Hⁿ⁺¹(S¹ × Y; M)` in
`Hⁿ⁺¹(S¹ × Y; M')` is pulled back from `Y`, then so is `φ`. -/
theorem mem_range_singularCohomologyMap_snd_sphere_of_injective (Y : TopCat.{w}) {n : ℕ}
    {M' : ModuleCat.{w} k} (g : M ⟶ M')
    (hg : Function.Injective (homologyMap (((toSSet.obj Y).chainComplex
      (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) n))
    (φ : (TopCat.sphere.{w} 1 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + 1))
    (hφ : homologyMap (((toSSet.obj (TopCat.sphere.{w} 1 ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) (n + 1) φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd (TopCat.sphere.{w} 1) Y) (n + 1)).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd (TopCat.sphere.{w} 1) Y) (n + 1)).hom := by
  rw [mem_range_singularCohomologyMap_snd_sphere_iff, singularSlant_coefficient_naturality] at hφ
  rw [mem_range_singularCohomologyMap_snd_sphere_iff]
  exact hg (hφ.trans (map_zero _).symm)

/-- **Degree-two classes of `S¹ × Y` pulled back after an injective change of coefficients**: if
`g : M ⟶ M'` is injective and the image of `φ ∈ H²(S¹ × Y; M)` in `H²(S¹ × Y; M')` is pulled back
from `Y`, then so is `φ`. For `ℤ → ℝ`: an integral class whose real class is pulled back from `Y`
is pulled back from `Y` integrally, because the cross quotient `H¹(Y; ℤ)` is torsion-free. -/
theorem mem_range_singularCohomologyMap_snd_sphere_two_of_injective (Y : TopCat.{w})
    {M' : ModuleCat.{w} k} (g : M ⟶ M') (hg : Function.Injective g)
    (φ : (TopCat.sphere.{w} 1 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M 2)
    (hφ : homologyMap (((toSSet.obj (TopCat.sphere.{w} 1 ⊗ Y)).chainComplex
        (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k g) 2 φ ∈
      LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M') (CartesianMonoidalCategory.snd (TopCat.sphere.{w} 1) Y) 2).hom) :
    φ ∈ LinearMap.range (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := M) (CartesianMonoidalCategory.snd (TopCat.sphere.{w} 1) Y) 2).hom := by
  have : Projective (𝟙_ (ModuleCat.{w} k)) := inferInstanceAs (Projective (ModuleCat.of k k))
  -- `H₀(Y; k)` is free, so `H¹(Y; M) = Hom(H₁(Y; k), M)` and `g` is injective on it
  exact mem_range_singularCohomologyMap_snd_sphere_of_injective Y g
    (Y.injective_homologyMap_linearYonedaObjMap_of_projective_homology_lt g hg 1 fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis k
        (((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (𝟙_ (ModuleCat.{w} k))).obj Y)))
    φ hφ

end Coefficients

end TopCat
