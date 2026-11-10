/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Kunneth
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# Positive-degree singular cohomology of spheres

For every commutative ring `k` and every `k`-module `M`, evaluation on the native standard
homology generator identifies `Hⁿ⁺¹(Sⁿ⁺¹; M)` with `M`. Positive-degree cohomology vanishes
outside the sphere dimension, including for the zero-sphere. No hereditary-ring or
injectivity assumption is needed: the singular homology of a sphere with coefficients in
`k` is free, so the Kronecker map is an isomorphism over any commutative ring.

The equivalence is natural in the coefficient module. Its evaluation formula uses exactly
`TauCeti.reducedSingularHomologyTopCatSphereIso` and the canonical reduced-to-ordinary
inclusion; it does not choose another orientation or generator. In particular its inverse
applied to a nonzero coefficient gives a nonzero top cohomology class.

Since the homology of a sphere is free of finite rank, the Künneth theorem for cohomology applies
to a product with a sphere over every commutative ring and with no hypothesis on the other factor
(`TopCat.singularCohomologyKunneth_sphere_bijective`).

In terms of pullbacks and cup products on `S^{d+1} × Y` itself, with coefficients in a
commutative ring `k`, every class of degree `d + 1 + n` is uniquely `pr₂^* a + pr₁^* θ ⌣ pr₂^* b`
with `a ∈ H^{d+1+n}(Y; k)` and `b ∈ Hⁿ(Y; k)`, where `θ` is the standard generator of
`H^{d+1}(S^{d+1}; k)` (`TopCat.singularCohomologySphereProdEquiv`). The two components of a class
are recovered as its slant products by the class of a point and by the standard generator of
`H_{d+1}(S^{d+1}; k)`, which detect the cohomology of the product
(`TopCat.eq_zero_of_forall_singularSlant_leftUnitor_eq_zero`). In degrees `m ≤ d` the pullback
along `pr₂` is bijective (`TopCat.singularCohomologyMap_snd_topCatSphere_bijective`). For the circle
and `k = ℤ` this is
the decomposition `H^{n+1}(S¹ × Y; ℤ) = pr₂^* H^{n+1}(Y; ℤ) ⊕ (θ ⌣ pr₂^* Hⁿ(Y; ℤ))`, with all
torsion of `Y` retained.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1 (universal coefficients), Section 3.2
  (the cohomology of spheres) and Theorem 3.15 with Section 3.B (the Künneth formula).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w

namespace TauCeti

variable (k : Type w) [CommRing k] (M : ModuleCat.{w} k)

/-- Evaluation on the standard homology generator identifies the top cohomology of a
positive-dimensional sphere with its coefficient module, over any commutative ring. -/
def singularCohomologyTopCatSphereEquiv (n : ℕ) :
    (TopCat.sphere.{w} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1) ≃ₗ[k] M :=
  ((TopCat.sphere (n + 1)).singularKroneckerEquivOfProjectiveHomology
      (ModuleCat.of k k) M (n + 1)).trans
    ((Linear.homCongr k
      (((reducedSingularHomologySuccIso (ModuleCat.of k k) n).app
        (TopCat.sphere (n + 1))).symm ≪≫
        reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (n + 1))
      (Iso.refl M)).trans
        (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k M)))

/-- The sphere cohomology equivalence evaluates on the native reduced generator, included
in ordinary homology. -/
@[simp]
lemma singularCohomologyTopCatSphereEquiv_apply (n : ℕ)
    (α : (TopCat.sphere.{w} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1)) :
    singularCohomologyTopCatSphereEquiv k M n α =
      ((TopCat.sphere (n + 1)).singularKronecker k (n + 1) α)
        (((reducedSingularHomologyι (ModuleCat.of k k) (n + 1)).app
          (TopCat.sphere (n + 1)))
          ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (n + 1)).inv 1)) := by
  simp only [singularCohomologyTopCatSphereEquiv, LinearEquiv.trans_apply,
    TopCat.singularKroneckerEquivOfProjectiveHomology_apply, Linear.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Iso.trans_inv, Iso.symm_inv]
  rw [← reducedSingularHomologySuccIso_hom]
  rw [ModuleCat.homLinearEquiv_apply, LinearMap.ringLmapEquivSelf_apply]
  -- The additive hom equivalence is the underlying linear map; it has no apply lemma.
  rfl

/-- The inverse sphere cohomology equivalence has prescribed evaluation on the native
standard generator. -/
-- Not a simp lemma: the reduced-to-ordinary inclusion simplifies inside the left-hand side.
lemma singularKronecker_singularCohomologyTopCatSphereEquiv_symm (n : ℕ) (m : M) :
    ((TopCat.sphere (n + 1)).singularKronecker k (n + 1)
      ((singularCohomologyTopCatSphereEquiv k M n).symm m))
        (((reducedSingularHomologyι (ModuleCat.of k k) (n + 1)).app
          (TopCat.sphere (n + 1)))
          ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (n + 1)).inv 1)) = m := by
  rw [← singularCohomologyTopCatSphereEquiv_apply]
  exact (singularCohomologyTopCatSphereEquiv k M n).apply_symm_apply m

/-- Positive-degree singular cohomology of a sphere vanishes away from its dimension,
with arbitrary module coefficients over any commutative ring. -/
theorem isZero_singularCohomology_topCatSphere_of_ne (d q : ℕ) (h : q + 1 ≠ d) :
    IsZero ((TopCat.sphere.{w} d).singularCohomology (ModuleCat.of k k) k M (q + 1)) := by
  have hz := (isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne
    (ModuleCat.of k k) h).of_iso
      ((reducedSingularHomologySuccIso (ModuleCat.of k k) q).app (TopCat.sphere d)).symm
  have : Subsingleton (_ ⟶ M) := ⟨hz.eq_of_src⟩
  have := ((TopCat.sphere d).singularKronecker_bijective_of_projective_homology
    (ModuleCat.of k k) M (q + 1)).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Evaluation on the sphere generator commutes with every coefficient-module map.
The map on cohomology is induced by postcomposition on the actual singular cochains. -/
lemma singularCohomologyTopCatSphereEquiv_naturality {N : ModuleCat.{w} k}
    (g : M ⟶ N) (n : ℕ)
    (α : (TopCat.sphere.{w} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1)) :
    singularCohomologyTopCatSphereEquiv k N n
      (HomologicalComplex.homologyMap
        (((TopCat.toSSet.obj (TopCat.sphere (n + 1))).chainComplex
          (ModuleCat.of k k)).linearYonedaObjMap k g) (n + 1) α) =
      g (singularCohomologyTopCatSphereEquiv k M n α) := by
  rw [singularCohomologyTopCatSphereEquiv_apply,
    singularCohomologyTopCatSphereEquiv_apply,
    TopCat.singularKronecker_coefficient_naturality, ModuleCat.comp_apply]

end TauCeti

namespace TopCat

variable {k : Type w} [CommRing k] (Y : TopCat.{w})

/-- **The cohomology of a product with a sphere**: over every commutative ring `k`, the cohomology
cross product induces an isomorphism `⨁_{p + q = n} Hᵖ(Sᵈ; k) ⊗ H^q(Y; k) ≅ Hⁿ(Sᵈ × Y; k)` for
every space `Y`, since the homology of the sphere is free of finite rank. For `d = 1` and
`k = ℤ` this splits `Hⁿ(S¹ × Y; ℤ)` into the cross products of `H⁰(S¹; ℤ) ≅ ℤ` with `Hⁿ(Y; ℤ)` and
of `H¹(S¹; ℤ) ≅ ℤ` with `Hⁿ⁻¹(Y; ℤ)`, torsion included. -/
theorem singularCohomologyKunneth_sphere_bijective (d n : ℕ) :
    Function.Bijective (singularCohomologyKunneth (TopCat.sphere.{w} d) Y (𝟙_ (ModuleCat.{w} k))
      (𝟙_ (ModuleCat.{w} k)) k (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  singularCohomologyKunneth_bijective _ Y n fun _ _ ↦ inferInstance

section SphereProduct

variable {k : Type w} [CommRing k]

/-- The standard generator of `H_{d+1}(S^{d+1}; k)`, the image of `1` under the standard
identification of the reduced homology with `k`. -/
private noncomputable def sphereHomologyGenerator (d : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{w} k) (d + 1)).obj (𝟙_ (ModuleCat.{w} k))).obj
      (TopCat.sphere.{w} (d + 1)) :=
  ((TauCeti.reducedSingularHomologyι (ModuleCat.of k k) (d + 1)).app (TopCat.sphere (d + 1)))
    ((TauCeti.reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (d + 1)).inv (1 : k))

/-- The standard cohomology generator of `S^{d+1}` takes the value `1` on the standard homology
generator. -/
private lemma singularKronecker_sphereHomologyGenerator (d : ℕ) :
    (TopCat.sphere.{w} (d + 1)).singularKronecker k (d + 1)
      ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) d).symm 1)
      (sphereHomologyGenerator d) = 1 :=
  TauCeti.singularKronecker_singularCohomologyTopCatSphereEquiv_symm k _ d 1

/-- Every class of `H_{d+1}(S^{d+1}; k)` is a multiple of the standard generator. -/
private lemma exists_eq_smul_sphereHomologyGenerator (d : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) (d + 1)).obj (𝟙_ (ModuleCat.{w} k))).obj
      (TopCat.sphere.{w} (d + 1))) :
    ∃ c : k, x = c • sphereHomologyGenerator d := by
  let E := ((TauCeti.reducedSingularHomologySuccIso (ModuleCat.of k k) d).app
    (TopCat.sphere.{w} (d + 1))).symm ≪≫
      TauCeti.reducedSingularHomologyTopCatSphereIso (ModuleCat.of k k) (d + 1)
  refine ⟨E.hom x, ?_⟩
  have h1 : E.inv (E.hom x) = x := ConcreteCategory.congr_hom E.hom_inv_id x
  have h2 : E.inv (E.hom x) = E.hom x • E.inv (1 : k) := by
    rw [← map_smul]
    congr 1
    exact (mul_one _).symm
  have h3 : E.inv (1 : k) = sphereHomologyGenerator d := by
    simp only [E, Iso.trans_inv, Iso.symm_inv, ConcreteCategory.comp_apply, Iso.app_hom,
      TauCeti.reducedSingularHomologySuccIso_hom, sphereHomologyGenerator]
  conv_lhs => rw [← h1, h2, h3]

/-- Every class of `H₀(S^{d+1}; k)` is a multiple of the class of a point: the reduced homology
of `S^{d+1}` vanishes in degree zero, so the augmentation is injective. -/
private lemma eq_smul_singularHomology₀Section (d : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj (𝟙_ (ModuleCat.{w} k))).obj
      (TopCat.sphere.{w} (d + 1))) (v : TopCat.sphere.{w} (d + 1)) :
    x = ((TopCat.sphere.{w} (d + 1)).singularHomology₀ε (𝟙_ (ModuleCat.{w} k)) x : k) •
      TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) v (1 : k) := by
  have hz := TauCeti.isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne
    (𝟙_ (ModuleCat.{w} k)) (k := 0) (n := d + 1) (by omega)
  rw [TauCeti.reducedSingularHomologyFunctor_zero_obj] at hz
  have hmono : Mono ((TopCat.sphere.{w} (d + 1)).singularHomology₀ε (𝟙_ (ModuleCat.{w} k))) :=
    Preadditive.mono_of_isZero_kernel _ hz
  apply (ModuleCat.mono_iff_injective _).1 hmono
  have hv := ConcreteCategory.congr_hom
    (TauCeti.singularHomology₀Section_singularHomology₀ε (𝟙_ (ModuleCat.{w} k)) v) (1 : k)
  rw [ConcreteCategory.comp_apply] at hv
  rw [map_smul, hv]
  exact (mul_one _).symm

/-- The homology of `S^{d+1}` vanishes outside degrees `0` and `d + 1`. -/
private lemma subsingleton_singularHomology_topCatSphere (d p : ℕ) (h0 : p ≠ 0)
    (hd : p ≠ d + 1) :
    Subsingleton (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj (TopCat.sphere.{w} (d + 1))) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact ModuleCat.subsingleton_of_isZero
    ((TauCeti.isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne
      (𝟙_ (ModuleCat.{w} k)) hd).of_iso
        ((TauCeti.reducedSingularHomologySuccIso (𝟙_ (ModuleCat.{w} k)) q).app _).symm)

variable (Y : TopCat.{w})

/-- The map `(a, b) ↦ pr₂^* a + pr₁^* θ ⌣ pr₂^* b` of `singularCohomologySphereProdEquiv`. -/
private noncomputable def sphereProdMap (d n : ℕ) :
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n) →ₗ[k]
    (TopCat.sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) :=
  LinearMap.coprod
    (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (d + 1 + n)).hom
    (((TopCat.sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n (d + 1 + n) rfl
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
        ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) d).symm 1))).comp
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n).hom)

/-- The inverse of `sphereProdMap`: the slant products by the class of a point and by the
standard generator of `H_{d+1}(S^{d+1}; k)`. -/
private noncomputable def sphereProdInv (d n : ℕ) :
    (TopCat.sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) →ₗ[k]
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n) :=
  LinearMap.prod
    (singularSlant k (𝟙_ (ModuleCat.{w} k)) _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 (d + 1 + n)
      (d + 1 + n) (zero_add _)
      (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k))
        (Classical.arbitrary (TopCat.sphere.{w} (d + 1))) (1 : k)))
    (singularSlant k (𝟙_ (ModuleCat.{w} k)) _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n
      (d + 1 + n) rfl (sphereHomologyGenerator d))

private lemma sphereProdInv_comp_sphereProdMap (d n : ℕ) :
    sphereProdInv (k := k) Y d n ∘ₗ sphereProdMap Y d n = LinearMap.id := by
  refine LinearMap.ext fun ⟨a, b⟩ ↦ Prod.ext ?_ ?_
  · simp [sphereProdInv, sphereProdMap]
  · simp only [sphereProdInv, sphereProdMap, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod_apply, map_add, ne_eq,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      singularSlant_singularCohomologyMap_snd_eq_zero,
      singularSlant_singularCup_singularCohomologyMap_fst_snd, LinearMap.id_coe, id_eq]
    rw [singularKronecker_sphereHomologyGenerator, one_smul, Prod.snd_add, zero_add]

private lemma sphereProdMap_comp_sphereProdInv (d n : ℕ) :
    sphereProdMap (k := k) Y d n ∘ₗ sphereProdInv Y d n = LinearMap.id := by
  -- the difference of a class and its image under the composite has vanishing slant products
  refine LinearMap.ext fun φ ↦ sub_eq_zero.1
    (eq_zero_of_forall_singularSlant_leftUnitor_eq_zero _ Y _ fun p q h x ↦ ?_)
  rcases (by omega : p = 0 ∨ p = d + 1 ∨ (p ≠ 0 ∧ p ≠ d + 1)) with rfl | rfl | ⟨h0, hd⟩
  · -- the slant product by a class of degree zero, a multiple of the class of a point
    obtain rfl : q = d + 1 + n := by omega
    rw [eq_smul_singularHomology₀Section d x (Classical.arbitrary _), map_smul,
      LinearMap.smul_apply, map_sub]
    simp only [sphereProdInv, sphereProdMap, LinearMap.comp_apply, LinearMap.coprod_apply,
      LinearMap.prod_apply, Function.prod, LinearMap.id_apply, map_add, ModuleCat.Hom.hom]
    rw [singularSlant_singularHomology₀Section_singularCohomologyMap_snd,
      singularSlant_singularCup_singularCohomologyMap_fst_snd_of_ne _ _ _ _ (by omega),
      add_zero, sub_self, smul_zero]
  · -- the slant product by a class of degree `d + 1`, a multiple of the standard generator
    obtain rfl : q = n := by omega
    obtain ⟨c, rfl⟩ := exists_eq_smul_sphereHomologyGenerator d x
    rw [map_smul, LinearMap.smul_apply, map_sub]
    simp only [sphereProdInv, sphereProdMap, LinearMap.comp_apply, LinearMap.coprod_apply,
      LinearMap.prod_apply, Function.prod, LinearMap.id_apply, map_add, ModuleCat.Hom.hom]
    rw [singularSlant_singularCohomologyMap_snd_eq_zero (hp := Nat.succ_ne_zero d),
      singularSlant_singularCup_singularCohomologyMap_fst_snd,
      singularKronecker_sphereHomologyGenerator, one_smul, zero_add, sub_self, smul_zero]
  · -- in every other degree the homology of the sphere vanishes
    have := subsingleton_singularHomology_topCatSphere (k := k) d p h0 hd
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

/-- **The cohomology of a product with a sphere**: for every space `Y` and `d, n ≥ 0`, with
coefficients in a commutative ring `k`,

`H^{d+1+n}(Y; k) × Hⁿ(Y; k) ≃ H^{d+1+n}(S^{d+1} × Y; k)`,  `(a, b) ↦ pr₂^* a + pr₁^* θ ⌣ pr₂^* b`,

where `θ ∈ H^{d+1}(S^{d+1}; k)` is the standard generator
(`TauCeti.singularCohomologyTopCatSphereEquiv`). For the circle (`d = 0`) and `k = ℤ`, every class
of `H^{n+1}(S¹ × Y; ℤ)` is uniquely `pr₂^* a + [dθ] ⌣ pr₂^* b`, torsion included. -/
noncomputable def singularCohomologySphereProdEquiv (d n : ℕ) :
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n) ≃ₗ[k]
    (TopCat.sphere.{w} (d + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) :=
  LinearEquiv.ofLinearMap (sphereProdMap Y d n) (sphereProdInv Y d n)
    (sphereProdMap_comp_sphereProdInv Y d n) (sphereProdInv_comp_sphereProdMap Y d n)

/-- The decomposition `TopCat.singularCohomologySphereProdEquiv` sends `(a, b)` to
`pr₂^* a + pr₁^* θ ⌣ pr₂^* b`. -/
@[simp]
lemma singularCohomologySphereProdEquiv_apply (d n : ℕ)
    (x : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (d + 1 + n) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n) :
    singularCohomologySphereProdEquiv Y d n x =
      TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) (d + 1 + n) x.1 +
        (TopCat.sphere.{w} (d + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom (d + 1) n (d + 1 + n) rfl
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst _ Y) (d + 1)
            ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) d).symm 1))
          (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) n x.2) :=
  (rfl)

/-- **The cohomology of a product with a sphere below the dimension of the sphere**: with
coefficients in a commutative ring `k`, pulling back along `pr₂ : S^{d+1} × Y ⟶ Y` is bijective
in every degree `m ≤ d`. -/
theorem singularCohomologyMap_snd_topCatSphere_bijective (d m : ℕ) (hm : m ≤ d) :
    Function.Bijective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
      (M := 𝟙_ (ModuleCat.{w} k)) (CartesianMonoidalCategory.snd (TopCat.sphere.{w} (d + 1)) Y)
      m) := by
  let v := Classical.arbitrary (TopCat.sphere.{w} (d + 1))
  -- the slant product by the class of a point is a left inverse
  have hleft (a : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) m) :
      singularSlant k (𝟙_ (ModuleCat.{w} k)) _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 m m
        (zero_add m) (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) v (1 : k))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd _ Y) m a) = a :=
    singularSlant_singularHomology₀Section_singularCohomologyMap_snd _ Y v m a
  refine ⟨fun a b hab ↦ (hleft a).symm.trans ((congrArg _ hab).trans (hleft b)), fun φ ↦
    ⟨singularSlant k (𝟙_ (ModuleCat.{w} k)) _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 m m (zero_add m)
      (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) v (1 : k)) φ,
      sub_eq_zero.1 (eq_zero_of_forall_singularSlant_leftUnitor_eq_zero _ Y _ fun p q h x ↦ ?_)⟩⟩
  rcases eq_or_ne p 0 with rfl | h0
  · obtain rfl : q = m := by omega
    rw [eq_smul_singularHomology₀Section d x v, map_smul, LinearMap.smul_apply, map_sub, hleft,
      sub_self, smul_zero]
  · -- in degrees `0 < p ≤ m ≤ d` the homology of the sphere vanishes
    have := subsingleton_singularHomology_topCatSphere (k := k) d p h0 (by omega)
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

end SphereProduct

end TopCat
