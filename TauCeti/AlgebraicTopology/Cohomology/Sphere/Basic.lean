/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Kunneth
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# Singular cohomology of spheres and of products with spheres

For every commutative ring `k` and every `k`-module `M`, evaluation on the native standard
homology generator identifies `Hⁿ⁺¹(Sⁿ⁺¹; M)` with `M`. Positive-degree cohomology vanishes
outside the sphere dimension, including for the zero-sphere. No hereditary-ring or
injectivity assumption is needed: the singular homology of a sphere with coefficients in
`k` is free, so the Kronecker map is an isomorphism over any commutative ring.

The equivalence is natural in the coefficient module. Its evaluation formula uses exactly
`TauCeti.reducedSingularHomologyTopCatSphereIso` and the canonical reduced-to-ordinary
inclusion; it does not choose another orientation or generator. In particular its inverse
applied to a nonzero coefficient gives a nonzero top cohomology class.

Dually to the standard generator `TauCeti.singularHomologyTopCatSphereGenerator` of
`Hₙ₊₁(Sⁿ⁺¹; k)`, the class `TauCeti.singularCohomologyTopCatSphereGenerator` of `Hⁿ⁺¹(Sⁿ⁺¹; k)`
takes the value `1` on it. Its cup square vanishes, since `H²ⁿ⁺²(Sⁿ⁺¹; k) = 0`
(`TopCat.singularCup_singularCohomologyTopCatSphereGenerator_self`).

Since the homology of a sphere is free of finite rank, the Künneth theorem for cohomology applies
to a product with a sphere over every commutative ring and with no hypothesis on the other factor
(`TopCat.singularCohomologyKunneth_sphere_bijective`).

For a sphere of positive dimension `m + 1` this decomposition is made explicit, with the summands
named as pullbacks and cup products (`TopCat.singularCohomologySphereProdEquiv`): for
`m + 1 + q = n`,

`Hⁿ(Y; k) × H^q(Y; k) ≃ Hⁿ(S^{m+1} × Y; k)`,  `(b, c) ↦ pr₂^* b + pr₁^* θ ⌣ pr₂^* c`,

where `θ ∈ H^{m+1}(S^{m+1}; k)` evaluates to `1` on the standard generator of the homology of the
sphere. The inverse sends a class to its slant products by the class of a point and by the
standard generator; that these two slant products determine the class is the detection theorem
`TopCat.eq_zero_of_forall_singularSlant_eq_zero`, since the two classes span the homology of the
sphere. For `k = ℤ` and the circle this splits `H²(S¹ × Y; ℤ)` into `pr₂^* H²(Y; ℤ)` and
`θ ⌣ pr₂^* H¹(Y; ℤ)`, with all torsion of `Y` retained.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1 (universal coefficients) and Section 3.2
  (the cohomology of spheres).
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
        (singularHomologyTopCatSphereGenerator k n) := by
  simp only [singularCohomologyTopCatSphereEquiv, LinearEquiv.trans_apply,
    TopCat.singularKroneckerEquivOfProjectiveHomology_apply, Linear.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Iso.trans_inv, Iso.symm_inv]
  rw [singularHomologyTopCatSphereGenerator_def, ← reducedSingularHomologySuccIso_hom]
  rw [ModuleCat.homLinearEquiv_apply, LinearMap.ringLmapEquivSelf_apply]
  -- The additive hom equivalence is the underlying linear map; it has no apply lemma.
  rfl

/-- The inverse sphere cohomology equivalence has prescribed evaluation on the native
standard generator. -/
@[simp]
lemma singularKronecker_singularCohomologyTopCatSphereEquiv_symm (n : ℕ) (m : M) :
    ((TopCat.sphere (n + 1)).singularKronecker k (n + 1)
      ((singularCohomologyTopCatSphereEquiv k M n).symm m))
        (singularHomologyTopCatSphereGenerator k n) = m := by
  rw [← singularCohomologyTopCatSphereEquiv_apply]
  exact (singularCohomologyTopCatSphereEquiv k M n).apply_symm_apply m

/-- **The dual of the sphere generator**: the class of `Hⁿ⁺¹(TopCat.sphere (n + 1); k)` taking
the value `1` on the standard generator `TauCeti.singularHomologyTopCatSphereGenerator`. It
generates `Hⁿ⁺¹(TopCat.sphere (n + 1); k) ≅ k`. Both coefficients are written as the monoidal unit
`𝟙_ (ModuleCat k)`, the form in which cup and slant products take them. -/
def singularCohomologyTopCatSphereGenerator (n : ℕ) :
    (TopCat.sphere.{w} (n + 1)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (n + 1) :=
  (singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) n).symm 1

/-- The dual of the sphere generator pairs to `1` with the standard generator. -/
@[simp]
lemma singularKronecker_singularCohomologyTopCatSphereGenerator (n : ℕ) :
    (TopCat.sphere.{w} (n + 1)).singularKronecker k (n + 1)
        (singularCohomologyTopCatSphereGenerator k n)
        (singularHomologyTopCatSphereGenerator k n) = (1 : k) :=
  singularKronecker_singularCohomologyTopCatSphereEquiv_symm k _ n 1

/-- Positive-degree singular cohomology of a sphere vanishes away from its dimension,
with arbitrary module coefficients over any commutative ring. -/
theorem isZero_singularCohomology_topCatSphere_of_ne (d q : ℕ) (h : q + 1 ≠ d) :
    IsZero ((TopCat.sphere.{w} d).singularCohomology (ModuleCat.of k k) k M (q + 1)) := by
  have hz := isZero_singularHomologyFunctor_topCatSphere_of_ne (ModuleCat.of k k) h
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
    Function.Bijective (singularCohomologyKunneth (sphere.{w} d) Y (𝟙_ (ModuleCat.{w} k))
      (𝟙_ (ModuleCat.{w} k)) k (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  singularCohomologyKunneth_bijective _ Y n fun _ _ ↦ inferInstance

/-- The cup square of the generator `θ` of `Hᵈ⁺¹(Sᵈ⁺¹; k)` vanishes, since
`H²ᵈ⁺²(Sᵈ⁺¹; k) = 0`. -/
@[simp]
theorem singularCup_singularCohomologyTopCatSphereGenerator_self (d : ℕ) :
    (TopCat.sphere.{w} (d + 1)).singularCup k (λ_ _).inv (λ_ _).hom (d + 1) (d + 1)
      (d + 1 + (d + 1)) rfl (TauCeti.singularCohomologyTopCatSphereGenerator k d)
      (TauCeti.singularCohomologyTopCatSphereGenerator k d) = 0 := by
  have hz : IsZero ((TopCat.sphere.{w} (d + 1)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (d + 1 + (d + 1))) := by
    rw [show d + 1 + (d + 1) = 2 * d + 1 + 1 by omega]
    exact TauCeti.isZero_singularCohomology_topCatSphere_of_ne k _ (d + 1) (2 * d + 1) (by omega)
  have := ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

end TopCat

namespace TopCat

section SphereProd

open CartesianMonoidalCategory HomologicalComplex

variable {k : Type w} [CommRing k] (Y : TopCat.{w})

/-- A class of `S^{m+1} × Y` whose slant products by the class of a point and by the standard
generator of `H_{m+1}(S^{m+1}; k)` vanish is zero: these two classes span the homology of the
sphere, and slant products by the homology of the sphere detect the cohomology of the product. -/
private lemma eq_zero_of_singularSlant_sphere (m q n : ℕ) (h : m + 1 + q = n)
    (x₀ : sphere.{w} (m + 1))
    (ψ : (sphere.{w} (m + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) n)
    (h₀ : singularSlant k _ _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 n n (zero_add n)
      (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) ψ = 0)
    (h₁ : singularSlant k _ _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (m + 1) q n h
      ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) (m + 1)).app _
        ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) (m + 1)).inv
          (1 : k))) ψ = 0) : ψ = 0 := by
  have : PathConnectedSpace (sphere.{w} (m + 1)) :=
    TauCeti.TopCat.pathConnectedSpace_diskBoundary (by omega)
  -- the detection theorem applies to `ψ` with its coefficients changed from `k` to `k ⊗ k` along
  -- the left unitor, an isomorphism of coefficients
  have hψ : homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k (𝟙_ (ModuleCat.{w} k))).map
        (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).inv).app
          (toSSet.obj (sphere.{w} (m + 1) ⊗ Y))).op) n
      (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k (𝟙_ (ModuleCat.{w} k))).map
        (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app
          (toSSet.obj (sphere.{w} (m + 1) ⊗ Y))).op) n ψ) = ψ :=
    -- the two coefficient changes are the two components of the image of `λ_` under functors
    ((homologyFunctor _ _ n).mapIso ((TauCeti.ChainComplex.linearYonedaFunctor k
      (𝟙_ (ModuleCat.{w} k))).mapIso (((SSet.chainComplexFunctor _).mapIso
        (λ_ (𝟙_ (ModuleCat.{w} k)))).app
          (toSSet.obj (sphere.{w} (m + 1) ⊗ Y))).op)).hom_inv_id_apply ψ
  rw [← hψ]
  refine (congrArg _ (eq_zero_of_forall_singularSlant_eq_zero _ _ Y _
    fun p q' h' x ↦ ?_)).trans (map_zero _)
  rw [singularSlant_coefficient_naturality, Category.id_comp]
  by_cases hp0 : p = 0
  · -- `H₀` of the sphere is spanned by the class of `x₀`
    subst hp0
    obtain rfl : q' = n := by omega
    -- the spanning lemma, restated for the coefficient object `𝟙_ (ModuleCat k)`, whose
    -- underlying module is `ModuleCat.of k k`
    have hx : x = (sphere.{w} (m + 1)).singularHomology₀ε (𝟙_ (ModuleCat.{w} k)) x •
        TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k) :=
      TauCeti.singularHomology₀_eq_smul_singularHomology₀Section x₀ x
    rw [hx, map_smul, LinearMap.smul_apply, h₀, smul_zero]
  by_cases hpm : p = m + 1
  · -- `H_{m+1}` of the sphere is spanned by the standard generator
    subst hpm
    obtain rfl : q' = q := by omega
    -- the spanning lemma, restated for the coefficient object `𝟙_ (ModuleCat k)`
    have hx : x =
        (TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) (m + 1)).hom
          (((TauCeti.reducedSingularHomologySuccIso (𝟙_ (ModuleCat.{w} k)) m).app _).inv x) •
        (TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) (m + 1)).app _
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) (m + 1)).inv
            (1 : k)) :=
      TauCeti.singularHomology_topCatSphere_eq_smul_generator m x
    rw [hx, map_smul, LinearMap.smul_apply, h₁, smul_zero]
  · -- the homology of the sphere vanishes in every other degree
    obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have hz : IsZero (((singularHomologyFunctor (ModuleCat.{w} k) (p + 1)).obj
        (𝟙_ (ModuleCat.{w} k))).obj (sphere.{w} (m + 1))) :=
      (TauCeti.isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne _ hpm).of_iso
        ((TauCeti.reducedSingularHomologySuccIso _ p).app _).symm
    rw [(ModuleCat.isZero_iff_subsingleton.mp hz).elim x 0, map_zero, LinearMap.zero_apply]

/-- The map `Hⁿ(Y; k) × H^q(Y; k) ⟶ Hⁿ(S^{m+1} × Y; k)`, `(b, c) ↦ pr₂^* b + pr₁^* θ ⌣ pr₂^* c`,
underlying `TopCat.singularCohomologySphereProdEquiv`. -/
private noncomputable def sphereProdCohomologyMap (m q n : ℕ) (h : m + 1 + q = n) :
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) →ₗ[k]
      (sphere.{w} (m + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n :=
  (TopCat.singularCohomologyMap (snd _ Y) n).hom.coprod
    (((sphere.{w} (m + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom (m + 1) q n h
      (TopCat.singularCohomologyMap (fst _ Y) (m + 1)
        ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) m).symm
          (1 : k)))).comp (TopCat.singularCohomologyMap (snd _ Y) q).hom)

/-- The slant products `φ ↦ (φ / [x₀], φ / [S^{m+1}])` by the class of a point and by the standard
generator, the inverse of `sphereProdCohomologyMap`. -/
private noncomputable def sphereProdSlant (m q n : ℕ) (h : m + 1 + q = n) :
    (sphere.{w} (m + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n →ₗ[k]
      (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n ×
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :=
  (singularSlant k _ _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 n n (zero_add n)
      (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k))
        (Classical.arbitrary (sphere.{w} (m + 1))) (1 : k))).prod
    (singularSlant k _ _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (m + 1) q n h
      ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) (m + 1)).app _
        ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) (m + 1)).inv
          (1 : k))))

private lemma sphereProdSlant_sphereProdCohomologyMap (m q n : ℕ) (h : m + 1 + q = n)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    sphereProdSlant Y m q n h (sphereProdCohomologyMap Y m q n h bc) = bc := by
  obtain ⟨b, c⟩ := bc
  simp only [sphereProdSlant, sphereProdCohomologyMap, LinearMap.coprod_apply,
    LinearMap.comp_apply, LinearMap.prod_apply, Function.prod, map_add, Prod.mk_add_mk,
    Prod.mk.injEq]
  -- `pr₁^* θ ⌣ pr₂^* c` has the slant products of `θ × c`, given by the Kronecker pairing of `θ`
  simp only [TauCeti.singularCup_fst_snd_eq_homologyMap_singularCross,
    singularSlant_coefficient_naturality, Iso.hom_inv_id]
  refine ⟨?_, ?_⟩
  · rw [singularSlant_singularHomology₀Section_singularCohomologyMap_snd_eq_self _ _ _ _ _ _ _
        fun s ↦ (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (1 : k) s).trans (one_smul k s),
      singularSlant_singularCross_of_ne (hp := by omega), add_zero]
  · -- `θ` evaluates to `1` on the standard generator; the sphere API states this with the
    -- coefficient ring written `ModuleCat.of k k` rather than `𝟙_ (ModuleCat k)`
    have hθ : (sphere.{w} (m + 1)).singularKronecker k (m + 1)
        (R := 𝟙_ (ModuleCat.{w} k)) (M := 𝟙_ (ModuleCat.{w} k))
        ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) m).symm (1 : k))
        ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) (m + 1)).app _
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) (m + 1)).inv
            (1 : k))) = (1 : k) := by
      have h := TauCeti.singularKronecker_singularCohomologyTopCatSphereEquiv_symm k
        (𝟙_ (ModuleCat.{w} k)) m (1 : k)
      rwa [TauCeti.singularHomologyTopCatSphereGenerator_def] at h
    rw [singularSlant_singularCohomologyMap_snd_eq_zero (hp := by omega),
      singularSlant_singularCross_leftUnitor, hθ, one_smul, zero_add]

private lemma sphereProdCohomologyMap_sphereProdSlant (m q n : ℕ) (h : m + 1 + q = n)
    (φ : (sphere.{w} (m + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) n) :
    sphereProdCohomologyMap Y m q n h (sphereProdSlant Y m q n h φ) = φ := by
  rw [← sub_eq_zero]
  have hG : sphereProdSlant Y m q n h
      (sphereProdCohomologyMap Y m q n h (sphereProdSlant Y m q n h φ) - φ) = 0 := by
    rw [map_sub, sphereProdSlant_sphereProdCohomologyMap, sub_self]
  exact eq_zero_of_singularSlant_sphere Y m q n h _ _ (congrArg Prod.fst hG)
    (congrArg Prod.snd hG)

/-- **The cohomology of a product with a sphere** of positive dimension `m + 1`, with
coefficients in a commutative ring `k`: for `m + 1 + q = n`,

`Hⁿ(Y; k) × H^q(Y; k) ≃ Hⁿ(S^{m+1} × Y; k)`,  `(b, c) ↦ pr₂^* b + pr₁^* θ ⌣ pr₂^* c`,

where `θ ∈ H^{m+1}(S^{m+1}; k)` is the class dual to the standard generator of the homology of the
sphere (`TauCeti.singularCohomologyTopCatSphereEquiv`). The inverse sends a class `φ` to its slant
products `(φ / [x₀], φ / [S^{m+1}])` by the class of a point and by the standard generator
(`TopCat.singularCohomologySphereProdEquiv_symm_apply`). No hypothesis is placed on `Y`, and
torsion is retained: for `k = ℤ`, `m = 0` and `n = 2` this is the splitting
`H²(S¹ × Y; ℤ) = pr₂^* H²(Y; ℤ) ⊕ (θ ⌣ pr₂^* H¹(Y; ℤ))`. -/
noncomputable def singularCohomologySphereProdEquiv (m q n : ℕ) (h : m + 1 + q = n) :
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) ≃ₗ[k]
      (sphere.{w} (m + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n :=
  LinearEquiv.ofLinearMap (sphereProdCohomologyMap Y m q n h) (sphereProdSlant Y m q n h)
    (LinearMap.ext (sphereProdCohomologyMap_sphereProdSlant Y m q n h))
    (LinearMap.ext (sphereProdSlant_sphereProdCohomologyMap Y m q n h))

/-- The splitting of the cohomology of `S^{m+1} × Y` sends `(b, c)` to
`pr₂^* b + pr₁^* θ ⌣ pr₂^* c`. -/
@[simp]
lemma singularCohomologySphereProdEquiv_apply (m q n : ℕ) (h : m + 1 + q = n)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n)
    (c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    singularCohomologySphereProdEquiv Y m q n h (b, c) =
      TopCat.singularCohomologyMap (snd _ Y) n b +
        (sphere.{w} (m + 1) ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
          (λ_ (𝟙_ (ModuleCat.{w} k))).hom (m + 1) q n h
          (TopCat.singularCohomologyMap (fst _ Y) (m + 1)
            ((TauCeti.singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) m).symm
              (1 : k)))
          (TopCat.singularCohomologyMap (snd _ Y) q c) :=
  (rfl)

/-- The inverse of the splitting of the cohomology of `S^{m+1} × Y` sends a class `φ` to its slant
products by the class of any point `x₀` and by the standard generator of `H_{m+1}(S^{m+1}; k)`. -/
lemma singularCohomologySphereProdEquiv_symm_apply (m q n : ℕ) (h : m + 1 + q = n)
    (x₀ : sphere.{w} (m + 1))
    (φ : (sphere.{w} (m + 1) ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) n) :
    (singularCohomologySphereProdEquiv Y m q n h).symm φ =
      (singularSlant k _ _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 n n (zero_add n)
        (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k)) φ,
       singularSlant k _ _ Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom (m + 1) q n h
        ((TauCeti.reducedSingularHomologyι (𝟙_ (ModuleCat.{w} k)) (m + 1)).app _
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (𝟙_ (ModuleCat.{w} k)) (m + 1)).inv
            (1 : k))) φ) := by
  have : PathConnectedSpace (sphere.{w} (m + 1)) :=
    TauCeti.TopCat.pathConnectedSpace_diskBoundary (by omega)
  rw [TauCeti.singularHomology₀Section_eq_of_pathConnectedSpace _ x₀ (Classical.arbitrary _)]
  -- with the point used to define the inverse, both sides agree by definition
  rfl

end SphereProd

end TopCat
