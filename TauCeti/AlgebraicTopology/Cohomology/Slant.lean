/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Slant
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The slant product in singular cohomology

For spaces `X` and `Y`, modules `R`, `S`, `T` and `M` over a commutative ring `k` and a
coefficient map `u : R ⊗ S ⟶ T`, the **slant product**

`Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)`,  `p + q = n`,

sends a homology class `x` of `X` and a cohomology class `φ` of the product to the class `φ / x`
on `Y` represented by the cochain `σ ↦ φ (u_*(z × σ))`, where `z` is a cycle representing `x` and
`z × σ` is the shuffle product of singular chains. It is the slant product of chains and cochains
`TauCeti.ChainComplex.slant` along the shuffle map followed by `u`, with `X` as the first factor.

The slant product satisfies the evaluation law
`⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩` (`TopCat.singularKronecker_singularSlant`), where `x × y` is the
homology cross product `TopCat.singularHomologyCross`; on the classes of a cycle and a cocycle it
is the class of the slant product of representatives (`TopCat.singularSlant_homologyπ`), and it is
natural, `(f × g)^* φ / x = g^* (φ / f_* x)` (`TopCat.singularSlant_naturality`).

Slant products by homology classes turn a cohomology class on a product into classes on the second
factor. For a line bundle `U` on `X × Y` with first Chern class `c₁(U) ∈ H²(X × Y; ℤ)`, the slant
by the class of a point of `X` is a class of degree two on `Y`, and the slant by a loop in `X` is a
class of degree one on `Y`; these are the point and loop classes of universal line bundles over
moduli spaces.

Slant products of cohomology cross products are computed by the Kronecker pairing: for
`a ∈ Hᵖ(X; R, M)`, `b ∈ H^q(Y; S, N)` and a pairing `μ : M ⊗ N ⟶ P`, the slant of `a × b` by
`x ∈ Hₚ(X; R)` is `b` with its coefficients changed along `n ↦ μ (⟨a, x⟩ ⊗ n)`
(`TopCat.singularSlant_singularCross`; with coefficients in `k` and the multiplication as pairing,
`(a × b) / x = ⟨a, x⟩ • b`, `TopCat.singularSlant_singularCross_leftUnitor`), and the slant by a
class of another degree vanishes
(`TopCat.singularSlant_singularCross_of_ne`). Conversely, when `R` and the homology modules
`Hₚ(X; R)` are projective, a class of `Hⁿ(X × Y; R ⊗ S, M)` is determined by its slant products
by the homology classes of `X` (`TopCat.eq_zero_of_forall_singularSlant_eq_zero`), whatever the
space `Y`. Through Eilenberg–Zilber both statements are those of the tensor product of singular
chain complexes, `TauCeti.ChainComplex.slant_cup` and
`TauCeti.ChainComplex.eq_zero_of_forall_slant_eq_zero`. Together they give the Künneth theorem
for the cohomology of a product one of whose factors has finitely generated projective homology,
`TopCat.singularCohomologyKunnethIso`.

## Main definitions and results

* `TopCat.singularSlant`: the slant product `Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)`.
* `TopCat.singularSlant_homologyπ`: its value on classes of cycles and cocycles.
* `TopCat.singularKronecker_singularSlant`: the evaluation law `⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩`.
* `TopCat.singularSlant_naturality`: naturality in both spaces.
* `TopCat.singularSlant_eq_slant`: through Eilenberg–Zilber, the slant product is the slant
  product on the tensor product of singular chain complexes.
* `TopCat.singularSlant_singularCross`, `TopCat.singularSlant_singularCross_of_ne` and
  `TopCat.singularSlant_singularCross_leftUnitor`: slant products of cross products.
* `TopCat.eq_zero_of_forall_singularSlant_eq_zero`: slant products by the homology of a factor
  with projective homology detect the cohomology of the product.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product of
  singular homology and cohomology).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII (products).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B, the Künneth formulas.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k] {R S T : ModuleCat.{w} k} (M : ModuleCat.{w} k)

variable (k) in
/-- **The slant product** `Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)` for `p + q = n`, along the
coefficient map `u : R ⊗ S ⟶ T`: the slant product of chains and cochains along the shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` followed by the map induced by `u`. -/
def singularSlant (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n) :
    ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X →ₗ[k]
      (X ⊗ Y).singularCohomology T k M n →ₗ[k] Y.singularCohomology S k M q :=
  TauCeti.ChainComplex.slant k
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y))) p q n h

/-- The slant product of singular cohomology is the slant product of chains and cochains along
the shuffle map followed by the coefficient map. -/
lemma singularSlant_def (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n) :
    singularSlant k M X Y u p q n h =
      TauCeti.ChainComplex.slant k
        (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y)))
        p q n h :=
  (rfl)

/-- **The slant product on classes**: the slant product of the classes of a singular cycle `z` and
a singular cocycle `φ` is the class of the cochain `σ ↦ φ (u_*(z × σ))`. -/
@[simp]
lemma singularSlant_homologyπ (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    (z : ((toSSet.obj X).chainComplex R).cycles p)
    (φ : ((X ⊗ Y).singularCochainComplex T k M).cycles n) :
    singularSlant k M X Y u p q n h (((toSSet.obj X).chainComplex R).homologyπ p z)
        (((X ⊗ Y).singularCochainComplex T k M).homologyπ n φ) =
      (Y.singularCochainComplex S k M).homologyπ q
        (TauCeti.ChainComplex.slantCycles k
          (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y)))
          p q n h z φ) :=
  TauCeti.ChainComplex.slant_homologyπ _ p q n h z φ

/-- **The evaluation law of the slant product**, `⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩`: the Kronecker
pairing of the slant product `φ / x ∈ H^q(Y; S, M)` with a class `y ∈ H_q(Y; S)` is the
Kronecker pairing of `φ` with the image under `u` of the homology cross product
`x × y ∈ Hₙ(X × Y; R ⊗ S)`. -/
theorem singularKronecker_singularSlant (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ)
    (h : p + q = n) (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X ⊗ Y).singularCohomology T k M n)
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).obj Y) :
    Y.singularKronecker k q (singularSlant k M X Y u p q n h x φ) y =
      (X ⊗ Y).singularKronecker k n φ
        (((singularHomologyFunctor (ModuleCat.{w} k) n).map u).app (X ⊗ Y)
          (singularHomologyCross X Y R S p q n h (x ⊗ₜ y))) := by
  -- the cross product is the algebraic one followed by the shuffle map, so both sides evaluate
  -- `φ` on the image of the algebraic cross product under the shuffle map followed by `u`
  have hev := TauCeti.ChainComplex.kronecker_slant
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y))) p q n h x
    φ y
  rw [homologyMap_comp, ConcreteCategory.comp_apply] at hev
  rw [singularKronecker_def, singularKronecker_def, singularHomologyCross_def]
  exact hev

/-- **Naturality of the slant product** in both spaces: for continuous maps `f : X ⟶ X'` and
`g : Y ⟶ Y'`, `(f × g)^* φ / x = g^* (φ / f_* x)`. -/
lemma singularSlant_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X' ⊗ Y').singularCohomology T k M n) :
    singularSlant k M X Y u p q n h x (TopCat.singularCohomologyMap (f ⊗ₘ g) n φ) =
      TopCat.singularCohomologyMap g q
        (singularSlant k M X' Y' u p q n h
          (((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).map f x) φ) :=
  TauCeti.ChainComplex.slant_naturality _ _ (SSet.chainComplexMap (toSSet.map f) R)
    (SSet.chainComplexMap (toSSet.map g) S) (SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) T)
    (by
      rw [Category.assoc, ← ((SSet.chainComplexFunctor _).map u).naturality]
      exact shuffle_naturality_assoc f g R S _)
    p q n h x φ

/-- **The slant product through Eilenberg–Zilber**: slanting a class `φ` of `X × Y` by `x` is
slanting its image `shuffle^* φ` in the cohomology of `Hom(C(X; R) ⊗ C(Y; S), M)` by `x` along the
identity. -/
lemma singularSlant_eq_slant (X Y : TopCat.{w}) (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X ⊗ Y).singularCohomology (R ⊗ S) k M n) :
    singularSlant k M X Y (𝟙 (R ⊗ S)) p q n h x φ =
      TauCeti.ChainComplex.slant k (𝟙 (HomologicalComplex.tensorObj
        ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S))) p q n h x
        ((TauCeti.singularEilenbergZilberCohomologyIso k X Y R S M n).hom φ) := by
  rw [TauCeti.singularEilenbergZilberCohomologyIso_hom, singularSlant_def]
  refine Eq.trans ?_ (TauCeti.ChainComplex.slant_naturality
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map (𝟙 (R ⊗ S))).app (toSSet.obj (X ⊗ Y)))
    (𝟙 _) (𝟙 _) (𝟙 _) (shuffle X Y R S) (by simp) p q n h x φ (P := M)).symm
  -- the identity maps induce identities; `simp` leaves `x` against `id x`
  simp
  rfl

/-- **The slant product of a cross product**: for `a ∈ Hᵖ(X; R, M)`, `b ∈ H^q(Y; S, N)`, a pairing
`μ : M ⊗ N ⟶ P` and `x ∈ Hₚ(X; R)`, the slant `(a × b) / x` is `b` with its coefficients changed
along `n ↦ μ (⟨a, x⟩ ⊗ n)`. For coefficients in `k` and `μ` the multiplication, `(a × b) / x` is
`⟨a, x⟩ • b`. -/
theorem singularSlant_singularCross (X Y : TopCat.{w}) {M N : ModuleCat.{w} k}
    (P : ModuleCat.{w} k) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularSlant k P X Y (𝟙 (R ⊗ S)) p q n h x (TauCeti.singularCross k X Y μ p q n h a b) =
      homologyMap (((toSSet.obj Y).chainComplex S).linearYonedaObjMap k
        (TauCeti.ModuleCat.tensorMk (X.singularKronecker k p a x) ≫ μ)) q b := by
  rw [singularSlant_eq_slant, TauCeti.singularEilenbergZilberCohomologyIso_hom_singularCross,
    singularKronecker_def]
  exact TauCeti.ChainComplex.slant_cup (K := (toSSet.obj X).chainComplex R) μ p q n h x a b

/-- The slant product of a cross product of classes of degrees `p` and `q` by a homology class of
degree `p' ≠ p` vanishes. -/
theorem singularSlant_singularCross_of_ne (X Y : TopCat.{w}) {M N : ModuleCat.{w} k}
    (P : ModuleCat.{w} k) (μ : M ⊗ N ⟶ P) {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n)
    (hp : p' ≠ p) (x : ((singularHomologyFunctor (ModuleCat.{w} k) p').obj R).obj X)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularSlant k P X Y (𝟙 (R ⊗ S)) p' q' n h' x
      (TauCeti.singularCross k X Y μ p q n h a b) = 0 := by
  rw [singularSlant_eq_slant, TauCeti.singularEilenbergZilberCohomologyIso_hom_singularCross]
  exact TauCeti.ChainComplex.slant_cup_of_ne (K := (toSSet.obj X).chainComplex R) μ h h' hp x a b

/-- **The slant product of a cross product with coefficients in `k`**: for `a ∈ Hᵖ(X; k)`,
`b ∈ H^q(Y; k)` and `x ∈ Hₚ(X; k)`, with the multiplication `k ⊗ k ⟶ k` as pairing,
`(a × b) / x = ⟨a, x⟩ • b`. -/
theorem singularSlant_singularCross_leftUnitor (X Y : TopCat.{w}) (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    singularSlant k (𝟙_ (ModuleCat.{w} k)) X Y (𝟙 _) p q n h x
        (TauCeti.singularCross k X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h a b) =
      (X.singularKronecker k p a x : k) • b := by
  rw [singularSlant_singularCross]
  -- the coefficient map `n ↦ ⟨a, x⟩ n` is multiplication by the scalar `⟨a, x⟩`
  have hmap (r : k) : ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k
      (TauCeti.ModuleCat.tensorMk r ≫ (λ_ (𝟙_ (ModuleCat.{w} k))).hom) = r • 𝟙 _ := by
    have hr : TauCeti.ModuleCat.tensorMk r ≫ (λ_ (𝟙_ (ModuleCat.{w} k))).hom = r • 𝟙 _ :=
      ModuleCat.hom_ext (LinearMap.ext fun v ↦ by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
          ModuleCat.hom_id, LinearMap.id_apply]
        exact (congrArg (ModuleCat.Hom.hom (λ_ (𝟙_ (ModuleCat.{w} k))).hom)
          (TauCeti.ModuleCat.tensorMk_apply (N := 𝟙_ (ModuleCat.{w} k)) r v)).trans
            (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r v))
    ext i (c : ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{w} k))).X i ⟶ _)
    -- both sides send a cochain `c` to `r • c`
    simp [hr]
    rfl
  -- `r • 𝟙` on cohomology is `r • id`
  rw [hmap, HomologicalComplex.homologyMap_smul, homologyMap_id]
  rfl

/-- **Slant products detect the cohomology of a product**: if the coefficient module `R` and the
homology modules `Hₚ(X; R)` are projective, a class `φ ∈ Hⁿ(X × Y; R ⊗ S, M)` whose slant products
`φ / x ∈ H^q(Y; S, M)` by all classes `x ∈ Hₚ(X; R)`, `p + q = n`, vanish is zero. There is no
hypothesis on `Y`. -/
theorem eq_zero_of_forall_singularSlant_eq_zero (X Y : TopCat.{w}) [Module.Projective k R]
    [hX : ∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)] {n : ℕ}
    (φ : (X ⊗ Y).singularCohomology (R ⊗ S) k M n)
    (hφ : ∀ p q (h : p + q = n) (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X),
      singularSlant k M X Y (𝟙 (R ⊗ S)) p q n h x φ = 0) : φ = 0 := by
  -- `Hₚ(X; R)` is by definition the homology of the singular chain complex `C(X; R)`
  have (p : ℕ) : Projective (((toSSet.obj X).chainComplex R).homology p) := hX p
  refine (TauCeti.singularEilenbergZilberCohomologyIso k X Y R S M n).toLinearEquiv.injective
    ((TauCeti.ChainComplex.eq_zero_of_forall_slant_eq_zero _ fun p q h x ↦ ?_).trans
      (map_zero _).symm)
  exact (singularSlant_eq_slant M X Y p q n h x φ).symm.trans (hφ p q h x)

end TopCat
