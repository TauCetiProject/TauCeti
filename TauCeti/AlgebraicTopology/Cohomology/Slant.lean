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
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.Cohomology.Point

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

On classes pulled back from one factor the slant product is computed by the cohomology of a point:

* a class `pr₁^* a` pulled back from `X` has `pr₁^* a / x = 0` whenever `q ≠ 0`
  (`TopCat.singularSlant_singularCohomologyMap_fst_eq_zero`), because by naturality it is pulled
  back from the slant product on `X × pt`, which lies in `H^q(pt) = 0`;
* a class `pr₂^* b` pulled back from `Y` has `pr₂^* b / x = 0` whenever `p ≠ 0`
  (`TopCat.singularSlant_singularCohomologyMap_snd_eq_zero`), because by naturality it is the slant
  product by the image of `x` in `Hₚ(pt) = 0`;
* for the class `x` of a point of `X` with coefficient `r`, `pr₂^* b / x` is `b` with its
  coefficients changed along `s ↦ u (r ⊗ s)`
  (`TopCat.singularSlant_homologyπ_singularCohomologyMap_snd`), and it is `b` itself when
  `u (r ⊗ s) = s` (`TopCat.singularSlant_homologyπ_singularCohomologyMap_snd_eq_self`). This uses
  the shuffle product of a vertex with a simplex
  (`TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_snd`).

So if a class on `X × Y` is `pr₁^* e + φ`, for instance the first Chern class
`c₁(pr₁^* E ⊗ U) = pr₁^* c₁(E) + c₁(U)` of a line bundle twisted by a line bundle `E` on `X`, then
its slant products by the point class (`p = 0`, `q = 2`) and by loops (`p = 1`, `q = 1`) are those
of `φ`: the class `pr₁^* e` contributes to neither. Classes pulled back from `Y` survive the slant
by a point and are killed by the slant by a loop.

Slant products of cohomology cross products are computed by the Kronecker pairing: for
`a ∈ Hᵖ(X; R, M)`, `b ∈ H^q(Y; S, N)` and a pairing `μ : M ⊗ N ⟶ P`, the slant of `a × b` by
`x ∈ Hₚ(X; R)` is `b` with its coefficients changed along `n ↦ μ (⟨a, x⟩ ⊗ n)`
(`TopCat.singularSlant_singularCross`; for `a` with coefficients in `k` and the scalar
multiplication `k ⊗ N ⟶ N` as pairing, `(a × b) / x = ⟨a, x⟩ • b`,
`TopCat.singularSlant_singularCross_leftUnitor`), and the slant by a
class of another degree vanishes
(`TopCat.singularSlant_singularCross_of_ne`). Conversely, when `R` and the homology modules
`Hₚ(X; R)` are projective, a class of `Hⁿ(X × Y; R ⊗ S, M)` is determined by its slant products
by the homology classes of `X` (`TopCat.eq_zero_of_forall_singularSlant_eq_zero`), whatever the
space `Y`. Through Eilenberg–Zilber both statements are those of the tensor product of singular
chain complexes, `TauCeti.ChainComplex.slant_cup` and
`TauCeti.ChainComplex.eq_zero_of_forall_slant_eq_zero`. Together they give the Künneth theorem
for the cohomology of a product one of whose factors has finitely generated projective homology,
`TopCat.singularCohomologyKunnethIso`.

Along the multiplication `k ⊗ k ≅ k` these results characterize the classes of `Hⁿ(X × Y; M)`
pulled back from `Y`, for `X` path-connected with projective homology and `x₀ ∈ X`: slanting by
the class `[x₀]` of the point returns a pulled-back class,
`pr₂^* b / [x₀] = b` (`TopCat.singularSlant_singularHomology₀Section_singularCohomologyMap_snd`),
and a class `φ` whose slant products by all classes of positive degree vanish is `pr₂^* (φ / [x₀])`
(`TopCat.singularCohomologyMap_snd_singularSlant_of_forall_ne_zero`). The slant products of a
cup product `pr₁^* a ⌣ pr₂^* c` are those of the cross product `a × c`
(`TopCat.singularSlant_singularCup_singularCohomologyMap_fst_snd`).

## Main definitions and results

* `TopCat.singularSlant`: the slant product `Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)`.
* `TopCat.singularSlant_homologyπ`: its value on classes of cycles and cocycles.
* `TopCat.singularKronecker_singularSlant`: the evaluation law `⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩`.
* `TopCat.singularSlant_naturality`: naturality in both spaces.
* `TopCat.singularSlant_coefficient_naturality`: slanting a class with changed coefficients
  `f^* φ` along `u` is slanting `φ` along `u ≫ f`.
* `TopCat.singularSlant_linearYonedaObjMap`: naturality in the coefficient module `M`.
* `TopCat.singularSlant_singularCohomologyMap_fst_eq_zero` and
  `TopCat.singularSlant_singularCohomologyMap_snd_eq_zero`: the vanishing of the slant product of a
  class pulled back from one factor in the degrees where the cohomology or homology of a point
  vanishes.
* `TopCat.singularSlant_homologyπ_singularCohomologyMap_snd` and
  `TopCat.singularSlant_homologyπ_singularCohomologyMap_snd_eq_self`: the slant product of a class
  pulled back from `Y` by the class of a point of `X`, restated for the point classes
  `TauCeti.singularHomology₀Section` in
  `TopCat.singularSlant_singularHomology₀Section_singularCohomologyMap_snd_eq_self`.
* `TopCat.singularSlant_eq_slant`: through Eilenberg–Zilber, the slant product is the slant
  product on the tensor product of singular chain complexes.
* `TopCat.singularSlant_singularCross`, `TopCat.singularSlant_singularCross_of_ne` and
  `TopCat.singularSlant_singularCross_leftUnitor`: slant products of cross products.
* `TopCat.eq_zero_of_forall_singularSlant_eq_zero`: slant products by the homology of a factor
  with projective homology detect the cohomology of the product;
  `TopCat.eq_zero_of_forall_singularSlant_eq_zero_of_isIso` is the same along an isomorphism
  `u : R ⊗ S ≅ T`, for instance `k ⊗ k ≅ k`.
* `TopCat.mem_range_singularCohomologyMap_snd_iff`: for `X` path-connected with projective
  homology, a class of `Hⁿ(X × Y; M)` is pulled back from `Y` if and only if its slant products
  by all classes of positive degree vanish.
* `TopCat.singularSlant_singularHomology₀Section_singularCohomologyMap_snd_add_singularCup` and
  `TopCat.singularSlant_singularCohomologyMap_snd_add_singularCup`: the slant products of
  `pr₂^* b + pr₁^* a ⌣ pr₂^* c` by a point and in the degree of `a`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product of
  singular homology and cohomology).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII (products).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B, the Künneth formulas.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Simplicial

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

/-- **Naturality of the slant product in the coefficients**: for coefficient maps
`u : R ⊗ S ⟶ T` and `f : T ⟶ T'`, slanting along `u` the class `f^* φ`, whose cochains are those
of `φ` precomposed with the chain map induced by `f`, is slanting `φ` along `u ≫ f`. -/
lemma singularSlant_coefficient_naturality (X Y : TopCat.{w}) {T' : ModuleCat.{w} k}
    (u : R ⊗ S ⟶ T) (f : T ⟶ T') (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X ⊗ Y).singularCohomology T' k M n) :
    singularSlant k M X Y u p q n h x
        (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
          (((SSet.chainComplexFunctor _).map f).app (toSSet.obj (X ⊗ Y))).op) n φ) =
      singularSlant k M X Y (u ≫ f) p q n h x φ := by
  rw [singularSlant_def, singularSlant_def]
  refine (TauCeti.ChainComplex.slant_naturality
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map (u ≫ f)).app (toSSet.obj (X ⊗ Y)))
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y)))
    (𝟙 _) (𝟙 _) (((SSet.chainComplexFunctor _).map f).app (toSSet.obj (X ⊗ Y)))
    (by simp) p q n h x φ).trans ?_
  -- the identity chain maps induce identities on homology; the remaining `id x` is `x`
  simp only [op_id, CategoryTheory.Functor.map_id, TauCeti.ChainComplex.linearYonedaFunctor_obj,
    homologyMap_id, ModuleCat.hom_id, LinearMap.id_coe]
  rfl

/-- **Naturality of the slant product in the coefficients**: for a map of coefficient modules
`g : M ⟶ M'`, `g_* φ / x = g_* (φ / x)`. -/
lemma singularSlant_linearYonedaObjMap (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T)
    {M' : ModuleCat.{w} k} (g : M ⟶ M') (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X ⊗ Y).singularCohomology T k M n) :
    singularSlant k M' X Y u p q n h x
        (homologyMap (((toSSet.obj (X ⊗ Y)).chainComplex T).linearYonedaObjMap k g) n φ) =
      homologyMap (((toSSet.obj Y).chainComplex S).linearYonedaObjMap k g) q
        (singularSlant k M X Y u p q n h x φ) := by
  rw [singularSlant_def, singularSlant_def]
  exact TauCeti.ChainComplex.slant_linearYonedaObjMap _ g p q n h x φ

/-- **A class pulled back from the first factor has no slant products in positive codegree**: for
`a ∈ Hⁿ(X; T, M)` and `x ∈ Hₚ(X; R)` with `p + q = n` and `q ≠ 0`, `pr₁^* a / x = 0`. In particular
`pr₁^* a` contributes nothing to the slant products by the class of a point (`p = 0`) or by a loop
(`p = 1`) of a class of degree two. -/
@[simp]
theorem singularSlant_singularCohomologyMap_fst_eq_zero (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T)
    (p q n : ℕ) (h : p + q = n) (hq : q ≠ 0)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (a : X.singularCohomology T k M n) :
    singularSlant k M X Y u p q n h x
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst X Y) n a) = 0 := by
  -- `pr₁ = pr₁ ∘ (𝟙 × g)` for the map `g` from `Y` to a point, and slant products of classes on
  -- `X × pt` lie in `H^q(pt) = 0`
  let g : Y ⟶ of PUnit.{w + 1} := ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  rw [← CartesianMonoidalCategory.whiskerLeft_fst X g, singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, ← id_tensorHom, singularSlant_naturality]
  have := ModuleCat.subsingleton_of_isZero
    (TauCeti.isZero_singularCohomology_point S k M (of PUnit.{w + 1}) hq)
  rw [Subsingleton.elim (singularSlant k M X _ u p q n h _ _) 0, map_zero]

/-- **A class pulled back from the second factor has no slant products by classes of positive
degree**: for `b ∈ Hⁿ(Y; T, M)` and `x ∈ Hₚ(X; R)` with `p + q = n` and `p ≠ 0`,
`pr₂^* b / x = 0`. In particular `pr₂^* b` has no slant products by loops. -/
@[simp]
theorem singularSlant_singularCohomologyMap_snd_eq_zero (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T)
    (p q n : ℕ) (h : p + q = n) (hp : p ≠ 0)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (b : Y.singularCohomology T k M n) :
    singularSlant k M X Y u p q n h x
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b) = 0 := by
  -- `pr₂ = pr₂ ∘ (f × 𝟙)` for the map `f` from `X` to a point, and `f_* x ∈ Hₚ(pt) = 0`
  let f : X ⟶ of PUnit.{w + 1} := ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  rw [← CartesianMonoidalCategory.whiskerRight_snd f Y, singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, ← tensorHom_id, singularSlant_naturality]
  have := ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{w} k) p R
      (of PUnit.{w + 1}) hp)
  rw [Subsingleton.elim (((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).map f x) 0,
    map_zero, LinearMap.zero_apply, map_zero]

/-- **The slant product of a class pulled back from the second factor by the class of a point**:
let `z` be the singular `0`-cycle of `X` given by a singular vertex `x` with coefficient `r ∈ R`,
and let `c : S ⟶ T` be the coefficient map `s ↦ u (r ⊗ s)`. Then for `b ∈ H^q(Y; T, M)`,
`pr₂^* b / [z] = c^* b ∈ H^q(Y; S, M)`, the class `b` with its coefficients changed along `c`. -/
theorem singularSlant_homologyπ_singularCohomologyMap_snd (X Y : TopCat.{w})
    (u : R ⊗ S ⟶ T) (q : ℕ) (z : ((toSSet.obj X).chainComplex R).cycles 0)
    (x : (toSSet.obj X) _⦋0⦌) (r : R)
    (hz : ((toSSet.obj X).chainComplex R).iCycles 0 z = (toSSet.obj X).ιChainComplex (R := R) x r)
    (c : S ⟶ T) (hc : ∀ s, u (r ⊗ₜ s) = c s) (b : Y.singularCohomology T k M q) :
    singularSlant k M X Y u 0 q q (zero_add q) (((toSSet.obj X).chainComplex R).homologyπ 0 z)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b) =
      homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
        (((SSet.chainComplexFunctor _).map c).app (toSSet.obj Y)).op) q b := by
  refine TauCeti.ChainComplex.slant_homologyπ_zero_homologyMap _
    (SSet.chainComplexMap (toSSet.map (CartesianMonoidalCategory.snd X Y)) T) _ z q ?_ b
  -- on the summand of a singular simplex `y` of `Y`, the shuffle product with `x` followed by the
  -- projection is `y`, and the coefficient `s` becomes `u (r ⊗ s) = c s`
  rw [hz]
  refine SSet.chainComplex_hom_ext (X := toSSet.obj Y) (R := S) fun y ↦ ?_
  have hy : (toSSet.obj Y).ιChainComplex (R := S) y ≫
        TauCeti.ModuleCat.tensorMk ((toSSet.obj X).ιChainComplex (R := R) x r) =
      TauCeti.ModuleCat.tensorMk r ≫
        ((toSSet.obj X).ιChainComplex x ⊗ₘ (toSSet.obj Y).ιChainComplex y) :=
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ by simp [TauCeti.ModuleCat.tensorMk_apply])
  have hu : TauCeti.ModuleCat.tensorMk r ≫ u = c :=
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ by simpa [TauCeti.ModuleCat.tensorMk_apply] using hc s)
  rw [SSet.ιChainComplex_chainComplexFunctor_map_app_f, reassoc_of% hy, HomologicalComplex.comp_f,
    Category.assoc, ← SSet.chainComplexMap_f_chainComplexFunctor_map_app_f,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f_snd_assoc,
    SSet.ιChainComplex_chainComplexFunctor_map_app_f, reassoc_of% hu]

/-- **Slanting a class pulled back from the second factor by a point returns the class**: for the
singular `0`-cycle `z` of `X` given by a singular vertex with coefficient `r`, and a coefficient map
`u : R ⊗ S ⟶ S` with `u (r ⊗ s) = s`, such as the unit `1` of a ring `R = S = k` and the
multiplication `k ⊗ k ⟶ k`, `pr₂^* b / [z] = b` for every `b ∈ H^q(Y; S, M)`. -/
theorem singularSlant_homologyπ_singularCohomologyMap_snd_eq_self (X Y : TopCat.{w})
    (u : R ⊗ S ⟶ S) (q : ℕ) (z : ((toSSet.obj X).chainComplex R).cycles 0)
    (x : (toSSet.obj X) _⦋0⦌) (r : R)
    (hz : ((toSSet.obj X).chainComplex R).iCycles 0 z = (toSSet.obj X).ιChainComplex (R := R) x r)
    (hu : ∀ s, u (r ⊗ₜ s) = s) (b : Y.singularCohomology S k M q) :
    singularSlant k M X Y u 0 q q (zero_add q) (((toSSet.obj X).chainComplex R).homologyπ 0 z)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b) = b := by
  rw [singularSlant_homologyπ_singularCohomologyMap_snd M X Y u q z x r hz (𝟙 S) hu]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, op_id]
  rw [HomologicalComplex.homologyMap_id]
  rfl

/-- **Slanting a class pulled back from the second factor by the class of a point returns the
class**: `pr₂^* b / [x₀] = b` for the class `[x₀] ∈ H₀(X; R)` of a point `x₀` with coefficient `r`
(`TauCeti.singularHomology₀Section`), along a coefficient map `u : R ⊗ S ⟶ S` with
`u (r ⊗ s) = s`. -/
theorem singularSlant_singularHomology₀Section_singularCohomologyMap_snd_eq_self
    (X Y : TopCat.{w}) (u : R ⊗ S ⟶ S) (q : ℕ) (x₀ : X) (r : R) (hu : ∀ s, u (r ⊗ₜ s) = s)
    (b : Y.singularCohomology S k M q) :
    singularSlant k M X Y u 0 q q (zero_add q) (TauCeti.singularHomology₀Section R x₀ r)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b) = b := by
  let z := ((toSSet.obj X).chainComplex R).liftCycles
    ((toSSet.obj X).ιChainComplex (toSSetObj₀Equiv.symm x₀)) 0 (by simp) (by simp) r
  have hx : TauCeti.singularHomology₀Section R x₀ r =
      ((toSSet.obj X).chainComplex R).homologyπ 0 z := by
    rw [TauCeti.singularHomology₀Section_def, SSet.ιHomology₀_def]
    -- the class of the vertex is the composite `liftCycles ≫ homologyπ` applied to `r`
    rfl
  rw [hx]
  exact singularSlant_homologyπ_singularCohomologyMap_snd_eq_self M X Y u q z
    (toSSetObj₀Equiv.symm x₀) r
    (ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i ((toSSet.obj X).chainComplex R)
      ((toSSet.obj X).ιChainComplex (toSSetObj₀Equiv.symm x₀)) 0 (by simp) (by simp)) r)
    hu b


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
@[simp]
theorem singularSlant_singularCross_of_ne (X Y : TopCat.{w}) {M N : ModuleCat.{w} k}
    (P : ModuleCat.{w} k) (μ : M ⊗ N ⟶ P) {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n)
    (hp : p' ≠ p) (x : ((singularHomologyFunctor (ModuleCat.{w} k) p').obj R).obj X)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularSlant k P X Y (𝟙 (R ⊗ S)) p' q' n h' x
      (TauCeti.singularCross k X Y μ p q n h a b) = 0 := by
  rw [singularSlant_eq_slant, TauCeti.singularEilenbergZilberCohomologyIso_hom_singularCross]
  exact TauCeti.ChainComplex.slant_cup_of_ne (K := (toSSet.obj X).chainComplex R) μ h h' hp x a b

/-- **The slant product of a cross product with coefficients in `k`**: for `a ∈ Hᵖ(X; k)`,
`b ∈ H^q(Y; N)` and `x ∈ Hₚ(X; k)`, with the scalar multiplication `k ⊗ N ⟶ N` as pairing,
`(a × b) / x = ⟨a, x⟩ • b`. -/
@[simp]
theorem singularSlant_singularCross_leftUnitor (X Y : TopCat.{w}) {N : ModuleCat.{w} k}
    (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k N q) :
    singularSlant k N X Y (𝟙 _) p q n h x
        (TauCeti.singularCross k X Y (λ_ N).hom p q n h a b) =
      (X.singularKronecker k p a x : k) • b := by
  rw [singularSlant_singularCross]
  -- the coefficient map `n ↦ ⟨a, x⟩ n` is multiplication by the scalar `⟨a, x⟩`
  have hmap (r : k) : ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{w} k))).linearYonedaObjMap k
      (TauCeti.ModuleCat.tensorMk r ≫ (λ_ N).hom) = r • 𝟙 _ := by
    have hr : TauCeti.ModuleCat.tensorMk r ≫ (λ_ N).hom = r • 𝟙 _ :=
      ModuleCat.hom_ext (LinearMap.ext fun v ↦ by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
          ModuleCat.hom_id, LinearMap.id_apply]
        exact (congrArg (ModuleCat.Hom.hom (λ_ N).hom)
          (TauCeti.ModuleCat.tensorMk_apply (N := N) r v)).trans
            (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r v))
    rw [hr, ChainComplex.linearYonedaObjMap_smul, ChainComplex.linearYonedaObjMap_id]
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

/-- **Slant products along an isomorphism detect the cohomology of a product**: if `R` and the
homology modules `Hₚ(X; R)` are projective and `u : R ⊗ S ⟶ T` is an isomorphism, a class
`φ ∈ Hⁿ(X × Y; T, M)` whose slant products along `u` by all classes of `Hₚ(X; R)` vanish is zero.
For `R = S = T = k` and `u` the multiplication `k ⊗ k ≅ k`, this applies to the cohomology of
`X × Y` with coefficients in `M`, computed from the singular chains with coefficients in `k`. -/
theorem eq_zero_of_forall_singularSlant_eq_zero_of_isIso (X Y : TopCat.{w})
    [Module.Projective k R]
    [∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)]
    (u : R ⊗ S ⟶ T) [IsIso u] {n : ℕ} (φ : (X ⊗ Y).singularCohomology T k M n)
    (hφ : ∀ p q (h : p + q = n) (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X),
      singularSlant k M X Y u p q n h x φ = 0) : φ = 0 := by
  -- changing the coefficients of the product along the isomorphism `u` is injective
  have he := (ModuleCat.mono_iff_injective (homologyMap
    ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
      (((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y))).op) n)).1 inferInstance
  refine he ((eq_zero_of_forall_singularSlant_eq_zero M X Y _ fun p q h x ↦ ?_).trans
    (map_zero _).symm)
  rw [singularSlant_coefficient_naturality, Category.id_comp]
  exact hφ p q h x

section PullbackFromFactor

/-- **Slanting a class pulled back from `Y` by a point of `X` returns it**:
`pr₂^* b / [x] = b`, for the class `[x] ∈ H₀(X; k)` of a point and the slant product along the
multiplication `k ⊗ k ≅ k`. -/
@[simp]
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
    obtain ⟨r, rfl⟩ : ∃ r : k,
        x = r • TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x₀ (1 : k) :=
      ⟨_, TauCeti.singularHomology₀_eq_smul_singularHomology₀Section x₀ x⟩
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      singularSlant_singularHomology₀Section_singularCohomologyMap_snd, sub_self]
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
  rw [TauCeti.singularCup_fst_snd_eq_homologyMap_singularCross,
    singularSlant_coefficient_naturality, Iso.hom_inv_id]

/-- **Slanting `pr₂^* b + pr₁^* a ⌣ pr₂^* c` by a point**: for `a ∈ Hᵖ(X; k)` with `p ≠ 0`, the
slant product of `pr₂^* b + pr₁^* a ⌣ pr₂^* c ∈ Hⁿ(X × Y; M)` by the class `[x] ∈ H₀(X; k)` of a
point is `b`. -/
theorem singularSlant_singularHomology₀Section_singularCohomologyMap_snd_add_singularCup
    (X Y : TopCat.{w}) (x : X) {p q n : ℕ} (h : p + q = n) (hp : p ≠ 0)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n)
    (c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M q) :
    singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom 0 n n (zero_add n)
        (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x (1 : k))
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b +
          (X ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom p q n h
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst X Y) p a)
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q c)) = b := by
  rw [map_add, singularSlant_singularHomology₀Section_singularCohomologyMap_snd,
    singularSlant_singularCup_singularCohomologyMap_fst_snd,
    singularSlant_singularCross_of_ne _ _ _ _ _ _ hp.symm, add_zero]

/-- **Slanting `pr₂^* b + pr₁^* a ⌣ pr₂^* c` in the degree of `a`**: for `a ∈ Hᵖ(X; k)` with
`p ≠ 0` and `x ∈ Hₚ(X; k)`, the slant product of `pr₂^* b + pr₁^* a ⌣ pr₂^* c ∈ Hⁿ(X × Y; M)` by
`x` is `⟨a, x⟩ • c`. -/
theorem singularSlant_singularCohomologyMap_snd_add_singularCup (X Y : TopCat.{w}) {p q n : ℕ}
    (h : p + q = n) (hp : p ≠ 0)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n)
    (c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M q) :
    singularSlant k M X Y (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h x
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b +
          (X ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom p q n h
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst X Y) p a)
            (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q c)) =
      (X.singularKronecker k p a x : k) • c := by
  rw [map_add, singularSlant_singularCohomologyMap_snd_eq_zero M X Y _ p q n h hp x b, zero_add,
    singularSlant_singularCup_singularCohomologyMap_fst_snd, singularSlant_singularCross_leftUnitor]

end PullbackFromFactor

end TopCat
