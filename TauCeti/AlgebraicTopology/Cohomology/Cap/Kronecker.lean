/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero

/-!
# The Kronecker pairing of singular cap and cup products

For a space `X`, a coefficient morphism `u : T ⟶ R ⊗ S`, a singular cohomology class
`α ∈ Hᵖ(X; R, 𝟙)` with values in the tensor unit and a class `β ∈ H^q(X; S, N)`, the cap product
`x ⌢ α ∈ H_q(X; S)` of a class `x ∈ Hₙ(X; T)`, `n = p + q`, taken along the left unitor
`𝟙 ⊗ S ⟶ S`, satisfies

`⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`,

where the cup product is taken along `u` and the left unitor `𝟙 ⊗ N ⟶ N`
(`TopCat.singularCap_comp_singularKronecker`).  There is no sign: with the front-face convention
of the Alexander–Whitney diagonal both sides evaluate `α` on the front `p`-face and `β` on the back
`q`-face of each singular simplex.  For modules over a commutative ring `k`, with all coefficients
the module `k` and `u` the inverse left unitor, this is the identity
`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩` of Hatcher, Section 3.3, which makes the cap product the adjoint of
the cup product under the Kronecker pairing.

For a class `μ ∈ Hₙ(X; k)`, evaluating cup products on `μ` is the bilinear cup pairing
`TopCat.singularCupPairing`, `(α, β) ↦ ⟨α ⌣ β, μ⟩`, and the identity above says that it is
`⟨β, μ ⌢ α⟩` (`TopCat.singularCupPairing_eq_singularKronecker_singularCapLinearMap`). The cup
pairing is natural in `X` (`TopCat.singularCupPairing_naturality`) and graded commutative
(`TopCat.singularCupPairing_gradedComm`), so in a middle degree it is reflexive
(`TopCat.isRefl_singularCupPairing`), symmetric in even degree
(`TopCat.isSymm_singularCupPairing`) and, in odd degree, twice the pairing of a class with itself
vanishes (`TopCat.two_mul_singularCupPairing_self_eq_zero_of_odd`), so the pairing is alternating
when `2` is a left regular element of `k` (`TopCat.isAlt_singularCupPairing`).

The key chain-level input is `SSet.chainComplexPairing_leftUnitor_hom_f`, from
`TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing`: the action of the tensor unit on
singular chains is the left unitor.

Capping into degree zero is the Kronecker pairing up to the augmentation: for a class
`α ∈ Hⁿ(X; R, M)` and a class `x ∈ Hₙ(X; R)`, the cap product `x ⌢ α ∈ H₀(X; M)` taken along the
right unitors `R ⟶ R ⊗ 𝟙` and `M ⊗ 𝟙 ⟶ M` has augmentation `ε (x ⌢ α) = ⟨α, x⟩`
(`TopCat.singularCap_comp_singularHomology₀ε`), and likewise for a relative class
`α ∈ Hⁿ(X, A; R, M)` and a relative class `x ∈ Hₙ(X, A; R)` of a topological pair `(X, A)`
(`TopPair.singularCap_comp_singularHomology₀ε`).  On chains,
the back `0`-face of each singular `n`-simplex is a vertex, whose augmentation is the identity.

For a class `α ∈ Hᵖ(X; R, M)` with values in an arbitrary object `M`, the cap product along a
pairing `μ : M ⊗ S ⟶ L` lands in `H_q(X; L)`, and the class to evaluate on it is a class
`ψ ∈ H^q(X; L, N')` which, pulled back along the chain map `M ⊗ C(X; S) ⟶ C(X; L)` of `μ`, is the
extension `(M ◁ β) ≫ ν` of a class `β ∈ H^q(X; S, N)` along a pairing `ν : M ⊗ N ⟶ N'`
(`ChainComplex.linearYonedaObjWhiskerLeft`).  Then again `⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`, with
the cup product along `u` and `ν` (`TopCat.singularCap_comp_singularKronecker_of_homologyMap_eq`).
When `μ` is invertible, every `β` has such an extension, through the isomorphism
`M ⊗ C(X; S) ≅ C(X; L)` (`TopCat.singularCap_comp_singularKronecker_of_isIso`, an instance of
`TauCeti.ChainComplex.cap_comp_kronecker_of_isIso`); for modules over `k`
this pairs `α ∈ Hᵖ(X; M)` with `β ∈ H^q(X; k)`, the general coefficient form of the identity.  For
a pair `(X, A)` the same identities hold for the relative cap product of a relative class
`α ∈ Hᵖ(X, A; R, M)` with a relative class `x ∈ Hₙ(X, A; T)`, with the relative cup product
`α ⌣ β ∈ Hⁿ(X, A; T, N')` along the relative Alexander–Whitney diagonal
(`TopPair.singularCap_comp_singularKronecker_of_homologyMap_eq` and
`TopPair.singularCap_comp_singularKronecker_of_isIso`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

open Simplicial

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T N : C}

/-- **The Kronecker pairing of a singular cap product**, `⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for a class
`α` of degree `p` with values in the tensor unit and a class `β` of degree `q` with values in `N`,
capping a class of degree `n = p + q` with `α` along `u` and the left unitor, and then evaluating
`β`, is evaluating the cup product of `α` and `β` along `u` and the left unitor of `N`. -/
theorem singularCap_comp_singularKronecker (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (p q n : ℕ) (h : p + q = n)
    (α : X.singularCohomology R k (𝟙_ C) p) (β : X.singularCohomology S k N q) :
    X.singularCap k u (λ_ S).hom p q n h α ≫ X.singularKronecker k q β =
      X.singularKronecker k n (X.singularCup k u (λ_ N).hom p q n h α β) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  refine TauCeti.ChainComplex.cap_comp_kronecker _ _ _ p q n h φ ψ ψ ?_
  rw [SSet.chainComplexPairing_leftUnitor_hom_f]
  exact (leftUnitor_naturality _).symm

variable {M N' L : C} [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The Kronecker pairing of a singular cap product with general coefficients**,
`⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for a class `α ∈ Hᵖ(X; R, M)`, cap along `u` and a pairing
`μ : M ⊗ S ⟶ L`, a class `ψ ∈ H^q(X; L, N')` and a class `β ∈ H^q(X; S, N)` such that `ψ`, pulled
back along the chain map `M ⊗ C(X; S) ⟶ C(X; L)` of `μ`, is the extension of `β` along a pairing
`ν : M ⊗ N ⟶ N'`, evaluating `ψ` on the cap product of a class of degree `n = p + q` with `α` is
evaluating on that class the cup product of `α` and `β` along `u` and `ν`. -/
theorem singularCap_comp_singularKronecker_of_homologyMap_eq (X : TopCat.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L)
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : X.singularCohomology R k M p)
    (ψ : X.singularCohomology L k N' q) (β : X.singularCohomology S k N q)
    (hψ : homologyMap (K := X.singularCochainComplex L k N')
        (L := ChainComplex.linearYonedaObj
          (((tensorLeft M).mapHomologicalComplex _).obj ((toSSet.obj X).chainComplex S)) k N')
        ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
          ((toSSet.obj X).chainComplexPairing μ).op) q ψ =
      homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β) :
    X.singularCap k u μ p q n h α ≫ X.singularKronecker k q ψ =
      X.singularKronecker k n (X.singularCup k u ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_homologyMap_eq _ _ ν p q n h α ψ β hψ

/-- **The Kronecker pairing of a singular cap product along an invertible pairing**,
`⟨ν(M ⊗ β), x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: when the pairing `μ : M ⊗ S ⟶ L` is invertible, every class
`β ∈ H^q(X; S, N)` extends along `ν : M ⊗ N ⟶ N'` to a class of `H^q(X; L, N')`, through the
isomorphism `M ⊗ C(X; S) ≅ C(X; L)` of `μ`, and evaluating it on the cap product with
`α ∈ Hᵖ(X; R, M)` is evaluating the cup product of `α` and `β`.  For modules over a commutative
ring `k`, with `R = S = T = N = k`, `μ = ν` the right unitor of a module `M` and `u` the inverse
left unitor, this pairs a class `α ∈ Hᵖ(X; M)` and a class `β ∈ H^q(X; k)`. -/
theorem singularCap_comp_singularKronecker_of_isIso (X : TopCat.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L) [IsIso μ]
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : X.singularCohomology R k M p)
    (β : X.singularCohomology S k N q) :
    X.singularCap k u μ p q n h α ≫ X.singularKronecker k q
        (homologyMap (K := ChainComplex.linearYonedaObj
            (((tensorLeft M).mapHomologicalComplex _).obj ((toSSet.obj X).chainComplex S)) k N')
          (L := X.singularCochainComplex L k N')
          ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
            (inv ((toSSet.obj X).chainComplexPairing μ)).op) q
          (homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β)) =
      X.singularKronecker k n (X.singularCup k u ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_isIso _ _ ν p q n h α β

section ModuleCat

variable (X : TopCat.{w}) (k : Type w) [CommRing k]

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
    X.singularCupPairing k h μ α β =
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
    X.singularCupPairing k h μ α β =
      (X.singularKronecker k q β).hom (X.singularCapLinearMap k h μ α) := by
  rw [singularCupPairing_apply, singularCapLinearMap_apply,
    ← singularCap_comp_singularKronecker, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Naturality of the cup pairing**, `⟨f^*α ⌣ f^*β, μ⟩ = ⟨α ⌣ β, f_*μ⟩`: for a continuous map
`f : X ⟶ Y`, the cup pairing on `μ ∈ Hₙ(X; k)` of pulled-back classes is the cup pairing on the
push-forward of `μ`. -/
theorem singularCupPairing_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCupPairing k h μ (TopCat.singularCohomologyMap f p α)
        (TopCat.singularCohomologyMap f q β) =
      Y.singularCupPairing k h
        ((((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).map f).hom μ)
        α β := by
  rw [singularCupPairing_apply, singularCupPairing_apply, singularCup_naturality,
    singularKronecker_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Graded commutativity of the cup pairing**: `⟨β ⌣ α, μ⟩ = (-1)^(p * q) ⟨α ⌣ β, μ⟩` for `α` of
degree `p` and `β` of degree `q`. -/
theorem singularCupPairing_gradedComm {p q n : ℕ} (h : p + q = n) (h' : q + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCupPairing k h' μ β α = (-1 : k) ^ (p * q) * X.singularCupPairing k h μ α β := by
  rw [singularCupPairing_apply, singularCupPairing_apply,
    X.singularCup_gradedComm_tensorUnit k (by simp [unitors_inv_equal]) h α β]
  simp

/-- In a middle degree `p` with `p + p = n`, the cup pairing on `μ` is reflexive: by graded
commutativity, `⟨α ⌣ β, μ⟩ = 0` exactly when `⟨β ⌣ α, μ⟩ = 0`. -/
theorem isRefl_singularCupPairing {p n : ℕ} (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing k h μ).IsRefl := fun α β hαβ ↦ by
  rw [X.singularCupPairing_gradedComm k h h μ α β, hαβ, mul_zero]

/-- In an even middle degree `p` with `p + p = n`, the cup pairing on `μ` is symmetric. -/
theorem isSymm_singularCupPairing {p n : ℕ} (hp : Even p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing k h μ).IsSymm :=
  LinearMap.isSymm_def.2 fun α β ↦ by
    rw [X.singularCupPairing_gradedComm k h h μ α β, (hp.mul_right p).neg_one_pow, one_mul,
      RingHom.id_apply]

/-- In an odd middle degree `p` with `p + p = n`, twice the cup pairing of a class with itself
on `μ` vanishes, `2 ⟨α ⌣ α, μ⟩ = 0`: by graded commutativity `⟨α ⌣ α, μ⟩ = -⟨α ⌣ α, μ⟩`. -/
theorem two_mul_singularCupPairing_self_eq_zero_of_odd {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    (2 : k) * X.singularCupPairing k h μ α α = 0 := by
  have hcomm := X.singularCupPairing_gradedComm k h h μ α α
  rw [(hp.mul hp).neg_one_pow, neg_one_mul, eq_neg_iff_add_eq_zero] at hcomm
  rw [two_mul, hcomm]

/-- In an odd middle degree `p` with `p + p = n`, the cup pairing on `μ` is alternating when `2`
is a left regular element of `k`, for instance when `k = ℤ` or `2` is invertible in `k`. -/
theorem isAlt_singularCupPairing (h2 : IsLeftRegular (2 : k)) {p n : ℕ} (hp : Odd p)
    (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing k h μ).IsAlt := fun α ↦
  h2.mul_left_eq_zero_iff.1 (X.two_mul_singularCupPairing_self_eq_zero_of_odd k hp h μ α)

end ModuleCat

end TopCat

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R M : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- On chains, capping a chain of degree `n` with a cochain of degree `n` along the right unitors
and taking the augmentation of the resulting degree-zero chain is evaluating the cochain. -/
lemma capChain_comp_homology₀ε (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n)
    (φ : ((toSSet.obj X).chainComplex R).X n ⟶ M) :
    TauCeti.ChainComplex.capChain k (X.alexanderWhitneyDiagonal (ρ_ R).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ M).hom) n 0 n h φ ≫
      ((toSSet.obj X).chainComplex M).cycles₀Iso.inv ≫
        ((toSSet.obj X).chainComplex M).homologyπ 0 ≫ (toSSet.obj X).homology₀ε M =
      φ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  -- The front `n`-face of an `n`-simplex is the simplex itself, and its back `0`-face is a vertex,
  -- whose augmentation is the identity.
  rw [reassoc_of% (ιChainComplex_capChain_alexanderWhitneyDiagonal X (k := k) (ρ_ R).inv
      (ρ_ M).hom n 0 n h φ σ), SSet.ιChainComplex_cycles₀Iso_inv_homologyπ_assoc,
    SSet.ιHomology₀_homology₀ε]
  simp [TauCeti.SimplexCategory.subinterval_zero_eq_id]

/-- **The augmentation of a cap product into degree zero**, `ε (x ⌢ α) = ⟨α, x⟩`: capping a class
`x ∈ Hₙ(X; R)` with a class `α ∈ Hⁿ(X; R, M)`, along the right unitors `R ⟶ R ⊗ 𝟙` and
`M ⊗ 𝟙 ⟶ M`, and then applying the augmentation `H₀(X; M) ⟶ M` is the Kronecker pairing of `α`
with `x`. -/
@[reassoc (attr := simp)]
theorem singularCap_comp_singularHomology₀ε (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n) (α : X.singularCohomology R k M n) :
    X.singularCap k (ρ_ R).inv (ρ_ M).hom n 0 n h α ≫ X.singularHomology₀ε M =
      X.singularKronecker k n α := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n α
  refine (cancel_epi (((toSSet.obj X).chainComplex R).homologyπ n)).1 ?_
  -- Zeroth singular homology is the homology of the singular chain complex only after unfolding
  -- `singularHomologyFunctor`, so `Category.assoc` is applied as a term rather than rewritten.
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [singularCap_homologyπ, singularKronecker_homologyπ,
    ← capChain_comp_homology₀ε X k n h ((X.singularCochainComplex R k M).iCycles n φ),
    ← TauCeti.ChainComplex.capCycles_i_assoc]
  -- In degree zero every chain is a cycle.
  simp only [HomologicalComplex.iCyclesIso_hom_inv_id_assoc]
  exact Category.assoc _ _ _

end TopCat

namespace TopPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R M : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- On chains, capping a relative chain of degree `n` with a relative cochain of degree `n` along
the right unitors and taking the augmentation of the resulting degree-zero chain is evaluating the
cochain. -/
lemma capChain_comp_homology₀ε (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n)
    (φ : (P.singularChainComplex R).X n ⟶ M) :
    TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal (ρ_ R).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (ρ_ M).hom) n 0 n h φ ≫
      ((TopCat.toSSet.obj P.fst).chainComplex M).cycles₀Iso.inv ≫
        ((TopCat.toSSet.obj P.fst).chainComplex M).homologyπ 0 ≫
          (TopCat.toSSet.obj P.fst).homology₀ε M =
      φ := by
  have : Epi ((P.singularChainComplexπ R).f n) :=
    inferInstanceAs (Epi (((TopPair.toSSetPair.obj P).chainComplexπ R).f n))
  refine (cancel_epi ((P.singularChainComplexπ R).f n)).1 ?_
  rw [singularChainComplexπ_capChain_alexanderWhitneyDiagonal_assoc]
  exact TopCat.capChain_comp_homology₀ε P.fst k n h _

/-- **The augmentation of a relative cap product into degree zero**, `ε (x ⌢ α) = ⟨α, x⟩`: capping
a relative class `x ∈ Hₙ(X, A; R)` with a relative class `α ∈ Hⁿ(X, A; R, M)`, along the right
unitors `R ⟶ R ⊗ 𝟙` and `M ⊗ 𝟙 ⟶ M`, and then applying the augmentation `H₀(X; M) ⟶ M` is the
Kronecker pairing of `α` with `x`. -/
theorem singularCap_comp_singularHomology₀ε (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (n : ℕ) (h : n + 0 = n) (α : P.singularCohomology R k M n) :
    P.singularCap k (ρ_ R).inv (ρ_ M).hom n 0 n h α ≫ P.fst.singularHomology₀ε M =
      P.singularKronecker k n α := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n α
  refine (cancel_epi ((P.singularChainComplex R).homologyπ n)).1 ?_
  rw [singularCap_homologyπ_assoc, singularKronecker_homologyπ,
    ← capChain_comp_homology₀ε P k n h ((P.singularCochainComplex R k M).iCycles n φ),
    ← TauCeti.ChainComplex.capCycles_i_assoc]
  -- In degree zero every chain is a cycle.
  simp only [HomologicalComplex.iCyclesIso_hom_inv_id_assoc]
  exact Category.assoc _ _ _

end TopPair

namespace TopPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N N' L : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The Kronecker pairing of a relative singular cap product**, `⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for
a pair `(X, A)`, a relative class `α ∈ Hᵖ(X, A; R, M)` capped along `u` and a pairing
`μ : M ⊗ S ⟶ L` with a relative class `x ∈ Hₙ(X, A; T)`, `n = p + q`, and absolute classes
`ψ ∈ H^q(X; L, N')` and `β ∈ H^q(X; S, N)` related as in
`TopCat.singularCap_comp_singularKronecker_of_homologyMap_eq`, evaluating `ψ` on `x ⌢ α` is
evaluating on `x` the relative cup product `α ⌣ β ∈ Hⁿ(X, A; T, N')` along the relative
Alexander–Whitney diagonal `P.alexanderWhitneyDiagonal u` and `ν`. -/
theorem singularCap_comp_singularKronecker_of_homologyMap_eq (P : TopPair.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L)
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : P.singularCohomology R k M p)
    (ψ : P.fst.singularCohomology L k N' q) (β : P.fst.singularCohomology S k N q)
    (hψ : homologyMap (K := P.fst.singularCochainComplex L k N')
        (L := ChainComplex.linearYonedaObj
          (((tensorLeft M).mapHomologicalComplex _).obj
            ((TopCat.toSSet.obj P.fst).chainComplex S)) k N')
        ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ).op) q ψ =
      homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β) :
    P.singularCap k u μ p q n h α ≫ P.fst.singularKronecker k q ψ =
      P.singularKronecker k n
        (TauCeti.ChainComplex.cup k (P.alexanderWhitneyDiagonal u) ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, TopCat.singularKronecker_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_homologyMap_eq _ _ ν p q n h α ψ β hψ

/-- **The Kronecker pairing of a relative singular cap product along an invertible pairing**:
the relative form of `TopCat.singularCap_comp_singularKronecker_of_isIso`. -/
theorem singularCap_comp_singularKronecker_of_isIso (P : TopPair.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L) [IsIso μ]
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : P.singularCohomology R k M p)
    (β : P.fst.singularCohomology S k N q) :
    P.singularCap k u μ p q n h α ≫ P.fst.singularKronecker k q
        (homologyMap (K := ChainComplex.linearYonedaObj
            (((tensorLeft M).mapHomologicalComplex _).obj
              ((TopCat.toSSet.obj P.fst).chainComplex S)) k N')
          (L := P.fst.singularCochainComplex L k N')
          ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
            (inv ((TopCat.toSSet.obj P.fst).chainComplexPairing μ)).op) q
          (homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β)) =
      P.singularKronecker k n
        (TauCeti.ChainComplex.cup k (P.alexanderWhitneyDiagonal u) ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, TopCat.singularKronecker_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_isIso _ _ ν p q n h α β

end TopPair
