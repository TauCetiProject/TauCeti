/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
public import TauCeti.AlgebraicTopology.Cohomology.Slant
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The Künneth theorem for singular cohomology

For topological spaces `X` and `Y`, the cohomology cross products
`Hᵖ(X; R, M) ⊗ H^q(Y; S, N) ⟶ Hⁿ(X × Y; R ⊗ S, P)` with `p + q = n`, along a coefficient pairing
`μ : M ⊗ N ⟶ P` (`TauCeti.singularCross`), assemble into the **cohomology Künneth map**

`⨁_{p + q = n} Hᵖ(X; R, M) ⊗ H^q(Y; S, N) ⟶ Hⁿ(X × Y; R ⊗ S, P)`

(`TopCat.singularCohomologyKunneth`), whose source is the degree `n` part of the tensor product of
the graded `k`-modules `H*(X; R, M)` and `H*(Y; S, N)`.

With coefficients in a commutative ring `k` itself, suppose that the homology modules `Hₚ(X; k)`
are projective, and finitely generated for `p ≤ n`. Then the Kronecker map
`Hᵖ(X; k) ⟶ Hom(Hₚ(X; k), k)` is an isomorphism
(`TopCat.singularKroneckerEquivOfProjectiveHomology`), and so is the canonical map
`Hom(Hₚ(X; k), k) ⊗ H^q(Y; k) ⟶ Hom(Hₚ(X; k), H^q(Y; k))` (`dualTensorHomEquiv`). The slant
products by the classes of `Hₚ(X; k)` (`TopCat.singularSlant`) send a class of
`Hⁿ(X × Y; k)` to `⨁_{p + q = n} Hom(Hₚ(X; k), H^q(Y; k))`. On cross products they are computed
by the Kronecker pairing, `(a × b) / x = ⟨a, x⟩ • b`, and vanish when the degrees of `a` and `x`
differ (`TopCat.singularSlant_singularCross`, `TopCat.singularSlant_singularCross_of_ne`); so the
slant products split the Künneth map. They are moreover injective on `Hⁿ(X × Y; k)`
(`TopCat.eq_zero_of_forall_singularSlant_eq_zero`). This gives the **Künneth theorem for
cohomology** (`TopCat.singularCohomologyKunnethIso`): the cross product induces an isomorphism

`⨁_{p + q = n} Hᵖ(X; k) ⊗ H^q(Y; k) ≅ Hⁿ(X × Y; k)`.

No hypothesis is placed on `Y`, and no `Tor` term appears: over `ℤ` this covers every `X` with
free homology of finite rank, for instance spheres
(`TopCat.singularCohomologyKunneth_sphere_bijective`, in
`TauCeti.AlgebraicTopology.Cohomology.Sphere`), but not, say, real projective space. Over
a commutative semisimple ring, for instance a field, every module is projective
(`Module.projective_of_isSemisimpleRing`), so there only the finite generation of `Hₚ(X; k)` for
`p ≤ n` is needed, for instance when `X` has finite CW type
(`TauCeti.finite_singularHomology_of_finiteCWType`). Here `Hⁿ(X × Y; k)` is computed from the
singular chains `C(X × Y; k ⊗ k)`, whose coefficient module `k ⊗ k ≅ k` is the one carried by the
cross product, and the pairing `k ⊗ k ⟶ k` is multiplication.

## Main definitions and results

* `TopCat.singularCohomologyKunneth`: the cohomology Künneth map, characterized on summands by
  `TopCat.singularCohomologyKunneth_ιTensorObj_tmul`, with
  `TopCat.singularCohomologyKunneth_naturality` its naturality in both spaces.
* `TopCat.singularCohomologyKunnethIso`, `TopCat.isIso_singularCohomologyKunneth` and
  `TopCat.singularCohomologyKunneth_bijective`: the Künneth theorem for cohomology over a
  commutative ring, when the homology of one factor is projective and finitely generated.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the cross product and Theorem 3.15, and Section 3.B, the Künneth formulas.
* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (slant products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Kunneth

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- **The cohomology Künneth map** `⨁_{p + q = n} Hᵖ(X; R, M) ⊗ H^q(Y; S, N) ⟶ Hⁿ(X × Y; R ⊗ S, P)`,
whose restriction to the summand `Hᵖ(X; R, M) ⊗ H^q(Y; S, N)` is the cohomology cross product
`TauCeti.singularCross` along the coefficient pairing `μ`. -/
def singularCohomologyKunneth (X Y : TopCat.{w}) (R S : C) (k : Type v) [CommRing k] [Linear k C]
    [MonoidalLinear k C] {M N P : C} (μ : M ⊗ N ⟶ P) (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ X.singularCohomology R k M p)
        (fun q ↦ Y.singularCohomology S k N q) n ⟶
      (X ⊗ Y).singularCohomology (R ⊗ S) k P n :=
  GradedObject.Monoidal.tensorObjDesc fun p q h ↦
    ModuleCat.ofHom (TensorProduct.lift (TauCeti.singularCross k X Y μ p q n h))

/-- The cohomology Künneth map restricts to the cohomology cross product on each summand. -/
@[simp]
lemma singularCohomologyKunneth_ιTensorObj_tmul (X Y : TopCat.{w}) {R S : C} {k : Type v}
    [CommRing k] [Linear k C] [MonoidalLinear k C] {M N P : C} (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularCohomologyKunneth X Y R S k μ n
        (GradedObject.Monoidal.ιTensorObj (fun p ↦ X.singularCohomology R k M p)
          (fun q ↦ Y.singularCohomology S k N q) p q n h (a ⊗ₜ b)) =
      TauCeti.singularCross k X Y μ p q n h a b := by
  rw [singularCohomologyKunneth, ← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom (GradedObject.Monoidal.ι_tensorObjDesc _ p q h) _).trans
    (TensorProduct.lift.tmul (f' := TauCeti.singularCross k X Y μ p q n h) a b)

/-- **Naturality of the cohomology Künneth map** in both spaces: for continuous maps
`f : X ⟶ X'` and `g : Y ⟶ Y'`, pulling back by `f^* ⊗ g^*` and then applying the Künneth map of
`X` and `Y` is applying the Künneth map of `X'` and `Y'` and then pulling back by `(f × g)^*`. -/
@[reassoc]
lemma singularCohomologyKunneth_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) (k : Type v) [CommRing k] [Linear k C] [MonoidalLinear k C] {M N P : C}
    (μ : M ⊗ N ⟶ P) (n : ℕ) :
    GradedObject.Monoidal.tensorHom
          (fun p ↦ TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f p)
          (fun q ↦ TopCat.singularCohomologyMap (R := S) (k := k) (M := N) g q) n ≫
        singularCohomologyKunneth X Y R S k μ n =
      singularCohomologyKunneth X' Y' R S k μ n ≫ TopCat.singularCohomologyMap (f ⊗ₘ g) n := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦
    ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  simp [TauCeti.singularCross_naturality]

end Kunneth

section ProjectiveHomology

variable {k : Type w} [CommRing k] (X Y : TopCat.{w})

-- Prefer the direct colimit instance of `ModuleCat`: with finiteness hypotheses on homology modules
-- in the local context, instance search otherwise finds the coproducts needed by singular homology
-- only after a long search.
attribute [local instance high] ModuleCat.hasColimitsOfShape

/-- The slant products of a class of `Hⁿ(X × Y; k ⊗ k, k)` by the classes of `Hₚ(X; k)`, as a
linear map to `Hom(Hₚ(X; k), H^q(Y; k))`. -/
private def slantCross (p q n : ℕ) (h : p + q = n) :
    (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n →ₗ[k]
      (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X →ₗ[k]
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :=
  (singularSlant k (𝟙_ (ModuleCat.{w} k)) X Y (𝟙 _) p q n h).flip

private lemma slantCross_apply (p q n : ℕ) (h : p + q = n)
    (α : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    slantCross X Y p q n h α x = singularSlant k (𝟙_ (ModuleCat.{w} k)) X Y (𝟙 _) p q n h x α :=
  rfl

/-- On the summand `Hᵖ'(X; k) ⊗ H^q'(Y; k)`, the Künneth map followed by the slant products by
`Hₚ(X; k)` vanishes when `p ≠ p'`. -/
private lemma slantCross_singularCohomologyKunneth_ιTensorObj_of_ne {p q p' q' n : ℕ}
    (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    (u : (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p' ⊗
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q' :)) :
    slantCross X Y p q n h
      (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
        (GradedObject.Monoidal.ιTensorObj
          (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
          (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
          p' q' n h' u)) = 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul a b =>
    ext x
    rw [singularCohomologyKunneth_ιTensorObj_tmul, slantCross_apply,
      singularSlant_singularCross_of_ne _ _ _ _ h' h hp, LinearMap.zero_apply]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

variable [hX : ∀ p, Projective (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
  (𝟙_ (ModuleCat.{w} k))).obj X)]

/-- For finitely generated projective `Hₚ(X; k)`, the Kronecker map of `X` identifies
`Hᵖ(X; k) ⊗ H^q(Y; k)` with `Hom(Hₚ(X; k), H^q(Y; k))`, through `Hom(A, k) ⊗ B ≅ Hom(A, B)` for
finitely generated projective `A`: the class `a ⊗ b` is sent to `x ↦ ⟨a, x⟩ • b`. -/
private def kroneckerTensorEquiv (p q : ℕ)
    (hp : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    TensorProduct k (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) ≃ₗ[k]
      (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X →ₗ[k]
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :=
  haveI := hp
  TensorProduct.congr
      ((X.singularKroneckerEquivOfProjectiveHomology _ _ p).trans ModuleCat.homLinearEquiv)
      (LinearEquiv.refl k _) ≪≫ₗ
    dualTensorHomEquiv k _ _

private lemma kroneckerTensorEquiv_tmul_apply (p q : ℕ)
    (hp : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X))
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    kroneckerTensorEquiv X Y p q hp (a ⊗ₜ b) x = (X.singularKronecker k p a x : k) • b := by
  simp [kroneckerTensorEquiv]

/-- On the summand `Hᵖ(X; k) ⊗ H^q(Y; k)`, the Künneth map followed by the slant products by
`Hₚ(X; k)` is the identification `kroneckerTensorEquiv`. -/
private lemma slantCross_singularCohomologyKunneth_ιTensorObj (p q n : ℕ) (h : p + q = n)
    (hp : Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X))
    (u : (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p ⊗
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q :)) :
    slantCross X Y p q n h
      (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
        (GradedObject.Monoidal.ιTensorObj
          (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
          (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
          p q n h u)) =
      kroneckerTensorEquiv X Y p q hp u := by
  induction u using TensorProduct.inductionOn with
  | tmul a b =>
    ext x
    rw [singularCohomologyKunneth_ιTensorObj_tmul, slantCross_apply,
      singularSlant_singularCross_leftUnitor, kroneckerTensorEquiv_tmul_apply]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The inverse of the cohomology Künneth map, as a linear map: a class of
`Hⁿ(X × Y; k ⊗ k, k)` is sent to the sum over `p + q = n` of the preimages under
`kroneckerTensorEquiv` of its slant products by the classes of `Hₚ(X; k)`. -/
private def singularCohomologyKunnethInvAux (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n →ₗ[k]
      GradedObject.Monoidal.tensorObj (C := ModuleCat.{w} k)
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :=
  ∑ x : Finset.antidiagonal n,
    (GradedObject.Monoidal.ιTensorObj
      (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
      (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
      x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2)).hom ∘ₗ
    (kroneckerTensorEquiv X Y x.1.1 x.1.2
      (hX _ (by have := Finset.mem_antidiagonal.1 x.2; omega))).symm.toLinearMap ∘ₗ
      slantCross X Y x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2)

/-- The inverse of the cohomology Künneth map. -/
private def singularCohomologyKunnethInv (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n ⟶
      GradedObject.Monoidal.tensorObj
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :=
  ModuleCat.ofHom (singularCohomologyKunnethInvAux X Y n hX)

private lemma singularCohomologyKunnethInv_apply (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X))
    (α : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n) :
    singularCohomologyKunnethInv X Y n hX α = ∑ x : Finset.antidiagonal n,
      GradedObject.Monoidal.ιTensorObj
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
        x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2)
        ((kroneckerTensorEquiv X Y x.1.1 x.1.2
            (hX _ (by have := Finset.mem_antidiagonal.1 x.2; omega))).symm
          (slantCross X Y x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2) α)) :=
  LinearMap.sum_apply _ _ α

private lemma singularCohomologyKunneth_comp_singularCohomologyKunnethInv (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n ≫
      singularCohomologyKunnethInv X Y n hX = 𝟙 _ := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ModuleCat.hom_ext ?_
  ext u
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Category.comp_id]
  rw [singularCohomologyKunnethInv_apply, Fintype.sum_eq_single ⟨(p, q), by simpa using h⟩]
  · rw [slantCross_singularCohomologyKunneth_ιTensorObj X Y p q n h (hX p (by omega)),
      LinearEquiv.symm_apply_apply]
  · intro x hx
    have hxp : x.1.1 ≠ p := fun hxp ↦ hx (Subtype.ext (Prod.ext hxp (by
      have := Finset.mem_antidiagonal.1 x.2
      dsimp only
      omega)))
    rw [slantCross_singularCohomologyKunneth_ιTensorObj_of_ne X Y _ h hxp, map_zero, map_zero]

private lemma singularCohomologyKunnethInv_comp_singularCohomologyKunneth (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    singularCohomologyKunnethInv X Y n hX ≫
      singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n = 𝟙 _ := by
  ext α : 2
  -- classes of `Hⁿ(X × Y; k ⊗ k, k)` are determined by their slant products by the homology of
  -- `X`, and the composite does not change these
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply,
    ← sub_eq_zero]
  refine eq_zero_of_forall_singularSlant_eq_zero (𝟙_ (ModuleCat.{w} k)) X Y _
    fun p q h x ↦ ?_
  rw [map_sub, sub_eq_zero, ← slantCross_apply, ← slantCross_apply,
    singularCohomologyKunnethInv_apply, map_sum, map_sum, LinearMap.sum_apply,
    Fintype.sum_eq_single ⟨(p, q), by simpa using h⟩]
  · rw [slantCross_singularCohomologyKunneth_ιTensorObj X Y p q n h (hX p (by omega)),
      LinearEquiv.apply_symm_apply]
  · intro x hx
    have hxp : p ≠ x.1.1 := fun hxp ↦ hx (Subtype.ext (Prod.ext hxp.symm (by
      have := Finset.mem_antidiagonal.1 x.2
      dsimp only
      omega)))
    rw [slantCross_singularCohomologyKunneth_ιTensorObj_of_ne X Y h _ hxp, LinearMap.zero_apply]

/-- **The Künneth isomorphism for cohomology**: over a commutative ring `k`, if the homology
`Hₚ(X; k)` is projective in every degree and finitely generated in degrees `p ≤ n`, the cohomology
cross product induces an isomorphism `⨁_{p + q = n} Hᵖ(X; k) ⊗ H^q(Y; k) ≅ Hⁿ(X × Y; k)`, for
every space `Y`. Here the product is computed from singular chains with coefficients in
`k ⊗ k ≅ k`, and the pairing `k ⊗ k ⟶ k` is multiplication. Over a commutative semisimple ring,
for instance a field, every module is projective (`Module.projective_of_isSemisimpleRing`), so
only the finite generation of `Hₚ(X; k)` is needed there. -/
def singularCohomologyKunnethIso (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n ≅
      (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n where
  hom := singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
  inv := singularCohomologyKunnethInv X Y n hX
  hom_inv_id := singularCohomologyKunneth_comp_singularCohomologyKunnethInv X Y n hX
  inv_hom_id := singularCohomologyKunnethInv_comp_singularCohomologyKunneth X Y n hX

@[simp]
lemma singularCohomologyKunnethIso_hom (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    (singularCohomologyKunnethIso X Y n hX).hom =
      singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n :=
  (rfl)

/-- Over a commutative ring, the cohomology Künneth map is an isomorphism when the homology of `X`
is projective, and finitely generated in degrees `p ≤ n`. -/
theorem isIso_singularCohomologyKunneth (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    IsIso (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  (singularCohomologyKunnethIso X Y n hX).isIso_hom

/-- **The Künneth theorem for cohomology**: over a commutative ring `k`, if the homology `Hₚ(X; k)`
is projective in every degree and finitely generated in degrees `p ≤ n`, for instance if it is
free of finite rank as for spheres and tori, the cohomology Künneth map
`⨁_{p + q = n} Hᵖ(X; k) ⊗ H^q(Y; k) ⟶ Hⁿ(X × Y; k)` is bijective for every space `Y`. -/
theorem singularCohomologyKunneth_bijective (n : ℕ)
    (hX : ∀ p ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)) :
    Function.Bijective (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k))
      (𝟙_ (ModuleCat.{w} k)) k (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  (singularCohomologyKunnethIso X Y n hX).toLinearEquiv.bijective

end ProjectiveHomology

end TopCat
