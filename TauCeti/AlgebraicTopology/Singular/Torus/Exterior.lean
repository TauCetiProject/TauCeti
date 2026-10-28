/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Pontryagin.Exterior
public import TauCeti.AlgebraicTopology.Singular.Torus.Basic
public import TauCeti.Geometry.Sphere.Circle

/-!
# The homology of a torus is the exterior algebra on its first homology

For a finite type `ι` and a commutative ring `k`, the torus `Tⁱ = ι → S¹`, a product of copies of
Mathlib's unit circle `Circle`, is a commutative topological group. The Pontryagin product of
classes of degree one induces linear maps `⋀ⁿ H₁(Tⁱ; k) → Hₙ(Tⁱ; k)`
(`TopCat.pontryaginExteriorPower`). This file proves that these maps are isomorphisms
(`TauCeti.bijective_pontryaginExteriorPower_torus`, `TauCeti.torusExteriorPowerEquiv`): the
homology of a torus is the exterior algebra on its first homology. The isomorphisms are natural
in continuous homomorphisms of tori, by `TopCat.pontryaginExteriorPower_naturality`.

The proof first shows surjectivity, by induction on the number of circle factors, splitting
`T^{Option α}` as `S¹ × T^α`. By the Künneth theorem
(`TopCat.isIso_singularHomologyKunneth_of_projective_homology`) the homology of `S¹ × T^α` is
spanned by the cross products `a × b` of classes `a` of the circle, of degree zero or one, with
classes `b` of `T^α`. In degree one, `a × b` is the Pontryagin product of the images of `a` and `b`
under the inclusions of the two factors (`TopCat.pontryaginMul_map_map`). In degree zero, `a` is
a multiple of the class of the identity point, and `a × b` is the image of a class of `T^α`. Both
sides are free of rank `(card ι).choose n` (`ModuleCat.finrank_singularHomology_torus` and
`exteriorPower.finrank_eq`), and over any commutative ring a surjection between free modules of the
same finite rank is bijective.

## Main results

* `TauCeti.free_singularHomology_circle`, `TauCeti.free_singularHomology_pi_circle`,
  `TauCeti.subsingleton_singularHomology_circle`: the homology of the circle and of the torus
  `ι → S¹` is free, and that of the circle vanishes above degree one.
* `TauCeti.bijective_pontryaginExteriorPower_torus`: the Pontryagin map
  `⋀ⁿ H₁(Tⁱ; k) → Hₙ(Tⁱ; k)` is bijective.
* `TauCeti.torusExteriorPowerEquiv`: the resulting isomorphism `⋀ⁿ H₁(Tⁱ; k) ≃ₗ[k] Hₙ(Tⁱ; k)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.C, the Pontryagin ring of a torus, and Section 3.B, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits AlgebraicTopology MonObj TensorProduct TopCat

namespace TauCeti

variable (k : Type) [CommRing k]

section Surjective

/-- A morphism of commutative monoid objects with a right inverse carries surjectivity of the
Pontryagin map `⋀ⁿ H₁ → Hₙ` from its source to its target. -/
private lemma surjective_pontryaginExteriorPower_of_comp_eq_id {G G' : TopCat.{0}} [MonObj G]
    [IsCommMonObj G] [MonObj G'] [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f] (g : G' ⟶ G)
    (hgf : g ≫ f = 𝟙 G') {n : ℕ} (h : Function.Surjective (pontryaginExteriorPower k G n)) :
    Function.Surjective (pontryaginExteriorPower k G' n) := by
  intro y
  obtain ⟨w, hw⟩ := h (((singularHomologyFunctor (ModuleCat.{0} k) n).obj (𝟙_ _)).map g y)
  refine ⟨exteriorPower.map n (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (𝟙_ _)).map f).hom
    w, ?_⟩
  rw [← LinearMap.comp_apply, ← pontryaginExteriorPower_naturality, LinearMap.comp_apply, hw]
  calc _ = ((singularHomologyFunctor (ModuleCat.{0} k) n).obj (𝟙_ _)).map (g ≫ f) y := by
        rw [Functor.map_comp, CategoryTheory.comp_apply]
    _ = y := by rw [hgf, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]

/-- The image of a class under a morphism of commutative monoid objects whose source has a
surjective Pontryagin map `⋀ⁿ H₁ → Hₙ` lies in the image of the Pontryagin map of the target. -/
private lemma map_mem_range_pontryaginExteriorPower {G G' : TopCat.{0}} [MonObj G]
    [IsCommMonObj G] [MonObj G'] [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f] {n : ℕ}
    (h : Function.Surjective (pontryaginExteriorPower k G n))
    (x : ((singularHomologyFunctor (ModuleCat.{0} k) n).obj (𝟙_ _)).obj G) :
    ((singularHomologyFunctor (ModuleCat.{0} k) n).obj (𝟙_ _)).map f x ∈
      LinearMap.range (pontryaginExteriorPower k G' n) := by
  obtain ⟨w, rfl⟩ := h x
  exact ⟨_, (LinearMap.congr_fun (pontryaginExteriorPower_naturality f n) w).symm⟩

/-- The Pontryagin product of a class of degree one with a class in the image of
`⋀ⁿ⁺¹ H₁ → Hₙ₊₁` lies in the image of `⋀ⁿ⁺² H₁ → Hₙ₊₂`. -/
private lemma pontryaginMul_mem_range_pontryaginExteriorPower {G : TopCat.{0}} [MonObj G]
    [IsCommMonObj G] (n : ℕ)
    (x : ((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (𝟙_ _)).obj G)
    (w : ⋀[k]^(n + 1) (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (𝟙_ _)).obj G)) :
    pontryaginMul k G 1 (n + 1) (n + 2) (by omega) x (pontryaginExteriorPower k G (n + 1) w) ∈
      LinearMap.range (pontryaginExteriorPower k G (n + 2)) := by
  -- the quotient by the image kills the product with `x` on every `ιMulti` generator
  have key : (LinearMap.range (pontryaginExteriorPower k G (n + 2))).mkQ ∘ₗ
      pontryaginMul k G 1 (n + 1) (n + 2) (by omega) x ∘ₗ pontryaginExteriorPower k G (n + 1) =
        0 :=
    exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.zero_compAlternatingMap,
        LinearMap.comp_apply, Submodule.mkQ_apply, zero_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨exteriorPower.ιMulti k (n + 2) (Fin.cons x v), ?_⟩
      rw [pontryaginExteriorPower_ιMulti, pontryaginMultilinear_add_two_apply, Fin.cons_zero,
        Fin.tail_cons]
      exact congrArg _ (pontryaginExteriorPower_ιMulti (n + 1) v).symm)
  exact (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun key w)

end Surjective

section Circle

/-- The circle `TopCat.sphere 1` of `ℝ²` is homeomorphic to Mathlib's complex unit circle. -/
private def sphereOneIsoCircle : TopCat.sphere.{0} 1 ≅ TopCat.of Circle :=
  TopCat.isoOfHomeo (Homeomorph.ulift.trans EuclideanSpace.sphereHomeomorphCircle)

/-- The torus `ι → TopCat.sphere 1` is homeomorphic to the torus `ι → Circle`. -/
private def sphereOnePiIsoCirclePi (ι : Type) :
    TopCat.of (ι → TopCat.sphere.{0} 1) ≅ TopCat.of (ι → Circle) :=
  TopCat.isoOfHomeo
    (Homeomorph.piCongrRight fun _ ↦ Homeomorph.ulift.trans EuclideanSpace.sphereHomeomorphCircle)

/-- The homology of the circle with coefficients in a commutative ring is free. -/
instance free_singularHomology_circle (q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (𝟙_ _)).obj
      (TopCat.of Circle)) :=
  have : Module.Free k (𝟙_ (ModuleCat.{0} k)) := inferInstanceAs (Module.Free k k)
  .of_equiv (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (𝟙_ _)).mapIso
    sphereOneIsoCircle).toLinearEquiv

/-- The homology of the torus `ι → S¹` with coefficients in a commutative ring is free. -/
instance free_singularHomology_pi_circle (ι : Type) [Finite ι] (q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (𝟙_ _)).obj
      (TopCat.of (ι → Circle))) :=
  have : Module.Free k (𝟙_ (ModuleCat.{0} k)) := inferInstanceAs (Module.Free k k)
  .of_equiv (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (𝟙_ _)).mapIso
    (sphereOnePiIsoCirclePi ι)).toLinearEquiv

/-- The homology of the circle vanishes in degrees at least two. -/
theorem subsingleton_singularHomology_circle (j : ℕ) :
    Subsingleton (((singularHomologyFunctor (ModuleCat.{0} k) (j + 2)).obj (𝟙_ _)).obj
      (TopCat.of Circle)) :=
  ModuleCat.subsingleton_of_isZero <|
    ((isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne (𝟙_ (ModuleCat.{0} k))
      (n := 1) (k := j + 2) (by omega)).of_iso
        ((reducedSingularHomologySuccIso _ (j + 1)).app _).symm).of_iso
      (((singularHomologyFunctor (ModuleCat.{0} k) (j + 2)).obj (𝟙_ _)).mapIso
        sphereOneIsoCircle).symm

end Circle

section Step

/-! ### Splitting off one circle -/

variable {B G : Type} [CommMonoid B] [TopologicalSpace B] [ContinuousMul B] [CommMonoid G]
  [TopologicalSpace G] [ContinuousMul G] (f : Circle →ₜ* G) (g : B →ₜ* G)

/-- In a commutative topological monoid `G` receiving homomorphisms `f : S¹ → G` and `g : B → G`,
the image under `(z, b) ↦ f z * g b` of the cross product of a class of the circle with a class of
`B`, of total degree at least two, lies in the image of the Pontryagin map, provided that the
Pontryagin maps of `B` are surjective in positive degrees. -/
private lemma map_cross_mem_range_pontryaginExteriorPower
    (hB : ∀ m, Function.Surjective (pontryaginExteriorPower k (TopCat.of B) (m + 1)))
    (n p q : ℕ) (h : p + q = n + 2)
    (a : ((singularHomologyFunctor (ModuleCat.{0} k) p).obj (𝟙_ _)).obj (TopCat.of Circle))
    (b : ((singularHomologyFunctor (ModuleCat.{0} k) q).obj (𝟙_ _)).obj (TopCat.of B)) :
    ((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj (𝟙_ _)).map
        ((ofHom (f : C(Circle, G)) ⊗ₘ ofHom (g : C(B, G))) ≫ μ[TopCat.of G])
        (((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).map (λ_ (𝟙_ _)).hom).app _
          (singularHomologyCross (C := ModuleCat.{0} k) (TopCat.of Circle) (TopCat.of B) (𝟙_ _)
            (𝟙_ _) p q (n + 2) h (a ⊗ₜ b))) ∈
      LinearMap.range (pontryaginExteriorPower k (TopCat.of G) (n + 2)) := by
  match p, h with
  | 0, h =>
    -- `a` is unchanged by the constant map `c` at `1`, and `c × id` followed by
    -- `(z, b) ↦ f z * g b` factors through `g`
    obtain rfl : q = n + 2 := by omega
    let c : TopCat.of Circle ⟶ TopCat.of Circle := ofHom (ContinuousMap.const _ 1)
    have h₁ := singularHomology₀ε_singularHomology₀Section (𝟙_ (ModuleCat.{0} k))
      (X := TopCat.of Circle) 1
    have h₂ : (TopCat.of Circle).singularHomology₀ε (𝟙_ (ModuleCat.{0} k)) ≫
        singularHomology₀Section (𝟙_ _) (1 : Circle) ≫
          ((singularHomologyFunctor (ModuleCat.{0} k) 0).obj (𝟙_ _)).map c =
        (TopCat.of Circle).singularHomology₀ε (𝟙_ (ModuleCat.{0} k)) ≫
          singularHomology₀Section (𝟙_ _) (1 : Circle) := by
      -- `c 1 = 1` by definition of the constant map
      rw [singularHomology₀Section_naturality]
      rfl
    have hc : ((singularHomologyFunctor (ModuleCat.{0} k) 0).obj (𝟙_ _)).map c a = a :=
      calc _ = ((TopCat.of Circle).singularHomology₀ε (𝟙_ (ModuleCat.{0} k)) ≫
            singularHomology₀Section (𝟙_ _) (1 : Circle) ≫
              ((singularHomologyFunctor (ModuleCat.{0} k) 0).obj (𝟙_ _)).map c) a := by
            rw [reassoc_of% h₁]
        _ = a := by rw [h₂, h₁, CategoryTheory.id_apply]
    have hfac : (c ⊗ₘ 𝟙 (TopCat.of B)) ≫
        (ofHom (f : C(Circle, G)) ⊗ₘ ofHom (g : C(B, G))) ≫ μ[TopCat.of G] =
          CartesianMonoidalCategory.snd _ _ ≫ ofHom (g : C(B, G)) := by
      ext x
      -- the multiplication of `G` sends `(f 1, g y)` to `f 1 * g y = g y`
      exact (congrArg (· * g x.2) (map_one f)).trans (_root_.one_mul _)
    have hcross := congrArg (fun φ ↦ φ (a ⊗ₜ b)) (singularHomologyCross_naturality
      (C := ModuleCat.{0} k) c (𝟙 (TopCat.of B)) (𝟙_ _) (𝟙_ _) 0 (n + 2) (n + 2) h)
    simp only [CategoryTheory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul, hc,
      CategoryTheory.Functor.map_id, ModuleCat.id_apply] at hcross
    rw [hcross, ← CategoryTheory.comp_apply (((singularHomologyFunctor _ (n + 2)).obj _).map _),
      NatTrans.naturality, CategoryTheory.comp_apply, ← CategoryTheory.comp_apply
        (((singularHomologyFunctor _ (n + 2)).obj _).map _), ← Functor.map_comp, hfac,
      Functor.map_comp, CategoryTheory.comp_apply]
    exact map_mem_range_pontryaginExteriorPower k _ (hB (n + 1)) _
  | 1, h =>
    -- the image of `a × b` is `f_* a · g_* b`, and `g_* b` is in the image of the Pontryagin map
    obtain rfl : q = n + 1 := by omega
    rw [← pontryaginMul_map_map]
    obtain ⟨w, hw⟩ := map_mem_range_pontryaginExteriorPower k (ofHom (g : C(B, G))) (hB n) b
    rw [← hw]
    exact pontryaginMul_mem_range_pontryaginExteriorPower k n _ w
  | j + 2, h =>
    -- the homology of the circle vanishes in degrees at least two
    have := subsingleton_singularHomology_circle k j
    rw [Subsingleton.elim a 0, TensorProduct.zero_tmul, map_zero, map_zero, map_zero]
    exact Submodule.zero_mem _

/-- If `(z, b) ↦ f z * g b` has a continuous right inverse `r : G → S¹ × B`, the homology of `B`
is free, and the Pontryagin maps of `B` are surjective in positive degrees, then the Pontryagin
maps of `G` are surjective in degrees at least two. -/
private lemma surjective_pontryaginExteriorPower_add_two
    [∀ q, Module.Free k (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (𝟙_ _)).obj
      (TopCat.of B))]
    (r : C(G, Circle × B)) (hr : ∀ x, f (r x).1 * g (r x).2 = x)
    (hB : ∀ m, Function.Surjective (pontryaginExteriorPower k (TopCat.of B) (m + 1))) (n : ℕ) :
    Function.Surjective (pontryaginExteriorPower k (TopCat.of G) (n + 2)) := by
  let e : TopCat.of Circle ⊗ TopCat.of B ⟶ TopCat.of G :=
    (ofHom (f : C(Circle, G)) ⊗ₘ ofHom (g : C(B, G))) ≫ μ[TopCat.of G]
  let ρ : TopCat.of G ⟶ TopCat.of Circle ⊗ TopCat.of B := ofHom r
  have hre : ρ ≫ e = 𝟙 _ := by
    ext x
    exact hr x
  have := isIso_singularHomologyKunneth_of_projective_homology (TopCat.of Circle) (TopCat.of B)
    (𝟙_ (ModuleCat.{0} k)) (𝟙_ _) (n + 2)
  -- the quotient by the image of the Pontryagin map kills the image of every cross product, hence
  -- the image of the Künneth map, which is everything
  let Q := ModuleCat.ofHom (LinearMap.range (pontryaginExteriorPower k (TopCat.of G) (n + 2))).mkQ
  have hQ : singularHomologyKunneth (TopCat.of Circle) (TopCat.of B) (𝟙_ (ModuleCat.{0} k)) (𝟙_ _)
      (n + 2) ≫ ((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).map (λ_ (𝟙_ _)).hom).app _ ≫
        ((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj (𝟙_ _)).map e ≫ Q = 0 := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    rw [ι_singularHomologyKunneth_assoc, Limits.comp_zero]
    refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      Q, ModuleCat.hom_ofHom, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (map_cross_mem_range_pontryaginExteriorPower k f g hB n p q h a b)
  have he : ((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj (𝟙_ _)).map e ≫ Q = 0 := by
    rw [← cancel_epi (((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).map
      (λ_ (𝟙_ _)).hom).app _), ← cancel_epi (singularHomologyKunneth (TopCat.of Circle)
        (TopCat.of B) (𝟙_ (ModuleCat.{0} k)) (𝟙_ _) (n + 2)), hQ, Limits.comp_zero,
      Limits.comp_zero]
  intro y
  -- `y` is the image under `e` of its image under `r`
  have hy : y = ((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj (𝟙_ _)).map e
      (((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj (𝟙_ _)).map ρ y) := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, hre, CategoryTheory.Functor.map_id,
      CategoryTheory.id_apply]
  rw [← LinearMap.mem_range, ← Submodule.Quotient.mk_eq_zero, hy, ← Submodule.mkQ_apply]
  exact congrArg (fun φ ↦ φ (((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj
    (𝟙_ _)).map ρ y)) he

end Step

section Torus

/-! ### The torus -/

/-- Reindexing the circle factors of a torus along `e : α ≃ β`, as a continuous homomorphism. -/
private def piCongrLeftHom {α β : Type} (e : α ≃ β) : (α → Circle) →ₜ* (β → Circle) where
  toFun x := x ∘ e.symm
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by fun_prop

/-- The inclusion of the circle factor indexed by `none` into `Option α → Circle`. -/
private def optionNoneHom (α : Type) : Circle →ₜ* (Option α → Circle) where
  toFun z o := o.elim z fun _ ↦ 1
  map_one' := by
    funext o
    cases o <;> rfl
  map_mul' z w := by
    funext o
    cases o
    · rfl
    · exact (_root_.mul_one 1).symm
  continuous_toFun := continuous_pi fun o ↦ by
    cases o <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop

/-- The inclusion of the circle factors indexed by `some a` into `Option α → Circle`. -/
private def optionSomeHom (α : Type) : (α → Circle) →ₜ* (Option α → Circle) where
  toFun x o := o.elim 1 x
  map_one' := by
    funext o
    cases o <;> rfl
  map_mul' x y := by
    funext o
    cases o
    · exact (_root_.mul_one 1).symm
    · rfl
  continuous_toFun := continuous_pi fun o ↦ by
    cases o <;> simp only [Option.elim_none, Option.elim_some] <;> fun_prop

/-- The decomposition `x ↦ (x none, x ∘ some)` of `Option α → Circle`. -/
private def optionSplit (α : Type) : C(Option α → Circle, Circle × (α → Circle)) :=
  ⟨fun x ↦ (x none, fun a ↦ x (some a)), by fun_prop⟩

private lemma optionNoneHom_mul_optionSomeHom (α : Type) (x : Option α → Circle) :
    optionNoneHom α (optionSplit α x).1 * optionSomeHom α (optionSplit α x).2 = x := by
  -- the two factors are `x` and `1` at `none`, and `1` and `x` at `some a`
  funext o
  cases o with
  | none => exact _root_.mul_one (x none)
  | some a => exact _root_.one_mul (x (some a))

/-- The Pontryagin map of a torus is surjective: over any commutative ring `k`, every class in
`Hₙ(Tⁱ; k)` of the torus `Tⁱ = ι → S¹` is a sum of Pontryagin products of `n` classes of degree
one. -/
private lemma surjective_pontryaginExteriorPower_torus (ι : Type) [Finite ι] :
    ∀ n, Function.Surjective (pontryaginExteriorPower k (TopCat.of (ι → Circle)) n)
  | 0 => (bijective_pontryaginExteriorPower_zero (k := k) (G := TopCat.of (ι → Circle))).surjective
  | 1 => (bijective_pontryaginExteriorPower_one (k := k) (G := TopCat.of (ι → Circle))).surjective
  | n + 2 => by
    -- induction on `ι`, splitting off one circle at a time
    have := Fintype.ofFinite ι
    revert n
    refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ n, Function.Surjective
      (pontryaginExteriorPower k (TopCat.of (ι → Circle)) (n + 2))) ?_ ?_ ?_ ι
    · intro α β _ e ih n
      refine surjective_pontryaginExteriorPower_of_comp_eq_id k
        (ofHom (piCongrLeftHom e : C(α → Circle, β → Circle)))
        (ofHom (piCongrLeftHom e.symm : C(β → Circle, α → Circle))) ?_ (ih n)
      ext x b
      exact congrArg _ (congrArg x (e.apply_symm_apply b))
    · intro n y
      -- the torus with no factors is a point
      have : Subsingleton (((singularHomologyFunctor (ModuleCat.{0} k) (n + 2)).obj
          (𝟙_ _)).obj (TopCat.of (PEmpty → Circle))) :=
        ModuleCat.subsingleton_of_isZero
          ((isZero_reducedSingularHomologyFunctor_of_contractibleSpace (𝟙_ (ModuleCat.{0} k))
            (TopCat.of (PEmpty → Circle)) (n + 2)).of_iso
              ((reducedSingularHomologySuccIso _ (n + 1)).app _).symm)
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro α _ ih n
      refine surjective_pontryaginExteriorPower_add_two k (optionNoneHom α) (optionSomeHom α)
        (optionSplit α) (optionNoneHom_mul_optionSomeHom α) (fun m ↦ ?_) n
      cases m with
      | zero => exact bijective_pontryaginExteriorPower_one.surjective
      | succ m => exact ih m

/-- **The homology of a torus is the exterior algebra on its first homology**: over any
commutative ring `k`, the Pontryagin map `⋀ⁿ H₁(Tⁱ; k) → Hₙ(Tⁱ; k)` of the torus `Tⁱ = ι → S¹`,
sending `a₁ ∧ ⋯ ∧ aₙ` to the Pontryagin product `a₁ ⋯ aₙ`, is bijective. -/
theorem bijective_pontryaginExteriorPower_torus (ι : Type) [Finite ι] (n : ℕ) :
    Function.Bijective (pontryaginExteriorPower k (TopCat.of (ι → Circle)) n) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · have := Module.subsingleton k
      (((singularHomologyFunctor (ModuleCat.{0} k) n).obj (𝟙_ _)).obj (TopCat.of (ι → Circle)))
    have := Module.subsingleton k (⋀[k]^n (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj
      (𝟙_ _)).obj (TopCat.of (ι → Circle))))
    exact ⟨Function.injective_of_subsingleton _, surjective_pontryaginExteriorPower_torus k ι n⟩
  -- both sides are free of rank `(card ι).choose n`, so the surjection is bijective
  have : Module.Finite k (𝟙_ (ModuleCat.{0} k)) := inferInstanceAs (Module.Finite k k)
  have h₁ : Module.finrank k (𝟙_ (ModuleCat.{0} k)) = 1 := Module.finrank_self k
  have hfin (m : ℕ) : Module.Finite k (((singularHomologyFunctor (ModuleCat.{0} k) m).obj
      (𝟙_ _)).obj (TopCat.of (ι → Circle))) :=
    .equiv (((singularHomologyFunctor (ModuleCat.{0} k) m).obj (𝟙_ _)).mapIso
      (sphereOnePiIsoCirclePi ι)).toLinearEquiv
  have hrank (m : ℕ) : Module.finrank k (((singularHomologyFunctor (ModuleCat.{0} k) m).obj
      (𝟙_ _)).obj (TopCat.of (ι → Circle))) = (Nat.card ι).choose m := by
    rw [← (((singularHomologyFunctor (ModuleCat.{0} k) m).obj (𝟙_ _)).mapIso
      (sphereOnePiIsoCirclePi ι)).toLinearEquiv.finrank_eq,
      ModuleCat.finrank_singularHomology_torus, h₁, _root_.mul_one]
  refine OrzechProperty.bijective_of_surjective_of_finrank_le _
    (surjective_pontryaginExteriorPower_torus k ι n) ?_
  rw [exteriorPower.finrank_eq, hrank, hrank, Nat.choose_one_right]

/-- **The homology of a torus is the exterior algebra on its first homology**: over any
commutative ring `k`, the Pontryagin product induces an isomorphism `⋀ⁿ H₁(Tⁱ; k) ≃ Hₙ(Tⁱ; k)` for
the torus `Tⁱ = ι → S¹`, sending `a₁ ∧ ⋯ ∧ aₙ` to `a₁ ⋯ aₙ`. -/
def torusExteriorPowerEquiv (ι : Type) [Finite ι] (n : ℕ) :
    ⋀[k]^n (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (𝟙_ _)).obj
        (TopCat.of (ι → Circle))) ≃ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{0} k) n).obj (𝟙_ _)).obj (TopCat.of (ι → Circle)) :=
  LinearEquiv.ofBijective _ (bijective_pontryaginExteriorPower_torus k ι n)

@[simp]
theorem torusExteriorPowerEquiv_apply (ι : Type) [Finite ι] (n : ℕ)
    (w : ⋀[k]^n (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (𝟙_ _)).obj
      (TopCat.of (ι → Circle)))) :
    torusExteriorPowerEquiv k ι n w = pontryaginExteriorPower k (TopCat.of (ι → Circle)) n w :=
  (rfl)

end Torus

end TauCeti
