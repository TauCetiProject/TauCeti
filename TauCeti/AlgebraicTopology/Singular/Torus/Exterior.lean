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
Mathlib's unit circle `Circle`, is a commutative topological group. It is modelled as
`ι → ULift Circle`, so that `ι`, `k` and the torus can live in any universe. The Pontryagin
product of classes of degree one induces linear maps `⋀ⁿ H₁(Tⁱ; k) → Hₙ(Tⁱ; k)`
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

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

section Circle

/-- The circle `TopCat.sphere 1` of `ℝ²` is homeomorphic to Mathlib's complex unit circle. -/
private def sphereOneHomeomorphCircle : TopCat.sphere.{u} 1 ≃ₜ ULift.{u} Circle :=
  (Homeomorph.ulift.trans EuclideanSpace.sphereHomeomorphCircle).trans Homeomorph.ulift.symm

/-- The circle `TopCat.sphere 1` of `ℝ²` is isomorphic to Mathlib's complex unit circle. -/
private def sphereOneIsoCircle : TopCat.sphere.{u} 1 ≅ TopCat.of (ULift.{u} Circle) :=
  TopCat.isoOfHomeo sphereOneHomeomorphCircle

/-- The torus `ι → TopCat.sphere 1` is isomorphic to the torus `ι → ULift Circle`. -/
private def sphereOnePiIsoCirclePi (ι : Type u) :
    TopCat.of (ι → TopCat.sphere.{u} 1) ≅ TopCat.of (ι → ULift.{u} Circle) :=
  TopCat.isoOfHomeo (Homeomorph.piCongrRight fun _ ↦ sphereOneHomeomorphCircle)

/-- The homology of the circle with coefficients in a commutative ring is free. -/
instance free_singularHomology_circle (q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj
      (TopCat.of (ULift.{u} Circle))) :=
  have : Module.Free k (𝟙_ (ModuleCat.{u} k)) := inferInstanceAs (Module.Free k k)
  .of_equiv (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).mapIso
    sphereOneIsoCircle).toLinearEquiv

/-- The homology of the torus `ι → S¹` with coefficients in a commutative ring is free. -/
instance free_singularHomology_pi_circle (ι : Type u) [Finite ι] (q : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj
      (TopCat.of (ι → ULift.{u} Circle))) :=
  have : Module.Free k (𝟙_ (ModuleCat.{u} k)) := inferInstanceAs (Module.Free k k)
  .of_equiv (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).mapIso
    (sphereOnePiIsoCirclePi ι)).toLinearEquiv

/-- The homology of the circle vanishes in degrees at least two. -/
theorem subsingleton_singularHomology_circle (j : ℕ) :
    Subsingleton (((singularHomologyFunctor (ModuleCat.{u} k) (j + 2)).obj (𝟙_ _)).obj
      (TopCat.of (ULift.{u} Circle))) :=
  ModuleCat.subsingleton_of_isZero <|
    ((isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne (𝟙_ (ModuleCat.{u} k))
      (n := 1) (k := j + 2) (by omega)).of_iso
        ((reducedSingularHomologySuccIso _ (j + 1)).app _).symm).of_iso
      (((singularHomologyFunctor (ModuleCat.{u} k) (j + 2)).obj (𝟙_ _)).mapIso
        sphereOneIsoCircle).symm

end Circle

section Step

/-! ### Splitting off one circle -/

variable {B G : Type u} [CommMonoid B] [TopologicalSpace B] [ContinuousMul B] [CommMonoid G]
  [TopologicalSpace G] [ContinuousMul G] (f : ULift.{u} Circle →ₜ* G) (g : B →ₜ* G)

/-- In a commutative topological monoid `G` receiving homomorphisms `f : S¹ → G` and `g : B → G`,
the image under `(z, b) ↦ f z * g b` of the cross product of a class of the circle with a class of
`B`, of total degree at least two, lies in the image of the Pontryagin map, provided that the
Pontryagin maps of `B` are surjective in positive degrees. -/
private lemma map_cross_mem_range_pontryaginExteriorPower
    (hB : ∀ m, Function.Surjective (pontryaginExteriorPower k (TopCat.of B) (m + 1)))
    (n p q : ℕ) (h : p + q = n + 2)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) p).obj (𝟙_ _)).obj
      (TopCat.of (ULift.{u} Circle)))
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj (TopCat.of B)) :
    ((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj (𝟙_ _)).map
        ((ofHom (f : C(ULift.{u} Circle, G)) ⊗ₘ ofHom (g : C(B, G))) ≫ μ[TopCat.of G])
        (((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).map (λ_ (𝟙_ _)).hom).app _
          (singularHomologyCross (C := ModuleCat.{u} k) (TopCat.of (ULift.{u} Circle))
            (TopCat.of B) (𝟙_ _) (𝟙_ _) p q (n + 2) h (a ⊗ₜ b))) ∈
      LinearMap.range (pontryaginExteriorPower k (TopCat.of G) (n + 2)) := by
  match p, h with
  | 0, h =>
    -- `a` is unchanged by the constant map `c` at `1`, and `c × id` followed by
    -- `(z, b) ↦ f z * g b` factors through `g`
    obtain rfl : q = n + 2 := by omega
    let c : TopCat.of (ULift.{u} Circle) ⟶ TopCat.of (ULift.{u} Circle) :=
      ofHom (ContinuousMap.const _ 1)
    have : PathConnectedSpace (ULift.{u} Circle) := Homeomorph.ulift.symm.pathConnectedSpace
    have hc : ((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (𝟙_ _)).map c a = a := by
      rw [singularHomology₀_map_eq_id_of_pathConnectedSpace, ModuleCat.id_apply]
    have hfac : (c ⊗ₘ 𝟙 (TopCat.of B)) ≫
        (ofHom (f : C(ULift.{u} Circle, G)) ⊗ₘ ofHom (g : C(B, G))) ≫ μ[TopCat.of G] =
          CartesianMonoidalCategory.snd _ _ ≫ ofHom (g : C(B, G)) := by
      ext x
      -- the multiplication of `G` sends `(f 1, g y)` to `f 1 * g y = g y`
      exact (congrArg (· * g x.2) (map_one f)).trans (_root_.one_mul _)
    have hcross := congrArg (fun φ ↦ φ (a ⊗ₜ b)) (singularHomologyCross_naturality
      (C := ModuleCat.{u} k) c (𝟙 (TopCat.of B)) (𝟙_ _) (𝟙_ _) 0 (n + 2) (n + 2) h)
    simp only [CategoryTheory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul, hc,
      CategoryTheory.Functor.map_id, ModuleCat.id_apply] at hcross
    rw [hcross, ← CategoryTheory.comp_apply (((singularHomologyFunctor _ (n + 2)).obj _).map _),
      NatTrans.naturality, CategoryTheory.comp_apply, ← CategoryTheory.comp_apply
        (((singularHomologyFunctor _ (n + 2)).obj _).map _), ← Functor.map_comp, hfac,
      Functor.map_comp, CategoryTheory.comp_apply]
    exact map_mem_range_pontryaginExteriorPower _ (hB (n + 1)) _
  | 1, h =>
    -- the image of `a × b` is `f_* a · g_* b`, and `g_* b` is in the image of the Pontryagin map
    obtain rfl : q = n + 1 := by omega
    rw [← pontryaginMul_map_map]
    obtain ⟨w, hw⟩ := map_mem_range_pontryaginExteriorPower (ofHom (g : C(B, G))) (hB n) b
    rw [← hw]
    exact pontryaginMul_mem_range_pontryaginExteriorPower n _ w
  | j + 2, h =>
    -- the homology of the circle vanishes in degrees at least two
    have := subsingleton_singularHomology_circle k j
    rw [Subsingleton.elim a 0, TensorProduct.zero_tmul, map_zero, map_zero, map_zero]
    exact Submodule.zero_mem _

/-- If `(z, b) ↦ f z * g b` has a continuous right inverse `r : G → S¹ × B`, the homology of `B`
is free, and the Pontryagin maps of `B` are surjective in positive degrees, then the Pontryagin
maps of `G` are surjective in degrees at least two. -/
private lemma surjective_pontryaginExteriorPower_add_two
    [∀ q, Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) q).obj (𝟙_ _)).obj
      (TopCat.of B))]
    (r : C(G, ULift.{u} Circle × B)) (hr : ∀ x, f (r x).1 * g (r x).2 = x)
    (hB : ∀ m, Function.Surjective (pontryaginExteriorPower k (TopCat.of B) (m + 1))) (n : ℕ) :
    Function.Surjective (pontryaginExteriorPower k (TopCat.of G) (n + 2)) := by
  let e : TopCat.of (ULift.{u} Circle) ⊗ TopCat.of B ⟶ TopCat.of G :=
    (ofHom (f : C(ULift.{u} Circle, G)) ⊗ₘ ofHom (g : C(B, G))) ≫ μ[TopCat.of G]
  let ρ : TopCat.of G ⟶ TopCat.of (ULift.{u} Circle) ⊗ TopCat.of B := ofHom r
  have hre : ρ ≫ e = 𝟙 _ := by
    ext x
    exact hr x
  have := isIso_singularHomologyKunneth_of_projective_homology (TopCat.of (ULift.{u} Circle))
    (TopCat.of B) (𝟙_ (ModuleCat.{u} k)) (𝟙_ _) (n + 2)
  -- the quotient by the image of the Pontryagin map kills the image of every cross product, hence
  -- the image of the Künneth map, which is everything
  let Q := ModuleCat.ofHom (LinearMap.range (pontryaginExteriorPower k (TopCat.of G) (n + 2))).mkQ
  have hQ : singularHomologyKunneth (TopCat.of (ULift.{u} Circle)) (TopCat.of B)
      (𝟙_ (ModuleCat.{u} k)) (𝟙_ _) (n + 2) ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).map (λ_ (𝟙_ _)).hom).app _ ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj (𝟙_ _)).map e ≫ Q = 0 := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    rw [ι_singularHomologyKunneth_assoc, Limits.comp_zero]
    refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      Q, ModuleCat.hom_ofHom, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2
      (map_cross_mem_range_pontryaginExteriorPower k f g hB n p q h a b)
  have he : ((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj (𝟙_ _)).map e ≫ Q = 0 := by
    rw [← cancel_epi (((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).map
      (λ_ (𝟙_ _)).hom).app _), ← cancel_epi (singularHomologyKunneth (TopCat.of (ULift.{u} Circle))
        (TopCat.of B) (𝟙_ (ModuleCat.{u} k)) (𝟙_ _) (n + 2)), hQ, Limits.comp_zero,
      Limits.comp_zero]
  intro y
  -- `y` is the image under `e` of its image under `r`
  have hy : y = ((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj (𝟙_ _)).map e
      (((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj (𝟙_ _)).map ρ y) := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, hre, CategoryTheory.Functor.map_id,
      CategoryTheory.id_apply]
  rw [← LinearMap.mem_range, ← Submodule.Quotient.mk_eq_zero, hy, ← Submodule.mkQ_apply]
  exact congrArg (fun φ ↦ φ (((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj
    (𝟙_ _)).map ρ y)) he

end Step

section Torus

/-! ### The torus -/

/-- Reindexing the circle factors of a torus along `e : α ≃ β`, as a continuous homomorphism. -/
private def piCongrLeftHom {α β : Type u} (e : α ≃ β) :
    (α → ULift.{u} Circle) →ₜ* (β → ULift.{u} Circle) where
  toFun x := x ∘ e.symm
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by fun_prop

/-- The inclusion of the circle factor indexed by `none` into `Option α → Circle`. -/
private def optionNoneHom (α : Type u) [DecidableEq α] :
    ULift.{u} Circle →ₜ* (Option α → ULift.{u} Circle) :=
  { MonoidHom.mulSingle (fun _ : Option α ↦ ULift.{u} Circle) none with
    continuous_toFun := continuous_mulSingle (A := fun _ : Option α ↦ ULift.{u} Circle) none }

/-- The inclusion of the circle factors indexed by `some a` into `Option α → Circle`. -/
private def optionSomeHom (α : Type u) : (α → ULift.{u} Circle) →ₜ* (Option α → ULift.{u} Circle)
    where
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

private lemma optionNoneHom_mul_optionSomeHom (α : Type u) [DecidableEq α]
    (x : Option α → ULift.{u} Circle) :
    optionNoneHom α (piOptionEquivProdHomeomorph _ x).1 *
      optionSomeHom α (piOptionEquivProdHomeomorph _ x).2 = x := by
  -- the two factors are `x` and `1` at `none`, and `1` and `x` at `some a`
  rw [piOptionEquivProdHomeomorph_apply]
  funext o
  cases o with
  | none =>
    change Pi.mulSingle (M := fun _ : Option α ↦ ULift.{u} Circle) none (x none) none * 1 = x none
    rw [Pi.mulSingle_eq_same, _root_.mul_one]
  | some a =>
    change Pi.mulSingle (M := fun _ : Option α ↦ ULift.{u} Circle) none (x none) (some a) *
      x (some a) = x (some a)
    rw [Pi.mulSingle_eq_of_ne (Option.some_ne_none a), _root_.one_mul]

/-- The Pontryagin map of a torus is surjective: over any commutative ring `k`, every class in
`Hₙ(Tⁱ; k)` of the torus `Tⁱ = ι → S¹` is a sum of Pontryagin products of `n` classes of degree
one. -/
private lemma surjective_pontryaginExteriorPower_torus (ι : Type u) [Finite ι] :
    ∀ n, Function.Surjective (pontryaginExteriorPower k (TopCat.of (ι → ULift.{u} Circle)) n)
  | 0 =>
    have : PathConnectedSpace (ULift.{u} Circle) := Homeomorph.ulift.symm.pathConnectedSpace
    bijective_pontryaginExteriorPower_zero.surjective
  | 1 => bijective_pontryaginExteriorPower_one.surjective
  | n + 2 => by
    -- induction on `ι`, splitting off one circle at a time
    have := Fintype.ofFinite ι
    revert n
    refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ n, Function.Surjective
      (pontryaginExteriorPower k (TopCat.of (ι → ULift.{u} Circle)) (n + 2))) ?_ ?_ ?_ ι
    · intro α β _ e ih n
      refine surjective_pontryaginExteriorPower_of_comp_eq_id
        (ofHom (piCongrLeftHom e : C(α → ULift.{u} Circle, β → ULift.{u} Circle)))
        (ofHom (piCongrLeftHom e.symm : C(β → ULift.{u} Circle, α → ULift.{u} Circle))) ?_ (ih n)
      ext x b
      exact congrArg (fun z : ULift.{u} Circle ↦ (z.down : ℂ))
        (congrArg x (e.apply_symm_apply b))
    · intro n y
      -- the torus with no factors is a point
      have : Subsingleton (((singularHomologyFunctor (ModuleCat.{u} k) (n + 2)).obj
          (𝟙_ _)).obj (TopCat.of (PEmpty → ULift.{u} Circle))) :=
        ModuleCat.subsingleton_of_isZero (isZero_singularHomologyFunctor_of_contractibleSpace
          (𝟙_ _) (TopCat.of (PEmpty → ULift.{u} Circle)) (by omega))
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro α _ ih n
      classical
      refine surjective_pontryaginExteriorPower_add_two k (optionNoneHom α) (optionSomeHom α)
        (piOptionEquivProdHomeomorph fun _ : Option α ↦ ULift.{u} Circle :
          C(Option α → ULift.{u} Circle, ULift.{u} Circle × (α → ULift.{u} Circle)))
        (optionNoneHom_mul_optionSomeHom α) (fun m ↦ ?_) n
      cases m with
      | zero => exact bijective_pontryaginExteriorPower_one.surjective
      | succ m => exact ih m

/-- **The homology of a torus is the exterior algebra on its first homology**: over any
commutative ring `k`, the Pontryagin map `⋀ⁿ H₁(Tⁱ; k) → Hₙ(Tⁱ; k)` of the torus `Tⁱ = ι → S¹`,
sending `a₁ ∧ ⋯ ∧ aₙ` to the Pontryagin product `a₁ ⋯ aₙ`, is bijective. -/
theorem bijective_pontryaginExteriorPower_torus (ι : Type u) [Finite ι] (n : ℕ) :
    Function.Bijective (pontryaginExteriorPower k (TopCat.of (ι → ULift.{u} Circle)) n) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · have := Module.subsingleton k (((singularHomologyFunctor (ModuleCat.{u} k) n).obj
      (𝟙_ _)).obj (TopCat.of (ι → ULift.{u} Circle)))
    have := Module.subsingleton k (⋀[k]^n (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj
      (𝟙_ _)).obj (TopCat.of (ι → ULift.{u} Circle))))
    exact ⟨Function.injective_of_subsingleton _, surjective_pontryaginExteriorPower_torus k ι n⟩
  -- both sides are free of rank `(card ι).choose n`, so the surjection is bijective
  have : Module.Finite k (𝟙_ (ModuleCat.{u} k)) := inferInstanceAs (Module.Finite k k)
  have h₁ : Module.finrank k (𝟙_ (ModuleCat.{u} k)) = 1 := Module.finrank_self k
  have hfin (m : ℕ) : Module.Finite k (((singularHomologyFunctor (ModuleCat.{u} k) m).obj
      (𝟙_ _)).obj (TopCat.of (ι → ULift.{u} Circle))) :=
    .equiv (((singularHomologyFunctor (ModuleCat.{u} k) m).obj (𝟙_ _)).mapIso
      (sphereOnePiIsoCirclePi ι)).toLinearEquiv
  have hrank (m : ℕ) : Module.finrank k (((singularHomologyFunctor (ModuleCat.{u} k) m).obj
      (𝟙_ _)).obj (TopCat.of (ι → ULift.{u} Circle))) = (Nat.card ι).choose m := by
    rw [← (((singularHomologyFunctor (ModuleCat.{u} k) m).obj (𝟙_ _)).mapIso
      (sphereOnePiIsoCirclePi ι)).toLinearEquiv.finrank_eq,
      ModuleCat.finrank_singularHomology_torus, h₁, _root_.mul_one]
  refine OrzechProperty.bijective_of_surjective_of_finrank_le _
    (surjective_pontryaginExteriorPower_torus k ι n) ?_
  rw [exteriorPower.finrank_eq, hrank, hrank, Nat.choose_one_right]

/-- **The homology of a torus is the exterior algebra on its first homology**: over any
commutative ring `k`, the Pontryagin product induces an isomorphism `⋀ⁿ H₁(Tⁱ; k) ≃ Hₙ(Tⁱ; k)` for
the torus `Tⁱ = ι → S¹`, sending `a₁ ∧ ⋯ ∧ aₙ` to `a₁ ⋯ aₙ`. -/
def torusExteriorPowerEquiv (ι : Type u) [Finite ι] (n : ℕ) :
    ⋀[k]^n (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj
        (TopCat.of (ι → ULift.{u} Circle))) ≃ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).obj
        (TopCat.of (ι → ULift.{u} Circle)) :=
  LinearEquiv.ofBijective _ (bijective_pontryaginExteriorPower_torus k ι n)

@[simp]
theorem torusExteriorPowerEquiv_apply (ι : Type u) [Finite ι] (n : ℕ)
    (w : ⋀[k]^n (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (𝟙_ _)).obj
      (TopCat.of (ι → ULift.{u} Circle)))) :
    torusExteriorPowerEquiv k ι n w =
      pontryaginExteriorPower k (TopCat.of (ι → ULift.{u} Circle)) n w :=
  (rfl)

end Torus

end TauCeti
