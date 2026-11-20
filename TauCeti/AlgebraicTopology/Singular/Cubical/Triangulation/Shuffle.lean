/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Chains
public import TauCeti.AlgebraicTopology.Singular.Shuffle
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Literal integral iterated shuffle

The comparison uses the actual singular shuffle with integral coefficients. It does not
require or assert a tensor product on modules over a noncommutative coefficient ring.

## Main definitions and results

* `TauCeti.integralShuffleStep`: native integral shuffle with the positive interval, followed
  by the coefficient unitor and coordinate concatenation.
* `TauCeti.iteratedIntegralShuffle`: the literal left-associated iteration starting at a point.
* `TauCeti.iteratedIntegralShuffle_eq_orderedChain`: its equality, in every degree, with
  the positive permutation sum on the universal coordinate cube.
-/

public section
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomologicalComplex Simplicial
open Equiv Convexity Equiv.Perm
namespace TauCeti
open SingularCube

/-- The vertical coordinate is the native affine simplex classified by the prism step. -/
private lemma staircaseSimplex_prism_last {n : ℕ} (r : Fin (n + 1)) (π : Perm (Fin n))
    (w : StdSimplex ℝ (Fin (n + 2))) :
    staircaseSimplex ((snocFin r π.symm).symm) w (Fin.last n) =
      StdSimplex.homeomorphI (w.map (SSet.stdSimplex.objEquiv
        (SSet.stdSimplex.objMk₁.{0} r.succ.castSucc))) := by
  let f : Fin (n + 2) → Fin 2 := SSet.stdSimplex.objEquiv
    (SSet.stdSimplex.objMk₁.{0} r.succ.castSucc)
  let a : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) ℝ :=
    ⟨fun w ↦ affineStaircaseSimplex ((snocFin r π.symm).symm) w (Fin.last n),
      (affineStaircaseSimplex ((snocFin r π.symm).symm)).isAffineMap.eval _⟩
  let b : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) ℝ :=
    ⟨fun w ↦ (w.map f).weights 1,
      Finsupp.isAffineMap_eval.comp ((StdSimplex.isAffineMap_weights ℝ (Fin 2)).comp
        (StdSimplex.affineMap f).isAffineMap)⟩
  have h : a = b := by
    apply StdSimplex.affineMap_ext
    intro k
    simp only [a, b, ConvexSpace.AffineMap.coe_mk,
      affineStaircaseSimplex_single, staircaseVertex_prismPermutation_last, StdSimplex.map_single,
      StdSimplex.weights_single, Finsupp.single_apply]
    change (if (r : ℕ) < (k : ℕ) then (1 : ℝ) else 0) = if f k = 1 then 1 else 0
    have hf : f k = if (r : ℕ) < (k : ℕ) then 1 else 0 := by
      change (SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{0} r.succ.castSucc)) k = _
      refine (SSet.stdSimplex.objMk₁_apply.{0} _ _).trans ?_
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> first | rfl | omega
    rw [hf]
    by_cases hk : (r : ℕ) < (k : ℕ) <;> simp [hk]
  apply Subtype.ext
  rw [StdSimplex.homeomorphI_apply_coe]
  rw [staircaseSimplex_coe_apply]
  exact DFunLike.congr_fun h w

private def prismIndexEquiv (n : ℕ) :
    Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.inv _)).trans
    ((snocFinEquiv n).trans (Equiv.inv _))

private lemma prismIndexEquiv_apply {n : ℕ} (r : Fin (n + 1)) (π : Perm (Fin n)) :
    prismIndexEquiv n (r, π) = (snocFin r π.symm).symm := by
  simp [prismIndexEquiv, Perm.inv_def]

private lemma sign_prismIndex {n : ℕ} (r : Fin (n + 1)) (π : Perm (Fin n)) :
    Perm.sign (snocFin r π.symm).symm = (-1) ^ (n + (r : ℕ)) * π.sign := by
  simp [sign_snocFin, add_comm]

/-- Summing the prism insertion signs is exactly the signed sum over all larger orderings. -/
private lemma sum_prismPermutation {A : Type*} [AddCommGroup A] (n : ℕ)
    (F : Perm (Fin (n + 1)) → A) :
    (∑ π : Perm (Fin n), (π.sign : ℤ) •
      ∑ r : Fin (n + 1), ((-1 : ℤ) ^ (n + (r : ℕ))) • F ((snocFin r π.symm).symm)) =
        ∑ ρ : Perm (Fin (n + 1)), (ρ.sign : ℤ) • F ρ := by
  have hc (r : Fin (n + 1)) (π : Perm (Fin n)) :
      (π.sign : ℤ) * (-1 : ℤ) ^ (n + (r : ℕ)) = Perm.sign (snocFin r π.symm).symm := by
    have h := congrArg (fun u : ℤˣ ↦ (u : ℤ)) (sign_prismIndex r π)
    simpa [mul_comm] using h.symm
  simp only [Finset.smul_sum, smul_smul, hc]
  rw [Finset.sum_comm]
  conv_rhs => rw [← Equiv.sum_comp (prismIndexEquiv n)]
  simp only [Fintype.sum_prod_type, prismIndexEquiv_apply]

/-- Append the interval factor as the last coordinate of the original coordinate cube. -/
def snocMap (n : ℕ) :
    (TopCat.of (Fin n → unitInterval)) ⊗ TopCat.of unitInterval ⟶
      TopCat.of (Fin (n + 1) → unitInterval) :=
  TopCat.ofHom ⟨fun z ↦ Fin.snoc z.1 z.2, by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.snoc_last] using continuous_snd
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j).comp continuous_fst⟩

/-- Evaluation of coordinate concatenation. -/
@[simp]
lemma snocMap_apply (n : ℕ) (z : (Fin n → unitInterval) × unitInterval) :
    snocMap n z = Fin.snoc z.1 z.2 := by
  unfold snocMap
  rfl

private lemma singularProduct_apply {X Y : TopCat.{0}} {n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (y : (TopCat.toSSet.obj Y) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (X ⊗ Y).toSSetObjEquiv _
      ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app _ (x, y)) w =
        (X.toSSetObjEquiv _ x w, Y.toSSetObjEquiv _ y w) := by
  refine Prod.ext ?_ ?_
  · exact congrArg (fun f ↦ X.toSSetObjEquiv _ (f.app _ (x, y)) w)
      (Functor.Monoidal.μ_fst TopCat.toSSet X Y)
  · exact congrArg (fun f ↦ Y.toSSetObjEquiv _ (f.app _ (x, y)) w)
      (Functor.Monoidal.μ_snd TopCat.toSSet X Y)

private lemma classified_apply {X : TopCat.{0}} {p n : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋p⦌) (f : (Δ[p] : SSet.{0}) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquiv _ ((SSet.yonedaEquiv.symm x).app _ f) w =
      X.toSSetObjEquiv _ x (w.map (SSet.stdSimplex.objEquiv f)) := by
  exact (congrArg (fun z : (TopCat.toSSet.obj X) _⦋n⦌ ↦ X.toSSetObjEquiv _ z w)
    (SSet.yonedaEquiv_symm_app x f)).trans
      (TopCat.toSSetObjEquiv_naturality_apply (SSet.stdSimplex.objEquiv f) x w)

/-- Each native prism simplex becomes the stated staircase simplex in the cube. -/
lemma classified_prism {n : ℕ} (r : Fin (n + 1)) (π : Perm (Fin n)) :
    ((SSet.yonedaEquiv.symm
        (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π)) ⊗ₘ
      SSet.yonedaEquiv.symm (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
          (ContinuousMap.id unitInterval))) ≫
      Functor.LaxMonoidal.μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map (snocMap n)).app _
      ((SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ r),
        SSet.stdSimplex.objMk₁ r.succ.castSucc) : ((Δ[n] : SSet.{0}) ⊗ Δ[1]) _⦋n + 1⦌) =
        ((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).symm
          (staircaseSimplex ((snocFin r π.symm).symm)) := by
  apply ((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro w
  -- Pointwise evaluation of the native product functor keeps its product instance intact.
  change snocMap n (((TopCat.of (Fin n → unitInterval)) ⊗ TopCat.of unitInterval).toSSetObjEquiv _
    ((Functor.LaxMonoidal.μ TopCat.toSSet _ _).app _
      ((SSet.yonedaEquiv.symm
        (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π))).app _
          (SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ r)),
       (SSet.yonedaEquiv.symm (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
          (ContinuousMap.id unitInterval))).app _
          (SSet.stdSimplex.objMk₁ r.succ.castSucc))) w) = _
  rw [singularProduct_apply]
  rw [classified_apply, classified_apply, Equiv.apply_symm_apply,
    TauCeti.TopCat.toSSetObjEquiv_simplex₁]
  simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, Equiv.apply_symm_apply]
  -- The native degeneracy has staircaseVertex map `r.predAbove`, and `snocMap` concatenates
    -- coordinates.
  change Fin.snoc (staircaseSimplex π (w.map r.predAbove))
    (StdSimplex.homeomorphI (w.map (SSet.stdSimplex.objEquiv
      (SSet.stdSimplex.objMk₁ r.succ.castSucc)))) = staircaseSimplex ((snocFin r π.symm).symm) w
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.snoc_last]
    exact (staircaseSimplex_prism_last r π w).symm
  · simp only [Fin.snoc_castSucc]
    exact (staircaseSimplex_prism_castSucc r π w j).symm


/-- One actual integral shuffle with the positive interval, with the coefficient tensor
identified with `ℤ` by its native unitor, followed by coordinate concatenation. -/
def integralShuffleStep (n : ℕ) :
    (((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).chainComplex
      (ModuleCat.of ℤ ℤ)).X n) →+
    (((TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → unitInterval))).chainComplex
      (ModuleCat.of ℤ ℤ)).X (n + 1)) where
  toFun a := ((SSet.chainComplexMap (TopCat.toSSet.map (snocMap n))
    (ModuleCat.of ℤ ℤ)).f (n + 1)).hom
      (((((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.toSSet.obj ((TopCat.of (Fin n → unitInterval)) ⊗ TopCat.of unitInterval))).f
          (n + 1)).hom
        (((TopCat.shuffle _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))).f
          (n + 1)).hom
          ((ιTensorObj ((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).chainComplex
            (ModuleCat.of ℤ ℤ)) ((TopCat.toSSet.obj (TopCat.of unitInterval)).chainComplex
            (ModuleCat.of ℤ ℤ)) n 1 (n + 1) rfl).hom
            (a ⊗ₜ[ℤ] ((TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
                (ContinuousMap.id unitInterval))).hom 1))))
  map_zero' := by
    simp only [TensorProduct.zero_tmul, map_zero]
  map_add' a b := by
    simp only [TensorProduct.add_tmul, map_add]

/-- The native binary shuffle formula, with its actual prism simplices. -/
lemma shuffle_prism (n : ℕ) (π : Perm (Fin n)) :
    ((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).ιChainComplex
      (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π)) ⊗ₘ
      (TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex
        (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
          (ContinuousMap.id unitInterval))) ≫
      ιTensorObj _ _ n 1 (n + 1) rfl ≫
      (TopCat.shuffle _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))).f (n + 1) =
    ∑ r : Fin (n + 1), ((-1 : ℤ) ^ (n + (r : ℕ))) •
      (TopCat.toSSet.obj
        ((TopCat.of (Fin n → unitInterval)) ⊗ TopCat.of unitInterval)).ιChainComplex
        (((SSet.yonedaEquiv.symm
          (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π)) ⊗ₘ
          SSet.yonedaEquiv.symm (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
          (ContinuousMap.id unitInterval))) ≫
          Functor.LaxMonoidal.μ TopCat.toSSet _ _).app _
          ((SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ r),
        SSet.stdSimplex.objMk₁ r.succ.castSucc) : ((Δ[n] : SSet.{0}) ⊗ Δ[1]) _⦋n + 1⦌)) := by
  rw [TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f,
    SSet.shuffleChain_right_interval]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  exact congrArg (fun f ↦ ((-1 : ℤ) ^ (n + (r : ℕ))) • f)
    (SSet.ι_chainComplexMap_f _ _ _ _ _)

private lemma eval_zsmul {M N : ModuleCat.{0} ℤ} (g : M ⟶ N) (a : M) (k : ℤ) :
    (k • g).hom a = k • g.hom a := by
  rw [ModuleCat.hom_zsmul]
  exact map_zsmul (LinearMap.evalAddMonoidHom a) k g.hom

private lemma integralShuffleStep_apply_ι (n : ℕ)
  (x : (TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))) _⦋n⦌) : integralShuffleStep n
    (((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ)
      x).hom 1) =
    ((λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
      ((TopCat.toSSet.obj _).ιChainComplex
        x ⊗ₘ
        (TopCat.toSSet.obj (TopCat.of unitInterval)).ιChainComplex
          (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
            (ContinuousMap.id unitInterval))) ≫
      ιTensorObj _ _ n 1 (n + 1) rfl ≫
      (TopCat.shuffle _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))).f (n + 1) ≫
      ((((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
          (TopCat.toSSet.obj ((TopCat.of (Fin n → unitInterval)) ⊗ TopCat.of unitInterval))).f
            (n + 1)) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (snocMap n))
        (ModuleCat.of ℤ ℤ)).f (n + 1)).hom 1 := by
  -- The coefficient unitor inverse sends `1` to `1 ⊗ 1`, and tensor maps act factorwise.
  rfl

/-- One integral shuffle inserts the interval at each possible ordered step. -/
lemma integralShuffleStep_simplex (n : ℕ) (π : Perm (Fin n)) :
    integralShuffleStep n
      (((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π))).hom 1) =
      ∑ r : Fin (n + 1), ((-1 : ℤ) ^ (n + (r : ℕ))) •
        ((TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → unitInterval))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          (((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).symm
            (staircaseSimplex ((snocFin r π.symm).symm)))).hom 1 := by
  let A := (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
      (TopCat.toSSet.obj ((TopCat.of (Fin n → unitInterval)) ⊗ TopCat.of unitInterval)))
  let B := SSet.chainComplexMap (TopCat.toSSet.map (snocMap n)) (ModuleCat.of ℤ ℤ)
  let f := (SSet.yonedaEquiv.symm
    (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π)) ⊗ₘ
      SSet.yonedaEquiv.symm (TauCeti.TopCat.simplex₁ (X := TopCat.of unitInterval)
          (ContinuousMap.id unitInterval))) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet _ _
  let z (r : Fin (n + 1)) : ((Δ[n] : SSet.{0}) ⊗ Δ[1]) _⦋n + 1⦌ :=
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ r),
      SSet.stdSimplex.objMk₁ r.succ.castSucc)
  have hz (r : Fin (n + 1)) : (TopCat.toSSet.map (snocMap n)).app _ (f.app _ (z r)) =
      ((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).symm
        (staircaseSimplex ((snocFin r π.symm).symm)) := classified_prism r π
  have ht (r : Fin (n + 1)) :
      (TopCat.toSSet.obj _).ιChainComplex (f.app _ (z r)) ≫ A.f (n + 1) ≫ B.f (n + 1) =
        (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom ≫
          (TopCat.toSSet.obj _).ιChainComplex
            (((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).symm
              (staircaseSimplex ((snocFin r π.symm).symm))) := by
    calc
      _ = (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom ≫
          (TopCat.toSSet.obj _).ιChainComplex (f.app _ (z r)) ≫ B.f (n + 1) := by
        exact SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc _ _ _
      _ = _ := by
        exact congrArg ((λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom ≫ ·)
          ((SSet.ι_chainComplexMap_f _ _ _ _ _).trans (congrArg _ (hz r)))
  have h := congrArg (fun g ↦ g ≫ A.f (n + 1) ≫ B.f (n + 1)) (shuffle_prism n π)
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp] at h
  have hfold := h.trans (Finset.sum_congr rfl fun r _ ↦
    congrArg (fun g ↦ ((-1 : ℤ) ^ (n + (r : ℕ))) • g) (ht r))
  have hunit := congrArg ((λ_ (𝟙_ (ModuleCat.{0} ℤ))).inv ≫ ·) hfold
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp] at hunit
  have he := congrArg (fun g ↦ g.hom (1 : ℤ)) hunit
  rw [integralShuffleStep_apply_ι]
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, eval_zsmul,
    Category.assoc] using he

/-- Evaluate the literal cube sum in integral coefficients on the universal coordinate cube. -/
lemma integralCubeChain_eq_sum (n : ℕ) :
    (orderedChain (X := TopCat.of (Fin n → unitInterval)) (ContinuousMap.id (Fin n →
      unitInterval)) (ModuleCat.of ℤ ℤ)).hom 1 =
      ∑ π : Perm (Fin n), (π.sign : ℤ) •
        ((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          (((TopCat.of (Fin n → unitInterval)).toSSetObjEquiv _).symm (staircaseSimplex π))).hom 1
            := by
  simp only [orderedChain_eq_sum, ContinuousMap.id_comp, Units.smul_def,
    ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  exact eval_zsmul _ 1 π.sign

/-- A shuffle step takes the actual integral ordered `n`-cube to the ordered `(n+1)`-cube. -/
lemma integralShuffleStep_orderedChain (n : ℕ) :
    integralShuffleStep n
      ((orderedChain (X := TopCat.of (Fin n → unitInterval)) (ContinuousMap.id (Fin n →
        unitInterval)) (ModuleCat.of ℤ ℤ)).hom 1) =
      (orderedChain (X := TopCat.of (Fin (n + 1) → unitInterval)) (ContinuousMap.id (Fin (n + 1) →
        unitInterval)) (ModuleCat.of ℤ ℤ)).hom 1 := by
  rw [integralCubeChain_eq_sum, integralCubeChain_eq_sum]
  simp only [map_sum, map_zsmul]
  calc
    _ = ∑ π : Perm (Fin n), (π.sign : ℤ) •
        ∑ r : Fin (n + 1), ((-1 : ℤ) ^ (n + (r : ℕ))) •
          ((TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → unitInterval))).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            (((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).symm
              (staircaseSimplex ((snocFin r π.symm).symm)))).hom 1 := by
      refine Finset.sum_congr rfl fun π _ ↦ ?_
      exact congrArg (fun a ↦ (π.sign : ℤ) • a) (integralShuffleStep_simplex n π)
    _ = _ := sum_prismPermutation
      (A := ↑(((TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → unitInterval))).chainComplex
        (ModuleCat.of ℤ ℤ)).X (n + 1))) n
      (fun ρ ↦ ((TopCat.toSSet.obj (TopCat.of (Fin (n + 1) → unitInterval))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        (((TopCat.of (Fin (n + 1) → unitInterval)).toSSetObjEquiv _).symm
          (staircaseSimplex ρ))).hom 1)

/-- The literal left-associated integral shuffle of `n` positive intervals,
starting with a point. -/
def iteratedIntegralShuffle : (n : ℕ) →
    ↑(((TopCat.toSSet.obj (TopCat.of (Fin n → unitInterval))).chainComplex
      (ModuleCat.of ℤ ℤ)).X n) :=
  Nat.rec (((TopCat.toSSet.obj (TopCat.of (Fin 0 → unitInterval))).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (TopCat.toSSetObj₀Equiv.symm 0)).hom 1)
    (fun n c ↦ integralShuffleStep n c)

/-- In every degree the literal integral iterated shuffle is exactly the positive ordered sum. -/
lemma iteratedIntegralShuffle_eq_orderedChain (n : ℕ) :
    iteratedIntegralShuffle n =
      (orderedChain (X := TopCat.of (Fin n → unitInterval)) (ContinuousMap.id (Fin n →
        unitInterval)) (ModuleCat.of ℤ ℤ)).hom 1 := by
  induction n with
  | zero =>
    rw [orderedChain_zero]
    have hz : (0 : Fin 0 → unitInterval) = (fun i ↦ i.elim0) := funext fun i ↦ i.elim0
    exact congrArg (fun x : Fin 0 → unitInterval ↦
      ((TopCat.toSSet.obj (TopCat.of (Fin 0 → unitInterval))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) (TopCat.toSSetObj₀Equiv.symm x)).hom 1) hz
  | succ n ih =>
    change integralShuffleStep n (iteratedIntegralShuffle n) = _
    rw [ih, integralShuffleStep_orderedChain]

end TauCeti
