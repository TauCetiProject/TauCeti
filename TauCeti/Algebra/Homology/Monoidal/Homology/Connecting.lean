/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import TauCeti.Algebra.Homology.BifunctorHomotopy
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross

/-!
# The cross product and connecting morphisms

Let `K` be a homological complex and `S : 0 ⟶ L₁ ⟶ L₂ ⟶ L₃ ⟶ 0` a short exact sequence of
homological complexes in an abelian monoidal category `C`, with a shape `c` carrying tensor signs.
Tensoring `S` on the left with `K` gives a short complex `K ⊗ L₁ ⟶ K ⊗ L₂ ⟶ K ⊗ L₃`
(`HomologicalComplex.tensorLeftShortComplex`).  When it is again short exact, the connecting
morphisms of the two long exact homology sequences are related by the homology cross product:
for a class `x ∈ Hₚ(K)` and `y ∈ H_q(L₃)`,

`δ (x × y) = ε(p) • (x × δ y)`,

where `ε(p)` is the sign of the vertical differential of the tensor product of complexes (so
`(-1)^p` for chain complexes indexed by `ℕ`).  The sign arises because the differential of `K ⊗ L`
acts on `x ⊗ y` by `d x ⊗ y + ε(p) • x ⊗ d y`.

This is the compatibility of the cross product with the boundary maps of a pair, and it is the
input which identifies the connecting morphisms in the proof of the Künneth formula.

## Main definitions and results

* `HomologicalComplex.tensorLeftShortComplex`: the short complex `K ⊗ S`.
* `HomologicalComplex.homologyCross_comp_δ`: the connecting morphism of `K ⊗ S` on a cross
  product.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, proof of Theorem 3.6.3, where
  the connecting morphism is computed in the same way.
* A. Hatcher, *Algebraic Topology*, Section 3.B, the relative cross product.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

section ShortComplex

variable (K : HomologicalComplex C c) (S : ShortComplex (HomologicalComplex C c))
  [HasTensor K S.X₁] [HasTensor K S.X₂] [HasTensor K S.X₃]

/-- The short complex `K ⊗ S.X₁ ⟶ K ⊗ S.X₂ ⟶ K ⊗ S.X₃` obtained by tensoring a short complex
of homological complexes on the left with `K`.  It is reducible, so that its terms are seen to be
the tensor products `tensorObj K S.Xᵢ` when stating results about its homology. -/
@[simps]
abbrev tensorLeftShortComplex : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (tensorHom (𝟙 K) S.f) (tensorHom (𝟙 K) S.g) (by
    rw [tensorHom, tensorHom, ← mapBifunctorMap_comp, Category.comp_id, S.zero]
    ext
    simp)

variable {S} in
/-- Tensoring on the left with `K` preserves short exact sequences of complexes which are split in
each degree. -/
lemma shortExact_tensorLeftShortComplex (hS : S.ShortExact) [∀ q, IsSplitMono (S.f.f q)] :
    (tensorLeftShortComplex K S).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have hq q := (shortExact_iff_degreewise_shortExact S).1 hS q
  let σ q := ShortComplex.Splitting.ofExactOfRetraction _ (hq q).exact
    (retraction (S.f.f q)) (by simp) (hq q).epi_g
  exact ShortComplex.Splitting.shortExact
    { r := mapBifunctorDesc fun p q h ↦ (K.X p ◁ (σ q).r) ≫ ιTensorObj K S.X₁ p q n h
      s := mapBifunctorDesc fun p q h ↦ (K.X p ◁ (σ q).s) ≫ ιTensorObj K S.X₂ p q n h
      f_r := by
        refine mapBifunctor.hom_ext fun p q h ↦ ?_
        have := (σ q).f_r
        dsimp at this ⊢
        simp [← whiskerLeft_comp_assoc, this]
      s_g := by
        refine mapBifunctor.hom_ext fun p q h ↦ ?_
        have := (σ q).s_g
        dsimp at this ⊢
        simp [← whiskerLeft_comp_assoc, this]
      id := by
        refine mapBifunctor.hom_ext fun p q h ↦ ?_
        have := (σ q).id
        dsimp at this ⊢
        simp only [Preadditive.comp_add, ι_mapBifunctorDesc_assoc, curriedTensor_obj_obj,
          Category.assoc, ι_mapBifunctorMap, id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
          curriedTensor_obj_map, Category.id_comp, ι_mapBifunctorMap_assoc, ι_mapBifunctorDesc,
          Category.comp_id]
        rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, ← Preadditive.add_comp,
          ← MonoidalPreadditive.whiskerLeft_add, this, whiskerLeft_id, Category.id_comp] }

end ShortComplex

section Connecting

variable (K : HomologicalComplex C c) {S : ShortComplex (HomologicalComplex C c)}
  [HasTensor K S.X₁] [HasTensor K S.X₂] [HasTensor K S.X₃]
  (hS : S.ShortExact) (hKS : (tensorLeftShortComplex K S).ShortExact)
  {p q q' : I} (hq : c.Rel q q') {n n' : I} (h : p + q = n) (h' : p + q' = n')

include hq in
/-- The connecting morphism of `K ⊗ S` computed on generalized elements: if `a₂` lifts the cycle
`a₃` of `S.X₃` to `S.X₂`, and `a₁` lifts the differential of `a₂` to `S.X₁`, then the connecting
morphism sends the class of `x ⊗ a₃` to `ε(p)` times the class of `x ⊗ a₁`, for a cycle `x` of
`K` of degree `p`. -/
private lemma cyclesCross_homologyπ_δ {P : C} (a₃ : P ⟶ S.X₃.cycles q) (a₂ : P ⟶ S.X₂.X q)
    (a₁ : P ⟶ S.X₁.X q') (h₂ : a₂ ≫ S.g.f q = a₃ ≫ S.X₃.iCycles q)
    (h₁ : a₁ ≫ S.f.f q' = a₂ ≫ S.X₂.d q q') (ha₁ : a₁ ≫ S.X₁.d q' (c.next q') = 0) :
    ((K.cycles p ◁ a₃) ≫ cyclesCross K S.X₃ p q n h) ≫ (tensorObj K S.X₃).homologyπ n ≫
        hKS.δ n n' (h ▸ h' ▸ c.add_rel p hq) =
      ((c.ε p : ℤ) • (K.cycles p ◁ S.X₁.liftCycles a₁ (c.next q') rfl ha₁) ≫
        cyclesCross K S.X₁ p q' n' h') ≫ (tensorObj K S.X₁).homologyπ n' := by
  have hn : c.Rel n n' := h ▸ h' ▸ c.add_rel p hq
  have hx₂ : ((K.iCycles p ⊗ₘ a₂) ≫ ιTensorObj K S.X₂ p q n h) ≫ (tensorHom (𝟙 K) S.g).f n =
      ((K.cycles p ◁ a₃) ≫ cyclesCross K S.X₃ p q n h) ≫ (tensorObj K S.X₃).iCycles n := by
    simp [tensorHom_comp_whiskerLeft_assoc, whiskerLeft_comp_tensorHom_assoc, h₂]
  -- the differential of `x ⊗ a₂` is `ε(p) • x ⊗ d a₂`, since `x` is a cycle
  have hx₁ : ((c.ε p : ℤ) • (K.iCycles p ⊗ₘ a₁) ≫ ιTensorObj K S.X₁ p q' n' h') ≫
      (tensorHom (𝟙 K) S.f).f n' =
        ((K.iCycles p ⊗ₘ a₂) ≫ ιTensorObj K S.X₂ p q n h) ≫ (tensorObj K S.X₂).d n n' := by
    have hd₁ :
        (K.iCycles p ▷ S.X₂.X q) ≫ mapBifunctor.d₁ K S.X₂ (curriedTensor C) c p q n' = 0 := by
      by_cases hp : c.Rel p (c.next p)
      · simp [mapBifunctor.d₁_eq' _ _ _ _ hp, ← comp_whiskerRight_assoc]
      · simp [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp]
    rw [Category.assoc, mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
      mapBifunctor.ι_D₂, mapBifunctor.d₂_eq _ _ _ _ _ hq _ h']
    simp only [tensorHom_def', Category.assoc, Preadditive.comp_add, hd₁, comp_zero, zero_add]
    simp [Units.smul_def]
    simp only [← whisker_exchange_assoc, ← whiskerLeft_comp_assoc, h₁]
  have hδ := hKS.δ_eq n n' hn
    (((K.cycles p ◁ a₃) ≫ cyclesCross K S.X₃ p q n h) ≫ (tensorObj K S.X₃).iCycles n)
    (by simp only [Category.assoc, iCycles_d, comp_zero])
    ((K.iCycles p ⊗ₘ a₂) ≫ ιTensorObj K S.X₂ p q n h) hx₂
    ((c.ε p : ℤ) • (K.iCycles p ⊗ₘ a₁) ≫ ιTensorObj K S.X₁ p q' n' h') hx₁ _ rfl
  have e₃ : ∀ hx, (tensorObj K S.X₃).liftCycles
      (((K.cycles p ◁ a₃) ≫ cyclesCross K S.X₃ p q n h) ≫ (tensorObj K S.X₃).iCycles n) n'
        (c.next_eq' hn) hx = (K.cycles p ◁ a₃) ≫ cyclesCross K S.X₃ p q n h := fun _ ↦ by
    simp [← cancel_mono ((tensorObj K S.X₃).iCycles n)]
  have e₁ : ∀ hx, (tensorObj K S.X₁).liftCycles
      ((c.ε p : ℤ) • (K.iCycles p ⊗ₘ a₁) ≫ ιTensorObj K S.X₁ p q' n' h') (c.next n') rfl hx =
        (c.ε p : ℤ) • (K.cycles p ◁ S.X₁.liftCycles a₁ (c.next q') rfl ha₁) ≫
          cyclesCross K S.X₁ p q' n' h' := fun _ ↦ by
    simp [← cancel_mono ((tensorObj K S.X₁).iCycles n'), whiskerLeft_comp_tensorHom_assoc]
  rwa [e₃, e₁] at hδ

variable [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (S.X₃.cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (S.X₃.X (c.prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (S.X₁.cycles q'))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (S.X₁.X (c.prev q')))]
  [(tensorLeft (K.cycles p)).PreservesEpimorphisms]

/-- **The connecting morphism on a cross product.**  If `S` is a short exact sequence of complexes
and `K ⊗ S` is again short exact, then the connecting morphism of `K ⊗ S` sends `x × y` to
`ε(p) • (x × δ y)` for `x ∈ Hₚ(K)` and `y ∈ H_q(S.X₃)`. -/
theorem homologyCross_comp_δ :
    homologyCross K S.X₃ p q n h ≫ hKS.δ n n' (h ▸ h' ▸ c.add_rel p hq) =
      (c.ε p : ℤ) • ((K.homology p ◁ hS.δ q q' hq) ≫ homologyCross K S.X₁ p q' n' h') := by
  have hq₁ := (shortExact_iff_degreewise_shortExact S).1 hS q
  have hq₂ := (shortExact_iff_degreewise_shortExact S).1 hS q'
  have : Epi (S.g.f q) := hq₁.epi_g
  have := hq₂.mono_f
  have : Mono (S.f.f (c.next q')) := ((shortExact_iff_degreewise_shortExact S).1 hS _).mono_f
  -- the data computing the connecting morphism of `S` on all cycles of `S.X₃` at once: the
  -- pullback of `S.X₂.X q ⟶ S.X₃.X q` along the cycles of `S.X₃` lifts them to `S.X₂`
  let a₃ := pullback.snd (S.g.f q) (S.X₃.iCycles q)
  let a₂ := pullback.fst (S.g.f q) (S.X₃.iCycles q)
  have h₂ : a₂ ≫ S.g.f q = a₃ ≫ S.X₃.iCycles q := pullback.condition
  let a₁ := hq₂.exact.lift (a₂ ≫ S.X₂.d q q') (by
    simp only [Category.assoc]
    dsimp
    rw [← S.g.comm, reassoc_of% h₂, iCycles_d, comp_zero])
  have h₁ : a₁ ≫ S.f.f q' = a₂ ≫ S.X₂.d q q' := hq₂.exact.lift_f _ _
  have ha₁ : a₁ ≫ S.X₁.d q' (c.next q') = 0 := by
    rw [← cancel_mono (S.f.f (c.next q')), Category.assoc, ← S.f.comm, reassoc_of% h₁]
    simp
  have hδS : a₃ ≫ S.X₃.homologyπ q ≫ hS.δ q q' hq =
      S.X₁.liftCycles a₁ (c.next q') rfl ha₁ ≫ S.X₁.homologyπ q' := by
    have := hS.δ_eq q q' hq (a₃ ≫ S.X₃.iCycles q) (by simp) a₂ h₂ a₁ h₁ _ rfl
    rwa [show S.X₃.liftCycles (a₃ ≫ S.X₃.iCycles q) q' (c.next_eq' hq) (by simp) = a₃ by
      simp [← cancel_mono (S.X₃.iCycles q)]] at this
  -- both sides agree on `x ⊗ a₃`, and these generate `Hₚ(K) ⊗ H_q(S.X₃)`
  have : Epi (K.cycles p ◁ a₃) := (tensorLeft (K.cycles p)).map_epi a₃
  refine homology_tensor_homology_hom_ext K S.X₃ p q ?_
  rw [← cancel_epi (K.cycles p ◁ a₃), homologyπ_tensorHom_homologyCross_assoc,
    ← Category.assoc, cyclesCross_homologyπ_δ K hKS hq h h' a₃ a₂ a₁ h₂ h₁ ha₁,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul, whiskerLeft_comp_tensorHom_assoc,
    tensorHom_comp_whiskerLeft_assoc, Category.assoc, hδS, ← whiskerLeft_comp_tensorHom_assoc,
    homologyπ_tensorHom_homologyCross, Preadditive.zsmul_comp, Category.assoc]

end Connecting

end HomologicalComplex
