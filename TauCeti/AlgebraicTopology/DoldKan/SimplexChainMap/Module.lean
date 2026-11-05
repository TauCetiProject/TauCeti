/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.SimplexChainMap.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# The simplicial module of simplex chain maps

The normalized-chain description of Dold–Kan carries a module structure: add chain maps
and multiply them by scalars pointwise. Pullback along simplicial operators is linear.
We bundle these operations into `CochainComplex.simplexChainModule`, whose underlying
simplicial set is the existing `CochainComplex.simplexChainMaps`.

In particular the explicit chain-map model is a Kan complex, by the theorem that the
underlying simplicial set of a simplicial module is Kan. The coface-vanishing criterion
expresses normalized Moore chains directly in terms of values on subsets of vertices;
it allows normalization calculations without unfolding the simplicial module.

## References

* P. Goerss and J. Jardine, *Simplicial Homotopy Theory*, Chapter III, §2.
* J. Lurie, *Higher Algebra*, §1.2.3 and Remark 1.3.1.12.
-/

public noncomputable section

open CategoryTheory Finset Simplicial Opposite

universe v u

namespace CochainComplex

variable {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}

namespace SimplexChainMap

variable {n m : ℕ}

instance : Zero (K.SimplexChainMap n) where
  zero :=
    { val := fun _ _ ↦ 0
      val_eq_zero_of_ne := fun _ _ _ ↦ rfl
      val_empty := rfl
      d_val := fun _ _ ↦ by simp }

instance : Add (K.SimplexChainMap n) where
  add f g :=
    { val := fun J d ↦ f.val J d + g.val J d
      val_eq_zero_of_ne := fun J d h ↦ by
        rw [f.val_eq_zero_of_ne J d h, g.val_eq_zero_of_ne J d h, add_zero]
      val_empty := by rw [f.val_empty, g.val_empty, add_zero]
      d_val := fun J d ↦ by simp [f.d_val, g.d_val, smul_add, sum_add_distrib] }

instance : Neg (K.SimplexChainMap n) where
  neg f :=
    { val := fun J d ↦ -f.val J d
      val_eq_zero_of_ne := fun J d h ↦ by rw [f.val_eq_zero_of_ne J d h, neg_zero]
      val_empty := by rw [f.val_empty, neg_zero]
      d_val := fun J d ↦ by simp [f.d_val, smul_neg, sum_neg_distrib] }

instance : Sub (K.SimplexChainMap n) where
  sub f g := f + -g

instance (S : Type*) [Semiring S] [Module S R]
    [∀ d, Module S (K.X d)] [∀ d, IsScalarTower S R (K.X d)] : SMul S (K.SimplexChainMap n) where
  smul a f :=
    { val := fun J d ↦ a • f.val J d
      val_eq_zero_of_ne := fun J d h ↦ by rw [f.val_eq_zero_of_ne J d h, smul_zero]
      val_empty := by rw [f.val_empty, smul_zero]
      d_val := fun J d ↦ by
        simp only [LinearMap.map_smul_of_tower, f.d_val, smul_sum, Units.smul_def]
        exact sum_congr rfl fun j _ ↦
          (smul_comm ((#{s ∈ J | s < j} : ℤ).negOnePow : ℤ) a _).symm }

@[simp] theorem zero_val (J : Finset (Fin (n + 1))) (d : ℤ) :
    (0 : K.SimplexChainMap n).val J d = 0 := (rfl)

@[simp] theorem add_val (f g : K.SimplexChainMap n) (J : Finset (Fin (n + 1))) (d : ℤ) :
    (f + g).val J d = f.val J d + g.val J d := (rfl)

@[simp] theorem neg_val (f : K.SimplexChainMap n) (J : Finset (Fin (n + 1))) (d : ℤ) :
    (-f).val J d = -f.val J d := (rfl)

@[simp] theorem sub_val (f g : K.SimplexChainMap n) (J : Finset (Fin (n + 1))) (d : ℤ) :
    (f - g).val J d = f.val J d - g.val J d := by
  exact (sub_eq_add_neg _ _).symm

@[simp] theorem smul_val {S : Type*} [Semiring S] [Module S R]
    [∀ d, Module S (K.X d)] [∀ d, IsScalarTower S R (K.X d)] (a : S) (f : K.SimplexChainMap n)
    (J : Finset (Fin (n + 1))) (d : ℤ) :
    (a • f).val J d = a • f.val J d := (rfl)

instance : AddCommGroup (K.SimplexChainMap n) :=
  Function.Injective.addCommGroup val (fun _ _ h ↦ SimplexChainMap.ext h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun f g ↦ funext₂ fun J d ↦ sub_val f g J d) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module R (K.SimplexChainMap n) :=
  Function.Injective.module R
    { toFun := val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    (fun _ _ h ↦ SimplexChainMap.ext h) (fun _ _ ↦ rfl)

/-- Evaluation on a subset of vertices is linear. -/
def eval (J : Finset (Fin (n + 1))) (d : ℤ) : K.SimplexChainMap n →ₗ[R] K.X d where
  toFun f := f.val J d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem eval_apply (J : Finset (Fin (n + 1))) (d : ℤ) (f : K.SimplexChainMap n) :
    eval J d f = f.val J d := (rfl)

/-- Pullback of simplex chain maps, bundled as a linear map. -/
def mapLinearMap (α : Fin (m + 1) →o Fin (n + 1)) :
    K.SimplexChainMap n →ₗ[R] K.SimplexChainMap m where
  toFun f := f.map α
  map_add' f g := by
    ext J d
    by_cases h : #(J.image α) = #J
    · simp only [map_val, add_val, h, ite_true]
    · simp only [map_val, add_val, h, ite_false, add_zero]
  map_smul' a f := by
    ext J d
    by_cases h : #(J.image α) = #J
    · simp only [map_val, smul_val, h, ite_true, RingHom.id_apply]
    · simp only [map_val, smul_val, h, ite_false, RingHom.id_apply, smul_zero]

@[simp] theorem mapLinearMap_apply (α : Fin (m + 1) →o Fin (n + 1))
    (f : K.SimplexChainMap n) : mapLinearMap α f = f.map α := (rfl)

/-- A coface of a simplex chain map vanishes exactly when all values on subsets
omitting the corresponding vertex vanish. -/
theorem map_δ_eq_zero_iff (f : K.SimplexChainMap (n + 1)) (i : Fin (n + 2)) :
    f.map (SimplexCategory.δ i).toOrderHom = 0 ↔
      ∀ (J : Finset (Fin (n + 2))) (d : ℤ), i ∉ J → f.val J d = 0 := by
  have hδ : ⇑((SimplexCategory.δ i).toOrderHom) = i.succAbove := SimplexCategory.coe_δ i
  constructor
  · intro h J d hi
    have hsub : J ⊆ univ.image i.succAbove := by
      intro j hj
      simp only [mem_image, mem_univ, true_and]
      exact Fin.exists_succAbove_eq (ne_of_mem_of_not_mem hj hi)
    obtain ⟨S, -, hS⟩ := subset_image_iff.1 hsub
    have hinj : #(S.image i.succAbove) = #S :=
      card_image_of_injective _ (Fin.succAbove_right_injective)
    have hv := congrArg (fun g : K.SimplexChainMap n ↦ g.val S d) h
    simp only [map_val, hδ, hinj, ite_true, zero_val] at hv
    rwa [hS] at hv
  · intro h
    ext J d
    rw [map_val]
    split_ifs
    · exact h _ _ (by simp [hδ, Fin.succAbove_ne])
    · rfl

/-- A normalized simplex chain map can be nonzero only on the full simplex and
its face opposite vertex zero. This is the support description of Moore normalization. -/
theorem higher_faces_eq_zero_iff (f : K.SimplexChainMap (n + 1)) :
    (∀ i : Fin (n + 1), f.map (SimplexCategory.δ i.succ).toOrderHom = 0) ↔
      ∀ (J : Finset (Fin (n + 2))) (d : ℤ),
        J ≠ univ → J ≠ univ.erase 0 → f.val J d = 0 := by
  constructor
  · intro h J d htop hface
    have hmissing : ∃ i : Fin (n + 1), i.succ ∉ J := by
      by_contra! hall
      by_cases hzero : 0 ∈ J
      · apply htop
        ext j
        induction j using Fin.cases with
        | zero => simp [hzero]
        | succ i => simp [hall i]
      · apply hface
        ext j
        induction j using Fin.cases with
        | zero => simp [hzero]
        | succ i => simp [hall i]
    obtain ⟨i, hi⟩ := hmissing
    exact (map_δ_eq_zero_iff f i.succ).1 (h i) J d hi
  · intro h i
    apply (map_δ_eq_zero_iff f i.succ).2
    intro J d hi
    apply h J d
    · rintro rfl
      exact hi (mem_univ _)
    · rintro rfl
      exact hi (by simp)

/-- In a normalized chain map the differential of its top value is its value
on the face opposite zero; every other term in the boundary vanishes. -/
theorem d_val_univ_of_higher_faces_eq_zero (f : K.SimplexChainMap (n + 1))
    (hf : ∀ i : Fin (n + 1), f.map (SimplexCategory.δ i.succ).toOrderHom = 0) (d : ℤ) :
    (K.d d (d + 1)).hom (f.val univ d) = f.val (univ.erase 0) (d + 1) := by
  rw [f.d_val]
  have hvanish (j : Fin (n + 2)) (hj : j ≠ 0) :
      f.val (univ.erase j) (d + 1) = 0 := by
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    exact (map_δ_eq_zero_iff f i.succ).1 (hf i) _ _ (notMem_erase _ _)
  rw [sum_eq_single 0 (fun j _ hj ↦ by rw [hvanish j hj, smul_zero])
    (fun h ↦ (h (mem_univ 0)).elim)]
  simp only [Fin.not_lt_zero, filter_false, card_empty, Nat.cast_zero,
    Int.negOnePow_zero, one_smul]

/-- A normalized simplex chain map is determined by its top-dimensional value. -/
theorem ext_of_higher_faces_eq_zero {f g : K.SimplexChainMap (n + 1)}
    (hf : ∀ i : Fin (n + 1), f.map (SimplexCategory.δ i.succ).toOrderHom = 0)
    (hg : ∀ i : Fin (n + 1), g.map (SimplexCategory.δ i.succ).toOrderHom = 0)
    (h : f.val univ (-(n + 1 : ℤ)) = g.val univ (-(n + 1 : ℤ))) : f = g := by
  have htop (d : ℤ) : f.val univ d = g.val univ d := by
    by_cases hd : d = -(n + 1 : ℤ)
    · subst d
      exact h
    · have harith : d + (n + 2 : ℤ) ≠ 1 := by omega
      have hdegree : d + #(univ : Finset (Fin (n + 2))) ≠ 1 := by
        simpa only [card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using harith
      rw [f.val_eq_zero_of_ne _ _ hdegree, g.val_eq_zero_of_ne _ _ hdegree]
  ext J d
  by_cases hJ : J = univ
  · subst J
    exact htop d
  by_cases hface : J = univ.erase 0
  · subst J
    -- Reindex the requested degree as the target of a differential, avoiding
    -- transport between the dependent modules K.X d and K.X (d - 1 + 1).
    obtain ⟨a, rfl⟩ : ∃ a : ℤ, d = a + 1 := ⟨d - 1, by omega⟩
    rw [← d_val_univ_of_higher_faces_eq_zero f hf,
      ← d_val_univ_of_higher_faces_eq_zero g hg, htop]
  rw [(higher_faces_eq_zero_iff f).1 hf J d hJ hface,
    (higher_faces_eq_zero_iff g).1 hg J d hJ hface]

end SimplexChainMap

variable (K)

/-- The simplicial module of chain maps from normalized chains of standard simplices
into the good connective truncation of a cochain complex. -/
def simplexChainModule : SimplicialObject (ModuleCat.{v} R) where
  obj Δ := ModuleCat.of R (K.SimplexChainMap Δ.unop.len)
  map f := ModuleCat.ofHom (SimplexChainMap.mapLinearMap f.unop.toOrderHom)
  -- Applying `ModuleCat.ofHom (mapLinearMap _)` is definitionally pullback by `map`;
  -- the order homs of the identity and composite are `OrderHom.id` and `OrderHom.comp`.
  map_id Δ := by ext g J d; exact congrArg (fun g ↦ g.val J d) g.map_id
  map_comp f g := by ext x J d; exact congrArg (fun x ↦ x.val J d) (x.map_map _ _).symm

/-- The simplicial module has the original simplex chain maps as its underlying simplicial set. -/
theorem simplexChainModule_comp_forget :
    K.simplexChainModule ⋙ forget (ModuleCat R) = K.simplexChainMaps := (rfl)

/-- The terms of the simplicial module are the modules of simplex chain maps. -/
@[simp] theorem simplexChainModule_obj (Δ : SimplexCategoryᵒᵖ) :
    K.simplexChainModule.obj Δ = ModuleCat.of R (K.SimplexChainMap Δ.unop.len) := (rfl)

/-- Simplicial operators on the module of simplex chain maps are the existing pullback maps. -/
@[simp] theorem simplexChainModule_map_apply {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (g : K.simplexChainModule.obj Δ) :
    K.simplexChainModule.map f g = (by
      simp only [simplexChainModule_obj] at g ⊢
      exact g.map f.unop.toOrderHom) := (rfl)

/-- The explicit normalized-chain model of the Dold–Kan simplicial set is Kan. -/
instance : SSet.KanComplex K.simplexChainMaps := by
  rw [← simplexChainModule_comp_forget]
  infer_instance

end CochainComplex
