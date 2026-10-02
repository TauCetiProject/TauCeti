/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Linear
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.TensorDifferential
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The tensor product of cochains

Let `C` be a preadditive monoidal category, let `A` and `B` be chain complexes in `C` indexed by
`ℕ` such that the tensor product `A ⊗ B` exists, and let `μ : M ⊗ N ⟶ P` be a pairing of
coefficient objects.
Cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` have a tensor product `(A ⊗ B)_n ⟶ P`, which on the
summand `A_p ⊗ B_q` is `φ ⊗ ψ` followed by `μ` and vanishes on every other summand.  Since the
differential of `A ⊗ B` carries the Koszul signs, it satisfies the Leibniz rule
`(φ ⊗ ψ) ∘ d = (φ ∘ d) ⊗ ψ + (-1)^p φ ⊗ (ψ ∘ d)`.

This is the common chain-level ingredient of the cup product of cochains
(`TauCeti.ChainComplex.cupCochain`) and of the cap product of chains and cochains
(`TauCeti.ChainComplex.capChain`), both of which precompose it with a diagonal `E ⟶ A ⊗ B`.

## Main definitions and results

* `TauCeti.ChainComplex.tensorCochain`: the morphism `(A ⊗ B)_n ⟶ P` given on the summand
  `A_p ⊗ B_q` by `φ ⊗ ψ` and `μ`.
* `TauCeti.ChainComplex.d_comp_tensorCochain`: its Leibniz rule.
* `TauCeti.ChainComplex.tensorHom_f_comp_tensorCochain`: its naturality in the complexes.
* `TauCeti.ChainComplex.tensorCochain_comp`, `TauCeti.ChainComplex.tensorCochain_whiskerLeft_comp`
  and `TauCeti.ChainComplex.tensorCochain_whiskerRight_comp`: changing the pairing.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Extend

section ZeroMorphisms

variable [HasZeroMorphisms C] {A : ChainComplex C ℕ} {M : C}

/-- A morphism `A_p ⟶ M` as a family of morphisms `A_i ⟶ M` in all degrees, zero away from `p`. -/
private def extendCochain {p : ℕ} (φ : A.X p ⟶ M) (i : ℕ) : A.X i ⟶ M :=
  if h : i = p then (A.XIsoOfEq h).hom ≫ φ else 0

private lemma extendCochain_self {p : ℕ} (φ : A.X p ⟶ M) : extendCochain φ p = φ := by
  simp [extendCochain]

private lemma extendCochain_of_ne {p i : ℕ} (φ : A.X p ⟶ M) (h : i ≠ p) :
    extendCochain φ i = 0 :=
  dite_eq_right h

/-- Extending `φ ∘ d` by zero is precomposing the extension of `φ` with the differential. -/
private lemma extendCochain_d_comp {p : ℕ} (φ : A.X p ⟶ M) (i : ℕ) :
    extendCochain (A.d (p + 1) p ≫ φ) (i + 1) = A.d (i + 1) i ≫ extendCochain φ i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · rw [extendCochain_of_ne _ (by omega), extendCochain_of_ne _ h, comp_zero]

private lemma extendCochain_d_comp_zero {p : ℕ} (φ : A.X p ⟶ M) :
    extendCochain (A.d (p + 1) p ≫ φ) 0 = 0 :=
  extendCochain_of_ne _ (by omega)

private lemma extendCochain_comp {A' : ChainComplex C ℕ} (g : A' ⟶ A) {p : ℕ} (φ : A.X p ⟶ M)
    (i : ℕ) : extendCochain (g.f p ≫ φ) i = g.f i ≫ extendCochain φ i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

private lemma extendCochain_comp_right {M' : C} {p : ℕ} (φ : A.X p ⟶ M) (g : M ⟶ M') (i : ℕ) :
    extendCochain (φ ≫ g) i = extendCochain φ i ≫ g := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

end ZeroMorphisms

section Preadditive

variable [Preadditive C] {A : ChainComplex C ℕ} {M : C}

/-- The sign `(-1)^i` on the extension of a cochain of degree `p` is `(-1)^p`. -/
private lemma zsmul_extendCochain {p : ℕ} (φ : A.X p ⟶ M) (i : ℕ) :
    ((-1 : ℤ) ^ i) • extendCochain φ i = ((-1 : ℤ) ^ p) • extendCochain φ i := by
  by_cases h : i = p
  · rw [h]
  · simp [extendCochain_of_ne _ h]

private lemma extendCochain_add {p : ℕ} (φ φ' : A.X p ⟶ M) (i : ℕ) :
    extendCochain (φ + φ') i = extendCochain φ i + extendCochain φ' i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

private lemma extendCochain_smul {k : Type*} [Semiring k] [Linear k C] {p : ℕ} (r : k)
    (φ : A.X p ⟶ M) (i : ℕ) :
    extendCochain (r • φ) i = r • extendCochain φ i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

end Preadditive

end Extend

section Tensor

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] {A B : ChainComplex C ℕ}
  [A.HasTensor B] {M N P : C} (μ : M ⊗ N ⟶ P)

/-- **The tensor product of cochains**: for cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N`, the morphism
`(A ⊗ B)_n ⟶ P` which on the summand `A_p ⊗ B_q` is `φ ⊗ ψ` followed by the pairing `μ`
(`TauCeti.ChainComplex.ιTensorObj_tensorCochain`) and vanishes on every other summand
(`TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_left` and
`TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_right`). -/
def tensorCochain {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (HomologicalComplex.tensorObj A B).X n ⟶ P :=
  mapBifunctorDesc fun i j _ ↦ (extendCochain φ i ⊗ₘ extendCochain ψ j) ≫ μ

@[reassoc]
private lemma ιTensorObj_tensorCochain_extend {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (i j n : ℕ) (h : i + j = n) :
    ιTensorObj A B i j n h ≫ tensorCochain μ φ ψ n =
      (extendCochain φ i ⊗ₘ extendCochain ψ j) ≫ μ :=
  ι_mapBifunctorDesc _ _ _ _

/-- The tensor product of cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` is `φ ⊗ ψ` followed by `μ` on
the summand `A_p ⊗ B_q`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorCochain {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ)
    (h : p + q = n) :
    ιTensorObj A B p q n h ≫ tensorCochain μ φ ψ n = (φ ⊗ₘ ψ) ≫ μ := by
  rw [ιTensorObj_tensorCochain_extend, extendCochain_self, extendCochain_self]

/-- The tensor product of cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` vanishes on the summands
`A_i ⊗ B_j` with `i ≠ p`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorCochain_of_ne_left {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) {i j n : ℕ}
    (h : i + j = n) (hi : i ≠ p) :
    ιTensorObj A B i j n h ≫ tensorCochain μ φ ψ n = 0 := by
  rw [ιTensorObj_tensorCochain_extend, extendCochain_of_ne _ hi, MonoidalPreadditive.zero_tensor,
    zero_comp]

/-- The tensor product of cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` vanishes on the summands
`A_i ⊗ B_j` with `j ≠ q`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorCochain_of_ne_right {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    {i j n : ℕ} (h : i + j = n) (hj : j ≠ q) :
    ιTensorObj A B i j n h ≫ tensorCochain μ φ ψ n = 0 := by
  rw [ιTensorObj_tensorCochain_extend, extendCochain_of_ne _ hj,
    MonoidalPreadditive.tensor_zero, zero_comp]

/-- **The Leibniz rule for the tensor product of cochains**: precomposed with the differential of
`A ⊗ B`, the tensor product of `φ` and `ψ` is the tensor product of `φ ∘ d` and `ψ` plus `(-1)^p`
times the tensor product of `φ` and `ψ ∘ d`. -/
lemma d_comp_tensorCochain {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (HomologicalComplex.tensorObj A B).d (n + 1) n ≫ tensorCochain μ φ ψ n =
      tensorCochain μ (A.d (p + 1) p ≫ φ) ψ (n + 1) +
        ((-1 : ℤ) ^ p) • tensorCochain μ φ (B.d (q + 1) q ≫ ψ) (n + 1) := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n + 1) ↦ ?_
  have hd : (HomologicalComplex.tensorObj A B).d (n + 1) n =
      mapBifunctor.D₁ A B (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ A B (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [hd]
  obtain _ | r := i
  · obtain _ | s := j
    · omega
    obtain rfl : s = n := by omega
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
      ChainComplex.ιTensorObj_D₁_zero_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
      Preadditive.zsmul_comp, Category.assoc, ιTensorObj_tensorCochain_extend,
      extendCochain_d_comp_zero, extendCochain_d_comp, MonoidalPreadditive.zero_tensor,
      zero_comp, zero_add, whiskerLeft_comp_tensorHom_assoc]
    rw [← Preadditive.zsmul_comp, ← Preadditive.zsmul_comp, ← zsmul_tensorHom, ← zsmul_tensorHom,
      zsmul_extendCochain]
  · obtain _ | s := j
    · obtain rfl : r = n := by omega
      simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_zero_assoc,
        ιTensorObj_tensorCochain_extend, extendCochain_d_comp_zero, extendCochain_d_comp,
        MonoidalPreadditive.tensor_zero, zero_comp, smul_zero, add_zero,
        whiskerRight_comp_tensorHom_assoc]
    · simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
        Preadditive.zsmul_comp, Category.assoc, ιTensorObj_tensorCochain_extend,
        extendCochain_d_comp, whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
      rw [← Preadditive.zsmul_comp, ← Preadditive.zsmul_comp, ← zsmul_tensorHom,
        ← zsmul_tensorHom, zsmul_extendCochain]

/-- The tensor product of cochains is natural: precomposing it with the tensor product of chain
maps `f : A' ⟶ A` and `g : B' ⟶ B` is the tensor product of the precomposed cochains. -/
@[reassoc]
lemma tensorHom_f_comp_tensorCochain {A' B' : ChainComplex C ℕ} [A'.HasTensor B'] (f : A' ⟶ A)
    (g : B' ⟶ B) {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (HomologicalComplex.tensorHom f g).f n ≫ tensorCochain μ φ ψ n =
      tensorCochain μ (f.f p ≫ φ) (g.f q ≫ ψ) n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ι_tensorHom_assoc, ιTensorObj_tensorCochain_extend, ιTensorObj_tensorCochain_extend,
    extendCochain_comp, extendCochain_comp, tensorHom_comp_tensorHom_assoc]

/-- The tensor product of cochains is additive in the first cochain. -/
lemma tensorCochain_add_left {p q : ℕ} (φ φ' : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    tensorCochain μ (φ + φ') ψ n = tensorCochain μ φ ψ n + tensorCochain μ φ' ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  simp only [Preadditive.comp_add, ιTensorObj_tensorCochain_extend, extendCochain_add,
    MonoidalPreadditive.add_tensor, Preadditive.add_comp]

/-- The tensor product of cochains is additive in the second cochain. -/
lemma tensorCochain_add_right {p q : ℕ} (φ : A.X p ⟶ M) (ψ ψ' : B.X q ⟶ N) (n : ℕ) :
    tensorCochain μ φ (ψ + ψ') n = tensorCochain μ φ ψ n + tensorCochain μ φ ψ' n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  simp only [Preadditive.comp_add, ιTensorObj_tensorCochain_extend, extendCochain_add,
    MonoidalPreadditive.tensor_add, Preadditive.add_comp]

/-- Postcomposing the tensor product of cochains with `g : P ⟶ P'` is the tensor product of the
same cochains along the pairing `μ ≫ g`. -/
@[reassoc]
lemma tensorCochain_comp {P' : C} (g : P ⟶ P') {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (n : ℕ) : tensorCochain μ φ ψ n ≫ g = tensorCochain (μ ≫ g) φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_tensorCochain_extend_assoc,
    ιTensorObj_tensorCochain_extend]

/-- The tensor product of cochains along the pairing `(M ◁ g) ≫ μ'` is the tensor product along
`μ'` with the second cochain postcomposed with `g`. -/
lemma tensorCochain_whiskerLeft_comp {N' : C} (g : N ⟶ N') (μ' : M ⊗ N' ⟶ P) {p q : ℕ}
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    tensorCochain ((M ◁ g) ≫ μ') φ ψ n = tensorCochain μ' φ (ψ ≫ g) n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_tensorCochain_extend,
    ιTensorObj_tensorCochain_extend, extendCochain_comp_right, tensorHom_comp_whiskerLeft_assoc]

/-- The tensor product of cochains along the pairing `(g ▷ N) ≫ μ'` is the tensor product along
`μ'` with the first cochain postcomposed with `g`. -/
lemma tensorCochain_whiskerRight_comp {M' : C} (g : M ⟶ M') (μ' : M' ⊗ N ⟶ P) {p q : ℕ}
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    tensorCochain ((g ▷ N) ≫ μ') φ ψ n = tensorCochain μ' (φ ≫ g) ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  rw [ιTensorObj_tensorCochain_extend,
    ιTensorObj_tensorCochain_extend, extendCochain_comp_right, tensorHom_comp_whiskerRight_assoc]

variable {k : Type*} [Semiring k] [Linear k C] [MonoidalLinear k C]

/-- The tensor product of cochains is `k`-linear in the first cochain. -/
lemma tensorCochain_smul_left {p q : ℕ} (r : k) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (n : ℕ) : tensorCochain μ (r • φ) ψ n = r • tensorCochain μ φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  simp only [Linear.comp_smul, ιTensorObj_tensorCochain_extend, extendCochain_smul,
    smul_tensorHom, Linear.smul_comp]

/-- The tensor product of cochains is `k`-linear in the second cochain. -/
lemma tensorCochain_smul_right {p q : ℕ} (r : k) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (n : ℕ) : tensorCochain μ φ (r • ψ) n = r • tensorCochain μ φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  simp only [Linear.comp_smul, ιTensorObj_tensorCochain_extend, extendCochain_smul,
    tensorHom_smul, Linear.smul_comp]

end Tensor

end TauCeti.ChainComplex
