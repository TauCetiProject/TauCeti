/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Multiplier

/-!
# Basic double centralizer lemmas

Dependency-light API for Mathlib's multiplier algebra `𝓜(𝕜, A)` of a normed algebra `A`,
requiring only `Mathlib.Analysis.CStarAlgebra.Multiplier` (without Banach closed-graph theory or
approximate units):

* `DoubleCentralizer.ext_fst_snd`, `DoubleCentralizer.continuous_toProd`: extensionality and
  norm continuity of the projection to `(A →L[𝕜] A) × (A →L[𝕜] A)`.
* `DoubleCentralizer.coe_zero`, `coe_add`, `coe_mul`, `coe_neg`, `coe_sub`, `coe_smul`,
  `coe_star`, `coe_one`: algebraic compatibility of the canonical inclusion `A → 𝓜(𝕜, A)`.
* `DoubleCentralizer.ofUnitalAlgEquiv`, `DoubleCentralizer.ofUnitalStarAlgEquiv`,
  `DoubleCentralizer.coeStarAlgEquiv`: for unital normed (`⋆`-)algebras, `A ≃ 𝓜(𝕜, A)`.
* `DoubleCentralizer.fst_mul`, `DoubleCentralizer.snd_mul`, `DoubleCentralizer.coe_injective`,
  `DoubleCentralizer.ext_fst`: module laws, injectivity, and left-centralizer extensionality under
  `FaithfulSMul`.
* `DoubleCentralizer.norm_fst_le`, `DoubleCentralizer.norm_snd_le`,
  `DoubleCentralizer.norm_coe_le`, `DoubleCentralizer.continuous_fst_of_opNorm_le`,
  `DoubleCentralizer.continuous_snd_of_opNorm_le`: basic operator-norm bounds and joint continuity.
* `DoubleCentralizer.eq_zero_of_forall_mul_coe_eq_zero`,
  `DoubleCentralizer.eq_zero_of_forall_coe_mul_eq_zero`,
  `DoubleCentralizer.forall_commute_iff_fst_eq_snd`, `DoubleCentralizer.mem_center_iff`:
  essentiality and centrality criteria under `FaithfulSMul`.
-/

public section

noncomputable section

open scoped MultiplierAlgebra

namespace DoubleCentralizer

section NontriviallyNormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- Two multipliers are equal if their left and right centralizers agree pointwise. -/
theorem ext_fst_snd {m n : 𝓜(𝕜, A)}
    (h₁ : ∀ a, m.fst a = n.fst a) (h₂ : ∀ a, m.snd a = n.snd a) : m = n :=
  DoubleCentralizer.ext _ _ _ _ <|
    Prod.ext (ContinuousLinearMap.ext h₁) (ContinuousLinearMap.ext h₂)

/-- Projection from a multiplier to its pair of left and right centralizers is norm continuous. -/
@[fun_prop]
theorem continuous_toProd :
    Continuous (DoubleCentralizer.toProd : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)) :=
  AddMonoidHomClass.continuous_of_bound toProdHom 1 fun m => by
    rw [one_mul, norm_def]

/-- The norm of a multiplier dominates the norm of its right centralizer. -/
theorem norm_snd_le (m : 𝓜(𝕜, A)) : ‖m.snd‖ ≤ ‖m‖ :=
  (norm_def m).symm ▸ _root_.norm_snd_le (toProdHom m)

/-- The norm of a multiplier dominates the norm of its left centralizer. -/
theorem norm_fst_le (m : 𝓜(𝕜, A)) : ‖m.fst‖ ≤ ‖m‖ :=
  (norm_def m).symm ▸ _root_.norm_fst_le (toProdHom m)

/-- The canonical map of `A` into its multiplier algebra is contractive. -/
theorem norm_coe_le (a : A) : ‖(a : 𝓜(𝕜, A))‖ ≤ ‖a‖ := by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, coe_fst, coe_snd, max_le_iff]
  exact ⟨ContinuousLinearMap.opNorm_mul_apply_le 𝕜 A a,
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => by
      simpa [mul_comm ‖a‖] using norm_mul_le x a⟩

/-- A pointwise continuous family of operator-norm-bounded left centralizers is jointly continuous
on `X × A`. -/
theorem continuous_fst_of_opNorm_le {X : Type*} [TopologicalSpace X] {C : ℝ} {m : X → 𝓜(𝕜, A)}
    (hC : ∀ x, ‖(m x).fst‖ ≤ C) (hm : ∀ a, Continuous fun x => (m x).fst a) :
    Continuous fun p : X × A => (m p.1).fst p.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ C.toNNReal
    (fun x => (m x).fst.lipschitzWith.weaken <| (hC x).trans (Real.le_coe_toNNReal C)) hm

/-- A pointwise continuous family of operator-norm-bounded right centralizers is jointly continuous
on `X × A`. -/
theorem continuous_snd_of_opNorm_le {X : Type*} [TopologicalSpace X] {C : ℝ} {m : X → 𝓜(𝕜, A)}
    (hC : ∀ x, ‖(m x).snd‖ ≤ C) (hm : ∀ a, Continuous fun x => (m x).snd a) :
    Continuous fun p : X × A => (m p.1).snd p.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ C.toNNReal
    (fun x => (m x).snd.lipschitzWith.weaken <| (hC x).trans (Real.le_coe_toNNReal C)) hm

/-- The inclusion of `A` into its multiplier algebra sends `0` to `0`. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : A) : 𝓜(𝕜, A)) = 0 :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with addition. -/
@[simp, norm_cast]
theorem coe_add (a b : A) : ((a + b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) + b :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with multiplication. -/
@[simp, norm_cast]
theorem coe_mul (a b : A) : ((a * b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) * b :=
  ext_fst_snd (fun _ => by simp [mul_assoc]) (fun _ => by simp [mul_assoc])

/-- The inclusion of `A` into its multiplier algebra commutes with negation. -/
@[simp, norm_cast]
theorem coe_neg (a : A) : ((-a : A) : 𝓜(𝕜, A)) = -(a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with subtraction. -/
@[simp, norm_cast]
theorem coe_sub (a b : A) : ((a - b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) - b :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with scalar multiplication. -/
@[simp, norm_cast]
theorem coe_smul (c : 𝕜) (a : A) : ((c • a : A) : 𝓜(𝕜, A)) = c • (a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with the star operation. -/
@[simp, norm_cast]
theorem coe_star [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] (a : A) :
    ((star a : A) : 𝓜(𝕜, A)) = star (a : 𝓜(𝕜, A)) :=
  map_star (coeHom (𝕜 := 𝕜)) a

end NontriviallyNormed

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The inclusion of a unital algebra into its multiplier algebra sends `1` to `1`. -/
@[simp, norm_cast]
theorem coe_one : ((1 : A) : 𝓜(𝕜, A)) = 1 :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

@[simp] theorem snd_one_eq_fst_one (m : 𝓜(𝕜, A)) : m.snd 1 = m.fst 1 := by
  simpa using m.central 1 1

theorem fst_apply_eq_fst_one_mul (m : 𝓜(𝕜, A)) (a : A) : m.fst a = m.fst 1 * a := by
  simpa using (m.central 1 a).symm

theorem snd_apply_eq_mul_fst_one (m : 𝓜(𝕜, A)) (a : A) : m.snd a = a * m.fst 1 := by
  simpa using m.central a 1

/-- Every multiplier of a unital normed algebra `A` is the image of `m.fst 1 : A`. -/
@[simp] theorem coe_fst_one (m : 𝓜(𝕜, A)) : ((m.fst 1 : A) : 𝓜(𝕜, A)) = m :=
  ext_fst_snd (fun a => (fst_apply_eq_fst_one_mul m a).symm)
    (fun a => (snd_apply_eq_mul_fst_one m a).symm)

variable (𝕜 A) in
/-- For a unital normed algebra `A`, the canonical inclusion `A → 𝓜(𝕜, A)` is an algebra
isomorphism with inverse `m ↦ m.fst 1`. -/
def ofUnitalAlgEquiv : A ≃ₐ[𝕜] 𝓜(𝕜, A) where
  toFun a := a
  invFun m := m.fst 1
  left_inv a := by simp
  right_inv := coe_fst_one
  map_mul' := coe_mul
  map_add' := coe_add
  commutes' k := ext_fst_snd (fun _ => by simp [Algebra.algebraMap_eq_smul_one])
    (fun _ => by simp [Algebra.algebraMap_eq_smul_one])

@[simp] theorem ofUnitalAlgEquiv_apply (a : A) : ofUnitalAlgEquiv 𝕜 A a = a := (rfl)

@[simp] theorem ofUnitalAlgEquiv_symm_apply (m : 𝓜(𝕜, A)) :
    (ofUnitalAlgEquiv 𝕜 A).symm m = m.fst 1 := (rfl)

theorem coe_surjective : Function.Surjective (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) :=
  (ofUnitalAlgEquiv 𝕜 A).surjective

theorem coe_bijective : Function.Bijective (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) :=
  (ofUnitalAlgEquiv 𝕜 A).bijective

variable (𝕜 A) in
/-- For a unital normed `⋆`-algebra `A`, the canonical inclusion `A → 𝓜(𝕜, A)` is a unital
`⋆`-algebra isomorphism with inverse `m ↦ m.fst 1`. -/
def ofUnitalStarAlgEquiv [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] :
    A ≃⋆ₐ[𝕜] 𝓜(𝕜, A) where
  __ := ofUnitalAlgEquiv 𝕜 A
  map_smul' := coe_smul
  map_star' := coe_star

@[simp] theorem ofUnitalStarAlgEquiv_apply [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A]
    [NormedStarGroup A] (a : A) : ofUnitalStarAlgEquiv 𝕜 A a = a := (rfl)

@[simp] theorem ofUnitalStarAlgEquiv_symm_apply [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A]
    [NormedStarGroup A] (m : 𝓜(𝕜, A)) : (ofUnitalStarAlgEquiv 𝕜 A).symm m = m.fst 1 := (rfl)

end Unital

section FaithfulMulOpposite

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [FaithfulSMul Aᵐᵒᵖ A]

/-- The left centralizer of a multiplier commutes with right multiplication. -/
theorem fst_mul (m : 𝓜(𝕜, A)) (a b : A) : m.fst (a * b) = m.fst a * b :=
  MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [op_smul_eq_mul, op_smul_eq_mul, ← mul_assoc, ← m.central, ← m.central, mul_assoc]

/-- A multiplier times an element of `A` is the element obtained from the left centralizer. -/
@[simp]
theorem mul_coe_eq_coe_fst (m : 𝓜(𝕜, A)) (a : A) : m * (a : 𝓜(𝕜, A)) = (m.fst a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp [fst_mul]) (fun _ => by simp [m.central])

/-- The canonical map of `A` into its multiplier algebra is injective. -/
theorem coe_injective : Function.Injective (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) :=
  fun a b h => MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [op_smul_eq_mul, op_smul_eq_mul]
    simpa using congrArg (fun m : 𝓜(𝕜, A) => m.snd y) h

@[simp, norm_cast]
theorem coe_inj {a b : A} : (a : 𝓜(𝕜, A)) = b ↔ a = b :=
  coe_injective.eq_iff

end FaithfulMulOpposite

section UnitalEquiv

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]

variable (𝕜 A) in
/-- A unital normed star algebra is star-isomorphic to its multiplier algebra through the
canonical inclusion; the inverse evaluates the left centralizer at `1`. -/
def coeStarAlgEquiv : A ≃⋆ₐ[𝕜] 𝓜(𝕜, A) where
  __ := (coeHom : A →⋆ₙₐ[𝕜] 𝓜(𝕜, A))
  invFun m := m.fst 1
  left_inv a := by simp
  right_inv := coe_fst_one

@[simp]
theorem coeStarAlgEquiv_apply (a : A) : coeStarAlgEquiv 𝕜 A a = (a : 𝓜(𝕜, A)) :=
  (rfl)

@[simp]
theorem coeStarAlgEquiv_symm_apply (m : 𝓜(𝕜, A)) : (coeStarAlgEquiv 𝕜 A).symm m = m.fst 1 :=
  (rfl)

/-- The star isomorphism `coeStarAlgEquiv`, as a nonunital star homomorphism, is the canonical
inclusion `coeHom`. -/
@[simp]
theorem coeStarAlgEquiv_toNonUnitalStarAlgHom :
    (coeStarAlgEquiv 𝕜 A).toNonUnitalStarAlgHom = coeHom :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- The inverse of `coeStarAlgEquiv` undoes the canonical inclusion `coeHom`. -/
@[simp]
theorem coeStarAlgEquiv_symm_comp_coeHom :
    (coeStarAlgEquiv 𝕜 A).symm.toNonUnitalStarAlgHom.comp coeHom =
      NonUnitalStarAlgHom.id 𝕜 A :=
  NonUnitalStarAlgHom.ext fun a ↦ by simp

end UnitalEquiv

section Faithful

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [FaithfulSMul A A]

/-- The right centralizer of a multiplier commutes with left multiplication. -/
theorem snd_mul (m : 𝓜(𝕜, A)) (a b : A) : m.snd (a * b) = a * m.snd b :=
  FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [smul_eq_mul, smul_eq_mul, m.central, mul_assoc, mul_assoc, m.central]

/-- An element of `A` times a multiplier is the element obtained from the right centralizer. -/
@[simp]
theorem coe_mul_eq_coe_snd (a : A) (m : 𝓜(𝕜, A)) : (a : 𝓜(𝕜, A)) * m = (m.snd a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp [m.central]) (fun _ => by simp [snd_mul])

/-- A multiplier is determined by its left centralizer. -/
theorem ext_fst {m n : 𝓜(𝕜, A)} (h : ∀ a, m.fst a = n.fst a) : m = n :=
  ext_fst_snd h fun a => FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [smul_eq_mul, smul_eq_mul, m.central, n.central, h]

end Faithful

section Essential

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [FaithfulSMul Aᵐᵒᵖ A] [FaithfulSMul A A]

/-- A multiplier whose products with every element of `A` on the right vanish is zero. -/
theorem eq_zero_of_forall_mul_coe_eq_zero {m : 𝓜(𝕜, A)} (h : ∀ a : A, m * (a : 𝓜(𝕜, A)) = 0) :
    m = 0 :=
  ext_fst fun a => coe_injective (𝕜 := 𝕜) <| by
    simp [← mul_coe_eq_coe_fst, h]

/-- A multiplier whose products with every element of `A` on the left vanish is zero. -/
theorem eq_zero_of_forall_coe_mul_eq_zero {m : 𝓜(𝕜, A)} (h : ∀ a : A, (a : 𝓜(𝕜, A)) * m = 0) :
    m = 0 := by
  have hsnd (a : A) : m.snd a = 0 := coe_injective (𝕜 := 𝕜) <| by
    rw [← coe_mul_eq_coe_snd, h, coe_zero]
  refine ext_fst_snd (fun a => MulOpposite.op_injective <|
    FaithfulSMul.eq_of_smul_eq_smul (α := A) fun c => ?_) fun a => by simp [hsnd]
  rw [op_smul_eq_mul, op_smul_eq_mul]
  simp [← m.central, hsnd]

/-- With zero left and right annihilators, a multiplier commutes with every multiplier if and only
if its left and right centralizers agree on `A`. -/
theorem forall_commute_iff_fst_eq_snd {m : 𝓜(𝕜, A)} :
    (∀ n : 𝓜(𝕜, A), Commute m n) ↔ ∀ a : A, m.fst a = m.snd a := by
  refine ⟨fun h a => coe_injective (𝕜 := 𝕜) ?_, fun h n => ext_fst fun c =>
    MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul (α := A) fun d => ?_⟩
  · rw [← mul_coe_eq_coe_fst, ← coe_mul_eq_coe_snd]
    exact h a
  · simp only [op_smul_eq_mul, mul_fst, mul_apply_eq_comp]
    calc d * m.fst (n.fst c)
        = d * m.snd (n.fst c) := by rw [h]
      _ = m.snd (d * n.fst c) := (snd_mul m d (n.fst c)).symm
      _ = m.snd (n.snd d * c) := by rw [n.central]
      _ = n.snd d * m.snd c := snd_mul m (n.snd d) c
      _ = d * n.fst (m.snd c) := n.central d (m.snd c)
      _ = d * n.fst (m.fst c) := by rw [h]

/-- With zero left and right annihilators, a multiplier lies in the center of `𝓜(𝕜, A)` if and
only if its left and right centralizers agree on `A`. -/
theorem mem_center_iff {m : 𝓜(𝕜, A)} :
    m ∈ Subring.center 𝓜(𝕜, A) ↔ ∀ a : A, m.fst a = m.snd a :=
  Subring.mem_center_iff.trans <|
    (forall_congr' fun g => (commute_iff_eq (a := g) (b := m)).symm.trans Commute.symm_iff).trans
      forall_commute_iff_fst_eq_snd

end Essential

end DoubleCentralizer
