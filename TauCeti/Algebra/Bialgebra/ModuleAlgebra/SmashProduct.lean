/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# The smash product of a module algebra

For a left module algebra `A` over a bialgebra `H`, the smash product `A # H` is the
`R`-module `A ⊗ H` with the product `(a # h)(b # l) = Σ a (h₁ · b) # h₂ l` and unit `1 # 1`.
It is the algebra whose modules are the `A`-modules with a compatible `H`-action, and the
algebra over which relative hopfological categories of `A`-modules are formed.

## Construction

Rather than checking associativity of the formula directly, the smash product is realised
through its left regular representation. The algebra maps `a ↦ (a ⊗ 1) · -` and
`h ↦ (b ⊗ l ↦ Σ (h₁ · b) ⊗ h₂ l)` into `End_R (A ⊗ H)` satisfy the covariance relation
`L_h L_a = Σ L_{h₁ · a} L_{h₂}`, so the operators `L_a L_h` span a subalgebra. Evaluation at
`1 ⊗ 1` identifies this subalgebra with `A ⊗ H`, and the product of two such operators is the
operator of the smash-product formula. The ring axioms are inherited from `End_R (A ⊗ H)`.

## Main definitions and results

* `TauCeti.LeftModuleAlgebra.SmashProduct μ`: the smash product `A # H`, an `R`-algebra.
* `SmashProduct.linearEquivTensor`: its underlying `R`-module is `A ⊗ H`.
* `SmashProduct.pure a h`: the element `a # h`, with the product formula
  `SmashProduct.pure_mul_pure` and unit `SmashProduct.pure_one_one`.
* `SmashProduct.includeA` and `SmashProduct.includeH`: the algebra maps `a ↦ a # 1` and
  `h ↦ 1 # h`, related by the covariance law `SmashProduct.includeH_mul_includeA`.
* `LeftModuleAlgebra.SmashCompatible`: the covariance relation
  `fH(h) fA(a) = Σ fA(h₁ · a) fH(h₂)` for a pair of algebra maps.
* `SmashProduct.lift` and `SmashProduct.liftEquiv`: the universal property, under which algebra
  maps out of `A # H` are the same as covariant pairs.
* `SmashProduct.includeA_injective`, and `SmashProduct.includeH_injective` for flat `H` and
  `R → A` injective.
* `SmashProduct.map`: functoriality in equivariant algebra maps.
* `SmashProduct.trivialAlgEquiv`: for the trivial action, `A # H ≅ A ⊗ H` as algebras.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS 82, §4.1.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra TensorProduct

namespace TauCeti

namespace LeftModuleAlgebra

variable {R H A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring A] [Algebra R A] (μ : LeftModuleAlgebra R H A)

/-! ### The left regular representation -/

/-- Left multiplication by `a ⊗ 1` on `A ⊗ H`. -/
private noncomputable def regA : A →ₐ[R] Module.End R (A ⊗[R] H) :=
  (Algebra.lmul R (A ⊗[R] H)).comp Algebra.TensorProduct.includeLeft

/-- The operator `b ⊗ l ↦ Σ (h₁ · b) ⊗ h₂ l` on `A ⊗ H`. -/
private noncomputable def regH : H →ₐ[R] Module.End R (A ⊗[R] H) :=
  (Module.endTensorEndAlgHom (R := R) (S := R) (A := R)).comp
    ((Algebra.TensorProduct.map μ.action (Algebra.lmul R H)).comp (Bialgebra.comulAlgHom R H))

private theorem regA_tmul (a b : A) (l : H) :
    regA (H := H) a (b ⊗ₜ[R] l) = (a * b) ⊗ₜ[R] l := by
  simp [regA]

private theorem regH_tmul {h : H} {ι : Type*} (r : Repr R h ι) (b : A) (l : H) :
    μ.regH h (b ⊗ₜ[R] l) = ∑ i ∈ r.index, μ.action (r.left i) b ⊗ₜ[R] (r.right i * l) := by
  simp [regH, ← r.eq, map_sum, Module.endTensorEndAlgHom_apply]

private theorem regH_tmul_arbitrary (h : H) (b : A) (l : H) :
    μ.regH h (b ⊗ₜ[R] l) =
      ∑ i ∈ (ℛ R h).index, μ.action ((ℛ R h).left i) b ⊗ₜ[R] ((ℛ R h).right i * l) :=
  μ.regH_tmul (ℛ R h) b l

/-- The covariance relation between the two halves of the regular representation. -/
private theorem regH_mul_regA {h : H} {ι : Type*} (r : Repr R h ι) (a : A) :
    μ.regH h * regA a =
      ∑ i ∈ r.index, regA (μ.action (r.left i) a) * μ.regH (r.right i) := by
  ext b l
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.restrictScalars_apply,
    mul_apply_eq_comp, LinearMap.coe_sum, Finset.sum_apply, regA_tmul, μ.regH_tmul r,
    regH_tmul_arbitrary, map_sum, μ.action_mul_eq_sum (ℛ R (r.left _)), TensorProduct.sum_tmul]
  -- Both sides are images of the two bracketings of `Δ² h` under the same linear map.
  let T : H ⊗[R] (H ⊗[R] H) →ₗ[R] A ⊗[R] H :=
    (LinearMap.mul' R A).rTensor H ∘ₗ (TensorProduct.assoc R A A H).symm.toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.applyₗ a ∘ₗ μ.action.toLinearMap)
        (TensorProduct.map (LinearMap.applyₗ b ∘ₗ μ.action.toLinearMap)
          (LinearMap.mulRight R l))
  have := congrArg T (sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
  simpa [T, map_sum, mul_assoc] using this

/-- The regular representation, `a ⊗ h ↦ L_a L_h`. -/
private noncomputable def reg : A ⊗[R] H →ₗ[R] Module.End R (A ⊗[R] H) :=
  TensorProduct.lift ((LinearMap.mul R _).compl₁₂ (regA (H := H)).toLinearMap
    μ.regH.toLinearMap)

private theorem reg_tmul (a : A) (h : H) : μ.reg (a ⊗ₜ[R] h) = regA a * μ.regH h := by
  simp [reg]

private theorem reg_apply_one (x : A ⊗[R] H) : μ.reg x (1 ⊗ₜ[R] 1) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a h =>
    rw [reg_tmul, mul_apply_eq_comp, μ.regH_tmul (ℛ R h)]
    simp only [regA_tmul, action_one, mul_one, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sum, sum_counit_smul]

private theorem reg_injective : Function.Injective μ.reg := fun x y hxy => by
  rw [← μ.reg_apply_one x, hxy, μ.reg_apply_one]

/-- The regular representation is multiplicative for the product `x * y = L_x y`. -/
private theorem reg_reg (x y : A ⊗[R] H) : μ.reg (μ.reg x y) = μ.reg x * μ.reg y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [hx, hx', add_mul]
  | tmul a h =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp [hy, hy', mul_add]
    | tmul b l =>
      rw [reg_tmul, reg_tmul, mul_assoc, ← mul_assoc (μ.regH h), μ.regH_mul_regA (ℛ R h),
        mul_apply_eq_comp, μ.regH_tmul (ℛ R h)]
      simp only [map_sum, regA_tmul, reg_tmul, Finset.mul_sum, Finset.sum_mul, map_mul,
        mul_assoc]

private theorem regA_eq_reg (a : A) : regA a = μ.reg (a ⊗ₜ[R] 1) := by
  simp [reg_tmul]

private theorem regH_eq_reg (h : H) : μ.regH h = μ.reg (1 ⊗ₜ[R] h) := by
  simp [reg_tmul]

/-- The smash product realised by operators: the image of the left regular representation
`a ⊗ h ↦ L_a L_h`, a subalgebra of `End_R (A ⊗ H)` which evaluation at `1 ⊗ 1` identifies with
`A ⊗ H`. This is an implementation detail of `SmashProduct`: it is public only because the
instances on `SmashProduct` unfold to it, and should be accessed through the `SmashProduct` API. -/
noncomputable def smashSubalgebra : Subalgebra R (Module.End R (A ⊗[R] H)) :=
  (LinearMap.range μ.reg).toSubalgebra ⟨1 ⊗ₜ[R] 1, by simp [reg_tmul]⟩ <| by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨μ.reg x y, μ.reg_reg x y⟩

/-- The smash product `A # H` of a left module algebra `A` over a bialgebra `H`: the algebra
with underlying module `A ⊗ H` and product `(a # h)(b # l) = Σ a (h₁ · b) # h₂ l`. -/
def SmashProduct : Type _ :=
  μ.smashSubalgebra

namespace SmashProduct

noncomputable instance : Semiring (SmashProduct μ) :=
  inferInstanceAs (Semiring μ.smashSubalgebra)

noncomputable instance : Algebra R (SmashProduct μ) :=
  inferInstanceAs (Algebra R μ.smashSubalgebra)

noncomputable instance {R H A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
    [Ring A] [Algebra R A] (μ : LeftModuleAlgebra R H A) : Ring (SmashProduct μ) :=
  letI : Neg μ.smashSubalgebra := ⟨fun f => ⟨-f, by
    obtain ⟨x, hx⟩ := f.property
    exact ⟨-x, by rw [map_neg, hx]⟩⟩⟩
  letI : Ring μ.smashSubalgebra :=
    { (inferInstance : Semiring μ.smashSubalgebra) with
      zsmul := zsmulRec
      neg_add_cancel := fun f => Subtype.ext (neg_add_cancel (f : Module.End R (A ⊗[R] H))) }
  inferInstanceAs (Ring μ.smashSubalgebra)

/-- The underlying `R`-module of `A # H` is `A ⊗ H`. -/
noncomputable def linearEquivTensor : SmashProduct μ ≃ₗ[R] A ⊗[R] H :=
  μ.smashSubalgebra.toSubmoduleEquiv.symm ≪≫ₗ
    LinearEquiv.ofEq _ _ (Submodule.toSubalgebra_toSubmodule _ _ _) ≪≫ₗ
      (LinearEquiv.ofInjective μ.reg μ.reg_injective).symm

variable {μ}

private theorem coe_linearEquivTensor_symm (x : A ⊗[R] H) :
    (((linearEquivTensor μ).symm x : SmashProduct μ) : μ.smashSubalgebra).val = μ.reg x :=
  rfl

/-- The product of `A # H` is the composition of operators. -/
private theorem val_mul (x y : SmashProduct μ) :
    ((x * y : SmashProduct μ) : μ.smashSubalgebra).val =
      (x : μ.smashSubalgebra).val * (y : μ.smashSubalgebra).val :=
  rfl

private theorem linearEquivTensor_mul (x y : SmashProduct μ) :
    linearEquivTensor μ (x * y) = μ.reg (linearEquivTensor μ x) (linearEquivTensor μ y) := by
  obtain ⟨x', rfl⟩ := (linearEquivTensor μ).symm.surjective x
  obtain ⟨y', rfl⟩ := (linearEquivTensor μ).symm.surjective y
  have h : (linearEquivTensor μ).symm x' * (linearEquivTensor μ).symm y' =
      (linearEquivTensor μ).symm (μ.reg x' y') :=
    Subtype.ext <| by
      rw [val_mul, coe_linearEquivTensor_symm, coe_linearEquivTensor_symm,
        coe_linearEquivTensor_symm, μ.reg_reg]
  simp only [h, LinearEquiv.apply_symm_apply]

/-- The element `a # h` of the smash product. -/
noncomputable def pure (a : A) (h : H) : SmashProduct μ :=
  (linearEquivTensor μ).symm (a ⊗ₜ[R] h)

private theorem val_pure (a : A) (h : H) :
    ((pure a h : SmashProduct μ) : μ.smashSubalgebra).val = μ.reg (a ⊗ₜ[R] h) :=
  coe_linearEquivTensor_symm _

@[simp]
theorem linearEquivTensor_pure (a : A) (h : H) :
    linearEquivTensor μ (pure a h) = a ⊗ₜ[R] h :=
  (linearEquivTensor μ).apply_symm_apply _

@[simp]
theorem linearEquivTensor_symm_tmul (a : A) (h : H) :
    (linearEquivTensor μ).symm (a ⊗ₜ[R] h) = pure a h :=
  (rfl)

/-- The product formula `(a # h)(b # l) = Σ a (h₁ · b) # h₂ l`, in any representation of
`Δ h`. -/
theorem pure_mul_pure {h : H} {ι : Type*} (r : Repr R h ι) (a b : A) (l : H) :
    pure (μ := μ) a h * pure b l =
      ∑ i ∈ r.index, pure (a * μ.action (r.left i) b) (r.right i * l) := by
  apply (linearEquivTensor μ).injective
  rw [linearEquivTensor_mul, linearEquivTensor_pure, linearEquivTensor_pure, map_sum, reg_tmul,
    mul_apply_eq_comp, μ.regH_tmul r]
  simp [regA_tmul]

/-- The unit of the smash product is `1 # 1`. -/
@[simp]
theorem pure_one_one : pure (μ := μ) 1 1 = 1 :=
  Subtype.ext (by
    rw [val_pure, reg_tmul, map_one, map_one, one_mul]
    exact (Subalgebra.coe_one _).symm)

@[simp]
theorem pure_zero_left (h : H) : pure (μ := μ) 0 h = 0 := by
  simp only [← linearEquivTensor_symm_tmul, TensorProduct.zero_tmul, map_zero]

@[simp]
theorem pure_zero_right (a : A) : pure (μ := μ) a 0 = 0 := by
  simp only [← linearEquivTensor_symm_tmul, TensorProduct.tmul_zero, map_zero]

@[simp]
theorem pure_add_left (a b : A) (h : H) : pure (μ := μ) (a + b) h = pure a h + pure b h := by
  simp only [← linearEquivTensor_symm_tmul, TensorProduct.add_tmul, map_add]

@[simp]
theorem pure_add_right (a : A) (h l : H) : pure (μ := μ) a (h + l) = pure a h + pure a l := by
  simp only [← linearEquivTensor_symm_tmul, TensorProduct.tmul_add, map_add]

@[simp]
theorem pure_smul_left (c : R) (a : A) (h : H) : pure (μ := μ) (c • a) h = c • pure a h := by
  simp only [← linearEquivTensor_symm_tmul, ← TensorProduct.smul_tmul', map_smul]

@[simp]
theorem pure_smul_right (c : R) (a : A) (h : H) : pure (μ := μ) a (c • h) = c • pure a h := by
  simp only [← linearEquivTensor_symm_tmul, TensorProduct.tmul_smul, map_smul]

/-- The algebra map `a ↦ a # 1`. -/
noncomputable def includeA : A →ₐ[R] SmashProduct μ :=
  regA.codRestrict μ.smashSubalgebra fun a => ⟨a ⊗ₜ[R] 1, (μ.regA_eq_reg a).symm⟩

/-- The algebra map `h ↦ 1 # h`. -/
noncomputable def includeH : H →ₐ[R] SmashProduct μ :=
  μ.regH.codRestrict μ.smashSubalgebra fun h => ⟨1 ⊗ₜ[R] h, (μ.regH_eq_reg h).symm⟩

private theorem val_includeA (a : A) :
    ((includeA a : SmashProduct μ) : μ.smashSubalgebra).val = regA a :=
  AlgHom.coe_codRestrict _ _ _ a

private theorem val_includeH (h : H) :
    ((includeH h : SmashProduct μ) : μ.smashSubalgebra).val = μ.regH h :=
  AlgHom.coe_codRestrict _ _ _ h

theorem includeA_eq_pure (a : A) : includeA (μ := μ) a = pure a 1 :=
  Subtype.ext <| by rw [val_includeA, val_pure, regA_eq_reg]

theorem includeH_eq_pure (h : H) : includeH (μ := μ) h = pure 1 h :=
  Subtype.ext <| by rw [val_includeH, val_pure, regH_eq_reg]

@[simp]
theorem includeA_mul_includeH (a : A) (h : H) :
    includeA (μ := μ) a * includeH h = pure a h :=
  Subtype.ext <| by
    rw [val_mul, val_includeA, val_includeH, val_pure, reg_tmul]

@[simp]
theorem linearEquivTensor_includeA (a : A) :
    linearEquivTensor μ (includeA a) = a ⊗ₜ[R] 1 := by
  rw [includeA_eq_pure, linearEquivTensor_pure]

@[simp]
theorem linearEquivTensor_includeH (h : H) :
    linearEquivTensor μ (includeH h) = 1 ⊗ₜ[R] h := by
  rw [includeH_eq_pure, linearEquivTensor_pure]

@[simp]
theorem linearEquivTensor_one : linearEquivTensor μ 1 = 1 ⊗ₜ[R] 1 := by
  rw [← pure_one_one, linearEquivTensor_pure]

/-- The covariance relation `(1 # h)(a # 1) = Σ (h₁ · a # 1)(1 # h₂)` in the smash product. -/
theorem includeH_mul_includeA {h : H} {ι : Type*} (r : Repr R h ι) (a : A) :
    includeH (μ := μ) h * includeA a =
      ∑ i ∈ r.index, includeA (μ.action (r.left i) a) * includeH (r.right i) := by
  rw [includeH_eq_pure, includeA_eq_pure, pure_mul_pure r]
  simp only [one_mul, mul_one, includeA_mul_includeH]

/-- Induction on the smash product: a property of sums of elements `a # h`. -/
@[elab_as_elim]
theorem inductionOn {motive : SmashProduct μ → Prop} (x : SmashProduct μ)
    (pure : ∀ a h, motive (pure a h)) (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x := by
  obtain ⟨x, rfl⟩ := (linearEquivTensor μ).symm.surjective x
  induction x using TensorProduct.inductionOn with
  | tmul a h => exact pure a h
  | add x y hx hy => simpa only [map_add] using add _ _ hx hy

end SmashProduct

/-! ### The universal property -/

variable {C D : Type*} [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]

/-- A pair of algebra maps out of `A` and `H` is smash-compatible when it satisfies the
covariance relation `fH(h) fA(a) = Σ fA(h₁ · a) fH(h₂)`, stated without a choice of
representation of `Δ h`. These are the pairs that factor through the smash product. -/
def SmashCompatible (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) : Prop :=
  ∀ h a, fH h * fA a = LinearMap.mul' R C (TensorProduct.map
    (fA.toLinearMap ∘ₗ LinearMap.applyₗ a ∘ₗ μ.action.toLinearMap) fH.toLinearMap (comul h))

variable {μ}

/-- The covariance relation in any representation of `Δ h`. -/
theorem SmashCompatible.mul_eq_sum {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hc : μ.SmashCompatible fA fH) {h : H} {ι : Type*} (r : Repr R h ι) (a : A) :
    fH h * fA a = ∑ i ∈ r.index, fA (μ.action (r.left i) a) * fH (r.right i) := by
  simp [hc h a, ← r.eq, map_sum]

/-- Smash compatibility is the covariance relation in the chosen representation `ℛ R h` of
`Δ h`. -/
theorem smashCompatible_iff {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} :
    μ.SmashCompatible fA fH ↔ ∀ h a,
      fH h * fA a = ∑ i ∈ (ℛ R h).index, fA (μ.action ((ℛ R h).left i) a) * fH ((ℛ R h).right i) :=
  ⟨fun hc h a => hc.mul_eq_sum (ℛ R h) a, fun hc h a => by
    simp [hc h a, ← (ℛ R h).eq, map_sum]⟩

/-- Smash-compatible pairs are stable under postcomposition. -/
theorem SmashCompatible.comp {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hc : μ.SmashCompatible fA fH) (g : C →ₐ[R] D) :
    μ.SmashCompatible (g.comp fA) (g.comp fH) :=
  smashCompatible_iff.mpr fun h a => by
    simp [← map_mul, hc.mul_eq_sum (ℛ R h) a, map_sum]

namespace SmashProduct

/-- The canonical maps into the smash product form a smash-compatible pair. -/
theorem smashCompatible_includeA_includeH :
    μ.SmashCompatible (includeA (μ := μ)) includeH :=
  smashCompatible_iff.mpr fun h a => includeH_mul_includeA (ℛ R h) a

/-- The linear map `a # h ↦ fA(a) fH(h)` underlying `SmashProduct.lift`. -/
private noncomputable def liftLinear (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) :
    SmashProduct μ →ₗ[R] C :=
  TensorProduct.lift ((LinearMap.mul R C).compl₁₂ fA.toLinearMap fH.toLinearMap) ∘ₗ
    (linearEquivTensor μ).toLinearMap

private theorem liftLinear_pure (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (a : A) (h : H) :
    liftLinear (μ := μ) fA fH (pure a h) = fA a * fH h := by
  simp [liftLinear]

private theorem liftLinear_mul {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hc : μ.SmashCompatible fA fH) (x y : SmashProduct μ) :
    liftLinear fA fH (x * y) = liftLinear fA fH x * liftLinear fA fH y := by
  induction x using inductionOn with
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | pure a h =>
    induction y using inductionOn with
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | pure b l =>
      simp only [pure_mul_pure (ℛ R h), map_sum, liftLinear_pure, map_mul]
      rw [mul_assoc (fA a), ← mul_assoc (fH h), hc.mul_eq_sum (ℛ R h)]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- The algebra map out of the smash product determined by a smash-compatible pair:
`a # h ↦ fA(a) fH(h)`. -/
noncomputable def lift (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hc : μ.SmashCompatible fA fH) :
    SmashProduct μ →ₐ[R] C :=
  AlgHom.ofLinearMap (liftLinear fA fH)
    (by rw [← pure_one_one, liftLinear_pure, map_one, map_one, one_mul])
    (liftLinear_mul hc)

@[simp]
theorem lift_pure {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hc : μ.SmashCompatible fA fH)
    (a : A) (h : H) : lift fA fH hc (pure a h) = fA a * fH h :=
  liftLinear_pure fA fH a h

@[simp]
theorem lift_includeA {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hc : μ.SmashCompatible fA fH)
    (a : A) : lift fA fH hc (includeA a) = fA a := by
  simp [includeA_eq_pure]

@[simp]
theorem lift_includeH {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hc : μ.SmashCompatible fA fH)
    (h : H) : lift fA fH hc (includeH h) = fH h := by
  simp [includeH_eq_pure]

@[simp]
theorem lift_comp_includeA {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hc : μ.SmashCompatible fA fH) :
    (lift fA fH hc).comp includeA = fA :=
  AlgHom.ext (lift_includeA hc)

@[simp]
theorem lift_comp_includeH {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hc : μ.SmashCompatible fA fH) :
    (lift fA fH hc).comp includeH = fH :=
  AlgHom.ext (lift_includeH hc)

/-- Algebra maps out of the smash product are determined by their restrictions to `A` and `H`. -/
@[ext]
theorem algHom_ext {f g : SmashProduct μ →ₐ[R] C} (hA : f.comp includeA = g.comp includeA)
    (hH : f.comp includeH = g.comp includeH) : f = g := by
  ext x
  induction x using inductionOn with
  | pure a h =>
    rw [← includeA_mul_includeH, map_mul, map_mul]
    exact congr($(congr($hA a)) * $(congr($hH h)))
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Uniqueness in the universal property: an algebra map out of `A # H` whose restrictions to
`A` and `H` are `fA` and `fH` is `lift fA fH hc`. -/
theorem lift_unique {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hc : μ.SmashCompatible fA fH)
    (f : SmashProduct μ →ₐ[R] C) (hA : f.comp includeA = fA) (hH : f.comp includeH = fH) :
    f = lift fA fH hc :=
  algHom_ext (by rw [hA, lift_comp_includeA]) (by rw [hH, lift_comp_includeH])

@[simp]
theorem lift_comp_includeA_includeH (f : SmashProduct μ →ₐ[R] C) :
    lift (f.comp includeA) (f.comp includeH) (smashCompatible_includeA_includeH.comp f) = f :=
  (lift_unique _ f rfl rfl).symm

/-- The universal property of the smash product: algebra maps out of `A # H` correspond to
smash-compatible pairs of algebra maps out of `A` and `H`. -/
noncomputable def liftEquiv :
    {p : (A →ₐ[R] C) × (H →ₐ[R] C) // μ.SmashCompatible p.1 p.2} ≃ (SmashProduct μ →ₐ[R] C) where
  toFun p := lift p.val.1 p.val.2 p.property
  invFun f := ⟨(f.comp includeA, f.comp includeH), smashCompatible_includeA_includeH.comp f⟩
  left_inv p :=
    Subtype.ext (Prod.ext (lift_comp_includeA p.property) (lift_comp_includeH p.property))
  right_inv := lift_comp_includeA_includeH

@[simp]
theorem liftEquiv_apply (p : {p : (A →ₐ[R] C) × (H →ₐ[R] C) // μ.SmashCompatible p.1 p.2}) :
    liftEquiv p = lift p.val.1 p.val.2 p.property :=
  (rfl)

@[simp]
theorem coe_liftEquiv_symm_apply (f : SmashProduct μ →ₐ[R] C) :
    (liftEquiv.symm f : (A →ₐ[R] C) × (H →ₐ[R] C)) = (f.comp includeA, f.comp includeH) :=
  (rfl)

/-! ### Injectivity of the inclusions -/

/-- The map `a ↦ a # 1` is injective for every module algebra. -/
theorem includeA_injective : Function.Injective (includeA (μ := μ)) := by
  intro a b hab
  have := congrArg (fun x => TensorProduct.rid R A ((counit (R := R) (A := H)).lTensor A
    (linearEquivTensor μ x))) hab
  simpa using this

/-- The map `h ↦ 1 # h` is injective when `H` is flat and `R → A` is injective, for instance
for a nonzero algebra over a field. -/
theorem includeH_injective [Module.Flat R H] (hA : Function.Injective (algebraMap R A)) :
    Function.Injective (includeH (μ := μ)) := by
  intro h l hhl
  have key : ∀ h : H, linearEquivTensor μ (includeH h) =
      (Algebra.linearMap R A).rTensor H ((TensorProduct.lid R H).symm h) := by
    simp
  have := congrArg (linearEquivTensor μ) hhl
  rw [key, key] at this
  exact (TensorProduct.lid R H).symm.injective
    (Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap R A) hA this)

/-! ### Functoriality and the trivial action -/

variable {B : Type*} [Semiring B] [Algebra R B] {ν : LeftModuleAlgebra R H B}

/-- An equivariant algebra map `A → B` induces `A # H → B # H`, `a # h ↦ f(a) # h`. -/
noncomputable def map (f : Hom μ ν) : SmashProduct μ →ₐ[R] SmashProduct ν :=
  lift (includeA.comp f.toAlgHom) includeH <| smashCompatible_iff.mpr fun h a => by
    simp [includeH_mul_includeA (ℛ R h)]

@[simp]
theorem map_pure (f : Hom μ ν) (a : A) (h : H) : map f (pure a h) = pure (f a) h := by
  simp [map]

@[simp]
theorem map_includeA (f : Hom μ ν) (a : A) : map f (includeA a) = includeA (f a) := by
  simp [map]

@[simp]
theorem map_includeH (f : Hom μ ν) (h : H) : map f (includeH h) = includeH h := by
  simp [map]

@[simp]
theorem map_id : map (Hom.id μ) = AlgHom.id R (SmashProduct μ) := by
  ext <;> simp

@[simp]
theorem map_comp {E : Type*} [Semiring E] [Algebra R E] {ξ : LeftModuleAlgebra R H E}
    (g : Hom ν ξ) (f : Hom μ ν) : map (g.comp f) = (map g).comp (map f) := by
  ext <;> simp

variable (R H A) in
/-- For the trivial action `h · a = ε(h) a`, the smash product is the tensor product algebra. -/
noncomputable def trivialAlgEquiv :
    SmashProduct (trivial (R := R) (H := H) (A := A)) ≃ₐ[R] A ⊗[R] H :=
  AlgEquiv.ofAlgHom
    (lift Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight <|
      smashCompatible_iff.mpr fun h a => by
        simp only [Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, trivial_action, TensorProduct.smul_tmul, smul_mul_assoc,
          ← TensorProduct.tmul_sum, sum_counit_smul])
    (Algebra.TensorProduct.lift includeA includeH fun a h => by
      rw [Commute, SemiconjBy, includeA_mul_includeH, includeH_mul_includeA (ℛ R h)]
      simp only [trivial_action, includeA_mul_includeH, ← linearEquivTensor_symm_tmul, ← map_sum,
        TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, sum_counit_smul])
    (by ext <;> simp)
    (by ext <;> simp)

@[simp]
theorem trivialAlgEquiv_pure (a : A) (h : H) :
    trivialAlgEquiv R H A (pure a h) = a ⊗ₜ[R] h := by
  simp [trivialAlgEquiv]

@[simp]
theorem trivialAlgEquiv_symm_tmul (a : A) (h : H) :
    (trivialAlgEquiv R H A).symm (a ⊗ₜ[R] h) = pure a h := by
  rw [AlgEquiv.symm_apply_eq, trivialAlgEquiv_pure]

end SmashProduct

end LeftModuleAlgebra

end TauCeti
