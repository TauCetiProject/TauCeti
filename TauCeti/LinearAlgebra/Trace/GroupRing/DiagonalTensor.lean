/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.LinearAlgebra.Trace.GroupRing.MonoidExtension

/-!
# Diagonal tensor products and group-ring Hattori–Stallings traces

Let `A` be a commutative ring, `Λ` a (not necessarily commutative) `A`-algebra (so `A → Λ` lands in
the center of `Λ`), `P` an `A[G]`-module, and `Q` a `Λ[G]`-module. The tensor product `P ⊗_A Q`
carries a left `Λ`-module structure through `Q` and a diagonal left `Λ[G]`-module structure sending
`single g c • (p ⊗ₜ q)` to `(single g 1 • p) ⊗ₜ (single g c • q)`.

This file packages `P ⊗_A Q` as `TauCeti.DiagonalTensor A Λ P Q` (so the diagonal `Λ[M]`-action does
not collide with the left-factor `TensorProduct.leftModule` instance on raw `Q ⊗[A] P`) and proves
Lemmas 64.15.6–64.15.8 of the Stacks Project, Section 64.15:

* `TauCeti.DiagonalTensor.shearingEquiv`: the `Λ[G]`-linear shearing isomorphism
  `Λ[G] ⊗_Λ Q ≃ₗ[Λ[G]] A[G] ⊗_A Q` sending `single g c ⊗ q` to `single g 1 ⊗ (single g c • q)`.
* `TauCeti.DiagonalTensor.monoidAlgebraFinite` and `TauCeti.DiagonalTensor.monoidAlgebraProjective`
  (Lemma 64.15.6): if `P` is finite projective over `A[G]` and `Q` is finite projective over `Λ`
  (without assuming `Q` is projective over `A`), then `P ⊗_A Q` is finite projective over `Λ[G]`.
* `LinearMap.hattoriStallingsGroupTrace_diagonalTensor_map` (Lemma 64.15.7): for an `A[G]`-linear
  endomorphism `u_P` of `P` and a `Λ[G]`-linear endomorphism `u_Q` of `Q`,
  `Tr_Λ^G(u_P ⊗ u_Q, P ⊗_A Q) = Tr_A^G(u_P, P) • Tr_Λ(u_Q, Q)` in `Λ / [Λ, Λ]`.
* `TauCeti.MonoidExtension.centralizerGroupTrace_diagonalTensor` and
  `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantEnd_diagonalTensor` (Lemma 64.15.8):
  for a monoid extension `1 → G → Γtilde → ℤ → 1`, the centralizer group-ring trace on `P ⊗_A Q`
  factors as `Tr_A^{Z_γ}(γ, P) • Tr_Λ(γ, Q)`, and the `Λ`-trace on `(P ⊗_A Q)_G` sums these
  products over `G`-conjugacy classes.

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.6, 64.15.7, and 64.15.8).
-/

public section

noncomputable section

namespace TauCeti

/-- The tensor product `P ⊗_A Q` over a commutative ring `A`, carrying left `Λ`-module structure
through `Q` and diagonal `Λ[M]`-module structure through both factors for any `A`-algebra `Λ` and
monoid `M`. Wrapping `Q ⊗[A] P` avoids typeclass collisions with the left-factor `MonoidAlgebra`
action `TensorProduct.leftModule` on `Q ⊗[A] P`. -/
structure DiagonalTensor (A : Type*) (_Λ : Type*) (P Q : Type*)
    [CommRing A] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] where
  /-- Underlying element of `Q ⊗[A] P` (ordered with `Q` on the left so `TensorProduct.leftModule`
  provides the left `Λ`-module structure). -/
  val : TensorProduct A Q P

@[ext]
theorem DiagonalTensor.ext {A Λ P Q : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] {x y : DiagonalTensor A Λ P Q} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

namespace DiagonalTensor

section BaseModule

variable (A Λ : Type*) [CommRing A] {P Q : Type*} [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q]

instance : AddCommGroup (DiagonalTensor A Λ P Q) :=
  Equiv.addCommGroup
    { toFun := DiagonalTensor.val, invFun := DiagonalTensor.mk
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

@[simp]
theorem val_zero : (0 : DiagonalTensor A Λ P Q).val = 0 := by rfl

@[simp]
theorem val_add (x y : DiagonalTensor A Λ P Q) : (x + y).val = x.val + y.val := by rfl

@[simp]
theorem val_neg (x : DiagonalTensor A Λ P Q) : (-x).val = -x.val := by rfl

@[simp]
theorem val_sub (x y : DiagonalTensor A Λ P Q) : (x - y).val = x.val - y.val := by rfl

@[simp]
theorem val_nsmul (n : ℕ) (x : DiagonalTensor A Λ P Q) : (n • x).val = n • x.val := by rfl

@[simp]
theorem val_zsmul (n : ℤ) (x : DiagonalTensor A Λ P Q) : (n • x).val = n • x.val := by rfl

/-- Pure tensor `p ⊗ₜ q` in `DiagonalTensor A Λ P Q`. -/
def tmul (p : P) (q : Q) : DiagonalTensor A Λ P Q :=
  ⟨TensorProduct.tmul A q p⟩

@[simp]
theorem val_tmul (p : P) (q : Q) : (tmul A Λ p q).val = TensorProduct.tmul A q p := by rfl

@[simp]
theorem tmul_zero (p : P) : tmul A Λ p (0 : Q) = 0 := by
  ext
  simp

@[simp]
theorem zero_tmul (q : Q) : tmul A Λ (0 : P) q = 0 := by
  ext
  simp

theorem tmul_add (p : P) (q₁ q₂ : Q) :
    tmul A Λ p (q₁ + q₂) = tmul A Λ p q₁ + tmul A Λ p q₂ := by
  ext
  simp [TensorProduct.add_tmul]

theorem add_tmul (p₁ p₂ : P) (q : Q) :
    tmul A Λ (p₁ + p₂) q = tmul A Λ p₁ q + tmul A Λ p₂ q := by
  ext
  simp [TensorProduct.tmul_add]

theorem smul_tmul_eq_tmul_smul (a : A) (p : P) (q : Q) :
    tmul A Λ (a • p) q = tmul A Λ p (a • q) := by
  ext
  exact (TensorProduct.smul_tmul a q p).symm

variable {A Λ} in
/-- Elimination principle for `DiagonalTensor A Λ P Q` by pure tensors and addition. -/
@[elab_as_elim]
theorem induction_on {motive : DiagonalTensor A Λ P Q → Prop} (x : DiagonalTensor A Λ P Q)
    (tmul : ∀ (p : P) (q : Q), motive (tmul A Λ p q))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x := by
  obtain ⟨v⟩ := x
  exact TensorProduct.inductionOn v (fun q p ↦ tmul p q) fun u w hu hw ↦ add ⟨u⟩ ⟨w⟩ hu hw

section ModuleLambda

variable [Ring Λ] [Algebra A Λ] [Module Λ Q] [IsScalarTower A Λ Q]

instance : Module Λ (DiagonalTensor A Λ P Q) :=
  AddEquiv.module Λ
    { toFun := DiagonalTensor.val, invFun := DiagonalTensor.mk
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl, map_add' := fun _ _ ↦ rfl }

/-- The tautological `Λ`-linear equivalence `DiagonalTensor A Λ P Q ≃ₗ[Λ] Q ⊗[A] P`. -/
def linearEquivTensorProduct (P Q : Type*) [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [Module Λ Q] [IsScalarTower A Λ Q] :
    DiagonalTensor A Λ P Q ≃ₗ[Λ] TensorProduct A Q P where
  toFun := DiagonalTensor.val
  invFun := DiagonalTensor.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smul_tmul (c : Λ) (p : P) (q : Q) :
    c • tmul A Λ p q = tmul A Λ p (c • q) := by
  rfl

end ModuleLambda

end BaseModule

section MonoidAction

open _root_.MonoidAlgebra

variable (A Λ M : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Monoid M]
  (P Q : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A M) P]
  [IsScalarTower A (MonoidAlgebra A M) P]
  [AddCommGroup Q] [Module A Q] [Module Λ Q] [IsScalarTower A Λ Q]
  [Module (MonoidAlgebra Λ M) Q] [IsScalarTower Λ (MonoidAlgebra Λ M) Q]

/-- Diagonal `Λ`-linear action of a monoid element `m : M` on `DiagonalTensor A Λ P Q`. -/
def diagElemEnd (m : M) : Module.End Λ (DiagonalTensor A Λ P Q) :=
  (linearEquivTensorProduct A Λ P Q).symm.toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.map (elemLinearMap Λ Q m) (elemLinearMap A P m) ∘ₗ
    (linearEquivTensorProduct A Λ P Q).toLinearMap

@[simp]
theorem diagElemEnd_tmul (m : M) (p : P) (q : Q) :
    diagElemEnd A Λ M P Q m (tmul A Λ p q) =
      tmul A Λ (single m (1 : A) • p) (single m (1 : Λ) • q) := by
  simp [diagElemEnd, linearEquivTensorProduct, tmul]

/-- The ring homomorphism `Λ[M] →+* End_ℤ(P ⊗_A Q)` combining left multiplication by `Λ` on `Q` with
the diagonal `M`-action on `P` and `Q`. -/
def monoidAlgebraActionHom :
    MonoidAlgebra Λ M →+* Module.End ℤ (DiagonalTensor A Λ P Q) :=
  liftNCRingHom
    { toFun := fun c ↦
        { toFun := fun x ↦ c • x
          map_add' := smul_add c
          map_smul' := fun n x ↦ by rw [RingHom.id_apply, smul_comm n c x] }
      map_one' := LinearMap.ext fun x ↦ one_smul Λ x
      map_mul' := fun a b ↦ LinearMap.ext fun x ↦ mul_smul a b x
      map_zero' := LinearMap.ext fun x ↦ zero_smul Λ x
      map_add' := fun a b ↦ LinearMap.ext fun x ↦ add_smul a b x }
    { toFun := fun m ↦ (diagElemEnd A Λ M P Q m).restrictScalars ℤ
      map_one' := LinearMap.ext fun x ↦ by
        have hidA : elemLinearMap A P (1 : M) = .id := LinearMap.ext fun p ↦ by simp [← one_def]
        have hidΛ : elemLinearMap Λ Q (1 : M) = .id := LinearMap.ext fun q ↦ by simp [← one_def]
        simp [diagElemEnd, hidA, hidΛ]
      map_mul' := fun m₁ m₂ ↦ LinearMap.ext fun x ↦ by
        have hmulA : elemLinearMap A P (m₁ * m₂) =
            elemLinearMap A P m₁ ∘ₗ elemLinearMap A P m₂ :=
          LinearMap.ext fun p ↦ by simp [← mul_smul, single_mul_single]
        have hmulΛ : elemLinearMap Λ Q (m₁ * m₂) =
            elemLinearMap Λ Q m₁ ∘ₗ elemLinearMap Λ Q m₂ :=
          LinearMap.ext fun q ↦ by simp [← mul_smul, single_mul_single]
        simp [diagElemEnd, hmulA, hmulΛ, TensorProduct.AlgebraTensorModule.map_comp,
          mul_apply_eq_comp] }
    fun c m ↦ show Commute _ _ from LinearMap.ext fun x ↦
      (map_smul (diagElemEnd A Λ M P Q m) c x).symm

/-- Diagonal left `Λ[M]`-module structure on `DiagonalTensor A Λ P Q`. -/
instance monoidAlgebraModule : Module (MonoidAlgebra Λ M) (DiagonalTensor A Λ P Q) :=
  Module.compHom (DiagonalTensor A Λ P Q) (monoidAlgebraActionHom A Λ M P Q)

@[simp]
theorem monoidAlgebraModule_single_smul_tmul (m : M) (c : Λ) (p : P) (q : Q) :
    (single m c : MonoidAlgebra Λ M) • tmul A Λ p q =
      tmul A Λ (single m (1 : A) • p) (single m c • q) := by
  have hact : (single m c : MonoidAlgebra Λ M) • tmul A Λ p q =
      monoidAlgebraActionHom A Λ M P Q (single m c) (tmul A Λ p q) := rfl
  rw [hact, monoidAlgebraActionHom, liftNCRingHom_single]
  simp [mul_apply_eq_comp, smul_tmul, ← single_smul_eq_smul_single_one_smul]

instance monoidAlgebraIsScalarTower :
    IsScalarTower Λ (MonoidAlgebra Λ M) (DiagonalTensor A Λ P Q) where
   smul_assoc c r x := by
    induction r using induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, add_smul, add_smul, smul_add, ha, hb]
    | single m d =>
      induction x using DiagonalTensor.induction_on with
      | tmul p q =>
        rw [smul_single, smul_eq_mul, monoidAlgebraModule_single_smul_tmul,
          monoidAlgebraModule_single_smul_tmul, smul_tmul, ← smul_eq_mul, ← smul_single,
          smul_assoc]
      | add u v hu hv => rw [smul_add, smul_add, smul_add, hu, hv]

theorem monoidAlgebraModule_comp_mapDomain {N : Type*} [Monoid N] (f : N →* M)
    [Module (MonoidAlgebra A N) P] [IsScalarTower A (MonoidAlgebra A N) P]
    [Module (MonoidAlgebra Λ N) Q] [IsScalarTower Λ (MonoidAlgebra Λ N) Q]
    (hPN : ∀ (r : MonoidAlgebra A N) (p : P), r • p = mapDomainRingHom A f r • p)
    (hQN : ∀ (r : MonoidAlgebra Λ N) (q : Q), r • q = mapDomainRingHom Λ f r • q)
    (r : MonoidAlgebra Λ N) (x : DiagonalTensor A Λ P Q) :
    r • x = mapDomainRingHom Λ f r • x := by
  induction r using induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_smul, _root_.map_add, add_smul, ha, hb]
  | single n c =>
    induction x using DiagonalTensor.induction_on with
    | tmul p q =>
      simp only [mapDomainRingHom_apply, mapDomain_single, monoidAlgebraModule_single_smul_tmul]
      rw [hPN (single n (1 : A)) p, hQN (single n c) q]
      simp
    | add u v hu hv => rw [smul_add, smul_add, hu, hv]

variable {P Q}

/-- Functoriality of `DiagonalTensor` in an `A[M]`-linear map on the left factor and a `Λ[M]`-linear
map on the right factor. -/
def map {P' Q' : Type*}
    [AddCommGroup P'] [Module A P'] [Module (MonoidAlgebra A M) P']
    [IsScalarTower A (MonoidAlgebra A M) P']
    [AddCommGroup Q'] [Module A Q'] [Module Λ Q'] [IsScalarTower A Λ Q']
    [Module (MonoidAlgebra Λ M) Q'] [IsScalarTower Λ (MonoidAlgebra Λ M) Q']
    (f : P →ₗ[MonoidAlgebra A M] P') (g : Q →ₗ[MonoidAlgebra Λ M] Q') :
    DiagonalTensor A Λ P Q →ₗ[MonoidAlgebra Λ M] DiagonalTensor A Λ P' Q' := by
  let φΛ : DiagonalTensor A Λ P Q →ₗ[Λ] DiagonalTensor A Λ P' Q' :=
    (linearEquivTensorProduct A Λ P' Q').symm.toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.map (g.restrictScalars Λ) (f.restrictScalars A) ∘ₗ
      (linearEquivTensorProduct A Λ P Q).toLinearMap
  refine
    { toFun := φΛ
      map_add' := _root_.map_add φΛ
      map_smul' := fun r x ↦ ?_ }
  rw [RingHom.id_apply]
  induction r using induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_smul, _root_.map_add, add_smul, ha, hb]
  | single m c =>
    induction x using DiagonalTensor.induction_on with
    | tmul p q =>
      have htmul : ∀ (p₀ : P) (q₀ : Q), φΛ (tmul A Λ p₀ q₀) = tmul A Λ (f p₀) (g q₀) :=
        fun _ _ ↦ rfl
      rw [monoidAlgebraModule_single_smul_tmul, htmul, htmul,
        monoidAlgebraModule_single_smul_tmul, map_smul, map_smul]
    | add u v hu hv => rw [smul_add, _root_.map_add, _root_.map_add, smul_add, hu, hv]

@[simp]
theorem map_tmul {P' Q' : Type*}
    [AddCommGroup P'] [Module A P'] [Module (MonoidAlgebra A M) P']
    [IsScalarTower A (MonoidAlgebra A M) P']
    [AddCommGroup Q'] [Module A Q'] [Module Λ Q'] [IsScalarTower A Λ Q']
    [Module (MonoidAlgebra Λ M) Q'] [IsScalarTower Λ (MonoidAlgebra Λ M) Q']
    (f : P →ₗ[MonoidAlgebra A M] P') (g : Q →ₗ[MonoidAlgebra Λ M] Q') (p : P) (q : Q) :
    map A Λ M f g (tmul A Λ p q) = tmul A Λ (f p) (g q) := by
  simp [map, linearEquivTensorProduct, tmul]

@[simp]
theorem map_id :
    map A Λ M (LinearMap.id : P →ₗ[MonoidAlgebra A M] P)
      (LinearMap.id : Q →ₗ[MonoidAlgebra Λ M] Q) = .id := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using DiagonalTensor.induction_on with
  | tmul p q => simp
  | add u v hu hv => simp only [_root_.map_add, LinearMap.id_apply] at hu hv ⊢; rw [hu, hv]

theorem map_comp {P' P'' Q' Q'' : Type*}
    [AddCommGroup P'] [Module A P'] [Module (MonoidAlgebra A M) P']
    [IsScalarTower A (MonoidAlgebra A M) P']
    [AddCommGroup P''] [Module A P''] [Module (MonoidAlgebra A M) P'']
    [IsScalarTower A (MonoidAlgebra A M) P'']
    [AddCommGroup Q'] [Module A Q'] [Module Λ Q'] [IsScalarTower A Λ Q']
    [Module (MonoidAlgebra Λ M) Q'] [IsScalarTower Λ (MonoidAlgebra Λ M) Q']
    [AddCommGroup Q''] [Module A Q''] [Module Λ Q''] [IsScalarTower A Λ Q'']
    [Module (MonoidAlgebra Λ M) Q''] [IsScalarTower Λ (MonoidAlgebra Λ M) Q'']
    (f₂ : P' →ₗ[MonoidAlgebra A M] P'') (f₁ : P →ₗ[MonoidAlgebra A M] P')
    (g₂ : Q' →ₗ[MonoidAlgebra Λ M] Q'') (g₁ : Q →ₗ[MonoidAlgebra Λ M] Q') :
    map A Λ M (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) = map A Λ M f₂ g₂ ∘ₗ map A Λ M f₁ g₁ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using DiagonalTensor.induction_on with
  | tmul p q => simp
  | add u v hu hv => simp only [_root_.map_add, LinearMap.comp_apply] at hu hv ⊢; rw [hu, hv]

theorem map_add_left {P' : Type*}
    [AddCommGroup P'] [Module A P'] [Module (MonoidAlgebra A M) P']
    [IsScalarTower A (MonoidAlgebra A M) P']
    (f₁ f₂ : P →ₗ[MonoidAlgebra A M] P') (g : Q →ₗ[MonoidAlgebra Λ M] Q) :
    map A Λ M (f₁ + f₂) g = map A Λ M f₁ g + map A Λ M f₂ g := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using DiagonalTensor.induction_on with
  | tmul p q => simp [add_tmul]
  | add u v hu hv => simp only [_root_.map_add, LinearMap.add_apply] at hu hv ⊢; rw [hu, hv]

@[simp]
theorem map_zero_left {P' : Type*}
    [AddCommGroup P'] [Module A P'] [Module (MonoidAlgebra A M) P']
    [IsScalarTower A (MonoidAlgebra A M) P']
    (g : Q →ₗ[MonoidAlgebra Λ M] Q) :
    map A Λ M (0 : P →ₗ[MonoidAlgebra A M] P') g = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using DiagonalTensor.induction_on with
  | tmul p q => simp
  | add u v hu hv =>
    simp only [_root_.map_add, LinearMap.zero_apply] at hu hv ⊢
    rw [hu, hv, add_zero]

theorem map_sum_left {ι P' : Type*} (s : Finset ι)
    [AddCommGroup P'] [Module A P'] [Module (MonoidAlgebra A M) P']
    [IsScalarTower A (MonoidAlgebra A M) P']
    (f : ι → P →ₗ[MonoidAlgebra A M] P') (g : Q →ₗ[MonoidAlgebra Λ M] Q) :
    map A Λ M (∑ i ∈ s, f i) g = ∑ i ∈ s, map A Λ M (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, map_add_left, ih, Finset.sum_insert hi]

end MonoidAction

section GroupAction

open _root_.MonoidAlgebra

variable (A Λ G : Type*) [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
  (Q : Type*) [AddCommGroup Q] [Module A Q] [Module Λ Q] [IsScalarTower A Λ Q]
  [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]

/-- **The shearing isomorphism** `Λ[G] ⊗_Λ Q ≃ₗ[Λ[G]] A[G] ⊗_A Q` sending `single g c ⊗ q` to
`single g 1 ⊗ (single g c • q)`, with inverse sending `single g a ⊗ q` to
`single g (algebraMap A Λ a) ⊗ (single g⁻¹ 1 • q)`. -/
def shearingEquiv :
    BalancedExtension (singleOneRingHom : Λ →+* MonoidAlgebra Λ G) Q ≃ₗ[MonoidAlgebra Λ G]
      DiagonalTensor A Λ (MonoidAlgebra A G) Q := by
  let φ : Λ →+* MonoidAlgebra Λ G := singleOneRingHom
  have hφ : ∀ c : Λ, φ c = single (1 : G) c := fun _ ↦ rfl
  let g_fwd : Q →ₛₗ[φ] DiagonalTensor A Λ (MonoidAlgebra A G) Q :=
    { toFun := fun q ↦ tmul A Λ 1 q
      map_add' := tmul_add A Λ 1
      map_smul' := fun c q ↦ by
        rw [hφ, monoidAlgebraModule_single_smul_tmul]
        have h1 : (single (1 : G) (1 : A) : MonoidAlgebra A G) • (1 : MonoidAlgebra A G) = 1 := by
          rw [← one_def, one_smul]
        have hc : (single (1 : G) c : MonoidAlgebra Λ G) • q = c • q := by
          rw [single_smul_eq_smul_single_one_smul, ← one_def, one_smul]
        rw [h1, hc] }
  let fwd : BalancedExtension φ Q →ₗ[MonoidAlgebra Λ G]
      DiagonalTensor A Λ (MonoidAlgebra A G) Q := BalancedExtension.lift g_fwd
  letI modA : Module A (BalancedExtension φ Q) :=
    Module.compHom (BalancedExtension φ Q) (φ.comp (algebraMap A Λ))
  have hmodA : ∀ (a : A) (x : BalancedExtension φ Q),
      a • x = (single (1 : G) (algebraMap A Λ a) : MonoidAlgebra Λ G) • x :=
    fun _ _ ↦ rfl
  let ψ : G → Q →ₗ[A] BalancedExtension φ Q := fun g ↦
    { toFun := fun q ↦ BalancedExtension.tmul φ (single g 1) (single g⁻¹ (1 : Λ) • q)
      map_add' := fun q₁ q₂ ↦ by rw [smul_add, BalancedExtension.tmul_add]
      map_smul' := fun a q ↦ by
        rw [RingHom.id_apply, hmodA, algebra_compatible_smul Λ a q, ← elemLinearMap_apply Λ,
          map_smul, elemLinearMap_apply, BalancedExtension.tmul_smul,
          BalancedExtension.smul_tmul, hφ]
        simp [single_mul_single] }
  let bil : Q →ₗ[A] MonoidAlgebra A G →ₗ[A] BalancedExtension φ Q :=
    { toFun := fun q ↦
        (Finsupp.linearCombination A (fun g ↦ ψ g q)).comp (coeffLinearEquiv (R := A)).toLinearMap
      map_add' := fun q₁ q₂ ↦
        lhom_ext' fun g ↦ LinearMap.ext fun a ↦ by
          simp [map_add, smul_add]
      map_smul' := fun c q ↦
        lhom_ext' fun g ↦ LinearMap.ext fun a ↦ by
          simp [map_smul, smul_comm a c] }
  let invA : TensorProduct A Q (MonoidAlgebra A G) →ₗ[A] BalancedExtension φ Q :=
    TensorProduct.lift bil
  have hinv_single : ∀ (g : G) (a : A) (q : Q),
      invA (TensorProduct.tmul A q (single g a)) =
        BalancedExtension.tmul φ (single g (algebraMap A Λ a)) (single g⁻¹ (1 : Λ) • q) := by
    intro g a q
    simp [invA, bil, hmodA, ψ, single_mul_single]
  let inv : DiagonalTensor A Λ (MonoidAlgebra A G) Q →ₗ[MonoidAlgebra Λ G]
      BalancedExtension φ Q :=
    { toFun := fun x ↦ invA x.val
      map_add' := fun x y ↦ _root_.map_add invA x.val y.val
      map_smul' := fun r x ↦ by
        rw [RingHom.id_apply]
        induction r using induction_linear with
        | zero => simp
        | add u v hu hv => rw [add_smul, val_add, _root_.map_add, add_smul, hu, hv]
        | single h c =>
          induction x using DiagonalTensor.induction_on with
          | tmul p q =>
            induction p using induction_linear with
            | zero =>
              have hz1 : tmul A Λ (0 : MonoidAlgebra A G) q = 0 := zero_tmul A Λ q
              rw [hz1, smul_zero, val_zero, map_zero, smul_zero]
            | add p₁ p₂ hp₁ hp₂ =>
              rw [add_tmul, smul_add, val_add, _root_.map_add, val_add, _root_.map_add,
                smul_add, hp₁, hp₂]
            | single g a =>
              rw [monoidAlgebraModule_single_smul_tmul, smul_eq_mul, single_mul_single, one_mul,
                val_tmul, val_tmul, hinv_single, hinv_single, ← mul_smul, single_mul_single,
                one_mul, mul_inv_rev, inv_mul_cancel_right,
                single_smul_eq_smul_single_one_smul g⁻¹ c q, BalancedExtension.tmul_smul,
                BalancedExtension.smul_tmul, hφ]
              simp [single_mul_single, Algebra.commutes a c]
          | add u v hu hv =>
            rw [smul_add, val_add, _root_.map_add, val_add, _root_.map_add, smul_add, hu, hv] }
  refine LinearEquiv.ofLinearMap fwd inv ?_ ?_
  · refine LinearMap.ext fun x ↦ ?_
    induction x using DiagonalTensor.induction_on with
    | tmul p q =>
      induction p using induction_linear with
      | zero => simp
      | add p₁ p₂ hp₁ hp₂ =>
        rw [add_tmul]
        simp only [_root_.map_add, LinearMap.id_apply] at hp₁ hp₂ ⊢
        rw [hp₁, hp₂]
      | single g a =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, inv, LinearMap.coe_mk, AddHom.coe_mk,
          val_tmul, hinv_single, fwd, BalancedExtension.lift_tmul, g_fwd,
          monoidAlgebraModule_single_smul_tmul, smul_eq_mul, mul_one, ← mul_smul,
          single_mul_single, mul_inv_cancel, mul_one]
        have h1a : (single (1 : G) (algebraMap A Λ a) : MonoidAlgebra Λ G) • q = a • q := by
          rw [single_smul_eq_smul_single_one_smul, ← one_def, one_smul,
            algebra_compatible_smul Λ a q]
        rw [h1a, ← smul_tmul_eq_tmul_smul, smul_single, smul_eq_mul, mul_one]
    | add u v hu hv => simp only [_root_.map_add, LinearMap.id_apply] at hu hv ⊢; rw [hu, hv]
  · refine BalancedExtension.hom_ext fun q ↦ ?_
    change inv (fwd (BalancedExtension.tmul φ 1 q)) = BalancedExtension.tmul φ 1 q
    have hfwd : fwd (BalancedExtension.tmul φ 1 q) = tmul A Λ (single 1 1) q := by
      rw [BalancedExtension.lift_tmul, one_smul]
      change tmul A Λ 1 q = tmul A Λ (single 1 1) q
      rw [one_def]
    have hq1 : (single (1 : G)⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • q = q := by
      rw [inv_one, ← one_def, one_smul]
    rw [hfwd]
    change invA (TensorProduct.tmul A q (single 1 1)) = BalancedExtension.tmul φ 1 q
    rw [hinv_single, _root_.map_one, ← one_def, hq1]

@[simp]
theorem shearingEquiv_tmul_one (q : Q) :
    shearingEquiv A Λ G Q (BalancedExtension.tmul _ 1 q) = tmul A Λ 1 q := by
  simp [shearingEquiv]

@[simp]
theorem shearingEquiv_symm_tmul_single (g : G) (a : A) (q : Q) :
    (shearingEquiv A Λ G Q).symm (tmul A Λ (single g a) q) =
      BalancedExtension.tmul (singleOneRingHom : Λ →+* MonoidAlgebra Λ G)
        (single g (algebraMap A Λ a)) (single g⁻¹ (1 : Λ) • q) := by
  apply (shearingEquiv A Λ G Q).injective
  rw [LinearEquiv.apply_symm_apply,
    BalancedExtension.tmul_eq_smul_one_tmul (f := (singleOneRingHom : Λ →+* MonoidAlgebra Λ G)),
    (shearingEquiv A Λ G Q).map_smul, shearingEquiv_tmul_one,
    monoidAlgebraModule_single_smul_tmul, smul_eq_mul, mul_one, ← mul_smul, single_mul_single,
    mul_inv_cancel, mul_one]
  have h1a : (single (1 : G) (algebraMap A Λ a) : MonoidAlgebra Λ G) • q = a • q := by
    rw [single_smul_eq_smul_single_one_smul, ← one_def, one_smul,
      algebra_compatible_smul Λ a q]
  rw [h1a, ← smul_tmul_eq_tmul_smul, smul_single, smul_eq_mul, mul_one]

section Retract

variable {P : Type*} [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A G) P]
  [IsScalarTower A (MonoidAlgebra A G) P]

/-- Retraction of `DiagonalTensor A Λ P Q` onto `Fin r → Fin s → Λ[G]` induced by retractions of `P`
over `A[G]` and `Q` over `Λ`. -/
private def retractToFree {r s : ℕ}
    (i_P : P →ₗ[MonoidAlgebra A G] Fin r → MonoidAlgebra A G)
    (π_P : (Fin r → MonoidAlgebra A G) →ₗ[MonoidAlgebra A G] P)
    (hπi_P : π_P ∘ₗ i_P = .id)
    (i_Q : Q →ₗ[Λ] Fin s → Λ)
    (π_Q : (Fin s → Λ) →ₗ[Λ] Q)
    (hπi_Q : π_Q ∘ₗ i_Q = .id) :
    { p : (DiagonalTensor A Λ P Q →ₗ[MonoidAlgebra Λ G] Fin r → Fin s → MonoidAlgebra Λ G) ×
        ((Fin r → Fin s → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] DiagonalTensor A Λ P Q) //
      p.2 ∘ₗ p.1 = .id } := by
  classical
  let φ : Λ →+* MonoidAlgebra Λ G := singleOneRingHom
  let eS := shearingEquiv A Λ G Q
  let eQ := BalancedExtension.piScalarRight φ (Fin s)
  let iQ' : BalancedExtension φ Q →ₗ[MonoidAlgebra Λ G] Fin s → MonoidAlgebra Λ G :=
    eQ.toLinearMap ∘ₗ BalancedExtension.map φ i_Q
  let πQ' : (Fin s → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] BalancedExtension φ Q :=
    BalancedExtension.map φ π_Q ∘ₗ eQ.symm.toLinearMap
  have hπi_Q' : πQ' ∘ₗ iQ' = .id := by
    have hassoc : πQ' ∘ₗ iQ' = BalancedExtension.map φ π_Q ∘ₗ
        (eQ.symm.toLinearMap ∘ₗ eQ.toLinearMap) ∘ₗ BalancedExtension.map φ i_Q := by
      simp [πQ', iQ', LinearMap.comp_assoc]
    rw [hassoc, eQ.symm_comp, LinearMap.id_comp, ← BalancedExtension.map_comp, hπi_Q,
      BalancedExtension.map_id]
  let i₁ : DiagonalTensor A Λ P Q →ₗ[MonoidAlgebra Λ G]
      Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q :=
    LinearMap.pi fun k ↦
      DiagonalTensor.map A Λ G ((LinearMap.proj k).comp i_P) LinearMap.id
  let π₁ : (Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q) →ₗ[MonoidAlgebra Λ G]
      DiagonalTensor A Λ P Q :=
    ∑ k : Fin r,
      (DiagonalTensor.map A Λ G
        (π_P.comp (LinearMap.single (MonoidAlgebra A G) (fun _ : Fin r ↦ MonoidAlgebra A G) k))
        LinearMap.id).comp (LinearMap.proj k)
  have hπ₁i₁ : π₁ ∘ₗ i₁ = .id := by
    have hsum_comp : π₁ ∘ₗ i₁ =
        ∑ k : Fin r,
          ((DiagonalTensor.map A Λ G
            (π_P.comp (LinearMap.single (MonoidAlgebra A G)
              (fun _ : Fin r ↦ MonoidAlgebra A G) k))
            LinearMap.id).comp (LinearMap.proj k)).comp i₁ :=
      LinearMap.ext fun x ↦ by simp [π₁]
    have hcomp : π₁ ∘ₗ i₁ =
        DiagonalTensor.map A Λ G
          (∑ k : Fin r,
            (π_P.comp (LinearMap.single (MonoidAlgebra A G)
              (fun _ : Fin r ↦ MonoidAlgebra A G) k)).comp ((LinearMap.proj k).comp i_P))
          LinearMap.id := by
      rw [hsum_comp, DiagonalTensor.map_sum_left]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hproj : (LinearMap.proj k).comp i₁ =
          DiagonalTensor.map A Λ G ((LinearMap.proj k).comp i_P) LinearMap.id := rfl
      rw [LinearMap.comp_assoc, hproj, ← DiagonalTensor.map_comp, LinearMap.id_comp]
    have hsum_P : (∑ k : Fin r,
        (π_P.comp (LinearMap.single (MonoidAlgebra A G)
          (fun _ : Fin r ↦ MonoidAlgebra A G) k)).comp ((LinearMap.proj k).comp i_P)) = .id := by
      refine LinearMap.ext fun p ↦ ?_
      have hexp : (∑ k : Fin r,
          LinearMap.single (MonoidAlgebra A G) (fun _ : Fin r ↦ MonoidAlgebra A G) k (i_P p k)) =
          i_P p := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← map_sum, hexp]
      exact LinearMap.congr_fun hπi_P p
    rw [hcomp, hsum_P, DiagonalTensor.map_id]
  let i₂ : (Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q) →ₗ[MonoidAlgebra Λ G]
      Fin r → Fin s → MonoidAlgebra Λ G :=
    LinearMap.pi fun k ↦ iQ' ∘ₗ eS.symm.toLinearMap ∘ₗ LinearMap.proj k
  let π₂ : (Fin r → Fin s → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G]
      Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q :=
    LinearMap.pi fun k ↦ eS.toLinearMap ∘ₗ πQ' ∘ₗ LinearMap.proj k
  have hπ₂i₂ : π₂ ∘ₗ i₂ = .id := by
    refine LinearMap.ext fun v ↦ ?_
    funext k
    have hstep : eS (πQ' (iQ' (eS.symm (v k)))) = v k := by
      have hq : πQ' (iQ' (eS.symm (v k))) = eS.symm (v k) :=
        LinearMap.congr_fun hπi_Q' (eS.symm (v k))
      rw [hq, eS.apply_symm_apply]
    exact hstep
  refine ⟨(i₂ ∘ₗ i₁, π₁ ∘ₗ π₂), ?_⟩
  calc
    (π₁ ∘ₗ π₂) ∘ₗ (i₂ ∘ₗ i₁) = π₁ ∘ₗ (π₂ ∘ₗ i₂) ∘ₗ i₁ := by simp [LinearMap.comp_assoc]
    _ = .id := by rw [hπ₂i₂, LinearMap.id_comp, hπ₁i₁]

/-- **Diagonal tensor finiteness** (Stacks Project, Section 64.15, Lemma 64.15.6, finiteness part):
if `P` is finite projective over `A[G]` and `Q` is finite projective over `Λ`, then `P ⊗_A Q` is a
finitely generated left `Λ[G]`-module. -/
instance monoidAlgebraFinite [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] [Module.Finite Λ Q] [Module.Projective Λ Q] :
    Module.Finite (MonoidAlgebra Λ G) (DiagonalTensor A Λ P Q) := by
  obtain ⟨r, π_P, i_P, -, -, hπi_P⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra A G) P
  obtain ⟨s, π_Q, i_Q, -, -, hπi_Q⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ Q
  obtain ⟨⟨i_tot, π_tot⟩, hπi_tot⟩ := retractToFree A Λ G Q i_P π_P hπi_P i_Q π_Q hπi_Q
  let bRS : Module.Basis ((_ : Fin r) × Fin s) (MonoidAlgebra Λ G)
      (Fin r → Fin s → MonoidAlgebra Λ G) :=
    Pi.basis fun _ ↦ Pi.basisFun (MonoidAlgebra Λ G) (Fin s)
  have : Module.Finite (MonoidAlgebra Λ G) (Fin r → Fin s → MonoidAlgebra Λ G) :=
    Module.Finite.of_basis bRS
  exact Module.Finite.of_surjective π_tot
    (Function.RightInverse.surjective (LinearMap.congr_fun hπi_tot))

/-- **Diagonal tensor projectivity** (Stacks Project, Section 64.15, Lemma 64.15.6): if `P` is
finite projective over `A[G]` and `Q` is finite projective over `Λ` (without assuming `Q` is
projective over `A`), then `P ⊗_A Q` is projective as a left `Λ[G]`-module. -/
instance monoidAlgebraProjective [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] [Module.Finite Λ Q] [Module.Projective Λ Q] :
    Module.Projective (MonoidAlgebra Λ G) (DiagonalTensor A Λ P Q) := by
  obtain ⟨r, π_P, i_P, -, -, hπi_P⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra A G) P
  obtain ⟨s, π_Q, i_Q, -, -, hπi_Q⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ Q
  obtain ⟨⟨i_tot, π_tot⟩, hπi_tot⟩ := retractToFree A Λ G Q i_P π_P hπi_P i_Q π_Q hπi_Q
  let bRS : Module.Basis ((_ : Fin r) × Fin s) (MonoidAlgebra Λ G)
      (Fin r → Fin s → MonoidAlgebra Λ G) :=
    Pi.basis fun _ ↦ Pi.basisFun (MonoidAlgebra Λ G) (Fin s)
  have : Module.Projective (MonoidAlgebra Λ G) (Fin r → Fin s → MonoidAlgebra Λ G) :=
    Module.Projective.of_basis bRS
  exact Module.Projective.of_split i_tot π_tot hπi_tot

end Retract

end GroupAction

end DiagonalTensor

end TauCeti

/-! ### Group-ring Hattori–Stallings trace of a diagonal tensor product (Lemma 64.15.7) -/

namespace LinearMap

open TauCeti

/-- **Group-ring Hattori–Stallings trace of a diagonal tensor product** (Stacks Project,
Section 64.15, Lemma 64.15.7). Let `A` be a commutative ring, `Λ` an `A`-algebra, `P` a finite
projective `A[G]`-module, and `Q` a `Λ[G]`-module that is finite projective over `Λ`. For any
`A[G]`-linear endomorphism `u_P` of `P` and `Λ[G]`-linear endomorphism `u_Q` of `Q`,
`Tr_Λ^G(u_P ⊗ u_Q, P ⊗_A Q) = Tr_A^G(u_P, P) • Tr_Λ(u_Q, Q)` in `Λ / [Λ, Λ]`. -/
theorem hattoriStallingsGroupTrace_diagonalTensor_map
    {A Λ G P Q : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A G) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    [AddCommGroup Q] [Module A Q] [Module Λ Q] [IsScalarTower A Λ Q]
    [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [Module.Finite Λ Q] [Module.Projective Λ Q]
    (u_P : Module.End (MonoidAlgebra A G) P) (u_Q : Module.End (MonoidAlgebra Λ G) Q) :
    hattoriStallingsGroupTrace Λ G (DiagonalTensor A Λ P Q) (DiagonalTensor.map A Λ G u_P u_Q) =
      cyclicQuotientCentralSMul A Λ (projectiveGroupTrace A G P u_P)
        (hattoriStallingsTrace Λ Q (u_Q.restrictScalars Λ)) := by
  classical
  obtain ⟨r, π_P, i_P, -, -, hπi_P⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra A G) P
  obtain ⟨s, π_Q, i_Q, -, -, hπi_Q⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ Q
  let φ : Λ →+* MonoidAlgebra Λ G := MonoidAlgebra.singleOneRingHom
  let eS := DiagonalTensor.shearingEquiv A Λ G Q
  let eQ := BalancedExtension.piScalarRight φ (Fin s)
  let iQ' : BalancedExtension φ Q →ₗ[MonoidAlgebra Λ G] Fin s → MonoidAlgebra Λ G :=
    eQ.toLinearMap ∘ₗ BalancedExtension.map φ i_Q
  let πQ' : (Fin s → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] BalancedExtension φ Q :=
    BalancedExtension.map φ π_Q ∘ₗ eQ.symm.toLinearMap
  have hπi_Q' : πQ' ∘ₗ iQ' = .id := by
    have hassoc : πQ' ∘ₗ iQ' = BalancedExtension.map φ π_Q ∘ₗ
        (eQ.symm.toLinearMap ∘ₗ eQ.toLinearMap) ∘ₗ BalancedExtension.map φ i_Q := by
      simp [πQ', iQ', LinearMap.comp_assoc]
    rw [hassoc, eQ.symm_comp, LinearMap.id_comp, ← BalancedExtension.map_comp, hπi_Q,
      BalancedExtension.map_id]
  let i₁ : DiagonalTensor A Λ P Q →ₗ[MonoidAlgebra Λ G]
      Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q :=
    LinearMap.pi fun k ↦
      DiagonalTensor.map A Λ G ((LinearMap.proj k).comp i_P) LinearMap.id
  let π₁ : (Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q) →ₗ[MonoidAlgebra Λ G]
      DiagonalTensor A Λ P Q :=
    ∑ k : Fin r,
      (DiagonalTensor.map A Λ G
        (π_P.comp (LinearMap.single (MonoidAlgebra A G) (fun _ : Fin r ↦ MonoidAlgebra A G) k))
        LinearMap.id).comp (LinearMap.proj k)
  have hπ₁i₁ : π₁ ∘ₗ i₁ = .id := by
    have hsum_comp : π₁ ∘ₗ i₁ =
        ∑ k : Fin r,
          ((DiagonalTensor.map A Λ G
            (π_P.comp (LinearMap.single (MonoidAlgebra A G)
              (fun _ : Fin r ↦ MonoidAlgebra A G) k))
            LinearMap.id).comp (LinearMap.proj k)).comp i₁ :=
      LinearMap.ext fun x ↦ by simp [π₁]
    have hcomp : π₁ ∘ₗ i₁ =
        DiagonalTensor.map A Λ G
          (∑ k : Fin r,
            (π_P.comp (LinearMap.single (MonoidAlgebra A G)
              (fun _ : Fin r ↦ MonoidAlgebra A G) k)).comp ((LinearMap.proj k).comp i_P))
          LinearMap.id := by
      rw [hsum_comp, DiagonalTensor.map_sum_left]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hproj : (LinearMap.proj k).comp i₁ =
          DiagonalTensor.map A Λ G ((LinearMap.proj k).comp i_P) LinearMap.id := rfl
      rw [LinearMap.comp_assoc, hproj, ← DiagonalTensor.map_comp, LinearMap.id_comp]
    have hsum_P : (∑ k : Fin r,
        (π_P.comp (LinearMap.single (MonoidAlgebra A G)
          (fun _ : Fin r ↦ MonoidAlgebra A G) k)).comp ((LinearMap.proj k).comp i_P)) = .id := by
      refine LinearMap.ext fun p ↦ ?_
      have hexp : (∑ k : Fin r,
          LinearMap.single (MonoidAlgebra A G) (fun _ : Fin r ↦ MonoidAlgebra A G) k (i_P p k)) =
          i_P p := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← map_sum, hexp]
      exact LinearMap.congr_fun hπi_P p
    rw [hcomp, hsum_P, DiagonalTensor.map_id]
  let i₂ : (Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q) →ₗ[MonoidAlgebra Λ G]
      Fin r → Fin s → MonoidAlgebra Λ G :=
    LinearMap.pi fun k ↦ iQ' ∘ₗ eS.symm.toLinearMap ∘ₗ LinearMap.proj k
  let π₂ : (Fin r → Fin s → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G]
      Fin r → DiagonalTensor A Λ (MonoidAlgebra A G) Q :=
    LinearMap.pi fun k ↦ eS.toLinearMap ∘ₗ πQ' ∘ₗ LinearMap.proj k
  have hπ₂i₂ : π₂ ∘ₗ i₂ = .id := by
    refine LinearMap.ext fun v ↦ ?_
    funext k
    have hq : πQ' (iQ' (eS.symm (v k))) = eS.symm (v k) :=
      LinearMap.congr_fun hπi_Q' (eS.symm (v k))
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    change eS (πQ' (iQ' (eS.symm (v k)))) = v k
    rw [hq, eS.apply_symm_apply]
  let i_tot := i₂ ∘ₗ i₁
  let π_tot := π₁ ∘ₗ π₂
  have hπi_tot : π_tot ∘ₗ i_tot = .id := by
    calc
      (π₁ ∘ₗ π₂) ∘ₗ (i₂ ∘ₗ i₁) = π₁ ∘ₗ (π₂ ∘ₗ i₂) ∘ₗ i₁ := by simp [LinearMap.comp_assoc]
      _ = .id := by rw [hπ₂i₂, LinearMap.id_comp, hπ₁i₁]
  let bRS : Module.Basis ((_ : Fin r) × Fin s) (MonoidAlgebra Λ G)
      (Fin r → Fin s → MonoidAlgebra Λ G) :=
    Pi.basis fun _ ↦ Pi.basisFun (MonoidAlgebra Λ G) (Fin s)
  -- Express all three traces on the chosen retracts.
  have hLHS : hattoriStallingsGroupTrace Λ G (DiagonalTensor A Λ P Q)
      (DiagonalTensor.map A Λ G u_P u_Q) =
      (commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin r, ∑ l : Fin s,
          ((i_tot ∘ₗ DiagonalTensor.map A Λ G u_P u_Q ∘ₗ π_tot) (bRS ⟨k, l⟩) k l).coeff 1) := by
    rw [hattoriStallingsGroupTrace_apply, hattoriStallingsTrace_eq_of_retract bRS i_tot π_tot
      hπi_tot, Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ]
    congr 1
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    simp [bRS]
  have hRHS_P : projectiveGroupTrace A G P u_P =
      ∑ k : Fin r, (i_P (u_P (π_P (Pi.single k 1))) k).coeff 1 := by
    rw [projectiveGroupTrace_apply, hattoriStallingsGroupTrace_apply,
      hattoriStallingsTrace_eq_of_retract (Pi.basisFun (MonoidAlgebra A G) (Fin r)) i_P π_P hπi_P,
      Module.Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ,
      cyclicQuotientEquivOfCommRing_mkQ, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp
  have hRHS_Q : hattoriStallingsTrace Λ Q (u_Q.restrictScalars Λ) =
      (commutatorSubmodule ℤ Λ).mkQ
        (∑ l : Fin s, i_Q (u_Q (π_Q (Pi.single l 1))) l) := by
    rw [hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin s)) i_Q π_Q hπi_Q,
      Module.Basis.hattoriStallingsTrace_apply]
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp
  rw [hLHS, hRHS_P, hRHS_Q, cyclicQuotientCentralSMul_mkQ]
  congr 1
  -- Evaluate the `(k, l)` diagonal entry at `1 : G`.
  have hentry : ∀ (k : Fin r) (l : Fin s),
      ((i_tot ∘ₗ DiagonalTensor.map A Λ G u_P u_Q ∘ₗ π_tot) (bRS ⟨k, l⟩) k l).coeff 1 =
        algebraMap A Λ ((i_P (u_P (π_P (Pi.single k 1))) k).coeff 1) *
          i_Q (u_Q (π_Q (Pi.single l 1))) l := by
    intro k l
    let el : Fin s → MonoidAlgebra Λ G := Pi.single l 1
    have hb : bRS ⟨k, l⟩ = Pi.single k el := by
      funext j m
      by_cases hjk : j = k
      · subst hjk; simp [bRS, el]
      · simp [bRS, Pi.single_eq_of_ne hjk]
    have heQ_symm : eQ.symm el =
        BalancedExtension.tmul φ 1 (Pi.single l (1 : Λ)) := by
      rw [BalancedExtension.piScalarRight_symm_apply,
        Finset.sum_eq_single l (fun m _ hml ↦ by simp [el, Pi.single_eq_of_ne hml]) (by simp)]
      simp [el]
    have hπ₂_apply : π₂ (bRS ⟨k, l⟩) =
        Pi.single k (DiagonalTensor.tmul A Λ (1 : MonoidAlgebra A G) (π_Q (Pi.single l 1))) := by
      rw [hb]
      funext j
      by_cases hjk : j = k
      · subst hjk
        simp [π₂, πQ', heQ_symm, eS, φ]
      · have h0 : Pi.single (M := fun _ : Fin r ↦ Fin s → MonoidAlgebra Λ G) k el j = 0 := by
          simp [Pi.single_eq_of_ne hjk]
        change (eS.toLinearMap ∘ₗ πQ')
          (Pi.single (M := fun _ : Fin r ↦ Fin s → MonoidAlgebra Λ G) k el j) = _
        rw [h0, map_zero, Pi.single_eq_of_ne hjk]
    have hπ₁_apply : π₁ (π₂ (bRS ⟨k, l⟩)) =
        DiagonalTensor.tmul A Λ (π_P (Pi.single k 1)) (π_Q (Pi.single l 1)) := by
      rw [hπ₂_apply]
      simp only [π₁, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single k
        (fun j _ hjk ↦ by rw [Pi.single_eq_of_ne hjk, map_zero]) (by simp)]
      simp
    let x_k : MonoidAlgebra A G := i_P (u_P (π_P (Pi.single k 1))) k
    let q_l : Q := u_Q (π_Q (Pi.single l 1))
    have hi₁_k : i₁ (DiagonalTensor.map A Λ G u_P u_Q (π_tot (bRS ⟨k, l⟩))) k =
        DiagonalTensor.tmul A Λ x_k q_l := by
      simp [π_tot, hπ₁_apply, i₁, x_k, q_l]
    have hx_expand : DiagonalTensor.tmul A Λ x_k q_l =
        x_k.coeff.sum fun g a ↦ DiagonalTensor.tmul A Λ (MonoidAlgebra.single g a) q_l := by
      conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x_k]
      rw [Finsupp.sum]
      let f_tmul : MonoidAlgebra A G →+ DiagonalTensor A Λ (MonoidAlgebra A G) Q :=
        { toFun := fun p ↦ DiagonalTensor.tmul A Λ p q_l
          map_zero' := DiagonalTensor.zero_tmul A Λ q_l
          map_add' := fun a b ↦ DiagonalTensor.add_tmul A Λ a b q_l }
      exact map_sum f_tmul _ _
    have hiQ'_single : ∀ (g : G) (a : A),
        iQ' (eS.symm (DiagonalTensor.tmul A Λ (MonoidAlgebra.single g a) q_l)) l =
          MonoidAlgebra.single g
            (algebraMap A Λ a * i_Q (MonoidAlgebra.single g⁻¹ (1 : Λ) • q_l) l) := by
      intro g a
      have hφ_apply : ∀ c : Λ, φ c = MonoidAlgebra.single (1 : G) c := fun _ ↦ rfl
      simp [iQ', eQ, eS, φ, hφ_apply, MonoidAlgebra.single_mul_single]
    have hval : (i_tot ∘ₗ DiagonalTensor.map A Λ G u_P u_Q ∘ₗ π_tot) (bRS ⟨k, l⟩) k l =
        x_k.coeff.sum fun g a ↦
          MonoidAlgebra.single g
            (algebraMap A Λ a * i_Q (MonoidAlgebra.single g⁻¹ (1 : Λ) • q_l) l) := by
      change iQ' (eS.symm (i₁ (DiagonalTensor.map A Λ G u_P u_Q (π_tot (bRS ⟨k, l⟩))) k)) l = _
      rw [hi₁_k, hx_expand]
      simp only [Finsupp.sum, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ ↦ hiQ'_single g (x_k.coeff g)
    rw [hval, Finsupp.sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    by_cases hmem : (1 : G) ∈ x_k.coeff.support
    · rw [Finset.sum_eq_single (1 : G)
        (fun g _ hg1 ↦ by
          rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
          simp only [hg1, ↓reduceIte])
        (fun h1 ↦ absurd hmem h1)]
      have hq1 : (MonoidAlgebra.single (1 : G) (1 : Λ) : MonoidAlgebra Λ G) • q_l = q_l := by
        rw [← MonoidAlgebra.one_def, one_smul]
      rw [inv_one, hq1, MonoidAlgebra.coeff_single, Finsupp.single_apply]
      simp only [↓reduceIte]
      rfl
    · rw [Finset.sum_eq_zero fun g hg ↦ by
        have hg1 : g ≠ 1 := fun h ↦ hmem (h ▸ hg)
        rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        simp only [hg1, ↓reduceIte]]
      have hc0 : x_k.coeff 1 = 0 := Finsupp.notMem_support_iff.1 hmem
      change 0 = algebraMap A Λ (x_k.coeff 1) * i_Q q_l l
      rw [hc0, map_zero, zero_mul]
  simp_rw [hentry]
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.mul_sum]

end LinearMap

/-! ### Monoid-extension corollaries for diagonal tensor products (Lemma 64.15.8) -/

namespace TauCeti.MonoidExtension

open _root_.MonoidAlgebra

section DiagonalTensor

variable (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ]
  {G Γtilde : Type*} [Group G] [Group Γtilde]
  (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (hker : ι.range = deg.ker)

/-- **`G`-conjugation invariance of `Tr_Λ(γ, Q)`.** For a `Λ[Γ]`-module `Q` finite projective over
`Λ`, conjugating `γ ∈ Γ` by any `k ∈ G` conjugates `elemLinearMap Λ Q γ` by the `Λ`-linear
automorphism `single k 1 • ·`, hence preserves `hattoriStallingsTrace`. -/
theorem hattoriStallingsTrace_elemLinearMap_conjNonneg
    {Q : Type*} [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [Module.Finite Λ Q] [Module.Projective Λ Q]
    (hQG : ∀ (r : MonoidAlgebra Λ G) (q : Q),
      r • q = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • q)
    (k : G) (γ : nonnegSubmonoid deg) :
    LinearMap.hattoriStallingsTrace Λ Q (elemLinearMap Λ Q (conjNonneg ι deg hker k γ)) =
      LinearMap.hattoriStallingsTrace Λ Q (elemLinearMap Λ Q γ) := by
  have hfac : elemLinearMap Λ Q (conjNonneg ι deg hker k γ) =
      elemLinearMap Λ Q k ∘ₗ (elemLinearMap Λ Q γ ∘ₗ elemLinearMap Λ Q k⁻¹) := by
    refine LinearMap.ext fun q ↦ ?_
    simp only [LinearMap.comp_apply, elemLinearMap_apply]
    rw [hQG (single k 1), hQG (single k⁻¹ 1)]
    simp only [mapDomainRingHom_apply, mapDomain_single, ← mul_smul, single_mul_single, one_mul]
    have hgrp : conjNonneg ι deg hker k γ =
        toNonnegSubmonoid ι deg hker k * (γ * toNonnegSubmonoid ι deg hker k⁻¹) := by
      ext
      simp [mul_assoc]
    rw [hgrp]
  have hinv : elemLinearMap Λ Q k⁻¹ ∘ₗ elemLinearMap Λ Q k = .id :=
    LinearMap.ext fun q ↦ by simp [← mul_smul, single_mul_single, ← one_def]
  rw [hfac, LinearMap.hattoriStallingsTrace_comp_comm, LinearMap.comp_assoc, hinv,
    LinearMap.comp_id]

/-- The `Λ`-trace `Tr_Λ(γ, Q)` descended to `G`-conjugacy classes in `DegreeFiber deg d`. -/
def conjClassElemTrace {Q : Type*} [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [Module.Finite Λ Q] [Module.Projective Λ Q]
    (hQG : ∀ (r : MonoidAlgebra Λ G) (q : Q),
      r • q = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • q)
    (d : ℕ) :
    ConjClasses ι deg d → TauCeti.cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ ↦ LinearMap.hattoriStallingsTrace Λ Q (elemLinearMap Λ Q γ.val))
    fun a b h ↦ by
      obtain ⟨k, hk⟩ := conjSetoid_rel.1 h
      have ha : a.val = conjNonneg ι deg hker k b.val :=
        Subtype.ext (by rw [coe_conjNonneg]; exact hk)
      rw [ha]
      exact hattoriStallingsTrace_elemLinearMap_conjNonneg Λ ι deg hker hQG k b.val

@[simp]
theorem conjClassElemTrace_mk {Q : Type*} [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [Module.Finite Λ Q] [Module.Projective Λ Q]
    (hQG : ∀ (r : MonoidAlgebra Λ G) (q : Q),
      r • q = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • q)
    {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassElemTrace Λ ι deg hker hQG d (Quotient.mk (conjSetoid ι deg d) γ) =
      LinearMap.hattoriStallingsTrace Λ Q (elemLinearMap Λ Q γ.val) := by
  rfl

/-- Scalar-valued centralizer group-ring trace descended to `G`-conjugacy classes over a commutative
ring `A`. -/
def conjClassProjectiveGroupTrace [Finite G] {P : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (d : ℕ) :
    ConjClasses ι deg d → A :=
  fun c ↦ TauCeti.cyclicQuotientEquivOfCommRing ℤ A (conjClassGroupTrace A ι deg hker hPG d c)

@[simp]
theorem conjClassProjectiveGroupTrace_mk [Finite G] {P : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    {d : ℕ} (γ : DegreeFiber deg d) :
    conjClassProjectiveGroupTrace A ι deg hker hPG d (Quotient.mk (conjSetoid ι deg d) γ) =
      centralizerProjectiveGroupTrace A ι deg hker hPG γ.val := by
  rw [conjClassProjectiveGroupTrace, conjClassGroupTrace_mk,
    centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace,
    TauCeti.cyclicQuotientEquivOfCommRing_mkQ]

variable {A Λ ι deg hker}

/-- **Centralizer group-ring trace of a diagonal tensor product** (Stacks Project, Section 64.15,
Lemma 64.15.8, centralizer formula). Let `P` be an `A[Γ]`-module finite projective over `A[G]` and
`Q` a `Λ[Γ]`-module finite projective over `Λ`. For every `γ ∈ Γ`,
`Tr_Λ^{Z_γ}(γ, P ⊗_A Q) = Tr_A^{Z_γ}(γ, P) • Tr_Λ(γ, Q)` in `Λ / [Λ, Λ]`. -/
theorem centralizerGroupTrace_diagonalTensor [Finite G]
    {P Q : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [IsScalarTower A (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    [AddCommGroup Q] [Module A Q] [Module Λ Q] [IsScalarTower A Λ Q]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [Module.Finite Λ Q] [Module.Projective Λ Q]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (hQG : ∀ (r : MonoidAlgebra Λ G) (q : Q),
      r • q = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • q)
    (γ : nonnegSubmonoid deg) :
    centralizerGroupTrace Λ ι deg hker
        (DiagonalTensor.monoidAlgebraModule_comp_mapDomain A Λ (nonnegSubmonoid deg) P Q
          (toNonnegSubmonoid ι deg hker) hPG hQG) γ =
      TauCeti.cyclicQuotientCentralSMul A Λ
        (centralizerProjectiveGroupTrace A ι deg hker hPG γ)
        (LinearMap.hattoriStallingsTrace Λ Q (elemLinearMap Λ Q γ)) := by
  let Z := centralizerSubgroup ι γ.1
  let φAZ := mapDomainRingHom A Z.subtype
  let φΛZ := mapDomainRingHom Λ Z.subtype
  let _ : Module (MonoidAlgebra A Z) (MonoidAlgebra A G) := φAZ.toModule
  let _ : Module (MonoidAlgebra A Z) P := Module.compHom P φAZ
  let _ : Module (MonoidAlgebra Λ Z) Q := Module.compHom Q φΛZ
  have hφΛZ_smul : ∀ (c : Λ) (r : MonoidAlgebra Λ Z), φΛZ (c • r) = c • φΛZ r := by
    intro c r
    induction r using induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, _root_.map_add, _root_.map_add, smul_add, ha, hb]
    | single z d => simp [φΛZ, smul_single]
  have hQ_tower : IsScalarTower Λ (MonoidAlgebra Λ Z) Q :=
    { smul_assoc := fun c r q ↦ by
        change φΛZ (c • r) • q = c • (φΛZ r • q)
        rw [hφΛZ_smul, smul_assoc] }
  obtain ⟨_, _, _, hfinPZ, hprojPZ⟩ :=
    Subgroup.restrictSubgroup_isScalarTower_finite_projective (R := A) Z (fun _ _ ↦ rfl) P
      fun _ _ ↦ rfl
  let ιZ : Z →* nonnegSubmonoid deg := (toNonnegSubmonoid ι deg hker).comp Z.subtype
  have hcommZ := commute_toNonnegSubmonoid_of_mem_centralizerSubgroup ι deg hker γ
  have hactPZ : ∀ (r : MonoidAlgebra A Z) (p : P), r • p = mapDomain ιZ r • p := fun r p ↦ by
    have hcomp : r • p = φAZ r • p := rfl
    rw [hcomp, hPG]
    simp [φAZ, ιZ, mapDomainRingHom_apply, mapDomain_mapDomain]
  have hactQZ : ∀ (r : MonoidAlgebra Λ Z) (q : Q), r • q = mapDomain ιZ r • q := fun r q ↦ by
    have hcomp : r • q = φΛZ r • q := rfl
    rw [hcomp, hQG]
    simp [φΛZ, ιZ, mapDomainRingHom_apply, mapDomain_mapDomain]
  let uPZ := ιZ.singleSMulLinearMap hcommZ P hactPZ
  let uQZ := ιZ.singleSMulLinearMap hcommZ Q hactQZ
  let uDZ := DiagonalTensor.map A Λ Z uPZ uQZ
  have huDZ : ∀ x : DiagonalTensor A Λ P Q, uDZ x = single γ (1 : Λ) • x := by
    intro x
    induction x using DiagonalTensor.induction_on with
    | tmul p q =>
      simp [uDZ, uPZ, uQZ, DiagonalTensor.monoidAlgebraModule_single_smul_tmul]
    | add u v hu hv => rw [map_add, smul_add, hu, hv]
  have hDZ := DiagonalTensor.monoidAlgebraModule_comp_mapDomain A Λ G P Q Z.subtype
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  have huQZ_elem : uQZ.restrictScalars Λ = elemLinearMap Λ Q γ :=
    LinearMap.ext fun q ↦ by simp [uQZ]
  have hP_proj : centralizerProjectiveGroupTrace A ι deg hker hPG γ =
      LinearMap.projectiveGroupTrace A Z P uPZ := by
    apply (TauCeti.cyclicQuotientEquivOfCommRing ℤ A).symm.injective
    rw [TauCeti.cyclicQuotientEquivOfCommRing_symm_apply,
      TauCeti.cyclicQuotientEquivOfCommRing_symm_apply,
      ← centralizerGroupTrace_eq_mkQ_centralizerProjectiveGroupTrace,
      centralizerGroupTrace_eq_hattoriStallingsGroupTrace hPG γ (fun _ _ ↦ rfl) uPZ
        (by simp [uPZ]),
      LinearMap.hattoriStallingsGroupTrace_eq_mkQ_projectiveGroupTrace]
  rw [centralizerGroupTrace_eq_hattoriStallingsGroupTrace
      (DiagonalTensor.monoidAlgebraModule_comp_mapDomain A Λ (nonnegSubmonoid deg) P Q
        (toNonnegSubmonoid ι deg hker) hPG hQG) γ hDZ uDZ huDZ,
    LinearMap.hattoriStallingsGroupTrace_diagonalTensor_map uPZ uQZ, huQZ_elem, hP_proj]

/-- **`G`-coinvariant trace of a diagonal tensor product** (Stacks Project, Section 64.15,
Lemma 64.15.8, coinvariant formula). For any `d : ℕ` and `γ₀ ∈ deg⁻¹(d)`,
`Tr_Λ(γ₀, (P ⊗_A Q)_G) = ∑_{[γ] ∈ deg⁻¹(d)/G} Tr_A^{Z_γ}(γ, P) • Tr_Λ(γ, Q)`. -/
theorem hattoriStallingsTrace_coinvariantEnd_diagonalTensor [Finite G] (hι : Function.Injective ι)
    {P Q : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [IsScalarTower A (MonoidAlgebra A (nonnegSubmonoid deg)) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    [AddCommGroup Q] [Module A Q] [Module Λ Q] [IsScalarTower A Λ Q]
    [Module (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ (nonnegSubmonoid deg)) Q]
    [Module (MonoidAlgebra Λ G) Q] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [Module.Finite Λ Q] [Module.Projective Λ Q]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P),
      r • p = mapDomainRingHom A (toNonnegSubmonoid ι deg hker) r • p)
    (hQG : ∀ (r : MonoidAlgebra Λ G) (q : Q),
      r • q = mapDomainRingHom Λ (toNonnegSubmonoid ι deg hker) r • q)
    {d : ℕ} [Fintype (ConjClasses ι deg d)] (γ₀ : DegreeFiber deg d) :
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G (DiagonalTensor A Λ P Q))
        (coinvariantEnd Λ ι deg hι hker
          (DiagonalTensor.monoidAlgebraModule_comp_mapDomain A Λ (nonnegSubmonoid deg) P Q
            (toNonnegSubmonoid ι deg hker) hPG hQG) γ₀.val) =
      ∑ c : ConjClasses ι deg d,
        TauCeti.cyclicQuotientCentralSMul A Λ
          (conjClassProjectiveGroupTrace A ι deg hker hPG d c)
          (conjClassElemTrace Λ ι deg hker hQG d c) := by
  rw [hattoriStallingsTrace_coinvariantEnd_eq_sum_conjClasses
    (DiagonalTensor.monoidAlgebraModule_comp_mapDomain A Λ (nonnegSubmonoid deg) P Q
      (toNonnegSubmonoid ι deg hker) hPG hQG) γ₀]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  obtain ⟨γ, rfl⟩ := Quotient.exists_rep c
  simp [centralizerGroupTrace_diagonalTensor hPG hQG γ.val]

end DiagonalTensor

end TauCeti.MonoidExtension
