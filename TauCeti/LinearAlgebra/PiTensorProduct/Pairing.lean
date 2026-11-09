/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum

/-!
# Pairings on tensor products of families

Mathlib's `PiTensorProduct.map₂` applies a family of bilinear pairings factorwise.
It preserves total degree when the factor pairings add degrees, and satisfies the unsigned
Leibniz rule for slot-sum differentials when the factor pairings do. These statements let
pairings of complexes in characteristic two pass to their tensor powers, including the
resolutions used for multiplicative cohomological norms. Pairing on the left with a tensor power
of elements whose factor pairings commute with a contraction commutes with its slot homotopy
(`TauCeti.PiTensorProduct.slotHomotopy_map₂_map`), which is how the classes of such products are
compared with cup products.
-/

public section

namespace TauCeti.PiTensorProduct

open Function
open _root_.PiTensorProduct
open scoped TensorProduct

universe u v w x y z

variable {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι]
  {M : ι → Type w} {N : ι → Type x} {P : ι → Type y}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- Factorwise pairings satisfying the unsigned Leibniz rule induce a pairing satisfying
that rule for the slot-sum differentials. No characteristic assumption is needed beyond
the stated rule for the factor pairings. -/
theorem slotSum_map₂ [DecidableEq ι] (f : ∀ i, M i →ₗ[R] N i →ₗ[R] P i)
    (dM : ∀ i, Module.End R (M i)) (dN : ∀ i, Module.End R (N i))
    (dP : ∀ i, Module.End R (P i))
    (hf : ∀ i a b, dP i (f i a b) = f i (dM i a) b + f i a (dN i b))
    (a : ⨂[R] i, M i) (b : ⨂[R] i, N i) :
    slotSum ι dP (map₂ f a b) =
      map₂ f (slotSum ι dM a) b + map₂ f a (slotSum ι dN b) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      suffices h : slotSum ι dP (map₂ f (tprod R a) (tprod R b)) =
          map₂ f (slotSum ι dM (tprod R a)) (tprod R b) +
            map₂ f (tprod R a) (slotSum ι dN (tprod R b)) by
        simpa only [map_smul, LinearMap.smul_apply, smul_add] using congrArg (s • r • ·) h
      simp only [map₂_tprod_tprod, slotSum_tprod, map_sum, LinearMap.sum_apply,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hf, MultilinearMap.map_update_add]
      congr 1 <;> apply congrArg (tprod R) <;> funext j <;>
        rcases eq_or_ne j i with rfl | h <;> simp_all
    | add b c hb hc => simp only [map_add, hb, hc]; ac_rfl
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]; ac_rfl

omit [Fintype ι] in
/-- Tensor powers of maps preserving the factor pairings preserve the induced pairing. -/
theorem map_map₂
    {M' : ι → Type*} {N' : ι → Type*} {P' : ι → Type*}
    [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    [∀ i, AddCommMonoid (N' i)] [∀ i, Module R (N' i)]
    [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)]
    (f : ∀ i, M i →ₗ[R] N i →ₗ[R] P i) (f' : ∀ i, M' i →ₗ[R] N' i →ₗ[R] P' i)
    (gM : ∀ i, M i →ₗ[R] M' i) (gN : ∀ i, N i →ₗ[R] N' i) (gP : ∀ i, P i →ₗ[R] P' i)
    (hf : ∀ i a b, gP i (f i a b) = f' i (gM i a) (gN i b))
    (a : ⨂[R] i, M i) (b : ⨂[R] i, N i) :
    map gP (map₂ f a b) = map₂ f' (map gM a) (map gN b) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, LinearMap.smul_apply, map_tprod, map₂_tprod_tprod, hf]
    | add b c hb hc => simp only [map_add, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]

/-- A family of degree-adding pairings adds total degrees on the tensor products. -/
theorem map₂_mem_totalDegreePiece {A : Type z} [AddCommMonoid A]
    (ℳ : ∀ i, A → Submodule R (M i)) (𝒩 : ∀ i, A → Submodule R (N i))
    (ℬ : ∀ i, A → Submodule R (P i)) (f : ∀ i, M i →ₗ[R] N i →ₗ[R] P i)
    (hf : ∀ i m n a b, a ∈ ℳ i m → b ∈ 𝒩 i n → f i a b ∈ ℬ i (m + n))
    {m n : A} {a : ⨂[R] i, M i} {b : ⨂[R] i, N i}
    (ha : a ∈ totalDegreePiece ι ℳ m) (hb : b ∈ totalDegreePiece ι 𝒩 n) :
    map₂ f a b ∈ totalDegreePiece ι ℬ (m + n) := by
  -- Two applications of the span universal property reduce to homogeneous pure tensors.
  refine (totalDegreePiece_le_iff (P :=
    (totalDegreePiece ι ℬ (m + n)).comap ((map₂ f).flip b)).2 ?_) ha
  rintro p x hx rfl
  refine (totalDegreePiece_le_iff (P :=
    (totalDegreePiece ι ℬ ((∑ i, p i) + n)).comap (map₂ f (tprod R x))).2 ?_) hb
  rintro q y hy rfl
  simp only [Submodule.mem_comap, map₂_tprod_tprod, ← Finset.sum_add_distrib]
  exact tprod_mem_totalDegreePiece fun i ↦ hf i _ _ _ _ (hx i) (hy i)

omit [Fintype ι] in
/-- Pairing with a pure tensor applies the factor pairings with its entries. -/
theorem map₂_tprod (f : ∀ i, M i →ₗ[R] N i →ₗ[R] P i) (a : ∀ i, M i) :
    map₂ f (tprod R a) = map fun i ↦ f i (a i) := by
  ext b
  simp only [LinearMap.compMultilinearMap_apply, map₂_tprod_tprod, map_tprod]

section SlotHomotopy

variable [LinearOrder ι] {M₀ : Type w} {N₀ : Type x} {P₀ : Type y} {M' : Type z}
  [AddCommMonoid M₀] [Module R M₀] [AddCommMonoid N₀] [Module R N₀]
  [AddCommMonoid P₀] [Module R P₀] [AddCommMonoid M'] [Module R M']

/-- Pairing on the left with a tensor power of elements in the image of `g` commutes with slot
homotopies, provided that pairing with each such element intertwines the endomorphisms `e`, `e'`
and the homotopies `h`, `h'`. -/
theorem slotHomotopy_map₂_map (f : M₀ →ₗ[R] N₀ →ₗ[R] P₀) (g : M' →ₗ[R] M₀)
    {e h : Module.End R N₀} {e' h' : Module.End R P₀}
    (he : ∀ m n, e' (f (g m) n) = f (g m) (e n)) (hh : ∀ m n, h' (f (g m) n) = f (g m) (h n))
    (x : ⨂[R] _ : ι, M') (w : ⨂[R] _ : ι, N₀) :
    slotHomotopy ι (fun _ ↦ e') (fun _ ↦ h') (map₂ (fun _ ↦ f) (map (fun _ ↦ g) x) w) =
      map₂ (fun _ ↦ f) (map (fun _ ↦ g) x) (slotHomotopy ι (fun _ ↦ e) (fun _ ↦ h) w) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, LinearMap.smul_apply, map_tprod, map₂_tprod]
    exact congrArg (r • ·) (LinearMap.congr_fun (slotHomotopy_comp_map _
      (fun i ↦ LinearMap.ext (he (x i))) (fun i ↦ LinearMap.ext (hh (x i)))) w)
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end SlotHomotopy

end TauCeti.PiTensorProduct
