/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Trace
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Star
-- Private: field structure on `ZMod 3`, permutation trace, and essential-idempotent trace are
-- proof-only.
import TauCeti.LinearAlgebra.Trace.Idempotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Adjoint, universal presentation, dimension of `cubicFixed`, and surjectivity of `cubicHom`

Building on `TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file supplies:

* The conjugate-linear reversal `cubicAdjoint N` on `CubicTorus N` and its restriction
  `cubicFixedAdjoint N` to `cubicFixed N`, showing that `cubicHom m` intertwines the
  Temperley–Lieb analytic adjoint with `cubicAdjoint (m - 1)` (`cubicHom_star`).
* The universal property `liftSite` of `CubicTorus N` on the site unitaries `cubicSite N`,
  together with `adjoin_range_cubicSite` and `algHom_ext_cubicSite`.
* The dimension formula `finrank_cubicFixed : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* Generation of `cubicFixed N` by the spectral projections (`adjoin_range_cubicProjection`) and
  surjectivity of the comparison homomorphism `cubicHom m` (`cubicHom_surjective`).

## Main definitions and results

* `TauCeti.TemperleyLieb.cubicAdjoint`, `TauCeti.TemperleyLieb.cubicFixedAdjoint`.
* `TauCeti.TemperleyLieb.liftSite`, `TauCeti.TemperleyLieb.adjoin_range_cubicSite`,
  `TauCeti.TemperleyLieb.algHom_ext_cubicSite`.
* `TauCeti.TemperleyLieb.finrank_cubicFixed`, `TauCeti.TemperleyLieb.cubicHom_star`,
  `TauCeti.TemperleyLieb.adjoin_range_cubicProjection`, `TauCeti.TemperleyLieb.cubicHom_surjective`.
-/

public section

namespace TauCeti.TemperleyLieb

open Multiplicative TwistedMonoidAlgebra

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` for the analytic `StarRing` structure
on `TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) := ⟨Complex.conj_ofReal _⟩

private theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by revert x; decide

private theorem cubeRootPow_eq_one_iff {x : ZMod 3} : cubeRootPow x = 1 ↔ x = 0 := by
  refine ⟨fun h ↦ by_contra fun hx ↦ ?_, fun h ↦ by simp [h]⟩
  have hsum := one_add_cubeRootPow_add_sq hx
  rw [h, Units.val_one, one_pow] at hsum
  norm_num at hsum

private theorem star_coe_cubeRootPow (x : ZMod 3) :
    star (cubeRootPow x : ℂ) = (cubeRootPow (-x) : ℂ) := by
  rw [coe_cubeRootPow, coe_cubeRootPow, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, Complex.star_def]

theorem cubicFactor_inv_self (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ a = 1 := by
  rw [cubicFactor_apply, toAdd_inv, LinearMap.map_neg₂, chainForm_self,
    neg_zero, mul_zero, AddChar.map_zero_eq_one]

theorem star_coe_cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    star (cubicFactor N a b : ℂ) = (cubicFactor N b⁻¹ a⁻¹ : ℂ) := by
  rw [cubicFactor_apply, star_coe_cubeRootPow, cubicFactor_apply, toAdd_inv, toAdd_inv,
    LinearMap.map_neg₂, LinearMap.map_neg, neg_neg, chainForm_swap, mul_neg, neg_neg]

/-! ### Conjugate-linear reversal on `CubicTorus N` and `cubicFixed N` -/

/-- **The conjugate-linear adjoint** `†` on `CubicTorus N`, sending `∑ z_a • W(a)` to
`∑ star z_a • W(-a)`. -/
noncomputable abbrev cubicAdjoint (N : ℕ) : CubicTorus N →ₗ⋆[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.conjReverse ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

@[simp] theorem cubicAdjoint_weyl (N : ℕ) (a : Fin N → ZMod 3) :
    cubicAdjoint N (weyl N a) = weyl N (-a) := by
  rw [weyl_def, cubicAdjoint, TwistedMonoidAlgebra.conjReverse_of, ← ofAdd_neg, ← weyl_def]

theorem cubicAdjoint_mul (N : ℕ) (x y : CubicTorus N) :
    cubicAdjoint N (x * y) = cubicAdjoint N y * cubicAdjoint N x :=
  TwistedMonoidAlgebra.conjReverse_mul (star_coe_cubicFactor N) x y

@[simp] theorem cubicAdjoint_cubicSite (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicSite N j) = cubicSite N j ^ 2 := by
  nth_rw 1 [cubicSite_def]
  rw [cubicAdjoint_weyl, ← Pi.single_neg,
    show (-1 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide, ← cubicSite_pow]

@[simp] theorem cubicAdjoint_cubicProjection (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicProjection N j) = cubicProjection N j := by
  have hsq : cubicAdjoint N (cubicSite N j ^ 2) = cubicSite N j := by
    rw [sq, cubicAdjoint_mul, cubicAdjoint_cubicSite, ← pow_add, show 2 + 2 = 3 + 1 from rfl,
      pow_succ, cubicSite_pow_three, one_mul]
  rw [cubicProjection_def, map_smulₛₗ, starRingEnd_apply, star_inv₀, star_ofNat, map_add, map_add,
    TwistedMonoidAlgebra.conjReverse_one, cubicAdjoint_cubicSite, hsq, add_right_comm]

theorem cubicAdjoint_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint N (cubicInversion N x) = cubicInversion N (cubicAdjoint N x) := by
  induction (TwistedMonoidAlgebra.basis ℂ _ (cubicFactor N)).mem_span x
      using Submodule.span_induction with
  | mem _ ha =>
    obtain ⟨a, rfl⟩ := ha
    rw [TwistedMonoidAlgebra.basis_apply, of_eq_weyl, cubicInversion_weyl, cubicAdjoint_weyl,
      cubicAdjoint_weyl, cubicInversion_weyl]
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul _ _ _ hx => simp [hx]

@[simp] theorem cubicScalarCoefficient_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicInversion N x) = cubicScalarCoefficient N x := by
  have h : cubicScalarCoefficient N ∘ₗ (cubicInversion N).toLinearMap =
      cubicScalarCoefficient N :=
    (TwistedMonoidAlgebra.basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, basis_apply, of_eq_weyl,
        cubicInversion_weyl, cubicScalarCoefficient_weyl, cubicScalarCoefficient_weyl]
      simp
  exact LinearMap.congr_fun h x

theorem cubicAdjoint_mem_cubicFixed {N : ℕ} {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicAdjoint N x ∈ cubicFixed N := by
  rw [mem_cubicFixed, ← cubicAdjoint_cubicInversion, mem_cubicFixed.mp hx]

/-- Restriction of `cubicAdjoint N` to the inversion-fixed subalgebra `cubicFixed N`. -/
noncomputable def cubicFixedAdjoint (N : ℕ) : cubicFixed N →ₗ⋆[ℂ] cubicFixed N where
  toFun x := ⟨cubicAdjoint N x.val, cubicAdjoint_mem_cubicFixed x.property⟩
  map_add' x y := Subtype.ext (map_add (cubicAdjoint N) x.val y.val)
  map_smul' c x := Subtype.ext (map_smulₛₗ (cubicAdjoint N) c x.val)

@[simp] theorem coe_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    (cubicFixedAdjoint N x : CubicTorus N) = cubicAdjoint N x := (rfl)

@[simp] theorem cubicFixedAdjoint_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    cubicFixedAdjoint N (cubicFixedAdjoint N x) = x :=
  Subtype.ext (TwistedMonoidAlgebra.conjReverse_conjReverse x.val)

theorem cubicFixedAdjoint_mul (N : ℕ) (x y : cubicFixed N) :
    cubicFixedAdjoint N (x * y) = cubicFixedAdjoint N y * cubicFixedAdjoint N x :=
  Subtype.ext (cubicAdjoint_mul N x.val y.val)

/-! ### Dimension of `cubicFixed N` -/

/-- **Dimension of the inversion-fixed subalgebra**: `dim_ℂ (cubicFixed N) = (3 ^ N + 1) / 2`. -/
@[simp] theorem finrank_cubicFixed (N : ℕ) : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  classical
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  let θ : Module.End ℂ (CubicTorus N) := (cubicInversion N).toLinearMap
  let f : Module.End ℂ (CubicTorus N) := 1 + θ
  have hsq : f * f = (2 : ℂ) • f := by
    ext x
    simp only [f, θ, mul_apply_eq_comp, _root_.LinearMap.add_apply, one_apply_eq_self,
      AlgHom.toLinearMap_apply, map_add, cubicInversion_cubicInversion, two_smul]
    abel_nf
  have hrange : _root_.LinearMap.range f = (cubicFixed N).toSubmodule := by
    ext x
    simp only [_root_.LinearMap.mem_range, Subalgebra.mem_toSubmodule, mem_cubicFixed]
    exact ⟨fun ⟨y, hy⟩ ↦ by subst hy; simp [f, θ, add_comm],
      fun hx ↦ ⟨(2 : ℂ)⁻¹ • x, by simp [f, θ, hx, ← two_smul ℂ x]⟩⟩
  let σ : Equiv.Perm (Multiplicative (Fin N → ZMod 3)) := inv_involutive.toPerm Inv.inv
  have : Module.Finite ℂ (CubicTorus N) := Module.Finite.of_basis b
  have : Module.Free ℂ (CubicTorus N) := Module.Free.of_basis b
  have hmat : _root_.LinearMap.toMatrix b b θ = σ.permMatrix ℂ := by
    ext i j
    rw [_root_.LinearMap.toMatrix_apply, TwistedMonoidAlgebra.basis_apply]
    dsimp only [θ, σ, Equiv.Perm.permMatrix]
    rw [AlgHom.toLinearMap_apply, of_eq_weyl, cubicInversion_weyl, weyl_def,
      TwistedMonoidAlgebra.repr_of, Finsupp.single_apply, PEquiv.toMatrix_apply,
      ofAdd_neg, ofAdd_toAdd]
    simp [Equiv.toPEquiv_apply, inv_eq_iff_eq_inv, eq_comm (a := i)]
  have hfix : Function.fixedPoints σ = {1} := by
    ext a
    simp only [Function.mem_fixedPoints_iff, σ, Set.mem_singleton_iff]
    refine ⟨fun h ↦ toAdd.injective (funext fun i ↦ ?_), fun h ↦ by simp [h]⟩
    have hi : -a.toAdd i = a.toAdd i := congrFun (congrArg toAdd h) i
    rw [ZMod.neg_eq_self_iff] at hi
    exact hi.resolve_right (by omega)
  have htrθ : _root_.LinearMap.trace ℂ (CubicTorus N) θ = 1 := by
    rw [_root_.LinearMap.trace_eq_matrix_trace ℂ b θ, hmat, Matrix.trace_permutation, hfix,
      Set.ncard_singleton, Nat.cast_one]
  have htr1 : _root_.LinearMap.trace ℂ (CubicTorus N) (1 : Module.End ℂ (CubicTorus N)) =
      (3 ^ N : ℂ) :=
    (_root_.LinearMap.trace_one (R := ℂ) (M := CubicTorus N)).trans
      (by rw [finrank_cubicTorus, Nat.cast_pow, Nat.cast_ofNat])
  have htr := TauCeti.LinearMap.trace_eq_mul_finrank_range (K := ℂ) (M := CubicTorus N) hsq
  rw [hrange] at htr
  dsimp only [f] at htr
  rw [map_add, htr1, htrθ] at htr
  have hnat : 3 ^ N + 1 = 2 * Module.finrank ℂ (cubicFixed N) := by exact_mod_cast htr
  omega

/-! ### Universal property of `CubicTorus N` on site generators -/

section UniversalProperty

private def halfChainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j else 0

private theorem chainForm_eq_sub (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (ZMod 3) N a b = halfChainForm N a b - halfChainForm N b a := by
  simp only [chainForm_apply, halfChainForm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_add_left (N : ℕ) (a₁ a₂ b : Fin N → ZMod 3) :
    halfChainForm N (a₁ + a₂) b = halfChainForm N a₁ b + halfChainForm N a₂ b := by
  simp only [halfChainForm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_add_right (N : ℕ) (a b₁ b₂ : Fin N → ZMod 3) :
    halfChainForm N a (b₁ + b₂) = halfChainForm N a b₁ + halfChainForm N a b₂ := by
  simp only [halfChainForm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_single_single (N : ℕ) (i j : Fin N) (c d : ZMod 3) :
    halfChainForm N (Pi.single i c) (Pi.single j d) =
      if (i : ℕ) + 1 = j then c * d else 0 := by
  rw [halfChainForm, Fintype.sum_eq_single i (fun x hx ↦ by simp [Pi.single_eq_of_ne hx]),
    Fintype.sum_eq_single j (fun y hy ↦ by simp [Pi.single_eq_of_ne hy])]
  simp

private theorem partialProd_one {A : Type*} [Monoid A] (N : ℕ) :
    Fin.partialProd (fun _ : Fin N ↦ (1 : A)) (Fin.last N) = 1 := by
  induction N with
  | zero => exact Fin.partialProd_zero _
  | succ N ih =>
    rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init]
    simpa [Fin.init_def] using ih

private theorem partialProd_pow_single {A : Type*} [Monoid A] :
    ∀ {N : ℕ} (u : Fin N → A) (j : Fin N),
      Fin.partialProd (fun i ↦ u i ^ ((Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) i).val)
        (Fin.last N) = u j
  | 0, _, j => Fin.elim0 j
  | N + 1, u, j => by
    rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init]
    induction j using Fin.lastCases with
    | last =>
      have hinit : Fin.init (fun i : Fin (N + 1) ↦
          u i ^ ((Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3) i).val) =
          fun _ ↦ 1 := by
        ext i; simp [Fin.init_def]
      rw [hinit, partialProd_one, one_mul, Pi.single_eq_same, ZMod.val_one, pow_one]
    | cast i =>
      have hinit : Fin.init (fun k : Fin (N + 1) ↦
          u k ^ ((Pi.single i.castSucc (1 : ZMod 3) : Fin (N + 1) → ZMod 3) k).val) =
          fun k ↦ (u ∘ Fin.castSucc) k ^
            ((Pi.single i (1 : ZMod 3) : Fin N → ZMod 3) k).val := by
        ext k; simp [Fin.init_def, Pi.single_apply, Fin.castSucc_inj]
      rw [hinit, partialProd_pow_single (u ∘ Fin.castSucc) i,
        Pi.single_eq_of_ne (M := fun _ : Fin (N + 1) ↦ ZMod 3) (Fin.castSucc_ne_last i).symm 1,
        ZMod.val_zero, pow_zero, mul_one]
      rfl

variable {A : Type*} [Semiring A] [Algebra ℂ A]

private theorem mul_partialProd_of_qcomm :
    ∀ {N : ℕ} {u : Fin N → A} {v : A} {φ : Fin N → ZMod 3},
      (∀ i : Fin N, v * u i = (cubeRootPow (2 * φ i) : ℂ) • (u i * v)) →
      ∀ b : Fin N → ZMod 3,
        v * Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) =
          (cubeRootPow (2 * ∑ i : Fin N, φ i * b i) : ℂ) •
            (Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) * v)
  | 0, _, _, _, _, _ => by simp
  | N + 1, u, v, φ, hφ, b => by
    have ih := mul_partialProd_of_qcomm (u := u ∘ Fin.castSucc) (φ := φ ∘ Fin.castSucc)
      (fun i ↦ hφ i.castSucc) (Fin.init b)
    have hsemi : SemiconjBy v (u (Fin.last N))
        ((cubeRootPow (2 * φ (Fin.last N)) : ℂ) • u (Fin.last N)) := by
      simpa [SemiconjBy, smul_mul_assoc] using hφ (Fin.last N)
    have hlast : v * u (Fin.last N) ^ (b (Fin.last N)).val =
        (cubeRootPow (2 * φ (Fin.last N) * b (Fin.last N)) : ℂ) •
          (u (Fin.last N) ^ (b (Fin.last N)).val * v) := by
      have hp := (hsemi.pow_right (b (Fin.last N)).val).eq
      rw [smul_pow, smul_mul_assoc, ← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow,
        nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm (b (Fin.last N))] at hp
      exact hp
    have hinit_fn : Fin.init (fun i ↦ u i ^ (b i).val) =
        fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val := rfl
    rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init, hinit_fn, ← mul_assoc, ih,
      smul_mul_assoc, mul_assoc, hlast, mul_smul_comm, smul_smul, ← Units.val_mul,
      ← AddChar.map_add_eq_mul, ← mul_assoc]
    congr 3; rw [Fin.sum_univ_castSucc]; simp [Fin.init, mul_add]; ring

private theorem halfChainForm_succ (N : ℕ) (b a : Fin (N + 1) → ZMod 3) :
    halfChainForm (N + 1) b a =
      halfChainForm N (Fin.init b) (Fin.init a) +
        a (Fin.last N) *
          ∑ i : Fin N, (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * b i.castSucc := by
  unfold halfChainForm
  rw [Fin.sum_univ_castSucc,
    show (∑ j : Fin (N + 1),
        if (Fin.last N : ℕ) + 1 = (j : ℕ) then b (Fin.last N) * a j else 0) = 0 from
      Finset.sum_eq_zero fun j _ ↦ by simp [Fin.val_last, show ¬ N + 1 = (j : ℕ) by omega],
    add_zero]
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, Finset.sum_add_distrib,
    Fin.init, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring

private theorem partialProd_mul_partialProd :
    ∀ {N : ℕ} (u : Fin N → A), (∀ j, u j ^ 3 = 1) →
      (∀ {i j : Fin N}, (i : ℕ) + 1 = j → u i * u j = (cubeRootPow 1 : ℂ) • (u j * u i)) →
      (∀ {i j : Fin N}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → u i * u j = u j * u i) →
      ∀ a b : Fin N → ZMod 3,
      Fin.partialProd (fun i ↦ u i ^ (a i).val) (Fin.last N) *
          Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) =
        (cubeRootPow (2 * halfChainForm N b a) : ℂ) •
          Fin.partialProd (fun i ↦ u i ^ ((a + b) i).val) (Fin.last N)
  | 0, _, _, _, _, _, _ => by simp [halfChainForm]
  | N + 1, u, hcube, hadj, hdist, a, b => by
    have hqcomm : ∀ i : Fin N, u (Fin.last N) * u i.castSucc =
        (cubeRootPow (2 * if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) : ℂ) •
          (u i.castSucc * u (Fin.last N)) := fun i ↦ by
      split_ifs with hi
      · have h := congrArg ((cubeRootPow 2 : ℂ) • ·) (hadj (i := i.castSucc) (j := Fin.last N) hi)
        rw [smul_smul, ← Units.val_mul, ← AddChar.map_add_eq_mul,
          show (2 : ZMod 3) + 1 = 0 by decide, AddChar.map_zero_eq_one, Units.val_one, one_smul]
          at h
        simpa [mul_one] using h.symm
      · have hd : (i.castSucc : ℕ) + 2 ≤ (Fin.last N : ℕ) := by
          have := i.isLt; simp at hi ⊢; omega
        simp [hdist (Or.inr hd)]
    have hmulb := mul_partialProd_of_qcomm (u := u ∘ Fin.castSucc) hqcomm (Fin.init b)
    have hsemi : SemiconjBy
        (Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N))
        ((cubeRootPow (2 * ∑ i : Fin N,
          (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * Fin.init b i) : ℂ) • u (Fin.last N))
        (u (Fin.last N)) := by
      simpa [SemiconjBy, smul_mul_assoc] using hmulb.symm
    have hcomm : u (Fin.last N) ^ (a (Fin.last N)).val *
          Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N) =
        (cubeRootPow (2 * (a (Fin.last N) * ∑ i : Fin N,
          (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * Fin.init b i)) : ℂ) •
          (Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N) *
            u (Fin.last N) ^ (a (Fin.last N)).val) := by
      have hp := (hsemi.pow_right (a (Fin.last N)).val).eq.symm
      rwa [smul_pow, mul_smul_comm, ← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow,
        nsmul_eq_mul, ZMod.natCast_zmod_val, mul_left_comm] at hp
    have ih := partialProd_mul_partialProd (u ∘ Fin.castSucc) (fun j ↦ hcube j.castSucc)
      (fun h ↦ hadj h) (fun h ↦ hdist h) (Fin.init a) (Fin.init b)
    have hpow : u (Fin.last N) ^ (a (Fin.last N)).val * u (Fin.last N) ^ (b (Fin.last N)).val =
        u (Fin.last N) ^ ((a + b) (Fin.last N)).val := by
      rw [← pow_add, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hcube (Fin.last N))]
    have hinit : Fin.init (a + b) = Fin.init a + Fin.init b := by ext i; simp [Fin.init_def]
    have hinit_fn (x : Fin (N + 1) → ZMod 3) :
        Fin.init (fun i ↦ u i ^ (x i).val) = fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init x i).val :=
      rfl
    simp only [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init, hinit_fn]
    rw [mul_assoc (Fin.partialProd _ _) (u (Fin.last N) ^ _),
      ← mul_assoc (u (Fin.last N) ^ _), hcomm, smul_mul_assoc, mul_smul_comm,
      mul_assoc (Fin.partialProd _ _), ← mul_assoc (Fin.partialProd _ _), ih, smul_mul_assoc,
      hpow, smul_smul, ← Units.val_mul, ← AddChar.map_add_eq_mul, halfChainForm_succ, hinit]
    refine congrArg (fun z ↦ (cubeRootPow z : ℂ) • _) ?_
    simp only [Fin.init]; ring

/-- **Universal property of `CubicTorus N` on site generators.** Any `N` elements `u : Fin N → A` of
a `ℂ`-algebra satisfying `u j ^ 3 = 1`, `u i * u_{i+1} = ω • (u_{i+1} * u i)`, and commuting at
distance `≥ 2` determine a `ℂ`-algebra homomorphism `CubicTorus N →ₐ[ℂ] A` sending `cubicSite N j`
to `u j`. -/
noncomputable def liftSite {N : ℕ} (u : Fin N → A)
    (hcube : ∀ j, u j ^ 3 = 1)
    (hadj : ∀ {i j : Fin N}, (i : ℕ) + 1 = j → u i * u j = (cubeRootPow 1 : ℂ) • (u j * u i))
    (hdist : ∀ {i j : Fin N}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → u i * u j = u j * u i) :
    CubicTorus N →ₐ[ℂ] A :=
  TwistedMonoidAlgebra.lift
    (fun a ↦ (cubeRootPow (halfChainForm N a.toAdd a.toAdd) : ℂ) •
      Fin.partialProd (fun i ↦ u i ^ (a.toAdd i).val) (Fin.last N))
    (by simp [partialProd_one, halfChainForm])
    (fun a b ↦ by
      rw [smul_mul_smul_comm, partialProd_mul_partialProd u hcube hadj hdist, smul_smul,
        smul_smul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, cubicFactor_apply,
        ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
        chainForm_eq_sub, toAdd_mul, halfChainForm_add_left, halfChainForm_add_right,
        halfChainForm_add_right]
      congr 3; apply sub_eq_zero.mp
      calc _ = (3 : ZMod 3) * (halfChainForm N b.toAdd a.toAdd -
              halfChainForm N a.toAdd b.toAdd) := by ring
        _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul])

/-- `liftSite` sends each site unitary `cubicSite N j` to `u j`. -/
@[simp] theorem liftSite_cubicSite {N : ℕ} (u : Fin N → A) (hcube) (hadj) (hdist) (j : Fin N) :
    liftSite u hcube hadj hdist (cubicSite N j) = u j := by
  rw [liftSite, cubicSite_def, weyl_def, TwistedMonoidAlgebra.lift_of, toAdd_ofAdd,
    halfChainForm_single_single]
  simp only [Nat.add_one_ne_self, ↓reduceIte, AddChar.map_zero_eq_one, Units.val_one, one_smul]
  exact partialProd_pow_single u j

end UniversalProperty

/-- The site unitaries `cubicSite N` generate `CubicTorus N` as a `ℂ`-algebra. -/
theorem adjoin_range_cubicSite (N : ℕ) :
    Algebra.adjoin ℂ (Set.range (cubicSite N)) = ⊤ := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicSite N))
  have hsingle (j : Fin N) (r : ZMod 3) : weyl N (Pi.single j r) ∈ S := by
    have hj : cubicSite N j ∈ S := Algebra.subset_adjoin (Set.mem_range_self j)
    rcases zmod3_cases r with rfl | rfl | rfl
    · rw [Pi.single_zero, weyl_zero]; exact S.one_mem
    · rwa [← cubicSite_def]
    · rw [show (2 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide, ← cubicSite_pow j 2]
      exact S.pow_mem hj 2
  have hweyl (a : Fin N → ZMod 3) : weyl N a ∈ S := by
    have hsum : a = ∑ j : Fin N, Pi.single j (a j) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    induction (Finset.univ : Finset (Fin N)) using Finset.cons_induction with
    | empty => simp [S.one_mem]
    | cons j s _ ih =>
      rw [Finset.sum_cons]
      set u : Fin N → ZMod 3 := Pi.single j (a j)
      set v : Fin N → ZMod 3 := ∑ i ∈ s, Pi.single i (a i)
      have hmul := S.smul_mem (S.mul_mem (hsingle j (a j)) ih)
        ((cubeRootPow (-(2 * chainForm (ZMod 3) N u v)) : ℂˣ) : ℂ)
      rwa [weyl_mul_weyl, smul_smul, ← Units.val_mul, ← AddChar.map_add_eq_mul,
        neg_add_cancel, AddChar.map_zero_eq_one, Units.val_one, one_smul] at hmul
  suffices ∀ x : CubicTorus N, x ∈ S from eq_top_iff.mpr fun x _ ↦ this x
  intro x
  induction (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
      (cubicFactor N)).mem_span x using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [TwistedMonoidAlgebra.basis_apply, of_eq_weyl]; exact hweyl a.toAdd
  | zero => exact S.zero_mem
  | add _ _ _ _ hx hy => exact S.add_mem hx hy
  | smul _ _ _ hx => exact S.smul_mem hx _

/-- Two `ℂ`-algebra homomorphisms out of `CubicTorus N` agreeing on `cubicSite N` are equal. -/
theorem algHom_ext_cubicSite {N : ℕ} {A : Type*} [Semiring A] [Algebra ℂ A]
    {F G : CubicTorus N →ₐ[ℂ] A} (h : ∀ j : Fin N, F (cubicSite N j) = G (cubicSite N j)) :
    F = G :=
  AlgHom.ext_of_adjoin_eq_top (adjoin_range_cubicSite N) (by rintro _ ⟨j, rfl⟩; exact h j)

/-! ### Star compatibility of `cubicHom` -/

/-- `cubicHom m` intertwines `star` with `cubicAdjoint (m - 1)` in `CubicTorus (m - 1)`. -/
theorem coe_cubicHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicHom m (star x) : CubicTorus (m - 1)) = cubicAdjoint (m - 1) (cubicHom m x) := by
  induction x using TemperleyLieb.induction with
  | e j =>
    rw [star_e, coe_cubicHom_e, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
      Complex.conj_ofReal, cubicAdjoint_cubicProjection]
  | algebraMap c =>
    have hstar : star (algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) c) =
        algebraMap ℂ _ (star c) := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, Algebra.algebraMap_eq_smul_one]
    rw [hstar, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
      Subalgebra.coe_smul, Subalgebra.coe_one, map_smulₛₗ, starRingEnd_apply,
      TwistedMonoidAlgebra.conjReverse_one]
  | add x y hx hy =>
    have hadd (a b) : cubicHom m (a + b) = cubicHom m a + cubicHom m b := (cubicHom m).map_add' a b
    rw [star_add, hadd, hadd, Subalgebra.coe_add, Subalgebra.coe_add,
      map_add (cubicAdjoint (m - 1)), hx, hy]
  | mul x y hx hy =>
    rw [star_mul, map_mul, map_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, cubicAdjoint_mul,
      hx, hy]

/-- `cubicHom m` intertwines `star` with `cubicFixedAdjoint (m - 1)`. -/
@[simp] theorem cubicHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicHom m (star x) = cubicFixedAdjoint (m - 1) (cubicHom m x) :=
  Subtype.ext (by rw [coe_cubicHom_star, coe_cubicFixedAdjoint])

/-! ### Generation of `cubicFixed N` by `cubicProjection N` and surjectivity of `cubicHom` -/

/-- Symmetrized Weyl element `S(a) = W(a) + W(-a)` in `CubicTorus N`. -/
private noncomputable def symmWeyl (N : ℕ) (a : Fin N → ZMod 3) : CubicTorus N :=
  weyl N a + weyl N (-a)

private theorem symmWeyl_neg (N : ℕ) (a : Fin N → ZMod 3) :
    symmWeyl N (-a) = symmWeyl N a := by simp [symmWeyl, add_comm]

private theorem symmWeyl_zero (N : ℕ) : symmWeyl N 0 = (2 : ℂ) • 1 := by
  simp [symmWeyl, two_smul]

private theorem symmWeyl_mul_symmWeyl (N : ℕ) (a b : Fin N → ZMod 3) :
    symmWeyl N a * symmWeyl N b =
      (cubeRootPow (2 * chainForm (ZMod 3) N a b) : ℂ) • symmWeyl N (a + b) +
        (cubeRootPow (-(2 * chainForm (ZMod 3) N a b)) : ℂ) • symmWeyl N (a - b) := by
  have h1 : -a + -b = -(a + b) := by ring
  have h2 : -a + b = -(a - b) := by ring
  simp only [symmWeyl, add_mul, mul_add, weyl_mul_weyl, map_neg, LinearMap.neg_apply,
    mul_neg, neg_neg, h1, h2, ← sub_eq_add_neg, smul_add]
  abel

private theorem symmWeyl_add_mem_of_chainForm_ne_zero {N : ℕ} {S : Subalgebra ℂ (CubicTorus N)}
    {a b : Fin N → ZMod 3} (ha : symmWeyl N a ∈ S) (hb : symmWeyl N b ∈ S)
    (hc : chainForm (ZMod 3) N a b ≠ 0) :
    symmWeyl N (a + b) ∈ S := by
  set αu : ℂˣ := cubeRootPow (2 * chainForm (ZMod 3) N a b)
  set α : ℂ := (αu : ℂ)
  set β : ℂ := ((αu⁻¹ : ℂˣ) : ℂ)
  have hαβ : α * β = 1 := by simp [α, β]
  have hβα : β * α = 1 := mul_comm α β ▸ hαβ
  have hα3 : α ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
      show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul, AddChar.map_zero_eq_one, Units.val_one]
  have hα1 : α ≠ 1 := fun h1 ↦ by
    have hu : αu = 1 := Units.ext h1
    rw [cubeRootPow_eq_one_iff] at hu
    exact hc ((mul_eq_zero.mp hu).resolve_left (by decide))
  have hba : symmWeyl N b * symmWeyl N a = β • symmWeyl N (a + b) + α • symmWeyl N (a - b) := by
    have hsw : 2 * chainForm (ZMod 3) N b a = -(2 * chainForm (ZMod 3) N a b) := by
      rw [chainForm_swap]; ring
    rw [symmWeyl_mul_symmWeyl, hsw, AddChar.map_neg_eq_inv, neg_neg, add_comm b a,
      show b - a = -(a - b) by ring, symmWeyl_neg]
  have hcomb : α • (symmWeyl N a * symmWeyl N b) + (-β) • (symmWeyl N b * symmWeyl N a) =
      (α ^ 2 - β ^ 2) • symmWeyl N (a + b) := by
    rw [symmWeyl_mul_symmWeyl N a b, AddChar.map_neg_eq_inv, hba, smul_add, smul_add, smul_smul,
      smul_smul, smul_smul, smul_smul, hαβ, show -β * β = -(β ^ 2) by ring,
      show -β * α = -1 by linear_combination -hβα, ← sq α, add_add_add_comm, ← add_smul,
      ← add_smul, add_neg_cancel, zero_smul, add_zero, ← sub_eq_add_neg]
  have hne : α ^ 2 - β ^ 2 ≠ 0 := fun h0 ↦ hα1 <| sub_eq_zero.mp <| by
    linear_combination (α ^ 2) * h0 - α * hα3 + (β * α + 1) * hβα
  have hmem := S.smul_mem
    (hcomb ▸ S.add_mem (S.smul_mem (S.mul_mem ha hb) α) (S.smul_mem (S.mul_mem hb ha) (-β)))
    (α ^ 2 - β ^ 2)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hmem

private theorem symmWeyl_single_mem_adjoin (N : ℕ) (j : Fin N) (r : ZMod 3) :
    symmWeyl N (Pi.single j r) ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  have hp : symmWeyl N (Pi.single j 1) ∈ S := by
    have h1 : (1 : CubicTorus N) + (-1 : ℂ) • (1 : CubicTorus N) = 0 := by
      nth_rw 1 [← one_smul ℂ (1 : CubicTorus N)]
      rw [← add_smul, add_neg_cancel, zero_smul]
    have heq : symmWeyl N (Pi.single j 1) =
        (3 : ℂ) • cubicProjection N j + (-1 : ℂ) • (1 : CubicTorus N) := by
      rw [symmWeyl, ← Pi.single_neg, show (-1 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide,
        ← cubicSite_pow j 2, ← cubicSite_def, cubicProjection_def, smul_smul,
        mul_inv_cancel₀ (by norm_num), one_smul, add_right_comm (1 + cubicSite N j),
        add_right_comm 1 (cubicSite N j), h1, zero_add]
    exact heq ▸ S.add_mem (S.smul_mem (Algebra.subset_adjoin (Set.mem_range_self j)) (3 : ℂ))
      (S.smul_mem S.one_mem (-1 : ℂ))
  rcases zmod3_cases r with rfl | rfl | rfl
  · rw [Pi.single_zero, symmWeyl_zero]; exact S.smul_mem S.one_mem (2 : ℂ)
  · exact hp
  · simpa [← show (-1 : ZMod 3) = 2 by decide, Pi.single_neg, symmWeyl_neg] using hp

private theorem chainForm_prefix_single {N m : ℕ} (hm : m + 1 < N)
    {y : Fin N → ZMod 3} (hy : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → y i = 0) (r : ZMod 3) :
    chainForm (ZMod 3) N y (Pi.single ⟨m + 1, hm⟩ r) = y ⟨m, by omega⟩ * r := by
  rw [chainForm_apply, Fintype.sum_eq_single (⟨m, by omega⟩ : Fin N)]
  · rw [Fintype.sum_eq_single (⟨m + 1, hm⟩ : Fin N)]
    · simp
    · intro j hj; simp [show ¬ (m : ℕ) + 1 = (j : ℕ) from fun h ↦ hj (Fin.ext h.symm)]
  · intro i hi
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    split_ifs with hij
    · have hj : j ≠ ⟨m + 1, hm⟩ := fun h ↦
        hi (Fin.ext (by have := congrArg Fin.val h; simp at this ⊢; omega))
      by_cases him : i = ⟨m + 1, hm⟩
      · subst him; simp [Pi.single_eq_of_ne hj, hy j (by simp at hij; omega)]
      · simp [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne him]
    · rfl

/-- Inductive elimination step for `symmWeyl_mem_adjoin_of_support`. -/
private theorem symmWeyl_add_single_mem_adjoin_of_prefix {N m : ℕ} (hm : m + 1 < N)
    (ih : ∀ z : Fin N → ZMod 3, (∀ i : Fin N, m + 1 ≤ (i : ℕ) → z i = 0) →
      symmWeyl N z ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)))
    {y : Fin N → ZMod 3} (hy : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → y i = 0)
    {r : ZMod 3} (hr : r ≠ 0) :
    symmWeyl N (y + Pi.single ⟨m + 1, hm⟩ r) ∈
      Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  let jk : Fin N := ⟨m + 1, hm⟩
  let jm : Fin N := ⟨m, by omega⟩
  have hstep : ∀ (z : Fin N → ZMod 3) (s : ZMod 3),
      (∀ i : Fin N, m + 1 ≤ (i : ℕ) → z i = 0) → z jm ≠ 0 → s ≠ 0 →
      symmWeyl N (z + Pi.single jk s) ∈ S := fun z s hz hzm hs ↦
    symmWeyl_add_mem_of_chainForm_ne_zero (ih z hz) (symmWeyl_single_mem_adjoin N jk s)
      (by rw [chainForm_prefix_single hm hz]; exact mul_ne_zero hzm hs)
  by_cases hym : y jm = 0
  · let em : Fin N → ZMod 3 := Pi.single jm 1
    let b := y + em
    let c := -em + Pi.single jk r
    let y' := y + Pi.single jm 2
    have hbc : b + c = y + Pi.single jk r := by simp [b, c, add_assoc]
    have hbcinv : b - c = y' + Pi.single jk (-r) := by
      ext i; simp [b, c, y', em, Pi.single_apply]; split_ifs <;> ring
    have hne_jm : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → i ≠ jm := fun i hi h ↦ by subst h; simp [jm] at hi
    have hb_mem : symmWeyl N b ∈ S := ih b fun i hi ↦ by
      simp [b, em, Pi.single_eq_of_ne (hne_jm i hi), hy i hi]
    have hc_mem : symmWeyl N c ∈ S :=
      hstep (-em) r (fun i hi ↦ by simp [em, Pi.single_eq_of_ne (hne_jm i hi)]) (by simp [em]) hr
    have hy'_mem : symmWeyl N (b - c) ∈ S :=
      hbcinv ▸ hstep y' (-r) (fun i hi ↦ by simp [y', Pi.single_eq_of_ne (hne_jm i hi), hy i hi])
        (by simp only [y', Pi.add_apply, hym, zero_add, Pi.single_eq_same, ne_eq]; decide)
        (neg_ne_zero.mpr hr)
    set α : ℂ := (cubeRootPow (2 * chainForm (ZMod 3) N b c) : ℂ)
    set γ : ℂ := (cubeRootPow (-(2 * chainForm (ZMod 3) N b c)) : ℂ)
    have hαγ : γ * α = 1 := by
      simp [α, γ, ← Units.val_mul, ← AddChar.map_add_eq_mul]
    have hcomb : symmWeyl N b * symmWeyl N c + (-γ) • symmWeyl N (b - c) =
        α • symmWeyl N (y + Pi.single jk r) := by
      rw [symmWeyl_mul_symmWeyl N b c, hbc, add_assoc, ← add_smul, add_neg_cancel, zero_smul,
        add_zero]
    have hres := S.smul_mem
      (hcomb ▸ S.add_mem (S.mul_mem hb_mem hc_mem) (S.smul_mem hy'_mem (-γ))) γ
    rwa [smul_smul, hαγ, one_smul] at hres
  · exact hstep y r hy hym hr

private theorem symmWeyl_mem_adjoin_of_support (N k : ℕ) :
    ∀ (a : Fin N → ZMod 3), (∀ i : Fin N, k ≤ (i : ℕ) → a i = 0) →
      symmWeyl N a ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  induction k with
  | zero =>
    intro a ha
    have ha0 : a = 0 := funext fun i ↦ ha i (Nat.zero_le _)
    rw [ha0, symmWeyl_zero]
    exact (Algebra.adjoin ℂ (Set.range (cubicProjection N))).smul_mem (Subalgebra.one_mem _) (2 : ℂ)
  | succ k ih =>
    intro a ha
    by_cases hkN : k < N
    · let jk : Fin N := ⟨k, hkN⟩
      set r := a jk
      by_cases hr : r = 0
      · refine ih a fun i hi ↦ ?_
        rcases eq_or_lt_of_le hi with hval | hlt
        · exact (Fin.ext hval.symm : i = jk) ▸ hr
        · exact ha i hlt
      · let d : Fin N → ZMod 3 := Pi.single jk r
        let y : Fin N → ZMod 3 := a - d
        have hy : ∀ i : Fin N, k ≤ (i : ℕ) → y i = 0 := fun i hi ↦ by
          rcases eq_or_lt_of_le hi with hval | hlt
          · have hij : i = jk := Fin.ext hval.symm; subst hij; simp [y, d, r]
          · have hne : i ≠ jk := fun h ↦ by subst h; exact Nat.lt_irrefl _ hlt
            simp [y, d, Pi.single_eq_of_ne hne, ha i hlt]
        rw [show a = y + d by simp [y]]
        rcases k with _ | m
        · rw [show y = 0 from funext fun i ↦ hy i (Nat.zero_le _), zero_add]
          exact symmWeyl_single_mem_adjoin N jk r
        · exact symmWeyl_add_single_mem_adjoin_of_prefix hkN ih hy hr
    · exact ih a fun i _ ↦ absurd i.isLt (by omega)

/-- **The projections `cubicProjection N` generate `cubicFixed N`** as a `ℂ`-algebra. -/
theorem adjoin_range_cubicProjection (N : ℕ) :
    Algebra.adjoin ℂ (Set.range (cubicProjection N)) = cubicFixed N := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  refine le_antisymm (Algebra.adjoin_le_iff.mpr <| by
    rintro _ ⟨j, rfl⟩; exact cubicProjection_mem_cubicFixed j) fun x hx ↦ ?_
  have hsymm : ∀ z : CubicTorus N, z + cubicInversion N z ∈ S := fun z ↦ by
    induction (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).mem_span z using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨a, rfl⟩ := hw
      rw [TwistedMonoidAlgebra.basis_apply, of_eq_weyl, cubicInversion_weyl]
      exact symmWeyl_mem_adjoin_of_support N N a.toAdd fun i hi ↦ absurd i.isLt (not_lt.mpr hi)
    | zero => simp [S.zero_mem]
    | add _ _ _ _ hy hw => rw [map_add, add_add_add_comm]; exact S.add_mem hy hw
    | smul c _ _ hy => rw [map_smul, ← smul_add]; exact S.smul_mem hy c
  have hx2 := hsymm x
  rw [mem_cubicFixed.mp hx, ← two_smul ℂ x] at hx2
  have hres := S.smul_mem hx2 (2 : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at hres

/-- **Surjectivity of `cubicHom`.** For every `m : ℕ`, the comparison homomorphism
`TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` is surjective. -/
theorem cubicHom_surjective (m : ℕ) : Function.Surjective (cubicHom m) := by
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  let Φ : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).val.comp (cubicHom m)
  have hrange : Φ.range = cubicFixed (m - 1) := by
    rw [← Algebra.map_top, ← adjoin_range_e, AlgHom.map_adjoin, ← Set.range_comp]
    let S₁ := Algebra.adjoin ℂ (Set.range (Φ ∘ e (Real.sqrt 3 : ℂ)))
    let S₂ := Algebra.adjoin ℂ (Set.range (cubicProjection (m - 1)))
    have hadj : S₁ = S₂ := le_antisymm
      (Algebra.adjoin_le_iff.mpr <| by
        rintro _ ⟨j, rfl⟩
        simpa [Φ, coe_cubicHom_e] using
          S₂.smul_mem (Algebra.subset_adjoin (Set.mem_range_self j)) (Real.sqrt 3 : ℂ))
      (Algebra.adjoin_le_iff.mpr <| by
        rintro _ ⟨j, rfl⟩
        have hj0 : (Φ ∘ e (Real.sqrt 3 : ℂ)) j ∈ S₁ :=
          Algebra.subset_adjoin (Set.mem_range_self j)
        simp only [Function.comp_apply, Φ, AlgHom.comp_apply, Subalgebra.coe_val,
          coe_cubicHom_e] at hj0
        have hres := S₁.smul_mem hj0 (Real.sqrt 3 : ℂ)⁻¹
        rwa [smul_smul, inv_mul_cancel₀ hsqrt, one_smul] at hres)
    exact hadj.trans (adjoin_range_cubicProjection (m - 1))
  intro y
  obtain ⟨x, hx⟩ : (y : CubicTorus (m - 1)) ∈ Φ.range := hrange.symm ▸ y.property
  exact ⟨x, Subtype.ext hx⟩

end TauCeti.TemperleyLieb
