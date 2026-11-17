/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TensorProduct.Module
public import TauCeti.RingTheory.Semisimple.IsotypicTensor
-- Non-public: flatness of a vector space is used only inside the proof.
import Mathlib.RingTheory.Flat.Basic

/-!
# Finite-dimensional simple modules over a tensor product of algebras

Let `A` and `B` be algebras over an algebraically closed field `k`. A finite-dimensional simple
module `M` over `A ⊗[k] B` is an exterior tensor product `V ⊗[k] W` of a finite-dimensional
simple `A`-module `V` and a finite-dimensional simple `B`-module `W`
(`TauCeti.finiteCornerFactorization`). This is the finite-dimensional step of Flath's
factorization of irreducible admissible representations of a restricted tensor product
(Flath, Theorem 1 and its proof).

The proof restricts `M` to the commuting actions of the two factors
(`TauCeti.Algebra.TensorProduct.moduleLeft` and `moduleRight`). A simple `A`-submodule `V` exists
by finite-dimensionality, and its isotypic component is stable under `B`, so it is all of `M`.
Evaluation identifies `V ⊗[k] (V →ₗ[A] M)` with `M` (`TauCeti.isotypicTensorEquiv`, which uses
Schur's lemma and density over the algebraically closed field `k`). The multiplicity space
`W = V →ₗ[A] M` carries the action of `B` on the target, evaluation intertwines the action of
`A ⊗[k] B` on `M` with `TauCeti.BialgebraModule.tensorPairAction`, and a dimension count shows
that `W` is simple.

Algebraic closedness cannot be dropped: `ℂ ⊗[ℝ] ℂ ≅ ℂ × ℂ` has the simple module `ℂ` of real
dimension `2`, while a tensor product of two simple `ℂ`-modules over `ℝ` has real dimension `4`.

## Main results

* `TauCeti.eq_bot_or_eq_top_of_tmul_smul_mem`: a subspace of a simple `A ⊗[k] B`-module stable
  under both factors is `⊥` or `⊤`.
* `TauCeti.finiteCornerFactorization`: **a finite-dimensional simple `A ⊗[k] B`-module is
  `V ⊗[k] W`** for finite-dimensional simple modules `V` over `A` and `W` over `B`.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. 33, Part 1 (1979), 179–183,
  Theorem 1.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u

section TensorModule

variable {k A B M : Type*} [CommSemiring k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module (A ⊗[k] B) M]

/-- **A subspace stable under both factors.** In a simple `A ⊗[k] B`-module, a `k`-subspace
stable under the actions of `a ⊗ 1` and of `1 ⊗ b` is `⊥` or `⊤`: these elements generate
`A ⊗[k] B` as a ring. -/
theorem eq_bot_or_eq_top_of_tmul_smul_mem [IsSimpleModule (A ⊗[k] B) M] (p : Submodule k M)
    (hA : ∀ (a : A), ∀ m ∈ p, (a ⊗ₜ[k] (1 : B)) • m ∈ p)
    (hB : ∀ (b : B), ∀ m ∈ p, ((1 : A) ⊗ₜ[k] b) • m ∈ p) : p = ⊥ ∨ p = ⊤ := by
  let q : Submodule (A ⊗[k] B) M :=
    { p.toAddSubmonoid with
      smul_mem' := fun t m hm ↦ by
        induction t using TensorProduct.inductionOn with
        | tmul a b =>
          have h : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] b) := by
            simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [h, mul_smul]
          exact hA a _ (hB b m hm)
        | add t u ht hu => rw [add_smul]; exact p.add_mem ht hu }
  refine (eq_bot_or_eq_top q).imp (fun h ↦ ?_) (fun h ↦ ?_)
  · refine eq_bot_iff.mpr fun m hm ↦ ?_
    have hm' : m ∈ q := hm
    rw [h, Submodule.mem_bot] at hm'
    exact (Submodule.mem_bot _).mpr hm'
  · refine eq_top_iff.mpr fun m _ ↦ ?_
    have hm' : m ∈ q := h ▸ Submodule.mem_top
    exact hm'

end TensorModule

variable {k A B : Type*} {M : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [AddCommGroup M] [Module k M]

/-! ### Two commuting actions with no common invariant subspace -/

section Commuting

variable [Module A M] [Module B M] [SMulCommClass A B M] [IsScalarTower k A M]
variable {S : Type*} [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]

omit [Algebra k B] in
/-- The isotypic component of a simple submodule is stable under the commuting action, so it is
everything. -/
private theorem isotypicComponent_eq_top_of_commuting
    (hM : ∀ p : Submodule k M, (∀ (a : A), ∀ m ∈ p, a • m ∈ p) →
      (∀ (b : B), ∀ m ∈ p, b • m ∈ p) → p = ⊥ ∨ p = ⊤)
    (V : Submodule A M) [IsSimpleModule A V] : isotypicComponent A M V = ⊤ := by
  have : SMulCommClass B A M := SMulCommClass.symm A B M
  have h := hM ((isotypicComponent A M V).restrictScalars k)
    (fun a m hm ↦ (isotypicComponent A M V).smul_mem a hm)
    (fun b m hm ↦ (DistribSMul.toLinearMap A M b).le_comap_isotypicComponent V hm)
  refine (Submodule.restrictScalars_eq_top_iff k A M).mp
    (h.resolve_left fun h ↦ ?_)
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  rw [Submodule.restrictScalars_eq_bot_iff k A M] at h
  exact (Submodule.nontrivial_iff_ne_bot.mp this) (eq_bot_iff.mpr (h ▸ V.le_isotypicComponent))

/-- Evaluation `S ⊗ W' → M` on a subspace `W'` of the multiplicity space has range stable under
both actions when `W'` is stable under `B`. -/
private theorem range_lTensor_eval_stable [IsScalarTower k B M] (W' : Submodule B (S →ₗ[A] M)) :
    let r := (isotypicEval k).restrictScalars k ∘ₗ (W'.restrictScalars k).subtype.lTensor S
    (∀ (a : A), ∀ m ∈ LinearMap.range r, a • m ∈ LinearMap.range r) ∧
      ∀ (b : B), ∀ m ∈ LinearMap.range r, b • m ∈ LinearMap.range r := by
  intro r
  have hr_tmul : ∀ (v : S) (f : W'.restrictScalars k), r (v ⊗ₜ f) = (f : S →ₗ[A] M) v :=
    fun v f ↦ isotypicEval_tmul k v (f : S →ₗ[A] M)
  constructor
  · rintro a _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul v f => exact ⟨(a • v) ⊗ₜ f, by rw [hr_tmul, hr_tmul, map_smul]⟩
    | add x y hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  · rintro b _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul v f =>
      exact ⟨v ⊗ₜ ⟨b • (f : S →ₗ[A] M), W'.smul_mem b f.2⟩, by rw [hr_tmul, hr_tmul]; rfl⟩
    | add x y hx hy => rw [map_add, smul_add]; exact add_mem hx hy

/-- The multiplicity space of a simple module `S` in an `S`-isotypic module with a commuting
action and no common invariant subspace is a simple module for that action. -/
private theorem isSimpleModule_linearMap_of_commuting [IsScalarTower k B M] [IsSimpleModule A S]
    [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k M] [Nontrivial M]
    (hM : ∀ p : Submodule k M, (∀ (a : A), ∀ m ∈ p, a • m ∈ p) →
      (∀ (b : B), ∀ m ∈ p, b • m ∈ p) → p = ⊥ ∨ p = ⊤)
    (htop : isotypicComponent A M S = ⊤) : IsSimpleModule B (S →ₗ[A] M) := by
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  have : FiniteDimensional k (S →ₗ[A] M) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k A S M k)
      (LinearMap.restrictScalars_injective _)
  have hM_rank : finrank k M = finrank k S * finrank k (S →ₗ[A] M) := by
    rw [← ((isotypicTensorEquiv k htop).restrictScalars k).finrank_eq,
      Module.finrank_tensorProduct]
  have : Nontrivial (S →ₗ[A] M) := Module.finrank_pos_iff.mp
    (Nat.pos_of_mul_pos_left (hM_rank ▸ Module.finrank_pos : 0 < _))
  refine { eq_bot_or_eq_top := fun W' ↦ ?_ }
  have hr : Function.Injective
      ((isotypicEval k).restrictScalars k ∘ₗ (W'.restrictScalars k).subtype.lTensor S) :=
    (isotypicEval_injective k).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hrank := LinearMap.finrank_range_of_inj hr
  rw [Module.finrank_tensorProduct] at hrank
  have hS0 : 0 < finrank k S := Module.finrank_pos
  obtain ⟨hA, hB⟩ := range_lTensor_eval_stable (k := k) W'
  rcases hM _ hA hB with h | h
  · left
    rw [h, finrank_bot, eq_comm, mul_eq_zero, Submodule.finrank_eq_zero] at hrank
    exact (Submodule.restrictScalars_eq_bot_iff k B _).mp (hrank.resolve_left hS0.ne')
  · right
    rw [h, finrank_top, hM_rank] at hrank
    exact (Submodule.restrictScalars_eq_top_iff k B _).mp
      (Submodule.eq_top_of_finrank_eq (Nat.eq_of_mul_eq_mul_left hS0 hrank).symm)

end Commuting

variable (k A B M) [Module (A ⊗[k] B) M]

/-- **Flath's finite-dimensional factorization.** A finite-dimensional simple module `M` over
`A ⊗[k] B`, for algebras `A` and `B` over an algebraically closed field `k`, is the exterior tensor
product `V ⊗[k] W` of a finite-dimensional simple `A`-module `V` and a finite-dimensional simple
`B`-module `W`: some `k`-linear isomorphism `V ⊗[k] W ≃ M` intertwines the action
`TauCeti.BialgebraModule.tensorPairAction` with the action on `M`.

The factors are `V`, a simple `A`-submodule of `M`, and its multiplicity space `V →ₗ[A] M`, on
which `B` acts through `M`. -/
theorem finiteCornerFactorization [IsScalarTower k (A ⊗[k] B) M] [IsAlgClosed k]
    [FiniteDimensional k M] [IsSimpleModule (A ⊗[k] B) M] :
    ∃ (V W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module A V)
      (_ : IsScalarTower k A V) (_ : AddCommGroup W) (_ : Module k W) (_ : Module B W)
      (_ : IsScalarTower k B W), IsSimpleModule A V ∧ IsSimpleModule B W ∧
      FiniteDimensional k V ∧ FiniteDimensional k W ∧
      ∃ e : V ⊗[k] W ≃ₗ[k] M,
        ∀ (t : A ⊗[k] B) x, e (BialgebraModule.tensorPairAction k V W t x) = t • e x := by
  let _ := Algebra.TensorProduct.moduleLeft (k := k) (A := A) (B := B) M
  let _ := Algebra.TensorProduct.moduleRight (k := k) (A := A) (B := B) M
  have := Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := A) (B := B) M
  have := Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := A) (B := B) M
  have := Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := A) (B := B) M
  have : Nontrivial M := IsSimpleModule.nontrivial (A ⊗[k] B) M
  have : IsArtinian A M := isArtinian_of_tower k inferInstance
  -- A simple `A`-submodule `V` of `M`; its isotypic component is everything.
  obtain ⟨V, hV⟩ := IsAtomic.exists_atom (Submodule A M)
  have : IsSimpleModule A V := isSimpleModule_iff_isAtom.mpr hV
  have : FiniteDimensional k V :=
    Module.Finite.of_injective (V.subtype.restrictScalars k) Subtype.val_injective
  have hM := eq_bot_or_eq_top_of_tmul_smul_mem (k := k) (A := A) (B := B) (M := M)
  have htop := isotypicComponent_eq_top_of_commuting (k := k) (B := B) hM V
  let E := (isotypicTensorEquiv k htop).restrictScalars k
  have hE : ∀ x, E x = isotypicEval k x := isotypicTensorEquiv_apply k htop
  refine ⟨V, V →ₗ[A] M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    isSimpleModule_linearMap_of_commuting hM htop, inferInstance,
    .of_injective (LinearMap.restrictScalarsₗ k A V M k) (LinearMap.restrictScalars_injective _),
    E, fun t x ↦ ?_⟩
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => rw [map_add, LinearMap.add_apply, map_add, ht, hu, add_smul]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
    | tmul v f =>
      rw [BialgebraModule.tensorPairAction_tmul, hE, hE, isotypicEval_tmul, isotypicEval_tmul,
        LinearMap.smul_apply, map_smul]
      have h : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] b) := by
        simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h, mul_smul]
      exact (smul_comm a b (f v)).symm

end TauCeti
