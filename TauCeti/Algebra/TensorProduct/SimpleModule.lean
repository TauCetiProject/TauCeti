/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TensorProduct.Module
public import TauCeti.RingTheory.Semisimple.IsotypicTensor

/-!
# Finite-dimensional simple modules over a tensor product of algebras

Let `A` and `B` be algebras over an algebraically closed field `k`. A finite-dimensional simple
module `M` over `A ⊗[k] B` is an exterior tensor product `V ⊗[k] W` of a finite-dimensional
simple `A`-module `V` and a finite-dimensional simple `B`-module `W`
(`TauCeti.exists_tensorProduct_equiv_of_isSimpleModule`). This is the finite-dimensional step of
Flath's factorization of irreducible admissible representations of a restricted tensor product
(Flath, Theorem 1 and its proof).

The proof restricts `M` to the commuting actions of the two factors
(`TauCeti.Algebra.TensorProduct.moduleLeft` and `moduleRight`). A simple `A`-submodule `V` exists
by finite-dimensionality, and its isotypic component is stable under `B`, so it is all of `M`.
Evaluation identifies `V ⊗[k] (V →ₗ[A] M)` with `M` (`TauCeti.isotypicTensorEquiv`, which uses
Schur's lemma and density over the algebraically closed field `k`). The multiplicity space
`W = V →ₗ[A] M` carries the action of `B` on the target, evaluation intertwines the action of
`A ⊗[k] B` on `M` with `TauCeti.BialgebraModule.tensorPairAction`, and a dimension count shows
that `W` is simple (`TauCeti.isotypicComponent_eq_top_of_commuting` and
`TauCeti.isSimpleModule_linearMap_of_commuting`).

Algebraic closedness cannot be dropped: `ℂ ⊗[ℝ] ℂ ≅ ℂ × ℂ` has the simple module `ℂ` of real
dimension `2`, while a tensor product of two simple `ℂ`-modules over `ℝ` has real dimension `4`.

## Main results

* `Submodule.eq_bot_or_eq_top_of_tmul_smul_mem`: a subspace of a simple `A ⊗[k] B`-module stable
  under both factors is `⊥` or `⊤`.
* `TauCeti.exists_tensorProduct_equiv_of_isSimpleModule`: **a finite-dimensional simple
  `A ⊗[k] B`-module is `V ⊗[k] W`** for finite-dimensional simple modules `V` over `A` and `W`
  over `B`.

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
theorem _root_.Submodule.eq_bot_or_eq_top_of_tmul_smul_mem [IsSimpleModule (A ⊗[k] B) M]
    (p : Submodule k M)
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


variable (k A B M) [Module (A ⊗[k] B) M]

/-- **Flath's finite-dimensional factorization** (existence of the factors). A
finite-dimensional simple module `M` over `A ⊗[k] B`, for algebras `A` and `B` over an
algebraically closed field `k`, is the exterior tensor product `V ⊗[k] W` of a
finite-dimensional simple `A`-module `V` and a finite-dimensional simple `B`-module `W`: some
`k`-linear isomorphism `V ⊗[k] W ≃ M` intertwines the action
`TauCeti.BialgebraModule.tensorPairAction` with the action on `M`.

The factors are `V`, a simple `A`-submodule of `M`, and its multiplicity space `V →ₗ[A] M`, on
which `B` acts through `M`. -/
theorem exists_tensorProduct_equiv_of_isSimpleModule [IsScalarTower k (A ⊗[k] B) M] [IsAlgClosed k]
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
  -- No `k`-subspace other than `⊥` and `⊤` is stable under both restricted actions.
  have hM : ∀ p : Submodule k M, (∀ (a : A), ∀ m ∈ p, a • m ∈ p) →
      (∀ (b : B), ∀ m ∈ p, b • m ∈ p) → p = ⊥ ∨ p = ⊤ := fun p hA hB ↦
    p.eq_bot_or_eq_top_of_tmul_smul_mem (A := A) (B := B)
      (fun a m hm ↦ by rw [← Algebra.TensorProduct.smul_moduleLeft]; exact hA a m hm)
      (fun b m hm ↦ by rw [← Algebra.TensorProduct.smul_moduleRight]; exact hB b m hm)
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
      rw [h, mul_smul, ← Algebra.TensorProduct.smul_moduleRight,
        ← Algebra.TensorProduct.smul_moduleLeft]
      exact (smul_comm a b (f v)).symm

end TauCeti
