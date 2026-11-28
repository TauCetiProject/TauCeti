/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.GradedComul

import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Filtered and graded bialgebra properties of universal enveloping algebras

For an arbitrary `Γ`-graded Lie algebra `L`, the bialgebra comultiplication
`Δ : U(L) → U(L) ⊗[R] U(L)` preserves total Lie degree (`comul_mem_tensorTotalDegree`). When `Γ`
carries an integer-valued degree functional `d : Γ →+ ℤ` and all negative-degree pieces of `L`
vanish, `Δ` preserves the total-degree filtration (`degreeFiltration_le_comap_comulAlgHom`), and
the first ideals of the enveloping degree filtration and the induced tensor-product filtration lie
in the kernels of their respective counits.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section Graded

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The total-degree-`m` submodule `⨆ p₁ + p₂ = m, U_{p₁} ⊗ U_{p₂}` of `U(L) ⊗[R] U(L)`. -/
def tensorTotalDegree (m : Γ) : Submodule R (U ⊗[R] U) :=
  InternalGrading.tensorProductPiece (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) m

/-- Unfolding characterization of `tensorTotalDegree`. -/
theorem tensorTotalDegree_def (m : Γ) :
    tensorTotalDegree ℒ m = ⨆ p : Γ × Γ, ⨆ _ : p.1 + p.2 = m,
      InternalGrading.tensorProductBidegreePiece
        (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) p :=
  InternalGrading.tensorProductPiece_def _ _ m

/-- `tensorTotalDegree` agrees with the `InternalGrading.tensorProduct` pieces on the enveloping
algebra grading. -/
theorem tensorTotalDegree_eq_internalGrading_piece [DecidableEq Γ] [GradedLieAlgebra ℒ] (m : Γ) :
    tensorTotalDegree ℒ m =
      ((InternalGrading.ofDecomposition (homogeneousSubmodule ℒ)).tensorProduct
        (InternalGrading.ofDecomposition (homogeneousSubmodule ℒ))).piece m := by
  rw [tensorTotalDegree_def]
  refine le_antisymm ?_
    (InternalGrading.tensorProduct_piece_le_of_add_eq _ _ fun p q hpq x hx y hy => ?_)
  · refine iSup_le fun p => iSup_le fun hp => ?_
    rw [InternalGrading.tensorProductBidegreePiece_def]
    refine Submodule.map₂_le.2 fun x hx y hy => ?_
    simpa only [hp, TensorProduct.mk_apply] using
      InternalGrading.tmul_mem_tensorProduct_ofDecomposition
        (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) hx hy
  · rw [InternalGrading.ofDecomposition_piece] at hx hy
    refine Submodule.mem_iSup_of_mem (p, q) (Submodule.mem_iSup_of_mem hpq ?_)
    rw [InternalGrading.tensorProductBidegreePiece_def]
    exact Submodule.apply_mem_map₂ (TensorProduct.mk R U U) hx hy

/-- Multiplication preserves the total-degree grading on `U(L) ⊗[R] U(L)`. -/
theorem mul_mem_tensorTotalDegree [DecidableEq Γ] [GradedLieAlgebra ℒ] {m₁ m₂ : Γ}
    {x y : U ⊗[R] U} (hx : x ∈ tensorTotalDegree ℒ m₁) (hy : y ∈ tensorTotalDegree ℒ m₂) :
    x * y ∈ tensorTotalDegree ℒ (m₁ + m₂) := by
  rw [tensorTotalDegree_eq_internalGrading_piece] at hx hy ⊢
  exact SetLike.mul_mem_graded hx hy

/-- Comultiplication sends homogeneous elements of degree `m` into total tensor degree `m`. -/
theorem comul_mem_tensorTotalDegree [DecidableEq Γ] [GradedLieAlgebra ℒ] {m : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a ∈ tensorTotalDegree ℒ m := by
  rw [tensorTotalDegree_eq_internalGrading_piece]
  simpa only [add_zero] using (isHomogeneous_comul ℒ).map_mem ha

end Graded

section Filtered

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ) [DecidableEq Γ] [GradedLieAlgebra ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d

/-- When all negative-degree pieces of `L` vanish, every total-degree tensor piece of `d`-degree
at least `k` lies in the order-`k` tensor degree-filtration ideal. -/
theorem tensorTotalDegree_le_tensorProduct_ideal (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {m : Γ} {k : ℕ} (hm : (k : ℤ) ≤ d m) :
    tensorTotalDegree ℒ m ≤ (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal k).restrictScalars R := by
  rw [tensorTotalDegree_eq_internalGrading_piece]
  exact tensorProduct_piece_le_tensorProduct_ideal ℒ d hneg hm

/-- When all negative-degree pieces of `L` vanish, comultiplication preserves the total-degree
filtration on `U(L)` (derived from degree preservation `comul_mem_tensorTotalDegree`). -/
theorem degreeFiltration_le_comap_comulAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (𝓕 hneg).ideal k ≤
      (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) :=
  (degreeFiltration_ideal_le_iff ℒ d hneg k _).mpr fun _ hm _ ha =>
    tensorTotalDegree_le_tensorProduct_ideal ℒ d hneg hm (comul_mem_tensorTotalDegree ℒ ha)

/-- The first degree-filtration ideal lies in the kernel of the enveloping counit. -/
theorem degreeFiltration_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (𝓕 hneg).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) :=
  fun _ hu => (HopfIdeal.mem_augmentation R U).mp
    (HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos hu))

/-- The first tensor degree-filtration ideal lies in the kernel of the tensor counit. -/
theorem tensorProduct_degreeFiltration_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal 1 ≤
      RingHom.ker (Bialgebra.counitAlgHom R (U ⊗[R] U)) := by
  intro t ht
  refine ((tensorFiltrationTail_le_iff (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (P := (RingHom.ker (Bialgebra.counitAlgHom R (U ⊗[R] U))).restrictScalars R)).mpr
    fun a b hab u hu v hv => ?_) (((𝓕 hneg).mem_tensorProduct_ideal_iff R (𝓕 hneg)).mp ht)
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, Bialgebra.counitAlgHom_apply,
    TensorProduct.counit_tmul]
  have hzero {w : U} (hw : w ∈ (𝓕 hneg).ideal 1) : Coalgebra.counit (R := R) w = 0 := by
    simpa [Bialgebra.counitAlgHom_apply] using degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg hw
  rcases Nat.lt_or_ge 0 a with ha | ha
  · simp [hzero ((𝓕 hneg).antitone ha hu)]
  · simp [hzero ((𝓕 hneg).antitone (by omega) hv)]

end Filtered

end TauCeti.UniversalEnvelopingAlgebra
