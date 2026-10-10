/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Continuation
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Parametrized cocycles and the chain homotopy between continuation maps

A **parametrized cocycle** between two continuation cocycles `ν₀ ν₁ : mP → mQ` (the source's
Definition 1.11) is a matrix `h x y ∈ 𝒜 (indQ y - ind x - 1)` with
`d (h x y) = ν₁ x y - ν₀ x y + Σ_z (-1) ^ (ind x - ind z) • (mP x z * h z y)
  + Σ_z (-1) ^ (ind x - indQ z) • (h x z * mQ z y)`.
It induces, for every differential graded right module `(ℳ, dM)`, the map
`homotopyMap h ℳ : ℳ ⊗ ⟨P⟩ → ℳ ⊗ ⟨Q⟩`, `𝔥 (α ⊗ x) = (-1) ^ |α| Σ_y (α · h x y) ⊗ y`, which lowers
the total degree by one and is a **chain homotopy** between the two continuation maps:
`Ψ¹ - Ψ⁰ = D⁻ ∘ 𝔥 + 𝔥 ∘ D⁺` (`homotopyMap_twistedDifferential`).  So homotopic continuation
cocycles induce chain homotopic continuation maps.

As in `TauCeti.Algebra.Homology.DG.Twisted.Continuation`, the map is defined for any matrix, the
theorems take the degree and parametrized equations as hypotheses, and the bundled
`ParametrizedCocycle` comes last.  The Koszul sign `(-1) ^ |α|` is the Koszul twist of parameter
one of `TauCeti.Algebra.Homology.DG.Twisted.Complex`.

## Main definitions

* `TauCeti.homotopyMap h ℳ`: the map `(P → M) →ₗ[R] (Q → M)` of a matrix `h`.
* `TauCeti.ParametrizedCocycle ν₀ ν₁`: parametrized cocycles between continuation cocycles.

## Main results

* `TauCeti.homotopyMap_mem_twistedTotalGrading`: the homotopy map lowers the total degree by one.
* `TauCeti.homotopyMap_twistedDifferential`: the chain homotopy identity
  `Ψ¹ - Ψ⁰ = D⁻ ∘ 𝔥 + 𝔥 ∘ D⁺` for a differential graded right module.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definition 1.11.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–4.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

section Map

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Semiring A]
  {P Q : Type uP} [Fintype P]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The map `ℳ ⊗ ⟨P⟩ → ℳ ⊗ ⟨Q⟩` of a matrix `h : P → Q → A` with the Koszul sign, on the models
`P → M` and `Q → M`: its `y`-component is `(𝔥 f) y = Σ_x op (h x y) • ε (f x)`, where `ε` is the
Koszul twist of parameter one, so that on a homogeneous elementary tensor
`𝔥 (α ⊗ x) = (-1) ^ |α| Σ_y (α · h x y) ⊗ y` (`homotopyMap_single`). -/
noncomputable def homotopyMap (h : P → Q → A) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ] : (P → M) →ₗ[R] (Q → M) where
  toFun f y := ∑ x, op (h x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x)
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext y
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum, smul_comm r]

variable (h : P → Q → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]

@[simp]
theorem homotopyMap_apply (f : P → M) (y : Q) :
    homotopyMap h ℳ f y =
      ∑ x, op (h x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) :=
  (rfl)

end Map

section Single

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Semiring A]
  {P Q : Type uP} [Fintype P]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  (h : P → Q → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]

/-- The `y`-component of the homotopy map of a homogeneous elementary tensor `α ⊗ x`, with `α` of
degree `q`. -/
theorem homotopyMap_single_apply [DecidableEq P] (x : P) {q : ℤ} {α : M} (hα : α ∈ ℳ q) (y : Q) :
    homotopyMap h ℳ (Pi.single x α) y = q.negOnePow • (op (h x y) • α) := by
  -- The Koszul twist of parameter one acts on `α` by the `ℤˣ`-scalar `q.negOnePow`.
  have hα' : α ∈ (InternalGrading.ofDecomposition ℳ).piece q := by
    rwa [InternalGrading.ofDecomposition_piece]
  have hε : (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α = q.negOnePow • α := by
    rw [InternalGrading.koszulTwist_one_apply_of_mem _ hα',
      negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  simp only [homotopyMap_apply, Pi.single_apply, apply_ite, map_zero, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hε, smul_comm (op (h x y)) q.negOnePow]

/-- The homotopy map of a homogeneous elementary tensor:
`𝔥 (α ⊗ x) = (-1) ^ |α| Σ_y (α · h x y) ⊗ y`. -/
theorem homotopyMap_single [Fintype Q] [DecidableEq P] [DecidableEq Q] (x : P) {q : ℤ} {α : M}
    (hα : α ∈ ℳ q) :
    homotopyMap h ℳ (Pi.single x α) = ∑ y, Pi.single y (q.negOnePow • (op (h x y) • α)) := by
  funext y'
  rw [homotopyMap_single_apply h x hα, Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Single

section Properties

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ}
  [Fintype P] [Fintype Q] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  (h : P → Q → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

omit [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M] [DirectSum.Decomposition ℳ] [Fintype P]
  [Fintype Q] in
/-- A homogeneous element `α` of degree `q`, multiplied by `a` of degree `e`, has degree
`q + e`. -/
theorem op_smul_mem_of_mem_graded' {e : ℤ} {a : A} (ha : a ∈ 𝒜 e) {q : ℤ} {α : M}
    (hα : α ∈ ℳ q) : op a • α ∈ ℳ (q + e) := by
  have hop : op a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece e := by
    rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
    exact ha
  have := SetLike.GradedSMul.smul_mem hop hα
  rwa [vadd_eq_add, add_comm] at this

omit [IsScalarTower R Aᵐᵒᵖ M] [Fintype Q] in
/-- The homotopy map of a matrix with homogeneous entries of degree `indQ y - ind x - 1` lowers
the total degree by one. -/
theorem homotopyMap_mem_twistedTotalGrading (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - ind x - 1))
    {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    homotopyMap h ℳ f ∈ twistedTotalGrading ℳ indQ (n - 1) := by
  rw [mem_twistedTotalGrading_iff] at hf ⊢
  intro y
  rw [homotopyMap_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hfx : f x ∈ (InternalGrading.ofDecomposition ℳ).piece (n + ind x) := by
    rw [InternalGrading.ofDecomposition_piece]
    exact hf x
  have hε : (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) ∈ ℳ (n + ind x) := by
    have := InternalGrading.koszulTwist_mem_piece _ hfx 1
    rwa [InternalGrading.ofDecomposition_piece] at this
  have := op_smul_mem_of_mem_graded' (ℳ := ℳ) (hh x y) hε
  convert this using 2
  ring

variable (mP : P → P → A) (mQ : Q → Q → A) (ν₀ ν₁ : P → Q → A) (dM : M →ₗ[R] M)

/-- **The chain homotopy identity**: for a matrix `h` with homogeneous entries which satisfies the
parametrized equation between the continuation cocycles `ν₀` and `ν₁`, and a differential graded
right module `(ℳ, dM)`, `Ψ¹ - Ψ⁰ = D⁻ ∘ 𝔥 + 𝔥 ∘ D⁺`. -/
theorem homotopyMap_twistedDifferential (hh : ∀ x y, h x y ∈ 𝒜 (indQ y - ind x - 1))
    (hm : ∀ x y, mP x y ∈ 𝒜 (ind y - ind x + 1))
    (hp : ∀ x y, d (h x y) = ν₁ x y - ν₀ x y + ∑ z, (ind x - ind z).negOnePow • (mP x z * h z y) +
      ∑ z, (ind x - indQ z).negOnePow • (h x z * mQ z y))
    (hM : IsDGRightModule hA ℳ dM) (f : P → M) :
    continuationMap R M ν₁ f - continuationMap R M ν₀ f =
      twistedDifferential mQ ℳ dM (homotopyMap h ℳ f) +
        homotopyMap h ℳ (twistedDifferential mP ℳ dM f) := by
  classical
  suffices key : ∀ (x : P) {q : ℤ} {α : M}, α ∈ ℳ q →
      continuationMap R M ν₁ (Pi.single x α) - continuationMap R M ν₀ (Pi.single x α) =
        twistedDifferential mQ ℳ dM (homotopyMap h ℳ (Pi.single x α)) +
          homotopyMap h ℳ (twistedDifferential mP ℳ dM (Pi.single x α)) by
    rw [← Finset.univ_sum_single f]
    simp only [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    generalize f x = α
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous i α => exact key x α.2
    | add a b ha hb =>
      simp only [Pi.single_add, map_add] at ha hb ⊢
      rw [add_sub_add_comm, ha, hb]
      abel
  intro x q α hα
  funext w
  have hdα : dM α ∈ ℳ (q + 1) := hM.isHomogeneous.map_mem hα
  have hγ : ∀ y, q.negOnePow • (op (h x y) • α) ∈ ℳ (q + (indQ y - ind x - 1)) := fun y ↦
    Submodule.smul_of_tower_mem _ _ (op_smul_mem_of_mem_graded' (hh x y) hα)
  have hδ : ∀ z, q.negOnePow • (op (mP x z) • α) ∈ ℳ (q + (ind z - ind x + 1)) := fun z ↦
    Submodule.smul_of_tower_mem _ _ (op_smul_mem_of_mem_graded' (hm x z) hα)
  -- The two continuation maps.
  have hL : (continuationMap R M ν₁ (Pi.single x α) - continuationMap R M ν₀ (Pi.single x α)) w =
      op (ν₁ x w) • α - op (ν₀ x w) • α := by
    simp only [Pi.sub_apply, continuationMap_single_apply]
  -- `D⁻ ∘ 𝔥`.
  have hR₁ : twistedDifferential mQ ℳ dM (homotopyMap h ℳ (Pi.single x α)) w =
      dM (q.negOnePow • (op (h x w) • α)) +
        ∑ y, (q + (indQ y - ind x - 1)).negOnePow •
          (op (mQ y w) • (q.negOnePow • (op (h x y) • α))) := by
    rw [homotopyMap_single h x hα, map_sum, Finset.sum_apply]
    simp only [fun y ↦ twistedDifferential_single_apply mQ dM y w (hγ y), Finset.sum_add_distrib,
      Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- `𝔥 ∘ D⁺`.
  have hR₂ : homotopyMap h ℳ (twistedDifferential mP ℳ dM (Pi.single x α)) w =
      (q + 1).negOnePow • (op (h x w) • dM α) +
        ∑ z, (q + (ind z - ind x + 1)).negOnePow •
          (op (h z w) • (q.negOnePow • (op (mP x z) • α))) := by
    rw [twistedDifferential_single mP dM x hα, map_add, map_sum, Pi.add_apply, Finset.sum_apply,
      homotopyMap_single_apply h x hdα w]
    simp only [fun z ↦ homotopyMap_single_apply h z (hδ z) w]
  set SQ := ∑ y, (ind x - indQ y).negOnePow • (op (h x y * mQ y w) • α) with hSQ_def
  set SP := ∑ z, (ind x - ind z).negOnePow • (op (mP x z * h z w) • α) with hSP_def
  have hSQ : ∑ y, (q + (indQ y - ind x - 1)).negOnePow •
      (op (mQ y w) • (q.negOnePow • (op (h x y) • α))) = -SQ := by
    rw [hSQ_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hexp : q + (indQ y - ind x - 1) + q =
        (ind x - indQ y) + 1 + 2 * (indQ y - ind x - 1 + q) := by
      ring
    have hsign : (q + (indQ y - ind x - 1)).negOnePow * q.negOnePow =
        -(ind x - indQ y).negOnePow := by
      rw [← Int.negOnePow_add, hexp, Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_two_mul,
        mul_one]
    rw [smul_comm (op (mQ y w)) q.negOnePow, smul_smul, hsign, op_mul, mul_smul, Units.neg_smul]
  have hSP : ∑ z, (q + (ind z - ind x + 1)).negOnePow •
      (op (h z w) • (q.negOnePow • (op (mP x z) • α))) = -SP := by
    rw [hSP_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have hexp : q + (ind z - ind x + 1) + q = (ind x - ind z) + 1 + 2 * (ind z - ind x + q) := by
      ring
    have hsign : (q + (ind z - ind x + 1)).negOnePow * q.negOnePow =
        -(ind x - ind z).negOnePow := by
      rw [← Int.negOnePow_add, hexp, Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_two_mul,
        mul_one]
    rw [smul_comm (op (h z w)) q.negOnePow, smul_smul, hsign, op_mul, mul_smul, Units.neg_smul]
  have hd : dM (q.negOnePow • (op (h x w) • α)) =
      q.negOnePow • (op (h x w) • dM α) + op (d (h x w)) • α := by
    rw [LinearMap.map_smul_of_tower, hM.leibniz hα (h x w), smul_add, smul_smul, Int.units_mul_self,
      one_smul]
  have hq : (q + 1).negOnePow • (op (h x w) • dM α) = -(q.negOnePow • (op (h x w) • dM α)) := by
    rw [Int.negOnePow_succ, Units.neg_smul]
  have hdh : op (d (h x w)) • α = (op (ν₁ x w) • α - op (ν₀ x w) • α) + SP + SQ := by
    rw [hp x w, op_add, op_add, op_sub, add_smul, add_smul, sub_smul, Finset.op_sum, Finset.op_sum,
      Finset.sum_smul, Finset.sum_smul]
    simp only [op_smul]
    simp only [smul_assoc, hSP_def, hSQ_def]
  rw [Pi.add_apply, hL, hR₁, hR₂, hSQ, hSP, hd, hq, hdh]
  abel

end Properties

end TauCeti
