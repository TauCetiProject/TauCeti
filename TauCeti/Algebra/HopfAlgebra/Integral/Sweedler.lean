/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Decomposition
public import TauCeti.Algebra.HopfAlgebra.Integral
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
import TauCeti.Algebra.Coalgebra.Comodule.Schur

/-!
# Sweedler's invariant integral on cosemisimple bialgebras

Every bialgebra `A` over a field `k` that is spanned by its simple matrix-coefficient submodules—in
particular, every linearly reductive bialgebra—is the internal direct sum of its distinct simple
coefficient spaces, with the line `k · 1` appearing as the coefficient space of the trivial
rank-one comodule (`TauCeti.Comodule.span_singleton_one_mem_simpleCoefficientSubmodules`).
Projecting onto `k · 1` via the counit and annihilating all nontrivial simple blocks defines
Sweedler's normalized two-sided invariant integral `TauCeti.sweedlerIntegral`.

## Main declarations

* `TauCeti.sweedlerIntegral`: the normalized two-sided invariant integral on a bialgebra over a
  field spanned by its simple coefficient submodules, with
  `TauCeti.isLeftInvariantIntegral_sweedlerIntegral` and
  `TauCeti.isRightInvariantIntegral_sweedlerIntegral`.
* `TauCeti.Coalgebra.IsLinearlyReductive.existsUnique_twoSidedInvariantIntegral`: existence and
  uniqueness of a normalized two-sided invariant integral on a linearly reductive bialgebra.

## References

* M. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Chapter XIV.
-/

public noncomputable section

open Module TauCeti.Comodule
open scoped TensorProduct DirectSum

namespace TauCeti

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Bialgebra k A]

/-- **Sweedler's invariant integral** on a bialgebra `A` over a field `k` whose simple coefficient
submodules span `A`: the `k`-linear functional equal to `Coalgebra.counit` on `k · 1` and `0` on
every nontrivial simple coefficient submodule. -/
def sweedlerIntegral (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤) : A →ₗ[k] k :=
  (Coalgebra.counit (R := k) (A := A) ∘ₗ (Submodule.span k ({1} : Set A)).subtype) ∘ₗ
    DirectSum.component k (simpleCoefficientSubmodules k A) (fun P ↦ (P.1 : Submodule k A))
      ⟨Submodule.span k ({1} : Set A), span_singleton_one_mem_simpleCoefficientSubmodules⟩ ∘ₗ
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun P : simpleCoefficientSubmodules k A ↦ (P.1 : Submodule k A))
      (isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hspan)).symm.toLinearMap

/-- On `k · 1`, `sweedlerIntegral` agrees with the counit. -/
theorem sweedlerIntegral_apply_of_mem_span_one (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤)
    {x : A} (hx : x ∈ Submodule.span k ({1} : Set A)) :
    sweedlerIntegral hspan x = Coalgebra.counit (R := k) x := by
  let hInt := isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hspan
  let P₁ : simpleCoefficientSubmodules k A :=
    ⟨Submodule.span k ({1} : Set A), span_singleton_one_mem_simpleCoefficientSubmodules⟩
  have hcomp := hInt.ofBijective_coeLinearMap_of_mem (i := P₁) hx
  simpa [sweedlerIntegral, P₁, ← DirectSum.apply_eq_component] using
    congrArg (fun y : P₁.1 ↦ Coalgebra.counit (R := k) (y : A)) hcomp

/-- On every simple coefficient submodule distinct from `k · 1`, `sweedlerIntegral` vanishes. -/
theorem sweedlerIntegral_apply_of_mem_of_ne (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤)
    {P : Submodule k A} (hP : P ∈ simpleCoefficientSubmodules k A)
    (hPne : P ≠ Submodule.span k ({1} : Set A)) {x : A} (hx : x ∈ P) :
    sweedlerIntegral hspan x = 0 := by
  let hInt := isInternal_of_sSup_simpleCoefficientSubmodules_eq_top hspan
  let P₁ : simpleCoefficientSubmodules k A :=
    ⟨Submodule.span k ({1} : Set A), span_singleton_one_mem_simpleCoefficientSubmodules⟩
  have hQne : (⟨P, hP⟩ : simpleCoefficientSubmodules k A) ≠ P₁ :=
    fun h ↦ hPne (congrArg Subtype.val h)
  have hcomp := hInt.ofBijective_coeLinearMap_of_mem_ne hQne hx
  simpa [sweedlerIntegral, P₁, ← DirectSum.apply_eq_component] using
    congrArg (fun y : P₁.1 ↦ Coalgebra.counit (R := k) (y : A)) hcomp

/-- `sweedlerIntegral` evaluates to `1` at `1`. -/
@[simp]
theorem sweedlerIntegral_one (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤) :
    sweedlerIntegral hspan 1 = 1 := by
  rw [sweedlerIntegral_apply_of_mem_span_one hspan (Submodule.subset_span (Set.mem_singleton 1)),
    Bialgebra.counit_one]

/-- `sweedlerIntegral` recovers scalar multiples of `1`. -/
@[simp]
theorem sweedlerIntegral_algebraMap (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤) (c : k) :
    sweedlerIntegral hspan (algebraMap k A c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, sweedlerIntegral_one, smul_eq_mul, mul_one]

private theorem linearMap_eq_of_sweedlerIntegral
    (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤) {F G : A →ₗ[k] A} (h1 : F 1 = G 1)
    (hmat : ∀ {M : ComoduleCat.{u, v, v} k A} [IsSimpleOrder (Subcomodule k A M)]
      {n : ℕ} (b : Basis (Fin n) k M),
      (∀ p q, sweedlerIntegral hspan (coefficientMatrix (C := A) b p q) = 0) →
      ∀ i j, F (coefficientMatrix (C := A) b i j) = G (coefficientMatrix (C := A) b i j))
    (a : A) : F a = G a := by
  suffices hFG : LinearMap.eqLocus F G = ⊤ from LinearMap.mem_eqLocus.mp (hFG ▸ Submodule.mem_top)
  rw [eq_top_iff, ← hspan]
  refine sSup_le fun P hP ↦ ?_
  by_cases hP1 : P = Submodule.span k ({1} : Set A)
  · rw [hP1, Submodule.span_le, Set.singleton_subset_iff]
    exact h1
  · obtain ⟨M, hM, rfl⟩ := mem_simpleCoefficientSubmodules.mp hP
    let _ := hM
    have : Module.Finite k M := finite_of_isSimpleOrder (C := A)
    let b := Module.finBasis k M
    have hzero (p q) : sweedlerIntegral hspan (coefficientMatrix (C := A) b p q) = 0 := by
      refine sweedlerIntegral_apply_of_mem_of_ne hspan
        matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules hP1 ?_
      rw [coefficientMatrix_apply]
      exact matrixCoefficient_mem_submodule _ _
    exact b.matrixCoefficientSubmodule_le_of_coefficientMatrix_mem fun i j ↦
      LinearMap.mem_eqLocus.mpr (hmat b hzero i j)

/-- `sweedlerIntegral` is a left invariant integral. -/
theorem isLeftInvariantIntegral_sweedlerIntegral
    (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤) :
    (sweedlerIntegral hspan).IsLeftInvariantIntegral := by
  rw [LinearMap.isLeftInvariantIntegral_iff]
  intro a
  have ha := linearMap_eq_of_sweedlerIntegral hspan
    (F := (TensorProduct.rid k A).toLinearMap ∘ₗ (sweedlerIntegral hspan).lTensor A ∘ₗ
      Coalgebra.comul)
    (G := Algebra.linearMap k A ∘ₗ sweedlerIntegral hspan)
    (by simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def])
    (fun b hzero i j ↦ by simp [comul_coefficientMatrix_eq_sum b i j, hzero]) a
  simpa [Algebra.algebraMap_eq_smul_one] using ha

/-- `sweedlerIntegral` is a right invariant integral. -/
theorem isRightInvariantIntegral_sweedlerIntegral
    (hspan : sSup (simpleCoefficientSubmodules k A) = ⊤) :
    (sweedlerIntegral hspan).IsRightInvariantIntegral := by
  rw [LinearMap.isRightInvariantIntegral_iff]
  intro a
  have ha := linearMap_eq_of_sweedlerIntegral hspan
    (F := (TensorProduct.lid k A).toLinearMap ∘ₗ (sweedlerIntegral hspan).rTensor A ∘ₗ
      Coalgebra.comul)
    (G := Algebra.linearMap k A ∘ₗ sweedlerIntegral hspan)
    (by simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def])
    (fun b hzero i j ↦ by simp [comul_coefficientMatrix_eq_sum b i j, hzero]) a
  simpa [Algebra.algebraMap_eq_smul_one] using ha

/-- On a Hopf algebra over a field, `sweedlerIntegral` is invariant under the antipode. -/
@[simp]
theorem sweedlerIntegral_antipode {H : Type v} [Ring H] [HopfAlgebra k H]
    (hspan : sSup (simpleCoefficientSubmodules k H) = ⊤) (a : H) :
    sweedlerIntegral hspan (HopfAlgebra.antipode k a) = sweedlerIntegral hspan a :=
  (isRightInvariantIntegral_sweedlerIntegral hspan).map_antipode (sweedlerIntegral_one hspan) a

end TauCeti

namespace TauCeti.Coalgebra.IsLinearlyReductive

universe u v

/-- Every linearly reductive bialgebra over a field admits a unique normalized two-sided invariant
integral. -/
theorem existsUnique_twoSidedInvariantIntegral {k : Type u} [Field k] {A : Type v} [Ring A]
    [Bialgebra k A] (hLR : IsLinearlyReductive.{u, v, u} k A) :
    ∃! h : A →ₗ[k] k, h.IsLeftInvariantIntegral ∧ h.IsRightInvariantIntegral ∧ h 1 = 1 := by
  have hspan := hLR.sSup_simpleCoefficientSubmodules_eq_top
  refine ⟨sweedlerIntegral hspan, ⟨isLeftInvariantIntegral_sweedlerIntegral hspan,
    isRightInvariantIntegral_sweedlerIntegral hspan, sweedlerIntegral_one hspan⟩, ?_⟩
  rintro h' ⟨hl', _, h1'⟩
  exact hl'.eq_of_isRightInvariantIntegral
    (isRightInvariantIntegral_sweedlerIntegral hspan) h1' (sweedlerIntegral_one hspan)

end TauCeti.Coalgebra.IsLinearlyReductive
