/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.RingTheory.MvPolynomial.Monogenic.Chiral
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Spinor-valued monogenic polynomials and the Clifford Fischer decomposition

For a Clifford module `ρ : CliffordAlgebra Q →ₐ[R] Module.End K W` and vectors `b : σ → V`,
`CliffordAlgebra.coordAction ρ b i = ρ (ι Q (b i))` acts on `MvPolynomial σ K ⊗[K] W` via
`MvPolynomial.cliffordMul` and `MvPolynomial.cliffordDirac`. When `Q v = -‖v‖²` and `b` is an
orthonormal basis, this yields the **Clifford Fischer decomposition**, its chiral counterpart and
`±1` chirality splitting for `CliffordAlgebra.complexVolume Q o` in even dimension `n`, and the
half-spinor monogenic dimension `(n - 1).multichoose k * 2 ^ (n / 2 - 1)` on spinor modules.

## Main definitions

* `CliffordAlgebra.coordAction` and `CliffordAlgebra.complexCoordAction`.

## Main results

* `CliffordAlgebra.disjoint_monogenicSubmodule_coordAction`,
  `CliffordAlgebra.monogenicSubmodule_coordAction_sup_map`, and
  `CliffordAlgebra.finrank_monogenicSubmodule_coordAction`.
* `CliffordAlgebra.chiralMonogenicSubmodule_complexCoordAction_sup_map`,
  `CliffordAlgebra.chiralMonogenicSubmodule_complexCoordAction_sup_neg`, and
  `CliffordAlgebra.finrank_chiralMonogenicSubmodule_complexCoordAction_of_bijective_lsmul`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Math. Series 38 (1989), Ch. II, §8.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

section General

variable {R K V W σ : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] {Q : QuadraticForm R V}
  [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

/-- Coordinate endomorphisms `i ↦ ρ (ι Q (b i))` on a Clifford module `W`. -/
def coordAction (ρ : CliffordAlgebra Q →ₐ[R] Module.End K W) (b : σ → V) : σ → Module.End K W :=
  fun i ↦ ρ (ι Q (b i))

@[simp] theorem coordAction_apply (ρ : CliffordAlgebra Q →ₐ[R] Module.End K W) (b : σ → V)
    (i : σ) (w : W) : coordAction ρ b i w = ρ (ι Q (b i)) w := (rfl)

theorem coordAction_comp_self (ρ : CliffordAlgebra Q →ₐ[R] Module.End K W) {b : σ → V}
    (hb : ∀ i, Q (b i) = -1) (i : σ) : coordAction ρ b i ∘ₗ coordAction ρ b i = -1 := by
  rw [← Module.End.mul_eq_comp, coordAction, ← map_mul ρ, ι_sq_scalar, hb i, map_neg, map_one,
    map_neg, map_one]

theorem pairwise_coordAction_comp_add (ρ : CliffordAlgebra Q →ₐ[R] Module.End K W) {b : σ → V}
    (hb : Pairwise fun i j ↦ Q.IsOrtho (b i) (b j)) :
    Pairwise fun i j ↦
      coordAction ρ b i ∘ₗ coordAction ρ b j + coordAction ρ b j ∘ₗ coordAction ρ b i = 0 := by
  intro i j hij
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, coordAction, coordAction, ← map_mul ρ,
    ← map_mul ρ, ← map_add ρ, ι_mul_ι_add_swap, (hb hij).polar_eq_zero, map_zero, map_zero]

end General

section Orthonormal

variable {K V W σ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  [CommRing K] [Algebra ℝ K] [AddCommGroup W] [Module ℝ W] [Module K W] [IsScalarTower ℝ K W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End K W) [Fintype σ] (b : OrthonormalBasis σ ℝ V)

include hQ

theorem coordAction_orthonormalBasis_comp_self (i : σ) :
    coordAction ρ b i ∘ₗ coordAction ρ b i = -1 :=
  coordAction_comp_self ρ (fun j ↦ by simp [hQ, b.orthonormal.1 j]) i

theorem pairwise_coordAction_orthonormalBasis_comp_add :
    Pairwise fun i j ↦
      coordAction ρ b i ∘ₗ coordAction ρ b j + coordAction ρ b j ∘ₗ coordAction ρ b i = 0 :=
  pairwise_coordAction_comp_add ρ fun _ _ hij ↦ b.isOrtho_apply hQ hij

/-- **Directness of the Clifford Fischer decomposition** on `W` for `Q v = -‖v‖²`. -/
theorem disjoint_monogenicSubmodule_coordAction (k : ℕ)
    (N : Submodule K (MvPolynomial σ K ⊗[K] W)) :
    Disjoint (MvPolynomial.monogenicSubmodule (coordAction ρ b) k)
      (N.map (MvPolynomial.cliffordMul (coordAction ρ b))) := by
  have : HasUniqueDiv W := @HasUniqueDiv.of_module_rat W _ (Module.compHom W (algebraMap ℚ ℝ))
  exact ((MvPolynomial.disjoint_ker_cliffordDirac_range_cliffordMul
    (coordAction_orthonormalBasis_comp_self hQ ρ b)
    (pairwise_coordAction_orthonormalBasis_comp_add hQ ρ b)).mono_left
      (MvPolynomial.monogenicSubmodule_le_ker_cliffordDirac _ k)).mono_right LinearMap.map_le_range

/-- **The Clifford Fischer decomposition** on a Clifford module `W` for `Q v = -‖v‖²`. -/
theorem monogenicSubmodule_coordAction_sup_map (k : ℕ) :
    MvPolynomial.monogenicSubmodule (coordAction ρ b) (k + 1) ⊔
        (MvPolynomial.homogeneousTensorSubmodule σ K W k).map
          (MvPolynomial.cliffordMul (coordAction ρ b)) =
      MvPolynomial.homogeneousTensorSubmodule σ K W (k + 1) := by
  let _ : Algebra ℚ K := RingHom.toAlgebra ((algebraMap ℝ K).comp (algebraMap ℚ ℝ))
  exact MvPolynomial.monogenicSubmodule_sup_map_cliffordMul
    (coordAction_orthonormalBasis_comp_self hQ ρ b)
    (pairwise_coordAction_orthonormalBasis_comp_add hQ ρ b) k

end Orthonormal

section OrthonormalField

variable {K V W σ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  [Field K] [Algebra ℝ K] [AddCommGroup W] [Module ℝ W] [Module K W] [IsScalarTower ℝ K W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End K W) [Fintype σ] (b : OrthonormalBasis σ ℝ V)

include hQ in
/-- **Dimension of spinor-valued monogenic polynomials** for `Q v = -‖v‖²`. -/
theorem finrank_monogenicSubmodule_coordAction (k : ℕ) :
    Module.finrank K (MvPolynomial.monogenicSubmodule (coordAction ρ b) k) =
      (Fintype.card σ - 1).multichoose k * Module.finrank K W := by
  have : CharZero K := charZero_of_inj_zero fun n hn ↦
    Nat.cast_eq_zero.mp ((algebraMap ℝ K).injective (by simp [hn]))
  rcases isEmpty_or_nonempty σ with _ | ⟨⟨i₀⟩⟩
  · rcases k with _ | k
    · rw [MvPolynomial.monogenicSubmodule_zero,
        ← (MvPolynomial.homogeneousTensorZeroEquiv σ K W).finrank_eq]; simp
    · rw [MvPolynomial.monogenicSubmodule_succ_eq_bot_of_isEmpty, finrank_bot,
        Fintype.card_eq_zero]; simp
  · exact MvPolynomial.finrank_monogenicSubmodule_of_bijective
      (MvPolynomial.bijective_of_comp_self_eq_neg_one
        (coordAction_orthonormalBasis_comp_self hQ ρ b i₀)) k

end OrthonormalField

section ComplexVolume

variable {V σ : Type*}

section Action

variable [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

variable (Q E) in
/-- Coordinate endomorphisms `i ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ b i) • ·` on `E`. -/
def complexCoordAction (b : σ → V) : σ → Module.End ℂ E :=
  coordAction (((Algebra.lsmul ℂ ℂ E).restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q)) b

@[simp] theorem complexCoordAction_apply (b : σ → V) (i : σ) (ψ : E) :
    complexCoordAction Q E b i ψ = ι (Q.baseChange ℂ) (1 ⊗ₜ b i) • ψ := by
  simp [complexCoordAction]

end Action

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))
  {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

theorem lsmul_complexVolume_comp_complexCoordAction_add (hn : Even n) (b : σ → V) (i : σ) :
    Algebra.lsmul ℂ ℂ E (complexVolume Q o) ∘ₗ complexCoordAction Q E b i +
      complexCoordAction Q E b i ∘ₗ Algebra.lsmul ℂ ℂ E (complexVolume Q o) = 0 := by
  ext ψ
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    Algebra.lsmul_coe, complexCoordAction_apply, ← mul_smul]
  rw [complexVolume_mul_ι_of_even o hn, neg_smul, neg_add_cancel]

variable [Fintype σ] (b : OrthonormalBasis σ ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **Directness of the chiral Clifford Fischer decomposition** for `Q v = -‖v‖²`. -/
theorem disjoint_chiralMonogenicSubmodule_complexCoordAction (ε : ℂ) (k : ℕ)
    (N : Submodule ℂ (MvPolynomial σ ℂ ⊗[ℂ] E)) :
    Disjoint (MvPolynomial.chiralMonogenicSubmodule (complexCoordAction Q E b)
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)) ε k)
      (N.map (MvPolynomial.cliffordMul (complexCoordAction Q E b))) := by
  have : HasUniqueDiv E := @HasUniqueDiv.of_module_rat E _ (Module.compHom E (algebraMap ℚ ℂ))
  exact MvPolynomial.disjoint_chiralMonogenicSubmodule_map_cliffordMul
    (coordAction_orthonormalBasis_comp_self hQ _ b)
    (pairwise_coordAction_orthonormalBasis_comp_add hQ _ b) _ ε k N

/-- **The chiral Clifford Fischer decomposition** in even dimension `n` for `Q v = -‖v‖²`. -/
theorem chiralMonogenicSubmodule_complexCoordAction_sup_map (hn : Even n) (ε : ℂ) (k : ℕ) :
    MvPolynomial.chiralMonogenicSubmodule (complexCoordAction Q E b)
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)) ε (k + 1) ⊔
      (MvPolynomial.chiralHomogeneousSubmodule σ
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)) (-ε) k).map
        (MvPolynomial.cliffordMul (complexCoordAction Q E b)) =
      MvPolynomial.chiralHomogeneousSubmodule σ
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)) ε (k + 1) :=
  MvPolynomial.chiralMonogenicSubmodule_sup_map_cliffordMul
    (coordAction_orthonormalBasis_comp_self hQ _ b)
    (pairwise_coordAction_orthonormalBasis_comp_add hQ _ b)
    (lsmul_complexVolume_comp_complexCoordAction_add o hn b) ε k

/-- **Chirality splitting of monogenic polynomials** in even dimension `n` for `Q v = -‖v‖²`. -/
theorem chiralMonogenicSubmodule_complexCoordAction_sup_neg (hn : Even n) (k : ℕ) :
    MvPolynomial.chiralMonogenicSubmodule (complexCoordAction Q E b)
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)) 1 k ⊔
      MvPolynomial.chiralMonogenicSubmodule (complexCoordAction Q E b)
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)) (-1) k =
      MvPolynomial.monogenicSubmodule (complexCoordAction Q E b) k := by
  have hsq : Algebra.lsmul ℂ ℂ E (complexVolume Q o) ∘ₗ
      Algebra.lsmul ℂ ℂ E (complexVolume Q o) = 1 := by
    rw [← Module.End.mul_eq_comp, ← map_mul, complexVolume_mul_self o hQ, map_one]
  exact MvPolynomial.chiralMonogenicSubmodule_sup_neg hsq
    (lsmul_complexVolume_comp_complexCoordAction_add o hn b) k

/-- **Dimension of half-spinor monogenic polynomials** on a spinor module `S` (`n ≠ 0`). -/
theorem finrank_chiralMonogenicSubmodule_complexCoordAction_of_bijective_lsmul
    {S : Type*} [AddCommGroup S] [Module ℂ S] [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]
    (h : Function.Bijective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    (hn0 : n ≠ 0) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) (k : ℕ) :
    Module.finrank ℂ (MvPolynomial.chiralMonogenicSubmodule (complexCoordAction Q S b)
        (Algebra.lsmul ℂ ℂ S (complexVolume Q o)) μ k) =
      (n - 1).multichoose k * 2 ^ (n / 2 - 1) := by
  have hV : finrank ℂ (ℂ ⊗[ℝ] V) = n := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)]
  have hn : Even n := hV ▸ even_finrank_of_algEquiv_end _ (AlgEquiv.ofBijective _ h)
  have hcard : Fintype.card σ = n := (Module.finrank_eq_card_basis b.toBasis).symm.trans Fact.out
  obtain ⟨i₀⟩ : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  have := Module.Finite.of_surjective_end _ h.2
  have hc : Function.Surjective (complexCoordAction Q S b i₀) :=
    (MvPolynomial.bijective_of_comp_self_eq_neg_one (coordAction_orthonormalBasis_comp_self hQ
      (((Algebra.lsmul ℂ ℂ S).restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q)) b i₀)).2
  rw [MvPolynomial.finrank_chiralMonogenicSubmodule hc
      (lsmul_complexVolume_comp_complexCoordAction_add o hn b) μ k,
    hcard, finrank_eigenspace_complexVolume_of_bijective_lsmul o hQ h hn0 hμ]

end ComplexVolume

end CliffordAlgebra
