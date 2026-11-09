/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Analysis.Normed.Group.Finsupp
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The `ℓ¹`-norm of simplicial chains and the `ℓ¹`-seminorm on homology

Let `X` be a simplicial set and `V` a seminormed abelian group, a module over a ring `k`. The
simplicial `n`-chains `(X.chainComplex (ModuleCat.of k V)).X n` are the finitely supported
functions from the `n`-simplices of `X` to `V` (`SSet.chainsLinearEquivFinsupp`), so a chain is a
finite sum `∑ vᵢ σᵢ` of simplices `σᵢ` with coefficients `vᵢ ∈ V`. Its **`ℓ¹`-norm**
`SSet.chainL1Norm` is `∑ ‖vᵢ‖`, the sum of the norms of the coefficients.

The **`ℓ¹`-seminorm** of a homology class `α ∈ Hₙ(X; V)` (`SSet.homologyL1Seminorm`) is the
infimum of the `ℓ¹`-norms of the cycles representing it. It is the seminorm of Gromov: with real
coefficients, the `ℓ¹`-seminorm of the fundamental class of a closed oriented manifold is its
simplicial volume. This file proves the properties of the seminorm that do not depend on any
particular space.

* It is a seminorm for the integer multiples: it vanishes at `0`, is invariant under negation,
  subadditive, and `‖d • α‖₁ ≤ ‖d‖ * ‖α‖₁` for `d : ℤ`. With coefficients in a rational normed
  space (for instance a real one), `‖d • α‖₁ = ‖d‖ * ‖α‖₁` for every `d : ℤ`
  (`SSet.homologyL1Seminorm_zsmul`): for `d ≠ 0` the class `α` is represented by the chains
  representing `d • α`, divided by `d`.
* A chain map multiplying the `ℓ¹`-norm of `n`-chains by at most `C ≥ 0` multiplies the seminorm
  of `n`-dimensional classes by at most `C` (`SSet.homologyL1Seminorm_homologyMap_le_mul`). In
  particular the seminorm does not increase under the maps induced by maps of simplicial sets
  (`SSet.homologyL1Seminorm_homologyMap_le`), which push a simplex to a simplex, and changing the
  coefficients along a map multiplying norms by at most `C` multiplies it by at most `C`.

## Main definitions

* `SSet.chainL1Norm`: the `ℓ¹`-norm of a simplicial chain.
* `SSet.homologyL1Seminorm`: the `ℓ¹`-seminorm of a homology class.

## Main results

* `SSet.homologyL1Seminorm_homologyMap_le`: maps of simplicial sets do not increase the
  seminorm.
* `SSet.homologyL1Seminorm_add_le`, `SSet.homologyL1Seminorm_neg`: the seminorm is subadditive
  and invariant under negation.
* `SSet.homologyL1Seminorm_zsmul`: with coefficients in a rational normed space, the seminorm is
  homogeneous for the integer multiples.

## References

* M. Gromov, *Volume and bounded cohomology*, Publ. Math. IHÉS 56 (1982), 5–99, Section 0.2.
* W. P. Thurston, *The Geometry and Topology of Three-Manifolds*, Princeton lecture notes
  (1978–1980), Chapter 6, Section 6.1.
-/

public section

noncomputable section

open CategoryTheory Limits

open scoped Simplicial

universe u

namespace SSet

variable (X : SSet.{u}) {k : Type*} [Ring k]

/-! ### The `ℓ¹`-norm of chains -/

section Norm

variable {V W : Type u} [SeminormedAddCommGroup V] [Module k V] [SeminormedAddCommGroup W]
  [Module k W] {n : ℕ}

/-- The **`ℓ¹`-norm** of a simplicial chain `∑ vᵢ σᵢ`: the sum `∑ ‖vᵢ‖` of the norms of its
coefficients. -/
def chainL1Norm (c : (X.chainComplex (ModuleCat.of k V)).X n) : ℝ :=
  (X.chainsLinearEquivFinsupp V n c).sum fun _ v ↦ ‖v‖

/-- The `ℓ¹`-norm of a chain is the sum of the norms of the values of its coefficient
function. -/
theorem chainL1Norm_def (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    X.chainL1Norm c = (X.chainsLinearEquivFinsupp V n c).sum fun _ v ↦ ‖v‖ :=
  (rfl)

/-- The `ℓ¹`-norm of a chain is nonnegative. -/
theorem chainL1Norm_nonneg (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    0 ≤ X.chainL1Norm c :=
  Finsupp.sum_norm_nonneg _

/-- The zero chain has `ℓ¹`-norm `0`. -/
@[simp]
theorem chainL1Norm_zero : X.chainL1Norm (0 : (X.chainComplex (ModuleCat.of k V)).X n) = 0 := by
  simp [chainL1Norm_def]

/-- The `ℓ¹`-norm of the chain of a simplex with coefficient `v` is `‖v‖`. -/
@[simp]
theorem chainL1Norm_ιChainComplex (σ : X _⦋n⦌) (v : V) :
    X.chainL1Norm (X.ιChainComplex (R := ModuleCat.of k V) σ v) = ‖v‖ := by
  rw [chainL1Norm_def, chainsLinearEquivFinsupp_ιChainComplex,
    Finsupp.sum_single_index (h := fun _ x ↦ ‖x‖) norm_zero]

/-- The `ℓ¹`-norm is invariant under negation. -/
@[simp]
theorem chainL1Norm_neg (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    X.chainL1Norm (-c) = X.chainL1Norm c := by
  simp [chainL1Norm_def]

/-- **The triangle inequality** for the `ℓ¹`-norm of chains. -/
theorem chainL1Norm_add_le (c c' : (X.chainComplex (ModuleCat.of k V)).X n) :
    X.chainL1Norm (c + c') ≤ X.chainL1Norm c + X.chainL1Norm c' := by
  simpa only [chainL1Norm_def, map_add] using Finsupp.sum_norm_add_le _ _

/-- Multiplying a chain by an integer `d` multiplies its `ℓ¹`-norm by at most `‖d‖`. -/
theorem chainL1Norm_zsmul_le (d : ℤ) (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    X.chainL1Norm (d • c) ≤ ‖d‖ * X.chainL1Norm c := by
  simpa only [chainL1Norm_def, map_zsmul] using Finsupp.sum_norm_zsmul_le d _

/-- **The chain map induced by a map of simplicial sets does not increase the `ℓ¹`-norm**: it
pushes each simplex to a simplex, keeping its coefficient. -/
theorem chainL1Norm_chainComplexMap_f_le {Y : SSet.{u}} (f : X ⟶ Y)
    (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    Y.chainL1Norm ((chainComplexMap f (ModuleCat.of k V)).f n c) ≤ X.chainL1Norm c := by
  rw [chainL1Norm_def, chainL1Norm_def, chainsLinearEquivFinsupp_chainComplexMap_f]
  exact Finsupp.sum_norm_mapDomain_le _ _

/-- Changing the coefficients along a linear map multiplying norms by at most `C` multiplies the
`ℓ¹`-norm by at most `C`. -/
theorem chainL1Norm_chainComplexFunctor_map_le {ψ : V →ₗ[k] W} {C : ℝ}
    (hψ : ∀ v, ‖ψ v‖ ≤ C * ‖v‖) (c : (X.chainComplex (ModuleCat.of k V)).X n) :
    X.chainL1Norm ((((chainComplexFunctor (ModuleCat.{u} k)).map (ModuleCat.ofHom ψ)).app X).f n
      c) ≤ C * X.chainL1Norm c := by
  rw [chainL1Norm_def, chainL1Norm_def, chainsLinearEquivFinsupp_chainComplexFunctor_map]
  exact Finsupp.sum_norm_mapRange_le _ hψ _

end Norm

/-! ### The `ℓ¹`-seminorm on homology -/

section Seminorm

variable {V W : Type u} [SeminormedAddCommGroup V] [Module k V] [SeminormedAddCommGroup W]
  [Module k W] {n : ℕ}

/-- The **`ℓ¹`-seminorm** of a homology class `α ∈ Hₙ(X; V)`: the infimum of the `ℓ¹`-norms of
the cycles representing `α`. -/
def homologyL1Seminorm (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) : ℝ :=
  ⨅ z : {z : (X.chainComplex (ModuleCat.of k V)).cycles n //
      (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α},
    X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z.1)

/-- The `ℓ¹`-seminorm of a class is the infimum of the `ℓ¹`-norms of its representing cycles. -/
theorem homologyL1Seminorm_def (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    X.homologyL1Seminorm α =
      ⨅ z : {z : (X.chainComplex (ModuleCat.of k V)).cycles n //
          (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α},
        X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z.1) :=
  (rfl)

/-- Every homology class is represented by a cycle
(`HomologicalComplex.moduleCat_homologyπ_surjective`), so the infimum defining the seminorm is
over a nonempty set. -/
private theorem nonempty_representative
    (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    Nonempty {z : (X.chainComplex (ModuleCat.of k V)).cycles n //
      (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α} :=
  let ⟨z, hz⟩ := (X.chainComplex (ModuleCat.of k V)).moduleCat_homologyπ_surjective n α
  ⟨⟨z, hz⟩⟩

/-- The seminorm of a class is at most the `ℓ¹`-norm of every cycle representing it. -/
theorem homologyL1Seminorm_le_chainL1Norm
    {α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)}
    (z : (X.chainComplex (ModuleCat.of k V)).cycles n)
    (hz : (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α) :
    X.homologyL1Seminorm α ≤ X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z) :=
  ciInf_le ⟨0, Set.forall_mem_range.2 fun _ ↦ X.chainL1Norm_nonneg _⟩
    (⟨z, hz⟩ : {w // (X.chainComplex (ModuleCat.of k V)).homologyπ n w = α})

/-- The `ℓ¹`-seminorm is nonnegative. -/
theorem homologyL1Seminorm_nonneg (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    0 ≤ X.homologyL1Seminorm α :=
  have := X.nonempty_representative α
  le_ciInf fun _ ↦ X.chainL1Norm_nonneg _

/-- A bound `x ≤ C * ‖z‖₁`, with `C ≥ 0`, on every cycle `z` representing `α` gives
`x ≤ C * ‖α‖₁`. -/
theorem le_mul_homologyL1Seminorm {α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)}
    {x C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z, (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α →
      x ≤ C * X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z)) :
    x ≤ C * X.homologyL1Seminorm α := by
  have := X.nonempty_representative α
  rw [homologyL1Seminorm_def, Real.mul_iInf_of_nonneg hC]
  exact le_ciInf fun z ↦ h z.1 z.2

/-- A lower bound on the `ℓ¹`-norm of every cycle representing `α` is a lower bound on the
seminorm of `α`. -/
theorem le_homologyL1Seminorm {α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)} {x : ℝ}
    (h : ∀ z, (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α →
      x ≤ X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z)) :
    x ≤ X.homologyL1Seminorm α := by
  simpa using X.le_mul_homologyL1Seminorm zero_le_one (x := x) fun z hz ↦ by simpa using h z hz

/-- If the seminorm of `α` is less than `r`, some cycle representing `α` has `ℓ¹`-norm less
than `r`. -/
theorem exists_chainL1Norm_lt {α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)} {r : ℝ}
    (h : X.homologyL1Seminorm α < r) :
    ∃ z, (X.chainComplex (ModuleCat.of k V)).homologyπ n z = α ∧
      X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z) < r := by
  have := X.nonempty_representative α
  obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt h
  exact ⟨z.1, z.2, hz⟩

/-- The zero class has `ℓ¹`-seminorm `0`. -/
@[simp]
theorem homologyL1Seminorm_zero :
    X.homologyL1Seminorm (0 : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) = 0 :=
  le_antisymm ((X.homologyL1Seminorm_le_chainL1Norm 0 (map_zero _)).trans_eq (by simp))
    (X.homologyL1Seminorm_nonneg 0)

/-- **Functoriality of the `ℓ¹`-seminorm.** A chain map between simplicial chain complexes
multiplying the `ℓ¹`-norm of `n`-chains by at most `C ≥ 0` multiplies the seminorm of
`n`-dimensional homology classes by at most `C`. -/
theorem homologyL1Seminorm_homologyMap_le_mul {Y : SSet.{u}}
    (φ : X.chainComplex (ModuleCat.of k V) ⟶ Y.chainComplex (ModuleCat.of k W)) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ c, Y.chainL1Norm (φ.f n c) ≤ C * X.chainL1Norm c)
    (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    Y.homologyL1Seminorm (HomologicalComplex.homologyMap φ n α) ≤
      C * X.homologyL1Seminorm α := by
  refine X.le_mul_homologyL1Seminorm hC fun z hz ↦ ?_
  have hπ := congrArg (fun g ↦ g.hom z) (HomologicalComplex.homologyπ_naturality φ n)
  have hi := congrArg (fun g ↦ g.hom z) (HomologicalComplex.cyclesMap_i φ n)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hz] at hπ hi
  exact (Y.homologyL1Seminorm_le_chainL1Norm _ hπ.symm).trans (hi ▸ hφ _)

/-- **Maps of simplicial sets do not increase the `ℓ¹`-seminorm.** -/
theorem homologyL1Seminorm_homologyMap_le {Y : SSet.{u}} (f : X ⟶ Y)
    (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    Y.homologyL1Seminorm (SSet.homologyMap f (ModuleCat.of k V) n α) ≤
      X.homologyL1Seminorm α := by
  simpa using X.homologyL1Seminorm_homologyMap_le_mul (chainComplexMap f _) zero_le_one
    (fun c ↦ by simpa using X.chainL1Norm_chainComplexMap_f_le f c) α

/-- Changing the coefficients along a linear map multiplying norms by at most `C ≥ 0` multiplies
the `ℓ¹`-seminorm by at most `C`. -/
theorem homologyL1Seminorm_homologyMap_chainComplexFunctor_map_le {ψ : V →ₗ[k] W} {C : ℝ}
    (hC : 0 ≤ C) (hψ : ∀ v, ‖ψ v‖ ≤ C * ‖v‖)
    (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    X.homologyL1Seminorm (HomologicalComplex.homologyMap
        (((chainComplexFunctor (ModuleCat.{u} k)).map (ModuleCat.ofHom ψ)).app X) n α) ≤
      C * X.homologyL1Seminorm α :=
  X.homologyL1Seminorm_homologyMap_le_mul _ hC (X.chainL1Norm_chainComplexFunctor_map_le hψ) α

private theorem homologyL1Seminorm_neg_le
    (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    X.homologyL1Seminorm (-α) ≤ X.homologyL1Seminorm α :=
  X.le_homologyL1Seminorm fun z hz ↦ by
    simpa using X.homologyL1Seminorm_le_chainL1Norm (-z) (by rw [map_neg, hz])

/-- The `ℓ¹`-seminorm is invariant under negation. -/
@[simp]
theorem homologyL1Seminorm_neg (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    X.homologyL1Seminorm (-α) = X.homologyL1Seminorm α :=
  le_antisymm (X.homologyL1Seminorm_neg_le α) (by simpa using X.homologyL1Seminorm_neg_le (-α))

/-- **The triangle inequality** for the `ℓ¹`-seminorm. -/
theorem homologyL1Seminorm_add_le (α β : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    X.homologyL1Seminorm (α + β) ≤ X.homologyL1Seminorm α + X.homologyL1Seminorm β := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨z, hz, hzε⟩ := X.exists_chainL1Norm_lt (α := α)
    (r := X.homologyL1Seminorm α + ε / 2) (by linarith)
  obtain ⟨w, hw, hwε⟩ := X.exists_chainL1Norm_lt (α := β)
    (r := X.homologyL1Seminorm β + ε / 2) (by linarith)
  calc X.homologyL1Seminorm (α + β)
      ≤ X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n (z + w)) :=
        X.homologyL1Seminorm_le_chainL1Norm _ (by rw [map_add, hz, hw])
    _ ≤ X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n z) +
        X.chainL1Norm ((X.chainComplex (ModuleCat.of k V)).iCycles n w) := by
        rw [map_add]
        exact X.chainL1Norm_add_le _ _
    _ < X.homologyL1Seminorm α + X.homologyL1Seminorm β + ε := by linarith

/-- Multiplying a class by an integer `d` multiplies its `ℓ¹`-seminorm by at most `‖d‖`. -/
theorem homologyL1Seminorm_zsmul_le (d : ℤ)
    (α : (X.homology (ModuleCat.of k V) n : ModuleCat.{u} k)) :
    X.homologyL1Seminorm (d • α) ≤ ‖d‖ * X.homologyL1Seminorm α :=
  X.le_mul_homologyL1Seminorm (norm_nonneg d) fun z hz ↦ by
    refine (X.homologyL1Seminorm_le_chainL1Norm (d • z) (by rw [map_zsmul, hz])).trans ?_
    rw [map_zsmul]
    exact X.chainL1Norm_zsmul_le d _

end Seminorm

/-! ### Rational coefficients -/

section Rat

variable {V : Type u} [SeminormedAddCommGroup V] [NormedSpace ℚ V] {n : ℕ}

/-- Division by a nonzero integer `d`, as a coefficient endomorphism of a rational normed
space. -/
private def divCoeff (d : ℤ) : V →ₗ[ℤ] V :=
  ((d : ℚ)⁻¹ • LinearMap.id : V →ₗ[ℚ] V).restrictScalars ℤ

private theorem divCoeff_apply (d : ℤ) (v : V) : divCoeff d v = (d : ℚ)⁻¹ • v := by
  simp [divCoeff]

/-- Dividing the coefficients of `d • c` by `d ≠ 0` gives back the chain `c`. -/
private theorem chainComplexFunctor_map_divCoeff_zsmul {d : ℤ} (hd : d ≠ 0)
    (c : (X.chainComplex (ModuleCat.of ℤ V)).X n) :
    (((chainComplexFunctor (ModuleCat.{u} ℤ)).map (ModuleCat.ofHom (divCoeff d))).app X).f n
      (d • c) = c := by
  apply (X.chainsLinearEquivFinsupp V n).injective
  rw [chainsLinearEquivFinsupp_chainComplexFunctor_map, map_zsmul]
  ext σ
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.2 hd
  simp [divCoeff_apply, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hd']

/-- Dividing the coefficients of the chains by `d ≠ 0` sends `d • α` back to `α`. -/
private theorem homologyMap_divCoeff_zsmul {d : ℤ} (hd : d ≠ 0)
    (α : (X.homology (ModuleCat.of ℤ V) n : ModuleCat.{u} ℤ)) :
    HomologicalComplex.homologyMap
      (((chainComplexFunctor (ModuleCat.{u} ℤ)).map (ModuleCat.ofHom (divCoeff d))).app X) n
        (d • α) = α := by
  obtain ⟨z, rfl⟩ := (X.chainComplex (ModuleCat.of ℤ V)).moduleCat_homologyπ_surjective n α
  let φ := ((chainComplexFunctor (ModuleCat.{u} ℤ)).map
    (ModuleCat.ofHom (divCoeff (V := V) d))).app X
  let K := X.chainComplex (ModuleCat.of ℤ V)
  have hπ : HomologicalComplex.homologyMap φ n (K.homologyπ n (d • z)) =
      K.homologyπ n (HomologicalComplex.cyclesMap φ n (d • z)) :=
    congrArg (fun g ↦ g.hom (d • z)) (HomologicalComplex.homologyπ_naturality φ n)
  have hi : K.iCycles n (HomologicalComplex.cyclesMap φ n (d • z)) =
      φ.f n (K.iCycles n (d • z)) :=
    congrArg (fun g ↦ g.hom (d • z)) (HomologicalComplex.cyclesMap_i φ n)
  have hz : HomologicalComplex.cyclesMap φ n (d • z) = z := by
    apply K.moduleCat_iCycles_injective n
    rw [hi, map_zsmul]
    exact X.chainComplexFunctor_map_divCoeff_zsmul hd _
  rw [← map_zsmul, hπ, hz]

/-- **Homogeneity of the `ℓ¹`-seminorm with rational normed coefficients**: for every integer
`d`, `‖d • α‖₁ = ‖d‖ * ‖α‖₁`. -/
theorem homologyL1Seminorm_zsmul (d : ℤ)
    (α : (X.homology (ModuleCat.of ℤ V) n : ModuleCat.{u} ℤ)) :
    X.homologyL1Seminorm (d • α) = ‖d‖ * X.homologyL1Seminorm α := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  refine le_antisymm (X.homologyL1Seminorm_zsmul_le d α) ?_
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd
  have h := X.homologyL1Seminorm_homologyMap_chainComplexFunctor_map_le (ψ := divCoeff d)
    (C := ‖d‖⁻¹) (inv_nonneg.2 hd'.le) (fun v ↦ by
      rw [divCoeff_apply, norm_smul, norm_inv, Int.norm_cast_rat]) (d • α)
  rw [X.homologyMap_divCoeff_zsmul hd] at h
  rwa [← le_div_iff₀' hd', div_eq_inv_mul]

end Rat

end SSet
