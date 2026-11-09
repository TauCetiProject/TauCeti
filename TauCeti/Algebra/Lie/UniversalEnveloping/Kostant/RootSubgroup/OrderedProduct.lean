/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Coordinate
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
import TauCeti.LinearAlgebra.Matrix.RaisesDegree
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Ordered products of positive Kostant root subgroups determine their parameters

Let a Kostant form act on an integral lattice `M` with a finite weight basis, and let `l` be a list
of root vectors whose roots `α i` are distinct and positive for a degree functional
`degree : (κ → ℤ) →+ ℤ`. Over a commutative ring `A`, the ordered product
`x_{i₁}(u_{i₁}) ⋯ x_{iₖ}(u_{iₖ})` of root-subgroup elements, taken in the order of `l`, determines
every parameter `u_i`, provided that each root operator `X_i` stays faithful after base change to
`A`: `c • X_i = 0` on `A ⊗[ℤ] M` forces `c = 0`.

For the positive roots of a Chevalley datum, listed in any fixed order, this is the uniqueness half
of the normal form `∏_{α > 0} x_α(u_α)` of the unipotent radical. Over a field the faithfulness
hypothesis says that every root operator survives reduction to the field; it is what lets the
linear term `u_i X_i` of a product detect the parameter `u_i`.

The proof writes each root-subgroup element in the weight basis as `1 + t X_i` plus divided powers
of `X_i` shifting weights by multiples `n α_i` with `n ≥ 2`, and applies the matrix uniqueness
theorem `TauCeti.Matrix.list_prod_map_inj_of_raisesDegree`. It uses no commutator relations.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.list_prod_map_kostantRootSubgroupParam_inj`: an ordered
  product of positive root-subgroup elements determines its parameters.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type x} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*}
variable {b : Module.Basis η ℤ M} {wt : η → κ → ℤ} {α : ι → κ → ℤ} {degree : (κ → ℤ) →+ ℤ}

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-- In a weight basis, the `n`-th divided power of a root operator of weight `α` has nonzero
entries only where it raises the weight by `n α`. -/
private theorem eq_add_nsmul_of_toMatrix_integralDividedPower_ne_zero [Fintype η] [DecidableEq η]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) {i : ι} {a : κ → ℤ}
    (hα : ∀ j, ⁅h j, e i⁆ = (a j : ℚ) • e i) (n : ℕ) {r s : η}
    (hrs : LinearMap.toMatrix b b
      (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
        (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)) r s ≠ 0) :
    wt r = wt s + n • a := by
  by_contra hne
  apply hrs
  rw [LinearMap.toMatrix_apply]
  apply repr_eq_zero_of_isCartanWeightVector h ρ M b wt hwt _ hne
  rw [coe_integralDividedPower_apply]
  exact IsCartanWeightVector.integralDividedPower e hα (hwt s) n

/-- A positive root-subgroup matrix is `1 + t X` up to a matrix raising the degree by more than the
degree of its root. -/
private theorem raisesDegree_kostantRootSubgroupMatrix_sub [Fintype η] [DecidableEq η]
    {A : Type*} [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) {i : ι} {a : κ → ℤ}
    (hα : ∀ j, ⁅h j, e i⁆ = (a j : ℚ) • e i) (hdeg : 0 < degree a) (t : A) :
    Matrix.RaisesDegree (degree ∘ wt) (degree a + 1)
      ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd t)) :
        Matrix η η A) - 1 -
        t • (LinearMap.toMatrix b b (kostantRootOperator e h ρ M hM i)).map
          (Int.cast : ℤ → A)) := by
  set N := nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  set D : ℕ → Matrix η η ℤ := fun n ↦ LinearMap.toMatrix b b
    (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
      (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv))
  have haction (n : ℕ) (s : η) :
      integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
        (fun _ hv ↦ dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv) (b s) =
        ∑ r, D n r s • b r := by
    simp [D, LinearMap.toMatrix_apply]
  -- Pad the divided-power expansion past the nilpotency class and split off degrees `0` and `1`.
  rw [kostantRootSubgroupMatrix_eq_sum e h ρ M hM i (hnil i) b (N + 2) D (by omega)
      (fun n _ s ↦ haction n s),
    MulEquiv.apply_symm_apply, toAdd_ofAdd, Finset.sum_range_succ', Finset.sum_range_succ']
  have hD0 : D 0 = 1 := by simp [D, integralDividedPower_zero, LinearMap.toMatrix_one]
  have hD1 : D 1 = LinearMap.toMatrix b b (kostantRootOperator e h ρ M hM i) := by
    rw [kostantRootOperator_def]
  simp only [zero_add, pow_zero, pow_one, one_smul, hD0, hD1, Matrix.map_one Int.cast Int.cast_zero
    Int.cast_one, add_sub_cancel_right]
  refine Matrix.RaisesDegree.sum fun n _ ↦ Matrix.RaisesDegree.smul ?_ _
  rw [Matrix.raisesDegree_iff]
  intro r s hrs
  have hrs' : D (n + 1 + 1) r s ≠ 0 := fun h0 ↦ hrs (by simp [h0])
  have hshift := eq_add_nsmul_of_toMatrix_integralDividedPower_ne_zero e h ρ M hM hwt hα _ hrs'
  rw [Function.comp_apply, Function.comp_apply, hshift, map_add, map_nsmul, nsmul_eq_mul]
  push_cast
  nlinarith

/-- **An ordered product of positive Kostant root-subgroup elements determines its parameters.**

Let `M` carry a finite weight basis, and let `l` list root vectors whose roots `α i` are distinct
and of positive degree. If each root operator stays faithful after base change to `A`, then two
ordered products `∏_{i ∈ l} x_i(u_i)` and `∏_{i ∈ l} x_i(v_i)` agree exactly when `u_i = v_i` for
every `i ∈ l`. -/
theorem list_prod_map_kostantRootSubgroupParam_inj [Finite η] (A : Type v) [CommRing A]
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) {l : List ι}
    (hl : (l.map α).Nodup) (hα : ∀ i ∈ l, ∀ j, ⁅h j, e i⁆ = (α i j : ℚ) • e i)
    (hdeg : ∀ i ∈ l, 0 < degree (α i))
    (hfaith : ∀ i ∈ l, ∀ c : A,
      c • (kostantRootOperator e h ρ M hM i).baseChange A = 0 → c = 0) {u v : ι → A} :
    (l.map fun i ↦ kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A)
        (Multiplicative.ofAdd (u i))).prod =
      (l.map fun i ↦ kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A)
        (Multiplicative.ofAdd (v i))).prod ↔
      ∀ i ∈ l, u i = v i := by
  classical
  have := Fintype.ofFinite η
  set X : ι → Matrix η η A := fun i ↦
    (LinearMap.toMatrix b b (kostantRootOperator e h ρ M hM i)).map (Int.cast : ℤ → A)
  set φ : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) →* Matrix η η A :=
    (Units.coeHom (Matrix η η A)).comp
      (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv)
  have hφ (w : ι → A) : φ (l.map fun i ↦ kostantRootSubgroupParam e h ρ M hM i (hnil i)
      (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (w i))).prod =
      (l.map fun i ↦ ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd (w i))) :
          Matrix η η A))).prod := by
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ ↦
      congrArg Units.val (basisMatrix_kostantRootSubgroupParam e h ρ M hM hnil b A i _))
  refine ⟨fun huv ↦ ?_, fun huv ↦ congrArg List.prod (List.map_congr_left fun i hi ↦ by
    rw [huv i hi])⟩
  have hmat := congrArg φ huv
  rw [hφ, hφ] at hmat
  refine (TauCeti.Matrix.list_prod_map_inj_of_raisesDegree wt degree α
    (fun i t ↦ (kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd t)) :
        Matrix η η A)) X hl hdeg ?_ ?_ ?_).mp hmat
  · -- Each root operator is the first divided power, so it shifts weights by its root.
    intro i hi r s hrs
    have hrs' : LinearMap.toMatrix b b (kostantRootOperator e h ρ M hM i) r s ≠ 0 :=
      fun h0 ↦ hrs (by simp [X, h0])
    rw [kostantRootOperator_def] at hrs'
    simpa using
      eq_add_nsmul_of_toMatrix_integralDividedPower_ne_zero e h ρ M hM hwt (hα i hi) 1 hrs'
  · exact fun i hi t ↦ raisesDegree_kostantRootSubgroupMatrix_sub e h ρ M hM hnil hwt (hα i hi)
      (hdeg i hi) t
  · -- Faithfulness of the base-changed root operator is faithfulness of its matrix.
    intro i hi c hc
    refine hfaith i hi c ((LinearMap.toMatrix (b.baseChange A) (b.baseChange A)).injective ?_)
    rw [map_smul, Module.Basis.toMatrix_baseChange_baseChange, map_zero, ← hc]
    simp [X, algebraMap_int_eq]

end TauCeti.UniversalEnvelopingAlgebra
