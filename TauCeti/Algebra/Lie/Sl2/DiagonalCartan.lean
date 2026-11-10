/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Basic

/-!
# The diagonal Cartan subalgebra and the positive base of `sl₂`

The rank-one model of the Cartan decomposition. For `L = sl (Fin 2) K`, with standard basis
`e = E₀₁`, `f = E₁₀`, `h = E₀₀ - E₁₁`, the diagonal matrices are a Cartan subalgebra `H` spanned by
`h`, and `L = H ⊕ K e ⊕ K f` is its root decomposition: the only roots are `±α`, where `α` takes a
diagonal matrix to twice its top entry, so `α(h) = 2`. The single root `α` is a base of the root
system. This pins down a concrete instance of the data `(H, b)` that the general highest-weight
theory is stated over, so that it can be evaluated in rank one.

Triangularizability is proved over every field, by exhibiting the eigenvectors `e`, `f` and `h`; no
algebraic closure is assumed.

## Main definitions

* `TauCeti.slTwoDiagonalCartan`: the diagonal matrices of `sl (Fin 2) R`.
* `TauCeti.slTwoCartanGenerator`: the element `h` of the diagonal Cartan.
* `TauCeti.slTwoWeight`: the weight taking the value `t` at `h`.
* `TauCeti.slTwoRoot`: the weight `α`, with index `TauCeti.slTwoRootIndex` in the root system.
* `TauCeti.slTwoPositiveBase`: the base `{α}` of the root system.

## Main results

* `TauCeti.mem_slTwoDiagonalCartan_iff`: the diagonal Cartan is the line spanned by `h`.
* `TauCeti.eq_slTwoRoot_or_eq_neg_slTwoRoot`: the nonzero weights of the adjoint action are `±α`.
* `TauCeti.slTwoPositiveBase_positive_generator`: the base selects `e` as positive.
* `TauCeti.coroot_slTwoRoot`: the coroot of `α` is `h`.
* `TauCeti.posRootsFinset_slTwoPositiveBase` and `TauCeti.weylDenominator_slTwoPositiveBase`: `α`
  is the only positive root, so the Weyl denominator is `1 - e^{-α}`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §7 and §8.
-/

public section

open LieAlgebra LieModule

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable (R : Type*) [CommRing R]

/-- The diagonal matrices of `sl (Fin 2) R`, spanned by `h = E₀₀ - E₁₁`. -/
def slTwoDiagonalCartan : LieSubalgebra R (SpecialLinear.sl (Fin 2) R) :=
  (diagonalCartan R (Fin 2)).comap (SpecialLinear.sl (Fin 2) R).incl

variable {R}

/-- Membership in the diagonal Cartan is diagonality of the matrix. -/
theorem mem_slTwoDiagonalCartan_iff_isDiag {x : SpecialLinear.sl (Fin 2) R} :
    x ∈ slTwoDiagonalCartan R ↔ (x : Matrix (Fin 2) (Fin 2) R).IsDiag :=
  mem_diagonalCartan_iff_isDiag

/-- An element of the diagonal Cartan is its top diagonal entry times `h = E₀₀ - E₁₁`. -/
theorem eq_smul_singleSubSingle_of_mem_slTwoDiagonalCartan {x : SpecialLinear.sl (Fin 2) R}
    (hx : x ∈ slTwoDiagonalCartan R) :
    x = x.val 0 0 • SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : R) := by
  have hd := mem_slTwoDiagonalCartan_iff_isDiag.mp hx
  have h₁ : x.val 0 1 = 0 := hd zero_ne_one
  have h₂ : x.val 1 0 = 0 := hd one_ne_zero
  conv_lhs => rw [eq_smul_single_add_smul_single_add_smul_singleSubSingle x (zero_ne_one' (Fin 2))]
  rw [h₁, h₂, zero_smul, zero_smul, zero_add, zero_add]

/-- The multiples of `h = E₀₀ - E₁₁` lie in the diagonal Cartan. -/
theorem singleSubSingle_mem_slTwoDiagonalCartan (a : R) :
    SpecialLinear.singleSubSingle (0 : Fin 2) 1 a ∈ slTwoDiagonalCartan R :=
  mem_slTwoDiagonalCartan_iff_isDiag.mpr <| (mem_specialLinearDiagonal_iff 1 R _).mp
    (singleSubSingle_mem_specialLinearDiagonal 1 R 0 1 a)

/-- **The diagonal Cartan is the line spanned by `h = E₀₀ - E₁₁`.** -/
theorem mem_slTwoDiagonalCartan_iff {x : SpecialLinear.sl (Fin 2) R} :
    x ∈ slTwoDiagonalCartan R ↔
      ∃ a : R, x = a • SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : R) :=
  ⟨fun hx ↦ ⟨_, eq_smul_singleSubSingle_of_mem_slTwoDiagonalCartan hx⟩, fun ⟨a, ha⟩ ↦
    ha ▸ (slTwoDiagonalCartan R).smul_mem a (singleSubSingle_mem_slTwoDiagonalCartan 1)⟩

instance : IsLieAbelian (slTwoDiagonalCartan R) where
  trivial x y := Subtype.ext <| Subtype.ext <| by
    simpa using lie_eq_zero_of_isDiag (mem_slTwoDiagonalCartan_iff_isDiag.mp x.2)
      (mem_slTwoDiagonalCartan_iff_isDiag.mp y.2)

/-- The top diagonal entry of `h = E₀₀ - E₁₁` is `1`. -/
private theorem val_singleSubSingle_zero_zero :
    (SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : R)).val 0 0 = 1 := by
  simp [SpecialLinear.val_singleSubSingle]

/-- The adjoint action of a diagonal element scales each entry by a difference of its diagonal
entries. -/
private theorem val_lie_of_mem_slTwoDiagonalCartan {x : SpecialLinear.sl (Fin 2) R}
    (hx : x ∈ slTwoDiagonalCartan R) (y : SpecialLinear.sl (Fin 2) R) (i j : Fin 2) :
    (⁅x, y⁆ : SpecialLinear.sl (Fin 2) R).val i j = (x.val i i - x.val j j) * y.val i j := by
  rw [LieSubalgebra.coe_bracket]
  exact lie_apply_of_mem_diagonalCartan (mem_diagonalCartan_iff_isDiag.mpr
    (mem_slTwoDiagonalCartan_iff_isDiag.mp hx)) _ _ _

/-- An element of the diagonal Cartan raises `E₀₁` by twice its top diagonal entry. -/
private theorem lie_single_zero_one_of_mem (x : slTwoDiagonalCartan R) (c : R) :
    ⁅x, SpecialLinear.single (0 : Fin 2) 1 zero_ne_one c⁆ =
      (2 * x.val.val 0 0) • SpecialLinear.single (0 : Fin 2) 1 zero_ne_one c := by
  rw [LieSubalgebra.coe_bracket_of_module, SpecialLinear.lie_single_of_isDiag
    (mem_slTwoDiagonalCartan_iff_isDiag.mp x.2), val_one_one_eq_neg_val_zero_zero, sub_neg_eq_add,
    two_mul]

/-- An element of the diagonal Cartan lowers `E₁₀` by twice its top diagonal entry. -/
private theorem lie_single_one_zero_of_mem (x : slTwoDiagonalCartan R) (c : R) :
    ⁅x, SpecialLinear.single (1 : Fin 2) 0 one_ne_zero c⁆ =
      -(2 * x.val.val 0 0) • SpecialLinear.single (1 : Fin 2) 0 one_ne_zero c := by
  rw [LieSubalgebra.coe_bracket_of_module, SpecialLinear.lie_single_of_isDiag
    (mem_slTwoDiagonalCartan_iff_isDiag.mp x.2), val_one_one_eq_neg_val_zero_zero]
  congr 1
  ring

/-- The diagonal Cartan kills `h = E₀₀ - E₁₁`. -/
private theorem lie_singleSubSingle_of_mem (x : slTwoDiagonalCartan R) (c : R) :
    ⁅x, SpecialLinear.singleSubSingle (0 : Fin 2) 1 c⁆ = 0 :=
  congrArg Subtype.val (trivial_lie_zero (slTwoDiagonalCartan R) (slTwoDiagonalCartan R) x
    ⟨_, singleSubSingle_mem_slTwoDiagonalCartan c⟩)

variable (R) in
/-- The element `h = E₀₀ - E₁₁`, as an element of the diagonal Cartan. -/
def slTwoCartanGenerator : slTwoDiagonalCartan R :=
  ⟨SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : R), singleSubSingle_mem_slTwoDiagonalCartan 1⟩

/-- The element `slTwoCartanGenerator` of the Cartan is `E₀₀ - E₁₁`. -/
@[simp]
theorem coe_slTwoCartanGenerator :
    (slTwoCartanGenerator R : SpecialLinear.sl (Fin 2) R) =
      SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : R) := (rfl)

/-- An element of the diagonal Cartan is its top diagonal entry times `h`. -/
theorem eq_smul_slTwoCartanGenerator (x : slTwoDiagonalCartan R) :
    x = x.val.val 0 0 • slTwoCartanGenerator R :=
  Subtype.ext (eq_smul_singleSubSingle_of_mem_slTwoDiagonalCartan x.2)

/-- A linear form on the diagonal Cartan is determined by its value at `h`. -/
theorem dual_ext_slTwoCartanGenerator {lam mu : Module.Dual R (slTwoDiagonalCartan R)}
    (h : lam (slTwoCartanGenerator R) = mu (slTwoCartanGenerator R)) : lam = mu :=
  LinearMap.ext fun x ↦ by
    rw [eq_smul_slTwoCartanGenerator x, map_smul, map_smul, h]

/-- The weight of the diagonal Cartan taking the value `t` at `h`: it sends a diagonal matrix to
`t` times its top entry. -/
def slTwoWeight (t : R) : Module.Dual R (slTwoDiagonalCartan R) where
  toFun x := t * x.val.val 0 0
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp [mul_left_comm]

/-- The defining property of `slTwoWeight`. -/
@[simp]
theorem slTwoWeight_slTwoCartanGenerator (t : R) :
    slTwoWeight t (slTwoCartanGenerator R) = t := by
  simp [slTwoWeight, SpecialLinear.val_singleSubSingle]

/-- A weight of the diagonal Cartan is determined by its value at `h`. -/
theorem slTwoWeight_injective : Function.Injective (slTwoWeight (R := R)) := fun s t h ↦ by
  simpa using congr($h (slTwoCartanGenerator R))

/-- Two weights `slTwoWeight` agree exactly when their values at `h` do. -/
@[simp]
theorem slTwoWeight_inj {s t : R} : slTwoWeight s = slTwoWeight t ↔ s = t :=
  slTwoWeight_injective.eq_iff

/-- `slTwoWeight` is additive in its value at `h`. -/
theorem slTwoWeight_add (s t : R) : slTwoWeight (s + t) = slTwoWeight s + slTwoWeight t :=
  dual_ext_slTwoCartanGenerator <| by simp

/-- `slTwoWeight` commutes with subtraction of the values at `h`. -/
theorem slTwoWeight_sub (s t : R) : slTwoWeight (s - t) = slTwoWeight s - slTwoWeight t :=
  dual_ext_slTwoCartanGenerator <| by simp

end CommRing

section Field

variable {K : Type*} [Field K]

variable (K) in
/-- **The diagonal matrices are a Cartan subalgebra of `sl₂`**: they are abelian, and they are
self-normalizing because `ad h` scales the off-diagonal entries by `±2`. -/
instance slTwoDiagonalCartan_isCartan [NeZero (2 : K)] :
    (slTwoDiagonalCartan K).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := by
    refine le_antisymm (fun x hx ↦ ?_) (LieSubalgebra.le_normalizer _)
    have hh := singleSubSingle_mem_slTwoDiagonalCartan (1 : K)
    have hlie := mem_slTwoDiagonalCartan_iff_isDiag.mp
      ((LieSubalgebra.mem_normalizer_iff' _ x).mp hx _ hh)
    have hentry {i j : Fin 2} (hij : i ≠ j) :
        (⁅SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : K), x⁆ :
          SpecialLinear.sl (Fin 2) K).val i j = 0 := hlie hij
    have h01 := hentry (zero_ne_one' (Fin 2))
    have h10 := hentry (one_ne_zero' (Fin 2))
    rw [val_lie_of_mem_slTwoDiagonalCartan hh, val_one_one_eq_neg_val_zero_zero,
      val_singleSubSingle_zero_zero] at h01 h10
    have h01' : x.val 0 1 = 0 :=
      (mul_eq_zero.mp (by linear_combination h01 : (2 : K) * x.val 0 1 = 0)).resolve_left
        two_ne_zero
    have h10' : x.val 1 0 = 0 :=
      (mul_eq_zero.mp (by linear_combination -h10 : (2 : K) * x.val 1 0 = 0)).resolve_left
        two_ne_zero
    refine mem_slTwoDiagonalCartan_iff_isDiag.mpr fun i j hij ↦ ?_
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption

variable (K) in
/-- **The diagonal Cartan of `sl₂` is split over every field**: `e`, `f` and `h` are simultaneous
eigenvectors spanning `sl₂`, so no algebraic closure is needed for the root decomposition. -/
instance slTwoDiagonalCartan_isTriangularizable :
    LieModule.IsTriangularizable K (slTwoDiagonalCartan K) (SpecialLinear.sl (Fin 2) K) where
  maxGenEigenspace_eq_top x := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [eq_smul_single_add_smul_single_add_smul_singleSubSingle y (zero_ne_one' (Fin 2))]
    have hmem {v : SpecialLinear.sl (Fin 2) K} {c : K} (hv : ⁅x, v⁆ = c • v) :
        v ∈ ⨆ φ, (LieModule.toEnd K (slTwoDiagonalCartan K)
          (SpecialLinear.sl (Fin 2) K) x).maxGenEigenspace φ :=
      Submodule.mem_iSup_of_mem c <| (Module.End.mem_maxGenEigenspace _ _ _).mpr
        ⟨1, by simp [hv]⟩
    refine add_mem (add_mem ?_ ?_) ?_
    · exact Submodule.smul_mem _ _ (hmem (lie_single_zero_one_of_mem x 1))
    · exact Submodule.smul_mem _ _ (hmem (lie_single_one_zero_of_mem x 1))
    · exact Submodule.smul_mem _ _
        (hmem (c := 0) (by simpa using lie_singleSubSingle_of_mem x 1))

variable (K) in
/-- **The positive root of `sl₂`**, the weight of `e = E₀₁` for the diagonal Cartan: it sends a
diagonal matrix to twice its top entry, so that it takes `h = E₀₀ - E₁₁` to `2`. -/
noncomputable def slTwoRoot : Weight K (slTwoDiagonalCartan K) (SpecialLinear.sl (Fin 2) K) where
  toFun x := 2 * x.val.val 0 0
  genWeightSpace_ne_bot' hbot := one_ne_zero (α := K) <| by
    have hmem : SpecialLinear.single (0 : Fin 2) 1 zero_ne_one (1 : K) ∈
        genWeightSpace (SpecialLinear.sl (Fin 2) K)
          (fun x : slTwoDiagonalCartan K ↦ 2 * x.val.val 0 0) :=
      weightSpace_le_genWeightSpace _ _ ((mem_weightSpace _ _).mpr fun x ↦
        lie_single_zero_one_of_mem x 1)
    rw [hbot, LieSubmodule.mem_bot] at hmem
    simpa using congrArg (fun v : SpecialLinear.sl (Fin 2) K ↦ v.val 0 1) hmem

/-- The value of `α` is twice the top diagonal entry. -/
@[simp]
theorem slTwoRoot_apply (x : slTwoDiagonalCartan K) : slTwoRoot K x = 2 * x.val.val 0 0 := (rfl)

/-- `α(h) = 2`. -/
theorem slTwoRoot_slTwoCartanGenerator : slTwoRoot K (slTwoCartanGenerator K) = 2 := by
  rw [slTwoRoot_apply, coe_slTwoCartanGenerator, val_singleSubSingle_zero_zero, mul_one]

/-- `α` is a nonzero weight, that is, a root. -/
theorem slTwoRoot_isNonZero [NeZero (2 : K)] : (slTwoRoot K).IsNonZero := fun h ↦
  two_ne_zero (α := K) <| by
    rw [← slTwoRoot_slTwoCartanGenerator]
    exact congrFun h (slTwoCartanGenerator K)

variable [CharZero K]

/-- A weight of the adjoint action is linear: its value at `x` is the top entry of `x` times its
value at `h`. -/
private theorem weight_apply_eq_mul
    (χ : Weight K (slTwoDiagonalCartan K) (SpecialLinear.sl (Fin 2) K))
    (x : slTwoDiagonalCartan K) :
    χ x = x.val.val 0 0 * χ (slTwoCartanGenerator K) := by
  rw [← Weight.toLinear_apply, ← Weight.toLinear_apply, ← smul_eq_mul, ← map_smul,
    ← eq_smul_slTwoCartanGenerator]

/-- A weight of the adjoint action is determined by its value at `h`. -/
theorem weight_ext_slTwoCartanGenerator {χ ψ : Weight K (slTwoDiagonalCartan K)
    (SpecialLinear.sl (Fin 2) K)} (h : χ (slTwoCartanGenerator K) = ψ (slTwoCartanGenerator K)) :
    χ = ψ :=
  Weight.ext fun x ↦ by rw [weight_apply_eq_mul χ, weight_apply_eq_mul ψ, h]

omit [CharZero K] in
/-- The eigenvalues of `ad h` on a nonzero eigenvector of `sl₂` are `2`, `-2` and `0`. -/
private theorem eq_two_or_eq_neg_two_or_eq_zero_of_lie_eq_smul {v : SpecialLinear.sl (Fin 2) K}
    (hv : v ≠ 0) {c : K} (hc : ⁅SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : K), v⁆ = c • v) :
    c = 2 ∨ c = -2 ∨ c = 0 := by
  have hentry (i j : Fin 2) : c * v.val i j =
      ((SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : K)).val i i -
        (SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : K)).val j j) * v.val i j := by
    rw [← val_lie_of_mem_slTwoDiagonalCartan (singleSubSingle_mem_slTwoDiagonalCartan (1 : K)), hc]
    simp
  have h01 := hentry 0 1
  have h10 := hentry 1 0
  have hzz := hentry 0 0
  simp only [val_one_one_eq_neg_val_zero_zero, val_singleSubSingle_zero_zero] at h01 h10 hzz
  by_cases ha : v.val 0 1 = 0
  · by_cases hb : v.val 1 0 = 0
    · have hd : v.val 0 0 ≠ 0 := fun hd ↦ hv <| by
        rw [eq_smul_single_add_smul_single_add_smul_singleSubSingle v (zero_ne_one' (Fin 2)), ha,
          hb, hd]
        simp
      exact .inr <| .inr <| (mul_eq_zero.mp (by simpa using hzz)).resolve_right hd
    · exact .inr <| .inl <| mul_right_cancel₀ hb (by linear_combination h10)
  · exact .inl <| mul_right_cancel₀ ha (by linear_combination h01)

/-- **The weights of the adjoint action**: a nonzero weight of the diagonal Cartan is `±α`. -/
theorem eq_slTwoRoot_or_eq_neg_slTwoRoot {χ : Weight K (slTwoDiagonalCartan K)
    (SpecialLinear.sl (Fin 2) K)} (hχ : χ.IsNonZero) : χ = slTwoRoot K ∨ χ = -slTwoRoot K := by
  obtain ⟨v, hv, hv0⟩ := χ.exists_ne_zero
  have hvh : ⁅slTwoCartanGenerator K, v⁆ = χ (slTwoCartanGenerator K) • v :=
    IsKilling.lie_eq_smul_of_mem_rootSpace (H := slTwoDiagonalCartan K) hv _
  rw [LieSubalgebra.coe_bracket_of_module, coe_slTwoCartanGenerator] at hvh
  obtain h | h | h := eq_two_or_eq_neg_two_or_eq_zero_of_lie_eq_smul hv0 hvh
  · exact .inl <| weight_ext_slTwoCartanGenerator <| by
      rw [h, slTwoRoot_slTwoCartanGenerator]
  · exact .inr <| weight_ext_slTwoCartanGenerator <| by
      rw [h, Weight.coe_neg, Pi.neg_apply, slTwoRoot_slTwoCartanGenerator]
  · exact absurd (funext fun x ↦ by simp [weight_apply_eq_mul χ x, h]) hχ

variable (K) in
/-- The positive root `α` as an index of the root system. -/
noncomputable def slTwoRootIndex :
    (LieSubalgebra.root : Finset (Weight K (slTwoDiagonalCartan K)
      (SpecialLinear.sl (Fin 2) K))) :=
  ⟨slTwoRoot K, by simpa [LieSubalgebra.root] using slTwoRoot_isNonZero⟩

/-- The weight underlying `slTwoRootIndex` is `α`. -/
@[simp]
theorem coe_slTwoRootIndex : (slTwoRootIndex K : Weight K (slTwoDiagonalCartan K)
    (SpecialLinear.sl (Fin 2) K)) = slTwoRoot K := (rfl)

/-- The root index of `-α` is the reflection of `α` in itself. -/
theorem eq_reflectionPerm_slTwoRootIndex
    {i : (LieSubalgebra.root : Finset (Weight K (slTwoDiagonalCartan K)
      (SpecialLinear.sl (Fin 2) K)))} (h : (i : Weight K (slTwoDiagonalCartan K)
        (SpecialLinear.sl (Fin 2) K)) = -slTwoRoot K) :
    i = (IsKilling.rootSystem (slTwoDiagonalCartan K)).reflectionPerm (slTwoRootIndex K)
      (slTwoRootIndex K) :=
  (IsKilling.rootSystem (slTwoDiagonalCartan K)).root.injective <| by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      IsKilling.rootSystem_root_apply, IsKilling.rootSystem_root_apply, coe_slTwoRootIndex, h]
    exact Weight.toLinear_neg

/-- Every root index is `α` or the reflection of `α` in itself, which is `-α`. -/
theorem eq_slTwoRootIndex_or_eq_reflectionPerm
    (i : (LieSubalgebra.root : Finset (Weight K (slTwoDiagonalCartan K)
      (SpecialLinear.sl (Fin 2) K)))) :
    i = slTwoRootIndex K ∨
      i = (IsKilling.rootSystem (slTwoDiagonalCartan K)).reflectionPerm (slTwoRootIndex K)
        (slTwoRootIndex K) :=
  (eq_slTwoRoot_or_eq_neg_slTwoRoot (LieSubalgebra.isNonZero_coe_root i)).imp Subtype.ext
    eq_reflectionPerm_slTwoRootIndex

/-- A family on the root indices that negates under the reflection of `α` in itself, such as the
roots and the coroots, takes every value in the closure of its value at `α`, up to sign. -/
private theorem mem_closure_or_neg_mem_closure {M : Type*} [AddCommGroup M]
    (f : ↥(LieSubalgebra.root : Finset (Weight K (slTwoDiagonalCartan K)
      (SpecialLinear.sl (Fin 2) K))) → M)
    (hf : f ((IsKilling.rootSystem (slTwoDiagonalCartan K)).reflectionPerm (slTwoRootIndex K)
      (slTwoRootIndex K)) = -f (slTwoRootIndex K)) (i) :
    f i ∈ AddSubmonoid.closure (f '' (({slTwoRootIndex K} : Finset _) : Set _)) ∨
      -f i ∈ AddSubmonoid.closure (f '' (({slTwoRootIndex K} : Finset _) : Set _)) := by
  have hmem : f (slTwoRootIndex K) ∈
      AddSubmonoid.closure (f '' (({slTwoRootIndex K} : Finset _) : Set _)) :=
    AddSubmonoid.subset_closure ⟨_, by simp, rfl⟩
  obtain rfl | rfl := eq_slTwoRootIndex_or_eq_reflectionPerm i
  · exact .inl hmem
  · exact .inr (by rwa [hf, neg_neg])

variable (K) in
/-- **The positive base of `sl₂`**: the single simple root `α`, whose root space contains
`e = E₀₁` (`TauCeti.slTwoPositiveBase_positive_generator`). -/
noncomputable def slTwoPositiveBase :
    (IsKilling.rootSystem (slTwoDiagonalCartan K)).Base where
  support := {slTwoRootIndex K}
  linearIndepOn_root := by simpa using slTwoRoot_isNonZero
  linearIndepOn_coroot := by simpa using slTwoRoot_isNonZero
  root_mem_or_neg_mem := mem_closure_or_neg_mem_closure _ <| by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  coroot_mem_or_neg_mem := mem_closure_or_neg_mem_closure _ <| by
    rw [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self]

/-- The base has the single simple root `α`. -/
@[simp]
theorem slTwoPositiveBase_support : (slTwoPositiveBase K).support = {slTwoRootIndex K} := (rfl)

/-- The root `α` is simple. -/
theorem slTwoRootIndex_mem_support : slTwoRootIndex K ∈ (slTwoPositiveBase K).support :=
  Finset.mem_singleton_self _

/-- `e = E₀₁` is a root vector for the simple root. -/
theorem single_zero_one_mem_rootSpace_slTwoRoot (c : K) :
    SpecialLinear.single (0 : Fin 2) 1 zero_ne_one c ∈
      rootSpace (slTwoDiagonalCartan K) (slTwoRoot K) :=
  weightSpace_le_genWeightSpace _ _ ((mem_weightSpace _ _).mpr fun x ↦
    lie_single_zero_one_of_mem x c)

/-- `f = E₁₀` is a root vector for the negative of the simple root. -/
theorem single_one_zero_mem_rootSpace_neg_slTwoRoot (c : K) :
    SpecialLinear.single (1 : Fin 2) 0 one_ne_zero c ∈
      rootSpace (slTwoDiagonalCartan K) (-slTwoRoot K) :=
  weightSpace_le_genWeightSpace _ _ ((mem_weightSpace _ _).mpr fun x ↦
    lie_single_one_zero_of_mem x c)

/-- The base `slTwoPositiveBase` selects `e = E₀₁` as positive. -/
theorem slTwoPositiveBase_positive_generator :
    ∃ i ∈ (slTwoPositiveBase K).support,
      SpecialLinear.single (0 : Fin 2) 1 zero_ne_one (1 : K) ∈
        rootSpace (slTwoDiagonalCartan K)
          ((IsKilling.rootSystem (slTwoDiagonalCartan K)).root i) :=
  ⟨slTwoRootIndex K, slTwoRootIndex_mem_support,
    single_zero_one_mem_rootSpace_slTwoRoot 1⟩

/-- The coroot of the simple root is `h = E₀₀ - E₁₁`. -/
@[simp]
theorem coroot_slTwoRoot : IsKilling.coroot (slTwoRoot K) = slTwoCartanGenerator K :=
  Subtype.ext <| ((isSl2Triple_single (R := K) (zero_ne_one' (Fin 2))).h_eq_coroot
    slTwoRoot_isNonZero (single_zero_one_mem_rootSpace_slTwoRoot 1)
    (single_one_zero_mem_rootSpace_neg_slTwoRoot 1)).symm

/-! ### The positive roots and the Weyl denominator -/

/-- The simple root `α`, as a linear form on the diagonal Cartan, is the weight `2`. -/
theorem toLinear_slTwoRoot : (slTwoRoot K).toLinear = slTwoWeight (2 : K) :=
  dual_ext_slTwoCartanGenerator <| by
    rw [Weight.toLinear_apply, slTwoRoot_slTwoCartanGenerator, slTwoWeight_slTwoCartanGenerator]

/-- **The only positive root of `sl₂` is the simple root `α`.** -/
theorem posRootsFinset_slTwoPositiveBase :
    posRootsFinset (IsKilling.rootSystem (slTwoDiagonalCartan K)) (slTwoPositiveBase K) =
      {slTwoRootIndex K} := by
  have hpos : slTwoRootIndex K ∈
      posRoots (IsKilling.rootSystem (slTwoDiagonalCartan K)) (slTwoPositiveBase K) :=
    support_subset_posRoots _ _ slTwoRootIndex_mem_support
  ext i
  rw [mem_posRootsFinset, Finset.mem_singleton]
  refine ⟨fun hi ↦ (eq_slTwoRootIndex_or_eq_reflectionPerm i).resolve_right ?_,
    fun hi ↦ hi ▸ hpos⟩
  rintro rfl
  exact reflectionPerm_self_notMem_posRoots _ _ hpos hi

/-- **The Weyl denominator of `sl₂`** is `1 - e^{-α}`, where `-α` is the weight `-2`. -/
theorem weylDenominator_slTwoPositiveBase :
    weylDenominator (IsKilling.rootSystem (slTwoDiagonalCartan K)) (slTwoPositiveBase K) =
      1 - AddMonoidAlgebra.single (slTwoWeight (-2 : K)) 1 := by
  rw [weylDenominator_def, posRootsFinset_slTwoPositiveBase, Finset.prod_singleton,
    IsKilling.rootSystem_root_apply, coe_slTwoRootIndex, toLinear_slTwoRoot]
  congr 2
  exact dual_ext_slTwoCartanGenerator <| by simp

end Field

end TauCeti
