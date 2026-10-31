/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim
public import TauCeti.CategoryTheory.Semisimple.Character

/-!
# The dimension character and the nonvanishing of the global dimension

Let `C` be a pivotal category which is `k`-linear, for an algebraically closed field `k`, whose
tensor unit is simple with finite-dimensional endomorphisms. Reading the left dimension in `k`
through `TauCeti.endAlgEquivOfSimple k (𝟙_ C)`, it is additive on biproducts, `1` on the unit,
and multiplicative on tensor products, because every scalar acts on every object in the same way
from the left and from the right (`TauCeti.leftDim_tensor_eq_comp_of_simple`). So it is a ring
homomorphism from the Grothendieck ring, the *left dimension character*
`TauCeti.SplitK0.leftDimChar k C`, with a mirror `TauCeti.SplitK0.rightDimChar k C`; the duality
`[X] ↦ [Xᘁ]` exchanges them, and they coincide in a spherical category.

For a fusion category over a field of characteristic zero this gives the theorem of
Etingof–Nikshych–Ostrik that the global dimension
`globalDim C = ∑ S, leftDim S ≫ leftDim Sᘁ` is nonzero:

1. the global dimension is the scalar `∑ S, χ [S] * χ [Sᘁ]`, where `χ` is the left dimension
   character (`TauCeti.globalDim_eq_sum_leftDimChar_smul`);
2. the values of `χ` are algebraic integers, since the Grothendieck ring is a finitely generated
   abelian group (`TauCeti.SplitK0.isIntegral_ringHom_apply`), so they lie in the algebraic
   closure of `ℚ` in `k`, which embeds into `ℂ` by some `σ`;
3. every ring homomorphism `ψ` from the Grothendieck ring to `ℂ` satisfies
   `ψ [Sᘁ] = conj (ψ [S])` (`TauCeti.SplitK0.ringHom_apply_dual`);
4. so `σ` sends the global dimension to `∑ S, |σ (χ [S])|²`, which is at least
   `|σ (χ [𝟙_ C])|² = 1`.

Characteristic zero is used exactly in the second step. It cannot be dropped: over an
algebraically closed field of characteristic `p > 0`, the pointed fusion category of
`ℤ/p`-graded vector spaces has `p` simple objects, each of dimension `1` for its standard pivotal
structure, so its global dimension is `p = 0`.

## Main declarations

* `TauCeti.SplitK0.leftDimChar` and `TauCeti.SplitK0.rightDimChar`: the left and right dimension
  characters of the Grothendieck ring;
* `TauCeti.globalDim_eq_sum_leftDimChar_smul`: the global dimension as a scalar;
* `TauCeti.globalDim_ne_zero`: the global dimension of a pivotal fusion category over a field of
  characteristic zero is nonzero.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Theorem 2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ComplexConjugate

universe w w' v u

namespace TauCeti

namespace SplitK0

section Character

variable (k : Type w') [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [HasKernels C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C] [Simple (𝟙_ C)]
  [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]

/-- The left dimension, read in `k`, as a biproduct-additive invariant. -/
private noncomputable def leftDimInvariant : AdditiveInvariant C k where
  obj X := endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X))
  map_iso _ _ e := by rw [leftDim_congr e]
  map_biprod X Y := by rw [leftDim_biprod, End.of_add, map_add]

/-- The right dimension, read in `k`, as a biproduct-additive invariant. -/
private noncomputable def rightDimInvariant : AdditiveInvariant C k where
  obj X := endAlgEquivOfSimple k (𝟙_ C) (End.of (rightDim X))
  map_iso _ _ e := by rw [rightDim_congr e]
  map_biprod X Y := by rw [rightDim_biprod, End.of_add, map_add]

/-- The *left dimension character* of a pivotal category whose tensor unit is simple with
finite-dimensional endomorphisms over an algebraically closed field `k`: the ring homomorphism
from the Grothendieck ring to `k` sending the class of `X` to its left dimension, read in `k`. -/
noncomputable def leftDimChar : SplitK0 C →+* k :=
  liftRingHom (leftDimInvariant k C)
    (by simp [leftDimInvariant, leftDim_unit])
    (fun X Y ↦ by simp [leftDimInvariant, leftDim_tensor_eq_comp_of_simple k, mul_comm])

/-- The *right dimension character* of a pivotal category whose tensor unit is simple with
finite-dimensional endomorphisms over an algebraically closed field `k`: the ring homomorphism
from the Grothendieck ring to `k` sending the class of `X` to its right dimension, read in `k`. -/
noncomputable def rightDimChar : SplitK0 C →+* k :=
  liftRingHom (rightDimInvariant k C)
    (by simp [rightDimInvariant, rightDim_unit])
    (fun X Y ↦ by simp [rightDimInvariant, rightDim_tensor_eq_comp_of_simple k, mul_comm])

variable {C}

/-- The left dimension character sends the class of `X` to the left dimension of `X`, read
in `k`. -/
@[simp]
theorem leftDimChar_of (X : C) :
    leftDimChar k C (of X) = endAlgEquivOfSimple k (𝟙_ C) (End.of (leftDim X)) :=
  liftRingHom_of _ _ _ X

/-- The right dimension character sends the class of `X` to the right dimension of `X`, read
in `k`. -/
@[simp]
theorem rightDimChar_of (X : C) :
    rightDimChar k C (of X) = endAlgEquivOfSimple k (𝟙_ C) (End.of (rightDim X)) :=
  liftRingHom_of _ _ _ X

/-- The left dimension of `X` is the value of the left dimension character at `[X]` times the
identity of the unit. -/
theorem leftDimChar_of_smul_id (X : C) : leftDimChar k C (of X) • 𝟙 (𝟙_ C) = leftDim X := by
  rw [leftDimChar_of, endAlgEquivOfSimple_smul_id]

/-- The right dimension of `X` is the value of the right dimension character at `[X]` times the
identity of the unit. -/
theorem rightDimChar_of_smul_id (X : C) : rightDimChar k C (of X) • 𝟙 (𝟙_ C) = rightDim X := by
  rw [rightDimChar_of, endAlgEquivOfSimple_smul_id]

/-- The left dimension character of the dual class is the right dimension character, since
`leftDim Xᘁ = rightDim X`. -/
@[simp]
theorem leftDimChar_dual (x : SplitK0 C) : leftDimChar k C (dual x) = rightDimChar k C x := by
  refine DFunLike.congr_fun (hom_ext (f := (leftDimChar k C : SplitK0 C →+ k).comp dual)
    (g := (rightDimChar k C : SplitK0 C →+ k)) fun X ↦ ?_) x
  simp [leftDim_rightDual]

/-- The right dimension character of the dual class is the left dimension character, since
`rightDim Xᘁ = leftDim X`. -/
@[simp]
theorem rightDimChar_dual (x : SplitK0 C) : rightDimChar k C (dual x) = leftDimChar k C x := by
  refine DFunLike.congr_fun (hom_ext (f := (rightDimChar k C : SplitK0 C →+ k).comp dual)
    (g := (leftDimChar k C : SplitK0 C →+ k)) fun X ↦ ?_) x
  simp [rightDim_rightDual]

/-- In a spherical category the left and right dimension characters agree. -/
theorem leftDimChar_eq_rightDimChar [SphericalCategory C] : leftDimChar k C = rightDimChar k C := by
  ext X
  simp [leftDim_eq_rightDim]

end Character

end SplitK0

section GlobalDim

variable (k : Type w') [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [HasKernels C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C] [Simple (𝟙_ C)]
  [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)] [Fintype (SimpleClasses C)]

/-- The global dimension is the scalar `∑ S, χ [S] * χ [Sᘁ]` times the identity of the unit,
where `χ` is the left dimension character. -/
theorem globalDim_eq_sum_leftDimChar_smul :
    globalDim C = (∑ S : SimpleClasses C,
      SplitK0.leftDimChar k C (SplitK0.of S.repr) *
        SplitK0.leftDimChar k C (SplitK0.of (S.repr)ᘁ)) • 𝟙 (𝟙_ C) := by
  rw [globalDim_def, Finset.sum_smul]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← SplitK0.leftDimChar_of_smul_id k S.repr, ← SplitK0.leftDimChar_of_smul_id k (S.repr)ᘁ,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]

end GlobalDim

section NeZero

variable (k : Type w') [Field k] [IsAlgClosed k] [CharZero k]
variable (C : Type u) [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C] [PivotalCategory C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [Simple (𝟙_ C)]
  [Fintype (SimpleClasses C)]

include k in
/-- **The global dimension of a pivotal fusion category over a field of characteristic zero is
nonzero** (Etingof–Nikshych–Ostrik). Here `C` is pivotal, `k`-linear abelian and finite semisimple
over an algebraically closed field `k` of characteristic zero, with finite-dimensional morphism
spaces, simple tensor unit, and finitely many simple classes. -/
theorem globalDim_ne_zero : globalDim C ≠ 0 := by
  have : EssentiallySmall.{max u v} C := essentiallySmall_of_small_of_locallySmall C
  let χ : SplitK0.{max u v} C →+* k := SplitK0.leftDimChar k C
  -- The values of `χ` are algebraic integers, so they lie in the algebraic closure of `ℚ` in `k`,
  -- which embeds into `ℂ`.
  have hχ (x : SplitK0 C) : χ x ∈ algebraicClosure ℚ k :=
    mem_algebraicClosure_iff'.2 (SplitK0.isIntegral_ringHom_apply χ x).tower_top
  let σ : algebraicClosure ℚ k →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ψ : SplitK0 C →+* ℂ := (σ : algebraicClosure ℚ k →+* ℂ).comp (χ.codRestrict _ hχ)
  intro h
  rw [globalDim_eq_sum_leftDimChar_smul k, smul_eq_zero, or_iff_left (id_nonzero _)] at h
  -- Transport the vanishing scalar `∑ S, χ [S] * χ [Sᘁ]` to `ℂ` along `σ`.
  have h₁ : ∑ S : SimpleClasses C, ψ (SplitK0.of S.repr) * ψ (SplitK0.of (S.repr)ᘁ) = 0 := by
    have h₀ : ∑ S : SimpleClasses C, χ.codRestrict _ hχ (SplitK0.of S.repr) *
        χ.codRestrict _ hχ (SplitK0.of (S.repr)ᘁ) = 0 :=
      Subtype.ext (by simpa [χ] using h)
    simpa [ψ, map_sum, map_mul] using congrArg σ h₀
  -- Since `ψ [Sᘁ] = conj (ψ [S])`, the sum is `∑ S, |ψ [S]|²`.
  have h₂ : ∑ S : SimpleClasses C, Complex.normSq (ψ (SplitK0.of S.repr)) = 0 := by
    rw [← Complex.ofReal_inj, Complex.ofReal_sum, Complex.ofReal_zero, ← h₁]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [← SplitK0.dual_of, SplitK0.ringHom_apply_dual k ψ, Complex.mul_conj]
  -- But the term of the unit class is `|ψ 1|² = 1`.
  have h₃ := (Finset.sum_eq_zero_iff_of_nonneg fun S _ ↦ Complex.normSq_nonneg _).1 h₂
    (SimpleClasses.classOf (𝟙_ C)) (Finset.mem_univ _)
  rw [← SplitK0.simpleBasis_apply, ← SplitK0.one_eq_simpleBasis, map_one, map_one] at h₃
  exact one_ne_zero h₃

end NeZero

end TauCeti
