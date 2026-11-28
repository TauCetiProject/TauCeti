/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Skew-symmetric bilinear forms modulo norms

Let the group `C₂` act on the bilinear forms on a module `M` over a commutative ring `R` by
`B ↦ -B.flip`; this is the action on forms with values in the sign-twisted coefficient `-R`. Its
fixed points are the skew-symmetric forms, `B y x = -B x y`
(`LinearMap.BilinForm.skewSubmodule`, in `TauCeti.LinearAlgebra.BilinearForm.Symmetric`), and
its norms are the forms `C - C.flip` (`LinearMap.BilinForm.skewNorm`). The quotient of the former
by the latter is the zeroth Tate cohomology group of `C₂` with coefficients in the bilinear forms.
This file computes it for a projective module `M` through the diagonal `B ↦ (x ↦ B x x)`
(`LinearMap.BilinForm.skewDiagonal`).

The diagonal of a skew-symmetric form is a quadratic form with zero polar form: an additive map
`Q` with `Q (r • x) = r ^ 2 * Q x`, whose values are therefore killed by `2`. Equivalently, it is
an `R`-linear map from `M` to the `2`-torsion of `R`, on which `R` acts through `r ↦ r ^ 2`. The
diagonal of a norm vanishes. For projective `M` both bounds are attained:

* `LinearMap.BilinForm.IsAlt.exists_sub_flip_eq`: every alternating form on a projective module
  is a norm `C - C.flip`. Conversely every norm is alternating
  (`LinearMap.BilinForm.isAlt_sub_flip`). So the forms in the image of the norm for `-R`, the
  `(-1)`-even forms, are exactly the alternating forms.
* `LinearMap.BilinForm.mem_range_skewDiagonal`: on a projective module, the diagonals of the
  skew-symmetric forms are exactly the quadratic forms with zero polar form.
* `LinearMap.BilinForm.exact_skewNorm_skewDiagonal`: on a projective module, the skew-symmetric
  forms with vanishing diagonal are exactly the norms. So the diagonal identifies the
  skew-symmetric forms modulo norms with the quadratic forms of zero polar form.

None of this needs `2` to be invertible, and the Tate group need not vanish: for nonzero `a : R`
with `2 * a = 0`, the form `(x, y) ↦ a * (x * y)` on `R` is skew-symmetric but is not a norm
(`LinearMap.BilinForm.smul_mul_mem_skewSubmodule`,
`LinearMap.BilinForm.sub_flip_ne_smul_mul`).

## Main definitions

* `LinearMap.BilinForm.skewNorm`: the norm `C ↦ C - C.flip`, valued in skew-symmetric forms.
* `LinearMap.BilinForm.skewDiagonal`: the diagonal `B ↦ (x ↦ B x x)` of a skew-symmetric form.

## References

* B. Calmès, E. Dotto, Y. Harpaz, F. Hebestreit, M. Land, K. Moi, D. Nardin, T. Nikolaus,
  W. Steimle, *Hermitian K-theory for stable ∞-categories III: Grothendieck–Witt groups of
  rings*, Remark R.7.
-/

public section

open LinearMap (BilinForm)
open QuadraticMap

namespace LinearMap.BilinForm

variable {R : Type*} [CommRing R]

section AddCommMonoid

variable (R) (M : Type*) [AddCommMonoid M] [Module R M]

/-- The norm `C ↦ C - C.flip` of the involution `B ↦ -B.flip`, as a linear map into the
skew-symmetric bilinear forms. -/
def skewNorm : BilinForm R M →ₗ[R] skewSubmodule R M where
  toFun C := ⟨C - C.flip, mem_skewSubmodule.2 fun x y => by simp⟩
  map_add' C₁ C₂ := Subtype.ext <| LinearMap.ext₂ fun x y => by simp; abel
  map_smul' c C := Subtype.ext <| LinearMap.ext₂ fun x y => by simp [mul_sub]

/-- The diagonal `B ↦ (x ↦ B x x)` of a skew-symmetric bilinear form, as a quadratic form. -/
def skewDiagonal : skewSubmodule R M →ₗ[R] QuadraticForm R M :=
  BilinMap.toQuadraticMapLinearMap R R M ∘ₗ (skewSubmodule R M).subtype

variable {R M}

@[simp]
theorem coe_skewNorm_apply (C : BilinForm R M) :
    (skewNorm R M C : BilinForm R M) = C - C.flip :=
  (rfl)

@[simp]
theorem skewDiagonal_apply (B : skewSubmodule R M) :
    skewDiagonal R M B = (B : BilinForm R M).toQuadraticMap :=
  (rfl)

/-- **The Tate group of skew-symmetric forms.** On a projective module, the skew-symmetric forms
whose diagonal vanishes are exactly the norms `C - C.flip`. Together with
`LinearMap.BilinForm.mem_range_skewDiagonal`, the diagonal identifies the skew-symmetric forms
modulo norms with the quadratic forms of zero polar form. -/
theorem exact_skewNorm_skewDiagonal [Module.Projective R M] :
    Function.Exact (skewNorm R M) (skewDiagonal R M) := fun B => by
  refine ⟨fun hB => ?_, ?_⟩
  · rw [skewDiagonal_apply] at hB
    obtain ⟨C, hC⟩ := IsAlt.exists_sub_flip_eq (BilinMap.toQuadraticMap_eq_zero.mp hB)
    exact ⟨C, Subtype.ext hC⟩
  · rintro ⟨C, rfl⟩
    ext x
    simp

end AddCommMonoid

section AddCommGroup

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A bilinear form is skew-symmetric exactly when the polar form of its diagonal vanishes. -/
theorem mem_skewSubmodule_iff_polarBilin_toQuadraticMap_eq_zero {B : BilinForm R M} :
    B ∈ skewSubmodule R M ↔ polarBilin B.toQuadraticMap = 0 := by
  simp [BilinMap.polarBilin_toQuadraticMap, LinearMap.ext_iff, eq_neg_iff_add_eq_zero, add_comm]

/-- On a free module every quadratic form with zero polar form is the diagonal of a
skew-symmetric bilinear form: its triangular bilinear form `QuadraticMap.toBilin` is diagonal. -/
private theorem exists_mem_skewSubmodule_toQuadraticMap_eq_of_free [Module.Free R M]
    {Q : QuadraticForm R M} (hQ : polarBilin Q = 0) :
    ∃ B ∈ skewSubmodule R M, B.toQuadraticMap = Q := by
  let b := Module.Free.chooseBasis R M
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    IsWellOrder.linearOrder WellOrderingRel
  have hpolar (x y : M) : polar Q x y = 0 := by
    simpa using LinearMap.congr_fun₂ hQ x y
  refine ⟨Q.toBilin b, mem_skewSubmodule.2 ?_, toQuadraticMap_toBilin Q b⟩
  have hflip : (Q.toBilin b).flip = -Q.toBilin b := by
    refine b.ext fun i => b.ext fun j => ?_
    rcases eq_or_ne i j with rfl | h
    · have h2 : Q (b i) + Q (b i) = 0 := by rw [← two_nsmul, ← polar_self, hpolar]
      simpa [toBilin_apply, eq_neg_iff_add_eq_zero] using h2
    · simp [toBilin_apply, h, h.symm, hpolar]
  intro x y
  simpa using LinearMap.congr_fun₂ hflip x y

/-- On a projective module, the quadratic forms with zero polar form are exactly the diagonals of
the skew-symmetric bilinear forms. -/
theorem mem_range_skewDiagonal [Module.Projective R M] {Q : QuadraticForm R M} :
    Q ∈ LinearMap.range (skewDiagonal R M) ↔ polarBilin Q = 0 := by
  constructor
  · rintro ⟨B, rfl⟩
    rw [skewDiagonal_apply]
    exact mem_skewSubmodule_iff_polarBilin_toQuadraticMap_eq_zero.mp B.property
  intro hQ
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := R) (P := M)).mp ‹_›
  let π := Finsupp.linearCombination R (_root_.id : M → M)
  have hπ (x : M) : π (s x) = x := LinearMap.congr_fun hs x
  obtain ⟨B, hB, hBQ⟩ := exists_mem_skewSubmodule_toQuadraticMap_eq_of_free
    (Q := Q.comp π) (by rw [polarBilin_comp, hQ]; ext; simp)
  refine ⟨⟨B.compl₁₂ s s, mem_skewSubmodule.2 fun x y => by
    simpa using mem_skewSubmodule.1 hB (s x) (s y)⟩, ?_⟩
  ext x
  simpa [hπ] using congr($hBQ (s x))

end AddCommGroup

/-- The form `(x, y) ↦ a * (x * y)` on `R` is skew-symmetric when `2 * a = 0`. -/
theorem smul_mul_mem_skewSubmodule {a : R} (ha : 2 * a = 0) :
    a • LinearMap.mul R R ∈ skewSubmodule R R := by
  refine mem_skewSubmodule.2 fun x y => ?_
  simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  linear_combination (x * y) * ha

/-- **The Tate group need not vanish.** For `a ≠ 0`, the form `(x, y) ↦ a * (x * y)` on `R` is
not a norm `C - C.flip`, since its diagonal does not vanish at `1`. When `2 * a = 0` it is
skew-symmetric (`LinearMap.BilinForm.smul_mul_mem_skewSubmodule`); over `ZMod 2` with `a = 1` it
is the skew-symmetric line `(x, y) ↦ x * y`. -/
theorem sub_flip_ne_smul_mul {a : R} (ha : a ≠ 0) (C : BilinForm R R) :
    C - C.flip ≠ a • LinearMap.mul R R := by
  intro h
  exact ha (by simpa using congr($h 1 1) : (0 : R) = a).symm

end LinearMap.BilinForm
