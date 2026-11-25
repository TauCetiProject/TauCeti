/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Dimension.Basis

/-!
# The standard polarized symplectic space `X × X*`

For a module `X` over a commutative ring `R`, the product `X × X*` of `X` with its dual
`X* = Module.Dual R X` carries the alternating form
`polarizationForm R X ((x, y), (x', y')) = y' x - y x'`.
It is the model of a symplectic space with a chosen *full polarization*: the factor `X × {0}` is
always Lagrangian, and when `X` is projective `{0} × X*` is Lagrangian too, so the two factors
are complementary Lagrangians; `(x, 0)` pairs with `(0, y)` to `y x`. Over a field every
finite-dimensional nondegenerate alternating space of dimension `2 * dim X` is isometric to it, so
a statement about symplectic spaces may be proved in these coordinates and transported. This is
the space on whose functions `X → ℂ` the Schrödinger and Weil representations of a finite
symplectic space act.

In block form with respect to `X × X*`, three families of linear automorphisms preserve the form:

* the Levi elements `m(A) = (A, 0; 0, A⁻ᵀ)`, `(x, y) ↦ (A x, y ∘ A⁻¹)`, for every linear
  automorphism `A` of `X`, forming a group homomorphism from `X ≃ₗ[R] X`;
* the lower shears `u(C) = (1, 0; C, 1)`, `(x, y) ↦ (x, y + C x)`, for every symmetric bilinear
  form `C` on `X` (read as a map `X → X*`), forming a group homomorphism from the additive group
  of symmetric forms;
* the rotation `J = (0, e⁻¹; -e, 0)`, `(x, y) ↦ (e⁻¹ y, -e x)`, for every symmetric
  identification `e : X ≃ₗ[R] X*`; in coordinates `X = Rⁿ` with `e` the dot product this is
  `(x, y) ↦ (y, -x)`, and `J² = -1`.

The sign convention `y' x - y x'` fixes the sign of the Gram matrix relative to Mathlib's
`Matrix.J`: in the basis `(eᵢ, 0)`, `(0, eⱼ*)` the Gram matrix of `polarizationForm` is the
negative of `Matrix.J`, so the basis `(eᵢ, 0)`, `(0, -eⱼ*)` has Gram matrix `Matrix.J`
(`TauCeti.toMatrix_polarizationForm`).

Over the reals this form, packaged as a `SymplecticForm`, is `TauCeti.cotangentSymplecticForm`.

## Main definitions

* `TauCeti.polarizationForm R X`: the form `((x, y), (x', y')) ↦ y' x - y x'` on `X × X*`.
* `Module.Basis.polarizationBasis b`: the basis `(bᵢ, 0)`, `(0, -bⱼ*)` of `X × X*` built from a
  basis `b` of `X`.
* `TauCeti.polarizationLevi R X`: the homomorphism `A ↦ m(A)` into the isometry group.
* `TauCeti.polarizationShear R X`: the homomorphism `C ↦ u(C)` into the isometry group.
* `LinearEquiv.polarizationJ e he`: the rotation `J` attached to a symmetric `e : X ≃ₗ[R] X*`.

## Main results

* `TauCeti.polarizationForm_isAlt`, `TauCeti.polarizationForm_nondegenerate`: the form is
  alternating, and nondegenerate when `X` is projective (for instance a vector space).
* `TauCeti.orthogonal_range_inl_polarizationForm`,
  `TauCeti.orthogonal_range_inr_polarizationForm`: `X × {0}` and `{0} × X*` are Lagrangian.
* `TauCeti.toMatrix_polarizationForm`: the Gram matrix in `polarizationBasis b` is `Matrix.J`.
* `LinearMap.BilinForm.IsAlt.nonempty_isometryEquiv_polarizationForm`: a nondegenerate
  alternating form on a space of dimension `2 * dim X` is isometric to `polarizationForm K X`.

## References

* M. Neuhauser, *An explicit construction of the metaplectic representation over a finite
  field*, J. Lie Theory 12 (2002), 15–30, §3 (the generators `m(A)`, `u(C)` and `J`).
-/

public section

open LinearMap (BilinForm isometryGroup mem_isometryGroup_iff)
open LinearMap.BilinForm Module

namespace TauCeti

section CommRing

variable (R X : Type*) [CommRing R] [AddCommGroup X] [Module R X]

/-- The standard alternating form on `X × X*`, `((x, y), (x', y')) ↦ y' x - y x'`. The factor
`X × {0}` is Lagrangian for it, and when `X` is projective so is `{0} × X*`, making the two factors
complementary Lagrangians; over a field every finite-dimensional nondegenerate alternating space of
dimension `2 * dim X` is isometric to it. -/
def polarizationForm : BilinForm R (X × Dual R X) :=
  LinearMap.mk₂ R (fun v w ↦ w.2 v.1 - v.2 w.1)
    (fun v v' w ↦ by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; abel)
    (fun c v w ↦ by simp [mul_sub])
    (fun v w w' ↦ by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; abel)
    (fun c v w ↦ by simp [mul_sub])

variable {R X}

@[simp]
theorem polarizationForm_apply (v w : X × Dual R X) :
    polarizationForm R X v w = w.2 v.1 - v.2 w.1 := (rfl)

variable (R X)

/-- The standard polarized form is alternating: its value at `(v, v)` is `y x - y x = 0`. -/
theorem polarizationForm_isAlt : (polarizationForm R X).IsAlt :=
  fun _ ↦ sub_self _

/-- The vectors `(x, 0)` form a Lagrangian for the standard polarized form: they pair trivially with
each other, and a vector `(x', y')` orthogonal to all of them has `y' = 0`. -/
@[simp]
theorem orthogonal_range_inl_polarizationForm :
    (polarizationForm R X).orthogonal (LinearMap.range (LinearMap.inl R X (Dual R X))) =
      LinearMap.range (LinearMap.inl R X (Dual R X)) := by
  ext v
  simp only [mem_orthogonal_iff, LinearMap.mem_range, LinearMap.inl_apply,
    forall_exists_index, forall_apply_eq_imp_iff, polarizationForm_apply, sub_zero,
    LinearMap.zero_apply]
  refine ⟨fun h ↦ ⟨v.1, Prod.ext rfl (LinearMap.ext fun x ↦ (h x).symm)⟩, ?_⟩
  rintro ⟨x', rfl⟩ _
  simp

variable [Projective R X]

/-- The vectors `(0, y)` form a Lagrangian for the standard polarized form when `X` is projective:
they pair trivially with each other, and a vector `(x', y')` orthogonal to all of them has
`y x' = 0` for every functional `y`, hence `x' = 0`. -/
@[simp]
theorem orthogonal_range_inr_polarizationForm :
    (polarizationForm R X).orthogonal (LinearMap.range (LinearMap.inr R X (Dual R X))) =
      LinearMap.range (LinearMap.inr R X (Dual R X)) := by
  ext v
  simp only [mem_orthogonal_iff, LinearMap.mem_range, LinearMap.inr_apply,
    forall_exists_index, forall_apply_eq_imp_iff, polarizationForm_apply, map_zero, zero_sub,
    neg_eq_zero]
  refine ⟨fun h ↦ ⟨v.2, Prod.ext ((forall_dual_apply_eq_zero_iff R v.1).mp h).symm rfl⟩, ?_⟩
  rintro ⟨y', rfl⟩ y
  simp

/-- The standard polarized form is nondegenerate when `X` is projective, for instance when `X` is a
vector space: pairing with `(x', 0)` detects the functional, and pairing with `(0, y')` detects the
vector, since the functionals on a projective module separate its points. -/
theorem polarizationForm_nondegenerate : (polarizationForm R X).Nondegenerate := by
  refine ((polarizationForm_isAlt R X).isRefl).nondegenerate_iff_separatingLeft.mpr fun v h ↦ ?_
  have h₁ : v.1 = 0 := (forall_dual_apply_eq_zero_iff R v.1).mp fun y ↦ by simpa using h (0, y)
  have h₂ : v.2 = 0 := LinearMap.ext fun x ↦ by simpa [h₁] using h (x, 0)
  exact Prod.ext h₁ h₂

end CommRing

end TauCeti

namespace Module.Basis

open TauCeti

variable {R X ι : Type*} [CommRing R] [AddCommGroup X] [Module R X] [DecidableEq ι]

/-- The basis `(bᵢ, 0)`, `(0, -bⱼ*)` of `X × X*` built from a finite basis `b` of `X` and its dual
basis. The vectors `(bᵢ, 0)` span the Lagrangian `X × {0}` and occupy the positions `Sum.inl i`;
the sign on the dual vectors makes the Gram matrix of `polarizationForm` equal to `Matrix.J`
(`TauCeti.toMatrix_polarizationForm`). -/
noncomputable def polarizationBasis [Finite ι] (b : Basis ι R X) : Basis (ι ⊕ ι) R (X × Dual R X) :=
  b.prod (b.dualBasis.map (LinearEquiv.neg R))

@[simp]
theorem polarizationBasis_inl [Finite ι] (b : Basis ι R X) (i : ι) :
    polarizationBasis b (Sum.inl i) = (b i, 0) := by
  simp [polarizationBasis]

@[simp]
theorem polarizationBasis_inr [Finite ι] (b : Basis ι R X) (i : ι) :
    polarizationBasis b (Sum.inr i) = (0, -b.dualBasis i) := by
  simp [polarizationBasis]

end Module.Basis

namespace TauCeti

/-- **The standard polarized space has a symplectic basis**: the Gram matrix of `polarizationForm`
in `polarizationBasis b` is Mathlib's standard symplectic matrix `Matrix.J`. -/
theorem toMatrix_polarizationForm {R X ι : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [DecidableEq ι] [Fintype ι] (b : Basis ι R X) :
    BilinForm.toMatrix b.polarizationBasis (polarizationForm R X) = Matrix.J ι R := by
  ext (i | i) (j | j) <;>
    simp [BilinForm.toMatrix_apply, Matrix.J, Matrix.one_apply, Finsupp.single_apply, eq_comm]

section Isometries

variable (R X : Type*) [CommRing R] [AddCommGroup X] [Module R X]

/-- The Levi elements of the standard polarized space: a linear automorphism `A` of `X` acts on
`X × X*` by `m(A) = (A, 0; 0, A⁻ᵀ)`, that is `(x, y) ↦ (A x, y ∘ A⁻¹)`, an isometry of
`polarizationForm R X`. The assignment `A ↦ m(A)` is a group homomorphism. -/
def polarizationLevi : (X ≃ₗ[R] X) →* isometryGroup (polarizationForm R X) where
  toFun A := ⟨A.prodCongr A.symm.dualMap, mem_isometryGroup_iff.mpr fun v w ↦ by simp⟩
  map_one' := by ext <;> simp [LinearEquiv.one_eq_refl]
  map_mul' _ _ := by ext <;> simp [LinearEquiv.mul_eq_trans]

variable {R X}

@[simp]
theorem polarizationLevi_apply (A : X ≃ₗ[R] X) (v : X × Dual R X) :
    (polarizationLevi R X A : (X × Dual R X) ≃ₗ[R] X × Dual R X) v = (A v.1, A.symm.dualMap v.2) :=
  (rfl)

variable (R X)

/-- The lower shears of the standard polarized space: a symmetric bilinear form `C` on `X`, read as
a linear map `X → X*`, acts on `X × X*` by `u(C) = (1, 0; C, 1)`, that is `(x, y) ↦ (x, y + C x)`,
an isometry of `polarizationForm R X` because `C x' x = C x x'`. The assignment `C ↦ u(C)` is a
group homomorphism from the additive group of symmetric forms. -/
def polarizationShear :
    Multiplicative (symmSubmodule R X) →* isometryGroup (polarizationForm R X) where
  toFun C := ⟨(LinearEquiv.refl R X).skewProd (LinearEquiv.refl R (Dual R X))
      (C.toAdd : BilinForm R X), mem_isometryGroup_iff.mpr fun v w ↦ by
    have hC := (mem_symmSubmodule.mp C.toAdd.property).eq v.1 w.1
    simp only [LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, polarizationForm_apply,
      LinearMap.add_apply]
    rw [hC]
    abel⟩
  map_one' := by ext <;> simp
  map_mul' C C' := by
    ext v
    · simp [mul_apply_eq_comp]
    · simp only [toAdd_mul, Submodule.coe_add, LinearEquiv.skewProd_apply, LinearEquiv.refl_apply,
        LinearMap.add_apply, Subgroup.coe_mul, mul_apply_eq_comp]
      abel

variable {R X}

@[simp]
theorem polarizationShear_apply (C : Multiplicative (symmSubmodule R X)) (v : X × Dual R X) :
    (polarizationShear R X C : (X × Dual R X) ≃ₗ[R] X × Dual R X) v =
      (v.1, v.2 + (C.toAdd : BilinForm R X) v.1) :=
  (rfl)

end Isometries

end TauCeti

namespace LinearEquiv

open TauCeti

variable {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]

/-- The rotation `J` of the standard polarized space attached to a symmetric linear identification
`e : X ≃ₗ[R] X*`: it acts by `(x, y) ↦ (e⁻¹ y, -e x)`, block form `(0, e⁻¹; -e, 0)`. In coordinates
`X = Rⁿ` with `e` the dot product this is `(x, y) ↦ (y, -x)`, the negative of the action of
Mathlib's `Matrix.J`. -/
def polarizationJ (e : X ≃ₗ[R] Dual R X) (he : ∀ x x', e x x' = e x' x) :
    isometryGroup (polarizationForm R X) :=
  ⟨(LinearEquiv.prodComm R X (Dual R X)).trans (e.symm.prodCongr (e.trans (LinearEquiv.neg R))),
    mem_isometryGroup_iff.mpr fun v w ↦ by
      simp only [LinearEquiv.trans_apply, LinearEquiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, LinearEquiv.prodCongr_apply, LinearEquiv.neg_apply, polarizationForm_apply,
        LinearMap.neg_apply, he _ (e.symm _), LinearEquiv.apply_symm_apply]
      abel⟩

@[simp]
theorem polarizationJ_apply (e : X ≃ₗ[R] Dual R X) (he : ∀ x x', e x x' = e x' x)
    (v : X × Dual R X) :
    (e.polarizationJ he : (X × Dual R X) ≃ₗ[R] X × Dual R X) v = (e.symm v.2, -e v.1) :=
  (rfl)

/-- The rotation `J` squares to `-1`. -/
theorem polarizationJ_mul_self_apply (e : X ≃ₗ[R] Dual R X) (he : ∀ x x', e x x' = e x' x)
    (v : X × Dual R X) :
    ((e.polarizationJ he * e.polarizationJ he : isometryGroup (polarizationForm R X)) :
      (X × Dual R X) ≃ₗ[R] X × Dual R X) v = -v := by
  ext <;> simp

end LinearEquiv

namespace LinearMap.BilinForm

open TauCeti

/-- **Classification of symplectic spaces by dimension**: a nondegenerate alternating form on a
finite-dimensional space of dimension `2 * dim X` is isometric to the standard polarized form on
`X × X*`. -/
theorem IsAlt.nonempty_isometryEquiv_polarizationForm {K V X : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : finrank K V = 2 * finrank K X) :
    Nonempty (B.IsometryEquiv (polarizationForm K X)) := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  have hm : finrank K X = m := by
    have := Module.finrank_eq_two_mul_card_of_basis_sum b
    rw [Fintype.card_fin] at this
    omega
  let c : Basis (Fin m) K X := Module.finBasisOfFinrankEq K X hm
  exact ⟨b.isometryEquivOfToMatrixEq c.polarizationBasis
    (hb.trans (toMatrix_polarizationForm c).symm)⟩

end LinearMap.BilinForm
