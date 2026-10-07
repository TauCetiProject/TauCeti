/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Congr
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# The isometry group of a bilinear form

An endomorphism `f` of a module `M` is an *isometry* of a bilinear form `B` when
`B (f x) (f y) = B x y`. Starting from the predicate `TauCeti.BilinForm.IsIsometry` defined in the
dependency-light module `TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic`, this file builds the
group it cuts out inside the linear automorphisms of `M`, `TauCeti.BilinForm.isometryGroup B`,
together with the API a consumer of the group needs: a Gram-matrix criterion, the resulting
constraint `(det f) ^ 2 = 1`, functoriality in the module and in the base ring, and stability of
orthogonal complements.

Mathlib bundles the same notion twice — as a map, `B₁ →bᵢ B₂`, and as an equivalence,
`LinearMap.BilinForm.IsometryEquiv B₁ B₂`. The bridge to the former
(`TauCeti.BilinForm.IsIsometry.toIsometry`, `TauCeti.BilinForm.isIsometry_toLinearMap`) lives
with the predicate; the bridge to the latter is
`TauCeti.BilinForm.isometryGroupEquivIsometryEquiv` here, an equivalence of *types* between the
subgroup and `B.IsometryEquiv B`. What is new is the unbundled predicate, which is what lets
"preserves `B`" be a side condition on an endomorphism one already has — the hypothesis of the
automatic-invertibility theorem below, and the membership condition of a subgroup — and the group
structure, needed as soon as one wants subgroups of it, group homomorphisms into it, or a group
action, none of which a bare type of bundled equivalences provides.

Two statements are worth singling out.

* Over an integral domain, isometries of a left-separating form on a finite free module are
  *automatically* invertible, so they already form elements of the group
  (`TauCeti.BilinForm.IsIsometry.toIsometryGroup`, `TauCeti.BilinForm.IsIsometry.bijective`):
  preserving `B` forces `(det f) ^ 2 = 1`, so `det f` is a unit. For a `ℤ`-lattice this says that a
  form-preserving endomorphism of the lattice already lies in the arithmetic group `Aut(V, Q)`,
  which is how such an automorphism usually presents itself — as an integer matrix satisfying
  `Aᵀ * G * A = G`.
* Base change along an algebra `R → A` is a group homomorphism
  `Aut(M, B) →* Aut(A ⊗[R] M, B_A)` (`TauCeti.BilinForm.isometryGroupBaseChange`). For `R = ℤ` and
  `A = ℂ` this is the action of `Aut(V, Q)` on the complexification of the lattice. When `Q` is
  preserved by monodromy, the monodromy of a variation of Hodge structure acts through this map.

## Main definitions

* `TauCeti.BilinForm.isometryGroup`: the isometry group `Aut(M, B) ≤ M ≃ₗ[R] M`.
* `TauCeti.BilinForm.isometryGroupEquivIsometryEquiv`: the isometry group as a type, equivalent to
  Mathlib's self-isometries `B.IsometryEquiv B`.
* `Module.Basis.isometryEquivOfToMatrixEq`: two bilinear forms with the same matrix in some bases
  are isometric.
* `LinearMap.BilinForm.specialIsometryGroup`: the determinant-one isometry group of `B`.
* `LinearMap.BilinForm.isometryDet`: the determinant of an isometry, as a homomorphism to `Rˣ`.
* `TauCeti.BilinForm.IsIsometry.toIsometryGroup`: an isometry of a left-separating form on a finite
  free module over an integral domain, as an element of the isometry group.
* `TauCeti.BilinForm.isometryGroupBaseChange`: base change of isometries, as a group homomorphism.
* `LinearMap.BilinForm.specialIsometryGroupBaseChange`: base change of determinant-one isometries.
* `TauCeti.BilinForm.isometryGroupCongr`: transport of the isometry group along a linear
  equivalence.
* `LinearMap.BilinForm.specialIsometryGroupCongr`: the corresponding transport of its
  determinant-one subgroup.

## Main results

* `TauCeti.BilinForm.isIsometry_iff_toMatrix`: the Gram-matrix criterion `Aᵀ * G * A = G`.
* `TauCeti.BilinForm.IsIsometry.det_sq_eq_one`: `(det f) ^ 2 = 1` for an isometry of a form whose
  Gram determinant is a non-zero-divisor.
* `TauCeti.BilinForm.IsIsometry.bijective`: over an integral domain, an isometry of a
  left-separating form on a finite free module is bijective.
* `TauCeti.BilinForm.IsIsometry.map_orthogonal`: a surjective isometry carries `B`-orthogonal
  complements to `B`-orthogonal complements.

## Implementation notes

The API is laid out by hypothesis strength: the imported predicate and elementary bridge to
Mathlib, the group, transport along a linear equivalence, the Gram-matrix criterion, and base
change need only a `CommSemiring` and additive monoids, which is where every Mathlib ingredient
they consume is stated; injectivity needs subtraction in `M`; the determinant results need `M` to
be an additive group over a `CommRing`; the automatic invertibility of an isometry of a
left-separating form needs an integral domain and a finite free module.

This is the bilinear-form counterpart of `TauCeti.QuadraticMap.orthogonalGroup` in
`TauCeti/LinearAlgebra/QuadraticForm/OrthogonalGroup/Basic.lean`, whose API it follows; for a
quadratic form `Q` over a ring in which `2` is a regular scalar the orthogonal group of `Q` is the
isometry group of `Q.polarBilin`,
`TauCeti.QuadraticMap.orthogonalGroup_eq_isometryGroup_polarBilin`.
-/

public section

namespace TauCeti

open Module
open LinearMap (BilinForm)
open scoped Matrix TensorProduct

namespace BilinForm

section CommSemiring

variable {R M M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M']
  [Module R M']

variable {B : BilinForm R M} {f g : M →ₗ[R] M}

namespace IsIsometry

/-- An isometry preserving a submodule restricts to an isometry of the restricted form. -/
theorem restrict {N : Submodule R M} (hf : IsIsometry B f) (hN : ∀ x ∈ N, f x ∈ N) :
    IsIsometry (B.restrict N) (f.restrict hN) := isIsometry_iff.mpr fun x y => by
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.coe_restrict_apply]
  exact hf.apply x y

/-- An isometry maps the `B`-orthogonal complement of `N` into the `B`-orthogonal complement of
the image of `N`. -/
theorem map_orthogonal_le (hf : IsIsometry B f) (N : Submodule R M) :
    (B.orthogonal N).map f ≤ B.orthogonal (N.map f) := by
  rintro - ⟨x, hx, rfl⟩
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rintro - ⟨n, hn, rfl⟩
  rw [hf.apply n x]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) n hn

/-- A surjective isometry carries `B`-orthogonal complements to `B`-orthogonal complements. -/
theorem map_orthogonal (hf : IsIsometry B f) (hsurj : Function.Surjective f) (N : Submodule R M) :
    (B.orthogonal N).map f = B.orthogonal (N.map f) := by
  refine le_antisymm (hf.map_orthogonal_le N) fun x hx => ?_
  obtain ⟨z, rfl⟩ := hsurj x
  refine Submodule.mem_map_of_mem ?_
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  rw [← hf.apply n z]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) _ ⟨n, hn, rfl⟩

end IsIsometry

/-- The isometry group `Aut(M, B)` of a bilinear form `B` on `M`: the linear automorphisms of `M`
that preserve `B`.

For a finite free `ℤ`-module `V` carrying an integral form `Q` this is the arithmetic group
`Aut(V, Q)`; when `Q` is preserved by monodromy, a variation of Hodge structure has its monodromy
representation land in this group and act on the complexification through
`TauCeti.BilinForm.isometryGroupBaseChange`. -/
def isometryGroup (B : BilinForm R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {e | IsIsometry B (e : M →ₗ[R] M)}
  one_mem' := isIsometry_iff.mpr fun _ _ => rfl
  mul_mem' := fun {a b} ha hb => isIsometry_iff.mpr fun x y =>
    (ha.apply (b x) (b y)).trans (hb.apply x y)
  inv_mem' := fun {a} ha => isIsometry_iff.mpr fun x y => by
    simpa using (ha.apply (a.symm x) (a.symm y)).symm

/-- Membership in the isometry group is the isometry predicate. -/
theorem mem_isometryGroup {e : M ≃ₗ[R] M} :
    e ∈ isometryGroup B ↔ IsIsometry B (e : M →ₗ[R] M) := Iff.rfl

@[simp]
theorem mem_isometryGroup_iff {e : M ≃ₗ[R] M} :
    e ∈ isometryGroup B ↔ ∀ x y, B (e x) (e y) = B x y :=
  mem_isometryGroup.trans isIsometry_iff

/-- Membership in `Aut(M, B)` is exactly Mathlib's notion of a self-isometry of `B`: the subgroup
`TauCeti.BilinForm.isometryGroup B` and the type `LinearMap.BilinForm.IsometryEquiv B B` carry the
same data, the subgroup adding the group structure. -/
def isometryGroupEquivIsometryEquiv (B : BilinForm R M) :
    isometryGroup B ≃ B.IsometryEquiv B where
  toFun e := ⟨e.1, fun x y => (mem_isometryGroup.mp e.2).apply x y⟩
  invFun e := ⟨e.toLinearEquiv,
    mem_isometryGroup.mpr (isIsometry_iff.mpr fun x y => e.map_app y x)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_isometryGroupEquivIsometryEquiv (B : BilinForm R M) (e : isometryGroup B) :
    ⇑(isometryGroupEquivIsometryEquiv B e) = ⇑(e : M ≃ₗ[R] M) := (rfl)

@[simp]
theorem coe_isometryGroupEquivIsometryEquiv_symm (B : BilinForm R M) (e : B.IsometryEquiv B) :
    (((isometryGroupEquivIsometryEquiv B).symm e : M ≃ₗ[R] M) : M → M) = ⇑e := (rfl)

section Congr

/-- Conjugation by `e` carries `Aut(M, B)` onto `Aut(M', B ∘ e⁻¹)`. -/
private theorem map_isometryGroup (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    (isometryGroup B).map (LinearEquiv.autCongr e : _ →* _)
      = isometryGroup (LinearMap.BilinForm.congr e B) := by
  ext g
  simp only [Subgroup.mem_map, MonoidHom.coe_ofClass, mem_isometryGroup_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ x y
    simp only [LinearEquiv.autCongr_apply_apply, LinearMap.BilinForm.congr_apply,
      LinearEquiv.symm_apply_apply]
    exact ha _ _
  · refine fun hg => ⟨(LinearEquiv.autCongr e).symm g, fun x y => ?_,
      (LinearEquiv.autCongr e).apply_symm_apply g⟩
    have := hg (e x) (e y)
    simpa only [LinearEquiv.autCongr_symm_apply_apply, LinearMap.BilinForm.congr_apply,
      LinearEquiv.symm_apply_apply] using this

/-- Transporting a bilinear form along a linear equivalence transports its isometry group:
conjugation by `e : M ≃ₗ[R] M'` carries `Aut(M, B)` onto `Aut(M', B ∘ e⁻¹)`. -/
def isometryGroupCongr (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    isometryGroup B ≃* isometryGroup (LinearMap.BilinForm.congr e B) :=
  ((LinearEquiv.autCongr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_isometryGroup B e))

@[simp]
theorem coe_isometryGroupCongr_apply (B : BilinForm R M) (e : M ≃ₗ[R] M') (a : isometryGroup B)
    (x : M') : (isometryGroupCongr B e a : M' ≃ₗ[R] M') x = e ((a : M ≃ₗ[R] M) (e.symm x)) := by
  simp [isometryGroupCongr]

@[simp]
theorem coe_isometryGroupCongr_symm_apply (B : BilinForm R M) (e : M ≃ₗ[R] M')
    (a : isometryGroup (LinearMap.BilinForm.congr e B)) (x : M) :
    ((isometryGroupCongr B e).symm a : M ≃ₗ[R] M) x
      = e.symm ((a : M' ≃ₗ[R] M') (e x)) := by
  simp [isometryGroupCongr]

end Congr

/-! ### The Gram-matrix criterion -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B' : BilinForm R M'}

/-- Two bilinear forms with the same matrix in bases `v` and `w` are isometric, through the
linear equivalence `v.equiv w (Equiv.refl ι)` carrying `v` to `w`. -/
noncomputable def _root_.Module.Basis.isometryEquivOfToMatrixEq (v : Basis ι R M)
    (w : Basis ι R M') (h : LinearMap.BilinForm.toMatrix v B = LinearMap.BilinForm.toMatrix w B') :
    B.IsometryEquiv B' where
  __ := v.equiv w (Equiv.refl ι)
  map_app' x y := by
    have key : B'.comp (v.equiv w (Equiv.refl ι) : M →ₗ[R] M') (v.equiv w (Equiv.refl ι)) = B :=
      LinearMap.BilinForm.ext_basis v fun i j => by
        simpa [LinearMap.BilinForm.toMatrix_apply] using (congrFun₂ h i j).symm
    simpa using LinearMap.congr_fun₂ key x y

@[simp]
theorem _root_.Module.Basis.toLinearEquiv_isometryEquivOfToMatrixEq (v : Basis ι R M)
    (w : Basis ι R M') (h : LinearMap.BilinForm.toMatrix v B = LinearMap.BilinForm.toMatrix w B') :
    (v.isometryEquivOfToMatrixEq w h : M ≃ₗ[R] M') = v.equiv w (Equiv.refl ι) := (rfl)

@[simp]
theorem _root_.Module.Basis.isometryEquivOfToMatrixEq_apply (v : Basis ι R M) (w : Basis ι R M')
    (h : LinearMap.BilinForm.toMatrix v B = LinearMap.BilinForm.toMatrix w B') (x : M) :
    v.isometryEquivOfToMatrixEq w h x = v.equiv w (Equiv.refl ι) x := (rfl)

/-- The isometry attached to an equality of matrices carries the basis `v` to the basis `w`. -/
theorem _root_.Module.Basis.isometryEquivOfToMatrixEq_apply_basis (v : Basis ι R M)
    (w : Basis ι R M') (h : LinearMap.BilinForm.toMatrix v B = LinearMap.BilinForm.toMatrix w B')
    (i : ι) : v.isometryEquivOfToMatrixEq w h (v i) = w i := by
  simp

/-- An endomorphism is an isometry of `B` exactly when its matrix `A` in a basis `b` satisfies
`Aᵀ * G * A = G` for the Gram matrix `G` of `B` in `b`. -/
theorem isIsometry_iff_toMatrix (b : Basis ι R M) :
    IsIsometry B f ↔
      (LinearMap.toMatrix b b f)ᵀ * LinearMap.BilinForm.toMatrix b B * LinearMap.toMatrix b b f
        = LinearMap.BilinForm.toMatrix b B := by
  rw [isIsometry_iff_comp, ← (LinearMap.BilinForm.toMatrix b).injective.eq_iff,
    LinearMap.BilinForm.toMatrix_comp b b B f f]

end Matrix

/-! ### Base change -/

section BaseChange

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- Base change along an `R`-algebra `A` carries an isometry of `B` to an isometry of the
base-changed form. -/
theorem IsIsometry.baseChange (hf : IsIsometry B f) :
    IsIsometry (LinearMap.BilinForm.baseChange A B) (f.baseChange A) := by
  rw [isIsometry_iff]
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a m =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul a' m' => simp [hf.apply m m']

/-- Base change along an `R`-algebra `A` is a group homomorphism
`Aut(M, B) →* Aut(A ⊗[R] M, B_A)`. For `R = ℤ` and `A = ℂ` this is the action of the arithmetic
group `Aut(V, Q)` on the complexification of the lattice, through which monodromy acts when it
preserves `Q`. -/
def isometryGroupBaseChange (B : BilinForm R M) :
    isometryGroup B →* isometryGroup (LinearMap.BilinForm.baseChange A B) where
  toFun e := ⟨LinearEquiv.baseChange R A M M (e : M ≃ₗ[R] M),
    mem_isometryGroup.mpr (IsIsometry.baseChange A (mem_isometryGroup.mp e.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [_root_.LinearEquiv.baseChange_mul])

@[simp]
theorem coe_isometryGroupBaseChange (B : BilinForm R M) (e : isometryGroup B) :
    (isometryGroupBaseChange A B e : A ⊗[R] M ≃ₗ[A] A ⊗[R] M)
      = LinearEquiv.baseChange R A M M (e : M ≃ₗ[R] M) := (rfl)

end BaseChange

end CommSemiring

section AddCommGroup

variable {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  {B : BilinForm R M} {f : M →ₗ[R] M}

/-- An isometry of a left-separating form is injective: it cannot collapse a vector that pairs
nontrivially with something. -/
theorem IsIsometry.injective (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    Function.Injective f := by
  intro x y hxy
  rw [← sub_eq_zero]
  refine hB (x - y) fun z => ?_
  rw [← hf.apply (x - y) z, map_sub, hxy, sub_self, LinearMap.map_zero₂]

end AddCommGroup

/-! ### Determinants -/

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}
  {f : M →ₗ[R] M}

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace IsIsometry

/-- For an isometry `f` of `B`, the Gram determinant `det G` of `B` in any basis satisfies
`(det f) ^ 2 * det G = det G`. -/
theorem det_sq_mul_det_toMatrix_self (b : Basis ι R M) (hf : IsIsometry B f) :
    LinearMap.det f ^ 2 * (LinearMap.BilinForm.toMatrix b B).det =
      (LinearMap.BilinForm.toMatrix b B).det := by
  have h := congrArg Matrix.det ((isIsometry_iff_toMatrix b).mp hf)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at h
  linear_combination h

/-- An isometry of a bilinear form whose Gram determinant is a non-zero-divisor has determinant
squaring to `1`; over `ℤ` this says its determinant is `±1`. -/
theorem det_sq_eq_one (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsIsometry B f) : LinearMap.det f ^ 2 = 1 :=
  (mul_cancel_right_mem_nonZeroDivisors hG).mp
    ((hf.det_sq_mul_det_toMatrix_self b).trans (one_mul _).symm)

/-- An isometry of a bilinear form whose Gram determinant is a non-zero-divisor has unit
determinant, its square being `1`. -/
theorem isUnit_det (b : Basis ι R M)
    (hG : (LinearMap.BilinForm.toMatrix b B).det ∈ nonZeroDivisors R)
    (hf : IsIsometry B f) : IsUnit (LinearMap.det f) :=
  IsUnit.of_mul_eq_one _ (by rw [← sq]; exact hf.det_sq_eq_one b hG)

end IsIsometry

end Matrix

section UnitDeterminant

variable [Module.Free R M] [Module.Finite R M]

namespace IsIsometry

/-- An isometry whose underlying endomorphism has unit determinant, as an element of the isometry
group. -/
noncomputable def toIsometryGroupOfIsUnitDet (hf : IsIsometry B f)
    (hdet : IsUnit (LinearMap.det f)) : isometryGroup B :=
  ⟨LinearMap.equivOfIsUnitDet hdet,
    mem_isometryGroup.mpr (isIsometry_iff.mpr fun x y => by simpa using hf.apply x y)⟩

@[simp]
theorem coe_toIsometryGroupOfIsUnitDet (hf : IsIsometry B f)
    (hdet : IsUnit (LinearMap.det f)) :
    ((hf.toIsometryGroupOfIsUnitDet hdet : isometryGroup B) : M →ₗ[R] M) = f :=
  LinearMap.coe_equivOfIsUnitDet hdet

@[simp]
theorem toIsometryGroupOfIsUnitDet_apply (hf : IsIsometry B f)
    (hdet : IsUnit (LinearMap.det f)) (x : M) :
    (hf.toIsometryGroupOfIsUnitDet hdet : M ≃ₗ[R] M) x = f x :=
  LinearMap.equivOfIsUnitDet_apply hdet x

end IsIsometry

end UnitDeterminant

section SeparatingLeft

variable [IsDomain R] [Module.Free R M] [Module.Finite R M]

namespace IsIsometry

/-- An isometry of a left-separating form on a finite free module over an integral domain has unit
determinant. -/
theorem isUnit_det_of_separatingLeft (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    IsUnit (LinearMap.det f) :=
  hf.isUnit_det (Module.Free.chooseBasis R M)
    (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))

/-- Over an integral domain, an endomorphism of a finite free module preserving a left-separating
bilinear form is automatically invertible, hence an element of the isometry group. This is how an
element of `Aut(V, Q)` usually presents itself: as an endomorphism of the lattice `V` preserving
`Q`, with invertibility a consequence rather than a hypothesis. -/
noncomputable def toIsometryGroup (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    isometryGroup B :=
  hf.toIsometryGroupOfIsUnitDet (hf.isUnit_det_of_separatingLeft hB)

@[simp]
theorem coe_toIsometryGroup (hB : B.SeparatingLeft) (hf : IsIsometry B f) :
    ((hf.toIsometryGroup hB : isometryGroup B) : M →ₗ[R] M) = f :=
  LinearMap.coe_equivOfIsUnitDet (hf.isUnit_det_of_separatingLeft hB)

@[simp]
theorem toIsometryGroup_apply (hB : B.SeparatingLeft) (hf : IsIsometry B f) (x : M) :
    (hf.toIsometryGroup hB : M ≃ₗ[R] M) x = f x :=
  LinearMap.equivOfIsUnitDet_apply (hf.isUnit_det_of_separatingLeft hB) x

/-- Over an integral domain, an endomorphism of a finite free module preserving a left-separating
bilinear form is automatically bijective. -/
theorem bijective (hB : B.SeparatingLeft) (hf : IsIsometry B f) : Function.Bijective f :=
  (Module.End.isUnit_iff f).mp
    ((LinearMap.isUnit_iff_isUnit_det f).mpr (hf.isUnit_det_of_separatingLeft hB))

end IsIsometry

end SeparatingLeft

end CommRing

end BilinForm

end TauCeti

/-! ### The determinant-one isometry group

These declarations live in Mathlib's `LinearMap.BilinForm` namespace so that dot notation such as
`B.specialIsometryGroup` works on a bilinear form `B`. -/

namespace LinearMap.BilinForm

open Module TauCeti.BilinForm
open LinearMap (BilinForm)
open scoped TensorProduct

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The determinant-one isometry group of a bilinear form.

The determinant is Mathlib's `LinearEquiv.det`, which is `1` by convention on a module that is not
finite free; on such a module this subgroup is therefore all of `isometryGroup B`. -/
noncomputable def specialIsometryGroup (B : BilinForm R M) : Subgroup (M ≃ₗ[R] M) :=
  isometryGroup B ⊓ (LinearEquiv.det (R := R) (M := M)).ker

@[simp]
theorem mem_specialIsometryGroup_iff {e : M ≃ₗ[R] M} :
    e ∈ specialIsometryGroup B ↔ e ∈ isometryGroup B ∧ LinearEquiv.det e = 1 :=
  Iff.rfl

/-- Every determinant-one isometry is an isometry. -/
theorem specialIsometryGroup_le_isometryGroup (B : BilinForm R M) :
    specialIsometryGroup B ≤ isometryGroup B :=
  inf_le_left

/-- The determinant-one isometry group is normal in the full isometry group. -/
instance specialIsometryGroup_normal (B : BilinForm R M) :
    ((specialIsometryGroup B).subgroupOf (isometryGroup B)).Normal := by
  rw [specialIsometryGroup, Subgroup.inf_subgroupOf_left]
  infer_instance

/-- The determinant of an isometry, as a homomorphism to the units of the base ring. -/
noncomputable def isometryDet (B : BilinForm R M) : isometryGroup B →* Rˣ :=
  LinearEquiv.det.comp (isometryGroup B).subtype

@[simp]
theorem isometryDet_apply (g : isometryGroup B) :
    isometryDet B g = LinearEquiv.det (g : M ≃ₗ[R] M) := by
  rw [isometryDet, MonoidHom.comp_apply, Subgroup.coe_subtype]

/-- The determinant-one subgroup regarded as a subgroup of the full isometry group. -/
noncomputable def specialIsometryWithin (B : BilinForm R M) : Subgroup (isometryGroup B) :=
  (isometryDet B).ker

@[simp]
theorem mem_specialIsometryWithin_iff {g : isometryGroup B} :
    g ∈ specialIsometryWithin B ↔ LinearEquiv.det (g : M ≃ₗ[R] M) = 1 :=
  Iff.rfl

/-- The two ambient-group presentations of the determinant-one isometry group agree. -/
theorem specialIsometryWithin_eq_subgroupOf :
    specialIsometryWithin B = (specialIsometryGroup B).subgroupOf (isometryGroup B) := by
  ext g
  simp [Subgroup.mem_subgroupOf, g.2]

/-- The inclusion from determinant-one isometries to all isometries. -/
noncomputable def specialIsometryToIsometry (B : BilinForm R M) :
    specialIsometryGroup B →* isometryGroup B :=
  Subgroup.inclusion (specialIsometryGroup_le_isometryGroup B)

@[simp]
theorem coe_specialIsometryToIsometry (g : specialIsometryGroup B) :
    ((specialIsometryToIsometry B g : isometryGroup B) : M ≃ₗ[R] M) = g := by
  simp [specialIsometryToIsometry]

/-- The determinant of a determinant-one isometry is one. -/
@[simp]
theorem det_coe_specialIsometryGroup (g : specialIsometryGroup B) :
    LinearEquiv.det (g : M ≃ₗ[R] M) = 1 :=
  (mem_specialIsometryGroup_iff.mp g.2).2

/-- Inclusion of determinant-one isometries into all isometries is injective. -/
theorem specialIsometryToIsometry_injective :
    Function.Injective (specialIsometryToIsometry B) :=
  Subgroup.inclusion_injective _

/-- The image of the determinant-one isometry group in the full isometry group is the determinant
kernel. -/
@[simp]
theorem range_specialIsometryToIsometry :
    (specialIsometryToIsometry B).range = specialIsometryWithin B := by
  rw [specialIsometryWithin_eq_subgroupOf, specialIsometryToIsometry,
    Subgroup.inclusion_range]

/-- The determinant kernel inside the isometry group is canonically isomorphic to the
determinant-one subgroup of the ambient linear automorphism group. -/
noncomputable def specialIsometryWithinEquiv (B : BilinForm R M) :
    specialIsometryWithin B ≃* specialIsometryGroup B :=
  (MulEquiv.subgroupCongr specialIsometryWithin_eq_subgroupOf).trans
    (Subgroup.subgroupOfEquivOfLe (specialIsometryGroup_le_isometryGroup B))

@[simp]
theorem coe_specialIsometryWithinEquiv_apply (g : specialIsometryWithin B) :
    ((specialIsometryWithinEquiv B g : specialIsometryGroup B) : M ≃ₗ[R] M) =
      ((g : isometryGroup B) : M ≃ₗ[R] M) := by
  simp [specialIsometryWithinEquiv, Subgroup.subgroupOfEquivOfLe]

@[simp]
theorem coe_specialIsometryWithinEquiv_symm_apply (g : specialIsometryGroup B) :
    (((specialIsometryWithinEquiv B).symm g : specialIsometryWithin B) : isometryGroup B) =
      specialIsometryToIsometry B g := by
  ext1
  simp [specialIsometryWithinEquiv, Subgroup.subgroupOfEquivOfLe]

/-- On a subsingleton module every isometry has determinant one. -/
theorem specialIsometryWithin_eq_top [Subsingleton M] : specialIsometryWithin B = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  rw [mem_specialIsometryWithin_iff, Subsingleton.elim (g : M ≃ₗ[R] M) 1, map_one]

section Congr

variable {M' : Type*} [AddCommGroup M'] [Module R M']

private theorem map_specialIsometryGroup (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    (specialIsometryGroup B).map (LinearEquiv.autCongr e : _ →* _) =
      specialIsometryGroup (LinearMap.BilinForm.congr e B) := by
  refine (Subgroup.map_inf_eq _ _ _ (LinearEquiv.autCongr e).injective).trans
    (congrArg₂ (· ⊓ ·) (map_isometryGroup B e) ?_)
  rw [Subgroup.map_equiv_eq_comap_symm, MonoidHom.comap_ker]
  congr 1
  ext g
  simpa [LinearEquiv.autCongr_symm_apply] using LinearMap.det_conj (g : M' →ₗ[R] M') e.symm

/-- Transporting a bilinear form along a linear equivalence transports its determinant-one
isometry group. -/
noncomputable def specialIsometryGroupCongr (B : BilinForm R M) (e : M ≃ₗ[R] M') :
    specialIsometryGroup B ≃* specialIsometryGroup (LinearMap.BilinForm.congr e B) :=
  ((LinearEquiv.autCongr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_specialIsometryGroup B e))

@[simp]
theorem coe_specialIsometryGroupCongr_apply (B : BilinForm R M) (e : M ≃ₗ[R] M')
    (g : specialIsometryGroup B) :
    (specialIsometryGroupCongr B e g : M' ≃ₗ[R] M') =
      (e.symm.trans (g : M ≃ₗ[R] M)).trans e := by
  rw [specialIsometryGroupCongr, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, LinearEquiv.autCongr_apply]

@[simp]
theorem coe_specialIsometryGroupCongr_symm_apply (B : BilinForm R M) (e : M ≃ₗ[R] M')
    (g : specialIsometryGroup (LinearMap.BilinForm.congr e B)) :
    ((specialIsometryGroupCongr B e).symm g : M ≃ₗ[R] M) =
      (e.trans (g : M' ≃ₗ[R] M')).trans e.symm := by
  rw [← (LinearEquiv.autCongr e).injective.eq_iff, LinearEquiv.autCongr_apply,
    ← coe_specialIsometryGroupCongr_apply, MulEquiv.apply_symm_apply]
  ext x
  simp

end Congr

section BaseChange

variable (A : Type*) [CommRing A] [Algebra R A] [Module.Free R M] [Module.Finite R M]

/-- Base change preserves determinant-one isometries. -/
noncomputable def specialIsometryGroupBaseChange (B : BilinForm R M) :
    specialIsometryGroup B →* specialIsometryGroup (LinearMap.BilinForm.baseChange A B) where
  toFun g := ⟨isometryGroupBaseChange A B
      ⟨g, specialIsometryGroup_le_isometryGroup B g.2⟩, by
    refine mem_specialIsometryGroup_iff.mpr ⟨(isometryGroupBaseChange A B _).2, ?_⟩
    rw [coe_isometryGroupBaseChange, LinearEquiv.det_baseChange,
      (mem_specialIsometryGroup_iff.mp g.2).2, map_one]⟩
  map_one' := Subtype.ext (by simp [isometryGroupBaseChange])
  map_mul' g h := Subtype.ext (by simp [isometryGroupBaseChange, LinearEquiv.baseChange_mul])

@[simp]
theorem coe_specialIsometryGroupBaseChange (B : BilinForm R M)
    (g : specialIsometryGroup B) :
    (specialIsometryGroupBaseChange A B g : A ⊗[R] M ≃ₗ[A] A ⊗[R] M) =
      LinearEquiv.baseChange R A M M (g : M ≃ₗ[R] M) := by
  simp [specialIsometryGroupBaseChange, isometryGroupBaseChange]

end BaseChange

end CommRing

end LinearMap.BilinForm
