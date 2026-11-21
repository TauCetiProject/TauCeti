/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearMap.Ker
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Kernels and cokernels under restriction of scalars

For a tower of scalars `R → S` and an `S`-linear map `f`, the kernel and cokernel of `f`, with
their `R`-module structures, are those of the underlying `R`-linear map
(`LinearMap.kerRestrictScalarsEquiv`, `LinearMap.cokerRestrictScalarsEquiv`). A commuting square
`f' ∘ e₁ = e₂ ∘ f` of `R`-linear isomorphisms between `S`-modules therefore induces `R`-linear
isomorphisms of the `S`-kernels and `S`-cokernels (`LinearMap.kerCongrOfComp`,
`LinearMap.cokerCongrOfComp`). If `e₁` and `e₂` send `a • x` to `s • e x`, so do the induced
isomorphisms (`LinearMap.kerCongrOfComp_smul`, `LinearMap.cokerCongrOfComp_smul`). For the tower
`ℝ → ℂ` with `a = I` and `s = ±I`, this says the induced isomorphisms are complex linear or
conjugate-linear.

For `S`-linear maps `f : M → N` and `g : N → P`, the identifications of kernels and cokernels
commute with the maps of the kernel–cokernel sequence
`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0` and of the
corresponding sequence of the underlying `R`-linear maps
(`LinearMap.inclusion_comp_kerRestrictScalarsEquiv`,
`LinearMap.kerCompToKer_comp_kerRestrictScalarsEquiv`,
`LinearMap.kerToCoker_comp_kerRestrictScalarsEquiv`,
`LinearMap.cokerToCokerComp_comp_cokerRestrictScalarsEquiv_symm`,
`LinearMap.factor_comp_cokerRestrictScalarsEquiv_symm`), so the two sequences are isomorphic.

When `S` is a finite `R`-module, the kernel and cokernel of the underlying `R`-linear map are
finite over `R` as soon as those of `f` are finite over `S`
(`LinearMap.finite_ker_restrictScalars`, `LinearMap.finite_quotient_range_restrictScalars`).
-/

public section

noncomputable section

namespace LinearMap

section Ker

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N)

/-- The kernel of an `S`-linear map, with its `R`-module structure, is the kernel of the
underlying `R`-linear map. -/
def kerRestrictScalarsEquiv : ker f ≃ₗ[R] ker (f.restrictScalars R) :=
  ((ker f).restrictScalarsEquiv R).symm.restrictScalars R

theorem coe_kerRestrictScalarsEquiv_apply (x : ker f) :
    (f.kerRestrictScalarsEquiv R x : M) = x :=
  (rfl)

theorem coe_kerRestrictScalarsEquiv_symm_apply (x : ker (f.restrictScalars R)) :
    ((f.kerRestrictScalarsEquiv R).symm x : M) = x :=
  (rfl)

variable {R} {M' N' : Type*} [AddCommMonoid M'] [Module R M'] [Module S M']
  [IsScalarTower R S M'] [AddCommMonoid N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  {f' : M' →ₗ[S] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
  (h : f'.restrictScalars R ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars R)

/-- The `R`-linear isomorphism of `S`-kernels induced by a commuting square `f' ∘ e₁ = e₂ ∘ f`
of `R`-linear isomorphisms: the restriction of `e₁`. -/
def kerCongrOfComp : ker f ≃ₗ[R] ker f' :=
  (f.kerRestrictScalarsEquiv R).trans ((e₁.ofSubmodules _ _
    ((f.restrictScalars R).map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)).trans
      (f'.kerRestrictScalarsEquiv R).symm)

@[simp]
theorem coe_kerCongrOfComp_apply (x : ker f) : (kerCongrOfComp f e₁ e₂ h x : M') = e₁ x :=
  (rfl)

@[simp]
theorem coe_kerCongrOfComp_symm_apply (x : ker f') :
    ((kerCongrOfComp f e₁ e₂ h).symm x : M) = e₁.symm x := by
  obtain ⟨x, rfl⟩ := (kerCongrOfComp f e₁ e₂ h).surjective x
  simp

/-- If `e₁` sends `a • x` to `s • e₁ x`, so does the induced isomorphism of kernels. -/
theorem kerCongrOfComp_smul {a s : S} (he₁ : ∀ x, e₁ (a • x) = s • e₁ x) (x : ker f) :
    kerCongrOfComp f e₁ e₂ h (a • x) = s • kerCongrOfComp f e₁ e₂ h x :=
  Subtype.ext (by simp [he₁])

end Ker

section Coker

variable (R : Type*) {S M N : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N)

/-- The cokernel of an `S`-linear map, with its `R`-module structure, is the cokernel of the
underlying `R`-linear map. -/
def cokerRestrictScalarsEquiv : (N ⧸ range (f.restrictScalars R)) ≃ₗ[R] N ⧸ range f :=
  (Submodule.quotEquivOfEq _ _ (range_restrictScalars f)).trans
    (Submodule.Quotient.restrictScalarsEquiv R (range f))

@[simp]
theorem cokerRestrictScalarsEquiv_mk (y : N) :
    f.cokerRestrictScalarsEquiv R (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

@[simp]
theorem cokerRestrictScalarsEquiv_symm_mk (y : N) :
    (f.cokerRestrictScalarsEquiv R).symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

variable {R} {M' N' : Type*} [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M'] [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  {f' : M' →ₗ[S] N'} (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
  (h : f'.restrictScalars R ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars R)

/-- The `R`-linear isomorphism of `S`-cokernels induced by a commuting square
`f' ∘ e₁ = e₂ ∘ f` of `R`-linear isomorphisms: the map of quotients induced by `e₂`. -/
def cokerCongrOfComp : (N ⧸ range f) ≃ₗ[R] N' ⧸ range f' :=
  (f.cokerRestrictScalarsEquiv R).symm.trans ((Submodule.Quotient.equiv _ _ e₂
    ((f.restrictScalars R).map_range_eq_range_of_comp_eq e₁.surjective h)).trans
      (f'.cokerRestrictScalarsEquiv R))

@[simp]
theorem cokerCongrOfComp_mk (y : N) :
    cokerCongrOfComp f e₁ e₂ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e₂ y) :=
  (rfl)

@[simp]
theorem cokerCongrOfComp_symm_mk (y : N') :
    (cokerCongrOfComp f e₁ e₂ h).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e₂.symm y) := by
  rw [LinearEquiv.symm_apply_eq, cokerCongrOfComp_mk, LinearEquiv.apply_symm_apply]

/-- If `e₂` sends `a • y` to `s • e₂ y`, so does the induced isomorphism of cokernels. -/
theorem cokerCongrOfComp_smul {a s : S} (he₂ : ∀ y, e₂ (a • y) = s • e₂ y)
    (y : N ⧸ range f) :
    cokerCongrOfComp f e₁ e₂ h (a • y) = s • cokerCongrOfComp f e₁ e₂ h y := by
  induction y using Submodule.Quotient.induction_on with
  | H y => rw [← Submodule.Quotient.mk_smul, cokerCongrOfComp_mk, cokerCongrOfComp_mk, he₂,
      Submodule.Quotient.mk_smul]

end Coker

section KerCokerComp

/-! ### The kernel–cokernel sequences of a composite and of its restriction of scalars

The maps of the sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) →
coker g → 0` of the restricted maps commute with the identifications of the `R`-kernels and
cokernels with the `S`-kernels and cokernels. -/

-- The maps act on representatives, but the kernel and cokernel of the restriction of `g ∘ f`
-- agree with those of the composite of the restrictions only up to definitional unfolding, which
-- defeats rewriting, so each square is checked by an explicit chain of equations.

variable (R : Type*) {S M N P : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  (f : M →ₗ[S] N) (g : N →ₗ[S] P)

/-- The inclusion of kernels commutes with the identifications of `R`-kernels and
`S`-kernels. -/
theorem inclusion_comp_kerRestrictScalarsEquiv :
    Submodule.inclusion (ker_le_ker_comp (f.restrictScalars R) (g.restrictScalars R)) ∘ₗ
    (f.kerRestrictScalarsEquiv R).toLinearMap =
      ((g ∘ₗ f).kerRestrictScalarsEquiv R).toLinearMap ∘ₗ
      (Submodule.inclusion (ker_le_ker_comp f g)).restrictScalars R :=
  LinearMap.ext fun x ↦ Subtype.ext ((coe_kerRestrictScalarsEquiv_apply R f x).trans
    (coe_kerRestrictScalarsEquiv_apply R (g ∘ₗ f)
      (Submodule.inclusion (ker_le_ker_comp f g) x)).symm)

/-- The map `ker (g ∘ f) → ker g` commutes with the identifications of `R`-kernels and
`S`-kernels. -/
theorem kerCompToKer_comp_kerRestrictScalarsEquiv :
    (f.restrictScalars R).kerCompToKer (g.restrictScalars R) ∘ₗ
    ((g ∘ₗ f).kerRestrictScalarsEquiv R).toLinearMap =
      (g.kerRestrictScalarsEquiv R).toLinearMap ∘ₗ (f.kerCompToKer g).restrictScalars R :=
  LinearMap.ext fun x ↦ Subtype.ext ((coe_kerCompToKer_apply _ _ _).trans
    ((congrArg f (coe_kerRestrictScalarsEquiv_apply R (g ∘ₗ f) x)).trans
      ((coe_kerCompToKer_apply f g x).symm.trans
        (coe_kerRestrictScalarsEquiv_apply R g (f.kerCompToKer g x)).symm)))

/-- The map `ker g → coker f` commutes with the identifications of `R`-kernels and cokernels
with `S`-kernels and cokernels. -/
theorem kerToCoker_comp_kerRestrictScalarsEquiv :
    (f.restrictScalars R).kerToCoker (g.restrictScalars R) ∘ₗ
    (g.kerRestrictScalarsEquiv R).toLinearMap =
      (f.cokerRestrictScalarsEquiv R).symm.toLinearMap ∘ₗ (f.kerToCoker g).restrictScalars R :=
  LinearMap.ext fun x ↦ (kerToCoker_apply _ _ _).trans
    ((congrArg Submodule.Quotient.mk (coe_kerRestrictScalarsEquiv_apply R g x)).trans
      ((cokerRestrictScalarsEquiv_symm_mk R f _).symm.trans
        (congrArg _ (kerToCoker_apply f g x)).symm))

/-- The map `coker f → coker (g ∘ f)` commutes with the identifications of `R`-cokernels and
`S`-cokernels. -/
theorem cokerToCokerComp_comp_cokerRestrictScalarsEquiv_symm :
    (f.restrictScalars R).cokerToCokerComp (g.restrictScalars R) ∘ₗ
    (f.cokerRestrictScalarsEquiv R).symm.toLinearMap =
      ((g ∘ₗ f).cokerRestrictScalarsEquiv R).symm.toLinearMap ∘ₗ
      (f.cokerToCokerComp g).restrictScalars R :=
  LinearMap.ext fun q ↦ Submodule.Quotient.induction_on _ q fun y ↦
    (congrArg _ (cokerRestrictScalarsEquiv_symm_mk R f y)).trans
      ((cokerToCokerComp_mk (f.restrictScalars R) (g.restrictScalars R) y).trans
        ((cokerRestrictScalarsEquiv_symm_mk R (g ∘ₗ f) (g y)).symm.trans
          (congrArg _ (cokerToCokerComp_mk f g y)).symm))

/-- The quotient map `coker (g ∘ f) → coker g` commutes with the identifications of
`R`-cokernels and `S`-cokernels. -/
theorem factor_comp_cokerRestrictScalarsEquiv_symm :
    Submodule.factor (range_comp_le_range (f.restrictScalars R) (g.restrictScalars R)) ∘ₗ
    ((g ∘ₗ f).cokerRestrictScalarsEquiv R).symm.toLinearMap =
      (g.cokerRestrictScalarsEquiv R).symm.toLinearMap ∘ₗ
      (Submodule.factor (range_comp_le_range f g)).restrictScalars R :=
  LinearMap.ext fun q ↦ Submodule.Quotient.induction_on _ q fun y ↦
    (congrArg _ (cokerRestrictScalarsEquiv_symm_mk R (g ∘ₗ f) y)).trans
      ((Submodule.factor_mk
        (range_comp_le_range (f.restrictScalars R) (g.restrictScalars R)) y).trans
        ((cokerRestrictScalarsEquiv_symm_mk R g y).symm.trans
          (congrArg _ (Submodule.factor_mk (range_comp_le_range f g) y)).symm))

end KerCokerComp

section Finite

variable {R S M N : Type*}

/-- If `S` is a finite `R`-module, the kernel of an `S`-linear map with finite `S`-kernel is
finite over `R`, as the kernel of the underlying `R`-linear map. -/
instance finite_ker_restrictScalars [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]
    [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M] [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[S] N) [Module.Finite S (ker f)] : Module.Finite R (ker (f.restrictScalars R)) :=
  have : Module.Finite R (ker f) := Module.Finite.trans S (ker f)
  Module.Finite.equiv (f.kerRestrictScalarsEquiv R)

/-- If `S` is a finite `R`-module, the cokernel of an `S`-linear map with finite `S`-cokernel is
finite over `R`, as the cokernel of the underlying `R`-linear map. -/
instance finite_quotient_range_restrictScalars [Ring R] [Ring S] [Module R S]
    [Module.Finite R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[S] N)
    [Module.Finite S (N ⧸ range f)] : Module.Finite R (N ⧸ range (f.restrictScalars R)) :=
  have : Module.Finite R (N ⧸ range f) := Module.Finite.trans S (N ⧸ range f)
  Module.Finite.equiv (f.cokerRestrictScalarsEquiv R).symm

end Finite

end LinearMap
