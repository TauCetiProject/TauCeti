/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Basis.Semilinear

/-!
# The contragredient dual along a ring isomorphism

Let `σ : S ≃+* R` be a ring isomorphism of commutative semirings and `M` an `R`-module. The
*contragredient dual* `ContragredientDual σ M` is the dual space `Hom_R(M, R)` equipped with the
`S`-module structure obtained by restricting scalars along `σ`:

  `(s • φ) x = φ (σ s • x) = σ s * φ x`.

For the group algebra `R = S = O[G]` of a commutative group `G` over a commutative ring `O`,
with `σ = #` the antipode `g ↦ g⁻¹`, this is the contragredient action `(g • φ) x = φ (g⁻¹ • x)`.
More generally, when `R = R_Ψ` is a character group ring of `G` over `O` and `S = R^# = R_{Ψ⁻¹}`
is its conjugate under `# : R^# ≃+* R`, it gives the `R^#`-module structure on `Hom_R(M, R)` used
by Dasgupta and Kakde to form transposed presentations.

Precomposition turns an `R`-linear map `f : M →ₗ[R] N` contravariantly into an `S`-linear map
`ContragredientDual.map σ f : ContragredientDual σ N →ₗ[S] ContragredientDual σ M`. Because `σ` is
a ring isomorphism, `toDualLinearEquiv` is a `σ`-semilinear equivalence onto `Module.Dual R M`: a
finite `R`-basis of `M` yields an `S`-basis of `ContragredientDual σ M`
(`Basis.contragredientDual`), freeness is preserved for finite free modules, and finite generation
and projectivity are preserved for finite projective modules.

## Main definitions

* `TauCeti.ContragredientDual σ M`: `Module.Dual R M` with scalars restricted along `σ : S ≃+* R`.
* `TauCeti.ContragredientDual.toDual`, `TauCeti.ContragredientDual.ofDual`: the underlying
  `R`-linear functional and the constructor from one, packaged semilinearly as
  `TauCeti.ContragredientDual.toDualLinearEquiv`.
* `TauCeti.ContragredientDual.map σ f`: the contragredient transpose
  `ContragredientDual σ N →ₗ[S] ContragredientDual σ M` of `f : M →ₗ[R] N`.
* `Module.Basis.contragredientDual b σ`: the dual `S`-basis of `ContragredientDual σ M` attached
  to a finite `R`-basis `b` of `M`.

## Main results

* `TauCeti.ContragredientDual.smul_apply`, `TauCeti.ContragredientDual.toDual_smul`: the
  contragredient action law `(s • φ) x = φ (σ s • x)` and semilinearity of `toDual`.
* `TauCeti.ContragredientDual.toMatrix_map`: in dual bases, the matrix of
  `ContragredientDual.map σ f` is the entrywise `σ⁻¹`-image of the transpose of the matrix of `f`.
* `TauCeti.ContragredientDual.free`, `TauCeti.ContragredientDual.finite`,
  `TauCeti.ContragredientDual.projective`: preservation of freeness for finite free modules, and of
  finite generation and projectivity for finite projective modules.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  §6.1, equation (80).
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- **The contragredient dual** of an `R`-module `M` along a ring isomorphism `σ : S ≃+* R`:
`Hom_R(M, R)` equipped with the `S`-module action `(s • φ) x = φ (σ s • x)`. -/
structure ContragredientDual {S R : Type*} [CommSemiring S] [CommSemiring R] (σ : S ≃+* R)
    (M : Type*) [AddCommMonoid M] [Module R M] where
  /-- Construct an element of the contragredient dual from an `R`-linear functional. -/
  ofDual ::
  /-- The underlying `R`-linear functional in `Module.Dual R M`. -/
  toDual : Module.Dual R M

namespace ContragredientDual

section CommSemiring

variable {S R M N P : Type*} [CommSemiring S] [CommSemiring R] {σ : S ≃+* R}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

theorem toDual_injective : Function.Injective (toDual (σ := σ) (M := M))
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance : FunLike (ContragredientDual σ M) M R where
  coe φ := φ.toDual
  coe_injective _ _ h := toDual_injective (DFunLike.coe_injective h)

instance : AddMonoidHomClass (ContragredientDual σ M) M R where
  map_add φ := map_add φ.toDual
  map_zero φ := map_zero φ.toDual

@[simp]
theorem coe_toDual (φ : ContragredientDual σ M) : (φ.toDual : M → R) = φ :=
  (rfl)

@[simp]
theorem toDual_apply (φ : ContragredientDual σ M) (x : M) : φ.toDual x = φ x :=
  (rfl)

@[simp]
theorem ofDual_apply (φ : Module.Dual R M) (x : M) : ofDual (σ := σ) φ x = φ x :=
  (rfl)

@[simp]
theorem toDual_ofDual (φ : Module.Dual R M) : (ofDual (σ := σ) φ).toDual = φ :=
  (rfl)

@[simp]
theorem ofDual_toDual (φ : ContragredientDual σ M) : ofDual (σ := σ) φ.toDual = φ :=
  (rfl)

/-- Two elements of the contragredient dual are equal iff they agree on every element of `M`. -/
@[ext]
theorem ext {φ ψ : ContragredientDual σ M} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext φ ψ h

theorem map_smul_eq_mul (φ : ContragredientDual σ M) (r : R) (x : M) :
    φ (r • x) = r * φ x :=
  (φ.toDual.map_smul r x).trans (smul_eq_mul r (φ x))

instance : Zero (ContragredientDual σ M) := ⟨ofDual 0⟩

instance : Add (ContragredientDual σ M) := ⟨fun φ ψ ↦ ofDual (φ.toDual + ψ.toDual)⟩

instance : SMul ℕ (ContragredientDual σ M) := ⟨fun n φ ↦ ofDual (n • φ.toDual)⟩

instance : AddCommMonoid (ContragredientDual σ M) :=
  toDual_injective.addCommMonoid toDual rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance : SMul S (ContragredientDual σ M) := ⟨fun s φ ↦ ofDual (σ s • φ.toDual)⟩

@[simp]
theorem zero_apply (x : M) : (0 : ContragredientDual σ M) x = 0 :=
  (rfl)

@[simp]
theorem add_apply (φ ψ : ContragredientDual σ M) (x : M) : (φ + ψ) x = φ x + ψ x :=
  (rfl)

@[simp]
theorem toDual_zero : (0 : ContragredientDual σ M).toDual = 0 :=
  (rfl)

@[simp]
theorem ofDual_zero : ofDual (σ := σ) (0 : Module.Dual R M) = 0 :=
  (rfl)

@[simp]
theorem toDual_add (φ ψ : ContragredientDual σ M) : (φ + ψ).toDual = φ.toDual + ψ.toDual :=
  (rfl)

@[simp]
theorem ofDual_add (φ ψ : Module.Dual R M) :
    ofDual (σ := σ) (φ + ψ) = ofDual φ + ofDual ψ :=
  (rfl)

/-- `toDual` intertwines the contragredient `S`-action with the `R`-action on `Module.Dual R M`
along `σ`. -/
@[simp]
theorem toDual_smul (s : S) (φ : ContragredientDual σ M) :
    (s • φ).toDual = σ s • φ.toDual :=
  (rfl)

theorem ofDual_smul (s : S) (φ : Module.Dual R M) :
    ofDual (σ := σ) (σ s • φ) = s • ofDual φ :=
  (rfl)

@[simp]
theorem ofDual_smul' (r : R) (φ : Module.Dual R M) :
    ofDual (σ := σ) (r • φ) = σ.symm r • ofDual φ := by
  rw [← ofDual_smul, σ.apply_symm_apply]

instance : Module S (ContragredientDual σ M) :=
  letI : Module S (Module.Dual R M) := Module.compHom (Module.Dual R M) (σ : S →+* R)
  toDual_injective.module S ⟨⟨toDual, toDual_zero⟩, toDual_add⟩ fun _ _ ↦ rfl

theorem smul_apply_eq_mul (s : S) (φ : ContragredientDual σ M) (x : M) :
    (s • φ) x = σ s * φ x := by
  rw [← toDual_apply, toDual_smul, LinearMap.smul_apply, smul_eq_mul, toDual_apply]

/-- **The contragredient scalar action**: `(s • φ) x = φ (σ s • x)`. -/
@[simp]
theorem smul_apply (s : S) (φ : ContragredientDual σ M) (x : M) :
    (s • φ) x = φ (σ s • x) := by
  rw [smul_apply_eq_mul, map_smul_eq_mul]

/-- `toDual` and `ofDual` form a `σ`-semilinear equivalence between `ContragredientDual σ M` and
`Module.Dual R M`. -/
def toDualLinearEquiv (σ : S ≃+* R) (M : Type*) [AddCommMonoid M] [Module R M] :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    ContragredientDual σ M ≃ₛₗ[(σ : S →+* R)] Module.Dual R M :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  { toFun := toDual
    invFun := ofDual
    map_add' := toDual_add
    map_smul' := toDual_smul
    left_inv := ofDual_toDual
    right_inv := toDual_ofDual }

@[simp]
theorem toDualLinearEquiv_apply (φ : ContragredientDual σ M) :
    toDualLinearEquiv σ M φ = φ.toDual :=
  (rfl)

@[simp]
theorem toDualLinearEquiv_symm_apply (φ : Module.Dual R M) :
    (toDualLinearEquiv σ M).symm φ = ofDual φ :=
  (rfl)

/-- `ofDual` and `toDual` form a `((RingEquiv.toOpposite R).symm.trans σ.symm)`-semilinear
equivalence from `Module.Dual R M` (with its `Rᵐᵒᵖ`-module structure) to
`ContragredientDual σ M`. -/
def ofDualOppositeLinearEquiv (σ : S ≃+* R) (M : Type*) [AddCommMonoid M] [Module R M] :
    let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
    haveI := RingHomInvPair.of_ringEquiv ρ
    haveI := RingHomInvPair.of_ringEquiv_symm ρ
    Module.Dual R M ≃ₛₗ[(ρ : Rᵐᵒᵖ →+* S)] ContragredientDual σ M :=
  let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
  haveI := RingHomInvPair.of_ringEquiv ρ
  haveI := RingHomInvPair.of_ringEquiv_symm ρ
  { toFun := ofDual
    invFun := toDual
    map_add' := ofDual_add
    map_smul' := fun r φ ↦ by
      ext x
      simp [LinearMap.smul_apply, mul_comm]
    left_inv := toDual_ofDual
    right_inv := ofDual_toDual }

/-- `ofDualOppositeLinearEquiv` sends a functional `φ` to `ofDual φ`. -/
@[simp]
theorem ofDualOppositeLinearEquiv_apply (φ : Module.Dual R M) :
    ofDualOppositeLinearEquiv σ M φ = ofDual φ :=
  (rfl)

/-- The inverse of `ofDualOppositeLinearEquiv` sends `φ` to `φ.toDual`. -/
@[simp]
theorem ofDualOppositeLinearEquiv_symm_apply (φ : ContragredientDual σ M) :
    (ofDualOppositeLinearEquiv σ M).symm φ = φ.toDual :=
  (rfl)

/-- Precomposition with `f : M →ₗ[R] N` as an `S`-linear map between contragredient duals. -/
def map (σ : S ≃+* R) (f : M →ₗ[R] N) : ContragredientDual σ N →ₗ[S] ContragredientDual σ M :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  ((toDualLinearEquiv σ N).arrowCongr (toDualLinearEquiv σ M)).symm f.dualMap

@[simp]
theorem map_apply (f : M →ₗ[R] N) (φ : ContragredientDual σ N) (x : M) :
    map σ f φ x = φ (f x) :=
  (rfl)

@[simp]
theorem toDual_map (f : M →ₗ[R] N) (φ : ContragredientDual σ N) :
    (map σ f φ).toDual = φ.toDual.comp f :=
  (rfl)

@[simp]
theorem map_ofDual (f : M →ₗ[R] N) (φ : Module.Dual R N) :
    map σ f (ofDual φ) = ofDual (φ.comp f) :=
  (rfl)

@[simp]
theorem map_id : map σ (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext φ x
  rfl

theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map σ (g.comp f) = (map σ f).comp (map σ g) := by
  ext φ x
  rfl

@[simp]
protected theorem map_zero : map σ (0 : M →ₗ[R] N) = 0 := by
  ext φ x
  simp

protected theorem map_add (f g : M →ₗ[R] N) : map σ (f + g) = map σ f + map σ g := by
  ext φ x
  simp

/-- `toDualLinearEquiv` intertwines `ContragredientDual.map` with `LinearMap.dualMap`. -/
theorem toDualLinearEquiv_comp_map (f : M →ₗ[R] N) :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    (toDualLinearEquiv σ M).toLinearMap.comp (map σ f) =
      f.dualMap.comp (toDualLinearEquiv σ N).toLinearMap := by
  ext φ x
  rfl

/-- `ofDualOppositeLinearEquiv` intertwines `LinearMap.lcomp Rᵐᵒᵖ R` with
`ContragredientDual.map`. -/
theorem ofDualOppositeLinearEquiv_comp_lcomp (f : M →ₗ[R] N) :
    let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
    haveI := RingHomInvPair.of_ringEquiv ρ
    haveI := RingHomInvPair.of_ringEquiv_symm ρ
    (ofDualOppositeLinearEquiv σ M).toLinearMap.comp (f.lcomp Rᵐᵒᵖ R) =
      (map σ f).comp (ofDualOppositeLinearEquiv σ N).toLinearMap := by
  ext φ x
  rfl

/-- `toDualLinearEquiv` transports the range of `ContragredientDual.map σ f` to the range of
`f.dualMap`. -/
theorem map_toDualLinearEquiv_range_map (f : M →ₗ[R] N) :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    (LinearMap.range (map σ f)).map (toDualLinearEquiv σ M).toLinearMap =
      LinearMap.range f.dualMap := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  rw [← LinearMap.range_comp, toDualLinearEquiv_comp_map, LinearEquiv.range_comp]

/-- `ofDualOppositeLinearEquiv` transports the range of `f.lcomp Rᵐᵒᵖ R` to the range of
`ContragredientDual.map σ f`. -/
theorem map_ofDualOppositeLinearEquiv_range_lcomp (f : M →ₗ[R] N) :
    let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
    haveI := RingHomInvPair.of_ringEquiv ρ
    haveI := RingHomInvPair.of_ringEquiv_symm ρ
    (LinearMap.range (f.lcomp Rᵐᵒᵖ R)).map (ofDualOppositeLinearEquiv σ M).toLinearMap =
      LinearMap.range (map σ f) := by
  let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
  have := RingHomInvPair.of_ringEquiv ρ
  have := RingHomInvPair.of_ringEquiv_symm ρ
  rw [← LinearMap.range_comp, ofDualOppositeLinearEquiv_comp_lcomp, LinearEquiv.range_comp]

/-- An `R`-linear equivalence `M ≃ₗ[R] N` induces an `S`-linear equivalence of contragredient
duals in the contravariant direction. -/
def congr (σ : S ≃+* R) (e : M ≃ₗ[R] N) :
    ContragredientDual σ N ≃ₗ[S] ContragredientDual σ M :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  (toDualLinearEquiv σ N).trans (e.dualMap.trans (toDualLinearEquiv σ M).symm)

@[simp]
theorem congr_apply (e : M ≃ₗ[R] N) (φ : ContragredientDual σ N) (x : M) :
    congr σ e φ x = φ (e x) :=
  (rfl)

@[simp]
theorem congr_symm (e : M ≃ₗ[R] N) : (congr σ e).symm = congr σ e.symm :=
  (rfl)

end CommSemiring

section CommRing

variable {S R M N : Type*} [CommRing S] [CommRing R] {σ : S ≃+* R}
  [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N]

instance : Neg (ContragredientDual σ M) := ⟨fun φ ↦ ofDual (-φ.toDual)⟩

instance : Sub (ContragredientDual σ M) := ⟨fun φ ψ ↦ ofDual (φ.toDual - ψ.toDual)⟩

instance : SMul ℤ (ContragredientDual σ M) := ⟨fun z φ ↦ ofDual (z • φ.toDual)⟩

instance : AddCommGroup (ContragredientDual σ M) :=
  toDual_injective.addCommGroup toDual
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

@[simp]
theorem neg_apply (φ : ContragredientDual σ M) (x : M) : (-φ) x = -φ x :=
  (rfl)

@[simp]
theorem sub_apply (φ ψ : ContragredientDual σ M) (x : M) : (φ - ψ) x = φ x - ψ x :=
  (rfl)

@[simp]
theorem toDual_neg (φ : ContragredientDual σ M) : (-φ).toDual = -φ.toDual :=
  (rfl)

@[simp]
theorem ofDual_neg (φ : Module.Dual R M) : ofDual (σ := σ) (-φ) = -ofDual φ :=
  (rfl)

@[simp]
theorem toDual_sub (φ ψ : ContragredientDual σ M) : (φ - ψ).toDual = φ.toDual - ψ.toDual :=
  (rfl)

@[simp]
theorem ofDual_sub (φ ψ : Module.Dual R M) :
    ofDual (σ := σ) (φ - ψ) = ofDual φ - ofDual ψ :=
  (rfl)

protected theorem map_neg (f : M →ₗ[R] N) : map σ (-f) = -map σ f := by
  ext φ x
  simp

protected theorem map_sub (f g : M →ₗ[R] N) : map σ (f - g) = map σ f - map σ g := by
  ext φ x
  simp

end CommRing

end ContragredientDual

end TauCeti

namespace Module.Basis

open TauCeti

variable {ι S R M : Type*} [Finite ι] [CommSemiring S] [CommSemiring R]
  [AddCommMonoid M] [Module R M]

/-- **Dual basis of the contragredient dual.** A finite `R`-basis `b` of `M` yields an `S`-basis
of `ContragredientDual σ M` whose `i`-th basis vector is `ContragredientDual.ofDual (b.coord i)` and
whose `i`-th coordinate of `φ` is `σ⁻¹(φ (b i))`. -/
def contragredientDual (b : Module.Basis ι R M) (σ : S ≃+* R) :
    Module.Basis ι S (ContragredientDual σ M) :=
  letI := Classical.decEq ι
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  b.dualBasis.mapₛₗ (ContragredientDual.toDualLinearEquiv σ M).symm

@[simp]
theorem contragredientDual_apply (b : Module.Basis ι R M) (σ : S ≃+* R) (i : ι) :
    b.contragredientDual σ i = ContragredientDual.ofDual (σ := σ) (b.coord i) := by
  classical
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  simp [contragredientDual, Module.Basis.mapₛₗ_apply]

@[simp]
theorem contragredientDual_repr_apply (b : Module.Basis ι R M) (σ : S ≃+* R)
    (φ : ContragredientDual σ M) (i : ι) :
    (b.contragredientDual σ).repr φ i = σ.symm (φ (b i)) := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  simp [contragredientDual, Module.Basis.mapₛₗ_repr, Module.Basis.dualBasis_repr]

theorem contragredientDual_equivFun_apply (b : Module.Basis ι R M) (σ : S ≃+* R)
    (φ : ContragredientDual σ M) (i : ι) :
    (b.contragredientDual σ).equivFun φ i = σ.symm (φ (b i)) := by
  rw [Module.Basis.equivFun_apply, contragredientDual_repr_apply]

theorem contragredientDual_apply_self (b : Module.Basis ι R M) (σ : S ≃+* R) [DecidableEq ι]
    (i j : ι) : b.contragredientDual σ i (b j) = if j = i then 1 else 0 := by
  rw [contragredientDual_apply, ContragredientDual.ofDual_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

end Module.Basis

namespace TauCeti.ContragredientDual

section MatrixAndProjective

variable {S R M N : Type*} [CommSemiring S] [CommSemiring R] {σ : S ≃+* R}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- In the contragredient dual bases attached to finite bases `b₁` of `M` and `b₀` of `N`, the
matrix of `ContragredientDual.map σ f` is the transpose of the matrix of `f` with `σ⁻¹` applied
entrywise. -/
theorem toMatrix_map {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (σ : S ≃+* R) (b₁ : Module.Basis ι R M) (b₀ : Module.Basis κ R N) (f : M →ₗ[R] N) :
    LinearMap.toMatrix (b₀.contragredientDual σ) (b₁.contragredientDual σ) (map σ f) =
      (LinearMap.toMatrix b₁ b₀ f)ᵀ.map σ.symm := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

/-- For a matrix `A`, the matrix of `ContragredientDual.map σ (Matrix.toLin' A)` in the
contragredient duals of the standard bases is `Aᵀ.map σ.symm`. -/
@[simp]
theorem toMatrix_map_toLin' {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (σ : S ≃+* R) (A : Matrix ι κ R) :
    LinearMap.toMatrix ((Pi.basisFun R ι).contragredientDual σ)
        ((Pi.basisFun R κ).contragredientDual σ) (map σ (Matrix.toLin' A)) =
      Aᵀ.map σ.symm := by
  rw [toMatrix_map, ← Matrix.toLin_eq_toLin', LinearMap.toMatrix_toLin]

instance free [Module.Finite R M] [Module.Free R M] :
    Module.Free S (ContragredientDual σ M) :=
  .of_basis ((Module.Free.chooseBasis R M).contragredientDual σ)

instance projective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective S (ContragredientDual σ M) :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  Module.Projective.of_equiv (toDualLinearEquiv σ M).symm

instance finite [Module.Finite R M] [Module.Projective R M] :
    Module.Finite S (ContragredientDual σ M) :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  Module.Finite.of_surjective (toDualLinearEquiv σ M).symm.toLinearMap
    (toDualLinearEquiv σ M).symm.surjective

end MatrixAndProjective

section Examples

-- Under the coordinate swap `σ = RingEquiv.prodComm` on `R × R`, the contragredient action of
-- `(1, 0)` on `id` evaluates at `1` to `(0, 1)`.
example {R : Type*} [CommRing R] :
    (((1, 0) : R × R) • ofDual (σ := (RingEquiv.prodComm : R × R ≃+* R × R)) LinearMap.id) 1 =
      (0, 1) := by
  simp

-- For `σ = id`, the contragredient dual recovers the ordinary dual action `(s • φ) x = s * φ x`.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : R) (φ : ContragredientDual (RingEquiv.refl R) M) (x : M) :
    (s • φ) x = s * φ x :=
  smul_apply_eq_mul s φ x

-- When `R` is nontrivial, the contragredient action `((1, 0) • id) 1 = (0, 1)` along
-- `RingEquiv.prodComm` differs from the ordinary dual value `((1, 0) • id) 1 = (1, 0)`.
example {R : Type*} [CommRing R] [Nontrivial R] :
    (((1, 0) : R × R) • ofDual (σ := (RingEquiv.prodComm : R × R ≃+* R × R)) LinearMap.id) 1 ≠
      (((1, 0) : R × R) • (LinearMap.id : Module.Dual (R × R) (R × R))) 1 := by
  intro h
  have hfst := congrArg Prod.fst h
  simp at hfst

end Examples

end TauCeti.ContragredientDual
