/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Projective

import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# The contragredient dual along a ring isomorphism

Let `σ : S ≃+* R` be a ring isomorphism of commutative semirings and `M` an `R`-module. The
*contragredient dual* `ContragredientDual σ M` is the dual space `Hom_R(M, R)` equipped with the
`S`-module structure obtained by restricting scalars along `σ`:

  `(s • φ) x = φ (σ s • x) = σ s * φ x`.

For a group algebra `R = S = O[G]` with `σ = #` the antipode `g ↦ g⁻¹`, this is the contragredient
action `(g • φ) x = φ (g⁻¹ • x)`. More generally, when `R = R_Ψ` is a character group ring and
`S = R^# = R_{Ψ⁻¹}` is its conjugate under `# : R^# ≃+* R`, it gives the `R^#`-module structure on
`Hom_R(M, R)` used by Dasgupta and Kakde to form transposed presentations.

Precomposition turns an `R`-linear map `f : M →ₗ[R] N` contravariantly into an `S`-linear map
`ContragredientDual.map σ f : ContragredientDual σ N →ₗ[S] ContragredientDual σ M`. Because `σ` is
a ring isomorphism, `toDualLinearEquiv` is a `σ`-semilinear equivalence onto `Module.Dual R M`: a
finite `R`-basis of `M` yields an `S`-basis of `ContragredientDual σ M`
(`Basis.contragredientDual`), and finite generation, freeness, and projectivity transport from `M`
over `R` to `ContragredientDual σ M` over `S`.

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
  `TauCeti.ContragredientDual.projective`: preservation of freeness, finite generation, and
  projectivity for finite modules.

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

theorem map_smul_of_tower (φ : ContragredientDual σ M) (r : R) (x : M) :
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

instance : Module S (ContragredientDual σ M) where
  one_smul φ := toDual_injective <| by simp
  mul_smul s t φ := toDual_injective <| by simp [mul_smul]
  smul_zero s := toDual_injective <| by simp
  smul_add s φ ψ := toDual_injective <| by simp
  add_smul s t φ := toDual_injective <| by simp [add_smul]
  zero_smul φ := toDual_injective <| by simp

/-- **The contragredient scalar action**: `(s • φ) x = φ (σ s • x)`. -/
@[simp]
theorem smul_apply (s : S) (φ : ContragredientDual σ M) (x : M) :
    (s • φ) x = φ (σ s • x) := by
  rw [← toDual_apply, toDual_smul, LinearMap.smul_apply, smul_eq_mul, ← smul_eq_mul,
    ← φ.toDual.map_smul, toDual_apply]

theorem smul_apply_eq_mul (s : S) (φ : ContragredientDual σ M) (x : M) :
    (s • φ) x = σ s * φ x := by
  rw [smul_apply, map_smul_of_tower]

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

/-- Precomposition with `f : M →ₗ[R] N` as an `S`-linear map between contragredient duals. -/
def map (σ : S ≃+* R) (f : M →ₗ[R] N) : ContragredientDual σ N →ₗ[S] ContragredientDual σ M where
  toFun φ := ofDual (φ.toDual.comp f)
  map_add' φ ψ := ext fun x ↦ by simp
  map_smul' s φ := ext fun x ↦ by simp

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
theorem map_zero : map σ (0 : M →ₗ[R] N) = 0 := by
  ext φ x
  simp

protected theorem map_add (f g : M →ₗ[R] N) : map σ (f + g) = map σ f + map σ g := by
  ext φ x
  simp

/-- An `R`-linear equivalence `M ≃ₗ[R] N` induces an `S`-linear equivalence of contragredient
duals in the contravariant direction. -/
def congr (σ : S ≃+* R) (e : M ≃ₗ[R] N) :
    ContragredientDual σ N ≃ₗ[S] ContragredientDual σ M :=
  LinearEquiv.ofLinearMap (map σ e.toLinearMap) (map σ e.symm.toLinearMap)
    (by rw [← map_comp, e.symm_comp, map_id])
    (by rw [← map_comp, e.comp_symm, map_id])

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
  let coordEquiv : ContragredientDual σ M ≃ₗ[S] (ι → S) :=
    { toFun φ i := σ.symm (φ (b i))
      invFun v := ContragredientDual.ofDual (b.constr R fun i ↦ σ (v i))
      map_add' φ ψ := funext fun i ↦ by simp
      map_smul' s φ := funext fun i ↦ by
        rw [ContragredientDual.smul_apply_eq_mul, map_mul, σ.symm_apply_apply,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      left_inv φ := ContragredientDual.ext fun x ↦ by
        simp only [ContragredientDual.ofDual_apply, σ.apply_symm_apply]
        exact LinearMap.congr_fun (b.ext fun i ↦ by simp :
          b.constr R (fun i ↦ φ (b i)) = φ.toDual) x
      right_inv v := funext fun i ↦ by
        simp only [ContragredientDual.ofDual_apply, Module.Basis.constr_basis,
          σ.symm_apply_apply] }
  Module.Basis.ofRepr (coordEquiv.trans (Finsupp.linearEquivFunOnFinite S S ι).symm)

@[simp]
theorem contragredientDual_repr_apply (b : Module.Basis ι R M) (σ : S ≃+* R)
    (φ : ContragredientDual σ M) (i : ι) :
    (b.contragredientDual σ).repr φ i = σ.symm (φ (b i)) := by
  simp [contragredientDual]

theorem contragredientDual_equivFun_apply (b : Module.Basis ι R M) (σ : S ≃+* R)
    (φ : ContragredientDual σ M) (i : ι) :
    (b.contragredientDual σ).equivFun φ i = σ.symm (φ (b i)) := by
  rw [Module.Basis.equivFun_apply, contragredientDual_repr_apply]

@[simp]
theorem contragredientDual_apply (b : Module.Basis ι R M) (σ : S ≃+* R) (i : ι) :
    b.contragredientDual σ i = ContragredientDual.ofDual (σ := σ) (b.coord i) := by
  classical
  apply (b.contragredientDual σ).repr.injective
  ext j
  rw [Module.Basis.repr_self, contragredientDual_repr_apply, ContragredientDual.ofDual_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

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
  rw [LinearMap.toMatrix_apply, Module.Basis.contragredientDual_repr_apply, map_apply,
    Module.Basis.contragredientDual_apply, ofDual_apply, Module.Basis.coord_apply,
    Matrix.map_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply]

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

private theorem exists_retract (σ : S ≃+* R) [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (i : ContragredientDual σ M →ₗ[S] ContragredientDual σ (Fin n → R))
      (s : ContragredientDual σ (Fin n → R) →ₗ[S] ContragredientDual σ M), s ∘ₗ i = .id := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨n, map σ f, map σ g, by rw [← map_comp, hfg, map_id]⟩

instance projective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective S (ContragredientDual σ M) := by
  obtain ⟨_, i, s, hsi⟩ := exists_retract σ (M := M)
  exact .of_split i s hsi

instance finite [Module.Finite R M] [Module.Projective R M] :
    Module.Finite S (ContragredientDual σ M) := by
  obtain ⟨n, i, s, hsi⟩ := exists_retract σ (M := M)
  have : Module.Finite S (ContragredientDual σ (Fin n → R)) :=
    .of_basis ((Pi.basisFun R (Fin n)).contragredientDual σ)
  exact .of_surjective s (LinearMap.surjective_of_comp_eq_id i s hsi)

end MatrixAndProjective

section Examples

-- Over `O[G]` with `σ = #` the antipode `g ↦ g⁻¹`, the contragredient action of `g` on `id`
-- evaluates at `1` to `g⁻¹`.
example {O G : Type*} [CommRing O] [CommGroup G] (g : G) :
    let σ := (TauCeti.HopfAlgebra.antipodeAlgEquiv (R := O) (A := MonoidAlgebra O G)).toRingEquiv
    (MonoidAlgebra.of O G g • ofDual (σ := σ) LinearMap.id) 1 = MonoidAlgebra.of O G g⁻¹ := by
  simp [MonoidAlgebra.of_apply]

-- For `σ = id`, the contragredient dual recovers the ordinary dual action `(s • φ) x = s * φ x`.
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : R) (φ : ContragredientDual (RingEquiv.refl R) M) (x : M) :
    (s • φ) x = s * φ x :=
  smul_apply_eq_mul s φ x

-- When `O` is nontrivial and `g⁻¹ ≠ g`, the contragredient action `(g • id) 1 = g⁻¹` differs
-- from the ordinary dual value `(g • id) 1 = g`.
example {O G : Type*} [CommRing O] [Nontrivial O] [CommGroup G] (g : G) (hg : g⁻¹ ≠ g) :
    (MonoidAlgebra.of O G g •
      ofDual (σ := (TauCeti.HopfAlgebra.antipodeAlgEquiv
        (R := O) (A := MonoidAlgebra O G)).toRingEquiv) LinearMap.id) 1 ≠
      (MonoidAlgebra.of O G g • (LinearMap.id : Module.Dual (MonoidAlgebra O G) _)) 1 := by
  intro h
  have h1 : (MonoidAlgebra.of O G g •
      ofDual (σ := (TauCeti.HopfAlgebra.antipodeAlgEquiv
        (R := O) (A := MonoidAlgebra O G)).toRingEquiv) LinearMap.id) 1 =
      MonoidAlgebra.of O G g⁻¹ := by
    simp [MonoidAlgebra.of_apply]
  have h2 : (MonoidAlgebra.of O G g • (LinearMap.id : Module.Dual (MonoidAlgebra O G) _)) 1 =
      MonoidAlgebra.of O G g := by
    simp [MonoidAlgebra.of_apply]
  rw [h1, h2, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply] at h
  have hcoeff := congrArg (fun x : MonoidAlgebra O G ↦ x.coeff g) h
  simp [MonoidAlgebra.coeff_single, hg] at hcoeff

end Examples

end TauCeti.ContragredientDual
