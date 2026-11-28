/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Ideal

/-!
# Intertwining Lie algebra homomorphisms

Basic constructors, simp, eigenvector, and intertwining lemmas for `LieHom`, `LieEquiv`, and
`LinearEquiv`: construction of `LieEquiv` from mutually inverse `LieHom`s (`LieEquiv.ofLieHoms`),
eigenvalue multiplication under brackets (`LieHom.map_lie_of_apply_eq_smul`), composition and
cancellation of intertwining homomorphisms and equivalences (`LieHom.comp_intertwines`,
`LieEquiv.symm_intertwines`, `LieEquiv.trans_intertwines`, `LinearEquiv.symm_lie_eq_of_lie_eq`),
the transport `e ∘ θ ∘ e⁻¹` of an automorphism along an isomorphism (`LieEquiv.conj`), and the
restriction of a Lie homomorphism to Lie subalgebras or Lie ideals it maps into each other
(`LieHom.restrict`, `LieHom.restrictIdeal`).
-/

public section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {M N : Type*} [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]

namespace LieHom

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- Intertwining homomorphisms compose to an intertwining homomorphism. -/
theorem comp_intertwines (u : L →ₗ⁅R⁆ M) (v : M →ₗ⁅R⁆ N)
    (hu : g.comp u = u.comp f) (hv : k.comp v = v.comp g) :
    k.comp (v.comp u) = (v.comp u).comp f := by
  ext x
  exact (congr_fun hv (u x)).trans (congrArg v (congr_fun hu x))

/-- A Lie algebra endomorphism multiplies eigenvalues on Lie brackets of eigenvectors. -/
theorem map_lie_of_apply_eq_smul (f : L →ₗ⁅R⁆ L) {u v : L} {μ ν : R}
    (hu : f u = μ • u) (hv : f v = ν • v) :
    f ⁅u, v⁆ = (μ * ν) • ⁅u, v⁆ := by
  rw [map_lie, hu, hv, smul_lie, lie_smul, smul_smul]

end LieHom

namespace LieEquiv

/-- Construct a `LieEquiv` from two mutually inverse `LieHom`s. -/
def ofLieHoms (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ L)
    (h₁ : g.comp f = LieHom.id) (h₂ : f.comp g = LieHom.id) : L ≃ₗ⁅R⁆ M where
  toLieHom := f
  invFun := g
  left_inv x := congr($h₁ x)
  right_inv x := congr($h₂ x)

@[simp]
theorem ofLieHoms_apply (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ L) (h₁ h₂) (x : L) :
    ofLieHoms f g h₁ h₂ x = f x :=
  (rfl)

@[simp]
theorem symm_ofLieHoms (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ L) (h₁ h₂) :
    (ofLieHoms f g h₁ h₂).symm = ofLieHoms g f h₂ h₁ := by
  ext x; rfl

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- The inverse of an intertwining equivalence intertwines in the opposite direction. -/
theorem symm_intertwines (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    f.comp e.symm.toLieHom = e.symm.toLieHom.comp g := by
  ext y
  apply e.injective
  simpa using (LieHom.congr_fun h (e.symm y)).symm

/-- The composite of intertwining equivalences intertwines. -/
theorem trans_intertwines (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N)
    (h₁ : g.comp e₁.toLieHom = e₁.toLieHom.comp f)
    (h₂ : k.comp e₂.toLieHom = e₂.toLieHom.comp g) :
    k.comp (e₁.trans e₂).toLieHom = (e₁.trans e₂).toLieHom.comp f :=
  LieHom.comp_intertwines e₁.toLieHom e₂.toLieHom h₁ h₂

/-- The transport `e ∘ θ ∘ e⁻¹` of an automorphism `θ` of `L` along an isomorphism `e : L ≃ M`. -/
def conj (e : L ≃ₗ⁅R⁆ M) (θ : L ≃ₗ⁅R⁆ L) : M ≃ₗ⁅R⁆ M :=
  (e.symm.trans θ).trans e

@[simp]
theorem conj_apply (e : L ≃ₗ⁅R⁆ M) (θ : L ≃ₗ⁅R⁆ L) (x : M) : e.conj θ x = e (θ (e.symm x)) :=
  (rfl)

/-- Transporting along `e` and then along `e⁻¹` gives back `θ`. -/
@[simp]
theorem symm_conj_conj (e : L ≃ₗ⁅R⁆ M) (θ : L ≃ₗ⁅R⁆ L) : e.symm.conj (e.conj θ) = θ :=
  LieEquiv.ext fun x ↦ by simp

/-- The transport of an involution is an involution. -/
theorem involutive_conj {e : L ≃ₗ⁅R⁆ M} {θ : L ≃ₗ⁅R⁆ L} (hθ : Function.Involutive θ) :
    Function.Involutive (e.conj θ) :=
  fun x ↦ by simp [hθ (e.symm x)]

end LieEquiv

namespace LinearEquiv

/-- If a linear equivalence `e` intertwines two bracket actions along a Lie equivalence `φ`, then
`e.symm` intertwines them along `φ.symm`. -/
theorem symm_lie_eq_of_lie_eq {L' M₀ M₀' : Type*}
    [LieRing L'] [LieAlgebra R L']
    [AddCommMonoid M₀] [Module R M₀] [Bracket L M₀]
    [AddCommMonoid M₀'] [Module R M₀'] [Bracket L' M₀']
    (e : M₀ ≃ₗ[R] M₀') (φ : L' ≃ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M₀), e ⁅φ x, m⁆ = ⁅x, e m⁆) (y : L) (m' : M₀') :
    e.symm ⁅φ.symm y, m'⁆ = ⁅y, e.symm m'⁆ :=
  e.injective <| by simpa using (he (φ.symm y) (e.symm m')).symm

end LinearEquiv

namespace LieHom

variable (f : L →ₗ⁅R⁆ M)

/-- The restriction of a Lie homomorphism `f` to Lie subalgebras `S` and `T` with `f(S) ⊆ T`, as
a Lie homomorphism `S → T`. Its linear map is `LinearMap.restrict`. -/
def restrict {S : LieSubalgebra R L} {T : LieSubalgebra R M} (hf : ∀ x ∈ S, f x ∈ T) :
    S →ₗ⁅R⁆ T :=
  { (f : L →ₗ[R] M).restrict (p := S.toSubmodule) (q := T.toSubmodule) hf with
    map_lie' := Subtype.ext (f.map_lie _ _) }

@[simp]
theorem coe_restrict_apply {S : LieSubalgebra R L} {T : LieSubalgebra R M}
    (hf : ∀ x ∈ S, f x ∈ T) (x : S) : (f.restrict hf x : M) = f x :=
  (rfl)

/-- The restriction of `f`, followed by the inclusion of `T`, is `f` on `S`. -/
@[simp]
theorem incl_comp_restrict {S : LieSubalgebra R L} {T : LieSubalgebra R M}
    (hf : ∀ x ∈ S, f x ∈ T) : T.incl.comp (f.restrict hf) = f.comp S.incl :=
  LieHom.ext fun _ ↦ (rfl)

/-- The restriction of a Lie homomorphism `f` to Lie ideals `J` and `J'` with `f(J) ⊆ J'`, as a Lie
homomorphism `J → J'`: `LieHom.restrict` for the underlying Lie subalgebras. -/
def restrictIdeal {J : LieIdeal R L} {J' : LieIdeal R M} (hf : ∀ x ∈ J, f x ∈ J') :
    J →ₗ⁅R⁆ J' :=
  f.restrict (S := J) (T := J') hf

@[simp]
theorem coe_restrictIdeal_apply {J : LieIdeal R L} {J' : LieIdeal R M}
    (hf : ∀ x ∈ J, f x ∈ J') (x : J) : (f.restrictIdeal hf x : M) = f x :=
  (rfl)

/-- The restriction of `f` to ideals, followed by the inclusion of `J'`, is `f` on `J`. -/
@[simp]
theorem incl_comp_restrictIdeal {J : LieIdeal R L} {J' : LieIdeal R M}
    (hf : ∀ x ∈ J, f x ∈ J') : J'.incl.comp (f.restrictIdeal hf) = f.comp J.incl :=
  LieHom.ext fun _ ↦ (rfl)

end LieHom
