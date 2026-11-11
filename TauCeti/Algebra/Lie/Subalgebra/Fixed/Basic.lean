/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.Algebra.Lie.Hom

/-!
# Fixed Lie subalgebras

The fixed submodule of a Lie endomorphism is closed under brackets. Its underlying
submodule is the existing linear fixed submodule.

Intertwining homomorphisms restrict to these subalgebras, and intertwining equivalences
restrict with the expected inverse.
-/

public section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {M N : Type*} [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N]

namespace LieHom

/-- The Lie subalgebra fixed by an endomorphism, with the native fixed submodule. -/
def fixedSubalgebra (f : L →ₗ⁅R⁆ L) : LieSubalgebra R L where
  __ := f.toLinearMap.fixedSubmodule
  lie_mem' {x y} hx hy := by
    exact LinearMap.mem_fixedSubmodule_iff.mpr ((f.map_lie x y).trans
      (congrArg₂ (fun x y : L => ⁅x, y⁆) (LinearMap.mem_fixedSubmodule_iff.mp hx)
        (LinearMap.mem_fixedSubmodule_iff.mp hy)))

/-- Membership in the fixed Lie subalgebra is the fixed-point equation. -/
@[simp]
theorem mem_fixedSubalgebra {f : L →ₗ⁅R⁆ L} {x : L} :
    x ∈ f.fixedSubalgebra ↔ f x = x :=
  Iff.rfl

/-- The underlying submodule is the existing linear fixed submodule. -/
@[simp]
theorem fixedSubalgebra_toSubmodule (f : L →ₗ⁅R⁆ L) :
    f.fixedSubalgebra.toSubmodule = f.toLinearMap.fixedSubmodule := by
  rfl

/-- The underlying fixed submodule is the equalizer of the endomorphism and identity. -/
theorem fixedSubalgebra_toSubmodule_eq_eqLocus (f : L →ₗ⁅R⁆ L) :
    f.fixedSubalgebra.toSubmodule = LinearMap.eqLocus f.toLinearMap LinearMap.id := by
  ext x
  exact mem_fixedSubalgebra

@[simp]
theorem apply_coe_fixedSubalgebra (f : L →ₗ⁅R⁆ L) (x : f.fixedSubalgebra) :
    f (x : L) = x :=
  x.property

/-- An endomorphism is the identity on its fixed subalgebra. -/
@[simp]
theorem comp_incl_fixedSubalgebra (f : L →ₗ⁅R⁆ L) :
    f.comp f.fixedSubalgebra.incl = f.fixedSubalgebra.incl :=
  LieHom.ext fun x => by simp

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- An intertwining homomorphism maps fixed elements to fixed elements. -/
theorem apply_mem_fixedSubalgebra (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f) {x : L}
    (hx : x ∈ f.fixedSubalgebra) : u x ∈ g.fixedSubalgebra :=
  mem_fixedSubalgebra.mpr <| calc
    g (u x) = u (f x) := congr_fun h x
    _ = u x := congrArg u (mem_fixedSubalgebra.mp hx)

/-- An intertwining homomorphism restricts to the fixed Lie subalgebras. -/
def restrictFixed (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f) :
    f.fixedSubalgebra →ₗ⁅R⁆ g.fixedSubalgebra where
  __ := u.toLinearMap.restrict (p := f.fixedSubalgebra.toSubmodule)
    (q := g.fixedSubalgebra.toSubmodule) fun _ hx =>
      (LieSubalgebra.mem_toSubmodule _).mpr
        (apply_mem_fixedSubalgebra u h ((LieSubalgebra.mem_toSubmodule _).mp hx))
  map_lie' {x y} := Subtype.ext (u.map_lie x y)

@[simp]
theorem coe_restrictFixed (u : L →ₗ⁅R⁆ M) (h : g.comp u = u.comp f)
    (x : f.fixedSubalgebra) : (restrictFixed u h x : M) = u x := by
  rfl

@[simp]
theorem restrictFixed_id (f : L →ₗ⁅R⁆ L) :
    restrictFixed (f := f) (g := f) (LieHom.id : L →ₗ⁅R⁆ L) rfl = LieHom.id := by
  rfl

/-- Restriction preserves composition of intertwining maps. -/
theorem restrictFixed_comp (u : L →ₗ⁅R⁆ M) (v : M →ₗ⁅R⁆ N)
    (hu : g.comp u = u.comp f) (hv : k.comp v = v.comp g) :
    restrictFixed (v.comp u) (comp_intertwines u v hu hv) =
      (restrictFixed v hv).comp (restrictFixed u hu) := by
  rfl

end LieHom

namespace LieEquiv

variable {f : L →ₗ⁅R⁆ L} {g : M →ₗ⁅R⁆ M} {k : N →ₗ⁅R⁆ N}

/-- An intertwining equivalence maps the fixed subalgebra onto the fixed subalgebra. -/
theorem map_fixedSubalgebra (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    f.fixedSubalgebra.map e.toLieHom = g.fixedSubalgebra := by
  ext y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact LieHom.apply_mem_fixedSubalgebra e.toLieHom h hx
  · intro hy
    exact ⟨e.symm y, LieHom.apply_mem_fixedSubalgebra e.symm.toLieHom (e.symm_intertwines h) hy,
      e.apply_symm_apply y⟩

/-- An intertwining equivalence restricts to an equivalence of fixed Lie subalgebras. -/
def restrictFixed (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    f.fixedSubalgebra ≃ₗ⁅R⁆ g.fixedSubalgebra :=
  e.ofSubalgebras _ _ (e.map_fixedSubalgebra h)

@[simp]
theorem coe_restrictFixed (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f)
    (x : f.fixedSubalgebra) : (e.restrictFixed h x : M) = e x :=
  e.ofSubalgebras_apply _ _ _ x

theorem coe_restrictFixed_symm (e : L ≃ₗ⁅R⁆ M)
    (h : g.comp e.toLieHom = e.toLieHom.comp f) (y : g.fixedSubalgebra) :
    ((e.restrictFixed h).symm y : L) = e.symm y :=
  e.ofSubalgebras_symm_apply _ _ _ y

/-- The restricted equivalence is, as a homomorphism, the restricted homomorphism. -/
@[simp]
theorem restrictFixed_toLieHom (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    (e.restrictFixed h).toLieHom = LieHom.restrictFixed e.toLieHom h :=
  LieHom.ext fun x => Subtype.ext
    ((coe_restrictFixed e h x).trans (LieHom.coe_restrictFixed e.toLieHom h x).symm)

@[simp]
theorem restrictFixed_refl (h : f.comp (LieEquiv.refl : L ≃ₗ⁅R⁆ L).toLieHom =
      (LieEquiv.refl : L ≃ₗ⁅R⁆ L).toLieHom.comp f) :
    LieEquiv.refl.restrictFixed h = (LieEquiv.refl : f.fixedSubalgebra ≃ₗ⁅R⁆ f.fixedSubalgebra) :=
  LieEquiv.ext fun x => Subtype.ext (coe_restrictFixed _ h x)

/-- Restriction preserves composition of intertwining equivalences. -/
@[simp]
theorem restrictFixed_trans (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N)
    (h₁ : g.comp e₁.toLieHom = e₁.toLieHom.comp f)
    (h₂ : k.comp e₂.toLieHom = e₂.toLieHom.comp g) :
    (e₁.restrictFixed h₁).trans (e₂.restrictFixed h₂) =
      (e₁.trans e₂).restrictFixed (trans_intertwines e₁ e₂ h₁ h₂) :=
  LieEquiv.ext fun x => Subtype.ext (by simp only [trans_apply, coe_restrictFixed])

/-- Restricting the inverse gives the inverse of the restricted equivalence. -/
@[simp]
theorem restrictFixed_symm (e : L ≃ₗ⁅R⁆ M) (h : g.comp e.toLieHom = e.toLieHom.comp f) :
    (e.restrictFixed h).symm = e.symm.restrictFixed (e.symm_intertwines h) :=
  LieEquiv.ext fun y => Subtype.ext
    ((coe_restrictFixed_symm e h y).trans (coe_restrictFixed e.symm _ y).symm)

end LieEquiv
