/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinear
public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Restriction from `GL` to `SL`

Every finite-dimensional irreducible representation of the general linear group over
an algebraically closed field stays irreducible on the special linear group. Scalar
matrices act by scalars by Schur's lemma, and every invertible matrix is a scalar
multiple of a determinant-one matrix. Thus restriction introduces no new invariant
subspaces. No rationality or characteristic assumption is needed for this result.

Restriction does lose the determinant: twisting by a power of `det` does not change the
restriction to `SL` (`Representation.charTwist_det_zpow_comp_toGL`). For representations on which
the scalar matrices act through characters `z ↦ z ^ a` and `z ↦ z ^ b`, this is the only
information lost. A linear map intertwining the two restrictions intertwines the `GL` actions
once the first is twisted by `det ^ t`, where `b = a + |ι| t`, because every invertible matrix is a
determinant-one matrix times a scalar matrix. Such a `t` exists as soon as the intertwiner is
nonzero: a primitive `|ι|`-th root of unity `ζ` gives the scalar matrix `ζ` of determinant one, on
which the intertwiner forces `ζ ^ a = ζ ^ b`. So the restrictions are equivalent exactly when one
representation is a determinant twist of the other
(`Representation.nonempty_equiv_comp_toGL_iff`). The root of unity is what fails when the
characteristic divides `|ι|`, and that hypothesis cannot be dropped: over an algebraically closed
field of characteristic `2`, the determinant of `GL₂` followed by the inverse of the Frobenius is a
character that is trivial on `SL₂` but on which the scalar `z` acts by `z ^ 1`.

## Main results

* `Representation.isIrreducible_comp_toGL_iff`: a finite-dimensional representation of `GL` is
  irreducible on `SL` exactly when it is irreducible.
* `Representation.charTwist_det_zpow_comp_toGL`: a determinant twist has the same restriction to
  `SL`.
* `Representation.dvd_sub_of_isIntertwiningMap_comp_toGL` and
  `Representation.isIntertwiningMap_charTwist_det_zpow_of_comp_toGL`: a nonzero intertwiner of
  the restrictions forces the scalar exponents to agree modulo `|ι|`, and then intertwines the
  matching determinant twist on all of `GL`.
* `Representation.nonempty_equiv_comp_toGL_iff`: two representations of `GL` with scalar central
  characters restrict to equivalent representations of `SL` exactly when one is equivalent to a
  determinant twist of the other.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

namespace Representation

variable {ι K V : Type*} [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A finite-dimensional representation of `GL` over an algebraically closed field is
irreducible on `SL` exactly when it is irreducible on `GL`, including in rank zero. -/
@[simp]
theorem isIrreducible_comp_toGL_iff (ρ : Representation K (Matrix.GeneralLinearGroup ι K) V) :
    Representation.IsIrreducible (ρ.comp Matrix.SpecialLinearGroup.toGL) ↔ ρ.IsIrreducible := by
  constructor
  · intro hρ
    have := hρ
    have := hρ.nontrivial
    refine ⟨fun S => ?_⟩
    let T : Subrepresentation (ρ.comp Matrix.SpecialLinearGroup.toGL) :=
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule _ hv }
    refine (eq_bot_or_eq_top T).imp (fun h => ?_) fun h => ?_
    · apply Subrepresentation.toSubmodule_injective
      simpa only [T, Subrepresentation.toSubmodule_bot] using
        congrArg Subrepresentation.toSubmodule h
    · apply Subrepresentation.toSubmodule_injective
      simpa only [T, Subrepresentation.toSubmodule_top] using
        congrArg Subrepresentation.toSubmodule h
  intro hρ
  have := hρ
  have := hρ.nontrivial
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g v hv := by
        obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
        obtain ⟨a, ha⟩ := IsIrreducible.exists_forall_apply_eq_smul
          (ρ (Matrix.GeneralLinearGroup.scalar ι z)) fun g v => by
            simpa only [map_mul, Module.End.mul_apply] using
              congrArg (fun g => ρ g v) (Matrix.GeneralLinearGroup.scalar_commute z g)
        rw [map_mul, Module.End.mul_apply, ha, map_smul]
        exact S.toSubmodule.smul_mem a (S.apply_mem_toSubmodule s hv) }
  refine (eq_bot_or_eq_top T).imp (fun h => ?_) fun h => ?_
  · apply Subrepresentation.toSubmodule_injective
    simpa only [T, Subrepresentation.toSubmodule_bot] using
      congrArg Subrepresentation.toSubmodule h
  · apply Subrepresentation.toSubmodule_injective
    simpa only [T, Subrepresentation.toSubmodule_top] using
      congrArg Subrepresentation.toSubmodule h

section CommRing

open Matrix

variable {ι K V : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
  [AddCommGroup V] [Module K V]

/-- **A determinant twist is invisible on `SL`**: twisting a representation of `GL` by a power of
the determinant does not change its restriction to the special linear group. -/
@[simp]
theorem charTwist_det_zpow_comp_toGL (ρ : Representation K (GL ι K) V) (t : ℤ) :
    (charTwist ((GeneralLinearGroup.det : GL ι K →* Kˣ) ^ t) ρ).comp SpecialLinearGroup.toGL =
      ρ.comp SpecialLinearGroup.toGL := by
  ext s v
  simp

end CommRing

section Twist

open Matrix

variable {ι K V W : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K (GL ι K) V} {σ : Representation K (GL ι K) W}

/-- **A nonzero intertwiner of the restrictions to `SL` matches the scalar exponents modulo the
matrix size.** If scalar matrices act on `ρ` by `z ↦ z ^ a` and on `σ` by `z ↦ z ^ b`, and a nonzero
linear map intertwines the restrictions of `ρ` and `σ` to `SL ι K`, then `|ι|` divides `b - a`: a
primitive `|ι|`-th root of unity `ζ` is a scalar matrix of determinant one, and the intertwiner
forces `ζ ^ a = ζ ^ b`. -/
theorem dvd_sub_of_isIntertwiningMap_comp_toGL [NeZero (Fintype.card ι)]
    [HasEnoughRootsOfUnity K (Fintype.card ι)] {a b : ℤ}
    (ha : ∀ (z : Kˣ) (v : V), ρ (GeneralLinearGroup.scalar ι z) v = ((z ^ a : Kˣ) : K) • v)
    (hb : ∀ (z : Kˣ) (w : W), σ (GeneralLinearGroup.scalar ι z) w = ((z ^ b : Kˣ) : K) • w)
    {f : V →ₗ[K] W}
    (hf : IsIntertwiningMap (ρ.comp SpecialLinearGroup.toGL) (σ.comp SpecialLinearGroup.toGL) f)
    (hf0 : f ≠ 0) :
    (Fintype.card ι : ℤ) ∣ b - a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (Fintype.card ι)
  let u : Kˣ := (hζ.isUnit (NeZero.ne _)).unit
  have hu : IsPrimitiveRoot u (Fintype.card ι) := IsPrimitiveRoot.coe_units_iff.mp hζ
  -- The scalar matrix `u` has determinant `u ^ |ι| = 1`, so it lies in `SL ι K`.
  let s : SpecialLinearGroup ι K :=
    ⟨GeneralLinearGroup.scalar ι u, by
      rw [← GeneralLinearGroup.val_det_apply, GeneralLinearGroup.det_scalar, hu.pow_eq_one,
        Units.val_one]⟩
  have hs : SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar ι u := Units.ext rfl
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext h)
  have h := hf.isIntertwining s v
  simp only [MonoidHom.coe_comp, Function.comp_apply, hs, ha, hb, map_smul] at h
  have hab : u ^ a = u ^ b := Units.ext (smul_left_injective K hv h)
  rw [← hu.zpow_eq_one_iff_dvd, zpow_sub, hab, mul_inv_cancel]

/-- **An intertwiner of the restrictions to `SL` intertwines a determinant twist on all of `GL`.**
If scalar matrices act on `ρ` by `z ↦ z ^ a` and on `σ` by `z ↦ z ^ (a + |ι| t)`, then a linear map
intertwining the restrictions of `ρ` and `σ` to `SL ι K` intertwines the twist of `ρ` by `det ^ t`
with `σ`, since over an algebraically closed field every invertible matrix is a determinant-one
matrix times a scalar matrix. -/
theorem isIntertwiningMap_charTwist_det_zpow_of_comp_toGL [IsAlgClosed K] {a t : ℤ}
    (ha : ∀ (z : Kˣ) (v : V), ρ (GeneralLinearGroup.scalar ι z) v = ((z ^ a : Kˣ) : K) • v)
    (hb : ∀ (z : Kˣ) (w : W),
      σ (GeneralLinearGroup.scalar ι z) w = ((z ^ (a + Fintype.card ι * t) : Kˣ) : K) • w)
    {f : V →ₗ[K] W}
    (hf : IsIntertwiningMap (ρ.comp SpecialLinearGroup.toGL) (σ.comp SpecialLinearGroup.toGL) f) :
    (charTwist ((GeneralLinearGroup.det : GL ι K →* Kˣ) ^ t) ρ).IsIntertwiningMap σ f := by
  refine ⟨fun g v => ?_⟩
  obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
  have hs := hf.isIntertwining s v
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hs
  simp only [charTwist_apply_apply, MonoidHom.zpow_apply, map_mul, Module.End.mul_apply, ha, hb,
    map_smul, hs, SpecialLinearGroup.coeToGL_det, GeneralLinearGroup.det_scalar, smul_smul]
  rw [← Units.val_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add, add_comm, one_zpow, Units.val_one,
    mul_one]

/-- **Two representations of `GL` restrict to equivalent representations of `SL` exactly when one
is a determinant twist of the other.** Let scalar matrices act on a nonzero `ρ` by `z ↦ z ^ a` and
on `σ` by `z ↦ z ^ b`, over an algebraically closed field whose characteristic does not divide
`|ι|`. Then the restrictions of `ρ` and `σ` to `SL ι K` are equivalent exactly when
`b = a + |ι| t` for an integer `t` such that the twist of `ρ` by `det ^ t` is equivalent to `σ`. -/
theorem nonempty_equiv_comp_toGL_iff [IsAlgClosed K] [NeZero (Fintype.card ι : K)] [Nontrivial V]
    {a b : ℤ}
    (ha : ∀ (z : Kˣ) (v : V), ρ (GeneralLinearGroup.scalar ι z) v = ((z ^ a : Kˣ) : K) • v)
    (hb : ∀ (z : Kˣ) (w : W), σ (GeneralLinearGroup.scalar ι z) w = ((z ^ b : Kˣ) : K) • w) :
    Nonempty (Equiv (ρ.comp SpecialLinearGroup.toGL) (σ.comp SpecialLinearGroup.toGL)) ↔
      ∃ t : ℤ, b = a + Fintype.card ι * t ∧
        Nonempty ((charTwist ((GeneralLinearGroup.det : GL ι K →* Kˣ) ^ t) ρ).Equiv σ) := by
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨t, _, ⟨e⟩⟩ => ?_⟩
  · have : NeZero (Fintype.card ι) := .of_neZero_natCast K
    have he : IsIntertwiningMap (ρ.comp SpecialLinearGroup.toGL) (σ.comp SpecialLinearGroup.toGL)
        e.toLinearMap := ⟨IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap⟩
    have he0 : e.toLinearMap ≠ 0 := fun h => by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (e.injective (by simpa using LinearMap.congr_fun h v))
    obtain ⟨t, ht⟩ := dvd_sub_of_isIntertwiningMap_comp_toGL ha hb he he0
    have hbt : b = a + Fintype.card ι * t := by omega
    subst hbt
    exact ⟨t, rfl, ⟨Equiv.mk e.toLinearEquiv fun g => LinearMap.ext
      ((isIntertwiningMap_charTwist_det_zpow_of_comp_toGL ha hb he).isIntertwining g)⟩⟩
  · rw [← charTwist_det_zpow_comp_toGL ρ t]
    exact ⟨Equiv.mk e.toLinearEquiv fun s => LinearMap.ext fun v =>
      IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (SpecialLinearGroup.toGL s) v⟩

end Twist

end Representation
