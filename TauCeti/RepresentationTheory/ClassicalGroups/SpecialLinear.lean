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
# Restriction from `GL` to `SL`, and extension back

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

Conversely, a representation `ρ` of `SL` extends to `GL` as soon as the determinant-one scalar
matrices act on it by a power character `z ↦ z ^ a`: the operator `z ^ a • ρ s` on
`toGL s * scalar z` does not depend on the factorization, because two factorizations differ by a
determinant-one scalar matrix (`Representation.extendToGL`). Every finite-dimensional irreducible
`ρ` has such a character when the characteristic does not divide `|ι|`, by Schur's lemma applied to
the scalar matrix of a primitive `|ι|`-th root of unity
(`Representation.IsIrreducible.exists_forall_apply_eq_zpow_smul`).

## Main definitions

* `Representation.extendToGL`: the extension to `GL` of a representation of `SL` on which the
  determinant-one scalar matrices act by `z ↦ z ^ a`, with every scalar matrix acting by `z ^ a`.

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
* `Representation.extendToGL_comp_toGL` and `Representation.extendToGL_scalar`: the extension
  restricts to the original representation, and scalar matrices act on it by `z ↦ z ^ a`.
* `Representation.isIrreducible_extendToGL_iff`: the extension is irreducible exactly when the
  original representation is.
* `Representation.IsIrreducible.exists_forall_apply_eq_zpow_smul`: on an irreducible
  representation of `SL`, the determinant-one scalar matrices act by a power character.

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

section Extension

open Matrix

variable {ι K V : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommMonoid V] [Module K V]

/-- If the determinant-one scalar matrices act on `ρ` by `z ↦ z ^ a`, two factorizations of the
same invertible matrix as a determinant-one matrix times a scalar matrix give the same operator
`z ^ a • ρ s`. -/
private theorem zpow_smul_eq_of_toGL_mul_scalar_eq {ρ : Representation K (SpecialLinearGroup ι K) V}
    {a : ℤ} (ha : ∀ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar ι z →
        ∀ v, ρ s v = ((z ^ a : Kˣ) : K) • v)
    {s s' : SpecialLinearGroup ι K} {z z' : Kˣ}
    (h : SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar ι z =
      SpecialLinearGroup.toGL s' * GeneralLinearGroup.scalar ι z') :
    ((z ^ a : Kˣ) : K) • ρ s = ((z' ^ a : Kˣ) : K) • ρ s' := by
  have hu : SpecialLinearGroup.toGL (s'⁻¹ * s) = GeneralLinearGroup.scalar ι (z' * z⁻¹) := by
    rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc,
      eq_mul_inv_iff_mul_eq, h]
  have hs : s = s' * (s'⁻¹ * s) := by group
  ext v
  conv_lhs => rw [hs, map_mul]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, ha _ _ hu, map_smul, smul_smul]
  rw [← Units.val_mul, ← mul_zpow, mul_comm z, inv_mul_cancel_right]

variable [IsAlgClosed K] (ρ : Representation K (SpecialLinearGroup ι K) V) (a : ℤ)
  (ha : ∀ (s : SpecialLinearGroup ι K) (z : Kˣ),
    SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar ι z →
      ∀ v, ρ s v = ((z ^ a : Kˣ) : K) • v)

/-- The operator `z ^ a • ρ s` attached to the chosen factorization `g = toGL s * scalar z`. This
is an implementation detail of `Representation.extendToGL`, whose interface is
`Representation.extendToGL_toGL_mul_scalar`. -/
private noncomputable def extendToGLFun (g : GL ι K) : Module.End K V :=
  ((g.exists_toGL_mul_scalar_eq.choose_spec.choose ^ a : Kˣ) : K) •
    ρ g.exists_toGL_mul_scalar_eq.choose

variable {ρ a}

include ha in
private theorem extendToGLFun_eq {g : GL ι K} {s : SpecialLinearGroup ι K} {z : Kˣ}
    (h : SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar ι z = g) :
    extendToGLFun ρ a g = ((z ^ a : Kˣ) : K) • ρ s :=
  zpow_smul_eq_of_toGL_mul_scalar_eq ha
    (g.exists_toGL_mul_scalar_eq.choose_spec.choose_spec.trans h.symm)

variable (ρ a)

/-- **The extension of a representation of `SL` to `GL`.** Over an algebraically closed field,
every invertible matrix factors as `toGL s * scalar z` with `s` of determinant one
(`Matrix.GeneralLinearGroup.exists_toGL_mul_scalar_eq`). If the determinant-one scalar matrices
act on `ρ` by `z ↦ z ^ a`, then `toGL s * scalar z ↦ z ^ a • ρ s` does not depend on the
factorization, and it is a representation of `GL ι K` restricting to `ρ`
(`Representation.extendToGL_comp_toGL`) on which every scalar matrix `z` acts by `z ^ a`
(`Representation.extendToGL_scalar`). -/
noncomputable def extendToGL : Representation K (GL ι K) V where
  toFun := extendToGLFun ρ a
  map_one' := by
    rw [extendToGLFun_eq ha (s := 1) (z := 1) (by rw [map_one, map_one, one_mul]), one_zpow,
      Units.val_one, one_smul, map_one]
  map_mul' g h := by
    obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
    obtain ⟨t, w, rfl⟩ := h.exists_toGL_mul_scalar_eq
    rw [extendToGLFun_eq ha rfl, extendToGLFun_eq ha rfl,
      extendToGLFun_eq ha (s := s * t) (z := z * w) (by
        rw [map_mul, map_mul, mul_assoc, ← mul_assoc (SpecialLinearGroup.toGL t),
          ← GeneralLinearGroup.scalar_commute z (SpecialLinearGroup.toGL t)]
        simp only [mul_assoc]),
      map_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm, mul_smul]

/-- On a factorization `toGL s * scalar z`, the extension acts by `z ^ a • ρ s`. -/
theorem extendToGL_toGL_mul_scalar (s : SpecialLinearGroup ι K) (z : Kˣ) :
    extendToGL ρ a ha (SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar ι z) =
      ((z ^ a : Kˣ) : K) • ρ s :=
  extendToGLFun_eq ha rfl

/-- **The extension restricts to the original representation** on `SL ι K`. -/
@[simp]
theorem extendToGL_comp_toGL : (extendToGL ρ a ha).comp SpecialLinearGroup.toGL = ρ := by
  ext s v
  have h := extendToGL_toGL_mul_scalar ρ a ha s 1
  rw [map_one, mul_one] at h
  simp [h]

/-- The extension acts on a determinant-one matrix by the original representation. -/
@[simp]
theorem extendToGL_toGL (s : SpecialLinearGroup ι K) :
    extendToGL ρ a ha (SpecialLinearGroup.toGL s) = ρ s :=
  congrArg (· s) (extendToGL_comp_toGL ρ a ha)

/-- **A scalar matrix `z` acts on the extension by `z ^ a`.** -/
@[simp]
theorem extendToGL_scalar (z : Kˣ) (v : V) :
    extendToGL ρ a ha (GeneralLinearGroup.scalar ι z) v = ((z ^ a : Kˣ) : K) • v := by
  have h := extendToGL_toGL_mul_scalar ρ a ha 1 z
  rw [map_one, one_mul] at h
  simp [h]

end Extension

section ExtensionIrreducible

open Matrix

variable {ι K V : Type*} [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V]

/-- The extension is irreducible exactly when the original representation of `SL ι K` is: both
have the same invariant subspaces, since every scalar matrix acts on the extension by a scalar. -/
@[simp]
theorem isIrreducible_extendToGL_iff (ρ : Representation K (SpecialLinearGroup ι K) V) (a : ℤ)
    (ha : ∀ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar ι z →
        ∀ v, ρ s v = ((z ^ a : Kˣ) : K) • v) :
    (extendToGL ρ a ha).IsIrreducible ↔ ρ.IsIrreducible := by
  let e : Subrepresentation (extendToGL ρ a ha) ≃o Subrepresentation ρ :=
    { toFun S := ⟨S.toSubmodule, fun s v hv => by
        simpa using S.apply_mem_toSubmodule (SpecialLinearGroup.toGL s) hv⟩
      invFun S := ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
        rw [extendToGL_toGL_mul_scalar, LinearMap.smul_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule s hv)⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff

/-- **The determinant-one scalar matrices act on an irreducible representation of `SL` by a power
character.** Let `ρ` be a finite-dimensional irreducible representation of `SL ι K` over an
algebraically closed field whose characteristic does not divide `|ι|`. The scalar matrices of
determinant one are the `|ι|`-th roots of unity `z`, and they act by `z ↦ z ^ a` for some `a`. This
is the hypothesis of `Representation.extendToGL`. -/
theorem IsIrreducible.exists_forall_apply_eq_zpow_smul [FiniteDimensional K V]
    [NeZero (Fintype.card ι : K)] (ρ : Representation K (SpecialLinearGroup ι K) V)
    [ρ.IsIrreducible] :
    ∃ a : ℤ, ∀ (s : SpecialLinearGroup ι K) (z : Kˣ),
      SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar ι z →
        ∀ v, ρ s v = ((z ^ a : Kˣ) : K) • v := by
  have : NeZero (Fintype.card ι) := .of_neZero_natCast K
  have := IsIrreducible.nontrivial (ρ := ρ) inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (Fintype.card ι)
  let u : Kˣ := (hζ.isUnit (NeZero.ne _)).unit
  have hu : IsPrimitiveRoot u (Fintype.card ι) := IsPrimitiveRoot.coe_units_iff.mp hζ
  -- The scalar matrix `u` has determinant `u ^ |ι| = 1`, so it lies in `SL ι K`.
  let s₀ : SpecialLinearGroup ι K :=
    ⟨GeneralLinearGroup.scalar ι u, by
      rw [← GeneralLinearGroup.val_det_apply, GeneralLinearGroup.det_scalar, hu.pow_eq_one,
        Units.val_one]⟩
  have hs₀ : SpecialLinearGroup.toGL s₀ = GeneralLinearGroup.scalar ι u := Units.ext rfl
  -- It is central, so it acts by a scalar `c`, which is an `|ι|`-th root of unity.
  obtain ⟨c, hc⟩ := IsIrreducible.exists_forall_apply_eq_smul (ρ s₀) fun g v => by
    have hcomm : s₀ * g = g * s₀ := SpecialLinearGroup.toGL_injective <| by
      rw [map_mul, map_mul, hs₀, GeneralLinearGroup.scalar_commute]
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  have hpow : ∀ (j : ℕ) (v : V), ρ (s₀ ^ j) v = c ^ j • v := fun j => by
    induction j with
    | zero => simp
    | succ j ih => intro v; rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih,
        smul_smul, pow_succ, mul_comm]
  have hcN : c ^ Fintype.card ι = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : s₀ ^ Fintype.card ι = 1 := SpecialLinearGroup.toGL_injective <| by
      rw [map_pow, hs₀, ← map_pow, hu.pow_eq_one, map_one, map_one]
    have h := hpow (Fintype.card ι) v
    rw [h1, map_one, Module.End.one_apply] at h
    exact (smul_left_injective K hv (h.symm.trans (one_smul K v).symm) :)
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hcN
  refine ⟨a, fun s z hs v => ?_⟩
  -- Every determinant-one scalar matrix is a power of the scalar matrix of `u`.
  have hzN : z ^ Fintype.card ι = 1 := by
    have h := congrArg GeneralLinearGroup.det hs
    rwa [SpecialLinearGroup.coeToGL_det, GeneralLinearGroup.det_scalar, eq_comm] at h
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, hzN,
    Units.val_one])
  obtain rfl : u ^ j = z := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hj)
  have hsj : s = s₀ ^ j := SpecialLinearGroup.toGL_injective <| by
    rw [hs, map_pow, map_pow, hs₀]
  rw [hsj, hpow, ← ha, zpow_natCast, Units.val_pow_eq_pow_val, ← hj, ← pow_mul, ← pow_mul,
    mul_comm]

end ExtensionIrreducible

end Representation
