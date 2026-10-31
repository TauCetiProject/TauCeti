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
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.RootsOfUnity.Basic

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

Conversely, a representation of `SL` extends to `GL` once its determinant-one scalar matrices act
through a power character `ζ ↦ ζ ^ a`: send `s * z`, for `s` of determinant one and `z` scalar, to
`z ^ a • ρ s`. Two such splittings of the same matrix differ by a determinant-one scalar matrix,
which is what makes this well defined, and the extension is unique among those on which `z` acts by
`z ^ a` (`Representation.existsUnique_comp_toGL_eq_and_apply_scalar`). On an irreducible
representation over an algebraically closed field whose characteristic does not divide `|ι|`, such
an `a` always exists, by Schur's lemma applied to a primitive root of unity
(`Representation.IsIrreducible.exists_forall_apply_eq_pow_smul_one`).

Over `ℂ` the extension preserves rationality. A representation of `SL n ℂ` is rational
(`TauCeti.IsRationalSLRep`) when its matrix entries in some basis are polynomials in the matrix
entries; no determinant denominator is needed, since `det = 1`. If `g = c • s` with `c ^ n = det g`,
the entries of `ρ g = c ^ a • ρ s` are `c ^ a` times polynomials in the entries of `c⁻¹ • g`. Since
the roots of unity act by `ζ ^ a`, only the homogeneous components of degree `k ≡ a` modulo `n`
contribute, and for those `c ^ a * c⁻¹ ^ k` is an integer power of `det g`
(`TauCeti.IsRationalRep.of_comp_toGL`).

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
* `Representation.IsIrreducible.exists_forall_apply_eq_pow_smul_one`: the determinant-one scalar
  matrices act on an irreducible representation of `SL` through a power of the scalar.
* `Representation.existsUnique_comp_toGL_eq_and_apply_scalar`: a representation of `SL` on which
  the determinant-one scalar matrices act through `ζ ↦ ζ ^ a` extends uniquely to `GL` with scalar
  matrices acting through `z ↦ z ^ a`.
* `TauCeti.IsRationalSLRep`: rational representations of `SL n ℂ`, with
  `TauCeti.IsRationalRep.comp_toGL` restricting rational representations of `GL n ℂ`, and
  `TauCeti.isRationalSLRep_iff_forall_exists_eval` checking rationality against any basis.
* `TauCeti.IsRationalRep.of_comp_toGL`: a representation of `GL n ℂ` with rational restriction to
  `SL n ℂ` and scalar matrices acting through `z ↦ z ^ a` is rational.

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
  [AddCommGroup V] [Module K V] {ρ : Representation K (SpecialLinearGroup ι K) V} {a : ℕ}

/-- Two splittings of an invertible matrix as a determinant-one matrix times a scalar matrix give
the same operator `z ^ a • ρ s`, when determinant-one scalar matrices `ζ` act by `ζ ^ a`. -/
private theorem pow_smul_apply_eq_of_toGL_mul_scalar_eq
    (H : ∀ (s : SpecialLinearGroup ι K) (ζ : K), (s : Matrix ι ι K) = scalar ι ζ →
      ρ s = ζ ^ a • 1)
    {s s' : SpecialLinearGroup ι K} {z z' : Kˣ}
    (h : SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar ι z =
      SpecialLinearGroup.toGL s' * GeneralLinearGroup.scalar ι z') :
    ((z : K) ^ a) • ρ s = ((z' : K) ^ a) • ρ s' := by
  have ht : ((s'⁻¹ * s : SpecialLinearGroup ι K) : Matrix ι ι K) =
      scalar ι ((z' : K) * (z⁻¹ : Kˣ)) := by
    have h' : SpecialLinearGroup.toGL (s'⁻¹ * s) =
        GeneralLinearGroup.scalar ι (z' * z⁻¹) := by
      simp only [map_mul, map_inv]
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h]
      group
    have := congrArg Units.val h'
    rwa [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar, Units.val_mul] at this
  have hs : ρ s = ((z' : K) * (z⁻¹ : Kˣ)) ^ a • ρ s' := by
    calc ρ s = ρ (s' * (s'⁻¹ * s)) := by rw [mul_inv_cancel_left]
      _ = ρ s' * ρ (s'⁻¹ * s) := map_mul ..
      _ = _ := by rw [H _ _ ht, mul_smul_comm, mul_one]
  rw [hs, smul_smul, ← mul_pow]
  congr 2
  simp [mul_left_comm (z : K)]

variable [IsAlgClosed K]

/-- **The determinant-one scalar matrices act on an irreducible representation of `SL` through a
power of the scalar.** Over an algebraically closed field whose characteristic does not divide
`|ι|`, the determinant-one scalar matrices are the `|ι|`-th roots of unity `ζ`, a cyclic group
generated by a primitive root `ζ₀`. By Schur's lemma the central element `ζ₀` acts by a scalar,
which is again an `|ι|`-th root of unity, hence a power `ζ₀ ^ a`; then every `ζ` acts by `ζ ^ a`. -/
theorem IsIrreducible.exists_forall_apply_eq_pow_smul_one [NeZero (Fintype.card ι : K)]
    [FiniteDimensional K V] [ρ.IsIrreducible] :
    ∃ a : ℕ, ∀ (s : SpecialLinearGroup ι K) (ζ : K), (s : Matrix ι ι K) = scalar ι ζ →
      ρ s = ζ ^ a • 1 := by
  have : NeZero (Fintype.card ι) := .of_neZero_natCast K
  have := IsIrreducible.nontrivial (ρ := ρ) inferInstance
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (Fintype.card ι)
  let z₀ : SpecialLinearGroup ι K := ⟨scalar ι ζ₀, by simp [hζ₀.pow_eq_one]⟩
  have hpow (j : ℕ) : ((z₀ ^ j : SpecialLinearGroup ι K) : Matrix ι ι K) = scalar ι (ζ₀ ^ j) := by
    rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_mk, map_pow]
  -- Schur's lemma: the central element `z₀` acts by a scalar `χ`.
  obtain ⟨χ, hχ⟩ := IsIrreducible.exists_forall_apply_eq_smul (ρ z₀) fun g v => by
    have hz : z₀ * g = g * z₀ := SpecialLinearGroup.ext _ _ fun i j => by
      rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mk,
        scalar_commute ζ₀ (Commute.all ζ₀)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hz]
  have hρz₀ : ρ z₀ = χ • 1 := LinearMap.ext hχ
  have hρpow (j : ℕ) : ρ (z₀ ^ j) = (χ ^ j) • 1 := by
    rw [map_pow, hρz₀, smul_pow, one_pow]
  -- The scalar `χ` is a root of unity, since `z₀ ^ |ι| = 1`.
  have hχn : χ ^ Fintype.card ι = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : z₀ ^ Fintype.card ι = 1 := SpecialLinearGroup.ext _ _ fun i j => by
      rw [hpow, hζ₀.pow_eq_one, map_one, SpecialLinearGroup.coe_one]
    refine smul_left_injective K hv ?_
    simpa [h1] using (LinearMap.congr_fun (hρpow (Fintype.card ι)) v).symm
  obtain ⟨a, -, ha⟩ := hζ₀.eq_pow_of_pow_eq_one hχn
  refine ⟨a, fun s ζ hs => ?_⟩
  have hζ : ζ ^ Fintype.card ι = 1 := by
    simpa [hs] using s.prop
  obtain ⟨j, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  have hsj : s = z₀ ^ j := SpecialLinearGroup.ext _ _ fun i k => by rw [hpow, hs]
  rw [hsj, hρpow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

variable (ρ a) in
/-- The operator `z ^ a • ρ s` for a chosen splitting `g = s * z` of an invertible matrix into a
determinant-one matrix and a scalar matrix. -/
private noncomputable def extendAux (g : GL ι K) : Module.End K V :=
  ((g.exists_toGL_mul_scalar_eq.choose_spec.choose : K) ^ a) •
    ρ g.exists_toGL_mul_scalar_eq.choose

private theorem extendAux_eq
    (H : ∀ (s : SpecialLinearGroup ι K) (ζ : K), (s : Matrix ι ι K) = scalar ι ζ →
      ρ s = ζ ^ a • 1)
    {g : GL ι K} {s : SpecialLinearGroup ι K} {z : Kˣ}
    (h : SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar ι z = g) :
    extendAux ρ a g = ((z : K) ^ a) • ρ s :=
  pow_smul_apply_eq_of_toGL_mul_scalar_eq H
    (g.exists_toGL_mul_scalar_eq.choose_spec.choose_spec.trans h.symm)

/-- **Extending a representation of `SL` to `GL`.** Over an algebraically closed field, a
representation `ρ` of the special linear group on which every determinant-one scalar matrix `ζ`
acts by `ζ ^ a` extends uniquely to a representation of the general linear group on which every
scalar matrix `z` acts by `z ^ a`. The extension sends `s * z`, for `s` of determinant one and `z`
scalar, to `z ^ a • ρ s`. -/
theorem existsUnique_comp_toGL_eq_and_apply_scalar
    (H : ∀ (s : SpecialLinearGroup ι K) (ζ : K), (s : Matrix ι ι K) = scalar ι ζ →
      ρ s = ζ ^ a • 1) :
    ∃! ρ' : Representation K (GL ι K) V, ρ'.comp SpecialLinearGroup.toGL = ρ ∧
      ∀ z : Kˣ, ρ' (GeneralLinearGroup.scalar ι z) = ((z : K) ^ a) • 1 := by
  let ρ' : Representation K (GL ι K) V :=
    { toFun := extendAux ρ a
      map_one' := by rw [extendAux_eq H (s := 1) (z := 1) (by simp), map_one]; simp
      map_mul' g h := by
        obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
        obtain ⟨t, w, rfl⟩ := h.exists_toGL_mul_scalar_eq
        have hst : SpecialLinearGroup.toGL (s * t) * GeneralLinearGroup.scalar ι (z * w) =
            SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar ι z *
              (SpecialLinearGroup.toGL t * GeneralLinearGroup.scalar ι w) := by
          rw [map_mul, map_mul]
          simp only [mul_assoc]
          rw [← mul_assoc (GeneralLinearGroup.scalar ι z),
            GeneralLinearGroup.scalar_commute z (SpecialLinearGroup.toGL t), mul_assoc]
        rw [extendAux_eq H hst, extendAux_eq H rfl, extendAux_eq H rfl, map_mul, Units.val_mul,
          mul_pow, smul_mul_smul_comm] }
  refine ⟨ρ', ⟨MonoidHom.ext fun s => ?_, fun z => ?_⟩, fun σ ⟨hσ, hσz⟩ => MonoidHom.ext
    fun g => ?_⟩
  · exact (extendAux_eq (ρ := ρ) (a := a) H (s := s) (z := 1) (mul_one _)).trans (by simp)
  · exact (extendAux_eq (ρ := ρ) (a := a) H (s := 1) (z := z) (by simp)).trans (by simp)
  · obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
    rw [map_mul, hσz, ← MonoidHom.comp_apply, hσ, mul_smul_comm, mul_one]
    exact (extendAux_eq H rfl).symm

end Extension

end Representation

open Matrix MvPolynomial TauCeti.Matrix.GeneralLinearGroup

namespace TauCeti

variable {n : ℕ} {W : Type*}

section Defs

variable [AddCommMonoid W] [Module ℂ W]

/-- **A rational representation** of `SL n ℂ`: in some basis of the carrier, every matrix entry
of `ρ s` is a polynomial in the entries of `s`. On the special linear group the determinant is `1`,
so allowing a power of the determinant in the denominator, as `TauCeti.IsRationalRep` does on
`GL n ℂ`, would change nothing: rational and polynomial representations of `SL n ℂ` coincide. The
carrier is forced to be finite-dimensional (`TauCeti.IsRationalSLRep.finite`). -/
def IsRationalSLRep (ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
    ∀ (s : SpecialLinearGroup (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ s) i j
        = MvPolynomial.eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsRationalSLRep`, as a lemma. -/
theorem isRationalSLRep_iff (ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W) :
    IsRationalSLRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
      ∀ (s : SpecialLinearGroup (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ s) i j
          = MvPolynomial.eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

/-- The carrier of a rational representation of `SL n ℂ` is finite-dimensional. -/
theorem IsRationalSLRep.finite {ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W}
    (h : IsRationalSLRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

/-- **Rationality on `SL n ℂ` is basis independent.** A representation of `SL n ℂ` is rational
exactly when, against *any* chosen basis, each matrix entry is a polynomial function of the entries
of `s`. -/
theorem isRationalSLRep_iff_forall_exists_eval
    {ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W) :
    IsRationalSLRep ρ ↔ ∀ i j, ∃ P : MvPolynomial (Fin n × Fin n) ℂ,
      ∀ s : SpecialLinearGroup (Fin n) ℂ,
        LinearMap.toMatrix b b (ρ s) i j =
          eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P := by
  let x (p : Fin n × Fin n) (s : SpecialLinearGroup (Fin n) ℂ) : ℂ :=
    (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2
  -- The polynomial functions on `SL n ℂ`, as a subalgebra of all functions.
  let A : Subalgebra ℂ (SpecialLinearGroup (Fin n) ℂ → ℂ) := (aeval x).range
  have hA {f : SpecialLinearGroup (Fin n) ℂ → ℂ} : f ∈ A ↔ ∃ P : MvPolynomial (Fin n × Fin n) ℂ,
      ∀ s, f s = eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P := by
    have heval (P : MvPolynomial (Fin n × Fin n) ℂ) (s : SpecialLinearGroup (Fin n) ℂ) :
        aeval x P s = eval (fun p => x p s) P := by
      simpa [aeval_eq_eval] using comp_aeval_apply x (Pi.evalAlgHom ℂ (fun _ => ℂ) s) P
    refine ⟨fun ⟨P, hP⟩ => ⟨P, fun s => hP ▸ heval P s⟩, fun ⟨P, hP⟩ => ⟨P, funext fun s => ?_⟩⟩
    exact (heval P s).trans (hP s).symm
  constructor
  · rintro ⟨b₀, P, hP⟩ i j
    exact hA.mp (Representation.toMatrix_mem_of_toMatrix_mem A b₀ b ρ
      (fun p l => hA.mpr ⟨P p l, fun s => hP s p l⟩) i j)
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) :=
      Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
    choose P hP using fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) =>
      hA.mp (Representation.toMatrix_mem_of_toMatrix_mem A b (b.reindex e) ρ
        (fun i j => hA.mpr (h i j)) q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), fun s i j => hP (i, j) s⟩

/-- **The restriction of a rational representation of `GL n ℂ` to `SL n ℂ` is rational**: the
determinant in the denominator of each matrix entry is `1` on `SL n ℂ`. -/
theorem IsRationalRep.comp_toGL {ρ : Representation ℂ (GL (Fin n) ℂ) W} (h : IsRationalRep ρ) :
    IsRationalSLRep (ρ.comp SpecialLinearGroup.toGL) := by
  obtain ⟨b, P, m, hP⟩ := (isRationalRep_iff ρ).mp h
  refine ⟨b, P, fun s i j => ?_⟩
  simpa using hP (SpecialLinearGroup.toGL s) i j

end Defs

section Extension

variable [AddCommGroup W] [Module ℂ W]

/-- On `SL n ℂ`, a matrix coefficient of a representation of `GL n ℂ` on which the scalar
matrices act through `z ↦ z ^ a`, given by a polynomial `P` in the matrix entries, only involves
the homogeneous components of `P` of degree `k` with `n ∣ k + (n - 1) * a`, that is `k ≡ a`
modulo `n`. Scaling by a primitive `n`-th root of unity `ζ` multiplies the coefficient by `ζ ^ a`
and the degree `k` component by `ζ ^ k`; averaging over the powers of `ζ` keeps only the
components with `ζ ^ k = ζ ^ a`. -/
private theorem eval_eq_sum_homogeneousComponent_of_apply_scalar [NeZero n]
    {ρ : Representation ℂ (GL (Fin n) ℂ) W} {a : ℕ}
    (ha : ∀ z : ℂˣ, ρ (GeneralLinearGroup.scalar (Fin n) z) = ((z : ℂ) ^ a) • 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W) {i j : ι}
    {P : MvPolynomial (Fin n × Fin n) ℂ}
    (hP : ∀ s : SpecialLinearGroup (Fin n) ℂ,
      LinearMap.toMatrix b b (ρ (SpecialLinearGroup.toGL s)) i j =
        eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P)
    (s : SpecialLinearGroup (Fin n) ℂ) :
    eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P =
      ∑ k ∈ (Finset.range (P.totalDegree + 1)).filter (fun k => n ∣ k + (n - 1) * a),
        eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (homogeneousComponent k P) := by
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  set x := fun p : Fin n × Fin n => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2
  have hpow (m : ℕ) : (ζ ^ m) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- The determinant-one scalar matrix `ζ ^ m` multiplies the coefficient by `(ζ ^ m) ^ a`.
  have hscal (m : ℕ) : eval ((ζ ^ m) • x) P = (ζ ^ m) ^ a * eval x P := by
    have hm0 : ζ ^ m ≠ 0 := pow_ne_zero _ hζ0
    let t : SpecialLinearGroup (Fin n) ℂ := ⟨scalar (Fin n) (ζ ^ m), by simp [hpow]⟩
    have ht : SpecialLinearGroup.toGL t =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 (ζ ^ m) hm0) :=
      Units.ext (by
        rw [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar, Units.val_mk0])
    have hts : (fun p : Fin n × Fin n =>
        ((t * s : SpecialLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) =
          (ζ ^ m) • x := by
      funext p
      rw [SpecialLinearGroup.coe_mul]
      simp [t, x, scalar_apply]
    rw [← hts, ← hP (t * s), ← hP s, map_mul, map_mul, ht, ha]
    simp
  have hsum (y : Fin n × Fin n → ℂ) : eval y P =
      ∑ k ∈ Finset.range (P.totalDegree + 1), eval y (homogeneousComponent k P) := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [map_sum]
  -- Average the transformation law over the powers of `ζ`, using `ζ ^ ((n - 1) * a) = ζ⁻¹ ^ a`.
  have hexp : (n - 1) * a + a = n * a := by rw [← add_one_mul, Nat.sub_add_cancel NeZero.one_le]
  have hterm (m : ℕ) : (ζ ^ m) ^ ((n - 1) * a) * eval ((ζ ^ m) • x) P = eval x P := by
    rw [hscal, ← mul_assoc, ← pow_add, hexp, pow_mul, hpow]
    simp
  have hmean : ∑ m : Fin n, (ζ ^ (m : ℕ)) ^ ((n - 1) * a) * eval ((ζ ^ (m : ℕ)) • x) P =
      n * eval x P := by
    simp [hterm]
  have hexpand (m : ℕ) : (ζ ^ m) ^ ((n - 1) * a) * eval ((ζ ^ m) • x) P =
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        (ζ ^ (k + (n - 1) * a)) ^ m * eval x (homogeneousComponent k P) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(homogeneousComponent_isHomogeneous k P).eval_smul, smul_eq_mul]
    ring
  refine mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)) ?_
  rw [← hmean, Finset.sum_congr rfl fun (m : Fin n) _ => hexpand m, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hζ.sum_pow_pow_eq, Finset.sum_filter, Finset.mul_sum, ite_mul,
    zero_mul, mul_ite, mul_zero]

/-- On `GL n ℂ`, a matrix coefficient of a representation on which the scalar matrices act through
`z ↦ z ^ a`, and whose restriction to `SL n ℂ` is given by a polynomial `P` in the matrix entries,
is a sum of integer powers of `det g` times homogeneous components of `P`. Write `g = c • s` with
`c ^ n = det g` and `s` of determinant one; then `ρ g = c ^ a • ρ s`, only the components of degree
`k ≡ a` modulo `n` contribute, and for those `c ^ a * c⁻¹ ^ k = det g ^ ((a - k) / n)`. -/
private theorem toMatrix_apply_eq_sum_det_zpow_mul_eval [NeZero n]
    {ρ : Representation ℂ (GL (Fin n) ℂ) W} {a : ℕ}
    (ha : ∀ z : ℂˣ, ρ (GeneralLinearGroup.scalar (Fin n) z) = ((z : ℂ) ^ a) • 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W) {i j : ι}
    {P : MvPolynomial (Fin n × Fin n) ℂ}
    (hP : ∀ s : SpecialLinearGroup (Fin n) ℂ,
      LinearMap.toMatrix b b (ρ (SpecialLinearGroup.toGL s)) i j =
        eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P)
    (g : GL (Fin n) ℂ) :
    LinearMap.toMatrix b b (ρ g) i j =
      ∑ k ∈ (Finset.range (P.totalDegree + 1)).filter (fun k => n ∣ k + (n - 1) * a),
        ((Matrix.GeneralLinearGroup.det g ^ (((a : ℤ) - k) / n) : ℂˣ) : ℂ) *
          eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (homogeneousComponent k P) := by
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((g : Matrix (Fin n) (Fin n) ℂ).det)
    (Nat.pos_of_ne_zero hn)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact Matrix.GeneralLinearGroup.det_ne_zero g (by rw [← hc, zero_pow hn])
  let s : SpecialLinearGroup (Fin n) ℂ := ⟨c⁻¹ • (g : Matrix (Fin n) (Fin n) ℂ), by
    rw [Matrix.det_smul, Fintype.card_fin, ← hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hc0)]⟩
  have hg : SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) = g :=
    Units.ext <| by
      simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
      ext
      simp [s, scalar_apply, mul_right_comm _ _ c, hc0]
  have hρg : ρ g = (c ^ a) • ρ (SpecialLinearGroup.toGL s) := by
    rw [← hg, map_mul, ha, mul_smul_comm, mul_one, Units.val_mk0]
  rw [hρg, map_smul, Matrix.smul_apply, smul_eq_mul, hP,
    eval_eq_sum_homogeneousComponent_of_apply_scalar ha b hP s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hdvd : (n : ℤ) ∣ (a : ℤ) - k := by
    have hsub : (a : ℤ) - k = n * a - ((k + (n - 1) * a : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub NeZero.one_le]
      ring
    rw [hsub]
    exact dvd_sub (dvd_mul_right _ _) (Int.natCast_dvd_natCast.mpr (Finset.mem_filter.mp hk).2)
  have hentries : (fun p : Fin n × Fin n => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) =
      c⁻¹ • fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 := by
    funext p
    rw [Pi.smul_apply, SpecialLinearGroup.coe_mk, Matrix.smul_apply]
  have hpow :
      c ^ a * c⁻¹ ^ k = ((Matrix.GeneralLinearGroup.det g ^ (((a : ℤ) - k) / n) : ℂˣ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← hc,
      ← zpow_natCast c n, ← zpow_mul, Int.mul_ediv_cancel' hdvd, zpow_sub₀ hc0]
    simp [div_eq_mul_inv]
  rw [hentries, (homogeneousComponent_isHomogeneous k P).eval_smul, smul_eq_mul, ← mul_assoc, hpow]

/-- **A representation of `GL n ℂ` is rational once its restriction to `SL n ℂ` is rational and
the scalar matrices act through a power `z ↦ z ^ a` of the scalar.** Writing `g = c • s` with
`c ^ n = det g` and `s` of determinant one, the matrix entries of `ρ g = c ^ a • ρ s` are
polynomials in the entries of `c⁻¹ • g`, times `c ^ a`. Only the homogeneous components of
degree `k ≡ a` modulo `n` contribute, because the determinant-one scalar matrices act by `ζ ^ a`,
and for those `c ^ a * c⁻¹ ^ k` is an integer power of `c ^ n = det g`. -/
theorem IsRationalRep.of_comp_toGL {ρ : Representation ℂ (GL (Fin n) ℂ) W}
    (h : IsRationalSLRep (ρ.comp SpecialLinearGroup.toGL)) {a : ℕ}
    (ha : ∀ z : ℂˣ, ρ (GeneralLinearGroup.scalar (Fin n) z) = ((z : ℂ) ^ a) • 1) :
    IsRationalRep ρ := by
  obtain ⟨b, P, hP⟩ := h
  refine (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `GL (Fin 0) ℂ` is trivial, so every matrix entry is constant.
    have hconst : (fun g : GL (Fin 0) ℂ => LinearMap.toMatrix b b (ρ g) i j) =
        algebraMap ℂ (GL (Fin 0) ℂ → ℂ) ((1 : Matrix (Fin (Module.finrank ℂ W))
          (Fin (Module.finrank ℂ W)) ℂ) i j) := by
      funext g
      rw [Subsingleton.elim g 1, map_one, LinearMap.toMatrix_one, Pi.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [hconst]
    exact Subalgebra.algebraMap_mem _ _
  have : NeZero n := ⟨hn.ne'⟩
  have hfun : (fun g : GL (Fin n) ℂ => LinearMap.toMatrix b b (ρ g) i j) =
      ∑ k ∈ (Finset.range ((P i j).totalDegree + 1)).filter (fun k => n ∣ k + (n - 1) * a),
        (fun g : GL (Fin n) ℂ =>
          ((Matrix.GeneralLinearGroup.det g ^ (((a : ℤ) - k) / n) : ℂˣ) : ℂ)) *
          fun g : GL (Fin n) ℂ => eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)
            (homogeneousComponent k (P i j)) := by
    funext g
    rw [toMatrix_apply_eq_sum_det_zpow_mul_eval ha b (fun s => hP s i j) g, Finset.sum_apply]
    rfl
  rw [hfun]
  refine Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (det_zpow_mem_rationalFunctions _)
    (polynomialFunctions_le_rationalFunctions (mem_polynomialFunctions.mpr ⟨_, fun _ => rfl⟩))

end Extension

end TauCeti
