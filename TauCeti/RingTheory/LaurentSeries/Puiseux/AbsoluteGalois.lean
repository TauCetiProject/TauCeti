/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.RingTheory.LaurentSeries.Puiseux.FiniteExtension
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Uniformizer

/-!
# The absolute Galois group of `K⸨X⸩` on any model of the Puiseux field

`TauCeti.puiseuxField.galEquivTateModule` identifies the Galois group of the Puiseux field over
`K⸨X⸩` with the Tate module `lim_n μₙ(K)`, when `K` contains a primitive `n`-th root of unity for
every `n > 0`. This file transports that identification to any field `L` isomorphic to the Puiseux
field over `K⸨X⸩`, such as Mathlib's chosen algebraic closure `AlgebraicClosure K⸨X⸩` when `K` is
algebraically closed of characteristic zero.

The transport along `e : puiseuxField K ≃ₐ[K⸨X⸩] L` conjugates `σ ∈ Gal(L/K⸨X⸩)` to
`e⁻¹ ∘ σ ∘ e`. It does not depend on `e`: two choices differ by an automorphism `τ` of the Puiseux
field, so the two conjugates of `σ` differ by conjugation by `τ`, and conjugation becomes trivial
in the commutative group `lim_n μₙ(K)`. On the image `e(level n)` of the level
`K⸨t ^ (1 / n)⸩`, which is the only intermediate field of `L` of degree `n` over `K⸨X⸩`,
`σ` acts by the Kummer automorphism of the level-`n` component of its image. So the subgroup
fixing an intermediate field of degree `n` is the kernel of the level-`n` projection.

On `L = AlgebraicClosure K⸨X⸩` the level-`n` component of the image of `σ` is the character
`θₙ (σ) = σ (α) / α`, for any `n`-th root `α` of any uniformizer of `K⸨X⸩`. A compatible family
`ζ = (ζₙ)ₙ` of primitive roots of unity identifies `lim_n μₙ(K)` with `ℤ̂`, so the absolute Galois
group of `K⸨X⸩` is `ℤ̂`. The automorphism with coordinate `a ∈ ℤ̂` multiplies every such `α` by
`ζₙ ^ (a mod n)`, and the canonical generator of `ℤ̂` corresponds to the unique automorphism
`σ_ζ` multiplying every `n`-th root of `t` by `ζₙ`. Replacing `ζ` by another compatible family
`ζ' = ζ ^ u`, for a unit `u` of the ring `ℤ̂`, divides every coordinate by `u`.

`Field.absoluteGaloisGroup K⸨X⸩` is a definition with no coercion to functions, so the statements
about the action on elements of the algebraic closure take `σ` in the underlying type
`Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩)`.

## Main definitions

* `TauCeti.puiseuxField.galEquivTateModuleOfAlgEquiv e`: for `e : puiseuxField K ≃ₐ[K⸨X⸩] L`, the
  isomorphism of topological groups `Gal(L/K⸨X⸩) ≃ₜ* lim_n μₙ(K)`.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivTateModule K`: for `K` algebraically closed of
  characteristic zero, the isomorphism of topological groups between the absolute Galois group
  `Field.absoluteGaloisGroup K⸨X⸩` and `lim_n μₙ(K)`.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivZHat K ζ hζ`: for a compatible family `ζ` of
  primitive roots of unity, the isomorphism of topological groups
  `Field.absoluteGaloisGroup K⸨X⸩ ≃ₜ* ℤ̂`.

## Main results

* `TauCeti.puiseuxField.galEquivTateModuleOfAlgEquiv_eq`: the isomorphism does not depend on `e`.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivTateModule_apply`: the absolute isomorphism is
  the transport along every `K⸨X⸩`-algebra isomorphism of the Puiseux field with
  `AlgebraicClosure K⸨X⸩`, not only the chosen one.
* `TauCeti.puiseuxField.eq_map_level_of_finrank_eq`: an intermediate field of `L` of degree `n`
  over `K⸨X⸩` is the image of level `n`.
* `TauCeti.puiseuxField.apply_algEquiv_coe_level`: on the image of level `n`, `σ` acts by the
  Kummer automorphism of the level-`n` component of its image.
* `TauCeti.puiseuxField.mem_fixingSubgroup_iff_of_finrank_eq`: the finite-level stabilizers. An
  automorphism of `L` fixes an intermediate field of degree `n` exactly when the level-`n`
  component of its image is trivial.
* `TauCeti.puiseuxField.proj_absoluteGaloisGroupEquivTateModule_eq_iff`: on the algebraic
  closure, the level-`n` component of the image of `σ` is the root of unity by which `σ` multiplies
  an `n`-th root of a uniformizer, whichever uniformizer and root are chosen.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivZHat_apply`: the isomorphism with `ℤ̂` is the
  transport of `TauCeti.puiseuxField.galEquivZHat` along every isomorphism of the Puiseux field
  with `AlgebraicClosure K⸨X⸩`.
* `TauCeti.puiseuxField.apply_eq_algebraMap_pow_toZMod_absoluteGaloisGroupEquivZHat_mul`: the
  automorphism with coordinate `a` multiplies every `n`-th root of a uniformizer by
  `ζₙ ^ (a mod n)`.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivZHat_eq_gen_iff`: an automorphism has coordinate
  the canonical generator of `ℤ̂` exactly when it multiplies every `n`-th root of a fixed
  uniformizer by `ζₙ`.
* `TauCeti.puiseuxField.mem_fixingSubgroup_iff_toZMod_eq_zero_of_finrank_eq`: an automorphism
  fixes an intermediate field of degree `n` exactly when its coordinate lies in `n ℤ̂`.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivZHat_apply_eq_zpowHat`: changing the compatible
  family of primitive roots of unity divides the coordinates by a unit of `ℤ̂`.
-/

public section

open IntermediateField Module
open scoped LaurentSeries

namespace TauCeti.puiseuxField

open PrimeToPTateModule

variable {K : Type*} [Field K] [∀ n : ℕ+, HasEnoughRootsOfUnity K n]
  {L : Type*} [Field L] [Algebra K⸨X⸩ L]

/-- **The Galois group of a model of the Puiseux field.** If `K` contains a primitive `n`-th root
of unity for every `n > 0`, an isomorphism `e : puiseuxField K ≃ₐ[K⸨X⸩] L` identifies
`Gal(L/K⸨X⸩)` with the Tate module `lim_n μₙ(K)` as topological groups, by transporting
`galEquivTateModule` along the conjugation `σ ↦ e⁻¹ ∘ σ ∘ e`. It does not depend on `e`
(`TauCeti.puiseuxField.galEquivTateModuleOfAlgEquiv_eq`). -/
noncomputable def galEquivTateModuleOfAlgEquiv (e : puiseuxField K ≃ₐ[K⸨X⸩] L) :
    Gal(L/K⸨X⸩) ≃ₜ* PrimeToPTateModule 1 K :=
  ({ e.symm.autCongr with
      continuous_toFun := e.symm.continuous_autCongr
      continuous_invFun := e.continuous_autCongr } :
      Gal(L/K⸨X⸩) ≃ₜ* Gal(puiseuxField K/K⸨X⸩)).trans (galEquivTateModule K)

/-- The image of `σ` is the image under `galEquivTateModule` of its conjugate `e⁻¹ ∘ σ ∘ e`. -/
@[simp]
theorem galEquivTateModuleOfAlgEquiv_apply (e : puiseuxField K ≃ₐ[K⸨X⸩] L)
    (σ : Gal(L/K⸨X⸩)) :
    galEquivTateModuleOfAlgEquiv e σ = galEquivTateModule K (e.symm.autCongr σ) :=
  (rfl)

/-- The inverse of `galEquivTateModuleOfAlgEquiv e` is the Kummer action conjugated by `e`. -/
@[simp]
theorem galEquivTateModuleOfAlgEquiv_symm_apply (e : puiseuxField K ≃ₐ[K⸨X⸩] L)
    (ζ : PrimeToPTateModule 1 K) :
    (galEquivTateModuleOfAlgEquiv e).symm ζ = e.autCongr (kummer K ζ) := by
  rw [ContinuousMulEquiv.symm_apply_eq, galEquivTateModuleOfAlgEquiv_apply,
    ← AlgEquiv.autCongr_symm, MulEquiv.symm_apply_apply, galEquivTateModule_kummer]

/-- Along the identity, `galEquivTateModuleOfAlgEquiv` is `galEquivTateModule`. -/
@[simp]
theorem galEquivTateModuleOfAlgEquiv_refl :
    galEquivTateModuleOfAlgEquiv (AlgEquiv.refl : puiseuxField K ≃ₐ[K⸨X⸩] puiseuxField K) =
      galEquivTateModule K :=
  (rfl)

/-- **Independence of the model.** The identification `Gal(L/K⸨X⸩) ≃ₜ* lim_n μₙ(K)` does not
depend on the isomorphism `e : puiseuxField K ≃ₐ[K⸨X⸩] L` it is transported along. -/
theorem galEquivTateModuleOfAlgEquiv_eq (e₁ e₂ : puiseuxField K ≃ₐ[K⸨X⸩] L) :
    galEquivTateModuleOfAlgEquiv e₁ = galEquivTateModuleOfAlgEquiv e₂ := by
  ext σ : 1
  -- The two conjugates of `σ` differ by conjugation by `τ = e₂⁻¹ ∘ e₁`, which the commutative
  -- Tate module does not see.
  let τ : Gal(puiseuxField K/K⸨X⸩) := e₁.trans e₂.symm
  have h : e₁.symm.autCongr σ = τ⁻¹ * e₂.symm.autCongr σ * τ := by
    ext x
    simp [τ, AlgEquiv.aut_inv]
  rw [galEquivTateModuleOfAlgEquiv_apply, galEquivTateModuleOfAlgEquiv_apply, h, map_mul, map_mul,
    map_inv, mul_comm, mul_inv_cancel_left]

/-- An intermediate field of `L` of degree `n` over `K⸨X⸩` is the image of the level
`K⸨t ^ (1 / n)⸩` under `e : puiseuxField K ≃ₐ[K⸨X⸩] L`. In particular `L` has at most one
intermediate field of each degree. -/
theorem eq_map_level_of_finrank_eq (e : puiseuxField K ≃ₐ[K⸨X⸩] L)
    {E : IntermediateField K⸨X⸩ L} {n : ℕ+} (h : finrank K⸨X⸩ E = n) :
    E = (level K n).map e.toAlgHom := by
  rw [← eq_level_of_finrank_eq ((intermediateFieldMap e.symm E).toLinearEquiv.finrank_eq ▸ h),
    map_map]
  ext x
  simp

/-- On the image under `e` of level `n`, an automorphism `σ` of `L` acts by the Kummer
automorphism attached to the level-`n` component of its image in the Tate module. -/
theorem apply_algEquiv_coe_level (e : puiseuxField K ≃ₐ[K⸨X⸩] L) (σ : Gal(L/K⸨X⸩)) {n : ℕ+}
    (x : level K n) :
    σ (e x) = e (levelKummer K n
      (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModuleOfAlgEquiv e σ)) x) := by
  rw [galEquivTateModuleOfAlgEquiv_apply, ← apply_coe_level, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

/-- **The finite-level stabilizers.** An automorphism of `L` fixes an intermediate field of degree
`n` over `K⸨X⸩` exactly when the level-`n` component of its image in the Tate module is
trivial. -/
theorem mem_fixingSubgroup_iff_of_finrank_eq (e : puiseuxField K ≃ₐ[K⸨X⸩] L)
    {E : IntermediateField K⸨X⸩ L} {n : ℕ+} (h : finrank K⸨X⸩ E = n) {σ : Gal(L/K⸨X⸩)} :
    σ ∈ E.fixingSubgroup ↔
      proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (galEquivTateModuleOfAlgEquiv e σ) = 1 := by
  rw [galEquivTateModuleOfAlgEquiv_apply, ← mem_fixingSubgroup_level_iff,
    e.symm.autCongr_mem_fixingSubgroup_iff, AlgEquiv.symm_symm, eq_map_level_of_finrank_eq e h]

end TauCeti.puiseuxField

namespace TauCeti.puiseuxField

open PrimeToPTateModule

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]

/-- **The absolute Galois group of `K⸨X⸩`.** If `K` is algebraically closed of characteristic
zero, the absolute Galois group of `K⸨X⸩`, with its Krull topology, is isomorphic as a topological
group to the Tate module `lim_n μₙ(K)`. It is the transport of `galEquivTateModule` along a chosen
isomorphism of the Puiseux field with `AlgebraicClosure K⸨X⸩`, and any other isomorphism gives the
same map (`TauCeti.puiseuxField.absoluteGaloisGroupEquivTateModule_apply`). -/
noncomputable def absoluteGaloisGroupEquivTateModule :
    Field.absoluteGaloisGroup K⸨X⸩ ≃ₜ* PrimeToPTateModule 1 K :=
  galEquivTateModuleOfAlgEquiv (IsAlgClosure.equiv K⸨X⸩ (puiseuxField K) (AlgebraicClosure K⸨X⸩))

variable {K}

/-- The image of `σ` in the Tate module is the image under `galEquivTateModule` of its conjugate
`e⁻¹ ∘ σ ∘ e`, for every isomorphism `e` of the Puiseux field with `AlgebraicClosure K⸨X⸩`. -/
theorem absoluteGaloisGroupEquivTateModule_apply
    (e : puiseuxField K ≃ₐ[K⸨X⸩] AlgebraicClosure K⸨X⸩) (σ : Field.absoluteGaloisGroup K⸨X⸩) :
    absoluteGaloisGroupEquivTateModule K σ = galEquivTateModule K (e.symm.autCongr σ) :=
  -- `Field.absoluteGaloisGroup K⸨X⸩` is by definition `Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩)`, the
  -- domain of `galEquivTateModuleOfAlgEquiv e`, so the two maps are compared pointwise.
  DFunLike.congr_fun (galEquivTateModuleOfAlgEquiv_eq _ e) σ

/-- **The characters `θₙ` on the algebraic closure.** Let `π` be a uniformizer of `K⸨X⸩` and `α`
an `n`-th root of `π` in `AlgebraicClosure K⸨X⸩`. An automorphism `σ` of the algebraic closure
over `K⸨X⸩` multiplies `α` by the level-`n` component of its image in the Tate module
`lim_n μₙ(K)`, whichever uniformizer and root are chosen. -/
theorem apply_eq_algebraMap_proj_absoluteGaloisGroupEquivTateModule_mul
    (σ : Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩)) (n : ℕ+) {π : K⸨X⸩} (hπ : π.order = 1)
    {α : AlgebraicClosure K⸨X⸩} (hα : α ^ (n : ℕ) = algebraMap K⸨X⸩ _ π) :
    σ α = algebraMap K (AlgebraicClosure K⸨X⸩)
      ((proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩
        (absoluteGaloisGroupEquivTateModule K σ) : Kˣ) : K) * α := by
  -- Transport the statement for the Puiseux field along a chosen isomorphism `e`.
  let e := IsAlgClosure.equiv K⸨X⸩ (puiseuxField K) (AlgebraicClosure K⸨X⸩)
  have hβ : e.symm α ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) π := by
    rw [← map_pow, hα, AlgEquiv.commutes]
  have h := apply_eq_algebraMap_proj_galEquivTateModule_mul (e.symm.autCongr σ) n hπ hβ
  -- Restate `absoluteGaloisGroupEquivTateModule_apply` for `σ : Gal(...)`, so that `rw` matches it
  -- against the goal, where `σ` does not have the type `Field.absoluteGaloisGroup K⸨X⸩`.
  have hσ : absoluteGaloisGroupEquivTateModule K σ = galEquivTateModule K (e.symm.autCongr σ) :=
    absoluteGaloisGroupEquivTateModule_apply e σ
  rw [hσ, ← e.symm.injective.eq_iff, map_mul,
    IsScalarTower.algebraMap_apply K K⸨X⸩ (AlgebraicClosure K⸨X⸩), AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply, ← h]
  simp [AlgEquiv.autCongr_apply]

/-- **The level-`n` component is the character `θₙ`.** For an `n`-th root `α` of a uniformizer
`π` of `K⸨X⸩`, the level-`n` component of the image of `σ` in the Tate module is the root of unity
`c` exactly when `σ (α) = c α`. -/
theorem proj_absoluteGaloisGroupEquivTateModule_eq_iff
    (σ : Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩)) (n : ℕ+) {π : K⸨X⸩} (hπ : π.order = 1)
    {α : AlgebraicClosure K⸨X⸩} (hα : α ^ (n : ℕ) = algebraMap K⸨X⸩ _ π)
    (c : rootsOfUnity n K) :
    proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ (absoluteGaloisGroupEquivTateModule K σ) = c ↔
      σ α = algebraMap K (AlgebraicClosure K⸨X⸩) ((c : Kˣ) : K) * α := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow n.ne_zero, eq_comm, map_eq_zero] at hα
    simp [hα] at hπ
  rw [apply_eq_algebraMap_proj_absoluteGaloisGroupEquivTateModule_mul σ n hπ hα,
    mul_left_inj' hα0, (algebraMap K _).injective.eq_iff, Units.val_inj, Subtype.coe_inj]

/-! ### The profinite integers -/

section ZHat

universe u

variable {ζ : PrimeToPTateModule 1 K}
  (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj m ζ : Kˣ) m)
include hζ

variable (K ζ) in
/-- **The absolute Galois group of `K⸨X⸩` is `ℤ̂`.** If `K` is algebraically closed of
characteristic zero and `ζ = (ζₙ)ₙ` is a compatible family of primitive `n`-th roots of unity in
`K`, the absolute Galois group of `K⸨X⸩`, with its Krull topology, is isomorphic as a topological
group to the profinite integers. The canonical generator of `ℤ̂` corresponds to the automorphism
multiplying every `n`-th root of `t` by `ζₙ`
(`TauCeti.puiseuxField.absoluteGaloisGroupEquivZHat_eq_gen_iff`). -/
noncomputable def absoluteGaloisGroupEquivZHat : Field.absoluteGaloisGroup K⸨X⸩ ≃ₜ* zHat.{u} :=
  (absoluteGaloisGroupEquivTateModule K).trans (continuousMulEquivZHat ζ hζ)

/-- The coordinate of `σ` in `ℤ̂` is the coordinate of its image in the Tate module. -/
theorem continuousMulEquivZHat_absoluteGaloisGroupEquivTateModule
    (σ : Field.absoluteGaloisGroup K⸨X⸩) :
    continuousMulEquivZHat ζ hζ (absoluteGaloisGroupEquivTateModule K σ) =
      absoluteGaloisGroupEquivZHat.{u} K ζ hζ σ := by
  rw [absoluteGaloisGroupEquivZHat, ContinuousMulEquiv.trans_apply]

/-- The coordinate of `σ` in `ℤ̂` is the image under `galEquivZHat` of its conjugate
`e⁻¹ ∘ σ ∘ e`, for every isomorphism `e` of the Puiseux field with `AlgebraicClosure K⸨X⸩`. In
particular it does not depend on the isomorphism. -/
theorem absoluteGaloisGroupEquivZHat_apply
    (e : puiseuxField K ≃ₐ[K⸨X⸩] AlgebraicClosure K⸨X⸩) (σ : Field.absoluteGaloisGroup K⸨X⸩) :
    absoluteGaloisGroupEquivZHat K ζ hζ σ = galEquivZHat K ζ hζ (e.symm.autCongr σ) := by
  -- Both sides are `continuousMulEquivZHat ζ hζ` applied to the image of `e⁻¹ ∘ σ ∘ e` in the
  -- Tate module; the body of `galEquivZHat` is not exposed, so compare through its inverse.
  rw [← continuousMulEquivZHat_absoluteGaloisGroupEquivTateModule,
    absoluteGaloisGroupEquivTateModule_apply e, ← (galEquivZHat K ζ hζ).symm_apply_eq,
    galEquivZHat_symm_apply]
  simp [← continuousMulEquivZHat_symm_apply hζ]

/-- The automorphism with coordinate `a ∈ ℤ̂` is the one whose image in the Tate module is
`zHat.lift ζ a`. -/
@[simp]
theorem absoluteGaloisGroupEquivZHat_symm_apply (a : zHat.{u}) :
    (absoluteGaloisGroupEquivZHat K ζ hζ).symm a =
      (absoluteGaloisGroupEquivTateModule K).symm (zHat.lift ζ a) := by
  rw [absoluteGaloisGroupEquivZHat, ContinuousMulEquiv.symm_trans_apply,
    continuousMulEquivZHat_symm_apply]

/-- **The action on roots of uniformizers.** An automorphism of the algebraic closure with
coordinate `a ∈ ℤ̂` multiplies every `n`-th root of every uniformizer of `K⸨X⸩` by
`ζₙ ^ (a mod n)`. -/
theorem apply_eq_algebraMap_pow_toZMod_absoluteGaloisGroupEquivZHat_mul
    (σ : Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩)) (n : ℕ+) {π : K⸨X⸩} (hπ : π.order = 1)
    {α : AlgebraicClosure K⸨X⸩} (hα : α ^ (n : ℕ) = algebraMap K⸨X⸩ _ π) :
    σ α = algebraMap K (AlgebraicClosure K⸨X⸩)
      (((proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Kˣ) : K) ^
        (zHat.toZMod n (Additive.ofMul (absoluteGaloisGroupEquivZHat.{u} K ζ hζ σ))).val) * α := by
  have hσ := continuousMulEquivZHat_absoluteGaloisGroupEquivTateModule.{u} hζ σ
  rw [← hσ, ← Units.val_pow_eq_pow_val, coe_proj_pow_toZMod_continuousMulEquivZHat hζ]
  exact apply_eq_algebraMap_proj_absoluteGaloisGroupEquivTateModule_mul σ n hπ hα

/-- **The generator.** Fix a uniformizer `π` of `K⸨X⸩`, for instance `t`. An automorphism of the
algebraic closure has coordinate the canonical generator of `ℤ̂` exactly when it multiplies every
`n`-th root of `π` by `ζₙ`, for every `n > 0`. -/
theorem absoluteGaloisGroupEquivZHat_eq_gen_iff (σ : Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩))
    {π : K⸨X⸩} (hπ : π.order = 1) :
    absoluteGaloisGroupEquivZHat.{u} K ζ hζ σ = zHat.gen ↔
      ∀ (n : ℕ+) (α : AlgebraicClosure K⸨X⸩), α ^ (n : ℕ) = algebraMap K⸨X⸩ _ π →
        σ α = algebraMap K (AlgebraicClosure K⸨X⸩)
          ((proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ : Kˣ) : K) * α := by
  have hσ := continuousMulEquivZHat_absoluteGaloisGroupEquivTateModule.{u} hζ σ
  rw [← hσ, ← continuousMulEquivZHat_self.{u} hζ, (continuousMulEquivZHat ζ hζ).injective.eq_iff]
  refine ⟨fun h n α hα ↦ ?_, fun h ↦ ext fun m ↦ ?_⟩
  · rw [← proj_absoluteGaloisGroupEquivTateModule_eq_iff σ n hπ hα, h]
  · -- Compare the level-`m` components through an `m`-th root of `π`.
    obtain ⟨m, hm0, _⟩ := m
    let n : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm0⟩
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap K⸨X⸩ (AlgebraicClosure K⸨X⸩) π) n.pos
    exact (proj_absoluteGaloisGroupEquivTateModule_eq_iff σ n hπ hα _).2 (h n α hα)

/-- **The finite-level stabilizers.** An automorphism of the algebraic closure fixes an
intermediate field of degree `n` over `K⸨X⸩` exactly when its coordinate in `ℤ̂` reduces to zero
modulo `n`. -/
theorem mem_fixingSubgroup_iff_toZMod_eq_zero_of_finrank_eq
    {E : IntermediateField K⸨X⸩ (AlgebraicClosure K⸨X⸩)} {n : ℕ+} (h : finrank K⸨X⸩ E = n)
    {σ : Gal(AlgebraicClosure K⸨X⸩/K⸨X⸩)} :
    σ ∈ E.fixingSubgroup ↔
      zHat.toZMod n (Additive.ofMul (absoluteGaloisGroupEquivZHat.{u} K ζ hζ σ)) = 0 := by
  let e := IsAlgClosure.equiv K⸨X⸩ (puiseuxField K) (AlgebraicClosure K⸨X⸩)
  -- As above, restate `absoluteGaloisGroupEquivZHat_apply` for `σ : Gal(...)` to rewrite with it.
  have hσ : absoluteGaloisGroupEquivZHat.{u} K ζ hζ σ = galEquivZHat K ζ hζ (e.symm.autCongr σ) :=
    absoluteGaloisGroupEquivZHat_apply hζ e σ
  rw [hσ, ← mem_fixingSubgroup_level_iff_toZMod_eq_zero hζ,
    e.symm.autCongr_mem_fixingSubgroup_iff, AlgEquiv.symm_symm, eq_map_level_of_finrank_eq e h]

/-! ### Changing the compatible family of primitive roots of unity -/

section Change

open scoped zHat

variable {ζ' : PrimeToPTateModule 1 K}
  (hζ' : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj m ζ' : Kˣ) m)

/-- **Changing the compatible family of primitive roots of unity.** If `ζ' = ζ ^ᶻ u` for the unit
`u = zHatUnit hζ hζ'` of `ℤ̂`, the coordinate of an absolute Galois automorphism relative to `ζ'`
is its coordinate relative to `ζ` multiplied by `u⁻¹`. -/
theorem absoluteGaloisGroupEquivZHat_apply_eq_zpowHat (σ : Field.absoluteGaloisGroup K⸨X⸩) :
    absoluteGaloisGroupEquivZHat.{u} K ζ' hζ' σ =
      absoluteGaloisGroupEquivZHat.{u} K ζ hζ σ ^ᶻ
        ((zHatUnit.{u} hζ hζ')⁻¹ : (Additive zHat.{u})ˣ) := by
  rw [← continuousMulEquivZHat_absoluteGaloisGroupEquivTateModule,
    ← continuousMulEquivZHat_absoluteGaloisGroupEquivTateModule]
  exact continuousMulEquivZHat_apply_eq_zpowHat hζ hζ' _

/-- **The inverse formula.** The automorphism with coordinate `a` relative to `ζ'` is the
automorphism with coordinate `a ^ᶻ u` relative to `ζ`, where `u = zHatUnit hζ hζ'`. -/
theorem absoluteGaloisGroupEquivZHat_symm_apply_eq_symm_zpowHat (a : zHat.{u}) :
    (absoluteGaloisGroupEquivZHat K ζ' hζ').symm a =
      (absoluteGaloisGroupEquivZHat K ζ hζ).symm
        (a ^ᶻ (zHatUnit.{u} hζ hζ' : Additive zHat.{u})) := by
  rw [ContinuousMulEquiv.symm_apply_eq, absoluteGaloisGroupEquivZHat_apply_eq_zpowHat hζ hζ',
    ContinuousMulEquiv.apply_symm_apply, ← zpowHat_mul, Units.mul_inv, zpowHat_one]

end Change

end ZHat

end TauCeti.puiseuxField
