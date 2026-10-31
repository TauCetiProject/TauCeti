/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.RingTheory.LaurentSeries.Puiseux.FiniteExtension
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois

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

## Main definitions

* `TauCeti.puiseuxField.galEquivTateModuleOfAlgEquiv e`: for `e : puiseuxField K ≃ₐ[K⸨X⸩] L`, the
  isomorphism of topological groups `Gal(L/K⸨X⸩) ≃ₜ* lim_n μₙ(K)`.
* `TauCeti.puiseuxField.absoluteGaloisGroupEquivTateModule K`: for `K` algebraically closed of
  characteristic zero, the isomorphism of topological groups between the absolute Galois group
  `Field.absoluteGaloisGroup K⸨X⸩` and `lim_n μₙ(K)`.

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

end TauCeti.puiseuxField
