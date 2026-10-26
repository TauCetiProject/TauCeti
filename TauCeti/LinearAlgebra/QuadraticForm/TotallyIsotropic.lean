/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Totally isotropic submodules

A submodule `W` of `M` is *totally isotropic* for a quadratic map `Q` when `Q` vanishes on every
vector of `W`, that is, when the restriction of `Q` to `W` is zero.

## Main definitions

* `QuadraticMap.IsTotallyIsotropic`: a submodule on which a quadratic map vanishes.

## Main results

* `QuadraticMap.isTotallyIsotropic_iff_restrict_eq_zero`: total isotropy is the vanishing of the
  restricted form.
* `QuadraticMap.isTotallyIsotropic_comp_iff`: total isotropy for `Q.comp f` is total isotropy of
  the image under `f`.
* `QuadraticMap.maximal_isTotallyIsotropic_bot_iff`: the zero submodule is maximal totally
  isotropic exactly when the form is anisotropic.
* `QuadraticMap.IsTotallyIsotropic.eq_zero_of_polar_eq_zero`: for a nondegenerate form and
  `W ⊔ W' = ⊤` with `W'` totally isotropic, a vector of `W'` which is polar-orthogonal to `W`
  vanishes.
* `QuadraticMap.IsTotallyIsotropic.finrank_eq_of_codisjoint`: two totally isotropic subspaces
  spanning a finite-dimensional nondegenerate quadratic space have the same dimension.

The Witt-index comparison for maximal totally isotropic subspaces (Lam I.4.4) is in
`TauCeti.LinearAlgebra.QuadraticForm.Witt.TotallyIsotropic`.
-/

public section

namespace QuadraticMap

section Semiring

variable {R M M' N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N] {Q : QuadraticMap R M N}
  {W W' : Submodule R M}

/-- A submodule `W` is *totally isotropic* for a quadratic map `Q` when `Q` vanishes on every
vector of `W`. -/
def IsTotallyIsotropic (Q : QuadraticMap R M N) (W : Submodule R M) : Prop :=
  ∀ v ∈ W, Q v = 0

/-- Unfolds `QuadraticMap.IsTotallyIsotropic`. -/
theorem isTotallyIsotropic_iff : Q.IsTotallyIsotropic W ↔ ∀ v ∈ W, Q v = 0 := Iff.rfl

/-- A quadratic map vanishes on each vector of a totally isotropic submodule. -/
theorem IsTotallyIsotropic.apply_eq_zero (hW : Q.IsTotallyIsotropic W) {v : M} (hv : v ∈ W) :
    Q v = 0 :=
  hW v hv

/-- A submodule is totally isotropic exactly when the restriction of the form to it is zero. -/
theorem isTotallyIsotropic_iff_restrict_eq_zero : Q.IsTotallyIsotropic W ↔ Q.restrict W = 0 :=
  ⟨fun h ↦ QuadraticMap.ext fun v ↦ h v v.2, fun h v hv ↦ by
    simpa using congr($h ⟨v, hv⟩)⟩

/-- A submodule is totally isotropic for `Q.comp f` exactly when its image under `f` is totally
isotropic for `Q`. -/
theorem isTotallyIsotropic_comp_iff {f : M' →ₗ[R] M} {T : Submodule R M'} :
    (Q.comp f).IsTotallyIsotropic T ↔ Q.IsTotallyIsotropic (T.map f) := by
  simp only [isTotallyIsotropic_iff, Submodule.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, comp_apply]

/-- The preimage of a totally isotropic submodule under a linear map `f` is totally isotropic
for `Q.comp f`. -/
theorem IsTotallyIsotropic.comap (hW : Q.IsTotallyIsotropic W) (f : M' →ₗ[R] M) :
    (Q.comp f).IsTotallyIsotropic (W.comap f) :=
  fun _ hv ↦ hW _ hv

/-- A submodule of `U` is totally isotropic for the restriction of `Q` to `U` exactly when it is
totally isotropic for `Q` as a submodule of `M`. -/
theorem isTotallyIsotropic_restrict_iff {U : Submodule R M} {T : Submodule R U} :
    (Q.restrict U).IsTotallyIsotropic T ↔ Q.IsTotallyIsotropic (T.map U.subtype) :=
  isTotallyIsotropic_comp_iff (Q := Q) (f := U.subtype)

/-- The vectors of `U` lying in a totally isotropic submodule `W` form a totally isotropic
submodule for the restriction of `Q` to `U`. -/
theorem IsTotallyIsotropic.restrict (hW : Q.IsTotallyIsotropic W) (U : Submodule R M) :
    (Q.restrict U).IsTotallyIsotropic (W.comap U.subtype) :=
  hW.comap U.subtype

/-- The zero submodule is totally isotropic. -/
@[simp]
theorem isTotallyIsotropic_bot : Q.IsTotallyIsotropic ⊥ := by
  intro v hv
  rw [Submodule.mem_bot] at hv
  rw [hv, map_zero]

/-- A submodule of a totally isotropic submodule is totally isotropic. -/
theorem IsTotallyIsotropic.mono (hW : Q.IsTotallyIsotropic W) (h : W' ≤ W) :
    Q.IsTotallyIsotropic W' :=
  fun v hv ↦ hW v (h hv)

/-- A line is totally isotropic exactly when its spanning vector is isotropic. -/
@[simp]
theorem isTotallyIsotropic_span_singleton_iff {v : M} :
    Q.IsTotallyIsotropic (R ∙ v) ↔ Q v = 0 := by
  refine ⟨fun h ↦ h v (Submodule.mem_span_singleton_self v), fun h u hu ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [QuadraticMap.map_smul, h, smul_zero]

/-- The zero subspace is a maximal totally isotropic subspace exactly when the form is
anisotropic. -/
theorem maximal_isTotallyIsotropic_bot_iff :
    Maximal Q.IsTotallyIsotropic ⊥ ↔ Q.Anisotropic := by
  refine ⟨fun h v hv ↦ ?_, fun h ↦ ⟨isTotallyIsotropic_bot, fun U hU _ v hv ↦ ?_⟩⟩
  · have hle := h.2 (isTotallyIsotropic_span_singleton_iff.mpr hv) bot_le
    rwa [le_bot_iff, Submodule.span_singleton_eq_bot] at hle
  · rw [Submodule.mem_bot]
    exact h v (hU v hv)

end Semiring

section Group

variable {R M N : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {Q : QuadraticMap R M N} {W : Submodule R M}

/-- The polar form vanishes on pairs of vectors of a totally isotropic submodule. -/
theorem IsTotallyIsotropic.polar_eq_zero (hW : Q.IsTotallyIsotropic W) {v w : M} (hv : v ∈ W)
    (hw : w ∈ W) : polar Q v w = 0 := by
  rw [polar, hW _ (W.add_mem hv hw), hW v hv, hW w hw, sub_zero, sub_zero]

end Group

section Ring

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {Q : QuadraticMap R M N} {W W' : Submodule R M}

/-- For a nondegenerate `Q`, if `W ⊔ W' = ⊤` with `W'` totally isotropic, a vector of `W'`
which is polar-orthogonal to `W` vanishes: it is then polar-orthogonal to all of `M = W + W'`,
hence lies in the radical. -/
theorem IsTotallyIsotropic.eq_zero_of_polar_eq_zero (hW' : Q.IsTotallyIsotropic W')
    (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') {y : M} (hy : y ∈ W')
    (hyW : ∀ x ∈ W, polar Q x y = 0) : y = 0 := by
  have hpolar (z : M) : polar Q y z = 0 := by
    obtain ⟨x, hx, z', hz', rfl⟩ := Submodule.mem_sup.mp (hWW'.eq_top ▸
      Submodule.mem_top : z ∈ W ⊔ W')
    rw [polar_add_right, hW'.polar_eq_zero hy hz', polar_comm, hyW x hx, add_zero]
  have hrad : y ∈ Q.radical := ⟨hW'.apply_eq_zero hy, LinearMap.ext hpolar⟩
  simpa [hQ.radical_eq_bot] using hrad

/-- For a nondegenerate `Q` and `W ⊔ W' = ⊤` with `W'` totally isotropic, the polar pairing of
`W'` with `W` is injective in the `W'` variable. -/
theorem IsTotallyIsotropic.polarBilin_compl₁₂_flip_injective (hW' : Q.IsTotallyIsotropic W')
    (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') :
    Function.Injective ((polarBilin Q).compl₁₂ W.subtype W'.subtype).flip := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => Subtype.ext ?_
  refine hW'.eq_zero_of_polar_eq_zero hQ hWW' y.2 fun x hx => ?_
  simpa using LinearMap.congr_fun hy ⟨x, hx⟩

end Ring

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V}

/-- Two totally isotropic subspaces spanning a finite-dimensional nondegenerate quadratic space
have the same dimension: the polar pairing embeds each into the dual of the other. -/
theorem IsTotallyIsotropic.finrank_eq_of_codisjoint (hW : Q.IsTotallyIsotropic W)
    (hW' : Q.IsTotallyIsotropic W') (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') :
    Module.finrank K W' = Module.finrank K W := by
  apply le_antisymm
  · simpa [Subspace.dual_finrank_eq] using
      LinearMap.finrank_le_finrank_of_injective (hW'.polarBilin_compl₁₂_flip_injective hQ hWW')
  · simpa [Subspace.dual_finrank_eq] using
      LinearMap.finrank_le_finrank_of_injective (hW.polarBilin_compl₁₂_flip_injective hQ hWW'.symm)

end Field

end QuadraticMap
