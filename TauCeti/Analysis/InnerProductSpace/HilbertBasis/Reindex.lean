/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reindexing Hilbert bases and unitary equivalences between Hilbert spaces

This file provides the infinite-dimensional `HilbertBasis` counterparts of Mathlib's
`EuclideanSpace.basisFun`, `OrthonormalBasis.reindex`, and `OrthonormalBasis.equiv`:

* `lp.hilbertBasisFun ι 𝕜`: the standard unit coordinate basis of `ℓ²(ι, 𝕜)`.
* `HilbertBasis.reindex b e`: reindexing a Hilbert basis `b` along `e : ι ≃ ι'`.
* `HilbertBasis.equiv b c e`: the linear isometric equivalence `E ≃ₗᵢ[𝕜] F` sending each basis
  vector `b i` to `c (e i)`, characterized as the unique unitary map with this action on `b`
  (`HilbertBasis.eq_equiv_of_forall_apply_eq`, `HilbertBasis.existsUnique_linearIsometryEquiv`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Theorem I.4.19.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.2.
-/

public section

open scoped InnerProductSpace lp

namespace lp

/-- The standard unit coordinate vectors, bundled as a Hilbert basis of `ℓ²(ι, 𝕜)`. This is the
`ℓ²` analogue of `EuclideanSpace.basisFun`. -/
noncomputable def hilbertBasisFun (ι 𝕜 : Type*) [RCLike 𝕜] : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 ℓ²(ι, 𝕜))

/-- The coordinate representation of `lp.hilbertBasisFun` is the identity isometry on `ℓ²(ι, 𝕜)`. -/
@[simp]
theorem hilbertBasisFun_repr (ι 𝕜 : Type*) [RCLike 𝕜] :
    (hilbertBasisFun ι 𝕜).repr = LinearIsometryEquiv.refl 𝕜 ℓ²(ι, 𝕜) :=
  (rfl)

/-- The `i`-th vector of `lp.hilbertBasisFun` is the unit single-coordinate vector at `i`. -/
@[simp]
theorem hilbertBasisFun_apply (ι 𝕜 : Type*) [RCLike 𝕜] [DecidableEq ι] (i : ι) :
    hilbertBasisFun ι 𝕜 i = lp.single 2 i 1 := by
  rw [← HilbertBasis.repr_symm_single, hilbertBasisFun_repr]
  exact (LinearIsometryEquiv.refl 𝕜 _).symm_apply_eq.2 rfl

/-- Inner product against the `i`-th vector of `lp.hilbertBasisFun` evaluates the `i`-th
coordinate. -/
@[simp]
theorem hilbertBasisFun_inner (ι 𝕜 : Type*) [RCLike 𝕜] (x : ℓ²(ι, 𝕜)) (i : ι) :
    ⟪hilbertBasisFun ι 𝕜 i, x⟫_𝕜 = x i := by
  rw [← (hilbertBasisFun ι 𝕜).repr_apply_apply]
  simp

end lp

namespace HilbertBasis

variable {ι ι' κ 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

section Reindex

/-- Reindex a Hilbert basis along an equivalence `e : ι ≃ ι'` of index types. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') : HilbertBasis ι' 𝕜 E :=
  ofRepr (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e))

/-- The coordinate representation of `b.reindex e` composes `b.repr` with
`LinearIsometryEquiv.lpCongrLeft`. -/
@[simp]
theorem repr_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).repr = b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e) :=
  (rfl)

/-- Reindexing `b` by `e` reads `b` at `e.symm i'`. -/
theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    b.reindex e i' = b (e.symm i') := by
  classical
  simp only [← HilbertBasis.repr_symm_single, repr_reindex, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.lpCongrLeft_symm,
    LinearIsometryEquiv.lpCongrLeft_single]

/-- Function-level form of `HilbertBasis.reindex_apply`. -/
@[simp]
theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

/-- Reindexing a Hilbert basis along the identity equivalence leaves it unchanged. -/
@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along two equivalences in succession agrees with reindexing along their
composition. -/
@[simp]
theorem reindex_trans {ι'' : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.reindex e).reindex e' = b.reindex (e.trans e') :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Index reindexing commutes with transporting a Hilbert basis along a linear isometric
equivalence. -/
theorem mapₗᵢ_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (U : E ≃ₗᵢ[𝕜] F) :
    (b.reindex e).mapₗᵢ U = (b.mapₗᵢ U).reindex e :=
  DFunLike.ext _ _ fun _ ↦ by simp

end Reindex

section Equiv

/-- **Unitary equivalence from a bijection of Hilbert bases.** Given Hilbert bases `b` of `E` and
`c` of `F`, a bijection `e : ι ≃ κ` induces a linear isometric equivalence `E ≃ₗᵢ[𝕜] F` sending
each `b i` to `c (e i)`. This is the infinite-dimensional analogue of `OrthonormalBasis.equiv`. -/
protected noncomputable def equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    E ≃ₗᵢ[𝕜] F :=
  b.repr.trans <| (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e).trans c.repr.symm

/-- Explicit decomposition of `b.equiv c e` through `ℓ²` coordinate representations. -/
theorem equiv_def (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    b.equiv c e =
      b.repr.trans ((LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e).trans c.repr.symm) :=
  (rfl)

/-- `b.equiv c e` sends the `i`-th vector of `b` to the `e i`-th vector of `c`. -/
@[simp]
theorem equiv_apply_basis (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) (i : ι) :
    b.equiv c e (b i) = c (e i) := by
  classical
  rw [equiv_def, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, b.repr_self,
    LinearIsometryEquiv.lpCongrLeft_single, c.repr_symm_single]

/-- Transporting `b` along `b.equiv c e` produces `c` reindexed by `e.symm`. -/
@[simp]
theorem mapₗᵢ_equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    b.mapₗᵢ (b.equiv c e) = c.reindex e.symm :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Expansion of `b.equiv c e x` in the target Hilbert basis:
`b.equiv c e x = ∑ᵢ ⟪b i, x⟫ • c (e i)`. -/
theorem hasSum_equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (x : E) :
    HasSum (fun i ↦ b.repr x i • c (e i)) (b.equiv c e x) := by
  simpa using (b.equiv c e).toLinearIsometry.toContinuousLinearMap.hasSum (b.hasSum_repr x)

/-- Any linear isometric equivalence sending every `b i` to `c (e i)` coincides with
`b.equiv c e`. -/
theorem eq_equiv_of_forall_apply_eq (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    {U : E ≃ₗᵢ[𝕜] F} (hU : ∀ i, U (b i) = c (e i)) :
    U = b.equiv c e := by
  suffices U.toLinearIsometry.toContinuousLinearMap =
      (b.equiv c e).toLinearIsometry.toContinuousLinearMap from
    LinearIsometryEquiv.ext fun x ↦ DFunLike.congr_fun this x
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span) ?_
  rintro _ ⟨i, rfl⟩
  simp [hU i]

/-- A bijection `e : ι ≃ κ` between the index types of Hilbert bases `b` and `c` determines a
unique linear isometric equivalence `U : E ≃ₗᵢ[𝕜] F` satisfying `U (b i) = c (e i)` for all `i`. -/
theorem existsUnique_linearIsometryEquiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) :
    ∃! U : E ≃ₗᵢ[𝕜] F, ∀ i, U (b i) = c (e i) :=
  ⟨b.equiv c e, b.equiv_apply_basis c e, fun _ hU ↦ b.eq_equiv_of_forall_apply_eq c e hU⟩

/-- Inverting `b.equiv c e` gives `c.equiv b e.symm`. -/
@[simp]
theorem equiv_symm (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    (b.equiv c e).symm = c.equiv b e.symm :=
  c.eq_equiv_of_forall_apply_eq b e.symm fun j ↦
    (b.equiv c e).symm_apply_eq.2 (by simp)

/-- `b.equiv b (Equiv.refl ι)` is the identity linear isometric equivalence on `E`. -/
@[simp]
theorem equiv_self_refl (b : HilbertBasis ι 𝕜 E) :
    b.equiv b (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  (b.eq_equiv_of_forall_apply_eq b (Equiv.refl ι) fun _ ↦ rfl).symm

/-- Composing `b.equiv c e₁` with `c.equiv d e₂` gives `b.equiv d (e₁.trans e₂)`. -/
@[simp]
theorem equiv_trans {μ G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (d : HilbertBasis μ 𝕜 G)
    (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    (b.equiv c e₁).trans (c.equiv d e₂) = b.equiv d (e₁.trans e₂) :=
  b.eq_equiv_of_forall_apply_eq d (e₁.trans e₂) fun _ ↦ by simp

end Equiv

end HilbertBasis
