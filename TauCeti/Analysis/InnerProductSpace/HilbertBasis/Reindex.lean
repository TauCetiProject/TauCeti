/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reindexing Hilbert bases and basis-induced unitaries

This file develops the Hilbert-basis analogues of `OrthonormalBasis.reindex` and
`OrthonormalBasis.equiv`:

* `HilbertBasis.reindex b e` reindexes a Hilbert basis `b : HilbertBasis ι 𝕜 E` along an
  equivalence `e : ι ≃ κ` by composing `b.repr` with `LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e`.
* `HilbertBasis.equiv b c e` constructs the canonical linear isometric equivalence `E ≃ₗᵢ[𝕜] F`
  sending each basis vector `b i` to `c (e i)` and expanding `b.equiv c e x` as the unconditionally
  convergent series `∑' i, b.repr x i • c (e i)`.
-/

public section

variable {ι κ 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

/-- Reindex a Hilbert basis along an equivalence of index types. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    HilbertBasis κ 𝕜 E :=
  ofRepr (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e))

/-- The coordinate representation of `b.reindex e` is `b.repr` followed by coordinate reindexing. -/
@[simp]
theorem repr_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).repr = b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e) := (rfl)

/-- The `j`th vector of `b.reindex e` is `b (e.symm j)`. -/
@[simp]
theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (j : κ) :
    b.reindex e j = b (e.symm j) := by
  classical
  simp only [← HilbertBasis.repr_symm_single, repr_reindex, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.lpCongrLeft_symm,
    LinearIsometryEquiv.lpCongrLeft_single]

/-- Function-level form of `HilbertBasis.reindex_apply`. -/
@[simp]
theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

/-- Reindexing along `Equiv.refl` leaves a Hilbert basis unchanged. -/
@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along two equivalences is the same as reindexing along their composition. -/
@[simp]
theorem reindex_trans {μ : Type*} (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (e' : κ ≃ μ) :
    (b.reindex e).reindex e' = b.reindex (e.trans e') :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along `e` and then along `e.symm` recovers the original Hilbert basis. -/
theorem reindex_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).reindex e.symm = b := by
  simp

/-- Reindexing along `e.symm` and then along `e` recovers the original Hilbert basis. -/
theorem reindex_symm_self (b : HilbertBasis κ 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e.symm).reindex e = b := by
  simp

/-- Reindexing commutes with transporting a Hilbert basis along a linear isometric equivalence. -/
theorem reindex_mapₗᵢ (b : HilbertBasis ι 𝕜 E) (U : E ≃ₗᵢ[𝕜] F) (e : ι ≃ κ) :
    (b.mapₗᵢ U).reindex e = (b.reindex e).mapₗᵢ U :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- The linear isometric equivalence sending a Hilbert basis `b` to a Hilbert basis `c` along an
equivalence `e` of their index types. -/
protected noncomputable def equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) : E ≃ₗᵢ[𝕜] F :=
  b.repr.trans ((LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e).trans c.repr.symm)

/-- The inverse of `b.equiv c e` is `c.equiv b e.symm`. -/
@[simp]
theorem equiv_symm (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    (b.equiv c e).symm = c.equiv b e.symm := by
  ext x
  simp [HilbertBasis.equiv]

/-- `b.equiv c e` sends each basis vector `b i` to `c (e i)`. -/
@[simp]
theorem equiv_apply_basis (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (i : ι) : b.equiv c e (b i) = c (e i) := by
  classical
  simp [HilbertBasis.equiv, b.repr_self]

/-- The basis-induced equivalence of a Hilbert basis with itself along `Equiv.refl` is the
identity. -/
@[simp]
theorem equiv_self_refl (b : HilbertBasis ι 𝕜 E) :
    b.equiv b (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E := by
  ext x
  simp [HilbertBasis.equiv]

/-- Composing two basis-induced equivalences along a common intermediate Hilbert basis composes the
index equivalences. -/
@[simp]
theorem equiv_trans {μ G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (d : HilbertBasis μ 𝕜 G)
    (e : ι ≃ κ) (e' : κ ≃ μ) :
    (b.equiv c e).trans (c.equiv d e') = b.equiv d (e.trans e') := by
  ext x
  simp only [HilbertBasis.equiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact congrArg d.repr.symm (by ext j; simp)

/-- Transporting `b` along `b.equiv c e` produces `c` reindexed by `e.symm`. -/
@[simp]
theorem mapₗᵢ_equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    b.mapₗᵢ (b.equiv c e) = c.reindex e.symm :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Coordinates of `b.equiv c e x` in `c` are the reindexed coordinates of `x` in `b`. -/
@[simp]
theorem repr_equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (x : E) (j : κ) : c.repr (b.equiv c e x) j = b.repr x (e.symm j) := by
  simp [HilbertBasis.equiv]

/-- `b.equiv c e x` is the unconditional sum `∑' i, b.repr x i • c (e i)`. -/
theorem hasSum_equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (x : E) : HasSum (fun i ↦ b.repr x i • c (e i)) (b.equiv c e x) := by
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    map_smul, b.equiv_apply_basis c e] using
    (b.equiv c e).toContinuousLinearEquiv.toContinuousLinearMap.hasSum (b.hasSum_repr x)

/-- Formula for `b.equiv c e x` as an infinite series in `c`. -/
theorem equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) (x : E) :
    b.equiv c e x = ∑' i, b.repr x i • c (e i) :=
  (b.hasSum_equiv_apply c e x).tsum_eq.symm

end HilbertBasis
