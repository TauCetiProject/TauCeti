/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reindexing Hilbert bases and basis-to-basis unitary equivalences

An equivalence `e : ι ≃ κ` between index types (possibly in different universes) reindexes a
Hilbert basis `b : HilbertBasis ι 𝕜 E` to a Hilbert basis `b.reindex e : HilbertBasis κ 𝕜 E` with
`(b.reindex e) j = b (e.symm j)`, obtained by composing `b.repr` with
`LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e`.

Given two Hilbert bases `b : HilbertBasis ι 𝕜 E` and `c : HilbertBasis κ 𝕜 F` and an equivalence
`e : ι ≃ κ`, composing `b.repr`, `LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e`, and `c.repr.symm`
yields the unique linear isometric equivalence `b.equiv c e : E ≃ₗᵢ[𝕜] F` sending `b i` to
`c (e i)` for every `i` (`HilbertBasis.equiv_apply_basis`,
`HilbertBasis.existsUnique_linearIsometryEquiv`).

## Main declarations

* `HilbertBasis.reindex`: reindex a Hilbert basis along `e : ι ≃ κ`.
* `HilbertBasis.equiv`: the linear isometric equivalence `E ≃ₗᵢ[𝕜] F` carrying `b i` to `c (e i)`.
* `HilbertBasis.existsUnique_linearIsometryEquiv`: existence and uniqueness of the unitary sending
  `b i` to `c (e i)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter I, §4.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, §II.2.
-/

public section

open scoped InnerProductSpace

namespace HilbertBasis

variable {ι : Type*} {κ : Type*} {μ : Type*} {𝕜 : Type*}
  {E : Type*} {F : Type*} {G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-! ### Reindexing a Hilbert basis -/

/-- Reindex a Hilbert basis along an equivalence `e : ι ≃ κ` of index types. This is the
`HilbertBasis` counterpart of `OrthonormalBasis.reindex`. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) : HilbertBasis κ 𝕜 E :=
  ofRepr (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e))

/-- The coordinate representation of `b.reindex e` is `b.repr` followed by
`LinearIsometryEquiv.lpCongrLeft`. -/
@[simp]
theorem repr_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).repr = b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e) :=
  (rfl)

/-- Pointwise coordinate formula for `HilbertBasis.reindex`. -/
theorem repr_reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (x : E) (j : κ) :
    (b.reindex e).repr x j = b.repr x (e.symm j) := by
  simp

/-- The `j`-th vector of `b.reindex e` is `b (e.symm j)`. -/
@[simp]
protected theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (j : κ) :
    b.reindex e j = b (e.symm j) := by
  classical
  simp [← HilbertBasis.repr_symm_single]

/-- Function-level form of `HilbertBasis.reindex_apply`. -/
@[simp]
protected theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

/-- Reindexing along the identity equivalence leaves a Hilbert basis unchanged. -/
@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along two equivalences in succession is reindexing along their composition. -/
@[simp]
theorem reindex_trans (b : HilbertBasis ι 𝕜 E) (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    (b.reindex e₁).reindex e₂ = b.reindex (e₁.trans e₂) :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along `e` and then along `e.symm` recovers the original Hilbert basis. -/
theorem reindex_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).reindex e.symm = b := by
  simp

/-- Transporting a Hilbert basis across a linear isometric equivalence commutes with reindexing. -/
theorem mapₗᵢ_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (U : E ≃ₗᵢ[𝕜] F) :
    (b.reindex e).mapₗᵢ U = (b.mapₗᵢ U).reindex e :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Converting a finite Hilbert basis to an `OrthonormalBasis` commutes with reindexing. -/
@[simp]
theorem toOrthonormalBasis_reindex [Fintype ι] [Fintype κ] (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).toOrthonormalBasis = b.toOrthonormalBasis.reindex e :=
  DFunLike.ext _ _ fun j ↦ by simp [OrthonormalBasis.reindex_apply]

/-! ### Basis-to-basis unitary equivalences -/

/-- The linear isometric equivalence `E ≃ₗᵢ[𝕜] F` carrying a Hilbert basis `b` of `E` to a Hilbert
basis `c` of `F` along an index equivalence `e : ι ≃ κ`. This is the `HilbertBasis` counterpart of
`OrthonormalBasis.equiv`. -/
protected noncomputable def equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) : E ≃ₗᵢ[𝕜] F :=
  b.repr.trans ((LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e).trans c.repr.symm)

/-- `b.equiv c e` maps the `i`-th basis vector of `b` to the `e i`-th basis vector of `c`. -/
@[simp]
theorem equiv_apply_basis (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) (i : ι) :
    b.equiv c e (b i) = c (e i) := by
  classical
  simp [HilbertBasis.equiv, b.repr_self]

/-- The `j`-th coordinate of `b.equiv c e x` in `c` is the `e.symm j`-th coordinate of `x` in `b`.
-/
@[simp]
theorem repr_equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (x : E) (j : κ) :
    c.repr (b.equiv c e x) j = b.repr x (e.symm j) := by
  simp [HilbertBasis.equiv]

/-- Pairing `b.equiv c e x` against `c j` gives the inner product `⟪b (e.symm j), x⟫_𝕜`. -/
theorem inner_equiv_left (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (x : E) (j : κ) :
    ⟪c j, b.equiv c e x⟫_𝕜 = ⟪b (e.symm j), x⟫_𝕜 := by
  rw [← c.repr_apply_apply, b.repr_equiv_apply c e, b.repr_apply_apply]

/-- Series expansion of `b.equiv c e x` in the target Hilbert basis `c`:
`b.equiv c e x = ∑ᵢ ⟪b i, x⟫_𝕜 • c (e i)`. -/
theorem hasSum_equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • c (e i)) (b.equiv c e x) := by
  have h : HasSum (fun i ↦ b.equiv c e (b.repr x i • b i)) (b.equiv c e x) :=
    (b.equiv c e).toContinuousLinearEquiv.toContinuousLinearMap.hasSum (b.hasSum_repr x)
  simpa only [map_smul, b.equiv_apply_basis c e, b.repr_apply_apply] using h

/-- The inverse of `b.equiv c e` is `c.equiv b e.symm`. -/
@[simp]
theorem equiv_symm (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    (b.equiv c e).symm = c.equiv b e.symm := by
  refine c.ext_linearIsometryEquiv fun j ↦ (b.equiv c e).injective ?_
  simp

/-- `b.equiv b (Equiv.refl ι)` is the identity linear isometric equivalence on `E`. -/
@[simp]
theorem equiv_refl (b : HilbertBasis ι 𝕜 E) :
    b.equiv b (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  b.ext_linearIsometryEquiv fun i ↦ by simp

/-- Composing `b.equiv c e₁` and `c.equiv d e₂` gives `b.equiv d (e₁.trans e₂)`. -/
@[simp]
theorem equiv_trans (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (d : HilbertBasis μ 𝕜 G)
    (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    (b.equiv c e₁).trans (c.equiv d e₂) = b.equiv d (e₁.trans e₂) :=
  b.ext_linearIsometryEquiv fun i ↦ by simp

/-- Transporting `b` along `b.equiv c e` produces `c.reindex e.symm`. -/
@[simp]
theorem mapₗᵢ_equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    b.mapₗᵢ (b.equiv c e) = c.reindex e.symm :=
  DFunLike.ext _ _ fun i ↦ by simp

/-- Reindexing the source basis of `HilbertBasis.equiv` composes on the left with `e₁`. -/
@[simp]
theorem reindex_equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis μ 𝕜 F) (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    (b.reindex e₁).equiv c e₂ = b.equiv c (e₁.trans e₂) :=
  b.ext_linearIsometryEquiv fun i ↦ by simpa using (b.reindex e₁).equiv_apply_basis c e₂ (e₁ i)

/-- Reindexing the target basis of `HilbertBasis.equiv` composes on the right with `e₂.symm`. -/
@[simp]
theorem equiv_reindex (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e₁ : ι ≃ μ) (e₂ : κ ≃ μ) :
    b.equiv (c.reindex e₂) e₁ = b.equiv c (e₁.trans e₂.symm) :=
  b.ext_linearIsometryEquiv fun i ↦ by simp

/-- On finite index types, `HilbertBasis.equiv` agrees with `OrthonormalBasis.equiv`. -/
@[simp]
theorem toOrthonormalBasis_equiv [Fintype ι] [Fintype κ] (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    b.toOrthonormalBasis.equiv c.toOrthonormalBasis e = b.equiv c e :=
  b.ext_linearIsometryEquiv fun i ↦ by
    simpa using b.toOrthonormalBasis.equiv_apply_basis c.toOrthonormalBasis e i

/-- Any linear isometric equivalence sending `b i` to `c (e i)` for all `i` equals `b.equiv c e`. -/
theorem eq_equiv_of_forall_apply_eq (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) {U : E ≃ₗᵢ[𝕜] F} (h : ∀ i, U (b i) = c (e i)) :
    U = b.equiv c e :=
  b.ext_linearIsometryEquiv fun i ↦ (h i).trans (b.equiv_apply_basis c e i).symm

/-- Given Hilbert bases `b` of `E` and `c` of `F` and an equivalence `e : ι ≃ κ`, there exists a
unique linear isometric equivalence `U : E ≃ₗᵢ[𝕜] F` satisfying `U (b i) = c (e i)` for every `i`.
-/
theorem existsUnique_linearIsometryEquiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) : ∃! U : E ≃ₗᵢ[𝕜] F, ∀ i, U (b i) = c (e i) :=
  ⟨b.equiv c e, b.equiv_apply_basis c e, fun _ hU ↦ b.eq_equiv_of_forall_apply_eq c e hU⟩

/-- Given Hilbert bases `b` of `E` and `c` of `F` and an equivalence `e : ι ≃ κ`, there exists a
linear isometric equivalence `U : E ≃ₗᵢ[𝕜] F` carrying `b i` to `c (e i)` for every `i`. -/
theorem exists_linearIsometryEquiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) : ∃ U : E ≃ₗᵢ[𝕜] F, ∀ i, U (b i) = c (e i) :=
  ⟨b.equiv c e, b.equiv_apply_basis c e⟩

end HilbertBasis
