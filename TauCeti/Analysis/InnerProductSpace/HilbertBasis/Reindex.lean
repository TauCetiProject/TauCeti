/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Reindexing Hilbert bases and basis-preserving unitary equivalences

Given an index equivalence `e : ι ≃ ι'`, a Hilbert basis `b : HilbertBasis ι 𝕜 E` reindexes to
`b.reindex e : HilbertBasis ι' 𝕜 E` via the coordinate-reindexing linear isometry
`LinearIsometryEquiv.lpCongrLeft`, extending `OrthonormalBasis.reindex` from finite index types to
arbitrary cardinalities.

For two Hilbert bases `b : HilbertBasis ι 𝕜 E` and `c : HilbertBasis ι' 𝕜 F` and an index
equivalence `e : ι ≃ ι'`, composing `b.repr`, `LinearIsometryEquiv.lpCongrLeft`, and `c.repr.symm`
yields the unique linear isometric equivalence `b.equiv c e : E ≃ₗᵢ[𝕜] F` sending `b i` to
`c (e i)` (`HilbertBasis.existsUnique_linearIsometryEquiv`), with convergent series expansion
`x ↦ ∑ᵢ ⟪b i, x⟫ • c (e i)` (`HilbertBasis.hasSum_equiv`). We also name the canonical coordinate
Hilbert basis `lp.hilbertBasisFun` of `ℓ²(ι, 𝕜)`.
-/

public section

open scoped InnerProductSpace lp

namespace lp

/-- The coordinate unit vectors bundled as the canonical Hilbert basis of `ℓ²(ι, 𝕜)`, analogous to
`EuclideanSpace.basisFun`. -/
noncomputable def hilbertBasisFun (ι 𝕜 : Type*) [RCLike 𝕜] : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 ℓ²(ι, 𝕜))

/-- The coordinate representation of `lp.hilbertBasisFun` is the identity linear isometry. -/
@[simp]
theorem repr_hilbertBasisFun (ι 𝕜 : Type*) [RCLike 𝕜] :
    (hilbertBasisFun ι 𝕜).repr = LinearIsometryEquiv.refl 𝕜 ℓ²(ι, 𝕜) :=
  (rfl)

/-- Evaluating `lp.hilbertBasisFun` at `i` returns the coordinate unit vector `lp.single 2 i 1`. -/
@[simp]
theorem hilbertBasisFun_apply (ι 𝕜 : Type*) [RCLike 𝕜] [DecidableEq ι] (i : ι) :
    hilbertBasisFun ι 𝕜 i = lp.single 2 i (1 : 𝕜) := by
  rw [← HilbertBasis.repr_symm_single, repr_hilbertBasisFun]
  rfl

noncomputable instance instInhabitedHilbertBasis (ι 𝕜 : Type*) [RCLike 𝕜] :
    Inhabited (HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) :=
  ⟨hilbertBasisFun ι 𝕜⟩

end lp

namespace HilbertBasis

variable {ι ι' ι'' 𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Two continuous linear maps out of `E` into a `T₂` topological module are equal when they agree
on every member of a Hilbert basis of `E`. -/
theorem ext_continuousLinearMap {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module 𝕜 M]
    [T2Space M] (b : HilbertBasis ι 𝕜 E) {A B : E →L[𝕜] M}
    (h : ∀ i, A (b i) = B (b i)) : A = B := by
  refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
    ?_
  rintro _ ⟨i, rfl⟩
  exact h i

/-- Two linear isometric equivalences out of `E` are equal when they agree on every member of a
Hilbert basis of `E`. -/
theorem ext_linearIsometryEquiv (b : HilbertBasis ι 𝕜 E) {U V : E ≃ₗᵢ[𝕜] F}
    (h : ∀ i, U (b i) = V (b i)) : U = V :=
  LinearIsometryEquiv.toContinuousLinearEquiv_injective <|
    ContinuousLinearEquiv.coe_injective <| b.ext_continuousLinearMap h

/-- Reindex a Hilbert basis along an equivalence `e : ι ≃ ι'`, extending `OrthonormalBasis.reindex`
to arbitrary index types. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    HilbertBasis ι' 𝕜 E :=
  ofRepr (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e))

/-- The coordinate representation of `b.reindex e` is `b.repr` followed by
`LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e`. -/
@[simp]
theorem repr_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).repr = b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e) :=
  (rfl)

/-- Evaluating `b.reindex e` at `j` returns `b (e.symm j)`. -/
@[simp]
theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (j : ι') :
    b.reindex e j = b (e.symm j) := by
  classical
  simp only [← HilbertBasis.repr_symm_single, repr_reindex, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.lpCongrLeft_symm,
    LinearIsometryEquiv.lpCongrLeft_single]

/-- Function-level form of `HilbertBasis.reindex_apply`. -/
@[simp]
theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

/-- Reindexing along the identity equivalence leaves a Hilbert basis unchanged. -/
@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along two equivalences in succession equals reindexing along their composition. -/
@[simp]
theorem reindex_trans (b : HilbertBasis ι 𝕜 E) (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'') :
    (b.reindex e₁).reindex e₂ = b.reindex (e₁.trans e₂) :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along `e` and then along `e.symm` recovers the original Hilbert basis. -/
theorem reindex_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).reindex e.symm = b := by
  simp

/-- Reindexing along `e.symm` and then along `e` recovers the original Hilbert basis. -/
theorem reindex_symm_self (b : HilbertBasis ι' 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e.symm).reindex e = b := by
  simp

/-- Transporting across a linear isometric equivalence commutes with reindexing. -/
theorem mapₗᵢ_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (U : E ≃ₗᵢ[𝕜] F) :
    (b.reindex e).mapₗᵢ U = (b.mapₗᵢ U).reindex e :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- On finite index types, `HilbertBasis.reindex` agrees with `OrthonormalBasis.reindex` under
`HilbertBasis.toOrthonormalBasis`. -/
@[simp]
theorem toOrthonormalBasis_reindex [Fintype ι] [Fintype ι'] (b : HilbertBasis ι 𝕜 E)
    (e : ι ≃ ι') :
    (b.reindex e).toOrthonormalBasis = b.toOrthonormalBasis.reindex e :=
  DFunLike.ext _ _ fun _ ↦ by simp [HilbertBasis.coe_toOrthonormalBasis]

/-- The linear isometric equivalence `E ≃ₗᵢ[𝕜] F` sending a Hilbert basis `b` to `c` along an index
equivalence `e : ι ≃ ι'`. -/
protected noncomputable def equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F)
    (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] F :=
  b.repr.trans ((LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e).trans c.repr.symm)

/-- The `j`th `c`-coordinate of `b.equiv c e x` is the `(e.symm j)`th `b`-coordinate of `x`. -/
@[simp]
theorem repr_equiv_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) (e : ι ≃ ι')
    (x : E) (j : ι') :
    c.repr (b.equiv c e x) j = b.repr x (e.symm j) := by
  simp [HilbertBasis.equiv]

/-- `b.equiv c e` sends the `i`th vector of `b` to the `(e i)`th vector of `c`. -/
@[simp]
theorem equiv_apply_basis (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) (e : ι ≃ ι')
    (i : ι) :
    b.equiv c e (b i) = c (e i) := by
  classical
  simp [HilbertBasis.equiv, b.repr_self]

/-- Unconditional series expansion of `b.equiv c e x` as `∑ᵢ ⟪b i, x⟫ • c (e i)`. -/
theorem hasSum_equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) (e : ι ≃ ι') (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • c (e i)) (b.equiv c e x) := by
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    b.equiv_apply_basis c e] using
    b.hasSum_inner_smul_apply (b.equiv c e).toContinuousLinearEquiv.toContinuousLinearMap x

/-- The inverse of `b.equiv c e` is `c.equiv b e.symm`. -/
@[simp]
theorem equiv_symm (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) (e : ι ≃ ι') :
    (b.equiv c e).symm = c.equiv b e.symm :=
  c.ext_linearIsometryEquiv fun j ↦
    (b.equiv c e).injective <| by simp

/-- `b.equiv b (Equiv.refl ι)` is the identity linear isometry on `E`. -/
@[simp]
theorem equiv_refl (b : HilbertBasis ι 𝕜 E) :
    b.equiv b (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  b.ext_linearIsometryEquiv fun i ↦ by simp

/-- Composing two basis-preserving unitaries corresponds to composing their index equivalences. -/
@[simp]
theorem equiv_trans (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) (d : HilbertBasis ι'' 𝕜 G)
    (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'') :
    (b.equiv c e₁).trans (c.equiv d e₂) = b.equiv d (e₁.trans e₂) :=
  b.ext_linearIsometryEquiv fun i ↦ by simp

/-- Transporting `b` along `b.equiv c e` produces `c.reindex e.symm`. -/
@[simp]
theorem mapₗᵢ_equiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) (e : ι ≃ ι') :
    b.mapₗᵢ (b.equiv c e) = c.reindex e.symm :=
  DFunLike.ext _ _ fun i ↦ by simp

/-- Any linear isometric equivalence sending `b i` to `c (e i)` for all `i` equals `b.equiv c e`. -/
theorem eq_equiv_of_forall_apply_eq (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F)
    (e : ι ≃ ι') {U : E ≃ₗᵢ[𝕜] F} (hU : ∀ i, U (b i) = c (e i)) :
    U = b.equiv c e :=
  b.ext_linearIsometryEquiv fun i ↦ (hU i).trans (b.equiv_apply_basis c e i).symm

/-- For Hilbert bases `b` of `E` and `c` of `F` and an equivalence `e : ι ≃ ι'`, there is a unique
linear isometric equivalence `U : E ≃ₗᵢ[𝕜] F` satisfying `U (b i) = c (e i)` for all `i`. -/
theorem existsUnique_linearIsometryEquiv (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F)
    (e : ι ≃ ι') :
    ∃! U : E ≃ₗᵢ[𝕜] F, ∀ i, U (b i) = c (e i) :=
  ⟨b.equiv c e, b.equiv_apply_basis c e, fun _ hU ↦ b.eq_equiv_of_forall_apply_eq c e hU⟩

end HilbertBasis
