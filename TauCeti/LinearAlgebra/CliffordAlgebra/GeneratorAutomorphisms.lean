/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Clifford automorphisms that preserve the vectors

An isometry `f` of quadratic forms induces the algebra equivalence
`CliffordAlgebra.equivOfIsometry f`, which maps the vectors `LinearMap.range (ι Q₁)` onto the
vectors `LinearMap.range (ι Q₂)`. This file proves the converse: an algebra equivalence of
Clifford algebras that maps the vectors onto the vectors is induced by a unique isometry. The
isometry is read off on generators through `CliffordAlgebra.ιRangeEquiv`, and the generator
square `ι v * ι v = Q v` forces it to preserve the forms. No hypothesis on the forms is needed,
only that `2` is invertible: degenerate forms, and the exterior algebra of the zero form, are
included.

For a single form `Q`, the algebra automorphisms that map the vectors onto themselves form a
subgroup `CliffordAlgebra.vectorStabilizer Q` of all algebra automorphisms (the stabilizer of the
vectors under the pointwise action), and `equivOfIsometry` identifies it with the orthogonal
group of `Q`.

The condition can be read on the degree filtration `CliffordAlgebra.filtration`. Preserving the
vectors is equivalent to preserving its first step `R ⊕ M`, and to preserving every step. The
first equivalence needs the scalars not to leak into the vectors: if `φ (ι v) = r + ι t`, the
vector part of the generator square is `2 r • t`, and when `R` is reduced this forces `r = 0`.

## Main definitions

* `CliffordAlgebra.isometryEquivOfιRangeMap`: the isometry underlying an algebra equivalence
  that maps the vectors onto the vectors.
* `CliffordAlgebra.vectorStabilizer`: the group of algebra automorphisms of `CliffordAlgebra Q`
  that map the vectors onto themselves.
* `CliffordAlgebra.orthogonalGroupEquivVectorStabilizer`: the group isomorphism from the
  orthogonal group of `Q` onto `vectorStabilizer Q`, given by `equivOfIsometry`.

## Main results

* `CliffordAlgebra.ι_range_map_eq_iff_existsUnique`: an algebra equivalence maps the vectors onto
  the vectors if and only if it is `equivOfIsometry f` for a unique isometry `f`.
* `CliffordAlgebra.equivOfIsometry_injective`: different isometries induce different algebra
  equivalences.
* `CliffordAlgebra.filtration_one_map_eq_iff`: an algebra equivalence maps the first filtration
  step onto the first filtration step if and only if it maps the vectors onto the vectors, when
  `R` is reduced.
* `CliffordAlgebra.forall_filtration_map_eq_iff`: an algebra map preserves every filtration step
  if and only if it preserves the first one.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.3 and Theorem 1.4.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open QuadraticMap
open scoped Pointwise

universe u v w

namespace CliffordAlgebra

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Two algebra equivalences out of a Clifford algebra agree when they agree on the generators. -/
private theorem algEquiv_ext_ι {φ ψ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂}
    (h : ∀ v, φ (ι Q₁ v) = ψ (ι Q₁ v)) : φ = ψ :=
  AlgEquiv.coe_toAlgHom_injective <| hom_ext <| LinearMap.ext h

/-! ### The vector stabilizer -/

section VectorStabilizer

variable (Q : QuadraticForm R M₁)

/-- The algebra automorphisms of `CliffordAlgebra Q` that map the vectors
`LinearMap.range (ι Q)` onto themselves: the stabilizer of the vectors under the pointwise action
of the automorphism group on submodules.

When `2` is invertible, `CliffordAlgebra.orthogonalGroupEquivVectorStabilizer` identifies these
with the automorphisms `equivOfIsometry f` induced by the isometries of `Q`. -/
def vectorStabilizer : Subgroup (CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) :=
  MulAction.stabilizer _ (LinearMap.range (ι Q))

variable {Q} in
/-- An automorphism lies in the vector stabilizer when it maps the vectors onto themselves. -/
@[simp]
theorem mem_vectorStabilizer_iff {φ : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q} :
    φ ∈ vectorStabilizer Q ↔
      (LinearMap.range (ι Q)).map φ.toLinearMap = LinearMap.range (ι Q) := by
  rw [vectorStabilizer, MulAction.mem_stabilizer_iff, Submodule.pointwise_smul_def]
  -- The pointwise action applies `φ` through its scalar action, `AlgEquiv.smul_def`.
  exact Iff.of_eq <| congrArg (fun g ↦ Submodule.map g (LinearMap.range (ι Q)) = _) <|
    LinearMap.ext fun x ↦ AlgEquiv.smul_def φ x

end VectorStabilizer

/-! ### The filtration criteria -/

/-- **An algebra map preserves every step of the degree filtration as soon as it preserves the
first.** Each step `filtration Q k` is the `k`-th power of the first one. -/
theorem forall_filtration_map_eq_iff (g : CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra Q₂) :
    (∀ k, (filtration Q₁ k).map g.toLinearMap = filtration Q₂ k) ↔
      (filtration Q₁ 1).map g.toLinearMap = filtration Q₂ 1 := by
  refine ⟨fun h ↦ h 1, fun h k ↦ TauCeti.Algebra.map_wordFiltration_eq (ι Q₁) g (ι Q₂) ?_ k⟩
  rwa [← TauCeti.Algebra.wordFiltration_one, ← TauCeti.Algebra.wordFiltration_one]

/-- The square of an element `r + ι Q t` of the first filtration step: its vector part is
`ι Q ((2 * r) • t)`. -/
theorem algebraMap_add_ι_mul_self (Q : QuadraticForm R M₂) (r : R) (t : M₂) :
    (algebraMap R (CliffordAlgebra Q) r + ι Q t) * (algebraMap R _ r + ι Q t) =
      algebraMap R _ (r * r + Q t) + ι Q ((2 * r) • t) := by
  rw [add_mul, mul_add, mul_add, ι_sq_scalar, ← map_mul, ← Algebra.commutes r (ι Q t),
    ← Algebra.smul_def, map_add, map_smul, mul_smul, two_smul]
  abel

variable [Invertible (2 : R)]

/-- **An injective algebra map sending a generator into the first filtration step sends it to a
vector**, when the base ring is reduced. Writing `g (ι Q₁ v) = r + ι Q₂ t`, the vector part of the
generator square `g (ι Q₁ v) ^ 2 = Q₁ v` is `ι Q₂ ((2 * r) • t)`, which must vanish. Then
`g (ι Q₁ (r • v)) = r * r` is a scalar, so `ι Q₁ (r • v)` is one too, and `r * r = 0`.

Both hypotheses on `R` are needed. In characteristic `2`, over `𝔽₄ = 𝔽₂(ω)`, the Clifford algebra
of `x ↦ x²` on a line has the automorphism `e ↦ ω + ω² e`. Over the dual numbers
`R = K[δ] ⧸ (δ²)`, the exterior algebra `R ⊕ K` of `K = R ⧸ (δ)` has the automorphism
`r + ι m ↦ r + δ m + ι m`. -/
theorem apply_ι_mem_range_ι_of_mem_filtration_one [IsReduced R]
    {g : CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra Q₂} (hg : Function.Injective g) {v : M₁}
    (hv : g (ι Q₁ v) ∈ filtration Q₂ 1) : g (ι Q₁ v) ∈ LinearMap.range (ι Q₂) := by
  rw [← range_scalarAddVector] at hv
  obtain ⟨⟨r, t⟩, hrt⟩ := hv
  simp only [scalarAddVector_apply] at hrt
  have hsq : ι Q₂ ((2 * r) • t) = algebraMap R _ (Q₁ v - (r * r + Q₂ t)) := by
    rw [map_sub, ← AlgHom.commutes g, ← ι_sq_scalar, map_mul, ← hrt, algebraMap_add_ι_mul_self]
    abel
  have hrt0 : r • t = 0 := by
    rw [← (isUnit_of_invertible (2 : R)).smul_eq_zero, smul_smul]
    exact ((ι_eq_algebraMap_iff Q₂ _ _).mp hsq).1
  have hrv : g (ι Q₁ (r • v)) = g (algebraMap R _ (r * r)) := by
    rw [map_smul, map_smul, ← hrt, smul_add, ← map_smul (ι Q₂), hrt0, map_zero, add_zero,
      Algebra.smul_def, ← map_mul, AlgHom.commutes]
  have hr : r = 0 :=
    IsNilpotent.eq_zero ⟨2, by rw [pow_two]; exact ((ι_eq_algebraMap_iff Q₁ _ _).mp (hg hrv)).2⟩
  exact ⟨t, by rw [← hrt, hr, map_zero, zero_add]⟩

/-- **The first filtration step detects the vector-preserving equivalences.** An algebra
equivalence of Clifford algebras maps the first filtration step `R ⊕ M₁` onto `R ⊕ M₂` if and
only if it maps the vectors onto the vectors, when `R` is reduced; see
`CliffordAlgebra.apply_ι_mem_range_ι_of_mem_filtration_one` for why the hypotheses on `R` are
needed. No hypothesis on the forms or the modules is needed. -/
theorem filtration_one_map_eq_iff [IsReduced R]
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂) :
    (filtration Q₁ 1).map φ.toLinearMap = filtration Q₂ 1 ↔
      (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hle : (LinearMap.range (ι Q₁)).map φ.toLinearMap ≤ LinearMap.range (ι Q₂) := by
      rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      exact apply_ι_mem_range_ι_of_mem_filtration_one (g := φ.toAlgHom) φ.injective
        (h ▸ Submodule.mem_map_of_mem (ι_mem_filtration_one Q₁ v))
    refine le_antisymm hle ?_
    -- A vector `ι Q₂ t` is `φ (r + ι Q₁ u)` with `φ (ι Q₁ u)` a vector `ι Q₂ s`, so the scalar
    -- `r` is the vector `ι Q₂ (t - s)` and vanishes.
    rintro _ ⟨t, rfl⟩
    obtain ⟨x, hx, hxt⟩ := h.symm ▸ ι_mem_filtration_one Q₂ t
    rw [← range_scalarAddVector] at hx
    obtain ⟨⟨r, u⟩, rfl⟩ := hx
    obtain ⟨s, hs⟩ := hle ⟨ι Q₁ u, ⟨u, rfl⟩, rfl⟩
    rw [AlgEquiv.toLinearMap_apply, scalarAddVector_apply, map_add, AlgEquiv.commutes] at hxt
    rw [AlgEquiv.toLinearMap_apply] at hs
    have hr : ι Q₂ (t - s) = algebraMap R _ r := by
      rw [map_sub, hs, ← hxt, add_sub_cancel_right]
    rw [((ι_eq_algebraMap_iff Q₂ _ _).mp hr).2, map_zero, zero_add, ← hs] at hxt
    exact ⟨ι Q₁ u, ⟨u, rfl⟩, by rw [AlgEquiv.toLinearMap_apply, ← hs, hxt]⟩
  · rw [filtration_eq_pow, filtration_eq_pow, pow_one, pow_one, Submodule.map_sup, h]
    -- `φ.toLinearMap` is the linear map underlying the algebra map `φ.toAlgHom`.
    exact congrArg (· ⊔ LinearMap.range (ι Q₂)) (Submodule.map_one φ.toAlgHom)

/-! ### The isometry underlying a vector-preserving equivalence -/

/-- The restriction of `φ` to the vectors, transported along `CliffordAlgebra.ιRangeEquiv`. -/
private noncomputable def ιRangeMapLinearEquiv
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) : M₁ ≃ₗ[R] M₂ :=
  (ιRangeEquiv Q₁).trans <|
    (φ.toLinearEquiv.submoduleMap _).trans <|
      (LinearEquiv.ofEq _ _ (by rw [AlgEquiv.toLinearEquiv_toLinearMap, h])).trans
        (ιRangeEquiv Q₂).symm

private theorem ι_ιRangeMapLinearEquiv (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) (v : M₁) :
    ι Q₂ (ιRangeMapLinearEquiv φ h v) = φ (ι Q₁ v) := by
  rw [ιRangeMapLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, ι_ιRangeEquiv_symm_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.submoduleMap_apply, coe_ιRangeEquiv_apply, AlgEquiv.toLinearEquiv_apply]

private theorem map_app_ιRangeMapLinearEquiv
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) (v : M₁) :
    Q₂ (ιRangeMapLinearEquiv φ h v) = Q₁ v := by
  -- Both scalars are the square of the same element `φ (ι Q₁ v)`.
  apply algebraMap_injective Q₂
  rw [← ι_sq_scalar, ι_ιRangeMapLinearEquiv, ← map_mul, ι_sq_scalar, AlgEquiv.commutes]

/-- An algebra equivalence of Clifford algebras that maps the vectors of `Q₁` onto the vectors of
`Q₂` restricts to an isometry from `Q₁` to `Q₂`: the vector `f v` is characterized by
`ι Q₂ (f v) = φ (ι Q₁ v)` (`CliffordAlgebra.ι_isometryEquivOfιRangeMap`).

The linear equivalence is the restriction of `φ` to the vectors, transported along
`CliffordAlgebra.ιRangeEquiv`; the generator squares show that it preserves the forms. -/
noncomputable def isometryEquivOfιRangeMap (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) :
    Q₁.IsometryEquiv Q₂ where
  toLinearEquiv := ιRangeMapLinearEquiv φ h
  map_app' := map_app_ιRangeMapLinearEquiv φ h

/-- **The defining equation** of `CliffordAlgebra.isometryEquivOfιRangeMap`: on generators it is
the algebra equivalence it comes from. -/
@[simp]
theorem ι_isometryEquivOfιRangeMap (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) (v : M₁) :
    ι Q₂ (isometryEquivOfιRangeMap φ h v) = φ (ι Q₁ v) :=
  ι_ιRangeMapLinearEquiv φ h v

/-- An algebra equivalence that maps the vectors onto the vectors is induced by the isometry it
restricts to. -/
@[simp]
theorem equivOfIsometry_isometryEquivOfιRangeMap
    (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂)
    (h : (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂)) :
    equivOfIsometry (isometryEquivOfιRangeMap φ h) = φ :=
  algEquiv_ext_ι fun v ↦ by
    rw [equivOfIsometry_apply, map_apply_ι, IsometryEquiv.toIsometry_apply,
      ι_isometryEquivOfιRangeMap]

/-- The isometry underlying `equivOfIsometry e` is `e`. -/
@[simp]
theorem isometryEquivOfιRangeMap_equivOfIsometry (e : Q₁.IsometryEquiv Q₂) :
    isometryEquivOfιRangeMap (equivOfIsometry e) (ι_range_map_equivOfIsometry e) = e :=
  DFunLike.ext _ _ fun v ↦ ι_injective Q₂ <| by
    rw [ι_isometryEquivOfιRangeMap, equivOfIsometry_apply, map_apply_ι,
      IsometryEquiv.toIsometry_apply]

/-- **Different isometries induce different Clifford algebra equivalences**: an isometry is
recovered from the algebra equivalence it induces by restricting it to the vectors. -/
theorem equivOfIsometry_injective :
    Function.Injective (equivOfIsometry : Q₁.IsometryEquiv Q₂ → _) := fun e e' h ↦ by
  rw [← isometryEquivOfιRangeMap_equivOfIsometry e, ← isometryEquivOfιRangeMap_equivOfIsometry e']
  simp only [h]

/-- Two isometries induce the same Clifford algebra equivalence only if they are equal. -/
@[simp]
theorem equivOfIsometry_inj {e e' : Q₁.IsometryEquiv Q₂} :
    equivOfIsometry e = equivOfIsometry e' ↔ e = e' :=
  equivOfIsometry_injective.eq_iff

/-- **The isometry criterion for Clifford algebra equivalences.** An algebra equivalence
`CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂` maps the vectors of `Q₁` onto the vectors of `Q₂`
if and only if it is `equivOfIsometry f` for a unique isometry `f`. No hypothesis on the forms is
needed: they may be degenerate, or zero. -/
theorem ι_range_map_eq_iff_existsUnique (φ : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂) :
    (LinearMap.range (ι Q₁)).map φ.toLinearMap = LinearMap.range (ι Q₂) ↔
      ∃! f : Q₁.IsometryEquiv Q₂, equivOfIsometry f = φ := by
  refine ⟨fun h ↦ ⟨isometryEquivOfιRangeMap φ h,
    equivOfIsometry_isometryEquivOfιRangeMap φ h, fun f hf ↦ ?_⟩, ?_⟩
  · rw [← equivOfIsometry_inj, hf, equivOfIsometry_isometryEquivOfιRangeMap]
  · rintro ⟨f, rfl, -⟩
    exact ι_range_map_equivOfIsometry f

/-! ### The vector stabilizer and the orthogonal group -/

variable (Q : QuadraticForm R M₁)

/-- **The vector stabilizer is the orthogonal group.** The automorphism `equivOfIsometry f`
induced by an orthogonal automorphism `f` of `Q` maps the vectors onto themselves, and every
automorphism that does arises from exactly one `f`; composition of automorphisms corresponds to
composition of isometries. -/
noncomputable def orthogonalGroupEquivVectorStabilizer :
    TauCeti.QuadraticMap.orthogonalGroup Q ≃* vectorStabilizer Q where
  toFun f := ⟨equivOfIsometry (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q f),
    mem_vectorStabilizer_iff.mpr (ι_range_map_equivOfIsometry _)⟩
  invFun φ := (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm
    (isometryEquivOfιRangeMap φ.1 (mem_vectorStabilizer_iff.mp φ.2))
  left_inv f := by simp only [isometryEquivOfιRangeMap_equivOfIsometry, Equiv.symm_apply_apply]
  right_inv φ := Subtype.ext <| by
    simp only [Equiv.apply_symm_apply, equivOfIsometry_isometryEquivOfιRangeMap]
  map_mul' f g := Subtype.ext <| algEquiv_ext_ι fun v ↦ by
    simp [equivOfIsometry_apply]

/-- The automorphism attached to an orthogonal automorphism `f` is `equivOfIsometry f`. -/
@[simp]
theorem coe_orthogonalGroupEquivVectorStabilizer_apply
    (f : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (orthogonalGroupEquivVectorStabilizer Q f : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) =
      equivOfIsometry (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q f) := by
  rw [orthogonalGroupEquivVectorStabilizer, MulEquiv.coe_mk, Equiv.coe_fn_mk]

/-- On generators, `orthogonalGroupEquivVectorStabilizer Q f` applies `f`. -/
theorem orthogonalGroupEquivVectorStabilizer_apply_ι
    (f : TauCeti.QuadraticMap.orthogonalGroup Q) (v : M₁) :
    (orthogonalGroupEquivVectorStabilizer Q f : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q)
      (ι Q v) = ι Q ((f : M₁ ≃ₗ[R] M₁) v) := by
  simp [equivOfIsometry_apply]

/-- The orthogonal automorphism underlying `φ ∈ vectorStabilizer Q` is characterized by its
action on generators. -/
@[simp]
theorem ι_orthogonalGroupEquivVectorStabilizer_symm_apply (φ : vectorStabilizer Q) (v : M₁) :
    ι Q (((orthogonalGroupEquivVectorStabilizer Q).symm φ : M₁ ≃ₗ[R] M₁) v) =
      (φ : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q) (ι Q v) := by
  simp only [orthogonalGroupEquivVectorStabilizer, MulEquiv.symm_mk, MulEquiv.coe_mk,
    Equiv.coe_fn_symm_mk, TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv_symm,
    ι_isometryEquivOfιRangeMap]

/-- The vector stabilizer consists of the automorphisms `equivOfIsometry f`. -/
theorem mem_vectorStabilizer_iff_exists {φ : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q} :
    φ ∈ vectorStabilizer Q ↔ ∃ f : Q.IsometryEquiv Q, equivOfIsometry f = φ := by
  rw [mem_vectorStabilizer_iff, ι_range_map_eq_iff_existsUnique]
  exact ⟨ExistsUnique.exists, fun ⟨f, hf⟩ ↦ ⟨f, hf, fun g hg ↦ equivOfIsometry_injective
    (hg.trans hf.symm)⟩⟩

end CliffordAlgebra
