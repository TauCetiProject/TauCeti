/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The real points of a conjugate-linear involution

A **conjugation** of a complex vector space `V` is a conjugate-linear map `K : V → V` with
`K ∘ K = id`, that is, a `starRingEnd ℂ`-semilinear self-map that is involutive.  Its **real
points** are the vectors it fixes.  They form a real subspace `TauCeti.realPoints K`, and the main
theorem of this file is that `V` is the complexification of that subspace: the canonical map

`ℂ ⊗[ℝ] realPoints K → V`, `c ⊗ₜ w ↦ c • w`

is a `ℂ`-linear isomorphism.  Conversely a complexification `ℂ ⊗[ℝ] W` carries the conjugation
`c ⊗ₜ w ↦ conj c ⊗ₜ w` (`TauCeti.tmulConj`), whose real points are the image of `W`.  So each of
the two constructions produces the other: a conjugation on `V` presents `V` as a complexification,
and a complexification carries a conjugation.  That is what makes conjugations the tool for
realizing an object over `ℝ`.

The canonical `TauCeti.realPointsEquiv` intertwines `TauCeti.tmulConj` with the original
conjugation `K`. For a chosen presentation `ℂ ⊗[ℝ] W ≃ₗ[ℂ] V`,
`LinearEquiv.conjugationOfComplexification` transports the existing tensor conjugation through
that equivalence. Its exact fixed locus is the image of the real inclusion. The equivariant
application is `Representation.IsRealForm.exists_isRealStructure`, downstream in
`TauCeti.RepresentationTheory.RealForm`.

Everything is stated for an arbitrary `V`; no finite-dimensionality is used anywhere.

## Main definitions

* `TauCeti.realPoints`: the real points of a conjugate-linear map, as a `Submodule ℝ V`.
* `TauCeti.conjRealPart` and `TauCeti.conjImaginaryPart`: the two real points a vector decomposes
  into; `TauCeti.conjRealPart_def` and `TauCeti.conjImaginaryPart_def` are their defining formulas.
* `TauCeti.realPointsLift`: the canonical `ℂ`-linear map `ℂ ⊗[ℝ] realPoints K →ₗ[ℂ] V`.
* `TauCeti.realPointsEquiv`: that map as a `ℂ`-linear isomorphism, for involutive `K`.
* `TauCeti.tmulConj`: the conjugation `c ⊗ₜ w ↦ conj c ⊗ₜ w` of a complexification `ℂ ⊗[ℝ] W`.
* `TauCeti.realPart` and `TauCeti.imaginaryPart`: the two real coordinates of a vector of a
  complexification, bundled as `TauCeti.complexificationLinearEquivProd`;
  `TauCeti.one_tmul_realPart_add_I_tmul_imaginaryPart` reassembles it, and
  `TauCeti.complexification_ext` says the two coordinates determine the vector.
* `LinearEquiv.conjugationOfComplexification`: the tensor conjugation transported through a
  complexification equivalence `ℂ ⊗[ℝ] W ≃ₗ[ℂ] V`.

## Main statements

* `TauCeti.conjRealPart_add_I_smul_conjImaginaryPart`: the decomposition
  `v = conjRealPart K v + I • conjImaginaryPart K v`, which makes `TauCeti.realPointsLift`
  surjective.
* `TauCeti.realPointsLift_injective`, `TauCeti.realPointsLift_surjective` and
  `TauCeti.realPointsEquiv`: **a complex vector space is the complexification of the real points of
  any conjugation on it.**
* `TauCeti.span_realPoints_eq_top`: the real points of an involutive conjugation span `V` over
  `ℂ`, so an identity between `ℂ`-linear or `ℂ`-bilinear maps may be checked on real vectors
  alone.
* `TauCeti.finrank_realPoints`: the real points have the `ℝ`-dimension that `V` has over `ℂ`.
* `TauCeti.finrank_selfAdjoint_submodule`: in particular, the self-adjoint elements of a complex
  star module have the `ℝ`-dimension that the module has over `ℂ`.
* `TauCeti.exists_one_tmul_add_I_tmul`: every element of `ℂ ⊗[ℝ] W` is `1 ⊗ₜ w₁ + I ⊗ₜ w₂`; this
  is what makes the lift injective.
* `LinearMap.liftBaseChange_complex_injective_of_conj`: more generally, an injective real-linear
  map whose values a conjugate-linear map fixes induces an injective map on the complexification,
  for any real structure compatible with the complex one.
* `TauCeti.tmulConj_involutive`, `TauCeti.tmulConj_tmul` and `TauCeti.tmulConj_eq_self_iff`: the
  conjugation of a complexification and its real points.
* `TauCeti.realPointsEquiv_tmulConj`: the canonical real-descent equivalence intertwines
  tensor conjugation with `K`.
* `TauCeti.tmulConj_baseChange`: that conjugation commutes with every base-changed map, which is
  what makes it equivariant for a base-changed action.
* `LinearEquiv.conjugationOfComplexification_apply_tmul`: the transported conjugation sends
  `e (c ⊗ₜ w)` to `e (star c ⊗ₜ w)`.
* `LinearEquiv.conjugationOfComplexification_eq_self_iff`,
  `LinearEquiv.conjugationOfComplexification_unique` and
  `LinearEquiv.conjugationOfComplexification_natural`: the transported conjugation fixes exactly
  the image of the real inclusion, is the only conjugate-linear map doing so, and commutes with
  complex-linear maps carrying one real inclusion to another.

## Implementation notes

A conjugation is carried here as the two unbundled hypotheses `K : V →ₛₗ[starRingEnd ℂ] V` and
`Function.Involutive K`, rather than as a bundled structure.  `TauCeti.Hodge.Conjugation` already
bundles exactly this data, but it lives downstream in `TauCeti/Geometry/Hodge/`, so bundling here
would either duplicate it or invert the dependency between `TauCeti.LinearAlgebra` and
`TauCeti.Geometry`; a `TauCeti.Hodge.Conjugation` supplies the hypotheses below from its two
fields.  For the same reason `TauCeti.realPoints` asks only for the semilinear map: the subspace
makes sense without involutivity, and only the complexification theorem needs it.

Mathlib's `realPart`/`imaginaryPart` decomposition of a star module over `ℂ` is the same
mathematics, but it reads the conjugation off the `Star` *instance* on `V`: `selfAdjoint.submodule`
and `realPart` both ask for `[StarAddMonoid V] [StarModule ℂ V]`, and `StarAddMonoid` already
carries involutivity.  Here the conjugation is instead a term `K` that `TauCeti.realPoints` and
`TauCeti.conjRealPart` are indexed by, because one `V` carries many conjugations and
`TauCeti.realPoints` is wanted before `K` is known to be involutive -- `TauCeti.realPointsLift` is
injective for every conjugate-linear `K`.  So the instance-borne spelling is not available here,
and a `TauCeti.Hodge.Conjugation`, or a `Representation.IsRealStructure`, hands its conjugation
over as a field rather than as an instance.

No definition here exposes its body: `TauCeti.mem_realPoints`, `TauCeti.conjRealPart_def`,
`TauCeti.conjImaginaryPart_def`, `TauCeti.realPointsLift_tmul`, `TauCeti.realPointsEquiv_tmul`,
`TauCeti.realPointsEquiv_symm_apply` and `TauCeti.tmulConj_tmul` are the characterizations a
consumer works from.

The real scalar structure on `V` is Mathlib's `Module.complexToReal`, the one `Module ℂ V` induces,
so `r • v` and `(r : ℂ) • v` are definitionally equal and no scalar tower hypothesis is carried.
The injectivity argument `LinearMap.liftBaseChange_complex_injective_of_conj` is the exception: it
takes an arbitrary real structure with `IsScalarTower ℝ ℂ E`, so that it also serves spaces such
as `Matrix n n ℂ` whose real structure is not syntactically `Module.complexToReal`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, where the
  conjugation attached to an invariant form realizes a representation over `ℝ`.
-/

public section

open scoped TensorProduct

open Module (finrank)

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ### The real points of a conjugate-linear map -/

/-- The **real points** of a conjugate-linear map `K : V → V`: the vectors `K` fixes.  They form a
subspace over `ℝ` but not over `ℂ`, since `K (c • v) = conj c • K v`. -/
def realPoints (K : V →ₛₗ[starRingEnd ℂ] V) : Submodule ℝ V where
  carrier := {v | K v = v}
  add_mem' {v w} (hv : K v = v) (hw : K w = w) := by
    rw [Set.mem_ofPred_eq, map_add, hv, hw]
  zero_mem' := map_zero K
  smul_mem' r v (hv : K v = v) := by
    -- `Complex.coe_smul` turns the `ℝ`-action of `Module.complexToReal` into the `ℂ`-action, the
    -- one the semilinearity of `K` speaks about.
    rw [Set.mem_ofPred_eq, ← Complex.coe_smul r, map_smulₛₗ, Complex.conj_ofReal, hv]

@[simp]
theorem mem_realPoints {K : V →ₛₗ[starRingEnd ℂ] V} {v : V} :
    v ∈ realPoints K ↔ K v = v :=
  (Iff.rfl)

variable {K : V →ₛₗ[starRingEnd ℂ] V}

private theorem add_conj_mem_realPoints (hK : Function.Involutive K) (v : V) :
    v + K v ∈ realPoints K := by
  rw [mem_realPoints, map_add, hK v, add_comm]

private theorem I_smul_conj_sub_mem_realPoints (hK : Function.Involutive K) (v : V) :
    Complex.I • (K v - v) ∈ realPoints K := by
  rw [mem_realPoints, map_smulₛₗ, map_sub, hK v, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

variable (K) in
/-- The **real part** of `v` relative to a conjugate-linear map: the vector `½ (v + K v)`, a real
point once `K` is involutive (`TauCeti.conjRealPart_mem`). -/
noncomputable def conjRealPart (v : V) : V := (2⁻¹ : ℝ) • (v + K v)

variable (K) in
/-- The **imaginary part** of `v` relative to a conjugate-linear map: the vector
`½ I • (K v - v)`, the coefficient of `I` in
`TauCeti.conjRealPart_add_I_smul_conjImaginaryPart`. -/
noncomputable def conjImaginaryPart (v : V) : V := (2⁻¹ : ℝ) • (Complex.I • (K v - v))

/-- The defining formula for the real part, the body of `TauCeti.conjRealPart` not being exposed. -/
theorem conjRealPart_def (v : V) : conjRealPart K v = (2⁻¹ : ℝ) • (v + K v) := (rfl)

/-- The defining formula for the imaginary part, the body of `TauCeti.conjImaginaryPart` not being
exposed. -/
theorem conjImaginaryPart_def (v : V) :
    conjImaginaryPart K v = (2⁻¹ : ℝ) • (Complex.I • (K v - v)) := (rfl)

theorem conjRealPart_mem (hK : Function.Involutive K) (v : V) : conjRealPart K v ∈ realPoints K :=
  Submodule.smul_mem _ _ (add_conj_mem_realPoints hK v)

theorem conjImaginaryPart_mem (hK : Function.Involutive K) (v : V) :
    conjImaginaryPart K v ∈ realPoints K :=
  Submodule.smul_mem _ _ (I_smul_conj_sub_mem_realPoints hK v)

/-- A real point is its own real part. -/
@[simp]
theorem conjRealPart_of_mem {v : V} (hv : v ∈ realPoints K) : conjRealPart K v = v := by
  rw [mem_realPoints] at hv
  rw [conjRealPart_def, hv, ← two_smul ℝ v, smul_smul]
  norm_num

/-- A real point has vanishing imaginary part. -/
@[simp]
theorem conjImaginaryPart_of_mem {v : V} (hv : v ∈ realPoints K) : conjImaginaryPart K v = 0 := by
  rw [mem_realPoints] at hv
  rw [conjImaginaryPart_def, hv, sub_self, smul_zero, smul_zero]

/-- **The decomposition into real points**: every vector is its real part plus `I` times its
imaginary part.  Once `K` is involutive both summands lie in `TauCeti.realPoints K`, so this is
what exhibits `V` as the complexification of that subspace. -/
theorem conjRealPart_add_I_smul_conjImaginaryPart (v : V) :
    conjRealPart K v + Complex.I • conjImaginaryPart K v = v := by
  have hI : Complex.I • (Complex.I • (K v - v)) = v - K v := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_sub]
  have hsum : (v + K v) + (v - K v) = (2 : ℝ) • v := by
    rw [two_smul]
    abel
  rw [conjRealPart_def, conjImaginaryPart_def, smul_comm Complex.I ((2⁻¹ : ℝ)), hI, ← smul_add,
    hsum, smul_smul]
  norm_num

/-- **The real points of a conjugation span the whole space over `ℂ`.**  Every vector is a
complex combination of the two real points it decomposes into, so an identity between `ℂ`-linear
or `ℂ`-bilinear maps may be checked on real vectors alone. -/
theorem span_realPoints_eq_top (hK : Function.Involutive K) :
    Submodule.span ℂ (realPoints K : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [← conjRealPart_add_I_smul_conjImaginaryPart (K := K) v]
  exact Submodule.add_mem _ (Submodule.subset_span (conjRealPart_mem hK v))
    (Submodule.smul_mem _ _ (Submodule.subset_span (conjImaginaryPart_mem hK v)))

/-! ### A complexification splits along `1` and `I` -/

/-- **Every element of `ℂ ⊗[ℝ] W` is `1 ⊗ₜ w₁ + I ⊗ₜ w₂`**: writing a complex scalar as
`x + y * I` with `x, y : ℝ` moves its two real coordinates into the second factor.  This is the
splitting `ℂ ⊗[ℝ] W ≅ W ⊕ I · W` in the form the injectivity argument below uses it. -/
theorem exists_one_tmul_add_I_tmul {W : Type*} [AddCommGroup W] [Module ℝ W] (u : ℂ ⊗[ℝ] W) :
    ∃ w₁ w₂ : W, u = 1 ⊗ₜ[ℝ] w₁ + Complex.I ⊗ₜ[ℝ] w₂ := by
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left Complex.basisOneI u
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two, Complex.coe_basisOneI]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### Real-linear maps into the real points -/

section LiftBaseChange

variable {E W : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup W] [Module ℝ W]

/-- **Vectors fixed by a conjugate-linear map complexify injectively.**  If a conjugate-linear
`K` fixes every value of an injective real-linear map `f : W → E`, then the induced map
`ℂ ⊗[ℝ] W → E`, `c ⊗ₜ w ↦ c • f w`, is injective: applying `K` to a relation
`f w₁ + I • f w₂ = 0` flips the sign of its `I`-component, so adding the two relations kills
`f w₂` and leaves `2 • f w₁ = 0`.

The real structure on `E` is an arbitrary one compatible with the complex structure
(`IsScalarTower ℝ ℂ E`), so this also applies to spaces such as `Matrix n n ℂ` whose real
structure is not syntactically `Module.complexToReal`. -/
theorem _root_.LinearMap.liftBaseChange_complex_injective_of_conj (f : W →ₗ[ℝ] E)
    {K : E →ₛₗ[starRingEnd ℂ] E} (hf : Function.Injective f) (hK : ∀ w, K (f w) = f w) :
    Function.Injective (f.liftBaseChange ℂ) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨w₁, w₂, rfl⟩ := exists_one_tmul_add_I_tmul u
  have h : f w₁ + Complex.I • f w₂ = 0 := by simpa using hu
  have hconj : f w₁ + (-Complex.I) • f w₂ = 0 := by simpa [hK] using congrArg K h
  have h₁ : f w₁ = 0 := by
    have h2 : (2 : ℂ) • f w₁ = 0 := by linear_combination (norm := module) h + hconj
    simpa using h2
  have h₂ : f w₂ = 0 := by simpa [h₁] using h
  rw [hf (h₁.trans (map_zero f).symm), hf (h₂.trans (map_zero f).symm)]
  simp

end LiftBaseChange

/-! ### The complexification of the real points -/

variable (K) in
/-- The canonical `ℂ`-linear map from the complexification of the real points, `c ⊗ₜ w ↦ c • w`.
It is `LinearMap.liftBaseChange` applied to the inclusion of the real points.
`TauCeti.realPointsEquiv` upgrades it to an isomorphism when `K` is involutive. -/
noncomputable def realPointsLift : ℂ ⊗[ℝ] realPoints K →ₗ[ℂ] V :=
  (realPoints K).subtype.liftBaseChange ℂ

@[simp]
theorem realPointsLift_tmul (c : ℂ) (w : realPoints K) :
    realPointsLift K (c ⊗ₜ[ℝ] w) = c • (w : V) :=
  (rfl)

/-- The lift is surjective once `K` is involutive: its image is the complex span of the real
points, which is all of `V` (`TauCeti.span_realPoints_eq_top`). -/
theorem realPointsLift_surjective (hK : Function.Involutive K) :
    Function.Surjective (realPointsLift K) := by
  rw [← LinearMap.range_eq_top, realPointsLift, LinearMap.range_liftBaseChange,
    Submodule.range_subtype]
  exact span_realPoints_eq_top hK

/-- The lift is injective for **any** conjugate-linear `K`: only its surjectivity uses that `K` is
involutive.  This is `LinearMap.liftBaseChange_complex_injective_of_conj` for the inclusion of
the real points. -/
theorem realPointsLift_injective : Function.Injective (realPointsLift K) :=
  (realPoints K).subtype.liftBaseChange_complex_injective_of_conj Subtype.val_injective
    fun w ↦ w.2

/-- **A complex vector space is the complexification of the real points of any conjugation on
it.**  The isomorphism is `c ⊗ₜ w ↦ c • w`; surjectivity is the decomposition
`TauCeti.conjRealPart_add_I_smul_conjImaginaryPart`, and injectivity is that a relation
`w₁ + I • w₂ = 0` between real points is killed by adding and subtracting its conjugate. -/
noncomputable def realPointsEquiv (hK : Function.Involutive K) :
    ℂ ⊗[ℝ] realPoints K ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (realPointsLift K)
    ⟨realPointsLift_injective, realPointsLift_surjective hK⟩

/-- The isomorphism sends `c ⊗ₜ w` to `c • w`. -/
@[simp]
theorem realPointsEquiv_tmul (hK : Function.Involutive K) (c : ℂ) (w : realPoints K) :
    realPointsEquiv hK (c ⊗ₜ[ℝ] w) = c • (w : V) :=
  realPointsLift_tmul c w

/-- The inverse of the isomorphism is the decomposition into real and imaginary parts:
`v ↦ 1 ⊗ₜ conjRealPart K v + I ⊗ₜ conjImaginaryPart K v`. -/
@[simp]
theorem realPointsEquiv_symm_apply (hK : Function.Involutive K) (v : V) :
    (realPointsEquiv hK).symm v =
      1 ⊗ₜ[ℝ] (⟨conjRealPart K v, conjRealPart_mem hK v⟩ : realPoints K) +
        Complex.I ⊗ₜ[ℝ] (⟨conjImaginaryPart K v, conjImaginaryPart_mem hK v⟩ : realPoints K) := by
  rw [LinearEquiv.symm_apply_eq, map_add, realPointsEquiv_tmul, realPointsEquiv_tmul, one_smul]
  exact (conjRealPart_add_I_smul_conjImaginaryPart v).symm

/-- **The real points of a conjugation halve the dimension**: their `ℝ`-dimension is the
`ℂ`-dimension of `V`, because `V` is their complexification and base change does not change the
dimension.  No finiteness is assumed: in the infinite-dimensional case both sides are the junk
value `0`. -/
theorem finrank_realPoints (hK : Function.Involutive K) :
    finrank ℝ (realPoints K) = finrank ℂ V := by
  rw [← (realPointsEquiv hK).finrank_eq, Module.finrank_baseChange]

/-- The self-adjoint elements of a complex star module have the `ℝ`-dimension that the module has
over `ℂ`: they are the real points of the conjugation `star`. -/
theorem finrank_selfAdjoint_submodule {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A]
    [StarModule ℂ A] : finrank ℝ (selfAdjoint.submodule ℝ A) = finrank ℂ A := by
  let K : A →ₛₗ[starRingEnd ℂ] A := (starLinearEquiv ℂ (A := A)).toLinearMap
  have h : selfAdjoint.submodule ℝ A = realPoints K := by
    ext x
    rw [mem_realPoints, LinearEquiv.coe_coe, starLinearEquiv_apply]
    exact selfAdjoint.mem_iff (R := A)
  rw [h, finrank_realPoints (K := K) star_star]

/-! ### The conjugation of a complexification -/

section Complexification

variable (W : Type*) [AddCommGroup W] [Module ℝ W]

/-- The **conjugation of a complexification**: `c ⊗ₜ w ↦ conj c ⊗ₜ w`, conjugate-linear because
conjugation is `ℝ`-linear and multiplicative on `ℂ`.  The underlying `ℝ`-linear map is
`LinearMap.rTensor W Complex.conjAe.toLinearMap`.  This is the construction converse to
`TauCeti.realPointsEquiv`: it turns a presentation of a space as a complexification into a
conjugation on it. -/
noncomputable def tmulConj : (ℂ ⊗[ℝ] W) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℝ] W) where
  toFun := LinearMap.rTensor W Complex.conjAe.toLinearMap
  map_add' := map_add _
  map_smul' c u := by
    induction u with
    | tmul c' w =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        TensorProduct.smul_tmul', smul_eq_mul]
      simp only [AlgEquiv.toLinearMap_apply, Complex.conjAe_coe, map_mul]
    | add u₁ u₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]

/-- The conjugation of a complexification conjugates the scalar and leaves the vector alone. -/
@[simp]
theorem tmulConj_tmul (c : ℂ) (w : W) :
    tmulConj W (c ⊗ₜ[ℝ] w) = (starRingEnd ℂ) c ⊗ₜ[ℝ] w :=
  (rfl)

/-- Conjugating twice is the identity, in the applied form `simp` can use.  The proof is an
induction on the tensor, run off the characterization `TauCeti.tmulConj_tmul` rather than the
unexposed body. -/
@[simp]
theorem tmulConj_tmulConj (u : ℂ ⊗[ℝ] W) : tmulConj W (tmulConj W u) = u := by
  induction u with
  | tmul c w => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- The conjugation of a complexification is involutive, so it is a conjugation in the sense of
this file. -/
theorem tmulConj_involutive : Function.Involutive (tmulConj W) :=
  tmulConj_tmulConj W

/-- The vectors the conjugation of a complexification fixes are exactly the image of `W`, that is,
the elements `1 ⊗ₜ w`.  Stated on `tmulConj W u = u` rather than on `u ∈ realPoints (tmulConj W)`
because `TauCeti.mem_realPoints` is the simp normal form of the latter. -/
@[simp]
theorem tmulConj_eq_self_iff (u : ℂ ⊗[ℝ] W) :
    tmulConj W u = u ↔ ∃ w : W, u = 1 ⊗ₜ[ℝ] w := by
  refine ⟨fun hu => ?_, ?_⟩
  · obtain ⟨w₁, w₂, rfl⟩ := exists_one_tmul_add_I_tmul u
    rw [map_add, tmulConj_tmul, tmulConj_tmul, map_one, Complex.conj_I] at hu
    refine ⟨w₁, ?_⟩
    have hc : -(Complex.I ⊗ₜ[ℝ] w₂) = Complex.I ⊗ₜ[ℝ] w₂ := by
      rw [← TensorProduct.neg_tmul]
      exact add_left_cancel hu
    have h : (2 : ℝ) • (Complex.I ⊗ₜ[ℝ] w₂) = (0 : ℂ ⊗[ℝ] W) := by
      rw [two_smul]
      nth_rewrite 1 [← hc]
      abel
    -- `(2 : ℝ) • x = 0` forces `x = 0`: `smul_eq_zero` and `2 ≠ 0`.
    have h₂ : Complex.I ⊗ₜ[ℝ] w₂ = (0 : ℂ ⊗[ℝ] W) := by simpa using h
    rw [h₂, add_zero]
  · rintro ⟨w, rfl⟩
    rw [tmulConj_tmul, map_one]

/-- The real-linear retraction `c ⊗ₜ w ↦ (re c) • w` of `w ↦ 1 ⊗ₜ w`. -/
noncomputable def realPart (W : Type*) [AddCommGroup W] [Module ℝ W] :
    ℂ ⊗[ℝ] W →ₗ[ℝ] W :=
  TensorProduct.lid ℝ W ∘ₗ Complex.reLm.rTensor W

/-- The real part of a pure tensor is its real scalar part acting on the vector. -/
@[simp]
theorem realPart_tmul (c : ℂ) (w : W) : realPart W (c ⊗ₜ[ℝ] w) = c.re • w := by
  simp [realPart]

/-- The real part of a real vector embedded in its complexification is that vector. -/
theorem realPart_one_tmul (w : W) : realPart W (1 ⊗ₜ[ℝ] w) = w := by
  simp

/-- The real-linear map `c ⊗ₜ w ↦ (im c) • w`, reading off the coefficient of `I` in the splitting
`ℂ ⊗[ℝ] W ≅ W ⊕ I · W`. -/
noncomputable def imaginaryPart (W : Type*) [AddCommGroup W] [Module ℝ W] :
    ℂ ⊗[ℝ] W →ₗ[ℝ] W :=
  TensorProduct.lid ℝ W ∘ₗ Complex.imLm.rTensor W

/-- The imaginary part of a pure tensor is its imaginary scalar part acting on the vector. -/
@[simp]
theorem imaginaryPart_tmul (c : ℂ) (w : W) : imaginaryPart W (c ⊗ₜ[ℝ] w) = c.im • w := by
  simp [imaginaryPart]

/-- **Every element of `ℂ ⊗[ℝ] W` is `1 ⊗ₜ realPart W u + I ⊗ₜ imaginaryPart W u`.** -/
@[simp]
theorem one_tmul_realPart_add_I_tmul_imaginaryPart (u : ℂ ⊗[ℝ] W) :
    1 ⊗ₜ[ℝ] realPart W u + Complex.I ⊗ₜ[ℝ] imaginaryPart W u = u := by
  obtain ⟨w₁, w₂, rfl⟩ := exists_one_tmul_add_I_tmul u
  simp

variable {W} in
/-- **Extensionality in a complexification**: a vector of `ℂ ⊗[ℝ] W` is determined by its real
and imaginary parts. -/
theorem complexification_ext {u v : ℂ ⊗[ℝ] W} (hre : realPart W u = realPart W v)
    (him : imaginaryPart W u = imaginaryPart W v) : u = v := by
  rw [← one_tmul_realPart_add_I_tmul_imaginaryPart W u,
    ← one_tmul_realPart_add_I_tmul_imaginaryPart W v, hre, him]

variable {W} in
/-- Two vectors of `ℂ ⊗[ℝ] W` are equal exactly when their real and imaginary parts are. -/
theorem complexification_ext_iff {u v : ℂ ⊗[ℝ] W} :
    u = v ↔ realPart W u = realPart W v ∧ imaginaryPart W u = imaginaryPart W v :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun h ↦ complexification_ext h.1 h.2⟩

/-- The two real coordinates of `1 ⊗ₜ w₁ + I ⊗ₜ w₂` are `w₁` and `w₂`. -/
@[simp]
theorem one_tmul_add_I_tmul_inj {w₁ w₂ w₁' w₂' : W} :
    1 ⊗ₜ[ℝ] w₁ + Complex.I ⊗ₜ[ℝ] w₂ = 1 ⊗ₜ[ℝ] w₁' + Complex.I ⊗ₜ[ℝ] w₂' ↔
      w₁ = w₁' ∧ w₂ = w₂' := by
  simp [complexification_ext_iff]

/-- Multiplication by a complex scalar `c` in the real coordinates of a complexification:
`c • (1 ⊗ₜ v + I ⊗ₜ w) = 1 ⊗ₜ (re c • v - im c • w) + I ⊗ₜ (re c • w + im c • v)`. -/
theorem smul_one_tmul_add_I_tmul (c : ℂ) (v w : W) :
    c • (1 ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w) =
      1 ⊗ₜ[ℝ] (c.re • v - c.im • w) + Complex.I ⊗ₜ[ℝ] (c.re • w + c.im • v) := by
  conv_lhs => rw [← one_tmul_realPart_add_I_tmul_imaginaryPart W (c • _)]
  simp [TensorProduct.smul_tmul', sub_eq_add_neg, add_comm]

/-- `I • (1 ⊗ₜ v + I ⊗ₜ w) = 1 ⊗ₜ (-w) + I ⊗ₜ v` in a complexification. -/
theorem I_smul_one_tmul_add_I_tmul (v w : W) :
    Complex.I • (1 ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w) = 1 ⊗ₜ[ℝ] (-w) + Complex.I ⊗ₜ[ℝ] v := by
  rw [smul_one_tmul_add_I_tmul]
  simp

/-- The real part of `c • u` is `re c • realPart W u - im c • imaginaryPart W u`. -/
@[simp]
theorem realPart_smul (c : ℂ) (u : ℂ ⊗[ℝ] W) :
    realPart W (c • u) = c.re • realPart W u - c.im • imaginaryPart W u := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
  simp [TensorProduct.smul_tmul', sub_eq_add_neg]

/-- The imaginary part of `c • u` is `re c • imaginaryPart W u + im c • realPart W u`. -/
@[simp]
theorem imaginaryPart_smul (c : ℂ) (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W (c • u) = c.re • imaginaryPart W u + c.im • realPart W u := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
  simp [TensorProduct.smul_tmul', add_comm]

/-- Real-linear isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℝ] W × W` given by `(realPart, imaginaryPart)`. -/
noncomputable def complexificationLinearEquivProd : ℂ ⊗[ℝ] W ≃ₗ[ℝ] W × W where
  toFun u := (realPart W u, imaginaryPart W u)
  map_add' u v := by ext <;> simp
  map_smul' r u := by ext <;> simp
  invFun p := 1 ⊗ₜ[ℝ] p.1 + Complex.I ⊗ₜ[ℝ] p.2
  left_inv := one_tmul_realPart_add_I_tmul_imaginaryPart W
  right_inv p := by ext <;> simp

variable {W}

@[simp] theorem complexificationLinearEquivProd_apply (u : ℂ ⊗[ℝ] W) :
    complexificationLinearEquivProd W u = (realPart W u, imaginaryPart W u) := (rfl)

@[simp] theorem complexificationLinearEquivProd_symm_apply (p : W × W) :
    (complexificationLinearEquivProd W).symm p = 1 ⊗ₜ[ℝ] p.1 + Complex.I ⊗ₜ[ℝ] p.2 := (rfl)

/-- Complex conjugation preserves the real part of `u : ℂ ⊗[ℝ] W`. -/
@[simp] theorem realPart_tmulConj (u : ℂ ⊗[ℝ] W) : realPart W (tmulConj W u) = realPart W u := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u; simp [TensorProduct.neg_tmul]

/-- Complex conjugation negates the imaginary part of `u : ℂ ⊗[ℝ] W`. -/
@[simp] theorem imaginaryPart_tmulConj (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W (tmulConj W u) = -imaginaryPart W u := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u; simp [TensorProduct.neg_tmul]

/-- Coordinate decomposition of `tmulConj W u` into `1 ⊗ₜ realPart W u - I ⊗ₜ imaginaryPart W u`. -/
theorem tmulConj_eq_one_tmul_sub_I_tmul (u : ℂ ⊗[ℝ] W) :
    tmulConj W u = 1 ⊗ₜ[ℝ] realPart W u - Complex.I ⊗ₜ[ℝ] imaginaryPart W u := by
  simpa [sub_eq_add_neg, TensorProduct.tmul_neg] using
    (one_tmul_realPart_add_I_tmul_imaginaryPart W (tmulConj W u)).symm

end Complexification

/-- Real descent intertwines tensor conjugation with the original conjugation. -/
@[simp]
theorem realPointsEquiv_tmulConj (hK : Function.Involutive K)
    (x : ℂ ⊗[ℝ] realPoints K) :
    realPointsEquiv hK (tmulConj (realPoints K) x) = K (realPointsEquiv hK x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z w => simp [mem_realPoints.mp w.property]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- **The conjugation of a complexification commutes with every base-changed map**, because
`LinearMap.baseChange` leaves the conjugated factor alone. -/
theorem tmulConj_baseChange {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W']
    [Module ℝ W'] (f : W →ₗ[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    tmulConj W' (f.baseChange ℂ u) = f.baseChange ℂ (tmulConj W u) := by
  induction u with
  | tmul c w => simp
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]

/-- Base change commutes with `realPart`. -/
@[simp] theorem realPart_baseChange {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W']
    [Module ℝ W'] (f : W →ₗ[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    realPart W' (f.baseChange ℂ u) = f (realPart W u) := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u; simp

/-- Base change commutes with `imaginaryPart`. -/
@[simp] theorem imaginaryPart_baseChange {W W' : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup W'] [Module ℝ W'] (f : W →ₗ[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W' (f.baseChange ℂ u) = f (imaginaryPart W u) := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u; simp

end TauCeti

namespace LinearEquiv

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

open TauCeti

/-- Transport the existing tensor conjugation through a complexification equivalence.
The result uses the native semilinear-map carrier. -/
noncomputable def conjugationOfComplexification {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) : V →ₛₗ[starRingEnd ℂ] V :=
  e.toLinearMap ∘ₛₗ (tmulConj W ∘ₛₗ e.symm.toLinearMap)

/-- The defining transport formula for tensor conjugation. -/
theorem conjugationOfComplexification_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) (v : V) :
    conjugationOfComplexification e v = e (tmulConj W (e.symm v)) := by
  simp only [conjugationOfComplexification, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]

/-- The transported conjugation conjugates the scalar of the image of a pure tensor. -/
@[simp]
theorem conjugationOfComplexification_apply_tmul {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) (c : ℂ) (w : W) :
    conjugationOfComplexification e (e (c ⊗ₜ[ℝ] w)) = e (star c ⊗ₜ[ℝ] w) := by
  rw [conjugationOfComplexification_apply, e.symm_apply_apply, tmulConj_tmul, starRingEnd_apply]

/-- Applying the transported tensor conjugation twice gives back the input. -/
@[simp]
theorem conjugationOfComplexification_conjugationOfComplexification {W : Type*} [AddCommGroup W]
    [Module ℝ W] (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) (v : V) :
    conjugationOfComplexification e (conjugationOfComplexification e v) = v := by
  simp only [conjugationOfComplexification_apply, e.symm_apply_apply, tmulConj_tmulConj,
    e.apply_symm_apply]

/-- Transported tensor conjugation is involutive. -/
theorem conjugationOfComplexification_involutive {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) : Function.Involutive (conjugationOfComplexification e) :=
  conjugationOfComplexification_conjugationOfComplexification e

/-- The exact fixed locus is the image of the real inclusion `w ↦ e (1 ⊗ w)`. -/
@[simp]
theorem conjugationOfComplexification_eq_self_iff {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) (v : V) :
    conjugationOfComplexification e v = v ↔ ∃ w : W, e (1 ⊗ₜ[ℝ] w) = v := by
  constructor
  · intro hv
    have hfix : tmulConj W (e.symm v) = e.symm v := by
      apply e.injective
      simpa only [conjugationOfComplexification_apply, e.apply_symm_apply] using hv
    obtain ⟨w, hw⟩ := (tmulConj_eq_self_iff W (e.symm v)).mp hfix
    exact ⟨w, by rw [← hw, e.apply_symm_apply]⟩
  · rintro ⟨w, rfl⟩
    simp only [conjugationOfComplexification_apply, e.symm_apply_apply, tmulConj_tmul,
      map_one]

/-- A conjugate-linear map fixing the real inclusion is uniquely the transported conjugation.
No involutivity assumption on the competing map is necessary. -/
theorem conjugationOfComplexification_unique {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V) (K : V →ₛₗ[starRingEnd ℂ] V)
    (hfix : ∀ w : W, K (e (1 ⊗ₜ[ℝ] w)) = e (1 ⊗ₜ[ℝ] w)) :
    K = conjugationOfComplexification e := by
  apply LinearMap.ext_on (span_realPoints_eq_top (conjugationOfComplexification_involutive e))
  intro v hv
  obtain ⟨w, rfl⟩ := (conjugationOfComplexification_eq_self_iff e v).mp (mem_realPoints.mp hv)
  simp only [hfix, conjugationOfComplexification_apply, e.symm_apply_apply, tmulConj_tmul,
    map_one]

/-- Transported conjugation is natural under complex-linear maps carrying the real inclusions
to each other. The map between the real carriers need not be invertible. -/
theorem conjugationOfComplexification_natural
    {W W' V' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    [AddCommGroup V'] [Module ℂ V'] (e : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] V)
    (e' : (ℂ ⊗[ℝ] W') ≃ₗ[ℂ] V') (A : V →ₗ[ℂ] V') (b : W →ₗ[ℝ] W')
    (hreal : ∀ w, A (e (1 ⊗ₜ[ℝ] w)) = e' (1 ⊗ₜ[ℝ] b w)) (v : V) :
    conjugationOfComplexification e' (A v) = A (conjugationOfComplexification e v) := by
  have h : conjugationOfComplexification e' ∘ₛₗ A = A ∘ₛₗ conjugationOfComplexification e := by
    apply LinearMap.ext_on (span_realPoints_eq_top (conjugationOfComplexification_involutive e))
    intro u hu
    obtain ⟨w, rfl⟩ := (conjugationOfComplexification_eq_self_iff e u).mp (mem_realPoints.mp hu)
    simp only [LinearMap.coe_comp, Function.comp_apply, hreal,
      conjugationOfComplexification_apply, e.symm_apply_apply, e'.symm_apply_apply,
      tmulConj_tmul, map_one]
  exact congrArg (fun f ↦ f v) h

end LinearEquiv
