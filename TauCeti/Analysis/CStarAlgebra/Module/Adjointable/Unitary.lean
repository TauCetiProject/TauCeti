/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Order

/-!
# Projections, isometries, and unitary equivalences of Hilbert C⋆-modules

This file develops the geometric operators of Hilbert C⋆-module theory on top of bundled
adjointable maps (`CStarModule.Adjointable`):

* **Adjointable projections**: for a star projection `P : Adjointable A E E` (`P ∘ P = P` and
  `P* = P`), we prove the inner-product orthogonality relation `⟪P x, y - P y⟫_A = 0`, the
  C⋆-valued Pythagorean identity `⟪x, x⟫_A = ⟪P x, P x⟫_A + ⟪x - P x, x - P x⟫_A`, the kernel
  characterization `P y = 0 ↔ ∀ x, ⟪P x, y⟫_A = 0`, closedness of `Set.range P`, topological
  complementation of `range P` and `ker P`, and contractivity `‖P x‖ ≤ ‖x‖`.
* **Adjointable isometries**: for `T : Adjointable A E F` between possibly distinct modules, we
  characterize `T* ∘ T = 1` by preservation of the `A`-valued inner product (and, via complex
  polarization, by preservation of diagonal inner products `⟪T x, T x⟫_A = ⟪x, x⟫_A`), deduce
  `‖T x‖ = ‖x‖`, and show that `T ∘ T*` is a star projection on `F` with range `Set.range T` (so
  every adjointable isometry has closed range without completeness hypotheses).
* **Module unitaries and Lance's Theorem 3.5** (`CStarModule.UnitaryEquiv`): we bundle isometric
  equivalences preserving the `A`-valued inner product as `UnitaryEquiv A E F`, prove Lance's
  automatic-linearity and automatic-adjointability theorem (`UnitaryEquiv.ofSurjectiveInner`: any
  surjective map `U : E → F` satisfying `⟪U x, U y⟫_A = ⟪x, y⟫_A` upgrades to a `UnitaryEquiv`),
  identify `UnitaryEquiv A E F` with two-sided isometric `Adjointable A E F` operators
  (`UnitaryEquiv.equivAdjointable`), and establish the group isomorphism
  `UnitaryEquiv A E E ≃* unitary (Adjointable A E E)` (`UnitaryEquiv.equivUnitary`).

## Main declarations

* `CStarModule.Adjointable.inner_self_eq_add_inner_sub_self_of_isStarProjection`,
  `CStarModule.Adjointable.norm_map_le_of_isStarProjection`: Pythagorean identity and
  contractivity for adjointable projections.
* `CStarModule.Adjointable.adjoint_comp_self_eq_one_iff`,
  `CStarModule.Adjointable.adjoint_comp_self_eq_one_iff_forall_inner_self`,
  `CStarModule.Adjointable.isStarProjection_comp_adjoint`: characterizations and range projection
  of adjointable isometries.
* `CStarModule.UnitaryEquiv`: bundled unitary equivalences between Hilbert C⋆-modules.
* `CStarModule.UnitaryEquiv.ofSurjectiveInner`: Lance's Theorem 3.5 constructing a `UnitaryEquiv`
  from a plain surjective inner-product-preserving function.
* `CStarModule.UnitaryEquiv.equivAdjointable`, `CStarModule.UnitaryEquiv.equivUnitary`:
  identifications with two-sided adjointable isometries and with `unitary (Adjointable A E E)`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 3
  (especially Theorem 3.5).
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite

namespace CStarModule

namespace Adjointable

/-! ### Adjointable projections -/

section Projections

variable {A E : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- An adjointable endomorphism `P` is a star projection if and only if `P ∘ P = P` and
`P* = P`. -/
theorem isStarProjection_iff_comp_self_and_adjoint {P : Adjointable A E E} :
    IsStarProjection P ↔ P.comp P = P ∧ P.adjoint = P := by
  rw [isStarProjection_iff', mul_def, star_def]

/-- Forgetting the adjoint carries an idempotent `Adjointable` endomorphism to an idempotent
continuous linear map. -/
theorem isIdempotentElem_toContinuousLinearMap {P : Adjointable A E E} (hP : IsIdempotentElem P) :
    IsIdempotentElem P.toContinuousLinearMap := by
  simpa only [coe_toContinuousLinearMapAlgHom] using
    hP.map (toContinuousLinearMapAlgHom (A := A) (E := E))

/-- The range of an idempotent adjointable endomorphism is its fixed-point set. -/
theorem range_eq_fixedPoints_of_isIdempotentElem {P : Adjointable A E E}
    (hP : IsIdempotentElem P) : Set.range P = {x : E | P x = x} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨x, hx⟩⟩
  rintro ⟨y, rfl⟩
  simpa only [Set.mem_ofPred_eq, mul_apply] using congrArg (· y) hP.eq

/-- Every idempotent adjointable endomorphism has closed range. -/
theorem isClosed_range_of_isIdempotentElem {P : Adjointable A E E} (hP : IsIdempotentElem P) :
    IsClosed (Set.range P) := by
  rw [range_eq_fixedPoints_of_isIdempotentElem hP]
  exact isClosed_eq (map_continuous P) continuous_id

/-- The range and kernel of an idempotent adjointable endomorphism are topological complements as
complex submodules of `E`. -/
theorem isTopCompl_range_ker_of_isIdempotentElem {P : Adjointable A E E}
    (hP : IsIdempotentElem P) :
    Submodule.IsTopCompl P.toContinuousLinearMap.range P.toContinuousLinearMap.ker :=
  ContinuousLinearMap.IsIdempotentElem.isTopCompl (isIdempotentElem_toContinuousLinearMap hP)

/-- For a star projection `P`, `⟪P x, P x⟫_A = ⟪x, P x⟫_A`. -/
theorem inner_map_self_of_isStarProjection {P : Adjointable A E E} (hP : IsStarProjection P)
    (x : E) : inner A (P x) (P x) = inner A x (P x) := by
  rw [← P.adjoint_inner_right, isSelfAdjoint_iff'.mp hP.isSelfAdjoint, ← mul_apply,
    hP.isIdempotentElem.eq]

/-- For a star projection `P`, `P x` is orthogonal to `y - P y` in the `A`-valued inner product. -/
theorem inner_sub_self_of_isStarProjection {P : Adjointable A E E} (hP : IsStarProjection P)
    (x y : E) : inner A (P x) (y - P y) = 0 := by
  rw [inner_sub_right, ← P.adjoint_inner_right, ← P.adjoint_inner_right,
    isSelfAdjoint_iff'.mp hP.isSelfAdjoint, ← mul_apply, hP.isIdempotentElem.eq, sub_self]

/-- For a star projection `P`, a vector lies in `ker P` if and only if it is `A`-orthogonal to
`range P`. -/
theorem apply_eq_zero_iff_forall_inner_map_eq_zero_of_isStarProjection {P : Adjointable A E E}
    (hP : IsStarProjection P) (y : E) :
    P y = 0 ↔ ∀ x : E, inner A (P x) y = 0 := by
  refine ⟨fun hy x ↦ ?_, fun h ↦ ?_⟩
  · rw [← P.adjoint_inner_right, isSelfAdjoint_iff'.mp hP.isSelfAdjoint, hy, inner_zero_right]
  · rw [← inner_self (A := A), inner_map_self_of_isStarProjection hP,
      ← inner_eq_right_of_isSelfAdjoint hP.isSelfAdjoint]
    exact h y

/-- **C⋆-valued Pythagorean identity** for a star projection `P`:
`⟪x, x⟫_A = ⟪P x, P x⟫_A + ⟪x - P x, x - P x⟫_A`. -/
theorem inner_self_eq_add_inner_sub_self_of_isStarProjection {P : Adjointable A E E}
    (hP : IsStarProjection P) (x : E) :
    inner A x x = inner A (P x) (P x) + inner A (x - P x) (x - P x) := by
  have horth₁ : inner A (P x) (x - P x) = 0 := inner_sub_self_of_isStarProjection hP x x
  have horth₂ : inner A (x - P x) (P x) = 0 := by
    rw [← star_inner, horth₁, star_zero]
  conv_lhs => rw [← add_sub_cancel (P x) x]
  rw [inner_add_left, inner_add_right, inner_add_right, horth₁, horth₂, add_zero, zero_add]

end Projections

/-- Every star projection in `Adjointable A E E` is contractive: `‖P x‖ ≤ ‖x‖`. -/
theorem norm_map_le_of_isStarProjection {A E : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    {P : Adjointable A E E} (hP : IsStarProjection P) (x : E) : ‖P x‖ ≤ ‖x‖ :=
  calc ‖P x‖ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hP.norm_le P) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-! ### Adjointable isometries -/

section Isometries

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator `T : Adjointable A E F` satisfies `T* ∘ T = 1` if and only if it
preserves the `A`-valued inner product on all pairs of vectors. -/
theorem adjoint_comp_self_eq_one_iff {T : Adjointable A E F} :
    T.adjoint.comp T = 1 ↔ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · rw [← T.adjoint_inner_right, ← comp_apply, h, one_apply]
  · ext y
    refine CStarModule.ext_inner_left (A := A) fun x ↦ ?_
    rw [comp_apply, T.adjoint_inner_right, one_apply, h x y]

/-- An adjointable operator `T : Adjointable A E F` satisfies `T* ∘ T = 1` if and only if it
preserves all diagonal inner products `⟪T x, T x⟫_A = ⟪x, x⟫_A`. -/
theorem adjoint_comp_self_eq_one_iff_forall_inner_self {T : Adjointable A E F} :
    T.adjoint.comp T = 1 ↔ ∀ x : E, inner A (T x) (T x) = inner A x x := by
  refine ⟨fun h x ↦ adjoint_comp_self_eq_one_iff.mp h x x, fun h ↦ ?_⟩
  have hlin : (T.adjoint.comp T).toContinuousLinearMap.toLinearMap =
      (1 : Adjointable A E E).toContinuousLinearMap.toLinearMap :=
    (CStarModule.ext_inner_map (A := A) _ _).mp fun x ↦ by
      simpa only [ContinuousLinearMap.coe_coe, toContinuousLinearMap_apply, comp_apply,
        adjoint_inner_right, one_apply] using h x
  exact ext (LinearMap.congr_fun hlin)

/-- If `T* ∘ T = 1`, then `T` preserves norms: `‖T x‖ = ‖x‖`. -/
theorem norm_map_of_adjoint_comp_self_eq_one {T : Adjointable A E F}
    (hT : T.adjoint.comp T = 1) (x : E) : ‖T x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A) (T x), norm_eq_sqrt_norm_inner_self (A := A) x,
    adjoint_comp_self_eq_one_iff.mp hT x x]

/-- Every adjointable operator satisfying `T* ∘ T = 1` is a metric isometry. -/
theorem isometry_of_adjoint_comp_self_eq_one {T : Adjointable A E F}
    (hT : T.adjoint.comp T = 1) : Isometry T :=
  AddMonoidHomClass.isometry_of_norm T (norm_map_of_adjoint_comp_self_eq_one hT)

/-- If `T* ∘ T = 1`, then `(T ∘ T*) ∘ T = T`. -/
theorem comp_adjoint_comp_self_of_adjoint_comp_self_eq_one {T : Adjointable A E F}
    (hT : T.adjoint.comp T = 1) : (T.comp T.adjoint).comp T = T := by
  rw [comp_assoc, hT, one_def, comp_id]

/-- If `T : Adjointable A E F` satisfies `T* ∘ T = 1`, then `T ∘ T*` is a star projection in
`Adjointable A F F`. -/
theorem isStarProjection_comp_adjoint {T : Adjointable A E F} (hT : T.adjoint.comp T = 1) :
    IsStarProjection (T.comp T.adjoint) := by
  rw [isStarProjection_iff_comp_self_and_adjoint]
  refine ⟨?_, ?_⟩
  · rw [← comp_assoc, comp_adjoint_comp_self_of_adjoint_comp_self_eq_one hT]
  · rw [adjoint_comp, adjoint_adjoint]

/-- For an adjointable isometry `T` (`T* ∘ T = 1`), the range projection `T ∘ T*` has the same
range as `T`. -/
theorem range_comp_adjoint_of_adjoint_comp_self_eq_one {T : Adjointable A E F}
    (hT : T.adjoint.comp T = 1) : Set.range (T.comp T.adjoint) = Set.range T := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨T.adjoint z, (comp_apply T T.adjoint z).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨T x, by
      simpa only [comp_apply] using
        congrArg (· x) (comp_adjoint_comp_self_of_adjoint_comp_self_eq_one hT)⟩

/-- Every adjointable isometry (`T* ∘ T = 1`) has closed range in `F`, even without completeness
assumptions on `E` or `F`. -/
theorem isClosed_range_of_adjoint_comp_self_eq_one {T : Adjointable A E F}
    (hT : T.adjoint.comp T = 1) : IsClosed (Set.range T) := by
  rw [← range_comp_adjoint_of_adjoint_comp_self_eq_one hT]
  exact isClosed_range_of_isIdempotentElem (isStarProjection_comp_adjoint hT).isIdempotentElem

end Isometries

/-- Right-module form of `adjoint_comp_self_eq_one_iff` for `CStarModule Bᵐᵒᵖ`. -/
theorem adjoint_comp_self_eq_one_iff_unop_inner {B E F : Type*}
    [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    {T : Adjointable Bᵐᵒᵖ E F} :
    T.adjoint.comp T = 1 ↔
      ∀ x y : E, unop (inner Bᵐᵒᵖ (T x) (T y)) = unop (inner Bᵐᵒᵖ x y) := by
  rw [adjoint_comp_self_eq_one_iff]
  exact forall₂_congr fun _ _ ↦ unop_inj.symm

end Adjointable

/-! ### Unitary equivalences of Hilbert C⋆-modules and Lance's Theorem 3.5 -/

/-- A *unitary equivalence* between Hilbert C⋆-modules `E` and `F` over `A` is a complex-linear
isometric equivalence `E ≃ₗᵢ[ℂ] F` that preserves the `A`-valued inner product. Compatibility with
the `A`-action and adjointability follow automatically (`UnitaryEquiv.map_smul_coeff`,
`UnitaryEquiv.toAdjointable`). Conversely, by Lance's Theorem 3.5
(`UnitaryEquiv.ofSurjectiveInner`), any plain surjective function preserving the `A`-valued inner
product upgrades to a `UnitaryEquiv`. -/
structure UnitaryEquiv (A E F : Type*)
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E ≃ₗᵢ[ℂ] F where
  /-- A unitary equivalence preserves the `A`-valued inner product. -/
  inner_map' (x y : E) : inner A (toLinearIsometryEquiv x) (toLinearIsometryEquiv y) = inner A x y

namespace UnitaryEquiv

section Basic

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

theorem toLinearIsometryEquiv_injective :
    Function.Injective (toLinearIsometryEquiv : UnitaryEquiv A E F → (E ≃ₗᵢ[ℂ] F))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
theorem toLinearIsometryEquiv_inj {U V : UnitaryEquiv A E F} :
    U.toLinearIsometryEquiv = V.toLinearIsometryEquiv ↔ U = V :=
  toLinearIsometryEquiv_injective.eq_iff

instance instEquivLike : EquivLike (UnitaryEquiv A E F) E F where
  coe U := U.toLinearIsometryEquiv
  inv U := U.toLinearIsometryEquiv.symm
  left_inv U x := by exact U.toLinearIsometryEquiv.symm_apply_apply x
  right_inv U y := by exact U.toLinearIsometryEquiv.apply_symm_apply y
  coe_injective' _ _ h _ := toLinearIsometryEquiv_injective (DFunLike.ext' h)

instance instLinearIsometryEquivClass : LinearIsometryEquivClass (UnitaryEquiv A E F) ℂ E F where
  map_add U := map_add U.toLinearIsometryEquiv
  map_smulₛₗ U := map_smul U.toLinearIsometryEquiv
  norm_map U := U.toLinearIsometryEquiv.norm_map

@[simp]
theorem coe_toLinearIsometryEquiv (U : UnitaryEquiv A E F) :
    ⇑U.toLinearIsometryEquiv = ⇑U := (rfl)

@[simp]
theorem toLinearIsometryEquiv_apply (U : UnitaryEquiv A E F) (x : E) :
    U.toLinearIsometryEquiv x = U x := (rfl)

@[ext]
theorem ext {U V : UnitaryEquiv A E F} (h : ∀ x, U x = V x) : U = V :=
  DFunLike.ext U V h

@[simp]
theorem inner_map (U : UnitaryEquiv A E F) (x y : E) :
    inner A (U x) (U y) = inner A x y :=
  U.inner_map' x y

/-- The identity unitary equivalence of a Hilbert C⋆-module. -/
def refl (A E : Type*)
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    UnitaryEquiv A E E where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ E
  inner_map' _ _ := by rfl

@[simp]
theorem refl_apply (x : E) : refl A E x = x := (rfl)

@[simp]
theorem coe_refl : ⇑(refl A E) = id := (rfl)

/-- The inverse of a unitary equivalence of Hilbert C⋆-modules. -/
@[symm]
def symm (U : UnitaryEquiv A E F) : UnitaryEquiv A F E where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.symm
  inner_map' x y := by
    calc inner A (U.toLinearIsometryEquiv.symm x) (U.toLinearIsometryEquiv.symm y)
        = inner A (U (U.toLinearIsometryEquiv.symm x)) (U (U.toLinearIsometryEquiv.symm y)) :=
          (U.inner_map _ _).symm
      _ = inner A x y := by
        rw [← toLinearIsometryEquiv_apply, U.toLinearIsometryEquiv.apply_symm_apply,
          ← toLinearIsometryEquiv_apply, U.toLinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem symm_symm (U : UnitaryEquiv A E F) : U.symm.symm = U := by rfl

@[simp]
theorem apply_symm_apply (U : UnitaryEquiv A E F) (y : F) : U (U.symm y) = y :=
  U.toLinearIsometryEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (U : UnitaryEquiv A E F) (x : E) : U.symm (U x) = x :=
  U.toLinearIsometryEquiv.symm_apply_apply x

@[simp]
theorem toLinearIsometryEquiv_symm (U : UnitaryEquiv A E F) :
    U.symm.toLinearIsometryEquiv = U.toLinearIsometryEquiv.symm := by rfl

/-- Composition of unitary equivalences of Hilbert C⋆-modules. -/
@[trans]
def trans (U : UnitaryEquiv A E F) (V : UnitaryEquiv A F G) : UnitaryEquiv A E G where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv
  inner_map' x y := by
    simp only [LinearIsometryEquiv.trans_apply, toLinearIsometryEquiv_apply, V.inner_map,
      U.inner_map]

@[simp]
theorem trans_apply (U : UnitaryEquiv A E F) (V : UnitaryEquiv A F G) (x : E) :
    U.trans V x = V (U x) := by rfl

@[simp]
theorem self_trans_symm (U : UnitaryEquiv A E F) : U.trans U.symm = refl A E := by
  ext x
  exact U.symm_apply_apply x

@[simp]
theorem symm_trans_self (U : UnitaryEquiv A E F) : U.symm.trans U = refl A F := by
  ext y
  exact U.apply_symm_apply y

@[simp]
theorem refl_trans (U : UnitaryEquiv A E F) : (refl A E).trans U = U := by rfl

@[simp]
theorem trans_refl (U : UnitaryEquiv A E F) : U.trans (refl A F) = U := by rfl

theorem inner_symm_right (U : UnitaryEquiv A E F) (x : E) (y : F) :
    inner A (U x) y = inner A x (U.symm y) := by
  calc inner A (U x) y = inner A (U x) (U (U.symm y)) := by rw [U.apply_symm_apply]
    _ = inner A x (U.symm y) := U.inner_map x (U.symm y)

/-- Every unitary equivalence commutes with the coefficient action of `A`. -/
theorem map_smul_coeff (U : UnitaryEquiv A E F) (a : A) (x : E) : U (a • x) = a • U x :=
  ((isAdjointPair_inner_iff (A := A)).mpr U.inner_symm_right).map_smul_coeff_cstarModule a x

/-! #### Lance's Theorem 3.5: constructing `UnitaryEquiv` from a surjective inner-preserving map -/

/-- **Lance's Theorem 3.5**: any plain surjective function `U : E → F` between Hilbert C⋆-modules
satisfying `⟪U x, U y⟫_A = ⟪x, y⟫_A` for all `x, y : E` is automatically injective, complex-linear,
`A`-linear, and norm-preserving, hence upgrades to a `UnitaryEquiv A E F`. Neither completeness nor
C⋆-algebra norm axioms on `A` are needed. -/
noncomputable def ofSurjectiveInner (U : E → F) (hsurj : Function.Surjective U)
    (hinner : ∀ x y : E, inner A (U x) (U y) = inner A x y) : UnitaryEquiv A E F :=
  let V : F → E := Function.surjInv hsurj
  have hUV : ∀ y : F, U (V y) = y := Function.surjInv_eq hsurj
  have hadj : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip U V :=
    isAdjointPair_inner_iff.mpr fun x y ↦ by
      calc inner A (U x) y = inner A (U x) (U (V y)) := by rw [hUV]
        _ = inner A x (V y) := hinner x (V y)
  have hVU : ∀ x : E, V (U x) = x := fun x ↦
    CStarModule.ext_inner_right (A := A) fun z ↦ by
      calc inner A (V (U x)) z = star (inner A z (V (U x))) := (star_inner z _).symm
        _ = star (inner A (U z) (U x)) := by rw [hadj.inner_eq_cstarModule]
        _ = star (inner A z x) := by rw [hinner]
        _ = inner A x z := star_inner z x
  { toLinearEquiv :=
      { toFun := U
        invFun := V
        left_inv := hVU
        right_inv := hUV
        map_add' := hadj.map_add_cstarModule
        map_smul' := hadj.map_smul_cstarModule }
    norm_map' := fun x ↦ by
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [norm_eq_sqrt_norm_inner_self (A := A) (U x), norm_eq_sqrt_norm_inner_self (A := A) x,
        hinner x x]
    inner_map' := hinner }

@[simp]
theorem ofSurjectiveInner_apply (U : E → F) (hsurj : Function.Surjective U)
    (hinner : ∀ x y : E, inner A (U x) (U y) = inner A x y) (x : E) :
    ofSurjectiveInner U hsurj hinner x = U x := by rfl

@[simp]
theorem coe_ofSurjectiveInner (U : E → F) (hsurj : Function.Surjective U)
    (hinner : ∀ x y : E, inner A (U x) (U y) = inner A x y) :
    ⇑(ofSurjectiveInner U hsurj hinner) = U := by rfl

/-! #### Equivalence with two-sided adjointable isometries and `unitary (Adjointable A E E)` -/

/-- Reinterpret a `UnitaryEquiv A E F` as a bundled `Adjointable A E F` operator with adjoint
`U.symm`. -/
def toAdjointable (U : UnitaryEquiv A E F) : Adjointable A E F :=
  Adjointable.mkOfInner U.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
    U.symm.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap U.inner_symm_right

@[simp]
theorem toAdjointable_apply (U : UnitaryEquiv A E F) (x : E) :
    U.toAdjointable x = U x := by
  simp [toAdjointable]

@[simp]
theorem coe_toAdjointable (U : UnitaryEquiv A E F) :
    ⇑U.toAdjointable = ⇑U :=
  funext U.toAdjointable_apply

theorem toAdjointable_injective :
    Function.Injective (toAdjointable : UnitaryEquiv A E F → Adjointable A E F) :=
  fun _ _ h ↦ ext fun x ↦ by simpa only [toAdjointable_apply] using congrArg (· x) h

@[simp]
theorem adjoint_toAdjointable (U : UnitaryEquiv A E F) :
    U.toAdjointable.adjoint = U.symm.toAdjointable := by
  ext y
  simp [toAdjointable, symm]

@[simp]
theorem toAdjointable_refl : (refl A E).toAdjointable = 1 := by
  ext x
  simp

theorem toAdjointable_trans (U : UnitaryEquiv A E F) (V : UnitaryEquiv A F G) :
    (U.trans V).toAdjointable = V.toAdjointable.comp U.toAdjointable := by
  ext x
  simp

@[simp]
theorem symm_toAdjointable_comp_toAdjointable (U : UnitaryEquiv A E F) :
    U.symm.toAdjointable.comp U.toAdjointable = 1 := by
  ext x
  simp

@[simp]
theorem toAdjointable_comp_symm_toAdjointable (U : UnitaryEquiv A E F) :
    U.toAdjointable.comp U.symm.toAdjointable = 1 := by
  ext y
  simp

theorem adjoint_comp_toAdjointable (U : UnitaryEquiv A E F) :
    U.toAdjointable.adjoint.comp U.toAdjointable = 1 := by
  simp

theorem toAdjointable_comp_adjoint (U : UnitaryEquiv A E F) :
    U.toAdjointable.comp U.toAdjointable.adjoint = 1 := by
  simp

/-- Construct a `UnitaryEquiv A E F` from an `Adjointable` operator `T` satisfying `T* ∘ T = 1`
and `T ∘ T* = 1`. -/
def ofAdjointable (T : Adjointable A E F) (h₁ : T.adjoint.comp T = 1)
    (h₂ : T.comp T.adjoint = 1) : UnitaryEquiv A E F where
  toFun := T
  invFun := T.adjoint
  left_inv x := by
    simpa only [Adjointable.comp_apply, Adjointable.one_apply] using congrArg (· x) h₁
  right_inv y := by
    simpa only [Adjointable.comp_apply, Adjointable.one_apply] using congrArg (· y) h₂
  map_add' := map_add T
  map_smul' := map_smul T
  norm_map' x := by exact Adjointable.norm_map_of_adjoint_comp_self_eq_one h₁ x
  inner_map' x y := by exact Adjointable.adjoint_comp_self_eq_one_iff.mp h₁ x y

@[simp]
theorem ofAdjointable_apply (T : Adjointable A E F) (h₁ : T.adjoint.comp T = 1)
    (h₂ : T.comp T.adjoint = 1) (x : E) :
    ofAdjointable T h₁ h₂ x = T x := by rfl

@[simp]
theorem symm_ofAdjointable (T : Adjointable A E F) (h₁ : T.adjoint.comp T = 1)
    (h₂ : T.comp T.adjoint = 1) :
    (ofAdjointable T h₁ h₂).symm =
      ofAdjointable T.adjoint (by rwa [Adjointable.adjoint_adjoint])
        (by rwa [Adjointable.adjoint_adjoint]) := by
  ext y
  rfl

@[simp]
theorem toAdjointable_ofAdjointable (T : Adjointable A E F) (h₁ : T.adjoint.comp T = 1)
    (h₂ : T.comp T.adjoint = 1) :
    (ofAdjointable T h₁ h₂).toAdjointable = T := by
  ext x
  simp

@[simp]
theorem ofAdjointable_toAdjointable (U : UnitaryEquiv A E F) :
    ofAdjointable U.toAdjointable U.adjoint_comp_toAdjointable U.toAdjointable_comp_adjoint = U :=
  by
    ext x
    simp

/-- Unitary equivalences `UnitaryEquiv A E F` correspond bijectively to adjointable operators
`T : Adjointable A E F` satisfying `T* ∘ T = 1` and `T ∘ T* = 1`. -/
def equivAdjointable :
    UnitaryEquiv A E F ≃ {T : Adjointable A E F // T.adjoint.comp T = 1 ∧ T.comp T.adjoint = 1}
    where
  toFun U := ⟨U.toAdjointable, U.adjoint_comp_toAdjointable, U.toAdjointable_comp_adjoint⟩
  invFun T := ofAdjointable T.1 T.2.1 T.2.2
  left_inv U := by exact ofAdjointable_toAdjointable U
  right_inv T := by exact Subtype.ext (toAdjointable_ofAdjointable _ _ _)

/-! #### Group structure on `UnitaryEquiv A E E` and isomorphism with `unitary` -/

instance instOne : One (UnitaryEquiv A E E) := ⟨refl A E⟩
instance instMul : Mul (UnitaryEquiv A E E) := ⟨fun U V ↦ V.trans U⟩
instance instInv : Inv (UnitaryEquiv A E E) := ⟨symm⟩

theorem one_def : (1 : UnitaryEquiv A E E) = refl A E := by rfl
theorem mul_def (U V : UnitaryEquiv A E E) : U * V = V.trans U := by rfl
theorem inv_def (U : UnitaryEquiv A E E) : U⁻¹ = U.symm := by rfl

@[simp] theorem one_apply (x : E) : (1 : UnitaryEquiv A E E) x = x := by rfl
@[simp] theorem mul_apply (U V : UnitaryEquiv A E E) (x : E) : (U * V) x = U (V x) := by rfl
@[simp] theorem inv_apply (U : UnitaryEquiv A E E) (x : E) : U⁻¹ x = U.symm x := by rfl

instance instGroup : Group (UnitaryEquiv A E E) where
  one_mul _ := by rfl
  mul_one _ := by rfl
  mul_assoc _ _ _ := by rfl
  inv_mul_cancel U := by exact U.self_trans_symm

/-- The group of unitary equivalences of `E` is canonically isomorphic to the unitary group
`unitary (Adjointable A E E)` of the endomorphism star-ring. -/
def equivUnitary : UnitaryEquiv A E E ≃* unitary (Adjointable A E E) where
  toFun U := ⟨U.toAdjointable, by
    rw [Unitary.mem_iff, Adjointable.star_def, Adjointable.mul_def, Adjointable.mul_def]
    exact ⟨U.adjoint_comp_toAdjointable, U.toAdjointable_comp_adjoint⟩⟩
  invFun T := ofAdjointable T.1
    (by simpa only [Adjointable.star_def, Adjointable.mul_def] using T.2.1)
    (by simpa only [Adjointable.star_def, Adjointable.mul_def] using T.2.2)
  left_inv U := by exact ofAdjointable_toAdjointable U
  right_inv T := by exact Subtype.ext (toAdjointable_ofAdjointable _ _ _)
  map_mul' U V := by
    refine Subtype.ext ?_
    simp only [Submonoid.coe_mul, mul_def, toAdjointable_trans, Adjointable.mul_def]

@[simp]
theorem coe_equivUnitary_apply (U : UnitaryEquiv A E E) :
    (equivUnitary U : Adjointable A E E) = U.toAdjointable := by rfl

@[simp]
theorem equivUnitary_symm_apply_apply (T : unitary (Adjointable A E E)) (x : E) :
    equivUnitary.symm T x = (T : Adjointable A E E) x := by
  simp [equivUnitary]

end Basic

section Right

variable {B E F : Type*}
  [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- Right-module form of `UnitaryEquiv.inner_map` for `CStarModule Bᵐᵒᵖ`. -/
theorem unop_inner_map (U : UnitaryEquiv Bᵐᵒᵖ E F) (x y : E) :
    unop (inner Bᵐᵒᵖ (U x) (U y)) = unop (inner Bᵐᵒᵖ x y) := by
  rw [U.inner_map]

/-- Every unitary equivalence of right Hilbert `B`-modules commutes with the right `B`-action. -/
theorem map_op_smul (U : UnitaryEquiv Bᵐᵒᵖ E F) (b : B) (x : E) :
    U (op b • x) = op b • U x :=
  U.map_smul_coeff (op b) x

end Right

end UnitaryEquiv

namespace Adjointable

/-- An adjointable endomorphism `T : Adjointable A E E` belongs to `unitary (Adjointable A E E)` if
and only if `T` is surjective and preserves the `A`-valued inner product. -/
theorem mem_unitary_iff_surjective_and_inner {A E : Type*}
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    {T : Adjointable A E E} :
    T ∈ unitary (Adjointable A E E) ↔
      Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  refine ⟨fun hT ↦ ?_, fun ⟨hsurj, hinner⟩ ↦ ?_⟩
  · let U := UnitaryEquiv.equivUnitary.symm ⟨T, hT⟩
    have hUT : ⇑U = ⇑T := funext (UnitaryEquiv.equivUnitary_symm_apply_apply ⟨T, hT⟩)
    rw [← hUT]
    exact ⟨U.toLinearIsometryEquiv.surjective, U.inner_map⟩
  · let U := UnitaryEquiv.ofSurjectiveInner T hsurj hinner
    have hUT : U.toAdjointable = T := by
      ext x
      simp [U]
    rw [← hUT]
    exact (UnitaryEquiv.equivUnitary U).2

end Adjointable

end CStarModule
