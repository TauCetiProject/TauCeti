/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Idempotent
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.Analysis.CStarAlgebra.Idempotent
import TauCeti.Analysis.CStarAlgebra.Unitary.Polar

/-!
# Projections and projective modules over a unital C⋆-algebra

Over a unital C⋆-algebra `A`, the operator `K₀`-group built from matrix projections agrees with
the algebraic `K₀`-group built from finitely generated projective right `A`-modules. A matrix
projection `p` of size `n` determines the projective module `p Aⁿ`, its column range, and

* two projections `p` and `q` have isomorphic modules exactly when they are Murray–von Neumann
  equivalent;
* every finitely generated projective module is isomorphic to `p Aⁿ` for a projection `p`.

The modules `e Aⁿ` and `f Aᵐ` of idempotent matrices are isomorphic exactly when `e` and `f` are
equivalent idempotents, and every finitely generated projective module is of this form. So the
two facts above say that passing from projections to idempotents
(`TauCeti.ProjectionMonoid.toIdempotentMonoid`) is injective and surjective.

Injectivity: if `e = x * y` and `f = y * x`, then `e ⊕ 0` and `0 ⊕ f` are conjugate by an
invertible matrix `a`. When `e` and `f` are projections, the unitary factor of the polar
decomposition of `a` still conjugates `e ⊕ 0` to `0 ⊕ f`
(`Units.polarUnitary_mul_eq_mul_polarUnitary`), and unitarily conjugate projections are
Murray–von Neumann equivalent.

Surjectivity: an idempotent matrix `e` has a range projection `p`, the unique projection with
`e * p = p` and `p * e = e`; these identities say that `e` and `p` have the same column range.

## Main statements

* `Matrix.isMurrayVonNeumannEquivalent_iff_idempotentEquivalent`: matrix projections over a unital
  C⋆-algebra are Murray–von Neumann equivalent exactly when they are equivalent idempotents.
* `IsIdempotentElem.matrix_existsUnique_isStarProjection_mul_eq_right`: every idempotent matrix
  `e` has a unique projection `p` with `e * p = p` and `p * e = e`.
* `TauCeti.ProjectionMonoid.idempotentMonoidEquiv`: the isomorphism `V(A) ≃+ IdempotentMonoid A`
  from the projection monoid to the idempotent monoid.
* `TauCeti.ProjectionKZero.kZeroEquiv`: the isomorphism from the projection `K₀`-group of `A` to
  the split Grothendieck group `TauCeti.KZero A` of finitely generated projective right
  `A`-modules, sending `[p]` to `[p Aⁿ]` (`TauCeti.ProjectionKZero.kZeroEquiv_of_mk`), natural for
  unital star ring homomorphisms (`TauCeti.ProjectionKZero.map_kZeroEquiv`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §1.7.2 and Propositions 4.6.2–4.6.5.
-/

public section

open Matrix

universe u

namespace Matrix

variable {A : Type*} [CStarAlgebra A] {m n : Type*} [Fintype m] [Fintype n]

/-- **Algebraically equivalent projections are Murray–von Neumann equivalent.** If two matrix
projections over a unital C⋆-algebra are equivalent idempotents, they are Murray–von Neumann
equivalent. -/
theorem IdempotentEquivalent.isMurrayVonNeumannEquivalent {p : Matrix m m A} {q : Matrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : IdempotentEquivalent p q) :
    IsMurrayVonNeumannEquivalent p q := by
  classical
  -- `CStarMatrix (m ⊕ n) (m ⊕ n) A` is a C⋆-algebra for the spectral order on `A`.
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  -- An invertible matrix `a` conjugates `P = p ⊕ 0` to `Q = 0 ⊕ q`.
  obtain ⟨a, ha⟩ := h.exists_units_conj_fromBlocks_zero
  set P := Matrix.fromBlocks p 0 0 (0 : Matrix n n A)
  set Q := Matrix.fromBlocks (0 : Matrix m m A) 0 0 q
  have hP : IsStarProjection P := hp.fromBlocks_zero₁₂_zero₂₁ (.zero _)
  have hQ : IsStarProjection Q := (IsStarProjection.zero _).fromBlocks_zero₁₂_zero₂₁ hq
  -- In the C⋆-algebra of C⋆-matrices, `P` and `Q` are similar self-adjoint elements, so a unitary
  -- `w` conjugates `P` to `Q`.
  let e : Matrix (m ⊕ n) (m ⊕ n) A ≃⋆ₐ[ℂ] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
    CStarMatrix.ofMatrixStarAlgEquiv
  have hconj : IsConj (e P) (e Q) := by
    refine ⟨Units.map (MonoidHom.ofClass e) a, ?_⟩
    have haPQ : a.val * P = Q * a.val := by
      rw [← ha, Matrix.mul_assoc _ a⁻¹.val, Units.inv_mul, Matrix.mul_one]
    simpa only [SemiconjBy, map_mul, Units.coe_map, MonoidHom.coe_ofClass] using congrArg e haPQ
  obtain ⟨w, hw, hwPQ⟩ := IsConj.exists_mem_unitary_mul_mul_star_eq hconj
    (CStarMatrix.isSelfAdjoint_ofMatrix_iff.2 hP.isSelfAdjoint)
    (CStarMatrix.isSelfAdjoint_ofMatrix_iff.2 hQ.isSelfAdjoint)
  refine isMurrayVonNeumannEquivalent_of_mem_unitary_mul_fromBlocks_mul_star hp
    (w := e.symm w) (Unitary.map_mem e.symm hw) ?_
  simpa only [map_mul, map_star, StarAlgEquiv.symm_apply_apply] using congrArg e.symm hwPQ

/-- **Murray–von Neumann equivalence is algebraic equivalence.** Matrix projections over a unital
C⋆-algebra are Murray–von Neumann equivalent exactly when they are equivalent idempotents. -/
theorem isMurrayVonNeumannEquivalent_iff_idempotentEquivalent {p : Matrix m m A}
    {q : Matrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsMurrayVonNeumannEquivalent p q ↔ IdempotentEquivalent p q :=
  ⟨IsMurrayVonNeumannEquivalent.idempotentEquivalent,
    IdempotentEquivalent.isMurrayVonNeumannEquivalent hp hq⟩

end Matrix

/-- **Range projections of idempotent matrices.** Every idempotent matrix `e` over a unital
C⋆-algebra has a unique star projection `p` with `e * p = p` and `p * e = e`; these identities say
that `e` and `p` have the same column range. -/
theorem IsIdempotentElem.matrix_existsUnique_isStarProjection_mul_eq_right {A : Type*}
    [CStarAlgebra A] {n : Type*} [Fintype n] {e : Matrix n n A} (he : IsIdempotentElem e) :
    ∃! p : Matrix n n A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  classical
  -- `CStarMatrix n n A` is a C⋆-algebra for the spectral order on `A`.
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  let φ : Matrix n n A ≃+* CStarMatrix n n A := CStarMatrix.ofMatrixRingEquiv
  have key (p : Matrix n n A) : (IsStarProjection p ∧ e * p = p ∧ p * e = e) ↔
      (IsStarProjection (φ p) ∧ φ e * φ p = φ p ∧ φ p * φ e = φ e) := by
    simp only [← map_mul, φ.injective.eq_iff]
    exact and_congr_left' CStarMatrix.isStarProjection_ofMatrix_iff.symm
  obtain ⟨P, hP, huniq⟩ := (he.map φ).existsUnique_isStarProjection_mul_eq_right
  refine ⟨φ.symm P, (key _).2 (by simpa using hP), fun p hp ↦ φ.injective ?_⟩
  simpa using huniq (φ p) ((key p).1 hp)

namespace TauCeti

namespace ProjectionMonoid

variable {A : Type*} [CStarAlgebra A] {m : Type*} [Fintype m]

/-- Over a unital C⋆-algebra, passing from projections to idempotents is injective on classes. -/
theorem toIdempotentMonoid_injective : Function.Injective (toIdempotentMonoid (R := A)) := by
  intro x y hxy
  induction x using ind with | mk _ p hp => ?_
  induction y using ind with | mk _ q hq => ?_
  rw [toIdempotentMonoid_mk, toIdempotentMonoid_mk, IdempotentMonoid.mk_eq_mk_iff] at hxy
  exact mk_eq_mk (hxy.isMurrayVonNeumannEquivalent hp hq)

/-- Over a unital C⋆-algebra, every idempotent matrix has the class of a projection. -/
theorem toIdempotentMonoid_surjective : Function.Surjective (toIdempotentMonoid (R := A)) := by
  intro x
  induction x using IdempotentMonoid.ind with | mk _ e he => ?_
  obtain ⟨p, ⟨hp, hep, hpe⟩, -⟩ := he.matrix_existsUnique_isStarProjection_mul_eq_right
  exact ⟨mk p hp, toIdempotentMonoid_mk_eq_mk he hp hep hpe⟩

variable (A) in
/-- **Projections and idempotents give the same monoid.** Over a unital C⋆-algebra `A`, the
projection monoid `V(A)` of matrix projections modulo Murray–von Neumann equivalence is isomorphic
to the idempotent monoid of `A`, the monoid of isomorphism classes of finitely generated projective
right `A`-modules. -/
noncomputable def idempotentMonoidEquiv : ProjectionMonoid A ≃+ IdempotentMonoid A :=
  AddEquiv.ofBijective toIdempotentMonoid
    ⟨toIdempotentMonoid_injective, toIdempotentMonoid_surjective⟩

/-- `TauCeti.ProjectionMonoid.idempotentMonoidEquiv` is
`TauCeti.ProjectionMonoid.toIdempotentMonoid`. -/
@[simp]
theorem idempotentMonoidEquiv_apply (x : ProjectionMonoid A) :
    idempotentMonoidEquiv A x = toIdempotentMonoid x :=
  (rfl)

/-- The inverse of `TauCeti.ProjectionMonoid.idempotentMonoidEquiv` sends the class of an
idempotent matrix `e` to the class of any projection `p` with `e * p = p` and `p * e = e`. -/
theorem idempotentMonoidEquiv_symm_mk {e p : Matrix m m A} (he : IsIdempotentElem e)
    (hp : IsStarProjection p) (hep : e * p = p) (hpe : p * e = e) :
    (idempotentMonoidEquiv A).symm (IdempotentMonoid.mk e he) = mk p hp :=
  (idempotentMonoidEquiv A).symm_apply_eq.2 (toIdempotentMonoid_mk_eq_mk he hp hep hpe).symm

end ProjectionMonoid

namespace ProjectionKZero

open _root_.Algebra (GrothendieckAddGroup)

variable (A : Type u) [CStarAlgebra A]

/-- **The projection `K₀`-group is the `K₀`-group of projective modules.** Over a unital
C⋆-algebra `A`, the Grothendieck group of matrix projections is isomorphic to the split
Grothendieck group `TauCeti.KZero A` of finitely generated projective right `A`-modules, by
`[p] ↦ [p Aⁿ]` (`TauCeti.ProjectionKZero.kZeroEquiv_of_mk`). -/
noncomputable def kZeroEquiv : ProjectionKZero A ≃+ KZero A :=
  (GrothendieckAddGroup.congr (ProjectionMonoid.idempotentMonoidEquiv A)).trans
    (IdempotentMonoid.kZeroEquiv A)

variable {A}

/-- On the image of `V(A)`, `TauCeti.ProjectionKZero.kZeroEquiv` is the class map of the
idempotent monoid. -/
theorem kZeroEquiv_of (x : ProjectionMonoid A) :
    kZeroEquiv A (GrothendieckAddGroup.of x) =
      IdempotentMonoid.toKZero A (ProjectionMonoid.toIdempotentMonoid x) := by
  rw [kZeroEquiv, AddEquiv.trans_apply, GrothendieckAddGroup.congr_of,
    ProjectionMonoid.idempotentMonoidEquiv_apply, IdempotentMonoid.kZeroEquiv_of]

/-- `TauCeti.ProjectionKZero.kZeroEquiv` sends the class of a matrix projection `p` to the class
of any module isomorphic to its column range `p Aⁿ`. -/
theorem kZeroEquiv_of_mk {m : Type*} [Fintype m] {p : Matrix m m A} (hp : IsStarProjection p)
    (X : FiniteProjectiveRight A)
    (θ : X.obj ≃ₗ[Aᵐᵒᵖ] LinearMap.range (p.mulVecBilin A Aᵐᵒᵖ)) :
    kZeroEquiv A (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) = SplitK0.of.{u} X := by
  rw [kZeroEquiv_of, ProjectionMonoid.toIdempotentMonoid_mk, ← IdempotentMonoid.kZeroEquiv_of,
    IdempotentMonoid.kZeroEquiv_of_mk _ X θ]

/-- **Naturality.** For a unital star ring homomorphism `f : A → B` of unital C⋆-algebras,
`TauCeti.ProjectionKZero.kZeroEquiv` carries the map `K₀(f)` of projection `K₀`-groups to the map of
projective-module `K₀`-groups given by extension of scalars along `f`. -/
theorem map_comp_kZeroEquiv {B : Type u} [CStarAlgebra B] {F : Type*} [FunLike F A B]
    [RingHomClass F A B] [StarHomClass F A B] (f : F) :
    (SplitK0.map.{u, u} (RingHom.op (f : A →+* B)).finiteProjectiveModulesExtendScalars).comp
        (kZeroEquiv A).toAddMonoidHom =
      (kZeroEquiv B).toAddMonoidHom.comp (map (NonUnitalStarRingHom.ofClass f)) := by
  have hf : (f : A →+* B).toNonUnitalRingHom =
      (NonUnitalStarRingHom.ofClass f).toNonUnitalRingHom :=
    NonUnitalRingHom.ext fun _ ↦ rfl
  refine GrothendieckAddGroup.addHom_ext fun a ↦ ?_
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [kZeroEquiv_of, IdempotentMonoid.map_toKZero, map_of, kZeroEquiv_of, hf,
    ProjectionMonoid.map_toIdempotentMonoid]

/-- **Naturality**, pointwise: `TauCeti.ProjectionKZero.kZeroEquiv` carries `K₀(f)` to extension
of scalars along `f`. -/
theorem map_kZeroEquiv {B : Type u} [CStarAlgebra B] {F : Type*} [FunLike F A B]
    [RingHomClass F A B] [StarHomClass F A B] (f : F) (x : ProjectionKZero A) :
    SplitK0.map.{u, u} (RingHom.op (f : A →+* B)).finiteProjectiveModulesExtendScalars
        (kZeroEquiv A x) =
      kZeroEquiv B (map (NonUnitalStarRingHom.ofClass f) x) :=
  DFunLike.congr_fun (map_comp_kZeroEquiv f) x

end ProjectionKZero

end TauCeti
