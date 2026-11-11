/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TraceFunctional.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# C*-norms from faithful positive functionals

A faithful positive functional on a finite-dimensional unital star algebra makes the algebra
a Hilbert space with inner product `⟪x, y⟫ = τ (star x * y)`. Left multiplication is a faithful
star representation on that Hilbert space. Its operator norm therefore makes the original
algebra a C*-algebra. In particular, this constructs the C*-norm on finite-dimensional
quotients equipped with a faithful positive trace, without presupposing an algebra norm.

The functional need not be tracial. Positivity and Hermitian symmetry are expressed using
`LinearMap.IsPosSemidef` for `LinearMap.traceSesqForm`; faithfulness says that its diagonal
vanishes only at zero. The Hilbert norm and the algebra norm are distinct: the latter is the
operator norm of left multiplication for the former. All norm structures here are explicit
definitions, so they can be installed locally without changing a pre-existing norm.

## Main constructions

* `LinearMap.TraceHilbert`: the Hilbert space supplied by the functional.
* `LinearMap.traceRegularRep`: the faithful left regular star representation.
* `LinearMap.traceNormedRing`: the operator norm pulled back along that representation.
* `LinearMap.traceCStarAlgebra`: the resulting complex C*-algebra structure.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Sections 4.4–4.5,
  for the application to positive trace quotients of Temperley–Lieb algebras.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace LinearMap

variable {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A]
  (τ : A →ₗ[𝕜] 𝕜) (hτ : τ.traceSesqForm.IsPosSemidef)
  (hfaith : ∀ x, τ (star x * x) = 0 → x = 0)

/-- A copy of the algebra carrying the Hilbert norm of the functional, kept separate from
the operator norm subsequently placed on the algebra itself. -/
def TraceHilbert (_τ : A →ₗ[𝕜] 𝕜) (_hτ : _τ.traceSesqForm.IsPosSemidef)
    (_hfaith : ∀ x, _τ (star x * x) = 0 → x = 0) := A

namespace TraceHilbert

instance : AddCommGroup (TraceHilbert τ hτ hfaith) := inferInstanceAs (AddCommGroup A)
instance : Module 𝕜 (TraceHilbert τ hτ hfaith) := inferInstanceAs (Module 𝕜 A)

/-- Identify the algebra with its functional Hilbert space as a vector space. -/
def equiv : A ≃ₗ[𝕜] TraceHilbert τ hτ hfaith := LinearEquiv.refl 𝕜 A

instance : InnerProductSpace.Core 𝕜 (TraceHilbert τ hτ hfaith) where
  inner x y := τ (star ((equiv τ hτ hfaith).symm x) * (equiv τ hτ hfaith).symm y)
  conj_inner_symm x y := by
    simpa only [traceSesqForm_apply] using
      hτ.isSymm.eq ((equiv τ hτ hfaith).symm y) ((equiv τ hτ hfaith).symm x)
  re_inner_nonneg x := by
    simpa only [map_zero, traceSesqForm_apply] using
      RCLike.re_le_re (hτ.isNonneg.nonneg ((equiv τ hτ hfaith).symm x))
  add_left x y z := by simp [add_mul]
  smul_left x y r := by simp
  definite x hx := by
    apply (equiv τ hτ hfaith).symm.injective
    simpa only [map_zero] using hfaith _ hx

instance : NormedAddCommGroup (TraceHilbert τ hτ hfaith) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := 𝕜)

instance : InnerProductSpace 𝕜 (TraceHilbert τ hτ hfaith) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core 𝕜 _)

/-- The Hilbert inner product is the sesquilinear form of the functional. -/
theorem inner_def (x y : TraceHilbert τ hτ hfaith) :
    inner 𝕜 x y = τ (star ((equiv τ hτ hfaith).symm x) * (equiv τ hτ hfaith).symm y) := (rfl)

/-- The vector-space identification carries the trace form to the Hilbert inner product. -/
@[simp]
theorem inner_equiv (x y : A) :
    inner 𝕜 (equiv τ hτ hfaith x) (equiv τ hτ hfaith y) = τ (star x * y) := by
  simp only [inner_def, LinearEquiv.symm_apply_apply]

instance [FiniteDimensional 𝕜 A] : FiniteDimensional 𝕜 (TraceHilbert τ hτ hfaith) :=
  inferInstanceAs (FiniteDimensional 𝕜 A)

instance [FiniteDimensional 𝕜 A] : CompleteSpace (TraceHilbert τ hτ hfaith) :=
  FiniteDimensional.complete 𝕜 _

end TraceHilbert

variable [FiniteDimensional 𝕜 A]

private def traceRegularAlgHom :
    A →ₐ[𝕜] (TraceHilbert τ hτ hfaith →L[𝕜] TraceHilbert τ hτ hfaith) :=
  (Module.End.toContinuousLinearMap (TraceHilbert τ hτ hfaith)).toAlgHom.comp
    (((TraceHilbert.equiv τ hτ hfaith).conjAlgEquiv 𝕜).toAlgHom.comp (Algebra.lmul 𝕜 A))

/-- Left multiplication on the Hilbert space of a faithful positive functional, as a unital
star representation. Finite dimensionality guarantees boundedness of every left multiplier. -/
def traceRegularRep : A →⋆ₐ[𝕜] (TraceHilbert τ hτ hfaith →L[𝕜] TraceHilbert τ hτ hfaith) where
  toAlgHom := τ.traceRegularAlgHom hτ hfaith
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    have happly (a : A) (x : TraceHilbert τ hτ hfaith) :
        τ.traceRegularAlgHom hτ hfaith a x =
          TraceHilbert.equiv τ hτ hfaith (a * (TraceHilbert.equiv τ hτ hfaith).symm x) := rfl
    simp [happly, TraceHilbert.inner_def, star_mul, mul_assoc]

/-- The regular representation acts by left multiplication under the vector-space
identification with the algebra. -/
@[simp]
theorem traceRegularRep_apply (a : A) (x : TraceHilbert τ hτ hfaith) :
    τ.traceRegularRep hτ hfaith a x =
      TraceHilbert.equiv τ hτ hfaith (a * (TraceHilbert.equiv τ hτ hfaith).symm x) := (rfl)

/-- The regular representation is faithful: evaluate at the vector corresponding to `1`. -/
theorem traceRegularRep_injective : Function.Injective (τ.traceRegularRep hτ hfaith) := by
  intro a b hab
  have h := DFunLike.congr_fun hab (TraceHilbert.equiv τ hτ hfaith 1)
  simpa only [traceRegularRep_apply, LinearEquiv.symm_apply_apply, mul_one,
    EmbeddingLike.apply_eq_iff_eq] using h

/-- The algebra norm of a faithful positive functional is the operator norm of left
multiplication on its Hilbert space. -/
-- The constructor is exposed so its underlying ring remains definitionally the original ring.
@[expose, instance_reducible]
def traceNormedRing : NormedRing A :=
  NormedRing.induced A (TraceHilbert τ hτ hfaith →L[𝕜] TraceHilbert τ hτ hfaith)
    (τ.traceRegularRep hτ hfaith) (τ.traceRegularRep_injective hτ hfaith)

/-- The induced algebra norm is the operator norm of the regular representation. -/
theorem traceNormedRing_norm (a : A) :
    @norm A (τ.traceNormedRing hτ hfaith).toNorm a = ‖τ.traceRegularRep hτ hfaith a‖ := (rfl)

/-- The operator norm of left multiplication is compatible with scalar multiplication. -/
-- Expose the constructor to preserve the given algebra and scalar action.
@[expose, instance_reducible]
def traceNormedAlgebra :
    letI := τ.traceNormedRing hτ hfaith
    NormedAlgebra 𝕜 A := by
  letI := τ.traceNormedRing hτ hfaith
  exact NormedAlgebra.induced 𝕜 A _ (τ.traceRegularRep hτ hfaith)

/-- The operator norm of left multiplication satisfies the C*-identity. -/
theorem traceCStarRing :
    letI := τ.traceNormedRing hτ hfaith
    CStarRing A := by
  let := τ.traceNormedRing hτ hfaith
  exact ⟨fun a ↦ by
    simp only [traceNormedRing_norm, map_mul, map_star]
    exact CStarRing.norm_mul_self_le _⟩

end LinearMap

namespace LinearMap

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [FiniteDimensional ℂ A]

/-- A finite-dimensional unital complex star algebra with a faithful positive functional is a
C*-algebra under the operator norm of left multiplication on its functional Hilbert space.
In particular this applies to a faithful positive trace. Completeness follows from finite
dimensionality. No norm on the algebra is assumed. -/
-- The constructor is exposed to retain the original ring, algebra and scalar action.
@[expose, instance_reducible]
def traceCStarAlgebra (τ : A →ₗ[ℂ] ℂ) (hτ : τ.traceSesqForm.IsPosSemidef)
    (hfaith : ∀ x, τ (star x * x) = 0 → x = 0) : CStarAlgebra A := by
  letI := τ.traceNormedRing hτ hfaith
  letI := τ.traceNormedAlgebra hτ hfaith
  letI := τ.traceCStarRing hτ hfaith
  exact {
    toCompleteSpace := FiniteDimensional.complete ℂ A
    toStarModule := inferInstance }

/-- The C*-algebra structure uses the left regular operator norm. -/
theorem traceCStarAlgebra_norm (τ : A →ₗ[ℂ] ℂ) (hτ : τ.traceSesqForm.IsPosSemidef)
    (hfaith : ∀ x, τ (star x * x) = 0 → x = 0) (a : A) :
    @norm A (τ.traceCStarAlgebra hτ hfaith).toNorm a = ‖τ.traceRegularRep hτ hfaith a‖ :=
  τ.traceNormedRing_norm hτ hfaith a

end LinearMap
