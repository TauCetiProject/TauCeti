/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Field
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.RingTheory.Trace.Basic

/-!
# Scharlau transfer of quadratic forms

The Scharlau transfer along a linear functional `s : L →ₗ[K] K` is the composite `s ∘ Q`,
on the underlying `K`-space. It is built from Mathlib's `LinearMap.compQuadraticMap'`.
It commutes with orthogonal sums and composition of functionals, and carries isometries
over `L` to isometries over `K`.

For field extensions of characteristic different from two, a nonzero functional preserves
the radical, after restriction of scalars, and hence preserves and reflects nondegeneracy.
Neither finiteness nor separability is needed for this assertion. Finiteness is needed to
compare arbitrary nonzero functionals, and separability makes the trace a nonzero choice.
The dimension of the transferred space is given by `Module.finrank_mul_finrank`.

This is the form-level construction used to transfer isometry classes and Witt classes.
Transfer is additive; it is not in general multiplicative on Witt rings.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

namespace QuadraticMap

section Semiring

variable {K L V W : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  [AddCommMonoid V] [Module L V] [Module K V] [IsScalarTower K L V]
  [AddCommMonoid W] [Module L W] [Module K W] [IsScalarTower K L W]

/-- The Scharlau transfer of `Q` along `s`, on the underlying space over the smaller ring.
Nonzeroness of `s` is required for preservation of regularity, not for this definition. -/
def scharlauTransfer (Q : QuadraticForm L V) (s : L →ₗ[K] K) : QuadraticForm K V :=
  s.compQuadraticMap' Q

@[simp]
theorem scharlauTransfer_apply (Q : QuadraticForm L V) (s : L →ₗ[K] K) (x : V) :
    Q.scharlauTransfer s x = s (Q x) := (rfl)

/-- The zero form transfers to the zero form. -/
@[simp]
theorem scharlauTransfer_zero (s : L →ₗ[K] K) :
    (0 : QuadraticForm L V).scharlauTransfer s = 0 := by
  ext x
  simp

/-- Transfer along the zero functional is zero. -/
@[simp]
theorem scharlauTransfer_zero_functional (Q : QuadraticForm L V) :
    Q.scharlauTransfer (0 : L →ₗ[K] K) = 0 := by
  ext x
  simp

/-- Transfer preserves addition of forms. -/
@[simp]
theorem scharlauTransfer_add (Q R : QuadraticForm L V) (s : L →ₗ[K] K) :
    (Q + R).scharlauTransfer s = Q.scharlauTransfer s + R.scharlauTransfer s := by
  ext x
  simp

/-- Transfer commutes with scaling by an element of the smaller ring. -/
@[simp]
theorem scharlauTransfer_smul (Q : QuadraticForm L V) (s : L →ₗ[K] K) (c : K) :
    (c • Q).scharlauTransfer s = c • Q.scharlauTransfer s := by
  ext x
  simp

/-- Transfer along the identity functional leaves a form unchanged. -/
@[simp]
theorem scharlauTransfer_id (Q : QuadraticForm L V) :
    Q.scharlauTransfer (LinearMap.id : L →ₗ[L] L) = Q := by
  ext x
  simp

/-- Transfer commutes with orthogonal sum. -/
@[simp]
theorem scharlauTransfer_prod (Q : QuadraticForm L V) (R : QuadraticForm L W)
    (s : L →ₗ[K] K) :
    (Q.prod R).scharlauTransfer s = (Q.scharlauTransfer s).prod (R.scharlauTransfer s) := by
  ext x
  simp

/-- Transfer commutes with pullback along an `L`-linear map, viewed as a `K`-linear map. -/
@[simp]
theorem scharlauTransfer_comp (Q : QuadraticForm L V) (s : L →ₗ[K] K) (f : W →ₗ[L] V) :
    (Q.comp f).scharlauTransfer s = (Q.scharlauTransfer s).comp (f.restrictScalars K) := by
  ext x
  simp

/-- Multiplying the input to the functional scales the form before transfer. -/
theorem scharlauTransfer_comp_mul (Q : QuadraticForm L V) (s : L →ₗ[K] K) (a : L) :
    Q.scharlauTransfer (s.comp (LinearMap.mul K L a)) = (a • Q).scharlauTransfer s := by
  ext x
  simp [smul_eq_mul]

end Semiring

section Tower

variable {K L E V : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring E]
  [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
  [AddCommMonoid V] [Module E V] [Module L V] [Module K V]
  [IsScalarTower L E V] [IsScalarTower K E V] [IsScalarTower K L V]

/-- Transfer is transitive in a tower of scalar rings. -/
@[simp]
theorem scharlauTransfer_scharlauTransfer (Q : QuadraticForm E V)
    (t : E →ₗ[L] L) (s : L →ₗ[K] K) :
    (Q.scharlauTransfer t).scharlauTransfer s =
      Q.scharlauTransfer (s.comp (t.restrictScalars K)) := by
  ext x
  simp

end Tower

section Trace

variable {K L V : Type*} [CommRing K] [CommRing L] [Algebra K L]
  [AddCommMonoid V] [Module L V] [Module K V] [IsScalarTower K L V]

variable (K) in
/-- Transfer along the algebra trace. For a finite separable field extension the functional is
nonzero, by `Algebra.trace_ne_zero`. -/
noncomputable def traceTransfer (Q : QuadraticForm L V) : QuadraticForm K V :=
  Q.scharlauTransfer (Algebra.trace K L)

theorem traceTransfer_apply (Q : QuadraticForm L V) (x : V) :
    Q.traceTransfer K x = Algebra.trace K L (Q x) := (rfl)

/-- Trace transfer is Scharlau transfer along the algebra trace. -/
@[simp]
theorem traceTransfer_eq_scharlauTransfer (Q : QuadraticForm L V) :
    Q.traceTransfer K = Q.scharlauTransfer (Algebra.trace K L) := (rfl)

/-- The trace transfer of the one-dimensional unit form is the quadratic trace form. -/
theorem traceTransfer_sq :
    (QuadraticMap.sq (R := L) (A := L)).traceTransfer K =
      (Algebra.traceForm K L).toQuadraticMap := by
  ext x
  simp [QuadraticMap.sq_apply, Algebra.traceForm_apply]

end Trace

section Ring

variable {K L V : Type*} [CommRing K] [CommRing L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- Transfer preserves negation of forms. -/
@[simp]
theorem scharlauTransfer_neg (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    (-Q).scharlauTransfer s = -Q.scharlauTransfer s := by
  ext x
  simp

/-- Transfer preserves subtraction of forms. -/
@[simp]
theorem scharlauTransfer_sub (Q R : QuadraticForm L V) (s : L →ₗ[K] K) :
    (Q - R).scharlauTransfer s = Q.scharlauTransfer s - R.scharlauTransfer s := by
  ext x
  simp

/-- The polar form of a transfer is obtained by applying the functional to the polar form. -/
@[simp]
theorem polar_scharlauTransfer (Q : QuadraticForm L V) (s : L →ₗ[K] K) (x y : V) :
    QuadraticMap.polar (Q.scharlauTransfer s) x y = s (QuadraticMap.polar Q x y) :=
  s.compQuadraticMap_polar Q x y

/-- A Frobenius functional preserves the radical when two is invertible. -/
@[simp]
theorem radical_scharlauTransfer [Invertible (2 : K)]
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (hs : s.IsFrobeniusFunctional) :
    (Q.scharlauTransfer s).radical = Q.radical.restrictScalars K := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  simp only [QuadraticMap.radical_eq_ker_polarBilin]
  ext x
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.ext_iff,
    LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply, polar_scharlauTransfer]
  constructor
  · intro hx y
    apply hs.eq_zero_of_forall_right
    intro a
    simpa only [QuadraticMap.polar_smul_right, smul_eq_mul] using hx (a • y)
  · intro hx y
    simp [hx y]

/-- Transfer along a Frobenius functional preserves and reflects regularity. -/
@[simp]
theorem nondegenerate_scharlauTransfer_iff [Invertible (2 : K)]
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (hs : s.IsFrobeniusFunctional) :
    (Q.scharlauTransfer s).Nondegenerate ↔ Q.Nondegenerate := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot,
    Q.radical_scharlauTransfer s hs, Submodule.restrictScalars_eq_bot_iff,
    QuadraticMap.nondegenerate_iff_radical_eq_bot]

end Ring

section Field

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- A nonzero functional preserves the radical in characteristic different from two. -/
theorem radical_scharlauTransfer_of_ne_zero [Invertible (2 : K)]
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (hs : s ≠ 0) :
    (Q.scharlauTransfer s).radical = Q.radical.restrictScalars K :=
  Q.radical_scharlauTransfer s (s.isFrobeniusFunctional_iff_ne_zero.mpr hs)

/-- Transfer along a nonzero functional preserves and reflects regularity over fields. -/
theorem nondegenerate_scharlauTransfer_iff_of_ne_zero [Invertible (2 : K)]
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (hs : s ≠ 0) :
    (Q.scharlauTransfer s).Nondegenerate ↔ Q.Nondegenerate :=
  Q.nondegenerate_scharlauTransfer_iff s (s.isFrobeniusFunctional_iff_ne_zero.mpr hs)

/-- Over a finite field extension, changing between any two nonzero functionals amounts to
scaling the form by a unit before transfer. -/
theorem exists_unit_scharlauTransfer_eq [FiniteDimensional K L]
    (Q : QuadraticForm L V) (s t : L →ₗ[K] K) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Lˣ, Q.scharlauTransfer t = ((a : L) • Q).scharlauTransfer s := by
  obtain ⟨a, ha, _⟩ := s.existsUnique_unit_apply_eq_apply_mul t hs ht
  exact ⟨a, QuadraticMap.ext fun x => by simpa [smul_eq_mul] using ha (Q x)⟩

/-- Trace transfer is regular exactly when the original form is, for a finite separable
extension in characteristic different from two. -/
theorem nondegenerate_traceTransfer_iff [Invertible (2 : K)]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (Q : QuadraticForm L V) :
    (Q.traceTransfer K).Nondegenerate ↔ Q.Nondegenerate := by
  rw [traceTransfer_eq_scharlauTransfer]
  exact Q.nondegenerate_scharlauTransfer_iff_of_ne_zero _ (Algebra.trace_ne_zero K L)

end Field

section Isometry

variable {K L V W : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  [AddCommMonoid V] [Module L V] [Module K V] [IsScalarTower K L V]
  [AddCommMonoid W] [Module L W] [Module K W] [IsScalarTower K L W]
  {Q : QuadraticForm L V} {R : QuadraticForm L W}

/-- An isometry over the larger ring induces an isometry of transferred forms. -/
def IsometryEquiv.scharlauTransfer (e : Q.IsometryEquiv R) (s : L →ₗ[K] K) :
    (Q.scharlauTransfer s).IsometryEquiv (R.scharlauTransfer s) where
  toLinearEquiv := e.toLinearEquiv.restrictScalars K
  map_app' x := by simp

@[simp]
theorem IsometryEquiv.scharlauTransfer_apply (e : Q.IsometryEquiv R) (s : L →ₗ[K] K) (x : V) :
    e.scharlauTransfer s x = e x := (rfl)

/-- Transfer respects isometry classes. -/
theorem Equivalent.scharlauTransfer (h : Q.Equivalent R) (s : L →ₗ[K] K) :
    (Q.scharlauTransfer s).Equivalent (R.scharlauTransfer s) :=
  h.map fun e => e.scharlauTransfer s

end Isometry

end QuadraticMap
