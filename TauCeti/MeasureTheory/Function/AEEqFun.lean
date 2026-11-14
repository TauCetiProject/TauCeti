/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Algebraic structure and sum equality on almost-everywhere equivalence classes

Two classes in `α →ₘ[μ] β` are equal exactly when their representatives agree almost everywhere,
and the representative of a sum is the sum of the representatives almost everywhere. Combining
these, an identity `a + b = c + d` between sums of classes is an almost-everywhere identity between
the sums of their representatives (`MeasureTheory.AEEqFun.add_eq_add_iff_ae_eq`). This is the form
in which a decomposition of a function into two summands, each in its own function space, is
compared with another such decomposition.

When the target is a topological (semi)ring, pointwise operations descend to `α →ₘ[μ] R`:
Mathlib supplies the additive group, multiplicative monoid, and module instances on `AEEqFun`, and
this file completes the hierarchy with `Semiring`, `CommSemiring`, `Ring`, `CommRing`, and
`Algebra` instances via `MeasureTheory.AEEqFun.toGerm_injective`.
-/

public noncomputable section

namespace MeasureTheory.AEEqFun

/-- Two sums in `α →ₘ[μ] β` are equal exactly when the sums of their representatives agree almost
everywhere. -/
theorem add_eq_add_iff_ae_eq {α β : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [TopologicalSpace β] [Add β] [ContinuousAdd β] {a b c d : α →ₘ[μ] β} :
    a + b = c + d ↔ ⇑a + ⇑b =ᵐ[μ] ⇑c + ⇑d := by
  rw [AEEqFun.ext_iff, (AEEqFun.coeFn_add a b).congr_left, (AEEqFun.coeFn_add c d).congr_right]

section Ring

variable {α 𝕜 R : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace R]

instance instNatCast [NatCast R] : NatCast (α →ₘ[μ] R) :=
  ⟨fun n => const α (n : R)⟩

/-- Natural-number cast on `α →ₘ[μ] R` is the constant class `const α n`. -/
theorem natCast_def [NatCast R] (n : ℕ) : (n : α →ₘ[μ] R) = const α (n : R) :=
  (rfl)

/-- Representative of `(n : α →ₘ[μ] R)` agrees with the constant `(n : R)` almost everywhere. -/
theorem coeFn_natCast [NatCast R] (n : ℕ) : ⇑(n : α →ₘ[μ] R) =ᵐ[μ] Function.const α (n : R) :=
  coeFn_const (μ := μ) α (n : R)

@[simp]
theorem coeFn_natCast_eq [NeZero μ] [NatCast R] (n : ℕ) (x : α) : (n : α →ₘ[μ] R) x = n :=
  coeFn_const_eq (μ := μ) α (n : R) x

@[simp]
theorem natCast_toGerm [NatCast R] (n : ℕ) : ((n : α →ₘ[μ] R)).toGerm = n :=
  (rfl)

instance instIntCast [IntCast R] : IntCast (α →ₘ[μ] R) :=
  ⟨fun n => const α (n : R)⟩

/-- Integer cast on `α →ₘ[μ] R` is the constant class `const α n`. -/
theorem intCast_def [IntCast R] (n : ℤ) : (n : α →ₘ[μ] R) = const α (n : R) :=
  (rfl)

/-- Representative of `(n : α →ₘ[μ] R)` agrees with the constant `(n : R)` almost everywhere. -/
theorem coeFn_intCast [IntCast R] (n : ℤ) : ⇑(n : α →ₘ[μ] R) =ᵐ[μ] Function.const α (n : R) :=
  coeFn_const (μ := μ) α (n : R)

@[simp]
theorem coeFn_intCast_eq [NeZero μ] [IntCast R] (n : ℤ) (x : α) : (n : α →ₘ[μ] R) x = n :=
  coeFn_const_eq (μ := μ) α (n : R) x

@[simp]
theorem intCast_toGerm [IntCast R] (n : ℤ) : ((n : α →ₘ[μ] R)).toGerm = n :=
  (rfl)

instance instSemiring [Semiring R] [IsTopologicalSemiring R] : Semiring (α →ₘ[μ] R) :=
  toGerm_injective.semiring toGerm zero_toGerm one_toGerm add_toGerm mul_toGerm
    (fun _ _ => smul_toGerm _ _) pow_toGerm natCast_toGerm

instance instCommSemiring [CommSemiring R] [IsTopologicalSemiring R] :
    CommSemiring (α →ₘ[μ] R) where
  __ := instSemiring
  __ := instCommMonoid

instance instRing [Ring R] [IsTopologicalRing R] : Ring (α →ₘ[μ] R) :=
  toGerm_injective.ring toGerm zero_toGerm one_toGerm add_toGerm mul_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) (fun _ _ => smul_toGerm _ _) pow_toGerm natCast_toGerm
    intCast_toGerm

instance instCommRing [CommRing R] [IsTopologicalRing R] : CommRing (α →ₘ[μ] R) where
  __ := instRing
  __ := instCommMonoid

/-- `MeasureTheory.AEEqFun.toGerm` bundled as a ring homomorphism. -/
def toGermRingHom [Semiring R] [IsTopologicalSemiring R] :
    (α →ₘ[μ] R) →+* (MeasureTheory.ae μ).Germ R where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm
  map_zero' := zero_toGerm
  map_add' := add_toGerm

@[simp]
theorem coe_toGermRingHom [Semiring R] [IsTopologicalSemiring R] :
    ⇑(toGermRingHom : (α →ₘ[μ] R) →+* (MeasureTheory.ae μ).Germ R) = toGerm := by
  rfl

/-- Constant-class embedding of a scalar semiring into `α →ₘ[μ] R` as a ring homomorphism. -/
def constRingHom [Semiring R] [IsTopologicalSemiring R] : R →+* α →ₘ[μ] R where
  toFun r := const α r
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem constRingHom_apply [Semiring R] [IsTopologicalSemiring R] (r : R) :
    (constRingHom r : α →ₘ[μ] R) = const α r := by
  rfl

instance instAlgebra [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    [ContinuousConstSMul 𝕜 R] : Algebra 𝕜 (α →ₘ[μ] R) where
  algebraMap := constRingHom.comp (algebraMap 𝕜 R)
  commutes' c f := ext <| by
    filter_upwards [coeFn_mul (const α (algebraMap 𝕜 R c)) f,
      coeFn_mul f (const α (algebraMap 𝕜 R c)),
      coeFn_const (μ := μ) α (algebraMap 𝕜 R c)] with x h₁ h₂ hc
    simpa [h₁, h₂, hc] using Algebra.commutes c (f x)
  smul_def' c f := ext <| by
    filter_upwards [coeFn_smul c f, coeFn_mul (const α (algebraMap 𝕜 R c)) f,
      coeFn_const (μ := μ) α (algebraMap 𝕜 R c)] with x hsmul hmul hc
    simpa [hsmul, hmul, hc] using Algebra.smul_def c (f x)

@[simp]
theorem algebraMap_apply [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    [ContinuousConstSMul 𝕜 R] (c : 𝕜) :
    algebraMap 𝕜 (α →ₘ[μ] R) c = const α (algebraMap 𝕜 R c) := by
  rfl

/-- Representative of `algebraMap 𝕜 (α →ₘ[μ] R) c` agrees with the constant `algebraMap 𝕜 R c`
almost everywhere. -/
theorem coeFn_algebraMap [CommSemiring 𝕜] [Semiring R] [IsTopologicalSemiring R] [Algebra 𝕜 R]
    [ContinuousConstSMul 𝕜 R] (c : 𝕜) :
    ⇑(algebraMap 𝕜 (α →ₘ[μ] R) c) =ᵐ[μ] Function.const α (algebraMap 𝕜 R c) :=
  coeFn_const (μ := μ) α (algebraMap 𝕜 R c)

end Ring

end MeasureTheory.AEEqFun
