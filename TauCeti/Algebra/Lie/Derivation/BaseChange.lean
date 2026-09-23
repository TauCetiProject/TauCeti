/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.Derivation.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Range

/-!
# Lie derivations after extension of scalars

Let `L` be a Lie algebra over a commutative ring `R` and let `A` be a commutative `R`-algebra.
Mathlib's `Lie.Derivation.ofLieDerivation` extends a derivation `D` of `L` to the base change
`A ⊗[R] L`, but records the result only as a derivation over `R`.  The extension is in fact
`A`-linear, because it is `LinearMap.baseChange`, and `A` is the ring the extended Lie algebra is
an algebra over; `LieDerivation.baseChange` is that sharper packaging.  Every statement below is
about the `A`-linear form, which is the one that can be compared with `LieSubmodule.baseChange`,
whose ideals are ideals over `A`.

The point of the construction is descent.  Extending an ideal is a faithful operation when `A` is
faithfully flat over `R` — a vector lies in an ideal exactly when its canonical image lies in the
extension — so a containment between the image of an ideal under a derivation and another ideal
may be *checked after extending scalars*:

```text
(∀ z ∈ I.baseChange A, D.baseChange A z ∈ J.baseChange A) ↔ ∀ x ∈ I, D x ∈ J
```

The direction that costs nothing is the ascent, and it is a span argument: the extension of an
ideal is generated over `A` by the canonical images `1 ⊗ₜ x` of its own elements, and the extended
derivation sends `1 ⊗ₜ x` to `1 ⊗ₜ D x`.  Descent is the direction that consumes faithful
flatness, and it consumes it in one way only: extending a submodule reflects containments, so
nothing is lost by passing to the extension.

This is the derivation half of the base-change toolkit that lets a structural statement about a
Lie algebra over a field of characteristic zero be proved over an algebraic closure, where
Mathlib's Lie theorem applies, and then descended.

## Main definitions

* `LieDerivation.baseChange`: the `A`-linear extension of a Lie derivation to `A ⊗[R] L`.

## Main results

* `LieDerivation.baseChange_ad`: the extension of an inner derivation `ad x` is the inner
  derivation at `1 ⊗ₜ x`, so the construction is compatible with the adjoint action.
* `LieDerivation.mapsTo_baseChange_iff` and `LieDerivation.mapsTo_baseChange_lieIdeal_iff`:
  **over a faithfully flat coefficient algebra, a derivation maps one submodule, respectively one
  Lie ideal, into another exactly when the extended derivation does so for the extensions.**
* `LieDerivation.range_baseChange_le_baseChange_iff`: a containment of the range of a derivation
  in a submodule may likewise be checked after extending scalars.
* `LieDerivation.isNilpotent_baseChange_iff`: a derivation is nilpotent exactly when its
  extension is.

## Implementation notes

The Leibniz rule is not reproved here: it is read off `Lie.Derivation.ofLieDerivation`, whose
underlying function is the same one (`LieDerivation.coe_ofLieDerivation`).  Only the module
structure that the extension is linear for is new.

The submodule bookkeeping behind the ascent is not specific to derivations, so it lives one level
down, as `LinearMap.map_baseChange` in `TauCeti/LinearAlgebra/TensorProduct/Range.lean`: the image
of an extended submodule under an extended linear map is the extension of the image.

Mathlib provides the extension for a derivation of `L` into `L` and not for one into a general
Lie module `M`, so that is the generality available by reuse and the generality used here; it is
also the one the descent statements need, since they compare the extended derivation with the
extensions of ideals of `L`.
-/

public section

open TensorProduct

namespace LieDerivation

universe u v w

variable {R : Type u} {A : Type v} {L : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

variable (A) in
/-- The extension of a Lie derivation `D` of `L` to the base change `A ⊗[R] L`, as a derivation
over `A`.  Its underlying map is `LinearMap.baseChange`, so it sends `a ⊗ₜ x` to `a ⊗ₜ D x`. -/
def baseChange (D : LieDerivation R L L) : LieDerivation A (A ⊗[R] L) (A ⊗[R] L) where
  toLinearMap := D.toLinearMap.baseChange A
  leibniz' x y := by
    simpa only [Lie.Derivation.ofLieDerivation_apply, LinearMap.baseChange_eq_ltensor] using
      (Lie.Derivation.ofLieDerivation A D).apply_lie_eq_sub x y

/-- The extended derivation differentiates the second factor of a pure tensor. -/
@[simp]
theorem baseChange_apply_tmul (D : LieDerivation R L L) (a : A) (x : L) :
    D.baseChange A (a ⊗ₜ[R] x) = a ⊗ₜ[R] D x :=
  (rfl)

/-- The linear map underlying the extension of `D` is the extension of the linear map underlying
`D`; this is what lets the linear-algebraic base-change API apply to it. -/
theorem coe_baseChange_linearMap (D : LieDerivation R L L) :
    ((D.baseChange A : LieDerivation A (A ⊗[R] L) (A ⊗[R] L)) : A ⊗[R] L →ₗ[A] A ⊗[R] L) =
      D.toLinearMap.baseChange A :=
  (rfl)

/-- The `R`-linear extension `Lie.Derivation.ofLieDerivation` supplied by Mathlib and the
`A`-linear extension `LieDerivation.baseChange` are the same function: only the ring over which
each is recorded as linear differs. -/
theorem coe_ofLieDerivation (D : LieDerivation R L L) :
    ⇑(Lie.Derivation.ofLieDerivation A D) = ⇑(D.baseChange A) :=
  (rfl)

/-- The zero derivation extends to the zero derivation. -/
@[simp]
theorem baseChange_zero : (0 : LieDerivation R L L).baseChange A = 0 := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add y z hy hz => simp [map_add, hy, hz]

/-- Extension of scalars is additive in the derivation. -/
theorem baseChange_add (D E : LieDerivation R L L) :
    (D + E).baseChange A = D.baseChange A + E.baseChange A := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [tmul_add]
  | add y z hy hz => simp [map_add, hy, hz]

/-- Extension of scalars is compatible with the bracket of derivations. -/
theorem baseChange_lie (D E : LieDerivation R L L) :
    (⁅D, E⁆ : LieDerivation R L L).baseChange A = ⁅D.baseChange A, E.baseChange A⁆ := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [tmul_sub]
  | add y z hy hz => simp [map_add, hy, hz]

/-- The extension of the inner derivation at `x` is the inner derivation at `1 ⊗ₜ x`. -/
@[simp]
theorem baseChange_ad (x : L) :
    (ad R L x).baseChange A = ad A (A ⊗[R] L) ((1 : A) ⊗ₜ[R] x) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LieAlgebra.ExtendScalars.bracket_tmul]
  | add y z hy hz => simp [map_add, hy, hz]

section FaithfullyFlat

variable [Module.FaithfullyFlat R A]

/-- Over a faithfully flat coefficient algebra no information is lost by extending a derivation:
two derivations agreeing after extension of scalars are equal. -/
theorem baseChange_injective :
    Function.Injective (baseChange A : LieDerivation R L L → LieDerivation A _ _) := by
  intro D E h
  ext x
  have hx : (1 : A) ⊗ₜ[R] (D x - E x) = 0 := by
    rw [tmul_sub, ← baseChange_apply_tmul D, ← baseChange_apply_tmul E, h, sub_self]
  rw [← sub_eq_zero]
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff R _ (D x - E x)).mp hx

end FaithfullyFlat

section Descent

variable (D : LieDerivation R L L)

/-- **Ascent of a containment of submodules along extension of scalars.**  If `D` maps `p` into
`q`, then the extended derivation maps the extension of `p` into the extension of `q`.  This
direction asks nothing of the coefficient algebra. -/
theorem baseChange_mem_baseChange {p q : Submodule R L} (h : ∀ x ∈ p, D x ∈ q)
    {z : A ⊗[R] L} (hz : z ∈ p.baseChange A) : D.baseChange A z ∈ q.baseChange A := by
  have hz' : D.baseChange A z ∈
      Submodule.map (D.toLinearMap.baseChange A) (p.baseChange A) := ⟨z, hz, rfl⟩
  rw [LinearMap.map_baseChange] at hz'
  refine Submodule.baseChange_mono A ?_ hz'
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

variable [Module.FaithfullyFlat R A]

/-- **A containment of submodules under a derivation may be checked after extending scalars.**
Over a faithfully flat coefficient algebra, the extended derivation maps the extension of `p`
into the extension of `q` exactly when `D` maps `p` into `q`. -/
theorem mapsTo_baseChange_iff (p q : Submodule R L) :
    (∀ z ∈ p.baseChange A, D.baseChange A z ∈ q.baseChange A) ↔ ∀ x ∈ p, D x ∈ q := by
  refine ⟨fun h x hx => ?_, fun h _ hz => baseChange_mem_baseChange D h hz⟩
  have hmem := h ((1 : A) ⊗ₜ[R] x) (Submodule.tmul_mem_baseChange_of_mem (1 : A) hx)
  rwa [baseChange_apply_tmul, Submodule.one_tmul_mem_baseChange_iff] at hmem

/-- **A containment of Lie ideals under a derivation may be checked after extending scalars.**
This is the form in which the descent is used: a structural statement proved over an algebraic
closure, where it is available, descends to the original coefficient field. -/
theorem mapsTo_baseChange_lieIdeal_iff (I J : LieIdeal R L) :
    (∀ z ∈ I.baseChange A, D.baseChange A z ∈ J.baseChange A) ↔ ∀ x ∈ I, D x ∈ J := by
  simp only [← LieSubmodule.mem_toSubmodule, LieSubmodule.coe_baseChange]
  exact mapsTo_baseChange_iff D _ _

/-- **A containment of the range of a derivation may be checked after extending scalars.**  This
is the shape in which a statement like "the derivation lands in the nilradical" descends. -/
theorem range_baseChange_le_baseChange_iff (q : Submodule R L) :
    LinearMap.range (D.toLinearMap.baseChange A) ≤ q.baseChange A ↔
      LinearMap.range D.toLinearMap ≤ q := by
  have h := LinearMap.map_baseChange (A := A) D.toLinearMap ⊤
  rw [Submodule.baseChange_top, Submodule.map_top, Submodule.map_top] at h
  rw [h, Submodule.baseChange_le_iff]

/-- **A derivation is nilpotent exactly when its extension of scalars is.** -/
theorem isNilpotent_baseChange_iff :
    IsNilpotent (D.baseChange A).toLinearMap ↔ IsNilpotent D.toLinearMap := by
  rw [coe_baseChange_linearMap]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  · rw [← LinearMap.baseChange_pow] at hn
    ext x
    have hx : (1 : A) ⊗ₜ[R] ((D.toLinearMap ^ n) x) = 0 := by
      simpa using congrArg (fun f => f ((1 : A) ⊗ₜ[R] x)) hn
    simpa using (Module.FaithfullyFlat.one_tmul_eq_zero_iff R _ _).mp hx
  · rw [← LinearMap.baseChange_pow, hn]
    ext z
    simp

end Descent

end LieDerivation
