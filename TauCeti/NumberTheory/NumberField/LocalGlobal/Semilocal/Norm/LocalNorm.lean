/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units

/-!
# Elements that are norms at a place

For an extension `L/K` of number fields, an element `x ∈ Kˣ` is a *local norm* at a place of `K`
when its image in the completion `K_v` is a norm from the local étale algebra `K_v ⊗[K] L`. Using
the scalar extension, rather than one completion `L_w` above `v`, keeps every place of `L` above
`v`: by `TauCeti.mem_range_normUnits_adicCompletion_iff` the local norms are the products of norms
from all the completions `L_w` with `w ∣ v`. This file defines

* `TauCeti.GlobalNumberFields.finiteLocalNormMap` and
  `TauCeti.GlobalNumberFields.infiniteLocalNormMap`, the norm maps of these local étale algebras
  on units;
* `TauCeti.GlobalNumberFields.IsFiniteLocalNorm`, the local norm condition at a finite place;
* `TauCeti.GlobalNumberFields.IsInfiniteLocalNorm`, the local norm condition at an infinite place,
  on Mathlib's completion `w.Completion`;
* `TauCeti.GlobalNumberFields.IsLocalNormEverywhere`, the conjunction of both conditions at every
  finite and every infinite place.

Complex places are not dropped from `IsLocalNormEverywhere`; instead their condition is proved to
be automatic (`isInfiniteLocalNorm_of_isComplex`), since every complex number is an `[L : K]`-th
power.

## Main results

* `TauCeti.GlobalNumberFields.isFiniteLocalNorm_iff` and
  `TauCeti.GlobalNumberFields.isInfiniteLocalNorm_iff`: the local norm conditions as products of
  norms from the completions of `L` above the place.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The **norm map of the local étale algebra** `K_w ⊗[K] L` at the infinite place `w`, on units,
landing in Mathlib's completion `K_w`. Using the scalar extension, rather than one completion of `L`
above `w`, retains every place of `L` above `w`. -/
abbrev infiniteLocalNormMap [_hKL : FiniteDimensional K L] (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ →* w.Completionˣ :=
  Algebra.normUnits w.Completion

/-- `x ∈ Kˣ` is a **local norm at the infinite place `w`** for a finite extension `L/K`: its
image in Mathlib's completion `K_w` is the norm of a unit of the local étale algebra
`K_w ⊗[K] L`. -/
def IsInfiniteLocalNorm [FiniteDimensional K L] (w : InfinitePlace K) (x : Kˣ) : Prop :=
  Units.map (algebraMap K w.Completion).toMonoidHom x ∈ (infiniteLocalNormMap K L w).range

variable [NumberField K]

/-- The **norm map of the local étale algebra** `K_v ⊗[K] L` at the finite place `v`, on units.
Using the scalar extension, rather than one completion of `L` above `v`, retains every place of
`L` above `v`. -/
abbrev finiteLocalNormMap [_hKL : FiniteDimensional K L] (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] L)ˣ →* (v.adicCompletion K)ˣ :=
  Algebra.normUnits (v.adicCompletion K)

/-- `x ∈ Kˣ` is a **local norm at the finite place `v`** for a finite extension `L/K`: its image
in `K_v` is the norm of a unit of the local étale algebra `K_v ⊗[K] L`, which accounts for every
place of `L` above `v`. -/
def IsFiniteLocalNorm [FiniteDimensional K L] (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Prop :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x ∈ (finiteLocalNormMap K L v).range

/-- `x ∈ Kˣ` is a **local norm everywhere** for a finite extension `L/K`: it is a local norm at
every finite place and at every infinite place of `K`, complex places included. -/
def IsLocalNormEverywhere [FiniteDimensional K L] (x : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), IsFiniteLocalNorm K L v x) ∧
    ∀ w : InfinitePlace K, IsInfiniteLocalNorm K L w x

section Def

variable {K L} [FiniteDimensional K L]

omit [NumberField K] in
/-- The defining characterization of `IsInfiniteLocalNorm`: membership in the range of
`infiniteLocalNormMap`. -/
theorem isInfiniteLocalNorm_def (w : InfinitePlace K) (x : Kˣ) :
    IsInfiniteLocalNorm K L w x ↔
      Units.map (algebraMap K w.Completion).toMonoidHom x ∈ (infiniteLocalNormMap K L w).range :=
  Iff.rfl

/-- The defining characterization of `IsFiniteLocalNorm`: membership in the range of
`finiteLocalNormMap`. -/
theorem isFiniteLocalNorm_def (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    IsFiniteLocalNorm K L v x ↔
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x ∈
        (finiteLocalNormMap K L v).range :=
  Iff.rfl

/-- The defining characterization of `IsLocalNormEverywhere`: a local norm at every finite and
every infinite place. -/
theorem isLocalNormEverywhere_def (x : Kˣ) :
    IsLocalNormEverywhere K L x ↔
      (∀ v : HeightOneSpectrum (𝓞 K), IsFiniteLocalNorm K L v x) ∧
        ∀ w : InfinitePlace K, IsInfiniteLocalNorm K L w x :=
  Iff.rfl

end Def

section Group

/-! ### Closure under the group operations of `Kˣ` -/

variable {K L} [FiniteDimensional K L]

omit [NumberField K] in
/-- `1` is a local norm at every infinite place. -/
@[simp]
theorem isInfiniteLocalNorm_one (w : InfinitePlace K) : IsInfiniteLocalNorm K L w 1 := by
  simp [isInfiniteLocalNorm_def]

omit [NumberField K] in
/-- Local norms at an infinite place are closed under multiplication. -/
theorem IsInfiniteLocalNorm.mul {w : InfinitePlace K} {x y : Kˣ}
    (hx : IsInfiniteLocalNorm K L w x) (hy : IsInfiniteLocalNorm K L w y) :
    IsInfiniteLocalNorm K L w (x * y) := by
  rw [isInfiniteLocalNorm_def] at *
  simpa only [map_mul] using mul_mem hx hy

omit [NumberField K] in
/-- `x⁻¹` is a local norm at an infinite place exactly when `x` is. -/
@[simp]
theorem isInfiniteLocalNorm_inv {w : InfinitePlace K} {x : Kˣ} :
    IsInfiniteLocalNorm K L w x⁻¹ ↔ IsInfiniteLocalNorm K L w x := by
  simp only [isInfiniteLocalNorm_def, map_inv, inv_mem_iff]

/-- `1` is a local norm at every finite place. -/
@[simp]
theorem isFiniteLocalNorm_one (v : HeightOneSpectrum (𝓞 K)) : IsFiniteLocalNorm K L v 1 := by
  simp [isFiniteLocalNorm_def]

/-- Local norms at a finite place are closed under multiplication. -/
theorem IsFiniteLocalNorm.mul {v : HeightOneSpectrum (𝓞 K)} {x y : Kˣ}
    (hx : IsFiniteLocalNorm K L v x) (hy : IsFiniteLocalNorm K L v y) :
    IsFiniteLocalNorm K L v (x * y) := by
  rw [isFiniteLocalNorm_def] at *
  simpa only [map_mul] using mul_mem hx hy

/-- `x⁻¹` is a local norm at a finite place exactly when `x` is. -/
@[simp]
theorem isFiniteLocalNorm_inv {v : HeightOneSpectrum (𝓞 K)} {x : Kˣ} :
    IsFiniteLocalNorm K L v x⁻¹ ↔ IsFiniteLocalNorm K L v x := by
  simp only [isFiniteLocalNorm_def, map_inv, inv_mem_iff]

/-- `1` is a local norm everywhere. -/
@[simp]
theorem isLocalNormEverywhere_one : IsLocalNormEverywhere K L 1 := by
  simp [isLocalNormEverywhere_def]

/-- Local norms everywhere are closed under multiplication. -/
theorem IsLocalNormEverywhere.mul {x y : Kˣ} (hx : IsLocalNormEverywhere K L x)
    (hy : IsLocalNormEverywhere K L y) : IsLocalNormEverywhere K L (x * y) :=
  ⟨fun v ↦ (hx.1 v).mul (hy.1 v), fun w ↦ (hx.2 w).mul (hy.2 w)⟩

/-- `x⁻¹` is a local norm everywhere exactly when `x` is. -/
@[simp]
theorem isLocalNormEverywhere_inv {x : Kˣ} :
    IsLocalNormEverywhere K L x⁻¹ ↔ IsLocalNormEverywhere K L x := by
  simp only [isLocalNormEverywhere_def, isFiniteLocalNorm_inv, isInfiniteLocalNorm_inv]

end Group

section Complex

variable {K L} [FiniteDimensional K L]

omit [NumberField K] in
/-- **The local norm condition at a complex place is automatic.** It is kept in
`IsLocalNormEverywhere` rather than silently omitted, and this theorem discharges it. -/
theorem isInfiniteLocalNorm_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (x : Kˣ) :
    IsInfiniteLocalNorm K L w x :=
  mem_range_normUnits_completion_of_isComplex L hw _

end Complex

variable {K L} [NumberField L]

/-- `x` is a local norm at the finite place `v` exactly when its image in `K_v` is a product of
norms from the completions of `L` at the places above `v`. -/
theorem isFiniteLocalNorm_iff (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    IsFiniteLocalNorm K L v x ↔
      ∃ u : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
          (w.1.adicCompletion L)ˣ,
        (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u w)) =
          Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x :=
  mem_range_normUnits_adicCompletion_iff K L v _

/-- `x` is a local norm at the infinite place `w` exactly when its image in `K_w` is a product of
norms from the completions of `L` at the places above `w`. -/
theorem isInfiniteLocalNorm_iff (w : InfinitePlace K) (x : Kˣ) :
    IsInfiniteLocalNorm K L w x ↔
      ∃ u : (w' : {w' : InfinitePlace L // w'.LiesOver w}) → w'.1.Completionˣ,
        (∏ᶠ w', Algebra.normUnits w.Completion (u w')) =
          Units.map (algebraMap K w.Completion).toMonoidHom x :=
  mem_range_normUnits_completion_iff K L w _

end TauCeti.GlobalNumberFields
