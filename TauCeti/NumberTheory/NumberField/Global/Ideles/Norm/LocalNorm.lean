/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective

/-!
# Elements that are norms at every place

For an extension `L/K` of number fields, an element `x ∈ Kˣ` is a *local norm* at a place of `K`
when its image in the completion `K_v` is a norm from the local étale algebra `K_v ⊗[K] L`. Using
the scalar extension, rather than one completion `L_w` above `v`, keeps every place of `L` above
`v`: by `TauCeti.mem_range_normUnits_adicCompletion_iff` the local norms are the products of norms
from all the completions `L_w` with `w ∣ v`. This file defines

* `TauCeti.GlobalNumberFields.IsFiniteLocalNorm`, the local norm condition at a finite place;
* `TauCeti.GlobalNumberFields.IsInfiniteLocalNorm`, the local norm condition at an infinite place,
  on Mathlib's completion `w.Completion`;
* `TauCeti.GlobalNumberFields.IsLocalNormEverywhere`, the conjunction of both conditions at every
  finite and every infinite place.

Complex places are not dropped from `IsLocalNormEverywhere`; instead their condition is proved to
be automatic (`isInfiniteLocalNorm_of_isComplex`), since every complex number is an `[L : K]`-th
power.

The main result, `unitEmbedding_mem_range_ideleNormMap_iff`, says that `x` is a norm at every
place exactly when its principal idele is the norm of an idele of `L`. It is the principal case of
the placewise criterion `mem_range_ideleNormMap_iff`. With the Hasse norm theorem for cyclic
extensions, which identifies global norms with principal ideles that are idele norms, it turns
the Hasse norm principle into a statement about norm equations in the completions. The easy half
of that principle holds for every extension: a global norm is a norm everywhere
(`isLocalNormEverywhere_normUnits`).

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2 (norms of ideles) and §4 (the Hasse norm
  theorem).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver

namespace TauCeti

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **Every unit is a local norm at a complex place.** At a complex place `w` of `K` every unit of
`K_w ≅ ℂ` is the norm of a unit of the local étale algebra `K_w ⊗[K] L`: it is an `[L : K]`-th
power, and the `[L : K]`-th power of `b ∈ K_wˣ` is the norm of `b ⊗ 1`. -/
theorem mem_range_normUnits_completion_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (a : w.Completionˣ) :
    a ∈ (Algebra.normUnits w.Completion (S := w.Completion ⊗[K] L)).range := by
  obtain ⟨b, rfl⟩ := Completion.mem_range_powMonoidHom (Module.finrank_pos (R := K) (M := L)).ne'
    a fun hr ↦ (not_isReal_iff_isComplex.mpr hw hr).elim
  have hb := Algebra.pow_finrank_mem_range_normUnits w.Completion (S := w.Completion ⊗[K] L) b
  rwa [Module.finrank_baseChange] at hb

end TauCeti

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- `x ∈ Kˣ` is a **local norm at the infinite place `w`** for `L/K`: its image in Mathlib's
completion `K_w` is the norm of a unit of the local étale algebra `K_w ⊗[K] L`. -/
def IsInfiniteLocalNorm (w : InfinitePlace K) (x : Kˣ) : Prop :=
  Units.map (algebraMap K w.Completion).toMonoidHom x ∈
    (Algebra.normUnits w.Completion (S := w.Completion ⊗[K] L)).range

variable [NumberField K]

/-- `x ∈ Kˣ` is a **local norm at the finite place `v`** for `L/K`: its image in `K_v` is the norm
of a unit of the local étale algebra `K_v ⊗[K] L`, which accounts for every place of `L`
above `v`. -/
def IsFiniteLocalNorm (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Prop :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x ∈
    (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range

/-- `x ∈ Kˣ` is a **local norm everywhere** for `L/K`: it is a local norm at every finite place
and at every infinite place of `K`, complex places included. -/
def IsLocalNormEverywhere (x : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), IsFiniteLocalNorm K L v x) ∧
    ∀ w : InfinitePlace K, IsInfiniteLocalNorm K L w x

variable {K L}

omit [NumberField K] in
/-- Unfolding `IsInfiniteLocalNorm`. -/
theorem isInfiniteLocalNorm_iff_mem_range (w : InfinitePlace K) (x : Kˣ) :
    IsInfiniteLocalNorm K L w x ↔
      Units.map (algebraMap K w.Completion).toMonoidHom x ∈
        (Algebra.normUnits w.Completion (S := w.Completion ⊗[K] L)).range :=
  Iff.rfl

omit [NumberField K] in
/-- **The local norm condition at a complex place is automatic.** It is kept in
`IsLocalNormEverywhere` rather than silently omitted, and this theorem discharges it. -/
theorem isInfiniteLocalNorm_of_isComplex [FiniteDimensional K L] {w : InfinitePlace K}
    (hw : w.IsComplex) (x : Kˣ) :
    IsInfiniteLocalNorm K L w x :=
  mem_range_normUnits_completion_of_isComplex L hw _

/-- Unfolding `IsFiniteLocalNorm`. -/
theorem isFiniteLocalNorm_iff_mem_range (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    IsFiniteLocalNorm K L v x ↔
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x ∈
        (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range :=
  Iff.rfl

/-- Unfolding `IsLocalNormEverywhere`. -/
theorem isLocalNormEverywhere_iff (x : Kˣ) :
    IsLocalNormEverywhere K L x ↔
      (∀ v : HeightOneSpectrum (𝓞 K), IsFiniteLocalNorm K L v x) ∧
        ∀ w : InfinitePlace K, IsInfiniteLocalNorm K L w x :=
  Iff.rfl

variable [NumberField L]

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

/-- **Principal idele norms are local norms everywhere.** For an extension `L/K` of number fields,
the principal idele of `x ∈ Kˣ` is the norm of an idele of `L` exactly when `x` is a norm from the
local étale algebra `K_v ⊗[K] L` at every finite and every infinite place `v` of `K`. -/
theorem unitEmbedding_mem_range_ideleNormMap_iff (x : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K x ∈ (ideleNormMap K L).toMonoidHom.range ↔
      IsLocalNormEverywhere K L x := by
  simp only [mem_range_ideleNormMap_iff, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
    InfinitePlace.ideleInfiniteCoord_unitEmbedding, isLocalNormEverywhere_iff,
    isFiniteLocalNorm_iff_mem_range, isInfiniteLocalNorm_iff_mem_range]

/-- **A global norm is a local norm everywhere.** This is the easy half of the Hasse norm
principle, valid for every extension of number fields. -/
theorem isLocalNormEverywhere_normUnits (y : Lˣ) :
    IsLocalNormEverywhere K L (Algebra.normUnits K y) :=
  (unitEmbedding_mem_range_ideleNormMap_iff _).mp
    ⟨IdeleGroup.unitEmbedding (𝓞 L) L y, ideleNormMap_unitEmbedding K L y⟩

end TauCeti.GlobalNumberFields
