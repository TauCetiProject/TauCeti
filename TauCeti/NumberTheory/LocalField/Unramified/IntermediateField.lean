/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Factorization
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal

/-!
# The unramified part of a finite subextension

For a finite subextension `L` of the separable closure of a nonarchimedean local field `K`,
the intersection of `L` with the maximal unramified extension is the canonical unramified
extension of degree `f(L/K)`. In particular, that canonical field is contained in `L`.
This identifies the unramified base over which extensions with a prescribed residue degree
are totally ramified, as needed in counting extensions by residue degree.

`IntermediateField.inertiaDegree` extends the residue degree to all subextensions, taking
value zero on infinite extensions. It uses the same local-field adapters and totalization as
`IntermediateField.discriminantExponent`. Its invariance under algebra equivalence includes
the infinite case, so residue degree can be used as a weight on isomorphism classes.

## Main results

* `IntermediateField.inertiaDegree_eq_of_algEquiv`: residue degree is an isomorphism invariant.
* `IntermediateField.unramifiedExtension_inertiaDegree_le`: `K_{f(L/K)} ≤ L` for finite `L`.
* `IntermediateField.inf_maximalUnramifiedExtension`: `L ∩ K^{ur} = K_{f(L/K)}` for finite `L`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel TauCeti

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open Classical in
/-- The residue degree of a subextension of `SeparableClosure K`, using the canonical
local-field structures when the extension is finite, and zero otherwise. -/
def inertiaDegree (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  if _ : Module.Finite K L then
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    TauCeti.inertiaDegree K L
  else 0

/-- On a finite subextension, the totalized residue degree agrees with the residue degree
for its canonical local-field structure. -/
theorem inertiaDegree_eq (L : IntermediateField K (SeparableClosure K))
    [hfin : Module.Finite K L] :
    L.inertiaDegree =
      (letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
      letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
      haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
      TauCeti.inertiaDegree K L) :=
  dite_eq_left hfin

/-- On an infinite subextension the totalized residue degree is zero. -/
theorem inertiaDegree_of_not_finite {L : IntermediateField K (SeparableClosure K)}
    (h : ¬ Module.Finite K L) : L.inertiaDegree = 0 :=
  dite_eq_right h

/-- The residue degree of a finite subextension is positive. -/
theorem inertiaDegree_pos (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] : 0 < L.inertiaDegree := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  exact TauCeti.inertiaDegree_pos

/-- The residue degree vanishes exactly on infinite subextensions. -/
@[simp]
theorem inertiaDegree_eq_zero_iff (L : IntermediateField K (SeparableClosure K)) :
    L.inertiaDegree = 0 ↔ ¬ Module.Finite K L := by
  by_cases h : Module.Finite K L
  · have := h
    simp [h, (inertiaDegree_pos L).ne']
  · simp [h, inertiaDegree_of_not_finite h]

/-- The residue degree is invariant under `K`-algebra equivalence, including the infinite case. -/
theorem inertiaDegree_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : L ≃ₐ[K] M) : L.inertiaDegree = M.inertiaDegree := by
  by_cases hL : Module.Finite K L
  · have : Module.Finite K M := Module.Finite.equiv e.toLinearEquiv
    rw [inertiaDegree_eq, inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) M
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) M
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) M
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) M
    exact TauCeti.inertiaDegree_eq_of_algEquiv K L M e
  · rw [inertiaDegree_of_not_finite hL, inertiaDegree_of_not_finite
      fun h ↦ hL (Module.Finite.equiv e.symm.toLinearEquiv)]

/-- The bottom subextension has residue degree one. -/
@[simp]
theorem inertiaDegree_bot :
    (⊥ : IntermediateField K (SeparableClosure K)).inertiaDegree = 1 := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) ⊥
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) ⊥
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) ⊥
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) ⊥
  have h := ramificationIndex_mul_inertiaDegree K (⊥ : IntermediateField K (SeparableClosure K))
  rw [IntermediateField.finrank_bot] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- The canonical unramified extension of degree `f(L/K)` is contained in every finite
subextension `L`. -/
theorem unramifiedExtension_inertiaDegree_le (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≤ L := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L
  rw [unramifiedExtension_eq_adjoin_simple TauCeti.inertiaDegree_pos.ne'
    (hζ.map_of_injective L.val.injective), adjoin_simple_le_iff]
  exact ζ.2

/-- The unramified part of a finite subextension is the canonical unramified extension of
its residue degree. No normality hypothesis on `L/K` is required. -/
@[simp]
theorem inf_maximalUnramifiedExtension (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    L ⊓ maximalUnramifiedExtension K (SeparableClosure K) =
      unramifiedExtension K (SeparableClosure K) L.inertiaDegree := by
  apply le_antisymm
  · let E := L ⊓ maximalUnramifiedExtension K (SeparableClosure K)
    have hEL : E ≤ L := inf_le_left
    let _ : Algebra E L := (inclusion hEL).toAlgebra
    have : IsScalarTower K E L := .of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite K E := Module.Finite.of_injective (inclusion hEL).toLinearMap
      (inclusion_injective hEL)
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) E
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) E
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) E
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) E
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    have : ValuativeExtension E L := (inclusion hEL).valuativeExtension
    have : IsUnramified K E := (E.le_maximalUnramifiedExtension_iff).1 inf_le_right
    calc
      L ⊓ maximalUnramifiedExtension K (SeparableClosure K) =
          unramifiedExtension K (SeparableClosure K) (Module.finrank K E) :=
        E.eq_unramifiedExtension_finrank
      _ ≤ unramifiedExtension K (SeparableClosure K) L.inertiaDegree := by
        rw [inertiaDegree_eq, ← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := E)]
        exact unramifiedExtension_le_of_dvd TauCeti.inertiaDegree_pos.ne'
          (Dvd.intro _ (TauCeti.inertiaDegree_tower (K := K) (L := E) L).symm)
  · exact le_inf (unramifiedExtension_inertiaDegree_le L)
      (unramifiedExtension_le_maximalUnramifiedExtension K (SeparableClosure K) _)

end IntermediateField
