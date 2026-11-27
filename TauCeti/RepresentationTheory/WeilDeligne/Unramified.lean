/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative
public import TauCeti.RepresentationTheory.WeilDeligne.Basic

/-!
# Unramified Weil–Deligne parameters

For a continuous degree map `deg : W →* Multiplicative ℤ` and a linear automorphism `A` of `V`,
the **unramified parameter** of `A` is the raw Weil–Deligne parameter with `r(w) = A ^ deg w` and
monodromy `N = 0`. Its Frobenius semisimplicity is governed by the semisimplicity of `A`.

## Main definitions

* `TauCeti.WeilDeligneParameter.unramified`: the parameter with `r(w) = A ^ deg w` and `N = 0`.

## Main results

* `TauCeti.WeilDeligneParameter.isFrobeniusSemisimple_unramified_iff`: when some degree is nonzero
  in `E` (or the degree is trivial), the unramified parameter of `A` is Frobenius semisimple
  exactly when the degree is trivial or `A` is semisimple.
* `TauCeti.WeilDeligneParameter.not_isFrobeniusSemisimple_unramified_of_isUnipotent_of_ne_one`:
  if some degree is nonzero in `E`, an unramified parameter whose Frobenius acts by a nontrivial
  unipotent automorphism, such as the Jordan block `[[1, 1], [0, 1]]`, is not Frobenius
  semisimple.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §§8.5–8.6, p. 570.
-/

public section

noncomputable section

namespace TauCeti

namespace WeilDeligneParameter

open LinearMap (GeneralLinearGroup)

variable {E W V : Type*} [Field E] [Group W] [TopologicalSpace W] [AddCommGroup V] [Module E V]
  {deg : W →* Multiplicative ℤ}

variable (q : ℕ) in
/-- **The unramified parameter** of a linear automorphism `A` of `V`, for a continuous degree map:
`r(w) = A ^ deg w` and `N = 0`. Elements of degree `0` act trivially. -/
def unramified (hdeg : Continuous deg) (A : GeneralLinearGroup E V) :
    WeilDeligneParameter E W V deg q where
  r := (Units.coeHom _).comp ((zpowersHom _ A).comp deg)
  isOpen_ker := by
    rw [← MonoidHom.comp_assoc]
    exact isOpen_ker_comp_deg hdeg _
  N := 0
  isNilpotent_N := .zero
  conj_N _ := by simp

variable {q : ℕ}

@[simp]
theorem unramified_r (hdeg : Continuous deg) (A : GeneralLinearGroup E V) (w : W) :
    (unramified q hdeg A).r w =
      ((A ^ (deg w).toAdd : GeneralLinearGroup E V) : Module.End E V) := by
  simp [unramified]

@[simp]
theorem unramified_N (hdeg : Continuous deg) (A : GeneralLinearGroup E V) :
    (unramified q hdeg A).N = 0 :=
  (rfl)

/-- **Frobenius semisimplicity of an unramified parameter**: if the degree is trivial or some
element has degree nonzero in `E`, the unramified parameter of `A` is Frobenius semisimple exactly
when the degree is trivial or `A` is semisimple. -/
theorem isFrobeniusSemisimple_unramified_iff [FiniteDimensional E V] (hdeg : Continuous deg)
    (A : GeneralLinearGroup E V) (hE : deg ≠ 1 → ∃ w, ((deg w).toAdd : E) ≠ 0) :
    (unramified q hdeg A).IsFrobeniusSemisimple ↔
      deg = 1 ∨ LinearMap.GeneralLinearGroup.IsSemisimple A := by
  simp_rw [isFrobeniusSemisimple_def, unramified_r,
    ← LinearMap.GeneralLinearGroup.isSemisimple_def]
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hd ↦ ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hE hd
    exact (LinearMap.GeneralLinearGroup.isSemisimple_zpow_iff hw A).1
      (h w fun h0 ↦ hw (by simp [h0]))
  · rintro (hd | hA) w hw
    · simp [hd] at hw
    · exact hA.zpow _

/-- **A nontrivial unipotent Frobenius is not semisimple**: if `A ≠ 1` is unipotent, as for the
Jordan block `[[1, 1], [0, 1]]`, and some `w` has degree nonzero in `E`, then the unramified
parameter of `A` is not Frobenius semisimple. -/
theorem not_isFrobeniusSemisimple_unramified_of_isUnipotent_of_ne_one [FiniteDimensional E V]
    (hdeg : Continuous deg) {A : GeneralLinearGroup E V}
    (hA : LinearMap.GeneralLinearGroup.IsUnipotent A) (hA₁ : A ≠ 1) {w : W}
    (hw : ((deg w).toAdd : E) ≠ 0) : ¬ (unramified q hdeg A).IsFrobeniusSemisimple := by
  have hd : deg ≠ 1 := fun h ↦ hw (by simp [h])
  rw [isFrobeniusSemisimple_unramified_iff hdeg A fun _ ↦ ⟨w, hw⟩, or_iff_right hd]
  exact fun hss ↦ hA₁ (hss.eq_one_of_isUnipotent hA)

end WeilDeligneParameter

end TauCeti
