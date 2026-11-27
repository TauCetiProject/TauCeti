/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange.Form
public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.CliffordGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.IsometryEquiv

/-!
# Base change of general spin groups

Let `q` be a quadratic form on `R^n` and `A` a commutative `R`-algebra, and let
`q_A = QuadraticForm.baseChangeForm q A` be the form on `A^n` with the same coefficients; nothing
assumes `2` invertible. The algebra morphism `CliffordAlgebra.baseChangeHom q A : C(q) → C(q_A)`
induced by `R^n → A^n` preserves the even part, and `ι(A^n)` is the `A`-span of the images of
`ι(R^n)`. Hence if `g ∈ C(q)^×` is even and `g ι(R^n) g⁻¹ = ι(R^n)`, its image in `C(q_A)^×` is
even with `g ι(A^n) g⁻¹ ⊆ ι(A^n)`, and likewise for `g⁻¹`: base change maps `GSpin(q)` to
`GSpin(q_A)` (`CliffordAlgebra.specialCliffordGroupBaseChange`), compatibly with the norm
`ν(g) = reverse(g) g`, and so maps `Spin(q)` to `Spin(q_A)`
(`CliffordAlgebra.normOneSpinGroupBaseChange`). These are the maps from `R`-points to `A`-points of
`A ↦ GSpin(q_A)` and `A ↦ Spin(q_A)` induced by `R → A`. They are functorial in `A`: over `A = R`
they are the identity, and for a tower `R → A → B` the composite `GSpin(q) → GSpin(q_A) →
GSpin((q_A)_B)` is `GSpin(q) → GSpin(q_B)`, both up to the identification of the equal forms
`q_R = q` and `(q_A)_B = q_B` (`QuadraticMap.IsometryEquiv.ofEq`), and likewise for `Spin`.

## Main results

* `CliffordAlgebra.specialCliffordGroupBaseChange`: the homomorphism `GSpin(q) → GSpin(q_A)`.
* `CliffordAlgebra.specialCliffordGroupNorm_specialCliffordGroupBaseChange`: compatibility with
  the norm `ν`.
* `CliffordAlgebra.normOneSpinGroupBaseChange`: the homomorphism `Spin(q) → Spin(q_A)`.
* `CliffordAlgebra.specialCliffordGroupBaseChange_self`,
  `CliffordAlgebra.specialCliffordGroupBaseChange_specialCliffordGroupBaseChange`, and the `Spin`
  versions `CliffordAlgebra.normOneSpinGroupBaseChange_self`,
  `CliffordAlgebra.normOneSpinGroupBaseChange_normOneSpinGroupBaseChange`: functoriality in `A`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.4, for the Clifford and spin groups of a
  quadratic space over a ring.
-/

public section

namespace CliffordAlgebra

open QuadraticForm (baseChangeForm)

variable {R n : Type*} [CommRing R] [Fintype n] [LinearOrder n] {q : QuadraticForm R (n → R)}
  {A : Type*} [CommRing A] [Algebra R A]

/-- **Base change maps `GSpin(q)` into `GSpin(q_A)`.** -/
theorem units_map_baseChangeHom_mem_specialCliffordGroup {g : (CliffordAlgebra q)ˣ}
    (hg : g ∈ specialCliffordGroup q) :
    Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A)) g ∈
      specialCliffordGroup (baseChangeForm q A) := by
  rw [mem_specialCliffordGroup_iff_conj] at hg ⊢
  obtain ⟨heven, hconj, hconj'⟩ := hg
  -- conjugation by the image of `g` or `g⁻¹` is `A`-linear and preserves the images of
  -- `ι(R^n)`
  have key (u v : CliffordAlgebra q)
      (h : ∀ m, u * CliffordAlgebra.ι q m * v ∈ LinearMap.range (CliffordAlgebra.ι q))
      (m : n → A) : baseChangeHom q A u * CliffordAlgebra.ι (baseChangeForm q A) m *
        baseChangeHom q A v ∈ LinearMap.range (CliffordAlgebra.ι (baseChangeForm q A)) := by
    rw [ι_eq_sum_smul_baseChangeHom, Finset.mul_sum, Finset.sum_mul]
    refine sum_mem fun i _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul]
    obtain ⟨w, hw⟩ := h (Pi.single i 1)
    rw [← hw, baseChangeHom_ι]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  refine ⟨baseChangeHom_mem_even heven, fun m ↦ ?_, fun m ↦ ?_⟩
  · exact key _ _ hconj m
  · exact key _ _ hconj' m

/-- **The base change homomorphism `GSpin(q) → GSpin(q_A)`** induced by `R → A`. -/
noncomputable def specialCliffordGroupBaseChange (q : QuadraticForm R (n → R)) (A : Type*)
    [CommRing A] [Algebra R A] :
    specialCliffordGroup q →* specialCliffordGroup (baseChangeForm q A) :=
  ((Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A))).comp
    (specialCliffordGroup q).subtype).codRestrict _ fun g ↦
      units_map_baseChangeHom_mem_specialCliffordGroup g.property

/-- The base change homomorphism applies `baseChangeHom` to the underlying element. -/
@[simp]
theorem coe_specialCliffordGroupBaseChange (g : specialCliffordGroup q) :
    (((specialCliffordGroupBaseChange q A g : (CliffordAlgebra (baseChangeForm q A))ˣ)) :
        CliffordAlgebra (baseChangeForm q A)) =
      baseChangeHom q A ((g : (CliffordAlgebra q)ˣ) : CliffordAlgebra q) := by
  simp [specialCliffordGroupBaseChange]

/-- **Base change is compatible with the norm** `ν(g) = reverse(g) g`. -/
theorem specialCliffordGroupNorm_specialCliffordGroupBaseChange (g : specialCliffordGroup q) :
    ((specialCliffordGroupNorm (baseChangeForm q A) (specialCliffordGroupBaseChange q A g) :
        (CliffordAlgebra (baseChangeForm q A))ˣ) : CliffordAlgebra (baseChangeForm q A)) =
      baseChangeHom q A ((specialCliffordGroupNorm q g : (CliffordAlgebra q)ˣ) :
        CliffordAlgebra q) := by
  rw [coe_specialCliffordGroupNorm, coe_specialCliffordGroupNorm,
    coe_specialCliffordGroupBaseChange, map_mul, baseChangeHom_reverse]

/-- **Base change maps `Spin(q)` into `Spin(q_A)`.** -/
theorem units_map_baseChangeHom_mem_normOneSpinGroup {g : (CliffordAlgebra q)ˣ}
    (hg : g ∈ normOneSpinGroup q) :
    Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A)) g ∈
      normOneSpinGroup (baseChangeForm q A) := by
  rw [mem_normOneSpinGroup_iff] at hg ⊢
  refine ⟨units_map_baseChangeHom_mem_specialCliffordGroup hg.1, ?_⟩
  rw [Units.coe_map, MonoidHom.coe_ofClass, ← baseChangeHom_reverse, ← map_mul, hg.2, map_one]

/-- **The base change homomorphism `Spin(q) → Spin(q_A)`** induced by `R → A`. -/
noncomputable def normOneSpinGroupBaseChange (q : QuadraticForm R (n → R)) (A : Type*)
    [CommRing A] [Algebra R A] :
    normOneSpinGroup q →* normOneSpinGroup (baseChangeForm q A) :=
  ((Units.map (baseChangeHom q A : CliffordAlgebra q →* CliffordAlgebra (baseChangeForm q A))).comp
    (normOneSpinGroup q).subtype).codRestrict _ fun g ↦
      units_map_baseChangeHom_mem_normOneSpinGroup g.property

/-- The base change homomorphism of spin groups applies `baseChangeHom` to the underlying
element. -/
@[simp]
theorem coe_normOneSpinGroupBaseChange (g : normOneSpinGroup q) :
    (((normOneSpinGroupBaseChange q A g : (CliffordAlgebra (baseChangeForm q A))ˣ)) :
        CliffordAlgebra (baseChangeForm q A)) =
      baseChangeHom q A ((g : (CliffordAlgebra q)ˣ) : CliffordAlgebra q) := by
  simp [normOneSpinGroupBaseChange]

/-- **Base change of `GSpin` over `R` itself is the identity**, up to the identification of the
equal forms `q` and `q_R`. -/
theorem specialCliffordGroupBaseChange_self (g : specialCliffordGroup q) :
    specialCliffordGroupBaseChange q R g =
      (QuadraticMap.IsometryEquiv.ofEq
        (QuadraticForm.baseChangeForm_self q).symm).specialCliffordGroupEquiv g :=
  Subtype.ext <| Units.ext <| by
    rw [coe_specialCliffordGroupBaseChange,
      QuadraticMap.IsometryEquiv.coe_specialCliffordGroupEquiv_apply, baseChangeHom_self]

/-- **Base change of `GSpin` is transitive**: for a tower `R → A → B`,
`GSpin(q) → GSpin(q_A) → GSpin((q_A)_B)` is `GSpin(q) → GSpin(q_B)` followed by the
identification of the equal forms `q_B` and `(q_A)_B`. -/
theorem specialCliffordGroupBaseChange_specialCliffordGroupBaseChange (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] (g : specialCliffordGroup q) :
    specialCliffordGroupBaseChange (baseChangeForm q A) B (specialCliffordGroupBaseChange q A g) =
      (QuadraticMap.IsometryEquiv.ofEq
        (QuadraticForm.baseChangeForm_baseChangeForm q A B).symm).specialCliffordGroupEquiv
        (specialCliffordGroupBaseChange q B g) :=
  Subtype.ext <| Units.ext <| by
    rw [coe_specialCliffordGroupBaseChange, coe_specialCliffordGroupBaseChange,
      QuadraticMap.IsometryEquiv.coe_specialCliffordGroupEquiv_apply,
      coe_specialCliffordGroupBaseChange, baseChangeHom_baseChangeHom]

/-- **Base change of `Spin` over `R` itself is the identity**, up to the identification of the
equal forms `q` and `q_R`. -/
theorem normOneSpinGroupBaseChange_self (g : normOneSpinGroup q) :
    normOneSpinGroupBaseChange q R g =
      (QuadraticMap.IsometryEquiv.ofEq
        (QuadraticForm.baseChangeForm_self q).symm).normOneSpinGroupEquiv g :=
  Subtype.ext <| Units.ext <| by
    rw [coe_normOneSpinGroupBaseChange,
      QuadraticMap.IsometryEquiv.coe_normOneSpinGroupEquiv_apply, baseChangeHom_self]

/-- **Base change of `Spin` is transitive**: for a tower `R → A → B`,
`Spin(q) → Spin(q_A) → Spin((q_A)_B)` is `Spin(q) → Spin(q_B)` followed by the identification of
the equal forms `q_B` and `(q_A)_B`. -/
theorem normOneSpinGroupBaseChange_normOneSpinGroupBaseChange (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] (g : normOneSpinGroup q) :
    normOneSpinGroupBaseChange (baseChangeForm q A) B (normOneSpinGroupBaseChange q A g) =
      (QuadraticMap.IsometryEquiv.ofEq
        (QuadraticForm.baseChangeForm_baseChangeForm q A B).symm).normOneSpinGroupEquiv
        (normOneSpinGroupBaseChange q B g) :=
  Subtype.ext <| Units.ext <| by
    rw [coe_normOneSpinGroupBaseChange, coe_normOneSpinGroupBaseChange,
      QuadraticMap.IsometryEquiv.coe_normOneSpinGroupEquiv_apply,
      coe_normOneSpinGroupBaseChange, baseChangeHom_baseChangeHom]

end CliffordAlgebra
