/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Orthogonal
public import TauCeti.Geometry.Hodge.SubquotientModel

/-!
# Polarizations on rational Hodge substructures

A rational Hodge substructure inherits a pure Hodge structure on its rational and complex
base-change models. If the ambient structure is polarized, restricting the integral form to the
integral vectors in the rational subspace polarizes this induced structure.

The only substantive point is nondegeneracy. Hodge--Riemann positivity makes a rational Hodge
substructure disjoint from its orthogonal complement, so the complex polarizing form restricts
nondegenerately. Nondegeneracy then descends to the restricted integral form.

This construction supplies the objects represented by rational Hodge substructures in the
category of polarizable rational Hodge structures. It follows the orthogonal-complement argument
of Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters--Steenbrink,
*Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure.hodgeStructure`: the pure Hodge structure induced on a
  rational Hodge substructure.
* `TauCeti.Hodge.RationalHodgeSubstructure.inducedPolarization`: the restriction of an ambient
  polarization to the induced structure.
* `TauCeti.Hodge.RationalHodgeSubstructure.isPolarizable_hodgeStructure`: polarizability is
  inherited by rational Hodge substructures.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n}

namespace RationalHodgeSubstructure

variable (W : RationalHodgeSubstructure hℚ hs)

/-- The pure Hodge structure induced on a rational Hodge substructure. Its integral carrier is
the lattice of integral vectors lying in `W.WQ`, its rational carrier is `W.WQ`, and its complex
carrier is `W.WC`. -/
noncomputable def hodgeStructure :
    HodgeStructure (isBaseChange_integralSubmoduleToComplex hℚ hℂ W.WQ) n := by
  have h : hs.IsSubstructure (rationalToComplexSubmodule hℚ hℂ W.WQ) := by
    rw [← W.WC_def]
    exact W.isSubstructure
  refine {
    F := fun p ↦ (hs.F p).comap (rationalToComplexSubmodule hℚ hℂ W.WQ).subtype
    F_antitone := fun _ _ hpq ↦ Submodule.comap_mono (hs.F_antitone hpq)
    F_top := ?_
    opposed := ?_ }
  · obtain ⟨p, hp⟩ := hs.F_top
    exact ⟨p, by rw [hp, Submodule.comap_top]⟩
  · intro p
    rw [latticeConjugation_integralSubmoduleToComplex,
      Conjugation.map_restrict_comap_subtype, ← hs.conjF_def]
    exact TauCeti.Submodule.isCompl_comap_subtype (hs.isCompl_F_conjF p).disjoint
      (h.le_inf_F_sup_inf_conjF p)

/-- The filtration on the induced Hodge structure is the trace of the ambient filtration. -/
@[simp]
theorem hodgeStructure_F (p : ℤ) : W.hodgeStructure.F p =
    (hs.F p).comap (rationalToComplexSubmodule hℚ hℂ W.WQ).subtype := by
  rw [hodgeStructure]

/-- The conjugate filtration on the induced structure is the trace of the ambient conjugate
filtration. -/
@[simp]
theorem hodgeStructure_conjF (p : ℤ) : W.hodgeStructure.conjF p =
    (hs.conjF p).comap (rationalToComplexSubmodule hℚ hℂ W.WQ).subtype := by
  rw [HodgeStructureOn.conjF_def, hodgeStructure_F,
    latticeConjugation_integralSubmoduleToComplex, Conjugation.map_restrict_comap_subtype,
    ← HodgeStructureOn.conjF_def]

/-- The Hodge components of the induced structure are the traces of the ambient components. -/
@[simp]
theorem hodgeStructure_piece (p : ℤ) :
    W.hodgeStructure.piece p =
      (hs.piece p).comap (rationalToComplexSubmodule hℚ hℂ W.WQ).subtype := by
  rw [HodgeStructureOn.piece_def, hodgeStructure_F, hodgeStructure_conjF, hs.piece_def,
    Submodule.comap_inf]

/-- The inclusion of a rational Hodge substructure into its ambient complex space is a morphism
of pure Hodge structures. -/
theorem isMorphism_subtype :
    HodgeStructureOn.IsMorphism W.hodgeStructure hs
      (rationalToComplexSubmodule hℚ hℂ W.WQ).subtype where
  commutes_conj x := by simp
  map_F_le p := by
    rw [hodgeStructure_F]
    exact Submodule.map_comap_le (rationalToComplexSubmodule hℚ hℂ W.WQ).subtype (hs.F p)

variable (P : Polarization hℂ hs)

/-- The integral polarizing form restricted to the integral vectors of a rational Hodge
substructure. -/
def inducedForm : LinearMap.BilinForm ℤ (integralSubmodule ιℚ W.WQ) :=
  P.Qint.restrict (integralSubmodule ιℚ W.WQ)

/-- The restricted integral form evaluates as the ambient integral form on underlying vectors. -/
@[simp]
theorem inducedForm_apply (x y : integralSubmodule ιℚ W.WQ) :
    W.inducedForm P x y = P.Qint (x : Vℤ) (y : Vℤ) := by
  simp [inducedForm]

/-- The complexification of the restricted integral form is the restriction of the ambient
complex polarizing form. -/
theorem integralFormBaseChange_inducedForm :
    integralFormBaseChange (isBaseChange_integralSubmoduleToComplex hℚ hℂ W.WQ)
        (W.inducedForm P) = P.Q.restrict (rationalToComplexSubmodule hℚ hℂ W.WQ) := by
  apply (integralFormBaseChange_unique _ _ _ fun x y ↦ ?_).symm
  simp [inducedForm]

/-- The restricted integral form is nondegenerate. -/
theorem inducedForm_nondegenerate : (W.inducedForm P).Nondegenerate := by
  have hrefl : P.Q.IsRefl := by
    intro x y hxy
    have h := P.Q_symm_weight x y
    rw [hxy, mul_zero] at h
    exact h
  have hcomplex :
      (P.Q.restrict (rationalToComplexSubmodule hℚ hℂ W.WQ)).Nondegenerate := by
    apply P.Q.nondegenerate_restrict_of_disjoint_orthogonal hrefl
    simpa only [W.WC_def] using disjoint_WC_orthogonal P W
  constructor
  · intro x hx
    have hxC : integralSubmoduleToComplex hℚ hℂ W.WQ x = 0 := hcomplex.1 _ fun y ↦ by
      induction y using (isBaseChange_integralSubmoduleToComplex hℚ hℂ W.WQ).inductionOn with
      | tmul y => simpa [inducedForm] using congrArg ((↑) : ℤ → ℂ) (hx y)
      | smul c y hy => rw [map_smul, hy, smul_zero]
      | add y z hy hz => rw [map_add, hy, hz, add_zero]
    apply Subtype.ext
    apply P.isPolarization.nondegenerate.1 (x : Vℤ)
    intro y
    have h := congrArg (fun z : Vℂ ↦ P.Q z (ιℂ y)) (congrArg Subtype.val hxC)
    simpa using h
  · intro x hx
    have hxC : integralSubmoduleToComplex hℚ hℂ W.WQ x = 0 := hcomplex.2 _ fun y ↦ by
      induction y using (isBaseChange_integralSubmoduleToComplex hℚ hℂ W.WQ).inductionOn with
      | tmul y => simpa [inducedForm] using congrArg ((↑) : ℤ → ℂ) (hx y)
      | smul c y hy =>
          rw [map_smul, LinearMap.smul_apply, hy, smul_zero]
      | add y z hy hz =>
          rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
    apply Subtype.ext
    apply P.isPolarization.nondegenerate.2 (x : Vℤ)
    intro y
    have h := congrArg (fun z : Vℂ ↦ P.Q (ιℂ y) z) (congrArg Subtype.val hxC)
    simpa using h

/-- Restricting a polarization to a rational Hodge substructure gives a polarization of its
induced Hodge structure. -/
noncomputable def inducedPolarization :
    Polarization (isBaseChange_integralSubmoduleToComplex hℚ hℂ W.WQ) W.hodgeStructure where
  Qint := W.inducedForm P
  isPolarization := {
    symm_weight := fun x y ↦ by
      simpa [inducedForm] using P.isPolarization.symm_weight (x : Vℤ) (y : Vℤ)
    nondegenerate := W.inducedForm_nondegenerate P
    orthogonal := fun p x hx y hy ↦ by
      rw [integralFormBaseChange_inducedForm]
      exact P.Q_orthogonal p (by simpa using hx) (by simpa using hy)
    positive := fun p x hx hx0 ↦ by
      rw [integralFormBaseChange_inducedForm]
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        coe_latticeConj_integralSubmoduleToComplex] using
        P.Q_positive p (by simpa using hx) (Subtype.coe_ne_coe.mpr hx0) }

/-- The integral form underlying the induced polarization is the restricted ambient form. -/
@[simp]
theorem inducedPolarization_Qint : (W.inducedPolarization P).Qint = W.inducedForm P := by
  rw [inducedPolarization]

/-- The complex form underlying the induced polarization is the restricted ambient complex
form. -/
@[simp]
theorem inducedPolarization_Q :
    (W.inducedPolarization P).Q =
      P.Q.restrict (rationalToComplexSubmodule hℚ hℂ W.WQ) := by
  rw [Polarization.Q_def, inducedPolarization_Qint, integralFormBaseChange_inducedForm]

/-- A rational Hodge substructure of a polarizable pure Hodge structure is polarizable. -/
theorem isPolarizable_hodgeStructure (hpol : IsPolarizable hℂ hs) :
    IsPolarizable (isBaseChange_integralSubmoduleToComplex hℚ hℂ W.WQ) W.hodgeStructure := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.mp hpol
  exact inducedPolarization W P |>.isPolarizable

end RationalHodgeSubstructure

end TauCeti.Hodge
