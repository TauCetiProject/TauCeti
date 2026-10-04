/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Existence

/-!
# The lattice of finite unramified extensions

Let `K` be a nonarchimedean local field and let `Ω` be a separably closed extension of `K`.
The finite unramified intermediate fields of `Ω / K` are classified by their positive degrees:
the degree-`f` field is `TauCeti.unramifiedExtension K Ω f`, and

`unramifiedExtension K Ω f ≤ unramifiedExtension K Ω g ↔ f ∣ g`.

Consequently these fields form a lattice: meet corresponds to the greatest common divisor of
the degrees, and join corresponds to their least common multiple. This file packages the
classification as an equivalence with `ℕ+` and equips the finite unramified subextensions with
their intrinsic inclusion order and lattice operations.

## Main definitions

* `TauCeti.FiniteUnramifiedSubextension`: a finite unramified intermediate field of a fixed
  separably closed extension.
* `TauCeti.unramifiedExtensionPNat`: the finite unramified subextension of a positive degree.
* `TauCeti.finiteUnramifiedSubextensionDegreeEquiv`: the classification by positive degrees.

## Main results

* `TauCeti.unramifiedExtension_le_unramifiedExtension_iff`: inclusion is divisibility of degrees.
* `TauCeti.FiniteUnramifiedSubextension.le_iff_degree_dvd`: the order characterization for
  arbitrary finite unramified subextensions.
* `TauCeti.FiniteUnramifiedSubextension.degree_inf` and
  `TauCeti.FiniteUnramifiedSubextension.degree_sup`: the degrees of meet and join are given by
  `Nat.gcd` and `Nat.lcm`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- The degree-`f` unramified extension is contained in the degree-`g` unramified extension
exactly when `f` divides `g`. Both degrees are required to be positive because the index `0`
is reserved for the trivial field, rather than a degree-zero extension. -/
theorem unramifiedExtension_le_unramifiedExtension_iff {f g : ℕ} (hf : f ≠ 0) (hg : g ≠ 0) :
    unramifiedExtension K Ω f ≤ unramifiedExtension K Ω g ↔ f ∣ g := by
  refine ⟨fun hfg ↦ ?_, unramifiedExtension_le_of_dvd hg⟩
  let _ : Algebra (unramifiedExtension K Ω f) (unramifiedExtension K Ω g) :=
    (IntermediateField.inclusion hfg).toAlgebra
  have : IsScalarTower K (unramifiedExtension K Ω f) (unramifiedExtension K Ω g) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite (unramifiedExtension K Ω f) (unramifiedExtension K Ω g) :=
    Module.Finite.of_restrictScalars_finite K _ _
  rw [← finrank_unramifiedExtension (K := K) (Ω := Ω) hf,
    ← finrank_unramifiedExtension (K := K) (Ω := Ω) hg]
  exact Module.finrank_dvd_finrank_right K (unramifiedExtension K Ω f)
    (unramifiedExtension K Ω g)

/-- A finite unramified subextension of `Ω / K`, using the canonical local-field structure on
finite intermediate fields. The local-field structures remain named definitions rather than
global instances, avoiding instance diamonds on the intermediate-field carrier. -/
def IsFiniteUnramifiedSubextension (E : IntermediateField K Ω) : Prop :=
  ∃ hE : Module.Finite K E,
    letI := hE
    letI := finiteIntermediateFieldValuativeRel K Ω E
    letI := finiteIntermediateFieldTopology K Ω E
    letI := finiteIntermediateField_isNonarchimedeanLocalField K Ω E
    letI := finiteIntermediateField_valuativeExtension K Ω E
    IsUnramified K E

/-- A finite intermediate field is unramified exactly when it is a canonical unramified
extension of some positive degree. The degree, and hence the extension, is unique by
`unramifiedExtension_le_unramifiedExtension_iff`. -/
theorem isFiniteUnramifiedSubextension_iff_exists_eq_unramifiedExtension
    (E : IntermediateField K Ω) :
    IsFiniteUnramifiedSubextension K Ω E ↔
      ∃ f : ℕ+, E = unramifiedExtension K Ω f := by
  constructor
  · rintro ⟨hE, h_unramified⟩
    let _ := hE
    let _ := finiteIntermediateFieldValuativeRel K Ω E
    let _ := finiteIntermediateFieldTopology K Ω E
    have _ := finiteIntermediateField_isNonarchimedeanLocalField K Ω E
    have _ := finiteIntermediateField_valuativeExtension K Ω E
    let f : ℕ+ := ⟨Module.finrank K E, Module.finrank_pos⟩
    exact ⟨f, E.eq_unramifiedExtension_finrank⟩
  · rintro ⟨f, rfl⟩
    refine ⟨inferInstance, ?_⟩
    let _ := finiteIntermediateFieldValuativeRel K Ω (unramifiedExtension K Ω f)
    let _ := finiteIntermediateFieldTopology K Ω (unramifiedExtension K Ω f)
    have _ := finiteIntermediateField_isNonarchimedeanLocalField K Ω
      (unramifiedExtension K Ω f)
    have _ := finiteIntermediateField_valuativeExtension K Ω (unramifiedExtension K Ω f)
    exact isUnramified_unramifiedExtension f.ne_zero

/-- The type of finite unramified intermediate fields of a fixed separably closed extension. -/
abbrev FiniteUnramifiedSubextension :=
  {E : IntermediateField K Ω // IsFiniteUnramifiedSubextension K Ω E}

namespace FiniteUnramifiedSubextension

omit [IsSepClosed Ω] in
/-- Two finite unramified subextensions are equal when their underlying intermediate fields are
equal. -/
@[ext]
theorem ext {E F : FiniteUnramifiedSubextension K Ω} (h : E.1 = F.1) : E = F :=
  Subtype.ext h

end FiniteUnramifiedSubextension

/-- The unramified extension attached to a positive integer, regarded as a finite unramified
subextension. -/
def unramifiedExtensionPNat (f : ℕ+) : FiniteUnramifiedSubextension K Ω :=
  ⟨unramifiedExtension K Ω f,
    (isFiniteUnramifiedSubextension_iff_exists_eq_unramifiedExtension K Ω _).2 ⟨f, rfl⟩⟩

/-- The underlying field of the finite unramified subextension of degree `f`. -/
@[simp]
theorem coe_unramifiedExtensionPNat (f : ℕ+) :
    (unramifiedExtensionPNat K Ω f).1 = unramifiedExtension K Ω f :=
  congrArg Subtype.val (unramifiedExtensionPNat.eq_def K Ω f)

/-- Positive integers classify the finite unramified subextensions of a separably closed
extension. This forward equivalence is kept private; the public API uses
`finiteUnramifiedSubextensionDegreeEquiv` in the degree direction. -/
private def unramifiedExtensionEquivFiniteUnramifiedSubextension :
    ℕ+ ≃ FiniteUnramifiedSubextension K Ω :=
  Equiv.ofBijective (unramifiedExtensionPNat K Ω) ⟨by
    intro f g hfg
    apply PNat.eq
    have hfields : unramifiedExtension K Ω f = unramifiedExtension K Ω g :=
      congrArg (fun E : FiniteUnramifiedSubextension K Ω ↦ E.1) hfg
    calc
      (f : ℕ) = Module.finrank K (unramifiedExtension K Ω f) :=
        (finrank_unramifiedExtension f.ne_zero).symm
      _ = Module.finrank K (unramifiedExtension K Ω g) :=
        congrArg (fun E : IntermediateField K Ω ↦ Module.finrank K E) hfields
      _ = (g : ℕ) := finrank_unramifiedExtension g.ne_zero,
    by
      intro E
      obtain ⟨f, hf⟩ :=
        (isFiniteUnramifiedSubextension_iff_exists_eq_unramifiedExtension K Ω E.1).1 E.2
      exact ⟨f, Subtype.ext hf.symm⟩⟩

/-- The classification of finite unramified subextensions by their positive degrees. -/
def finiteUnramifiedSubextensionDegreeEquiv :
    FiniteUnramifiedSubextension K Ω ≃ ℕ+ :=
  (unramifiedExtensionEquivFiniteUnramifiedSubextension K Ω).symm

namespace FiniteUnramifiedSubextension

/-- The degree of a finite unramified subextension. -/
def degree (E : FiniteUnramifiedSubextension K Ω) : ℕ+ :=
  finiteUnramifiedSubextensionDegreeEquiv K Ω E

/-- The degree classification sends a finite unramified subextension to its degree. -/
theorem finiteUnramifiedSubextensionDegreeEquiv_apply
    (E : FiniteUnramifiedSubextension K Ω) :
    finiteUnramifiedSubextensionDegreeEquiv K Ω E = E.degree :=
  (degree.eq_def K Ω E).symm

@[simp]
theorem degree_unramifiedExtensionPNat (f : ℕ+) :
    (unramifiedExtensionPNat K Ω f).degree = f :=
  (unramifiedExtensionEquivFiniteUnramifiedSubextension K Ω).symm_apply_apply f

/-- The inverse degree classification sends `f` to the canonical unramified extension of
degree `f`. -/
@[simp]
theorem finiteUnramifiedSubextensionDegreeEquiv_symm_apply (f : ℕ+) :
    (finiteUnramifiedSubextensionDegreeEquiv K Ω).symm f =
      unramifiedExtensionPNat K Ω f := by
  apply (finiteUnramifiedSubextensionDegreeEquiv K Ω).injective
  rw [Equiv.apply_symm_apply, finiteUnramifiedSubextensionDegreeEquiv_apply,
    degree_unramifiedExtensionPNat]

/-- The positive degree of a finite unramified subextension is its vector-space dimension over
the base field. -/
@[simp]
theorem coe_degree (E : FiniteUnramifiedSubextension K Ω) :
    (E.degree : ℕ) = Module.finrank K E.1 := by
  have hE : unramifiedExtension K Ω E.degree = E.1 :=
    congrArg Subtype.val
      ((unramifiedExtensionEquivFiniteUnramifiedSubextension K Ω).apply_symm_apply E)
  calc
    (E.degree : ℕ) = Module.finrank K (unramifiedExtension K Ω E.degree) :=
      (finrank_unramifiedExtension E.degree.ne_zero).symm
    _ = Module.finrank K E.1 := congrArg (fun F : IntermediateField K Ω ↦
      Module.finrank K F) hE

/-- A finite unramified subextension is the canonical unramified extension of its vector-space
degree over the base field. -/
@[simp]
theorem unramifiedExtension_finrank (E : FiniteUnramifiedSubextension K Ω) :
    unramifiedExtension K Ω (Module.finrank K E.1) = E.1 := by
  rw [← coe_degree K Ω E]
  exact congrArg Subtype.val
    ((unramifiedExtensionEquivFiniteUnramifiedSubextension K Ω).apply_symm_apply E)

/-- Inclusion of finite unramified subextensions is divisibility of their degrees. -/
theorem le_iff_degree_dvd {E F : FiniteUnramifiedSubextension K Ω} :
    E ≤ F ↔ (E.degree : ℕ) ∣ F.degree := by
  have hE : unramifiedExtension K Ω E.degree = E.1 := by
    simpa only [coe_degree] using unramifiedExtension_finrank K Ω E
  have hF : unramifiedExtension K Ω F.degree = F.1 := by
    simpa only [coe_degree] using unramifiedExtension_finrank K Ω F
  rw [← Subtype.coe_le_coe, ← hE, ← hF]
  exact unramifiedExtension_le_unramifiedExtension_iff K Ω E.degree.ne_zero F.degree.ne_zero

instance : Lattice (FiniteUnramifiedSubextension K Ω) where
  sup E F := unramifiedExtensionPNat K Ω
    (Nat.lcm E.degree F.degree).toPNat'
  le_sup_left E F := (le_iff_degree_dvd K Ω).2 (by
    rw [degree_unramifiedExtensionPNat,
      PNat.toPNat'_coe (Nat.pos_of_ne_zero (Nat.lcm_ne_zero E.degree.ne_zero F.degree.ne_zero))]
    exact Nat.dvd_lcm_left E.degree F.degree)
  le_sup_right E F := (le_iff_degree_dvd K Ω).2 (by
    rw [degree_unramifiedExtensionPNat,
      PNat.toPNat'_coe (Nat.pos_of_ne_zero (Nat.lcm_ne_zero E.degree.ne_zero F.degree.ne_zero))]
    exact Nat.dvd_lcm_right E.degree F.degree)
  sup_le E F G hEG hFG := (le_iff_degree_dvd K Ω).2 (by
    rw [degree_unramifiedExtensionPNat,
      PNat.toPNat'_coe (Nat.pos_of_ne_zero (Nat.lcm_ne_zero E.degree.ne_zero F.degree.ne_zero))]
    exact Nat.lcm_dvd ((le_iff_degree_dvd K Ω).1 hEG)
      ((le_iff_degree_dvd K Ω).1 hFG))
  inf E F := unramifiedExtensionPNat K Ω
    (Nat.gcd E.degree F.degree).toPNat'
  inf_le_left E F := (le_iff_degree_dvd K Ω).2 (by
    rw [degree_unramifiedExtensionPNat,
      PNat.toPNat'_coe (Nat.gcd_pos_of_pos_left F.degree E.degree.pos)]
    exact Nat.gcd_dvd_left E.degree F.degree)
  inf_le_right E F := (le_iff_degree_dvd K Ω).2 (by
    rw [degree_unramifiedExtensionPNat,
      PNat.toPNat'_coe (Nat.gcd_pos_of_pos_left F.degree E.degree.pos)]
    exact Nat.gcd_dvd_right E.degree F.degree)
  le_inf E F G hEF hEG := (le_iff_degree_dvd K Ω).2 (by
    rw [degree_unramifiedExtensionPNat,
      PNat.toPNat'_coe (Nat.gcd_pos_of_pos_left G.degree F.degree.pos)]
    exact Nat.dvd_gcd ((le_iff_degree_dvd K Ω).1 hEF)
      ((le_iff_degree_dvd K Ω).1 hEG))

/-- The positive degree of a meet is the positive natural associated to the greatest common
divisor of the two degrees. This records the defining meet equation of the lattice instance. -/
@[simp]
theorem degree_inf_pnat (E F : FiniteUnramifiedSubextension K Ω) :
    (E ⊓ F).degree = (Nat.gcd E.degree F.degree).toPNat' :=
  degree_unramifiedExtensionPNat K Ω _

/-- The positive degree of a join is the positive natural associated to the least common
multiple of the two degrees. This records the defining join equation of the lattice instance. -/
@[simp]
theorem degree_sup_pnat (E F : FiniteUnramifiedSubextension K Ω) :
    (E ⊔ F).degree = (Nat.lcm E.degree F.degree).toPNat' :=
  degree_unramifiedExtensionPNat K Ω _

/-- The degree of a meet of finite unramified subextensions is the greatest common divisor of
the two degrees. -/
@[simp]
theorem degree_inf (E F : FiniteUnramifiedSubextension K Ω) :
    Module.finrank K (E ⊓ F).1 =
      Nat.gcd (Module.finrank K E.1) (Module.finrank K F.1) := by
  rw [← coe_degree K Ω (E ⊓ F), ← coe_degree K Ω E, ← coe_degree K Ω F]
  rw [degree_inf_pnat,
    PNat.toPNat'_coe (Nat.gcd_pos_of_pos_left F.degree E.degree.pos)]

/-- The degree of a join of finite unramified subextensions is the least common multiple of the
two degrees. -/
@[simp]
theorem degree_sup (E F : FiniteUnramifiedSubextension K Ω) :
    Module.finrank K (E ⊔ F).1 =
      Nat.lcm (Module.finrank K E.1) (Module.finrank K F.1) := by
  rw [← coe_degree K Ω (E ⊔ F), ← coe_degree K Ω E, ← coe_degree K Ω F]
  rw [degree_sup_pnat,
    PNat.toPNat'_coe (Nat.pos_of_ne_zero (Nat.lcm_ne_zero E.degree.ne_zero F.degree.ne_zero))]

end FiniteUnramifiedSubextension

end TauCeti
