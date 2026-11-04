/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf

/-!
# Effective Cartier divisors on integral schemes

A Cartier divisor is effective when its local equations are regular at every point. On an
integral scheme, a nonzero local equation is automatically a nonzerodivisor. This absolute
divisor construction supports the divisor and line-bundle dictionary and, later, relative
effective Cartier divisors in families of curves.

Effectivity can be checked using one local equation at each point. Equivalently, the constant
section `1` of the rational-function sheaf belongs to `𝒪_X(D)` globally. For a principal
Cartier divisor, effectivity says that its defining rational function is a global regular
function. The zero divisor is effective, and sums of effective divisors are effective.

The local-equation definition follows the Stacks Project, *Divisors*, Tag 01WQ. The sheaf
criterion uses the construction of `𝒪_X(D)` in `CartierDivisor/Sheaf`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- A Cartier divisor is effective if each of its local equations is regular at the point
where it is an equation. Since `X` is integral, these nonzero equations are nonzerodivisors. -/
def IsEffective (D : CartierDivisor X) : Prop :=
  ∀ (x : X) (f : X.functionFieldˣ), D.IsLocalEquationAt x f →
    (f : X.functionField) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range

/-- To check effectivity, it suffices to find one regular local equation at every point. -/
theorem isEffective_iff_exists {D : CartierDivisor X} :
    D.IsEffective ↔ ∀ x : X, ∃ f : X.functionFieldˣ,
      D.IsLocalEquationAt x f ∧
        (f : X.functionField) ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · intro h x
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    exact ⟨f, hf, h x f hf⟩
  · intro h x f hf
    obtain ⟨g, hg, hreg⟩ := h x
    simpa only [mul_one] using (hf.mul_mem_range_iff hg 1).mpr (by simpa using hreg)

/-- The zero Cartier divisor is effective. -/
@[simp]
theorem isEffective_zero : (0 : CartierDivisor X).IsEffective := by
  apply isEffective_iff_exists.mpr
  intro x
  refine ⟨1, isLocalEquationAt_zero x, ?_⟩
  simp

/-- The sum of two effective Cartier divisors is effective. -/
theorem IsEffective.add {D E : CartierDivisor X} (hD : D.IsEffective) (hE : E.IsEffective) :
    (D + E).IsEffective := by
  apply isEffective_iff_exists.mpr
  intro x
  obtain ⟨f, hf, hfr⟩ := isEffective_iff_exists.mp hD x
  obtain ⟨g, hg, hgr⟩ := isEffective_iff_exists.mp hE x
  refine ⟨f * g, hf.mul hg, ?_⟩
  exact Subring.mul_mem _ hfr hgr

/-- Effective Cartier divisors form an additive submonoid. -/
def effectiveSubmonoid (X : Scheme.{u}) [IsIntegral X] : AddSubmonoid (CartierDivisor X) where
  carrier := {D | D.IsEffective}
  zero_mem' := isEffective_zero
  add_mem' := fun hD hE => hD.add hE

/-- Membership in the effective Cartier divisor submonoid is effectivity. -/
@[simp]
theorem mem_effectiveSubmonoid (D : CartierDivisor X) :
    D ∈ effectiveSubmonoid X ↔ D.IsEffective :=
  Iff.rfl

/-- Effectivity can be tested by the single global section `1` of `𝒪_X`. -/
theorem isEffective_iff_one_mem_sections {D : CartierDivisor X} :
    D.IsEffective ↔
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) ⊤
        (1 : Γ(X, (⊤ : X.Opens))) ∈ D.sections ⊤ := by
  rw [isEffective_iff_exists, mem_sections_iff_exists]
  simp only [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one]
  simp

/-- A Cartier divisor is effective exactly when the regular functions are sections of
`𝒪_X(D)` under the canonical inclusion into rational functions. -/
theorem isEffective_iff_toRationalFunctions_mem_sections {D : CartierDivisor X} :
    D.IsEffective ↔ ∀ (U : X.Opens) (s : Γ(X, U)),
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U s ∈ D.sections U := by
  constructor
  · intro h U s
    rw [mem_sections]
    intro x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app,
      ← _root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx s]
    exact Subring.mul_mem _ (h x f hf) (RingHom.mem_range_self _ _)
  · intro h
    exact isEffective_iff_one_mem_sections.mpr (h ⊤ 1)

/-- An effective Cartier divisor has the canonical inclusion `𝒪_X ⟶ 𝒪_X(D)`.
Its composite with `𝒪_X(D) ⟶ 𝒦_X` is the usual inclusion of regular functions into rational
functions. -/
def unitToSheaf (D : CartierDivisor X) (hD : D.IsEffective) :
    SheafOfModules.unit X.ringCatSheaf ⟶ D.sheaf :=
  D.sheafLift (Scheme.toRationalFunctions X)
    (isEffective_iff_toRationalFunctions_mem_sections.mp hD)

/-- The inclusion `𝒪_X ⟶ 𝒪_X(D)` of an effective Cartier divisor agrees with the usual
inclusion after embedding both sheaves in rational functions. -/
@[simp, reassoc]
theorem unitToSheaf_ι (D : CartierDivisor X) (hD : D.IsEffective) :
    D.unitToSheaf hD ≫ D.sheafι = Scheme.toRationalFunctions X :=
  D.sheafLift_ι _ _

/-- The canonical map from regular functions to the sheaf of an effective Cartier divisor
is a monomorphism. -/
instance (D : CartierDivisor X) (hD : D.IsEffective) : Mono (D.unitToSheaf hD) := by
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _
    (Scheme.instMonoModulesToRationalFunctions (X := X)) (D.unitToSheaf_ι hD)

/-- Effectivity is equivalent to the existence of a map `𝒪_X ⟶ 𝒪_X(D)` whose composite
with the inclusion into rational functions is the usual inclusion of regular functions. -/
theorem isEffective_iff_exists_unitToSheaf {D : CartierDivisor X} :
    D.IsEffective ↔ ∃ φ : SheafOfModules.unit X.ringCatSheaf ⟶ D.sheaf,
      φ ≫ D.sheafι = Scheme.toRationalFunctions X := by
  constructor
  · intro hD
    exact ⟨D.unitToSheaf hD, D.unitToSheaf_ι hD⟩
  · rintro ⟨φ, hφ⟩
    apply isEffective_iff_toRationalFunctions_mem_sections.mpr
    intro U s
    have h := D.sheafι_app_mem U (Scheme.Modules.Hom.app φ U s)
    rw [← hφ]
    exact h

/-- The map from regular functions to `𝒪_X(D)` is determined by its composite with the
inclusion into rational functions. -/
theorem eq_unitToSheaf (D : CartierDivisor X) (hD : D.IsEffective)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ D.sheaf)
    (hφ : φ ≫ D.sheafι = Scheme.toRationalFunctions X) :
    φ = D.unitToSheaf hD := by
  apply (cancel_mono D.sheafι).mp
  exact hφ.trans (D.unitToSheaf_ι hD).symm

/-- A principal Cartier divisor is effective exactly when its rational equation is regular
on the whole scheme. -/
theorem isEffective_principalCartierDivisor_iff (f : X.functionFieldˣ) :
    (principalCartierDivisor X f).IsEffective ↔
      ∃ a : Γ(X, (⊤ : X.Opens)), X.germToFunctionField ⊤ a = (f : X.functionField) := by
  have : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstanceAs (Nonempty X)), by simp⟩⟩
  rw [isEffective_iff_one_mem_sections,
    mem_sections_iff_of_rationalUnitClass_eq le_rfl
      (principalCartierDivisor_restrict X f ⊤).symm]
  simp only [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one]

end Scheme.CartierDivisor

end

end AlgebraicGeometry

end TauCeti
