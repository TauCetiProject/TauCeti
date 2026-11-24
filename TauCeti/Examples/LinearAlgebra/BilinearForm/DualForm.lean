/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.Standard
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Form

/-!
# The dual of a doubled principal form

Let `E₀` be the standard principal alternating form on the lattice `ℤ + iℤ`
(`TauCeti.Hodge.StandardWeightOne.riemannForm` for `g = 1`), and `E = 2 E₀`. The map
`E♭ : Λ → Hom(Λ, ℤ)` is injective with cokernel killed by `2` but not by `1`. The dual form of the
rational extension of `E` takes the value `1/2` on two integral functionals, so it is not integral
on `Hom(Λ, ℤ)`. With `e = 2`, the integral form `2 E^∨` is the dual form `E₀^∨` of `E₀`, which is
principal.
-/

public section

namespace TauCeti.DualFormExamples

open LinearMap LinearMap.BilinForm Module TauCeti.Hodge.StandardWeightOne

/-- The lattice `ℤ + iℤ`, as `ℤ^{1 ⊕ 1}`. -/
abbrev Λ : Type := Hodge.StandardWeightOne.Lattice Unit

/-- The standard principal alternating form `E₀` on `ℤ + iℤ`. -/
noncomputable abbrev E₀ : LinearMap.BilinForm ℤ Λ := riemannForm Unit

/-- The doubled form `E = 2 E₀`. -/
noncomputable abbrev E : LinearMap.BilinForm ℤ Λ := (2 : ℤ) • E₀

/-- `E₀` is principal. -/
instance instIsPerfPairE₀ : E₀.IsPerfPair := isPerfPair_riemannForm Unit

/-- `E♭ = 2 E₀♭` is injective. -/
theorem injective_E : Function.Injective E := fun _ _ h ↦
  (IsPerfPair.bijective_left E₀).injective <| smul_right_injective _ two_ne_zero h

/-- The cokernel of `E♭` is killed by `2`. -/
theorem two_smul_mem_range_E (η : Dual ℤ Λ) : (2 : ℤ) • η ∈ LinearMap.range E :=
  ⟨E₀.toPerfPair.symm η, by simp⟩

/-- The rational extension of `E` is nondegenerate. -/
theorem nondegenerate_E_rational :
    ((isBaseChange_latticeToRational Unit).bilinForm E).Nondegenerate := by
  refine (isBaseChange_latticeToRational Unit).nondegenerate_bilinForm_iff E |>.mpr
    ⟨fun x hx ↦ injective_E ?_, fun y hy ↦ ?_⟩
  · exact LinearMap.ext fun z ↦ by simpa using hx z
  · refine (IsPerfPair.bijective_right E₀).injective <|
      smul_right_injective _ (two_ne_zero (α := ℤ)) (LinearMap.ext fun z ↦ ?_)
    simpa using hy z

/-- The vector `1 ∈ ℤ + iℤ`. -/
abbrev one : Λ := Pi.single (Sum.inl ()) 1

/-- The coordinate functional of `1 ∈ ℤ + iℤ`. -/
abbrev coordOne : Dual ℤ Λ := LinearMap.proj (Sum.inl ())

/-- The integral form `2 E^∨` is `E₀^∨`: it pairs `ξ` with `E₀♭ y` to `ξ(y)`. -/
theorem scaledDualForm_E_apply (ξ : Dual ℤ Λ) (y : Λ) :
    E.scaledDualForm injective_E 2 two_smul_mem_range_E ξ (E₀ y) = ξ y := by
  rw [scaledDualForm_apply, (E.scaledDualPreimage_eq_iff injective_E 2 two_smul_mem_range_E _ y).mpr
    (by simp)]

/-- **The dual form of `2 E₀` is not integral**: it pairs the integral functionals `ξ = x ↦ x₁`
and `E₀♭ 1` to `1/2`. -/
theorem dualForm_E_eq_half :
    ((isBaseChange_latticeToRational Unit).bilinForm E).dualForm nondegenerate_E_rational
        ((isBaseChange_latticeToRational Unit).toDual coordOne)
        ((isBaseChange_latticeToRational Unit).toDual (E₀ one)) = 1 / 2 := by
  have h := algebraMap_scaledDualForm E injective_E 2 two_smul_mem_range_E
    (isBaseChange_latticeToRational Unit) nondegenerate_E_rational coordOne (E₀ one)
  rw [scaledDualForm_E_apply] at h
  have h1 : coordOne one = 1 := by simp
  rw [h1, map_one, map_ofNat] at h
  linear_combination -h / 2

/-- The cokernel of `E♭` is not killed by `1`: otherwise the dual form would be integral. -/
theorem not_forall_mem_range_E : ¬ ∀ η : Dual ℤ Λ, (1 : ℤ) • η ∈ LinearMap.range E := by
  intro h1
  have h := algebraMap_scaledDualForm E injective_E 1 h1
    (isBaseChange_latticeToRational Unit) nondegenerate_E_rational coordOne (E₀ one)
  rw [dualForm_E_eq_half, map_one, one_mul] at h
  rw [eq_intCast] at h
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (c : ℚ) = 1 / 2 := ⟨_, h⟩
  have : (c : ℚ) * 2 = 1 := by rw [hc]; norm_num
  have : c * 2 = 1 := by exact_mod_cast this
  omega

/-- **`2 E^∨` is principal**: it is the integral dual form of the principal form `E₀`. -/
theorem scaledDualForm_E_eq :
    E.scaledDualForm injective_E 2 two_smul_mem_range_E =
      E₀.scaledDualForm (IsPerfPair.bijective_left E₀).injective 1
        E₀.one_smul_mem_range_of_isPerfPair := by
  refine LinearMap.ext₂ fun ξ η ↦ ?_
  obtain ⟨y, rfl⟩ := (IsPerfPair.bijective_left E₀).surjective η
  rw [scaledDualForm_E_apply, scaledDualForm_apply_right, one_mul]

/-- `2 E^∨` is a perfect pairing on `Hom(Λ, ℤ)`. -/
theorem isPerfPair_scaledDualForm_E :
    (E.scaledDualForm injective_E 2 two_smul_mem_range_E).IsPerfPair := by
  rw [scaledDualForm_E_eq]
  exact isPerfPair_scaledDualForm_one E₀

end TauCeti.DualFormExamples
