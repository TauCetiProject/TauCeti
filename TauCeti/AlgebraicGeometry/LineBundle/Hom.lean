/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import TauCeti.AlgebraicGeometry.LineBundle.Germ
public import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# Morphisms of line bundles on integral schemes

A morphism into a line bundle on an integral scheme is determined on any nonempty open
subset. A nonzero functional on a line bundle is injective, so it embeds the line bundle
as an ideal of the structure sheaf. This is the injectivity input for constructing the
ideal of an effective Cartier divisor from a nonzero section of the dual. These statements
do not require Noetherianity or regularity.

## References

* The Stacks Project, Section 31.14, *Effective Cartier divisors and invertible sheaves*.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- Morphisms into a line bundle on an integral scheme are determined on a nonempty open. -/
theorem hom_ext_of_app {M : X.Modules} (L : InvertibleSheaf X) {φ ψ : M ⟶ L.obj}
    (U : X.Opens) [Nonempty U] (h : ∀ V ≤ U, φ.app V = ψ.app V) : φ = ψ := by
  ext V s
  by_cases hV : Nonempty V
  · let := hV
    have : Nonempty (V ⊓ U : X.Opens) :=
      ⟨⟨genericPoint X, Scheme.genericPoint_mem _, Scheme.genericPoint_mem _⟩⟩
    apply L.map_injective_of_isIntegral (homOfLE (inf_le_left : V ⊓ U ≤ V))
    -- Compare restrictions through the intersection, using naturality on both sides.
    have hnat (f : M ⟶ L.obj) :=
      f.mapPresheaf.naturality_apply (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s
    exact (hnat φ).symm.trans ((congrArg (fun f ↦ f
      (M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s))
        (h (V ⊓ U) inf_le_right)).trans (hnat ψ))
  · let : IsEmpty V := ⟨fun x ↦ hV ⟨x⟩⟩
    exact Scheme.Modules.section_ext_of_isEmpty _ _

variable (L : InvertibleSheaf X)

private theorem app_generator_ne_zero
    (φ : L.obj ⟶ 𝟙_ X.Modules) (hφ : φ ≠ 0)
    {U V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (i : V ⟶ U) [Nonempty V] :
    φ.app V (L.obj.presheaf.map i.op (Scheme.Modules.trivializationGenerator L.obj t)) ≠ 0 := by
  intro hz
  apply hφ
  apply hom_ext_of_app (⟨𝟙_ X.Modules, inferInstance⟩ : InvertibleSheaf X) V
  intro W hWV
  ext s
  rw [Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator
    L.obj t (homOfLE hWV ≫ i) s]
  rw [Scheme.Modules.Hom.app_smul]
  have hnat : φ.app W (L.obj.presheaf.map (homOfLE hWV).op
      (L.obj.presheaf.map i.op (Scheme.Modules.trivializationGenerator L.obj t))) =
      (𝟙_ X.Modules).presheaf.map (homOfLE hWV).op
        (φ.app V (L.obj.presheaf.map i.op (Scheme.Modules.trivializationGenerator L.obj t))) :=
    φ.mapPresheaf.naturality_apply _ _
  rw [hz, map_zero] at hnat
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hnat, smul_zero,
    Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]

/-- A nonzero functional on a line bundle on an integral scheme is injective on sections. -/
theorem app_injective_of_ne_zero_to_unit
    (φ : L.obj ⟶ 𝟙_ X.Modules) (hφ : φ ≠ 0) (V : X.Opens) :
    Function.Injective (φ.app V) := by
  by_cases hV : Nonempty V
  · let := hV
    obtain ⟨U, t, hx⟩ := Scheme.Modules.exists_mem_trivialization L.obj (genericPoint X)
    have : Nonempty (V ⊓ U : X.Opens) :=
      ⟨⟨genericPoint X, Scheme.genericPoint_mem V, hx⟩⟩
    let i : V ⊓ U ⟶ U := homOfLE inf_le_right
    let j : V ⊓ U ⟶ V := homOfLE inf_le_left
    let b := L.obj.presheaf.map i.op (Scheme.Modules.trivializationGenerator L.obj t)
    have hb : (φ.app (V ⊓ U) b : Γ(X, V ⊓ U)) ≠ 0 := L.app_generator_ne_zero φ hφ t i
    apply (injective_iff_map_eq_zero (φ.app V).hom).mpr
    intro s hs
    apply L.map_injective_of_isIntegral j
    apply (Scheme.Modules.trivializationCoordinate L.obj t i).injective
    have hzero : φ.app (V ⊓ U) (L.obj.presheaf.map j.op s) = 0 := by
      have hnat : φ.app (V ⊓ U) (L.obj.presheaf.map j.op s) =
          (𝟙_ X.Modules).presheaf.map j.op (φ.app V s) :=
        φ.mapPresheaf.naturality_apply _ _
      rwa [hs, map_zero] at hnat
    rw [Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator
      L.obj t i (L.obj.presheaf.map j.op s)] at hzero
    rw [Scheme.Modules.Hom.app_smul] at hzero
    -- In the unit sheaf scalar multiplication is multiplication of regular functions.
    let a : Γ(X, V ⊓ U) := φ.app (V ⊓ U) b
    have hmul : (Scheme.Modules.trivializationCoordinate L.obj t i
        (L.obj.presheaf.map j.op s) * a : Γ(X, V ⊓ U)) = 0 := by
      exact (Scheme.Modules.unit_smul_eq_mul X (V ⊓ U) _ _).symm.trans hzero
    simpa only [map_zero] using (mul_eq_zero.mp hmul).resolve_right hb
  · let : IsEmpty V := ⟨fun x ↦ hV ⟨x⟩⟩
    intro s s' _
    exact Scheme.Modules.section_ext_of_isEmpty s s'

/-- A nonzero morphism from a line bundle to the structure sheaf of an integral scheme
is a monomorphism. Equivalently, a nonzero section of the dual is a regular section. -/
theorem mono_of_ne_zero_to_unit
    (φ : L.obj ⟶ 𝟙_ X.Modules) (hφ : φ ≠ 0) : Mono φ :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun V ↦ L.app_injective_of_ne_zero_to_unit φ hφ V.unop)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
