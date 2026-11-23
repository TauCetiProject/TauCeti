/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorProduct

/-!
# Tensoring the exact sequence of a closed subscheme

For an ideal sheaf `I` and a finite locally free module sheaf `E`, tensoring the ideal sequence
with `E` gives the short exact sequence

`0 → E ⊗ I → E ⊗ 𝒪_X → E ⊗ i_*𝒪_{V(I)} → 0`.

The target retains the scheme structure of the closed subscheme, including nilpotents. This
sequence is used to prescribe restrictions of global sections, and in particular jets along
nonreduced effective divisors. No finiteness or regularity of the closed subscheme is needed.

The exactness follows from dualizability: tensoring with a finite locally free sheaf is both
a left and a right adjoint, so it preserves every short exact sequence of sheaves of modules
(`AlgebraicGeometry.Scheme.Modules.shortExact_map_tensorLeft`).

## References

* R. Hartshorne, *Algebraic Geometry*, II, Section 5, and IV, Section 3.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Tensoring the ideal sequence of a closed subscheme with a finite locally free sheaf
preserves short exactness. -/
theorem shortExact_tensor_toPushforwardSubscheme (E : X.Modules)
    [E.IsLocallyFree] [E.IsFiniteType] :
    ((ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft E)).ShortExact :=
  Scheme.Modules.shortExact_map_tensorLeft E I.shortExact_toPushforwardSubscheme

/-- Sections of a finite locally free sheaf restrict surjectively to a closed subscheme
if first cohomology of its tensor product with the ideal sheaf vanishes. -/
theorem surjective_tensorRestriction_of_subsingleton_cohomology_one (E : X.Modules)
    [E.IsLocallyFree] [E.IsFiniteType]
    (hvan : Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (E ⊗ I.sheaf) 1)) :
    Function.Surjective (Scheme.Modules.Hom.app
      ((ρ_ E).inv ≫ E ◁ I.toPushforwardSubscheme) ⊤) := by
  have hsurj := TauCeti.AlgebraicGeometry.Scheme.Modules.sections_surjective
    (I.shortExact_tensor_toPushforwardSubscheme E) hvan
  have hunitor : Function.Surjective (Scheme.Modules.Hom.app (ρ_ E).inv ⊤) :=
    (ConcreteCategory.bijective_of_isIso ((ρ_ E).inv.app ⊤)).2
  exact hsurj.comp hunitor

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules

open MonoidalClosed TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- Tensoring a finite locally free sheaf with an ideal strictly lowers the dimension of
global sections if the ideal support meets the nonvanishing locus of a dual functional. -/
theorem finrank_cohomology_zero_tensorIdeal_lt (k : Type u) [Field k]
    [X.Over (Spec (.of k))] (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType]
    [FiniteDimensional k (Cohomology M 0)]
    (I : X.IdealSheafData) (φ : (ihom M).obj (𝟙_ X.Modules) ⟶ 𝟙_ X.Modules)
    (x : X) (hxI : x ∈ I.support) (hxφ : x ∉ φ.imageIdealSheaf.support) :
    Module.finrank k (Cohomology (M ⊗ I.sheaf) 0) < Module.finrank k (Cohomology M 0) := by
  let j : M ⊗ I.sheaf ⟶ M := M ◁ I.sheafι ≫ (ρ_ M).hom
  have : Mono j := by
    have hmono := (I.shortExact_tensor_toPushforwardSubscheme M).mono_f
    have : Mono (M ◁ I.sheafι) := hmono
    exact inferInstanceAs (Mono (M ◁ I.sheafι ≫ (ρ_ M).hom))
  let j₀ := cohomologyMapBaseLinear k X j 0
  have hjinj : Function.Injective j₀ := by
    dsimp only [j₀]
    simpa only [coe_cohomologyMapBaseLinear] using cohomologyMap_injective j
  have hjnot : ¬Function.Surjective j₀ := by
    intro hj
    apply not_surjective_app_tensorIdeal M I φ x hxI hxφ
    intro s
    obtain ⟨a, ha⟩ := hj ((cohomologyZeroBaseLinearEquiv k X M).symm s)
    refine ⟨cohomologyZeroBaseLinearEquiv k X (M ⊗ I.sheaf) a, ?_⟩
    rw [← cohomologyZeroBaseLinearEquiv_naturality, ha]
    exact (cohomologyZeroBaseLinearEquiv k X M).apply_symm_apply s
  have hrange : j₀.range < ⊤ := lt_top_iff_ne_top.mpr fun h ↦
    hjnot (LinearMap.range_eq_top.mp h)
  have h := Submodule.finrank_lt_finrank_of_lt hrange
  rwa [finrank_top, LinearMap.finrank_range_of_inj hjinj] at h

end

end AlgebraicGeometry.Scheme.Modules
