/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence

/-!
# Subtracting a rational point from an invertible sheaf

Let `L` be an invertible sheaf on a scheme `X` over a field `k`, with finite-dimensional global
sections and vanishing first cohomology. If a `k`-rational point `p` avoids the zero locus of a
section of `L`, then tensoring `L` with the ideal sheaf of `p` lowers the dimension of global
sections by one and preserves the vanishing of first cohomology.

The proof combines the exact sequence of the point ideal with the Euler-characteristic
formula for tensoring an invertible sheaf with a finite subscheme's ideal sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- If a rational point avoids the zero locus of a section of a line bundle with vanishing
first cohomology, subtracting the point leaves one fewer global section and still has
vanishing first cohomology. The zero locus is expressed by the image ideal of the associated
functional on the dual bundle. Only finiteness of the original space of global sections is
required; first cohomology is finite-dimensional because it vanishes. -/
theorem finrank_cohomology_zero_tensor_ker_add_one_and_subsingleton
    (k : Type u) [Field k] [X.Over (Spec (.of k))] (L : InvertibleSheaf X)
    [FiniteDimensional k (Cohomology L.obj 0)]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ X ↘ Spec (.of k) = 𝟙 _)
    (φ : (InvertibleSheaf.dual L).obj ⟶ 𝟙_ X.Modules)
    (hpφ : p default ∉ φ.imageIdealSheaf.support)
    (hvan : Subsingleton (Cohomology L.obj 1)) :
    Module.finrank k (Cohomology (L.obj ⊗ p.ker.sheaf) 0) + 1 =
      Module.finrank k (Cohomology L.obj 0) ∧
      Subsingleton (Cohomology (L.obj ⊗ p.ker.sheaf) 1) := by
  have := _root_.AlgebraicGeometry.isClosedImmersion_of_comp_eq_id
    (X ↘ Spec (.of k)) p hp
  have := hvan
  have : FiniteDimensional k (Cohomology L.obj 1) := inferInstance
  let M : SheafOfModules X.ringCatSheaf := L.obj
  have : L.obj.IsLocallyFree := inferInstanceAs M.IsLocallyFree
  have : L.obj.IsFiniteType := inferInstanceAs M.IsFiniteType
  let e : (ihom L.obj).obj (𝟙_ X.Modules) ≅ (InvertibleSheaf.dual L).obj :=
    eqToIso (InvertibleSheaf.dual_obj L).symm
  let φ₀ := e.hom ≫ φ
  have hφ₀ : φ₀.imageIdealSheaf = φ.imageIdealSheaf := φ.imageIdealSheaf_comp_iso e
  have := p.isIso_ker_subschemeι_comp hp
  let E := (InvertibleSheaf.toFixedRankOne X).obj L
  have hE : E.obj.obj = L.obj := by
    rw [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj]
  have hfin := p.ker.finiteDimensional_cohomology_tensor_sheaf_iff (k := k) (E := E)
  rw [hE] at hfin
  have := hfin.mpr (fun i hi ↦ by interval_cases i <;> infer_instance) 1 (by omega)
  have hlt := finrank_cohomology_zero_tensorIdeal_lt k L.obj p.ker φ₀ (p default)
    (p.range_subset_ker_support ⟨default, rfl⟩) (hφ₀ ▸ hpφ)
  have : FiniteDimensional k (Cohomology E.obj.obj 0) := hE ▸ inferInstance
  have : FiniteDimensional k (Cohomology E.obj.obj 1) := hE ▸ inferInstance
  have hχ := p.ker.eulerCharBelow_tensor_sheaf k E default
  rw [hE, Nat.cast_one, one_mul,
    Scheme.Hom.finrank_eq_one_of_isIso (p.ker.subschemeι ≫ X ↘ Spec (.of k)),
    Pi.one_apply] at hχ
  rw [eulerCharBelow_two, eulerCharBelow_two,
    Module.finrank_zero_of_subsingleton (M := Cohomology L.obj 1)] at hχ
  have hzero : Module.finrank k (Cohomology (L.obj ⊗ p.ker.sheaf) 1) = 0 := by omega
  exact ⟨by omega, Module.finrank_zero_iff.mp hzero⟩

end

end AlgebraicGeometry.Scheme.Modules
