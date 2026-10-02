/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The connecting map across the Tate norm

For a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, the connecting map
`Ĥ⁻¹(G, M₃) → Ĥ⁰(G, M₁)` has a concrete description: lift a norm-zero element of `M₃` to
`M₂`, take its norm, and lift that norm to an invariant element of `M₁`. The class of this
invariant is the image under the connecting map. This description allows the change-of-group
maps on the norm kernel and the invariants to be compared across the boundary of the Tate complex.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep groupHomology groupCohomology

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The connecting map from degree `-1` to degree zero sends a norm-zero representative to the
class of the norm of a lift, read in the invariant submodule of the first coefficient module. -/
theorem δ_neg_one_HNegOneπ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (z : LinearMap.ker S.X₃.ρ.norm) (y : S.X₂) (hy : S.g.hom y = z)
    (x : S.X₁.ρ.invariants) (hx : S.f.hom x = S.X₂.ρ.norm y) :
    _root_.TateCohomology.δ hS (-1) (HNegOneπ S.X₃ z) = H0π S.X₁ x := by
  -- Translate the norm-kernel and invariant representatives to the cycles used by the
  -- snake lemma. The two squares below express that `y` lifts `z` and its norm lifts `x`.
  let y' : (tateComplex S.X₂).X (-1) := (chainsIso₀ S.X₂).inv y
  have hc₃ : (HNegOneCyclesIso S.X₃).inv ≫ (tateComplex S.X₃).iCycles (-1) ≫
      (chainsIso₀ S.X₃).hom = ModuleCat.ofHom (LinearMap.ker S.X₃.ρ.norm).subtype :=
    (congrArg ((HNegOneCyclesIso S.X₃).inv ≫ ·)
      (HNegOneCyclesIso_hom_comp_subtype S.X₃).symm).trans (Iso.inv_hom_id_assoc _ _)
  have hc₁ : (H0CyclesIso S.X₁).inv ≫ (tateComplex S.X₁).iCycles 0 ≫
      (cochainsIso₀ S.X₁).hom = ModuleCat.ofHom S.X₁.ρ.invariants.subtype :=
    (congrArg ((H0CyclesIso S.X₁).inv ≫ ·)
      (H0CyclesIso_hom_comp_subtype S.X₁).symm).trans (Iso.inv_hom_id_assoc _ _)
  have hp₃ : HNegOneπ S.X₃ ≫ (tateComplex S.X₃).homologyι (-1) =
      (HNegOneCyclesIso S.X₃).inv ≫ (tateComplex S.X₃).iCycles (-1) ≫
        (tateComplex S.X₃).pOpcycles (-1) :=
    (congrArg (· ≫ (tateComplex S.X₃).homologyι (-1))
      (HNegOneπ_eq_cyclesIso_inv_comp_homologyπ S.X₃)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (HomologicalComplex.homology_π_ι (K := tateComplex S.X₃) (-1))))
  have hg : (tateComplex.map S.g).f (-1) y' =
      (tateComplex S.X₃).iCycles (-1) ((HNegOneCyclesIso S.X₃).inv z) := by
    apply (ModuleCat.mono_iff_injective (chainsIso₀ S.X₃).hom).mp inferInstance
    calc
      _ = S.g.hom y := by
        simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using!
          ConcreteCategory.congr_hom (chainsMap_f_0_comp_chainsIso₀ (.id G) S.g)
            ((chainsIso₀ S.X₂).inv y)
      _ = z := hy
      _ = _ := by
        simpa only [ConcreteCategory.comp_apply] using! (ConcreteCategory.congr_hom hc₃ z).symm
  have hf : HomologicalComplex.cyclesMap (tateComplex.map S.f) 0
      ((H0CyclesIso S.X₁).inv x) =
      (tateComplex S.X₂).opcyclesToCycles (-1) 0
        ((tateComplex S.X₂).pOpcycles (-1) y') := by
    apply (ModuleCat.mono_iff_injective ((tateComplex S.X₂).iCycles 0)).mp inferInstance
    have hleft := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (tateComplex.map S.f) 0) ((H0CyclesIso S.X₁).inv x)
    have hright := ConcreteCategory.congr_hom
      (HomologicalComplex.p_fromOpcycles (tateComplex S.X₂) (-1) 0) y'
    have hright' := ConcreteCategory.congr_hom
      (HomologicalComplex.opcyclesToCycles_iCycles (tateComplex S.X₂) (-1) 0)
      ((tateComplex S.X₂).pOpcycles (-1) y')
    simp only [ConcreteCategory.comp_apply] at hleft hright hright'
    refine hleft.trans (Eq.trans ?_ (hright.symm.trans hright'.symm))
    apply (ModuleCat.mono_iff_injective (cochainsIso₀ S.X₂).hom).mp inferInstance
    calc
      _ = S.f.hom x := by
        have hnat := ConcreteCategory.congr_hom
          (cochainsMap_f_0_comp_cochainsIso₀ (.id G) S.f)
          ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x))
        have hcx := ConcreteCategory.congr_hom hc₁ x
        simp only [ConcreteCategory.comp_apply] at hnat hcx
        exact hnat.trans (congrArg S.f.hom hcx)
      _ = S.X₂.ρ.norm y := hx
      _ = _ := by
        -- The differential at the join is the Tate norm; the two comparison isomorphisms cancel.
        have hn : (chainsIso₀ S.X₂).inv ≫ (tateComplex S.X₂).d (-1) 0 ≫
            (cochainsIso₀ S.X₂).hom = S.X₂.norm.toModuleCatHom := by
          rw [tateComplex_d_neg_one, Rep.tateNorm]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
        simpa only [ConcreteCategory.comp_apply] using!
          (ConcreteCategory.congr_hom hn y).symm
  have h := (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).δ_apply'
    (-1) 0 (by simp) (HNegOneπ S.X₃ z)
    ((tateComplex S.X₂).pOpcycles (-1) y') ((H0CyclesIso S.X₁).inv x) ?_ ?_
  · simpa only [H0π_eq_cyclesIso_inv_comp_homologyπ, ConcreteCategory.comp_apply] using! h
  · -- The snake-lemma API inserts the forgetful functor and `ShortComplex.map`. These wrappers
    -- have the same underlying functions as the module maps used above.
    change HomologicalComplex.opcyclesMap (tateComplex.map S.g) (-1)
      ((tateComplex S.X₂).pOpcycles (-1) y') =
        (tateComplex S.X₃).homologyι (-1) (HNegOneπ S.X₃ z)
    have hn := ConcreteCategory.congr_hom
      (HomologicalComplex.p_opcyclesMap (tateComplex.map S.g) (-1)) y'
    simp only [ConcreteCategory.comp_apply] at hn
    have hp := ConcreteCategory.congr_hom hp₃ z
    simp only [ConcreteCategory.comp_apply] at hp
    exact hn.trans ((congrArg ((tateComplex S.X₃).pOpcycles (-1)) hg).trans hp.symm)
  · -- Remove the same snake-lemma wrappers on the degree-zero cycles.
    exact hf

/-- Every class in degree `-1` admits lifts realizing the norm formula for its connecting image. -/
theorem exists_δ_neg_one_eq_H0π {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (z : LinearMap.ker S.X₃.ρ.norm) :
    ∃ (y : S.X₂) (x : S.X₁.ρ.invariants), S.g.hom y = z ∧
      S.f.hom x = S.X₂.ρ.norm y ∧
      _root_.TateCohomology.δ hS (-1) (HNegOneπ S.X₃ z) = H0π S.X₁ x := by
  obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective S.g).mp hS.epi_g z
  have hzero : S.g.hom (S.X₂.ρ.norm y) = 0 := by
    have hn := congrArg (fun f : S.X₂ ⟶ S.X₃ => f.hom y) (Rep.norm_comm S.g)
    calc
      _ = S.X₃.ρ.norm (S.g.hom y) := by simpa using hn.symm
      _ = 0 := by rw [hy]; exact z.2
  have he : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.exact.map (forget₂ (Rep R G) (ModuleCat R)))
  obtain ⟨x, hx⟩ := (he (S.X₂.ρ.norm y)).mp hzero
  have hxinv : x ∈ S.X₁.ρ.invariants := by
    intro g
    apply (Rep.mono_iff_injective S.f).mp hS.mono_f
    rw [Rep.hom_comm_apply, hx]
    simp
  exact ⟨y, ⟨x, hxinv⟩, hy, hx, δ_neg_one_HNegOneπ hS z y hy ⟨x, hxinv⟩ hx⟩

end TauCeti.TateCohomology
