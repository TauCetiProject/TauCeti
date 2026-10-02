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

For a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, the Tate connecting map from degree `-1`
of `M₃` to degree zero of `M₁` has a concrete description: lift a norm-zero element of `M₃` to
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
  -- concrete connecting-map formula. The two squares express that `y` lifts `z`
  -- and its norm lifts `x`.
  let y' : (tateComplex S.X₂).X (-1) := (chainsIso₀ S.X₂).inv y
  have hc₃ : (HNegOneCyclesIso S.X₃).inv ≫ (tateComplex S.X₃).iCycles (-1) ≫
      (chainsIso₀ S.X₃).hom = ModuleCat.ofHom (LinearMap.ker S.X₃.ρ.norm).subtype :=
    (congrArg ((HNegOneCyclesIso S.X₃).inv ≫ ·)
      (HNegOneCyclesIso_hom_comp_subtype S.X₃).symm).trans (Iso.inv_hom_id_assoc _ _)
  have hc₁ : (H0CyclesIso S.X₁).inv ≫ (tateComplex S.X₁).iCycles 0 ≫
      (cochainsIso₀ S.X₁).hom = ModuleCat.ofHom S.X₁.ρ.invariants.subtype :=
    (congrArg ((H0CyclesIso S.X₁).inv ≫ ·)
      (H0CyclesIso_hom_comp_subtype S.X₁).symm).trans (Iso.inv_hom_id_assoc _ _)
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
  have hf : (tateComplex.map S.f).f 0
      ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x)) =
      (tateComplex S.X₂).d (-1) 0 y' := by
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
  have hz : (tateComplex S.X₃).d (-1) 0
      ((tateComplex S.X₃).iCycles (-1) ((HNegOneCyclesIso S.X₃).inv z)) = 0 := by
    simpa using!
      ConcreteCategory.congr_hom ((tateComplex S.X₃).iCycles_d (-1) 0)
        ((HNegOneCyclesIso S.X₃).inv z)
  have h := (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).δ_apply
    (-1) 0 (by simp)
    ((tateComplex S.X₃).iCycles (-1) ((HNegOneCyclesIso S.X₃).inv z)) hz
    y' hg ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x)) hf 1 (by simp)
  have hc₃' : (tateComplex S.X₃).cyclesMk (i := (-1))
      ((tateComplex S.X₃).iCycles (-1) ((HNegOneCyclesIso S.X₃).inv z)) 0
      (by simp) hz = (HNegOneCyclesIso S.X₃).inv z := by
    apply (ModuleCat.mono_iff_injective ((tateComplex S.X₃).iCycles (-1))).mp inferInstance
    simpa using! HomologicalComplex.i_cyclesMk (tateComplex S.X₃) (i := (-1))
      ((tateComplex S.X₃).iCycles (-1) ((HNegOneCyclesIso S.X₃).inv z)) 0 (by simp) hz
  have hc₁' (hzero : (tateComplex S.X₁).d 0 1
      ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x)) = 0) :
      (tateComplex S.X₁).cyclesMk (i := 0)
      ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x)) 1 (by simp)
      hzero = (H0CyclesIso S.X₁).inv x := by
    apply (ModuleCat.mono_iff_injective ((tateComplex S.X₁).iCycles 0)).mp inferInstance
    simpa using! HomologicalComplex.i_cyclesMk (tateComplex S.X₁) (i := 0)
      ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x)) 1 (by simp) hzero
  change _root_.TateCohomology.δ hS (-1)
      ((tateComplex S.X₃).homologyπ (-1) ((tateComplex S.X₃).cyclesMk (i := (-1))
        ((tateComplex S.X₃).iCycles (-1) ((HNegOneCyclesIso S.X₃).inv z)) 0 (by simp) hz)) =
      (tateComplex S.X₁).homologyπ 0 ((tateComplex S.X₁).cyclesMk (i := 0)
        ((tateComplex S.X₁).iCycles 0 ((H0CyclesIso S.X₁).inv x)) 1 (by simp) _) at h
  erw [hc₃', hc₁'] at h
  rw [HNegOneπ_eq_cyclesIso_inv_comp_homologyπ, H0π_eq_cyclesIso_inv_comp_homologyπ]
  exact h

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
