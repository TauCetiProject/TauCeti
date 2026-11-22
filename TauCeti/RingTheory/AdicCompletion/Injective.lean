/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.AdicCompletion.Basic
import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicCompletion.Torsion

/-!
# Injectivity of ideal-power-torsion modules over the completion

Let `I` be an ideal of a Noetherian commutative ring `R`, let `R̂ = AdicCompletion I R`, and let
`M` be an `R`-module in which every element is killed by a power of `I`. By
`TauCeti.AdicCompletion.torsionModule`, `M` carries a canonical `R̂`-module structure in which each
completed scalar acts on an `I ^ n`-torsion element through its residue modulo `I ^ n`.

Since `R` is Noetherian, `R̂` is Noetherian (`Ideal.isNoetherianRing_adicCompletion`). Using
Baer's criterion and the Artin–Rees lemma on ideals of `R̂`, any `I`-power-torsion `R`-module
satisfying Baer's criterion over `R` also satisfies Baer's criterion over `R̂`, so injectivity of
`M` over `R` lifts to injectivity over `R̂` (`TauCeti.AdicCompletion.torsionModule_injective`,
Stacks Project Tag 08Z5). Moreover, `[Small.{v} R]` supplies `[Small.{v} R̂]` via
`TauCeti.AdicCompletion.instSmall` (from `TauCeti.RingTheory.AdicCompletion.Basic`).

## Main declarations

* `TauCeti.AdicCompletion.torsionModule_baer` and `TauCeti.AdicCompletion.torsionModule_injective`:
  Baer's criterion and module injectivity lift from `R` to `AdicCompletion I R` over a Noetherian
  ring `R`.

## References

* [Stacks Project, Lemma 47.7.4](https://stacks.math.columbia.edu/tag/08Z5)
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

universe u v w

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

section Noetherian

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
  {M : Type w} [AddCommGroup M] [Module R M]
  (hM : ∀ x : M, x ∈ I.primaryComponent M)

/-- By Artin–Rees on ideals of the Noetherian completion `R̂`, any `R̂`-linear map out of an ideal
`𝔟` of `R̂` into an `I`-power-torsion module vanishes on `𝔟 ⊓ I ^ m R̂` for some `m : ℕ`. -/
private theorem exists_ker_evalₐ_le_ker_of_torsionModule
    (𝔟 : Ideal (_root_.AdicCompletion I R))
    (g : letI := torsionModule hM; 𝔟 →ₗ[_root_.AdicCompletion I R] M) :
    letI := torsionModule hM
    haveI := torsionModule_isScalarTower hM
    ∃ m : ℕ, LinearMap.ker ((evalₐ I m).toLinearMap ∘ₗ 𝔟.subtype.restrictScalars R) ≤
      LinearMap.ker (g.restrictScalars R) := by
  let A := _root_.AdicCompletion I R
  let := torsionModule hM
  have := torsionModule_isScalarTower hM
  let IA : Ideal A := I.map (algebraMap R A)
  have hfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨n, hn⟩ := IA.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent g
    fun b ↦ mem_map_primaryComponent_torsionModule hM hfg (g b)
  obtain ⟨k, hk⟩ := IA.exists_pow_inf_eq_pow_smul (M := A) 𝔟
  refine ⟨n + k, fun b hb ↦ ?_⟩
  have hm : IA ^ (n + k) ⊓ 𝔟 ≤ IA ^ n • 𝔟 := by
    have hmk := hk (n + k) (Nat.le_add_left k n)
    simp only [smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_right] at hmk
    exact hmk.le.trans (Submodule.smul_mono le_rfl inf_le_right)
  have hbm : (b : A) ∈ IA ^ (n + k) := by
    rw [← Ideal.map_pow, ← ker_evalₐ_eq_map_pow hfg (n + k)]
    exact hb
  have hmem : (b : A) ∈ (LinearMap.ker g).map 𝔟.subtype := by
    refine Submodule.smul_le.mpr ?_ (hm ⟨hbm, b.property⟩)
    intro a ha c hc
    have hac : (⟨a * c, 𝔟.mul_mem_left a hc⟩ : 𝔟) = a • ⟨c, hc⟩ := Subtype.ext rfl
    refine ⟨⟨a * c, 𝔟.mul_mem_left a hc⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hac, map_smul]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn ⟨c, hc⟩) ⟨a, ha⟩
  rcases hmem with ⟨⟨w, hw⟩, hgw, hw_eq⟩
  have hbw : b = ⟨w, hw⟩ := Subtype.ext hw_eq.symm
  exact hbw ▸ hgw

/-- Over a Noetherian ring `R`, an `I`-power-torsion `R`-module satisfying Baer's criterion over `R`
also satisfies Baer's criterion over `AdicCompletion I R`. -/
@[stacks 08Z5]
theorem torsionModule_baer (hBaer : Module.Baer R M) :
    letI := torsionModule hM
    Module.Baer (_root_.AdicCompletion I R) M := by
  let A := _root_.AdicCompletion I R
  let := torsionModule hM
  have := torsionModule_isScalarTower hM
  intro 𝔟 g
  obtain ⟨m, hker⟩ := exists_ker_evalₐ_le_ker_of_torsionModule hM 𝔟 g
  -- Factor `g` through the image of `𝔟` in `R ⧸ I ^ m`, then pull back to an ideal `K` of `R`.
  let p : 𝔟 →ₗ[R] R ⧸ I ^ m := (evalₐ I m).toLinearMap ∘ₗ 𝔟.subtype.restrictScalars R
  let gbar : LinearMap.range p →ₗ[R] M :=
    (LinearMap.ker p).liftQ (g.restrictScalars R) hker ∘ₗ p.quotKerEquivRange.symm.toLinearMap
  let K : Ideal R := (LinearMap.range p).comap (I ^ m).mkQ
  let q : K →ₗ[R] LinearMap.range p := ((I ^ m).mkQ ∘ₗ K.subtype).codRestrict _ fun x ↦ x.property
  obtain ⟨ψ, hψ⟩ := hBaer K (gbar ∘ₗ q)
  have hy₀ : ψ 1 ∈ Submodule.torsionBySet R M ↑(I ^ m) := by
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨r, hr⟩
    have hr0 : (I ^ m).mkQ r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    have hrK : r ∈ K := Submodule.mem_comap.mpr (hr0 ▸ zero_mem p.range)
    have hqr : q ⟨r, hrK⟩ = 0 := Subtype.ext hr0
    rw [← map_smul, smul_eq_mul, mul_one, hψ r hrK, LinearMap.comp_apply, hqr, gbar.map_zero]
  refine ⟨LinearMap.toSpanSingleton A M (ψ 1), fun b hb ↦ ?_⟩
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I m b)
  have hrK : r ∈ K := Submodule.mem_comap.mpr (hr.symm ▸ LinearMap.mem_range_self p ⟨b, hb⟩)
  have hqb : q ⟨r, hrK⟩ = ⟨p ⟨b, hb⟩, LinearMap.mem_range_self p ⟨b, hb⟩⟩ := Subtype.ext hr
  rw [LinearMap.toSpanSingleton_apply, b.torsion_smul_eq hM (ψ 1) r hy₀ hr.symm, ← map_smul,
    smul_eq_mul, mul_one, hψ r hrK, LinearMap.comp_apply, hqb]
  simp [gbar]

/-- Over a Noetherian ring `R`, an injective `R`-module whose elements are each killed by a power
of `I` is injective over `AdicCompletion I R`. -/
@[stacks 08Z5]
theorem torsionModule_injective [Small.{w} R] [Module.Injective R M] :
    letI := torsionModule hM
    Module.Injective (_root_.AdicCompletion I R) M := by
  let := torsionModule hM
  exact (torsionModule_baer hM (Module.Baer.of_injective ‹_›)).injective

end Noetherian

end TauCeti.AdicCompletion
