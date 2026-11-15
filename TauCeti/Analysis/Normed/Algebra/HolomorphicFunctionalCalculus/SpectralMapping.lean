/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Composition
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Uniqueness
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

/-!
# Naturality, spectral mapping, and composition for the holomorphic functional calculus

This file establishes the structural theorems of the single-element holomorphic functional calculus
on a complex Banach algebra `A`:

* **Commutant preservation** (`Commute.holomorphicCalculusOn_right`,
  `Commute.holomorphicCalculus_right`): every element commuting with `a` commutes with `f(a)`.
* **Naturality** (`AlgHom.map_holomorphicCalculusOn`, `AlgHom.map_holomorphicCalculus`,
  `ContinuousAlgHom.map_holomorphicCalculus`): continuous unital `ℂ`-algebra homomorphisms commute
  with the holomorphic functional calculus.
* **Scalar and nonunital unitization evaluation** (`TauCeti.holomorphicCalculusOn_algebraMap`,
  `TauCeti.holomorphicCalculus_complex`, `TauCeti.fst_holomorphicCalculus_unitizationInrL`,
  `TauCeti.mem_range_unitizationInrL_holomorphicCalculus_iff`): on scalar elements `f(z · 1)` is
  `f(z) · 1`, and for `a` in a nonunital Banach algebra embedded in `WithLp 1 (Unitization ℂ A)`,
  `f(a)` lies in the nonunital algebra precisely when `f(0) = 0`.
* **Spectral mapping theorem** (`TauCeti.spectrum_holomorphicCalculus`,
  `TauCeti.spectrum_holomorphicCalculusOn`, `TauCeti.spectrum_holomorphicCalculus_ofFun`):
  `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`, i.e. `σ(f(a)) = f(σ(a))`, including in the
  zero algebra where both sides are empty.
* **Composition theorem** (`TauCeti.holomorphicCalculusOn_comp`,
  `TauCeti.holomorphicCalculus_comp`, `TauCeti.holomorphicCalculus_ofFun_comp`):
  `g(f(a)) = (g ∘ f)(a)` whenever `g` is holomorphic near `σ(f(a)) = f(σ(a))`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.7.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Theorems VII.4.8 and VII.4.11.
* W. Rudin, *Functional Analysis*, second edition, Theorems 10.28 and 10.29.
-/

public noncomputable section

open Complex Filter Function Set TopologicalSpace Topology
open scoped Real

/-! ### Commutant preservation -/

namespace Commute

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`. -/
theorem holomorphicCalculusOn_right {a b : A} (hb : Commute b a) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute b (holomorphicCalculusOn a U ha f) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw]
  have hf : ContinuousOn (extend f) (Cycle.trace Γ) :=
    (differentiableOn_extend f).continuousOn.mono fun _ hz => (Cycle.isIn_iff.mp hΓ hz).1
  have hres : Cycle.IsIn Γ (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz => spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  exact (hb.integral_smul_resolvent_right hf hres).smul_right _

/-- `holomorphicCalculusOn a U ha f` commutes with every element commuting with `a`. -/
theorem holomorphicCalculusOn_left {a b : A} (hb : Commute a b) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute (holomorphicCalculusOn a U ha f) b :=
  (hb.symm.holomorphicCalculusOn_right U ha f).symm

/-- Every element commuting with `a` commutes with `holomorphicCalculus a g`. -/
theorem holomorphicCalculus_right {a b : A} (hb : Commute b a)
    (g : holomorphicGerms (spectrum ℂ a)) : Commute b (holomorphicCalculus a g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  exact hb.holomorphicCalculusOn_right U ha f

/-- `holomorphicCalculus a g` commutes with every element commuting with `a`. -/
theorem holomorphicCalculus_left {a b : A} (hb : Commute a b)
    (g : holomorphicGerms (spectrum ℂ a)) : Commute (holomorphicCalculus a g) b :=
  (hb.symm.holomorphicCalculus_right g).symm

end Commute

/-! ### Naturality under continuous algebra homomorphisms -/

namespace AlgHom

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [FunLike F A B] [AlgHomClass F ℂ A B]

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn (φ : F) (hφ : Continuous φ) (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  have hsub := AlgHom.spectrum_apply_subset φ a
  have hΓ' : Γ.IsIn (U \ spectrum ℂ (φ a)) := Cycle.isIn_iff.mpr fun z hz =>
    ⟨(Cycle.isIn_iff.mp hΓ hz).1, fun hmem => (Cycle.isIn_iff.mp hΓ hz).2 (hsub hmem)⟩
  have hw' : ∀ z ∈ spectrum ℂ (φ a), Cycle.windingNumber z Γ = 1 := fun z hz => hw z (hsub hz)
  have hres : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz => spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  have hcont : ContinuousOn (fun z => extend f z • resolvent a z) (Cycle.trace Γ) :=
    ((differentiableOn_extend f).continuousOn.mono fun _ hz => (Cycle.isIn_iff.mp hΓ hz).1).smul
      (Cycle.continuousOn_resolvent hres)
  let L : A →L[ℂ] B := { toLinearMap := (AlgHom.ofClass φ : A →ₐ[ℂ] B).toLinearMap, cont := hφ }
  have hL : (L : A → B) = φ := rfl
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw,
    holomorphicCalculusOn_eq_integral (φ a) U (hsub.trans ha) f Γ hΓ' hn hw', ← hL, L.map_smul,
    ← Cycle.integral_comp_comm (fun _ => Cycle.intervalIntegrable_of_mem_support hcont) L]
  congr 1
  exact Cycle.integral_congr fun z hz => by
    rw [L.map_smul, hL, AlgHom.map_resolvent φ (Cycle.isIn_iff.mp hres hz)]

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculus`, restricting the
germ from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus (φ : F) (hφ : Continuous φ) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, restrict_toGerm, holomorphicCalculus_toGerm]
  exact AlgHom.map_holomorphicCalculusOn φ hφ a U ha f

/-- Naturality of `holomorphicCalculus` on ambient holomorphic representatives. -/
theorem map_holomorphicCalculus_ofFun (φ : F) (hφ : Continuous φ) (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) := by
  rw [AlgHom.map_holomorphicCalculus φ hφ, holomorphicGerms.restrict_ofFun]

end AlgHom

namespace ContinuousAlgHom

open TauCeti

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn (φ : A →A[ℂ] B) (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ.toAlgHom a).trans ha) f :=
  AlgHom.map_holomorphicCalculusOn φ.toAlgHom φ.continuous a U ha f

/-- Continuous algebra homomorphisms commute with `holomorphicCalculus`. -/
theorem map_holomorphicCalculus (φ : A →A[ℂ] B) (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ.toAlgHom a) g) :=
  AlgHom.map_holomorphicCalculus φ.toAlgHom φ.continuous a g

/-- Naturality of `holomorphicCalculus` on ambient holomorphic representatives for `A →A[ℂ] B`. -/
theorem map_holomorphicCalculus_ofFun (φ : A →A[ℂ] B) (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ.toAlgHom a))) :=
  AlgHom.map_holomorphicCalculus_ofFun φ.toAlgHom φ.continuous a f hf

end ContinuousAlgHom

/-! ### Scalar evaluation and nonunital unitization characterization -/

namespace WithLp

/-- The spectrum of `toLp 1 (a : Unitization 𝕜 A)` in the ℓ¹ unitization equals
`quasispectrum 𝕜 a`. -/
@[simp]
theorem spectrum_toLp_inr {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (a : A) :
    spectrum 𝕜 (toLp 1 (a : Unitization 𝕜 A)) = quasispectrum 𝕜 a := by
  rw [← AlgEquiv.spectrum_eq (unitizationAlgEquiv (𝕜 := 𝕜) (A := A) 𝕜),
    unitizationAlgEquiv_apply, ofLp_toLp, ← Unitization.quasispectrum_eq_spectrum_inr]

/-- The spectrum of `unitizationInrL 𝕜 A a` in the ℓ¹ unitization equals `quasispectrum 𝕜 a`. -/
theorem spectrum_unitizationInrL {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (a : A) :
    spectrum 𝕜 (unitizationInrL 𝕜 A a) = quasispectrum 𝕜 a := by
  rw [unitizationInrL_apply, spectrum_toLp_inr]

/-- Zero lies in the spectrum of `unitizationInrL 𝕜 A a` for every element `a` of a nonunital
normed algebra over a normed field `𝕜`. -/
theorem zero_mem_spectrum_unitizationInrL {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (a : A) :
    (0 : 𝕜) ∈ spectrum 𝕜 (unitizationInrL 𝕜 A a) := by
  rw [spectrum_unitizationInrL]
  exact quasispectrum.zero_mem 𝕜 a

end WithLp

namespace TauCeti

open Contour HolomorphicFunctions

section ScalarAndUnitization

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Factor `extend f z₀ - f(z)` as `(z₀ - z) * dslope (extend f) z₀ z` inside
`holomorphicFunctions U`. -/
private theorem add_sub_mul_dslope_eq_algebraMap {U : Opens ℂ} (f : holomorphicFunctions U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    f + of U (fun z => (Polynomial.C z₀ - Polynomial.X).eval z)
        (Polynomial.C z₀ - Polynomial.X).differentiable.differentiableOn *
      of U (dslope (extend f) z₀)
        ((Complex.differentiableOn_dslope (U.isOpen.mem_nhds hz₀)).mpr
          (differentiableOn_extend f)) =
      algebraMap ℂ (holomorphicFunctions U) (extend f z₀) := by
  apply Subtype.ext
  ext z
  rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one, of_apply, of_apply, ← extend_apply f z]
  have hd := sub_smul_dslope (extend f) z₀ z
  rw [smul_eq_mul] at hd
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  calc extend f z + (z₀ - (z : ℂ)) * dslope (extend f) z₀ z
      = extend f z - ((z : ℂ) - z₀) * dslope (extend f) z₀ z := by ring
    _ = extend f z - (extend f z - extend f z₀) := by rw [hd]
    _ = extend f z₀ := by ring

/-- Evaluating `holomorphicCalculusOn` at a scalar multiple `algebraMap ℂ A z` gives
`algebraMap ℂ A (extend f z)`, without assuming `Nontrivial A` or `NormOneClass A`. -/
@[simp]
theorem holomorphicCalculusOn_algebraMap (z : ℂ) (U : Opens ℂ)
    (hz : spectrum ℂ (algebraMap ℂ A z) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (algebraMap ℂ A z) U hz f = algebraMap ℂ A (extend f z) := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact Subsingleton.elim _ _
  · have hz_mem : z ∈ spectrum ℂ (algebraMap ℂ A z) :=
      (spectrum.scalar_eq (A := A) z).symm ▸ mem_singleton z
    have h := congrArg (holomorphicCalculusOn (algebraMap ℂ A z) U hz)
      (add_sub_mul_dslope_eq_algebraMap f (hz hz_mem))
    simpa only [map_add, map_mul, holomorphicCalculusOn_polynomial, AlgHom.commutes, map_sub,
      Polynomial.aeval_C, Polynomial.aeval_X, sub_self, zero_mul, add_zero] using h

/-- On `ℂ`, `holomorphicCalculusOn` at `z` is evaluation at `z`. -/
@[simp]
theorem holomorphicCalculusOn_complex (z : ℂ) (U : Opens ℂ) (hz : spectrum ℂ z ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn z U hz f = extend f z := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    holomorphicCalculusOn_algebraMap (A := ℂ) z U hz f

/-- On `ℂ`, `holomorphicCalculus` at `z` agrees with germ evaluation at `z`. -/
@[simp]
theorem holomorphicCalculus_complex (z : ℂ) (g : holomorphicGerms (spectrum ℂ z)) :
    holomorphicCalculus z g =
      holomorphicGerms.eval z
        (AlgHom.id_apply (R := ℂ) z ▸ AlgHom.apply_mem_spectrum (AlgHom.id ℂ ℂ) z) g := by
  obtain ⟨U, hz, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  have hz_mem : z ∈ spectrum ℂ z :=
    AlgHom.id_apply (R := ℂ) z ▸ AlgHom.apply_mem_spectrum (AlgHom.id ℂ ℂ) z
  rw [holomorphicCalculus_toGerm, holomorphicCalculusOn_complex, eval_toGerm,
    extend_apply f ⟨z, hz hz_mem⟩]

/-- Evaluating `holomorphicCalculus` of an ambient representative at `algebraMap ℂ A z` gives
`algebraMap ℂ A (f z)`, without assuming `Nontrivial A` or `NormOneClass A`. -/
@[simp]
theorem holomorphicCalculus_algebraMap_ofFun (z : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ (algebraMap ℂ A z))) :
    holomorphicCalculus (algebraMap ℂ A z) (holomorphicGerms.ofFun f hf) =
      algebraMap ℂ A (f z) := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact Subsingleton.elim _ _
  · let U : Opens ℂ := ⟨{w | AnalyticAt ℂ f w}, isOpen_analyticAt ℂ f⟩
    have hzU : spectrum ℂ (algebraMap ℂ A z) ⊆ U := hf
    have hdiff : DifferentiableOn ℂ f U := fun w hw => hw.differentiableAt.differentiableWithinAt
    have hz_mem : z ∈ spectrum ℂ (algebraMap ℂ A z) :=
      (spectrum.scalar_eq (A := A) z).symm ▸ mem_singleton z
    rw [← toGerm_of (U := U) hzU f hdiff, holomorphicCalculus_toGerm,
      holomorphicCalculusOn_algebraMap, extend_apply _ ⟨z, hzU hz_mem⟩, of_apply]

end ScalarAndUnitization

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A]

/-- For an element `a` of a nonunital complex Banach algebra embedded in
`WithLp 1 (Unitization ℂ A)`, the scalar part of `holomorphicCalculus` at `unitizationInrL ℂ A a`
is `g(0)`. -/
@[simp]
theorem fst_holomorphicCalculus_unitizationInrL (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    (WithLp.ofLp (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)).fst =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
  let φ : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] ℂ :=
    (Unitization.fstHom ℂ A).comp (WithLp.unitizationAlgEquiv ℂ).toAlgHom
  have hφ : Continuous φ := AddMonoidHomClass.continuous_of_bound φ 1 fun u => by
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, WithLp.unitizationAlgEquiv_apply,
      Unitization.fstHom_apply, WithLp.unitization_norm_def, one_mul]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hφ_inr : φ (WithLp.unitizationInrL ℂ A a) = 0 := by
    simp [φ, WithLp.unitizationInrL_apply]
  have hnat := AlgHom.map_holomorphicCalculus φ hφ (WithLp.unitizationInrL ℂ A a) g
  have heval : holomorphicCalculus (φ (WithLp.unitizationInrL ℂ A a))
      (holomorphicGerms.restrict
        (AlgHom.spectrum_apply_subset φ (WithLp.unitizationInrL ℂ A a)) g) =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
    obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
    rw [restrict_toGerm, holomorphicCalculus_toGerm, eval_toGerm]
    have hsub := (AlgHom.spectrum_apply_subset φ (WithLp.unitizationInrL ℂ A a)).trans ha
    rw [holomorphicCalculusOn_complex _ U hsub f, hφ_inr,
      extend_apply f ⟨0, ha (WithLp.zero_mem_spectrum_unitizationInrL a)⟩]
  exact hnat.trans heval

/-- For `a` in a nonunital complex Banach algebra, `holomorphicCalculus` at `unitizationInrL ℂ A a`
lands in `Set.range (WithLp.unitizationInrL ℂ A)` if and only if `g(0) = 0`. -/
theorem mem_range_unitizationInrL_holomorphicCalculus_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0 := by
  rw [← fst_holomorphicCalculus_unitizationInrL a g]
  set u := holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g
  constructor
  · rintro ⟨b, hb⟩
    rw [← hb, WithLp.unitizationInrL_apply, WithLp.ofLp_toLp, Unitization.fst_inr]
  · intro hfst
    refine ⟨(WithLp.ofLp u).snd, ?_⟩
    rw [WithLp.unitizationInrL_apply]
    simpa only [hfst, zero_smul, zero_add] using (WithLp.unitization_eq_fst_smul_one_add_inr u).symm

end NonUnital

/-! ### Spectral mapping theorem -/

section SpectralMapping

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Spectral mapping theorem for holomorphic germs.** For any `a : A` and
`g : holomorphicGerms (spectrum ℂ a)`, `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`. -/
@[simp]
theorem spectrum_holomorphicCalculus (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g := by
  apply Subset.antisymm (AlgHom.spectrum_apply_subset (holomorphicCalculus a) g)
  intro c hc
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  obtain ⟨z₀, hz₀, hc_eq⟩ := (holomorphicGerms.spectrum_eq (toGerm ha f)) ▸ hc
  rw [eval_toGerm, ← extend_apply f ⟨z₀, ha hz₀⟩] at hc_eq
  let hU : holomorphicFunctions U := of U (dslope (extend f) z₀)
    ((Complex.differentiableOn_dslope (U.isOpen.mem_nhds (ha hz₀))).mpr (differentiableOn_extend f))
  have hfac := congrArg (holomorphicCalculusOn a U ha)
    (add_sub_mul_dslope_eq_algebraMap f (ha hz₀))
  rw [hc_eq, map_add, map_mul, holomorphicCalculusOn_polynomial, AlgHom.commutes,
    ← holomorphicCalculus_toGerm, map_sub, Polynomial.aeval_C, Polynomial.aeval_X] at hfac
  have hsub : algebraMap ℂ A c - holomorphicCalculus a (toGerm ha f) =
      (algebraMap ℂ A z₀ - a) * holomorphicCalculusOn a U ha hU :=
    sub_eq_of_eq_add' hfac.symm
  have hcomm : Commute (algebraMap ℂ A z₀ - a) (holomorphicCalculusOn a U ha hU) :=
    (Algebra.commute_algebraMap_left z₀ _).sub_left
      ((Commute.refl a).holomorphicCalculusOn_right U ha hU)
  rw [spectrum.mem_iff]
  exact fun hu => hz₀ (hcomm.isUnit_mul_iff.mp (hsub ▸ hu)).1

/-- **Spectral mapping theorem on an open domain.** For `f : holomorphicFunctions U` with
`spectrum ℂ a ⊆ U`, `spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm, spectrum_holomorphicCalculus, holomorphicGerms.spectrum_eq]
  ext c
  simp only [mem_ofPred, mem_image]
  refine exists_congr fun z => ⟨fun ⟨hz, h⟩ => ⟨hz, ?_⟩, fun ⟨hz, h⟩ => ⟨hz, ?_⟩⟩
  · rwa [eval_toGerm, ← extend_apply f ⟨z, ha hz⟩] at h
  · rwa [eval_toGerm, ← extend_apply f ⟨z, ha hz⟩]

/-- **Spectral mapping theorem for ambient holomorphic functions.** -/
theorem spectrum_holomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) = f '' spectrum ℂ a := by
  rw [spectrum_holomorphicCalculus, holomorphicGerms.spectrum_ofFun]

end SpectralMapping

/-! ### Composition theorem -/

section Composition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Composing a Cauchy kernel `(w - ·)⁻¹` with `f` evaluates under `holomorphicCalculusOn` to
`resolvent (holomorphicCalculusOn a U ha f) w` whenever `w ∉ extend f '' spectrum ℂ a`. -/
private theorem holomorphicCalculusOn_comp_cauchyKernel (a : A) {U : Opens ℂ}
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) {w : ℂ}
    (hw : w ∉ extend f '' spectrum ℂ a) :
    let Vw : Opens ℂ := ⟨{w}ᶜ, isOpen_compl_singleton⟩
    let W : Opens ℂ := preimageOpen f Vw
    have haW : spectrum ℂ a ⊆ W :=
      subset_preimageOpen ha fun z hz hzw => hw ⟨z, hz, mem_singleton_iff.mp hzw⟩
    holomorphicCalculusOn a W haW
      (HolomorphicFunctions.comp (cauchyKernel Vw w (not_not_intro (mem_singleton w))) f
        (preimageOpen_le f Vw) (mapsTo_extend_preimageOpen f Vw)) =
      resolvent (holomorphicCalculusOn a U ha f) w := by
  intro Vw W haW
  let hwVw : w ∉ (Vw : Set ℂ) := not_not_intro (mem_singleton w)
  let k := HolomorphicFunctions.comp (cauchyKernel Vw w hwVw) f
    (preimageOpen_le f Vw) (mapsTo_extend_preimageOpen f Vw)
  let d : holomorphicFunctions W :=
    algebraMap ℂ (holomorphicFunctions W) w +
      (-1 : ℂ) • HolomorphicFunctions.restrict (preimageOpen_le f Vw) f
  have hdk : d * k = 1 := by
    apply Subtype.ext
    ext z
    have hzw : extend f z ≠ w :=
      mem_compl_singleton_iff.mp (mapsTo_extend_preimageOpen f Vw z.property)
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, ContinuousMap.mul_apply, ContinuousMap.one_apply,
      HolomorphicFunctions.comp_apply, extend_apply (cauchyKernel Vw w hwVw) ⟨extend f z, hzw⟩,
      cauchyKernel_apply]
    dsimp only [d]
    rw [Subalgebra.coe_add, Subalgebra.coe_algebraMap, SetLike.val_smul, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, neg_one_smul,
      HolomorphicFunctions.restrict_apply, ← sub_eq_add_neg,
      ← extend_apply f ⟨z, (preimageOpen_le f Vw) z.property⟩]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr hzw.symm)
  have hkd : k * d = 1 := by rw [mul_comm, hdk]
  have hd_calc : holomorphicCalculusOn a W haW d =
      algebraMap ℂ A w - holomorphicCalculusOn a U ha f := by
    simp only [d, map_add, AlgHom.commutes, map_smul, neg_one_smul, holomorphicCalculusOn_restrict,
      sub_eq_add_neg]
  let u : Aˣ :=
    { val := algebraMap ℂ A w - holomorphicCalculusOn a U ha f
      inv := holomorphicCalculusOn a W haW k
      val_inv := by rw [← hd_calc, ← map_mul, hdk, map_one]
      inv_val := by rw [← hd_calc, ← map_mul, hkd, map_one] }
  exact (Ring.inverse_unit u).symm

/-- Contour integral representation of `resolvent (holomorphicCalculusOn a U ha f) w` over a cycle
`Γ_U` in `W \ spectrum ℂ a` whose image under `extend f` avoids `w`. -/
private theorem resolvent_holomorphicCalculusOn_eq_integral (a : A) {U W : Opens ℂ}
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) (hWU : W ≤ U) (haW : spectrum ℂ a ⊆ W)
    {Γ_U : Cycle} (hΓ_U : Γ_U.IsIn (W \ spectrum ℂ a)) (hn_U : Γ_U.IsNullHomologous W)
    (hw_U : ∀ z ∈ spectrum ℂ a, Cycle.windingNumber z Γ_U = 1) {w : ℂ}
    (hwW : ∀ z ∈ (W : Set ℂ), extend f z ≠ w) :
    resolvent (holomorphicCalculusOn a U ha f) w =
      (2 * π * I)⁻¹ • Cycle.integral (fun z => (w - extend f z)⁻¹ • resolvent a z) Γ_U := by
  let Vw : Opens ℂ := ⟨{w}ᶜ, isOpen_compl_singleton⟩
  have hw : w ∉ extend f '' spectrum ℂ a := by
    rintro ⟨z, hz, rfl⟩
    exact hwW z (haW hz) rfl
  have hWle : W ≤ preimageOpen f Vw := fun z hz =>
    mem_preimageOpen.mpr ⟨hWU hz, mem_compl_singleton_iff.mpr (hwW z hz)⟩
  rw [← holomorphicCalculusOn_comp_cauchyKernel a ha f hw,
    ← holomorphicCalculusOn_restrict a haW hWle,
    holomorphicCalculusOn_eq_integral a W haW _ Γ_U hΓ_U hn_U hw_U]
  congr 1
  refine Cycle.integral_congr fun z hz => ?_
  have hzW : z ∈ W := (Cycle.isIn_iff.mp hΓ_U hz).1
  rw [extend_apply _ ⟨z, hzW⟩, HolomorphicFunctions.restrict_apply,
    HolomorphicFunctions.comp_apply,
    extend_apply _ ⟨extend f z, mem_compl_singleton_iff.mpr (hwW z hzW)⟩, cauchyKernel_apply]

/-- Joint continuity on `trace Γ_V ×ˢ trace Γ_U` of the double-cycle integrand for composition. -/
private theorem continuousOn_comp_integrand (a : A) {U V : Opens ℂ}
    (f : holomorphicFunctions U) (g : holomorphicFunctions V) {Γ_V Γ_U : Cycle}
    (hΓ_VV : Γ_V.IsIn V) (hΓ_UU : Γ_U.IsIn U) (hres_U : Γ_U.IsIn (resolventSet ℂ a))
    (hdisj : ∀ z ∈ Cycle.trace Γ_U, extend f z ∉ Cycle.trace Γ_V) :
    ContinuousOn (uncurry fun w z => (extend g w / (w - extend f z)) • resolvent a z)
      (Cycle.trace Γ_V ×ˢ Cycle.trace Γ_U) := by
  have hg_c : ContinuousOn (fun p : ℂ × ℂ => extend g p.1)
      (Cycle.trace Γ_V ×ˢ Cycle.trace Γ_U) :=
    ((differentiableOn_extend g).continuousOn.mono (Cycle.isIn_iff.mp hΓ_VV)).comp
      continuousOn_fst fun _ hp => hp.1
  have hf_c : ContinuousOn (fun p : ℂ × ℂ => extend f p.2)
      (Cycle.trace Γ_V ×ˢ Cycle.trace Γ_U) :=
    ((differentiableOn_extend f).continuousOn.mono (Cycle.isIn_iff.mp hΓ_UU)).comp
      continuousOn_snd fun _ hp => hp.2
  have hsub_ne : ∀ p ∈ Cycle.trace Γ_V ×ˢ Cycle.trace Γ_U, p.1 - extend f p.2 ≠ 0 :=
    fun p hp h0 => hdisj p.2 hp.2 (sub_eq_zero.mp h0 ▸ hp.1)
  exact (hg_c.div (continuousOn_fst.sub hf_c) hsub_ne).smul
    ((Cycle.continuousOn_resolvent hres_U).comp continuousOn_snd fun _ hp => hp.2)

/-- **Composition theorem on open domains.** If `f : holomorphicFunctions U` maps `U' ≤ U`
(containing `spectrum ℂ a`) into `V`, and `g : holomorphicFunctions V`, then evaluating `g` at
`holomorphicCalculusOn a U ha f` agrees with evaluating `HolomorphicFunctions.comp g f hU' hmaps`
at `a`. -/
theorem holomorphicCalculusOn_comp (a : A) {U U' V : Opens ℂ} (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) (hfV : extend f '' spectrum ℂ a ⊆ V) (g : holomorphicFunctions V)
    (hU' : U' ≤ U) (ha' : spectrum ℂ a ⊆ U') (hmaps : MapsTo (extend f) U' V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U ha f) V
      ((spectrum_holomorphicCalculusOn a U ha f).subset.trans hfV) g =
      holomorphicCalculusOn a U' ha' (HolomorphicFunctions.comp g f hU' hmaps) := by
  set b := holomorphicCalculusOn a U ha f
  have hb_spec : spectrum ℂ b = extend f '' spectrum ℂ a := spectrum_holomorphicCalculusOn a U ha f
  have hbV : spectrum ℂ b ⊆ V := hb_spec.subset.trans hfV
  obtain ⟨Γ_V, hΓ_V, hn_V, hw_V⟩ :=
    (spectrum.isCompact b).exists_cycle_windingNumber_eq_one V.isOpen hbV
  let W : Opens ℂ :=
    preimageOpen (HolomorphicFunctions.restrict hU' f) (V ⊓ Cycle.windingOneOpen Γ_V)
  have hWU' : W ≤ U' := preimageOpen_le _ _
  have hf_eq : ∀ z ∈ (U' : Set ℂ),
      extend (HolomorphicFunctions.restrict hU' f) z = extend f z := fun z hz => by
    rw [extend_apply _ ⟨z, hz⟩, HolomorphicFunctions.restrict_apply, extend_apply f ⟨z, hU' hz⟩]
  have haW : spectrum ℂ a ⊆ W := fun z hz => by
    have hmem : extend f z ∈ spectrum ℂ b := hb_spec.symm ▸ ⟨z, hz, rfl⟩
    refine mem_preimageOpen.mpr ⟨ha' hz, ?_⟩
    rw [hf_eq z (ha' hz)]
    exact ⟨hbV hmem, Cycle.mem_windingOneOpen.mpr
      ⟨fun ht => (Cycle.isIn_iff.mp hΓ_V ht).2 hmem, hw_V _ hmem⟩⟩
  obtain ⟨Γ_U, hΓ_U, hn_U, hw_U⟩ :=
    (spectrum.isCompact a).exists_cycle_windingNumber_eq_one W.isOpen haW
  have hW_wind : ∀ z ∈ (W : Set ℂ),
      extend f z ∉ Cycle.trace Γ_V ∧ Cycle.windingNumber (extend f z) Γ_V = 1 := fun z hz => by
    obtain ⟨hzU', hzVW⟩ := mem_preimageOpen.mp hz
    rw [hf_eq z hzU'] at hzVW
    exact Cycle.mem_windingOneOpen.mp hzVW.2
  have hΓ_VV : Γ_V.IsIn V := Cycle.isIn_iff.mpr fun _ hw => (Cycle.isIn_iff.mp hΓ_V hw).1
  have hF_cont := continuousOn_comp_integrand a f g hΓ_VV
    (Cycle.isIn_iff.mpr fun _ hz => hU' (hWU' (Cycle.isIn_iff.mp hΓ_U hz).1))
    (Cycle.isIn_iff.mpr fun _ hz => spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ_U hz).2)
    (fun z hz => (hW_wind z (Cycle.isIn_iff.mp hΓ_U hz).1).1)
  rw [holomorphicCalculusOn_eq_integral b V hbV g Γ_V hΓ_V hn_V hw_V,
    ← holomorphicCalculusOn_restrict a haW hWU',
    holomorphicCalculusOn_eq_integral a W haW _ Γ_U hΓ_U hn_U hw_U]
  have hstep₁ : Cycle.integral (fun w => extend g w • resolvent b w) Γ_V =
      (2 * π * I)⁻¹ • Cycle.integral (fun w =>
        Cycle.integral (fun z => (extend g w / (w - extend f z)) • resolvent a z) Γ_U) Γ_V := by
    rw [← Cycle.integral_smul]
    refine Cycle.integral_congr fun w hw => ?_
    rw [resolvent_holomorphicCalculusOn_eq_integral a ha f (hWU'.trans hU') haW hΓ_U hn_U hw_U
      (fun z hz hzw => (hW_wind z hz).1 (hzw ▸ hw)), smul_comm, ← Cycle.integral_smul]
    exact congrArg ((2 * π * I)⁻¹ • ·) (Cycle.integral_congr fun _ _ => by
      rw [smul_smul, div_eq_mul_inv])
  rw [hstep₁, Cycle.integral_integral_swap hF_cont, smul_smul]
  have hstep₂ : Cycle.integral (fun z =>
      Cycle.integral (fun w => (extend g w / (w - extend f z)) • resolvent a z) Γ_V) Γ_U =
      (2 * π * I) • Cycle.integral
        (fun z => extend (HolomorphicFunctions.restrict hWU'
          (HolomorphicFunctions.comp g f hU' hmaps)) z • resolvent a z) Γ_U := by
    rw [← Cycle.integral_smul]
    refine Cycle.integral_congr fun z hz => ?_
    have hzW : z ∈ W := (Cycle.isIn_iff.mp hΓ_U hz).1
    obtain ⟨hoff, hwind⟩ := hW_wind z hzW
    rw [Cycle.integral_smul_const,
      Cycle.cauchyIntegralFormula_nullHomologous V.isOpen (differentiableOn_extend g)
        hΓ_VV hn_V hoff,
      hwind, mul_one, mul_smul, extend_apply _ ⟨z, hzW⟩, HolomorphicFunctions.restrict_apply,
      HolomorphicFunctions.comp_apply]
  rw [hstep₂, ← mul_smul, mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, mul_one]

/-- **Composition theorem for the holomorphic germ functional calculus.** For any
`f : holomorphicGerms (spectrum ℂ a)` and
`g : holomorphicGerms (spectrum ℂ (holomorphicCalculus a f))`, evaluating `g` at
`holomorphicCalculus a f` agrees with evaluating the composite germ at `a`. -/
@[simp]
theorem holomorphicCalculus_comp (a : A) (f : holomorphicGerms (spectrum ℂ a))
    (g : holomorphicGerms (spectrum ℂ (holomorphicCalculus a f))) :
    holomorphicCalculus (holomorphicCalculus a f) g =
      holomorphicCalculus a
        (holomorphicGerms.comp g f (spectrum_holomorphicCalculus a f).symm.subset) := by
  obtain ⟨U, ha, fU, rfl⟩ := holomorphicGerms.exists_toGerm_eq f
  obtain ⟨V, hb, gV, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  have hfV : extend fU '' spectrum ℂ a ⊆ V := by
    rwa [holomorphicCalculus_toGerm, spectrum_holomorphicCalculusOn] at hb
  let U' : Opens ℂ := preimageOpen fU V
  have ha' : spectrum ℂ a ⊆ U' := subset_preimageOpen ha (mapsTo_iff_image_subset.mpr hfV)
  have hb' : spectrum ℂ (holomorphicCalculusOn a U ha fU) ⊆ V :=
    (spectrum_holomorphicCalculusOn a U ha fU).subset.trans hfV
  have hcongr : ∀ {x y : A} (_ : x = y) (hx : spectrum ℂ x ⊆ V) (hy : spectrum ℂ y ⊆ V),
      holomorphicCalculusOn x V hx gV = holomorphicCalculusOn y V hy gV := by
    rintro x _ rfl _ _
    rfl
  rw [holomorphicCalculus_toGerm,
    hcongr (holomorphicCalculus_toGerm a U ha fU) hb hb',
    holomorphicGerms.comp_toGerm ha hb gV fU (preimageOpen_le fU V) ha'
      (mapsTo_extend_preimageOpen fU V)
      (spectrum_holomorphicCalculus a (toGerm ha fU)).symm.subset,
    holomorphicCalculus_toGerm]
  exact holomorphicCalculusOn_comp a ha fU hfV gV (preimageOpen_le fU V) ha'
    (mapsTo_extend_preimageOpen fU V)

/-- **Composition theorem for ambient holomorphic representatives.** -/
theorem holomorphicCalculus_ofFun_comp (a : A) {f g : ℂ → ℂ} {t : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (ht : f '' spectrum ℂ a ⊆ t)
    (hg : AnalyticOnNhd ℂ g t) :
    holomorphicCalculus (holomorphicCalculus a (holomorphicGerms.ofFun f hf))
      (holomorphicGerms.ofFun g
        (hg.mono ((spectrum_holomorphicCalculus_ofFun a f hf).subset.trans ht))) =
      holomorphicCalculus a
        (holomorphicGerms.ofFun (g ∘ f) (hg.comp hf (mapsTo_iff_image_subset.mpr ht))) := by
  rw [holomorphicCalculus_comp, holomorphicGerms.comp_ofFun]

end Composition

end TauCeti
