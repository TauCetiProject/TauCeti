/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Composition
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic
import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Uniqueness

/-!
# Naturality, spectral mapping, and composition for the holomorphic functional calculus

This file establishes the structural theorems of the single-element holomorphic functional calculus
on a complex Banach algebra `A`:

* **Commutant preservation** (`Commute.holomorphicCalculusOn_right`,
  `Commute.holomorphicCalculus_right`): every element commuting with `a` commutes with `f(a)`.
* **Naturality** (`TauCeti.map_holomorphicCalculusOn`, `TauCeti.map_holomorphicCalculus`,
  `AlgHom.map_holomorphicCalculus`, `ContinuousAlgHom.map_holomorphicCalculus`): continuous unital
  `ℂ`-algebra homomorphisms commute with the holomorphic functional calculus.
* **Scalar and nonunital unitization evaluation** (`TauCeti.holomorphicCalculusOn_algebraMap`,
  `TauCeti.holomorphicCalculus_algebraMap`, `TauCeti.holomorphicCalculus_complex`,
  `TauCeti.fst_holomorphicCalculus_toLp_inr`, `TauCeti.fst_holomorphicCalculus_unitizationInrL`,
  `TauCeti.holomorphicCalculus_unitizationInrL_mem_range_iff`): on scalar elements `f(z · 1)` is
  `f(z) · 1`, and for `a` in a nonunital Banach algebra embedded in `WithLp 1 (Unitization ℂ A)`,
  `f(a)` lies in the nonunital algebra precisely when `f(0) = 0`.
* **Spectral mapping theorem** (`TauCeti.spectrum_holomorphicCalculus`,
  `TauCeti.spectrum_holomorphicCalculusOn`, `TauCeti.spectrum_holomorphicCalculus_ofFun`):
  `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`, i.e. `σ(f(a)) = f(σ(a))`, including in the
  zero algebra where both sides are empty.
* **Composition theorem** (`TauCeti.holomorphicCalculus_comp`,
  `TauCeti.holomorphicCalculusOn_comp`, `TauCeti.holomorphicCalculus_ofFun_comp`):
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

namespace TauCeti

open Contour HolomorphicFunctions

section Naturality

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
  let L : A →L[ℂ] B :=
    ⟨{ toFun := φ, map_add' := map_add φ, map_smul' := map_smul φ }, hφ⟩
  have hL : (L : A → B) = φ := by
    simp only [L, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw,
    holomorphicCalculusOn_eq_integral (φ a) U (hsub.trans ha) f Γ hΓ' hn hw', ← hL, L.map_smul,
    ← Cycle.integral_comp_comm (fun _ => Cycle.intervalIntegrable_of_mem_support hcont) L]
  congr 1
  exact Cycle.integral_congr fun z hz => by
    rw [L.map_smul, hL, TauCeti.map_resolvent φ (Cycle.isIn_iff.mp hres hz)]

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculus`, restricting the
germ from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus (φ : F) (hφ : Continuous φ) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, restrict_toGerm, holomorphicCalculus_toGerm]
  exact map_holomorphicCalculusOn φ hφ a U ha f

/-- Naturality of `holomorphicCalculus` on ambient holomorphic representatives. -/
theorem map_holomorphicCalculus_ofFun (φ : F) (hφ : Continuous φ) (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) := by
  rw [map_holomorphicCalculus φ hφ, holomorphicGerms.restrict_ofFun]

end Naturality

end TauCeti

namespace AlgHom

open TauCeti

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn (φ : A →ₐ[ℂ] B) (hφ : Continuous φ) (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  TauCeti.map_holomorphicCalculusOn φ hφ a U ha f

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculus`. -/
theorem map_holomorphicCalculus (φ : A →ₐ[ℂ] B) (hφ : Continuous φ) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  TauCeti.map_holomorphicCalculus φ hφ a g

/-- Naturality of `holomorphicCalculus` on ambient holomorphic representatives for `A →ₐ[ℂ] B`. -/
theorem map_holomorphicCalculus_ofFun (φ : A →ₐ[ℂ] B) (hφ : Continuous φ) (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) :=
  TauCeti.map_holomorphicCalculus_ofFun φ hφ a f hf

end AlgHom

namespace ContinuousAlgHom

open TauCeti

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn (φ : A →A[ℂ] B) (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  TauCeti.map_holomorphicCalculusOn φ φ.continuous a U ha f

/-- Continuous algebra homomorphisms commute with `holomorphicCalculus`. -/
theorem map_holomorphicCalculus (φ : A →A[ℂ] B) (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  TauCeti.map_holomorphicCalculus φ φ.continuous a g

/-- Naturality of `holomorphicCalculus` on ambient holomorphic representatives for `A →A[ℂ] B`. -/
theorem map_holomorphicCalculus_ofFun (φ : A →A[ℂ] B) (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) :=
  TauCeti.map_holomorphicCalculus_ofFun φ φ.continuous a f hf

end ContinuousAlgHom

/-! ### Scalar evaluation and nonunital unitization characterization -/

namespace TauCeti

open Contour HolomorphicFunctions

section ScalarAndUnitization

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

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
      (algebraMap_sub_id_mul_of_dslope f (hz hz_mem))
    simp only [map_mul, map_sub (holomorphicCalculusOn (algebraMap ℂ A z) U hz),
      AlgHom.commutes, holomorphicCalculusOn_id, sub_self, zero_mul] at h
    exact (sub_eq_zero.mp h.symm).symm

/-- On `ℂ`, `holomorphicCalculusOn` at `z` is evaluation at `z`. -/
@[simp]
theorem holomorphicCalculusOn_complex (z : ℂ) (U : Opens ℂ) (hz : spectrum ℂ z ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn z U hz f = extend f z := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    holomorphicCalculusOn_algebraMap (A := ℂ) z U hz f

/-- Evaluating `holomorphicCalculus` at a scalar multiple `algebraMap ℂ A z` in a nontrivial
complex Banach algebra agrees with `algebraMap ℂ A` applied to germ evaluation at `z`. -/
@[simp]
theorem holomorphicCalculus_algebraMap [Nontrivial A] (z : ℂ)
    (g : holomorphicGerms (spectrum ℂ (algebraMap ℂ A z))) :
    holomorphicCalculus (algebraMap ℂ A z) g =
      algebraMap ℂ A
        (holomorphicGerms.eval z
          ((spectrum.scalar_eq (A := A) z).symm ▸ mem_singleton z) g) := by
  obtain ⟨U, hz, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  have hz_mem : z ∈ spectrum ℂ (algebraMap ℂ A z) :=
    (spectrum.scalar_eq (A := A) z).symm ▸ mem_singleton z
  rw [holomorphicCalculus_toGerm, holomorphicCalculusOn_algebraMap, eval_toGerm,
    extend_apply f ⟨z, hz hz_mem⟩]

/-- On `ℂ`, `holomorphicCalculus` at `z` agrees with germ evaluation at `z`. -/
@[simp]
theorem holomorphicCalculus_complex (z : ℂ) (g : holomorphicGerms (spectrum ℂ z)) :
    holomorphicCalculus z g =
      holomorphicGerms.eval z
        ((spectrum.scalar_eq (A := ℂ) z).symm ▸ mem_singleton z) g := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    holomorphicCalculus_algebraMap (A := ℂ) z g

/-- Evaluating `holomorphicCalculus` of an ambient representative at `algebraMap ℂ A z` gives
`algebraMap ℂ A (f z)`, without assuming `Nontrivial A` or `NormOneClass A`. -/
@[simp]
theorem holomorphicCalculus_algebraMap_ofFun (z : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ (algebraMap ℂ A z))) :
    holomorphicCalculus (algebraMap ℂ A z) (holomorphicGerms.ofFun f hf) =
      algebraMap ℂ A (f z) := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact Subsingleton.elim _ _
  · rw [holomorphicCalculus_algebraMap, holomorphicGerms.eval_ofFun]

end ScalarAndUnitization

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A]

/-- For an element `a` of a nonunital complex Banach algebra embedded in
`WithLp 1 (Unitization ℂ A)`, the scalar part of `holomorphicCalculus` at
`WithLp.toLp 1 (a : Unitization ℂ A)` is `g(0)`. -/
@[simp]
theorem fst_holomorphicCalculus_toLp_inr (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))) :
    (WithLp.ofLp (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g)).fst =
      holomorphicGerms.eval 0 (zero_mem_spectrum_unitization_toLp_inr a) g := by
  let φ : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] ℂ :=
    (Unitization.fstHom ℂ A).comp (WithLp.unitizationAlgEquiv ℂ).toAlgHom
  have hφ_apply (u : WithLp 1 (Unitization ℂ A)) : φ u = (WithLp.ofLp u).fst := by
    simp [φ]
  have hφ_inr : φ (WithLp.toLp 1 (a : Unitization ℂ A)) = 0 := by
    rw [hφ_apply, WithLp.ofLp_toLp, Unitization.fst_inr]
  have hnat :=
    AlgHom.map_holomorphicCalculus φ (map_continuous φ) (WithLp.toLp 1 (a : Unitization ℂ A)) g
  have heval : holomorphicCalculus (φ (WithLp.toLp 1 (a : Unitization ℂ A)))
      (holomorphicGerms.restrict
        (AlgHom.spectrum_apply_subset φ (WithLp.toLp 1 (a : Unitization ℂ A))) g) =
      holomorphicGerms.eval 0 (zero_mem_spectrum_unitization_toLp_inr a) g := by
    obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
    rw [restrict_toGerm, holomorphicCalculus_toGerm, eval_toGerm]
    have hsub := (AlgHom.spectrum_apply_subset φ (WithLp.toLp 1 (a : Unitization ℂ A))).trans ha
    rw [holomorphicCalculusOn_complex _ U hsub f, hφ_inr,
      extend_apply f ⟨0, ha (zero_mem_spectrum_unitization_toLp_inr a)⟩]
  rw [← hφ_apply]
  exact hnat.trans heval

/-- For an element `a` of a nonunital complex Banach algebra embedded in
`WithLp 1 (Unitization ℂ A)`, the scalar part of `holomorphicCalculus` at `unitizationInrL ℂ A a`
is `g(0)`. -/
@[simp]
theorem fst_holomorphicCalculus_unitizationInrL (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    (WithLp.ofLp (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)).fst =
      holomorphicGerms.eval 0 (zero_mem_spectrum_unitizationInrL a) g := by
  have key : ∀ (x : WithLp 1 (Unitization ℂ A)) (_ : x = WithLp.toLp 1 (a : Unitization ℂ A))
      (h0 : (0 : ℂ) ∈ spectrum ℂ x) (g : holomorphicGerms (spectrum ℂ x)),
      (WithLp.ofLp (holomorphicCalculus x g)).fst = holomorphicGerms.eval 0 h0 g := by
    rintro _ rfl _ g
    exact fst_holomorphicCalculus_toLp_inr a g
  exact key _ (WithLp.unitizationInrL_apply ℂ A a) _ g

/-- For `a` in a nonunital complex Banach algebra, `holomorphicCalculus` at `unitizationInrL ℂ A a`
lands in `Set.range (WithLp.unitizationInrL ℂ A)` if and only if `g(0) = 0`. -/
theorem holomorphicCalculus_unitizationInrL_mem_range_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (zero_mem_spectrum_unitizationInrL a) g = 0 := by
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
    (algebraMap_sub_id_mul_of_dslope f (ha hz₀))
  rw [hc_eq, map_mul, map_sub (holomorphicCalculusOn a U ha),
    map_sub (holomorphicCalculusOn a U ha), AlgHom.commutes, holomorphicCalculusOn_id,
    AlgHom.commutes, ← holomorphicCalculus_toGerm a U ha f] at hfac
  have hcomm : Commute (algebraMap ℂ A z₀ - a) (holomorphicCalculusOn a U ha hU) :=
    (Algebra.commute_algebraMap_left z₀ _).sub_left
      ((Commute.refl a).holomorphicCalculusOn_right U ha hU)
  rw [spectrum.mem_iff]
  exact fun hu => hz₀ (hcomm.isUnit_mul_iff.mp (hfac.symm ▸ hu)).1

/-- **Spectral mapping theorem on an open domain.** For `f : holomorphicFunctions U` with
`spectrum ℂ a ⊆ U`, `spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a`. -/
@[simp]
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

/-- **Composition theorem for the holomorphic germ functional calculus.** For any
`f : holomorphicGerms (spectrum ℂ a)` and
`g : holomorphicGerms (spectrum ℂ (holomorphicCalculus a f))`, evaluating `g` at
`holomorphicCalculus a f` agrees with evaluating the composite germ at `a`. -/
@[simp]
theorem holomorphicCalculus_comp (a : A) (f : holomorphicGerms (spectrum ℂ a))
    (g : holomorphicGerms (spectrum ℂ (holomorphicCalculus a f))) :
    holomorphicCalculus (holomorphicCalculus a f) g =
      holomorphicCalculus a
        (holomorphicGerms.compRight f (spectrum_holomorphicCalculus a f).symm.subset g) := by
  let Ψ : holomorphicGerms (spectrum ℂ (holomorphicCalculus a f)) →ₐ[ℂ] A :=
    (holomorphicCalculus a).comp
      (holomorphicGerms.compRight f (spectrum_holomorphicCalculus a f).symm.subset)
  suffices hΨ : Ψ = holomorphicCalculus (holomorphicCalculus a f) from
    (DFunLike.congr_fun hΨ g).symm
  refine holomorphicCalculus_unique (holomorphicCalculus a f) Ψ ?_ fun V hb => ?_
  · simp [Ψ]
  · obtain ⟨U, ha, fU, rfl⟩ := holomorphicGerms.exists_toGerm_eq f
    have hfV : extend fU '' spectrum ℂ a ⊆ V := by
      rwa [holomorphicCalculus_toGerm, spectrum_holomorphicCalculusOn] at hb
    let U' : Opens ℂ := preimageOpen fU V
    have ha' : spectrum ℂ a ⊆ U' := subset_preimageOpen ha (mapsTo_iff_image_subset.mpr hfV)
    have hcomp : Ψ.comp (toGerm hb) =
        (holomorphicCalculusOn a U' ha').comp
          (HolomorphicFunctions.compRight fU (preimageOpen_le fU V)
            (mapsTo_extend_preimageOpen fU V)) := by
      ext gV
      simp only [Ψ, AlgHom.comp_apply,
        holomorphicGerms.compRight_toGerm hb fU gV (preimageOpen_le fU V) ha'
          (mapsTo_extend_preimageOpen fU V)
          (spectrum_holomorphicCalculus a (toGerm ha fU)).symm.subset,
        holomorphicCalculus_toGerm]
      rfl
    rw [hcomp]
    exact (continuous_holomorphicCalculusOn a U' ha').comp
      (HolomorphicFunctions.continuous_compRight fU (preimageOpen_le fU V)
        (mapsTo_extend_preimageOpen fU V))

/-- **Composition theorem on open domains.** If `f : holomorphicFunctions U` maps `U' ≤ U`
(containing `spectrum ℂ a`) into `V`, and `g : holomorphicFunctions V`, then evaluating `g` at
`holomorphicCalculusOn a U (ha'.trans hU') f` agrees with evaluating
`HolomorphicFunctions.compRight f hU' hmaps g` at `a`. -/
theorem holomorphicCalculusOn_comp (a : A) {U U' V : Opens ℂ}
    (f : holomorphicFunctions U) (g : holomorphicFunctions V)
    (hU' : U' ≤ U) (ha' : spectrum ℂ a ⊆ U') (hmaps : MapsTo (extend f) U' V) :
    holomorphicCalculusOn (holomorphicCalculusOn a U (ha'.trans hU') f) V
      ((spectrum_holomorphicCalculusOn a U (ha'.trans hU') f).subset.trans
        (hmaps.mono_left ha').image_subset) g =
      holomorphicCalculusOn a U' ha' (HolomorphicFunctions.compRight f hU' hmaps g) := by
  have hb : spectrum ℂ (holomorphicCalculus a (toGerm (ha'.trans hU') f)) ⊆ V := by
    rw [holomorphicCalculus_toGerm, spectrum_holomorphicCalculusOn]
    exact (hmaps.mono_left ha').image_subset
  have hcongr : ∀ {x y : A} (_ : x = y) (hx : spectrum ℂ x ⊆ V) (hy : spectrum ℂ y ⊆ V),
      holomorphicCalculusOn x V hx g = holomorphicCalculusOn y V hy g := by
    rintro _ _ rfl _ _
    rfl
  rw [← hcongr (holomorphicCalculus_toGerm a U (ha'.trans hU') f) hb _,
    ← holomorphicCalculus_toGerm _ V hb, holomorphicCalculus_comp,
    holomorphicGerms.compRight_toGerm hb f g hU' ha' hmaps, holomorphicCalculus_toGerm]

/-- **Composition theorem for ambient holomorphic representatives.** -/
theorem holomorphicCalculus_ofFun_comp (a : A) {f g : ℂ → ℂ} {t : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (ht : f '' spectrum ℂ a ⊆ t)
    (hg : AnalyticOnNhd ℂ g t) :
    holomorphicCalculus (holomorphicCalculus a (holomorphicGerms.ofFun f hf))
      (holomorphicGerms.ofFun g
        (hg.mono ((spectrum_holomorphicCalculus_ofFun a f hf).subset.trans ht))) =
      holomorphicCalculus a
        (holomorphicGerms.ofFun (g ∘ f) (hg.comp hf (mapsTo_iff_image_subset.mpr ht))) := by
  rw [holomorphicCalculus_comp, holomorphicGerms.compRight_ofFun]

end Composition

end TauCeti
