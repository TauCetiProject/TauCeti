/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Uniqueness

/-!
# Naturality, scalar and character evaluation, and unitized nonunital holomorphic calculus

Continuous unital `ℂ`-algebra homomorphisms intertwine `holomorphicCalculusOn` and
`holomorphicCalculus`. Applying uniqueness to evaluation at a complex scalar identifies
`holomorphicCalculus z` on `ℂ` with point evaluation at `z`; naturality then evaluates the calculus
at scalar multiples of the identity and under arbitrary complex characters (which are automatically
continuous on Banach algebras).

For an element `a` of a nonunital complex Banach algebra `A` canonically included into its ℓ¹
unitization `WithLp 1 (Unitization ℂ A)` as `WithLp.toLp 1 (a : Unitization ℂ A)`, character
evaluation along the scalar projection identifies the scalar component of
`holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g` with `g(0)`. Consequently the
unitized calculus lands in `A` precisely when `g(0) = 0`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped Ring

namespace TauCeti

open Contour HolomorphicFunctions

section Naturality

variable {A B F : Type*}
  [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn [FunLike F A B] [AlgHomClass F ℂ A B]
    (φ : F) (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U)
    (hφ : Continuous φ := by fun_prop) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f := by
  let φL : A →L[ℂ] B := ContinuousLinearMap.mk (LinearMap.ofClass φ)
    (by simpa only [LinearMap.toFun_eq_coe, LinearMap.coe_ofClass] using hφ)
  have hφL_apply (x : A) : φL x = φ x := by simp [φL, ContinuousLinearMap.coe_mk']
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  have hsub : spectrum ℂ (φ a) ⊆ spectrum ℂ a := AlgHom.spectrum_apply_subset φ a
  have hΓ' : Γ.IsIn (U \ spectrum ℂ (φ a)) :=
    Cycle.isIn_iff.mpr fun z hz ↦
      ⟨(Cycle.isIn_iff.mp hΓ hz).1, fun hzφ ↦ (Cycle.isIn_iff.mp hΓ hz).2 (hsub hzφ)⟩
  have hw' : ∀ z ∈ spectrum ℂ (φ a), Cycle.windingNumber z Γ = 1 :=
    fun z hz ↦ hw z (hsub hz)
  have hf_cont : ContinuousOn (extend f) (Cycle.trace Γ) :=
    (differentiableOn_extend f).continuousOn.mono fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  have hΓ_res : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  have hint : ∀ γ ∈ FreeAbelianGroup.support Γ,
      IntervalIntegrable (fun t ↦ deriv γ t • (extend f (γ t) • resolvent a (γ t)))
        MeasureTheory.volume γ.a γ.b :=
    fun _ ↦ Cycle.intervalIntegrable_of_mem_support
      (hf_cont.smul (Cycle.continuousOn_resolvent hΓ_res))
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw,
    holomorphicCalculusOn_eq_integral (φ a) U (hsub.trans ha) f Γ hΓ' hn hw',
    ← hφL_apply, map_smul, ← Cycle.integral_comp_comm hint φL]
  congr 1
  refine Cycle.integral_congr fun z hz ↦ ?_
  have hz_res : z ∈ resolventSet ℂ a := Cycle.isIn_iff.mp hΓ_res hz
  rw [map_smul, hφL_apply, resolvent, (spectrum.mem_resolventSet_iff.mp hz_res).map_ringInverse φ,
    map_sub, AlgHomClass.commutes, ← resolvent]

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculus`, restricting
the germ from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus [FunLike F A B] [AlgHomClass F ℂ A B]
    (φ : F) (a : A) (g : holomorphicGerms (spectrum ℂ a))
    (hφ : Continuous φ := by fun_prop) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, map_holomorphicCalculusOn φ a U ha f hφ,
    restrict_toGerm, holomorphicCalculus_toGerm]

/-- Naturality of `holomorphicCalculus` on represented germs under continuous unital `ℂ`-algebra
homomorphisms. -/
theorem map_holomorphicCalculus_ofFun [FunLike F A B] [AlgHomClass F ℂ A B]
    (φ : F) (a : A) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a))
    (hφ : Continuous φ := by fun_prop) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) := by
  rw [map_holomorphicCalculus φ a (holomorphicGerms.ofFun f hf) hφ,
    holomorphicGerms.restrict_ofFun]

end Naturality

section ScalarAndCharacter

/-- On `ℂ`, the holomorphic germ calculus at `z` is evaluation at `z`. -/
@[simp]
theorem holomorphicCalculus_complex (z : ℂ) (g : holomorphicGerms (spectrum ℂ z)) :
    holomorphicCalculus z g =
      holomorphicGerms.eval z (by simp [spectrum.mem_iff]) g := by
  have hz : z ∈ spectrum ℂ z := by simp [spectrum.mem_iff]
  have huniq : holomorphicGerms.eval z hz = holomorphicCalculus z := by
    refine holomorphicCalculus_unique z (holomorphicGerms.eval z hz)
      (holomorphicGerms.eval_ofFun z hz id analyticOnNhd_id) fun U hU ↦ ?_
    have hfun : ((holomorphicGerms.eval z hz).comp (toGerm hU) : holomorphicFunctions U → ℂ) =
        fun f : holomorphicFunctions U ↦ f.val ⟨z, hU hz⟩ := by
      ext f
      exact eval_toGerm hU z hz f
    rw [hfun]
    exact (continuous_eval_const (⟨z, hU hz⟩ : U)).comp continuous_subtype_val
  exact AlgHom.congr_fun huniq.symm g

/-- On `ℂ`, `holomorphicCalculusOn z U hz` evaluates a holomorphic function at `z`. -/
@[simp]
theorem holomorphicCalculusOn_complex (z : ℂ) (U : Opens ℂ) (hz : spectrum ℂ z ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn z U hz f = f.val ⟨z, hz (by simp [spectrum.mem_iff])⟩ := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_complex, eval_toGerm]

/-- Every complex character `φ` on a Banach algebra `A` evaluates `holomorphicCalculus a g` by
evaluating `g` at `φ a ∈ spectrum ℂ a`. -/
theorem algHom_apply_holomorphicCalculus {A F : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [FunLike F A ℂ] [AlgHomClass F ℂ A ℂ]
    (φ : F) (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicGerms.eval (φ a) (AlgHom.apply_mem_spectrum φ a) g := by
  rw [map_holomorphicCalculus φ a g, holomorphicCalculus_complex, holomorphicGerms.eval_restrict]

/-- Every complex character `φ` on a Banach algebra `A` evaluates `holomorphicCalculusOn a U ha f`
to `f(φ a)`. -/
theorem algHom_apply_holomorphicCalculusOn {A F : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [FunLike F A ℂ] [AlgHomClass F ℂ A ℂ]
    (φ : F) (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      f.val ⟨φ a, ha (AlgHom.apply_mem_spectrum φ a)⟩ := by
  rw [← holomorphicCalculus_toGerm, algHom_apply_holomorphicCalculus, eval_toGerm]

/-- Evaluating the holomorphic calculus at `algebraMap ℂ A c` in a nontrivial Banach algebra sends
`g` to `algebraMap ℂ A (g c)`. -/
@[simp]
theorem holomorphicCalculus_algebraMap {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (c : ℂ)
    (g : holomorphicGerms (spectrum ℂ (algebraMap ℂ A c))) :
    holomorphicCalculus (algebraMap ℂ A c) g =
      algebraMap ℂ A (holomorphicGerms.eval c (by simp [spectrum.scalar_eq]) g) := by
  obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
  have hsub : spectrum ℂ c ⊆ spectrum ℂ (algebraMap ℂ A c) := by
    intro z hz
    have hzc : z = c := by simpa [spectrum.mem_iff, sub_eq_zero] using hz
    simp [hzc, spectrum.scalar_eq]
  have h := map_holomorphicCalculus_ofFun (Algebra.ofId ℂ A) c f (hf.mono hsub)
    (algebraMapCLM ℂ A).continuous
  rw [holomorphicCalculus_complex, holomorphicGerms.eval_ofFun, Algebra.ofId_apply] at h
  rw [holomorphicGerms.eval_ofFun]
  exact h.symm

/-- Open-domain evaluation of `holomorphicCalculusOn` at `algebraMap ℂ A c` in a nontrivial Banach
algebra. -/
@[simp]
theorem holomorphicCalculusOn_algebraMap {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (c : ℂ) (U : Opens ℂ)
    (hc : spectrum ℂ (algebraMap ℂ A c) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (algebraMap ℂ A c) U hc f =
      algebraMap ℂ A (f.val ⟨c, hc (by simp [spectrum.scalar_eq])⟩) := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_algebraMap, eval_toGerm]

end ScalarAndCharacter

section Nonunital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- For any element `u` of the ℓ¹ unitization `WithLp 1 (Unitization ℂ A)`, the scalar component of
`holomorphicCalculus u g` evaluates `g` at the scalar coordinate `(WithLp.ofLp u).fst`. -/
theorem fst_holomorphicCalculus_unitization (u : WithLp 1 (Unitization ℂ A))
    (g : holomorphicGerms (spectrum ℂ u)) :
    (WithLp.ofLp (holomorphicCalculus u g)).fst =
      holomorphicGerms.eval (WithLp.ofLp u).fst (WithLp.fst_mem_spectrum_unitization u) g := by
  let π : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] ℂ :=
    (Unitization.fstHom ℂ A).comp (WithLp.unitizationAlgEquiv ℂ).toAlgHom
  have hπ (x : WithLp 1 (Unitization ℂ A)) : π x = (WithLp.ofLp x).fst := by simp [π]
  obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
  simpa only [hπ, holomorphicGerms.eval_ofFun] using
    algHom_apply_holomorphicCalculus π u (holomorphicGerms.ofFun f hf)

/-- Open-domain form of `fst_holomorphicCalculus_unitization` for an arbitrary element `u` of the
ℓ¹ unitization. -/
theorem fst_holomorphicCalculusOn_unitization (u : WithLp 1 (Unitization ℂ A)) (U : Opens ℂ)
    (hu : spectrum ℂ u ⊆ U) (f : holomorphicFunctions U) :
    (WithLp.ofLp (holomorphicCalculusOn u U hu f)).fst =
      f.val ⟨(WithLp.ofLp u).fst, hu (WithLp.fst_mem_spectrum_unitization u)⟩ := by
  rw [← holomorphicCalculus_toGerm, fst_holomorphicCalculus_unitization, eval_toGerm]

/-- The scalar component of `holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g` in the
ℓ¹ unitization is `g(0)`. -/
@[simp]
theorem fst_holomorphicCalculus_unitization_toLp_inr (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))) :
    (WithLp.ofLp (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g)).fst =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitization_toLp_inr a) g := by
  obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
  simpa using fst_holomorphicCalculus_unitization
    (WithLp.toLp 1 (a : Unitization ℂ A)) (holomorphicGerms.ofFun f hf)

/-- The scalar component of `holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f` is
`f(0)`. -/
@[simp]
theorem fst_holomorphicCalculusOn_unitization_toLp_inr (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)) ⊆ U) (f : holomorphicFunctions U) :
    (WithLp.ofLp (holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f)).fst =
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitization_toLp_inr a)⟩ := by
  rw [← holomorphicCalculus_toGerm, fst_holomorphicCalculus_unitization_toLp_inr, eval_toGerm]

/-- When `g(0) = 0`, the unitized holomorphic calculus equals the canonical inclusion of its
`A`-component. -/
theorem holomorphicCalculus_unitization_toLp_inr_eq_toLp_inr (a : A)
    {g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))}
    (hg0 : holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitization_toLp_inr a) g = 0) :
    holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g =
      WithLp.toLp 1
        ((WithLp.ofLp (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g)).snd :
          Unitization ℂ A) :=
  WithLp.eq_unitization_toLp_inr_of_fst_eq_zero
    ((fst_holomorphicCalculus_unitization_toLp_inr a g).trans hg0)

/-- For a nonunital Banach algebra `A`, the unitized holomorphic calculus
`holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g` lies in the image of `A` if and only
if `g(0) = 0`. -/
theorem holomorphicCalculus_unitization_toLp_inr_mem_range_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))) :
    holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g ∈
        Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitization_toLp_inr a) g = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, fst_holomorphicCalculus_unitization_toLp_inr]

/-- Open-domain form of `holomorphicCalculus_unitization_toLp_inr_mem_range_iff`: the unitized
calculus of `f : holomorphicFunctions U` lies in `A` if and only if `f(0) = 0`. -/
theorem holomorphicCalculusOn_unitization_toLp_inr_mem_range_iff (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f ∈
        Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitization_toLp_inr a)⟩ = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, fst_holomorphicCalculusOn_unitization_toLp_inr]

end Nonunital

end TauCeti
