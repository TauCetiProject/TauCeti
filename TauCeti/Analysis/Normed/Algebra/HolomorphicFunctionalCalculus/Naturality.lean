/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Uniqueness
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

/-!
# Naturality, scalar evaluation, and unitized nonunital holomorphic calculus

Continuous unital `ℂ`-algebra homomorphisms intertwine `holomorphicCalculusOn` and
`holomorphicCalculus`. Applying uniqueness to evaluation at a complex scalar identifies
`holomorphicCalculus z` on `ℂ` with point evaluation at `z`, and naturality along `algebraMap ℂ A`
evaluates the calculus on scalar multiples of the identity.

For an element `a` of a nonunital complex Banach algebra `A` embedded into its ℓ¹ unitization
`WithLp 1 (Unitization ℂ A)` via `WithLp.unitizationInrL ℂ A a`, naturality along the continuous
scalar-part homomorphism `(Unitization.fstHom ℂ A).comp (WithLp.unitizationAlgEquiv ℂ)` identifies
the scalar component of `holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g` with `g(0)`.
Consequently the unitized calculus lands in `A` precisely when `g(0) = 0`.

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
theorem map_holomorphicCalculusOn_of_continuous [FunLike F A B] [AlgHomClass F ℂ A B]
    (φ : F) (hφ : Continuous φ) (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f := by
  let φL : A →L[ℂ] B := { (AlgHom.ofClass φ : A →ₐ[ℂ] B).toLinearMap with cont := hφ }
  have hφL_apply (x : A) : φL x = φ x := rfl
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

/-- Bundled continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn [FunLike F A B] [AlgHomClass F ℂ A B] [ContinuousMapClass F A B]
    (φ : F) (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  map_holomorphicCalculusOn_of_continuous φ (map_continuous φ) a U ha f

/-- Continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculus`, restricting
the germ from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus_of_continuous [FunLike F A B] [AlgHomClass F ℂ A B]
    (φ : F) (hφ : Continuous φ) (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, map_holomorphicCalculusOn_of_continuous φ hφ a U ha f,
    restrict_toGerm, holomorphicCalculus_toGerm]

/-- Bundled continuous unital `ℂ`-algebra homomorphisms commute with `holomorphicCalculus`. -/
theorem map_holomorphicCalculus [FunLike F A B] [AlgHomClass F ℂ A B] [ContinuousMapClass F A B]
    (φ : F) (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  map_holomorphicCalculus_of_continuous φ (map_continuous φ) a g

/-- Naturality of `holomorphicCalculus` on represented germs under continuous unital `ℂ`-algebra
homomorphisms. -/
theorem map_holomorphicCalculus_ofFun_of_continuous [FunLike F A B] [AlgHomClass F ℂ A B]
    (φ : F) (hφ : Continuous φ) (a : A) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) := by
  rw [map_holomorphicCalculus_of_continuous φ hφ a (holomorphicGerms.ofFun f hf),
    holomorphicGerms.restrict_ofFun]

/-- Naturality of `holomorphicCalculus` on represented germs for bundled continuous homomorphisms.
-/
theorem map_holomorphicCalculus_ofFun [FunLike F A B] [AlgHomClass F ℂ A B]
    [ContinuousMapClass F A B] (φ : F) (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    φ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.ofFun f (hf.mono (AlgHom.spectrum_apply_subset φ a))) :=
  map_holomorphicCalculus_ofFun_of_continuous φ (map_continuous φ) a f hf

end Naturality

section Scalar

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
  exact congrFun (congrArg DFunLike.coe huniq.symm) g

/-- On `ℂ`, `holomorphicCalculusOn z U hz` evaluates a holomorphic function at `z`. -/
@[simp]
theorem holomorphicCalculusOn_complex (z : ℂ) (U : Opens ℂ) (hz : spectrum ℂ z ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn z U hz f = f.val ⟨z, hz (by simp [spectrum.mem_iff])⟩ := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_complex, eval_toGerm]

/-- Evaluating the holomorphic calculus at `algebraMap ℂ A c` in a nontrivial Banach algebra sends
`g` to `algebraMap ℂ A (g c)`. -/
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
  have h := map_holomorphicCalculus_ofFun_of_continuous (Algebra.ofId ℂ A)
    (algebraMapCLM ℂ A).continuous c f (hf.mono hsub)
  rw [holomorphicCalculus_complex, holomorphicGerms.eval_ofFun, Algebra.ofId_apply] at h
  rw [holomorphicGerms.eval_ofFun]
  exact h.symm

end Scalar

section Nonunital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- The scalar component of `holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g` in the ℓ¹
unitization is `g(0)`. -/
@[simp]
theorem fst_holomorphicCalculus_unitizationInrL (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    (WithLp.ofLp (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)).fst =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
  let π : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] ℂ :=
    (Unitization.fstHom ℂ A).comp (WithLp.unitizationAlgEquiv ℂ).toAlgHom
  have hπ_cont : Continuous π :=
    (WithLp.unitizationFstL ℂ A).continuous.congr fun u ↦ WithLp.unitizationFstL_apply ℂ A u
  have hπ_inr : π (WithLp.unitizationInrL ℂ A a) = 0 := by
    simp [π]
  have h := map_holomorphicCalculus_of_continuous π hπ_cont
    (WithLp.unitizationInrL ℂ A a) g
  have hrhs :
      holomorphicCalculus (π (WithLp.unitizationInrL ℂ A a))
        (holomorphicGerms.restrict
          (AlgHom.spectrum_apply_subset π (WithLp.unitizationInrL ℂ A a)) g) =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
    have hgen : ∀ (c : ℂ), c = 0 →
        ∀ (hsub' : spectrum ℂ c ⊆ spectrum ℂ (WithLp.unitizationInrL ℂ A a)),
          holomorphicCalculus c (holomorphicGerms.restrict hsub' g) =
            holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
      rintro _ rfl hsub'
      rw [holomorphicCalculus_complex, holomorphicGerms.eval_restrict]
    exact hgen _ hπ_inr _
  have hfst : π (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g) =
      (WithLp.ofLp (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)).fst := rfl
  exact hfst.symm.trans (h.trans hrhs)

/-- The scalar component of `holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f` is
`f(0)`. -/
@[simp]
theorem fst_holomorphicCalculusOn_toLp_inr (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)) ⊆ U) (f : holomorphicFunctions U) :
    (WithLp.ofLp (holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f)).fst =
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_toLp_inr a)⟩ := by
  have ha' : spectrum ℂ (WithLp.unitizationInrL ℂ A a) ⊆ U := by
    simpa only [WithLp.unitizationInrL_apply] using ha
  have heq : holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f =
      holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha' f := by
    have hgen : ∀ (x : WithLp 1 (Unitization ℂ A)), x = WithLp.unitizationInrL ℂ A a →
        ∀ (hx : spectrum ℂ x ⊆ U),
          holomorphicCalculusOn x U hx f =
            holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha' f := by
      rintro _ rfl _
      rfl
    exact hgen _ (WithLp.unitizationInrL_apply ℂ A a).symm ha
  rw [heq, ← holomorphicCalculus_toGerm, fst_holomorphicCalculus_unitizationInrL, eval_toGerm]

/-- The scalar component of `holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha f` is
`f(0)`. -/
theorem fst_holomorphicCalculusOn_unitizationInrL (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.unitizationInrL ℂ A a) ⊆ U) (f : holomorphicFunctions U) :
    (WithLp.ofLp (holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha f)).fst =
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitizationInrL a)⟩ := by
  rw [← holomorphicCalculus_toGerm, fst_holomorphicCalculus_unitizationInrL, eval_toGerm]

/-- For a nonunital Banach algebra `A`, the unitized holomorphic calculus
`holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g` lies in the image of `A` if and only if
`g(0) = 0`. -/
theorem holomorphicCalculus_unitizationInrL_mem_range_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g ∈
        Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    rw [← fst_holomorphicCalculus_unitizationInrL a g, ← hb]
    simp
  · intro hg0
    refine ⟨WithLp.unitizationSndL ℂ A
      (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g), ?_⟩
    conv_rhs =>
      rw [WithLp.unitization_eq_fst_smul_one_add_inr
        (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)]
    rw [fst_holomorphicCalculus_unitizationInrL, hg0, zero_smul, zero_add]
    simp [WithLp.unitizationInrL_apply, WithLp.unitizationSndL_apply]

/-- When `g(0) = 0`, the unitized holomorphic calculus equals the inclusion of its `A`-component. -/
theorem holomorphicCalculus_unitizationInrL_eq_inr (a : A)
    {g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))}
    (hg0 : holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g =
      WithLp.unitizationInrL ℂ A
        (WithLp.unitizationSndL ℂ A
          (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)) := by
  conv_lhs =>
    rw [WithLp.unitization_eq_fst_smul_one_add_inr
      (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)]
  rw [fst_holomorphicCalculus_unitizationInrL, hg0, zero_smul, zero_add]
  simp [WithLp.unitizationInrL_apply, WithLp.unitizationSndL_apply]

/-- Open-domain form of `holomorphicCalculus_unitizationInrL_mem_range_iff`: the unitized calculus
of `f : holomorphicFunctions U` lies in `A` if and only if `f(0) = 0`. -/
theorem holomorphicCalculusOn_unitizationInrL_mem_range_iff (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.unitizationInrL ℂ A a) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha f ∈
        Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitizationInrL a)⟩ = 0 := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_unitizationInrL_mem_range_iff, eval_toGerm]

end Nonunital

end TauCeti
