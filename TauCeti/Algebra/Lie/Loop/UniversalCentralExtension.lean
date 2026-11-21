/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Loop
public import Mathlib.Algebra.Lie.Weights.IsSimple
public import TauCeti.Algebra.Lie.Extension.Basic
-- Proof-only: dual separation, H² classification on loops, quotient lifts, and form uniqueness.
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Lie.Loop.Cocycle
import TauCeti.Algebra.Lie.Quotient
import TauCeti.Algebra.Lie.Weights.IsSimple

/-!
# Universal central extension property of the residue loop extension

Let `L` be a Lie algebra over a field `K` of characteristic zero with nondegenerate Killing form
whose `L`-invariant bilinear forms are all scalar multiples of a symmetric invariant form `Φ`, and
let `c₀ = twoCocycleOfBilinear K ℤ L Φ hΦ hΦs` be the residue 2-cocycle on the polynomial loop
algebra `loopAlgebra K ℤ L = K[t, t⁻¹] ⊗ L`.

This file proves the universal central extension criterion for `ofTwoCocycle c₀`
(`TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_ofTwoCocycle`): for any
surjective Lie algebra homomorphism `f : G →ₗ⁅K⁆ ofTwoCocycle c₀` from a perfect Lie algebra `G`
admitting a central lift `cG` of `centralElement c₀`, the kernel satisfies `⁅⊤, f.ker⁆ = f.ker`.

In particular, when `L` is a split finite-dimensional simple Lie algebra over `K` (without assuming
`K` is algebraically closed), uniqueness of invariant bilinear forms
(`LieSubalgebra.exists_eq_smul_killingForm_of_isSimple`) discharges the spanning
hypothesis automatically for any nonzero symmetric invariant form `Φ`
(`LieSubalgebra.lie_top_ker_eq_ker_of_surjective_ofTwoCocycle_of_isSimple`).

## Main results

* `TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_ofTwoCocycle`: universal central
  extension property (`⁅⊤, f.ker⁆ = f.ker`) for perfect covers of `ofTwoCocycle c₀`.
* `LieSubalgebra.lie_top_ker_eq_ker_of_surjective_ofTwoCocycle_of_isSimple`:
  specialization to any split finite-dimensional simple Lie algebra `L` and nonzero symmetric
  invariant form `Φ`.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §7.4, for the universal central
  extension step in the realization of untwisted affine Kac–Moody algebras.
* C. Kassel, *Kähler differentials and coverings of complex simple Lie algebras extended over a
  commutative algebra*, J. Pure Appl. Algebra 34 (1984), 265–275.
-/

public section

noncomputable section

open _root_.LieAlgebra _root_.LieAlgebra.LoopAlgebra
open _root_.LieModule.Cohomology
open _root_.LieAlgebra.ofTwoCocycle (centralElement)

namespace TauCeti.LieAlgebra.LoopAlgebra

section UniversalCentralExtension

variable {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [LieRing G] [LieAlgebra K G]

private theorem eq_bot_of_central_extension_of_loopAlgebra
    {K L Q : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsKilling K L] [LieRing Q] [LieAlgebra K Q]
    {Φ : LinearMap.BilinForm K L} (hΦs : Φ.IsSymm)
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    (πQ : Q →ₗ⁅K⁆ loopAlgebra K ℤ L) (hπQ_surj : Function.Surjective πQ)
    (hker_central : ∀ z ∈ πQ.ker, ∀ y : Q, ⁅y, z⁆ = 0)
    (hQ_perf : (⁅(⊤ : LieIdeal K Q), (⊤ : LieIdeal K Q)⁆ : LieIdeal K Q) = ⊤)
    (Z : LieIdeal K Q) (hZ_le : Z ≤ πQ.ker)
    {cQ : Q} (hcQ_ker : cQ ∈ πQ.ker) (hcQ_not_Z : cQ ∉ Z)
    {ι : Type*} {s : Finset ι} {a : ι → K} {u v : ι → Q}
    (hcQ_sum : cQ = ∑ k ∈ s, a k • ⁅u k, v k⁆)
    (hpair : ∑ k ∈ s, a k * residuePairing K ℤ L Φ (πQ (u k)) (πQ (v k)) ≠ 0) :
    Z = ⊥ := by
  by_contra hZ_ne
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ : ∃ z₀ ∈ Z, z₀ ≠ 0 := by
    by_contra! h
    exact hZ_ne (eq_bot_iff.mpr fun z hz ↦ by simp [h z hz])
  have hz₀_ker : z₀ ∈ πQ.ker := hZ_le hz₀Z
  -- Build a linear form `μ : πQ.ker →ₗ[K] K` killing `cQ` and nonzero at `z₀`.
  let U : Submodule K πQ.ker := K ∙ (⟨cQ, hcQ_ker⟩ : πQ.ker)
  have hz₀_not_U : (⟨z₀, hz₀_ker⟩ : πQ.ker) ∉ U := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨r, hr⟩
    have hr' : r • cQ = z₀ := congrArg Subtype.val hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr'
      exact hz₀ne hr'.symm
    apply hcQ_not_Z
    have : cQ = r⁻¹ • z₀ := by rw [← hr', smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact Z.smul_mem r⁻¹ hz₀Z
  have hmk_ne : U.mkQ ⟨z₀, hz₀_ker⟩ ≠ 0 := fun h0 ↦
    hz₀_not_U ((Submodule.Quotient.mk_eq_zero U).mp h0)
  obtain ⟨ν, hν⟩ : ∃ ν : Module.Dual K (πQ.ker ⧸ U), ν (U.mkQ ⟨z₀, hz₀_ker⟩) ≠ 0 := by
    by_contra! h
    exact hmk_ne ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  let μ : πQ.ker →ₗ[K] K := ν ∘ₗ U.mkQ
  have hμ_cQ : μ ⟨cQ, hcQ_ker⟩ = 0 := by
    simp only [μ, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero U).mpr (Submodule.mem_span_singleton_self _), map_zero]
  have hμ_z₀ : μ ⟨z₀, hz₀_ker⟩ ≠ 0 := by
    simpa only [μ, LinearMap.comp_apply] using hν
  -- Choose a `K`-linear section `sec` of `πQ` and form the associated 2-cocycle `ω`.
  obtain ⟨sec, hsec⟩ := LinearMap.exists_rightInverse_of_surjective πQ.toLinearMap
    (LinearMap.range_eq_top.mpr hπQ_surj)
  have hsec_apply (p : loopAlgebra K ℤ L) : πQ (sec p) = p :=
    congrArg (fun g : loopAlgebra K ℤ L →ₗ[K] loopAlgebra K ℤ L ↦ g p) hsec
  have hsec_ker (p₁ p₂ : loopAlgebra K ℤ L) : ⁅sec p₁, sec p₂⁆ - sec ⁅p₁, p₂⁆ ∈ πQ.ker := by
    rw [LieHom.mem_ker, map_sub, LieHom.map_lie, hsec_apply, hsec_apply, hsec_apply, sub_self]
  let e := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
  have hsmul_lie (r : K) (p₁ p₂ : loopAlgebra K ℤ L) : ⁅r • p₁, p₂⁆ = r • ⁅p₁, p₂⁆ :=
    calc ⁅r • p₁, p₂⁆ = -⁅p₂, r • p₁⁆ := (lie_skew (r • p₁) p₂).symm
      _ = -(r • ⁅p₂, p₁⁆) := congrArg Neg.neg (LieAlgebra.lie_smul r p₂ p₁)
      _ = r • (-⁅p₂, p₁⁆) := (smul_neg r ⁅p₂, p₁⁆).symm
      _ = r • ⁅p₁, p₂⁆ := congrArg (r • ·) (lie_skew p₁ p₂)
  let ωB : loopAlgebra K ℤ L →ₗ[K] loopAlgebra K ℤ L →ₗ[K]
      TrivialLieModule K (loopAlgebra K ℤ L) K :=
    LinearMap.mk₂ K (fun p₁ p₂ ↦ e.symm (μ ⟨⁅sec p₁, sec p₂⁆ - sec ⁅p₁, p₂⁆, hsec_ker p₁ p₂⟩))
      (fun p₁ p₂ p₃ ↦ by
        rw [← map_add, ← map_add]
        congr 2
        apply Subtype.ext
        rw [AddMemClass.coe_add]
        dsimp only
        rw [map_add, add_lie, LieRing.add_lie, map_add]
        abel)
      (fun r p₁ p₂ ↦ by
        rw [← map_smul, ← map_smul]
        congr 2
        apply Subtype.ext
        rw [SetLike.val_smul]
        dsimp only
        rw [map_smul, smul_lie, hsmul_lie, map_smul, smul_sub])
      (fun p₁ p₂ p₃ ↦ by
        rw [← map_add, ← map_add]
        congr 2
        apply Subtype.ext
        rw [AddMemClass.coe_add]
        dsimp only
        rw [map_add, lie_add, LieRing.lie_add, map_add]
        abel)
      (fun r p₁ p₂ ↦ by
        rw [← map_smul, ← map_smul]
        congr 2
        apply Subtype.ext
        rw [SetLike.val_smul]
        dsimp only
        rw [map_smul, lie_smul, LieAlgebra.lie_smul r p₁ p₂, map_smul, smul_sub])
  let ω : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) :=
    ⟨ωB, fun p ↦ by
      simp only [ωB, LinearMap.mk₂_apply]
      have h0 : (⟨⁅sec p, sec p⁆ - sec ⁅p, p⁆, hsec_ker p p⟩ : πQ.ker) = 0 :=
        Subtype.ext (by simp)
      rw [h0, map_zero, map_zero]⟩
  have hω_apply (p₁ p₂ : loopAlgebra K ℤ L) :
      ω p₁ p₂ = e.symm (μ ⟨⁅sec p₁, sec p₂⁆ - sec ⁅p₁, p₂⁆, hsec_ker p₁ p₂⟩) := by
    rw [← twoCochain_val_apply]
    simp only [ω, ωB, LinearMap.mk₂_apply]
  have hω_cocycle : ω ∈ twoCocycle K (loopAlgebra K ℤ L)
      (TrivialLieModule K (loopAlgebra K ℤ L) K) := by
    rw [mem_twoCocycle_iff_of_trivial]
    intro p₁ p₂ p₃
    simp only [hω_apply]
    rw [← map_add, ← map_add]
    congr 2
    apply Subtype.ext
    have hrep_r (x y z : loopAlgebra K ℤ L) : ⁅sec x, sec ⁅y, z⁆⁆ = ⁅sec x, ⁅sec y, sec z⁆⁆ := by
      have h0 := hker_central (⁅sec y, sec z⁆ - sec ⁅y, z⁆) (hsec_ker y z) (sec x)
      rw [lie_sub, sub_eq_zero] at h0
      exact h0.symm
    have hrep_l (x y z : loopAlgebra K ℤ L) : ⁅sec ⁅x, y⁆, sec z⁆ = ⁅⁅sec x, sec y⁆, sec z⁆ := by
      have h0 := hker_central (⁅sec x, sec y⁆ - sec ⁅x, y⁆) (hsec_ker x y) (sec z)
      rw [← lie_skew, neg_eq_zero, sub_lie, sub_eq_zero] at h0
      exact h0.symm
    rw [AddMemClass.coe_add]
    dsimp only
    rw [hrep_r p₁ p₂ p₃, hrep_l p₁ p₂ p₃, hrep_r p₂ p₁ p₃,
      leibniz_lie (sec p₁) (sec p₂) (sec p₃), LieRing.leibniz_lie p₁ p₂ p₃, map_add]
    abel
  -- Decompose `ω = t • twoCochainOfBilinear Φ + d₁₂ η`.
  have hdecomp : ω ∈ (K ∙ twoCochainOfBilinear K ℤ L Φ hΦs) ⊔
      LinearMap.range (d₁₂ K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) := by
    rw [← twoCocycle_eq_span_sup_range_d₁₂ hΦs hspan]
    exact hω_cocycle
  obtain ⟨_, hmem_span, _, ⟨η, rfl⟩, hω_eq⟩ := Submodule.mem_sup.mp hdecomp
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem_span
  have hproj_ker (y : Q) : y - sec (πQ y) ∈ πQ.ker := by
    rw [LieHom.mem_ker, map_sub, hsec_apply, sub_self]
  let ψ : Q →ₗ[K] K :=
    { toFun y := μ ⟨y - sec (πQ y), hproj_ker y⟩ + e (η (πQ y))
      map_add' y₁ y₂ := by
        have hsub : (⟨y₁ + y₂ - sec (πQ (y₁ + y₂)), hproj_ker (y₁ + y₂)⟩ : πQ.ker) =
            ⟨y₁ - sec (πQ y₁), hproj_ker y₁⟩ + ⟨y₂ - sec (πQ y₂), hproj_ker y₂⟩ := by
          apply Subtype.ext
          simp only [AddMemClass.coe_add, map_add]
          abel
        rw [hsub, map_add, map_add, map_add, map_add]
        ring
      map_smul' r y := by
        have hsub : (⟨r • y - sec (πQ (r • y)), hproj_ker (r • y)⟩ : πQ.ker) =
            r • ⟨y - sec (πQ y), hproj_ker y⟩ := by
          apply Subtype.ext
          simp only [SetLike.val_smul, map_smul, smul_sub]
        rw [hsub, map_smul, map_smul, map_smul, map_smul]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }
  have hψ_apply (y : Q) : ψ y = μ ⟨y - sec (πQ y), hproj_ker y⟩ + e (η (πQ y)) := by
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
  have hψ_lie (y₁ y₂ : Q) :
      ψ ⁅y₁, y₂⁆ = t * residuePairing K ℤ L Φ (πQ y₁) (πQ y₂) := by
    have hbra : ⁅y₁, y₂⁆ = ⁅sec (πQ y₁), sec (πQ y₂)⁆ := by
      have h1 := hker_central (y₁ - sec (πQ y₁)) (hproj_ker y₁) y₂
      rw [← lie_skew, neg_eq_zero, sub_lie, sub_eq_zero] at h1
      have h2 := hker_central (y₂ - sec (πQ y₂)) (hproj_ker y₂) (sec (πQ y₁))
      rw [lie_sub, sub_eq_zero] at h2
      exact h1.trans h2
    have hω_eval := congrArg
      (fun c : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) ↦
        e (c (πQ y₁) (πQ y₂))) hω_eq
    have he_inv (r : K) :
        e ((TrivialLieModule.equiv K (loopAlgebra K ℤ L) K).symm r) = r :=
      e.apply_symm_apply r
    simp only [add_apply_apply, smul_apply_apply, twoCochainOfBilinear_apply_apply,
      d₁₂_apply_apply_ofTrivial, map_add, map_smul, map_neg, he_inv, smul_eq_mul] at hω_eval
    rw [hψ_apply]
    have heq_sub : (⟨⁅y₁, y₂⁆ - sec (πQ ⁅y₁, y₂⁆), hproj_ker ⁅y₁, y₂⁆⟩ : πQ.ker) =
        ⟨⁅sec (πQ y₁), sec (πQ y₂)⁆ - sec ⁅πQ y₁, πQ y₂⁆, hsec_ker (πQ y₁) (πQ y₂)⟩ := by
      apply Subtype.ext
      dsimp only
      rw [hbra, LieHom.map_lie, hsec_apply, hsec_apply]
    rw [heq_sub, LieHom.map_lie]
    have hω_val : e (ω (πQ y₁) (πQ y₂)) =
        μ ⟨⁅sec (πQ y₁), sec (πQ y₂)⁆ - sec ⁅πQ y₁, πQ y₂⁆, hsec_ker (πQ y₁) (πQ y₂)⟩ := by
      rw [hω_apply, e.apply_symm_apply]
    rw [hω_val] at hω_eval
    linear_combination -hω_eval
  -- Evaluate `ψ cQ` both directly (`0`) and via `hcQ_sum`, forcing `t = 0`.
  have hψ_cQ_zero : ψ cQ = 0 := by
    rw [hψ_apply]
    have hπc : πQ cQ = 0 := LieHom.mem_ker.mp hcQ_ker
    have hsub : (⟨cQ - sec (πQ cQ), hproj_ker cQ⟩ : πQ.ker) = ⟨cQ, hcQ_ker⟩ :=
      Subtype.ext (by simp [hπc])
    rw [hsub, hμ_cQ, hπc, map_zero, map_zero, add_zero]
  have hψ_cQ_sum : ψ cQ = t * ∑ k ∈ s, a k * residuePairing K ℤ L Φ (πQ (u k)) (πQ (v k)) := by
    rw [hcQ_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul, hψ_lie]
    ring
  have ht0 : t = 0 := (mul_eq_zero.mp (hψ_cQ_sum.symm.trans hψ_cQ_zero)).resolve_right hpair
  have hψ_lie0 (y₁ y₂ : Q) : ψ ⁅y₁, y₂⁆ = 0 := by rw [hψ_lie, ht0, zero_mul]
  -- Since `Q` is perfect, `ψ` vanishes identically on `Q`.
  have hψ_zero : ∀ y : Q, ψ y = 0 := by
    have hle : (↑(⁅(⊤ : LieIdeal K Q), (⊤ : LieIdeal K Q)⁆ : LieIdeal K Q) : Submodule K Q) ≤
        LinearMap.ker ψ := by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.span_le]
      rintro _ ⟨x₁, _, x₂, _, rfl⟩
      exact hψ_lie0 x₁ x₂
    intro y
    exact hle (by rw [hQ_perf]; trivial)
  -- Evaluate `ψ z₀ = μ ⟨z₀, hz₀_ker⟩` to obtain a contradiction.
  have hψ_z₀ : ψ z₀ = μ ⟨z₀, hz₀_ker⟩ := by
    rw [hψ_apply]
    have hπz : πQ z₀ = 0 := LieHom.mem_ker.mp hz₀_ker
    have hsub : (⟨z₀ - sec (πQ z₀), hproj_ker z₀⟩ : πQ.ker) = ⟨z₀, hz₀_ker⟩ :=
      Subtype.ext (by simp [hπz])
    rw [hsub, hπz, map_zero, map_zero, add_zero]
  exact hμ_z₀ (hψ_z₀.symm.trans (hψ_zero z₀))

/-- **Universal central extension property of the residue central extension**:
let `L` be a Lie algebra with nondegenerate Killing form over a field `K` of characteristic zero
whose invariant bilinear forms are all scalar multiples of a symmetric invariant form `Φ`, and let
`c₀ = twoCocycleOfBilinear K ℤ L Φ hΦ hΦs`. Suppose `f : G →ₗ⁅K⁆ ofTwoCocycle c₀` is a surjective
Lie algebra homomorphism from a perfect Lie algebra `G` (`⁅⊤, ⊤⁆ = ⊤`) admitting a central element
`cG` with `f cG = centralElement c₀`. Then `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_ofTwoCocycle
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker := by
  let c₀ := twoCocycleOfBilinear K ℤ L Φ hΦ hΦs
  let I : LieIdeal K G := f.ker
  let J : LieIdeal K G := ⁅(⊤ : LieIdeal K G), I⁆
  let π : G →ₗ⁅K⁆ loopAlgebra K ℤ L := (ofTwoCocycle.proj c₀).comp f
  have hπ_apply (y : G) : π y = ofTwoCocycle.proj c₀ (f y) := LieHom.comp_apply _ _ _
  have hπ_surj : Function.Surjective π := (ofTwoCocycle.proj_surjective c₀).comp hf
  have hker_π (y : G) : y ∈ π.ker ↔ ∃ r : K, y - r • cG ∈ I := by
    rw [LieHom.mem_ker, hπ_apply]
    constructor
    · intro h0
      set r := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K ((ofProd c₀).symm (f y)).2
      refine ⟨r, LieHom.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, hcG_map, sub_eq_zero]
      have hdecomp := ofTwoCocycle.ofProd_eq_add_smul_centralElement c₀
        ((ofProd c₀).symm (f y)).1 ((ofProd c₀).symm (f y)).2
      rw [Prod.mk.eta, Equiv.apply_symm_apply] at hdecomp
      have h1 : ((ofProd c₀).symm (f y)).1 = 0 := by rwa [← ofTwoCocycle.proj_apply]
      have h00 : ofProd c₀ (0, 0) = 0 := of_zero c₀
      rw [h1, h00, zero_add] at hdecomp
      exact hdecomp
    · rintro ⟨r, hr⟩
      have hfy : f y = r • centralElement c₀ := by
        have hsub := LieHom.mem_ker.mp hr
        rw [map_sub, map_smul, hcG_map, sub_eq_zero] at hsub
        exact hsub
      rw [hfy, map_smul, ofTwoCocycle.proj_apply, ofTwoCocycle.ofProd_symm_centralElement,
        smul_zero]
  have hJ_le_I : J ≤ I := LieSubmodule.lie_le_right _ _
  have hI_le_ker : I ≤ π.ker := fun y hy ↦ (hker_π y).mpr ⟨0, by simpa using hy⟩
  let q : G →ₗ⁅K⁆ G ⧸ J := J.mkQ
  let πQ : G ⧸ J →ₗ⁅K⁆ loopAlgebra K ℤ L := J.liftQ π (le_trans hJ_le_I hI_le_ker)
  have hπQ_q (y : G) : πQ (q y) = π y := LieHom.congr_fun (J.liftQ_mkQ π _) y
  have hπQ_surj : Function.Surjective πQ := fun p ↦ by
    obtain ⟨y, rfl⟩ := hπ_surj p
    exact ⟨q y, hπQ_q y⟩
  let Z : LieIdeal K (G ⧸ J) := LieIdeal.map q I
  let cQ : G ⧸ J := q cG
  have hker_central : ∀ z ∈ πQ.ker, ∀ y : G ⧸ J, ⁅y, z⁆ = 0 := by
    intro z hz y
    obtain ⟨w, rfl⟩ := J.surjective_mkQ y
    obtain ⟨x, rfl⟩ := J.surjective_mkQ z
    have hx : x ∈ π.ker := by rwa [LieHom.mem_ker, ← hπQ_q]
    obtain ⟨r, hr⟩ := (hker_π x).mp hx
    have hbra : ⁅w, x⁆ ∈ J := by
      have hx_eq : x = (x - r • cG) + r • cG := by abel
      rw [hx_eq, lie_add, lie_smul, hcG_cent w, smul_zero, add_zero]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top w) hr
    rw [← LieHom.map_lie]
    exact LieSubmodule.Quotient.mk_eq_zero'.mpr hbra
  have hQ_perf : (⁅(⊤ : LieIdeal K (G ⧸ J)), (⊤ : LieIdeal K (G ⧸ J))⁆ :
      LieIdeal K (G ⧸ J)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨w, rfl⟩ := J.surjective_mkQ y
    have hle : (↑(⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) : Submodule K G) ≤
        Submodule.comap q.toLinearMap
          (↑(⁅(⊤ : LieIdeal K (G ⧸ J)), (⊤ : LieIdeal K (G ⧸ J))⁆ : LieIdeal K (G ⧸ J))) := by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.span_le]
      rintro _ ⟨x₁, _, x₂, _, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LieHom.coe_toLinearMap,
        LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.mem_toSubmodule, LieHom.map_lie]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    exact hle (by rw [hperf]; trivial)
  have hZ_le : Z ≤ πQ.ker := by
    intro z hz
    obtain ⟨⟨x, hxI⟩, rfl⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hz
    rw [LieHom.mem_ker, hπQ_q]
    exact hI_le_ker hxI
  have hcQ_ker : cQ ∈ πQ.ker := by
    rw [LieHom.mem_ker, hπQ_q]
    exact (hker_π cG).mpr ⟨1, by simp⟩
  have hcQ_not_Z : cQ ∉ Z := by
    intro hcZ
    obtain ⟨⟨x, hxI⟩, hxq⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hcZ
    have hdiff : cG - x ∈ J := by
      have h0 : q (cG - x) = 0 := by rw [map_sub, hxq, sub_self]
      exact LieSubmodule.Quotient.mk_eq_zero'.mp h0
    have hcI : cG ∈ I := by
      have : cG = (cG - x) + x := by abel
      rw [this]
      exact add_mem (hJ_le_I hdiff) hxI
    have hc0 : centralElement c₀ = 0 := hcG_map ▸ LieHom.mem_ker.mp hcI
    exact ofTwoCocycle.centralElement_ne_zero c₀ hc0
  have hcG_mem : cG ∈ Submodule.span K {z : G | ∃ u v : G, ⁅u, v⁆ = z} := by
    have hcG_top : cG ∈ (↑(⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) :
        Submodule K G) := by
      rw [hperf]
      trivial
    rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hcG_top
    simpa only [LieSubmodule.mem_top, true_and] using hcG_top
  obtain ⟨n, a, g, hg_sum⟩ := Submodule.mem_span_set'.mp hcG_mem
  choose u v huv using fun k : Fin n ↦ (g k).property
  have hcG_sum : cG = ∑ k : Fin n, a k • ⁅u k, v k⁆ := by
    rw [← hg_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [huv k]
  have hcQ_sum : cQ = ∑ k ∈ Finset.univ, a k • ⁅q (u k), q (v k)⁆ := by
    dsimp only [cQ]
    rw [hcG_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, LieHom.map_lie]
  let χ : ofTwoCocycle c₀ →ₗ[K] K :=
    (TrivialLieModule.equiv K (loopAlgebra K ℤ L) K).toLinearMap ∘ₗ
      LinearMap.snd K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) ∘ₗ
      (ofProdLinearEquiv c₀).symm.toLinearMap
  have hχ_apply (x : ofTwoCocycle c₀) :
      χ x = TrivialLieModule.equiv K (loopAlgebra K ℤ L) K ((ofProd c₀).symm x).2 := by
    simp only [χ, LinearMap.comp_apply, LinearEquiv.coe_coe, coe_ofProdLinearEquiv_symm,
      LinearMap.snd_apply]
  have hχ_lie (x y : ofTwoCocycle c₀) :
      χ ⁅x, y⁆ = residuePairing K ℤ L Φ (ofTwoCocycle.proj c₀ x) (ofTwoCocycle.proj c₀ y) := by
    obtain ⟨⟨px, zx⟩, rfl⟩ := (ofProd c₀).surjective x
    obtain ⟨⟨py, zy⟩, rfl⟩ := (ofProd c₀).surjective y
    simp only [hχ_apply, bracket_ofTwoCocycle, Equiv.symm_apply_apply, trivial_lie_zero, sub_zero,
      add_zero, ofTwoCocycle.proj_apply]
    simp only [c₀, twoCocycleOfBilinear_coe, twoCochain_val_apply, twoCochainOfBilinear_apply_apply,
      LinearEquiv.apply_symm_apply]
  have hpair_sum :
      ∑ k : Fin n, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) = 1 := by
    have h1 : χ (centralElement c₀) = 1 := by
      simp only [hχ_apply, ofTwoCocycle.ofProd_symm_centralElement, LinearEquiv.apply_symm_apply]
    have h2 : χ (f cG) =
        ∑ k : Fin n, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) := by
      calc χ (f cG)
          = χ (f (∑ k : Fin n, a k • ⁅u k, v k⁆)) := by rw [hcG_sum]
        _ = ∑ k : Fin n, a k * residuePairing K ℤ L Φ (π (u k)) (π (v k)) := by
            simp only [map_sum, map_smul, smul_eq_mul, LieHom.map_lie, hχ_lie, hπ_apply]
        _ = ∑ k : Fin n, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [hπQ_q, hπQ_q]
    calc ∑ k : Fin n, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k)))
        = χ (f cG) := h2.symm
      _ = χ (centralElement c₀) := congrArg χ hcG_map
      _ = 1 := h1
  have hpair' :
      ∑ k ∈ Finset.univ, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) ≠ 0 := by
    rw [hpair_sum]
    exact one_ne_zero
  have hZ : Z = ⊥ := eq_bot_of_central_extension_of_loopAlgebra hΦs hspan πQ hπQ_surj
    hker_central hQ_perf Z hZ_le hcQ_ker hcQ_not_Z hcQ_sum hpair'
  refine le_antisymm hJ_le_I fun y hy ↦ ?_
  have hqy : q y ∈ Z := LieIdeal.mem_map hy
  rw [hZ, LieSubmodule.mem_bot] at hqy
  exact LieSubmodule.Quotient.mk_eq_zero'.mp hqy

end UniversalCentralExtension

end TauCeti.LieAlgebra.LoopAlgebra

namespace LieSubalgebra

open _root_.LieAlgebra _root_.LieAlgebra.LoopAlgebra
open _root_.LieAlgebra.ofTwoCocycle (centralElement)
open TauCeti.LieAlgebra.LoopAlgebra

section SplitSimple

variable {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsSimple K L] [LieRing G] [LieAlgebra K G]

/-- **Universal central extension property for a split finite-dimensional simple Lie algebra**:
for any nonzero symmetric invariant bilinear form `Φ` on a split finite-dimensional simple Lie
algebra `L` over a characteristic-zero field `K` (without assuming algebraic closure), any
surjective homomorphism from a perfect Lie algebra `G` onto
`ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)` lifting the central element to a central
element satisfies `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_ofTwoCocycle_of_isSimple
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker := by
  refine lie_top_ker_eq_ker_of_surjective_ofTwoCocycle hΦ hΦs (fun Ψ hΨ ↦ ?_)
    hf hperf hcG_cent hcG_map
  obtain ⟨c, hc⟩ := H.exists_eq_smul_killingForm_of_isSimple hΦ
  obtain ⟨d, hd⟩ := H.exists_eq_smul_killingForm_of_isSimple hΨ
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΦ0 (by simpa using hc)
  refine ⟨d * c⁻¹, ?_⟩
  rw [hd, hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

end SplitSimple

end LieSubalgebra
