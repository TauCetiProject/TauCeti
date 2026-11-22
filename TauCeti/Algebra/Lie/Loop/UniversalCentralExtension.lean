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
import TauCeti.Algebra.Lie.Cochain
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
(`TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle`): for any
surjective Lie algebra homomorphism `f : G →ₗ⁅K⁆ ofTwoCocycle c₀` from a perfect Lie algebra `G`
admitting a central lift `cG` of `centralElement c₀`, the kernel satisfies `⁅⊤, f.ker⁆ = f.ker`.

In particular, when `L` is a split finite-dimensional simple Lie algebra over `K` (without assuming
`K` is algebraically closed), uniqueness of invariant bilinear forms
(`LieSubalgebra.exists_eq_smul_killingForm_of_isSimple`) discharges the spanning
hypothesis automatically for any nonzero symmetric invariant form `Φ`
(`LieSubalgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple`).

## Main results

* `TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle`: universal
  central extension property (`⁅⊤, f.ker⁆ = f.ker`) for perfect covers of `ofTwoCocycle c₀`.
* `LieSubalgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple`:
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

/-- Package a surjective Lie algebra homomorphism `πQ : Q →ₗ⁅K⁆ L` as a bundled `Extension`
whose middle algebra is reducibly `Q`. -/
private abbrev loopExtension {K L Q : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieRing Q] [LieAlgebra K Q] (πQ : Q →ₗ⁅K⁆ L) (hπQ_surj : Function.Surjective πQ) :
    LieAlgebra.Extension K πQ.ker L :=
  ⟨Q, inferInstance, inferInstance, πQ.ker.incl, πQ,
    LieAlgebra.isExtension_of_surjective πQ hπQ_surj⟩

/-- Bracket-evaluation identity for the linear form `ψ = μ ∘ splittingCoordinate + e ∘ η ∘ πQ`
attached to a decomposition of the pushed-forward section cocycle as `t • ω_res + d₁₂ η`. -/
private theorem splittingCoordinate_add_eta_lie
    {K L Q : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LieRing Q] [LieAlgebra K Q]
    {Φ : LinearMap.BilinForm K L} (hΦs : Φ.IsSymm)
    {πQ : Q →ₗ⁅K⁆ loopAlgebra K ℤ L} (hπQ_surj : Function.Surjective πQ)
    (hker_central : ∀ z ∈ πQ.ker, ∀ y : Q, ⁅y, z⁆ = 0)
    (μ : πQ.ker →ₗ[K] K)
    {sec : loopAlgebra K ℤ L →ₗ[K] Q} (hsec : Function.LeftInverse πQ sec)
    (η : oneCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K))
    {t : K}
    (hω_eq :
      letI : IsLieAbelian πQ.ker := ⟨fun a b ↦ Subtype.ext (hker_central _ b.2 _)⟩
      letI := (loopExtension πQ hπQ_surj).ringModuleOf
      letI := (loopExtension πQ hπQ_surj).lieModuleOf
      twoCochainMap ((TrivialLieModule.equiv K (loopAlgebra K ℤ L) K).symm.toLinearMap ∘ₗ μ)
          LieHom.id ((loopExtension πQ hπQ_surj).twoCocycleOf (s := sec) hsec).1 =
        t • twoCochainOfBilinear K ℤ L Φ hΦs +
          d₁₂ K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) η)
    (y₁ y₂ : Q) :
    let e := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
    (μ ∘ₗ (loopExtension πQ hπQ_surj).splittingCoordinate hsec +
      e.toLinearMap ∘ₗ η ∘ₗ πQ.toLinearMap) ⁅y₁, y₂⁆ =
      t * residuePairing K ℤ L Φ (πQ y₁) (πQ y₂) := by
  let : IsLieAbelian πQ.ker := ⟨fun a b ↦ Subtype.ext (hker_central _ b.2 _)⟩
  let := (loopExtension πQ hπQ_surj).ringModuleOf
  let := (loopExtension πQ hπQ_surj).lieModuleOf
  let e := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
  have hbra : ⁅y₁, y₂⁆ = ⁅sec (πQ y₁), sec (πQ y₂)⁆ := by
    have h1 := hker_central (y₁ - sec (πQ y₁)) (by simp [hsec (πQ y₁)]) y₂
    rw [← lie_skew, neg_eq_zero, sub_lie, sub_eq_zero] at h1
    have h2 := hker_central (y₂ - sec (πQ y₂)) (by simp [hsec (πQ y₂)]) (sec (πQ y₁))
    rw [lie_sub, sub_eq_zero] at h2
    exact h1.trans h2
  have hω_eval := congrArg
    (fun c : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) ↦
      e (c (πQ y₁) (πQ y₂))) hω_eq
  simp only [e, twoCochainMap_apply_apply, LieHom.id_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, add_apply_apply, smul_apply_apply,
    twoCochainOfBilinear_apply_apply, d₁₂_apply_apply_ofTrivial, map_add, map_smul, map_neg,
    smul_eq_mul] at hω_eval
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap, LieHom.map_lie]
  rw [hbra, ← (loopExtension πQ hπQ_surj).twoCocycleOf_eq_splittingCoordinate hsec (πQ y₁) (πQ y₂)]
  change μ (((loopExtension πQ hπQ_surj).twoCocycleOf hsec).1 (πQ y₁) (πQ y₂)) +
      e (η ⁅πQ y₁, πQ y₂⁆) = t * residuePairing K ℤ L Φ (πQ y₁) (πQ y₂)
  rw [hω_eval]
  ring

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
    by_contra! h; exact hZ_ne (eq_bot_iff.mpr fun z hz ↦ h z hz)
  have hz₀_ker : z₀ ∈ πQ.ker := hZ_le hz₀Z
  let U : Submodule K πQ.ker := K ∙ (⟨cQ, hcQ_ker⟩ : πQ.ker)
  have hz₀_not_U : (⟨z₀, hz₀_ker⟩ : πQ.ker) ∉ U := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨r, hr⟩
    have hr' : r • cQ = z₀ := congrArg Subtype.val hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hz₀ne (by simpa using hr'.symm)
    exact hcQ_not_Z (by
      rw [show cQ = r⁻¹ • z₀ by rw [← hr', smul_smul, inv_mul_cancel₀ hr0, one_smul]]
      exact Z.smul_mem r⁻¹ hz₀Z)
  have hmk_ne : U.mkQ ⟨z₀, hz₀_ker⟩ ≠ 0 := mt (Submodule.Quotient.mk_eq_zero U).mp hz₀_not_U
  obtain ⟨ν, hν⟩ : ∃ ν : Module.Dual K (πQ.ker ⧸ U), ν (U.mkQ ⟨z₀, hz₀_ker⟩) ≠ 0 := by
    by_contra! h; exact hmk_ne ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  let μ : πQ.ker →ₗ[K] K := ν ∘ₗ U.mkQ
  have hμ_cQ : μ ⟨cQ, hcQ_ker⟩ = 0 := by
    simp [μ, (Submodule.Quotient.mk_eq_zero U).mpr (Submodule.mem_span_singleton_self _)]
  have hμ_z₀ : μ ⟨z₀, hz₀_ker⟩ ≠ 0 := by simpa only [μ, LinearMap.comp_apply] using hν
  have : IsLieAbelian πQ.ker := ⟨fun a b ↦ Subtype.ext (hker_central _ b.2 _)⟩
  let := (loopExtension πQ hπQ_surj).ringModuleOf
  let := (loopExtension πQ hπQ_surj).lieModuleOf
  have : LieModule.IsTrivial (loopAlgebra K ℤ L) πQ.ker := ⟨fun p z ↦ by
    obtain ⟨y, rfl⟩ := (loopExtension πQ hπQ_surj).proj_surjective p
    rw [(loopExtension πQ hπQ_surj).ringModuleOf_bracket_proj,
      show ⁅y, (loopExtension πQ hπQ_surj).toKer z⁆ = 0 from Subtype.ext (hker_central _ z.2 y),
      map_zero]⟩
  obtain ⟨sec, hsec⟩ := LinearMap.exists_rightInverse_of_surjective πQ.toLinearMap
    (LinearMap.range_eq_top.mpr hπQ_surj)
  have hsec_apply : Function.LeftInverse (loopExtension πQ hπQ_surj).proj sec := fun p ↦
    congrArg (fun g : loopAlgebra K ℤ L →ₗ[K] loopAlgebra K ℤ L ↦ g p) hsec
  let e := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
  let ω : twoCochain K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) :=
    twoCochainMap (e.symm.toLinearMap ∘ₗ μ) LieHom.id
      ((loopExtension πQ hπQ_surj).twoCocycleOf hsec_apply).1
  have hω_cocycle : ω ∈ twoCocycle K (loopAlgebra K ℤ L)
      (TrivialLieModule K (loopAlgebra K ℤ L) K) :=
    twoCochainMap_mem_twoCocycle _ LieHom.id ((loopExtension πQ hπQ_surj).twoCocycleOf hsec_apply).2
  have hdecomp : ω ∈ (K ∙ twoCochainOfBilinear K ℤ L Φ hΦs) ⊔
      LinearMap.range (d₁₂ K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K)) := by
    rw [← twoCocycle_eq_span_sup_range_d₁₂ hΦs hspan]; exact hω_cocycle
  obtain ⟨_, hmem_span, _, ⟨η, rfl⟩, hω_eq⟩ := Submodule.mem_sup.mp hdecomp
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem_span
  let ψ : Q →ₗ[K] K :=
    μ ∘ₗ (loopExtension πQ hπQ_surj).splittingCoordinate hsec_apply +
      e.toLinearMap ∘ₗ η ∘ₗ πQ.toLinearMap
  have hψ_lie (y₁ y₂ : Q) : ψ ⁅y₁, y₂⁆ = t * residuePairing K ℤ L Φ (πQ y₁) (πQ y₂) :=
    splittingCoordinate_add_eta_lie hΦs hπQ_surj hker_central μ hsec_apply η hω_eq.symm y₁ y₂
  have hψ_cQ_zero : ψ cQ = 0 := by
    have hc_split : (loopExtension πQ hπQ_surj).splittingCoordinate hsec_apply cQ = ⟨cQ, hcQ_ker⟩ :=
      (loopExtension πQ hπQ_surj).splittingCoordinate_incl hsec_apply ⟨cQ, hcQ_ker⟩
    simp [ψ, hc_split, LieHom.mem_ker.mp hcQ_ker, hμ_cQ]
  have hψ_cQ_sum : ψ cQ = t * ∑ k ∈ s, a k * residuePairing K ℤ L Φ (πQ (u k)) (πQ (v k)) := by
    rw [hcQ_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, hψ_lie]; ring
  have ht0 : t = 0 := (mul_eq_zero.mp (hψ_cQ_sum.symm.trans hψ_cQ_zero)).resolve_right hpair
  have hψ_zero (y : Q) : ψ y = 0 := by
    have hle : (↑(⁅(⊤ : LieIdeal K Q), (⊤ : LieIdeal K Q)⁆ : LieIdeal K Q) : Submodule K Q) ≤
        LinearMap.ker ψ := by
      rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.span_le]
      rintro _ ⟨x₁, _, x₂, _, rfl⟩; simp [hψ_lie, ht0]
    exact hle (by rw [hQ_perf]; trivial)
  have hψ_z₀ : ψ z₀ = μ ⟨z₀, hz₀_ker⟩ := by
    have hz_split : (loopExtension πQ hπQ_surj).splittingCoordinate hsec_apply z₀ = ⟨z₀, hz₀_ker⟩ :=
      (loopExtension πQ hπQ_surj).splittingCoordinate_incl hsec_apply ⟨z₀, hz₀_ker⟩
    simp [ψ, hz_split, LieHom.mem_ker.mp hz₀_ker]
  exact hμ_z₀ (hψ_z₀.symm.trans (hψ_zero z₀))

/-- **Universal central extension property of the residue central extension**:
let `L` be a Lie algebra with nondegenerate Killing form over a field `K` of characteristic zero
whose invariant bilinear forms are all scalar multiples of a symmetric invariant form `Φ`, and let
`c₀ = twoCocycleOfBilinear K ℤ L Φ hΦ hΦs`. Suppose `f : G →ₗ⁅K⁆ ofTwoCocycle c₀` is a surjective
Lie algebra homomorphism from a perfect Lie algebra `G` (`⁅⊤, ⊤⁆ = ⊤`) admitting a central element
`cG` with `f cG = centralElement c₀`. Then `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle
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
      refine ⟨TrivialLieModule.equiv K (loopAlgebra K ℤ L) K ((ofProd c₀).symm (f y)).snd,
        LieHom.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, hcG_map, sub_eq_zero]
      have hdecomp := ofTwoCocycle.ofProd_eq_add_smul_centralElement c₀
        ((ofProd c₀).symm (f y)).fst ((ofProd c₀).symm (f y)).snd
      rw [Prod.mk.eta, Equiv.apply_symm_apply] at hdecomp
      have h1 : ((ofProd c₀).symm (f y)).fst = 0 := by rwa [← ofTwoCocycle.proj_apply]
      rw [h1, show ofProd c₀ (0, 0) = 0 from of_zero c₀, zero_add] at hdecomp
      exact hdecomp
    · rintro ⟨r, hr⟩
      have hfy : f y = r • centralElement c₀ :=
        sub_eq_zero.mp (by simpa [map_sub, map_smul, hcG_map] using LieHom.mem_ker.mp hr)
      simp [hfy, ofTwoCocycle.proj_apply]
  have hJ_le_I : J ≤ I := LieSubmodule.lie_le_right _ _
  have hI_le_ker : I ≤ π.ker := fun y hy ↦ (hker_π y).mpr ⟨0, by simpa using hy⟩
  let q : G →ₗ⁅K⁆ G ⧸ J := J.mkQ
  let πQ : G ⧸ J →ₗ⁅K⁆ loopAlgebra K ℤ L := J.liftQ π (le_trans hJ_le_I hI_le_ker)
  have hπQ_q (y : G) : πQ (q y) = π y := LieHom.congr_fun (J.liftQ_mkQ π _) y
  have hπQ_surj : Function.Surjective πQ := fun p ↦
    let ⟨y, hy⟩ := hπ_surj p; ⟨q y, (hπQ_q y).trans hy⟩
  let Z : LieIdeal K (G ⧸ J) := LieIdeal.map q I
  let cQ : G ⧸ J := q cG
  have hker_central : ∀ z ∈ πQ.ker, ∀ y : G ⧸ J, ⁅y, z⁆ = 0 := by
    intro z hz y
    obtain ⟨w, rfl⟩ := J.surjective_mkQ y
    obtain ⟨x, rfl⟩ := J.surjective_mkQ z
    obtain ⟨r, hr⟩ := (hker_π x).mp (by rwa [LieHom.mem_ker, ← hπQ_q])
    have hbra : ⁅w, x⁆ ∈ J := by
      rw [show x = (x - r • cG) + r • cG by abel, lie_add, lie_smul, hcG_cent w, smul_zero,
        add_zero]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top w) hr
    rw [← LieHom.map_lie]
    exact LieSubmodule.Quotient.mk_eq_zero'.mpr hbra
  have hQ_perf : (⁅(⊤ : LieIdeal K (G ⧸ J)), (⊤ : LieIdeal K (G ⧸ J))⁆ :
      LieIdeal K (G ⧸ J)) = ⊤ := by
    have htop : LieIdeal.map q ⊤ = ⊤ := by
      rw [← q.idealRange_eq_map]; exact q.idealRange_eq_top_of_surjective J.surjective_mkQ
    rw [← htop, ← LieIdeal.map_bracket_eq q J.surjective_mkQ, hperf, htop]
  have hZ_le : Z ≤ πQ.ker := fun z hz ↦ by
    obtain ⟨⟨x, hxI⟩, rfl⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hz
    rw [LieHom.mem_ker, hπQ_q]; exact hI_le_ker hxI
  have hcQ_ker : cQ ∈ πQ.ker := by rw [LieHom.mem_ker, hπQ_q]; exact (hker_π cG).mpr ⟨1, by simp⟩
  have hcQ_not_Z : cQ ∉ Z := fun hcZ ↦ by
    obtain ⟨⟨x, hxI⟩, hxq⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hcZ
    have h0 : q (cG - x) = 0 := by rw [map_sub, hxq, sub_self]
    have hdiff : cG - x ∈ J := LieSubmodule.Quotient.mk_eq_zero'.mp h0
    have hcI : cG ∈ I := by
      rw [show cG = (cG - x) + x by abel]; exact add_mem (hJ_le_I hdiff) hxI
    exact ofTwoCocycle.centralElement_ne_zero c₀ (hcG_map ▸ LieHom.mem_ker.mp hcI)
  have hcG_mem : cG ∈ Submodule.span K {z : G | ∃ u v : G, ⁅u, v⁆ = z} := by
    have hcG_top : cG ∈ (↑(⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) :
        Submodule K G) := by rw [hperf]; trivial
    rw [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hcG_top
    simpa only [LieSubmodule.mem_top, true_and] using hcG_top
  obtain ⟨n, a, g, hg_sum⟩ := Submodule.mem_span_set'.mp hcG_mem
  choose u v huv using fun k : Fin n ↦ (g k).property
  have hcG_sum : cG = ∑ k : Fin n, a k • ⁅u k, v k⁆ := by
    rw [← hg_sum]; exact Finset.sum_congr rfl fun k _ ↦ by rw [huv k]
  have hcQ_sum : cQ = ∑ k ∈ Finset.univ, a k • ⁅q (u k), q (v k)⁆ := by
    simp [cQ, hcG_sum, map_sum]
  let χ : ofTwoCocycle c₀ →ₗ[K] K :=
    (TrivialLieModule.equiv K (loopAlgebra K ℤ L) K).toLinearMap ∘ₗ
      LinearMap.snd K (loopAlgebra K ℤ L) (TrivialLieModule K (loopAlgebra K ℤ L) K) ∘ₗ
      (ofProdLinearEquiv c₀).symm.toLinearMap
  have hχ_apply (x : ofTwoCocycle c₀) :
      χ x = TrivialLieModule.equiv K (loopAlgebra K ℤ L) K ((ofProd c₀).symm x).snd := by
    simp only [χ, LinearMap.comp_apply, LinearEquiv.coe_coe, coe_ofProdLinearEquiv_symm,
      LinearMap.snd_apply]
  have hχ_lie (x y : ofTwoCocycle c₀) :
      χ ⁅x, y⁆ = residuePairing K ℤ L Φ (ofTwoCocycle.proj c₀ x) (ofTwoCocycle.proj c₀ y) := by
    obtain ⟨⟨px, zx⟩, rfl⟩ := (ofProd c₀).surjective x
    obtain ⟨⟨py, zy⟩, rfl⟩ := (ofProd c₀).surjective y
    simp [hχ_apply, bracket_ofTwoCocycle, c₀, trivial_lie_zero]
  have hpair_sum :
      ∑ k : Fin n, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) = 1 := by
    have h1 : χ (centralElement c₀) = 1 := by simp [hχ_apply]
    have h2 : χ (f cG) =
        ∑ k : Fin n, a k * residuePairing K ℤ L Φ (πQ (q (u k))) (πQ (q (v k))) := by
      simp only [hcG_sum, map_sum, map_smul, smul_eq_mul, LieHom.map_lie, hχ_lie, hπ_apply, hπQ_q]
    rw [← h2, hcG_map, h1]
  have hZ : Z = ⊥ := eq_bot_of_central_extension_of_loopAlgebra hΦs hspan πQ hπQ_surj
    hker_central hQ_perf Z hZ_le hcQ_ker hcQ_not_Z hcQ_sum (by rw [hpair_sum]; exact one_ne_zero)
  refine le_antisymm hJ_le_I fun y hy ↦ LieSubmodule.Quotient.mk_eq_zero'.mp ?_
  have hqy : q y ∈ Z := LieIdeal.mem_map hy
  rwa [hZ, LieSubmodule.mem_bot] at hqy

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
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker := by
  refine lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle hΦ hΦs (fun Ψ hΨ ↦ ?_)
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
