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
-- Proof-only: dual separation, H² classification on loops, quotient lifts, perfectness, and form
-- uniqueness.
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Lie.BaseChange.Perfect
import TauCeti.Algebra.Lie.Cochain
import TauCeti.Algebra.Lie.Loop.Cocycle
import TauCeti.Algebra.Lie.Quotient
import TauCeti.Algebra.Lie.Weights.IsSimple

/-!
# Universal central extension property for 1-dimensional central extensions

For a field `K` and a Lie algebra `L₀` whose scalar 2-cocycle `c₀` generates `H²(L₀, K)` (modulo
coboundaries), `TauCeti.LieAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle` shows that
any surjective homomorphism `f : G →ₗ⁅K⁆ ofTwoCocycle c₀` from a perfect Lie algebra `G` admitting
a central lift of `centralElement c₀` satisfies `⁅⊤, f.ker⁆ = f.ker`.

Specializing via `twoCocycle_eq_span_sup_range_d₁₂` and `exists_eq_smul_killingForm_of_isSimple`
yields `TauCeti.LieAlgebra.LoopAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle` and
`LieSubalgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple`.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §7.4.
* C. Kassel, *Kähler differentials and coverings of complex simple Lie algebras extended over a
  commutative algebra*, J. Pure Appl. Algebra 34 (1984), 265–275.
-/

public section

noncomputable section

open _root_.LieAlgebra _root_.LieModule.Cohomology
open _root_.LieAlgebra.ofTwoCocycle (centralElement)

namespace TauCeti.LieAlgebra

section UniversalCentralExtension

/-- Package a surjective `πQ : Q →ₗ⁅K⁆ L₀` as an `Extension` with middle algebra `Q`. -/
private abbrev quotientExtension {K L₀ Q : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀]
    [LieRing Q] [LieAlgebra K Q] (πQ : Q →ₗ⁅K⁆ L₀) (hπQ : Function.Surjective πQ) :
    LieAlgebra.Extension K πQ.ker L₀ :=
  ⟨Q, inferInstance, inferInstance, πQ.ker.incl, πQ, LieAlgebra.isExtension_of_surjective πQ hπQ⟩

/-- Bracket-evaluation identity for `ψ = μ ∘ splittingCoordinate + e ∘ η ∘ πQ` attached to a
decomposition `t • c₀ + d₁₂ η` of the pushed-forward section cocycle. -/
private theorem splittingCoordinate_add_eta_lie
    {K L₀ Q : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀] [LieRing Q] [LieAlgebra K Q]
    (c₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K))
    {πQ : Q →ₗ⁅K⁆ L₀} (hπQ : Function.Surjective πQ)
    (hcent : ∀ z ∈ πQ.ker, ∀ y : Q, ⁅y, z⁆ = 0) (μ : πQ.ker →ₗ[K] K)
    {sec : L₀ →ₗ[K] Q} (hsec : Function.LeftInverse πQ sec)
    (η : oneCochain K L₀ (TrivialLieModule K L₀ K)) {t : K}
    (hω :
      letI : IsLieAbelian πQ.ker := ⟨fun _ b ↦ Subtype.ext (hcent _ b.property _)⟩
      letI := (quotientExtension πQ hπQ).ringModuleOf
      letI := (quotientExtension πQ hπQ).lieModuleOf
      twoCochainMap ((TrivialLieModule.equiv K L₀ K).symm.toLinearMap ∘ₗ μ) LieHom.id
          ((quotientExtension πQ hπQ).twoCocycleOf (s := sec) hsec).val =
        t • (c₀ : twoCochain K L₀ _) + d₁₂ K L₀ (TrivialLieModule K L₀ K) η)
    (y₁ y₂ : Q) :
    let e := TrivialLieModule.equiv K L₀ K
    (μ ∘ₗ (quotientExtension πQ hπQ).splittingCoordinate hsec +
      e.toLinearMap ∘ₗ η ∘ₗ πQ.toLinearMap) ⁅y₁, y₂⁆ =
      t * e ((c₀ : twoCochain K L₀ _) (πQ y₁) (πQ y₂)) := by
  let : IsLieAbelian πQ.ker := ⟨fun _ b ↦ Subtype.ext (hcent _ b.property _)⟩
  let := (quotientExtension πQ hπQ).ringModuleOf
  let := (quotientExtension πQ hπQ).lieModuleOf
  let e := TrivialLieModule.equiv K L₀ K
  have hbra : ⁅y₁, y₂⁆ = ⁅sec (πQ y₁), sec (πQ y₂)⁆ := by
    have h1 := hcent (y₁ - sec (πQ y₁)) (by simp [hsec (πQ y₁)]) y₂
    rw [← lie_skew, neg_eq_zero, sub_lie, sub_eq_zero] at h1
    have h2 := hcent (y₂ - sec (πQ y₂)) (by simp [hsec (πQ y₂)]) (sec (πQ y₁))
    rw [lie_sub, sub_eq_zero] at h2
    exact h1.trans h2
  have hω_eval := congrArg
    (fun c : twoCochain K L₀ (TrivialLieModule K L₀ K) ↦ e (c (πQ y₁) (πQ y₂))) hω
  simp only [e, twoCochainMap_apply_apply, LieHom.id_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, add_apply_apply, smul_apply_apply,
    d₁₂_apply_apply_ofTrivial, map_add, map_smul, map_neg, smul_eq_mul] at hω_eval
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LieHom.coe_toLinearMap, LieHom.map_lie]
  rw [hbra, ← (quotientExtension πQ hπQ).twoCocycleOf_eq_splittingCoordinate hsec (πQ y₁) (πQ y₂),
    twoCochain_val_apply, hω_eval]
  ring

/-- Extend `μ : πQ.ker →ₗ[K] K` on a central extension `πQ : Q →ₗ⁅K⁆ L₀` to `ψ : Q →ₗ[K] K`
evaluating brackets via a multiple of `c₀` when `c₀` spans `H²(L₀, K)`. -/
private theorem exists_linearMap_lie_eq_mul_of_twoCocycle_eq
    {K L₀ Q : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀] [LieRing Q] [LieAlgebra K Q]
    (c₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K))
    (hc₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K) =
      (K ∙ (c₀ : twoCochain K L₀ _)) ⊔ LinearMap.range (d₁₂ K L₀ _))
    (πQ : Q →ₗ⁅K⁆ L₀) (hπQ : Function.Surjective πQ)
    (hcent : ∀ z ∈ πQ.ker, ∀ y : Q, ⁅y, z⁆ = 0) (μ : πQ.ker →ₗ[K] K) :
    ∃ (ψ : Q →ₗ[K] K) (t : K), (∀ x (hx : x ∈ πQ.ker), ψ x = μ ⟨x, hx⟩) ∧
      (∀ y₁ y₂ : Q, ψ ⁅y₁, y₂⁆ =
        t * TrivialLieModule.equiv K L₀ K ((c₀ : twoCochain K L₀ _) (πQ y₁) (πQ y₂))) := by
  have : IsLieAbelian πQ.ker := ⟨fun _ b ↦ Subtype.ext (hcent _ b.property _)⟩
  let := (quotientExtension πQ hπQ).ringModuleOf
  let := (quotientExtension πQ hπQ).lieModuleOf
  have : LieModule.IsTrivial L₀ πQ.ker := ⟨fun p z ↦ by
    obtain ⟨y, rfl⟩ := (quotientExtension πQ hπQ).proj_surjective p
    have hyz : ⁅y, (quotientExtension πQ hπQ).toKer z⁆ = 0 := Subtype.ext (hcent _ z.property y)
    rw [(quotientExtension πQ hπQ).ringModuleOf_bracket_proj, hyz, map_zero]⟩
  obtain ⟨sec, hsec⟩ := LinearMap.exists_rightInverse_of_surjective πQ.toLinearMap
    (LinearMap.range_eq_top.mpr hπQ)
  have hsec' : Function.LeftInverse (quotientExtension πQ hπQ).proj sec :=
    fun p ↦ congrArg (fun g : L₀ →ₗ[K] L₀ ↦ g p) hsec
  let e := TrivialLieModule.equiv K L₀ K
  have hω := twoCochainMap_mem_twoCocycle (e.symm.toLinearMap ∘ₗ μ) LieHom.id
    ((quotientExtension πQ hπQ).twoCocycleOf hsec').property
  rw [hc₀] at hω
  obtain ⟨_, hmem, _, ⟨η, rfl⟩, hω_eq⟩ := Submodule.mem_sup.mp hω
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨μ ∘ₗ (quotientExtension πQ hπQ).splittingCoordinate hsec' +
      e.toLinearMap ∘ₗ η ∘ₗ πQ.toLinearMap, t, fun x hx ↦ ?_,
    splittingCoordinate_add_eta_lie c₀ hπQ hcent μ hsec' η hω_eq.symm⟩
  have hsplit : (quotientExtension πQ hπQ).splittingCoordinate hsec' x = ⟨x, hx⟩ :=
    (quotientExtension πQ hπQ).splittingCoordinate_incl hsec' ⟨x, hx⟩
  simp [hsplit, LieHom.mem_ker.mp hx]

/-- Dual-separation criterion: if `c₀` spans `H²(L₀, K)`, any central ideal `Z ≤ πQ.ker` missing
a bracket-sum lift `cQ` with nonzero `c₀`-pairing is `⊥`. -/
private theorem eq_bot_of_central_extension
    {K L₀ Q : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀] [LieRing Q] [LieAlgebra K Q]
    (c₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K))
    (hc₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K) =
      (K ∙ (c₀ : twoCochain K L₀ _)) ⊔ LinearMap.range (d₁₂ K L₀ _))
    (πQ : Q →ₗ⁅K⁆ L₀) (hπQ : Function.Surjective πQ)
    (hcent : ∀ z ∈ πQ.ker, ∀ y : Q, ⁅y, z⁆ = 0) (hQ : derivedSeries K Q 1 = ⊤)
    (Z : LieIdeal K Q) (hZ : Z ≤ πQ.ker) {cQ : Q} (hcQ : cQ ∈ πQ.ker) (hcQZ : cQ ∉ Z)
    {ι : Type*} {s : Finset ι} {a : ι → K} {u v : ι → Q}
    (hsum : cQ = ∑ k ∈ s, a k • ⁅u k, v k⁆)
    (hpair : ∑ k ∈ s, a k * TrivialLieModule.equiv K L₀ K
      ((c₀ : twoCochain K L₀ _) (πQ (u k)) (πQ (v k))) ≠ 0) :
    Z = ⊥ := by
  by_contra hZ_ne
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ : ∃ z₀ ∈ Z, z₀ ≠ 0 := by
    by_contra! h; exact hZ_ne (eq_bot_iff.mpr fun z hz ↦ h z hz)
  let U : Submodule K πQ.ker := K ∙ (⟨cQ, hcQ⟩ : πQ.ker)
  have hz₀_not_U : (⟨z₀, hZ hz₀Z⟩ : πQ.ker) ∉ U := by
    rw [Submodule.mem_span_singleton]; rintro ⟨r, hr⟩
    have hr' : r • cQ = z₀ := congrArg Subtype.val hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hz₀ne (by simpa using hr'.symm)
    have hcQ_eq : cQ = r⁻¹ • z₀ := by
      rw [← hr', smul_smul, inv_mul_cancel₀ hr0, one_smul]
    exact hcQZ (hcQ_eq ▸ Z.smul_mem r⁻¹ hz₀Z)
  obtain ⟨μ, hμ_z₀, hU_bot⟩ := U.exists_dual_map_eq_bot_of_notMem hz₀_not_U inferInstance
  have hμ_cQ : μ ⟨cQ, hcQ⟩ = 0 := by
    rw [← Submodule.mem_bot (R := K), ← hU_bot]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  obtain ⟨ψ, t, hψ_ker, hψ_lie⟩ :=
    exists_linearMap_lie_eq_mul_of_twoCocycle_eq c₀ hc₀ πQ hπQ hcent μ
  have hψ_cQ_sum : ψ cQ = t * ∑ k ∈ s, a k *
      TrivialLieModule.equiv K L₀ K ((c₀ : twoCochain K L₀ _) (πQ (u k)) (πQ (v k))) := by
    rw [hsum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, hψ_lie]; ring
  have ht0 : t = 0 := (mul_eq_zero.mp
    (hψ_cQ_sum.symm.trans (by rw [hψ_ker cQ hcQ, hμ_cQ]))).resolve_right hpair
  have hle : Submodule.span K {⁅x₁, x₂⁆ | (x₁ : Q) (x₂ : Q)} ≤ LinearMap.ker ψ :=
    Submodule.span_le.mpr <| by rintro _ ⟨x₁, x₂, rfl⟩; simp [hψ_lie, ht0]
  exact hμ_z₀ (by
    rw [← hψ_ker z₀ (hZ hz₀Z)]; exact hle (mem_span_lie_of_derivedSeries_one_eq_top hQ z₀))

/-- In `G ⧸ ⁅⊤, f.ker⁆`, the kernel of the induced map to `L₀` is central. -/
private theorem quotient_ker_liftQ_central
    {K L₀ G : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀] [LieRing G] [LieAlgebra K G]
    {c₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K)} {f : G →ₗ⁅K⁆ ofTwoCocycle c₀}
    {cG : G} (hcG : ∀ y : G, ⁅y, cG⁆ = 0)
    (hker : ∀ y : G,
      y ∈ ((ofTwoCocycle.proj c₀).comp f).ker ↔ ∃ r : K, y - r • cG ∈ f.ker)
    (hJ : ⁅(⊤ : LieIdeal K G), f.ker⁆ ≤ ((ofTwoCocycle.proj c₀).comp f).ker) :
    let J := ⁅(⊤ : LieIdeal K G), f.ker⁆
    ∀ z ∈ (J.liftQ ((ofTwoCocycle.proj c₀).comp f) hJ).ker,
      ∀ y : G ⧸ J, ⁅y, z⁆ = 0 := by
  intro J z hz y
  obtain ⟨w, rfl⟩ := J.surjective_mkQ y; obtain ⟨x, rfl⟩ := J.surjective_mkQ z
  obtain ⟨r, hr⟩ := (hker x).mp (by
    simpa [LieHom.mem_ker, LieHom.congr_fun (J.liftQ_mkQ _ hJ) x] using hz)
  rw [← LieHom.map_lie]
  refine LieSubmodule.Quotient.mk_eq_zero'.mpr ?_
  rw [← sub_add_cancel x (r • cG), lie_add, lie_smul, hcG w, smul_zero, add_zero]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top w) hr

/-- Express a central lift `cG` of `centralElement c₀` in a perfect Lie algebra as a bracket sum
whose `c₀`-pairing is `1`. -/
private theorem exists_bracket_sum_pairing_eq_one
    {K L₀ G : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀] [LieRing G] [LieAlgebra K G]
    {c₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K)} {f : G →ₗ⁅K⁆ ofTwoCocycle c₀}
    (hperf : derivedSeries K G 1 = ⊤) {cG : G} (hcG : f cG = centralElement c₀) :
    ∃ (n : ℕ) (a : Fin n → K) (u v : Fin n → G),
      cG = ∑ k : Fin n, a k • ⁅u k, v k⁆ ∧
      ∑ k : Fin n, a k * TrivialLieModule.equiv K L₀ K
        ((c₀ : twoCochain K L₀ _) (ofTwoCocycle.proj c₀ (f (u k)))
          (ofTwoCocycle.proj c₀ (f (v k)))) = 1 := by
  obtain ⟨n, a, g, hg⟩ :=
    Submodule.mem_span_set'.mp (mem_span_lie_of_derivedSeries_one_eq_top hperf cG)
  choose u v huv using fun k : Fin n ↦ (g k).property
  have hsum : cG = ∑ k : Fin n, a k • ⁅u k, v k⁆ := by
    rw [← hg]; exact Finset.sum_congr rfl fun k _ ↦ by rw [huv k]
  let χ : ofTwoCocycle c₀ →ₗ[K] K := (TrivialLieModule.equiv K L₀ K).toLinearMap ∘ₗ
    LinearMap.snd K L₀ (TrivialLieModule K L₀ K) ∘ₗ
    (ofProdLinearEquiv c₀).symm.toLinearMap
  have hχ_lie (x y : ofTwoCocycle c₀) : χ ⁅x, y⁆ = TrivialLieModule.equiv K L₀ K
      ((c₀ : twoCochain K L₀ _) (ofTwoCocycle.proj c₀ x) (ofTwoCocycle.proj c₀ y)) := by
    obtain ⟨⟨px, zx⟩, rfl⟩ := (ofProd c₀).surjective x
    obtain ⟨⟨py, zy⟩, rfl⟩ := (ofProd c₀).surjective y
    simp [χ, bracket_ofTwoCocycle, trivial_lie_zero]
  refine ⟨n, a, u, v, hsum, ?_⟩
  have h2 : χ (f cG) = ∑ k : Fin n, a k * TrivialLieModule.equiv K L₀ K
      ((c₀ : twoCochain K L₀ _) (ofTwoCocycle.proj c₀ (f (u k)))
        (ofTwoCocycle.proj c₀ (f (v k)))) := by
    simp only [hsum, map_sum, map_smul, smul_eq_mul, LieHom.map_lie, hχ_lie]
  simpa [χ, hcG] using h2.symm

/-- **Universal central extension property for `ofTwoCocycle c₀`**: if every scalar 2-cocycle on
`L₀` is a multiple of `c₀` modulo coboundaries, any surjective homomorphism
`f : G →ₗ⁅K⁆ ofTwoCocycle c₀` from a perfect Lie algebra `G` admitting a central lift `cG` of
`centralElement c₀` satisfies `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle
    {K L₀ G : Type*} [Field K] [LieRing L₀] [LieAlgebra K L₀] [LieRing G] [LieAlgebra K G]
    {c₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K)}
    (hc₀ : twoCocycle K L₀ (TrivialLieModule K L₀ K) =
      (K ∙ (c₀ : twoCochain K L₀ _)) ⊔ LinearMap.range (d₁₂ K L₀ _))
    {f : G →ₗ⁅K⁆ ofTwoCocycle c₀} (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0) (hcG_map : f cG = centralElement c₀) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker := by
  let I : LieIdeal K G := f.ker
  let J : LieIdeal K G := ⁅(⊤ : LieIdeal K G), I⁆
  let π : G →ₗ⁅K⁆ L₀ := (ofTwoCocycle.proj c₀).comp f
  have hker_π (y : G) : y ∈ π.ker ↔ ∃ r : K, y - r • cG ∈ I := by
    rw [LieHom.mem_ker, LieHom.comp_apply]
    refine ⟨fun h0 ↦ ⟨TrivialLieModule.equiv K L₀ K ((ofProd c₀).symm (f y)).snd,
      LieHom.mem_ker.mpr ?_⟩, fun ⟨r, hr⟩ ↦ by
      have hfy : f y = r • centralElement c₀ :=
        sub_eq_zero.mp (by simpa [map_sub, map_smul, hcG_map] using LieHom.mem_ker.mp hr)
      simp [hfy, ofTwoCocycle.proj_apply]⟩
    rw [map_sub, map_smul, hcG_map, sub_eq_zero]
    have hd := ofTwoCocycle.ofProd_eq_add_smul_centralElement c₀
      ((ofProd c₀).symm (f y)).fst ((ofProd c₀).symm (f y)).snd
    rw [Prod.mk.eta, Equiv.apply_symm_apply, show ((ofProd c₀).symm (f y)).fst = 0 from by
      rwa [← ofTwoCocycle.proj_apply], Prod.mk_zero_zero, of_zero c₀, zero_add] at hd
    exact hd
  have hJ_le_I : J ≤ I := LieSubmodule.lie_le_right _ _
  have hI_le_ker : I ≤ π.ker := fun y hy ↦ (hker_π y).mpr ⟨0, by simpa using hy⟩
  let q : G →ₗ⁅K⁆ G ⧸ J := J.mkQ
  let πQ : G ⧸ J →ₗ⁅K⁆ L₀ := J.liftQ π (le_trans hJ_le_I hI_le_ker)
  have hπQ_q (y : G) : πQ (q y) = π y := LieHom.congr_fun (J.liftQ_mkQ π _) y
  have hπQ_surj : Function.Surjective πQ := fun p ↦
    let ⟨y, hy⟩ := ((ofTwoCocycle.proj_surjective c₀).comp hf) p; ⟨q y, (hπQ_q y).trans hy⟩
  let Z : LieIdeal K (G ⧸ J) := LieIdeal.map q I
  have hG_perf : derivedSeries K G 1 = ⊤ := hperf
  have hQ_perf : derivedSeries K (G ⧸ J) 1 = ⊤ := by
    rw [← LieIdeal.derivedSeries_map_eq 1 J.surjective_mkQ, hG_perf, ← q.idealRange_eq_map,
      q.idealRange_eq_top_of_surjective J.surjective_mkQ]
  have hZ_le : Z ≤ πQ.ker := fun z hz ↦ by
    obtain ⟨⟨x, hxI⟩, rfl⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hz
    rw [LieHom.mem_ker, hπQ_q]; exact hI_le_ker hxI
  have hcQ_not_Z : q cG ∉ Z := fun hcZ ↦ by
    obtain ⟨⟨x, hxI⟩, hxq⟩ := LieIdeal.mem_map_of_surjective J.surjective_mkQ hcZ
    have h0 : q (cG - x) = 0 := by rw [map_sub, hxq, sub_self]
    exact ofTwoCocycle.centralElement_ne_zero c₀ (hcG_map ▸ LieHom.mem_ker.mp
      (sub_add_cancel cG x ▸ add_mem (hJ_le_I (LieSubmodule.Quotient.mk_eq_zero'.mp h0)) hxI))
  obtain ⟨n, a, u, v, hcG_sum, hpair_sum⟩ := exists_bracket_sum_pairing_eq_one hG_perf hcG_map
  have hcQ_sum : q cG = ∑ k ∈ Finset.univ, a k • ⁅q (u k), q (v k)⁆ := by simp [hcG_sum, map_sum]
  have hpair_ne : ∑ k ∈ Finset.univ, a k * TrivialLieModule.equiv K L₀ K
      ((c₀ : twoCochain K L₀ _) (πQ (q (u k))) (πQ (q (v k)))) ≠ 0 := by
    simp only [hπQ_q, π, LieHom.comp_apply]; rw [hpair_sum]; exact one_ne_zero
  have hZ : Z = ⊥ := eq_bot_of_central_extension c₀ hc₀ πQ hπQ_surj
    (quotient_ker_liftQ_central hcG_cent hker_π (le_trans hJ_le_I hI_le_ker)) hQ_perf Z hZ_le
    (by rw [LieHom.mem_ker, hπQ_q]; exact (hker_π cG).mpr ⟨1, by simp⟩) hcQ_not_Z
    hcQ_sum hpair_ne
  refine le_antisymm hJ_le_I fun y hy ↦ LieSubmodule.Quotient.mk_eq_zero'.mp ?_
  have hqy : q y ∈ Z := LieIdeal.mem_map hy
  rwa [hZ, LieSubmodule.mem_bot] at hqy

end UniversalCentralExtension

namespace LoopAlgebra

open _root_.LieAlgebra.LoopAlgebra

/-- **Universal central extension property of the residue central extension**:
for a Lie algebra `L` with nondegenerate Killing form over a characteristic-zero field `K` whose
invariant bilinear forms are scalar multiples of a symmetric invariant form `Φ`, any surjective
`f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)` from a perfect Lie algebra `G`
lifting `centralElement` to a central element satisfies `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle
    {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsKilling K L] [LieRing G] [LieAlgebra K G]
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    {f : G →ₗ⁅K⁆ ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)}
    (hf : Function.Surjective f)
    (hperf : (⁅(⊤ : LieIdeal K G), (⊤ : LieIdeal K G)⁆ : LieIdeal K G) = ⊤)
    {cG : G} (hcG_cent : ∀ y : G, ⁅y, cG⁆ = 0)
    (hcG_map : f cG = centralElement (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)) :
    ⁅(⊤ : LieIdeal K G), f.ker⁆ = f.ker :=
  TauCeti.LieAlgebra.lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle
    (by rw [twoCocycleOfBilinear_coe]; exact twoCocycle_eq_span_sup_range_d₁₂ hΦs hspan)
    hf hperf hcG_cent hcG_map

end LoopAlgebra

end TauCeti.LieAlgebra

namespace LieSubalgebra

open _root_.LieAlgebra _root_.LieAlgebra.LoopAlgebra
open _root_.LieAlgebra.ofTwoCocycle (centralElement)
open TauCeti.LieAlgebra.LoopAlgebra

/-- **Universal central extension property for a split finite-dimensional simple Lie algebra**:
for any nonzero symmetric invariant bilinear form `Φ` on a split finite-dimensional simple Lie
algebra `L` over a characteristic-zero field `K` (without assuming algebraic closure), any
surjective homomorphism from a perfect Lie algebra `G` onto
`ofTwoCocycle (twoCocycleOfBilinear K ℤ L Φ hΦ hΦs)` lifting the central element to a central
element satisfies `⁅⊤, f.ker⁆ = f.ker`. -/
theorem lie_top_ker_eq_ker_of_surjective_to_ofTwoCocycle_of_isSimple
    {K L G : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [IsSimple K L] [LieRing G] [LieAlgebra K G] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0)
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
  have hc0 : c ≠ 0 := by rintro rfl; exact hΦ0 (by simpa using hc)
  exact ⟨d * c⁻¹, by rw [hd, hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]⟩

end LieSubalgebra
