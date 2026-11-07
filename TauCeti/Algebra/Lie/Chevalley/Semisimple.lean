/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Transport
public import TauCeti.Algebra.Lie.Weights.Root.IntegralBasis
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Vector

/-!
# Realizing Chevalley structure constants from a Killing Chevalley system

Given a finite-dimensional Killing Lie algebra `L` over a characteristic-zero field `K`, a
splitting Cartan subalgebra `H`, and `hx : TauCeti.IsChevalleySystem ω x`, this file extracts a
`RootPairing.ChevalleyConstants P` table on any integral root datum `P : RootPairing ι ℤ X Y`
equipped with `e : ι ≃ H.root` satisfying `(rootSystem H).pairingIn ℤ (e i) (e j) = P.pairing i j`,
without assuming that roots or coroots span `X` or `Y`. A compatible cocharacter map `γ : Y →ₗ[ℤ] H`
landing in `hx.chevalleyLieLattice` induces `toChevalleyLieLattice`, which upgrades to
`toChevalleyLieLatticeEquiv` when `Y` is free on simple coroots; specializing to
`TauCeti.DynkinType.isChevalleySystem_chevalleySystem` treats every valid `TauCeti.DynkinType`.

## Main definitions and results

* `TauCeti.IsChevalleySystem.chevalleyConstants`,
  `TauCeti.IsChevalleySystem.lie_eq_chevalleyConstants_structConst_zsmul`: Chevalley constants on
  `P` extracted from `hx` along `e`.
* `TauCeti.IsChevalleySystem.toChevalleyLieLattice`,
  `TauCeti.IsChevalleySystem.toChevalleyLieLatticeEquiv`: comparison with `hx.chevalleyLieLattice`.
* `TauCeti.DynkinType.simplyConnectedChevalleyConstants`,
  `TauCeti.DynkinType.simplyConnectedChevalleyLieEquiv`, `TauCeti.DynkinType.chevalleyConstants`:
  canonical tables and simply connected isomorphism for valid Dynkin types.

## References

* C. Chevalley, *Sur certains groupes simples*, Tohoku Math. J. (2) **7** (1955), 14--66.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module Set

namespace TauCeti

namespace IsChevalleySystem

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)
  {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]

omit [Finite ι] in
private theorem pairingIn_eq {P : RootPairing ι ℤ X Y} (e : ι ≃ H.root)
    (he : ∀ i j, (rootSystem H).pairingIn ℤ (e i) (e j) = P.pairing i j) (a b : ι) :
    (rootSystem H).pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b := by simp [he]

/-- A pairing-preserving root-index bijection carries root sums in `P` to weight sums in `H`. -/
theorem coe_weight_eq_add_of_root_eq_add {P : RootPairing ι ℤ X Y} (e : ι ≃ H.root)
    (he : ∀ i j, (rootSystem H).pairingIn ℤ (e i) (e j) = P.pairing i j)
    {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    ((e k : Weight K H L) : H → K) = ((e i : Weight K H L) : H → K) + (e j : Weight K H L) := by
  have hkH := (RootPairing.root_eq_add_iff_of_pairingIn e (pairingIn_eq e he) k i j).mpr hk
  funext z
  simpa [rootSystem_root_apply, Weight.toLinear_apply] using DFunLike.congr_fun hkH z

variable (P : RootPairing ι ℤ X Y) (e : ι ≃ H.root)
  (he : ∀ i j, (rootSystem H).pairingIn ℤ (e i) (e j) = P.pairing i j)

include he in
private theorem weight_eq_neg_of_root_add_eq_zero {i j : ι} (h0 : P.root i + P.root j = 0) :
    (e j : Weight K H L) = -(e i : Weight K H L) := by
  have hH := (RootPairing.root_add_eq_zero_iff_of_pairingIn e (pairingIn_eq e he) i j).mpr h0
  ext z
  have hz : (e i : Weight K H L) z + (e j : Weight K H L) z = 0 := by
    simpa [rootSystem_root_apply, Weight.toLinear_apply] using DFunLike.congr_fun hH z
  simp only [Weight.coe_neg, Pi.neg_apply]; linear_combination hz

include he in
private theorem rootSpace_add_eq_bot_of_notMem {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) (hne : P.root i + P.root j ≠ 0) :
    rootSpace H (((e i : Weight K H L) : H → K) + (e j : Weight K H L)) = ⊥ := by
  by_contra hbot
  let χ : Weight K H L := ⟨((e i : Weight K H L) : H → K) + (e j : Weight K H L), hbot⟩
  have hχ : χ.IsNonZero := fun h0 ↦ hne <|
    (RootPairing.root_add_eq_zero_iff_of_pairingIn e (pairingIn_eq e he) i j).mp <| by
      ext z; simpa [χ, rootSystem_root_apply, Weight.toLinear_apply] using congrFun h0 z
  let r : H.root := ⟨χ, by simpa [LieSubalgebra.root] using hχ⟩
  exact hnot <| (RootPairing.root_add_mem_range_iff_of_pairingIn e (pairingIn_eq e he) i j).mp
    ⟨r, by ext z; simp [r, χ, rootSystem_root_apply, Weight.toLinear_apply]⟩

open scoped Classical in
private noncomputable def rawStructConst (i j : ι) : ℤ :=
  if h : ∃ k, P.root k = P.root i + P.root j then
    hx.intStructureConstant (e i) (e j) (e h.choose) (H.isNonZero_coe_root (e h.choose))
      (coe_weight_eq_add_of_root_eq_add e he h.choose_spec)
  else 0

private theorem rawStructConst_of_root_eq_add {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    hx.rawStructConst P e he i j =
      hx.intStructureConstant (e i) (e j) (e k) (H.isNonZero_coe_root (e k))
        (coe_weight_eq_add_of_root_eq_add e he hk) := by
  classical
  have hex : ∃ k', P.root k' = P.root i + P.root j := ⟨k, hk⟩
  rw [rawStructConst, dite_eq_left hex]
  cases P.root.injective (hex.choose_spec.trans hk.symm); rfl

private theorem rawStructConst_of_notMem {i j : ι} (hnot : P.root i + P.root j ∉ range P.root) :
    hx.rawStructConst P e he i j = 0 := by
  classical exact dite_eq_right fun ⟨k, hk⟩ ↦ hnot ⟨k, hk⟩

private theorem lie_eq_rawStructConst_zsmul {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    ⁅x (e i), x (e j)⁆ = hx.rawStructConst P e he i j • x (e k) := by
  rw [hx.rawStructConst_of_root_eq_add P e he hk]
  exact hx.lie_eq_intStructureConstant_zsmul (e i) (e j) (e k) (H.isNonZero_coe_root (e k))
    (coe_weight_eq_add_of_root_eq_add e he hk)

omit [Finite ι] in
private theorem tripleRootCoeff_eq_zero_of_ne_sum (N : ι → ι → ℤ)
    {a b c l : ι} (hl : P.root l ≠ P.root a + P.root b + P.root c) :
    P.tripleRootCoeff N a b c l = 0 := by
  classical
  by_cases hbc0 : P.root b + P.root c = 0
  · rw [P.tripleRootCoeff_of_add_eq_zero _ hbc0,
      ite_eq_right (by rintro rfl; exact hl (by rw [add_assoc, hbc0, add_zero]))]
  · by_cases hex : ∃ m, P.root m = P.root b + P.root c
    · obtain ⟨m, hm⟩ := hex
      rw [P.tripleRootCoeff_of_root_eq_add _ hm,
        ite_eq_right (fun h ↦ hl (by rw [h, hm, add_assoc]))]
    · exact P.tripleRootCoeff_of_notMem_of_add_ne_zero _ (fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩) hbc0

private theorem lie_lie_eq_tripleRootCoeff_zsmul {a b c l : ι}
    (hl : P.root l = P.root a + P.root b + P.root c) :
    ⁅x (e a), ⁅x (e b), x (e c)⁆⁆ =
      P.tripleRootCoeff (hx.rawStructConst P e he) a b c l • x (e l) := by
  by_cases hbc0 : P.root b + P.root c = 0
  · obtain rfl : l = a := P.root.injective (by rw [hl, add_assoc, hbc0, add_zero])
    rw [P.tripleRootCoeff_of_add_eq_zero _ hbc0, ite_eq_left rfl,
      weight_eq_neg_of_root_add_eq_zero P e he hbc0,
      hx.toIsSl2System.lie_neg (e b) (H.isNonZero_coe_root (e b)),
      ← lie_skew (x (e l)) (coroot (e b : Weight K H L) : L),
      hx.toIsSl2System.lie_coroot (e l) (e b)]
    have hpair : (e l : Weight K H L) (coroot (e b : Weight K H L)) = (P.pairing l b : K) := by
      rw [← rootSystem_pairing_apply, ← (rootSystem H).algebraMap_pairingIn ℤ, he]; rfl
    rw [hpair, ← neg_smul, ← Int.cast_neg, Int.cast_smul_eq_zsmul]
  · by_cases hex : ∃ m, P.root m = P.root b + P.root c
    · obtain ⟨m, hm⟩ := hex
      have hlm : P.root l = P.root a + P.root m := by rw [hl, hm, add_assoc]
      rw [P.tripleRootCoeff_of_root_eq_add _ hm, ite_eq_left hlm,
        hx.lie_eq_rawStructConst_zsmul P e he hm, lie_zsmul,
        hx.lie_eq_rawStructConst_zsmul P e he hlm, mul_comm, mul_smul]
    · have hnot : P.root b + P.root c ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      rw [P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hnot hbc0, zero_smul,
        hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot (e b) (e c)
          (rootSpace_add_eq_bot_of_notMem P e he hnot hbc0), lie_zero]

private theorem rawStructConst_swap (i j : ι) :
    hx.rawStructConst P e he j i = -hx.rawStructConst P e he i j := by
  by_cases hex : ∃ k, P.root k = P.root i + P.root j
  · obtain ⟨k, hk⟩ := hex
    rw [hx.rawStructConst_of_root_eq_add P e he (hk.trans (add_comm (P.root i) (P.root j))),
      hx.rawStructConst_of_root_eq_add P e he hk]
    refine (Int.cast_injective : Function.Injective (Int.cast : ℤ → K)) ?_
    rw [Int.cast_neg, hx.intStructureConstant_cast, hx.intStructureConstant_cast]
    exact hx.toIsSl2System.structureConstant_skew (e i) (e j) (e k) (H.isNonZero_coe_root (e k))
      (coe_weight_eq_add_of_root_eq_add e he hk)
  · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
    rw [hx.rawStructConst_of_notMem P e he (add_comm (P.root i) (P.root j) ▸ hnot),
      hx.rawStructConst_of_notMem P e he hnot, neg_zero]

private theorem natAbs_rawStructConst {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    (hx.rawStructConst P e he i j).natAbs = P.chainBotCoeff i j + 1 := by
  have hkH := (RootPairing.root_eq_add_iff_of_pairingIn e (pairingIn_eq e he) k i j).mpr hk
  have hli := (rootSystem H).linearIndependent_of_add_mem_range_root' ⟨e k, hkH⟩
  have hbot : chainBotCoeff (e i : Weight K H L) (e j : Weight K H L) = P.chainBotCoeff i j :=
    (rootSystem_chainCoeffs_eq hli).2.symm.trans
      (RootPairing.chainBotCoeff_eq_of_pairingIn e (pairingIn_eq e he) i j)
  rw [hx.rawStructConst_of_root_eq_add P e he hk, ← hbot]
  rcases hx.intStructureConstant_eq_natCast_or_eq_neg_natCast (e i) (e j) (e k)
      (H.isNonZero_coe_root (e i)) (H.isNonZero_coe_root (e j)) (H.isNonZero_coe_root (e k))
      (coe_weight_eq_add_of_root_eq_add e he hk) with hN | hN
  · rw [hN, Int.natAbs_natCast]
  · rw [hN, Int.natAbs_neg, Int.natAbs_natCast]

private theorem rawStructConst_reflectionPerm (i j : ι) :
    hx.rawStructConst P e he (P.reflectionPerm i i) (P.reflectionPerm j j) =
      -hx.rawStructConst P e he i j := by
  have hneg_e (a : ι) : e (P.reflectionPerm a a) = -e a :=
    (RootPairing.map_reflectionPerm_of_pairingIn e (pairingIn_eq e he) a a).trans
      (rootSystem_reflectionPerm_self_eq_neg (e a))
  by_cases hex : ∃ k, P.root k = P.root i + P.root j
  · obtain ⟨k, hk⟩ := hex
    have hk' : P.root (P.reflectionPerm k k) =
        P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) := by
      simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]; rw [hk]; abel
    rw [hx.rawStructConst_of_root_eq_add P e he hk', hx.rawStructConst_of_root_eq_add P e he hk]
    refine (Int.cast_injective : Function.Injective (Int.cast : ℤ → K)) ?_
    rw [Int.cast_neg, hx.intStructureConstant_cast, hx.intStructureConstant_cast]
    have hneg := (hx.toIsSl2System.structureConstant_neg_neg_eq_neg_iff
      (e i) (e j) (e k) (H.isNonZero_coe_root (e i)) (H.isNonZero_coe_root (e j))
      (H.isNonZero_coe_root (e k)) (coe_weight_eq_add_of_root_eq_add e he hk)).mpr
      (hx.structureConstant_eq_natCast_or_eq_neg_natCast (e i) (e j) (e k)
        (H.isNonZero_coe_root (e i)) (H.isNonZero_coe_root (e j)) (H.isNonZero_coe_root (e k))
        (coe_weight_eq_add_of_root_eq_add e he hk))
    convert hneg using 2 <;> simp [hneg_e]
  · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
    rw [hx.rawStructConst_of_notMem P e he
        (mt (P.root_reflectionPerm_add_mem_range_iff i j).mp hnot),
      hx.rawStructConst_of_notMem P e he hnot, neg_zero]

private theorem rawStructConst_coroot_jacobi {i j k : ι}
    (hsum : P.root i + P.root j + P.root k = 0) :
    hx.rawStructConst P e he j k • P.coroot i + hx.rawStructConst P e he k i • P.coroot j +
      hx.rawStructConst P e he i j • P.coroot k = 0 := by
  have hterm {a b c : ι} (habc : P.root a + P.root b + P.root c = 0) :
      ⁅x (e a), ⁅x (e b), x (e c)⁆⁆ =
        hx.rawStructConst P e he b c • (coroot (e a : Weight K H L) : L) := by
    have hea' : (e (P.reflectionPerm a a) : Weight K H L) = -(e a : Weight K H L) :=
      congrArg Subtype.val <|
        (RootPairing.map_reflectionPerm_of_pairingIn e (pairingIn_eq e he) a a).trans
          (rootSystem_reflectionPerm_self_eq_neg (e a))
    rw [hx.lie_eq_rawStructConst_zsmul P e he
        (RootPairing.root_reflectionPerm_self_eq_add_of_add_add_eq_zero habc),
      lie_zsmul, hea', hx.toIsSl2System.lie_neg (e a) (H.isNonZero_coe_root (e a))]
  have hjac := lie_jacobi (x (e i)) (x (e j)) (x (e k))
  rw [hterm hsum, hterm (by rw [← hsum]; abel), hterm (by rw [← hsum]; abel)] at hjac
  have hH : hx.rawStructConst P e he j k • (rootSystem H).coroot (e i) +
      hx.rawStructConst P e he k i • (rootSystem H).coroot (e j) +
      hx.rawStructConst P e he i j • (rootSystem H).coroot (e k) = 0 :=
    Subtype.ext (by simpa [rootSystem_coroot_apply, add_assoc] using hjac)
  have hc (r) : P.coroot r ∈ P.corootSpan ℤ := Submodule.subset_span (mem_range_self _)
  refine P.eq_zero_of_mem_corootSpan_of_forall_root'_eq_zero
    (add_mem (add_mem (Submodule.smul_mem _ _ (hc _)) (Submodule.smul_mem _ _ (hc _)))
      (Submodule.smul_mem _ _ (hc _))) fun s ↦ ?_
  have hs := congrArg ((rootSystem H).toLinearMap ((rootSystem H).root (e s))) hH
  simp only [map_add, LinearMap.map_smul_of_tower, map_zero, rootSystem_toLinearMap_apply,
    rootSystem_root_apply, Weight.toLinear_apply, rootSystem_coroot_apply,
    ← rootSystem_pairing_apply, ← (rootSystem H).algebraMap_pairingIn ℤ, he] at hs
  exact (Int.cast_injective : Function.Injective (Int.cast : ℤ → K))
    (by simpa [RootPairing.root'_coroot_eq_pairing, zsmul_eq_mul] using hs)

include hx in
/-- **Chevalley structure constants from a Killing Chevalley system.** Any Chevalley system `hx`
induces a `RootPairing.ChevalleyConstants` table on any finite integral root pairing `P` whose root
indices match `H.root` with equal Cartan integers. -/
noncomputable def chevalleyConstants : P.ChevalleyConstants where
  structConst := hx.rawStructConst P e he
  structConst_eq_zero_of_notMem_range _ _ := hx.rawStructConst_of_notMem P e he
  structConst_swap := hx.rawStructConst_swap P e he
  natAbs_structConst := hx.natAbs_rawStructConst P e he
  structConst_reflectionPerm := hx.rawStructConst_reflectionPerm P e he
  coroot_jacobi := hx.rawStructConst_coroot_jacobi P e he
  root_jacobi i j k l := by
    by_cases hl : P.root l = P.root i + P.root j + P.root k
    · have hjac := lie_jacobi (x (e i)) (x (e j)) (x (e k))
      rw [hx.lie_lie_eq_tripleRootCoeff_zsmul P e he hl,
        hx.lie_lie_eq_tripleRootCoeff_zsmul P e he (by rw [hl]; abel),
        hx.lie_lie_eq_tripleRootCoeff_zsmul P e he (by rw [hl]; abel),
        ← add_smul, ← add_smul, ← Int.cast_smul_eq_zsmul K] at hjac
      exact Int.cast_eq_zero.mp
        ((smul_eq_zero.mp hjac).resolve_right (hx.toIsSl2System.ne_zero (e l)
          (H.isNonZero_coe_root (e l))))
    · rw [tripleRootCoeff_eq_zero_of_ne_sum P _ hl,
        tripleRootCoeff_eq_zero_of_ne_sum P _ (fun h ↦ hl (by rw [h]; abel)),
        tripleRootCoeff_eq_zero_of_ne_sum P _ (fun h ↦ hl (by rw [h]; abel)), add_zero, add_zero]

/-- On a root sum `P.root k = P.root i + P.root j`, `(hx.chevalleyConstants P e he).structConst i j`
equals the integer structure constant of the Killing Chevalley system `hx`. -/
theorem chevalleyConstants_structConst_of_root_eq_add {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    (hx.chevalleyConstants P e he).structConst i j =
      hx.intStructureConstant (e i) (e j) (e k) (H.isNonZero_coe_root (e k))
        (coe_weight_eq_add_of_root_eq_add e he hk) :=
  hx.rawStructConst_of_root_eq_add P e he hk

/-- On a root sum `P.root k = P.root i + P.root j`, the bracket of `x (e i)` and `x (e j)` in `L`
is given by `(hx.chevalleyConstants P e he).structConst i j • x (e k)`. -/
theorem lie_eq_chevalleyConstants_structConst_zsmul {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    ⁅x (e i), x (e j)⁆ = (hx.chevalleyConstants P e he).structConst i j • x (e k) :=
  hx.lie_eq_rawStructConst_zsmul P e he hk

/-! ### Comparison with the Chevalley Lie lattice -/

omit [Finite ι] in
include he in
private theorem gamma_coroot_eq (γ : Y →ₗ[ℤ] H)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) (i : ι) :
    γ (P.coroot i) = (rootSystem H).coroot (e i) := by
  have hsub (α : Dual K H) : α (γ (P.coroot i) - (rootSystem H).coroot (e i)) = 0 := by
    have hmem : α ∈ Submodule.span K (range (rootSystem H).root) := by
      rw [RootPairing.IsRootSystem.span_root_eq_top]; trivial
    induction hmem using Submodule.span_induction with
    | mem _ hf =>
      obtain ⟨r, rfl⟩ := hf; obtain ⟨j, rfl⟩ := e.surjective r
      rw [map_sub, sub_eq_zero, rootSystem_root_apply, Weight.toLinear_apply,
        Weight.toLinear_apply, hγ_pair, rootSystem_coroot_apply, P.root_coroot_eq_pairing]
      have hp : (e j : Weight K H L) (coroot (e i : Weight K H L)) =
          (rootSystem H).pairing (e j) (e i) := rfl
      rw [hp, ← (rootSystem H).algebraMap_pairingIn ℤ, he]; rfl
    | zero => simp
    | add _ _ _ _ hf hg => simp only [LinearMap.add_apply, hf, hg, add_zero]
    | smul _ _ _ hf => simp only [LinearMap.smul_apply, hf, smul_zero]
  exact sub_eq_zero.mp <| (rootSystem H).toPerfPair.flip.bijective.injective <| by
    ext α; simpa using hsub α

include hx in
/-- **The `ℤ`-Lie homomorphism from `ChevalleyLieAlgebra` into `hx.chevalleyLieLattice`** induced by
any cocharacter map `γ : Y →ₗ[ℤ] H` landing in `hx.chevalleyLieLattice` and compatible with the
root-cocharacter pairing. -/
noncomputable def toChevalleyLieLattice (γ : Y →ₗ[ℤ] H)
    (hγ_mem : ∀ y, (γ y : L) ∈ hx.chevalleyLieLattice)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) :
    RootPairing.ChevalleyLieAlgebra (hx.chevalleyConstants P e he) →ₗ⁅ℤ⁆ hx.chevalleyLieLattice :=
  let γL : Y →ₗ[ℤ] hx.chevalleyLieLattice :=
    { toFun y := ⟨(γ y : L), hγ_mem y⟩, map_add' _ _ := Subtype.ext (by simp)
      map_smul' _ _ := Subtype.ext (by simp) }
  RootPairing.ChevalleyLieAlgebra.liftLieHom (hx.chevalleyConstants P e he) γL
    (fun i ↦ ⟨x (e i), hx.rootVector_mem_chevalleyLieLattice (e i)⟩)
    (fun y z ↦ Subtype.ext <| LieSubalgebra.lie_eq_zero_of_mem (γ y).2 (γ z).2)
    (fun y i ↦ Subtype.ext <| by
      change ⁅(γ y : L), x (e i)⁆ = P.toLinearMap (P.root i) y • x (e i)
      rw [← LieSubalgebra.coe_bracket_of_module,
        lie_eq_smul_of_mem_rootSpace (hx.toIsSl2System.mem_rootSpace (e i)) (γ y),
        hγ_pair, Int.cast_smul_eq_zsmul])
    (fun {i j} h0 ↦ Subtype.ext <| by
      change ⁅x (e i), x (e j)⁆ = (γ (P.coroot i) : L)
      rw [weight_eq_neg_of_root_add_eq_zero P e he h0,
        hx.toIsSl2System.lie_neg (e i) (H.isNonZero_coe_root (e i)),
        gamma_coroot_eq P e he γ hγ_pair i, rootSystem_coroot_apply])
    (fun {_ _ _} hk ↦ Subtype.ext <| hx.lie_eq_chevalleyConstants_structConst_zsmul P e he hk)
    (fun {i j} hnot h0 ↦ Subtype.ext <|
      hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot (e i) (e j)
        (rootSpace_add_eq_bot_of_notMem P e he hnot h0))

/-- `toChevalleyLieLattice` sends a Cartan element `cartan _ y` to `γ y`. -/
@[simp] theorem coe_toChevalleyLieLattice_cartan (γ : Y →ₗ[ℤ] H)
    (hγ_mem : ∀ y, (γ y : L) ∈ hx.chevalleyLieLattice)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) (y : Y) :
    (hx.toChevalleyLieLattice P e he γ hγ_mem hγ_pair
      (RootPairing.ChevalleyLieAlgebra.cartan _ y) : L) = (γ y : L) := by
  simp [toChevalleyLieLattice]

/-- `toChevalleyLieLattice` sends the `i`-th Chevalley root generator to `x (e i)`. -/
@[simp] theorem coe_toChevalleyLieLattice_root (γ : Y →ₗ[ℤ] H)
    (hγ_mem : ∀ y, (γ y : L) ∈ hx.chevalleyLieLattice)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) (i : ι) :
    (hx.toChevalleyLieLattice P e he γ hγ_mem hγ_pair
      (RootPairing.ChevalleyLieAlgebra.root _ i) : L) = x (e i) := by simp [toChevalleyLieLattice]

section SimpleCoroot

variable (b : (rootSystem H).Base) {J : Type*} (bY : Basis J ℤ Y) (s : J ≃ b.support)

private noncomputable def simpleCorootCoweightMap : Y →ₗ[ℤ] H :=
  bY.constr ℤ fun j : J ↦ (rootSystem H).coroot (s j : H.root)

include hx in
private theorem simpleCorootCoweightMap_mem (y : Y) :
    (simpleCorootCoweightMap b bY s y : L) ∈ hx.chevalleyLieLattice := by
  have hy : y ∈ Submodule.span ℤ (range bY) := by rw [bY.span_eq]; trivial
  let γL' : Y →ₗ[ℤ] L := (H.toSubmodule.subtype.restrictScalars ℤ).comp
    (simpleCorootCoweightMap b bY s)
  change γL' y ∈ hx.chevalleyLieLattice
  induction hy using Submodule.span_induction with
  | mem _ hv =>
    obtain ⟨j, rfl⟩ := hv
    change ((simpleCorootCoweightMap b bY s (bY j) : H) : L) ∈ hx.chevalleyLieLattice
    rw [simpleCorootCoweightMap, Basis.constr_basis, rootSystem_coroot_apply]
    exact hx.coroot_mem_chevalleyLieLattice ((s j : H.root) : Weight K H L)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul z _ _ hu => rw [map_smul]; exact Submodule.smul_mem _ z hu

variable (hbY : ∀ j : J, bY j = P.coroot (e.symm (s j)))

include he hbY

omit [Finite ι] in
private theorem simpleCorootCoweightMap_pair (y : Y) (i : ι) :
    (e i : Weight K H L) (simpleCorootCoweightMap b bY s y) =
      (P.toLinearMap (P.root i) y : K) := by
  let lhs : Y →ₗ[ℤ] K := ((e i : Weight K H L).toLinear.restrictScalars ℤ).comp
    (simpleCorootCoweightMap b bY s)
  let rhs : Y →ₗ[ℤ] K := (Int.castAddHom K).toIntLinearMap.comp (P.toLinearMap (P.root i))
  suffices lhs = rhs from DFunLike.congr_fun this y
  refine bY.ext fun j ↦ ?_
  change (e i : Weight K H L) (simpleCorootCoweightMap b bY s (bY j)) =
    (P.toLinearMap (P.root i) (bY j) : K)
  rw [simpleCorootCoweightMap, Basis.constr_basis, rootSystem_coroot_apply, hbY,
    P.root_coroot_eq_pairing]
  have hp : (e i : Weight K H L) (coroot ((s j : H.root) : Weight K H L)) =
      (rootSystem H).pairing (e i) (s j) := rfl
  rw [hp, ← (rootSystem H).algebraMap_pairingIn ℤ, ← he i (e.symm (s j)), e.apply_symm_apply]; rfl

include hx in
private theorem toChevalleyLieLattice_simpleCoroot_bijective :
    Function.Bijective (hx.toChevalleyLieLattice P e he (simpleCorootCoweightMap b bY s)
      (hx.simpleCorootCoweightMap_mem b bY s)
      (simpleCorootCoweightMap_pair P e he b bY s hbY)) := by
  let f := hx.toChevalleyLieLattice P e he (simpleCorootCoweightMap b bY s)
    (hx.simpleCorootCoweightMap_mem b bY s) (simpleCorootCoweightMap_pair P e he b bY s hbY)
  let σ : J ⊕ ι ≃ H.root ⊕ b.support := (Equiv.sumCongr s e).trans (Equiv.sumComm _ _)
  let bSrc := RootPairing.ChevalleyLieAlgebra.basis (hx.chevalleyConstants P e he) bY
  let bDst := (hx.rootSimpleCorootBasis b).reindex σ.symm
  have hf_eq : f.toLinearMap = (bSrc.equiv bDst (.refl _)).toLinearMap :=
    bSrc.ext fun idx ↦ by
      have hrhs : (bSrc.equiv bDst (.refl _)).toLinearMap (bSrc idx) = bDst idx := by simp
      rw [hrhs]
      rcases idx with j | i <;> apply Subtype.ext <;>
        simp [f, bSrc, bDst, σ, simpleCorootCoweightMap]
  rw [← LieHom.coe_toLinearMap, hf_eq]
  exact (bSrc.equiv bDst (.refl _)).bijective

include hx in
/-- **Simply connected identification with the Chevalley Lie lattice.** When `b` is a base of
`rootSystem H` and `Y` has a `ℤ`-basis `bY` indexed by `J ≃ b.support` consisting of the
corresponding simple coroots of `P`, the abstract `ChevalleyLieAlgebra` is canonically isomorphic
over `ℤ` to `hx.chevalleyLieLattice`. -/
noncomputable def toChevalleyLieLatticeEquiv :
    RootPairing.ChevalleyLieAlgebra (hx.chevalleyConstants P e he) ≃ₗ⁅ℤ⁆ hx.chevalleyLieLattice :=
  LieEquiv.ofBijective
    (hx.toChevalleyLieLattice P e he (simpleCorootCoweightMap b bY s)
      (hx.simpleCorootCoweightMap_mem b bY s) (simpleCorootCoweightMap_pair P e he b bY s hbY))
    (hx.toChevalleyLieLattice_simpleCoroot_bijective P e he b bY s hbY)

/-- `toChevalleyLieLatticeEquiv` sends the `j`-th Cartan basis generator to the `s j`-th simple
coroot in `L`. -/
theorem coe_toChevalleyLieLatticeEquiv_cartan_basis (j : J) :
    (hx.toChevalleyLieLatticeEquiv P e he b bY s hbY
      (RootPairing.ChevalleyLieAlgebra.cartan _ (bY j)) : L) =
      (coroot ((s j : H.root) : Weight K H L) : L) := by
  simp [toChevalleyLieLatticeEquiv, simpleCorootCoweightMap]

/-- `toChevalleyLieLatticeEquiv` sends the `i`-th Chevalley root generator to `x (e i)`. -/
@[simp] theorem coe_toChevalleyLieLatticeEquiv_root (i : ι) :
    (hx.toChevalleyLieLatticeEquiv P e he b bY s hbY
      (RootPairing.ChevalleyLieAlgebra.root _ i) : L) = x (e i) := by
  simp [toChevalleyLieLatticeEquiv]

end SimpleCoroot

end IsChevalleySystem

/-! ## Pinned Dynkin types and general integral root data -/

namespace DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- The Killing root system of the pinned rational Lie algebra has the exact Cartan integers of
`TauCeti.DynkinType.simplyConnectedRootDatum` under `TauCeti.DynkinType.rootEquiv`. -/
@[simp] theorem pairingIn_rootEquiv (i j : Fin t.numRoots) :
    (rootSystem (t.cartanSubalgebra ht)).pairingIn ℤ (t.rootEquiv ht i) (t.rootEquiv ht j) =
      (t.simplyConnectedRootDatum ht).pairing i j :=
  FaithfulSMul.algebraMap_injective ℤ ℚ <| by
    rw [RootPairing.algebraMap_pairingIn, rootEquiv_eq_indexEquiv,
      (t.rationalRootSystemEquiv ht).toHom.pairing, t.pairing_rationalRootSystem ht]; rfl

/-- **The canonical Chevalley structure-constant table on the pinned simply connected root datum**
of type `t`, extracted from `TauCeti.DynkinType.isChevalleySystem_chevalleySystem`. -/
noncomputable def simplyConnectedChevalleyConstants :
    (t.simplyConnectedRootDatum ht).ChevalleyConstants :=
  (t.isChevalleySystem_chevalleySystem ht).chevalleyConstants
    (t.simplyConnectedRootDatum ht) (t.rootEquiv ht) (t.pairingIn_rootEquiv ht)

open Classical in
private noncomputable def killingSimpleSupportEquiv :
    Fin t.rank ≃ ((t.rationalBase ht).map (t.rationalRootSystemEquiv ht)).support :=
  (t.simpleSupportEquiv ht).trans
    ((t.rationalBase ht).supportMapEquiv (t.rationalRootSystemEquiv ht))

open Classical in
private theorem killingSimpleCoroot_eq (j : Fin t.rank) :
    Pi.basisFun ℤ (Fin t.rank) j = (t.simplyConnectedRootDatum ht).coroot
      ((t.rootEquiv ht).symm (t.killingSimpleSupportEquiv ht j)) := by
  have hcoe : ((t.killingSimpleSupportEquiv ht j :
      ((t.rationalBase ht).map (t.rationalRootSystemEquiv ht)).support) :
      (t.cartanSubalgebra ht).root) = t.rootEquiv ht (t.simpleIndex ht j) :=
    (RootPairing.Base.supportMapEquiv_apply_coe (t.rationalBase ht)
      (t.rationalRootSystemEquiv ht) (t.simpleSupportEquiv ht j)).trans <|
      (congrArg (t.rationalRootSystemEquiv ht).indexEquiv (t.coe_simpleSupportEquiv ht j)).trans
        (DFunLike.congr_fun (t.rootEquiv_eq_indexEquiv ht).symm _)
  rw [hcoe, (t.rootEquiv ht).symm_apply_apply, t.coroot_simpleIndex ht]
  ext k; simp [Pi.single_apply]

/-- **The abstract simply connected `ChevalleyLieAlgebra` of type `t` is canonically isomorphic over
`ℤ` to the Chevalley lattice of the pinned rational Lie algebra.** -/
noncomputable def simplyConnectedChevalleyLieEquiv :
    RootPairing.ChevalleyLieAlgebra (t.simplyConnectedChevalleyConstants ht) ≃ₗ⁅ℤ⁆
      (t.isChevalleySystem_chevalleySystem ht).chevalleyLieLattice :=
  (t.isChevalleySystem_chevalleySystem ht).toChevalleyLieLatticeEquiv
    (t.simplyConnectedRootDatum ht) (t.rootEquiv ht) (t.pairingIn_rootEquiv ht)
    ((t.rationalBase ht).map (t.rationalRootSystemEquiv ht))
    (Pi.basisFun ℤ (Fin t.rank)) (t.killingSimpleSupportEquiv ht) (t.killingSimpleCoroot_eq ht)

/-- **Canonical Chevalley structure constants on any integral root datum of Dynkin type `t`.**
Transporting `TauCeti.DynkinType.simplyConnectedChevalleyConstants` along a pairing-preserving root
enumeration equips every reductive or non-simply-connected root datum of type `t` with Chevalley
structure constants. -/
noncomputable def chevalleyConstants {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : ι ≃ Fin t.numRoots)
    (he : ∀ i j, P.pairing i j = (t.simplyConnectedRootDatum ht).pairing (e i) (e j)) :
    letI : Finite ι := Finite.of_equiv _ e.symm
    P.ChevalleyConstants :=
  letI : Finite ι := Finite.of_equiv _ e.symm
  (t.simplyConnectedChevalleyConstants ht).reindex e.symm fun i j ↦ by
    rw [he (e.symm i) (e.symm j), e.apply_symm_apply, e.apply_symm_apply]

end DynkinType

end TauCeti
