/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.GroupTheory.Index.Indicator
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.ClassFunction
public import TauCeti.RepresentationTheory.Tensor.Induction.Trace

import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.GroupAction.Orbit.Basic
import TauCeti.GroupTheory.GroupAction.Orbit.Finset
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.GroupTheory.GroupAction.FinRotate
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
import TauCeti.GroupTheory.QuotientGroup.Index
import TauCeti.RepresentationTheory.Induction.Character
import TauCeti.RepresentationTheory.LinearCharacter.Basic
import TauCeti.RepresentationTheory.Tensor.Induction.PrimeIndex

/-!
# Tensor induction and virtual characters

Tensor induction `Subgroup.tensorIndClassFun` preserves `TauCeti.virtualCharacters` for every
finite-index subgroup `U ≤ G` and every coefficient field `k` (Evens' theorem on virtual
characters): if `ψ = χ_A - χ_B` is a virtual character of `U`, then `U.tensorIndClassFun ψ` is an
alternating sum of induced characters with one term for the setwise stabilizer
`MulAction.stabilizer G S` of a representative subset `S ⊆ G ⧸ U` in each `G`-orbit.

For each stabilizer representation `W_S = ε_S ⊗ B_S ⊗ A_{Sᶜ}`, the pieces assemble via
`Subgroup.monomialHom`, `Representation.wreathTensor`,
`Equiv.Perm.sign_eq_neg_one_pow_card_sub_orbitCount`, and `Subgroup.indClassFun_ofFDRep_character`:
at each `g : G`, expanding `∏ ω, (χ_A(m_ω) - χ_B(m_ω))` sums over `g`-invariant subsets
`T ⊆ G ⧸ U` with sign `(-1)^{c(T)} = (-1)^{|T|} · sgn(g|_T)` determined by the cycle count
`c(T)`. Grouping invariant subsets by their `G`-orbit matches the alternating sum
`∑ O, (-1)^{|O.out|} • (MulAction.stabilizer G O.out).indClassFun W_{O.out}.character`.

In prime index `l` for a normal subgroup `H ≤ G`, the explicit formula
`Subgroup.tensorIndClassFun_sub_of_index_prime` decomposes `H.tensorIndClassFun (ψ₁ - ψ₂)`, for
`H`-conjugation-invariant functions `ψ₁, ψ₂`, using the sign `H.quotientSign` of the action of `G`
on `G ⧸ H` and induced class functions indexed by cyclic-shift orbits on nonempty proper subsets
of `Fin l`.

## Main results

* `Subgroup.tensorIndClassFun_character_mem_virtualCharacters`: tensor induction of a genuine
  character of a finite-index subgroup is a virtual character of `G`.
* `Subgroup.tensorIndClassFun_mem_virtualCharacters`: tensor induction of any virtual character of
  a finite-index subgroup is a virtual character of `G`.
* `Subgroup.tensorIndClassFun_sub_of_index_prime`: prime-index decomposition of
  `H.tensorIndClassFun (ψ₁ - ψ₂)` for conjugation-invariant functions `ψ₁, ψ₂`; for characters
  `ψ₁, ψ₂` each term of the orbit sum is a signed induced character.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3.
* L. Alpöge, *The Riemann Hypothesis for Dirichlet L-Functions* (2026).
-/

public section

open scoped Pointwise CategoryTheory.MonoidalCategory TensorProduct

namespace Subgroup

/-- Tensor induction of a genuine character of a finite-index subgroup is a virtual character. -/
theorem tensorIndClassFun_character_mem_virtualCharacters {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (V : FDRep k U) :
    U.tensorIndClassFun V.character ∈ TauCeti.virtualCharacters k G := by
  let := U.fintypeQuotientOfFiniteIndex
  let s : U.LeftTransversal :=
    ⟨Set.range Quotient.out, isComplement_range_left QuotientGroup.out_eq'⟩
  have : FiniteDimensional k (⨂[k] _ : G ⧸ U, V) := PiTensorProduct.finite
  let W := FDRep.ofShrink (U.tensorInducedRepresentation s V.ρ)
  have hV : V.character = fun u ↦ LinearMap.trace k V (V.ρ u) := rfl
  have hch : U.tensorIndClassFun V.character = W.character := by
    ext g
    rw [hV, ← U.trace_tensorInducedRepresentation s V.ρ g]
    exact (FDRep.character_ofShrink (U.tensorInducedRepresentation s V.ρ) g).symm
  rw [hch]
  exact TauCeti.character_mem_virtualCharacters W

private noncomputable def subsetMonomialHom {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] (H : Subgroup G) (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) : H →* TauCeti.WreathProduct U ↥T where
  toFun x := ⟨fun y ↦ (U.monomialHom s x.val).left y.val, MulAction.subsetPermOn H T hT x⟩
  map_one' := SemidirectProduct.ext (funext fun y ↦ by simp) (by simp)
  map_mul' x z := by
    refine SemidirectProduct.ext (funext fun y ↦ ?_) (by simp)
    rw [Subgroup.coe_mul, map_mul, TauCeti.PermutationWreathProduct.mul_left,
      TauCeti.PermutationWreathProduct.mul_left]
    congr 1
    dsimp only
    rw [Equiv.Perm.smul_def, Subgroup.monomialHom_right_inv, Equiv.Perm.smul_def, ← map_inv,
      MulAction.subsetPermOn_apply, InvMemClass.coe_inv]

private theorem subsetMonomialHom_right {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] (H : Subgroup G) (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H) :
    (subsetMonomialHom U s H T hT x).right = MulAction.subsetPermOn H T hT x :=
  rfl

private noncomputable def subsetWreathRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] (H : Subgroup G)
    (T : Finset (G ⧸ U)) (hT : ∀ x : H, (x : G) • T = T) (V : FDRep k U) : FDRep k H :=
  have : FiniteDimensional k (⨂[k] _ : ↥T, V) := PiTensorProduct.finite
  FDRep.ofShrink ((Representation.wreathTensor V.ρ ↥T).comp (subsetMonomialHom U s H T hT))

private theorem subsetMonomialHom_orbit_prod {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H) (q₀ : ↥T) :
    (List.ofFn fun t : Fin (Function.minimalPeriod ((MulAction.subsetPermOn H T hT x) • ·) q₀) ↦
        (subsetMonomialHom U s H T hT x).left
          (((MulAction.subsetPermOn H T hT x)⁻¹ ^ (t : ℕ)) q₀)).prod =
      ⟨(U.leftTransversalRep s q₀.val)⁻¹ *
          x.val ^ Function.minimalPeriod (x.val • ·) q₀.val * U.leftTransversalRep s q₀.val,
        conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s q₀.val)⟩ := by
  rw [← Subgroup.monomialHom_orbit_prod U s x.val q₀.val]
  -- The restricted orbit list is the ambient orbit list of `U.monomialHom s x`.
  refine congrArg List.prod (List.ext_getElem (by
    simp only [List.length_ofFn]
    rw [MulAction.minimalPeriod_subsetPermOn]
    exact congrArg₂ _ (funext fun y ↦ (Subgroup.monomialHom_right U s x.val y).symm) rfl)
    fun i _ _ ↦ ?_)
  have ha : (((MulAction.subsetPermOn H T hT x)⁻¹ ^ i) q₀).val =
      ((U.monomialHom s x.val).right⁻¹ ^ i) q₀.val := by
    rw [← map_inv, ← zpow_natCast (MulAction.subsetPermOn H T hT x⁻¹),
      MulAction.subsetPermOn_zpow_val hT x⁻¹ (i : ℕ) q₀, ← SemidirectProduct.inv_right,
      ← map_inv (U.monomialHom s), ← zpow_natCast, Subgroup.monomialHom_right_zpow]
    simp
  simp only [List.getElem_ofFn]
  -- Unfold `(subsetMonomialHom ... x).left` to `(U.monomialHom s x.val).left`.
  change (U.monomialHom s x.val).left (((MulAction.subsetPermOn H T hT x)⁻¹ ^ i) q₀).val = _
  rw [ha]

private theorem character_subsetWreathRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Finite (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal) (H : Subgroup G)
    (T : Finset (G ⧸ U)) (hT : ∀ x : H, (x : G) • T = T) (V : FDRep k U) (x : H)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U))] :
    (subsetWreathRep U s H T hT V).character x =
      ∏ ω ∈ Finset.univ.filter (fun ω :
          MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) ↦ ω.out ∈ T),
        V.character
          ⟨(U.leftTransversalRep s ω.out)⁻¹ * x.val ^ Function.minimalPeriod (x.val • ·) ω.out *
              U.leftTransversalRep s ω.out,
            conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s ω.out)⟩ := by
  let _ := Fintype.ofFinite (G ⧸ U)
  let _ : Fintype
      (MulAction.orbitRel.Quotient (Subgroup.zpowers (MulAction.subsetPermOn H T hT x)) ↥T) :=
    Fintype.ofFinite _
  have : FiniteDimensional k (⨂[k] _ : ↥T, V) := PiTensorProduct.finite
  let a : TauCeti.WreathProduct U ↥T :=
    ⟨(subsetMonomialHom U s H T hT x).left, MulAction.subsetPermOn H T hT x⟩
  have ha : subsetMonomialHom U s H T hT x = a :=
    SemidirectProduct.ext rfl (subsetMonomialHom_right U s H T hT x)
  dsimp only [subsetWreathRep]
  rw [FDRep.character_ofShrink, Representation.character, MonoidHom.comp_apply, ha,
    Representation.trace_wreathTensor]
  dsimp only [a]
  let e := MulAction.subsetOrbitEquiv T hT x
  refine (Fintype.prod_equiv e _ (fun ω ↦ V.character
    ⟨(U.leftTransversalRep s ω.val.out)⁻¹ * x.val ^ Function.minimalPeriod (x.val • ·) ω.val.out *
        U.leftTransversalRep s ω.val.out,
      conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s ω.val.out)⟩) fun q ↦ ?_).trans
    (Finset.prod_subtype
      (Finset.univ.filter fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) ↦
        ω.out ∈ T)
      (p := fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) ↦ ω.out ∈ T)
      (fun _ ↦ by simp)
      fun ω ↦ V.character
        ⟨(U.leftTransversalRep s ω.out)⁻¹ * x.val ^ Function.minimalPeriod (x.val • ·) ω.out *
            U.leftTransversalRep s ω.out,
          conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s ω.out)⟩).symm
  have hm := subsetMonomialHom_orbit_prod U s T hT x q.out
  exact (congrArg (fun u : U ↦ LinearMap.trace k V (V.ρ u)) hm).trans
    (apply_conj_pow_minimalPeriod_eq_of_orbitRel (fun u v ↦ V.char_conj u v) x.val
      (MulAction.subsetOrbitEquiv_out_rel T hT x q) (U.leftTransversalRep_mk s q.out.val)
      (U.leftTransversalRep_mk s (e q).val.out)).symm

private noncomputable def stabilizerRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) : FDRep k (MulAction.stabilizer G S) :=
  let ε : MulAction.stabilizer G S →* kˣ :=
    (Units.map (Int.castRingHom k).toMonoidHom).comp
      (Equiv.Perm.sign.comp
        (MulAction.subsetPermOn _ S fun x ↦ MulAction.mem_stabilizer_iff.mp x.property))
  FDRep.ofLinearCharacter ε ⊗
    subsetWreathRep U s _ S (fun x ↦ MulAction.mem_stabilizer_iff.mp x.property) B ⊗
    subsetWreathRep U s _ Sᶜ (fun x ↦ MulAction.smul_compl_eq_of_smul_eq x.property) A

private noncomputable def evalOrbitFactor {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (A B : FDRep k U) (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))]
    (T : Finset (G ⧸ U)) : k :=
  (∏ ω ∈ Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) ↦
      ω.out ∈ T),
    -B.character
      ⟨(U.leftTransversalRep s ω.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) ω.out *
          U.leftTransversalRep s ω.out,
        conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s ω.out)⟩) *
  (∏ ω ∈ Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) ↦
      ω.out ∈ Tᶜ),
    A.character
      ⟨(U.leftTransversalRep s ω.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) ω.out *
          U.leftTransversalRep s ω.out,
        conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s ω.out)⟩)

private theorem neg_one_pow_mul_stabilizerRep_character {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) (y : MulAction.stabilizer G S)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers y.val) (G ⧸ U))] :
    (-1 : k) ^ S.card * (stabilizerRep U s S A B).character y =
      evalOrbitFactor U s A B y.val S := by
  rw [evalOrbitFactor]
  let := Fintype.ofFinite
    (MulAction.orbitRel.Quotient
      (Subgroup.zpowers
        (MulAction.subsetPermOn _ S (fun x ↦ MulAction.mem_stabilizer_iff.mp x.property) y)) ↥S)
  dsimp only [stabilizerRep]
  have hε : ∀ n : ℤ, (Int.castRingHom k).toMonoidHom n = (n : k) := fun _ ↦ rfl
  simp only [FDRep.char_tensor, Pi.mul_apply, FDRep.char_ofLinearCharacter, MonoidHom.comp_apply,
    Units.coe_map, hε, ← mul_assoc]
  have hsign : (-1 : k) ^ S.card *
      ((Equiv.Perm.sign (MulAction.subsetPermOn _ S
        (fun x ↦ MulAction.mem_stabilizer_iff.mp x.property) y) : ℤ) : k) =
      (-1 : k) ^ (Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient
          (Subgroup.zpowers y.val) (G ⧸ U) ↦ ω.out ∈ S)).card := by
    rw [← Fintype.card_coe S, Equiv.Perm.neg_one_pow_card_mul_sign,
      TauCeti.orbitCount_eq_natCard_orbitRelQuotient_zpowers,
      Nat.card_congr
        (MulAction.subsetOrbitEquiv S (fun x ↦ MulAction.mem_stabilizer_iff.mp x.property) y),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsign, character_subsetWreathRep, character_subsetWreathRep]
  congr 1
  rw [Finset.prod_neg]

private theorem neg_one_pow_mul_stabilizerRep_character_conj {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) (g r : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))]
    (hr : r⁻¹ * g * r ∈ MulAction.stabilizer G S) :
    (-1 : k) ^ S.card * (stabilizerRep U s S A B).character ⟨r⁻¹ * g * r, hr⟩ =
      evalOrbitFactor U s A B g (r • S) := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U))
  rw [neg_one_pow_mul_stabilizerRep_character, evalOrbitFactor, evalOrbitFactor]
  simp_rw [Finset.prod_filter]
  congr 1
  · refine Fintype.prod_equiv (MulAction.conjOrbitEquiv (α := G ⧸ U) g r) _ _ fun ω ↦ ?_
    have hm := (MulAction.conjOrbitEquiv_out_mem_smul_iff hr ω).symm
    by_cases hω : ω.out ∈ S
    · simp only [hω, hm.mp hω, ↓reduceIte,
        apply_conj_pow_minimalPeriod_conjOrbitEquiv (fun u v ↦ B.char_conj u v)
          (U.leftTransversalRep s) (U.leftTransversalRep_mk s) g r ω]
    · have hmr : (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∉ r • S := fun h ↦ hω (hm.mpr h)
      simp only [hω, hmr, ↓reduceIte]
  · refine Fintype.prod_equiv (MulAction.conjOrbitEquiv (α := G ⧸ U) g r) _ _ fun ω ↦ ?_
    have hm := (MulAction.conjOrbitEquiv_out_mem_smul_iff hr ω).symm
    by_cases hω : ω.out ∈ S
    · have hmr : (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∈ r • S := hm.mp hω
      simp only [Finset.mem_compl, hω, hmr, not_true_eq_false, ↓reduceIte]
    · have hmr : (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∉ r • S := fun h ↦ hω (hm.mpr h)
      simp only [Finset.mem_compl, hω, hmr, not_false_eq_true, ↓reduceIte,
        apply_conj_pow_minimalPeriod_conjOrbitEquiv (fun u v ↦ A.char_conj u v)
          (U.leftTransversalRep s) (U.leftTransversalRep_mk s) g r ω]

private theorem indClassFun_stabilizerRep_apply {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) [(MulAction.stabilizer G S).FiniteIndex] [Fintype (MulAction.orbit G S)]
    (A B : FDRep k U) (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    (-1 : k) ^ S.card *
        (MulAction.stabilizer G S).indClassFun (stabilizerRep U s S A B).character g =
      ∑ T : MulAction.orbit G S,
        if g • T.val = T.val then evalOrbitFactor U s A B g T.val else 0 := by
  let := Fintype.ofFinite (G ⧸ MulAction.stabilizer G S)
  rw [Subgroup.indClassFun_apply, Finset.mul_sum]
  refine (Fintype.sum_equiv (MulAction.orbitEquivQuotientStabilizer G S) _ _ fun T ↦ ?_).symm
  set r : G := (MulAction.orbitEquivQuotientStabilizer G S T).out
  have hr_smul : r • S = T.val := by
    have hmk : (r : G ⧸ MulAction.stabilizer G S) = MulAction.orbitEquivQuotientStabilizer G S T :=
      QuotientGroup.out_eq' _
    have hs := congrArg
      (fun q ↦ ((MulAction.orbitEquivQuotientStabilizer G S).symm q : Finset (G ⧸ U))) hmk
    rw [Equiv.symm_apply_apply] at hs
    rw [← MulAction.orbitEquivQuotientStabilizer_symm_apply G S r]
    exact hs
  have hiff : r⁻¹ * g * r ∈ MulAction.stabilizer G S ↔ g • T.val = T.val := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hr_smul, inv_smul_eq_iff, hr_smul]
  split_ifs with hg hmem hmem
  · rw [neg_one_pow_mul_stabilizerRep_character_conj, ← hr_smul]
  · exact absurd (hiff.mpr hg) hmem
  · exact absurd (hiff.mp hmem) hg
  · simp

private noncomputable def orbitStabTerm {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (A B : FDRep k U) (O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U))) : G → k :=
  let := MulAction.finiteIndex_stabilizer (G := G) O.out
  (-1 : k) ^ O.out.card • (MulAction.stabilizer G O.out).indClassFun
    (stabilizerRep U s O.out A B).character

private theorem orbitStabTerm_mem_virtualCharacters {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)]
    (s : U.LeftTransversal) (A B : FDRep k U)
    (O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U))) :
    orbitStabTerm U s A B O ∈ TauCeti.virtualCharacters k G := by
  let := MulAction.finiteIndex_stabilizer (G := G) O.out
  dsimp only [orbitStabTerm]
  rw [Subgroup.indClassFun_ofFDRep_character]
  exact TauCeti.neg_one_pow_smul_mem_virtualCharacters _ (TauCeti.character_mem_virtualCharacters _)

private theorem sum_orbitStabTerm_apply {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (A B : FDRep k U) (g : G)
    [Fintype (MulAction.orbitRel.Quotient G (Finset (G ⧸ U)))]
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    (∑ O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)), orbitStabTerm U s A B O) g =
      ∑ T : {T : Finset (G ⧸ U) // g • T = T}, evalOrbitFactor U s A B g T.val := by
  rw [Finset.sum_apply]
  have hterm :
      (∑ O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)), orbitStabTerm U s A B O g) =
        ∑ O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)),
          let := Fintype.ofFinite (MulAction.orbit G O.out)
          ∑ T : MulAction.orbit G O.out,
            if g • T.val = T.val then evalOrbitFactor U s A B g T.val else 0 := by
    refine Finset.sum_congr rfl fun O _ ↦ ?_
    let := MulAction.finiteIndex_stabilizer (G := G) O.out
    let := Fintype.ofFinite (MulAction.orbit G O.out)
    exact indClassFun_stabilizerRep_apply U s O.out A B g
  have hsig :
      (∑ O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)),
          let := Fintype.ofFinite (MulAction.orbit G O.out)
          ∑ T : MulAction.orbit G O.out,
            if g • T.val = T.val then evalOrbitFactor U s A B g T.val else 0) =
        ∑ T : Finset (G ⧸ U), if g • T = T then evalOrbitFactor U s A B g T else 0 := by
    let := fun O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)) ↦
      Fintype.ofFinite (MulAction.orbit G O.out)
    rw [← Fintype.sum_sigma']
    exact Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits G (Finset (G ⧸ U))).symm _ _
      fun _ ↦ rfl
  rw [hterm, hsig, ← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun T : Finset (G ⧸ U) ↦ g • T = T)
    (p := fun T : Finset (G ⧸ U) ↦ g • T = T) (fun T ↦ by simp)
    fun T ↦ evalOrbitFactor U s A B g T

/-- **Tensor induction preserves virtual characters.** For any finite-index subgroup `U ≤ G` and
any virtual character `ψ ∈ TauCeti.virtualCharacters k U` over any field `k`, the tensor-induced
function `U.tensorIndClassFun ψ` belongs to `TauCeti.virtualCharacters k G`. -/
theorem tensorIndClassFun_mem_virtualCharacters {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] {ψ : U → k} (hψ : ψ ∈ TauCeti.virtualCharacters k U) :
    U.tensorIndClassFun ψ ∈ TauCeti.virtualCharacters k G := by
  let := U.fintypeQuotientOfFiniteIndex
  let := Classical.decEq (G ⧸ U)
  let s : U.LeftTransversal :=
    ⟨Set.range Quotient.out, isComplement_range_left QuotientGroup.out_eq'⟩
  obtain ⟨A, B, rfl⟩ := TauCeti.exists_eq_character_sub_character hψ
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient G (Finset (G ⧸ U)))
  suffices heq : U.tensorIndClassFun (A.character - B.character) =
      ∑ O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)), orbitStabTerm U s A B O by
    rw [heq]
    exact AddSubgroup.sum_mem _ fun O _ ↦ orbitStabTerm_mem_virtualCharacters U s A B O
  ext g
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
  let := Classical.decEq (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
  have hfg : ∀ u v : U, (A.character - B.character) (v * u * v⁻¹) = (A.character - B.character) u :=
    fun u v ↦ by simp [A.char_conj, B.char_conj]
  rw [tensorIndClassFun_eq_prod_of_rep U hfg (U.leftTransversalRep s) (U.leftTransversalRep_mk s) g,
    sum_orbitStabTerm_apply]
  have hfilt :
      (∑ T : {T : Finset (G ⧸ U) // g • T = T}, evalOrbitFactor U s A B g T.val) =
        ∑ S : Finset (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U)),
          (∏ ω ∈ S, -B.character ⟨(U.leftTransversalRep s ω.out)⁻¹ *
              g ^ Function.minimalPeriod (g • ·) ω.out * U.leftTransversalRep s ω.out,
              conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s ω.out)⟩) *
          (∏ ω ∈ Sᶜ, A.character ⟨(U.leftTransversalRep s ω.out)⁻¹ *
              g ^ Function.minimalPeriod (g • ·) ω.out * U.leftTransversalRep s ω.out,
              conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s ω.out)⟩) := by
    refine Fintype.sum_equiv (MulAction.fixedFinsetEquivOrbitFinset g) _ _ fun T ↦ ?_
    dsimp only [evalOrbitFactor]
    rw [MulAction.fixedFinsetEquivOrbitFinset_apply]
    congr 2
    ext ω
    simp
  rw [hfilt, ← Fintype.prod_add]
  refine Finset.prod_congr rfl fun ω _ ↦ ?_
  simp [sub_eq_neg_add]

private theorem conjNormal_prod_conj {k G : Type*} [CommMonoid k] [Group G]
    (H : Subgroup G) [H.Normal] {l : ℕ} (x : G) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u)
    (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u) (S : Finset (Fin l)) (u v : H) :
    (∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) (v * u * v⁻¹))) =
      ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) u) := by
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_mul, map_inv]
  split_ifs <;> [exact hψ₂ _ _; exact hψ₁ _ _]

private theorem indClassFun_conjNormal_prod_apply {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {x : G} (hx : x ∉ H) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u) (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u)
    (S : Finset (Fin l)) (h : H) :
    H.indClassFun
        (fun h' ↦ ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) h'))
        (h : G) =
      ∑ j : Fin l, ∏ i : Fin l,
        (if i ∈ (finRotate l ^ (j : ℕ)) • S then ψ₂ else ψ₁)
          (MulAut.conjNormal (x ^ (i : ℕ)) h) := by
  classical
  have : NeZero l := ⟨hl.ne_zero⟩
  let := H.fintypeQuotientOfFiniteIndex
  let f : H → k := fun h' ↦
    ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) h')
  have hf : ∀ y s : H, f (s * y * s⁻¹) = f y :=
    fun y s ↦ conjNormal_prod_conj H x hψ₁ hψ₂ S y s
  rw [Subgroup.indClassFun_eq_sum_of_smul_eq_self_mem H f (h : G) Finset.univ
    fun _ _ ↦ Finset.mem_univ _]
  refine (Fintype.sum_equiv (Subgroup.quotientPrimeEquiv H hl hH hx) _ _ fun j ↦ ?_).symm
  rw [Function.indTerm_eq_of_mk_eq_of_conj f hf _ _ _
    ((QuotientGroup.out_eq' _).trans (Subgroup.quotientPrimeEquiv_apply H hl hH hx j))]
  have hmem : ((x ^ (j : ℕ))⁻¹)⁻¹ * (h : G) * (x ^ (j : ℕ))⁻¹ ∈ H := by
    rw [inv_inv]
    exact (MulAut.conjNormal (x ^ (j : ℕ)) h).property
  have heq : (⟨((x ^ (j : ℕ))⁻¹)⁻¹ * (h : G) * (x ^ (j : ℕ))⁻¹, hmem⟩ : H) =
      MulAut.conjNormal (x ^ (j : ℕ)) h := by
    apply Subtype.ext
    dsimp only
    rw [inv_inv, MulAut.conjNormal_apply]
  rw [Function.indTerm_apply, dite_eq_left_of_eq_true (eq_true hmem), heq]
  dsimp only [f]
  refine (Fintype.prod_equiv (Equiv.addRight j) _ _ fun i ↦ ?_).symm
  rw [Equiv.coe_addRight]
  have hmod := MulAut.conjNormal_pow_conjNormal_pow (hH ▸ H.pow_index_mem x) h i j
  have hval : (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ))
        (MulAut.conjNormal (x ^ (j : ℕ)) h)) =
      (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ ((i + j : Fin l) : ℕ)) h) := by
    rw [hmod]
    split_ifs <;> [exact hψ₂ _ _; exact hψ₁ _ _]
  rw [hval]
  have hrot : (finRotate l ^ (j : ℕ)) i = i + j := by
    ext
    simp [Fin.coe_finRotate_pow, Fin.val_add]
  have hmem_rot : i + j ∈ (finRotate l ^ (j : ℕ)) • S ↔ i ∈ S := by
    rw [← hrot]
    exact Finset.smul_mem_smul_finset_iff (finRotate l ^ (j : ℕ))
  simp only [hmem_rot]

private theorem sum_orbit_finRotate_eq {k : Type*} [AddCommMonoid k] {l : ℕ} (hl : l.Prime)
    {S : Finset (Fin l)} (hne : S.Nonempty) (hS : S ≠ Finset.univ)
    (F : Finset (Fin l) → k) [Fintype (MulAction.orbit (Subgroup.zpowers (finRotate l)) S)] :
    (∑ j : Fin l, F ((finRotate l ^ (j : ℕ)) • S)) =
      ∑ T : MulAction.orbit (Subgroup.zpowers (finRotate l)) S, F T.val :=
  Fintype.sum_equiv (TauCeti.finRotateOrbitEquiv hl hne hS) _ _ fun j ↦ by
    rw [TauCeti.finRotateOrbitEquiv_apply]

private theorem sum_finRotate_orbit_indClassFun_eq {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {x : G} (hx : x ∉ H) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u) (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)))]
    (h : H) :
    (∑ O ∈ Finset.univ.filter (fun O : MulAction.orbitRel.Quotient
          (Subgroup.zpowers (finRotate l)) (Finset (Fin l)) ↦
          O.out.Nonempty ∧ O.out ≠ Finset.univ),
        (-1 : k) ^ O.out.card * H.indClassFun
          (fun h' ↦ ∏ i : Fin l, (if i ∈ O.out then ψ₂ else ψ₁)
            (MulAut.conjNormal (x ^ (i : ℕ)) h')) (h : G)) =
      ∑ S : Finset (Fin l),
        if S.Nonempty ∧ S ≠ Finset.univ then
          (-1 : k) ^ S.card *
            ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) h)
        else 0 := by
  classical
  let φ : Finset (Fin l) → H → k := fun S h' ↦
    ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) h')
  rw [Finset.sum_filter]
  have horb :
      (∑ O : MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)),
          if O.out.Nonempty ∧ O.out ≠ Finset.univ then
            (-1 : k) ^ O.out.card * H.indClassFun (φ O.out) (h : G) else 0) =
        ∑ O : MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)),
          let := Fintype.ofFinite (MulAction.orbit (Subgroup.zpowers (finRotate l)) O.out)
          ∑ T : MulAction.orbit (Subgroup.zpowers (finRotate l)) O.out,
            if T.val.Nonempty ∧ T.val ≠ Finset.univ then (-1 : k) ^ T.val.card * φ T.val h
              else 0 := by
    refine Finset.sum_congr rfl fun O _ ↦ ?_
    let := Fintype.ofFinite (MulAction.orbit (Subgroup.zpowers (finRotate l)) O.out)
    by_cases hO : O.out.Nonempty ∧ O.out ≠ Finset.univ
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hO),
        indClassFun_conjNormal_prod_apply H hl hH hx hψ₁ hψ₂ O.out h]
      refine (congrArg ((-1 : k) ^ O.out.card * ·)
        (sum_orbit_finRotate_eq hl hO.1 hO.2 fun T ↦ φ T h)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ ↦ ?_
      have hrel := MulAction.orbitRel_apply.mpr T.property
      rw [MulAction.card_eq_of_orbitRel_finset hrel, ite_eq_left_of_eq_true _ _
        (eq_true ((MulAction.nonempty_and_ne_univ_iff_of_orbitRel_finset hrel).mpr hO))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hO)]
      refine (Finset.sum_eq_zero fun T _ ↦ ?_).symm
      have hrel := MulAction.orbitRel_apply.mpr T.property
      have hnt : ¬ (T.val.Nonempty ∧ T.val ≠ Finset.univ) := fun hT ↦
        hO ((MulAction.nonempty_and_ne_univ_iff_of_orbitRel_finset hrel).mp hT)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnt)]
  rw [horb]
  dsimp only [φ]
  let := fun O : MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)) ↦
    Fintype.ofFinite (MulAction.orbit (Subgroup.zpowers (finRotate l)) O.out)
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv
    (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers (finRotate l)) (Finset (Fin l))).symm
    _ _ fun _ ↦ rfl

private theorem tensorIndClassFun_sub_of_index_prime_mem {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {x : G} (hx : x ∉ H) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u) (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)))]
    (h : H) :
    H.tensorIndClassFun (ψ₁ - ψ₂) h =
      H.tensorIndClassFun ψ₁ h +
        (-1 : k) ^ l * (((H.quotientSign h : ℤ) : k) * H.tensorIndClassFun ψ₂ h) +
        ∑ O ∈ Finset.univ.filter (fun O : MulAction.orbitRel.Quotient
            (Subgroup.zpowers (finRotate l)) (Finset (Fin l)) ↦
            O.out.Nonempty ∧ O.out ≠ Finset.univ),
          (-1 : k) ^ O.out.card * H.indClassFun
            (fun h' ↦ ∏ i : Fin l, (if i ∈ O.out then ψ₂ else ψ₁)
              (MulAut.conjNormal (x ^ (i : ℕ)) h')) (h : G) := by
  classical
  have hsub : ∀ u v : H, (ψ₁ - ψ₂) (v * u * v⁻¹) = (ψ₁ - ψ₂) u :=
    fun u v ↦ by simp [hψ₁, hψ₂]
  rw [tensorIndClassFun_apply_of_mem_of_index_prime H hl hH hx hsub h,
    tensorIndClassFun_apply_of_mem_of_index_prime H hl hH hx hψ₁ h,
    tensorIndClassFun_apply_of_mem_of_index_prime H hl hH hx hψ₂ h,
    quotientSign_apply_of_mem H h.property, Units.val_one, Int.cast_one, one_mul,
    sum_finRotate_orbit_indClassFun_eq H hl hH hx hψ₁ hψ₂ h]
  simp only [Pi.sub_apply]
  rw [Finset.prod_sub, Finset.powerset_univ]
  have hsplit : ∀ S : Finset (Fin l),
      (-1 : k) ^ S.card * (∏ i ∈ Finset.univ \ S, ψ₁ (MulAut.conjNormal (x ^ (i : ℕ)) h)) *
          ∏ i ∈ S, ψ₂ (MulAut.conjNormal (x ^ (i : ℕ)) h) =
        (if S = ∅ then ∏ i : Fin l, ψ₁ (MulAut.conjNormal (x ^ (i : ℕ)) h) else 0) +
        (if S = Finset.univ then (-1 : k) ^ l * ∏ i : Fin l,
            ψ₂ (MulAut.conjNormal (x ^ (i : ℕ)) h) else 0) +
        (if S.Nonempty ∧ S ≠ Finset.univ then (-1 : k) ^ S.card *
            ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) h)
          else 0) := by
    intro S
    have hne_u : (Finset.univ : Finset (Fin l)) ≠ ∅ := by
      intro he
      have hc := congrArg Finset.card he
      simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty] at hc
      exact hl.ne_zero hc
    by_cases h0 : S = ∅
    · subst h0; simp [hne_u.symm]
    · by_cases hu : S = Finset.univ
      · subst hu; simp [hne_u]
      · have hne : S.Nonempty := Finset.ne_empty_iff_nonempty.mp h0
        simp only [h0, hu, hne, ne_eq, not_false_eq_true, and_self, ↓reduceIte, zero_add, ite_apply,
          Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
          mul_assoc, mul_comm (∏ _ ∈ Finset.univ \ S, _)]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **Prime-index decomposition of tensor induction.** For a normal subgroup `H ≤ G` of
prime index `l`, `x ∉ H`, and `H`-conjugation-invariant functions `ψ₁, ψ₂ : H → k` over a
commutative ring `k`, `H.tensorIndClassFun (ψ₁ - ψ₂)` decomposes as `H.tensorIndClassFun ψ₁`,
`(-1) ^ l • (H.quotientSign * H.tensorIndClassFun ψ₂)`, and the alternating sum over
cyclic-shift orbits on nonempty proper subsets of `Fin l` of `H.indClassFun` applied to the twisted
product along the subset. -/
theorem tensorIndClassFun_sub_of_index_prime {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {x : G} (hx : x ∉ H) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u) (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)))] :
    H.tensorIndClassFun (ψ₁ - ψ₂) =
      H.tensorIndClassFun ψ₁ +
        (-1 : k) ^ l • ((fun g ↦ ((H.quotientSign g : ℤ) : k)) *
          H.tensorIndClassFun ψ₂) +
        ∑ O ∈ Finset.univ.filter (fun O : MulAction.orbitRel.Quotient
            (Subgroup.zpowers (finRotate l)) (Finset (Fin l)) ↦
            O.out.Nonempty ∧ O.out ≠ Finset.univ),
          (-1 : k) ^ O.out.card • H.indClassFun
            fun h ↦ ∏ i : Fin l, (if i ∈ O.out then ψ₂ else ψ₁)
              (MulAut.conjNormal (x ^ (i : ℕ)) h) := by
  ext g
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Finset.sum_apply, smul_eq_mul]
  by_cases hg : g ∈ H
  · exact tensorIndClassFun_sub_of_index_prime_mem H hl hH hx hψ₁ hψ₂ ⟨g, hg⟩
  · have hgl : g ^ l ∈ H := hH ▸ H.pow_index_mem g
    have hsub : ∀ u v : H, (ψ₁ - ψ₂) (v * u * v⁻¹) = (ψ₁ - ψ₂) u :=
      fun u v ↦ by simp [hψ₁, hψ₂]
    rw [tensorIndClassFun_apply_of_notMem_of_index_prime H hl hH hsub hg (h := ⟨g ^ l, hgl⟩) rfl,
      tensorIndClassFun_apply_of_notMem_of_index_prime H hl hH hψ₁ hg (h := ⟨g ^ l, hgl⟩) rfl,
      tensorIndClassFun_apply_of_notMem_of_index_prime H hl hH hψ₂ hg (h := ⟨g ^ l, hgl⟩) rfl,
      quotientSign_apply_of_notMem_of_index_prime H hl hH hg]
    have hpow : (-1 : k) ^ l * ((((-1 : ℤˣ) ^ (l - 1) : ℤˣ) : ℤ) : k) = -1 := by
      have hlpos : 1 ≤ l := hl.pos
      have hadd : l + (l - 1) = 1 + 2 * (l - 1) := by omega
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg,
        Int.cast_one, ← pow_add, hadd, pow_add, pow_mul]
      simp
    simp only [Pi.sub_apply, H.indClassFun_apply_of_notMem _ hg, mul_zero, Finset.sum_const_zero,
      add_zero, ← mul_assoc, hpow, neg_one_mul, ← sub_eq_add_neg]

end Subgroup
