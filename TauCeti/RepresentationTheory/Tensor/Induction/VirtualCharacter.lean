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
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.ClassFunction
public import TauCeti.RepresentationTheory.Tensor.Induction.Trace

import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.GroupAction.Orbit.Basic
import TauCeti.GroupTheory.GroupAction.Orbit.Finset
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate
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

In prime index `l` for a normal subgroup `H ≤ G`, this specializes to the explicit decomposition
`Subgroup.tensorIndClassFun_sub_of_index_prime` of `H.tensorIndClassFun (ψ₁ - ψ₂)` using the sign
character `H.primeIndexSignChar hl hH` and induced class functions indexed by cyclic-shift orbits
on nonempty proper subsets of `Fin l`.

## Main definitions

* `Subgroup.primeIndexSignChar`: the linear character of `G` factoring through `G ⧸ H` sending
  `g ∈ H` to `1` and `g ∉ H` to `(-1) ^ (l - 1)` when `H` has prime index `l`.

## Main results

* `Subgroup.tensorIndClassFun_character_mem_virtualCharacters`: tensor induction of a genuine
  character of a finite-index subgroup is a virtual character of `G`.
* `Subgroup.tensorIndClassFun_mem_virtualCharacters`: tensor induction of any virtual character of
  a finite-index subgroup is a virtual character of `G`.
* `Subgroup.tensorIndClassFun_sub_of_index_prime`: explicit prime-index virtual-character
  decomposition of `H.tensorIndClassFun (ψ₁ - ψ₂)`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3.
* L. Alpöge, *The Riemann Hypothesis for Dirichlet L-Functions* (2026).
-/

public section

open scoped Pointwise CategoryTheory.MonoidalCategory TensorProduct

namespace Subgroup

private theorem neg_one_pow_smul_mem_virtualCharacters {k G : Type*} [Field k] [Monoid G]
    (n : ℕ) {f : G → k} (hf : f ∈ TauCeti.virtualCharacters k G) :
    ((-1 : k) ^ n • f) ∈ TauCeti.virtualCharacters k G := by
  rcases Nat.even_or_odd n with h | h
  · simpa [h.neg_one_pow] using hf
  · simpa [h.neg_one_pow] using neg_mem hf

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

private theorem neg_one_pow_card_mul_sign {k α : Type*} [CommRing k]
    [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α)] :
    (-1 : k) ^ Fintype.card α * ((Equiv.Perm.sign σ : ℤ) : k) =
      (-1 : k) ^ Fintype.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α) := by
  have qEquiv : Quotient (Equiv.Perm.SameCycle.setoid σ) ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α :=
    Quotient.congrRight fun x y ↦ by
      rw [MulAction.orbitRel_apply, ← Equiv.Perm.sameCycle_iff_mem_orbit_zpowers]
      exact Equiv.Perm.sameCycle_comm
  let c := Fintype.card (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α)
  have hc : TauCeti.orbitCount σ = c := by
    rw [TauCeti.orbitCount_def, Nat.card_congr qEquiv, Nat.card_eq_fintype_card]
  have hle : c ≤ Fintype.card α :=
    Fintype.card_le_of_injective Quotient.out Quotient.out_injective
  have hadd : Fintype.card α + (Fintype.card α - c) = c + 2 * (Fintype.card α - c) := by omega
  rw [Equiv.Perm.sign_eq_neg_one_pow_card_sub_orbitCount, hc, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one,
    ← pow_add, hadd, pow_add, pow_mul]
  simp [c]

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
    rw [Equiv.Perm.smul_def, Subgroup.monomialHom_right_inv]
    rfl

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
    (hT : ∀ x : H, (x : G) • T = T) (x : H) (q₀ : ↥T) (hper : (x.val ^
      Function.minimalPeriod (x.val • ·) q₀.val) • q₀.val = q₀.val) :
    (List.ofFn fun t : Fin (Function.minimalPeriod ((MulAction.subsetPermOn H T hT x) • ·) q₀) ↦
        (subsetMonomialHom U s H T hT x).left
          (((MulAction.subsetPermOn H T hT x)⁻¹ ^ (t : ℕ)) q₀)).prod =
      ⟨(U.leftTransversalRep s q₀.val)⁻¹ *
          x.val ^ Function.minimalPeriod (x.val • ·) q₀.val * U.leftTransversalRep s q₀.val,
        conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s q₀.val)⟩ := by
  have hm : Function.minimalPeriod ((MulAction.subsetPermOn H T hT x) • ·) q₀ =
      Function.minimalPeriod (x.val • ·) q₀.val :=
    MulAction.subsetPermOn_minimalPeriod hT x q₀
  apply Subtype.ext
  rw [Subgroup.val_list_prod, List.map_ofFn]
  have hlist :
      (List.ofFn (Subtype.val ∘ fun t :
          Fin (Function.minimalPeriod ((MulAction.subsetPermOn H T hT x) • ·) q₀) ↦
          (subsetMonomialHom U s H T hT x).left
            (((MulAction.subsetPermOn H T hT x)⁻¹ ^ (t : ℕ)) q₀))) =
        List.ofFn fun t : Fin (Function.minimalPeriod (x.val • ·) q₀.val) ↦
          TauCeti.lWord U (U.leftTransversalRep s) ((x.val⁻¹ ^ (t : ℕ)) • q₀.val) x.val := by
    refine List.ext_get (by simpa only [List.length_ofFn] using hm) fun i _ _ ↦ ?_
    have ha : (((MulAction.subsetPermOn H T hT x)⁻¹ ^ (i : ℕ)) q₀).val =
        (x.val⁻¹ ^ (i : ℕ)) • q₀.val := by
      rw [← map_inv, ← zpow_natCast (MulAction.subsetPermOn H T hT x⁻¹),
        MulAction.subsetPermOn_zpow_val hT x⁻¹ (i : ℕ) q₀, Subgroup.coe_inv, zpow_natCast]
    simp only [List.getElem_ofFn, List.get_eq_getElem, Function.comp_apply]
    -- Unfold `(subsetMonomialHom ... x).left` to `(U.monomialHom s x.val).left`.
    change ((U.monomialHom s x.val).left
      (((MulAction.subsetPermOn H T hT x)⁻¹ ^ (i : ℕ)) q₀).val : G) = _
    rw [Subgroup.monomialHom_left, ha]
  rw [hlist, Subgroup.lWord_list_ofFn_prod]
  have hinv : (x.val⁻¹ ^ Function.minimalPeriod (x.val • ·) q₀.val) • q₀.val = q₀.val := by
    rw [inv_pow]
    exact inv_smul_eq_iff.mpr hper.symm
  rw [hinv]

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
  have hper : (x.val ^ Function.minimalPeriod (x.val • ·) q.out.val) • q.out.val = q.out.val := by
    rw [← smul_iterate_apply]
    exact Function.isPeriodicPt_minimalPeriod (x.val • ·) q.out.val
  have hm := subsetMonomialHom_orbit_prod U s T hT x q.out hper
  exact (congrArg (fun u : U ↦ LinearMap.trace k V (V.ρ u)) hm).trans
    (apply_conj_pow_minimalPeriod_eq_of_orbitRel (fun u v ↦ V.char_conj u v) x.val
      (MulAction.subsetOrbitEquiv_out_rel T hT x q) (U.leftTransversalRep_mk s q.out.val)
      (U.leftTransversalRep_mk s (e q).val.out)).symm

private noncomputable def stabilizerRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) : FDRep k (MulAction.stabilizer G S) :=
  let ε : MulAction.stabilizer G S →* kˣ :=
    (Units.map (Int.castRingHom k).toMonoidHom).comp
      (Equiv.Perm.sign.comp (MulAction.subsetPermOn _ S (MulAction.stabilizer_smul_finset S)))
  FDRep.ofLinearCharacter ε ⊗
    subsetWreathRep U s _ S (MulAction.stabilizer_smul_finset S) B ⊗
    subsetWreathRep U s _ Sᶜ (MulAction.stabilizer_smul_compl S) A

private theorem neg_one_pow_mul_stabilizerRep_character {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) (y : MulAction.stabilizer G S)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers y.val) (G ⧸ U))] :
    (-1 : k) ^ S.card * (stabilizerRep U s S A B).character y =
      (∏ ω ∈ Finset.univ.filter (fun ω :
          MulAction.orbitRel.Quotient (Subgroup.zpowers y.val) (G ⧸ U) ↦ ω.out ∈ S),
        -B.character
          ⟨(U.leftTransversalRep s ω.out)⁻¹ * y.val ^ Function.minimalPeriod (y.val • ·) ω.out *
              U.leftTransversalRep s ω.out,
            conj_pow_minimalPeriod_mem U y.val (U.leftTransversalRep_mk s ω.out)⟩) *
      (∏ ω ∈ Finset.univ.filter (fun ω :
          MulAction.orbitRel.Quotient (Subgroup.zpowers y.val) (G ⧸ U) ↦ ω.out ∈ Sᶜ),
        A.character
          ⟨(U.leftTransversalRep s ω.out)⁻¹ * y.val ^ Function.minimalPeriod (y.val • ·) ω.out *
              U.leftTransversalRep s ω.out,
            conj_pow_minimalPeriod_mem U y.val (U.leftTransversalRep_mk s ω.out)⟩) := by
  let := Fintype.ofFinite
    (MulAction.orbitRel.Quotient
      (Subgroup.zpowers (MulAction.subsetPermOn _ S (MulAction.stabilizer_smul_finset S) y)) ↥S)
  dsimp only [stabilizerRep]
  have hε : ∀ n : ℤ, (Int.castRingHom k).toMonoidHom n = (n : k) := fun _ ↦ rfl
  simp only [FDRep.char_tensor, Pi.mul_apply, FDRep.char_ofLinearCharacter, MonoidHom.comp_apply,
    Units.coe_map, hε, ← mul_assoc]
  have hsign : (-1 : k) ^ S.card *
      ((Equiv.Perm.sign (MulAction.subsetPermOn _ S
        (MulAction.stabilizer_smul_finset S) y) : ℤ) : k) =
      (-1 : k) ^ (Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient
          (Subgroup.zpowers y.val) (G ⧸ U) ↦ ω.out ∈ S)).card := by
    rw [← Fintype.card_coe S,
      neg_one_pow_card_mul_sign (MulAction.subsetPermOn _ S
        (MulAction.stabilizer_smul_finset S) y),
      Fintype.card_congr (MulAction.subsetOrbitEquiv S (MulAction.stabilizer_smul_finset S) y),
      Fintype.card_subtype]
  rw [hsign, character_subsetWreathRep, character_subsetWreathRep]
  congr 1
  rw [Finset.prod_neg]

private theorem conjOrbitEquiv_mem_iff {G : Type*} [Group G] (U : Subgroup G)
    [DecidableEq (G ⧸ U)] (S : Finset (G ⧸ U)) (g r : G)
    (hr : r⁻¹ * g * r ∈ MulAction.stabilizer G S)
    (ω : MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U)) :
    ω.out ∈ S ↔ (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∈ r • S := by
  have hgT : g • (r • S) = r • S := by
    have hs : (r⁻¹ * g * r) • S = S := hr
    simpa [mul_smul, smul_inv_smul] using congrArg (r • ·) hs
  have hq : MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω = Quotient.mk'' (r • ω.out) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    exact MulAction.conjOrbitEquiv_mk g r ω.out
  have horb : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U)
      (r • ω.out) (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out :=
    Quotient.exact' (hq.symm.trans (Quotient.out_eq _).symm)
  rw [← MulAction.zpow_smul_mem_of_smul_eq hgT horb, Finset.smul_mem_smul_finset_iff]

private theorem conjOrbitEquiv_monodromy_eq {R G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u)
    (g r : G) (ω : MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U)) :
    f ⟨(U.leftTransversalRep s ω.out)⁻¹ * (r⁻¹ * g * r) ^ Function.minimalPeriod
          ((r⁻¹ * g * r) • ·) ω.out * U.leftTransversalRep s ω.out,
        conj_pow_minimalPeriod_mem U (r⁻¹ * g * r) (U.leftTransversalRep_mk s ω.out)⟩ =
      f ⟨(U.leftTransversalRep s (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out)⁻¹ *
          g ^ Function.minimalPeriod
            (g • ·) (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out *
          U.leftTransversalRep s (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out,
        conj_pow_minimalPeriod_mem U g
          (U.leftTransversalRep_mk s (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out)⟩ := by
  have hq : MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω = Quotient.mk'' (r • ω.out) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    exact MulAction.conjOrbitEquiv_mk g r ω.out
  have horb : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U)
      (r • ω.out) (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out :=
    Quotient.exact' (hq.symm.trans (Quotient.out_eq _).symm)
  have hrep : (QuotientGroup.mk (r * U.leftTransversalRep s ω.out) : G ⧸ U) = r • ω.out := by
    -- Rewrite left multiplication on cosets as the left action of `G` on `G ⧸ U`.
    change r • (QuotientGroup.mk (U.leftTransversalRep s ω.out) : G ⧸ U) = r • ω.out
    rw [U.leftTransversalRep_mk s ω.out]
  refine Eq.trans ?_ (apply_conj_pow_minimalPeriod_eq_of_orbitRel hf g horb hrep
    (U.leftTransversalRep_mk s (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out)).symm
  congr 1
  apply Subtype.ext
  dsimp only
  have hm : Function.minimalPeriod ((r⁻¹ * g * r) • ·) ω.out =
      Function.minimalPeriod (g • ·) (r • ω.out) := by
    simpa [inv_inv, inv_smul_smul] using
      (MulAction.minimalPeriod_conj_smul g r⁻¹ (r • ω.out))
  have hp : (r⁻¹ * g * r) ^ Function.minimalPeriod (g • ·) (r • ω.out) =
      r⁻¹ * g ^ Function.minimalPeriod (g • ·) (r • ω.out) * r := by
    simpa [inv_inv] using (conj_pow (a := r⁻¹) (b := g))
  rw [hm, hp]
  simp [mul_assoc]

private theorem neg_one_pow_mul_stabilizerRep_character_conj {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) (g r : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))]
    (hr : r⁻¹ * g * r ∈ MulAction.stabilizer G S) :
    (-1 : k) ^ S.card * (stabilizerRep U s S A B).character ⟨r⁻¹ * g * r, hr⟩ =
      (∏ ω ∈ Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) ↦
          ω.out ∈ r • S),
        -B.character
          ⟨(U.leftTransversalRep s ω.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) ω.out *
              U.leftTransversalRep s ω.out,
            conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s ω.out)⟩) *
      (∏ ω ∈ Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) ↦
          ω.out ∈ (r • S)ᶜ),
        A.character
          ⟨(U.leftTransversalRep s ω.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) ω.out *
              U.leftTransversalRep s ω.out,
            conj_pow_minimalPeriod_mem U g (U.leftTransversalRep_mk s ω.out)⟩) := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U))
  rw [neg_one_pow_mul_stabilizerRep_character]
  simp_rw [Finset.prod_filter]
  congr 1
  · refine Fintype.prod_equiv (MulAction.conjOrbitEquiv (α := G ⧸ U) g r) _ _ fun ω ↦ ?_
    have hm := conjOrbitEquiv_mem_iff U S g r hr ω
    by_cases hω : ω.out ∈ S
    · simp only [hω, hm.mp hω, ↓reduceIte,
        conjOrbitEquiv_monodromy_eq U s (fun u v ↦ B.char_conj u v) g r ω]
    · have hmr : (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∉ r • S := fun h ↦ hω (hm.mpr h)
      simp only [hω, hmr, ↓reduceIte]
  · refine Fintype.prod_equiv (MulAction.conjOrbitEquiv (α := G ⧸ U) g r) _ _ fun ω ↦ ?_
    have hm := conjOrbitEquiv_mem_iff U S g r hr ω
    by_cases hω : ω.out ∈ S
    · have hmr : (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∈ r • S := hm.mp hω
      simp only [Finset.mem_compl, hω, hmr, not_true_eq_false, ↓reduceIte]
    · have hmr : (MulAction.conjOrbitEquiv (α := G ⧸ U) g r ω).out ∉ r • S := fun h ↦ hω (hm.mpr h)
      simp only [Finset.mem_compl, hω, hmr, not_false_eq_true, ↓reduceIte,
        conjOrbitEquiv_monodromy_eq U s (fun u v ↦ A.char_conj u v) g r ω]

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
    rfl
  · exact absurd (hiff.mpr hg) hmem
  · exact absurd (hiff.mp hmem) hg
  · simp

private theorem selfEquivSigmaOrbits_symm_coe {G α : Type*} [Group G] [MulAction G α]
    (p : Σ q : MulAction.orbitRel.Quotient G α, MulAction.orbit G q.out) :
    (MulAction.selfEquivSigmaOrbits G α).symm p = p.snd.val :=
  rfl

private noncomputable def orbitStabTerm {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [U.FiniteIndex] [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (A B : FDRep k U) (O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U))) : G → k :=
  let := MulAction.stabilizer_finset_finiteIndex (G := G) O.out
  (-1 : k) ^ O.out.card • (MulAction.stabilizer G O.out).indClassFun
    (stabilizerRep U s O.out A B).character

private theorem orbitStabTerm_mem_virtualCharacters {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)]
    (s : U.LeftTransversal) (A B : FDRep k U)
    (O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U))) :
    orbitStabTerm U s A B O ∈ TauCeti.virtualCharacters k G := by
  let := MulAction.stabilizer_finset_finiteIndex (G := G) O.out
  dsimp only [orbitStabTerm]
  rw [Subgroup.indClassFun_ofFDRep_character]
  exact neg_one_pow_smul_mem_virtualCharacters _ (TauCeti.character_mem_virtualCharacters _)

private theorem sum_orbitStabTerm_apply {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [U.FiniteIndex] [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
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
    let := MulAction.stabilizer_finset_finiteIndex (G := G) O.out
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
    exact Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits G (Finset (G ⧸ U))).symm _ _ fun p ↦ by
      rw [selfEquivSigmaOrbits_symm_coe]
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

/-- **Prime-index sign character.** For a normal subgroup `H ≤ G` of prime index `l` and a
commutative ring `k`, the homomorphism `G →* kˣ` sending elements of `H` to `1` and elements
outside `H` to `(-1 : kˣ) ^ (l - 1)`. -/
noncomputable def primeIndexSignChar {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] {l : ℕ} (hl : l.Prime) (hH : H.index = l) : G →* kˣ where
  toFun g := by classical exact if g ∈ H then 1 else (-1 : kˣ) ^ (l - 1)
  map_one' := by classical simp [H.one_mem]
  map_mul' a b := by
    classical
    rcases eq_or_ne l 2 with rfl | hl2
    · by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
      · simp [ha, hb, H.mul_mem ha hb]
      · have hab : a * b ∉ H := fun hab ↦ hb ((H.mul_mem_cancel_left ha).mp hab)
        simp [ha, hb, hab]
      · have hab : a * b ∉ H := fun hab ↦ ha ((H.mul_mem_cancel_right hb).mp hab)
        simp [ha, hb, hab]
      · have : H.FiniteIndex := ⟨hH.symm ▸ hl.ne_zero⟩
        let := H.fintypeQuotientOfFiniteIndex
        have ha1 : (QuotientGroup.mk a : G ⧸ H) ≠ 1 := by
          simpa [QuotientGroup.eq_one_iff] using ha
        have hb1 : (QuotientGroup.mk b : G ⧸ H) ≠ 1 := by
          simpa [QuotientGroup.eq_one_iff] using hb
        have hcard : Fintype.card (G ⧸ H) = 2 := by
          simpa [Subgroup.index_eq_card, Nat.card_eq_fintype_card] using hH
        have huniv : (Finset.univ : Finset (G ⧸ H)) = {1, QuotientGroup.mk a} :=
          (Finset.eq_univ_of_card {1, QuotientGroup.mk a}
            (by rw [Finset.card_pair ha1.symm, hcard])).symm
        have hba : (QuotientGroup.mk b : G ⧸ H) = QuotientGroup.mk a := by
          have hm : (QuotientGroup.mk b : G ⧸ H) ∈ ({1, QuotientGroup.mk a} : Finset (G ⧸ H)) :=
            huniv ▸ Finset.mem_univ _
          simpa [hb1] using hm
        have hab : a * b ∈ H := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hba, ← sq,
            ← Subgroup.orderOf_mk_eq_index_of_prime_of_notMem H hl hH ha, pow_orderOf_eq_one]
        simp [ha, hb, hab]
    · have hodd : l % 2 = 1 := (hl.eq_two_or_odd).resolve_left hl2
      have heven : Even (l - 1) := Nat.even_iff.mpr (by omega)
      have hneg : (-1 : kˣ) ^ (l - 1) = 1 :=
        Units.ext (by simpa using heven.neg_one_pow (α := k))
      simp [hneg]

/-- Evaluating `Subgroup.primeIndexSignChar` on elements of `H` gives `1`. -/
@[simp]
theorem primeIndexSignChar_apply_of_mem {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {g : G} (hg : g ∈ H) :
    H.primeIndexSignChar (k := k) hl hH g = 1 := by
  classical
  simp [primeIndexSignChar, hg]

/-- Evaluating `Subgroup.primeIndexSignChar` outside `H` gives `(-1 : kˣ) ^ (l - 1)`. -/
@[simp]
theorem primeIndexSignChar_apply_of_notMem {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {g : G} (hg : g ∉ H) :
    H.primeIndexSignChar (k := k) hl hH g = (-1 : kˣ) ^ (l - 1) := by
  classical
  simp [primeIndexSignChar, hg]

private theorem prod_sub_eq_sum_finset_ite {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    (a b : ι → k) :
    ∏ i : ι, (a i - b i) =
      ∑ S : Finset ι, (-1 : k) ^ S.card * ∏ i : ι, if i ∈ S then b i else a i := by
  have hsub : (fun i : ι ↦ a i - b i) = fun i : ι ↦ (-b i) + a i :=
    funext fun i ↦ by rw [sub_eq_neg_add, add_comm]
  rw [hsub, Fintype.prod_add]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [Finset.prod_neg, mul_assoc]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
  congr 1 <;> refine Finset.prod_congr (by ext i; simp) fun i hi ↦ ?_
  · simp at hi
    simp [hi]
  · simp at hi
    simp [hi]

private theorem zpowers_finRotate_stabilizer_eq_bot {l : ℕ} (hl : l.Prime)
    {S : Finset (Fin l)} (hne : S.Nonempty) (hS : S ≠ Finset.univ) :
    MulAction.stabilizer (Subgroup.zpowers (finRotate l)) S = ⊥ := by
  have : NeZero l := ⟨hl.ne_zero⟩
  have hcard : Nat.card (Subgroup.zpowers (finRotate l)) = l := by
    rw [Nat.card_zpowers, TauCeti.orderOf_finRotate hl.ne_zero]
  have : Fact (Nat.card (Subgroup.zpowers (finRotate l))).Prime := ⟨by rw [hcard]; exact hl⟩
  refine (Subgroup.eq_bot_or_eq_top_of_prime_card _).resolve_right fun htop ↦ hS ?_
  obtain ⟨a, ha⟩ := hne
  refine Finset.eq_univ_of_forall fun b ↦ ?_
  let k : ℕ := (b - a : Fin l).val
  have hmem : (⟨finRotate l ^ k,
      (Subgroup.zpowers (finRotate l)).pow_mem (Subgroup.mem_zpowers _) _⟩ :
      Subgroup.zpowers (finRotate l)) ∈
      MulAction.stabilizer (Subgroup.zpowers (finRotate l)) S :=
    htop ▸ Subgroup.mem_top _
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hmem
  have hsm := Finset.smul_mem_smul_finset (a := finRotate l ^ k) ha
  have hrot : (finRotate l ^ k) • a = b := by
    rw [Equiv.Perm.smul_def]
    ext
    have heq : (a + (b - a) : Fin l) = b := add_sub_cancel a b
    rw [Fin.coe_finRotate_pow, ← heq, Fin.val_add]
  rw [hmem, hrot] at hsm
  exact hsm

private theorem conjNormal_prod_conj {k G : Type*} [CommMonoid k] [Group G]
    (H : Subgroup G) [H.Normal] {l : ℕ} (x : G) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u)
    (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u) (S : Finset (Fin l)) (u v : H) :
    (∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) (v * u * v⁻¹))) =
      ∏ i : Fin l, (if i ∈ S then ψ₂ else ψ₁) (MulAut.conjNormal (x ^ (i : ℕ)) u) := by
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_mul, map_inv]
  split_ifs <;> [exact hψ₂ _ _; exact hψ₁ _ _]

private theorem conjNormal_pow_eq_conjNormal_mod {G : Type*} [Group G] (H : Subgroup G)
    [H.Normal] {l : ℕ} (hl : l.Prime) (hH : H.index = l) {x : G} (hx : x ∉ H)
    (h : H) (i j : Fin l) :
    let q := ((i : ℕ) + (j : ℕ)) / l
    have hxl : x ^ l ∈ H := by
      have ho := Subgroup.orderOf_mk_eq_index_of_prime_of_notMem H hl hH hx
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← ho, pow_orderOf_eq_one]
    let u : H := ⟨x ^ l, hxl⟩ ^ q
    MulAut.conjNormal (x ^ (i : ℕ)) (MulAut.conjNormal (x ^ (j : ℕ)) h) =
      u * MulAut.conjNormal (x ^ ((i + j : Fin l) : ℕ)) h * u⁻¹ := by
  intro q hxl u
  have : NeZero l := ⟨hl.ne_zero⟩
  apply Subtype.ext
  have hdiv : ((i : ℕ) + (j : ℕ)) = l * q + ((i + j : Fin l) : ℕ) := by
    rw [Fin.val_add]
    exact (Nat.div_add_mod ((i : ℕ) + (j : ℕ)) l).symm
  have hpow : x ^ (i : ℕ) * x ^ (j : ℕ) = (x ^ l) ^ q * x ^ ((i + j : Fin l) : ℕ) := by
    rw [← pow_add, hdiv, pow_add, pow_mul]
  have hu : (u : G) = (x ^ l) ^ q := rfl
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, MulAut.conjNormal_apply, hu]
  calc
    x ^ (i : ℕ) * (x ^ (j : ℕ) * (h : G) * (x ^ (j : ℕ))⁻¹) * (x ^ (i : ℕ))⁻¹ =
        (x ^ (i : ℕ) * x ^ (j : ℕ)) * (h : G) * (x ^ (i : ℕ) * x ^ (j : ℕ))⁻¹ := by group
    _ = ((x ^ l) ^ q * x ^ ((i + j : Fin l) : ℕ)) * (h : G) *
          ((x ^ l) ^ q * x ^ ((i + j : Fin l) : ℕ))⁻¹ := by rw [hpow]
    _ = (x ^ l) ^ q * (x ^ ((i + j : Fin l) : ℕ) * (h : G) *
          (x ^ ((i + j : Fin l) : ℕ))⁻¹) * ((x ^ l) ^ q)⁻¹ := by group

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
    rw [inv_inv]
    rfl
  rw [Function.indTerm_apply, dite_eq_left_of_eq_true (eq_true hmem), heq]
  dsimp only [f]
  refine (Fintype.prod_equiv (Equiv.addRight j) _ _ fun i ↦ ?_).symm
  rw [Equiv.coe_addRight]
  have hmod := conjNormal_pow_eq_conjNormal_mod H hl hH hx h i j
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
      ∑ T : MulAction.orbit (Subgroup.zpowers (finRotate l)) S, F T.val := by
  have : NeZero l := ⟨hl.ne_zero⟩
  have hord : orderOf (finRotate l) = l := TauCeti.orderOf_finRotate hl.ne_zero
  have hstab := zpowers_finRotate_stabilizer_eq_bot hl hne hS
  let g : Fin l → MulAction.orbit (Subgroup.zpowers (finRotate l)) S := fun j ↦
    ⟨(finRotate l ^ (j : ℕ)) • S,
      ⟨finRotate l ^ (j : ℕ),
        (Subgroup.zpowers (finRotate l)).pow_mem (Subgroup.mem_zpowers _) _⟩, rfl⟩
  have hbij : Function.Bijective g := by
    refine ⟨fun j₁ j₂ hij ↦ ?_, ?_⟩
    · have hsm : (finRotate l ^ (j₁ : ℕ)) • S = (finRotate l ^ (j₂ : ℕ)) • S :=
        congrArg Subtype.val hij
      have hmem : (⟨(finRotate l ^ (j₂ : ℕ))⁻¹ * finRotate l ^ (j₁ : ℕ),
          (Subgroup.zpowers (finRotate l)).mul_mem ((Subgroup.zpowers (finRotate l)).inv_mem
            ((Subgroup.zpowers (finRotate l)).pow_mem (Subgroup.mem_zpowers _) _))
            ((Subgroup.zpowers (finRotate l)).pow_mem (Subgroup.mem_zpowers _) _)⟩ :
          Subgroup.zpowers (finRotate l)) ∈
          MulAction.stabilizer (Subgroup.zpowers (finRotate l)) S := by
        rw [MulAction.mem_stabilizer_iff]
        -- Expose the `zpowers` subtype action on finsets as permutation powers.
        change ((finRotate l ^ (j₂ : ℕ))⁻¹ * finRotate l ^ (j₁ : ℕ)) • S = S
        rw [mul_smul, inv_smul_eq_iff, hsm]
      rw [hstab, Subgroup.mem_bot, Subtype.ext_iff, OneMemClass.coe_one] at hmem
      have hpow : finRotate l ^ (j₁ : ℕ) = finRotate l ^ (j₂ : ℕ) :=
        (eq_of_inv_mul_eq_one hmem).symm
      exact Fin.ext (pow_injOn_Iio_orderOf (hord.symm ▸ j₁.isLt) (hord.symm ▸ j₂.isLt) hpow)
    · rintro ⟨T, ⟨_, m, rfl⟩, rfl⟩
      let r : ℤ := m % (l : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg m (by exact_mod_cast hl.ne_zero)
      have hrl : r < l := Int.emod_lt_of_pos m (by exact_mod_cast hl.pos)
      refine ⟨⟨r.toNat, by omega⟩, Subtype.ext ?_⟩
      dsimp only [g]
      -- Unfold the `zpowers` subtype action to permutation integer powers.
      change (finRotate l ^ (r.toNat : ℕ)) • S = (finRotate l ^ m) • S
      have hpow : finRotate l ^ m = finRotate l ^ (r.toNat : ℕ) := by
        rw [← zpow_natCast, Int.ofNat_toNat, max_eq_left hr0, ← zpow_mod_orderOf, hord]
      rw [hpow]
  exact Fintype.sum_equiv (Equiv.ofBijective g hbij) _ _ fun _ ↦ rfl

private theorem orbitRel_finRotate_prop {l : ℕ} {S T : Finset (Fin l)}
    (h : MulAction.orbitRel (Subgroup.zpowers (finRotate l)) (Finset (Fin l)) S T) :
    S.card = T.card ∧ ((S.Nonempty ∧ S ≠ Finset.univ) ↔ (T.Nonempty ∧ T ≠ Finset.univ)) := by
  obtain ⟨⟨σ, _⟩, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  refine ⟨Finset.card_smul_finset σ T, ?_⟩
  constructor <;> rintro ⟨hne, hne_univ⟩
  · refine ⟨Finset.smul_finset_nonempty.mp hne, fun hT ↦ hne_univ ?_⟩
    rw [hT, Finset.smul_finset_univ]
  · refine ⟨Finset.smul_finset_nonempty.mpr hne, fun hsm ↦ hne_univ ?_⟩
    have := congrArg (σ⁻¹ • ·) hsm
    simpa [inv_smul_smul, Finset.smul_finset_univ] using this

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
      have hrel := orbitRel_finRotate_prop (MulAction.orbitRel_apply.mpr T.property)
      rw [hrel.1, ite_eq_left_of_eq_true _ _ (eq_true (hrel.2.mpr hO))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hO)]
      refine (Finset.sum_eq_zero fun T _ ↦ ?_).symm
      have hrel := orbitRel_finRotate_prop (MulAction.orbitRel_apply.mpr T.property)
      have hnt : ¬ (T.val.Nonempty ∧ T.val ≠ Finset.univ) := fun hT ↦ hO (hrel.2.mp hT)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnt)]
  rw [horb]
  dsimp only [φ]
  let := fun O : MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)) ↦
    Fintype.ofFinite (MulAction.orbit (Subgroup.zpowers (finRotate l)) O.out)
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv
    (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers (finRotate l)) (Finset (Fin l))).symm
    _ _ fun p ↦ by rw [selfEquivSigmaOrbits_symm_coe]

private theorem tensorIndClassFun_sub_of_index_prime_mem {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {x : G} (hx : x ∉ H) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u) (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)))]
    (h : H) :
    H.tensorIndClassFun (ψ₁ - ψ₂) h =
      H.tensorIndClassFun ψ₁ h +
        (-1 : k) ^ l * ((H.primeIndexSignChar (k := k) hl hH h : k) * H.tensorIndClassFun ψ₂ h) +
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
    primeIndexSignChar_apply_of_mem H hl hH h.property, Units.val_one, one_mul,
    sum_finRotate_orbit_indClassFun_eq H hl hH hx hψ₁ hψ₂ h]
  simp only [Pi.sub_apply]
  rw [prod_sub_eq_sum_finset_ite]
  have hsplit : ∀ S : Finset (Fin l),
      (-1 : k) ^ S.card * ∏ i : Fin l, (if i ∈ S then ψ₂ (MulAut.conjNormal (x ^ (i : ℕ)) h)
          else ψ₁ (MulAut.conjNormal (x ^ (i : ℕ)) h)) =
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
        simp only [h0, hu, hne, ne_eq, not_false_eq_true, and_self, ↓reduceIte, zero_add]
        congr 1; refine Finset.prod_congr rfl fun i _ ↦ ?_; split_ifs <;> rfl
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **Prime-index virtual-character decomposition (6.1 (b)).** For a normal subgroup `H ≤ G` of
prime index `l`, `x ∉ H`, and `H`-conjugation-invariant functions `ψ₁, ψ₂ : H → k` over a
commutative ring `k`, `H.tensorIndClassFun (ψ₁ - ψ₂)` decomposes as `H.tensorIndClassFun ψ₁`,
`(-1) ^ l • (primeIndexSignChar * H.tensorIndClassFun ψ₂)`, and the alternating sum over
cyclic-shift orbits on nonempty proper subsets of `Fin l` of `H.indClassFun` applied to the twisted
product along the subset. -/
theorem tensorIndClassFun_sub_of_index_prime {k G : Type*} [CommRing k] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] {l : ℕ} (hl : l.Prime) (hH : H.index = l)
    {x : G} (hx : x ∉ H) {ψ₁ ψ₂ : H → k}
    (hψ₁ : ∀ u v : H, ψ₁ (v * u * v⁻¹) = ψ₁ u) (hψ₂ : ∀ u v : H, ψ₂ (v * u * v⁻¹) = ψ₂ u)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers (finRotate l)) (Finset (Fin l)))] :
    H.tensorIndClassFun (ψ₁ - ψ₂) =
      H.tensorIndClassFun ψ₁ +
        (-1 : k) ^ l • ((fun g ↦ (H.primeIndexSignChar (k := k) hl hH g : k)) *
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
  · have hgl : g ^ l ∈ H := by
      have ho := Subgroup.orderOf_mk_eq_index_of_prime_of_notMem H hl hH hg
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← ho, pow_orderOf_eq_one]
    have hsub : ∀ u v : H, (ψ₁ - ψ₂) (v * u * v⁻¹) = (ψ₁ - ψ₂) u :=
      fun u v ↦ by simp [hψ₁, hψ₂]
    rw [tensorIndClassFun_apply_of_notMem_of_index_prime H hl hH hsub hg (h := ⟨g ^ l, hgl⟩) rfl,
      tensorIndClassFun_apply_of_notMem_of_index_prime H hl hH hψ₁ hg (h := ⟨g ^ l, hgl⟩) rfl,
      tensorIndClassFun_apply_of_notMem_of_index_prime H hl hH hψ₂ hg (h := ⟨g ^ l, hgl⟩) rfl,
      primeIndexSignChar_apply_of_notMem H hl hH hg]
    have hpow : (-1 : k) ^ l * ((((-1 : kˣ) ^ (l - 1)).val : k)) = -1 := by
      have hlpos : 1 ≤ l := hl.pos
      have hadd : l + (l - 1) = 1 + 2 * (l - 1) := by omega
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← pow_add, hadd, pow_add, pow_mul]
      simp
    have hind_zero : ∀ f : H → k, H.indClassFun f g = 0 := fun f ↦ by
      rw [Subgroup.indClassFun_apply]
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      split_ifs with ht
      · exact absurd (by simpa [mul_assoc] using ‹H.Normal›.conj_mem _ ht t.out) hg
      · rfl
    simp only [Pi.sub_apply, hind_zero, mul_zero, Finset.sum_const_zero, add_zero, ← mul_assoc,
      hpow, neg_one_mul, ← sub_eq_add_neg]

end Subgroup
