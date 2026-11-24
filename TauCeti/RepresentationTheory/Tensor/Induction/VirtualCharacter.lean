/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Tensor.Induction.Trace

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.RepresentationTheory.Induction.Character
import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# Tensor induction and virtual characters

Tensor induction `Subgroup.tensorIndClassFun` preserves `TauCeti.virtualCharacters` for every
finite-index subgroup `U ≤ G` and every coefficient field `k` (Evens' theorem on virtual
characters): if `ψ = χ_A - χ_B` is a virtual character of `U`, then `U.tensorIndClassFun ψ` is an
alternating sum of representations induced from the setwise stabilizers `MulAction.stabilizer G S`
of orbits of subsets `S ⊆ G ⧸ U`.

Explicitly, at each `g : G`, expanding
`∏ ω, (χ_A(m_ω) - χ_B(m_ω)) = ∑_T (-1)^{c(T)} (∏_{ω ∈ O(T)} χ_B(m_ω)) (∏_{ω ∉ O(T)} χ_A(m_ω))`
sums over all `g`-invariant subsets `T ⊆ G ⧸ U`, where `c(T)` is the number of `⟨g⟩`-orbits in `T`.
Since `(-1)^{c(T)} = (-1)^{|T|} · sgn(g|_T)` on `T`, grouping invariant subsets `T` by their
`G`-orbit decomposes the entire sum as
`∑_{O} (-1)^{|O.out|} • (MulAction.stabilizer G O.out).indClassFun W_{O.out}.character`, where
`W_S = ε_S ⊗ B_S ⊗ A_{Sᶜ}` is the tensor product of the sign character on `S` and the restricted
wreath tensor representations of `B` on `S` and `A` on `Sᶜ`.

## Main results

* `Subgroup.tensorIndClassFun_character_mem_virtualCharacters`: tensor induction of a genuine
  character of a finite-index subgroup is a virtual character of `G`.
* `Subgroup.tensorIndClassFun_mem_virtualCharacters`: tensor induction of any virtual character of
  a finite-index subgroup is a virtual character of `G`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3.
* L. Alpöge, *The Riemann Hypothesis for Dirichlet L-Functions* (2026).
-/

public section

open scoped Pointwise CategoryTheory.MonoidalCategory TensorProduct

namespace Subgroup

private theorem finiteDimensional_piTensorProduct {k ι : Type*} {M : ι → Type*}
    [Field k] [Finite ι] [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, FiniteDimensional k (M i)] :
    FiniteDimensional k (⨂[k] i, M i) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun i ↦ Module.Free.chooseBasis k (M i))

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
  have : FiniteDimensional k (⨂[k] _ : G ⧸ U, V) := finiteDimensional_piTensorProduct
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
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨⟨σ ^ (-i), -i, rfl⟩, ?_⟩
        rw [Subgroup.smul_def, Equiv.Perm.smul_def, ← Equiv.Perm.mul_apply, ← zpow_add,
          neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
      · rintro ⟨⟨_, i, rfl⟩, rfl⟩
        exact ⟨-i, by
          rw [Subgroup.smul_def, Equiv.Perm.smul_def, ← Equiv.Perm.mul_apply, ← zpow_add,
            neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]⟩
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

private theorem stabilizer_finset_finiteIndex {G : Type*} [Group G] (U : Subgroup G)
    [U.FiniteIndex] [DecidableEq (G ⧸ U)] (S : Finset (G ⧸ U)) :
    (MulAction.stabilizer G S).FiniteIndex := by
  let := U.fintypeQuotientOfFiniteIndex
  have : Finite (MulAction.orbit G S) := Subtype.finite
  exact @Subgroup.finiteIndex_of_finite_quotient _ _ _
    (Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G S))

private theorem zpow_smul_finset_eq {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    {g : G} {T : Finset α} (hT : g • T = T) (k : ℤ) : (g ^ k) • T = T := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, hT, ih]
  | pred n ih =>
    have hinv : g⁻¹ • T = T := inv_smul_eq_iff.mpr hT.symm
    rw [zpow_sub_one, mul_smul, hinv, ih]

private theorem zpow_smul_mem_of_smul_eq {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    {g : G} {T : Finset α} (hT : g • T = T) {x y : α}
    (horb : MulAction.orbitRel (Subgroup.zpowers g) α x y) : x ∈ T ↔ y ∈ T := by
  obtain ⟨⟨_, k, rfl⟩, rfl⟩ := MulAction.mem_orbit_iff.mp horb
  have hk : (g ^ k) • T = T := zpow_smul_finset_eq hT k
  constructor <;> intro hm
  · have hmem : (g ^ (-k)) • ((g ^ k) • y) ∈ (g ^ (-k)) • T :=
      Finset.smul_mem_smul_finset hm
    rwa [← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul,
      zpow_smul_finset_eq hT (-k)] at hmem
  · exact hk ▸ Finset.smul_mem_smul_finset hm

private theorem smul_compl_eq_of_smul_eq {G α : Type*} [Group G] [MulAction G α]
    [Fintype α] [DecidableEq α] {g : G} {S : Finset α} (hS : g • S = S) : g • Sᶜ = Sᶜ := by
  ext x
  have hinv : g⁻¹ • S = S := inv_smul_eq_iff.mpr hS.symm
  constructor <;> intro hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hx
    rw [Finset.mem_compl] at hy ⊢
    intro hm
    apply hy
    have hy' : g⁻¹ • (g • y) ∈ g⁻¹ • S := Finset.smul_mem_smul_finset hm
    rwa [inv_smul_smul, hinv] at hy'
  · refine Finset.mem_smul_finset.mpr ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    rw [Finset.mem_compl] at hx ⊢
    intro hm
    apply hx
    have hmem : g • (g⁻¹ • x) ∈ g • S := Finset.smul_mem_smul_finset hm
    rwa [smul_inv_smul, hS] at hmem

private def subsetPermOn {G : Type*} [Group G] {U : Subgroup G} [DecidableEq (G ⧸ U)]
    (H : Subgroup G) (T : Finset (G ⧸ U)) (hT : ∀ x : H, (x : G) • T = T) :
    H →* Equiv.Perm ↥T where
  toFun x :=
    { toFun := fun y ↦ ⟨(x : G) • y.val, by
        have hm := Finset.smul_mem_smul_finset (a := (x : G)) y.property
        rwa [hT x] at hm⟩
      invFun := fun y ↦ ⟨(x⁻¹ : H).val • y.val, by
        have hm := Finset.smul_mem_smul_finset (a := (x⁻¹ : H).val) y.property
        rwa [hT x⁻¹] at hm⟩
      left_inv := fun y ↦ Subtype.ext (by simp [inv_smul_smul])
      right_inv := fun y ↦ Subtype.ext (by simp [smul_inv_smul]) }
  map_one' := by ext y; simp
  map_mul' x z := by ext y; simp [mul_smul]

private theorem subsetPermOn_zpow_val {G : Type*} [Group G] {U : Subgroup G} [DecidableEq (G ⧸ U)]
    {H : Subgroup G} {T : Finset (G ⧸ U)} (hT : ∀ x : H, (x : G) • T = T)
    (x : H) (k : ℤ) (y : ↥T) :
    ((subsetPermOn H T hT x ^ k) y).val = ((x : G) ^ k) • y.val := by
  induction k using Int.induction_on generalizing y with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, zpow_add_one, mul_smul]
    rfl
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, zpow_sub_one, mul_smul]
    rfl

private theorem subsetPermOn_minimalPeriod {G : Type*} [Group G] {U : Subgroup G}
    [DecidableEq (G ⧸ U)] {H : Subgroup G} {T : Finset (G ⧸ U)}
    (hT : ∀ x : H, (x : G) • T = T) (x : H) (y : ↥T) :
    Function.minimalPeriod ((subsetPermOn H T hT x) • ·) y =
      Function.minimalPeriod ((x : G) • ·) y.val := by
  have h1 : ∀ m : ℕ, ((subsetPermOn H T hT x) • ·)^[m] y = (subsetPermOn H T hT x ^ m) y :=
    fun m ↦ by
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply]; rfl
  have h2 : ∀ m : ℕ, ((x : G) • ·)^[m] y.val = ((x : G) ^ m) • y.val := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  refine Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ ?_
  rw [Function.IsPeriodicPt, Function.IsFixedPt, h1 n, Function.IsPeriodicPt, Function.IsFixedPt,
    h2 n, Subtype.ext_iff, ← zpow_natCast (subsetPermOn H T hT x) n, subsetPermOn_zpow_val,
    zpow_natCast]

private noncomputable def subsetMonomialHom {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] (H : Subgroup G) (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) : H →* TauCeti.WreathProduct U ↥T where
  toFun x := ⟨fun y ↦ (U.monomialHom s x.val).left y.val, subsetPermOn H T hT x⟩
  map_one' := SemidirectProduct.ext (funext fun y ↦ by simp) (by simp)
  map_mul' x z := by
    refine SemidirectProduct.ext (funext fun y ↦ ?_) (by simp)
    rw [Subgroup.coe_mul, map_mul, TauCeti.PermutationWreathProduct.mul_left,
      TauCeti.PermutationWreathProduct.mul_left]
    congr 1
    rw [Equiv.Perm.smul_def, Subgroup.monomialHom_right_inv]
    rfl

private noncomputable def subsetOrbitEquiv {G : Type*} [Group G] {U : Subgroup G}
    [DecidableEq (G ⧸ U)] {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H) :
    MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T ≃
      {ω : MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) // ω.out ∈ T} where
  toFun q :=
    ⟨Quotient.mk'' q.out.val,
      (zpow_smul_mem_of_smul_eq (hT x)
        (Quotient.exact' (Quotient.out_eq (Quotient.mk'' q.out.val)))).mpr q.out.property⟩
  invFun ω := Quotient.mk'' ⟨ω.val.out, ω.property⟩
  left_inv q := by
    induction q using Quotient.inductionOn' with | h y =>
    let q₀ : MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T :=
      Quotient.mk'' y
    have hy : MulAction.orbitRel (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T q₀.out y :=
      Quotient.exact' (Quotient.out_eq q₀)
    let q₁ : MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) :=
      Quotient.mk'' q₀.out.val
    have h1 : MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U) q₁.out q₀.out.val :=
      Quotient.exact' (Quotient.out_eq q₁)
    have h2 : MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U) q₀.out.val y.val := by
      obtain ⟨⟨_, k, rfl⟩, hk⟩ := MulAction.mem_orbit_iff.mp hy
      exact ⟨⟨x.val ^ k, k, rfl⟩, by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, subsetPermOn_zpow_val] using
          congrArg Subtype.val hk⟩
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := MulAction.mem_orbit_iff.mp
      ((MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U)).trans h1 h2)
    refine Quotient.sound' ⟨⟨(subsetPermOn H T hT x) ^ k, k, rfl⟩, Subtype.ext ?_⟩
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, subsetPermOn_zpow_val] using hk
  right_inv ω := by
    rcases ω with ⟨ω, hω⟩
    apply Subtype.ext
    dsimp only
    let q : MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T :=
      Quotient.mk'' ⟨ω.out, hω⟩
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact' (Quotient.out_eq q))
    have horb : MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U) q.out.val ω.out :=
      ⟨⟨x.val ^ k, k, rfl⟩, by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, subsetPermOn_zpow_val] using
          congrArg Subtype.val hk⟩
    exact (Quotient.sound' horb).trans (Quotient.out_eq ω)

private theorem subsetOrbitEquiv_out_rel {G : Type*} [Group G] {U : Subgroup G}
    [DecidableEq (G ⧸ U)] {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H)
    (q : MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T) :
    MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U)
      q.out.val (subsetOrbitEquiv T hT x q).val.out :=
  Quotient.exact' (Quotient.out_eq (subsetOrbitEquiv T hT x q).val).symm

private noncomputable def subsetWreathRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] (H : Subgroup G)
    (T : Finset (G ⧸ U)) (hT : ∀ x : H, (x : G) • T = T) (V : FDRep k U) : FDRep k H :=
  have : FiniteDimensional k (⨂[k] _ : ↥T, V) := finiteDimensional_piTensorProduct
  FDRep.ofShrink ((Representation.wreathTensor V.ρ ↥T).comp (subsetMonomialHom U s H T hT))

private theorem subsetMonomialHom_left {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H) (y : ↥T) :
    (subsetMonomialHom U s H T hT x).left y = (U.monomialHom s x.val).left y.val :=
  rfl

private theorem subsetMonomialHom_orbit_prod {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H) (q₀ : ↥T) :
    (List.ofFn fun t : Fin (Function.minimalPeriod ((subsetPermOn H T hT x) • ·) q₀) ↦
        (subsetMonomialHom U s H T hT x).left
          (((subsetPermOn H T hT x)⁻¹ ^ (t : ℕ)) q₀)).prod =
      ⟨(U.leftTransversalRep s q₀.val)⁻¹ *
          x.val ^ Function.minimalPeriod (x.val • ·) q₀.val * U.leftTransversalRep s q₀.val,
        conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s q₀.val)⟩ := by
  have hper : Function.minimalPeriod ((subsetPermOn H T hT x) • ·) q₀ =
      Function.minimalPeriod ((U.monomialHom s x.val).right • ·) q₀.val := by
    rw [subsetPermOn_minimalPeriod]
    congr 1
    ext z
    rw [Equiv.Perm.smul_def, Subgroup.monomialHom_right]
  have ha : ∀ t : ℕ, (((subsetPermOn H T hT x)⁻¹ ^ t) q₀).val = ((x.val)⁻¹ ^ t) • q₀.val :=
    fun t ↦ by
      rw [← map_inv, ← zpow_natCast (subsetPermOn H T hT x⁻¹) t, subsetPermOn_zpow_val,
        Subgroup.coe_inv, zpow_natCast]
  have hb : ∀ t : ℕ, ((U.monomialHom s x.val).right⁻¹ ^ t) q₀.val = ((x.val)⁻¹ ^ t) • q₀.val :=
    fun t ↦ by
      induction t with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, Subgroup.monomialHom_right_inv, ih, ← mul_smul,
          ← pow_succ']
  have hlist :
      (List.ofFn fun t : Fin (Function.minimalPeriod ((subsetPermOn H T hT x) • ·) q₀) ↦
          (subsetMonomialHom U s H T hT x).left
            (((subsetPermOn H T hT x)⁻¹ ^ (t : ℕ)) q₀)) =
        List.ofFn fun t :
            Fin (Function.minimalPeriod ((U.monomialHom s x.val).right • ·) q₀.val) ↦
          (U.monomialHom s x.val).left
            (((U.monomialHom s x.val).right⁻¹ ^ (t : ℕ)) q₀.val) := by
    refine List.ext_get (by simpa only [List.length_ofFn] using hper) fun i _ _ ↦ ?_
    simp only [List.getElem_ofFn, List.get_eq_getElem, subsetMonomialHom_left]
    exact congrArg (U.monomialHom s x.val).left ((ha i).trans (hb i).symm)
  rw [hlist, Subgroup.monomialHom_orbit_prod]

private theorem subsetMonomialHom_orbit_out_rel {G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) [DecidableEq (G ⧸ U)] {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (x : H)
    (q : MulAction.orbitRel.Quotient
      (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T) :
    let qRight : MulAction.orbitRel.Quotient
        (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T ≃
        MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T :=
      Quotient.congrRight fun _ _ ↦ Iff.rfl
    MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U) q.out.val
      ((qRight.trans (subsetOrbitEquiv T hT x)) q).val.out := by
  intro qRight
  have hq0 : qRight q = Quotient.mk'' q.out := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hq1 : MulAction.orbitRel (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T
      q.out (qRight q).out :=
    Quotient.exact' (hq0.symm.trans (Quotient.out_eq (qRight q)).symm)
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := MulAction.mem_orbit_iff.mp hq1
  have hqx : MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U) q.out.val (qRight q).out.val :=
    ⟨⟨x.val ^ k, k, rfl⟩, by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, subsetPermOn_zpow_val] using
        congrArg Subtype.val hk⟩
  exact (MulAction.orbitRel (Subgroup.zpowers x.val) (G ⧸ U)).trans hqx
    (subsetOrbitEquiv_out_rel T hT x (qRight q))

private theorem character_subsetWreathRep_factor {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [DecidableEq (G ⧸ U)] (s : U.LeftTransversal) {H : Subgroup G} (T : Finset (G ⧸ U))
    (hT : ∀ x : H, (x : G) • T = T) (V : FDRep k U) (x : H)
    (q : MulAction.orbitRel.Quotient
      (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T) :
    let qRight : MulAction.orbitRel.Quotient
        (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T ≃
        MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T :=
      Quotient.congrRight fun _ _ ↦ Iff.rfl
    let e := qRight.trans (subsetOrbitEquiv T hT x)
    LinearMap.trace k V (V.ρ (List.ofFn fun t :
        Fin (Function.minimalPeriod ((subsetMonomialHom U s H T hT x).right • ·) q.out) ↦
      (subsetMonomialHom U s H T hT x).left
        (((subsetMonomialHom U s H T hT x).right⁻¹ ^ (t : ℕ)) q.out)).prod) =
      V.character
        ⟨(U.leftTransversalRep s (e q).val.out)⁻¹ *
            x.val ^ Function.minimalPeriod (x.val • ·) (e q).val.out *
            U.leftTransversalRep s (e q).val.out,
          conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s (e q).val.out)⟩ := by
  intro qRight e
  -- Expose `(subsetMonomialHom ... x).right` as `subsetPermOn` to rewrite the orbit product.
  change LinearMap.trace k V (V.ρ (List.ofFn fun t :
      Fin (Function.minimalPeriod ((subsetPermOn H T hT x) • ·) q.out) ↦
    (subsetMonomialHom U s H T hT x).left
      (((subsetPermOn H T hT x)⁻¹ ^ (t : ℕ)) q.out)).prod) = _
  rw [subsetMonomialHom_orbit_prod]
  exact (apply_conj_pow_minimalPeriod_eq_of_orbitRel (fun u v ↦ V.char_conj u v) x.val
    (subsetMonomialHom_orbit_out_rel U s T hT x q) (U.leftTransversalRep_mk s q.out.val)
    (U.leftTransversalRep_mk s (e q).val.out)).symm

private theorem character_subsetWreathRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [DecidableEq (G ⧸ U)] (s : U.LeftTransversal) (H : Subgroup G)
    (T : Finset (G ⧸ U)) (hT : ∀ x : H, (x : G) • T = T) (V : FDRep k U) (x : H)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U))] :
    (subsetWreathRep U s H T hT V).character x =
      ∏ ω ∈ Finset.univ.filter (fun ω :
          MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) ↦ ω.out ∈ T),
        V.character
          ⟨(U.leftTransversalRep s ω.out)⁻¹ * x.val ^ Function.minimalPeriod (x.val • ·) ω.out *
              U.leftTransversalRep s ω.out,
            conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s ω.out)⟩ := by
  let qRight :
      MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T ≃
        MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetPermOn H T hT x)) ↥T :=
    Quotient.congrRight fun _ _ ↦ Iff.rfl
  let := Fintype.ofFinite
    (MulAction.orbitRel.Quotient (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T)
  have : FiniteDimensional k (⨂[k] _ : ↥T, V) := finiteDimensional_piTensorProduct
  dsimp only [subsetWreathRep]
  rw [FDRep.character_ofShrink, Representation.character]
  dsimp only [MonoidHom.comp_apply]
  rw [Representation.trace_wreathTensor]
  let e := qRight.trans (subsetOrbitEquiv T hT x)
  have hprod :
      (∏ q : MulAction.orbitRel.Quotient
            (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T,
          LinearMap.trace k V (V.ρ (List.ofFn fun t :
              Fin (Function.minimalPeriod
                ((subsetMonomialHom U s H T hT x).right • ·) q.out) ↦
            (subsetMonomialHom U s H T hT x).left
              (((subsetMonomialHom U s H T hT x).right⁻¹ ^ (t : ℕ)) q.out)).prod)) =
        ∏ q : MulAction.orbitRel.Quotient
            (Subgroup.zpowers (subsetMonomialHom U s H T hT x).right) ↥T,
          V.character
            ⟨(U.leftTransversalRep s (e q).val.out)⁻¹ *
                x.val ^ Function.minimalPeriod (x.val • ·) (e q).val.out *
                U.leftTransversalRep s (e q).val.out,
              conj_pow_minimalPeriod_mem U x.val
                (U.leftTransversalRep_mk s (e q).val.out)⟩ :=
    Finset.prod_congr rfl fun q _ ↦ character_subsetWreathRep_factor U s T hT V x q
  rw [hprod]
  refine (Fintype.prod_equiv e _ (fun ω ↦ V.character
    ⟨(U.leftTransversalRep s ω.val.out)⁻¹ * x.val ^ Function.minimalPeriod (x.val • ·) ω.val.out *
        U.leftTransversalRep s ω.val.out,
      conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s ω.val.out)⟩)
    fun _ ↦ rfl).trans ?_
  exact (Finset.prod_subtype
    (Finset.univ.filter fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) ↦
      ω.out ∈ T)
    (p := fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers x.val) (G ⧸ U) ↦ ω.out ∈ T)
    (fun _ ↦ by simp)
    fun ω ↦ V.character
      ⟨(U.leftTransversalRep s ω.out)⁻¹ * x.val ^ Function.minimalPeriod (x.val • ·) ω.out *
          U.leftTransversalRep s ω.out,
        conj_pow_minimalPeriod_mem U x.val (U.leftTransversalRep_mk s ω.out)⟩).symm

private theorem mem_stabilizer_finset {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    (S : Finset α) (x : MulAction.stabilizer G S) : (x : G) • S = S :=
  x.property

private theorem mem_stabilizer_compl {G α : Type*} [Group G] [MulAction G α] [Fintype α]
    [DecidableEq α] (S : Finset α) (x : MulAction.stabilizer G S) : (x : G) • Sᶜ = Sᶜ :=
  smul_compl_eq_of_smul_eq x.property

private noncomputable def stabilizerRep {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (S : Finset (G ⧸ U)) (A B : FDRep k U) : FDRep k (MulAction.stabilizer G S) :=
  let ε : MulAction.stabilizer G S →* kˣ :=
    (Units.map (Int.castRingHom k).toMonoidHom).comp
      (Equiv.Perm.sign.comp (subsetPermOn _ S (mem_stabilizer_finset S)))
  FDRep.ofLinearCharacter ε ⊗
    subsetWreathRep U s _ S (mem_stabilizer_finset S) B ⊗
    subsetWreathRep U s _ Sᶜ (mem_stabilizer_compl S) A

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
      (Subgroup.zpowers (subsetPermOn _ S (mem_stabilizer_finset S) y)) ↥S)
  dsimp only [stabilizerRep]
  have hε : ∀ n : ℤ, (Int.castRingHom k).toMonoidHom n = (n : k) := fun _ ↦ rfl
  simp only [FDRep.char_tensor, Pi.mul_apply, FDRep.char_ofLinearCharacter, MonoidHom.comp_apply,
    Units.coe_map, hε, ← mul_assoc]
  have hsign : (-1 : k) ^ S.card *
      ((Equiv.Perm.sign (subsetPermOn _ S (mem_stabilizer_finset S) y) : ℤ) : k) =
      (-1 : k) ^ (Finset.univ.filter (fun ω : MulAction.orbitRel.Quotient
          (Subgroup.zpowers y.val) (G ⧸ U) ↦ ω.out ∈ S)).card := by
    rw [← Fintype.card_coe S,
      neg_one_pow_card_mul_sign (subsetPermOn _ S (mem_stabilizer_finset S) y),
      Fintype.card_congr (subsetOrbitEquiv S (mem_stabilizer_finset S) y), Fintype.card_subtype]
  rw [hsign, character_subsetWreathRep, character_subsetWreathRep]
  congr 1
  rw [Finset.prod_neg]

private theorem inv_conj_pow {G : Type*} [Group G] (r g : G) (n : ℕ) :
    (r⁻¹ * g * r) ^ n = r⁻¹ * g ^ n * r := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih]; group

private theorem inv_conj_zpow {G : Type*} [Group G] (r g : G) (n : ℤ) :
    (r⁻¹ * g * r) ^ n = r⁻¹ * g ^ n * r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, ih]; group
  | pred n ih => rw [zpow_sub_one, ih]; group

private theorem conj_smul_zpow {G : Type*} [Group G] (U : Subgroup G) (g r : G) (n : ℤ)
    (q : G ⧸ U) : r • ((r⁻¹ * g * r) ^ n • q) = g ^ n • (r • q) := by
  calc
    r • ((r⁻¹ * g * r) ^ n • q) = (r * (r⁻¹ * g ^ n * r)) • q := by
      rw [inv_conj_zpow, ← mul_smul]
    _ = (g ^ n * r) • q := by rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = g ^ n • (r • q) := mul_smul _ _ _

private noncomputable def conjOrbitEquiv {G : Type*} [Group G] (U : Subgroup G) (g r : G) :
    MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U) ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) :=
  Quotient.congr (MulAction.toPerm r) fun x y ↦ by
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
    constructor
    · rintro ⟨⟨_, k, rfl⟩, rfl⟩
      exact ⟨⟨g ^ k, k, rfl⟩, (conj_smul_zpow U g r k y).symm⟩
    · rintro ⟨⟨_, k, rfl⟩, h⟩
      refine ⟨⟨(r⁻¹ * g * r) ^ k, k, rfl⟩, (MulAction.toPerm r).injective ?_⟩
      exact (conj_smul_zpow U g r k y).trans h

private theorem conjOrbitEquiv_mem_iff {G : Type*} [Group G] (U : Subgroup G)
    [DecidableEq (G ⧸ U)] (S : Finset (G ⧸ U)) (g r : G)
    (hr : r⁻¹ * g * r ∈ MulAction.stabilizer G S)
    (ω : MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U)) :
    ω.out ∈ S ↔ (conjOrbitEquiv U g r ω).out ∈ r • S := by
  have hgT : g • (r • S) = r • S := by
    have hs : (r⁻¹ * g * r) • S = S := hr
    simpa [mul_smul, smul_inv_smul] using congrArg (r • ·) hs
  have hq : conjOrbitEquiv U g r ω = Quotient.mk'' (r • ω.out) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  have horb : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U)
      (r • ω.out) (conjOrbitEquiv U g r ω).out :=
    Quotient.exact' (hq.symm.trans (Quotient.out_eq (conjOrbitEquiv U g r ω)).symm)
  rw [← zpow_smul_mem_of_smul_eq hgT horb, Finset.smul_mem_smul_finset_iff]

private theorem conj_minimalPeriod_eq {G : Type*} [Group G] (U : Subgroup G) (g r : G)
    (q : G ⧸ U) :
    Function.minimalPeriod ((r⁻¹ * g * r) • ·) q = Function.minimalPeriod (g • ·) (r • q) := by
  have hi1 : ∀ m : ℕ, ((r⁻¹ * g * r) • ·)^[m] q = ((r⁻¹ * g * r) ^ m) • q := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']
  have hi2 : ∀ m : ℕ, (g • ·)^[m] (r • q) = g ^ m • (r • q) := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']
  refine Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ ?_
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, hi1 n, hi2 n]
  constructor <;> intro h
  · simpa [← zpow_natCast, conj_smul_zpow] using congrArg (r • ·) h
  · exact (MulAction.toPerm r).injective (by
      simpa [MulAction.toPerm_apply, ← zpow_natCast, conj_smul_zpow] using h)

private theorem conjOrbitEquiv_monodromy_eq {R G : Type*} [Group G] (U : Subgroup G)
    (s : U.LeftTransversal) {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u)
    (g r : G) (ω : MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U)) :
    f ⟨(U.leftTransversalRep s ω.out)⁻¹ * (r⁻¹ * g * r) ^ Function.minimalPeriod
          ((r⁻¹ * g * r) • ·) ω.out * U.leftTransversalRep s ω.out,
        conj_pow_minimalPeriod_mem U (r⁻¹ * g * r) (U.leftTransversalRep_mk s ω.out)⟩ =
      f ⟨(U.leftTransversalRep s (conjOrbitEquiv U g r ω).out)⁻¹ * g ^ Function.minimalPeriod
          (g • ·) (conjOrbitEquiv U g r ω).out *
          U.leftTransversalRep s (conjOrbitEquiv U g r ω).out,
        conj_pow_minimalPeriod_mem U g
          (U.leftTransversalRep_mk s (conjOrbitEquiv U g r ω).out)⟩ := by
  have hq : conjOrbitEquiv U g r ω = Quotient.mk'' (r • ω.out) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  have horb : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U)
      (r • ω.out) (conjOrbitEquiv U g r ω).out :=
    Quotient.exact' (hq.symm.trans (Quotient.out_eq (conjOrbitEquiv U g r ω)).symm)
  have hrep : (QuotientGroup.mk (r * U.leftTransversalRep s ω.out) : G ⧸ U) = r • ω.out := by
    -- Rewrite left multiplication on cosets as the left action of `G` on `G ⧸ U`.
    change r • (QuotientGroup.mk (U.leftTransversalRep s ω.out) : G ⧸ U) = r • ω.out
    rw [U.leftTransversalRep_mk s ω.out]
  refine Eq.trans ?_ (apply_conj_pow_minimalPeriod_eq_of_orbitRel hf g horb hrep
    (U.leftTransversalRep_mk s (conjOrbitEquiv U g r ω).out)).symm
  congr 1
  apply Subtype.ext
  dsimp only
  rw [conj_minimalPeriod_eq, inv_conj_pow]
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
  · refine Fintype.prod_equiv (conjOrbitEquiv U g r) _ _ fun ω ↦ ?_
    have hm := conjOrbitEquiv_mem_iff U S g r hr ω
    by_cases hω : ω.out ∈ S
    · simp only [hω, hm.mp hω, ↓reduceIte,
        conjOrbitEquiv_monodromy_eq U s (fun u v ↦ B.char_conj u v) g r ω]
    · have hmr : (conjOrbitEquiv U g r ω).out ∉ r • S := fun h ↦ hω (hm.mpr h)
      simp only [hω, hmr, ↓reduceIte]
  · refine Fintype.prod_equiv (conjOrbitEquiv U g r) _ _ fun ω ↦ ?_
    have hm := conjOrbitEquiv_mem_iff U S g r hr ω
    by_cases hω : ω.out ∈ S
    · have hmr : (conjOrbitEquiv U g r ω).out ∈ r • S := hm.mp hω
      simp only [Finset.mem_compl, hω, hmr, not_true_eq_false, ↓reduceIte]
    · have hmr : (conjOrbitEquiv U g r ω).out ∉ r • S := fun h ↦ hω (hm.mpr h)
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

private noncomputable def orbitSigmaFinsetEquiv {G : Type*} [Group G] (U : Subgroup G)
    [DecidableEq (G ⧸ U)] :
    (Σ O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U)), MulAction.orbit G O.out) ≃
      Finset (G ⧸ U) where
  toFun p := p.snd.val
  invFun T := ⟨Quotient.mk'' T,
    ⟨T, MulAction.orbitRel_apply.mp (Quotient.exact' (Quotient.out_eq (Quotient.mk'' T)).symm)⟩⟩
  left_inv p := by
    rcases p with ⟨O, ⟨T, hT⟩⟩
    have hO : Quotient.mk'' T = O :=
      (Quotient.sound hT).trans (Quotient.out_eq O)
    subst hO
    rfl
  right_inv _ := rfl

private noncomputable def fixedFinsetEquivOrbitFinset {G : Type*} [Group G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    {T : Finset (G ⧸ U) // g • T = T} ≃
      Finset (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U)) where
  toFun T := Finset.univ.filter fun ω ↦ ω.out ∈ T.val
  invFun s :=
    let := Classical.decEq (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
    ⟨Finset.univ.filter fun q ↦ Quotient.mk'' q ∈ s, by
      ext q
      simp only [Finset.mem_smul_finset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨q', hq', hqq'⟩
        have hrel : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U) q q' :=
          ⟨⟨g, 1, zpow_one g⟩, by simpa [Subgroup.smul_def] using hqq'⟩
        rwa [Quotient.sound' hrel]
      · intro hq
        refine ⟨g⁻¹ • q, ?_, smul_inv_smul g q⟩
        have hrel : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U) (g⁻¹ • q) q :=
          ⟨⟨g⁻¹, -1, zpow_neg_one g⟩, rfl⟩
        rwa [Quotient.sound' hrel]⟩
  left_inv T := Subtype.ext <| by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact zpow_smul_mem_of_smul_eq T.property (Quotient.exact' (Quotient.out_eq (Quotient.mk'' q)))
  right_inv s := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.out_eq]

private noncomputable def orbitStabTerm {k G : Type*} [Field k] [Group G] (U : Subgroup G)
    [U.FiniteIndex] [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (A B : FDRep k U) (O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U))) : G → k :=
  let := stabilizer_finset_finiteIndex U O.out
  (-1 : k) ^ O.out.card • (MulAction.stabilizer G O.out).indClassFun
    (stabilizerRep U s O.out A B).character

private theorem orbitStabTerm_mem_virtualCharacters {k G : Type*} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)]
    (s : U.LeftTransversal) (A B : FDRep k U)
    (O : MulAction.orbitRel.Quotient G (Finset (G ⧸ U))) :
    orbitStabTerm U s A B O ∈ TauCeti.virtualCharacters k G := by
  let := stabilizer_finset_finiteIndex U O.out
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
    let := stabilizer_finset_finiteIndex U O.out
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
    exact Fintype.sum_equiv (orbitSigmaFinsetEquiv U) _ _ fun _ ↦ rfl
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
    refine Fintype.sum_equiv (fixedFinsetEquivOrbitFinset U g) _ _ fun T ↦ ?_
    dsimp only [evalOrbitFactor]
    congr 2
    ext ω
    have hto : fixedFinsetEquivOrbitFinset U g T =
        Finset.univ.filter fun ω : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) ↦
          ω.out ∈ T.val := rfl
    rw [hto]
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilt, ← Fintype.prod_add]
  refine Finset.prod_congr rfl fun ω _ ↦ ?_
  simp [sub_eq_neg_add]

end Subgroup
