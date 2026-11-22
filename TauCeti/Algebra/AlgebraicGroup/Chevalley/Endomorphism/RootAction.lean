/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
import TauCeti.Algebra.Group.Pow
import TauCeti.Algebra.Ring.Hom

/-!
# Root permutations and field automorphisms of standard endomorphisms

Over an infinite field with divisible units (in particular an algebraically closed field), a
standard endomorphism `F` of a Chevalley datum `D` with an injective character map `φ` acts on
each root subgroup by `F (x_α(u)) = x_{π α}(c_α · g_α(u))` for a permutation `π` of the roots,
units `c_α`, and field automorphisms `g_α : K ≃+* K` satisfying `g_α(α(s)) = (φ (π α))(s)` and
rational proportionality between `φ (π α)` and `α`.

Both the target root `π α` and the field endomorphism `g_α` are uniquely determined by `(α, φ)`
alone over any infinite field, even without divisible units
(`ChevalleyDatum.eq_of_ringHom_torusCharacter_eq`); in particular `π` commutes with root negation
and `g_{-α} = g_α`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.eq_of_ringHom_torusCharacter_eq`: an injective character
  map uniquely determines both the target root (including sign) and the field endomorphism.
* `TauCeti.DynkinType.ChevalleyDatum.exists_root_and_ringEquiv_of_isStandardEndomorphism`: root
  action `F (x_α(u)) = x_β(c · g(u))` on a single root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.exists_rootPerm_of_isStandardEndomorphism`: every standard
  endomorphism with an injective character map induces a negation-preserving permutation of the
  roots and compatible field automorphisms on every root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.mem_posRoots_iff_of_isBasedEndomorphism`: for a based
  endomorphism over a nontrivial commutative ring, the induced root permutation preserves positive
  roots.

## References

* R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  §§1.15–1.17.
-/

public section

open Multiplicative

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Root parameters and field automorphisms from a character map -/

private theorem coordinateRoot_eq_or_eq_neg_of_smul_eq
    {γ₁ γ₂ : Fin t.numRoots} {a b : ℤ} (ha : a ≠ 0)
    (h : a • D.coordinateRoot γ₂ = b • D.coordinateRoot γ₁) :
    γ₁ = γ₂ ∨ D.coordinateRoot γ₂ = -D.coordinateRoot γ₁ := by
  rcases D.eq_or_eq_neg_of_smul_coordinateRoot_eq ha h with heq | hneg
  · exact Or.inl ((t.simplyConnectedRootDatum ht).root.injective heq)
  · refine Or.inr (D.weightLatticeEmbedding_injective ?_)
    rw [map_neg]
    simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using
      neg_eq_iff_eq_neg.mp hneg.symm

private theorem false_of_ringHom_torusCharacter_mul_eq_one {K : Type*} [Field K] [Infinite K]
    {δ : Fin t.numRoots} {g₁ g₂ : K →+* K}
    (h : ∀ s : Fin t.rank → Kˣ,
      (g₁ (torusCharacter s (D.coordinateRoot δ)) : K) *
        g₂ (torusCharacter s (D.coordinateRoot δ)) = 1) :
    False := by
  obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot δ i ≠ 0 := Function.ne_iff.mp (D.coordinateRoot_ne_zero δ)
  refine RingHom.false_of_pow_mul_eq_one g₁ g₂ (Int.natAbs_ne_zero.mpr hi) fun x hx => ?_
  have h1 : (g₁ x * g₂ x) ^ D.coordinateRoot δ i = (1 : K) ^ D.coordinateRoot δ i := by
    rw [one_zpow, mul_zpow, ← map_zpow₀ g₁, ← map_zpow₀ g₂]
    have hs := h (Pi.mulSingle i (Units.mk0 x hx))
    simpa only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0] using hs
  exact (TauCeti.pow_natAbs_eq_of_zpow_eq h1).trans (one_pow _)

/-- **Uniqueness of the target root and field endomorphism from the character map.** Over any
infinite field, an injective character map `φ` and source root `α` uniquely determine both the
target root `β` (including its sign) and the field endomorphism `g : K →+* K` satisfying
`g (α(s)) = (φ β)(s)` for all torus parameters `s`. Divisibility of `Kˣ` is not required. -/
theorem eq_of_ringHom_torusCharacter_eq {K : Type*} [Field K] [Infinite K]
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hinj : Function.Injective φ)
    {α β₁ β₂ : Fin t.numRoots} {g₁ g₂ : K →+* K}
    (h₁ : ∀ s : Fin t.rank → Kˣ,
      g₁ (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β₁)))
    (h₂ : ∀ s : Fin t.rank → Kˣ,
      g₂ (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β₂))) :
    β₁ = β₂ ∧ g₁ = g₂ := by
  obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α i ≠ 0 := Function.ne_iff.mp (D.coordinateRoot_ne_zero α)
  have hker {β : Fin t.numRoots} {g : K →+* K}
      (hg : ∀ s : Fin t.rank → Kˣ,
        g (torusCharacter s (D.coordinateRoot α)) = torusCharacter s (φ (D.coordinateRoot β))) :
      D.coordinateRoot α i • φ (D.coordinateRoot β) =
        φ (D.coordinateRoot β) i • D.coordinateRoot α ∧ φ (D.coordinateRoot β) i ≠ 0 := by
    have hk : ∀ s : Fin t.rank → Kˣ,
        torusCharacter s (D.coordinateRoot α) = 1 → torusCharacter s (φ (D.coordinateRoot β)) = 1 :=
      fun s hs => Units.ext <| by simpa only [hs, Units.val_one, map_one] using (hg s).symm
    have hp := smul_eq_smul_of_torusCharacter_eq_one hk i
    refine ⟨hp, fun h0 => ?_⟩
    rw [h0, zero_smul] at hp
    exact D.coordinateRoot_ne_zero β
      (hinj (((smul_eq_zero.mp hp).resolve_left hi).trans (map_zero φ).symm))
  obtain ⟨hp₁, hm₁⟩ := hker h₁
  obtain ⟨hp₂, _⟩ := hker h₂
  have hpropβ :
      φ (D.coordinateRoot β₁) i • D.coordinateRoot β₂ =
        φ (D.coordinateRoot β₂) i • D.coordinateRoot β₁ := by
    apply hinj
    rw [map_zsmul, map_zsmul]
    refine smul_right_injective _ hi ?_
    calc
      D.coordinateRoot α i • (φ (D.coordinateRoot β₁) i • φ (D.coordinateRoot β₂))
          = φ (D.coordinateRoot β₁) i • (D.coordinateRoot α i • φ (D.coordinateRoot β₂)) :=
        smul_comm _ _ _
      _ = φ (D.coordinateRoot β₁) i • (φ (D.coordinateRoot β₂) i • D.coordinateRoot α) := by
        rw [hp₂]
      _ = φ (D.coordinateRoot β₂) i • (φ (D.coordinateRoot β₁) i • D.coordinateRoot α) :=
        smul_comm _ _ _
      _ = φ (D.coordinateRoot β₂) i • (D.coordinateRoot α i • φ (D.coordinateRoot β₁)) := by
        rw [← hp₁]
      _ = _ := smul_comm _ _ _
  have hβ : β₁ = β₂ := by
    rcases D.coordinateRoot_eq_or_eq_neg_of_smul_eq hm₁ hpropβ with heq | hcoord_neg
    · exact heq
    · refine (D.false_of_ringHom_torusCharacter_mul_eq_one (δ := α) (g₁ := g₁) (g₂ := g₂)
        fun s => ?_).elim
      rw [h₁ s, h₂ s, hcoord_neg, map_neg, torusCharacter_neg, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ (Units.ne_zero _)]
  subst hβ
  refine ⟨rfl, RingHom.eq_of_pow_eq_pow g₁ g₂ (Int.natAbs_ne_zero.mpr hi) fun x hx =>
    TauCeti.pow_natAbs_eq_of_zpow_eq ?_⟩
  let u : Kˣ := Units.mk0 x hx
  have hs₁ := h₁ (Pi.mulSingle i u)
  have hs₂ := h₂ (Pi.mulSingle i u)
  simp only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0, u] at hs₁ hs₂
  exact (map_zpow₀ g₁ x _).symm.trans (hs₁.trans (hs₂.symm.trans (map_zpow₀ g₂ x _)))

/-- **Root-subgroup structure of a standard endomorphism.** Over an infinite field with divisible
units, a standard endomorphism `F` with character map `φ` sends each root subgroup `x_α` to
`u ↦ x_β(c · g(u))` for a root `β`, a unit `c`, and a field automorphism `g : K ≃+* K`
intertwining `α` with `φ β`, which is rationally proportional to `α`. -/
theorem exists_root_and_ringEquiv_of_isStandardEndomorphism {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism K F) (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (α : Fin t.numRoots) :
    ∃ (β : Fin t.numRoots) (c : Kˣ) (g : K ≃+* K),
      (∀ u : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
        D.rootSubgroupPoints β K (ofAdd ((c : K) * g u))) ∧
      (∀ s : Fin t.rank → Kˣ,
        g (torusCharacter s (D.coordinateRoot α)) =
          torusCharacter s (φ (D.coordinateRoot β))) ∧
      (∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧
        n • φ (D.coordinateRoot β) = m • D.coordinateRoot α) := by
  obtain ⟨β, hβ⟩ := isStandardEndomorphism_iff.mp hstd α
  have hex (u : K) : ∃ v : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints β K (ofAdd v) := by
    obtain ⟨w, hw⟩ : F (D.rootSubgroupPoints α K (ofAdd u)) ∈ (D.rootSubgroupPoints β K).range :=
      hβ ▸ ⟨_, ⟨ofAdd u, rfl⟩, rfl⟩
    exact ⟨toAdd w, by simpa only [ofAdd_toAdd] using hw.symm⟩
  choose f hf using hex
  have hf_add (u v : K) : f (u + v) = f u + f v := ofAdd.injective <|
    D.rootSubgroupPoints_injective β K <| by
      rw [← hf (u + v), ofAdd_add, map_mul, map_mul, hf u, hf v, ← map_mul, ← ofAdd_add]
  have hf_zero : f 0 = 0 := ofAdd.injective <| D.rootSubgroupPoints_injective β K <| by
    rw [← hf 0, ofAdd_zero, map_one, map_one, map_one]
  have hf_scale (s : Fin t.rank → Kˣ) (u : K) :
      f ((torusCharacter s (D.coordinateRoot α) : K) * u) =
        (torusCharacter s (φ (D.coordinateRoot β)) : K) * f u := by
    have hconj := congrArg F (D.torusPoints_conj_rootSubgroupPoints α K s u)
    rw [map_mul, map_mul, map_inv, hφ.map_apply s, hf u,
      D.torusPoints_conj_rootSubgroupPoints, torusCharacter_torusPointMap, hf] at hconj
    exact ofAdd.injective (D.rootSubgroupPoints_injective β K hconj.symm)
  have hf_surj : Function.Surjective f := fun v => by
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ :
        D.rootSubgroupPoints β K (ofAdd v) ∈ (D.rootSubgroupPoints α K).range.map F :=
      hβ.symm ▸ ⟨ofAdd v, rfl⟩
    exact ⟨toAdd u, ofAdd.injective <| D.rootSubgroupPoints_injective β K <| by
      rw [← hf (toAdd u), ofAdd_toAdd, hu]⟩
  have hf1_ne : f 1 ≠ 0 := fun h0 => by
    obtain ⟨u, hu⟩ := hf_surj 1
    have hf_all (a : K) : f a = 0 := by
      by_cases ha : a = 0
      · rw [ha, hf_zero]
      · obtain ⟨s, hs⟩ := torusCharacter_surjective (R := K) (D.coordinateRoot_ne_zero α)
          (Units.mk0 a ha)
        dsimp only at hs
        simpa only [hs, Units.val_mk0, mul_one, h0, mul_zero] using hf_scale s 1
    exact one_ne_zero (hu.symm.trans (hf_all u))
  let c : Kˣ := Units.mk0 (f 1) hf1_ne
  have hg_one : ((c⁻¹ : Kˣ) : K) * f 1 = 1 := by simp [c, hf1_ne]
  have hg_scale (s : Fin t.rank → Kˣ) (u : K) :
      ((c⁻¹ : Kˣ) : K) * f ((torusCharacter s (D.coordinateRoot α) : K) * u) =
        (torusCharacter s (φ (D.coordinateRoot β)) : K) * (((c⁻¹ : Kˣ) : K) * f u) := by
    rw [hf_scale s u]; ring
  have hg_char (s : Fin t.rank → Kˣ) :
      ((c⁻¹ : Kˣ) : K) * f (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β)) := by
    simpa only [mul_one, hg_one] using hg_scale s 1
  let gHom : K →+* K :=
    { toFun := fun u => ((c⁻¹ : Kˣ) : K) * f u
      map_one' := hg_one
      map_mul' := fun a b => by
        by_cases ha : a = 0
        · simp [ha, hf_zero]
        · obtain ⟨s, hs⟩ := torusCharacter_surjective (R := K) (D.coordinateRoot_ne_zero α)
            (Units.mk0 a ha)
          dsimp only at hs
          have h1 := hg_scale s b; have h2 := hg_char s
          rw [hs, Units.val_mk0] at h1 h2; rw [h1, h2]
      map_zero' := by simp [hf_zero]
      map_add' := fun a b => by rw [hf_add, mul_add] }
  have hg_bij : Function.Bijective gHom := ⟨gHom.injective, fun v => by
    obtain ⟨u, hu⟩ := hf_surj ((c : K) * v)
    refine ⟨u, ?_⟩
    dsimp only [gHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hu, ← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero c), one_mul]⟩
  refine ⟨β, c, RingEquiv.ofBijective gHom hg_bij, fun u => ?_, hg_char, ?_⟩
  · rw [hf u, RingEquiv.ofBijective_apply]
    dsimp only [gHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero c), one_mul]
  · obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α i ≠ 0 :=
      Function.ne_iff.mp (D.coordinateRoot_ne_zero α)
    have hker : ∀ s : Fin t.rank → Kˣ,
        torusCharacter s (D.coordinateRoot α) = 1 →
          torusCharacter s (φ (D.coordinateRoot β)) = 1 :=
      fun s hs => Units.ext <| by simpa only [hs, Units.val_one, hg_one] using (hg_char s).symm
    have hp := smul_eq_smul_of_torusCharacter_eq_one hker i
    have hφβ_ne : φ (D.coordinateRoot β) ≠ 0 := fun h0 => by
      obtain ⟨s, hs⟩ : ∃ s : Fin t.rank → Kˣ, torusCharacter s (D.coordinateRoot α) ≠ 1 := by
        by_contra hall
        push Not at hall
        exact D.coordinateRoot_ne_zero α <| weightChar_injective (K := K) <|
          MonoidHom.ext fun s => by simpa only [weightChar_apply, torusCharacter_zero] using hall s
      have hgs : ((c⁻¹ : Kˣ) : K) * f (torusCharacter s (D.coordinateRoot α)) ≠ 1 := by
        simpa only [gHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one,
          map_one] using gHom.injective.ne fun h => hs (Units.ext h)
      have hc := hg_char s
      rw [h0, torusCharacter_zero, Units.val_one] at hc
      exact hgs hc
    have hm : φ (D.coordinateRoot β) i ≠ 0 := fun h0 => by
      rw [h0, zero_smul] at hp
      exact hφβ_ne ((smul_eq_zero.mp hp).resolve_left hi)
    exact ⟨φ (D.coordinateRoot β) i, D.coordinateRoot α i, hm, hi, hp⟩

/-- **A standard endomorphism with an injective character map induces a negation-preserving root
permutation** together with compatible units and field automorphisms on every root subgroup, over
every infinite field with divisible units. -/
theorem exists_rootPerm_of_isStandardEndomorphism {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism K F) (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hinj : Function.Injective φ) :
    ∃ (π : Equiv.Perm (Fin t.numRoots)) (c : Fin t.numRoots → Kˣ)
      (g : Fin t.numRoots → (K ≃+* K)),
      (∀ α u, F (D.rootSubgroupPoints α K (ofAdd u)) =
        D.rootSubgroupPoints (π α) K (ofAdd ((c α : K) * g α u))) ∧
      (∀ α (s : Fin t.rank → Kˣ),
        g α (torusCharacter s (D.coordinateRoot α)) =
          torusCharacter s (φ (D.coordinateRoot (π α)))) ∧
      (∀ α, π ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (π α) (π α)) ∧
      (∀ α, g ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = g α) ∧
      (∀ α, ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧
        n • φ (D.coordinateRoot (π α)) = m • D.coordinateRoot α) := by
  choose β c g hF hchar hprop using
    fun α => D.exists_root_and_ringEquiv_of_isStandardEndomorphism hstd hφ α
  have hneg_and_g (α : Fin t.numRoots) :
      β ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (β α) (β α) ∧
      g ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = g α := by
    let α' := (t.simplyConnectedRootDatum ht).reflectionPerm α α
    let β' := (t.simplyConnectedRootDatum ht).reflectionPerm (β α') (β α')
    have h₂ (s : Fin t.rank → Kˣ) :
        (g α').toRingHom (torusCharacter s (D.coordinateRoot α)) =
          torusCharacter s (φ (D.coordinateRoot β')) := by
      have hs := hchar α' s
      rw [D.coordinateRoot_reflectionPerm_self α, torusCharacter_neg, Units.val_inv_eq_inv_val,
        map_inv₀] at hs
      have hinv := congrArg Inv.inv hs
      rwa [inv_inv, ← Units.val_inv_eq_inv_val, ← torusCharacter_neg, ← map_neg,
        ← D.coordinateRoot_reflectionPerm_self (β α')] at hinv
    obtain ⟨hβeq, hgeq⟩ := D.eq_of_ringHom_torusCharacter_eq hinj
      (g₁ := (g α).toRingHom) (g₂ := (g α').toRingHom) (hchar α) h₂
    refine ⟨?_, RingEquiv.ext fun x => DFunLike.congr_fun hgeq.symm x⟩
    rw [hβeq]
    exact (reflectionPerm_self_involutive (t.simplyConnectedRootDatum ht) (β α')).symm
  have hβ_inj : Function.Injective β := by
    intro α₁ α₂ hβeq
    obtain ⟨m₁, n₁, _, hn₁, hp₁⟩ := hprop α₁
    obtain ⟨m₂, n₂, hm₂, _, hp₂⟩ := hprop α₂
    rw [hβeq] at hp₁
    have hcoord : (n₁ * m₂) • D.coordinateRoot α₂ = (n₂ * m₁) • D.coordinateRoot α₁ := by
      calc
        (n₁ * m₂) • D.coordinateRoot α₂ = n₁ • (m₂ • D.coordinateRoot α₂) := mul_smul _ _ _
        _ = n₁ • (n₂ • φ (D.coordinateRoot (β α₂))) := by rw [← hp₂]
        _ = n₂ • (n₁ • φ (D.coordinateRoot (β α₂))) := smul_comm _ _ _
        _ = n₂ • (m₁ • D.coordinateRoot α₁) := by rw [hp₁]
        _ = (n₂ * m₁) • D.coordinateRoot α₁ := (mul_smul _ _ _).symm
    rcases D.coordinateRoot_eq_or_eq_neg_of_smul_eq (mul_ne_zero hn₁ hm₂) hcoord
      with heq | hcoord_neg
    · exact heq
    · have hneg' : D.coordinateRoot α₂ =
          D.coordinateRoot ((t.simplyConnectedRootDatum ht).reflectionPerm α₁ α₁) :=
        hcoord_neg.trans (D.coordinateRoot_reflectionPerm_self α₁).symm
      have hα₂ : α₂ = (t.simplyConnectedRootDatum ht).reflectionPerm α₁ α₁ :=
        (t.simplyConnectedRootDatum ht).root.injective <| by
          simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using
            congrArg D.weightLatticeEmbedding hneg'
      have hβ_refl :
          β α₁ = (t.simplyConnectedRootDatum ht).reflectionPerm (β α₁) (β α₁) := by
        calc
          β α₁ = β α₂ := hβeq
          _ = β ((t.simplyConnectedRootDatum ht).reflectionPerm α₁ α₁) := by rw [hα₂]
          _ = (t.simplyConnectedRootDatum ht).reflectionPerm (β α₁) (β α₁) :=
            (hneg_and_g α₁).1
      have h2 : (2 : ℤ) • D.coordinateRoot (β α₁) = 0 := by
        have hneg := congrArg D.coordinateRoot hβ_refl
        rw [D.coordinateRoot_reflectionPerm_self] at hneg
        rw [two_smul]
        nth_rw 2 [hneg]
        rw [add_neg_cancel]
      exact (D.coordinateRoot_ne_zero (β α₁) ((smul_eq_zero.mp h2).resolve_left (by decide))).elim
  let π : Equiv.Perm (Fin t.numRoots) :=
    Equiv.ofBijective β (Finite.injective_iff_bijective.mp hβ_inj)
  exact ⟨π, c, g, hF, hchar, fun α => (hneg_and_g α).1, fun α => (hneg_and_g α).2, hprop⟩

/-- If a based endomorphism maps `x_α` onto `x_{π α}` over a nontrivial commutative ring, then `π`
preserves the set of positive roots. -/
theorem mem_posRoots_iff_of_isBasedEndomorphism {A : Type v} [CommRing A] [Nontrivial A]
    {F : D.points A →* D.points A} (hbased : D.IsBasedEndomorphism A F)
    {π : Equiv.Perm (Fin t.numRoots)}
    (hπ : ∀ α, (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints (π α) A).range)
    (α : Fin t.numRoots) :
    π α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ↔
      α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  have hfwd : Set.MapsTo π (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) := fun γ hγ => by
    obtain ⟨β, hβ, hmap⟩ := (isBasedEndomorphism_iff.mp hbased).2 γ hγ
    rwa [(D.range_rootSubgroupPoints_eq_iff A (π γ) β).mp ((hπ γ).symm.trans hmap)]
  have hbij := ((posRoots_finite _ _).injOn_iff_bijOn_of_mapsTo hfwd).mp π.injective.injOn
  refine ⟨fun hπα => ?_, fun hα => hfwd hα⟩
  obtain ⟨γ, hγ, hπγ⟩ := hbij.surjOn hπα
  rwa [← π.injective hπγ]

end TauCeti.DynkinType.ChevalleyDatum
