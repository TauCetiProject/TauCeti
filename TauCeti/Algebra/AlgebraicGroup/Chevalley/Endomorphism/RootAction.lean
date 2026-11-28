/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.ClosedImmersion
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
import TauCeti.Algebra.Group.Pow
import TauCeti.FieldTheory.RingHom

/-!
# Root permutations and field automorphisms of standard endomorphisms

Over an infinite field with divisible units (in particular an algebraically closed field), a
standard endomorphism `F` of a Chevalley datum `D` with an injective character map `φ` acts on
each root subgroup by `F (x_α(u)) = x_{π α}(c_α · g_α(u))` for a permutation `π` of the roots,
units `c_α`, and field automorphisms `g_α : K ≃+* K` satisfying `g_α(α(s)) = (φ (π α))(s)` and
rational proportionality between `φ (π α)` and `α`.

Both the target root `π α` and the field endomorphism `g_α` are uniquely determined by `(α, φ)`
alone over any infinite field, even without divisible units
(`ChevalleyDatum.rootIndex_eq_and_ringHom_eq_of_torusCharacter_eq`); in particular `π` commutes
with root negation and `g_{-α} = g_α`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.rootIndex_eq_and_ringHom_eq_of_torusCharacter_eq`: over an
  infinite field, an injective character map and a fixed source root jointly determine both the
  target root (including sign) and the field endomorphism.
* `TauCeti.DynkinType.ChevalleyDatum.exists_root_and_ringEquiv_of_isStandardEndomorphism`: root
  action `F (x_α(u)) = x_β(c · g(u))` on a single root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.exists_rootPerm_of_isStandardEndomorphism`: over an infinite
  field with divisible units (`[Infinite K]` and `[RootableBy Kˣ ℕ]`), every standard
  endomorphism with an injective character map induces a negation-preserving permutation of the
  roots and compatible field automorphisms on every root subgroup.
* `TauCeti.DynkinType.ChevalleyDatum.mem_posRoots_iff_of_isBasedEndomorphism`: over a nontrivial
  commutative ring, any permutation `π` realizing the root-subgroup images of a based endomorphism
  preserves positive roots.

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

private theorem not_forall_ringHom_torusCharacter_mul_eq_one {K : Type*} [Field K] [Infinite K]
    {δ : Fin t.numRoots} {g₁ g₂ : K →+* K} :
    ¬ ∀ s : Fin t.rank → Kˣ,
      (g₁ (torusCharacter s (D.coordinateRoot δ)) : K) *
        g₂ (torusCharacter s (D.coordinateRoot δ)) = 1 := by
  intro h
  obtain ⟨i, hi⟩ := D.exists_coordinateRoot_ne_zero δ
  refine RingHom.not_forall_mul_apply_pow_eq_one g₁ g₂ (Int.natAbs_ne_zero.mpr hi)
    fun x hx => ?_
  have h1 : (g₁ x * g₂ x) ^ D.coordinateRoot δ i = (1 : K) ^ D.coordinateRoot δ i := by
    rw [one_zpow, mul_zpow, ← map_zpow₀ g₁, ← map_zpow₀ g₂]
    have hs := h (Pi.mulSingle i (Units.mk0 x hx))
    simpa only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0] using hs
  exact (TauCeti.pow_natAbs_eq_of_zpow_eq h1).trans (one_pow _)

private theorem smul_coordinateRoot_eq_of_forall_ringHom_torusCharacter
    {K : Type*} [Field K] [Infinite K] {φ : Module.End ℤ (Fin t.rank → ℤ)}
    {α β : Fin t.numRoots} {g : K →+* K}
    (hg : ∀ s : Fin t.rank → Kˣ,
      g (torusCharacter s (D.coordinateRoot α)) = torusCharacter s (φ (D.coordinateRoot β)))
    {i : Fin t.rank} (hi : D.coordinateRoot α i ≠ 0) :
    D.coordinateRoot α i • φ (D.coordinateRoot β) =
      φ (D.coordinateRoot β) i • D.coordinateRoot α ∧ φ (D.coordinateRoot β) i ≠ 0 := by
  have hk : (weightChar K (D.coordinateRoot α)).ker ≤
      (weightChar K (φ (D.coordinateRoot β))).ker := by
    intro s hs
    rw [MonoidHom.mem_ker, weightChar_apply] at hs ⊢
    exact Units.ext <| by simpa only [hs, Units.val_one, map_one] using (hg s).symm
  have hp := smul_eq_smul_of_weightChar_ker_le hk i
  refine ⟨hp, fun h0 => ?_⟩
  rw [h0, zero_smul] at hp
  have hφβ0 : φ (D.coordinateRoot β) = 0 := (smul_eq_zero.mp hp).resolve_left hi
  obtain ⟨s, hs⟩ := D.exists_torusCharacter_coordinateRoot_ne_one (K := K) α
  have hgs := hg s
  rw [hφβ0, torusCharacter_zero, Units.val_one] at hgs
  exact hs (Units.ext (g.injective (hgs.trans (map_one g).symm)))

/-- **Uniqueness of the target root and field endomorphism from the character map.** Over any
infinite field, an injective character map `φ` and source root `α` uniquely determine both the
target root `β` (including its sign) and the field endomorphism `g : K →+* K` satisfying
`g (α(s)) = (φ β)(s)` for all torus parameters `s`. Divisibility of `Kˣ` is not required. -/
theorem rootIndex_eq_and_ringHom_eq_of_torusCharacter_eq {K : Type*} [Field K] [Infinite K]
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hinj : Function.Injective φ)
    {α β₁ β₂ : Fin t.numRoots} {g₁ g₂ : K →+* K}
    (h₁ : ∀ s : Fin t.rank → Kˣ,
      g₁ (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β₁)))
    (h₂ : ∀ s : Fin t.rank → Kˣ,
      g₂ (torusCharacter s (D.coordinateRoot α)) =
        torusCharacter s (φ (D.coordinateRoot β₂))) :
    β₁ = β₂ ∧ g₁ = g₂ := by
  -- Step 1: relate both `φ β₁` and `φ β₂` to `α` with nonzero proportionality coefficients.
  obtain ⟨i, hi⟩ := D.exists_coordinateRoot_ne_zero α
  obtain ⟨hp₁, hm₁⟩ := D.smul_coordinateRoot_eq_of_forall_ringHom_torusCharacter h₁ hi
  obtain ⟨hp₂, _⟩ := D.smul_coordinateRoot_eq_of_forall_ringHom_torusCharacter h₂ hi
  -- Step 2: infer `β₁ = ±β₂` by injectivity of `φ` and rule out `-β₂` via `g₁ · g₂ ≠ 1`.
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
    rcases D.eq_or_eq_reflectionPerm_of_smul_coordinateRoot_eq hm₁ hpropβ with heq | hcoord_neg
    · exact heq
    · refine absurd (fun s => ?_)
        (D.not_forall_ringHom_torusCharacter_mul_eq_one (δ := α) (g₁ := g₁) (g₂ := g₂))
      rw [h₁ s, h₂ s, hcoord_neg, D.coordinateRoot_reflectionPerm_self, map_neg, torusCharacter_neg,
        Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
  -- Step 3: conclude `g₁ = g₂` from pointwise power agreement along coordinate `i`.
  subst hβ
  refine ⟨rfl, RingHom.eq_of_forall_apply_pow_eq g₁ g₂ (Int.natAbs_ne_zero.mpr hi) fun x hx =>
    TauCeti.pow_natAbs_eq_of_zpow_eq ?_⟩
  let u : Kˣ := Units.mk0 x hx
  have hs₁ := h₁ (Pi.mulSingle i u)
  have hs₂ := h₂ (Pi.mulSingle i u)
  simp only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0, u] at hs₁ hs₂
  exact (map_zpow₀ g₁ x _).symm.trans (hs₁.trans (hs₂.symm.trans (map_zpow₀ g₂ x _)))

private theorem exists_additive_equivariant_of_rootSubgroup_map {K : Type v} [Field K]
    {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap (D.torusPoints K) F φ) {α β : Fin t.numRoots}
    (hβ : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) :
    ∃ f : K → K,
      (∀ u : K, F (D.rootSubgroupPoints α K (ofAdd u)) = D.rootSubgroupPoints β K (ofAdd (f u))) ∧
      (∀ u v : K, f (u + v) = f u + f v) ∧
      (∀ (s : Fin t.rank → Kˣ) (u : K),
        f ((torusCharacter s (D.coordinateRoot α) : K) * u) =
          (torusCharacter s (φ (D.coordinateRoot β)) : K) * f u) ∧
      Function.Surjective f := by
  have hex (u : K) : ∃ v : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints β K (ofAdd v) := by
    obtain ⟨w, hw⟩ : F (D.rootSubgroupPoints α K (ofAdd u)) ∈ (D.rootSubgroupPoints β K).range :=
      hβ ▸ ⟨_, ⟨ofAdd u, rfl⟩, rfl⟩
    exact ⟨toAdd w, by simpa only [ofAdd_toAdd] using hw.symm⟩
  choose f hf using hex
  have hf_add (u v : K) : f (u + v) = f u + f v := ofAdd.injective <|
    (D.rootSubgroupPoints_inj β K).mp <| by
      rw [← hf (u + v), ofAdd_add, map_mul, map_mul, hf u, hf v, ← map_mul, ← ofAdd_add]
  have hf_scale (s : Fin t.rank → Kˣ) (u : K) :
      f ((torusCharacter s (D.coordinateRoot α) : K) * u) =
        (torusCharacter s (φ (D.coordinateRoot β)) : K) * f u := by
    have hconj := congrArg F (D.torusPoints_conj_rootSubgroupPoints α K s u)
    rw [map_mul, map_mul, map_inv, hφ.map_apply s, hf u,
      D.torusPoints_conj_rootSubgroupPoints, torusCharacter_torusPointMap, hf] at hconj
    exact ofAdd.injective ((D.rootSubgroupPoints_inj β K).mp hconj.symm)
  have hf_surj : Function.Surjective f := fun v => by
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ :
        D.rootSubgroupPoints β K (ofAdd v) ∈ (D.rootSubgroupPoints α K).range.map F :=
      hβ.symm ▸ ⟨ofAdd v, rfl⟩
    exact ⟨toAdd u, ofAdd.injective <| (D.rootSubgroupPoints_inj β K).mp <| by
      rw [← hf (toAdd u), ofAdd_toAdd, hu]⟩
  exact ⟨f, hf, hf_add, hf_scale, hf_surj⟩

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
  obtain ⟨f, hf, hf_add, hf_scale, hf_surj⟩ :=
    D.exists_additive_equivariant_of_rootSubgroup_map hφ hβ
  obtain ⟨c, g, hfg, hg_char⟩ := exists_ringEquiv_of_additive_equivariant
    (D.coordinateRoot_ne_zero α) hf_add hf_scale hf_surj
  obtain ⟨i, hi⟩ := D.exists_coordinateRoot_ne_zero α
  obtain ⟨hp, hm⟩ := D.smul_coordinateRoot_eq_of_forall_ringHom_torusCharacter
    (g := g.toRingHom) hg_char hi
  exact ⟨β, c, g, fun u => by rw [hf u, hfg u], hg_char,
    φ (D.coordinateRoot β) i, D.coordinateRoot α i, hm, hi, hp⟩

private theorem rootPerm_injective_of_prop {φ : Module.End ℤ (Fin t.rank → ℤ)}
    {β : Fin t.numRoots → Fin t.numRoots}
    (hneg : ∀ α, β ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
      (t.simplyConnectedRootDatum ht).reflectionPerm (β α) (β α))
    (hprop : ∀ α, ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧
      n • φ (D.coordinateRoot (β α)) = m • D.coordinateRoot α) :
    Function.Injective β := by
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
  rcases D.eq_or_eq_reflectionPerm_of_smul_coordinateRoot_eq (mul_ne_zero hn₁ hm₂) hcoord
    with heq | hα₁
  · exact heq
  · have hβ_refl :
        β α₂ = (t.simplyConnectedRootDatum ht).reflectionPerm (β α₂) (β α₂) := by
      calc
        β α₂ = β α₁ := hβeq.symm
        _ = β ((t.simplyConnectedRootDatum ht).reflectionPerm α₂ α₂) := by rw [hα₁]
        _ = (t.simplyConnectedRootDatum ht).reflectionPerm (β α₂) (β α₂) := hneg α₂
    exact ((t.simplyConnectedRootDatum ht).ne_neg (β α₂) hβ_refl).elim

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
  -- Step 1: pick a target root, unit scalar, and field automorphism for each root subgroup.
  choose β c g hF hchar hprop using
    fun α => D.exists_root_and_ringEquiv_of_isStandardEndomorphism hstd hφ α
  -- Step 2: deduce negation compatibility and `g_{-α} = g_α` from character-map uniqueness.
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
    obtain ⟨hβeq, hgeq⟩ := D.rootIndex_eq_and_ringHom_eq_of_torusCharacter_eq hinj
      (g₁ := (g α).toRingHom) (g₂ := (g α').toRingHom) (hchar α) h₂
    refine ⟨?_, RingEquiv.ext fun x => DFunLike.congr_fun hgeq.symm x⟩
    rw [hβeq]
    exact (reflectionPerm_self_involutive (t.simplyConnectedRootDatum ht) (β α')).symm
  -- Step 3: promote `β` to a permutation via proportionality and negation compatibility.
  let π : Equiv.Perm (Fin t.numRoots) :=
    Equiv.ofBijective β
      (Finite.injective_iff_bijective.mp
        (D.rootPerm_injective_of_prop (fun α => (hneg_and_g α).1) hprop))
  exact ⟨π, c, g,
    fun α u => by simpa only [π, Equiv.coe_ofBijective] using hF α u,
    fun α s => by simpa only [π, Equiv.coe_ofBijective] using hchar α s,
    fun α => by simpa only [π, Equiv.coe_ofBijective] using (hneg_and_g α).1,
    fun α => (hneg_and_g α).2,
    fun α => by simpa only [π, Equiv.coe_ofBijective] using hprop α⟩

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
    rwa [(D.range_rootSubgroupPoints_inj A (π γ) β).mp ((hπ γ).symm.trans hmap)]
  have hbij := ((posRoots_finite _ _).injOn_iff_bijOn_of_mapsTo hfwd).mp π.injective.injOn
  refine ⟨fun hπα => ?_, fun hα => hfwd hα⟩
  obtain ⟨γ, hγ, hπγ⟩ := hbij.surjOn hπα
  rwa [← π.injective hπγ]

end TauCeti.DynkinType.ChevalleyDatum
