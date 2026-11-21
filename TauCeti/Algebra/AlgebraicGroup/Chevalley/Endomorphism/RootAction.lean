/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Quotient
import Mathlib.RingTheory.RootsOfUnity.Basic

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
  endomorphism over an integral domain, the induced root permutation preserves positive roots.

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

private theorem pow_natAbs_eq_one_of_zpow_eq_one {K : Type*} [Field K] {x : K} {n : ℤ}
    (h : x ^ n = 1) : x ^ n.natAbs = 1 := by
  rcases Int.natAbs_eq n with hn | hn
  · rw [hn, zpow_natCast] at h; exact h
  · rw [hn, zpow_neg, zpow_natCast] at h; exact inv_eq_one.mp h

private theorem pow_natAbs_eq_of_zpow_eq {K : Type*} [Field K] {x y : K} {n : ℤ}
    (h : x ^ n = y ^ n) : x ^ n.natAbs = y ^ n.natAbs := by
  rcases Int.natAbs_eq n with hn | hn
  · rw [hn, zpow_natCast, zpow_natCast] at h; exact h
  · rw [hn, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast] at h; exact inv_injective h

private theorem finite_rootsOfUnity_set {K : Type*} [Field K] {N : ℕ} (hN : N ≠ 0) :
    {ζ : K | ζ ^ N = 1}.Finite := by
  have : NeZero N := ⟨hN⟩
  let f : {ζ : K | ζ ^ N = 1} → rootsOfUnity N K := fun ζ =>
    ⟨Units.mk0 ζ.1 fun h0 => zero_ne_one (α := K) <| by
        have h : (ζ : K) ^ N = 1 := ζ.2
        rwa [h0, zero_pow hN] at h,
      by
        rw [mem_rootsOfUnity]
        exact Units.ext <| by
          have h : (ζ : K) ^ N = 1 := ζ.2
          simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using h⟩
  have hf : Function.Injective f := fun _ _ hab => Subtype.ext <| by
    simpa [f] using congrArg (fun u : rootsOfUnity N K => (u.1 : K)) hab
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

private theorem false_of_pow_mul_eq_one {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x * g₂ x) ^ N = 1) : False := by
  let R : Set K := {ζ : K | ζ ^ N = 1}
  have hR : R.Finite := finite_rootsOfUnity_set hN
  let Q : K × K → Set K := fun p => {y : K | y ^ 2 - (p.2 - 1 - p.1) * y + p.1 = 0}
  have hQ (p : K × K) : (Q p).Finite := by
    by_cases hne : (Q p).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      refine (Set.toFinite ({y₀, (p.2 - 1 - p.1) - y₀} : Set K)).subset fun y hy => ?_
      have hfac : (y - y₀) * (y + y₀ - (p.2 - 1 - p.1)) = 0 := by
        have h1 : y ^ 2 - (p.2 - 1 - p.1) * y + p.1 = 0 := hy
        have h2 : y₀ ^ 2 - (p.2 - 1 - p.1) * y₀ + p.1 = 0 := hy₀
        linear_combination h1 - h2
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · exact Or.inl (sub_eq_zero.mp hsub)
      · exact Or.inr (eq_of_sub_eq_zero (by linear_combination hadd))
    · exact (Set.not_nonempty_iff_eq_empty.mp hne) ▸ Set.finite_empty
  have hU : (⋃ p ∈ R ×ˢ R, Q p).Finite := (hR.prod hR).biUnion fun p _ => hQ p
  let T : Set K := Set.univ \ ({0, -1} : Set K)
  have hsub : g₁ '' T ⊆ ⋃ p ∈ R ×ˢ R, Q p := by
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    have hx0 : x ≠ 0 := fun h0 => hx (Or.inl h0)
    have hx1 : 1 + x ≠ 0 := fun h1 => hx (Or.inr (eq_of_sub_eq_zero (by linear_combination h1)))
    have hp : (g₁ x * g₂ x, g₁ (1 + x) * g₂ (1 + x)) ∈ R ×ˢ R := ⟨h x hx0, h (1 + x) hx1⟩
    refine Set.mem_biUnion hp ?_
    change (g₁ x) ^ 2 - (g₁ (1 + x) * g₂ (1 + x) - 1 - g₁ x * g₂ x) * g₁ x + g₁ x * g₂ x = 0
    rw [map_add, map_one, map_add, map_one]
    ring
  exact ((Set.infinite_univ.sdiff (Set.toFinite _)).image g₁.injective.injOn) (hU.subset hsub)

private theorem eq_of_pow_eq_pow {K : Type*} [Field K] [Infinite K]
    (g₁ g₂ : K →+* K) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ x : K, x ≠ 0 → (g₁ x) ^ N = (g₂ x) ^ N) : g₁ = g₂ := by
  let R : Set K := {ζ : K | ζ ^ N = 1}
  have hR : R.Finite := finite_rootsOfUnity_set hN
  let E : K × K → Set K := fun p => {y : K | p.1 ≠ p.2 ∧ (p.1 - p.2) * y = p.2 - 1}
  have hE (p : K × K) : (E p).Finite := Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ => by
    have hdiff : (p.1 - p.2) * (y₁ - y₂) = 0 := by
      have h1 : (p.1 - p.2) * y₁ = p.2 - 1 := hy₁.2
      have h2 : (p.1 - p.2) * y₂ = p.2 - 1 := hy₂.2
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hy₁.1))
  let B : Set K := ⋃ p ∈ R ×ˢ R, E p
  have hB : B.Finite := (hR.prod hR).biUnion fun p _ => hE p
  let bad : Set K := {x : K | g₁ x ≠ g₂ x}
  have hbad_sub : bad ⊆ ({0, -1} : Set K) ∪ g₂ ⁻¹' B := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl (Or.inl hx0)
    by_cases hx1 : x = -1
    · exact Or.inl (Or.inr hx1)
    right
    have hx1' : 1 + x ≠ 0 := fun h1 => hx1 (eq_of_sub_eq_zero (by linear_combination h1))
    have hg2x : g₂ x ≠ 0 := fun h0 => hx0 (g₂.injective (h0.trans (map_zero g₂).symm))
    have hg21x : g₂ (1 + x) ≠ 0 := fun h0 => hx1' (g₂.injective (h0.trans (map_zero g₂).symm))
    let ζ₁ : K := g₁ x * (g₂ x)⁻¹
    let ζ₂ : K := g₁ (1 + x) * (g₂ (1 + x))⁻¹
    have hζ₁ : ζ₁ ∈ R := by
      change (g₁ x * (g₂ x)⁻¹) ^ N = 1
      rw [mul_pow, inv_pow, h x hx0, mul_inv_cancel₀ (pow_ne_zero N hg2x)]
    have hζ₂ : ζ₂ ∈ R := by
      change (g₁ (1 + x) * (g₂ (1 + x))⁻¹) ^ N = 1
      rw [mul_pow, inv_pow, h (1 + x) hx1', mul_inv_cancel₀ (pow_ne_zero N hg21x)]
    have h1 : g₁ x = ζ₁ * g₂ x := (inv_mul_cancel_right₀ hg2x (g₁ x)).symm
    have h2 : 1 + g₁ x = ζ₂ * (1 + g₂ x) := by
      have h2' : g₁ (1 + x) = ζ₂ * g₂ (1 + x) := (inv_mul_cancel_right₀ hg21x (g₁ (1 + x))).symm
      simpa only [map_add, map_one] using h2'
    have heq : (ζ₁ - ζ₂) * g₂ x = ζ₂ - 1 := by linear_combination h2 - h1
    have hne : ζ₁ ≠ ζ₂ := fun h12 => by
      rw [h12, sub_self, zero_mul] at heq
      rw [h12.trans (eq_of_sub_eq_zero heq.symm), one_mul] at h1
      exact hx h1
    have hp : (ζ₁, ζ₂) ∈ R ×ˢ R := ⟨hζ₁, hζ₂⟩
    exact Set.mem_biUnion hp ⟨hne, heq⟩
  have hbad : bad.Finite :=
    ((Set.toFinite _).union (hB.preimage g₂.injective.injOn)).subset hbad_sub
  refine RingHom.ext fun x => ?_
  obtain ⟨y, hy⟩ := (Set.infinite_univ.sdiff (hbad.union (hbad.image (fun z => z - x)))).nonempty
  have hgy : g₁ y = g₂ y := not_not.mp fun hmem => hy.2 (Or.inl hmem)
  have hgxy : g₁ (x + y) = g₂ (x + y) := not_not.mp fun hmem => hy.2 (Or.inr ⟨x + y, hmem, by ring⟩)
  rw [map_add, map_add, hgy] at hgxy
  exact add_right_cancel hgxy

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
  have hN : (D.coordinateRoot α i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hi
  have hβ : β₁ = β₂ := by
    rcases D.eq_or_eq_neg_of_smul_coordinateRoot_eq hm₁ hpropβ with heq | hneg
    · exact (t.simplyConnectedRootDatum ht).root.injective heq
    · have hcoord_neg : D.coordinateRoot β₂ = -D.coordinateRoot β₁ := by
        apply D.weightLatticeEmbedding_injective
        rw [map_neg]
        simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using
          neg_eq_iff_eq_neg.mp hneg.symm
      refine (false_of_pow_mul_eq_one g₁ g₂ hN fun x hx => ?_).elim
      let u : Kˣ := Units.mk0 x hx
      refine pow_natAbs_eq_one_of_zpow_eq_one ?_
      rw [mul_zpow, ← map_zpow₀ g₁, ← map_zpow₀ g₂]
      have hs₁ := h₁ (Pi.mulSingle i u)
      have hs₂ := h₂ (Pi.mulSingle i u)
      simp only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0, u] at hs₁ hs₂
      rw [hs₁, hs₂, hcoord_neg, map_neg, Pi.neg_apply, zpow_neg,
        mul_inv_cancel₀ (zpow_ne_zero _ hx)]
  subst hβ
  refine ⟨rfl, eq_of_pow_eq_pow g₁ g₂ hN fun x hx => pow_natAbs_eq_of_zpow_eq ?_⟩
  let u : Kˣ := Units.mk0 x hx
  have hs₁ := h₁ (Pi.mulSingle i u)
  have hs₂ := h₂ (Pi.mulSingle i u)
  simp only [torusCharacter_mulSingle, Units.val_zpow_eq_zpow_val, Units.val_mk0, u] at hs₁ hs₂
  exact (map_zpow₀ g₁ x _).symm.trans (hs₁.trans (hs₂.symm.trans (map_zpow₀ g₂ x _)))

/-- **Root-subgroup structure of a standard endomorphism.** Over an infinite field with divisible
units, a standard endomorphism `F` with injective character map `φ` sends each root subgroup `x_α`
to `u ↦ x_β(c · g(u))` for a root `β`, a unit `c`, and a field automorphism `g : K ≃+* K`
intertwining `α` with `φ β`, which is rationally proportional to `α`. -/
theorem exists_root_and_ringEquiv_of_isStandardEndomorphism {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hstd : D.IsStandardEndomorphism K F) (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hinj : Function.Injective φ) (α : Fin t.numRoots) :
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
    change ((c⁻¹ : Kˣ) : K) * f u = v
    rw [hu, ← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero c), one_mul]⟩
  refine ⟨β, c, RingEquiv.ofBijective gHom hg_bij, fun u => ?_, hg_char, ?_⟩
  · rw [hf u]; congr 2
    change f u = (c : K) * (((c⁻¹ : Kˣ) : K) * f u)
    simp
  · obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α i ≠ 0 :=
      Function.ne_iff.mp (D.coordinateRoot_ne_zero α)
    have hker : ∀ s : Fin t.rank → Kˣ,
        torusCharacter s (D.coordinateRoot α) = 1 →
          torusCharacter s (φ (D.coordinateRoot β)) = 1 :=
      fun s hs => Units.ext <| by simpa only [hs, Units.val_one, hg_one] using (hg_char s).symm
    have hp := smul_eq_smul_of_torusCharacter_eq_one hker i
    have hm : φ (D.coordinateRoot β) i ≠ 0 := fun h0 => by
      rw [h0, zero_smul] at hp
      exact D.coordinateRoot_ne_zero β
        (hinj (((smul_eq_zero.mp hp).resolve_left hi).trans (map_zero φ).symm))
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
    fun α => D.exists_root_and_ringEquiv_of_isStandardEndomorphism hstd hφ hinj α
  have hβ_inj : Function.Injective β := by
    intro α₁ α₂ hβeq
    obtain ⟨m₁, n₁, _, hn₁, hp₁⟩ := hprop α₁
    obtain ⟨m₂, n₂, hm₂, hn₂, hp₂⟩ := hprop α₂
    rw [hβeq] at hp₁
    have hcoord : (n₁ * m₂) • D.coordinateRoot α₂ = (n₂ * m₁) • D.coordinateRoot α₁ := by
      calc
        (n₁ * m₂) • D.coordinateRoot α₂ = n₁ • (m₂ • D.coordinateRoot α₂) := mul_smul _ _ _
        _ = n₁ • (n₂ • φ (D.coordinateRoot (β α₂))) := by rw [← hp₂]
        _ = n₂ • (n₁ • φ (D.coordinateRoot (β α₂))) := smul_comm _ _ _
        _ = n₂ • (m₁ • D.coordinateRoot α₁) := by rw [hp₁]
        _ = (n₂ * m₁) • D.coordinateRoot α₁ := (mul_smul _ _ _).symm
    rcases D.eq_or_eq_neg_of_smul_coordinateRoot_eq (mul_ne_zero hn₁ hm₂) hcoord with heq | hneg
    · exact (t.simplyConnectedRootDatum ht).root.injective heq
    · have hcoord_neg : D.coordinateRoot α₂ = -D.coordinateRoot α₁ := by
        apply D.weightLatticeEmbedding_injective
        rw [map_neg]
        simpa only [coordinateRoot_def, D.weightLatticeEmbedding_repr, Submodule.coe_mk] using
          neg_eq_iff_eq_neg.mp hneg.symm
      obtain ⟨i, hi⟩ : ∃ i, D.coordinateRoot α₁ i ≠ 0 :=
        Function.ne_iff.mp (D.coordinateRoot_ne_zero α₁)
      refine (false_of_pow_mul_eq_one (g α₁).toRingHom (g α₂).toRingHom
        (Int.natAbs_ne_zero.mpr hi) fun x hx => pow_natAbs_eq_one_of_zpow_eq_one ?_).elim
      let u : Kˣ := Units.mk0 x hx
      have hs₁ := hchar α₁ (Pi.mulSingle i u)
      have hs₂ := hchar α₂ (Pi.mulSingle i u)
      rw [hβeq, torusCharacter_mulSingle] at hs₁
      rw [hcoord_neg, torusCharacter_neg, torusCharacter_mulSingle] at hs₂
      have hs₁' : (g α₁) (x ^ D.coordinateRoot α₁ i) =
          (torusCharacter (Pi.mulSingle i u) (φ (D.coordinateRoot (β α₂))) : K) := by
        simpa only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0] using hs₁
      have hs₂' : ((g α₂) (x ^ D.coordinateRoot α₁ i))⁻¹ =
          (torusCharacter (Pi.mulSingle i u) (φ (D.coordinateRoot (β α₂))) : K) := by
        simpa only [u, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0,
          map_inv₀] using hs₂
      rw [mul_zpow, ← map_zpow₀ (g α₁).toRingHom, ← map_zpow₀ (g α₂).toRingHom]
      change (g α₁) (x ^ D.coordinateRoot α₁ i) * (g α₂) (x ^ D.coordinateRoot α₁ i) = 1
      rw [hs₁', ← hs₂', inv_mul_cancel₀ fun h0 =>
        zpow_ne_zero _ hx ((g α₂).injective (h0.trans (map_zero _).symm))]
  let π : Equiv.Perm (Fin t.numRoots) :=
    Equiv.ofBijective β (Finite.injective_iff_bijective.mp hβ_inj)
  have hneg_and_g (α : Fin t.numRoots) :
      π ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (π α) (π α) ∧
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
    change β α' = (t.simplyConnectedRootDatum ht).reflectionPerm (β α) (β α)
    rw [hβeq]
    exact (reflectionPerm_self_involutive (t.simplyConnectedRootDatum ht) (β α')).symm
  exact ⟨π, c, g, hF, hchar, fun α => (hneg_and_g α).1, fun α => (hneg_and_g α).2, hprop⟩

/-- If a based endomorphism maps `x_α` onto `x_{π α}` over an integral domain, then `π` preserves
the set of positive roots. -/
theorem mem_posRoots_iff_of_isBasedEndomorphism {A : Type v} [CommRing A] [IsDomain A]
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
