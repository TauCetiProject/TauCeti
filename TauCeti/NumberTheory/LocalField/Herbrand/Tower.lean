/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Quotient

/-!
# Transitivity of the Herbrand functions

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field Galois over `K`, so that `H = Gal(M/L)` is normal in `G` and
restriction to `L` identifies `Gal(L/K)` with `G / H`. Herbrand's theorem
`(G/H)_{φ_{M/L}(u)} = G_u H / H` has a **counting form**, `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`,
because `H_u = H ∩ G_u`. Both `φ_{M/K}` and `φ_{L/K} ∘ φ_{M/L}` are affine on each interval
`[m, m + 1]`, and the counting form says that their slopes `#G_{m+1} / #G_0` and
`(#H_{m+1} / #H_0) · (#(G/H)_{φ_{M/L}(m+1)} / #(G/H)_0)` agree; since both functions are the
identity on `[-1, 0]`, this gives the **transitivity of the Herbrand functions**

`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`   and   `ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`,

together with its integral form `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`.

## Main results

All declarations live in the namespace `TauCeti.LocalFieldsRamification`.

* `natCard_lowerRamificationGroupReal_herbrand_mul`: Herbrand's theorem in counting form,
  `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`.
* `lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand`: the filtration of
  `L/K` is constant on `(φ_{M/L}(a), φ_{M/L}(b)]` when that of `M/K` is constant on `(a, b]`.
* `herbrand_tower`: `φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`, as the identity
  `herbrandOrderIso K M = (herbrandOrderIso L M).trans (herbrandOrderIso K L)` of bundled order
  isomorphisms.
* `inverseHerbrand_tower`: `ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`, as the identity of the inverse order
  isomorphisms.
* `psiNat_tower`: `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Proposition 15.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [Algebra K M] [ValuativeExtension K M]
  [IsScalarTower K L M]

/-! ### Herbrand's theorem in counting form

Finiteness of `M/K` follows from that of `L/K` and `M/L` (`Module.Finite.trans`), but instance
synthesis cannot recover it, since `L` is not determined by `K` and `M`; the statements therefore
install `Module.Finite K M` with `haveI` rather than assuming it separately. -/

/-- **Herbrand's theorem in counting form.** For `G = Gal(M/K)`, `H = Gal(M/L)` and
`G/H = Gal(L/K)`, the orders satisfy `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`: the lower ramification
group of the quotient at `φ_{M/L}(u)` is the image of `G_u` under restriction to `L`, and the
kernel of restriction on `G_u` is `H ∩ G_u = H_u`. -/
theorem natCard_lowerRamificationGroupReal_herbrand_mul [Normal K L] [IsGalois L M] [Normal K M]
    (u : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) *
        Nat.card (lowerRamificationGroupReal L M u) =
      Nat.card (lowerRamificationGroupReal K M u) := by
  have : Module.Finite K M := Module.Finite.trans L M
  rw [← map_restrictNormalHom_lowerRamificationGroupReal (K := K) (L := L) (M := M) u,
    ← MonoidHom.domRestrict_range,
    ← Subgroup.card_map_of_injective (K := lowerRamificationGroupReal L M u)
      (AlgEquiv.restrictScalarsHom_injective K),
    map_restrictScalarsHom_lowerRamificationGroupReal K M L u,
    AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M,
    ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype, ← MonoidHom.ker_domRestrict,
    mul_comm, Subgroup.card_ker_mul_card_range]

/-- Through Herbrand's theorem, the lower filtration of `L/K` is constant on the interval
`(φ_{M/L}(a), φ_{M/L}(b)]` as soon as that of `M/K` is constant on `(a, b]`. -/
theorem lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand [Normal K L]
    [IsGalois L M] [Normal K M] {a b : RamificationIndexDomain} {t : ℝ}
    (ht₁ : (herbrand L M a : ℝ) < t) (ht₂ : t ≤ herbrand L M b) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    (∀ s : ℝ, (a : ℝ) < s → s ≤ b →
      lowerRamificationGroupReal K M s = lowerRamificationGroupReal K M b) →
    lowerRamificationGroupReal K L t = lowerRamificationGroupReal K L (herbrand L M b) := by
  have : Module.Finite K M := Module.Finite.trans L M
  intro h
  set s : RamificationIndexDomain := ⟨t, Set.mem_Ici.2 ((herbrand L M a).2.trans ht₁.le)⟩
  -- `t = φ_{M/L}(ψ_{M/L}(t))` with `a < ψ_{M/L}(t) ≤ b`.
  have hs₁ : a < inverseHerbrand L M s := by
    rw [← inverseHerbrand_herbrand L M a]
    exact inverseHerbrand_strictMono L M (Subtype.coe_lt_coe.1 ht₁)
  have hs₂ : inverseHerbrand L M s ≤ b := by
    rw [← inverseHerbrand_herbrand L M b]
    exact (inverseHerbrand_strictMono L M).monotone (Subtype.coe_le_coe.1 ht₂)
  have ht : t = herbrand L M (inverseHerbrand L M s) := by rw [herbrand_inverseHerbrand]
  rw [ht, ← map_restrictNormalHom_lowerRamificationGroupReal,
    ← map_restrictNormalHom_lowerRamificationGroupReal, h _ hs₁ hs₂]

/-! ### Transitivity of the Herbrand functions

Here `L/K` and `M/K` are Galois, so `M/L` is Galois as well (`IsGalois.tower_top_of_isGalois`).
Since `L` is an arbitrary field rather than an `IntermediateField K M`, instance synthesis cannot
recover `IsGalois L M` from `[IsGalois K M]`; the statements below therefore install it with
`haveI` as well. -/

variable [IsGalois K L] [IsGalois K M]

/-- The transitivity `φ_{M/K}(u) = φ_{L/K}(φ_{M/L}(u))` propagates from the left endpoint `m` of
an interval `[m, m + 1]`, `m : ℕ`, to every point `u` of that interval: both sides are affine
there, and Herbrand's theorem in counting form identifies their slopes. -/
private theorem herbrand_tower_of_mem_Icc_of_eq (m : ℕ) {u : RamificationIndexDomain}
    (h₁ : (m : ℝ) ≤ u) (h₂ : (u : ℝ) ≤ m + 1) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    herbrand K M ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩ =
        herbrand K L (herbrand L M ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩) →
      herbrand K M u = herbrand K L (herbrand L M u) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  intro hm
  set a : RamificationIndexDomain := ⟨m, Nat.cast_mem_ramificationIndexDomain m⟩
  have hau : a ≤ u := Subtype.coe_le_coe.1 h₁
  -- The lower filtrations of `M/K` and `M/L` are constant on `(m, u] ⊆ (m, m + 1]`.
  have hGM : ∀ t : ℝ, (a : ℝ) < t → t ≤ u →
      lowerRamificationGroupReal K M t = lowerRamificationGroupReal K M u := fun t ht₁ ht₂ ↦ by
    rw [lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  have hHM : ∀ t : ℝ, (a : ℝ) < t → t ≤ u →
      lowerRamificationGroupReal L M t = lowerRamificationGroupReal L M u := fun t ht₁ ht₂ ↦ by
    rw [lowerRamificationGroupReal_eq_of_sub_one_lt_of_le L M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      lowerRamificationGroupReal_eq_of_sub_one_lt_of_le L M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  -- The three affine formulas and the two counting identities.
  have hMK := coe_herbrand_sub_coe_herbrand_of_forall_eq K M hau hGM
  have hML := coe_herbrand_sub_coe_herbrand_of_forall_eq L M hau hHM
  have hLK := coe_herbrand_sub_coe_herbrand_of_forall_eq K L
    ((herbrand_strictMono L M).monotone hau) fun _ ht₁ ht₂ ↦
      lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand K L M ht₁ ht₂ hGM
  have hcard : (Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) : ℝ) *
      Nat.card (lowerRamificationGroupReal L M u) =
        Nat.card (lowerRamificationGroupReal K M u) := by
    exact_mod_cast natCard_lowerRamificationGroupReal_herbrand_mul K L M u
  have hcard₀ : (Nat.card (lowerRamificationGroup K L 0) : ℝ) *
      Nat.card (lowerRamificationGroup L M 0) = Nat.card (lowerRamificationGroup K M 0) := by
    rw [natCard_lowerRamificationGroup_zero, natCard_lowerRamificationGroup_zero,
      natCard_lowerRamificationGroup_zero, ramificationIndex_tower (K := K) (L := L) M]
    push_cast
    ring
  -- The slopes agree: `#G_u / #G_0 = (#H_u / #H_0) · (#(G/H)_{φ(u)} / #(G/H)_0)`.
  have hslope : (Nat.card (lowerRamificationGroupReal K M u) : ℝ) /
      Nat.card (lowerRamificationGroup K M 0) =
        (Nat.card (lowerRamificationGroupReal L M u) / Nat.card (lowerRamificationGroup L M 0)) *
          (Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) /
            Nat.card (lowerRamificationGroup K L 0)) := by
    rw [div_mul_div_comm, ← hcard, ← hcard₀,
      mul_comm (Nat.card (lowerRamificationGroupReal L M u) : ℝ),
      mul_comm (Nat.card (lowerRamificationGroup L M 0) : ℝ)]
  have hm' : (herbrand K M a : ℝ) = herbrand K L (herbrand L M a) := congrArg Subtype.val hm
  apply Subtype.ext
  rw [hslope] at hMK
  rw [hML] at hLK
  linear_combination hMK - hLK + hm'

/-- `φ_{M/K} = φ_{L/K} ∘ φ_{M/L}` on `[m, m + 1]`, by induction on `m : ℕ`. -/
private theorem herbrand_tower_of_mem_Icc (m : ℕ) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    ∀ u : RamificationIndexDomain, (m : ℝ) ≤ u → (u : ℝ) ≤ m + 1 →
      herbrand K M u = herbrand K L (herbrand L M u) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  induction m with
  | zero =>
    intro u h₁ h₂
    refine herbrand_tower_of_mem_Icc_of_eq K L M 0 h₁ h₂ ?_
    rw [herbrand_of_coe_le_zero L M (by simp), herbrand_of_coe_le_zero K L (by simp),
      herbrand_of_coe_le_zero K M (by simp)]
  | succ m ih =>
    intro u h₁ h₂
    exact herbrand_tower_of_mem_Icc_of_eq K L M (m + 1) h₁ h₂
      (ih _ (by push_cast; linarith) (by push_cast; linarith))

/-- **Transitivity of the Herbrand function** in a tower `M/L/K` of Galois extensions:
`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`, as an identity of the bundled order isomorphisms of
`RamificationIndexDomain`. -/
theorem herbrand_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    herbrandOrderIso K M = (herbrandOrderIso L M).trans (herbrandOrderIso K L) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  refine OrderIso.ext <| funext fun u ↦ ?_
  rw [OrderIso.trans_apply, herbrandOrderIso_apply, herbrandOrderIso_apply, herbrandOrderIso_apply]
  rcases le_or_gt (u : ℝ) 0 with hu | hu
  · rw [herbrand_of_coe_le_zero L M hu, herbrand_of_coe_le_zero K L hu,
      herbrand_of_coe_le_zero K M hu]
  · exact herbrand_tower_of_mem_Icc K L M ⌊(u : ℝ)⌋₊ u (Nat.floor_le hu.le)
      (Nat.lt_floor_add_one _).le

/-- **Transitivity of the inverse Herbrand function** in a tower `M/L/K` of Galois extensions:
`ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`, as an identity of the inverse order isomorphisms. Inverting the
composite `φ_{L/K} ∘ φ_{M/L}` reverses its order. -/
theorem inverseHerbrand_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    (herbrandOrderIso K M).symm =
      (herbrandOrderIso K L).symm.trans (herbrandOrderIso L M).symm := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  rw [herbrand_tower K L M, OrderIso.symm_trans]

/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`. -/
theorem psiNat_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    psiNat K M = psiNat L M ∘ psiNat K L := funext fun n ↦ by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  have h : (⟨(psiNat K L n : ℝ), Nat.cast_mem_ramificationIndexDomain _⟩ :
        RamificationIndexDomain) =
      inverseHerbrand K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ :=
    Subtype.ext (coe_psiNat K L n)
  apply Nat.cast_injective (R := ℝ)
  rw [Function.comp_apply, coe_psiNat, coe_psiNat, h, ← herbrandOrderIso_symm_apply,
    inverseHerbrand_tower K L M, OrderIso.trans_apply, herbrandOrderIso_symm_apply,
    herbrandOrderIso_symm_apply]

end TauCeti.LocalFieldsRamification
