/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
public import TauCeti.GroupTheory.FreeGroup.GenEq.Surgery
import Mathlib.Data.Fin.VecNotation
import TauCeti.GroupTheory.GroupAlgGeom.RelatorElimination

/-!
# Elimination of a base of a generalised equation

Let `Ω` be a generalised equation without boundary connections. A variable base `μ` is
*eliminable* (Kharlampovich–Myasnikov, §5.2, D4) when `Δ(μ) ≠ μ` and

* (a) `μ` contains an item `hₖ` of degree one, that is an item belonging to no other base; or
* (b) an end-point `i` of `μ`, different from the first and the last boundary, touches no other
  base, variable or constant.

Eliminating `μ` removes the pair `μ, Δ(μ)` (`TauCeti.GenEq.removePair`). On the groups presented
by the systems `Ω*`, the basic equation of an eliminable base is, after a change of variables, a
member of a free basis of `F(A)[h]` over `F(A)` in which the other equations do not involve it: in
case (a) it can be solved for `hₖ`, and in case (b), after replacing the two items `h_{i-1}, hᵢ`
next to `i` by the item of `μ` among them and the product `h_{i-1} hᵢ`, it can be solved for the
item of `μ`. Hence removing an eliminable base makes one generator free:
`F[h]/ncl(Ω₁*) ≅ (F[h]/ncl(Ω*)) ∗ ⟨z⟩` for `Ω₁ = Ω.removePair μ`, and sending `z` to `1` gives back
the map induced by the identity on the items
(`TauCeti.GenEq.exists_bijective_systemGroup_removePair`).

The source states the effect of an elimination process as `F_{R(Ω)} ≃ F_{R(Ker Ω)} ∗ F(Z)`, with
the free factor on the side of the kernel. For one elimination by rule (b) this fails: the
generator which becomes free is not an item of the result. The form proved here, with the free
factor on the side of the result, is what the source's case analysis establishes. It concerns
the groups presented by the systems, not their coordinate groups.

For a parametric generalised equation the source eliminates active bases only; that restriction
is not part of `TauCeti.GenEq.IsEliminable` and is to be imposed where it is used.

We require `Δ(μ) ≠ μ` of an eliminable base: the basic equation of a base which is its own dual
is trivial, and removing it frees no generator.

## Main definitions

* `TauCeti.GenEq.IsEliminable`: a variable base is eliminable.

## Main results

* `TauCeti.GenEq.exists_bijective_systemGroup_removePair`: removing an eliminable base from a
  generalised equation without boundary connections adds a free factor `⟨z⟩` to the presented
  group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2, D4.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open scoped Finset

variable {A : Type*} (Ω : GenEq A)

/-- A variable base `μ` is eliminable (D4): it is not its own dual, and either (a) it contains
an item of degree one, or (b) one of its end-points, different from the first and the last
boundary, is an end-point of no other variable base and of no constant base. -/
def IsEliminable (μ : Fin Ω.numBases) : Prop :=
  Ω.dual μ ≠ μ ∧ ((∃ k ∈ Ω.baseItems μ, Ω.degree k = 1) ∨
    ∃ i : Fin (Ω.numItems + 1), Ω.Touches i μ ∧ i ≠ 0 ∧ i ≠ Fin.last Ω.numItems ∧
      (∀ ν, ν ≠ μ → ¬ Ω.Touches i ν) ∧
      ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i)

/-- The definition of an eliminable base. -/
theorem isEliminable_iff {μ : Fin Ω.numBases} : Ω.IsEliminable μ ↔
    Ω.dual μ ≠ μ ∧ ((∃ k ∈ Ω.baseItems μ, Ω.degree k = 1) ∨
      ∃ i : Fin (Ω.numItems + 1), Ω.Touches i μ ∧ i ≠ 0 ∧ i ≠ Fin.last Ω.numItems ∧
        (∀ ν, ν ≠ μ → ¬ Ω.Touches i ν) ∧
        ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i) :=
  Iff.rfl

/-! ### Separating an item of an eliminable base -/

/-- Let `χ` send the words avoiding `h_p` and `h_{p+1}` and the word `h_p h_{p+1}` to words
avoiding `hₖ`. Then it sends the word of every base which does not have `p + 1` as an end-point
to a word avoiding `hₖ`: such a base contains both `h_p` and `h_{p+1}`, adjacent, or neither. -/
private theorem mem_avoiding_of_not_touches {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))}
    {k : Fin Ω.numItems} {p : ℕ} (hp : p + 1 < Ω.numItems)
    (hfix : ∀ c, c ∈ GX.avoiding (⟨p, by omega⟩ : Fin Ω.numItems) →
      c ∈ GX.avoiding (⟨p + 1, hp⟩ : Fin Ω.numItems) → χ c ∈ GX.avoiding k)
    (hpair : χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) ∈ GX.avoiding k)
    {ν : Fin Ω.numBases} (hl : (Ω.left ν : ℕ) ≠ p + 1) (hr : (Ω.right ν : ℕ) ≠ p + 1) :
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left ν) (Ω.right ν) true))) ∈
      GX.avoiding k := by
  have hlr : (Ω.left ν : ℕ) < Ω.right ν := Ω.left_lt_right ν
  have hrn : (Ω.right ν : ℕ) ≤ Ω.numItems := Nat.lt_succ_iff.1 (Ω.right ν).isLt
  by_cases hout : (Ω.right ν : ℕ) ≤ p ∨ p + 1 < Ω.left ν
  · exact hfix _ (Ω.toGX_segment_mem_avoiding _ (by simp only; omega))
      (Ω.toGX_segment_mem_avoiding _ (by simp only; omega))
  · rw [Ω.toGX_segment_eq_mul_pair (p := p) (by omega) (by omega) hrn, map_mul, map_mul]
    refine mul_mem (mul_mem (hfix _ ?_ ?_) hpair) (hfix _ ?_ ?_) <;>
      exact Ω.toGX_segment_mem_avoiding _ (by simp only; omega)

/-- After the coefficient-fixing automorphism `χ` of `F(A)[h]`, the word `h[α(μ), β(μ)]` is
unchanged, while the item `hₖ` of `μ` occurs neither in the image of the word of another base nor
in the image of a constant item. -/
private structure Separates (μ : Fin Ω.numBases) (χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems)))
    (k : Fin Ω.numItems) : Prop where
  map_inl (g : FreeGroup A) : χ (inl g) = inl g
  mem_baseItems : k ∈ Ω.baseItems μ
  map_segment :
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true))) =
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true))
  mem_avoiding_segment (ν : Fin Ω.numBases) : ν ≠ μ →
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left ν) (Ω.right ν) true))) ∈
      GX.avoiding k
  mem_avoiding_const (b : Fin Ω.numItems × (A × Bool)) : b ∈ Ω.constBases →
    χ (inr (FreeGroup.of b.1)) ∈ GX.avoiding k

variable {Ω}

/-- Case (a): an item of degree one of `μ` occurs in no other base. -/
private theorem separates_of_degree_eq_one {μ : Fin Ω.numBases} {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) (hdeg : Ω.degree k = 1) : Ω.Separates μ 1 k where
  map_inl _ := rfl
  mem_baseItems := hk
  map_segment := rfl
  mem_avoiding_segment ν hν := by
    have h₁ : #{ν | k ∈ Ω.baseItems ν} ≤ 1 := by rw [degree_def] at hdeg; omega
    have hkν : k ∉ Ω.baseItems ν := fun hkν =>
      hν (Finset.card_le_one.1 h₁ ν (by simpa using hkν) μ (by simpa using hk))
    rw [mem_baseItems] at hkν
    exact Ω.toGX_segment_mem_avoiding _ (by omega)
  mem_avoiding_const b hb := by
    have hpos : 0 < #{ν | k ∈ Ω.baseItems ν} := Finset.card_pos.2 ⟨μ, by simpa using hk⟩
    have h₀ : #{b ∈ Ω.constBases | b.1 = k} = 0 := by rw [degree_def] at hdeg; omega
    exact GX.inr_of_mem_avoiding (Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h₀) hb)

/-- Case (b), after the choice of the shear: the item `hₖ` of `μ` next to the boundary `p + 1` and
the other item `h_{k'}` next to it, and an automorphism `χ` fixing the words avoiding `h_{k'}` and
sending `h_p h_{p+1}` to `h_{k'}`. -/
private theorem separates_of_shear {μ : Fin Ω.numBases} {p : ℕ} (hp : p + 1 < Ω.numItems)
    {k k' : Fin Ω.numItems} (hkk' : (k : ℕ) = p ∧ (k' : ℕ) = p + 1 ∨ (k : ℕ) = p + 1 ∧ (k' : ℕ) = p)
    (hk : k ∈ Ω.baseItems μ) (hk' : (k' : ℕ) < Ω.left μ ∨ Ω.right μ ≤ (k' : ℕ))
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} (hχ : ∀ c ∈ GX.avoiding k', χ c = c)
    (hpair : χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) =
      inr (FreeGroup.of k'))
    (hν : ∀ ν, ν ≠ μ → (Ω.left ν : ℕ) ≠ p + 1 ∧ (Ω.right ν : ℕ) ≠ p + 1)
    (hb : ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ p ∧ (b.1 : ℕ) ≠ p + 1) : Ω.Separates μ χ k where
  map_inl g := hχ _ (GX.inl_mem_avoiding _ g)
  mem_baseItems := hk
  map_segment := hχ _ (Ω.toGX_segment_mem_avoiding _ hk')
  mem_avoiding_segment ν hν' := by
    refine Ω.mem_avoiding_of_not_touches hp (fun c hc hc' => ?_) ?_ (hν ν hν').1 (hν ν hν').2
    · obtain ⟨hk, hk'⟩ | ⟨hk, hk'⟩ := hkk'
      · rw [hχ c (by rwa [(Fin.ext hk' : k' = ⟨p + 1, hp⟩)]), (Fin.ext hk : k = ⟨p, by omega⟩)]
        exact hc
      · rw [hχ c (by rwa [(Fin.ext hk' : k' = ⟨p, by omega⟩)]), (Fin.ext hk : k = ⟨p + 1, hp⟩)]
        exact hc'
    · rw [hpair]
      exact GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega)
  mem_avoiding_const b hb' := by
    obtain ⟨h₁, h₂⟩ := hb b hb'
    rw [hχ _ (GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega))]
    exact GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega)

/-- Case (b): an end-point `i ≠ 0, ρ` of `μ` touches no other base. After the shear sending
`h_{i-1} hᵢ` to the item next to `i` outside `μ`, the item next to `i` in `μ` is separated. -/
private theorem exists_separates_of_touches {μ : Fin Ω.numBases} {i : Fin (Ω.numItems + 1)}
    (hi : Ω.Touches i μ) (h0 : i ≠ 0) (hlast : i ≠ Fin.last Ω.numItems)
    (hν : ∀ ν, ν ≠ μ → ¬ Ω.Touches i ν)
    (hb : ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i) :
    ∃ χ k, Ω.Separates μ χ k := by
  obtain ⟨p, hp⟩ : ∃ p, (i : ℕ) = p + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fin.val_ne_iff.2 h0)
  have hpn : p + 1 < Ω.numItems := hp ▸ Fin.val_lt_last hlast
  have hν' (ν : Fin Ω.numBases) (h : ν ≠ μ) :
      (Ω.left ν : ℕ) ≠ p + 1 ∧ (Ω.right ν : ℕ) ≠ p + 1 := by
    have := hν ν h
    rw [touches_iff, not_or, Fin.ext_iff, Fin.ext_iff] at this
    omega
  have hb' (b) (h : b ∈ Ω.constBases) : (b.1 : ℕ) ≠ p ∧ (b.1 : ℕ) ≠ p + 1 := by
    have := hb b h
    omega
  have hlr : (Ω.left μ : ℕ) < Ω.right μ := Ω.left_lt_right μ
  have hab : (⟨p, by omega⟩ : Fin Ω.numItems) ≠ ⟨p + 1, hpn⟩ := by simp [Fin.ext_iff]
  rw [touches_iff, Fin.ext_iff, Fin.ext_iff, hp] at hi
  rcases hi with hl | hr
  · -- `i = α(μ)`: the item `hᵢ` lies in `μ`; the shear is `h_{i-1} ↦ h_{i-1} hᵢ⁻¹`.
    refine ⟨GX.transvection _ 1 (inr (FreeGroup.of ⟨p + 1, hpn⟩))⁻¹ (one_mem _)
      (inv_mem (GX.inr_of_mem_avoiding hab.symm)), ⟨p + 1, hpn⟩,
      Ω.separates_of_shear hpn (Or.inr ⟨rfl, rfl⟩) (by rw [mem_baseItems]; simp only; omega)
        (Or.inl (by simp only; omega)) (fun c hc => GX.transvection_apply_of_mem_avoiding _ _ hc)
        ?_ hν' hb'⟩
    simp [GX.transvection_inr_of_of_ne _ _ hab.symm]
  · -- `i = β(μ)`: the item `h_{i-1}` lies in `μ`; the shear is `hᵢ ↦ h_{i-1}⁻¹ hᵢ`.
    refine ⟨GX.transvection _ (inr (FreeGroup.of ⟨p, by omega⟩))⁻¹ 1
      (inv_mem (GX.inr_of_mem_avoiding hab)) (one_mem _), ⟨p, by omega⟩,
      Ω.separates_of_shear hpn (Or.inl ⟨rfl, rfl⟩) (by rw [mem_baseItems]; simp only; omega)
        (Or.inr (by simp only; omega)) (fun c hc => GX.transvection_apply_of_mem_avoiding _ _ hc)
        ?_ hν' hb'⟩
    simp [GX.transvection_inr_of_of_ne _ _ hab]

/-- The word of a base other than `μ`, with either sign, avoids the separated item. -/
private theorem Separates.mem_avoiding_segment' {μ : Fin Ω.numBases}
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} {k : Fin Ω.numItems} (h : Ω.Separates μ χ k)
    {ν : Fin Ω.numBases} (hν : ν ≠ μ) (s : Bool) :
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left ν) (Ω.right ν) s))) ∈
      GX.avoiding k := by
  cases s
  · rw [toGX_segment_false, map_inv]
    exact inv_mem (h.mem_avoiding_segment ν hν)
  · exact h.mem_avoiding_segment ν hν

/-- After `χ`, the separated item occurs in no equation of `Ω` with `μ, Δ(μ)` removed. -/
private theorem Separates.mem_avoiding_toSystem {μ : Fin Ω.numBases}
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} {k : Fin Ω.numItems} (h : Ω.Separates μ χ k)
    (hc : Ω.connections = ∅) {t : GX (FreeGroup A) (Fin Ω.numItems)}
    (ht : t ∈ (Ω.removePair μ).toSystem) : χ t ∈ GX.avoiding k := by
  have key : ∀ e ∈ (Ω.removePair μ).equations,
      χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk e.1)) ∈ GX.avoiding k ∧
        χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk e.2)) ∈ GX.avoiding k := by
    refine ((Ω.removePair μ).forall_mem_equations).2
      ⟨fun ν' => ?_, fun b hb => ?_, fun c hc' => ?_⟩
    · rw [basicEquation_removeBases, basicEquation_fst, basicEquation_snd]
      have hν := Finset.mem_compl.1 (Finset.orderEmbOfFin_mem ({μ, Ω.dual μ} : Finset _)ᶜ rfl ν')
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hν
      exact ⟨h.mem_avoiding_segment' hν.1 _, h.mem_avoiding_segment'
        (fun h' => hν.2 ((Ω.dual_involutive _).symm.trans (congrArg Ω.dual h'))) _⟩
    · obtain ⟨j, a, s⟩ := b
      refine ⟨by simpa [EqIneqSystem.toGX_eq_lift, FreeGroup.lift_mk] using
        h.mem_avoiding_const _ hb, ?_⟩
      cases s <;> simp [EqIneqSystem.toGX_eq_lift, FreeGroup.lift_mk, h.map_inl]
    · exact absurd ((mem_connections_removeBases _).1 hc') (by simp [hc])
  obtain ⟨e, he, rfl⟩ := (mem_toSystem_iff _).1 ht
  rw [map_mul, map_inv, map_mul, map_inv]
  exact mul_mem (key e he).1 (inv_mem (key e he).2)

/-- **Elimination of a base on presented groups.** If `Ω` has no boundary connections and `μ` is
eliminable, the group presented by the system of `Ω` with the pair `μ, Δ(μ)` removed is the free
product of the group presented by `Ω*` with an infinite cyclic group `⟨z⟩`; sending `z` to `1`
gives back the homomorphism induced by the identity on the items. -/
theorem exists_bijective_systemGroup_removePair (hc : Ω.connections = ∅) {μ : Fin Ω.numBases}
    (hμ : Ω.IsEliminable μ) :
    ∃ e : GHom (SystemGroup.coeff (Ω.removePair μ).toSystem)
        ((inl : SystemGroup (FreeGroup A) Ω.toSystem →*
          GX (SystemGroup (FreeGroup A) Ω.toSystem) Unit).comp (SystemGroup.coeff Ω.toSystem)),
      Function.Bijective e ∧ ∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem) := by
  -- After a change of variables `χ`, an item `hₖ` of `μ` occurs in no other equation, and the
  -- basic equation of `μ` (or of `Δ(μ)`, according to the sign of `μ`) is `u hₖ v` with `hₖ`
  -- occurring neither in `u` nor in `v`.
  obtain ⟨hd, hμ⟩ := hμ
  obtain ⟨χ, k, h⟩ : ∃ χ k, Ω.Separates μ χ k := by
    obtain ⟨k, hk, hdeg⟩ | ⟨i, hi, h0, hlast, hν, hb⟩ := hμ
    exacts [⟨1, k, separates_of_degree_eq_one hk hdeg⟩,
      exists_separates_of_touches hi h0 hlast hν hb]
  have hk := Ω.mem_baseItems.1 h.mem_baseItems
  have hL := Ω.toGX_segment_eq_mul hk.1 hk.2 (Nat.lt_succ_iff.1 (Ω.right μ).isLt)
  simp only [Fin.eta] at hL
  have hP := Ω.toGX_segment_mem_avoiding (i := Ω.left μ) (j := k) true (Or.inr le_rfl)
  have hQ := Ω.toGX_segment_mem_avoiding (i := k + 1) (j := Ω.right μ) true
    (Or.inl (Nat.lt_succ_self _))
  have hR := h.mem_avoiding_segment' hd (Ω.sign (Ω.dual μ))
  have hS (t) (ht : t ∈ (Ω.removePair μ).toSystem) := h.mem_avoiding_toSystem hc ht
  have hc' : ∀ c ∈ Ω.connections, c.2.1 ≠ μ := by simp [hc]
  cases hs : Ω.sign μ
  · -- `ε(μ) = -1`: the equation of `Δ(μ)` is `R (P hₖ Q)` with `R` the word of `Δ(μ)`.
    obtain ⟨e, he, hw, -⟩ := SystemGroup.exists_bijective_of_normalClosure_eq_insert χ h.map_inl
      (mul_mem hR hP) hQ (by
        rw [basicEquation_fst, basicEquation_snd, Ω.dual_involutive μ, hs, map_mul, map_inv,
          toGX_segment_false, inv_inv, map_mul χ, h.map_segment, hL]
        simp only [mul_assoc]) hS
      (normalClosure_toSystem_eq_insert_removePair hc' (Or.inr rfl))
    exact ⟨e, he, hw⟩
  · obtain ⟨e, he, hw, -⟩ := SystemGroup.exists_bijective_of_normalClosure_eq_insert χ h.map_inl
      hP (mul_mem hQ (inv_mem hR)) (by
        rw [basicEquation_fst, basicEquation_snd, hs, map_mul, map_inv, map_mul χ, map_inv χ,
          h.map_segment, hL]
        simp only [mul_assoc]) hS
      (normalClosure_toSystem_eq_insert_removePair hc' (Or.inl rfl))
    exact ⟨e, he, hw⟩

/-! ### Examples -/

/-- The generalised equation with the single basic equation `h₀h₁ = h₂`. -/
private abbrev productExample : GenEq (Fin 2) where
  numItems := 3
  numBases := 2
  left := ![0, 2]
  right := ![2, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- In `h₀h₁ = h₂` the base `[0, 2]` contains the item `h₀` of degree one, so it is eliminable
by rule (a). -/
example : productExample.IsEliminable 0 := by
  simp only [isEliminable_iff, degree_def, mem_baseItems productExample]
  decide

/-- The generalised equation with the basic equations `h₀h₁ = h₂h₃` (twice) and
`h₁h₂h₃ = h₀h₁h₂`, given by the pairs `[0, 2] ∼ [2, 4]`, `[0, 2] ∼ [2, 4]` and `[1, 4] ∼ [0, 3]`.
-/
private abbrev ruleBExample : GenEq (Fin 2) where
  numItems := 4
  numBases := 6
  left := ![0, 2, 0, 2, 1, 0]
  right := ![2, 4, 2, 4, 4, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0, 3, 2, 5, 4]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- The base `[1, 4]` has no item of degree one, but its end-point `1` touches no other base, so
it is eliminable by rule (b). -/
example : ruleBExample.IsEliminable 4 := by
  simp only [isEliminable_iff, degree_def, mem_baseItems ruleBExample, touches_iff]
  decide

/-- The base `[0, 2]` is not eliminable: each of its items lies in at least three bases, and its
end-point `2` touches three other bases. -/
example : ¬ ruleBExample.IsEliminable 0 := by
  simp only [isEliminable_iff, degree_def, mem_baseItems ruleBExample, touches_iff]
  decide

end GenEq

end TauCeti
