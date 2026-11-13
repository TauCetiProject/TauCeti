/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.FreeItems
public import TauCeti.GroupTheory.FreeGroup.GenEq.Kernel
import Mathlib.GroupTheory.FreeGroup.Center
import TauCeti.GroupTheory.GroupAlgGeom.SumVars

/-!
# Elimination processes and the kernel of a generalised equation

Let `Ω` be a generalised equation without boundary connections. An *elimination process*
(Kharlampovich–Myasnikov, §5.2, D4) removes eliminable bases (`TauCeti.GenEq.IsEliminable`), one
pair `μ, Δ(μ)` at a time, until no eliminable base is left; the result is a *kernel* of `Ω`
(`TauCeti.GenEq.IsKernelOf`). Every generalised equation has a kernel
(`TauCeti.GenEq.exists_isKernelOf`).

Each elimination makes one generator of the presented group free
(`TauCeti.GenEq.exists_bijective_gHom_systemGroup_removePair`). Hence, for an elimination process
of `n` steps from `Ω` to `K`, the group presented by `K*` is the free product of the group
presented by `Ω*` with a free group of rank `n`, `F[h]/ncl(K*) ≅ (F[h]/ncl(Ω*)) ∗ F(z₁, …, zₙ)`
(`TauCeti.GenEq.EliminatesTo.exists_bijective_systemGroup`); sending `z₁, …, zₙ` to `1` gives
back the homomorphism induced by the identity on the items. For coordinate groups this isomorphism
induces a surjection `F_{R(Ω)} ∗ F(z₁, …, zₙ) → F_{R(K)}`
(`TauCeti.GenEq.EliminatesTo.exists_surjective_coordGroup`), which need not be injective.

The source (Lemma 16) states `F_{R(Ω)} ≃ F_{R(Ker Ω)} ∗ F(Z)`, with the free factor on the side
of the kernel. For the kernel as the source defines it, and as it is defined here, by removing
bases only, this can fail on the presented groups once rule (b) is used: the generator that becomes
free need not be an item of the kernel. The proof of the source passes at each elimination to the
generalised equation `Ω′` in which the item of degree one (rule (a)) or the boundary (rule (b)) is
deleted (see `TauCeti.GenEq.IsEliminable`); this surgery is not formalised here. What its case
analysis proves for the kernel defined here is the form above, for the groups presented by the
systems. The source also asserts that the kernel does not depend on the elimination process; this
is not formalised here.

## Main definitions

* `TauCeti.GenEq.EliminatesTo`: `K` is obtained from `Ω` by `n` eliminations.
* `TauCeti.GenEq.IsKernelOf`: `K` is a kernel of `Ω`.

## Main results

* `TauCeti.GenEq.exists_isKernelOf`: every generalised equation has a kernel.
* `TauCeti.GenEq.EliminatesTo.exists_bijective_systemGroup`: the presented groups along an
  elimination process.
* `TauCeti.GenEq.EliminatesTo.exists_surjective_coordGroup`: the coordinate groups along an
  elimination process.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2, D4 and Lemma 16.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open scoped Finset commutatorElement

variable {A : Type*}

/-- `EliminatesTo Ω K n`: the generalised equation `K` is obtained from `Ω` by `n` successive
removals of eliminable bases. -/
inductive EliminatesTo : GenEq A → GenEq A → ℕ → Prop
  | refl (Ω : GenEq A) : EliminatesTo Ω Ω 0
  | step {Ω K : GenEq A} {n : ℕ} {μ : Fin Ω.numBases} (hμ : Ω.IsEliminable μ)
      (h : EliminatesTo (Ω.removePair μ) K n) : EliminatesTo Ω K (n + 1)

/-- Removing bases creates no boundary connection. -/
theorem EliminatesTo.connections_eq_empty {Ω K : GenEq A} {n : ℕ} (h : EliminatesTo Ω K n)
    (hc : Ω.connections = ∅) : K.connections = ∅ := by
  induction h with
  | refl => exact hc
  | step _ _ ih => exact ih (Finset.eq_empty_of_forall_notMem fun c hc' => by simp [hc] at hc')

/-- An elimination process keeps the items. -/
theorem EliminatesTo.numItems_eq {Ω K : GenEq A} {n : ℕ} (h : EliminatesTo Ω K n) :
    K.numItems = Ω.numItems := by
  induction h with
  | refl => rfl
  | step _ _ ih => exact ih

/-- `K` is a kernel of `Ω`: it is obtained from `Ω` by removing eliminable bases and has no
eliminable base. -/
def IsKernelOf (K Ω : GenEq A) : Prop :=
  (∃ n, EliminatesTo Ω K n) ∧ ∀ μ, ¬ K.IsEliminable μ

/-- The definition of a kernel. -/
theorem isKernelOf_iff {K Ω : GenEq A} :
    IsKernelOf K Ω ↔ (∃ n, EliminatesTo Ω K n) ∧ ∀ μ, ¬ K.IsEliminable μ :=
  Iff.rfl

/-- Every generalised equation has a kernel. -/
theorem exists_isKernelOf (Ω : GenEq A) : ∃ K, IsKernelOf K Ω := by
  induction hn : Ω.numBases using Nat.strong_induction_on generalizing Ω with
  | _ n ih =>
  by_cases h : ∃ μ, Ω.IsEliminable μ
  · obtain ⟨μ, hμ⟩ := h
    obtain ⟨K, ⟨m, hK⟩, hK'⟩ := ih _ (hn ▸ Ω.numBases_removeBases_lt (Ω.dual_mem_pair μ)
      (Finset.insert_nonempty _ _)) (Ω.removePair μ) rfl
    exact ⟨K, ⟨m + 1, .step hμ hK⟩, hK'⟩
  · exact ⟨Ω, ⟨0, .refl Ω⟩, not_exists.1 h⟩

/-- One more elimination: an isomorphism `G(Ω₁) ≅ G(Ω) ∗ ⟨z⟩` extends to
`G(Ω₁) ∗ F(n) ≅ G(Ω) ∗ F(n + 1)`, and sending the free generators to `1` commutes with it. -/
private theorem exists_bijective_succ {Ω : GenEq A} {μ : Fin Ω.numBases} (n : ℕ)
    {e₁ : GHom (SystemGroup.coeff (Ω.removePair μ).toSystem)
      ((inl : SystemGroup (FreeGroup A) Ω.toSystem →*
        GX (SystemGroup (FreeGroup A) Ω.toSystem) Unit).comp (SystemGroup.coeff Ω.toSystem))}
    (he₁ : Function.Bijective e₁) :
    ∃ E : GHom ((inl : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem →*
        GX (SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) (Fin n)).comp
          (SystemGroup.coeff (Ω.removePair μ).toSystem))
        ((inl : SystemGroup (FreeGroup A) Ω.toSystem →*
          GX (SystemGroup (FreeGroup A) Ω.toSystem) (Fin (n + 1))).comp
            (SystemGroup.coeff Ω.toSystem)),
      Function.Bijective E ∧ ∀ y, eval (MonoidHom.id _) (fun _ => 1) (E y) =
        eval (MonoidHom.id _) (fun _ => 1) (e₁ (eval (MonoidHom.id _) (fun _ => 1) y)) := by
  -- `G(Ω₁) ∗ F(n) ≅ (G(Ω) ∗ ⟨z⟩) ∗ F(n) ≅ G(Ω) ∗ F(n ⊕ 1) ≅ G(Ω) ∗ F(n + 1)`.
  let E : GX (SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) (Fin n) ≃*
      GX (SystemGroup (FreeGroup A) Ω.toSystem) (Fin (n + 1)) :=
    ((MulEquiv.coprodCongr (MulEquiv.ofBijective (e₁ : _ →* _) he₁) (.refl _)).trans
      (GX.sumEquiv _ (Fin n) Unit).symm).trans
        (GX.renameEquiv _ ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv n).symm))
  -- Sending the free generators to `1` after `E` is sending them to `1` before and after `e₁`.
  have hE : (eval (MonoidHom.id _) fun _ => (1 : SystemGroup (FreeGroup A) Ω.toSystem)).comp
      E.toMonoidHom = ((eval (MonoidHom.id _) fun _ => 1).comp e₁.toMonoidHom).comp
        (eval (MonoidHom.id _) fun _ => 1) :=
    GX.ext_hom (fun _ => by simp [E, Function.comp_def]) fun _ => by simp [E]
  refine ⟨GHom.ofMulEquiv E fun g => ?_, GHom.ofMulEquiv_bijective _ _, fun y => ?_⟩
  · simpa [E] using congrArg (fun x => GX.renameEquiv _ _ ((GX.sumEquiv _ (Fin n) Unit).symm
      (inl x))) (e₁.map_coeff g)
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, GHom.coe_ofMulEquiv] using DFunLike.congr_fun hE y

/-- **Elimination process on presented groups** (the form of Lemma 16 which holds). If `Ω` has
no boundary connections and `K` is obtained from `Ω` by `n` removals of eliminable bases, the
group presented by `K*` is the free product of the group presented by `Ω*` with a free group of
rank `n`; sending the free generators to `1` gives back the homomorphism induced by the identity on
the items (which `K` and `Ω` share). -/
theorem EliminatesTo.exists_bijective_systemGroup {Ω K : GenEq A} {n : ℕ} (h : EliminatesTo Ω K n)
    (hc : Ω.connections = ∅) :
    ∃ e : GHom (SystemGroup.coeff K.toSystem)
        ((inl : SystemGroup (FreeGroup A) Ω.toSystem →*
          GX (SystemGroup (FreeGroup A) Ω.toSystem) (Fin n)).comp (SystemGroup.coeff Ω.toSystem)),
      Function.Bijective e ∧ ∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (GX.renameEquiv (FreeGroup A) (finCongr h.numItems_eq.symm) w :
              SystemGroup (FreeGroup A) K.toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem) := by
  induction h with
  | refl Ω =>
    exact ⟨GHom.ofMulEquiv GX.equivOfIsEmpty.symm fun g => by simp,
      GHom.ofMulEquiv_bijective _ _, fun w => by simp⟩
  | @step Ω K n μ hμ hK ih =>
    obtain ⟨e, he, hew⟩ := ih ((EliminatesTo.step hμ (.refl _)).connections_eq_empty hc)
    obtain ⟨e₁, he₁, -, he₁w⟩ := exists_bijective_gHom_systemGroup_removePair hc hμ
    obtain ⟨E, hE, hEw⟩ := exists_bijective_succ n he₁
    refine ⟨E.comp e, ?_, fun w => ?_⟩
    · rw [GHom.coe_comp]
      exact hE.comp he
    · rw [GHom.coe_comp, Function.comp_apply, hEw, hew w, he₁w w]

/-- **Elimination process on coordinate groups.** If `Ω` has no boundary connections and `K` is
obtained from `Ω` by `n` removals of eliminable bases, an isomorphism `e` of the presented groups
`F[h]/ncl(K*) ≅ (F[h]/ncl(Ω*)) ∗ F(z₁, …, zₙ)` induces a surjection
`f : F_{R(Ω)} ∗ F(z₁, …, zₙ) → F_{R(K)}` of coordinate groups: `f` composed with the projections
of presented groups onto coordinate groups is the projection composed with `e⁻¹`. Here `e` is an
isomorphism of `exists_bijective_systemGroup`: sending the free generators to `1` after `e` gives
back the homomorphism induced by the identity on the items. -/
theorem EliminatesTo.exists_surjective_coordGroup {Ω K : GenEq A} {n : ℕ} (h : EliminatesTo Ω K n)
    (hc : Ω.connections = ∅) {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    ∃ (e : GHom (SystemGroup.coeff K.toSystem)
        ((inl : SystemGroup (FreeGroup A) Ω.toSystem →*
          GX (SystemGroup (FreeGroup A) Ω.toSystem) (Fin n)).comp (SystemGroup.coeff Ω.toSystem)))
      (f : GHom ((inl : CoordGroup ι Ω.toSystem →* GX (CoordGroup ι Ω.toSystem) (Fin n)).comp
        (CoordGroup.coeff ι Ω.toSystem)) (CoordGroup.coeff ι K.toSystem)),
      Function.Bijective e ∧ (∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (GX.renameEquiv (FreeGroup A) (finCongr h.numItems_eq.symm) w :
              SystemGroup (FreeGroup A) K.toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      Function.Surjective f ∧ ∀ q : SystemGroup (FreeGroup A) K.toSystem,
        f (Monoid.Coprod.map
            (SystemGroup.toCoordGroup ι Ω.toSystem :
              SystemGroup (FreeGroup A) Ω.toSystem →* CoordGroup ι Ω.toSystem) (.id _) (e q)) =
          SystemGroup.toCoordGroup ι K.toSystem q := by
  obtain ⟨e, he, hew⟩ := h.exists_bijective_systemGroup hc
  refine ⟨e, CoordGroup.freeProdMap ι (e.symmOfBijective he), he, hew,
    CoordGroup.freeProdMap_surjective fun q => ⟨e q, e.symmOfBijective_apply_apply he q⟩,
    fun q => ?_⟩
  rw [CoordGroup.freeProdMap_map_toCoordGroup, GHom.symmOfBijective_apply_apply]

/-! ### A kernel whose coordinate group with the free items is not a free product -/

/-- The generalised equation over `F(a, b)` with thirteen items, all bases of sign `+1`, no
boundary connections, the pairs of bases `[0, 2] ∼ [2, 4]`, `[4, 6] ∼ [6, 8]`, `[8, 10] ∼ [10, 12]`,
`[0, 1] ∼ [3, 4]`, `[0, 1] ∼ [8, 9]`, `[0, 1] ∼ [11, 12]`, `[4, 5] ∼ [7, 8]`, `[4, 5] ∼ [9, 10]`,
`[4, 5] ∼ [10, 11]`, the constant bases `h₁ = h₂ = a`, `h₅ = h₆ = b`, and the free item `h₁₂`. Its
equations amount to `[h₀, a] = [h₄, b] = [h₀, h₄] = 1`. -/
private abbrev kernelExample : GenEq (Fin 2) where
  numItems := 13
  numBases := 18
  left := ![0, 2, 4, 6, 8, 10, 0, 3, 0, 8, 0, 11, 4, 7, 4, 9, 4, 10]
  right := ![2, 4, 6, 8, 10, 12, 1, 4, 1, 9, 1, 12, 5, 8, 5, 10, 5, 11]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := {(1, (0, true)), (2, (0, true)), (5, (1, true)), (6, (1, true))}
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- No base of the example is eliminable, so the example is its own kernel. -/
example : IsKernelOf kernelExample kernelExample :=
  ⟨⟨0, .refl _⟩, by decide⟩

/-- The only free item of the example is `h₁₂`. -/
private theorem kernelExample_freeItems : kernelExample.freeItems = {12} := by
  ext k
  simp only [mem_freeItems (Ω := kernelExample), kernelExample.isFreeItem_iff,
    kernelExample.isConstantItem_iff, mem_baseItems kernelExample, Finset.mem_singleton]
  decide +revert

private theorem kernelExample_card : #kernelExample.freeItemsᶜ = 12 := by
  rw [kernelExample_freeItems, Finset.card_compl]
  rfl

/-- The remaining items `h₀, …, h₁₁` keep their numbers. -/
private theorem kernelExample_orderEmbOfFin (k : Fin #kernelExample.freeItemsᶜ) :
    kernelExample.freeItemsᶜ.orderEmbOfFin rfl k = (Fin.cast kernelExample_card k).castSucc := by
  have hmem : ∀ j : Fin 13, j ≠ Fin.last 12 → j ∈ kernelExample.freeItemsᶜ := by
    rw [kernelExample_freeItems]
    intro j hj
    simpa using hj
  refine congrFun (Finset.orderEmbOfFin_unique rfl
    (f := fun k => (Fin.cast kernelExample_card k).castSucc)
    (fun k => hmem _ (Fin.castSucc_ne_last _)) fun a b h => ?_).symm k
  rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def, Fin.val_cast, Fin.val_cast]
  exact h

/-- The basic equation of a base of the example holds at a point. -/
private theorem kernelExample_basicEquation {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) (μ : Fin 18) :
    FreeGroup.lift (Sum.elim v (MonoidHom.id (FreeGroup (Fin 2)) ∘ FreeGroup.of))
        (FreeGroup.mk (kernelExample.basicEquation μ).1) =
      FreeGroup.lift (Sum.elim v (MonoidHom.id (FreeGroup (Fin 2)) ∘ FreeGroup.of))
        (FreeGroup.mk (kernelExample.basicEquation μ).2) :=
  (mem_V_toSystem_iff _).1 hv _ (kernelExample.basicEquation_mem_equations μ)

/-- The coefficient equation of a constant base of the example holds at a point. -/
private theorem kernelExample_coeffEquation {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem)
    {b : Fin 13 × Fin 2 × Bool} (hb : b ∈ kernelExample.constBases) :
    FreeGroup.lift (Sum.elim v (MonoidHom.id (FreeGroup (Fin 2)) ∘ FreeGroup.of))
        (FreeGroup.mk (kernelExample.coeffEquation b).1) =
      FreeGroup.lift (Sum.elim v (MonoidHom.id (FreeGroup (Fin 2)) ∘ FreeGroup.of))
        (FreeGroup.mk (kernelExample.coeffEquation b).2) :=
  (mem_V_toSystem_iff _).1 hv _ (kernelExample.coeffEquation_mem_equations hb)

/-- `[h₀, a] = 1` at every point: `h₀ a = h₂ h₃`, `h₂ = a`, `h₃ = h₀`. -/
private theorem kernelExample_commute_zero {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    Commute (v 0) (FreeGroup.of 0) := by
  have h₀ := kernelExample_basicEquation hv 0
  have h₆ := kernelExample_basicEquation hv 6
  have c₁ := kernelExample_coeffEquation hv (b := (1, 0, true)) (by decide)
  have c₂ := kernelExample_coeffEquation hv (b := (2, 0, true)) (by decide)
  simp only [MonoidHom.coe_id, CompTriple.comp_eq, Fin.isValue, basicEquation_fst, Nat.reduceAdd,
    Matrix.cons_val_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.reduceMod, segment_true,
    List.finRange_succ, List.finRange_zero, List.map_nil, List.map_cons, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.reduceSucc, List.take_succ_cons, List.take_zero, List.drop_zero,
    FreeGroup.lift_mk, cond_eq_ite, ↓reduceIte, Sum.elim_inl, List.prod_cons, List.prod_nil,
    mul_one, basicEquation_snd, Matrix.cons_val_one, List.drop_succ_cons, Matrix.cons_val,
    Nat.one_mod, coeffEquation_fst, coeffEquation_snd, Sum.elim_inr] at h₀ h₆ c₁ c₂
  rw [Commute, SemiconjBy, ← c₁, h₀, c₁, ← c₂, h₆]

/-- `[h₄, b] = 1` at every point: `h₄ b = h₆ h₇`, `h₆ = b`, `h₇ = h₄`. -/
private theorem kernelExample_commute_four {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    Commute (v 4) (FreeGroup.of 1) := by
  have h₂ := kernelExample_basicEquation hv 2
  have h₁₂ := kernelExample_basicEquation hv 12
  have c₅ := kernelExample_coeffEquation hv (b := (5, 1, true)) (by decide)
  have c₆ := kernelExample_coeffEquation hv (b := (6, 1, true)) (by decide)
  simp only [MonoidHom.coe_id, CompTriple.comp_eq, Fin.isValue, basicEquation_fst, Nat.reduceAdd,
    Matrix.cons_val, Fin.coe_ofNat_eq_mod, Nat.reduceMod, segment_true, List.finRange_succ,
    List.finRange_zero, List.map_nil, List.map_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    FreeGroup.lift_mk, cond_eq_ite, ↓reduceIte, Sum.elim_inl, List.prod_cons, List.prod_nil,
    mul_one, basicEquation_snd, coeffEquation_fst, coeffEquation_snd, Sum.elim_inr] at h₂ h₁₂ c₅ c₆
  rw [Commute, SemiconjBy, ← c₅, h₂, c₅, ← c₆, h₁₂]

/-- `[h₀, h₄] = 1` at every point: `h₈ h₉ = h₁₀ h₁₁` with `h₈ = h₁₁ = h₀` and `h₉ = h₁₀ = h₄`. -/
private theorem kernelExample_commute_zero_four {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    Commute (v 0) (v 4) := by
  have h₄ := kernelExample_basicEquation hv 4
  have h₈ := kernelExample_basicEquation hv 8
  have h₁₀ := kernelExample_basicEquation hv 10
  have h₁₄ := kernelExample_basicEquation hv 14
  have h₁₆ := kernelExample_basicEquation hv 16
  simp only [MonoidHom.coe_id, CompTriple.comp_eq, Fin.isValue, basicEquation_fst, Nat.reduceAdd,
    Matrix.cons_val, Fin.coe_ofNat_eq_mod, Nat.reduceMod, segment_true, List.finRange_succ,
    List.finRange_zero, List.map_nil, List.map_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    FreeGroup.lift_mk, cond_eq_ite, ↓reduceIte, Sum.elim_inl, List.prod_cons, List.prod_nil,
    mul_one, basicEquation_snd, Nat.zero_mod, Nat.one_mod] at h₄ h₈ h₁₀ h₁₄ h₁₆
  calc v 0 * v 4 = v 8 * v 9 := by rw [h₈, h₁₄]
    _ = v 10 * v 11 := h₄
    _ = v 4 * v 0 := by rw [h₁₆, h₁₀]

/-- Every point of the example in `F(a, b)` has `h₀ = 1` or `h₄ = 1`: commutation is transitive on
the nontrivial elements of a free group, and `a`, `b` do not commute. -/
private theorem kernelExample_eq_one_or_eq_one {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    v 0 = 1 ∨ v 4 = 1 := by
  by_contra! hne
  exact absurd (IsFreeGroup.commute_trans (IsFreeGroup.commute_trans
    (kernelExample_commute_zero hv).symm (kernelExample_commute_zero_four hv) hne.1)
      (kernelExample_commute_four hv) hne.2).eq (by decide)

/-- The point `(a, a, a, a, 1, b, b, 1, a, 1, 1, a, 1)` of the example. -/
private theorem kernelExample_mem_V₁ :
    ![.of 0, .of 0, .of 0, .of 0, 1, .of 1, .of 1, 1, .of 0, 1, 1, .of 0, 1] ∈
      V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem :=
  (mem_V_toSystem_iff _).2 ((forall_mem_equations _).2
    ⟨by simp only [basicEquation_fst, basicEquation_snd, segment_true]; decide,
      by simp only [coeffEquation_fst, coeffEquation_snd]; decide,
      fun _ hc => absurd hc (Finset.notMem_empty _)⟩)

/-- The point `(1, a, a, 1, b, b, b, b, 1, b, b, 1, 1)` of the example. -/
private theorem kernelExample_mem_V₂ :
    ![1, .of 0, .of 0, 1, .of 1, .of 1, .of 1, .of 1, 1, .of 1, .of 1, 1, 1] ∈
      V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem :=
  (mem_V_toSystem_iff _).2 ((forall_mem_equations _).2
    ⟨by simp only [basicEquation_fst, basicEquation_snd, segment_true]; decide,
      by simp only [coeffEquation_fst, coeffEquation_snd]; decide,
      fun _ hc => absurd hc (Finset.notMem_empty _)⟩)

/-- The remaining items `h₀` and `h₄` of the example, as items of `Ω̄`. -/
private abbrev kernelExampleItem (i : Fin 12) : Fin #kernelExample.freeItemsᶜ :=
  Fin.cast kernelExample_card.symm i

private theorem kernelExample_orderEmbOfFin_item (i : Fin 12) :
    kernelExample.freeItemsᶜ.orderEmbOfFin rfl (kernelExampleItem i) = i.castSucc := by
  rw [kernelExample_orderEmbOfFin]
  rfl

/-- The commutator `[h₀, z h₄ z⁻¹]` in `F_{R(Ω̄)} ∗ ⟨z⟩`, `z` the free item of the example. -/
private abbrev kernelExampleCommutator :
    GX kernelExample.deleteFreeItems.coordGroup (Fin #kernelExample.freeItems) :=
  let x : GX kernelExample.deleteFreeItems.coordGroup (Fin #kernelExample.freeItems) :=
    inl ((inr (FreeGroup.of (kernelExampleItem 0)) :
      GX (FreeGroup (Fin 2)) (Fin #kernelExample.freeItemsᶜ)) : CoordGroup _ _)
  let y : GX kernelExample.deleteFreeItems.coordGroup (Fin #kernelExample.freeItems) :=
    inl ((inr (FreeGroup.of (kernelExampleItem 4)) :
      GX (FreeGroup (Fin 2)) (Fin #kernelExample.freeItemsᶜ)) : CoordGroup _ _)
  let z : GX kernelExample.deleteFreeItems.coordGroup (Fin #kernelExample.freeItems) :=
    inr (FreeGroup.of ⟨0, by simp [kernelExample_freeItems]⟩)
  ⁅x, z * y * z⁻¹⁆

/-- The commutator `[h₀, z h₄ z⁻¹]` vanishes at every point: every point of `Ω̄` extends to a point
of `Ω`, at which `h₀ = 1` or `h₄ = 1`. -/
private theorem freeVarsHom_kernelExampleCommutator :
    CoordGroup.freeVarsHom (.id _) _ _ kernelExampleCommutator = 1 := by
  refine CoordGroup.freeVarsHom_eq_one_iff.2 fun v hv u => ?_
  let e := finSumEquivOfFinset (s := kernelExample.freeItemsᶜ) rfl
    (congrArg Finset.card (compl_compl _))
  have hext (k : Fin #kernelExample.freeItemsᶜ) :
      (Sum.elim v 1 ∘ e.symm) (kernelExample.freeItemsᶜ.orderEmbOfFin rfl k) = v k := by
    simp [e, (Equiv.symm_apply_eq _).2 (finSumEquivOfFinset_inl _ _ k).symm]
  have hv' : Sum.elim v 1 ∘ e.symm ∈ V (.id _) kernelExample.toSystem :=
    mem_V_toSystem_iff_deleteFreeItems.2 (by simpa only [hext] using hv)
  obtain h | h := kernelExample_eq_one_or_eq_one hv'
  · rw [← Fin.castSucc_zero, ← kernelExample_orderEmbOfFin_item, hext] at h
    simp [h]
  · rw [show (4 : Fin 13) = (4 : Fin 12).castSucc from rfl, ← kernelExample_orderEmbOfFin_item,
      hext] at h
    simp [h]

/-- The commutator `[h₀, z h₄ z⁻¹]` is not trivial: the points `(a, …, 1, …)` and `(1, …, b, …)`
give a homomorphism to the permutations of four points under which `h₀` and `h₄` go to disjoint
transpositions, and `z` can be sent to a transposition meeting both. -/
private theorem kernelExampleCommutator_ne_one : kernelExampleCommutator ≠ 1 := by
  have hp₁ := mem_V_toSystem_iff_deleteFreeItems.1 kernelExample_mem_V₁
  have hp₂ := mem_V_toSystem_iff_deleteFreeItems.1 kernelExample_mem_V₂
  let ρ : FreeGroup (Fin 2) →* Equiv.Perm (Fin 2) := FreeGroup.lift fun _ => Equiv.swap 0 1
  let κ : kernelExample.deleteFreeItems.coordGroup →* Equiv.Perm (Fin 2 ⊕ Fin 2) :=
    (Equiv.Perm.sumCongrHom (Fin 2) (Fin 2)).comp
      ((ρ.comp (CoordGroup.evalGHom _ hp₁).toMonoidHom).prod
        (ρ.comp (CoordGroup.evalGHom _ hp₂).toMonoidHom))
  let t : Equiv.Perm (Fin 2 ⊕ Fin 2) := Equiv.swap (Sum.inl 0) (Sum.inr 0)
  have hne : ⁅(Equiv.swap (Sum.inl 0) (Sum.inl 1) : Equiv.Perm (Fin 2 ⊕ Fin 2)),
      t * Equiv.swap (Sum.inr 0) (Sum.inr 1) * t⁆ ≠ 1 := by decide
  have h₀ : kernelExample.freeItemsᶜ.orderEmbOfFin rfl (kernelExampleItem 0) = 0 :=
    kernelExample_orderEmbOfFin_item 0
  have h₄ : kernelExample.freeItemsᶜ.orderEmbOfFin rfl (kernelExampleItem 4) = 4 :=
    kernelExample_orderEmbOfFin_item 4
  refine fun h => hne ?_
  simpa [κ, ρ, t, h₀, h₄] using congrArg (eval κ fun _ => t) h

/-- For the example `Ω`, its own kernel, with the free item `z = h₁₂`, the surjection
`F_{R(Ω̄)} ∗ ⟨z⟩ → F_{R(Ω)}` (the coordinate group of `Ω` being that of `Ω̄*` with the free variable
`z`, by `toSystem_eq_image_addFreeVars`) is not injective: `[h₀, z h₄ z⁻¹]` vanishes at every point,
since every point has `h₀ = 1` or `h₄ = 1`, but it is not trivial in the free product, since the
points `(a, 1, …)` and `(1, b, …)` show that neither `h₀` nor `h₄` is trivial in `F_{R(Ω̄)}`. -/
example : ¬ Function.Injective (CoordGroup.freeVarsHom (.id (FreeGroup (Fin 2)))
    (Fin #kernelExample.freeItems) kernelExample.deleteFreeItems.toSystem) := fun h =>
  kernelExampleCommutator_ne_one (h (freeVarsHom_kernelExampleCommutator.trans (map_one _).symm))

end GenEq

end TauCeti
