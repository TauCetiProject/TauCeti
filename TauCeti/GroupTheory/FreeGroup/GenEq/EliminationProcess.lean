/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.FreeItems
public import TauCeti.GroupTheory.FreeGroup.GenEq.Kernel
import TauCeti.GroupTheory.FreeGroup.CSA
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
open scoped Finset

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
  refine ⟨GHom.ofMulEquiv E fun g => ?_, GHom.ofMulEquiv_bijective _ _, fun y => ?_⟩
  · simp [E]
  -- Sending the free generators to `1` after `E` is sending them to `1` before and after `e₁`.
  · have hy : MulEquiv.coprodCongr (MulEquiv.ofBijective (e₁ : _ →* _) he₁) (.refl _) y =
        Monoid.Coprod.map e₁.toMonoidHom (FreeGroup.map id) y :=
      DFunLike.congr_fun (congrArg (Monoid.Coprod.map e₁.toMonoidHom)
        (FreeGroup.ext_hom (MonoidHom.id _) (FreeGroup.map id) fun _ => rfl)) y
    rw [GHom.coe_ofMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, GX.eval_renameEquiv,
      GX.eval_sumEquiv_symm, hy, eval_map]
    simp only [hom_eval]
    congr 2
    funext
    simp

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
  -- The finset also occurs in the type of `k`, so it is generalised rather than rewritten.
  have key (s : Finset (Fin 13)) (hs : s = {Fin.last 12}) (k : Fin #sᶜ) (hk : #sᶜ = 12) :
      sᶜ.orderEmbOfFin rfl k = (Fin.cast hk k).castSucc := by
    subst hs
    rw [Finset.orderEmbOfFin_compl_singleton_apply, Fin.succAbove_last]
  exact key _ kernelExample_freeItems k kernelExample_card

/-- The basic equation of a base of the example holds at a point. -/
private theorem kernelExample_basicEquation {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) (μ : Fin 18) :
    FreeGroup.lift (Sum.elim v FreeGroup.of) (FreeGroup.mk (kernelExample.basicEquation μ).1) =
      FreeGroup.lift (Sum.elim v FreeGroup.of) (FreeGroup.mk (kernelExample.basicEquation μ).2) :=
  (mem_V_toSystem_iff _).1 hv _ (kernelExample.basicEquation_mem_equations μ)

/-- The coefficient equation `hₖ = a` of a constant base of the example holds at a point. -/
private theorem kernelExample_coeffEquation {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) {k : Fin 13}
    {a : Fin 2} (hb : (k, a, true) ∈ kernelExample.constBases) :
    v k = FreeGroup.of a := by
  simpa using (mem_V_toSystem_iff _).1 hv _ (kernelExample.coeffEquation_mem_equations hb)

/-- The basic equations of the example used below, evaluated at a point: those of the bases
`[0, 2]`, `[4, 6]`, `[8, 10]`, `[0, 1]` (three times) and `[4, 5]` (three times). -/
private theorem kernelExample_basicEquations {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    v 0 * v 1 = v 2 * v 3 ∧ v 4 * v 5 = v 6 * v 7 ∧ v 8 * v 9 = v 10 * v 11 ∧
      v 0 = v 3 ∧ v 0 = v 8 ∧ v 0 = v 11 ∧ v 4 = v 7 ∧ v 4 = v 9 ∧ v 4 = v 10 := by
  have h₀ := kernelExample_basicEquation hv 0
  have h₂ := kernelExample_basicEquation hv 2
  have h₄ := kernelExample_basicEquation hv 4
  have h₆ := kernelExample_basicEquation hv 6
  have h₈ := kernelExample_basicEquation hv 8
  have h₁₀ := kernelExample_basicEquation hv 10
  have h₁₂ := kernelExample_basicEquation hv 12
  have h₁₄ := kernelExample_basicEquation hv 14
  have h₁₆ := kernelExample_basicEquation hv 16
  simp (disch := decide) only [basicEquation_fst, basicEquation_snd, Matrix.cons_val,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, lift_mk_segment_add_one kernelExample,
    lift_mk_segment_add_two kernelExample, Nat.reduceAdd, Fin.reduceFinMk,
    Sum.elim_inl] at h₀ h₂ h₄ h₆ h₈ h₁₀ h₁₂ h₁₄ h₁₆
  exact ⟨h₀, h₂, h₄, h₆, h₈, h₁₀, h₁₂, h₁₄, h₁₆⟩

/-- `[h₀, a] = 1` at every point: `h₀ a = h₂ h₃`, `h₂ = a`, `h₃ = h₀`. -/
private theorem kernelExample_commute_zero {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    Commute (v 0) (FreeGroup.of 0) := by
  obtain ⟨h₀, -, -, h₆, -⟩ := kernelExample_basicEquations hv
  have c₁ := kernelExample_coeffEquation (k := 1) (a := 0) hv (by decide)
  have c₂ := kernelExample_coeffEquation (k := 2) (a := 0) hv (by decide)
  rw [Commute, SemiconjBy, ← c₁, h₀, c₁, ← c₂, h₆]

/-- `[h₄, b] = 1` at every point: `h₄ b = h₆ h₇`, `h₆ = b`, `h₇ = h₄`. -/
private theorem kernelExample_commute_four {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    Commute (v 4) (FreeGroup.of 1) := by
  obtain ⟨-, h₂, -, -, -, -, h₁₂, -⟩ := kernelExample_basicEquations hv
  have c₅ := kernelExample_coeffEquation (k := 5) (a := 1) hv (by decide)
  have c₆ := kernelExample_coeffEquation (k := 6) (a := 1) hv (by decide)
  rw [Commute, SemiconjBy, ← c₅, h₂, c₅, ← c₆, h₁₂]

/-- `[h₀, h₄] = 1` at every point: `h₈ h₉ = h₁₀ h₁₁` with `h₈ = h₁₁ = h₀` and `h₉ = h₁₀ = h₄`. -/
private theorem kernelExample_commute_zero_four {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    Commute (v 0) (v 4) := by
  obtain ⟨-, -, h₄, -, h₈, h₁₀, -, h₁₄, h₁₆⟩ := kernelExample_basicEquations hv
  calc v 0 * v 4 = v 8 * v 9 := by rw [h₈, h₁₄]
    _ = v 10 * v 11 := h₄
    _ = v 4 * v 0 := by rw [h₁₆, h₁₀]

/-- Every point of the example in `F(a, b)` has `h₀ = 1` or `h₄ = 1`: commutation is transitive on
the nontrivial elements of a free group, and `a`, `b` do not commute. -/
private theorem kernelExample_eq_one_or_eq_one {v : Fin 13 → FreeGroup (Fin 2)}
    (hv : v ∈ V (MonoidHom.id (FreeGroup (Fin 2))) kernelExample.toSystem) :
    v 0 = 1 ∨ v 4 = 1 :=
  IsFreeGroup.isCommTransitive.eq_one_or_eq_one_of_not_commute
    (fun hab => absurd hab.eq (by decide)) (kernelExample_commute_zero hv).symm
    (kernelExample_commute_zero_four hv) (kernelExample_commute_four hv)

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

/-- The remaining items `h₀` and `h₄` of the example, as items of `\overline{Ω}`. -/
private abbrev kernelExampleItem (i : Fin 12) : Fin #kernelExample.freeItemsᶜ :=
  Fin.cast kernelExample_card.symm i

private theorem kernelExample_orderEmbOfFin_zero :
    kernelExample.freeItemsᶜ.orderEmbOfFin rfl (kernelExampleItem 0) = 0 := by
  rw [kernelExample_orderEmbOfFin]
  decide

private theorem kernelExample_orderEmbOfFin_four :
    kernelExample.freeItemsᶜ.orderEmbOfFin rfl (kernelExampleItem 4) = 4 := by
  rw [kernelExample_orderEmbOfFin]
  decide

/-- Every point of `\overline{Ω}` has `h₀ = 1` or `h₄ = 1`: it extends to a point of `Ω`. -/
private theorem kernelExample_deleteFreeItems_eq_one_or_eq_one
    {v : Fin kernelExample.deleteFreeItems.numItems → FreeGroup (Fin 2)}
    (hv : v ∈ V (.id _) kernelExample.deleteFreeItems.toSystem) :
    v (kernelExampleItem 0) = 1 ∨ v (kernelExampleItem 4) = 1 := by
  let e := finSumEquivOfFinset (s := kernelExample.freeItemsᶜ) rfl
    (congrArg Finset.card (compl_compl _))
  have hext (k : Fin #kernelExample.freeItemsᶜ) :
      (Sum.elim v 1 ∘ e.symm) (kernelExample.freeItemsᶜ.orderEmbOfFin rfl k) = v k := by
    simp [e, (Equiv.symm_apply_eq _).2 (finSumEquivOfFinset_inl _ _ k).symm]
  have hv' : Sum.elim v 1 ∘ e.symm ∈ V (.id _) kernelExample.toSystem :=
    mem_V_toSystem_iff_deleteFreeItems.2 (by simpa only [hext] using hv)
  rw [← hext, ← hext, kernelExample_orderEmbOfFin_zero, kernelExample_orderEmbOfFin_four]
  exact kernelExample_eq_one_or_eq_one hv'

/-- For the example `Ω`, its own kernel, with the free item `z = h₁₂`, the surjection
`F_{R(\overline{Ω})} ∗ ⟨z⟩ → F_{R(Ω)}` (the coordinate group of `Ω` being that of `\overline{Ω}*`
with the free variable `z`, by `toSystem_eq_image_addFreeVars`) is not injective: every point has
`h₀ = 1` or `h₄ = 1`, but the points `(a, 1, …)` and `(1, b, …)` show that neither `h₀` nor `h₄`
is trivial in `F_{R(\overline{Ω})}`. -/
example : ¬ Function.Injective (CoordGroup.freeVarsHom (.id (FreeGroup (Fin 2)))
    (Fin #kernelExample.freeItems) kernelExample.deleteFreeItems.toSystem) := by
  have : Nonempty (Fin #kernelExample.freeItems) := ⟨⟨0, by simp [kernelExample_freeItems]⟩⟩
  have hp₁ := mem_V_toSystem_iff_deleteFreeItems.1 kernelExample_mem_V₁
  have hp₂ := mem_V_toSystem_iff_deleteFreeItems.1 kernelExample_mem_V₂
  -- Passed to `simp` as hypotheses: as global lemmas they do not fire on the evaluated points.
  have h₀ := kernelExample_orderEmbOfFin_zero
  have h₄ := kernelExample_orderEmbOfFin_four
  exact CoordGroup.not_injective_freeVarsHom_of_forall_eq_one_or_eq_one
    (CoordGroup.genericPoint_ne_one_iff (x := kernelExampleItem 0).2 ⟨_, hp₁, by simp [h₀]⟩)
    (CoordGroup.genericPoint_ne_one_iff (x := kernelExampleItem 4).2 ⟨_, hp₂, by simp [h₄]⟩)
    fun _ hv => by simpa using kernelExample_deleteFreeItems_eq_one_or_eq_one hv

end GenEq

end TauCeti
