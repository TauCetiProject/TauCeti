/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Elementary facts about permutations

This file records general-purpose facts about permutations: a map intertwining two permutations
intertwines their integer powers (`Function.Semiconj.perm_zpow_right`), a transposition
preserves the complement of a set containing neither of its swapped points, an identity between
transpositions,
a permutation transporting two points outside a fixed set to another such pair,
the values of the three-cycle written as a product of two transpositions sharing a point,
a characterization of permutations with a unique fixed point, functions constant on a permutation
orbit, the orbit relation of an involution, a positive-power representative of a relation inside a
periodic orbit, a function whose difference `z ↦ c (σ⁻¹ z) - c z` joins points in the same orbit
(`Equiv.Perm.SameCycle.exists_comp_symm_sub_eq`, `Equiv.Perm.exists_comp_symm_sub_eq_sum`), a
transposition forming one cycle on a `Fin 2` fibre over `Fin 1`, a
permutation transported along an injection, the combination of two
permutations transported along injections with disjoint ranges, the fact that a permutation
is a single cycle on each of its own orbits, the transport of its cycles along an equivalence of
types, and the factorization of an invariant function
through a map on whose fibres the permutation is a single cycle, and a correction by a power of
a cycle for a permutation commuting with it. It also identifies functions invariant under a
permutation with functions on its cycle quotient (`TauCeti.invariantColouringEquiv`). Finally,
right multiplication by `a` is a single cycle on the whole group exactly when `a` generates it
(`Equiv.isCycleOn_mulRight_univ_iff`). Alternating a signed sum over permutations a second
time, along a sign-preserving map of permutation groups, multiplies it by the number of
permutations alternated over (`TauCeti.sum_sign_smul_sum_sign_smul_eq_card_nsmul`), and a signed
sum over the permutations of `Fin (n + 1)` evaluated on a tuple `Fin.cons x w` expands along the
slot that receives `x` (`TauCeti.sum_sign_smul_cons_comp_eq_sum_insertNth`).
-/

public section

namespace Function.Semiconj

variable {α γ : Type*} {σ : Equiv.Perm α} {τ : Equiv.Perm γ} {g : α → γ}

/-- A map intertwining two permutations also intertwines all of their integer powers. This
extends `Function.Semiconj.iterate_right` to negative exponents. -/
theorem perm_zpow_right (hg : Function.Semiconj g σ τ) (k : ℤ) :
    Function.Semiconj g ⇑(σ ^ k) ⇑(τ ^ k) := by
  intro z
  have hinv : Function.Semiconj g (σ⁻¹ : Equiv.Perm α) (τ⁻¹ : Equiv.Perm γ) :=
    Function.Semiconj.inverses_right hg σ.right_inv τ.left_inv
  cases k with
  | ofNat m =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hg m z)
  | negSucc m =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hinv (m + 1) z)

end Function.Semiconj

namespace Equiv.Perm.SameCycle

variable {α : Type*} {β : Sort*} {σ : Equiv.Perm α} {x y : α} {f : α → β}

variable {γ : Type*} {τ : Equiv.Perm γ} {g : α → γ}

/-- A function invariant under one application of a permutation is constant on every orbit of
that permutation. -/
theorem apply_eq_of_apply_eq (hσ : σ.SameCycle x y) (hf : ∀ z, f (σ z) = f z) : f x = f y := by
  obtain ⟨k, rfl⟩ := hσ
  have hmap := Function.Semiconj.perm_zpow_right (τ := 1) (g := fun z => PLift.up (f z))
    (fun z => congrArg PLift.up (hf z)) k x
  exact congrArg PLift.down (by simpa only [one_zpow, Equiv.Perm.one_apply] using hmap.symm)

/-- A map intertwining two permutations carries orbits of the first permutation into orbits of
the second. -/
theorem map (hσ : σ.SameCycle x y) (hg : ∀ z, g (σ z) = τ (g z)) :
    τ.SameCycle (g x) (g y) := by
  obtain ⟨k, rfl⟩ := hσ
  exact ⟨k, (Function.Semiconj.perm_zpow_right hg k x).symm⟩

/-- If a periodic point `x` of `σ` shares its orbit with `y`, some positive natural power of `σ`
carries `x` to `y`. -/
theorem exists_pos_pow_eq_of_mem_periodicPts (h : σ.SameCycle x y)
    (hx : x ∈ Function.periodicPts (σ : α → α)) : ∃ j : ℕ, 0 < j ∧ (σ ^ j) x = y := by
  obtain ⟨k, hk⟩ := h
  have hperiod : MulAction.period σ x = Function.minimalPeriod (σ : α → α) x :=
    MulAction.period_eq_minimalPeriod
  have hpos : 0 < MulAction.period σ x :=
    hperiod ▸ Function.minimalPeriod_pos_of_mem_periodicPts hx
  have hnonneg : 0 ≤ k % (MulAction.period σ x : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hpos.ne')
  refine ⟨(k % (MulAction.period σ x : ℤ)).toNat + MulAction.period σ x, by omega, ?_⟩
  have hred : σ ^ (k % (MulAction.period σ x : ℤ) + (MulAction.period σ x : ℤ)) • x = y := by
    rw [MulAction.zpow_add_period_smul, MulAction.zpow_mod_period_smul]
    exact hk
  rw [Equiv.Perm.smul_def] at hred
  rw [← zpow_natCast, Nat.cast_add, Int.toNat_of_nonneg hnonneg]
  exact hred

/-- Two points `x`, `y` in the same orbit of `σ` are joined along the orbit: some `c : α → M`
has difference `z ↦ c (σ⁻¹ z) - c z` equal to `Pi.single y a - Pi.single x a`. -/
theorem exists_comp_symm_sub_eq [DecidableEq α] {M : Type*} [AddCommGroup M]
    (h : σ.SameCycle x y) (a : M) :
    ∃ c : α → M, (fun z => c (σ.symm z) - c z) = Pi.single y a - Pi.single x a := by
  -- Adding `s • [w]` to `c` adds `s • ([σ w] - [w])` to its difference.
  have step (c : α → M) (w : α) (s : ℤ) :
      (fun z => (c + s • Pi.single w a : α → M) (σ.symm z) - (c + s • Pi.single w a : α → M) z) =
        (fun z => c (σ.symm z) - c z) + s • (Pi.single (σ w) a - Pi.single w a) := by
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Equiv.symm_apply_eq]
    split_ifs <;> simp only [smul_sub] <;> abel
  obtain ⟨k, rfl⟩ := h
  induction k using Int.induction_on with
  | zero => exact ⟨0, funext fun z => by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (1 : ℤ) • Pi.single ((σ ^ (k : ℤ)) x) a, ?_⟩
    rw [step, hc, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm (1 : ℤ)]
    abel
  | pred k ih =>
    obtain ⟨c, hc⟩ := ih
    have h_exp : (1 + (-k - 1) : ℤ) = -k := by omega
    refine ⟨c + (-1 : ℤ) • Pi.single ((σ ^ (-k - 1 : ℤ)) x) a, ?_⟩
    rw [step, hc, ← Equiv.Perm.mul_apply, ← zpow_one_add, h_exp]
    abel

end Equiv.Perm.SameCycle

namespace TauCeti

/-- The transposition of `Fin 2` is one cycle on every fibre of a map to `Fin 1`. -/
theorem isCycleOn_swap_fin_two_fiber (f : Fin 2 → Fin 1) (i : Fin 1) :
    (Equiv.swap (0 : Fin 2) 1).IsCycleOn {p | f p = i} := by
  convert Equiv.Perm.isCycleOn_swap (a := (0 : Fin 2)) (b := 1) (by decide) using 1
  ext p
  fin_cases p <;> simp [Subsingleton.elim (f _) i]

end TauCeti

namespace Equiv.Perm

variable {α : Type*} (σ : Equiv.Perm α)

/-- A permutation is a single cycle on each of its own orbits. -/
theorem isCycleOn_setOf_sameCycle (x : α) : σ.IsCycleOn {y | σ.SameCycle x y} :=
  ⟨σ.bijOn fun _ => sameCycle_apply_right, fun _ hy _ hz => hy.symm.trans hz⟩

/-- A permutation is a single cycle on each fibre of the quotient map onto its orbits. This is the
form in which the cyclic order around a vertex of a ribbon graph is read off a permutation. -/
theorem isCycleOn_preimage_quotientMk (b : Quotient (SameCycle.setoid σ)) :
    σ.IsCycleOn (Quotient.mk (SameCycle.setoid σ) ⁻¹' {b}) := by
  induction b using Quotient.inductionOn with
  | _ x =>
    have hfibre : Quotient.mk (SameCycle.setoid σ) ⁻¹' {Quotient.mk _ x} =
        {y | σ.SameCycle x y} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Set.mem_ofPred_eq]
      exact sameCycle_comm
    rw [hfibre]
    exact σ.isCycleOn_setOf_sameCycle x

/-- A function invariant under a permutation that is a single cycle on each fibre of `g` factors
through `g`. -/
theorem factorsThrough_of_forall_isCycleOn {ι β : Type*} {g : α → ι}
    (hσ : ∀ i, σ.IsCycleOn {x | g x = i}) {f : α → β} (hf : ∀ x, f (σ x) = f x) :
    f.FactorsThrough g :=
  fun _ b hab => ((hσ (g b)).2 hab rfl).apply_eq_of_apply_eq hf

/-- Finitely many pairs `u i`, `v i`, each in a single orbit of `σ`, are joined along the
orbits with weights `a i`: some `c : α → M` has difference `z ↦ c (σ⁻¹ z) - c z` equal to
`∑ i, Pi.single (v i) (a i) - ∑ i, Pi.single (u i) (a i)`. -/
theorem exists_comp_symm_sub_eq_sum [DecidableEq α] {ι M : Type*} [Fintype ι] [AddCommGroup M]
    {σ : Perm α} {u v : ι → α} (h : ∀ i, σ.SameCycle (u i) (v i)) (a : ι → M) :
    ∃ c : α → M, (fun z => c (σ.symm z) - c z) =
      ∑ i, Pi.single (v i) (a i) - ∑ i, Pi.single (u i) (a i) := by
  choose c hc using fun i => (h i).exists_comp_symm_sub_eq (a i)
  refine ⟨∑ i, c i, funext fun z => ?_⟩
  simp only [Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => congrFun (hc i) z

/-- A permutation commuting with a cycle can be corrected by a power of that cycle to fix its
support pointwise, without changing it outside the support. -/
theorem IsCycle.exists_mul_zpow_inv_apply_eq_of_commute [Fintype α] [DecidableEq α]
    {g t : Perm α} (hgc : g.IsCycle) (htg : Commute t g) :
    ∃ j : ℤ, (∀ z ∈ g.support, (t * (g ^ j)⁻¹) z = z) ∧
      (∀ z ∉ g.support, (t * (g ^ j)⁻¹) z = t z) := by
  obtain ⟨hts, j, hj⟩ := hgc.commute_iff.1 htg
  refine ⟨j, ?_, ?_⟩
  · intro z hz
    have hw : (g ^ j)⁻¹ z ∈ g.support := by rwa [← zpow_neg, zpow_apply_mem_support]
    rw [Perm.mul_apply, ← ofSubtype_subtypePerm_of_mem hts hw, ← hj, ← Perm.mul_apply,
      mul_inv_cancel, Perm.one_apply]
  · intro z hz
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq.2 (zpow_apply_eq_self_of_apply_eq_self
      (notMem_support.1 hz) j).symm]

/-- Transporting a permutation along an equivalence transports its cycles. -/
@[simp]
theorem sameCycle_permCongr {β : Type*} (e : α ≃ β) {x y : α} :
    (e.permCongr σ).SameCycle (e x) (e y) ↔ σ.SameCycle x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map fun z ↦ by simp⟩
  simpa using h.map (g := e.symm) fun z ↦ by simp

/-- The cycles of a permutation transported along an equivalence are the transported cycles:
two points lie in the same cycle of `e.permCongr σ` exactly when their preimages under `e` lie in
the same cycle of `σ`. -/
theorem sameCycle_permCongr_iff {β : Type*} (e : α ≃ β) {x y : β} :
    (e.permCongr σ).SameCycle x y ↔ σ.SameCycle (e.symm x) (e.symm y) := by
  rw [← sameCycle_permCongr σ e, e.apply_symm_apply, e.apply_symm_apply]

/-- Transporting a permutation along an equivalence transports its cycles on a set: the analogue of
`Equiv.Perm.IsCycleOn.conj` for an equivalence between two types. -/
theorem IsCycleOn.permCongr {σ : Perm α} {β : Type*} (e : α ≃ β) {s : Set α}
    (h : σ.IsCycleOn s) : (e.permCongr σ).IsCycleOn (e '' s) := by
  refine ⟨⟨?_, (e.permCongr σ).injective.injOn, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨σ x, h.1.mapsTo hx, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := h.1.surjOn hx
    exact ⟨e y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (sameCycle_permCongr σ e).2 (h.2 hx hy)

end Equiv.Perm

namespace Equiv

/-- Right multiplication by `a` is a single cycle on the whole group exactly when `a` generates
the group. -/
@[to_additive /-- Right addition of `a` is a single cycle on the whole group exactly when `a`
generates the group. -/]
theorem isCycleOn_mulRight_univ_iff {G : Type*} [Group G] {a : G} :
    (Equiv.mulRight a).IsCycleOn _root_.Set.univ ↔ Subgroup.zpowers a = ⊤ := by
  simp only [Subgroup.eq_top_iff', Subgroup.mem_zpowers_iff]
  refine ⟨fun h y => ?_, fun h => ⟨(Equiv.mulRight a).bijective.bijOn_univ, fun x _ y _ => ?_⟩⟩
  · obtain ⟨k, hk⟩ := h.2 (Set.mem_univ 1) (Set.mem_univ y)
    exact ⟨k, by simpa using hk⟩
  · obtain ⟨k, hk⟩ := h (x⁻¹ * y)
    exact ⟨k, by simp [hk]⟩

end Equiv

namespace TauCeti

open Equiv Equiv.Perm

variable {α σ : Type*}

/-- Colourings fixed by a permutation are exactly the colourings of its cycles. -/
def invariantColouringEquiv (π : Perm α) :
    (Quotient (SameCycle.setoid π) → σ) ≃ {f : α → σ // f ∘ π = f} where
  toFun g := ⟨fun a => g (Quotient.mk _ a), funext fun a =>
    congrArg g (Quotient.sound (sameCycle_apply_left.mpr (SameCycle.refl π a)))⟩
  invFun f := Quotient.lift f.1 fun _ _ h =>
    SameCycle.apply_eq_of_apply_eq h (congrFun f.2)
  left_inv _ := funext fun c => Quotient.inductionOn c fun _ => rfl
  right_inv _ := rfl

/-- The colouring corresponding to a map on cycles evaluates at the cycle containing the point. -/
@[simp]
theorem invariantColouringEquiv_apply_coe (π : Perm α)
    (g : Quotient (SameCycle.setoid π) → σ) (a : α) :
    (invariantColouringEquiv π g : α → σ) a = g (Quotient.mk _ a) :=
  (rfl)

/-- The map on cycles corresponding to an invariant colouring evaluates at a cycle by evaluating
the colouring at any point in that cycle. -/
@[simp]
theorem invariantColouringEquiv_symm_apply (π : Perm α)
    (f : {f : α → σ // f ∘ π = f}) (a : α) :
    (invariantColouringEquiv π).symm f (Quotient.mk _ a) = f.1 a :=
  congrFun (congrArg Subtype.val ((invariantColouringEquiv π).apply_symm_apply f)) a

/-- Precomposing a function with a permutation preserves the cardinality of each fiber. -/
theorem card_filter_comp_perm {ι : Type*} [Fintype α] [DecidableEq ι]
    (f : α → ι) (g : Perm α) (i : ι) :
    (Finset.univ.filter fun a => f (g a) = i).card =
      (Finset.univ.filter fun a => f a = i).card :=
  Finset.card_equiv g fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A transposition of two points outside `s` maps the complement of `s` to itself. -/
theorem swap_apply_notMem {α : Type*} [DecidableEq α] {s : Finset α} {a b z : α}
    (ha : a ∉ s) (hb : b ∉ s) (hz : z ∉ s) : Equiv.swap a b z ∉ s := by
  rw [Equiv.swap_apply_def]; split_ifs <;> assumption

/-- Any ordered pair of distinct points outside `s` can be carried to another such pair by a
permutation fixing `s` pointwise. -/
theorem exists_pair_perm_fixed {α : Type*} {s : Set α}
    {i j i' j' : α} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hi : i ∉ s) (hj : j ∉ s) (hi' : i' ∉ s) (hj' : j' ∉ s) :
    ∃ perm : Equiv.Perm α, (∀ a ∈ s, perm a = a) ∧ perm i = i' ∧ perm j = j' := by
  classical
  let τ := Equiv.swap i i'
  let υ := Equiv.swap (τ j) j'
  have hτs (a : α) (ha : a ∈ s) : τ a = a :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ ha)) (fun h => hi' (h ▸ ha))
  have hτj : τ j ∉ s := by
    by_cases hji' : j = i'
    · simpa [τ, hji'] using hi
    · simpa [τ, Equiv.swap_apply_of_ne_of_ne hij.symm hji'] using hj
  have hτji' : τ j ≠ i' := by
    intro h
    exact hij (τ.injective ((Equiv.swap_apply_left i i').trans h.symm))
  refine ⟨τ.trans υ, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Equiv.trans_apply]
    rw [hτs a ha]
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hτj (h ▸ ha)) (fun h => hj' (h ▸ ha))
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hτji'.symm hi'j'
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

/-- Two points lie in the same orbit of an involution exactly when they are equal or one is the
image of the other. -/
theorem sameCycle_toPerm_iff {α : Type*} (f : α → α) (hf : Function.Involutive f) (a b : α) :
    (hf.toPerm f).SameCycle a b ↔ a = b ∨ a = f b := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.symm
    rcases Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self
      (f := hf.toPerm f) (x := b) (hf b) i with h | h
    · exact Or.inl (hi.symm.trans h)
    · exact Or.inr (hi.symm.trans h)
  · rintro (rfl | h)
    · exact Equiv.Perm.SameCycle.rfl
    · refine ⟨1, ?_⟩
      have : f a = b := by
        calc
          f a = f (f b) := congrArg f h
          _ = b := hf b
      simpa using this

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation moves all but one point exactly when it has a unique fixed point. -/
theorem card_support_add_one_eq_card_iff_existsUnique_fixedPoint (σ : Equiv.Perm α) :
    σ.support.card + 1 = Fintype.card α ↔ ∃! x : α, σ x = x := by
  have hfixed : (∃! x : α, x ∈ σ.supportᶜ) ↔ ∃! x : α, σ x = x := by
    simp only [Finset.mem_compl, Equiv.Perm.notMem_support]
  rw [← hfixed, ← Finset.card_eq_one_iff_existsUnique, Finset.card_compl]
  omega

/-- Whenever `a` and `c` are both distinct from `b`, the transpositions `(a b)` and `(b c)`
satisfy the braid relation. The two points `a` and `c` need not be distinct: for `a = c` both
sides are `(a b)`. -/
theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hcb : c ≠ b) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  rcases eq_or_ne a c with rfl | hac
  · rw [Equiv.swap_comm b a]
  · calc Equiv.swap a b * Equiv.swap b c * Equiv.swap a b
        = Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
          rw [Equiv.swap_comm a b, Equiv.swap_comm b c]
      _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hcb (Ne.symm hac)
      _ = Equiv.swap c a := Equiv.swap_comm a c
      _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
          (Equiv.swap_mul_swap_mul_swap hab hac).symm

/-- The product `Equiv.swap a b * Equiv.swap b c` of two transpositions sharing the point `b`
carries `a` to `b`. Together with `TauCeti.swap_mul_swap_apply_middle` and
`TauCeti.swap_mul_swap_apply_right` this evaluates that product, which for three distinct points
is the three-cycle `a ↦ b ↦ c ↦ a`, at each of the three points it moves. -/
@[simp]
theorem swap_mul_swap_apply_left {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hca : c ≠ a) : (Equiv.swap a b * Equiv.swap b c) a = b := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hca.symm, Equiv.swap_apply_left]

/-- The product `Equiv.swap a b * Equiv.swap b c` of two transpositions sharing the point `b`
carries `b` to `c`, the point the second transposition moves it to. -/
@[simp]
theorem swap_mul_swap_apply_middle {α : Type*} [DecidableEq α] {a b c : α} (hca : c ≠ a)
    (hcb : c ≠ b) : (Equiv.swap a b * Equiv.swap b c) b = c := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb]

/-- The product `Equiv.swap a b * Equiv.swap b c` of two transpositions sharing the point `b`
carries `c` to `a`, through the shared point `b`; no distinctness is needed for this value. -/
@[simp]
theorem swap_mul_swap_apply_right {α : Type*} [DecidableEq α] (a b c : α) :
    (Equiv.swap a b * Equiv.swap b c) c = a := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]

/-- **A permutation along an injection extends to a permutation of the ambient type.** Given an
injection `e : α → γ`, every permutation `σ` of `α` is realized along `e` by some
`ρ : Equiv.Perm γ`. This is `Equiv.Perm.viaEmbedding` stated in terms of the underlying function
of the injection, which is the form a consumer reindexing along `e` needs. -/
theorem exists_perm_apply_eq {α γ : Type*} {e : α → γ} (he : Function.Injective e)
    (σ : Equiv.Perm α) : ∃ ρ : Equiv.Perm γ, ∀ a, ρ (e a) = e (σ a) :=
  ⟨σ.viaEmbedding ⟨e, he⟩, fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a⟩

/-- **Two permutations along disjoint injections extend to one permutation of the ambient type.**
Given injections `e : α → γ` and `f : β → γ` with disjoint ranges, every pair of permutations
`σ` of `α` and `τ` of `β` is realized by a single `ρ : Equiv.Perm γ` which acts as `σ` along `e`
and as `τ` along `f`. -/
theorem exists_perm_apply_eq_of_disjoint_range {α β γ : Type*} {e : α → γ} {f : β → γ}
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    ∃ ρ : Equiv.Perm γ, (∀ a, ρ (e a) = e (σ a)) ∧ ∀ b, ρ (f b) = f (τ b) := by
  -- `Function.Embedding.coeFn_mk` is what carries a statement about the bundled embedding
  -- `⟨e, he⟩` over to the function `e` it is built from.
  have hrange_e : Set.range (⟨e, he⟩ : α ↪ γ) = Set.range e := by
    rw [Function.Embedding.coeFn_mk]
  have hrange_f : Set.range (⟨f, hf⟩ : β ↪ γ) = Set.range f := by
    rw [Function.Embedding.coeFn_mk]
  have hone : ∀ a, σ.viaEmbedding ⟨e, he⟩ (e a) = e (σ a) :=
    fun a => Equiv.Perm.viaEmbedding_apply (ι := ⟨e, he⟩) σ a
  have htwo : ∀ b, τ.viaEmbedding ⟨f, hf⟩ (f b) = f (τ b) :=
    fun b => Equiv.Perm.viaEmbedding_apply (ι := ⟨f, hf⟩) τ b
  refine ⟨σ.viaEmbedding ⟨e, he⟩ * τ.viaEmbedding ⟨f, hf⟩, fun a => ?_, fun b => ?_⟩
  · have hmem : e a ∉ Set.range (⟨f, hf⟩ : β ↪ γ) :=
      hrange_f ▸ Set.disjoint_left.mp hd ⟨a, rfl⟩
    rw [Equiv.Perm.mul_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨f, hf⟩) _ _ hmem, hone]
  · have hmem : f (τ b) ∉ Set.range (⟨e, he⟩ : α ↪ γ) :=
      hrange_e ▸ Set.disjoint_right.mp hd ⟨τ b, rfl⟩
    rw [Equiv.Perm.mul_apply, htwo,
      Equiv.Perm.viaEmbedding_apply_of_notMem (ι := ⟨e, he⟩) _ _ hmem]

/-- Alternating a signed sum over the permutations of `α` a second time, along any
sign-preserving map `ext` from the permutations of `β`, only multiplies it by the number of
permutations of `β`. With `ext` the
extension of permutations of a block of indices by the identity, this is the statement that the
alternatization of a partially alternatized multilinear map is a multiple of the alternatization. -/
theorem sum_sign_smul_sum_sign_smul_eq_card_nsmul {β M : Type*} [Fintype β] [DecidableEq β]
    [AddCommGroup M] (ext : Perm β → Perm α) (hext : ∀ τ, sign (ext τ) = sign τ)
    (T : Perm α → M) :
    ∑ σ : Perm α, sign σ • ∑ τ : Perm β, sign τ • T (σ * ext τ) =
      Fintype.card (Perm β) • ∑ σ : Perm α, sign σ • T σ := by
  rw [← Finset.card_univ, ← Finset.sum_const]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight (ext τ)) _ _ fun σ => ?_
  rw [Equiv.coe_mulRight, sign_mul, hext, mul_smul, smul_comm]

/-- Expansion of a signed sum over the permutations of `Fin (n + 1)` along the slot that receives
the first entry: rearranging `Fin.cons x w` by all permutations is the same as inserting `x` at
each position `j`, with sign `(-1) ^ j`, into all rearrangements of `w`. Applied to the summand of
an alternatization, this expands the alternatization along its first argument, in the manner of
the Laplace expansion of a determinant along a column. -/
theorem sum_sign_smul_cons_comp_eq_sum_insertNth {α M : Type*} [AddCommGroup M] {n : ℕ}
    (g : (Fin (n + 1) → α) → M) (x : α) (w : Fin n → α) :
    ∑ σ : Perm (Fin (n + 1)), sign σ • g (Fin.cons x w ∘ σ) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ τ : Perm (Fin n), sign τ • g (j.insertNth x (w ∘ τ)) := by
  cases n with
  | zero => simp [Fin.insertNth_zero']
  | succ n =>
  -- Reindex by Mathlib's `decomposeFin'`: `(decomposeFin'Symm j τ⁻¹)⁻¹` sends `j` to `0` and
  -- `j.succAbove m` to `(τ m).succ`, so it rearranges `Fin.cons x w` into
  -- `j.insertNth x (w ∘ τ)`, and its sign is `(-1) ^ j * sign τ`.
  symm
  simp_rw [Finset.smul_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.prodCongr (Equiv.refl _) (Equiv.inv _)).trans
    (decomposeFin'.symm.trans (Equiv.inv _))) _ _ fun ⟨j, τ⟩ => ?_
  have hcomp : Fin.cons x w ∘ ⇑((decomposeFin'Symm j τ⁻¹)⁻¹) = j.insertNth x (w ∘ τ) := by
    rw [Fin.eq_insertNth_iff]
    refine ⟨by simp, funext fun m => ?_⟩
    have : (decomposeFin'Symm j τ⁻¹)⁻¹ (j.succAbove m) = (τ m).succ :=
      Perm.inv_eq_iff_eq.mpr (by simp)
    simp only [Fin.removeNth, Function.comp_apply, this, Fin.cons_succ]
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq,
    Equiv.inv_apply, decomposeFin'_symm]
  rw [hcomp, Perm.sign_inv, sign_decomposeFin'Symm, Perm.sign_inv, mul_smul]
  simp [Units.smul_def]

end TauCeti
