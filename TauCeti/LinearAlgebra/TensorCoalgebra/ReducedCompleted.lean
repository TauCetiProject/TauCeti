/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Completed

/-!
# Completed reduced tensor coalgebras

The length completion of reduced tensor words is the product of the positive tensor powers.
Its reduced coproduct has a `(p,q)` coordinate for each pair of positive lengths, obtained by
cutting the component of length `p+q`. In particular, words of length one are primitive.
The coproduct takes values in a product of tensor products, rather than the algebraic tensor
square of the product. This is the completed reduced coalgebra used by continuous bar
coderivations.

The length-completion convention follows J.-L. Loday and B. Vallette, *Algebraic Operads*,
Chapters 9--10. Reduced deconcatenation is coassociative in each triple of positive lengths.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The product of the positive tensor powers of `M`, completed in tensor length. -/
abbrev CompletedReducedTensorWords :=
  ∀ n : {n : ℕ // 0 < n}, TensorPower R n.1 M

namespace CompletedReducedTensorWords

/-- Insert a zero empty-word component to view a completed reduced word as a completed
coaugmented word. -/
noncomputable def toCompleted : CompletedReducedTensorWords R M →ₗ[R]
    CompletedTensorWords R M :=
  LinearMap.pi fun n ↦
    if h : 0 < n then LinearMap.proj (⟨n, h⟩ : {n : ℕ // 0 < n}) else 0

/-- The inserted empty-word component is zero. -/
@[simp] theorem toCompleted_zero (x : CompletedReducedTensorWords R M) :
    toCompleted R M x 0 = 0 := by
  simp [toCompleted]

/-- Positive-length components are unchanged by insertion. -/
@[simp] theorem toCompleted_pos (x : CompletedReducedTensorWords R M)
    (n : {n : ℕ // 0 < n}) : toCompleted R M x n.1 = x n := by
  simp [toCompleted, n.2]

/-- Forget the empty-word component of a completed coaugmented word. -/
noncomputable def ofCompleted : CompletedTensorWords R M →ₗ[R]
    CompletedReducedTensorWords R M :=
  LinearMap.pi fun n ↦ LinearMap.proj n.1

/-- Forgetting the empty word reads each positive-length component unchanged. -/
@[simp] theorem ofCompleted_apply (x : CompletedTensorWords R M)
    (n : {n : ℕ // 0 < n}) : ofCompleted R M x n = x n.1 := by
  simp [ofCompleted]

/-- Forgetting the empty component after inserting it is the identity. -/
@[simp] theorem ofCompleted_toCompleted (x : CompletedReducedTensorWords R M) :
    ofCompleted R M (toCompleted R M x) = x := by
  funext n
  exact toCompleted_pos R M x n

/-- A completed word with zero empty component is recovered from its positive-length part. -/
theorem toCompleted_ofCompleted (x : CompletedTensorWords R M) (hx : x 0 = 0) :
    toCompleted R M (ofCompleted R M x) = x := by
  funext n
  by_cases hn : 0 < n
  · exact (toCompleted_pos R M (ofCompleted R M x) ⟨n, hn⟩).trans
      (ofCompleted_apply R M x ⟨n, hn⟩)
  · have hn0 : n = 0 := by omega
    subst n
    simpa only [toCompleted_zero] using hx.symm

/-- The positive-length product embeds linearly into the coaugmented completed words. -/
theorem toCompleted_injective : Function.Injective (toCompleted R M) :=
  Function.LeftInverse.injective (g := ofCompleted R M) (ofCompleted_toCompleted R M)

/-- The image of the reduced completion consists of completed words with zero empty component. -/
theorem range_toCompleted : LinearMap.range (toCompleted R M) =
    LinearMap.ker (LinearMap.proj (R := R) (i := 0) :
      CompletedTensorWords R M →ₗ[R] TensorPower R 0 M) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact toCompleted_zero R M y
  · intro hx
    exact ⟨ofCompleted R M x, toCompleted_ofCompleted R M x hx⟩

/-- Include a finite reduced word in its length completion. -/
noncomputable def ofFinite : ReducedTensorWords R M →ₗ[R]
    CompletedReducedTensorWords R M :=
  DFinsupp.coeFnLinearMap R

/-- The completion includes each length component unchanged. -/
@[simp] theorem ofFinite_apply (x : ReducedTensorWords R M)
    (n : {n : ℕ // 0 < n}) : ofFinite R M x n = x n := by
  exact congrFun (DFinsupp.coeFnLinearMap_apply (γ := R) x) n

/-- Finite reduced words embed in their length completion. -/
theorem ofFinite_injective : Function.Injective (ofFinite R M) := by
  intro x y h
  ext n
  exact congrFun h n

/-- Including a finite reduced word and then inserting the empty word agrees with first
including its empty-word-free version among finite coaugmented words. -/
theorem toCompleted_ofFinite (x : ReducedTensorWords R M) :
    toCompleted R M (ofFinite R M x) =
      DFinsupp.coeFnLinearMap R (TensorWords.reducedInclusion R M x) := by
  funext k
  rw [DFinsupp.coeFnLinearMap_apply, ← TensorWords.component_apply R M,
    TensorWords.component_reducedInclusion]
  by_cases hk : 0 < k
  · simpa only [dite_eq_left hk, ReducedTensorWords.apply_eq_component,
      ofFinite_apply] using (toCompleted_pos R M (ofFinite R M x) ⟨k, hk⟩)
  · have hk0 : k = 0 := by omega
    subst k
    simp only [toCompleted_zero, dite_eq_right (by omega)]

/-- Reduced deconcatenation, with one coordinate for every pair of positive output lengths. -/
noncomputable def deconcatenation : CompletedReducedTensorWords R M →ₗ[R]
    ∀ p q : {n : ℕ // 0 < n}, TensorPower R p.1 M ⊗[R] TensorPower R q.1 M :=
  LinearMap.pi fun p ↦ LinearMap.pi fun q ↦
    (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
      LinearMap.proj (⟨p.1 + q.1, by omega⟩ : {n : ℕ // 0 < n})

/-- Each reduced coproduct coordinate cuts the corresponding length component. -/
@[simp] theorem deconcatenation_apply (x : CompletedReducedTensorWords R M)
    (p q : {n : ℕ // 0 < n}) :
    deconcatenation R M x p q =
      (TensorPower.mulEquiv (R := R) (M := M)).symm
        (x ⟨p.1 + q.1, by omega⟩) := by
  simp [deconcatenation]

/-- Reduced deconcatenation agrees with coaugmented deconcatenation in positive bidegrees. -/
theorem deconcatenation_eq_completed (x : CompletedReducedTensorWords R M)
    (p q : {n : ℕ // 0 < n}) :
    deconcatenation R M x p q =
      CompletedTensorWords.deconcatenation R M (toCompleted R M x) p.1 q.1 := by
  rw [deconcatenation_apply, CompletedTensorWords.deconcatenation_apply]
  exact congrArg _ (toCompleted_pos R M x ⟨p.1 + q.1, by omega⟩).symm

/-- On finite reduced words, completed deconcatenation is the ordinary reduced coproduct
projected to its two output lengths. -/
@[simp↓] theorem deconcatenation_ofFinite (x : ReducedTensorWords R M)
    (p q : {n : ℕ // 0 < n}) :
    deconcatenation R M (ofFinite R M x) p q =
      TensorProduct.map (ReducedTensorWords.component R M p)
        (ReducedTensorWords.component R M q)
        (ReducedTensorWords.deconcatenation R M x) := by
  calc
    _ = TensorProduct.map (TensorWords.component R M p.1)
          (TensorWords.component R M q.1)
          (TensorWords.deconcatenation R M (TensorWords.reducedInclusion R M x)) := by
      rw [deconcatenation_eq_completed, toCompleted_ofFinite]
      exact CompletedTensorWords.deconcatenation_coe R M
        (TensorWords.reducedInclusion R M x) p.1 q.1
    _ = _ := by
      have hp : ReducedTensorWords.component R M p ∘ₗ
          TensorWords.reducedProjection R M = TensorWords.component R M p.1 :=
        LinearMap.ext (fun w ↦ TensorWords.component_reducedProjection R M p w)
      have hq : ReducedTensorWords.component R M q ∘ₗ
          TensorWords.reducedProjection R M = TensorWords.component R M q.1 :=
        LinearMap.ext (fun w ↦ TensorWords.component_reducedProjection R M q w)
      have h := congrArg
        (TensorProduct.map (ReducedTensorWords.component R M p)
          (ReducedTensorWords.component R M q))
        (TensorWords.map_reducedProjection_deconcatenation_reducedInclusion R M x)
      simpa only [TensorProduct.map_map, hp, hq] using h

/-- The reduced completed coproduct is coassociative in each triple of positive lengths. -/
theorem deconcatenation_coassoc (x : CompletedReducedTensorWords R M)
    (p q r : {n : ℕ // 0 < n}) :
    (TensorProduct.assoc R _ _ _)
      (TensorProduct.map (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        LinearMap.id (deconcatenation R M x ⟨p.1 + q.1, by omega⟩ r)) =
      TensorProduct.map LinearMap.id
        (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap
        (deconcatenation R M x p ⟨q.1 + r.1, by omega⟩) := by
  simpa only [deconcatenation_eq_completed] using
    CompletedTensorWords.deconcatenation_coassoc R M (toCompleted R M x) p.1 q.1 r.1

/-- The length filtration consists of completed reduced words with no components below `n`. -/
noncomputable def filtration (n : ℕ) : Submodule R (CompletedReducedTensorWords R M) :=
  (CompletedTensorWords.filtration R M n).comap (toCompleted R M)

/-- Membership in the reduced length filtration is coordinatewise vanishing below its cutoff. -/
@[simp] theorem mem_filtration (x : CompletedReducedTensorWords R M) (n : ℕ) :
    x ∈ filtration R M n ↔
      ∀ k : {k : ℕ // 0 < k}, k.1 < n → x k = 0 := by
  rw [filtration, Submodule.mem_comap, CompletedTensorWords.mem_filtration]
  constructor
  · intro hx k hk
    simpa only [toCompleted_pos] using hx k.1 hk
  · intro hx k hk
    by_cases hpos : 0 < k
    · exact (toCompleted_pos R M x ⟨k, hpos⟩).trans (hx ⟨k, hpos⟩ hk)
    · have hk0 : k = 0 := by omega
      subst k
      exact toCompleted_zero R M x

/-- The reduced length filtration is decreasing. -/
theorem filtration_antitone : Antitone (filtration R M) := by
  intro n m h
  exact Submodule.comap_mono (CompletedTensorWords.filtration_antitone R M h)

/-- The reduced length filtration is separated. -/
@[simp] theorem iInf_filtration_eq_bot : ⨅ n, filtration R M n = ⊥ := by
  simp only [filtration]
  rw [← Submodule.comap_iInf, CompletedTensorWords.iInf_filtration_eq_bot]
  apply eq_bot_iff.mpr
  intro x hx
  apply toCompleted_injective R M
  simpa only [Submodule.mem_comap, Submodule.mem_bot, map_zero] using hx

/-- Deconcatenation of a word filtered in degree `n` vanishes in total length below `n`. -/
theorem deconcatenation_eq_zero_of_mem_filtration
    {x : CompletedReducedTensorWords R M} {n : ℕ}
    {p q : {k : ℕ // 0 < k}} (hx : x ∈ filtration R M n) (hpq : p.1 + q.1 < n) :
    deconcatenation R M x p q = 0 := by
  rw [deconcatenation_apply,
    (mem_filtration R M x n).mp hx ⟨p.1 + q.1, by omega⟩ hpq]
  exact map_zero _

/-- Keep only the components of positive length below `n`, as a finite reduced word. -/
noncomputable def truncate (n : ℕ) : CompletedReducedTensorWords R M →ₗ[R]
    ReducedTensorWords R M :=
  TensorWords.reducedProjection R M ∘ₗ
    CompletedTensorWords.truncate R M n ∘ₗ toCompleted R M

/-- Truncation keeps precisely the positive-length components below its cutoff. -/
@[simp] theorem truncate_component (n : ℕ) (x : CompletedReducedTensorWords R M)
    (k : {k : ℕ // 0 < k}) :
    ReducedTensorWords.component R M k (truncate R M n x) =
      if k.1 < n then x k else 0 := by
  rw [truncate, LinearMap.comp_apply,
    LinearMap.comp_apply, TensorWords.component_reducedProjection,
    TensorWords.component_apply, CompletedTensorWords.truncate_apply]
  split_ifs with hk
  · exact toCompleted_pos R M x k
  · rfl

/-- Truncating after insertion into the coaugmented completion agrees with inserting the
truncated reduced word. -/
theorem truncate_toCompleted (n : ℕ)
    (x : CompletedReducedTensorWords R M) :
    CompletedTensorWords.truncate R M n (toCompleted R M x) =
      TensorWords.reducedInclusion R M (truncate R M n x) := by
  ext k
  rw [CompletedTensorWords.truncate_apply]
  by_cases hk : 0 < k
  · rw [← TensorWords.component_apply R M,
      TensorWords.component_reducedInclusion R M k, dite_eq_left hk,
      truncate_component]
    have hpos := toCompleted_pos R M x ⟨k, hk⟩
    exact congrArg (fun z ↦ if k < n then z else 0) hpos
  · have hk0 : k = 0 := by omega
    subst k
    rw [← TensorWords.component_apply R M,
      TensorWords.component_reducedInclusion R M 0]
    simp only [toCompleted_zero, ite_self, dite_eq_right (by omega)]

/-- The length filtration is the kernel of finite truncation. -/
theorem filtration_eq_ker_truncate (n : ℕ) :
    filtration R M n = LinearMap.ker (truncate R M n) := by
  rw [filtration, CompletedTensorWords.filtration_eq_ker_truncate]
  ext x
  simp only [Submodule.mem_comap, LinearMap.mem_ker]
  constructor
  · intro hx
    apply TensorWords.reducedInclusion_injective R M
    simpa only [truncate_toCompleted, map_zero] using hx
  · intro hx
    rw [truncate_toCompleted, hx, map_zero]

/-- Truncating a finite truncation again retains the shorter prefix. -/
@[simp] theorem truncate_truncate (n m : ℕ) (x : CompletedReducedTensorWords R M) :
    truncate R M n (ofFinite R M (truncate R M m x)) =
      truncate R M (min n m) x := by
  apply TensorWords.reducedInclusion_injective R M
  calc
    _ = CompletedTensorWords.truncate R M n
          (toCompleted R M (ofFinite R M (truncate R M m x))) :=
        (truncate_toCompleted R M n _).symm
    _ = CompletedTensorWords.truncate R M n
          (CompletedTensorWords.truncate R M m (toCompleted R M x)) := by
        rw [toCompleted_ofFinite, DFinsupp.coeFnLinearMap_apply,
          truncate_toCompleted]
    _ = CompletedTensorWords.truncate R M (min n m) (toCompleted R M x) :=
        CompletedTensorWords.truncate_truncate R M n m _
    _ = _ := truncate_toCompleted R M (min n m) x

/-- The reduced completion is complete for its length filtration: a compatible sequence
of finite positive-length truncations determines exactly one completed reduced word. -/
theorem existsUnique_of_compatible_truncations (x : ℕ → ReducedTensorWords R M)
    (hx : ∀ n m, n ≤ m → truncate R M n (ofFinite R M (x m)) = x n) :
    ∃! y : CompletedReducedTensorWords R M, ∀ n, truncate R M n y = x n := by
  have hcompat : ∀ n m, n ≤ m →
      CompletedTensorWords.truncate R M n (TensorWords.reducedInclusion R M (x m)) =
        TensorWords.reducedInclusion R M (x n) := by
    intro n m hnm
    have h := truncate_toCompleted R M n (ofFinite R M (x m))
    rw [toCompleted_ofFinite, hx n m hnm] at h
    exact h
  obtain ⟨y, hy, hunique⟩ :=
    CompletedTensorWords.existsUnique_of_compatible_truncations R M
      (fun n ↦ TensorWords.reducedInclusion R M (x n)) hcompat
  have hy0 : y 0 = 0 := by
    have hzero : (TensorWords.reducedInclusion R M (x 1)) 0 = 0 := by
      rw [← TensorWords.component_apply R M,
        TensorWords.component_reducedInclusion R M 0]
      simp
    have h := congrArg (fun w : TensorWords R M ↦ w 0) (hy 1)
    simpa only [CompletedTensorWords.truncate_apply, Nat.zero_lt_one, ite_true,
      hzero] using h
  refine ⟨ofCompleted R M y, ?_, ?_⟩
  · intro n
    apply TensorWords.reducedInclusion_injective R M
    rw [← truncate_toCompleted, toCompleted_ofCompleted R M y hy0, hy n]
  · intro z hz
    have hz' : ∀ n, CompletedTensorWords.truncate R M n (toCompleted R M z) =
        TensorWords.reducedInclusion R M (x n) := by
      intro n
      rw [truncate_toCompleted, hz n]
    have h := hunique (toCompleted R M z) hz'
    exact (ofCompleted_toCompleted R M z).symm.trans
      (congrArg (ofCompleted R M) h)

end CompletedReducedTensorWords
end TauCeti

namespace TauCeti.CompletedReducedTensorWords

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The tensor-length filtration of completed reduced tensor words is complete and separated. -/
theorem isCompleteFiltration_filtration : IsCompleteFiltration (filtration R M) :=
  isCompleteFiltration_pi Subtype.val _ fun n x ↦ mem_filtration R M x n

end TauCeti.CompletedReducedTensorWords
