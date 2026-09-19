/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Range
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives

/-!
# Coalgebra morphisms of reduced tensor coalgebras

For `R`-modules `M` and `N`, a linear map `F : Tᶜ(M) ⟶ Tᶜ(N)` between the reduced tensor
coalgebras `⨁_{n ≥ 1} M^{⊗n}` and `⨁_{n ≥ 1} N^{⊗n}` is a *coalgebra morphism* when it commutes
with reduced deconcatenation: `Δ ∘ F = (F ⊗ F) ∘ Δ`.  This file proves that the reduced tensor
coalgebra is cofree among conilpotent coalgebras in the following concrete form: a coalgebra
morphism is exactly its family of Taylor components, the composite `Tᶜ(M) ⟶ N` with the projection
onto single letters.

That a coalgebra morphism is *determined* by its Taylor components is an induction along the
conilpotence filtration, exactly as for coderivations.  That *every* family `f` of components
occurs is the Taylor expansion `coalgHom f`, which sends a word `x₁ ⋯ xₙ` to the sum, over all
ways of cutting it into consecutive nonempty blocks `B₁ ⋯ B_k`, of the word
`f(B₁) ⋯ f(B_k)`.  It is built recursively by splitting off the first block,
`coalgHom f (x₁ ⋯ xₙ) = f(x₁ ⋯ xₙ) + ∑_{0 < d < n} f(x₁ ⋯ x_d) · coalgHom f (x_{d+1} ⋯ xₙ)`,
where `·` prepends a letter to a word (`ReducedTensorWords.prepend`).  Deconcatenating a
prepended word either separates the new letter or cuts the remaining word, which is what makes the
coalgebra-morphism identity an induction on the length of the word.

No sign enters: a coalgebra morphism of a bar construction has degree zero, so this ungraded
correspondence is the one describing `A∞` morphisms through their components `f_n`.

## Main definitions

* `TauCeti.ReducedTensorWords.prepend`: prepend a letter to a reduced tensor word.
* `TauCeti.ReducedTensorWords.IsCoalgHom`: a linear map commuting with reduced deconcatenation.
* `TauCeti.ReducedTensorWords.coalgHom`: the coalgebra morphism with prescribed Taylor components.
* `TauCeti.ReducedTensorWords.coalgHomEquivTaylor`: coalgebra morphisms are in bijection with
  their Taylor components.

## Main results

* `TauCeti.ReducedTensorWords.deconcatenation_prepend`: the cuts of a prepended word.
* `TauCeti.ReducedTensorWords.coalgHom_subword`: the recursive evaluation rule of `coalgHom f`.
* `TauCeti.ReducedTensorWords.isCoalgHom_coalgHom` and
  `TauCeti.ReducedTensorWords.letter_comp_coalgHom`: `coalgHom f` is a coalgebra morphism with
  Taylor components `f`.
* `TauCeti.ReducedTensorWords.IsCoalgHom.eq_of_letter_comp_eq`: a coalgebra morphism is determined
  by its Taylor components.
* `TauCeti.ReducedTensorWords.coalgHom_comp_letter`: the letterwise map of a linear map is the
  coalgebra morphism whose only nonzero Taylor component is that map in arity one.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

namespace TauCeti

namespace ReducedTensorWords

section Prepend

variable (R : Type uR) (N : Type uN) [CommSemiring R] [AddCommMonoid N] [Module R N]

/-- Prepend a letter to a reduced tensor word: `a` and `y₁ ⋯ y_k` give `a y₁ ⋯ y_k`. -/
noncomputable def prepend : N →ₗ[R] ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N :=
  (DirectSum.toModule R {n : ℕ // 0 < n} (N →ₗ[R] ReducedTensorWords R N) fun k ↦
    ((TensorProduct.mk R (TensorPower R 1 N) (TensorPower R k.1 N)).compr₂
        (of R N ⟨1 + k.1, by omega⟩ ∘ₗ (TensorPower.mulEquiv (R := R) (M := N)).toLinearMap) ∘ₗ
      (TauCeti.TensorPower.oneEquiv R N).symm.toLinearMap).flip).flip

variable {R N}

/-- Prepending a letter to a pure tensor word conses it onto the letters. -/
theorem prepend_of_tprod (a : N) (k : {n : ℕ // 0 < n}) (y : Fin k.1 → N) :
    prepend R N a (of R N k (PiTensorProduct.tprod R y)) =
      of R N ⟨k.1 + 1, by omega⟩ (PiTensorProduct.tprod R (Fin.cons a y)) := by
  simp only [prepend, LinearMap.flip_apply, toModule_of, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
    TauCeti.TensorPower.oneEquiv_symm_apply, ← TensorPower.gMul_def, TensorPower.tprod_mul_tprod,
    Fin.append_left_eq_cons]
  exact of_tprod_congr R N _ (Nat.add_comm 1 k.1) fun _ ↦ rfl

/-- Prepending the letter at position `a` to the block that starts right after it extends the
block by that letter. -/
theorem prepend_subword {n : ℕ} (z : Fin n → N) {a b : ℕ} (ha : a < n) (hb : 0 < b) :
    prepend R N (z ⟨a, ha⟩) (subword R z (a + 1) b) = subword R z a (b + 1) := by
  by_cases hab : a + 1 + b ≤ n
  · rw [subword_eq_of_tprod R z hb hab, prepend_of_tprod,
      subword_eq_of_tprod R z (Nat.succ_pos b) (by omega)]
    refine of_tprod_congr R N _ rfl fun i ↦ ?_
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
        simp only [Fin.cons_succ, Fin.cast_eq_self, Fin.val_succ]
        exact congrArg z (Fin.ext (by simp only; omega))
  · rw [subword_eq_zero_of_lt_add R z (by omega), map_zero,
      subword_eq_zero_of_lt_add R z (by omega)]

/-- A prepended word has length at least two, so it has no letter component. -/
@[simp]
theorem letter_prepend (a : N) (w : ReducedTensorWords R N) : letter R N (prepend R N a w) = 0 := by
  have h : letter R N ∘ₗ prepend R N a = 0 := by
    refine linearMap_ext R N fun k y ↦ ?_
    rw [LinearMap.comp_apply, prepend_of_tprod, letter_apply,
      component_of_of_ne R N (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega),
      map_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun h w

/-- Cutting a prepended word `a · w` either separates the new letter from `w`, or cuts `w` and
prepends `a` to the left half. -/
theorem deconcatenation_prepend (a : N) (w : ReducedTensorWords R N) :
    deconcatenation R N (prepend R N a w) =
      ofLetter R N a ⊗ₜ[R] w +
        LinearMap.rTensor (ReducedTensorWords R N) (prepend R N a) (deconcatenation R N w) := by
  have h : deconcatenation R N ∘ₗ prepend R N a =
      (TensorProduct.mk R _ _ (ofLetter R N a)) +
        LinearMap.rTensor (ReducedTensorWords R N) (prepend R N a) ∘ₗ deconcatenation R N := by
    refine linearMap_ext R N fun k y ↦ ?_
    obtain ⟨k, hk⟩ := k
    -- Read `a · y` as the whole of the tuple `z = a y`, and `y` as its block after position `0`.
    set z : Fin (k + 1) → N := Fin.cons a y with hz
    have hw : of R N ⟨k, hk⟩ (PiTensorProduct.tprod R y) = subword R z 1 k := by
      rw [subword_eq_of_tprod R z hk (by omega)]
      exact of_tprod_congr R N _ rfl fun i ↦ by
        simp only [hz, Fin.cast_eq_self]
        exact (Fin.cons_succ (α := fun _ ↦ N) a y i).symm.trans
          (congrArg (Fin.cons a y) (Fin.ext ((Fin.val_succ i).trans (Nat.add_comm _ _))))
    have ha : z ⟨0, Nat.succ_pos k⟩ = a := Fin.cons_zero _ _
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
      TensorProduct.mk_apply]
    rw [hw, ← ha, prepend_subword z (Nat.succ_pos _) hk, deconcatenation_subword,
      deconcatenation_subword, map_sum,
      sum_Ioo_eq_sum_range _ _ (by rw [subword_length_zero, TensorProduct.zero_tmul]),
      sum_Ioo_eq_sum_range _ _ (by rw [subword_length_zero, TensorProduct.zero_tmul, map_zero]),
      Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [subword_length_zero, TensorProduct.zero_tmul, map_zero, add_zero]
    rw [subword_one R N z (Nat.succ_pos _), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [LinearMap.rTensor_tmul, prepend_subword z (Nat.succ_pos _) (Nat.succ_pos c)]
      exact congrArg _ (congrArg₂ (subword R z) (by omega) (by omega))
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
    TensorProduct.mk_apply] using LinearMap.congr_fun h w

end Prepend

section CoalgHom

variable (R : Type uR) {M : Type uM} {N : Type uN} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The length-`n` component of the Taylor expansion `coalgHom f`: split off a nonempty first block
of `d` letters, apply `f` to it, and prepend the result to the expansion of the remaining letters;
the block of all `n` letters contributes the single letter `f(x₁ ⋯ xₙ)`. -/
private noncomputable def coalgHomComponent (f : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if h : 0 < n then ofLetter R N ∘ₗ f ∘ₗ of R M ⟨n, h⟩ else 0) +
      ∑ d : Fin n, if h : 0 < d.1 then
        TensorProduct.lift ((prepend R N).compl₁₂ (f ∘ₗ of R M ⟨d.1, h⟩)
          (coalgHomComponent f (n - d.1))) ∘ₗ TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The coalgebra morphism of reduced tensor coalgebras with Taylor components `f`: it sends a word
`x₁ ⋯ xₙ` to the sum, over all ways of cutting it into consecutive nonempty blocks `B₁ ⋯ B_k`, of
the word `f(B₁) ⋯ f(B_k)`. -/
noncomputable def coalgHom (f : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ coalgHomComponent R f n.1

variable {R}

/-- The recursive evaluation rule of `coalgHom f` on a pure tensor word. -/
private theorem coalgHom_of_tprod (f : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n)
    (x : Fin n → M) :
    coalgHom R f (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (f (subword R x 0 n)) +
        ∑ d ∈ Finset.range n,
          prepend R N (f (subword R x 0 d)) (coalgHom R f (subword R x d (n - d))) := by
  rw [coalgHom, toModule_of, coalgHomComponent, dite_eq_left hn, ← of_tprod_eq_subword R hn x]
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  congr 1
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases Nat.eq_zero_or_pos d.1 with hd | hd
  · rw [dite_eq_right (by omega), hd, subword_length_zero, map_zero, map_zero, LinearMap.zero_apply,
      LinearMap.zero_apply]
  · have hdn := d.isLt
    rw [dite_eq_left hd, subword_eq_of_tprod R x hd (by omega),
      subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega), toModule_of]
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorPower.splitAt_tprod,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    congr 3
    exact of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))

/-- The recursive evaluation rule of `coalgHom f` on a block of a tensor word: either the whole
block is collapsed to the single letter `f(B)`, or a nonempty first block of `d` letters is
collapsed and prepended to the expansion of the rest.  The summand `d = 0` vanishes. -/
theorem coalgHom_subword (f : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    coalgHom R f (subword R x a b) =
      ofLetter R N (f (subword R x a b)) +
        ∑ d ∈ Finset.range b,
          prepend R N (f (subword R x a d)) (coalgHom R f (subword R x (a + d) (b - d))) := by
  by_cases h : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := h
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j hj ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (coalgHom R f) (subword_eq_of_tprod R x hb hab)
    rw [hx, coalgHom_of_tprod f hb, hy 0 b (by omega), Nat.add_zero]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 h with hb | hab
      · rw [show b = 0 by omega, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 h with hb | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega), map_zero, map_zero]

/-- The Taylor expansion of `f` has Taylor components `f`: every word it produces from more than
one block has length at least two. -/
@[simp]
theorem letter_comp_coalgHom (f : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ coalgHom R f = f := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, coalgHom_subword, map_add, map_sum,
    letter_ofLetter]
  simp only [letter_prepend, Finset.sum_const_zero, add_zero]

/-- On a single letter, `coalgHom f` is the single letter given by the arity-one component. -/
@[simp]
theorem coalgHom_ofLetter (f : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    coalgHom R f (ofLetter R M a) = ofLetter R N (f (ofLetter R M a)) := by
  have h := coalgHom_subword f (fun _ : Fin 1 ↦ a) 0 1
  rw [subword_one R M _ Nat.one_pos, Finset.sum_range_one, subword_length_zero, map_zero,
    map_zero, LinearMap.zero_apply, add_zero] at h
  exact h

variable (R) in
/-- A linear map of reduced tensor coalgebras is a *coalgebra morphism* when it commutes with
reduced deconcatenation: cutting its value is the same as cutting first and mapping both halves. -/
def IsCoalgHom (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) : Prop :=
  deconcatenation R N ∘ₗ F = TensorProduct.map F F ∘ₗ deconcatenation R M

/-- The defining identity of a coalgebra morphism, as a reusable `Iff`: this exposes the body of
`IsCoalgHom` to consumers in other modules, for which the definition's body is not exposed. -/
theorem isCoalgHom_iff {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} :
    IsCoalgHom R F ↔ deconcatenation R N ∘ₗ F = TensorProduct.map F F ∘ₗ deconcatenation R M :=
  Iff.rfl

/-- The defining identity of a coalgebra morphism, applied to an element. -/
theorem IsCoalgHom.deconcatenation_apply
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (z : ReducedTensorWords R M) :
    deconcatenation R N (F z) = TensorProduct.map F F (deconcatenation R M z) :=
  LinearMap.congr_fun hF z

/-- Mapping both halves of the cuts of a block, written as one sum over the cut position. -/
private theorem map_deconcatenation_subword {P Q : Type*} [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] (F : ReducedTensorWords R M →ₗ[R] P)
    (G : ReducedTensorWords R M →ₗ[R] Q) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    TensorProduct.map F G (deconcatenation R M (subword R x a b)) =
      ∑ c ∈ Finset.range b, F (subword R x a c) ⊗ₜ[R] G (subword R x (a + c) (b - c)) := by
  rw [deconcatenation_subword, map_sum,
    sum_Ioo_eq_sum_range _ _ (by rw [subword_length_zero, TensorProduct.zero_tmul, map_zero])]
  simp only [TensorProduct.map_tmul]

/-- The Taylor expansion `coalgHom f` is a coalgebra morphism. -/
theorem isCoalgHom_coalgHom (f : ReducedTensorWords R M →ₗ[R] N) :
    IsCoalgHom R (coalgHom R f) := by
  -- By induction on the length `b` of a block: cutting `f(B₁) · coalgHom f (rest)` either
  -- separates `f(B₁)`, or cuts the expansion of the shorter rest, which the induction handles.
  have key : ∀ {n : ℕ} (x : Fin n → M) (b a : ℕ),
      deconcatenation R N (coalgHom R f (subword R x a b)) =
        TensorProduct.map (coalgHom R f) (coalgHom R f)
          (deconcatenation R M (subword R x a b)) := by
    intro n x b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a
      -- Cutting the expansion of the rest of the word, by the induction hypothesis.
      have hP : ∀ d ∈ Finset.range b,
          LinearMap.rTensor (ReducedTensorWords R N) (prepend R N (f (subword R x a d)))
              (deconcatenation R N (coalgHom R f (subword R x (a + d) (b - d)))) =
            ∑ c ∈ Finset.range (b - d),
              prepend R N (f (subword R x a d)) (coalgHom R f (subword R x (a + d) c)) ⊗ₜ[R]
                coalgHom R f (subword R x (a + d + c) (b - d - c)) := by
        intro d hd
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.rTensor_zero, LinearMap.zero_apply,
            LinearMap.zero_apply, TensorProduct.zero_tmul, Finset.sum_const_zero]
        · rw [ih (b - d) (by omega), map_deconcatenation_subword, map_sum]
          simp only [LinearMap.rTensor_tmul]
      rw [coalgHom_subword, map_add, deconcatenation_ofLetter, zero_add, map_sum,
        map_deconcatenation_subword]
      rw [Finset.sum_congr rfl fun d _ ↦ deconcatenation_prepend _ _, Finset.sum_add_distrib,
        Finset.sum_congr rfl hP]
      simp only [coalgHom_subword f x a, TensorProduct.add_tmul, TensorProduct.sum_tmul,
        Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_range_diag_flip]
      refine Finset.sum_congr rfl fun e he ↦ ?_
      rw [Finset.mem_range] at he
      rw [Finset.sum_range_succ, Nat.sub_self, subword_length_zero, map_zero, map_zero,
        TensorProduct.zero_tmul, add_zero]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [Finset.mem_range] at hd
      rw [show a + d + (e - d) = a + e by omega, show b - d - (e - d) = b - e by omega]
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, of_tprod_eq_subword R n.2]
  exact key x n.1 0

/-- A coalgebra morphism of reduced tensor coalgebras is determined by its Taylor components, that
is by its composite with the projection onto single letters.  Two coalgebra morphisms agreeing
there agree on every tensor word, by induction along the conilpotence filtration. -/
theorem IsCoalgHom.eq_of_letter_comp_eq
    {F₁ F₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (h₁ : IsCoalgHom R F₁)
    (h₂ : IsCoalgHom R F₂) (hl : letter R N ∘ₗ F₁ = letter R N ∘ₗ F₂) : F₁ = F₂ := by
  have key : ∀ n : ℕ, ∀ z ∈ filtration R M n, F₁ z = F₂ z := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [filtration_zero] at hz
        rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
    | succ n ih =>
        intro z hz
        refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (LinearMap.congr_fun hl z)
        obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
        rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
        clear hw
        induction w using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul u v =>
            simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype]
            rw [ih _ u.2, ih _ v.2]
        | add u v hu hv => simp only [map_add, hu, hv]
  refine LinearMap.ext fun z ↦ ?_
  have hz : z ∈ ⨆ n : ℕ, filtration R M n := by rw [iSup_filtration_eq_top]; trivial
  obtain ⟨n, hn⟩ :=
    (Submodule.mem_iSup_of_directed _ (filtration_monotone R M).directed_le).1 hz
  exact key n z hn

/-- A coalgebra morphism is the Taylor expansion of its own Taylor components. -/
theorem IsCoalgHom.eq_coalgHom {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) : F = coalgHom R (letter R N ∘ₗ F) :=
  hF.eq_of_letter_comp_eq (isCoalgHom_coalgHom _) (letter_comp_coalgHom _).symm

variable (R M N) in
/-- Coalgebra morphisms of reduced tensor coalgebras are in bijection with their Taylor
components, the linear maps from tensor words to letters.

Its body is sealed; reason about it through
`TauCeti.ReducedTensorWords.coalgHomEquivTaylor_apply` and
`TauCeti.ReducedTensorWords.coalgHomEquivTaylor_symm_apply`. -/
noncomputable def coalgHomEquivTaylor :
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N // IsCoalgHom R F} ≃
      (ReducedTensorWords R M →ₗ[R] N) where
  toFun F := letter R N ∘ₗ F.1
  invFun f := ⟨coalgHom R f, isCoalgHom_coalgHom f⟩
  left_inv F := Subtype.ext F.2.eq_coalgHom.symm
  right_inv f := letter_comp_coalgHom f

@[simp]
theorem coalgHomEquivTaylor_apply
    (F : {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N // IsCoalgHom R F}) :
    coalgHomEquivTaylor R M N F = letter R N ∘ₗ F.1 :=
  (rfl)

@[simp]
theorem coalgHomEquivTaylor_symm_apply (f : ReducedTensorWords R M →ₗ[R] N) :
    ((coalgHomEquivTaylor R M N).symm f).1 = coalgHom R f :=
  (rfl)

variable (M) in
/-- The identity is a coalgebra morphism. -/
theorem isCoalgHom_id : IsCoalgHom R (LinearMap.id : ReducedTensorWords R M →ₗ[R] _) := by
  rw [isCoalgHom_iff, TensorProduct.map_id, LinearMap.id_comp, LinearMap.comp_id]

/-- A composite of coalgebra morphisms is a coalgebra morphism. -/
theorem IsCoalgHom.comp {P : Type uP} [AddCommMonoid P] [Module R P]
    {G : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R P}
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hG : IsCoalgHom R G)
    (hF : IsCoalgHom R F) : IsCoalgHom R (G ∘ₗ F) := by
  rw [isCoalgHom_iff, ← LinearMap.comp_assoc, hG, LinearMap.comp_assoc, hF, TensorProduct.map_comp,
    LinearMap.comp_assoc]

/-- Applying a linear map to every letter is a coalgebra morphism. -/
theorem isCoalgHom_map (g : M →ₗ[R] N) : IsCoalgHom R (ReducedTensorWords.map (R := R) g) :=
  deconcatenation_natural R g

/-- The letterwise map of `g` is the coalgebra morphism whose Taylor components are `g` in arity one
and zero in every higher arity. -/
theorem coalgHom_comp_letter (g : M →ₗ[R] N) :
    coalgHom R (g ∘ₗ letter R M) = ReducedTensorWords.map (R := R) g := by
  rw [(isCoalgHom_map g).eq_coalgHom, letter_comp_map]

end CoalgHom

end ReducedTensorWords

end TauCeti
