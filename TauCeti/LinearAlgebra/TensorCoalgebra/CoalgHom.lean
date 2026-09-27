/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives

/-!
# Coalgebra morphisms of reduced tensor coalgebras

For `R`-modules `M` and `N`, a linear map `F : Tᶜ(M) ⟶ Tᶜ(N)` between the reduced tensor
coalgebras `⨁_{n ≥ 1} M^{⊗n}` and `⨁_{n ≥ 1} N^{⊗n}` is a *coalgebra morphism* when it commutes
with reduced deconcatenation: `Δ ∘ F = (F ⊗ F) ∘ Δ`.  This file proves the concrete correspondence
between coalgebra morphisms `Tᶜ(M) ⟶ Tᶜ(N)` and their families of Taylor components, obtained by
composing with the projection `Tᶜ(N) ⟶ N` onto single letters.

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

* `TauCeti.ReducedTensorWords.IsCoalgHom`: a linear map commuting with reduced deconcatenation.
* `TauCeti.ReducedTensorWords.coalgHom`: the coalgebra morphism with prescribed Taylor components.
* `TauCeti.ReducedTensorWords.coalgHomEquivTaylor`: coalgebra morphisms are in bijection with
  their Taylor components.

## Main results

* `TauCeti.ReducedTensorWords.coalgHom_subword`: the recursive evaluation rule of `coalgHom f`.
* `TauCeti.ReducedTensorWords.isCoalgHom_coalgHom` and
  `TauCeti.ReducedTensorWords.letter_comp_coalgHom`: `coalgHom f` is a coalgebra morphism with
  Taylor components `f`.
* `TauCeti.ReducedTensorWords.IsCoalgHom.eq_of_letter_comp_eq`: a coalgebra morphism is determined
  by its Taylor components.
* `TauCeti.ReducedTensorWords.coalgHom_comp_letter`: the letterwise map of a linear map is the
  coalgebra morphism whose only nonzero Taylor component is that map in arity one.
* `TauCeti.ReducedTensorWords.IsCoalgHom.mem_filtration`: a coalgebra morphism does not increase
  tensor length.
* `TauCeti.ReducedTensorWords.IsCoalgHom.bijective_of_letter_comp_comp_ofLetter_bijective`: a
  coalgebra morphism with bijective arity-one component is bijective, and
  `TauCeti.ReducedTensorWords.IsCoalgHom.linearEquiv_symm`: the inverse of a bijective coalgebra
  morphism is a coalgebra morphism.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

namespace TauCeti

namespace ReducedTensorWords

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
      · have hb0 : b = 0 := by omega
        rw [hb0, subword_length_zero]
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
      have had : a + d + (e - d) = a + e := by omega
      have hbd : b - d - (e - d) = b - e := by omega
      rw [had, hbd]
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
        induction w using TensorProduct.inductionOn with
        | tmul u v =>
            simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype]
            rw [ih _ u.2, ih _ v.2]
        | add u v hu hv => simp only [map_add, hu, hv]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
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
@[simp]
theorem coalgHom_comp_letter (g : M →ₗ[R] N) :
    coalgHom R (g ∘ₗ letter R M) = ReducedTensorWords.map (R := R) g := by
  rw [(isCoalgHom_map g).eq_coalgHom, letter_comp_map]

end CoalgHom

/-! ### The length filtration and bijectivity

A coalgebra morphism of reduced tensor coalgebras never increases tensor length, and it is
bijective as soon as its arity-one Taylor component is.  The proof reduces, by correcting with the
letterwise inverse of that component, to a coalgebra endomorphism fixing every single letter; such
an endomorphism differs from the identity by a map lowering the length filtration, hence is
bijective by induction along the filtration. -/

section Filtration

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The Taylor expansion of `f` does not increase tensor length: it sends a block of `b` letters
into the words of length at most `b`. -/
theorem coalgHom_subword_mem_filtration (f : ReducedTensorWords R M →ₗ[R] N) {n : ℕ}
    (x : Fin n → M) (a b : ℕ) : coalgHom R f (subword R x a b) ∈ filtration R N b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [subword_length_zero, map_zero]
      exact Submodule.zero_mem _
    rw [coalgHom_subword]
    refine Submodule.add_mem _ (filtration_monotone R N hb (ofLetter_mem_filtration R N _))
      (Submodule.sum_mem _ fun d hd ↦ ?_)
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    · exact filtration_monotone R N (by omega)
        (prepend_mem_filtration R N _ (ih (b - d) (by omega) (a + d)))

/-- The Taylor expansion of `f` preserves the conilpotence filtration. -/
theorem coalgHom_mem_filtration (f : ReducedTensorWords R M →ₗ[R] N) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    coalgHom R f z ∈ filtration R N n := by
  have h : filtration R M n ≤ (filtration R N n).comap (coalgHom R f) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _
          (filtration_monotone R N hk (coalgHom_subword_mem_filtration f y 0 k.1))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  exact h hz

/-- A coalgebra morphism preserves the conilpotence filtration. -/
theorem IsCoalgHom.mem_filtration {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) {n : ℕ} {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    F z ∈ filtration R N n := by
  rw [hF.eq_coalgHom]
  exact coalgHom_mem_filtration _ hz

/-- A coalgebra morphism sends a single letter to the single letter given by its arity-one Taylor
component. -/
theorem IsCoalgHom.apply_ofLetter {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (a : M) :
    F (ofLetter R M a) = ofLetter R N (letter R N (F (ofLetter R M a))) := by
  nth_rw 1 [hF.eq_coalgHom]
  rw [coalgHom_ofLetter, LinearMap.comp_apply]

/-- The inverse of a linear equivalence of reduced tensor coalgebras which is a coalgebra morphism
is again a coalgebra morphism. -/
theorem IsCoalgHom.linearEquiv_symm {e : ReducedTensorWords R M ≃ₗ[R] ReducedTensorWords R N}
    (he : IsCoalgHom R e.toLinearMap) : IsCoalgHom R e.symm.toLinearMap := by
  rw [isCoalgHom_iff]
  refine LinearMap.ext fun w ↦ ?_
  have h := he.deconcatenation_apply (e.symm w)
  rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
    ← LinearMap.comp_apply (TensorProduct.map _ _),
    ← TensorProduct.map_comp, LinearEquiv.symm_comp, TensorProduct.map_id, LinearMap.id_apply]

/-- The arity-one Taylor component of a linear equivalence of reduced tensor coalgebras which is a
coalgebra morphism is bijective, with inverse the arity-one component of the inverse. -/
theorem IsCoalgHom.letter_comp_comp_ofLetter_bijective
    {e : ReducedTensorWords R M ≃ₗ[R] ReducedTensorWords R N} (he : IsCoalgHom R e.toLinearMap) :
    Function.Bijective (letter R N ∘ₗ e.toLinearMap ∘ₗ ofLetter R M) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨letter R M ∘ₗ e.symm.toLinearMap ∘ₗ ofLetter R N, fun a ↦ ?_, fun b ↦ ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [← he.apply_ofLetter, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, letter_ofLetter]
  · simp only [LinearMap.comp_apply]
    rw [← he.linearEquiv_symm.apply_ofLetter, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, letter_ofLetter]

/-- Correcting a coalgebra morphism with bijective arity-one component by the letterwise inverse
of that component yields a coalgebra endomorphism fixing every single letter. -/
theorem IsCoalgHom.map_symm_comp_comp_ofLetter
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hf : Function.Bijective (letter R N ∘ₗ F ∘ₗ ofLetter R M)) :
    (ReducedTensorWords.map (R := R) (LinearEquiv.ofBijective _ hf).symm.toLinearMap ∘ₗ F) ∘ₗ
        ofLetter R M = ofLetter R M := by
  refine LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [hF.apply_ofLetter, map_ofLetter, LinearEquiv.coe_coe]
  exact congrArg (ofLetter R M) ((LinearEquiv.ofBijective _ hf).symm_apply_apply a)

end Filtration

section Unipotent

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A coalgebra endomorphism of the reduced tensor coalgebra fixing every single letter moves a
block of `b` letters by a word of length at most `b - 1`. -/
theorem IsCoalgHom.sub_subword_mem_filtration
    {G : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hG : IsCoalgHom R G)
    (h₁ : G ∘ₗ ofLetter R M = ofLetter R M) {l : ℕ} (x : Fin l → M) (a b : ℕ) :
    G (subword R x a b) - subword R x a b ∈ filtration R M (b - 1) := by
  -- Expand `G` as the Taylor expansion of its components: the summand cutting off the first
  -- letter reproduces the block up to a shorter correction, handled by induction on the length,
  -- and every other summand is shorter than the block.
  have hf₁ : ∀ y : M, (letter R M ∘ₗ G) (ofLetter R M y) = y := fun y ↦ by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply G, h₁, letter_ofLetter]
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [subword_length_zero, map_zero, sub_self]
      exact Submodule.zero_mem _
    by_cases hab : a + b ≤ l
    swap
    · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero, sub_self]
      exact Submodule.zero_mem _
    have ha : a < l := by omega
    obtain rfl | hb2 : b = 1 ∨ 2 ≤ b := by omega
    · rw [subword_one R M x ha, ← LinearMap.comp_apply, h₁, sub_self]
      exact Submodule.zero_mem _
    -- The summand collapsing the whole block to a letter.
    have hL : ofLetter R M ((letter R M ∘ₗ G) (subword R x a b)) ∈ filtration R M (b - 1) :=
      filtration_monotone R M (by omega) (ofLetter_mem_filtration R M _)
    -- The correction in the summand cutting off the first letter, by induction.
    have hP : prepend R M (x ⟨a, ha⟩)
        (G (subword R x (a + 1) (b - 1)) - subword R x (a + 1) (b - 1)) ∈
          filtration R M (b - 1) := by
      have h := prepend_mem_filtration R M (x ⟨a, ha⟩) (ih (b - 1) (by omega) (a + 1))
      rwa [Nat.sub_add_cancel (by omega)] at h
    -- The summands cutting off at least two letters are shorter than the block.
    have hS : ∑ d ∈ (Finset.range b).erase 1,
        prepend R M ((letter R M ∘ₗ G) (subword R x a d)) (G (subword R x (a + d) (b - d))) ∈
          filtration R M (b - 1) := by
      refine Submodule.sum_mem _ fun d hd ↦ ?_
      rw [Finset.mem_erase, Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
        exact Submodule.zero_mem _
      · exact filtration_monotone R M (by omega) (prepend_mem_filtration R M _
          (hG.mem_filtration (subword_mem_filtration R M x (a + d) le_rfl)))
    have hsplit : G (subword R x (a + 1) (b - 1)) = subword R x (a + 1) (b - 1) +
        (G (subword R x (a + 1) (b - 1)) - subword R x (a + 1) (b - 1)) :=
      (add_sub_cancel _ _).symm
    nth_rw 1 [hG.eq_coalgHom]
    rw [coalgHom_subword, ← hG.eq_coalgHom,
      ← Finset.add_sum_erase (Finset.range b) _ (Finset.mem_range.2 (by omega : 1 < b)),
      subword_one R M x ha, hf₁, hsplit, map_add, prepend_subword x ha (by omega),
      Nat.sub_add_cancel (by omega : 1 ≤ b)]
    have hcalc : ∀ L P S w : ReducedTensorWords R M, L + (w + P + S) - w = L + P + S := by
      intros
      abel
    rw [hcalc]
    exact Submodule.add_mem _ (Submodule.add_mem _ hL hP) hS

/-- A coalgebra endomorphism of the reduced tensor coalgebra fixing every single letter moves a
word of length at most `n + 1` by a word of length at most `n`: it is the identity plus a map
lowering the length filtration. -/
theorem IsCoalgHom.sub_mem_filtration {G : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hG : IsCoalgHom R G) (h₁ : G ∘ₗ ofLetter R M = ofLetter R M) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    G z - z ∈ filtration R M n := by
  have h : filtration R M (n + 1) ≤ (filtration R M n).comap (G - LinearMap.id) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    simp only [Submodule.mem_comap]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r y =>
        rw [map_smul, map_smul, LinearMap.sub_apply, LinearMap.id_apply, of_tprod_eq_subword R k.2]
        exact Submodule.smul_mem _ _
          (filtration_monotone R M (by omega) (hG.sub_subword_mem_filtration h₁ y 0 k.1))
    | add u v hu hv =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ hu hv
  simpa only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply] using h hz

/-- A coalgebra endomorphism of the reduced tensor coalgebra fixing every single letter is
bijective. -/
theorem IsCoalgHom.bijective_of_comp_ofLetter_eq
    {G : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hG : IsCoalgHom R G)
    (h₁ : G ∘ₗ ofLetter R M = ofLetter R M) : Function.Bijective G := by
  constructor
  · refine (injective_iff_map_eq_zero G).2 fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_filtration R M z
    induction n generalizing z with
    | zero =>
        rw [filtration_zero] at hn
        exact (Submodule.mem_bot R).1 hn
    | succ n ih =>
        refine ih z hz ?_
        have h := hG.sub_mem_filtration h₁ hn
        rwa [hz, zero_sub, Submodule.neg_mem_iff] at h
  · have key : ∀ n : ℕ, filtration R M n ≤ LinearMap.range G := by
      intro n
      induction n with
      | zero =>
          rw [filtration_zero]
          exact bot_le
      | succ n ih =>
          intro w hw
          obtain ⟨u, hu⟩ := ih (hG.sub_mem_filtration h₁ hw)
          exact ⟨w - u, by rw [map_sub, hu, sub_sub_cancel]⟩
    intro w
    obtain ⟨n, hn⟩ := exists_mem_filtration R M w
    exact key n hn

/-- A coalgebra endomorphism of the reduced tensor coalgebra fixing every single letter maps every
submodule it preserves onto itself. -/
theorem IsCoalgHom.map_eq_of_map_le
    {G : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hG : IsCoalgHom R G)
    (h₁ : G ∘ₗ ofLetter R M = ofLetter R M) {p : Submodule R (ReducedTensorWords R M)}
    (hp : p.map G ≤ p) : p.map G = p := by
  refine le_antisymm hp fun w hw ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M w
  induction n generalizing w with
  | zero =>
      rw [filtration_zero] at hn
      rw [(Submodule.mem_bot R).1 hn]
      exact Submodule.zero_mem _
  | succ n ih =>
      have hGw : G w - w ∈ p := Submodule.sub_mem _ (hp ⟨w, hw, rfl⟩) hw
      obtain ⟨u, hu, hGu⟩ := ih (G w - w) hGw (hG.sub_mem_filtration h₁ hn)
      exact ⟨w - u, Submodule.sub_mem _ hw hu, by rw [map_sub, hGu, sub_sub_cancel]⟩

/-- A coalgebra morphism of reduced tensor coalgebras whose arity-one Taylor component is
bijective is bijective. -/
theorem IsCoalgHom.bijective_of_letter_comp_comp_ofLetter_bijective
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hf : Function.Bijective (letter R N ∘ₗ F ∘ₗ ofLetter R M)) :
    Function.Bijective F := by
  set e := LinearEquiv.ofBijective _ hf
  have hFeq : F = ReducedTensorWords.map (R := R) e.toLinearMap ∘ₗ
      (ReducedTensorWords.map (R := R) e.symm.toLinearMap ∘ₗ F) := by
    rw [← LinearMap.comp_assoc, ← map_comp, LinearEquiv.comp_symm, map_id, LinearMap.id_comp]
  rw [hFeq]
  exact (map_bijective R e).comp
    (((isCoalgHom_map _).comp hF).bijective_of_comp_ofLetter_eq (hF.map_symm_comp_comp_ofLetter hf))

end Unipotent

end ReducedTensorWords

end TauCeti
