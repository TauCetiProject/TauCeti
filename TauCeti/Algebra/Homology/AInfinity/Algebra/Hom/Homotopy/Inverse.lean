/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Equiv
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential

/-!
# Homotopy inverses of A-infinity morphisms

Let `f : A ⟶ B` be a morphism of `A∞` algebras over a commutative ring `R`, with bar map `F`.  In
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Equiv` we projected any two-sided `A∞`
homotopy equivalence (`TauCeti.AInfinityHom.HomotopyEquiv`) to a homogeneous degree-`(-1)` linear
chain-homotopy equivalence between the unary complexes (`HomotopyEquiv.toLinearHomotopyEquiv`).

In this file we prove the converse: any homogeneous degree-`(-1)` chain-homotopy equivalence `e`
between `(A, m₁)` and `(B, m₁)` whose forward map is `f.linearPart` lifts to a two-sided `A∞`
homotopy equivalence with forward morphism `f`, inverse linear part `e.inv`, and right linear
homotopy `e.homotopyHomInv` (`HomotopyEquiv.ofLinear`).  Hence an `A∞` morphism over `R` is a
homotopy equivalence if and only if its linear part admits a graded chain-homotopy inverse
(`isHomotopyEquiv_iff_exists_linearHomotopyEquiv`).  Because `A∞` homotopies on reduced bar
constructions are coderivations along distinct pairs of coalgebra maps, they cannot be composed
vertically by naive addition; passing through `isHomotopyEquiv_iff_exists_linearHomotopyEquiv`
immediately yields closure of `A∞` homotopy equivalences under composition (`HomotopyEquiv.trans`,
`IsHomotopyEquiv.comp`), invariance under `A∞` homotopy (`Homotopy.isHomotopyEquiv_iff`), and
two-out-of-three (`IsHomotopyEquiv.of_precomp`, `IsHomotopyEquiv.of_postcomp`).  The specialization
to quasi-isomorphisms over a field (the Whitehead theorem for `A∞` algebras) is proved in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Whitehead`.

The lifting proof works directly on reduced bar constructions by induction along the word-length
filtration, in two stages:
1. **Right homotopy inverse.** Starting from `g₁ = e.inv` and `h₁ = e.homotopyHomInv` on single
   letters, assume Taylor maps `g_k : Tᶜ(sB) ⟶ sA` and `h_k : Tᶜ(sB) ⟶ sB` have been constructed so
   that `G_k = coalgHom g_k` and `K_k = gradedCoderivAlong (F ∘ G_k) id h_k` satisfy
   `b_A ∘ G_k - G_k ∘ b_B = 0` and `(F ∘ G_k - id) - (b_B ∘ K_k + K_k ∘ b_B) = 0` on words of
   length at most `k`.  On words of length `k + 1` both defects take single-letter values `Φ` and
   `Ψ` satisfying `d_A ∘ Φ + Φ ∘ b_{B,1} = 0` and `d_B ∘ Ψ - Ψ ∘ b_{B,1} = f₁ ∘ Φ`, which are
   killed simultaneously by explicit arity-`(k + 1)` corrections built from `e`.  Taking the
   stabilising limit over `k` produces `g : B ⟶ A` and a right homotopy `H_B : f ∘ g ⇒ id_B`.
2. **Left homotopy.** With `g` and `H_B` fixed, `g ∘ f` already has linear part chain-homotopic to
   `id_A`, and `K_B ∘ F - F ∘ K_A` measures compatibility with `H_B`.  Starting at `k = 0`, we
   simultaneously lift the Taylor components of a left homotopy `K_A` along `(G ∘ F, id)` and a
   degree-`(-2)` auxiliary `(F ∘ G ∘ F, F)`-coderivation `T` killing both
   `(G ∘ F - id) - (b_A ∘ K_A + K_A ∘ b_A)` and `(K_B ∘ F - F ∘ K_A) - (b_B ∘ T - T ∘ b_A)` at each
   arity, without assuming side or adjointness conditions on the linear homotopies of `e`.

## Main definitions

* `TauCeti.AInfinityHom.HomotopyEquiv.ofLinear`: lift a graded linear chain-homotopy equivalence on
  `f.linearPart` to an `A∞` homotopy equivalence with forward morphism `f`.
* `TauCeti.AInfinityHom.HomotopyEquiv.trans`: compose two `A∞` homotopy equivalences.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyEquiv`: over any commutative ring,
  `f` is an `A∞` homotopy equivalence if and only if `f.linearPart` extends to a homogeneous
  degree-`(-1)` linear chain-homotopy equivalence.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`, `TauCeti.AInfinityHom.Homotopy.isHomotopyEquiv_iff`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_precomp`, and
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_postcomp`: closure under composition, homotopy
  invariance, and two-out-of-three for `A∞` homotopy equivalences.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Section 1.3.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Theorem 10.4.4.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### Arity-by-arity lifting of linear chain-homotopy equivalences -/

section Lifting

open ReducedTensorWords

/-- Assemble a sequence of Taylor maps `φ n` into a single map taking `φ k` on words of length `k`.
When `φ (n + 1)` agrees with `φ n` on `filtration R M n` for every `n`, this agrees with `φ n` on
`filtration R M n`. -/
private noncomputable def stabilisingTaylor {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (φ : ℕ → ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] N :=
  DirectSum.toModule R _ _ fun k ↦ φ k.1 ∘ₗ of R M k

private theorem stabilisingTaylor_eq_of_le {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {φ : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (hφ : ∀ n, ∀ z ∈ filtration R M n, φ (n + 1) z = φ n z) {k n : ℕ} (hkn : k ≤ n)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M k) : φ n z = φ k z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [hφ n z (filtration_monotone R M hkn hz), ih]

private theorem stabilisingTaylor_apply_of_mem_filtration {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] {φ : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (hφ : ∀ n, ∀ z ∈ filtration R M n, φ (n + 1) z = φ n z) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    stabilisingTaylor φ z = φ n z := by
  have h : filtration R M n ≤ LinearMap.eqLocus (stabilisingTaylor φ) (φ n) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, stabilisingTaylor, toModule_of, LinearMap.comp_apply,
      stabilisingTaylor_eq_of_le hφ hk (of_mem_filtration R M le_rfl x)]
  exact h hz

private theorem isHomogeneous_stabilisingTaylor {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {r : ℤ}
    {φ : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (hφ : ∀ n, ∀ z ∈ filtration R M n, φ (n + 1) z = φ n z)
    (hdeg : ∀ n, LinearMap.IsHomogeneous (φ n) (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (stabilisingTaylor φ) (gradedPiece G) H.piece r := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [stabilisingTaylor_apply_of_mem_filtration hφ hn]
  exact (hdeg n).map_mem hz

/-- Shifting both source and target internal gradings by `1` preserves the degree of a homogeneous
linear map. -/
private theorem isHomogeneous_shift_one {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {r : ℤ}
    {u : M →ₗ[R] N} (hu : LinearMap.IsHomogeneous u G.piece H.piece r) :
    LinearMap.IsHomogeneous u (G.shift 1).piece (H.shift 1).piece r := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [InternalGrading.shift_piece] at hx ⊢
  rw [show p + r + 1 = (p + 1) + r by ring]
  exact hu.map_mem hx

private theorem letter_barDifferential_apply {M : Type*} [AddCommGroup M] [Module R M]
    (ℳ : AInfinityAlgebra R M) (w : ReducedTensorWords R M) :
    letter R M (ℳ.barDifferential w) = ℳ.taylor w :=
  LinearMap.congr_fun ℳ.letter_comp_barDifferential w

private theorem letter_coalgHom_apply {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (φ : ReducedTensorWords R M →ₗ[R] N)
    (w : ReducedTensorWords R M) :
    letter R N (coalgHom R φ w) = φ w :=
  LinearMap.congr_fun (letter_comp_coalgHom φ) w

private theorem letter_gradedCoderivAlong_apply {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) (w : ReducedTensorWords R M) :
    letter R N (gradedCoderivAlong G q F F' h w) = h w :=
  LinearMap.congr_fun (letter_comp_gradedCoderivAlong G q F F' h) w

private theorem letter_barMap_apply {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ℳ : AInfinityAlgebra R M} {𝒩 : AInfinityAlgebra R N}
    (φ : AInfinityHom ℳ 𝒩) (w : ReducedTensorWords R M) :
    letter R N (φ.barMap w) = φ.taylor w :=
  (LinearMap.congr_fun φ.taylor_def w).symm

private theorem barDifferential_barDifferential_apply {M : Type*} [AddCommGroup M] [Module R M]
    (ℳ : AInfinityAlgebra R M) (w : ReducedTensorWords R M) :
    ℳ.barDifferential (ℳ.barDifferential w) = 0 := by
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun ℳ.barDifferential_sq w

/-- Projecting onto words of length one and then taking single letters is `letter`. -/
private theorem letter_comp_lengthProj_one (M : Type*) [AddCommMonoid M] [Module R M] :
    letter R M ∘ₗ lengthProj R M (1 : {n : ℕ // 0 < n}) = letter R M := by
  refine linearMap_ext R M fun k x ↦ ?_
  rw [LinearMap.comp_apply]
  by_cases hk : k = (1 : {n : ℕ // 0 < n})
  · subst hk
    rw [lengthProj_of_self]
  · rw [lengthProj_of_of_ne R M hk, map_zero, letter_of_of_ne_one R M hk]

/-- The unary bar differential commutes with every word-length projection. -/
private theorem lengthProj_comp_unaryBarDifferential (ℳ : AInfinityAlgebra R A)
    (n : {n : ℕ // 0 < n}) :
    lengthProj R A n ∘ₗ ℳ.unaryBarDifferential = ℳ.unaryBarDifferential ∘ₗ lengthProj R A n := by
  rw [ℳ.unaryBarDifferential_eq_gradedCoderiv]
  exact lengthProj_comp_gradedCoderiv (ℳ.grading.shift 1) 1
    (by rw [LinearMap.comp_assoc, letter_comp_lengthProj_one]) rfl

/-- If `D` vanishes on `filtration R A k`, precomposing `D ∘ b` with `lengthProj (k + 1)` replaces
the full bar differential `b` by `unaryBarDifferential` and commutes `lengthProj` past it. -/
private theorem apply_barDifferential_lengthProj_eq {P : Type*} [AddCommGroup P] [Module R P]
    (ℳ : AInfinityAlgebra R A) {D : ReducedTensorWords R A →ₗ[R] P} {k : ℕ}
    (hD₀ : ∀ u ∈ filtration R A k, D u = 0) (w : ReducedTensorWords R A) :
    D (ℳ.barDifferential (lengthProj R A ⟨k + 1, k.succ_pos⟩ w)) =
      D (lengthProj R A ⟨k + 1, k.succ_pos⟩ (ℳ.unaryBarDifferential w)) := by
  set p := lengthProj R A ⟨k + 1, k.succ_pos⟩
  have hhigh : ℳ.higherBarDifferential (p w) ∈ filtration R A k :=
    ℳ.higherBarDifferential_filtration k
      ⟨p w, lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w, rfl⟩
  have hcomm := LinearMap.congr_fun (lengthProj_comp_unaryBarDifferential ℳ ⟨k + 1, k.succ_pos⟩) w
  rw [ℳ.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, hD₀ _ hhigh, add_zero,
    ← LinearMap.comp_apply p, hcomm, LinearMap.comp_apply]

/-- Perturbing Taylor components `g` by `δg` vanishing on `filtration R B k` leaves `coalgHom`
unchanged on `filtration R B k` and adds `ofLetter (δg z)` on `filtration R B (k + 1)`. -/
private theorem coalgHom_add_apply_of_mem_filtration (G : InternalGrading R B ℤ)
    {g δg : ReducedTensorWords R B →ₗ[R] A} {k : ℕ}
    (hδ : ∀ u ∈ filtration R B k, δg u = 0) :
    (∀ u ∈ filtration R B k, coalgHom R (g + δg) u = coalgHom R g u) ∧
      ∀ z ∈ filtration R B (k + 1),
        coalgHom R (g + δg) z = coalgHom R g z + ofLetter R A (δg z) := by
  have hk : ∀ u ∈ filtration R B k, coalgHom R (g + δg) u = coalgHom R g u := fun u hu ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ by
        rw [letter_coalgHom_apply, letter_coalgHom_apply, LinearMap.add_apply, hδ w hw, add_zero])
      hu
  refine ⟨hk, fun z hz ↦ ?_⟩
  have hsub := ((isCoalgHom_coalgHom (R := R) (g + δg)).isGradedCoderivationAlong_sub
    (G := G) (isCoalgHom_coalgHom g)).apply_eq_ofLetter_letter_of_mem_filtration
    (fun w hw ↦ by rw [LinearMap.sub_apply, hk w hw, sub_self]) hz
  rw [LinearMap.sub_apply, map_sub, letter_coalgHom_apply, letter_coalgHom_apply,
    LinearMap.add_apply, add_sub_cancel_left] at hsub
  exact eq_add_of_sub_eq' hsub

/-- Perturbing Taylor components `h` by `δh` vanishing on `filtration R M k`, while changing the
left coalgebra morphism only above `filtration R M k`, leaves `gradedCoderivAlong` unchanged on
`filtration R M k` and adds `ofLetter (δh z)` on `filtration R M (k + 1)`. -/
private theorem gradedCoderivAlong_add_apply_of_mem_filtration
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (G : InternalGrading R M ℤ) (q : ℤ)
    {F₁ F₂ F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₁ : IsCoalgHom R F₁) (hF₂ : IsCoalgHom R F₂) (hF' : IsCoalgHom R F')
    {h δh : ReducedTensorWords R M →ₗ[R] N} {k : ℕ}
    (hF : ∀ u ∈ filtration R M k, F₁ u = F₂ u)
    (hδ : ∀ u ∈ filtration R M k, δh u = 0) :
    (∀ u ∈ filtration R M k,
        gradedCoderivAlong G q F₁ F' (h + δh) u = gradedCoderivAlong G q F₂ F' h u) ∧
      ∀ z ∈ filtration R M (k + 1),
        gradedCoderivAlong G q F₁ F' (h + δh) z =
          gradedCoderivAlong G q F₂ F' h z + ofLetter R N (δh z) := by
  have hD₁₂ : ∀ z ∈ filtration R M (k + 1),
      gradedCoderivAlong G q F₁ F' (h + δh) z = gradedCoderivAlong G q F₂ F' (h + δh) z :=
    fun z hz ↦
      (isGradedCoderivationAlong_gradedCoderivAlong G q hF₁ hF' _).apply_eq_of_mem_filtration
        (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF' _)
        (fun w hw ↦ hF w (by simpa only [Nat.add_sub_cancel] using hw))
        (fun _ _ ↦ rfl)
        (fun w _ ↦ by rw [letter_gradedCoderivAlong_apply, letter_gradedCoderivAlong_apply]) hz
  have hk : ∀ u ∈ filtration R M k,
      gradedCoderivAlong G q F₂ F' (h + δh) u = gradedCoderivAlong G q F₂ F' h u :=
    fun u hu ↦
      (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF' _).apply_eq_of_mem_filtration
        (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF' _)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun w hw ↦ by
          rw [letter_gradedCoderivAlong_apply, letter_gradedCoderivAlong_apply,
            LinearMap.add_apply, hδ w hw, add_zero]) hu
  refine ⟨fun u hu ↦ (hD₁₂ u (filtration_monotone R M k.le_succ hu)).trans (hk u hu), fun z hz ↦ ?_⟩
  have hsub := ((isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF' (h + δh)).sub
    (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF'
      h)).apply_eq_ofLetter_letter_of_mem_filtration
    (fun w hw ↦ by rw [LinearMap.sub_apply, hk w hw, sub_self]) hz
  rw [LinearMap.sub_apply, map_sub, letter_gradedCoderivAlong_apply,
    letter_gradedCoderivAlong_apply, LinearMap.add_apply, add_sub_cancel_left] at hsub
  rw [hD₁₂ z hz, eq_add_of_sub_eq' hsub]

/-! #### Parametric linear obstruction solver -/

/-- First component `δg = γ - g₁ ∘ (Ψ + f₁ ∘ γ)` (with `γ = h_A ∘ Φ - g₁ ∘ Ψ`) solving the coupled
linear obstruction system `d_A ∘ δg - δg ∘ d_W = -Φ` and `f₁ ∘ δg - (d_B ∘ δh + δh ∘ d_W) = -Ψ`. -/
private def solveStepG {W : Type*} [AddCommGroup W] [Module R W]
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] A :=
  (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ) -
    e.inv ∘ₗ (Ψ + e.hom ∘ₗ (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ))

/-- Second component `δh = -h_B ∘ (Ψ + f₁ ∘ γ)` of the coupled linear obstruction solver. -/
private def solveStepH {W : Type*} [AddCommGroup W] [Module R W]
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] B :=
  -(e.homotopyHomInv ∘ₗ (Ψ + e.hom ∘ₗ (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ)))

private theorem solveStepG_apply_eq_zero {W : Type*} [AddCommGroup W] [Module R W]
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {u : W} (hΦ : Φ u = 0) (hΨ : Ψ u = 0) :
    solveStepG e Φ Ψ u = 0 := by
  simp only [solveStepG, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    hΦ, hΨ, map_zero, sub_zero, add_zero]

private theorem solveStepH_apply_eq_zero {W : Type*} [AddCommGroup W] [Module R W]
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {u : W} (hΦ : Φ u = 0) (hΨ : Ψ u = 0) :
    solveStepH e Φ Ψ u = 0 := by
  simp only [solveStepH, LinearMap.neg_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, hΦ, hΨ, map_zero, sub_zero, add_zero, neg_zero]

private theorem isHomogeneous_solveStepG {W : Type*} [AddCommGroup W] [Module R W]
    {𝒲 : ℤ → Submodule R W} {e : LinearHomotopyEquiv AA.differential BB.differential}
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) {r : ℤ}
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 (AA.grading.shift 1).piece (r + 1))
    (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 (BB.grading.shift 1).piece r) :
    LinearMap.IsHomogeneous (solveStepG e Φ Ψ) 𝒲 (AA.grading.shift 1).piece r := by
  rw [solveStepG]
  have hγ : LinearMap.IsHomogeneous (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ) 𝒲
      (AA.grading.shift 1).piece r := by
    refine LinearMap.IsHomogeneous.sub ?_ ?_
    · simpa only [add_neg_cancel_right] using (isHomogeneous_shift_one hG.homotopyInvHom).comp hΦ
    · simpa only [add_zero] using (isHomogeneous_shift_one hG.inv).comp hΨ
  have hZ : LinearMap.IsHomogeneous (Ψ + e.hom ∘ₗ (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ)) 𝒲
      (BB.grading.shift 1).piece r := by
    refine hΨ.add ?_
    simpa only [add_zero] using (isHomogeneous_shift_one hG.hom).comp hγ
  refine hγ.sub ?_
  simpa only [add_zero] using (isHomogeneous_shift_one hG.inv).comp hZ

private theorem isHomogeneous_solveStepH {W : Type*} [AddCommGroup W] [Module R W]
    {𝒲 : ℤ → Submodule R W} {e : LinearHomotopyEquiv AA.differential BB.differential}
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) {r : ℤ}
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 (AA.grading.shift 1).piece (r + 1))
    (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 (BB.grading.shift 1).piece r) :
    LinearMap.IsHomogeneous (solveStepH e Φ Ψ) 𝒲 (BB.grading.shift 1).piece (r + -1) := by
  rw [solveStepH]
  have hγ : LinearMap.IsHomogeneous (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ) 𝒲
      (AA.grading.shift 1).piece r := by
    refine LinearMap.IsHomogeneous.sub ?_ ?_
    · simpa only [add_neg_cancel_right] using (isHomogeneous_shift_one hG.homotopyInvHom).comp hΦ
    · simpa only [add_zero] using (isHomogeneous_shift_one hG.inv).comp hΨ
  have hZ : LinearMap.IsHomogeneous (Ψ + e.hom ∘ₗ (e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ)) 𝒲
      (BB.grading.shift 1).piece r := by
    refine hΨ.add ?_
    simpa only [add_zero] using (isHomogeneous_shift_one hG.hom).comp hγ
  exact ((isHomogeneous_shift_one hG.homotopyHomInv).comp hZ).neg

private theorem solveStep_gamma_eqs {W : Type*} [AddCommGroup W] [Module R W]
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    {dW : Module.End R W} {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + Φ ∘ₗ dW = 0)
    (hΨ : BB.differential ∘ₗ Ψ - Ψ ∘ₗ dW = e.hom ∘ₗ Φ) (w : W) :
    let γ := e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ
    let Z := Ψ + e.hom ∘ₗ γ
    (AA.differential (γ w) - γ (dW w) = -Φ w) ∧ BB.differential (Z w) = Z (dW w) := by
  intro γ Z
  have hΦw : Φ (dW w) = -AA.differential (Φ w) :=
    eq_neg_of_add_eq_zero_right (by simpa using LinearMap.congr_fun hΦ w)
  have hΨw' : BB.differential (Ψ w) - Ψ (dW w) = e.hom (Φ w) := by
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using LinearMap.congr_fun hΨ w
  have hΨw : Ψ (dW w) = BB.differential (Ψ w) - e.hom (Φ w) := by
    rw [← hΨw']; abel
  have hinv := LinearMap.congr_fun e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM (Φ w)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hinv
  have hγ : AA.differential (γ w) - γ (dW w) = -Φ w := by
    simp only [γ, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hΦw, hΨw, map_neg,
      e.dM_inv_apply]
    rw [eq_sub_of_add_eq hinv]
    abel
  refine ⟨hγ, sub_eq_zero.1 ?_⟩
  simp only [Z, LinearMap.add_apply, LinearMap.comp_apply, map_add, e.dN_hom_apply]
  rw [show BB.differential (Ψ w) + e.hom (AA.differential (γ w)) -
      (Ψ (dW w) + e.hom (γ (dW w))) =
      (BB.differential (Ψ w) - Ψ (dW w)) + e.hom (AA.differential (γ w) - γ (dW w)) by
    rw [map_sub]; abel, hΨw', hγ, map_neg, add_neg_cancel]

private theorem solveStep_eqs {W : Type*} [AddCommGroup W] [Module R W]
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    {dW : Module.End R W} {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + Φ ∘ₗ dW = 0)
    (hΨ : BB.differential ∘ₗ Ψ - Ψ ∘ₗ dW = e.hom ∘ₗ Φ) :
    (AA.differential ∘ₗ solveStepG e Φ Ψ - solveStepG e Φ Ψ ∘ₗ dW = -Φ) ∧
      (e.hom ∘ₗ solveStepG e Φ Ψ -
        (BB.differential ∘ₗ solveStepH e Φ Ψ + solveStepH e Φ Ψ ∘ₗ dW) = -Ψ) := by
  set γ : W →ₗ[R] A := e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ
  set Z : W →ₗ[R] B := Ψ + e.hom ∘ₗ γ
  refine ⟨LinearMap.ext fun w ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨hγ, hZ⟩ := solveStep_gamma_eqs e hΦ hΨ w
    simp only [solveStepG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply]
    change AA.differential (γ w - e.inv (Z w)) - (γ (dW w) - e.inv (Z (dW w))) = -Φ w
    rw [map_sub, e.dM_inv_apply, hZ, sub_sub_sub_comm, sub_self, sub_zero, hγ]
  · obtain ⟨_, hZ⟩ := solveStep_gamma_eqs e hΦ hΨ w
    simp only [solveStepG, solveStepH, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.neg_apply, LinearMap.comp_apply]
    change e.hom (γ w - e.inv (Z w)) -
      (BB.differential (-(e.homotopyHomInv (Z w))) + -(e.homotopyHomInv (Z (dW w)))) = -Ψ w
    have hhom := LinearMap.congr_fun e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN (Z w)
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hhom
    rw [map_sub, map_neg, ← hZ, ← neg_add, hhom]
    dsimp only [Z, LinearMap.add_apply, LinearMap.comp_apply]
    abel

/-! #### Stage 1: lifting the right homotopy inverse -/

/-- Data at stage `k` of the right-inverse induction: suspended Taylor components `gTaylor` (degree
`0`) and `hTaylor` (degree `-1`) whose bar expansions satisfy the morphism and right-homotopy
equations on `filtration R B k`. -/
private structure RightStage (f : AInfinityHom AA BB) (k : ℕ) where
  gTaylor : ReducedTensorWords R B →ₗ[R] A
  hTaylor : ReducedTensorWords R B →ₗ[R] B
  hg : LinearMap.IsHomogeneous gTaylor (gradedPiece (BB.grading.shift 1))
    (AA.grading.shift 1).piece 0
  hh : LinearMap.IsHomogeneous hTaylor (gradedPiece (BB.grading.shift 1))
    (BB.grading.shift 1).piece (-1)
  hE : ∀ z ∈ filtration R B k,
    (AA.barDifferential ∘ₗ coalgHom R gTaylor - coalgHom R gTaylor ∘ₗ BB.barDifferential) z = 0
  hD : ∀ z ∈ filtration R B k,
    ((f.barMap ∘ₗ coalgHom R gTaylor - (LinearMap.id : Module.End R (ReducedTensorWords R B))) -
      (BB.barDifferential ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R gTaylor) LinearMap.id hTaylor +
        gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R gTaylor) LinearMap.id hTaylor ∘ₗ BB.barDifferential)) z = 0

private noncomputable abbrev RightStage.barMap {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  coalgHom R S.gTaylor

private noncomputable abbrev RightStage.barHomotopy {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) : Module.End R (ReducedTensorWords R B) :=
  gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ S.barMap) LinearMap.id S.hTaylor

private noncomputable abbrev RightStage.defectE {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) : ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ S.barMap - S.barMap ∘ₗ BB.barDifferential

private noncomputable abbrev RightStage.defectD {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) : Module.End R (ReducedTensorWords R B) :=
  (f.barMap ∘ₗ S.barMap - LinearMap.id) -
    (BB.barDifferential ∘ₗ S.barHomotopy + S.barHomotopy ∘ₗ BB.barDifferential)

private noncomputable abbrev RightStage.obstructionΦ {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) : ReducedTensorWords R B →ₗ[R] A :=
  letter R A ∘ₗ S.defectE ∘ₗ lengthProj R B ⟨k + 1, k.succ_pos⟩

private noncomputable abbrev RightStage.obstructionΨ {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) : ReducedTensorWords R B →ₗ[R] B :=
  letter R B ∘ₗ S.defectD ∘ₗ lengthProj R B ⟨k + 1, k.succ_pos⟩

/-- Trivial stage `k = 0` sharing the arity-one Taylor maps of `rightStageOne`. -/
private noncomputable def rightStageZero (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) : RightStage f 0 where
  gTaylor := e.inv ∘ₗ letter R B
  hTaylor := e.homotopyHomInv ∘ₗ letter R B
  hg := by
    simpa only [zero_add] using
      (isHomogeneous_shift_one hG.inv).comp (isHomogeneous_letter (BB.grading.shift 1))
  hh := by
    simpa only [zero_add] using
      (isHomogeneous_shift_one hG.homotopyHomInv).comp (isHomogeneous_letter (BB.grading.shift 1))
  hE z hz := by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]
  hD z hz := by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]

/-- Base stage `k = 1` of the right-inverse induction, built from `e.inv` and `e.homotopyHomInv`. -/
private noncomputable def rightStageOne (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) : RightStage f 1 where
  gTaylor := e.inv ∘ₗ letter R B
  hTaylor := e.homotopyHomInv ∘ₗ letter R B
  hg := (rightStageZero f e hG).hg
  hh := (rightStageZero f e hG).hh
  hE := by
    refine apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, coalgHom_ofLetter, letter_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      e.dM_inv_apply, sub_self, LinearMap.zero_apply]
  hD := by
    refine apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_)
    have hB := LinearMap.congr_fun e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN b
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, he] at hB
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
      coalgHom_ofLetter, gradedCoderivAlong_ofLetter, letter_ofLetter, f.barMap_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      ← map_add, ← map_sub, hB, sub_self, LinearMap.zero_apply]

/-- On `filtration R B (k + 1)`, both defects of a `RightStage f k` are single letters. -/
private theorem rightStage_defects_eq_ofLetter {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (k + 1)) :
    S.defectE z = ofLetter R A (letter R A (S.defectE z)) ∧
      S.defectD z = ofLetter R B (letter R B (S.defectD z)) := by
  have hGc : IsCoalgHom R S.barMap := isCoalgHom_coalgHom S.gTaylor
  have hGh : LinearMap.IsHomogeneous S.barMap (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 := isHomogeneous_coalgHom S.hg
  have hEc : IsGradedCoderivationAlong (BB.grading.shift 1) 1 S.barMap S.barMap S.defectE :=
    (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hGc hGh).sub
      (hGc.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential)
  refine ⟨hEc.apply_eq_ofLetter_letter_of_mem_filtration S.hE hz, ?_⟩
  have hFGh : LinearMap.IsHomogeneous (f.barMap ∘ₗ S.barMap) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hGh
  have hKc : IsGradedCoderivationAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ S.barMap) LinearMap.id
      S.barHomotopy :=
    isGradedCoderivationAlong_gradedCoderivAlong _ 1 (f.isCoalgHom_barMap.comp hGc)
      (isCoalgHom_id B) S.hTaylor
  have hKh : LinearMap.IsHomogeneous S.barHomotopy (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) :=
    isHomogeneous_gradedCoderivAlong (q := 1) hFGh (LinearMap.isHomogeneous_id _) S.hh
  have hFG_int : ∀ w ∈ filtration R B k,
      BB.barDifferential ((f.barMap ∘ₗ S.barMap) w) =
        (f.barMap ∘ₗ S.barMap) (BB.barDifferential w) := fun w hw ↦ by
    simp only [LinearMap.comp_apply, f.barDifferential_barMap]
    exact congrArg f.barMap (sub_eq_zero.1 (S.hE w hw))
  have hΔ₁ := ((f.isCoalgHom_barMap.comp hGc).isGradedCoderivationAlong_sub
    (G := BB.grading.shift 1) (isCoalgHom_id B)).deconcatenation_apply z
  have hΔ₂ := hKc.deconcatenation_comp_add_comp_of_mem_filtration hKh (by decide)
    BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential hFGh hFG_int (fun _ _ ↦ rfl) hz
  refine eq_ofLetter_letter_of_deconcatenation_eq_of_mem_filtration (BB.grading.shift 1) 0
    (F := f.barMap ∘ₗ S.barMap) (F' := LinearMap.id) (D := S.defectD) S.hD hz ?_
  simp only [InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.id_apply] at hΔ₁ ⊢
  rw [LinearMap.sub_apply, map_sub, hΔ₁, hΔ₂, sub_eq_iff_eq_add, add_add_add_comm]
  have hcancel : S.defectD +
      (BB.barDifferential ∘ₗ S.barHomotopy + S.barHomotopy ∘ₗ BB.barDifferential) =
      f.barMap ∘ₗ S.barMap - LinearMap.id := LinearMap.ext fun _ ↦ sub_add_cancel _ _
  simp only [← LinearMap.add_apply, ← TensorProduct.map_add_left, ← TensorProduct.map_add_right,
    hcancel]

/-- The length-`(k + 1)` obstruction components `Φ` and `Ψ` of a `RightStage f k` satisfy the
coupled linear differential equations over `BB.unaryBarDifferential`. -/
private theorem rightStage_obstruction_eqs {f : AInfinityHom AA BB} {k : ℕ} (S : RightStage f k) :
    (AA.differential ∘ₗ S.obstructionΦ + S.obstructionΦ ∘ₗ BB.unaryBarDifferential = 0) ∧
      (BB.differential ∘ₗ S.obstructionΨ - S.obstructionΨ ∘ₗ BB.unaryBarDifferential =
        f.linearPart ∘ₗ S.obstructionΦ) := by
  set p := lengthProj R B ⟨k + 1, k.succ_pos⟩
  have hAE (u : ReducedTensorWords R B) :
      AA.barDifferential (S.defectE u) + S.defectE (BB.barDifferential u) = 0 := by
    simp only [RightStage.defectE, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      barDifferential_barDifferential_apply, map_zero]
    abel
  have hBD (u : ReducedTensorWords R B) :
      BB.barDifferential (S.defectD u) - S.defectD (BB.barDifferential u) =
        f.barMap (S.defectE u) := by
    simp only [RightStage.defectD, RightStage.defectE, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap,
      barDifferential_barDifferential_apply, map_zero]
    abel
  refine ⟨LinearMap.ext fun w ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · have hEp := (rightStage_defects_eq_ofLetter S
      (lengthProj_mem_filtration R B ⟨k + 1, k.succ_pos⟩ w)).1
    have hcomm := apply_barDifferential_lengthProj_eq BB
      (D := letter R A ∘ₗ S.defectE)
      (fun u hu ↦ by rw [LinearMap.comp_apply, S.hE u hu, map_zero]) w
    have hzero := hAE (p w)
    rw [hEp, AInfinityAlgebra.barDifferential_ofLetter] at hzero
    have hzero' := congrArg (letter R A) hzero
    rw [map_add, map_zero, letter_ofLetter, ← AInfinityAlgebra.differential_apply] at hzero'
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [hcomm] at hzero'
    simpa only [RightStage.obstructionΦ, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] using hzero'
  · have hdef := rightStage_defects_eq_ofLetter S
      (lengthProj_mem_filtration R B ⟨k + 1, k.succ_pos⟩ w)
    have hcomm := apply_barDifferential_lengthProj_eq BB
      (D := letter R B ∘ₗ S.defectD)
      (fun u hu ↦ by rw [LinearMap.comp_apply, S.hD u hu, map_zero]) w
    have hrel := hBD (p w)
    rw [hdef.2, hdef.1, AInfinityAlgebra.barDifferential_ofLetter, f.barMap_ofLetter] at hrel
    have hrel' := congrArg (letter R B) hrel
    rw [map_sub, letter_ofLetter, letter_ofLetter, ← AInfinityAlgebra.differential_apply] at hrel'
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [hcomm] at hrel'
    simpa only [RightStage.obstructionΦ, RightStage.obstructionΨ, LinearMap.sub_apply,
      LinearMap.comp_apply] using hrel'

private theorem rightStage_isHomogeneous_obstructions {f : AInfinityHom AA BB} {k : ℕ}
    (S : RightStage f k) :
    LinearMap.IsHomogeneous S.obstructionΦ (gradedPiece (BB.grading.shift 1))
        (AA.grading.shift 1).piece (0 + 1) ∧
      LinearMap.IsHomogeneous S.obstructionΨ (gradedPiece (BB.grading.shift 1))
        (BB.grading.shift 1).piece 0 := by
  have hGh : LinearMap.IsHomogeneous S.barMap (gradedPiece (BB.grading.shift 1))
      (gradedPiece (AA.grading.shift 1)) 0 := isHomogeneous_coalgHom S.hg
  have hFGh : LinearMap.IsHomogeneous (f.barMap ∘ₗ S.barMap) (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hGh
  refine ⟨?_, ?_⟩
  · have hEh : LinearMap.IsHomogeneous S.defectE (gradedPiece (BB.grading.shift 1))
        (gradedPiece (AA.grading.shift 1)) 1 := by
      refine LinearMap.IsHomogeneous.sub ?_ ?_
      · simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp hGh
      · simpa only [add_zero] using hGh.comp BB.isHomogeneous_barDifferential
    simpa only [zero_add, add_zero] using
      (isHomogeneous_letter _).comp (hEh.comp (isHomogeneous_lengthProj _ _))
  · have hKh := isHomogeneous_gradedCoderivAlong (q := 1) hFGh (LinearMap.isHomogeneous_id _) S.hh
    have hDh : LinearMap.IsHomogeneous S.defectD (gradedPiece (BB.grading.shift 1))
        (gradedPiece (BB.grading.shift 1)) 0 := by
      refine (hFGh.sub (LinearMap.isHomogeneous_id _)).sub ?_
      refine LinearMap.IsHomogeneous.add ?_ ?_
      · simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp hKh
      · simpa only [add_neg_cancel] using hKh.comp BB.isHomogeneous_barDifferential
    simpa only [add_zero] using
      (isHomogeneous_letter _).comp (hDh.comp (isHomogeneous_lengthProj _ _))

private theorem rightStageSucc_hE {f : AInfinityHom AA BB} {k : ℕ} (S : RightStage f k)
    {δg : ReducedTensorWords R B →ₗ[R] A} (hδg₀ : ∀ u ∈ filtration R B k, δg u = 0)
    (hsol₁ : AA.differential ∘ₗ δg - δg ∘ₗ BB.unaryBarDifferential = -S.obstructionΦ)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (k + 1)) :
    (AA.barDifferential ∘ₗ coalgHom R (S.gTaylor + δg) -
      coalgHom R (S.gTaylor + δg) ∘ₗ BB.barDifferential) z = 0 := by
  have hG_step := coalgHom_add_apply_of_mem_filtration (BB.grading.shift 1) (g := S.gTaylor) hδg₀
  have hhigh : BB.higherBarDifferential z ∈ filtration R B k :=
    BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have hunary : BB.unaryBarDifferential z ∈ filtration R B (k + 1) :=
    BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩
  have hEz : AA.barDifferential (S.barMap z) - S.barMap (BB.barDifferential z) =
      ofLetter R A (S.obstructionΦ z) :=
    (rightStage_defects_eq_ofLetter S hz).1.trans (congrArg (ofLetter R A)
      (apply_lengthProj_of_mem_filtration R B (f := letter R A ∘ₗ S.defectE)
        (fun u hu ↦ by rw [LinearMap.comp_apply, S.hE u hu, map_zero]) hz).symm)
  have hGz : coalgHom R (S.gTaylor + δg) (BB.barDifferential z) =
      S.barMap (BB.barDifferential z) + ofLetter R A (δg (BB.unaryBarDifferential z)) := by
    rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
      hG_step.2 _ hunary, hG_step.1 _ hhigh]
    abel
  have hsol₁z : AA.differential (δg z) - δg (BB.unaryBarDifferential z) = -S.obstructionΦ z := by
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply] using
      LinearMap.congr_fun hsol₁ z
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hG_step.2 z hz, hGz,
    map_add, AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    eq_add_of_sub_eq hEz, eq_add_of_sub_eq hsol₁z, map_add, map_neg]
  abel

private theorem rightStageSucc_hD {f : AInfinityHom AA BB} {k : ℕ} (S : RightStage f k)
    {δg : ReducedTensorWords R B →ₗ[R] A} {δh : ReducedTensorWords R B →ₗ[R] B}
    (hδg₀ : ∀ u ∈ filtration R B k, δg u = 0) (hδh₀ : ∀ u ∈ filtration R B k, δh u = 0)
    (hsol₂ : f.linearPart ∘ₗ δg -
      (BB.differential ∘ₗ δh + δh ∘ₗ BB.unaryBarDifferential) = -S.obstructionΨ)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (k + 1)) :
    ((f.barMap ∘ₗ coalgHom R (S.gTaylor + δg) -
        (LinearMap.id : Module.End R (ReducedTensorWords R B))) -
      (BB.barDifferential ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R (S.gTaylor + δg)) LinearMap.id (S.hTaylor + δh) +
        gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ coalgHom R (S.gTaylor + δg)) LinearMap.id (S.hTaylor + δh) ∘ₗ
          BB.barDifferential)) z = 0 := by
  have hG_step := coalgHom_add_apply_of_mem_filtration (BB.grading.shift 1) (g := S.gTaylor) hδg₀
  have hK_step := gradedCoderivAlong_add_apply_of_mem_filtration (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (S.gTaylor + δg)))
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.gTaylor)) (isCoalgHom_id B)
    (h := S.hTaylor) (fun u hu ↦ congrArg f.barMap (hG_step.1 u hu)) hδh₀
  have hhigh : BB.higherBarDifferential z ∈ filtration R B k :=
    BB.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have hunary : BB.unaryBarDifferential z ∈ filtration R B (k + 1) :=
    BB.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩
  have hDz : (f.barMap (S.barMap z) - z) -
      (BB.barDifferential (S.barHomotopy z) + S.barHomotopy (BB.barDifferential z)) =
      ofLetter R B (S.obstructionΨ z) :=
    (rightStage_defects_eq_ofLetter S hz).2.trans (congrArg (ofLetter R B)
      (apply_lengthProj_of_mem_filtration R B (f := letter R B ∘ₗ S.defectD)
        (fun u hu ↦ by rw [LinearMap.comp_apply, S.hD u hu, map_zero]) hz).symm)
  have hKz : gradedCoderivAlong (BB.grading.shift 1) 1
      (f.barMap ∘ₗ coalgHom R (S.gTaylor + δg)) LinearMap.id (S.hTaylor + δh)
      (BB.barDifferential z) =
      S.barHomotopy (BB.barDifferential z) + ofLetter R B (δh (BB.unaryBarDifferential z)) := by
    rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
      hK_step.2 _ hunary, hK_step.1 _ hhigh]
    abel
  have hsol₂z : f.linearPart (δg z) -
      (BB.differential (δh z) + δh (BB.unaryBarDifferential z)) = -S.obstructionΨ z := by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.neg_apply] using LinearMap.congr_fun hsol₂ z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [hG_step.2 z hz, hK_step.2 z hz, hKz, map_add, map_add, f.barMap_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    eq_add_of_sub_eq (eq_add_of_sub_eq hDz), eq_add_of_sub_eq hsol₂z, map_add, map_add, map_neg]
  abel

/-- Inductive step of the right-inverse construction: lift a `RightStage f k` to
`RightStage f (k + 1)` without changing the Taylor components on `filtration R B k`. -/
private noncomputable def rightStageSucc (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) {k : ℕ}
    (S : RightStage f k) :
    {S' : RightStage f (k + 1) //
      (∀ z ∈ filtration R B k, S'.gTaylor z = S.gTaylor z) ∧
        (∀ z ∈ filtration R B k, S'.hTaylor z = S.hTaylor z)} := by
  set δg := solveStepG e S.obstructionΦ S.obstructionΨ
  set δh := solveStepH e S.obstructionΦ S.obstructionΨ
  have hp₀ : ∀ u ∈ filtration R B k, lengthProj R B ⟨k + 1, k.succ_pos⟩ u = 0 := fun u hu ↦
    lengthProj_apply_eq_zero_of_mem_filtration R B (Nat.lt_succ_self k) hu
  have hδg₀ : ∀ u ∈ filtration R B k, δg u = 0 := fun u hu ↦
    solveStepG_apply_eq_zero e
      (by simp only [RightStage.obstructionΦ, LinearMap.comp_apply, hp₀ u hu, map_zero])
      (by simp only [RightStage.obstructionΨ, LinearMap.comp_apply, hp₀ u hu, map_zero])
  have hδh₀ : ∀ u ∈ filtration R B k, δh u = 0 := fun u hu ↦
    solveStepH_apply_eq_zero e
      (by simp only [RightStage.obstructionΦ, LinearMap.comp_apply, hp₀ u hu, map_zero])
      (by simp only [RightStage.obstructionΨ, LinearMap.comp_apply, hp₀ u hu, map_zero])
  have hdeg := rightStage_isHomogeneous_obstructions S
  have hob := rightStage_obstruction_eqs S
  have hsol := solveStep_eqs e hob.1 (by rw [he]; exact hob.2)
  refine ⟨⟨S.gTaylor + δg, S.hTaylor + δh,
    S.hg.add (isHomogeneous_solveStepG hG hdeg.1 hdeg.2),
    S.hh.add (by simpa only [zero_add] using isHomogeneous_solveStepH hG hdeg.1 hdeg.2),
    fun z hz ↦ rightStageSucc_hE S hδg₀ hsol.1 hz,
    fun z hz ↦ rightStageSucc_hD S hδg₀ hδh₀ (by rw [← he]; exact hsol.2) hz⟩,
    fun z hz ↦ by rw [LinearMap.add_apply, hδg₀ z hz, add_zero],
    fun z hz ↦ by rw [LinearMap.add_apply, hδh₀ z hz, add_zero]⟩

/-- Full `ℕ`-indexed sequence of right stages starting at `rightStageZero` and `rightStageOne`. -/
private noncomputable def rightStageNat (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    ∀ n : ℕ, RightStage f n
  | 0 => rightStageZero f e hG
  | 1 => rightStageOne f e he hG
  | m + 2 => (rightStageSucc f e he hG (rightStageNat f e he hG (m + 1))).1

private theorem rightStageNat_stabilises (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) (n : ℕ) :
    (∀ z ∈ filtration R B n,
        (rightStageNat f e he hG (n + 1)).gTaylor z = (rightStageNat f e he hG n).gTaylor z) ∧
      (∀ z ∈ filtration R B n,
        (rightStageNat f e he hG (n + 1)).hTaylor z = (rightStageNat f e he hG n).hTaylor z) := by
  cases n with
  | zero => exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | succ m =>
      exact ⟨(rightStageSucc f e he hG (rightStageNat f e he hG (m + 1))).2.1,
        (rightStageSucc f e he hG (rightStageNat f e he hG (m + 1))).2.2⟩

private noncomputable abbrev liftInvTaylor (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    ReducedTensorWords R B →ₗ[R] A :=
  stabilisingTaylor fun n ↦ (rightStageNat f e he hG n).gTaylor

/-- The lifted right-inverse `A∞` morphism `g : BB ⟶ AA`. -/
private noncomputable def liftInv (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) : AInfinityHom BB AA :=
  AInfinityHom.ofTaylor (liftInvTaylor f e he hG)
    (isHomogeneous_stabilisingTaylor (fun n ↦ (rightStageNat_stabilises f e he hG n).1)
      fun n ↦ (rightStageNat f e he hG n).hg)
    (LinearMap.ext fun z ↦ by
      have hstab := fun n ↦ (rightStageNat_stabilises f e he hG n).1
      obtain ⟨m, hm⟩ := exists_mem_filtration R B z
      have hz : z ∈ filtration R B (m + 1) := filtration_monotone R B m.le_succ hm
      have hG_eq : coalgHom R (liftInvTaylor f e he hG) z =
          coalgHom R (rightStageNat f e he hG (m + 1)).gTaylor z :=
        (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
          (fun u hu ↦ by
            rw [letter_coalgHom_apply, letter_coalgHom_apply,
              stabilisingTaylor_apply_of_mem_filtration hstab hu]) hz
      have hE := congrArg (letter R A) ((rightStageNat f e he hG (m + 1)).hE z hz)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub, map_zero, sub_eq_zero] at hE
      rw [letter_barDifferential_apply, letter_coalgHom_apply] at hE
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hG_eq,
        stabilisingTaylor_apply_of_mem_filtration hstab (BB.barDifferential_mem_filtration hz),
        hE])

private theorem linearPart_liftInv (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    (liftInv f e he hG).linearPart = e.inv := by
  have hstab := fun n ↦ (rightStageNat_stabilises f e he hG n).1
  refine LinearMap.ext fun b ↦ ?_
  rw [linearPart_apply, liftInv, AInfinityHom.taylor_ofTaylor,
    stabilisingTaylor_apply_of_mem_filtration hstab (ofLetter_mem_filtration R B b)]
  exact congrArg e.inv (letter_ofLetter R B b)

private noncomputable abbrev liftRightHomotopyTaylor (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    ReducedTensorWords R B →ₗ[R] B :=
  stabilisingTaylor fun n ↦ (rightStageNat f e he hG n).hTaylor

/-- The lifted right homotopy `f ∘ liftInv ⇒ id_B`. -/
private noncomputable def liftRightHomotopy (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    Homotopy (f.comp (liftInv f e he hG)) (AInfinityHom.id BB) :=
  Homotopy.ofTaylor (liftRightHomotopyTaylor f e he hG)
    (isHomogeneous_stabilisingTaylor (fun n ↦ (rightStageNat_stabilises f e he hG n).2)
      fun n ↦ (rightStageNat f e he hG n).hh)
    (LinearMap.ext fun z ↦ by
      set g := liftInv f e he hG with hg_def
      have hg_stab := fun n ↦ (rightStageNat_stabilises f e he hG n).1
      have hh_stab := fun n ↦ (rightStageNat_stabilises f e he hG n).2
      obtain ⟨m, hm⟩ := exists_mem_filtration R B z
      have hz : z ∈ filtration R B (m + 1) := filtration_monotone R B m.le_succ hm
      have hG_eq : ∀ w ∈ filtration R B (m + 1),
          g.barMap w = coalgHom R (rightStageNat f e he hG (m + 1)).gTaylor w :=
        fun w hw ↦ g.isCoalgHom_barMap.apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
          (fun u hu ↦ by
            rw [letter_barMap_apply, letter_coalgHom_apply, hg_def, liftInv,
              AInfinityHom.taylor_ofTaylor, stabilisingTaylor_apply_of_mem_filtration hg_stab hu])
          hw
      have hK_eq : gradedCoderivAlong (BB.grading.shift 1) 1 (f.comp g).barMap
          (AInfinityHom.id BB).barMap (liftRightHomotopyTaylor f e he hG) z =
          (rightStageNat f e he hG (m + 1)).barHomotopy z :=
        (isGradedCoderivationAlong_gradedCoderivAlong _ 1 (f.comp g).isCoalgHom_barMap
          (AInfinityHom.id BB).isCoalgHom_barMap _).apply_eq_of_mem_filtration
          (isGradedCoderivationAlong_gradedCoderivAlong _ 1
            (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _)) (isCoalgHom_id B) _)
          (fun u hu ↦ by
            rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply,
              hG_eq u (filtration_monotone R B (by omega) hu)])
          (fun u _ ↦ by rw [barMap_id, LinearMap.id_apply])
          (fun u hu ↦ by
            rw [letter_gradedCoderivAlong_apply, letter_gradedCoderivAlong_apply,
              stabilisingTaylor_apply_of_mem_filtration hh_stab hu]) hz
      have hD := congrArg (letter R B) ((rightStageNat f e he hG (m + 1)).hD z hz)
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply, map_sub, map_add, map_zero, sub_eq_zero] at hD
      rw [letter_barMap_apply, letter_barDifferential_apply, letter_gradedCoderivAlong_apply] at hD
      rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        taylor_comp, LinearMap.comp_apply, taylor_id, hG_eq z hz, hK_eq,
        stabilisingTaylor_apply_of_mem_filtration hh_stab (BB.barDifferential_mem_filtration hz)]
      exact hD)

private theorem linearHomotopy_liftRightHomotopy (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    (liftRightHomotopy f e he hG).linearHomotopy = e.homotopyHomInv := by
  have hh_stab := fun n ↦ (rightStageNat_stabilises f e he hG n).2
  refine LinearMap.ext fun b ↦ ?_
  rw [liftRightHomotopy, Homotopy.linearHomotopy_ofTaylor, LinearMap.comp_apply,
    stabilisingTaylor_apply_of_mem_filtration hh_stab (ofLetter_mem_filtration R B b)]
  exact congrArg e.homotopyHomInv (letter_ofLetter R B b)

/-! #### Stage 2: lifting the left homotopy alongside a compatibility 2-homotopy -/

/-- Data at stage `k` of the left-homotopy induction, given `g : BB ⟶ AA` and
`H_B : f ∘ g ⇒ id_B`: Taylor maps `kATaylor` (degree `-1`) and `tTaylor` (degree `-2`) whose bar
expansions `K_A` and `T` satisfy the left-homotopy equation and `H_B`-compatibility equation on
`filtration R A k`. -/
private structure LeftStage (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (H_B : Homotopy (f.comp g) (AInfinityHom.id BB)) (k : ℕ) where
  kATaylor : ReducedTensorWords R A →ₗ[R] A
  tTaylor : ReducedTensorWords R A →ₗ[R] B
  hkA : LinearMap.IsHomogeneous kATaylor (gradedPiece (AA.grading.shift 1))
    (AA.grading.shift 1).piece (-1)
  ht : LinearMap.IsHomogeneous tTaylor (gradedPiece (AA.grading.shift 1))
    (BB.grading.shift 1).piece (-2)
  hM : ∀ z ∈ filtration R A k,
    (((g.comp f).barMap - (LinearMap.id : Module.End R (ReducedTensorWords R A))) -
      (AA.barDifferential ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 1
          (g.comp f).barMap LinearMap.id kATaylor +
        gradedCoderivAlong (AA.grading.shift 1) 1
          (g.comp f).barMap LinearMap.id kATaylor ∘ₗ AA.barDifferential)) z = 0
  hU : ∀ z ∈ filtration R A k,
    ((H_B.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 1
        (g.comp f).barMap LinearMap.id kATaylor) -
      (BB.barDifferential ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 0
          (f.barMap ∘ₗ (g.comp f).barMap) f.barMap tTaylor -
        gradedCoderivAlong (AA.grading.shift 1) 0
          (f.barMap ∘ₗ (g.comp f).barMap) f.barMap tTaylor ∘ₗ AA.barDifferential)) z = 0

private noncomputable abbrev LeftStage.barHomotopy {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) : Module.End R (ReducedTensorWords R A) :=
  gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap LinearMap.id S.kATaylor

private noncomputable abbrev LeftStage.barTwoHomotopy {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  gradedCoderivAlong (AA.grading.shift 1) 0 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap S.tTaylor

private noncomputable abbrev LeftStage.defectM {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) : Module.End R (ReducedTensorWords R A) :=
  ((g.comp f).barMap - LinearMap.id) -
    (AA.barDifferential ∘ₗ S.barHomotopy + S.barHomotopy ∘ₗ AA.barDifferential)

private noncomputable abbrev LeftStage.defectU {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  (H_B.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ S.barHomotopy) -
    (BB.barDifferential ∘ₗ S.barTwoHomotopy - S.barTwoHomotopy ∘ₗ AA.barDifferential)

private noncomputable abbrev LeftStage.obstructionΘ {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) : ReducedTensorWords R A →ₗ[R] A :=
  letter R A ∘ₗ S.defectM ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩

private noncomputable abbrev LeftStage.obstructionΥ {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) : ReducedTensorWords R A →ₗ[R] B :=
  letter R B ∘ₗ S.defectU ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩

/-- Base stage `k = 0` of the left-homotopy induction: `0` vanishes on `filtration R A 0 = ⊥`. -/
private noncomputable def leftStageZero (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (H_B : Homotopy (f.comp g) (AInfinityHom.id BB)) : LeftStage f g H_B 0 where
  kATaylor := 0
  tTaylor := 0
  hkA := LinearMap.isHomogeneous_zero _ _ _
  ht := LinearMap.isHomogeneous_zero _ _ _
  hM z hz := by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]
  hU z hz := by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]

/-- Both defects `defectM` and `defectU` of a `LeftStage f g H_B k` are globally coderivations
along `((g.comp f).barMap, id)` and `(f.barMap ∘ (g.comp f).barMap, f.barMap)` respectively. -/
private theorem leftStage_isGradedCoderivationAlong {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 0 (g.comp f).barMap LinearMap.id S.defectM ∧
      IsGradedCoderivationAlong (AA.grading.shift 1) 1
        (f.barMap ∘ₗ (g.comp f).barMap) f.barMap S.defectU := by
  have hKAc : IsGradedCoderivationAlong (AA.grading.shift 1) 1 (g.comp f).barMap LinearMap.id
      S.barHomotopy :=
    isGradedCoderivationAlong_gradedCoderivAlong _ 1 (g.comp f).isCoalgHom_barMap
      (isCoalgHom_id A) S.kATaylor
  have hKAh := isHomogeneous_gradedCoderivAlong (q := 1) (g.comp f).isHomogeneous_barMap
    (LinearMap.isHomogeneous_id _) S.hkA
  have hMc : IsGradedCoderivationAlong (AA.grading.shift 1) 0 (g.comp f).barMap LinearMap.id
      S.defectM :=
    ((g.comp f).isCoalgHom_barMap.isGradedCoderivationAlong_sub (isCoalgHom_id A)).sub
      (hKAc.comp_add_comp hKAh (by decide) AA.isGradedCoderivation_barDifferential
        AA.isHomogeneous_barDifferential (by decide) AA.isGradedCoderivation_barDifferential
        (g.comp f).isHomogeneous_barMap (g.comp f).barDifferential_comp_barMap
        (by rw [LinearMap.comp_id, LinearMap.id_comp]))
  have hKBf : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (H_B.barHomotopy ∘ₗ f.barMap) := by
    have h := H_B.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom f.isCoalgHom_barMap
      f.isHomogeneous_barMap
    have heq : (f.comp g).barMap ∘ₗ f.barMap = f.barMap ∘ₗ (g.comp f).barMap := by
      rw [barMap_comp, barMap_comp, LinearMap.comp_assoc]
    rwa [heq, barMap_id, LinearMap.id_comp] at h
  have hfKA : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (f.barMap ∘ₗ S.barHomotopy) := by
    simpa only [LinearMap.comp_id] using
      f.isCoalgHom_barMap.comp_isGradedCoderivationAlong hKAc
  have hFGFh : LinearMap.IsHomogeneous (f.barMap ∘ₗ (g.comp f).barMap)
      (gradedPiece (AA.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp (g.comp f).isHomogeneous_barMap
  have hTc : IsGradedCoderivationAlong (AA.grading.shift 1) 0
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap S.barTwoHomotopy :=
    isGradedCoderivationAlong_gradedCoderivAlong _ 0
      (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap S.tTaylor
  have hTh := isHomogeneous_gradedCoderivAlong (q := 0) hFGFh f.isHomogeneous_barMap S.ht
  have hFGF_int : BB.barDifferential ∘ₗ (f.barMap ∘ₗ (g.comp f).barMap) =
      (f.barMap ∘ₗ (g.comp f).barMap) ∘ₗ AA.barDifferential := by
    rw [← LinearMap.comp_assoc, f.barDifferential_comp_barMap, LinearMap.comp_assoc,
      (g.comp f).barDifferential_comp_barMap, LinearMap.comp_assoc]
  have hT_comm : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap
      (BB.barDifferential ∘ₗ S.barTwoHomotopy - S.barTwoHomotopy ∘ₗ AA.barDifferential) := by
    have h := hTc.comp_sub_negOnePow_smul_comp hTh AA.isGradedCoderivation_barDifferential
      AA.isHomogeneous_barDifferential (q := 1) (by decide) BB.isGradedCoderivation_barDifferential
      hFGFh hFGF_int f.barDifferential_comp_barMap
    have hone : ((1 * (-2 : ℤ)).negOnePow : ℤ) = 1 := by decide
    simpa only [zero_add, hone, Int.cast_one, one_smul] using h
  exact ⟨hMc, (hKBf.sub hfKA).sub hT_comm⟩

private theorem leftStage_barDifferential_defects {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) :
    (AA.barDifferential ∘ₗ S.defectM - S.defectM ∘ₗ AA.barDifferential = 0) ∧
      (BB.barDifferential ∘ₗ S.defectU + S.defectU ∘ₗ AA.barDifferential =
        f.barMap ∘ₗ S.defectM) := by
  refine ⟨LinearMap.ext fun w ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · simp only [LeftStage.defectM, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add, (g.comp f).barDifferential_barMap,
      barDifferential_barDifferential_apply, map_zero]
    abel
  · have hHB : BB.barDifferential (H_B.barHomotopy (f.barMap w)) +
        H_B.barHomotopy (f.barMap (AA.barDifferential w)) =
        f.barMap ((g.comp f).barMap w) - f.barMap w := by
      have h := H_B.barMap_sub_barMap_apply (f.barMap w)
      rw [barMap_comp, barMap_id, LinearMap.comp_apply, LinearMap.id_apply,
        f.barDifferential_barMap] at h
      rw [barMap_comp, LinearMap.comp_apply]
      exact h.symm
    simp only [LeftStage.defectU, LeftStage.defectM, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap,
      barDifferential_barDifferential_apply, map_zero]
    rw [eq_sub_of_add_eq hHB]
    abel

/-- The length-`(k + 1)` obstruction components `Θ` and `Υ` of a `LeftStage f g H_B k` satisfy
`d_A ∘ Θ - Θ ∘ b_{A,1} = 0` and `d_B ∘ Υ + Υ ∘ b_{A,1} = f₁ ∘ Θ`. -/
private theorem leftStage_obstruction_eqs {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ} (S : LeftStage f g H_B k) :
    (AA.differential ∘ₗ S.obstructionΘ - S.obstructionΘ ∘ₗ AA.unaryBarDifferential = 0) ∧
      (BB.differential ∘ₗ S.obstructionΥ + S.obstructionΥ ∘ₗ AA.unaryBarDifferential =
        f.linearPart ∘ₗ S.obstructionΘ) := by
  set p := lengthProj R A ⟨k + 1, k.succ_pos⟩
  have hcod := leftStage_isGradedCoderivationAlong S
  have hbd := leftStage_barDifferential_defects S
  refine ⟨LinearMap.ext fun w ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · have hMp := hcod.1.apply_eq_ofLetter_letter_of_mem_filtration S.hM
      (lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w)
    have hcomm := apply_barDifferential_lengthProj_eq AA
      (D := letter R A ∘ₗ S.defectM)
      (fun u hu ↦ by rw [LinearMap.comp_apply, S.hM u hu, map_zero]) w
    have hzero := LinearMap.congr_fun hbd.1 (p w)
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      hMp, AInfinityAlgebra.barDifferential_ofLetter] at hzero
    have hzero' := congrArg (letter R A) hzero
    rw [map_sub, map_zero, letter_ofLetter, ← AInfinityAlgebra.differential_apply] at hzero'
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [hcomm] at hzero'
    simpa only [LeftStage.obstructionΘ, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] using hzero'
  · have hMp := hcod.1.apply_eq_ofLetter_letter_of_mem_filtration S.hM
      (lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w)
    have hUp := hcod.2.apply_eq_ofLetter_letter_of_mem_filtration S.hU
      (lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w)
    have hcomm := apply_barDifferential_lengthProj_eq AA
      (D := letter R B ∘ₗ S.defectU)
      (fun u hu ↦ by rw [LinearMap.comp_apply, S.hU u hu, map_zero]) w
    have hrel := LinearMap.congr_fun hbd.2 (p w)
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      hUp, hMp, AInfinityAlgebra.barDifferential_ofLetter, f.barMap_ofLetter] at hrel
    have hrel' := congrArg (letter R B) hrel
    rw [map_add, letter_ofLetter, letter_ofLetter, ← AInfinityAlgebra.differential_apply] at hrel'
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [hcomm] at hrel'
    simpa only [LeftStage.obstructionΘ, LeftStage.obstructionΥ, LinearMap.add_apply,
      LinearMap.comp_apply] using hrel'

private theorem leftStage_isHomogeneous_obstructions {f : AInfinityHom AA BB}
    {g : AInfinityHom BB AA} {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}
    (S : LeftStage f g H_B k) :
    LinearMap.IsHomogeneous (-S.obstructionΘ) (gradedPiece (AA.grading.shift 1))
        (AA.grading.shift 1).piece (-1 + 1) ∧
      LinearMap.IsHomogeneous (-S.obstructionΥ) (gradedPiece (AA.grading.shift 1))
        (BB.grading.shift 1).piece (-1) := by
  have hKAh := isHomogeneous_gradedCoderivAlong (q := 1) (g.comp f).isHomogeneous_barMap
    (LinearMap.isHomogeneous_id _) S.hkA
  have hFGFh : LinearMap.IsHomogeneous (f.barMap ∘ₗ (g.comp f).barMap)
      (gradedPiece (AA.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp (g.comp f).isHomogeneous_barMap
  have hTh := isHomogeneous_gradedCoderivAlong (q := 0) hFGFh f.isHomogeneous_barMap S.ht
  refine ⟨?_, ?_⟩
  · have hMh : LinearMap.IsHomogeneous S.defectM (gradedPiece (AA.grading.shift 1))
        (gradedPiece (AA.grading.shift 1)) 0 := by
      refine ((g.comp f).isHomogeneous_barMap.sub (LinearMap.isHomogeneous_id _)).sub ?_
      refine LinearMap.IsHomogeneous.add ?_ ?_
      · simpa only [neg_add_cancel] using AA.isHomogeneous_barDifferential.comp hKAh
      · simpa only [add_neg_cancel] using hKAh.comp AA.isHomogeneous_barDifferential
    simpa only [neg_add_cancel, add_zero] using
      ((isHomogeneous_letter _).comp (hMh.comp (isHomogeneous_lengthProj _ _))).neg
  · have hUh : LinearMap.IsHomogeneous S.defectU (gradedPiece (AA.grading.shift 1))
        (gradedPiece (BB.grading.shift 1)) (-1) := by
      refine LinearMap.IsHomogeneous.sub ?_ ?_
      · refine LinearMap.IsHomogeneous.sub ?_ ?_
        · simpa only [zero_add] using H_B.isHomogeneous_barHomotopy.comp f.isHomogeneous_barMap
        · simpa only [add_zero] using f.isHomogeneous_barMap.comp hKAh
      · refine LinearMap.IsHomogeneous.sub ?_ ?_
        · simpa only [show (-2 : ℤ) + 1 = -1 by ring] using
            BB.isHomogeneous_barDifferential.comp hTh
        · simpa only [show (1 : ℤ) + -2 = -1 by ring] using
            hTh.comp AA.isHomogeneous_barDifferential
    simpa only [zero_add, add_zero] using
      ((isHomogeneous_letter _).comp (hUh.comp (isHomogeneous_lengthProj _ _))).neg

private theorem leftStageSucc_hM {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ} (S : LeftStage f g H_B k)
    {δkA : ReducedTensorWords R A →ₗ[R] A} (hδkA₀ : ∀ u ∈ filtration R A k, δkA u = 0)
    (hsol₁ : AA.differential ∘ₗ δkA + δkA ∘ₗ AA.unaryBarDifferential = S.obstructionΘ)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (k + 1)) :
    (((g.comp f).barMap - (LinearMap.id : Module.End R (ReducedTensorWords R A))) -
      (AA.barDifferential ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 1
          (g.comp f).barMap LinearMap.id (S.kATaylor + δkA) +
        gradedCoderivAlong (AA.grading.shift 1) 1
          (g.comp f).barMap LinearMap.id (S.kATaylor + δkA) ∘ₗ AA.barDifferential)) z = 0 := by
  have hcod := leftStage_isGradedCoderivationAlong S
  have hKA_step := gradedCoderivAlong_add_apply_of_mem_filtration (AA.grading.shift 1) 1
    (g.comp f).isCoalgHom_barMap (g.comp f).isCoalgHom_barMap (isCoalgHom_id A)
    (h := S.kATaylor) (fun _ _ ↦ rfl) hδkA₀
  have hhigh : AA.higherBarDifferential z ∈ filtration R A k :=
    AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have hunary : AA.unaryBarDifferential z ∈ filtration R A (k + 1) :=
    AA.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩
  have hMz : ((g.comp f).barMap z - z) -
      (AA.barDifferential (S.barHomotopy z) + S.barHomotopy (AA.barDifferential z)) =
      ofLetter R A (S.obstructionΘ z) :=
    (hcod.1.apply_eq_ofLetter_letter_of_mem_filtration S.hM hz).trans (congrArg (ofLetter R A)
      (apply_lengthProj_of_mem_filtration R A (f := letter R A ∘ₗ S.defectM)
        (fun u hu ↦ by rw [LinearMap.comp_apply, S.hM u hu, map_zero]) hz).symm)
  have hKAz : gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap LinearMap.id
      (S.kATaylor + δkA) (AA.barDifferential z) =
      S.barHomotopy (AA.barDifferential z) + ofLetter R A (δkA (AA.unaryBarDifferential z)) := by
    rw [AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
      hKA_step.2 _ hunary, hKA_step.1 _ hhigh]
    abel
  have hsol₁z : AA.differential (δkA z) + δkA (AA.unaryBarDifferential z) = S.obstructionΘ z := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply] using LinearMap.congr_fun hsol₁ z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [hKA_step.2 z hz, hKAz, map_add, AInfinityAlgebra.barDifferential_ofLetter,
    ← AInfinityAlgebra.differential_apply, eq_add_of_sub_eq (eq_add_of_sub_eq hMz), ← hsol₁z,
    map_add]
  abel

private theorem leftStageSucc_hU {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    {H_B : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ} (S : LeftStage f g H_B k)
    {δkA : ReducedTensorWords R A →ₗ[R] A} {δt : ReducedTensorWords R A →ₗ[R] B}
    (hδkA₀ : ∀ u ∈ filtration R A k, δkA u = 0) (hδt₀ : ∀ u ∈ filtration R A k, δt u = 0)
    (hsol₂ : f.linearPart ∘ₗ δkA +
      (BB.differential ∘ₗ δt - δt ∘ₗ AA.unaryBarDifferential) = S.obstructionΥ)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (k + 1)) :
    ((H_B.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 1
        (g.comp f).barMap LinearMap.id (S.kATaylor + δkA)) -
      (BB.barDifferential ∘ₗ gradedCoderivAlong (AA.grading.shift 1) 0
          (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (S.tTaylor + δt) -
        gradedCoderivAlong (AA.grading.shift 1) 0
          (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (S.tTaylor + δt) ∘ₗ
          AA.barDifferential)) z = 0 := by
  have hcod := leftStage_isGradedCoderivationAlong S
  have hKA_step := gradedCoderivAlong_add_apply_of_mem_filtration (AA.grading.shift 1) 1
    (g.comp f).isCoalgHom_barMap (g.comp f).isCoalgHom_barMap (isCoalgHom_id A)
    (h := S.kATaylor) (fun _ _ ↦ rfl) hδkA₀
  have hT_step := gradedCoderivAlong_add_apply_of_mem_filtration (AA.grading.shift 1) 0
    (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap)
    (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap
    (h := S.tTaylor) (fun _ _ ↦ rfl) hδt₀
  have hhigh : AA.higherBarDifferential z ∈ filtration R A k :=
    AA.higherBarDifferential_filtration k ⟨z, hz, rfl⟩
  have hunary : AA.unaryBarDifferential z ∈ filtration R A (k + 1) :=
    AA.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩
  have hUz : (H_B.barHomotopy (f.barMap z) - f.barMap (S.barHomotopy z)) -
      (BB.barDifferential (S.barTwoHomotopy z) - S.barTwoHomotopy (AA.barDifferential z)) =
      ofLetter R B (S.obstructionΥ z) :=
    (hcod.2.apply_eq_ofLetter_letter_of_mem_filtration S.hU hz).trans (congrArg (ofLetter R B)
      (apply_lengthProj_of_mem_filtration R A (f := letter R B ∘ₗ S.defectU)
        (fun u hu ↦ by rw [LinearMap.comp_apply, S.hU u hu, map_zero]) hz).symm)
  have hTz : gradedCoderivAlong (AA.grading.shift 1) 0 (f.barMap ∘ₗ (g.comp f).barMap)
      f.barMap (S.tTaylor + δt) (AA.barDifferential z) =
      S.barTwoHomotopy (AA.barDifferential z) + ofLetter R B (δt (AA.unaryBarDifferential z)) := by
    rw [AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
      hT_step.2 _ hunary, hT_step.1 _ hhigh]
    abel
  have hsol₂z : f.linearPart (δkA z) +
      (BB.differential (δt z) - δt (AA.unaryBarDifferential z)) = S.obstructionΥ z := by
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply] using
      LinearMap.congr_fun hsol₂ z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hKA_step.2 z hz, hT_step.2 z hz, hTz, map_add, map_add, f.barMap_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
    eq_add_of_sub_eq (eq_add_of_sub_eq hUz), ← hsol₂z, map_add, map_sub]
  abel

/-- Inductive step of the left-homotopy construction: lift a `LeftStage f g H_B k` to `k + 1`
without changing `kATaylor` on `filtration R A k`. -/
private noncomputable def leftStageSucc (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (H_B : Homotopy (f.comp g) (AInfinityHom.id BB))
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) {k : ℕ}
    (S : LeftStage f g H_B k) :
    {S' : LeftStage f g H_B (k + 1) //
      ∀ z ∈ filtration R A k, S'.kATaylor z = S.kATaylor z} := by
  set δkA := solveStepG e (-S.obstructionΘ) (-S.obstructionΥ)
  set δt := -(solveStepH e (-S.obstructionΘ) (-S.obstructionΥ))
  have hpΘ : ∀ u ∈ filtration R A k, (-S.obstructionΘ) u = 0 := fun u hu ↦ by
    simp only [LeftStage.obstructionΘ, LinearMap.neg_apply, LinearMap.comp_apply,
      lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨k + 1, k.succ_pos⟩)
        (Nat.lt_succ_self k) hu, map_zero, neg_zero]
  have hpΥ : ∀ u ∈ filtration R A k, (-S.obstructionΥ) u = 0 := fun u hu ↦ by
    simp only [LeftStage.obstructionΥ, LinearMap.neg_apply, LinearMap.comp_apply,
      lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨k + 1, k.succ_pos⟩)
        (Nat.lt_succ_self k) hu, map_zero, neg_zero]
  have hδkA₀ : ∀ u ∈ filtration R A k, δkA u = 0 := fun u hu ↦
    solveStepG_apply_eq_zero e (hpΘ u hu) (hpΥ u hu)
  have hδt₀ : ∀ u ∈ filtration R A k, δt u = 0 := fun u hu ↦ by
    rw [LinearMap.neg_apply, solveStepH_apply_eq_zero e (hpΘ u hu) (hpΥ u hu), neg_zero]
  have hdeg := leftStage_isHomogeneous_obstructions S
  have hob := leftStage_obstruction_eqs S
  have hsol := solveStep_eqs e (dW := -AA.unaryBarDifferential)
    (Φ := -S.obstructionΘ) (Ψ := -S.obstructionΥ)
    (LinearMap.ext fun z ↦ by
      have h := LinearMap.congr_fun hob.1 z
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.zero_apply, map_neg, sub_eq_zero] at h ⊢
      rw [h]; abel)
    (LinearMap.ext fun z ↦ by
      have h := LinearMap.congr_fun hob.2 z
      simp only [he, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
        LinearMap.comp_apply, map_neg] at h ⊢
      rw [← h]; abel)
  have hsol₁' : AA.differential ∘ₗ δkA + δkA ∘ₗ AA.unaryBarDifferential = S.obstructionΘ :=
    LinearMap.ext fun z ↦ by
      have h := LinearMap.congr_fun hsol.1 z
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
        LinearMap.comp_apply, map_neg] at h ⊢
      simpa only [sub_neg_eq_add, neg_neg] using h
  have hsol₂' : f.linearPart ∘ₗ δkA +
      (BB.differential ∘ₗ δt - δt ∘ₗ AA.unaryBarDifferential) = S.obstructionΥ :=
    LinearMap.ext fun z ↦ by
      have h := LinearMap.congr_fun hsol.2 z
      simp only [δt, he, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
        LinearMap.comp_apply, map_neg] at h ⊢
      rw [eq_add_of_sub_eq h]
      abel
  refine ⟨⟨S.kATaylor + δkA, S.tTaylor + δt,
    S.hkA.add (isHomogeneous_solveStepG hG hdeg.1 hdeg.2),
    S.ht.add (by simpa only [show (-1 : ℤ) + -1 = -2 by ring] using
      (isHomogeneous_solveStepH hG hdeg.1 hdeg.2).neg),
    fun z hz ↦ leftStageSucc_hM S hδkA₀ hsol₁' hz,
    fun z hz ↦ leftStageSucc_hU S hδkA₀ hδt₀ hsol₂' hz⟩,
    fun z hz ↦ by rw [LinearMap.add_apply, hδkA₀ z hz, add_zero]⟩

/-- Full `ℕ`-indexed sequence of left stages starting at `leftStageZero`. -/
private noncomputable def leftStageNat (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (H_B : Homotopy (f.comp g) (AInfinityHom.id BB))
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    ∀ n : ℕ, LeftStage f g H_B n
  | 0 => leftStageZero f g H_B
  | n + 1 => (leftStageSucc f g H_B e he hG (leftStageNat f g H_B e he hG n)).1

private theorem leftStageNat_stabilises (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (H_B : Homotopy (f.comp g) (AInfinityHom.id BB))
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) (n : ℕ) :
    ∀ z ∈ filtration R A n,
      (leftStageNat f g H_B e he hG (n + 1)).kATaylor z =
        (leftStageNat f g H_B e he hG n).kATaylor z :=
  (leftStageSucc f g H_B e he hG (leftStageNat f g H_B e he hG n)).2

private noncomputable abbrev liftLeftHomotopyTaylor (f : AInfinityHom AA BB)
    (g : AInfinityHom BB AA) (H_B : Homotopy (f.comp g) (AInfinityHom.id BB))
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    ReducedTensorWords R A →ₗ[R] A :=
  stabilisingTaylor fun n ↦ (leftStageNat f g H_B e he hG n).kATaylor

/-- The lifted left homotopy `g ∘ f ⇒ id_A` given any right homotopy `H_B : f ∘ g ⇒ id_B`. -/
private noncomputable def liftLeftHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (H_B : Homotopy (f.comp g) (AInfinityHom.id BB))
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    Homotopy (g.comp f) (AInfinityHom.id AA) :=
  Homotopy.ofTaylor (liftLeftHomotopyTaylor f g H_B e he hG)
    (isHomogeneous_stabilisingTaylor (leftStageNat_stabilises f g H_B e he hG)
      fun n ↦ (leftStageNat f g H_B e he hG n).hkA)
    (LinearMap.ext fun z ↦ by
      have hstab := leftStageNat_stabilises f g H_B e he hG
      obtain ⟨m, hm⟩ := exists_mem_filtration R A z
      have hz : z ∈ filtration R A (m + 1) := filtration_monotone R A m.le_succ hm
      have hKA_eq : gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap
          (AInfinityHom.id AA).barMap (liftLeftHomotopyTaylor f g H_B e he hG) z =
          (leftStageNat f g H_B e he hG (m + 1)).barHomotopy z :=
        (isGradedCoderivationAlong_gradedCoderivAlong _ 1 (g.comp f).isCoalgHom_barMap
          (AInfinityHom.id AA).isCoalgHom_barMap _).apply_eq_of_mem_filtration
          (isGradedCoderivationAlong_gradedCoderivAlong _ 1 (g.comp f).isCoalgHom_barMap
            (isCoalgHom_id A) _)
          (fun _ _ ↦ rfl) (fun u _ ↦ by rw [barMap_id, LinearMap.id_apply])
          (fun u hu ↦ by
            rw [letter_gradedCoderivAlong_apply, letter_gradedCoderivAlong_apply,
              stabilisingTaylor_apply_of_mem_filtration hstab hu]) hz
      have hM := congrArg (letter R A) ((leftStageNat f g H_B e he hG (m + 1)).hM z hz)
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        map_sub, map_add, map_zero, sub_eq_zero] at hM
      rw [letter_barMap_apply, letter_barDifferential_apply, letter_gradedCoderivAlong_apply] at hM
      rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        taylor_id, hKA_eq,
        stabilisingTaylor_apply_of_mem_filtration hstab (AA.barDifferential_mem_filtration hz)]
      exact hM)

end Lifting

/-! ### Lifting linear chain-homotopy equivalences and closure properties -/

namespace HomotopyEquiv

/-- Lift a homogeneous degree-`(-1)` linear chain-homotopy equivalence `e` with
`e.hom = f.linearPart` to a two-sided `A∞` homotopy equivalence with forward morphism `f`, inverse
linear part `e.inv`, and right linear homotopy `e.homotopyHomInv`. -/
noncomputable def ofLinear (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    HomotopyEquiv AA BB where
  hom := f
  inv := liftInv f e he hG
  homotopyInvHomId := liftLeftHomotopy f (liftInv f e he hG) (liftRightHomotopy f e he hG) e he hG
  homotopyHomInvId := liftRightHomotopy f e he hG

@[simp]
theorem hom_ofLinear (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    (ofLinear f e he hG).hom = f := (rfl)

@[simp]
theorem linearPart_inv_ofLinear (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    (ofLinear f e he hG).inv.linearPart = e.inv :=
  linearPart_liftInv f e he hG

@[simp]
theorem linearHomotopy_homotopyHomInvId_ofLinear (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) :
    (ofLinear f e he hG).homotopyHomInvId.linearHomotopy = e.homotopyHomInv :=
  linearHomotopy_liftRightHomotopy f e he hG

/-- Compose two `A∞` homotopy equivalences by lifting the composite of their underlying linear
chain-homotopy equivalences along `e₂.hom.comp e₁.hom`. -/
noncomputable def trans (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    HomotopyEquiv AA CC :=
  ofLinear (e₂.hom.comp e₁.hom)
    (e₁.toLinearHomotopyEquiv.trans e₂.toLinearHomotopyEquiv)
    (by rw [LinearHomotopyEquiv.hom_trans, hom_toLinearHomotopyEquiv,
      hom_toLinearHomotopyEquiv, linearPart_comp])
    (e₁.isHomogeneous_toLinearHomotopyEquiv.trans e₂.isHomogeneous_toLinearHomotopyEquiv)

@[simp]
theorem hom_trans (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    (e₁.trans e₂).hom = e₂.hom.comp e₁.hom := (rfl)

@[simp]
theorem linearPart_inv_trans (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    (e₁.trans e₂).inv.linearPart = e₁.inv.linearPart ∘ₗ e₂.inv.linearPart := by
  rw [trans, linearPart_inv_ofLinear, LinearHomotopyEquiv.inv_trans,
    inv_toLinearHomotopyEquiv, inv_toLinearHomotopyEquiv]

end HomotopyEquiv

/-- **Linear criterion for `A∞` homotopy equivalences.**  Over any commutative ring, an `A∞`
morphism is a two-sided `A∞` homotopy equivalence if and only if its linear part extends to a
homogeneous degree-`(-1)` linear chain-homotopy equivalence between the unary complexes. -/
theorem isHomotopyEquiv_iff_exists_linearHomotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ e : LinearHomotopyEquiv AA.differential BB.differential,
        e.hom = f.linearPart ∧ e.IsHomogeneous AA.grading.piece BB.grading.piece (-1) := by
  constructor
  · intro hf
    obtain ⟨E, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
    exact ⟨E.toLinearHomotopyEquiv, E.hom_toLinearHomotopyEquiv,
      E.isHomogeneous_toLinearHomotopyEquiv⟩
  · rintro ⟨e, he, hG⟩
    exact (HomotopyEquiv.ofLinear f e he hG).isHomotopyEquiv_hom

/-- `A∞` homotopy equivalences are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨e₁, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  obtain ⟨e₂, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv g).1 hg
  exact (e₁.trans e₂).isHomotopyEquiv_hom

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  simp only [isHomotopyEquiv_iff_exists_linearHomotopyEquiv]
  constructor
  · rintro ⟨e, he, hG⟩
    have hs : e.hom - g.linearPart =
        BB.differential ∘ₗ h.linearHomotopy + h.linearHomotopy ∘ₗ AA.differential := by
      rw [he, h.differential_comp_linearHomotopy_add]
    exact ⟨e.ofHomotopy g.differential_comp_linearPart h.linearHomotopy hs,
      e.hom_ofHomotopy _ _ hs,
      hG.ofHomotopy g.differential_comp_linearPart g.isHomogeneous_linearPart
        h.isHomogeneous_linearHomotopy hs⟩
  · rintro ⟨e, he, hG⟩
    have hs : e.hom - f.linearPart =
        BB.differential ∘ₗ (-h.linearHomotopy) + (-h.linearHomotopy) ∘ₗ AA.differential := by
      rw [he, LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add,
        h.differential_comp_linearHomotopy_add, neg_sub]
    exact ⟨e.ofHomotopy f.differential_comp_linearPart (-h.linearHomotopy) hs,
      e.hom_ofHomotopy _ _ hs,
      hG.ofHomotopy f.differential_comp_linearPart f.isHomogeneous_linearPart
        h.isHomogeneous_linearHomotopy.neg hs⟩

/-- Two out of three: if `f` and `g ∘ f` are `A∞` homotopy equivalences, then so is `g`. -/
theorem IsHomotopyEquiv.of_precomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : g.IsHomotopyEquiv := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  have h : Homotopy ((g.comp e.hom).comp e.inv) g := by
    simpa only [comp_assoc, comp_id] using e.homotopyHomInvId.compRight g
  exact h.isHomotopyEquiv_iff.1 (hgf.comp e.isHomotopyEquiv_inv)

/-- Two out of three: if `g` and `g ∘ f` are `A∞` homotopy equivalences, then so is `f`. -/
theorem IsHomotopyEquiv.of_postcomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : f.IsHomotopyEquiv := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv g).1 hg
  have h : Homotopy (e.inv.comp (e.hom.comp f)) f := by
    simpa only [← comp_assoc, id_comp] using e.homotopyInvHomId.compLeft f
  exact h.isHomotopyEquiv_iff.1 (e.isHomotopyEquiv_inv.comp hgf)

end CommRing

end AInfinityHom

end TauCeti
