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

We prove the converse to `TauCeti.AInfinityHom.HomotopyEquiv.toLinearHomotopyEquiv`: over any
commutative ring `R`, a homogeneous degree-`(-1)` linear chain-homotopy equivalence `e` with
`e.hom = f.linearPart` lifts to a two-sided `A∞` homotopy equivalence with forward morphism `f`,
inverse linear part `e.inv`, and right linear homotopy `e.homotopyHomInv`
(`HomotopyEquiv.ofLinear`).  This yields the linear criterion, closure under composition,
homotopy invariance, and two-out-of-three.

The lifting proceeds by word-length filtration induction on the reduced bar construction in two
stages: first lift a right inverse `g` and right homotopy `H_B : f ∘ g ⇒ id`, then lift a left
homotopy `K_A : g ∘ f ⇒ id` alongside a degree-`(-2)` `(F ∘ G ∘ F, F)`-coderivation `T`.

## Main definitions

* `TauCeti.AInfinityHom.HomotopyEquiv.ofLinear`: lift a linear chain-homotopy equivalence on
  `f.linearPart` to an `A∞` homotopy equivalence.
* `TauCeti.AInfinityHom.HomotopyEquiv.trans`: compose two `A∞` homotopy equivalences.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyEquiv`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`, `TauCeti.AInfinityHom.Homotopy.isHomotopyEquiv_iff`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_precomp`,
  `TauCeti.AInfinityHom.IsHomotopyEquiv.of_postcomp`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Université Paris 7 (2003), Section 1.3.
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

open ReducedTensorWords

section Helpers
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private noncomputable def stabilisingTaylor (φ : ℕ → ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] N :=
  DirectSum.toModule R _ _ fun k ↦ φ k.1 ∘ₗ of R M k
private theorem stabilisingTaylor_apply_of_mem_filtration {φ : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (hφ : ∀ n, ∀ z ∈ filtration R M n, φ (n + 1) z = φ n z) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : stabilisingTaylor φ z = φ n z :=
  (show filtration R M n ≤ LinearMap.eqLocus (stabilisingTaylor φ) (φ n) by
    clear hz; rw [filtration_le_iff]; rintro _ hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, stabilisingTaylor, toModule_of, LinearMap.comp_apply]
    induction n, hk using Nat.le_induction with
    | base => rfl
    | succ n hk ih =>
      rw [hφ n _ (filtration_monotone R M hk (of_mem_filtration R M le_rfl x)), ih]) hz
private theorem isHomogeneous_stabilisingTaylor {G : InternalGrading R M ℤ}
    {H : InternalGrading R N ℤ} {r : ℤ} {φ : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (hφ : ∀ n, ∀ z ∈ filtration R M n, φ (n + 1) z = φ n z)
    (hdeg : ∀ n, LinearMap.IsHomogeneous (φ n) (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (stabilisingTaylor φ) (gradedPiece G) H.piece r :=
  LinearMap.isHomogeneous_def.2 fun _ z hz ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R M z
    rw [stabilisingTaylor_apply_of_mem_filtration hφ hn]; exact (hdeg n).map_mem hz
private theorem barDifferential_sq_apply (ℳ : AInfinityAlgebra R M) (w : ReducedTensorWords R M) :
    ℳ.barDifferential (ℳ.barDifferential w) = 0 := by
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun ℳ.barDifferential_sq w
private theorem lengthProj_comp_unaryBarDifferential (ℳ : AInfinityAlgebra R M)
    (n : {n : ℕ // 0 < n}) :
    lengthProj R M n ∘ₗ ℳ.unaryBarDifferential = ℳ.unaryBarDifferential ∘ₗ lengthProj R M n :=
  ℳ.unaryBarDifferential_eq_gradedCoderiv ▸ lengthProj_comp_gradedCoderiv (ℳ.grading.shift 1) 1 (by
    rw [LinearMap.comp_assoc]; congr 1; refine linearMap_ext R M fun k x ↦ ?_
    rw [LinearMap.comp_apply]; by_cases hk : k = 1
    · subst hk; rw [lengthProj_of_self]
    · rw [lengthProj_of_of_ne R M hk, map_zero, letter_of_of_ne_one R M hk]) rfl
private theorem isHomogeneous_obstruction {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}
    {r : ℤ} {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r) (n : {n : ℕ // 0 < n}) :
    LinearMap.IsHomogeneous (letter R N ∘ₗ D ∘ₗ lengthProj R M n) (gradedPiece G) H.piece r := by
  simpa only [zero_add, add_zero] using
    (isHomogeneous_letter H).comp (hD.comp (isHomogeneous_lengthProj G n))
private theorem isHomogeneous_barDiff_comm {ℳ : AInfinityAlgebra R M} {𝒩 : AInfinityAlgebra R N}
    {r : ℤ} {K : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hK : LinearMap.IsHomogeneous K (gradedPiece (ℳ.grading.shift 1))
      (gradedPiece (𝒩.grading.shift 1)) r) :
    LinearMap.IsHomogeneous (𝒩.barDifferential ∘ₗ K + K ∘ₗ ℳ.barDifferential)
        (gradedPiece (ℳ.grading.shift 1)) (gradedPiece (𝒩.grading.shift 1)) (r + 1) ∧
      LinearMap.IsHomogeneous (𝒩.barDifferential ∘ₗ K - K ∘ₗ ℳ.barDifferential)
        (gradedPiece (ℳ.grading.shift 1)) (gradedPiece (𝒩.grading.shift 1)) (r + 1) :=
  have h₁ := 𝒩.isHomogeneous_barDifferential.comp hK
  have h₂ := add_comm 1 r ▸ hK.comp ℳ.isHomogeneous_barDifferential
  ⟨h₁.add h₂, h₁.sub h₂⟩
private theorem obstruction_eq_of_barDifferential {ℳ : AInfinityAlgebra R M}
    {𝒩 : AInfinityAlgebra R N} {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {k : ℕ}
    (hD₀ : ∀ u ∈ filtration R M k, D u = 0)
    (hD₁ : ∀ z ∈ filtration R M (k + 1), D z = ofLetter R N (letter R N (D z)))
    (s : ℤ) {rhs : ReducedTensorWords R M →ₗ[R] N}
    (h : ∀ w, 𝒩.barDifferential (D (lengthProj R M ⟨k + 1, k.succ_pos⟩ w)) +
      s • D (ℳ.barDifferential (lengthProj R M ⟨k + 1, k.succ_pos⟩ w)) = ofLetter R N (rhs w)) :
    𝒩.differential ∘ₗ (letter R N ∘ₗ D ∘ₗ lengthProj R M ⟨k + 1, k.succ_pos⟩) +
      s • ((letter R N ∘ₗ D ∘ₗ lengthProj R M ⟨k + 1, k.succ_pos⟩) ∘ₗ ℳ.unaryBarDifferential) =
      rhs :=
  LinearMap.ext fun w ↦ by
    have hw := congrArg (letter R N) (h w)
    rw [map_add, map_zsmul, letter_ofLetter,
      hD₁ _ (lengthProj_mem_filtration R M ⟨k + 1, k.succ_pos⟩ w),
      AInfinityAlgebra.barDifferential_ofLetter, letter_ofLetter,
      ← AInfinityAlgebra.differential_apply, ℳ.barDifferential_eq_unary_add_higher,
      LinearMap.add_apply, map_add, hD₀ _ (ℳ.higherBarDifferential_filtration k
        ⟨_, lengthProj_mem_filtration R M ⟨k + 1, k.succ_pos⟩ w, rfl⟩), add_zero,
      ← LinearMap.comp_apply ℳ.unaryBarDifferential, ← lengthProj_comp_unaryBarDifferential,
      LinearMap.comp_apply] at hw
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply] using hw
private theorem defect_eq_ofLetter_obstruction
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {k : ℕ}
    (hD₀ : ∀ u ∈ filtration R M k, D u = 0)
    (hD₁ : ∀ z ∈ filtration R M (k + 1), D z = ofLetter R N (letter R N (D z)))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (k + 1)) :
    D z = ofLetter R N ((letter R N ∘ₗ D ∘ₗ lengthProj R M ⟨k + 1, k.succ_pos⟩) z) :=
  (hD₁ z hz).trans <| congrArg (ofLetter R N) <|
    (apply_lengthProj_of_mem_filtration R M (f := letter R N ∘ₗ D)
      (fun u hu ↦ by rw [LinearMap.comp_apply, hD₀ u hu, map_zero]) hz).symm
private theorem barDifferential_perturb_apply (ℳ : AInfinityAlgebra R M)
    {F₁ F₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {δ : ReducedTensorWords R M →ₗ[R] N} {k : ℕ}
    (h₁ : ∀ u ∈ filtration R M k, F₁ u = F₂ u)
    (h₂ : ∀ u ∈ filtration R M (k + 1), F₁ u = F₂ u + ofLetter R N (δ u))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (k + 1)) :
    F₁ (ℳ.barDifferential z) =
      F₂ (ℳ.barDifferential z) + ofLetter R N (δ (ℳ.unaryBarDifferential z)) := by
  rw [ℳ.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
    h₂ _ (ℳ.unaryBarDifferential_filtration (k + 1) ⟨z, hz, rfl⟩),
    h₁ _ (ℳ.higherBarDifferential_filtration k ⟨z, hz, rfl⟩)]; abel
private theorem coalgHom_add_apply_of_mem_filtration (G : InternalGrading R M ℤ)
    {g δg : ReducedTensorWords R M →ₗ[R] N} {k : ℕ} (hδ : ∀ u ∈ filtration R M k, δg u = 0) :
    (∀ u ∈ filtration R M k, coalgHom R (g + δg) u = coalgHom R g u) ∧
      ∀ z ∈ filtration R M (k + 1),
        coalgHom R (g + δg) z = coalgHom R g z + ofLetter R N (δg z) := by
  have hk : ∀ u ∈ filtration R M k, coalgHom R (g + δg) u = coalgHom R g u := fun u hu ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _) (fun w hw ↦ by
      simp only [← LinearMap.comp_apply (letter R N), letter_comp_coalgHom, LinearMap.add_apply,
        hδ w hw, add_zero]) hu
  refine ⟨hk, fun z hz ↦ eq_add_of_sub_eq' ?_⟩
  simpa only [LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply (letter R N),
    letter_comp_coalgHom, LinearMap.add_apply, add_sub_cancel_left] using
    ((isCoalgHom_coalgHom (R := R) (g + δg)).isGradedCoderivationAlong_sub (G := G)
      (isCoalgHom_coalgHom g)).apply_eq_ofLetter_letter_of_mem_filtration
        (fun w hw ↦ by rw [LinearMap.sub_apply, hk w hw, sub_self]) hz
private theorem gradedCoderivAlong_add_apply_of_mem_filtration (G : InternalGrading R M ℤ) (q : ℤ)
    {F₁ F₂ F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₁ : IsCoalgHom R F₁) (hF₂ : IsCoalgHom R F₂) (hF' : IsCoalgHom R F')
    {h δh : ReducedTensorWords R M →ₗ[R] N} {k : ℕ}
    (hF : ∀ u ∈ filtration R M k, F₁ u = F₂ u) (hδ : ∀ u ∈ filtration R M k, δh u = 0) :
    (∀ u ∈ filtration R M k,
        gradedCoderivAlong G q F₁ F' (h + δh) u = gradedCoderivAlong G q F₂ F' h u) ∧
      ∀ z ∈ filtration R M (k + 1),
        gradedCoderivAlong G q F₁ F' (h + δh) z =
          gradedCoderivAlong G q F₂ F' h z + ofLetter R N (δh z) := by
  have h₁ := isGradedCoderivationAlong_gradedCoderivAlong G q hF₁ hF' (h + δh)
  have h₂ := isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF' (h + δh)
  have h₃ := isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF' h
  have hD₁₂ : ∀ z ∈ filtration R M (k + 1),
      gradedCoderivAlong G q F₁ F' (h + δh) z = gradedCoderivAlong G q F₂ F' (h + δh) z :=
    fun z hz ↦ h₁.apply_eq_of_mem_filtration h₂ (fun w hw ↦ hF w (Nat.add_sub_cancel k 1 ▸ hw))
      (fun _ _ ↦ rfl) (fun _ _ ↦ by
        simp only [← LinearMap.comp_apply (letter R N), letter_comp_gradedCoderivAlong]) hz
  have hk : ∀ u ∈ filtration R M k,
      gradedCoderivAlong G q F₂ F' (h + δh) u = gradedCoderivAlong G q F₂ F' h u :=
    fun u hu ↦ h₂.apply_eq_of_mem_filtration h₃ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun w hw ↦ by
      simp only [← LinearMap.comp_apply (letter R N), letter_comp_gradedCoderivAlong,
        LinearMap.add_apply, hδ w hw, add_zero]) hu
  refine ⟨fun u hu ↦ (hD₁₂ u (filtration_monotone R M k.le_succ hu)).trans (hk u hu),
    fun z hz ↦ (hD₁₂ z hz).trans <| eq_add_of_sub_eq' ?_⟩
  simpa only [LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply (letter R N),
    letter_comp_gradedCoderivAlong, LinearMap.add_apply, add_sub_cancel_left] using
    (h₂.sub h₃).apply_eq_ofLetter_letter_of_mem_filtration
      (fun w hw ↦ by rw [LinearMap.sub_apply, hk w hw, sub_self]) hz
private theorem coalgHom_stabilisingTaylor_apply (φ : ℕ → ReducedTensorWords R M →ₗ[R] N)
    (hφ : ∀ n, ∀ u ∈ filtration R M n, φ (n + 1) u = φ n u) {m : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M m) :
    coalgHom R (stabilisingTaylor φ) z = coalgHom R (φ m) z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _) (fun u hu ↦ by
    simp only [← LinearMap.comp_apply (letter R N), letter_comp_coalgHom,
      stabilisingTaylor_apply_of_mem_filtration hφ hu]) hz
private theorem gradedCoderivAlong_stabilisingTaylor_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F₁ F₂ F'₁ F'₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF₁ : IsCoalgHom R F₁) (hF₂ : IsCoalgHom R F₂)
    (hF'₁ : IsCoalgHom R F'₁) (hF'₂ : IsCoalgHom R F'₂)
    (φ : ℕ → ReducedTensorWords R M →ₗ[R] N)
    (hφ : ∀ n, ∀ u ∈ filtration R M n, φ (n + 1) u = φ n u) {m : ℕ}
    (hF : ∀ u ∈ filtration R M m, F₁ u = F₂ u) (hF' : ∀ u ∈ filtration R M m, F'₁ u = F'₂ u)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M m) :
    gradedCoderivAlong G q F₁ F'₁ (stabilisingTaylor φ) z =
      gradedCoderivAlong G q F₂ F'₂ (φ m) z :=
  (isGradedCoderivationAlong_gradedCoderivAlong G q hF₁ hF'₁ _).apply_eq_of_mem_filtration
    (isGradedCoderivationAlong_gradedCoderivAlong G q hF₂ hF'₂ _)
    (fun u hu ↦ hF u (filtration_monotone R M (Nat.sub_le m 1) hu))
    (fun u hu ↦ hF' u (filtration_monotone R M (Nat.sub_le m 1) hu)) (fun u hu ↦ by
      simp only [← LinearMap.comp_apply (letter R N), letter_comp_gradedCoderivAlong,
        stabilisingTaylor_apply_of_mem_filtration hφ hu]) hz
private theorem taylor_homotopy_of_defect_zero {ℳ : AInfinityAlgebra R M} (F : AInfinityHom ℳ ℳ)
    {F' K K' : Module.End R (ReducedTensorWords R M)} (φ : ℕ → ReducedTensorWords R M →ₗ[R] M)
    (hφ : ∀ n, ∀ u ∈ filtration R M n, φ (n + 1) u = φ n u) {m : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M m)
    (hD : ((F' - (LinearMap.id : Module.End R (ReducedTensorWords R M))) -
      (ℳ.barDifferential ∘ₗ K' + K' ∘ₗ ℳ.barDifferential)) z = 0)
    (hF : F.barMap z = F' z) (hK : K z = K' z) (hlK' : letter R M ∘ₗ K' = φ m) :
    (F.taylor - (AInfinityHom.id ℳ).taylor) z =
      (ℳ.taylor ∘ₗ K + stabilisingTaylor φ ∘ₗ ℳ.barDifferential) z := by
  have h := congrArg (letter R M) hD
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, map_add, map_zero, sub_eq_zero] at h
  rw [← LinearMap.comp_apply (letter R M) ℳ.barDifferential, ℳ.letter_comp_barDifferential,
    ← LinearMap.comp_apply (letter R M) K', hlK'] at h
  rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    F.taylor_def, LinearMap.comp_apply, hF, taylor_id, hK,
    stabilisingTaylor_apply_of_mem_filtration hφ (ℳ.barDifferential_mem_filtration hz)]; exact h
end Helpers

/-! #### Parametric linear obstruction solver -/

section Solver
variable {W : Type*} [AddCommGroup W] [Module R W]
  (e : LinearHomotopyEquiv AA.differential BB.differential)

private def solveGamma (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] A :=
  e.homotopyInvHom ∘ₗ Φ - e.inv ∘ₗ Ψ
private def solveZ (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] B :=
  Ψ + e.hom ∘ₗ solveGamma e Φ Ψ
private def solveStepG (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] A :=
  solveGamma e Φ Ψ - e.inv ∘ₗ solveZ e Φ Ψ
private def solveStepH (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] B :=
  -(e.homotopyHomInv ∘ₗ solveZ e Φ Ψ)
private theorem solveStep_apply_eq_zero {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {u : W}
    (hΦ : Φ u = 0) (hΨ : Ψ u = 0) : solveStepG e Φ Ψ u = 0 ∧ solveStepH e Φ Ψ u = 0 := by
  simp only [solveStepG, solveStepH, solveZ, solveGamma, LinearMap.neg_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, hΦ, hΨ, map_zero, sub_zero, add_zero, neg_zero,
    and_self]
private theorem isHomogeneous_solveStep {𝒲 : ℤ → Submodule R W}
    {e : LinearHomotopyEquiv AA.differential BB.differential}
    (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1)) {r : ℤ}
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ 𝒲 (AA.grading.shift 1).piece (r + 1))
    (hΨ : LinearMap.IsHomogeneous Ψ 𝒲 (BB.grading.shift 1).piece r) :
    LinearMap.IsHomogeneous (solveStepG e Φ Ψ) 𝒲 (AA.grading.shift 1).piece r ∧
      LinearMap.IsHomogeneous (solveStepH e Φ Ψ) 𝒲 (BB.grading.shift 1).piece (r + -1) :=
  have hγ : LinearMap.IsHomogeneous (solveGamma e Φ Ψ) 𝒲 (AA.grading.shift 1).piece r :=
    (add_neg_cancel_right r 1 ▸
      (LinearMap.isHomogeneous_shift_piece_iff.2 hG.homotopyInvHom).comp hΦ).sub
      (add_zero r ▸ (LinearMap.isHomogeneous_shift_piece_iff.2 hG.inv).comp hΨ)
  have hZ : LinearMap.IsHomogeneous (solveZ e Φ Ψ) 𝒲 (BB.grading.shift 1).piece r :=
    hΨ.add (add_zero r ▸ (LinearMap.isHomogeneous_shift_piece_iff.2 hG.hom).comp hγ)
  ⟨hγ.sub (add_zero r ▸ (LinearMap.isHomogeneous_shift_piece_iff.2 hG.inv).comp hZ),
    ((LinearMap.isHomogeneous_shift_piece_iff.2 hG.homotopyHomInv).comp hZ).neg⟩
private theorem solveStep_eqs {dW : Module.End R W} {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + Φ ∘ₗ dW = 0)
    (hΨ : BB.differential ∘ₗ Ψ - Ψ ∘ₗ dW = e.hom ∘ₗ Φ) :
    (AA.differential ∘ₗ solveStepG e Φ Ψ - solveStepG e Φ Ψ ∘ₗ dW = -Φ) ∧
      (e.hom ∘ₗ solveStepG e Φ Ψ -
        (BB.differential ∘ₗ solveStepH e Φ Ψ + solveStepH e Φ Ψ ∘ₗ dW) = -Ψ) := by
  have hγ : ∀ w, AA.differential (solveGamma e Φ Ψ w) - solveGamma e Φ Ψ (dW w) = -Φ w :=
    fun w ↦ by
      have h1 := LinearMap.congr_fun e.dM_comp_homotopyInvHom_add_homotopyInvHom_comp_dM (Φ w)
      have h2 := congrArg e.inv (LinearMap.congr_fun hΨ w)
      have hΦw := LinearMap.congr_fun hΦ w
      simp only [solveGamma, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply, LinearMap.zero_apply, map_sub, e.dM_inv_apply] at h1 h2 hΦw ⊢
      rw [eq_sub_of_add_eq h1, eq_add_of_sub_eq h2, eq_neg_of_add_eq_zero_right hΦw, map_neg]; abel
  have hZ : ∀ w, BB.differential (solveZ e Φ Ψ w) = solveZ e Φ Ψ (dW w) := fun w ↦ by
    have hΨw := LinearMap.congr_fun hΨ w
    simp only [solveZ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add,
      e.dN_hom_apply] at hΨw ⊢
    rw [eq_add_of_sub_eq hΨw, eq_add_of_sub_eq (hγ w), map_add, map_neg]; abel
  refine ⟨LinearMap.ext fun w ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · simp only [solveStepG, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
      map_sub, e.dM_inv_apply, hZ w]
    rw [sub_sub_sub_comm, sub_self, sub_zero, hγ w]
  · have hH := LinearMap.congr_fun e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN
      (solveZ e Φ Ψ w)
    simp only [solveStepG, solveStepH, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, map_sub, map_neg] at hH ⊢
    rw [← hZ w, eq_sub_of_add_eq hH]
    simp only [solveZ, LinearMap.add_apply, LinearMap.comp_apply]; abel
private theorem solveStep_eqs_neg {dW : Module.End R W} {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ - Φ ∘ₗ dW = 0)
    (hΨ : BB.differential ∘ₗ Ψ + Ψ ∘ₗ dW = e.hom ∘ₗ Φ) :
    (AA.differential ∘ₗ solveStepG e (-Φ) (-Ψ) + solveStepG e (-Φ) (-Ψ) ∘ₗ dW = Φ) ∧
      (e.hom ∘ₗ solveStepG e (-Φ) (-Ψ) +
        (BB.differential ∘ₗ (-solveStepH e (-Φ) (-Ψ)) -
          (-solveStepH e (-Φ) (-Ψ)) ∘ₗ dW) = Ψ) := by
  have h := solveStep_eqs e (dW := -dW) (Φ := -Φ) (Ψ := -Ψ)
    (by simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_neg, neg_add_eq_sub]
        rw [← neg_sub, hΦ, neg_zero])
    (by simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_neg, ← neg_add', hΨ])
  exact ⟨by simpa only [LinearMap.comp_neg, sub_neg_eq_add, neg_neg] using h.1,
    by have h2 := h.2
       simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_neg] at h2 ⊢
       exact Eq.trans (by abel) h2⟩
end Solver

/-! #### Stage 1: lifting the right homotopy inverse -/

section Right
variable (f : AInfinityHom AA BB)

private noncomputable abbrev rightBarHomotopy (gT : ReducedTensorWords R B →ₗ[R] A)
    (hT : ReducedTensorWords R B →ₗ[R] B) : Module.End R (ReducedTensorWords R B) :=
  gradedCoderivAlong (BB.grading.shift 1) 1 (f.barMap ∘ₗ coalgHom R gT) LinearMap.id hT
private noncomputable abbrev rightDefectE (gT : ReducedTensorWords R B →ₗ[R] A) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ coalgHom R gT - coalgHom R gT ∘ₗ BB.barDifferential
private noncomputable abbrev rightDefectD (gT : ReducedTensorWords R B →ₗ[R] A)
    (hT : ReducedTensorWords R B →ₗ[R] B) : Module.End R (ReducedTensorWords R B) :=
  (f.barMap ∘ₗ coalgHom R gT - LinearMap.id) -
    (BB.barDifferential ∘ₗ rightBarHomotopy f gT hT +
      rightBarHomotopy f gT hT ∘ₗ BB.barDifferential)
private structure RightStage (k : ℕ) where
  gTaylor : ReducedTensorWords R B →ₗ[R] A
  hTaylor : ReducedTensorWords R B →ₗ[R] B
  hg : LinearMap.IsHomogeneous gTaylor (gradedPiece (BB.grading.shift 1))
    (AA.grading.shift 1).piece 0
  hh : LinearMap.IsHomogeneous hTaylor (gradedPiece (BB.grading.shift 1))
    (BB.grading.shift 1).piece (-1)
  hE : ∀ z ∈ filtration R B k, rightDefectE (AA := AA) (BB := BB) gTaylor z = 0
  hD : ∀ z ∈ filtration R B k, rightDefectD f gTaylor hTaylor z = 0

variable {f}
private noncomputable abbrev RightStage.obstructionΦ {k : ℕ} (S : RightStage f k) :
    ReducedTensorWords R B →ₗ[R] A :=
  letter R A ∘ₗ rightDefectE (AA := AA) (BB := BB) S.gTaylor ∘ₗ lengthProj R B ⟨k + 1, k.succ_pos⟩
private noncomputable abbrev RightStage.obstructionΨ {k : ℕ} (S : RightStage f k) :
    ReducedTensorWords R B →ₗ[R] B :=
  letter R B ∘ₗ rightDefectD f S.gTaylor S.hTaylor ∘ₗ lengthProj R B ⟨k + 1, k.succ_pos⟩
private theorem rightStage_defects_eq_ofLetter {k : ℕ} (S : RightStage f k)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (k + 1)) :
    rightDefectE (AA := AA) (BB := BB) S.gTaylor z =
        ofLetter R A (letter R A (rightDefectE (AA := AA) (BB := BB) S.gTaylor z)) ∧
      rightDefectD f S.gTaylor S.hTaylor z =
        ofLetter R B (letter R B (rightDefectD f S.gTaylor S.hTaylor z)) := by
  have hGc := isCoalgHom_coalgHom (R := R) S.gTaylor
  have hGh := isHomogeneous_coalgHom S.hg
  refine ⟨((AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hGc hGh).sub
    (hGc.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential))
      |>.apply_eq_ofLetter_letter_of_mem_filtration S.hE hz, ?_⟩
  have hFGh := add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp hGh
  have hΔ₁ := ((f.isCoalgHom_barMap.comp hGc).isGradedCoderivationAlong_sub
    (G := BB.grading.shift 1) (isCoalgHom_id B)).deconcatenation_apply z
  have hΔ₂ := (isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp hGc) (isCoalgHom_id B)
    S.hTaylor).deconcatenation_comp_add_comp_of_mem_filtration
    (isHomogeneous_gradedCoderivAlong (q := 1) hFGh (LinearMap.isHomogeneous_id _) S.hh)
    (by decide) BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential hFGh (fun w hw ↦ by
      simp only [LinearMap.comp_apply, f.barDifferential_barMap]
      exact congrArg f.barMap (sub_eq_zero.1 (S.hE w hw))) (fun _ _ ↦ rfl) hz
  refine eq_ofLetter_letter_of_deconcatenation_eq_of_mem_filtration (BB.grading.shift 1) 0
    (F := f.barMap ∘ₗ coalgHom R S.gTaylor) (F' := LinearMap.id) S.hD hz ?_
  simp only [InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.id_apply] at hΔ₁ ⊢
  rw [LinearMap.sub_apply, map_sub, hΔ₁, hΔ₂, sub_eq_iff_eq_add, add_add_add_comm]
  simp only [← LinearMap.add_apply, ← TensorProduct.map_add_left, ← TensorProduct.map_add_right,
    show rightDefectD f S.gTaylor S.hTaylor +
        (BB.barDifferential ∘ₗ rightBarHomotopy f S.gTaylor S.hTaylor +
          rightBarHomotopy f S.gTaylor S.hTaylor ∘ₗ BB.barDifferential) =
        f.barMap ∘ₗ coalgHom R S.gTaylor - LinearMap.id from
      LinearMap.ext fun _ ↦ sub_add_cancel _ _]
private theorem rightStage_obstruction_eqs {k : ℕ} (S : RightStage f k) :
    (AA.differential ∘ₗ S.obstructionΦ + S.obstructionΦ ∘ₗ BB.unaryBarDifferential = 0) ∧
      (BB.differential ∘ₗ S.obstructionΨ - S.obstructionΨ ∘ₗ BB.unaryBarDifferential =
        f.linearPart ∘ₗ S.obstructionΦ) := by
  have hE₁ : ∀ z ∈ filtration R B (k + 1), _ := fun z hz ↦ (rightStage_defects_eq_ofLetter S hz).1
  have hD₁ : ∀ z ∈ filtration R B (k + 1), _ := fun z hz ↦ (rightStage_defects_eq_ofLetter S hz).2
  refine ⟨by simpa only [one_zsmul] using
      obstruction_eq_of_barDifferential S.hE hE₁ (1 : ℤ) (rhs := 0) (fun w ↦ by
        simp only [rightDefectE, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
          map_sub, barDifferential_sq_apply, map_zero]; abel),
    by simpa only [neg_one_zsmul, ← sub_eq_add_neg] using
      obstruction_eq_of_barDifferential S.hD hD₁ (-1 : ℤ) (rhs := f.linearPart ∘ₗ S.obstructionΦ)
        (fun w ↦ by
          rw [LinearMap.comp_apply, ← f.barMap_ofLetter, RightStage.obstructionΦ,
            LinearMap.comp_apply, LinearMap.comp_apply,
            ← hE₁ _ (lengthProj_mem_filtration R B ⟨k + 1, k.succ_pos⟩ w)]
          simp only [rightDefectD, rightDefectE, LinearMap.sub_apply, LinearMap.add_apply,
            LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap,
            barDifferential_sq_apply, map_zero]; abel)⟩
private theorem rightStage_isHomogeneous_obstructions {k : ℕ} (S : RightStage f k) :
    LinearMap.IsHomogeneous S.obstructionΦ (gradedPiece (BB.grading.shift 1))
        (AA.grading.shift 1).piece (0 + 1) ∧
      LinearMap.IsHomogeneous S.obstructionΨ (gradedPiece (BB.grading.shift 1))
        (BB.grading.shift 1).piece 0 :=
  have hGh := isHomogeneous_coalgHom S.hg
  have hFGh := add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp hGh
  have hKh := isHomogeneous_gradedCoderivAlong (q := 1) hFGh (LinearMap.isHomogeneous_id _) S.hh
  ⟨isHomogeneous_obstruction (isHomogeneous_barDiff_comm hGh).2 _,
    isHomogeneous_obstruction ((hFGh.sub (LinearMap.isHomogeneous_id _)).sub
      (neg_add_cancel (1 : ℤ) ▸ (isHomogeneous_barDiff_comm hKh).1)) _⟩
private theorem rightStageSucc_defects {k : ℕ} (S : RightStage f k)
    {δg : ReducedTensorWords R B →ₗ[R] A} {δh : ReducedTensorWords R B →ₗ[R] B}
    (hδg₀ : ∀ u ∈ filtration R B k, δg u = 0) (hδh₀ : ∀ u ∈ filtration R B k, δh u = 0)
    (hsol₁ : AA.differential ∘ₗ δg - δg ∘ₗ BB.unaryBarDifferential = -S.obstructionΦ)
    (hsol₂ : f.linearPart ∘ₗ δg -
      (BB.differential ∘ₗ δh + δh ∘ₗ BB.unaryBarDifferential) = -S.obstructionΨ)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (k + 1)) :
    rightDefectE (AA := AA) (BB := BB) (S.gTaylor + δg) z = 0 ∧
      rightDefectD f (S.gTaylor + δg) (S.hTaylor + δh) z = 0 := by
  have hG_step := coalgHom_add_apply_of_mem_filtration (BB.grading.shift 1) (g := S.gTaylor) hδg₀
  refine ⟨?_, ?_⟩
  · have hEz := defect_eq_ofLetter_obstruction S.hE
      (fun w hw ↦ (rightStage_defects_eq_ofLetter S hw).1) hz
    have hsol₁z := LinearMap.congr_fun hsol₁ z
    simp only [LinearMap.sub_apply, LinearMap.neg_apply] at hsol₁z
    generalize S.obstructionΦ z = φ at hEz hsol₁z
    simp only [rightDefectE, LinearMap.sub_apply, LinearMap.comp_apply] at hEz hsol₁z ⊢
    rw [hG_step.2 z hz, barDifferential_perturb_apply BB hG_step.1 hG_step.2 hz, map_add,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      eq_add_of_sub_eq hEz, eq_add_of_sub_eq hsol₁z, map_add, map_neg]; abel
  · have hK_step := gradedCoderivAlong_add_apply_of_mem_filtration (BB.grading.shift 1) 1
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (S.gTaylor + δg)))
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom S.gTaylor)) (isCoalgHom_id B)
      (h := S.hTaylor) (fun u hu ↦ congrArg f.barMap (hG_step.1 u hu)) hδh₀
    have hDz := defect_eq_ofLetter_obstruction S.hD
      (fun w hw ↦ (rightStage_defects_eq_ofLetter S hw).2) hz
    have hsol₂z := LinearMap.congr_fun hsol₂ z
    simp only [LinearMap.sub_apply, LinearMap.neg_apply] at hsol₂z
    generalize S.obstructionΨ z = ψ at hDz hsol₂z
    simp only [rightDefectD, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hDz hsol₂z ⊢
    rw [hG_step.2 z hz, hK_step.2 z hz, barDifferential_perturb_apply BB hK_step.1 hK_step.2 hz,
      map_add, map_add, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, eq_add_of_sub_eq (eq_add_of_sub_eq hDz),
      eq_add_of_sub_eq hsol₂z, map_add, map_add, map_neg]; abel

section BuildRight
variable (f) (e : LinearHomotopyEquiv AA.differential BB.differential)
  (he : e.hom = f.linearPart) (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1))

private noncomputable def rightStageOne : RightStage f 1 where
  gTaylor := e.inv ∘ₗ letter R B
  hTaylor := e.homotopyHomInv ∘ₗ letter R B
  hg := add_zero (0 : ℤ) ▸ (LinearMap.isHomogeneous_shift_piece_iff.2 hG.inv).comp
    (isHomogeneous_letter (BB.grading.shift 1))
  hh := zero_add (-1 : ℤ) ▸ (LinearMap.isHomogeneous_shift_piece_iff.2 hG.homotopyHomInv).comp
    (isHomogeneous_letter (BB.grading.shift 1))
  hE := apply_eq_zero_of_mem_filtration_one R B <| LinearMap.ext fun b ↦ by
    simp only [rightDefectE, LinearMap.comp_apply, LinearMap.sub_apply, coalgHom_ofLetter,
      letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, e.dM_inv_apply, sub_self, LinearMap.zero_apply]
  hD := apply_eq_zero_of_mem_filtration_one R B <| LinearMap.ext fun b ↦ by
    have hB := LinearMap.congr_fun e.dN_comp_homotopyHomInv_add_homotopyHomInv_comp_dN b
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, he] at hB
    simp only [rightDefectD, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.id_apply, coalgHom_ofLetter, gradedCoderivAlong_ofLetter, letter_ofLetter,
      f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, ← map_add, ← map_sub, hB, sub_self,
      LinearMap.zero_apply]
private noncomputable def rightStageSucc {k : ℕ} (S : RightStage f k) :
    {S' : RightStage f (k + 1) //
      (∀ z ∈ filtration R B k, S'.gTaylor z = S.gTaylor z) ∧
        (∀ z ∈ filtration R B k, S'.hTaylor z = S.hTaylor z)} := by
  set δg := solveStepG e S.obstructionΦ S.obstructionΨ
  set δh := solveStepH e S.obstructionΦ S.obstructionΨ
  have hp₀ : ∀ u ∈ filtration R B k, lengthProj R B ⟨k + 1, k.succ_pos⟩ u = 0 := fun u hu ↦
    lengthProj_apply_eq_zero_of_mem_filtration R B (Nat.lt_succ_self k) hu
  have hδ₀ : ∀ u ∈ filtration R B k, δg u = 0 ∧ δh u = 0 := fun u hu ↦
    solveStep_apply_eq_zero e
      (by simp only [RightStage.obstructionΦ, LinearMap.comp_apply, hp₀ u hu, map_zero])
      (by simp only [RightStage.obstructionΨ, LinearMap.comp_apply, hp₀ u hu, map_zero])
  have hdeg := isHomogeneous_solveStep hG
    (rightStage_isHomogeneous_obstructions S).1 (rightStage_isHomogeneous_obstructions S).2
  have hob := rightStage_obstruction_eqs S
  have hsol := solveStep_eqs e hob.1 (he.symm ▸ hob.2)
  have hdef := fun {z} (hz : z ∈ filtration R B (k + 1)) ↦ rightStageSucc_defects S
    (fun u hu ↦ (hδ₀ u hu).1) (fun u hu ↦ (hδ₀ u hu).2) hsol.1 (he ▸ hsol.2) hz
  exact ⟨⟨S.gTaylor + δg, S.hTaylor + δh, S.hg.add hdeg.1,
    S.hh.add (zero_add (-1 : ℤ) ▸ hdeg.2), fun _ hz ↦ (hdef hz).1, fun _ hz ↦ (hdef hz).2⟩,
    fun z hz ↦ by rw [LinearMap.add_apply, (hδ₀ z hz).1, add_zero],
    fun z hz ↦ by rw [LinearMap.add_apply, (hδ₀ z hz).2, add_zero]⟩
private noncomputable def rightStageNat : ∀ n : ℕ, RightStage f n
  | 0 => let S := rightStageOne f e he hG
    ⟨S.gTaylor, S.hTaylor, S.hg, S.hh,
      fun _ hz ↦ by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero],
      fun _ hz ↦ by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]⟩
  | 1 => rightStageOne f e he hG
  | n + 2 => (rightStageSucc f e he hG (rightStageNat (n + 1))).1
private theorem rightStageNat_stabilises : ∀ n : ℕ,
    (∀ z ∈ filtration R B n,
        (rightStageNat f e he hG (n + 1)).gTaylor z = (rightStageNat f e he hG n).gTaylor z) ∧
      (∀ z ∈ filtration R B n,
        (rightStageNat f e he hG (n + 1)).hTaylor z = (rightStageNat f e he hG n).hTaylor z)
  | 0 => ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | n + 1 => (rightStageSucc f e he hG (rightStageNat f e he hG (n + 1))).2
private noncomputable def liftInv : AInfinityHom BB AA :=
  AInfinityHom.ofTaylor (stabilisingTaylor fun n ↦ (rightStageNat f e he hG n).gTaylor)
    (isHomogeneous_stabilisingTaylor (fun n ↦ (rightStageNat_stabilises f e he hG n).1)
      fun n ↦ (rightStageNat f e he hG n).hg) (LinearMap.ext fun z ↦ by
      have hstab := fun n ↦ (rightStageNat_stabilises f e he hG n).1
      obtain ⟨m, hm⟩ := exists_mem_filtration R B z
      have hE := congrArg (letter R A) ((rightStageNat f e he hG m).hE z hm)
      simp only [rightDefectE, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, map_zero,
        sub_eq_zero] at hE
      rw [← LinearMap.comp_apply (letter R A), AA.letter_comp_barDifferential,
        ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom] at hE
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        coalgHom_stabilisingTaylor_apply _ hstab hm,
        stabilisingTaylor_apply_of_mem_filtration hstab (BB.barDifferential_mem_filtration hm)]
      exact hE)
private noncomputable def liftRightHomotopy :
    Homotopy (f.comp (liftInv f e he hG)) (AInfinityHom.id BB) :=
  Homotopy.ofTaylor (stabilisingTaylor fun n ↦ (rightStageNat f e he hG n).hTaylor)
    (isHomogeneous_stabilisingTaylor (fun n ↦ (rightStageNat_stabilises f e he hG n).2)
      fun n ↦ (rightStageNat f e he hG n).hh) (LinearMap.ext fun z ↦ by
      have hg_stab := fun n ↦ (rightStageNat_stabilises f e he hG n).1
      have hh_stab := fun n ↦ (rightStageNat_stabilises f e he hG n).2
      obtain ⟨m, hm⟩ := exists_mem_filtration R B z
      have hG_eq : ∀ w ∈ filtration R B m,
          (liftInv f e he hG).barMap w = coalgHom R (rightStageNat f e he hG m).gTaylor w :=
        fun w hw ↦ by
          rw [liftInv, barMap_ofTaylor]; exact coalgHom_stabilisingTaylor_apply _ hg_stab hw
      exact taylor_homotopy_of_defect_zero (f.comp (liftInv f e he hG)) _ hh_stab hm
        ((rightStageNat f e he hG m).hD z hm)
        (by rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply, hG_eq z hm])
        (gradedCoderivAlong_stabilisingTaylor_apply (BB.grading.shift 1) 1
          (f.comp (liftInv f e he hG)).isCoalgHom_barMap
          (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom _))
          (AInfinityHom.id BB).isCoalgHom_barMap (isCoalgHom_id B) _ hh_stab
          (fun u hu ↦ by rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply, hG_eq u hu])
          (fun _ _ ↦ by rw [barMap_id, LinearMap.id_apply]) hm)
        (letter_comp_gradedCoderivAlong _ _ _ _ _))
end BuildRight
end Right

/-! #### Stage 2: lifting the left homotopy alongside a compatibility 2-homotopy -/

section Left
variable (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
  (H_B : Homotopy (f.comp g) (AInfinityHom.id BB))

private noncomputable abbrev leftBarHomotopy (kT : ReducedTensorWords R A →ₗ[R] A) :
    Module.End R (ReducedTensorWords R A) :=
  gradedCoderivAlong (AA.grading.shift 1) 1 (g.comp f).barMap LinearMap.id kT
private noncomputable abbrev leftBarTwoHomotopy (tT : ReducedTensorWords R A →ₗ[R] B) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  gradedCoderivAlong (AA.grading.shift 1) 0 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap tT
private noncomputable abbrev leftDefectM (kT : ReducedTensorWords R A →ₗ[R] A) :
    Module.End R (ReducedTensorWords R A) :=
  ((g.comp f).barMap - LinearMap.id) -
    (AA.barDifferential ∘ₗ leftBarHomotopy f g kT + leftBarHomotopy f g kT ∘ₗ AA.barDifferential)
private noncomputable abbrev leftDefectU (kT : ReducedTensorWords R A →ₗ[R] A)
    (tT : ReducedTensorWords R A →ₗ[R] B) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  (H_B.barHomotopy ∘ₗ f.barMap - f.barMap ∘ₗ leftBarHomotopy f g kT) -
    (BB.barDifferential ∘ₗ leftBarTwoHomotopy f g tT -
      leftBarTwoHomotopy f g tT ∘ₗ AA.barDifferential)
private structure LeftStage (k : ℕ) where
  kATaylor : ReducedTensorWords R A →ₗ[R] A
  tTaylor : ReducedTensorWords R A →ₗ[R] B
  hkA : LinearMap.IsHomogeneous kATaylor (gradedPiece (AA.grading.shift 1))
    (AA.grading.shift 1).piece (-1)
  ht : LinearMap.IsHomogeneous tTaylor (gradedPiece (AA.grading.shift 1))
    (BB.grading.shift 1).piece (-2)
  hM : ∀ z ∈ filtration R A k, leftDefectM f g kATaylor z = 0
  hU : ∀ z ∈ filtration R A k, leftDefectU f g H_B kATaylor tTaylor z = 0

variable {f g H_B}
private noncomputable abbrev LeftStage.obstructionΘ {k : ℕ} (S : LeftStage f g H_B k) :
    ReducedTensorWords R A →ₗ[R] A :=
  letter R A ∘ₗ leftDefectM f g S.kATaylor ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩
private noncomputable abbrev LeftStage.obstructionΥ {k : ℕ} (S : LeftStage f g H_B k) :
    ReducedTensorWords R A →ₗ[R] B :=
  letter R B ∘ₗ leftDefectU f g H_B S.kATaylor S.tTaylor ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩
private noncomputable def leftStageZero : LeftStage f g H_B 0 where
  kATaylor := 0; tTaylor := 0
  hkA := LinearMap.isHomogeneous_zero _ _ _; ht := LinearMap.isHomogeneous_zero _ _ _
  hM _ hz := by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]
  hU _ hz := by rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero]
private theorem leftStage_isGradedCoderivationAlong {k : ℕ} (S : LeftStage f g H_B k) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 0 (g.comp f).barMap LinearMap.id
        (leftDefectM f g S.kATaylor) ∧
      IsGradedCoderivationAlong (AA.grading.shift 1) 1 (f.barMap ∘ₗ (g.comp f).barMap) f.barMap
        (leftDefectU f g H_B S.kATaylor S.tTaylor) := by
  have hKAc := isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
    (g.comp f).isCoalgHom_barMap (isCoalgHom_id A) S.kATaylor
  have hKBf : IsGradedCoderivationAlong (AA.grading.shift 1) 1
      (f.barMap ∘ₗ (g.comp f).barMap) f.barMap (H_B.barHomotopy ∘ₗ f.barMap) := by
    have h := H_B.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom f.isCoalgHom_barMap
      f.isHomogeneous_barMap
    rwa [show (f.comp g).barMap ∘ₗ f.barMap = f.barMap ∘ₗ (g.comp f).barMap by
      rw [barMap_comp, barMap_comp, LinearMap.comp_assoc], barMap_id, LinearMap.id_comp] at h
  have hFGFh := add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp (g.comp f).isHomogeneous_barMap
  have hT_comm : IsGradedCoderivationAlong (AA.grading.shift 1) 1 (f.barMap ∘ₗ (g.comp f).barMap)
      f.barMap (BB.barDifferential ∘ₗ leftBarTwoHomotopy f g S.tTaylor -
        leftBarTwoHomotopy f g S.tTaylor ∘ₗ AA.barDifferential) := by
    have hone : ((1 * (-2 : ℤ)).negOnePow : ℤ) = 1 := by decide
    simpa only [zero_add, hone, Int.cast_one, one_smul] using
      (isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 0
        (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap
        S.tTaylor).comp_sub_negOnePow_smul_comp
        (isHomogeneous_gradedCoderivAlong (q := 0) hFGFh f.isHomogeneous_barMap S.ht)
        AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential (q := 1)
        (by decide) BB.isGradedCoderivation_barDifferential hFGFh
        (by rw [← LinearMap.comp_assoc, f.barDifferential_comp_barMap, LinearMap.comp_assoc,
          (g.comp f).barDifferential_comp_barMap, LinearMap.comp_assoc])
        f.barDifferential_comp_barMap
  exact ⟨((g.comp f).isCoalgHom_barMap.isGradedCoderivationAlong_sub (isCoalgHom_id A)).sub
      (hKAc.comp_add_comp (isHomogeneous_gradedCoderivAlong (q := 1)
          (g.comp f).isHomogeneous_barMap (LinearMap.isHomogeneous_id _) S.hkA)
        (by decide) AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential
        (by decide) AA.isGradedCoderivation_barDifferential (g.comp f).isHomogeneous_barMap
        (g.comp f).barDifferential_comp_barMap (by rw [LinearMap.comp_id, LinearMap.id_comp])),
    (hKBf.sub (by simpa only [LinearMap.comp_id] using
      f.isCoalgHom_barMap.comp_isGradedCoderivationAlong hKAc)).sub hT_comm⟩
private theorem leftStage_obstruction_eqs {k : ℕ} (S : LeftStage f g H_B k) :
    (AA.differential ∘ₗ S.obstructionΘ - S.obstructionΘ ∘ₗ AA.unaryBarDifferential = 0) ∧
      (BB.differential ∘ₗ S.obstructionΥ + S.obstructionΥ ∘ₗ AA.unaryBarDifferential =
        f.linearPart ∘ₗ S.obstructionΘ) := by
  have hM₁ : ∀ z ∈ filtration R A (k + 1), _ := fun z hz ↦
    (leftStage_isGradedCoderivationAlong S).1.apply_eq_ofLetter_letter_of_mem_filtration S.hM hz
  have hU₁ : ∀ z ∈ filtration R A (k + 1), _ := fun z hz ↦
    (leftStage_isGradedCoderivationAlong S).2.apply_eq_ofLetter_letter_of_mem_filtration S.hU hz
  refine ⟨by simpa only [neg_one_zsmul, ← sub_eq_add_neg] using
      obstruction_eq_of_barDifferential S.hM hM₁ (-1 : ℤ) (rhs := 0) (fun w ↦ by
        simp only [leftDefectM, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply, LinearMap.zero_apply, map_sub, map_add,
          (g.comp f).barDifferential_barMap, barDifferential_sq_apply, map_zero]; abel),
    by simpa only [one_zsmul] using
      obstruction_eq_of_barDifferential S.hU hU₁ (1 : ℤ) (rhs := f.linearPart ∘ₗ S.obstructionΘ)
        (fun w ↦ by
          have hHB := H_B.barMap_sub_barMap_apply
            (f.barMap (lengthProj R A ⟨k + 1, k.succ_pos⟩ w))
          rw [barMap_comp, barMap_id, LinearMap.comp_apply, LinearMap.id_apply,
            f.barDifferential_barMap] at hHB
          rw [LinearMap.comp_apply, ← f.barMap_ofLetter, LeftStage.obstructionΘ,
            LinearMap.comp_apply, LinearMap.comp_apply,
            ← hM₁ _ (lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w)]
          simp only [leftDefectU, leftDefectM, LinearMap.sub_apply, LinearMap.add_apply,
            LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap,
            barDifferential_sq_apply, map_zero]
          rw [barMap_comp, LinearMap.comp_apply, eq_sub_of_add_eq hHB.symm]; abel)⟩
private theorem leftStage_isHomogeneous_obstructions {k : ℕ} (S : LeftStage f g H_B k) :
    LinearMap.IsHomogeneous (-S.obstructionΘ) (gradedPiece (AA.grading.shift 1))
        (AA.grading.shift 1).piece (-1 + 1) ∧
      LinearMap.IsHomogeneous (-S.obstructionΥ) (gradedPiece (AA.grading.shift 1))
        (BB.grading.shift 1).piece (-1) :=
  have hKAh := isHomogeneous_gradedCoderivAlong (q := 1) (g.comp f).isHomogeneous_barMap
    (LinearMap.isHomogeneous_id _) S.hkA
  have hTh := isHomogeneous_gradedCoderivAlong (q := 0)
    (add_zero (0 : ℤ) ▸ f.isHomogeneous_barMap.comp (g.comp f).isHomogeneous_barMap)
    f.isHomogeneous_barMap S.ht
  ⟨(neg_add_cancel (1 : ℤ)).symm ▸ (isHomogeneous_obstruction
      (((g.comp f).isHomogeneous_barMap.sub (LinearMap.isHomogeneous_id _)).sub
        (neg_add_cancel (1 : ℤ) ▸ (isHomogeneous_barDiff_comm hKAh).1)) _).neg,
    (isHomogeneous_obstruction
      (((zero_add (-1 : ℤ) ▸ H_B.isHomogeneous_barHomotopy.comp f.isHomogeneous_barMap).sub
        (add_zero (-1 : ℤ) ▸ f.isHomogeneous_barMap.comp hKAh)).sub
        ((show (-2 : ℤ) + 1 = -1 from rfl) ▸ (isHomogeneous_barDiff_comm hTh).2)) _).neg⟩
private theorem leftStageSucc_defects {k : ℕ} (S : LeftStage f g H_B k)
    {δkA : ReducedTensorWords R A →ₗ[R] A} {δt : ReducedTensorWords R A →ₗ[R] B}
    (hδkA₀ : ∀ u ∈ filtration R A k, δkA u = 0) (hδt₀ : ∀ u ∈ filtration R A k, δt u = 0)
    (hsol₁ : AA.differential ∘ₗ δkA + δkA ∘ₗ AA.unaryBarDifferential = S.obstructionΘ)
    (hsol₂ : f.linearPart ∘ₗ δkA +
      (BB.differential ∘ₗ δt - δt ∘ₗ AA.unaryBarDifferential) = S.obstructionΥ)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (k + 1)) :
    leftDefectM f g (S.kATaylor + δkA) z = 0 ∧
      leftDefectU f g H_B (S.kATaylor + δkA) (S.tTaylor + δt) z = 0 := by
  have hKA_step := gradedCoderivAlong_add_apply_of_mem_filtration (AA.grading.shift 1) 1
    (g.comp f).isCoalgHom_barMap (g.comp f).isCoalgHom_barMap (isCoalgHom_id A)
    (h := S.kATaylor) (fun _ _ ↦ rfl) hδkA₀
  refine ⟨?_, ?_⟩
  · have hMz := defect_eq_ofLetter_obstruction S.hM (fun w hw ↦
      (leftStage_isGradedCoderivationAlong S).1.apply_eq_ofLetter_letter_of_mem_filtration
        S.hM hw) hz
    have hsol₁z := LinearMap.congr_fun hsol₁ z
    generalize S.obstructionΘ z = θ at hMz hsol₁z
    simp only [leftDefectM, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hMz hsol₁z ⊢
    rw [hKA_step.2 z hz, barDifferential_perturb_apply AA hKA_step.1 hKA_step.2 hz, map_add,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      eq_add_of_sub_eq (eq_add_of_sub_eq hMz), ← hsol₁z, map_add]; abel
  · have hT_step := gradedCoderivAlong_add_apply_of_mem_filtration (AA.grading.shift 1) 0
      (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap)
      (f.isCoalgHom_barMap.comp (g.comp f).isCoalgHom_barMap) f.isCoalgHom_barMap
      (h := S.tTaylor) (fun _ _ ↦ rfl) hδt₀
    have hUz := defect_eq_ofLetter_obstruction S.hU (fun w hw ↦
      (leftStage_isGradedCoderivationAlong S).2.apply_eq_ofLetter_letter_of_mem_filtration
        S.hU hw) hz
    have hsol₂z := LinearMap.congr_fun hsol₂ z
    generalize S.obstructionΥ z = υ at hUz hsol₂z
    simp only [leftDefectU, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply] at hUz hsol₂z ⊢
    rw [hKA_step.2 z hz, hT_step.2 z hz, barDifferential_perturb_apply AA hT_step.1 hT_step.2 hz,
      map_add, map_add, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply, eq_add_of_sub_eq (eq_add_of_sub_eq hUz),
      ← hsol₂z, map_add, map_sub]; abel

section BuildLeft
variable (f g H_B) (e : LinearHomotopyEquiv AA.differential BB.differential)
  (he : e.hom = f.linearPart) (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1))

private noncomputable def leftStageSucc {k : ℕ} (S : LeftStage f g H_B k) :
    {S' : LeftStage f g H_B (k + 1) //
      ∀ z ∈ filtration R A k, S'.kATaylor z = S.kATaylor z} := by
  set δkA := solveStepG e (-S.obstructionΘ) (-S.obstructionΥ)
  set δt := -(solveStepH e (-S.obstructionΘ) (-S.obstructionΥ))
  have hp₀ : ∀ u ∈ filtration R A k, lengthProj R A ⟨k + 1, k.succ_pos⟩ u = 0 := fun u hu ↦
    lengthProj_apply_eq_zero_of_mem_filtration R A (Nat.lt_succ_self k) hu
  have hδ₀ : ∀ u ∈ filtration R A k, δkA u = 0 ∧ δt u = 0 := fun u hu ↦ by
    have h := solveStep_apply_eq_zero e (Φ := -S.obstructionΘ) (Ψ := -S.obstructionΥ) (u := u)
      (by simp only [LeftStage.obstructionΘ, LinearMap.neg_apply, LinearMap.comp_apply,
        hp₀ u hu, map_zero, neg_zero])
      (by simp only [LeftStage.obstructionΥ, LinearMap.neg_apply, LinearMap.comp_apply,
        hp₀ u hu, map_zero, neg_zero])
    exact ⟨h.1, by simp only [δt, LinearMap.neg_apply, h.2, neg_zero]⟩
  have hdeg := isHomogeneous_solveStep hG
    (leftStage_isHomogeneous_obstructions S).1 (leftStage_isHomogeneous_obstructions S).2
  have hob := leftStage_obstruction_eqs S
  have hsol := solveStep_eqs_neg e hob.1 (he.symm ▸ hob.2)
  have hdef := fun {z} (hz : z ∈ filtration R A (k + 1)) ↦ leftStageSucc_defects S
    (fun u hu ↦ (hδ₀ u hu).1) (fun u hu ↦ (hδ₀ u hu).2) hsol.1 (he ▸ hsol.2) hz
  exact ⟨⟨S.kATaylor + δkA, S.tTaylor + δt, S.hkA.add hdeg.1, S.ht.add hdeg.2.neg,
    fun _ hz ↦ (hdef hz).1, fun _ hz ↦ (hdef hz).2⟩,
    fun z hz ↦ by rw [LinearMap.add_apply, (hδ₀ z hz).1, add_zero]⟩
private noncomputable def leftStageNat : ∀ n : ℕ, LeftStage f g H_B n
  | 0 => leftStageZero
  | n + 1 => (leftStageSucc f g H_B e he hG (leftStageNat n)).1
private theorem leftStageNat_stabilises (n : ℕ) :
    ∀ z ∈ filtration R A n,
      (leftStageNat f g H_B e he hG (n + 1)).kATaylor z =
        (leftStageNat f g H_B e he hG n).kATaylor z :=
  (leftStageSucc f g H_B e he hG (leftStageNat f g H_B e he hG n)).2
private noncomputable def liftLeftHomotopy : Homotopy (g.comp f) (AInfinityHom.id AA) :=
  Homotopy.ofTaylor (stabilisingTaylor fun n ↦ (leftStageNat f g H_B e he hG n).kATaylor)
    (isHomogeneous_stabilisingTaylor (leftStageNat_stabilises f g H_B e he hG)
      fun n ↦ (leftStageNat f g H_B e he hG n).hkA) (LinearMap.ext fun z ↦ by
      have hstab := leftStageNat_stabilises f g H_B e he hG
      obtain ⟨m, hm⟩ := exists_mem_filtration R A z
      exact taylor_homotopy_of_defect_zero (g.comp f) _ hstab hm
        ((leftStageNat f g H_B e he hG m).hM z hm) rfl
        (gradedCoderivAlong_stabilisingTaylor_apply (AA.grading.shift 1) 1
          (g.comp f).isCoalgHom_barMap (g.comp f).isCoalgHom_barMap
          (AInfinityHom.id AA).isCoalgHom_barMap (isCoalgHom_id A) _ hstab
          (fun _ _ ↦ rfl) (fun _ _ ↦ by rw [barMap_id, LinearMap.id_apply]) hm)
        (letter_comp_gradedCoderivAlong _ _ _ _ _))
end BuildLeft
end Left

/-! ### Lifting linear chain-homotopy equivalences and closure properties -/

namespace HomotopyEquiv

section OfLinear
variable (f : AInfinityHom AA BB) (e : LinearHomotopyEquiv AA.differential BB.differential)
  (he : e.hom = f.linearPart) (hG : e.IsHomogeneous AA.grading.piece BB.grading.piece (-1))

/-- Lift a homogeneous degree-`(-1)` linear chain-homotopy equivalence `e` with
`e.hom = f.linearPart` to a two-sided `A∞` homotopy equivalence with forward morphism `f`, inverse
linear part `e.inv`, and right linear homotopy `e.homotopyHomInv`. -/
noncomputable def ofLinear : HomotopyEquiv AA BB where
  hom := f; inv := liftInv f e he hG
  homotopyInvHomId := liftLeftHomotopy f (liftInv f e he hG) (liftRightHomotopy f e he hG) e he hG
  homotopyHomInvId := liftRightHomotopy f e he hG

@[simp] theorem hom_ofLinear : (ofLinear f e he hG).hom = f := (rfl)
@[simp] theorem linearPart_inv_ofLinear : (ofLinear f e he hG).inv.linearPart = e.inv :=
  LinearMap.ext fun b ↦ by
    dsimp only [ofLinear, liftInv]
    rw [linearPart_apply, AInfinityHom.taylor_ofTaylor,
      stabilisingTaylor_apply_of_mem_filtration (fun n ↦ (rightStageNat_stabilises f e he hG n).1)
        (ofLetter_mem_filtration R B b)]
    exact congrArg e.inv (letter_ofLetter R B b)
@[simp] theorem linearHomotopy_homotopyHomInvId_ofLinear :
    (ofLinear f e he hG).homotopyHomInvId.linearHomotopy = e.homotopyHomInv :=
  LinearMap.ext fun b ↦ by
    dsimp only [ofLinear, liftRightHomotopy]
    rw [Homotopy.linearHomotopy_ofTaylor, LinearMap.comp_apply,
      stabilisingTaylor_apply_of_mem_filtration (fun n ↦ (rightStageNat_stabilises f e he hG n).2)
        (ofLetter_mem_filtration R B b)]
    exact congrArg e.homotopyHomInv (letter_ofLetter R B b)
end OfLinear

section Trans
variable (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC)

/-- Compose two `A∞` homotopy equivalences by lifting the composite of their underlying linear
chain-homotopy equivalences along `e₂.hom.comp e₁.hom`. -/
noncomputable def trans : HomotopyEquiv AA CC :=
  ofLinear (e₂.hom.comp e₁.hom) (e₁.toLinearHomotopyEquiv.trans e₂.toLinearHomotopyEquiv)
    (by rw [LinearHomotopyEquiv.trans_hom, toLinearHomotopyEquiv_hom, toLinearHomotopyEquiv_hom,
      linearPart_comp])
    (e₁.isHomogeneous_toLinearHomotopyEquiv.trans e₂.isHomogeneous_toLinearHomotopyEquiv)

@[simp] theorem hom_trans : (e₁.trans e₂).hom = e₂.hom.comp e₁.hom := (rfl)
@[simp] theorem linearPart_inv_trans :
    (e₁.trans e₂).inv.linearPart = e₁.inv.linearPart ∘ₗ e₂.inv.linearPart := by
  rw [trans, linearPart_inv_ofLinear, LinearHomotopyEquiv.trans_inv,
    toLinearHomotopyEquiv_inv, toLinearHomotopyEquiv_inv]
end Trans
end HomotopyEquiv

/-- **Linear criterion for `A∞` homotopy equivalences.**  Over any commutative ring, an `A∞`
morphism is a two-sided `A∞` homotopy equivalence if and only if its linear part extends to a
homogeneous degree-`(-1)` linear chain-homotopy equivalence between the unary complexes. -/
theorem isHomotopyEquiv_iff_exists_linearHomotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ e : LinearHomotopyEquiv AA.differential BB.differential,
        e.hom = f.linearPart ∧ e.IsHomogeneous AA.grading.piece BB.grading.piece (-1) :=
  ⟨fun hf ↦ by
      obtain ⟨E, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
      exact ⟨E.toLinearHomotopyEquiv, E.toLinearHomotopyEquiv_hom,
        E.isHomogeneous_toLinearHomotopyEquiv⟩,
    fun ⟨e, he, hG⟩ ↦ (HomotopyEquiv.ofLinear f e he hG).isHomotopyEquiv_hom⟩

/-- `A∞` homotopy equivalences are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨e₁, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  obtain ⟨e₂, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv g).1 hg
  exact (e₁.trans e₂).isHomotopyEquiv_hom

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  have step : ∀ {f₁ f₂ : AInfinityHom AA BB} (s : A →ₗ[R] B),
      LinearMap.IsHomogeneous s AA.grading.piece BB.grading.piece (-1) →
      BB.differential ∘ₗ s + s ∘ₗ AA.differential = f₁.linearPart - f₂.linearPart →
      f₁.IsHomotopyEquiv → f₂.IsHomotopyEquiv := fun {f₁ f₂} s hs₀ hs hf₁ ↦ by
    obtain ⟨e, he, hG⟩ := (isHomotopyEquiv_iff_exists_linearHomotopyEquiv f₁).1 hf₁
    have hs' : e.hom - f₂.linearPart = BB.differential ∘ₗ s + s ∘ₗ AA.differential := by rw [he, hs]
    exact (isHomotopyEquiv_iff_exists_linearHomotopyEquiv f₂).2
      ⟨e.ofHomotopy f₂.differential_comp_linearPart s hs', e.ofHomotopy_hom _ _ hs',
        hG.ofHomotopy f₂.differential_comp_linearPart f₂.isHomogeneous_linearPart hs₀ hs'⟩
  refine ⟨step h.linearHomotopy h.isHomogeneous_linearHomotopy
      h.differential_comp_linearHomotopy_add,
    step (-h.linearHomotopy) h.isHomogeneous_linearHomotopy.neg ?_⟩
  rw [LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add,
    h.differential_comp_linearHomotopy_add, neg_sub]

/-- Two out of three: if `f` and `g ∘ f` are `A∞` homotopy equivalences, then so is `g`. -/
theorem IsHomotopyEquiv.of_precomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : g.IsHomotopyEquiv := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  exact (show Homotopy ((g.comp e.hom).comp e.inv) g by
    simpa only [comp_assoc, comp_id] using e.homotopyHomInvId.compRight g).isHomotopyEquiv_iff.1
    (hgf.comp e.isHomotopyEquiv_inv)

/-- Two out of three: if `g` and `g ∘ f` are `A∞` homotopy equivalences, then so is `f`. -/
theorem IsHomotopyEquiv.of_postcomp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hgf : (g.comp f).IsHomotopyEquiv) : f.IsHomotopyEquiv := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv g).1 hg
  exact (show Homotopy (e.inv.comp (e.hom.comp f)) f by
    simpa only [← comp_assoc, id_comp] using e.homotopyInvHomId.compLeft f).isHomotopyEquiv_iff.1
    (e.isHomotopyEquiv_inv.comp hgf)
end CommRing

end AInfinityHom

end TauCeti
