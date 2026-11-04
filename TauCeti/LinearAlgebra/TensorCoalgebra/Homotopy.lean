/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom.CoderivationAlong

/-!
# Transitivity and symmetry of homotopies of differential graded coalgebra morphisms

For internally graded modules `M` and `N` with degree-one square-zero coderivations `b_M`, `b_N` and
intertwining degree-zero coalgebra morphisms `F, F', F'' : Tᶜ(M) ⟶ Tᶜ(N)`, the co-Leibniz mismatch
in composing coderivation homotopies (`homotopyTrans`) or reversing one (`homotopySymm`) is
corrected by `b_N ∘ S - S ∘ b_M` for a degree-`(-2)` biderivation `S` built along `filtration R M`.

## References

* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapter 1, Section 1.2–1.3.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* M. Markl, *Transferring `A∞` (strongly homotopy associative) structures*, Rend. Circ. Mat.
  Palermo (2) Suppl. 79 (2006), 139–151.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-! ### Contractive biderivation recursion -/

private abbrev HW (R : Type uR) (M : Type uM) (N : Type uN) [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] :=
  ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N
private noncomputable abbrev GP {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M]
    [Module R M] (G : InternalGrading R M) := gradedPiece G

private noncomputable def biderivStep (G : InternalGrading R M) (q : ℤ) (F D₁ S D₂ : HW R M N) :
    HW R M N :=
  cutPrepend (letter R N ∘ₗ F) S +
    cutPrepend (letter R N ∘ₗ D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂
private def isBideriv (G : InternalGrading R M) (q : ℤ) (F F'' D₁ D₂ S : HW R M N)
    (w : ReducedTensorWords R M) : Prop :=
  deconcatenation R N (S w) = (TensorProduct.map S F'' +
    TensorProduct.map (D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂ +
    TensorProduct.map F S) (deconcatenation R M w)
private theorem biderivStep_apply_eq_zero_of_mem_filtration_one (G : InternalGrading R M) (q : ℤ)
    (F D₁ S D₂ : HW R M N) {z : ReducedTensorWords R M} (hz : z ∈ filtration R M 1) :
    biderivStep G q F D₁ S D₂ z = 0 := by
  simp only [biderivStep, LinearMap.add_apply, cutPrepend_apply_of_mem_filtration_one _ _ hz,
    add_zero]
private theorem biderivStep_congr_of_mem_filtration (G : InternalGrading R M) (q : ℤ)
    (F D₁ : HW R M N) {S S' D₂ D₂' : HW R M N} {n : ℕ}
    (hS : ∀ w ∈ filtration R M n, S w = S' w) (hD₂ : ∀ w ∈ filtration R M n, D₂ w = D₂' w)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    biderivStep G q F D₁ S D₂ z = biderivStep G q F D₁ S' D₂' z := by
  simp only [biderivStep, LinearMap.add_apply,
    cutPrepend_congr_of_mem_filtration_succ (fun _ _ ↦ rfl) hS hz,
    cutPrepend_congr_of_mem_filtration_succ (fun _ _ ↦ rfl) hD₂ hz]
private theorem isHomogeneous_biderivStep {G : InternalGrading R M} {H : InternalGrading R N}
    (q : ℤ) {F D₁ S D₂ : HW R M N} (hF : LinearMap.IsHomogeneous F (GP G) (GP H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (GP G) (GP H) (-1))
    (hS : LinearMap.IsHomogeneous S (GP G) (GP H) (-2))
    (hD₂ : LinearMap.IsHomogeneous D₂ (GP G) (GP H) (-1)) :
    LinearMap.IsHomogeneous (biderivStep G q F D₁ S D₂) (GP G) (GP H) (-2) := by
  have hα₁ : LinearMap.IsHomogeneous (letter R N ∘ₗ F) (GP G) H.piece 0 := by
    simpa using (isHomogeneous_letter H).comp hF
  have hα₂ : LinearMap.IsHomogeneous
      (letter R N ∘ₗ D₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (GP G) H.piece (-1) := by
    simpa using (isHomogeneous_letter H).comp (hD₁.comp (isHomogeneous_map_koszulTwist G q))
  exact LinearMap.IsHomogeneous.add (by simpa using isHomogeneous_cutPrepend hα₁ hS)
    (by simpa only [show (-1 : ℤ) + -1 = -2 by decide] using isHomogeneous_cutPrepend hα₂ hD₂)
private noncomputable def biderivSeq (G : InternalGrading R M) (F D₁ : HW R M N)
    (step : HW R M N → HW R M N) : ℕ → HW R M N
  | 0 => 0
  | n + 1 => biderivStep G 1 F D₁ (biderivSeq G F D₁ step n) (step (biderivSeq G F D₁ step n))
private theorem biderivSeq_stabilises (G : InternalGrading R M) (F D₁ : HW R M N)
    {step : HW R M N → HW R M N} (hstep : ∀ {n} {S₁ S₂ : HW R M N},
      (∀ w ∈ filtration R M n, S₁ w = S₂ w) → ∀ w ∈ filtration R M n, step S₁ w = step S₂ w) :
    ∀ n, ∀ z ∈ filtration R M n, biderivSeq G F D₁ step (n + 1) z = biderivSeq G F D₁ step n z
  | 0, z, hz => apply_eq_zero_of_mem_filtration_zero R M _ z hz
  | n + 1, _, hz =>
    let ih := biderivSeq_stabilises G F D₁ hstep n
    biderivStep_congr_of_mem_filtration G 1 F D₁ ih (hstep ih) hz
private noncomputable def biderivFix (G : InternalGrading R M) (F D₁ : HW R M N)
    (step : HW R M N → HW R M N) : HW R M N := filtrationLimit (biderivSeq G F D₁ step)
private theorem biderivFix_eq (G : InternalGrading R M) (F D₁ : HW R M N)
    {step : HW R M N → HW R M N} (hstep : ∀ {n} {S₁ S₂ : HW R M N},
      (∀ w ∈ filtration R M n, S₁ w = S₂ w) → ∀ w ∈ filtration R M n, step S₁ w = step S₂ w) :
    biderivFix G F D₁ step =
      biderivStep G 1 F D₁ (biderivFix G F D₁ step) (step (biderivFix G F D₁ step)) := by
  have hs := biderivSeq_stabilises G F D₁ hstep; refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z; have hn1 := filtration_monotone R M n.le_succ hn
  have hlim : ∀ w ∈ filtration R M n, biderivSeq G F D₁ step n w = biderivFix G F D₁ step w :=
    fun _ hw ↦ (filtrationLimit_apply_of_mem_filtration hs hw).symm
  rw [biderivFix, filtrationLimit_apply_of_mem_filtration hs hn1, biderivSeq]
  exact biderivStep_congr_of_mem_filtration G 1 F D₁ hlim (hstep hlim) hn1
private theorem isHomogeneous_biderivFix {G : InternalGrading R M} {H : InternalGrading R N}
    {F D₁ : HW R M N} {step : HW R M N → HW R M N} (hstep : ∀ {n} {S₁ S₂ : HW R M N},
      (∀ w ∈ filtration R M n, S₁ w = S₂ w) → ∀ w ∈ filtration R M n, step S₁ w = step S₂ w)
    (hF₀ : LinearMap.IsHomogeneous F (GP G) (GP H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (GP G) (GP H) (-1))
    (hhom : ∀ {S}, LinearMap.IsHomogeneous S (GP G) (GP H) (-2) →
      LinearMap.IsHomogeneous (step S) (GP G) (GP H) (-1)) :
    LinearMap.IsHomogeneous (biderivFix G F D₁ step) (GP G) (GP H) (-2) := by
  refine isHomogeneous_filtrationLimit (biderivSeq_stabilises G F D₁ hstep) fun n ↦ ?_
  induction n with
  | zero => exact LinearMap.isHomogeneous_zero _ _ _
  | succ _ ih => exact isHomogeneous_biderivStep 1 hF₀ hD₁ ih (hhom ih)
private theorem map_rTensor_eq (f h : HW R M N) {K : HW R M M}
    (w : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :
    TensorProduct.map f h (LinearMap.rTensor (ReducedTensorWords R M) K w) =
      TensorProduct.map (f ∘ₗ K) h w := by
  rw [LinearMap.rTensor_def, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]

private theorem deconcatenation_biderivStep_of_mem_filtration {G : InternalGrading R M} {q : ℤ}
    {F F' F'' D₁ S D₂ : HW R M N} (hS_fix : S = biderivStep G q F D₁ S D₂) (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (hD₁ : IsGradedCoderivationAlong G q F F' D₁) {n : ℕ}
    (ihS : ∀ w ∈ filtration R M n, isBideriv G q F F'' D₁ D₂ S w)
    (ihD₂ : ∀ w ∈ filtration R M n, deconcatenation R N (D₂ w) =
      (TensorProduct.map D₂ F'' +
        TensorProduct.map (F' ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) D₂)
        (deconcatenation R M w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    isBideriv G q F F'' D₁ D₂ S z := by
  let τ := ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have hFττ : (F ∘ₗ τ) ∘ₗ τ = F := by
    rw [LinearMap.comp_assoc, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.comp_id]
  have hD₁τ : D₁ ∘ₗ τ = ofLetter R N ∘ₗ (letter R N ∘ₗ (D₁ ∘ₗ τ)) +
      cutPrepend (letter R N ∘ₗ (D₁ ∘ₗ τ)) (F' ∘ₗ τ) + cutPrepend (letter R N ∘ₗ F) (D₁ ∘ₗ τ) := by
    have h1 := (hD₁.comp_isCoalgHom (isCoalgHom_map _)
      (isHomogeneous_map_koszulTwist G q)).eq_gradedCoderivAlong
      (hF.comp (isCoalgHom_map _)) (hF'.comp (isCoalgHom_map _))
    have h2 := gradedCoderivAlong_eq G q (F ∘ₗ τ) (F' ∘ₗ τ) (letter R N ∘ₗ (D₁ ∘ₗ τ))
    rw [hFττ, ← h1] at h2; exact h2
  have hSz : S z = cutPrepend (letter R N ∘ₗ F) S z +
      cutPrepend (letter R N ∘ₗ (D₁ ∘ₗ τ)) D₂ z := by
    simpa only [biderivStep, τ, LinearMap.add_apply, LinearMap.comp_assoc] using
      LinearMap.congr_fun hS_fix z
  rw [isBideriv, hSz, map_add, deconcatenation_cutPrepend_of_mem_filtration_succ _ ihS hz,
    deconcatenation_cutPrepend_of_mem_filtration_succ _ ihD₂ hz]
  calc _ = (TensorProduct.map (biderivStep G q F D₁ S D₂) F'' +
        TensorProduct.map (ofLetter R N ∘ₗ (letter R N ∘ₗ (D₁ ∘ₗ τ)) +
          cutPrepend (letter R N ∘ₗ (D₁ ∘ₗ τ)) (F' ∘ₗ τ) +
          cutPrepend (letter R N ∘ₗ F) (D₁ ∘ₗ τ)) D₂ +
        TensorProduct.map (ofLetter R N ∘ₗ (letter R N ∘ₗ F) +
          cutPrepend (letter R N ∘ₗ F) F) S) (deconcatenation R M z) := by
        simp only [biderivStep, τ, cutPrependLeft_add, cutPrependLeft_map,
          TensorProduct.map_add_left, LinearMap.add_apply]; abel
    _ = _ := by rw [← hS_fix, ← hD₁τ, ← hF.eq_ofLetter_add_cutPrepend]

private theorem deconcatenation_commutator_of_bideriv {G : InternalGrading R M}
    {H : InternalGrading R N} {F F' F'' D₁ S D₂ : HW R M N} {bM : HW R M M} {bN : HW R N N}
    (hbM : IsGradedCoderivation G 1 bM) (hbM₁ : LinearMap.IsHomogeneous bM (GP G) (GP G) 1)
    (hbN : IsGradedCoderivation H 1 bN) (hF₀ : LinearMap.IsHomogeneous F (GP G) (GP H) 0)
    (hD₁_hom : LinearMap.IsHomogeneous D₁ (GP G) (GP H) (-1))
    (hS_hom : LinearMap.IsHomogeneous S (GP G) (GP H) (-2))
    (hFb : bN ∘ₗ F = F ∘ₗ bM) (hF''b : bN ∘ₗ F'' = F'' ∘ₗ bM)
    (hD₁_eq : F - F' = bN ∘ₗ D₁ + D₁ ∘ₗ bM) (hD₂_eq : F' - F'' = bN ∘ₗ D₂ + D₂ ∘ₗ bM)
    {z : ReducedTensorWords R M} (hSz : isBideriv G 1 F F'' D₁ D₂ S z)
    (hSbMz : isBideriv G 1 F F'' D₁ D₂ S (bM z)) :
    let τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
    deconcatenation R N ((bN ∘ₗ S - S ∘ₗ bM) z) =
      TensorProduct.map (bN ∘ₗ S - S ∘ₗ bM) F'' (deconcatenation R M z) +
        TensorProduct.map (F ∘ₗ τ) (bN ∘ₗ S - S ∘ₗ bM) (deconcatenation R M z) +
        TensorProduct.map ((F - F') ∘ₗ τ) D₂ (deconcatenation R M z) -
        TensorProduct.map D₁ (F' - F'') (deconcatenation R M z) := by
  intro τ; have hτ_def : τ = ReducedTensorWords.map (R := R) (G.koszulTwist 1) := rfl
  set τN := ReducedTensorWords.map (R := R) (H.koszulTwist 1) with hτN_def
  have hττ (w) : τ (τ w) = w := by
    rw [← LinearMap.comp_apply, hτ_def, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]
  have hτF (w) : τN (F w) = F (τ w) := by
    simpa [← hτN_def, ← hτ_def] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp 1) w
  have hτS (w) : τN (S w) = S (τ w) := by
    simpa [show ((1 : ℤ) * -2).negOnePow = 1 by decide, ← hτN_def, ← hτ_def] using
      LinearMap.congr_fun (hS_hom.map_koszulTwist_comp 1) w
  have hτD₁ (w) : τN (D₁ (τ w)) = -D₁ w := by
    have h := LinearMap.congr_fun (hD₁_hom.map_koszulTwist_comp 1) (τ w)
    simpa [show ((1 : ℤ) * -1).negOnePow = -1 by decide, ← hτN_def, ← hτ_def, hττ] using h
  have hτb (w) : τ (bM w) = -bM (τ w) := by
    simpa [show ((1 : ℤ) * 1).negOnePow = -1 by decide, ← hτ_def] using
      LinearMap.congr_fun (hbM₁.map_koszulTwist_comp 1) w
  have hFb' (w) : bN (F w) = F (bM w) := LinearMap.congr_fun hFb w
  have hF''b' (w) : bN (F'' w) = F'' (bM w) := LinearMap.congr_fun hF''b w
  rw [hD₁_eq, hD₂_eq]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [hbN.deconcatenation_apply, hSz, hSbMz, hbM.deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [map_add, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearMap.sub_apply, ← hτN_def, ← hτ_def]
      simp only [hτF, hτS, hτD₁, hτb, hττ, hFb', hF''b', map_neg, TensorProduct.neg_tmul,
        TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
      abel
  | add _ _ hu hv =>
      simp only [map_add] at hu hv ⊢; convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-! ### Transitivity of coderivation homotopies -/

/-- **Composition of coderivation homotopies**: `D₁ + D₂ + (b_N ∘ S - S ∘ b_M)`. -/
noncomputable def homotopyTrans (G : InternalGrading R M)
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  let S := biderivFix G F D₁ fun _ ↦ D₂
  D₁ + D₂ + (bN ∘ₗ S - S ∘ₗ bM)

theorem homotopyTrans_apply_of_mem_filtration_one {G : InternalGrading R M} {q : ℤ}
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G q bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M 1) :
    homotopyTrans G F D₁ D₂ bM bN z = D₁ z + D₂ z := by
  have hS : ∀ w ∈ filtration R M 1, biderivFix G F D₁ (fun _ ↦ D₂) w = 0 := fun w hw ↦ by
    rw [biderivFix_eq G F D₁ (fun _ _ _ ↦ rfl)]
    exact biderivStep_apply_eq_zero_of_mem_filtration_one G 1 F D₁ _ D₂ hw
  simp only [homotopyTrans, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    hS z hz, hS (bM z) (hbM.mem_filtration hz), map_zero, sub_zero, add_zero]

@[simp] theorem homotopyTrans_ofLetter {G : InternalGrading R M}
    (F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) (a : M) :
    homotopyTrans G F D₁ D₂ bM bN (ofLetter R M a) =
      D₁ (ofLetter R M a) + D₂ (ofLetter R M a) :=
  homotopyTrans_apply_of_mem_filtration_one F D₁ D₂ hbM bN (ofLetter_mem_filtration R M a)

theorem isHomogeneous_homotopyTrans {G : InternalGrading R M} {H : InternalGrading R N}
    {F D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD₁ : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hD₂ : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) (-1))
    (hbM : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) :
    LinearMap.IsHomogeneous (homotopyTrans G F D₁ D₂ bM bN)
      (gradedPiece G) (gradedPiece H) (-1) := by
  have hS := isHomogeneous_biderivFix (fun _ _ _ ↦ rfl) hF₀ hD₁ fun _ ↦ hD₂
  exact (hD₁.add hD₂).add (LinearMap.IsHomogeneous.sub (by simpa using hbN.comp hS)
    (by simpa using hS.comp hbM))

/-- Under square-zero differentials `bM` and `bN`, `homotopyTrans` satisfies the composite homotopy
equation between `F` and `F''` whenever `D₁` and `D₂` witness homotopies `F ~ F'` and `F' ~ F''`. -/
theorem homotopyTrans_eq {G : InternalGrading R M}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0)
    (hD₁_eq : F - F' = bN ∘ₗ D₁ + D₁ ∘ₗ bM) (hD₂_eq : F' - F'' = bN ∘ₗ D₂ + D₂ ∘ₗ bM) :
    F - F'' = bN ∘ₗ homotopyTrans G F D₁ D₂ bM bN + homotopyTrans G F D₁ D₂ bM bN ∘ₗ bM := by
  refine LinearMap.ext fun z ↦ ?_
  have hd₁ := LinearMap.congr_fun hD₁_eq z; have hd₂ := LinearMap.congr_fun hD₂_eq z
  have hbm : bM (bM z) = 0 := LinearMap.congr_fun hbM_sq z
  have hbn (w) : bN (bN w) = 0 := LinearMap.congr_fun hbN_sq w
  simp only [homotopyTrans, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_add, map_sub, hbm, hbn, map_zero] at hd₁ hd₂ ⊢
  calc F z - F'' z = (F z - F' z) + (F' z - F'' z) := by abel
    _ = _ := by rw [hd₁, hd₂]; abel

/-- `homotopyTrans` is a `1`-twisted coderivation along `F` and `F''`. -/
theorem isGradedCoderivationAlong_homotopyTrans {G : InternalGrading R M} {H : InternalGrading R N}
    {F F' F'' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : IsGradedCoderivation H 1 bN) (hFb : bN ∘ₗ F = F ∘ₗ bM) (hF''b : bN ∘ₗ F'' = F'' ∘ₗ bM)
    (hD₁ : IsGradedCoderivationAlong G 1 F F' D₁)
    (hD₁_hom : LinearMap.IsHomogeneous D₁ (gradedPiece G) (gradedPiece H) (-1))
    (hD₁_eq : F - F' = bN ∘ₗ D₁ + D₁ ∘ₗ bM) (hD₂ : IsGradedCoderivationAlong G 1 F' F'' D₂)
    (hD₂_hom : LinearMap.IsHomogeneous D₂ (gradedPiece G) (gradedPiece H) (-1))
    (hD₂_eq : F' - F'' = bN ∘ₗ D₂ + D₂ ∘ₗ bM) :
    IsGradedCoderivationAlong G 1 F F'' (homotopyTrans G F D₁ D₂ bM bN) := by
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1) with hτ_def
  set S := biderivFix G F D₁ fun _ ↦ D₂
  have hS_bideriv : ∀ n : ℕ, ∀ w ∈ filtration R M n, isBideriv G 1 F F'' D₁ D₂ S w := by
    intro n; induction n with
    | zero => intro w hw; rw [filtration_zero, Submodule.mem_bot] at hw; simp [isBideriv, hw]
    | succ _ ih =>
        exact fun w hw ↦ deconcatenation_biderivStep_of_mem_filtration
          (biderivFix_eq G F D₁ (step := fun _ ↦ D₂) (fun _ _ _ ↦ rfl)) hF hF' hD₁ ih
          (fun _ _ ↦ by rw [hD₂.deconcatenation_apply, map_rTensor_eq]; rfl) hw
  have hS_global (w) : isBideriv G 1 F F'' D₁ D₂ S w :=
    let ⟨n, hn⟩ := exists_mem_filtration R M w; hS_bideriv n w hn
  rw [isGradedCoderivationAlong_iff, show homotopyTrans G F D₁ D₂ bM bN =
    D₁ + D₂ + (bN ∘ₗ S - S ∘ₗ bM) from rfl]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, ← hτ_def]
  rw [map_add, map_add, hD₁.deconcatenation_apply, hD₂.deconcatenation_apply,
    deconcatenation_commutator_of_bideriv hbM hbM₁ hbN hF₀ hD₁_hom
      (isHomogeneous_biderivFix (fun _ _ _ ↦ rfl) hF₀ hD₁_hom fun _ ↦ hD₂_hom)
      hFb hF''b hD₁_eq hD₂_eq (hS_global z) (hS_global (bM z))]
  simp only [← hτ_def, map_rTensor_eq]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul _ _ =>
      simp only [TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
  | add _ _ hu hv =>
      simp only [map_add] at hu hv ⊢; convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-! ### Symmetry of coderivation homotopies -/

private noncomputable def symmStep (D : HW R M N) (bM : HW R M M) (bN : HW R N N) (S : HW R M N) :
    HW R M N := -D - (bN ∘ₗ S - S ∘ₗ bM)
private theorem symmStep_congr {G : InternalGrading R M} {D : HW R M N} {bM : HW R M M}
    (hbM : IsGradedCoderivation G 1 bM) {bN : HW R N N} {n : ℕ} {S₁ S₂ : HW R M N}
    (hS : ∀ w ∈ filtration R M n, S₁ w = S₂ w) :
    ∀ w ∈ filtration R M n, symmStep D bM bN S₁ w = symmStep D bM bN S₂ w := fun w hw ↦ by
  simp only [symmStep, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    hS w hw, hS (bM w) (hbM.mem_filtration hw)]
private theorem isHomogeneous_symmStep {G : InternalGrading R M} {H : InternalGrading R N}
    {D S : HW R M N} {bM : HW R M M} {bN : HW R N N}
    (hD : LinearMap.IsHomogeneous D (GP G) (GP H) (-1))
    (hbM₁ : LinearMap.IsHomogeneous bM (GP G) (GP G) 1)
    (hbN₁ : LinearMap.IsHomogeneous bN (GP H) (GP H) 1)
    (hS : LinearMap.IsHomogeneous S (GP G) (GP H) (-2)) :
    LinearMap.IsHomogeneous (symmStep D bM bN S) (GP G) (GP H) (-1) :=
  hD.neg.sub (LinearMap.IsHomogeneous.sub (by simpa using hbN₁.comp hS)
    (by simpa using hS.comp hbM₁))

/-- **Reversal of a coderivation homotopy**: `-D - (b_N ∘ S - S ∘ b_M)`. -/
noncomputable def homotopySymm (G : InternalGrading R M)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  symmStep D bM bN (biderivFix G F D (symmStep D bM bN))

theorem homotopySymm_apply_of_mem_filtration_one {G : InternalGrading R M}
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M 1) :
    homotopySymm G F D bM bN z = -D z := by
  have hS : ∀ w ∈ filtration R M 1, biderivFix G F D (symmStep D bM bN) w = 0 := fun w hw ↦ by
    rw [biderivFix_eq G F D (symmStep_congr hbM)]
    exact biderivStep_apply_eq_zero_of_mem_filtration_one G 1 F D _ _ hw
  simp only [homotopySymm, symmStep, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, hS z hz, hS (bM z) (hbM.mem_filtration hz), map_zero, sub_zero]

@[simp] theorem homotopySymm_ofLetter {G : InternalGrading R M}
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N) (a : M) :
    homotopySymm G F D bM bN (ofLetter R M a) = -D (ofLetter R M a) :=
  homotopySymm_apply_of_mem_filtration_one F D hbM bN (ofLetter_mem_filtration R M a)

theorem isHomogeneous_homotopySymm {G : InternalGrading R M} {H : InternalGrading R N}
    {F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN₁ : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) :
    LinearMap.IsHomogeneous (homotopySymm G F D bM bN) (gradedPiece G) (gradedPiece H) (-1) :=
  isHomogeneous_symmStep hD hbM₁ hbN₁
    (isHomogeneous_biderivFix (symmStep_congr hbM) hF₀ hD (isHomogeneous_symmStep hD hbM₁ hbN₁))

/-- Under square-zero differentials `bM` and `bN`, `homotopySymm` satisfies the reversed homotopy
equation between `F'` and `F` whenever `D` witnesses `F ~ F'`. -/
theorem homotopySymm_eq {G : InternalGrading R M}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0) (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) :
    F' - F = bN ∘ₗ homotopySymm G F D bM bN + homotopySymm G F D bM bN ∘ₗ bM := by
  refine LinearMap.ext fun z ↦ ?_
  have hd := LinearMap.congr_fun hD_eq z
  have hbm : bM (bM z) = 0 := LinearMap.congr_fun hbM_sq z
  have hbn (w) : bN (bN w) = 0 := LinearMap.congr_fun hbN_sq w
  simp only [homotopySymm, symmStep, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, map_sub, map_neg, hbm, hbn, map_zero] at hd ⊢
  calc F' z - F z = -(F z - F' z) := by abel
    _ = _ := by rw [hd]; abel

/-- `homotopySymm` is a `1`-twisted coderivation along `F'` and `F`. -/
theorem isGradedCoderivationAlong_homotopySymm {G : InternalGrading R M} {H : InternalGrading R N}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1) (hbM_sq : bM ∘ₗ bM = 0)
    (hbN : IsGradedCoderivation H 1 bN)
    (hbN₁ : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) (hbN_sq : bN ∘ₗ bN = 0)
    (hFb : bN ∘ₗ F = F ∘ₗ bM) (hD : IsGradedCoderivationAlong G 1 F F' D)
    (hD_hom : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) :
    IsGradedCoderivationAlong G 1 F' F (homotopySymm G F D bM bN) := by
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1) with hτ_def
  set S := biderivFix G F D (symmStep D bM bN); set M' := homotopySymm G F D bM bN
  have hM'_unfold : M' = -D - (bN ∘ₗ S - S ∘ₗ bM) := rfl
  have hM'_eq : F' - F = bN ∘ₗ M' + M' ∘ₗ bM := homotopySymm_eq hbM_sq hbN_sq hD_eq
  have hS_hom := isHomogeneous_biderivFix (symmStep_congr hbM) hF₀ hD_hom
    (isHomogeneous_symmStep hD_hom hbM₁ hbN₁)
  have hcoupled : ∀ n : ℕ, (∀ w ∈ filtration R M n, isBideriv G 1 F F D M' S w) ∧
      (∀ w ∈ filtration R M n, deconcatenation R N (M' w) =
        (TensorProduct.map M' F + TensorProduct.map (F' ∘ₗ τ) M') (deconcatenation R M w)) := by
    intro n; induction n with
    | zero => refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩ <;>
        (rw [filtration_zero, Submodule.mem_bot] at hw; simp [isBideriv, hw])
    | succ n ih =>
        have hS_succ : ∀ w ∈ filtration R M (n + 1), isBideriv G 1 F F D M' S w := fun w hw ↦
          deconcatenation_biderivStep_of_mem_filtration
            (biderivFix_eq G F D (symmStep_congr hbM)) hF hF' hD ih.1 ih.2 hw
        refine ⟨hS_succ, fun z hz ↦ ?_⟩
        rw [hM'_unfold, LinearMap.sub_apply, LinearMap.neg_apply, map_sub, map_neg,
          hD.deconcatenation_apply,
          deconcatenation_commutator_of_bideriv hbM hbM₁ hbN hF₀ hD_hom hS_hom hFb hFb hD_eq hM'_eq
            (hS_succ z hz) (hS_succ (bM z) (hbM.mem_filtration hz))]
        simp only [← hτ_def, hM'_unfold, map_rTensor_eq, LinearMap.add_apply]
        induction deconcatenation R M z using TensorProduct.inductionOn with
        | tmul _ _ =>
            simp only [TensorProduct.map_tmul, LinearMap.sub_apply, LinearMap.neg_apply,
              LinearMap.comp_apply, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
              TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
        | add _ _ hu hv =>
            simp only [map_add] at hu hv ⊢; convert congrArg₂ (· + ·) hu hv using 1 <;> abel
  rw [isGradedCoderivationAlong_iff]; refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, ← hτ_def, map_rTensor_eq] using
    (hcoupled n).2 z hn

end TauCeti.ReducedTensorWords
