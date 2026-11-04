/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom
import TauCeti.LinearAlgebra.TensorCoalgebra.Coassoc
import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation

/-!
# Taylor expansion of coderivations along coalgebra morphisms

For coalgebra morphisms `F F' : Tᶜ(M) ⟶ Tᶜ(N)` of reduced tensor coalgebras and a linear map
`δ : Tᶜ(M) ⟶ N` of Taylor components, there is a unique `(F, F')`-coderivation `D`
(`gradedCoderivAlong`) with twist parameter `q` and letter component `π ∘ D = δ`, inducing
`gradedCoderivAlongEquivTaylor`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.6--3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7 (2003).
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti.ReducedTensorWords

/-! ### Cutting and prepending -/

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Cut a reduced tensor word into two nonempty parts, map them by `α` and `Φ`, and prepend. -/
noncomputable def cutPrepend (α : ReducedTensorWords R M →ₗ[R] N)
    (Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  TensorProduct.lift (prepend R N) ∘ₗ TensorProduct.map α Φ ∘ₗ deconcatenation R M

theorem cutPrepend_subword (α : ReducedTensorWords R M →ₗ[R] N)
    (Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    cutPrepend α Φ (subword R x a b) = ∑ d ∈ Finset.range b,
      prepend R N (α (subword R x a d)) (Φ (subword R x (a + d) (b - d))) := by
  rw [cutPrepend, LinearMap.comp_apply, LinearMap.comp_apply, map_deconcatenation_subword, map_sum]
  simp only [TensorProduct.lift.tmul]
@[simp] theorem letter_cutPrepend_apply (α : ReducedTensorWords R M →ₗ[R] N)
    (Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) (z : ReducedTensorWords R M) :
    letter R N (cutPrepend α Φ z) = 0 :=
  LinearMap.congr_fun (TensorProduct.ext' fun a w ↦ letter_prepend a w :
    letter R N ∘ₗ TensorProduct.lift (prepend R N) = 0) _
@[simp] theorem cutPrepend_ofLetter (α : ReducedTensorWords R M →ₗ[R] N)
    (Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) (a : M) :
    cutPrepend α Φ (ofLetter R M a) = 0 := by
  simp only [cutPrepend, LinearMap.comp_apply, deconcatenation_ofLetter, map_zero]
theorem cutPrepend_apply_of_mem_filtration_one (α : ReducedTensorWords R M →ₗ[R] N)
    (Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M 1) : cutPrepend α Φ z = 0 :=
  apply_eq_zero_of_mem_filtration_one R M (LinearMap.ext (cutPrepend_ofLetter α Φ)) z hz

theorem cutPrepend_congr_of_mem_filtration_succ {α₁ α₂ : ReducedTensorWords R M →ₗ[R] N}
    {Φ₁ Φ₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {n : ℕ}
    (hα : ∀ u ∈ filtration R M n, α₁ u = α₂ u) (hΦ : ∀ v ∈ filtration R M n, Φ₁ v = Φ₂ v)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    cutPrepend α₁ Φ₁ z = cutPrepend α₂ Φ₂ z := by
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  simp only [cutPrepend, LinearMap.comp_apply, ← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v => simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
      TensorProduct.lift.tmul, hα u.1 u.2, hΦ v.1 v.2]
  | add _ _ hx hy => simp only [map_add, hx, hy]

theorem cutPrepend_mem_filtration_succ (α : ReducedTensorWords R M →ₗ[R] N)
    {Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {n : ℕ}
    (hΦ : ∀ v ∈ filtration R M n, Φ v ∈ filtration R N n) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (n + 1)) : cutPrepend α Φ z ∈ filtration R N (n + 1) := by
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  simp only [cutPrepend, LinearMap.comp_apply, ← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul _ v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        TensorProduct.lift.tmul]
      exact prepend_mem_filtration R N _ (hΦ v.1 v.2)
  | add _ _ hx hy => simp only [map_add]; exact add_mem hx hy

theorem isHomogeneous_cutPrepend {G : InternalGrading R M} {H : InternalGrading R N} {r₁ r₂ : ℤ}
    {α : ReducedTensorWords R M →ₗ[R] N} {Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hα : LinearMap.IsHomogeneous α (gradedPiece G) H.piece r₁)
    (hΦ : LinearMap.IsHomogeneous Φ (gradedPiece G) (gradedPiece H) r₂) :
    LinearMap.IsHomogeneous (cutPrepend α Φ) (gradedPiece G) (gradedPiece H) (r₁ + r₂) := by
  rw [LinearMap.isHomogeneous_def]; intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ cutPrepend α Φ w ∈ gradedPiece H (D + (r₁ + r₂))) hz ?_ ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    rw [of_tprod_eq_subword R hn, cutPrepend_subword]; refine Submodule.sum_mem _ fun d hd ↦ ?_
    rw [Finset.mem_range] at hd; rcases Nat.eq_zero_or_pos d with rfl | _
    · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]; exact zero_mem _
    · have h1 : ∑ j ∈ Finset.range n, g (0 + j) = D := by
        rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
        exact Finset.sum_congr rfl fun _ _ ↦ by simp [hg]
      have hsum : (∑ j ∈ Finset.range d, g (0 + j)) +
          ∑ j ∈ Finset.range (n - d), g (0 + d + j) = D := by
        rw [← h1, ← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
        simp only [Nat.add_assoc]
      rw [show D + (r₁ + r₂) = ((∑ j ∈ Finset.range d, g (0 + j)) + r₁) +
          ((∑ j ∈ Finset.range (n - d), g (0 + d + j)) + r₂) by omega]
      exact prepend_mem_gradedPiece
        (hα.map_mem (subword_mem_gradedPiece x g hxg 0 d (by omega)))
        (hΦ.map_mem (subword_mem_gradedPiece x g hxg (0 + d) (n - d) (by omega)))
  · rw [map_zero]; exact zero_mem _
  · intro _ _ _ _ hu hv; rw [map_add]; exact add_mem hu hv
  · intro _ _ _ hu; rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- Apply `α` to the first of three cut blocks, `Ψ` to the remaining two, and prepend. -/
noncomputable def cutPrependLeft (α : ReducedTensorWords R M →ₗ[R] N)
    (Ψ : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M →ₗ[R]
      ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) :
    ReducedTensorWords R M ⊗[R] ReducedTensorWords R M →ₗ[R]
      ReducedTensorWords R N ⊗[R] ReducedTensorWords R N :=
  TensorProduct.map (TensorProduct.lift (prepend R N)) LinearMap.id ∘ₗ
    (TensorProduct.assoc R N _ _).symm.toLinearMap ∘ₗ TensorProduct.map α Ψ ∘ₗ
    (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ (deconcatenation R M)

@[simp] theorem cutPrependLeft_add (α : ReducedTensorWords R M →ₗ[R] N)
    (Ψ₁ Ψ₂ : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M →ₗ[R]
      ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) :
    cutPrependLeft α (Ψ₁ + Ψ₂) = cutPrependLeft α Ψ₁ + cutPrependLeft α Ψ₂ := by
  simp only [cutPrependLeft, TensorProduct.map_add_right, LinearMap.comp_add, LinearMap.add_comp]

@[simp] theorem cutPrependLeft_map (α : ReducedTensorWords R M →ₗ[R] N)
    (L R' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    cutPrependLeft α (TensorProduct.map L R') = TensorProduct.map (cutPrepend α L) R' := by
  refine TensorProduct.ext' fun x y ↦ ?_
  simp only [cutPrependLeft, cutPrepend, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul]
  induction deconcatenation R M x using TensorProduct.inductionOn with
  | tmul u v => simp only [LinearEquiv.coe_coe, TensorProduct.assoc_tmul, TensorProduct.map_tmul,
      TensorProduct.assoc_symm_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
  | add _ _ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]

theorem deconcatenation_cutPrepend_of_mem_filtration_succ (α : ReducedTensorWords R M →ₗ[R] N)
    {Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {Ψ : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M →ₗ[R]
      ReducedTensorWords R N ⊗[R] ReducedTensorWords R N} {n : ℕ}
    (hΦ : ∀ v ∈ filtration R M n, deconcatenation R N (Φ v) = Ψ (deconcatenation R M v))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N (cutPrepend α Φ z) =
      TensorProduct.map (ofLetter R N ∘ₗ α) Φ (deconcatenation R M z) +
        cutPrependLeft α Ψ (deconcatenation R M z) := by
  let μ := TensorProduct.map (TensorProduct.lift (prepend R N)) LinearMap.id ∘ₗ
    (TensorProduct.assoc R N (ReducedTensorWords R N) (ReducedTensorWords R N)).symm.toLinearMap
  have hμ (a : N) : LinearMap.rTensor (ReducedTensorWords R N) (prepend R N a) =
      μ ∘ₗ TensorProduct.mk R N _ a := TensorProduct.ext' fun _ _ ↦ by simp [μ]
  have hstep : deconcatenation R N ∘ₗ TensorProduct.lift (prepend R N) ∘ₗ TensorProduct.map α Φ =
      TensorProduct.map (ofLetter R N ∘ₗ α) Φ +
        μ ∘ₗ TensorProduct.map α (deconcatenation R N ∘ₗ Φ) :=
    TensorProduct.ext' fun _ _ ↦ by simp [deconcatenation_prepend, LinearMap.congr_fun (hμ _)]
  have hcongr : TensorProduct.map α (deconcatenation R N ∘ₗ Φ) (deconcatenation R M z) =
      TensorProduct.map α Ψ
        (LinearMap.lTensor _ (deconcatenation R M) (deconcatenation R M z)) := by
    rw [LinearMap.lTensor_def, ← LinearMap.comp_apply (TensorProduct.map α Ψ),
      ← TensorProduct.map_comp, LinearMap.comp_id]
    obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
    rw [← hw]; clear hw; induction w using TensorProduct.inductionOn with
    | tmul _ v => simp [TensorProduct.mapIncl, hΦ v.1 v.2]
    | add _ _ h₁ h₂ => simp [h₁, h₂]
  have hcoassoc := LinearMap.congr_fun (deconcatenation_coassoc R M) z
  have hstep_z := LinearMap.congr_fun hstep (deconcatenation R M z)
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at hcoassoc hstep_z
  rw [cutPrepend, LinearMap.comp_apply, LinearMap.comp_apply, hstep_z, hcongr, ← hcoassoc]; rfl

theorem deconcatenation_cutPrepend (α : ReducedTensorWords R M →ₗ[R] N)
    {Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {Ψ : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M →ₗ[R]
      ReducedTensorWords R N ⊗[R] ReducedTensorWords R N}
    (hΦ : ∀ v, deconcatenation R N (Φ v) = Ψ (deconcatenation R M v)) (z : ReducedTensorWords R M) :
    deconcatenation R N (cutPrepend α Φ z) =
      TensorProduct.map (ofLetter R N ∘ₗ α) Φ (deconcatenation R M z) +
        cutPrependLeft α Ψ (deconcatenation R M z) :=
  let ⟨n, hn⟩ := exists_mem_filtration R M z
  deconcatenation_cutPrepend_of_mem_filtration_succ α (fun v _ ↦ hΦ v)
    (filtration_monotone R M n.le_succ hn)

theorem IsCoalgHom.eq_ofLetter_add_cutPrepend
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F) :
    F = ofLetter R N ∘ₗ (letter R N ∘ₗ F) + cutPrepend (letter R N ∘ₗ F) F := by
  conv_lhs => rw [hF.eq_coalgHom]
  conv_rhs => rw [hF.eq_coalgHom]
  rw [letter_comp_coalgHom]; refine linearMap_ext R M fun n x ↦ ?_
  rw [of_tprod_eq_subword R n.2, coalgHom_subword, LinearMap.add_apply, cutPrepend_subword]
  simp only [LinearMap.comp_apply]

/-! ### Taylor expansion of coderivations along coalgebra morphisms -/

private noncomputable def gradedCoderivAlongSeq (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) : ℕ → (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
  | 0 => 0
  | n + 1 => ofLetter R N ∘ₗ δ + cutPrepend δ F' +
      cutPrepend (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
        (gradedCoderivAlongSeq G q F F' δ n)
private theorem gradedCoderivAlongSeq_stabilises (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) (n : ℕ) :
    ∀ z ∈ filtration R M n,
      gradedCoderivAlongSeq G q F F' δ (n + 1) z = gradedCoderivAlongSeq G q F F' δ n z := by
  induction n with
  | zero => exact apply_eq_zero_of_mem_filtration_zero R M _
  | succ _ ih =>
      intro z hz; conv_lhs => rw [gradedCoderivAlongSeq]
      conv_rhs => rw [gradedCoderivAlongSeq]
      simp only [LinearMap.add_apply]
      rw [cutPrepend_congr_of_mem_filtration_succ (fun _ _ ↦ rfl) ih hz]

/-- The coderivation along `F` and `F'` with twist parameter `q` and Taylor components `δ`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  filtrationLimit (gradedCoderivAlongSeq G q F F' δ)
theorem gradedCoderivAlong_eq (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' δ = ofLetter R N ∘ₗ δ + cutPrepend δ F' +
      cutPrepend (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
        (gradedCoderivAlong G q F F' δ) := by
  have hs := gradedCoderivAlongSeq_stabilises G q F F' δ; refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z; have hn' := filtration_monotone R M n.le_succ hn
  rw [gradedCoderivAlong, filtrationLimit_apply_of_mem_filtration hs hn', gradedCoderivAlongSeq]
  simp only [LinearMap.add_apply]
  rw [cutPrepend_congr_of_mem_filtration_succ (fun _ _ ↦ rfl)
    (fun _ hv ↦ (filtrationLimit_apply_of_mem_filtration hs hv).symm) hn']
theorem gradedCoderivAlong_subword (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' δ (subword R x a b) = ofLetter R N (δ (subword R x a b)) +
      ∑ d ∈ Finset.range b,
        (prepend R N (δ (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
          prepend R N
            (letter R N (F (ReducedTensorWords.map (R := R) (G.koszulTwist q) (subword R x a d))))
            (gradedCoderivAlong G q F F' δ (subword R x (a + d) (b - d)))) := by
  conv_lhs => rw [gradedCoderivAlong_eq]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cutPrepend_subword,
    ← Finset.sum_add_distrib, add_assoc]
@[simp] theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) : letter R N ∘ₗ gradedCoderivAlong G q F F' δ = δ := by
  refine LinearMap.ext fun z ↦ ?_; conv_lhs => rw [LinearMap.comp_apply, gradedCoderivAlong_eq]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, letter_ofLetter,
    letter_cutPrepend_apply, add_zero]
@[simp] theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' δ (ofLetter R M a) = ofLetter R N (δ (ofLetter R M a)) := by
  conv_lhs => rw [gradedCoderivAlong_eq]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cutPrepend_ofLetter, add_zero]

/-- The Taylor extension along `F` and `F'` is `R`-linear in the Taylor map. -/
@[simp] theorem gradedCoderivAlong_smul (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) (c : R)
    (δ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (c • δ) = c • gradedCoderivAlong G q F F' δ := by
  have h (n) : gradedCoderivAlongSeq G q F F' (c • δ) n =
      c • gradedCoderivAlongSeq G q F F' δ n := by
    induction n with
    | zero => simp [gradedCoderivAlongSeq]
    | succ _ ih => simp only [gradedCoderivAlongSeq, ih, cutPrepend, TensorProduct.map_smul_left,
        TensorProduct.map_smul_right, LinearMap.comp_smul, LinearMap.smul_comp, smul_add]
  refine (eq_filtrationLimit (gradedCoderivAlongSeq_stabilises G q F F' (c • δ))
    fun n z hz ↦ ?_).symm
  rw [LinearMap.smul_apply, gradedCoderivAlong,
    filtrationLimit_apply_of_mem_filtration (gradedCoderivAlongSeq_stabilises G q F F' δ) hz, h n]
  rfl

/-- The Taylor extension along `F` and `F'` of the zero Taylor map is zero. -/
@[simp] theorem gradedCoderivAlong_zero (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    gradedCoderivAlong G q F F' 0 = 0 := by
  simpa using gradedCoderivAlong_smul G q F F' (0 : R) 0

/-- The Taylor extension along `F` and `F'` is additive in the Taylor map. -/
@[simp] theorem gradedCoderivAlong_add (G : InternalGrading R M) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (δ₁ δ₂ : ReducedTensorWords R M →ₗ[R] N) :
    gradedCoderivAlong G q F F' (δ₁ + δ₂) =
      gradedCoderivAlong G q F F' δ₁ + gradedCoderivAlong G q F F' δ₂ := by
  have h (n) : gradedCoderivAlongSeq G q F F' (δ₁ + δ₂) n =
      gradedCoderivAlongSeq G q F F' δ₁ n + gradedCoderivAlongSeq G q F F' δ₂ n := by
    induction n with
    | zero => simp [gradedCoderivAlongSeq]
    | succ _ ih =>
        simp only [gradedCoderivAlongSeq, ih, cutPrepend, TensorProduct.map_add_left,
          TensorProduct.map_add_right, LinearMap.comp_add, LinearMap.add_comp]
        ac_rfl
  refine (eq_filtrationLimit (gradedCoderivAlongSeq_stabilises G q F F' (δ₁ + δ₂))
    fun n z hz ↦ ?_).symm
  rw [LinearMap.add_apply, gradedCoderivAlong, gradedCoderivAlong,
    filtrationLimit_apply_of_mem_filtration (gradedCoderivAlongSeq_stabilises G q F F' δ₁) hz,
    filtrationLimit_apply_of_mem_filtration (gradedCoderivAlongSeq_stabilises G q F F' δ₂) hz, h n]
  rfl

theorem isGradedCoderivationAlong_gradedCoderivAlong {G : InternalGrading R M} (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (δ : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' δ) := by
  let τ := ReducedTensorWords.map (R := R) (G.koszulTwist q); let D := gradedCoderivAlong G q F F' δ
  have hFτ := (hF.comp (isCoalgHom_map (G.koszulTwist q))).eq_ofLetter_add_cutPrepend
  have key : ∀ n, ∀ z ∈ filtration R M n, deconcatenation R N (D z) =
      (TensorProduct.map D F' + TensorProduct.map (F ∘ₗ τ) D) (deconcatenation R M z) := by
    intro n; induction n with
    | zero => intro z hz; rw [filtration_zero, Submodule.mem_bot] at hz; simp only [hz, map_zero]
    | succ _ ih =>
        intro z hz
        have hD_eq : D = ofLetter R N ∘ₗ δ + cutPrepend δ F' +
            cutPrepend (letter R N ∘ₗ (F ∘ₗ τ)) D := gradedCoderivAlong_eq G q F F' δ
        rw [LinearMap.congr_fun hD_eq z]
        simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, deconcatenation_ofLetter,
          zero_add, deconcatenation_cutPrepend δ hF'.deconcatenation_apply,
          deconcatenation_cutPrepend_of_mem_filtration_succ _ ih hz, cutPrependLeft_add,
          cutPrependLeft_map]
        have hrhs : (TensorProduct.map D F') (deconcatenation R M z) +
              (TensorProduct.map (F ∘ₗ τ) D) (deconcatenation R M z) =
            (TensorProduct.map (ofLetter R N ∘ₗ δ + cutPrepend δ F' +
              cutPrepend (letter R N ∘ₗ F ∘ₗ τ) D) F' +
            TensorProduct.map (ofLetter R N ∘ₗ letter R N ∘ₗ F ∘ₗ τ +
              cutPrepend (letter R N ∘ₗ F ∘ₗ τ) (F ∘ₗ τ)) D) (deconcatenation R M z) := by
          rw [← hD_eq, ← hFτ, LinearMap.add_apply]
        rw [hrhs]; simp only [TensorProduct.map_add_left, LinearMap.add_apply]; abel
  rw [isGradedCoderivationAlong_iff]; refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.rTensor_def,
    ← LinearMap.comp_apply (TensorProduct.map F _), ← TensorProduct.map_comp, LinearMap.comp_id]
  exact key n z hn

theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {G : InternalGrading R M} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (hD : IsGradedCoderivationAlong G q F F' D) :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Coderivations along coalgebra morphisms `F` and `F'` are in bijection with Taylor maps. -/
noncomputable def gradedCoderivAlongEquivTaylor (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') :
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D} ≃ (ReducedTensorWords R M →ₗ[R] N) where
  toFun D := letter R N ∘ₗ D.1
  invFun δ := ⟨gradedCoderivAlong G q F F' δ,
    isGradedCoderivationAlong_gradedCoderivAlong q hF hF' δ⟩
  left_inv D := Subtype.ext (D.2.eq_gradedCoderivAlong hF hF').symm
  right_inv δ := letter_comp_gradedCoderivAlong G q F F' δ

@[simp] theorem gradedCoderivAlongEquivTaylor_apply (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (D : {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D}) :
    gradedCoderivAlongEquivTaylor G q hF hF' D = letter R N ∘ₗ D.1 := (rfl)
@[simp] theorem gradedCoderivAlongEquivTaylor_symm_apply (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (δ : ReducedTensorWords R M →ₗ[R] N) :
    ((gradedCoderivAlongEquivTaylor G q hF hF').symm δ).1 = gradedCoderivAlong G q F F' δ := (rfl)

/-! ### Conilpotence filtration and homogeneity -/

/-- Two `q`-twisted coderivations along `(F₁, F₁')` and `(F₂, F₂')` agree on `filtration R M n`
whenever their base maps agree on strictly lower filtration steps and their letter components
agree on `filtration R M n`. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {G : InternalGrading R M} {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁) (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂)
    {n : ℕ} (hF : ∀ k < n, ∀ z ∈ filtration R M k, F₁ z = F₂ z)
    (hF' : ∀ k < n, ∀ z ∈ filtration R M k, F₁' z = F₂' z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero => rw [filtration_zero] at hz; rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
  | succ n ih =>
      have ih' : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
        ih (fun k hk w hw ↦ hF k (by omega) w hw) (fun k hk w hw ↦ hF' k (by omega) w hw)
          (fun w hw ↦ hl w (filtration_monotone R M n.le_succ hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
      rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]; clear hw
      induction w using TensorProduct.inductionOn with
      | tmul u v =>
          have hτu := (isCoalgHom_map (G.koszulTwist q)).mem_filtration u.2
          simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.rTensor_tmul, ih' _ u.2, ih' _ v.2, hF' n n.lt_succ_self _ v.2,
            hF n n.lt_succ_self _ hτu]
      | add _ _ hu hv =>
          simp only [map_add] at hu hv ⊢; rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- If `F'` preserves every step of the conilpotence filtration, then
`gradedCoderivAlong G q F F' δ` maps `filtration R M n` into `filtration R N n` for arbitrary
`F` and `δ`. -/
theorem gradedCoderivAlong_mem_filtration (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ k, ∀ z ∈ filtration R M k, F' z ∈ filtration R N k)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M n) : gradedCoderivAlong G q F F' δ z ∈ filtration R N n := by
  induction n generalizing z with
  | zero => rw [filtration_zero, Submodule.mem_bot] at hz; rw [hz, map_zero]; exact zero_mem _
  | succ n ih =>
      rw [LinearMap.congr_fun (gradedCoderivAlong_eq G q F F' δ) z]
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      exact add_mem (add_mem (filtration_monotone R N n.succ_pos (ofLetter_mem_filtration R N _))
        (cutPrepend_mem_filtration_succ δ (hF' n) hz))
        (cutPrepend_mem_filtration_succ _ (fun _ hv ↦ ih hv) hz)

theorem gradedCoderivAlong_subword_mem_filtration (G : InternalGrading R M) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : ∀ k, ∀ z ∈ filtration R M k, F' z ∈ filtration R N k)
    (δ : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' δ (subword R x a b) ∈ filtration R N b :=
  gradedCoderivAlong_mem_filtration G q hF' δ (subword_mem_filtration R M x a le_rfl)

/-- Every graded coderivation along coalgebra morphisms preserves the conilpotence filtration. -/
theorem IsGradedCoderivationAlong.mem_filtration {G : InternalGrading R M} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D z ∈ filtration R N n := by
  rw [hD.eq_gradedCoderivAlong hF hF']
  exact gradedCoderivAlong_mem_filtration G q (fun _ _ hw ↦ hF'.mem_filtration hw) _ hz

/-- If `F` and `F'` are homogeneous of degree `0` and `δ` is homogeneous of degree `r`, then
`gradedCoderivAlong G q F F' δ` is homogeneous of degree `r` independently of `q`. -/
theorem isHomogeneous_gradedCoderivAlong {G : InternalGrading R M} {H : InternalGrading R N}
    {q r : ℤ} {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {δ : ReducedTensorWords R M →ₗ[R] N}
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF'₀ : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hδ : LinearMap.IsHomogeneous δ (gradedPiece G) H.piece r) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' δ) (gradedPiece G) (gradedPiece H) r := by
  have hFτ : LinearMap.IsHomogeneous
      (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) H.piece 0 := by
    simpa only [add_zero] using
      (isHomogeneous_letter H).comp (hF₀.comp (isHomogeneous_map_koszulTwist G q))
  have hof : LinearMap.IsHomogeneous (ofLetter R N ∘ₗ δ) (gradedPiece G) (gradedPiece H) r := by
    rw [LinearMap.isHomogeneous_def]; exact fun _ _ hz ↦ ofLetter_mem_gradedPiece H (hδ.map_mem hz)
  refine isHomogeneous_filtrationLimit (gradedCoderivAlongSeq_stabilises G q F F' δ) fun n ↦ ?_
  induction n with
  | zero => exact LinearMap.isHomogeneous_zero _ _ _
  | succ _ ih =>
      refine (hof.add (by simpa only [add_zero] using isHomogeneous_cutPrepend hδ hF'₀)).add ?_
      simpa only [zero_add] using isHomogeneous_cutPrepend hFτ ih

end TauCeti.ReducedTensorWords
