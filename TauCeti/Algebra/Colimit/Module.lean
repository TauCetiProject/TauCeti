/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Linear maps from finite modules into directed colimits of modules

Let `(Gᵢ, fᵢⱼ)` be a directed system of `R`-modules over a directed preorder `ι`, and let
`φᵢ : Gᵢ → L` be compatible linear maps (`φⱼ ∘ fᵢⱼ = φᵢ`). As in
`TauCeti.Algebra.Colimit.CommonStage`, the colimit conditions are stated as hypotheses, so the
results of the first part apply to `Module.DirectLimit` with its canonical maps, and equally to
its tensor products with fixed modules.

* If every element of `L` comes from a stage, every linear map from a finite projective module
  into `L` factors through a stage (`TauCeti.DirectLimit.exists_comp_eq_of_projective`).
* If two elements of a stage with the same image in `L` become equal at a later stage, then two
  linear maps from a finite module into a stage with the same composite to `L` become equal at a
  later stage (`TauCeti.DirectLimit.exists_comp_eq_comp`).
* Over a ring, under both conditions, every linear map from a finitely presented module into `L`
  factors through a stage (`TauCeti.DirectLimit.exists_comp_eq_of_finitePresentation`).

The second part supplies these conditions for tensor products of `Module.DirectLimit G f`: every
element of `P ⊗ colim Gᵢ` comes from a stage, and two elements of `P ⊗ Gᵢ`, of `Gᵢ ⊗ Q` or of
`P ⊗ (Gᵢ ⊗ Gᵢ)` with the same image in `P ⊗ colim Gᵢ`, `colim Gᵢ ⊗ Q` or
`P ⊗ (colim Gᵢ ⊗ colim Gᵢ)` have the same image at a later stage. The one-factor statements come
from Mathlib's identifications `TensorProduct.directLimitLeft` and
`TensorProduct.directLimitRight`; the two-factor statement applies them one factor at a time.
These are the finiteness arguments needed to descend comodules over a directed colimit of
coalgebras to a stage.

The finitely presented module factorization follows the proof plan of
`TauCeti.DirectLimit.Algebra.exists_eq_comp_of_finitePresentation` in
`TauCeti/Algebra/Colimit/FinitePresentation.lean`: lift finitely many generators to a stage,
then pass to a later stage where the finitely many relations vanish.
-/

public section

open TensorProduct

namespace TauCeti.DirectLimit

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  {G : ι → Type*} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} {L : Type*} [AddCommMonoid L] [Module R L]
  {φ : ∀ i, G i →ₗ[R] L} {M : Type*} [AddCommMonoid M] [Module R M]

/-- If every element of `L` comes from a stage, then every linear map from a finite projective
module into `L` factors through a stage. -/
theorem exists_comp_eq_of_projective [Module.Finite R M] [Module.Projective R M]
    (hφf : ∀ i j (h : i ≤ j) x, φ j (f i j h x) = φ i x)
    (hcover : ∀ x : L, ∃ i a, φ i a = x) (u : M →ₗ[R] L) :
    ∃ i, ∃ v : M →ₗ[R] G i, φ i ∘ₗ v = u := by
  classical
  have : Nonempty ι := let ⟨i, _⟩ := hcover 0; ⟨i⟩
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  choose i₀ a ha using fun k : Fin n ↦ hcover (u (π (Pi.single k 1)))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image i₀)
  have hle (k : Fin n) : i₀ k ≤ i := hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  obtain ⟨σ, hσ⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  let w := Fintype.linearCombination R fun k ↦ f (i₀ k) i (hle k) (a k)
  have hw : φ i ∘ₗ w = u ∘ₗ π := by
    ext k
    simp [w, hφf, ha]
  exact ⟨i, w ∘ₗ σ, by rw [← LinearMap.comp_assoc, hw, LinearMap.comp_assoc, hσ,
    LinearMap.comp_id]⟩

/-- If two elements of a stage with the same image in `L` become equal at a later stage, then
two linear maps from a finite module into a stage with the same composite to `L` become equal at
a later stage. -/
theorem exists_comp_eq_comp [DirectedSystem G (f · · ·)] [Module.Finite R M]
    (hker : ∀ i (a b : G i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, f i j h a = f i j h b)
    {i : ι} {u v : M →ₗ[R] G i} (h : φ i ∘ₗ u = φ i ∘ₗ v) :
    ∃ j, ∃ hij : i ≤ j, f i j hij ∘ₗ u = f i j hij ∘ₗ v := by
  classical
  have : Nonempty ι := ⟨i⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose! j hij hj using fun x (_ : x ∈ s) ↦ hker i (u x) (v x) (LinearMap.congr_fun h x)
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (s.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  refine ⟨k, hik, LinearMap.ext_on hs fun x hx ↦ ?_⟩
  have hjk : j x ≤ k := hk _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
  simp only [LinearMap.comp_apply]
  rw [← DirectedSystem.map_map' (f · · ·) (hij x hx) hjk (u x),
    ← DirectedSystem.map_map' (f · · ·) (hij x hx) hjk (v x), hj x hx]

section Ring

variable {R : Type*} [Ring R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} {L : Type*} [AddCommGroup L] [Module R L]
  {φ : ∀ i, G i →ₗ[R] L} {M : Type*} [AddCommGroup M] [Module R M]

/-- If every element of `L` comes from a stage, and two elements of a stage with the same image
in `L` become equal at a later stage, then every linear map from a finitely presented module into
`L` factors through a stage. -/
theorem exists_comp_eq_of_finitePresentation [DirectedSystem G (f · · ·)]
    [Module.FinitePresentation R M]
    (hφf : ∀ i j (h : i ≤ j) x, φ j (f i j h x) = φ i x)
    (hcover : ∀ x : L, ∃ i a, φ i a = x)
    (hker : ∀ i (a b : G i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, f i j h a = f i j h b)
    (u : M →ₗ[R] L) :
    ∃ i, ∃ v : M →ₗ[R] G i, φ i ∘ₗ v = u := by
  -- Write `M` as `Rⁿ ⧸ K` with `K` the range of `g : Rᵐ → Rⁿ`, and lift `u` to `Rⁿ`.
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  obtain ⟨m, g, hg⟩ := K.fg_iff_exists_fin_linearMap.mp hK
  obtain ⟨i, w, hw⟩ :=
    exists_comp_eq_of_projective hφf hcover (u ∘ₗ e.symm.toLinearMap ∘ₗ K.mkQ)
  -- The lift vanishes on `K` at a later stage.
  have hmk : K.mkQ ∘ₗ g = 0 :=
    LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero K).2 (hg ▸ LinearMap.mem_range_self g x)
  obtain ⟨j, hij, hj⟩ := exists_comp_eq_comp hker (u := w ∘ₗ g) (v := 0) (by
    rw [← LinearMap.comp_assoc, hw, LinearMap.comp_assoc, LinearMap.comp_assoc, hmk,
      LinearMap.comp_zero, LinearMap.comp_zero, LinearMap.comp_zero])
  have hle : K ≤ LinearMap.ker (f i j hij ∘ₗ w) := by
    rw [← hg]
    rintro _ ⟨x, rfl⟩
    simpa using LinearMap.congr_fun hj x
  refine ⟨j, K.liftQ (f i j hij ∘ₗ w) hle ∘ₗ e.toLinearMap, LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := K.mkQ_surjective (e x)
  have hwy := LinearMap.congr_fun hw y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hwy ⊢
  rw [← hy, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, hφf, hwy, hy,
    LinearEquiv.symm_apply_apply]

end Ring

end TauCeti.DirectLimit

namespace Module.DirectLimit

variable {R : Type*} [CommSemiring R] {ι : Type*} [Preorder ι] [DecidableEq ι]
  {G : ι → Type*} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
  (P : Type*) [AddCommMonoid P] [Module R P] (Q : Type*) [AddCommMonoid Q] [Module R Q]

/-- Under `TensorProduct.directLimitRight`, tensoring the canonical map of a stage with `P` is the
canonical map of the tensored stage. -/
theorem directLimitRight_lTensor_of {i : ι} (x : P ⊗[R] G i) :
    directLimitRight f P ((of R ι G f i).lTensor P x) =
      of R ι (P ⊗[R] G ·) (fun _ _ h ↦ (f _ _ h).lTensor P) i x := by
  induction x using TensorProduct.inductionOn with
  | tmul p g => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring the canonical maps with `P` is compatible with the transition maps. -/
theorem lTensor_of_lTensor_f {i j : ι} (h : i ≤ j) (x : P ⊗[R] G i) :
    (of R ι G f j).lTensor P ((f i j h).lTensor P x) = (of R ι G f i).lTensor P x := by
  rw [← LinearMap.lTensor_comp_apply]
  congr 2
  exact LinearMap.ext fun _ ↦ of_f

/-- Every element of `P ⊗ colim Gᵢ` comes from a stage. -/
theorem exists_lTensor_of_eq [Nonempty ι] [IsDirectedOrder ι] (z : P ⊗[R] DirectLimit G f) :
    ∃ i x, (of R ι G f i).lTensor P x = z := by
  obtain ⟨i, x, hx⟩ := exists_of (directLimitRight f P z)
  exact ⟨i, x, (directLimitRight f P).injective (by rw [directLimitRight_lTensor_of, hx])⟩

/-- Tensoring both factors of `Gᵢ ⊗ Gᵢ` with the transition maps, and then with `P`, gives a
directed system. -/
instance [DirectedSystem G (f · · ·)] :
    DirectedSystem (fun i ↦ P ⊗[R] (G i ⊗[R] G i))
      fun i j h ↦ (TensorProduct.map (f i j h) (f i j h)).lTensor P where
  map_self i x := by
    have : f i i le_rfl = LinearMap.id := LinearMap.ext fun x ↦ DirectedSystem.map_self' (f · · ·) x
    simp [this]
  map_map k j i hij hjk x := by
    have : f j k hjk ∘ₗ f i j hij = f i k (hij.trans hjk) :=
      LinearMap.ext (DirectedSystem.map_map' (f · · ·) hij hjk)
    rw [← LinearMap.lTensor_comp_apply, ← TensorProduct.map_comp, this]

variable [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]

variable {P Q} in
/-- Two elements of `P ⊗ Gᵢ` with the same image in `P ⊗ colim Gᵢ` have the same image in some
later `P ⊗ Gⱼ`. -/
theorem exists_lTensor_eq_of_lTensor_of_eq {i : ι} {x y : P ⊗[R] G i}
    (h : (of R ι G f i).lTensor P x = (of R ι G f i).lTensor P y) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).lTensor P x = (f i j hij).lTensor P y := by
  apply exists_eq_of_of_eq
  rw [← directLimitRight_lTensor_of, ← directLimitRight_lTensor_of, h]

variable {P Q} in
/-- Two elements of `Gᵢ ⊗ Q` with the same image in `colim Gᵢ ⊗ Q` have the same image in some
later `Gⱼ ⊗ Q`. -/
theorem exists_rTensor_eq_of_rTensor_of_eq {i : ι} {x y : G i ⊗[R] Q}
    (h : (of R ι G f i).rTensor Q x = (of R ι G f i).rTensor Q y) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).rTensor Q x = (f i j hij).rTensor Q y := by
  apply exists_eq_of_of_eq
  rw [← directLimitLeft_rTensor_of, ← directLimitLeft_rTensor_of, h]

variable {P Q} in
/-- Two elements of `P ⊗ (Gᵢ ⊗ Gᵢ)` with the same image in `P ⊗ (colim Gᵢ ⊗ colim Gᵢ)` have the
same image in some later `P ⊗ (Gⱼ ⊗ Gⱼ)`. -/
theorem exists_lTensor_map_eq_of_lTensor_map_of_eq {i : ι} {x y : P ⊗[R] (G i ⊗[R] G i)}
    (h : (TensorProduct.map (of R ι G f i) (of R ι G f i)).lTensor P x =
      (TensorProduct.map (of R ι G f i) (of R ι G f i)).lTensor P y) :
    ∃ j, ∃ hij : i ≤ j, (TensorProduct.map (f i j hij) (f i j hij)).lTensor P x =
      (TensorProduct.map (f i j hij) (f i j hij)).lTensor P y := by
  let D := DirectLimit G f
  -- First pass to a stage `k` in the right factor, inside `(P ⊗ colim Gᵢ) ⊗ Gₖ`.
  have h₁ : (of R ι G f i).lTensor (P ⊗[R] D) ∘ₗ (TensorProduct.assoc R P D (G i)).symm ∘ₗ
      ((of R ι G f i).rTensor (G i)).lTensor P =
        (TensorProduct.assoc R P D D).symm ∘ₗ
          (TensorProduct.map (of R ι G f i) (of R ι G f i)).lTensor P :=
    TensorProduct.ext_threefold' fun _ _ _ ↦ by simp
  obtain ⟨k, hik, hk⟩ := exists_lTensor_eq_of_lTensor_of_eq (f := f) (i := i)
    (x := (TensorProduct.assoc R P D (G i)).symm (((of R ι G f i).rTensor (G i)).lTensor P x))
    (y := (TensorProduct.assoc R P D (G i)).symm (((of R ι G f i).rTensor (G i)).lTensor P y))
    (by
      have h₁x := LinearMap.congr_fun h₁ x
      have h₁y := LinearMap.congr_fun h₁ y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₁x h₁y
      rw [h₁x, h₁y, h])
  -- Then pass to a stage `j` in the left factor, inside `(P ⊗ Gⱼ) ⊗ Gₖ`.
  let e := directLimitRight f P
  have h₂ : (f i k hik).lTensor (P ⊗[R] D) ∘ₗ (TensorProduct.assoc R P D (G i)).symm ∘ₗ
      ((of R ι G f i).rTensor (G i)).lTensor P =
        (e.symm.toLinearMap.rTensor (G k)) ∘ₗ
          (of R ι (P ⊗[R] G ·) (fun _ _ h ↦ (f _ _ h).lTensor P) i).rTensor (G k) ∘ₗ
            (TensorProduct.assoc R P (G i) (G k)).symm ∘ₗ ((f i k hik).lTensor (G i)).lTensor P :=
    TensorProduct.ext_threefold' fun _ _ _ ↦ by simp [e]
  have hk' := congr($h₂ x).symm.trans (hk.trans congr($h₂ y))
  simp only [LinearMap.comp_apply, ← LinearEquiv.coe_rTensor] at hk'
  obtain ⟨j, hij, hj⟩ := exists_rTensor_eq_of_rTensor_of_eq ((e.symm.rTensor (G k)).injective hk')
  -- Finally move both factors to a common stage `m`.
  obtain ⟨m, hjm, hkm⟩ := exists_ge_ge j k
  have h₃ : (TensorProduct.map (f i m (hij.trans hjm)) (f i m (hij.trans hjm))).lTensor P =
      (TensorProduct.map (f j m hjm) (f k m hkm)).lTensor P ∘ₗ
        (TensorProduct.assoc R P (G j) (G k)).toLinearMap ∘ₗ
        ((f i j hij).lTensor P).rTensor (G k) ∘ₗ (TensorProduct.assoc R P (G i) (G k)).symm ∘ₗ
          ((f i k hik).lTensor (G i)).lTensor P :=
    TensorProduct.ext_threefold' fun _ _ _ ↦ by simp [DirectedSystem.map_map' (f · · ·)]
  refine ⟨m, hij.trans hjm, ?_⟩
  rw [h₃]
  simp only [LinearMap.comp_apply]
  rw [hj]

end Module.DirectLimit
