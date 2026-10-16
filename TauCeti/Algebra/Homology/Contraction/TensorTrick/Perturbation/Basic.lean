/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom

/-!
# Perturbing the tensor trick preserves the coalgebra structure

The tensor trick (`TauCeti.LinearSpecialContraction.reducedTensorWords`) turns a special
contraction of `(M, d)` onto `(N, d')` into a special contraction of the reduced tensor coalgebras
`Tᶜ(M)` onto `Tᶜ(N)`, with letterwise inclusion `i` and projection `p`, and with homotopy `H`.
Homological transfer then perturbs the letterwise differential `D` of `Tᶜ(M)` by a graded
coderivation `δ` which lowers tensor length, such as the part of the bar differential of an `A∞`
algebra collapsing at least two letters, and applies the basic perturbation lemma
(`TauCeti.LinearSpecialContraction.perturb`).

This file shows that the output of the perturbation lemma is again compatible with
deconcatenation: the perturbed inclusion `i' = i - H X i` and the perturbed projection
`p' = p - p X H` are morphisms of reduced tensor coalgebras, and the perturbed differential
`D' = D + p X i` of `Tᶜ(N)` is a graded coderivation.  Consequently `D'` is determined by its
letter component, which carries the transferred operations on `N`, and `i'` and `p'` are
determined by their Taylor components.

The key input is that `H` is a *coderivation homotopy*: with `τ` the letterwise Koszul twist,

`Δ H = (H ⊗ i p + τ ⊗ H) Δ`

(`TauCeti.LinearSpecialContraction.deconcatenation_comp_reducedTensorWordsHomotopy`).

## Main results

* `TauCeti.LinearSpecialContraction.isCoalgHom_reducedTensorWords_perturb_incl`: the perturbed
  inclusion is a coalgebra morphism.
* `TauCeti.LinearSpecialContraction.isCoalgHom_reducedTensorWords_perturb_proj`: the perturbed
  projection is a coalgebra morphism.
* `TauCeti.LinearSpecialContraction.isGradedCoderivation_reducedTensorWords_perturbedDifferential`:
  the perturbed differential is a graded coderivation.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* J. Huebschmann and T. Kadeishvili, *Small models for chain algebras*, Mathematische Zeitschrift
  207 (1991), 245--280.
-/

public section

open scoped DirectSum TensorProduct

universe uR uM uN

namespace TauCeti

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-! ### Local nilpotence on pairs of words -/

namespace ReducedTensorWords

variable (R M) in
/-- On pairs of words, the operator lowering tensor length on one side by a perturbation `d` and
then applying length-preserving maps is locally nilpotent. -/
private theorem exists_pow_perturbationTensor_apply_eq_zero
    {f g t d : Module.End R (ReducedTensorWords R M)}
    (hf : ∀ n, Submodule.map f (filtration R M n) ≤ filtration R M n)
    (hg : ∀ n, Submodule.map g (filtration R M n) ≤ filtration R M n)
    (ht : ∀ n, Submodule.map t (filtration R M n) ≤ filtration R M n)
    (hd : ∀ n, Submodule.map d (filtration R M (n + 1)) ≤ filtration R M n)
    (z : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :
    ∃ n, (((TensorProduct.map f g + TensorProduct.map t f) ∘ₗ
      (TensorProduct.map d LinearMap.id + TensorProduct.map t d)) ^ n) z = 0 := by
  set K := (TensorProduct.map f g + TensorProduct.map t f) ∘ₗ
    (TensorProduct.map d LinearMap.id + TensorProduct.map t d)
  have mem : ∀ {e : Module.End R (ReducedTensorWords R M)} {n m : ℕ} {x},
      (∀ n, Submodule.map e (filtration R M n) ≤ filtration R M n) → x ∈ filtration R M n →
        n ≤ m → e x ∈ filtration R M m :=
    fun he hx hnm ↦ filtration_monotone R M hnm (he _ ⟨_, hx, rfl⟩)
  have key : ∀ n a b x y, x ∈ filtration R M a → y ∈ filtration R M b → a + b ≤ n →
      (K ^ n) (x ⊗ₜ[R] y) = 0 := by
    intro n
    induction n with
    | zero =>
        intro a b x y hx _ hab
        obtain rfl : a = 0 := by omega
        rw [filtration_zero, Submodule.mem_bot] at hx
        simp [hx]
    | succ n ih =>
        intro a b x y hx hy hab
        rcases a with _ | a
        · rw [filtration_zero, Submodule.mem_bot] at hx
          simp [hx]
        rcases b with _ | b
        · rw [filtration_zero, Submodule.mem_bot] at hy
          simp [hy]
        have hdx : d x ∈ filtration R M a := hd a ⟨x, hx, rfl⟩
        have hdy : d y ∈ filtration R M b := hd b ⟨y, hy, rfl⟩
        rw [pow_succ, Module.End.mul_apply]
        simp only [K, LinearMap.comp_apply, LinearMap.add_apply, TensorProduct.map_tmul,
          LinearMap.id_apply, map_add]
        rw [ih a (b + 1) _ _ (mem hf hdx le_rfl) (mem hg hy le_rfl) (by omega),
          ih a (b + 1) _ _ (mem ht hdx le_rfl) (mem hf hy le_rfl) (by omega),
          ih (a + 1) b _ _ (mem hf (mem ht hx le_rfl) le_rfl) (mem hg hdy le_rfl) (by omega),
          ih (a + 1) b _ _ (mem ht (mem ht hx le_rfl) le_rfl) (mem hf hdy le_rfl) (by omega)]
        simp
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨a, ha⟩ := exists_mem_filtration R M x
      obtain ⟨b, hb⟩ := exists_mem_filtration R M y
      exact ⟨a + b, key _ a b x y ha hb le_rfl⟩
  | add z w hz hw =>
      obtain ⟨m, hm⟩ := hz
      obtain ⟨k, hk⟩ := hw
      refine ⟨k + m, ?_⟩
      rw [map_add, pow_add, Module.End.mul_apply, hm, map_zero, zero_add, pow_mul_comm,
        Module.End.mul_apply, hk, map_zero]

end ReducedTensorWords

/-! ### The perturbed tensor-trick contraction -/

namespace LinearSpecialContraction

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {G : InternalGrading R M} {H : InternalGrading R N}
  (hdM : LinearMap.IsHomogeneous dM G.piece G.piece 1)
  (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0)
  {δ : Module.End R (ReducedTensorWords R M)}
  (hsq : (gradedCoderiv G (dM ∘ₗ letter R M) 1 + δ) ∘ₗ (gradedCoderiv G (dM ∘ₗ letter R M) 1 + δ) =
    gradedCoderiv G (dM ∘ₗ letter R M) 1 ∘ₗ gradedCoderiv G (dM ∘ₗ letter R M) 1)
  (hU : IsUnit (1 + δ * (c.reducedTensorWords G H hdM hh hincl hproj).homotopy))

include hsq hU in
/-- The perturbed inclusion `i' = i - H X i` is the fixed point `i' = i - H δ i'`. -/
private theorem reducedTensorWords_perturb_incl_add :
    ((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).incl +
        c.reducedTensorWordsHomotopy G ∘ₗ δ ∘ₗ
          ((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).incl =
      ReducedTensorWords.map (R := R) c.incl := by
  set T := c.reducedTensorWords G H hdM hh hincl hproj
  have hX := T.comp_homotopy_comp_perturbationSeries δ hU
  simp only [perturb_incl, T, reducedTensorWords_incl, reducedTensorWords_homotopy] at hX ⊢
  have h := congrArg (fun f ↦ c.reducedTensorWordsHomotopy G ∘ₗ f ∘ₗ
    ReducedTensorWords.map (R := R) c.incl) hX
  simp only [LinearMap.comp_assoc, LinearMap.sub_comp, LinearMap.comp_sub] at h
  rw [LinearMap.comp_sub, LinearMap.comp_sub, h]
  abel

include hsq hU in
/-- **The coalgebra perturbation lemma for the tensor trick.**  Perturbing the tensor-trick
contraction by a graded coderivation `δ` which lowers tensor length, the perturbed inclusion
`i' = i - H X i` is again a morphism of reduced tensor coalgebras.  The unit hypothesis `hU` of
the perturbation lemma holds automatically for such `δ`, by
`TauCeti.ReducedTensorWords.exists_pow_comp_apply_eq_zero_of_filtration_lowering` and
`Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`. -/
theorem isCoalgHom_reducedTensorWords_perturb_incl (hδ : IsGradedCoderivation G 1 δ)
    (hδfil : ∀ n, Submodule.map δ (filtration R M (n + 1)) ≤ filtration R M n) :
    IsCoalgHom R ((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).incl := by
  -- Strategy: `Δ i'` and `(i' ⊗ i') Δ` both solve `F + K F = (i ⊗ i) Δ`, where
  -- `K = (H ⊗ i p + τ ⊗ H) (δ ⊗ 1 + τ ⊗ δ)`; the operator `1 + K` is injective since `K` is
  -- locally nilpotent.  First collect the identities satisfied by `i' = i - H δ i'`.
  set T := c.reducedTensorWords G H hdM hh hincl hproj
  set i := ReducedTensorWords.map (R := R) c.incl
  set p := ReducedTensorWords.map (R := R) c.proj
  set h := c.reducedTensorWordsHomotopy G
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
  set X := T.perturbationSeries δ
  set i' := (T.perturb δ hsq hU).incl
  have hTi : T.incl = i := c.reducedTensorWords_incl G H hdM hh hincl hproj
  have hTp : T.proj = p := c.reducedTensorWords_proj G H hdM hh hincl hproj
  have hTh : T.homotopy = h := c.reducedTensorWords_homotopy G H hdM hh hincl hproj
  have hfix : i' + h ∘ₗ δ ∘ₗ i' = i :=
    c.reducedTensorWords_perturb_incl_add hdM hh hincl hproj hsq hU
  have hi' : i' = i - h ∘ₗ X ∘ₗ i := by
    rw [← hTi, ← hTh]
    exact T.perturb_incl δ hsq hU
  have hhi' : h ∘ₗ i' = 0 := by
    have h1 := T.homotopy_comp_incl
    have h2 := T.homotopy_comp_homotopy_assoc (X ∘ₗ T.incl)
    simp only [hTi, hTh] at h1 h2
    rw [hi', LinearMap.comp_sub, h1, h2]
    abel
  have hττ : τ ∘ₗ τ = LinearMap.id := by
    rw [← ReducedTensorWords.map_comp, G.koszulTwist_comp_self, ReducedTensorWords.map_id]
  set π := ReducedTensorWords.map (R := R) (c.incl ∘ₗ c.proj)
  have hπi' : π ∘ₗ i' = i := by
    have h1 := T.proj_comp_incl
    have h2 := T.proj_comp_homotopy_assoc (X ∘ₗ T.incl)
    simp only [hTi, hTp, hTh] at h1 h2
    rw [show π = i ∘ₗ p by simp only [π, i, p, ReducedTensorWords.map_comp], hi',
      LinearMap.comp_sub, LinearMap.comp_assoc, h1, LinearMap.comp_assoc, h2,
      LinearMap.comp_zero, LinearMap.comp_id]
    abel
  have hhτi' : h ∘ₗ τ ∘ₗ i' = 0 := by
    have h1 := c.map_koszulTwist_comp_reducedTensorWordsHomotopy G H hh hincl hproj
    rw [← LinearMap.comp_assoc, ← neg_neg (h ∘ₗ τ), ← h1, LinearMap.neg_comp,
      LinearMap.comp_assoc, hhi', LinearMap.comp_zero]
    abel
  -- The three co-Leibniz rules: for `i`, for the homotopy `h`, and for the perturbation `δ`.
  have hΔi : deconcatenation R M ∘ₗ i = TensorProduct.map i i ∘ₗ deconcatenation R N :=
    isCoalgHom_iff.mp (isCoalgHom_map c.incl)
  have hΔh : deconcatenation R M ∘ₗ h =
      (TensorProduct.map h π + TensorProduct.map τ h) ∘ₗ deconcatenation R M :=
    c.deconcatenation_comp_reducedTensorWordsHomotopy G
  have hΔδ : deconcatenation R M ∘ₗ δ =
      (TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ deconcatenation R M := by
    rw [isGradedCoderivation_iff.mp hδ, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_def,
      LinearMap.add_comp]
  set K := (TensorProduct.map h π + TensorProduct.map τ h) ∘ₗ
    (TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ)
  have hK : Function.Injective
      (1 + K : Module.End R (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M)) := by
    refine (Module.End.isUnit_iff _).mp
      (Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero (R := R)
        (M := ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) K fun z ↦ ?_) |>.1
    exact ReducedTensorWords.exists_pow_perturbationTensor_apply_eq_zero R M
      (c.reducedTensorWordsHomotopy_filtration G)
      (fun _ ↦ Submodule.map_le_iff_le_comap.2 fun _ hz ↦ (isCoalgHom_map _).mem_filtration hz)
      (fun _ ↦ Submodule.map_le_iff_le_comap.2 fun _ hz ↦ (isCoalgHom_map _).mem_filtration hz)
      hδfil z
  have hΔh' : ∀ f : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R M,
      deconcatenation R M ∘ₗ h ∘ₗ f =
        (TensorProduct.map h π + TensorProduct.map τ h) ∘ₗ deconcatenation R M ∘ₗ f := fun f ↦ by
    rw [← LinearMap.comp_assoc, hΔh, LinearMap.comp_assoc]
  have hΔδ' : ∀ f : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R M,
      deconcatenation R M ∘ₗ δ ∘ₗ f = (TensorProduct.map δ LinearMap.id +
        TensorProduct.map τ δ) ∘ₗ deconcatenation R M ∘ₗ f := fun f ↦ by
    rw [← LinearMap.comp_assoc, hΔδ, LinearMap.comp_assoc]
  -- `Δ i'` solves `F + K F = (i ⊗ i) Δ`.
  have h1 : deconcatenation R M ∘ₗ i' + K ∘ₗ deconcatenation R M ∘ₗ i' =
      TensorProduct.map i i ∘ₗ deconcatenation R N := by
    rw [← hΔi, ← hfix, LinearMap.comp_add, hΔh', hΔδ']
    simp only [K, LinearMap.comp_assoc]
  -- So does `(i' ⊗ i') Δ`.
  have hKi' : K ∘ₗ TensorProduct.map i' i' =
      TensorProduct.map (h ∘ₗ δ ∘ₗ i') i + TensorProduct.map i' (h ∘ₗ δ ∘ₗ i') := by
    simp only [K, LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_assoc,
      ← TensorProduct.map_comp, LinearMap.id_comp]
    have hττi' : τ ∘ₗ τ ∘ₗ i' = i' := by
      rw [← LinearMap.comp_assoc, hττ, LinearMap.id_comp]
    rw [hπi', hhτi', hhi', hττi', TensorProduct.map_zero_left, TensorProduct.map_zero_right]
    abel
  have h2 : TensorProduct.map i' i' + K ∘ₗ TensorProduct.map i' i' = TensorProduct.map i i := by
    rw [hKi', ← hfix, TensorProduct.map_add_left, TensorProduct.map_add_right,
      TensorProduct.map_add_right]
    abel
  rw [isCoalgHom_iff]
  refine LinearMap.ext fun z ↦ hK ?_
  have e1 := LinearMap.congr_fun h1 z
  have e2 := LinearMap.congr_fun h2 (deconcatenation R N z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at e1 e2
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.comp_apply, e1, e2]

include hsq hU in
/-- **The perturbed projection is a coalgebra morphism.**  Perturbing the tensor-trick
contraction by a graded coderivation `δ`, the perturbed projection `p' = p - p X H` is again a
morphism of reduced tensor coalgebras.  Unlike the perturbed inclusion, no filtration hypothesis on
`δ` is needed beyond the invertibility of `1 + δ H`. -/
theorem isCoalgHom_reducedTensorWords_perturb_proj (hδ : IsGradedCoderivation G 1 δ) :
    IsCoalgHom R ((c.reducedTensorWords G H hdM hh hincl hproj).perturb δ hsq hU).proj := by
  -- Strategy: `Δ p'` and `(p' ⊗ p') Δ` both become `(p ⊗ p) Δ` after precomposition with the
  -- invertible operator `1 + δ H`, using the fixed point `p' (1 + δ H) = p`.
  set T := c.reducedTensorWords G H hdM hh hincl hproj
  set p := ReducedTensorWords.map (R := R) c.proj
  set h := c.reducedTensorWordsHomotopy G
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
  set π := ReducedTensorWords.map (R := R) (c.incl ∘ₗ c.proj)
  set X := T.perturbationSeries δ
  set p' := (T.perturb δ hsq hU).proj
  have hTp : T.proj = p := c.reducedTensorWords_proj G H hdM hh hincl hproj
  have hTh : T.homotopy = h := c.reducedTensorWords_homotopy G H hdM hh hincl hproj
  have hfix : p' + p' ∘ₗ δ ∘ₗ h = p := by
    have e := T.perturb_proj_comp_one_add_mul δ hsq hU
    rwa [hTp, hTh, Module.End.mul_eq_comp, LinearMap.comp_add, Module.End.one_eq_id,
      LinearMap.comp_id] at e
  -- The side conditions of the perturbed projection against `h`, `τ h` and `π = i p`.
  have hp'h : p' ∘ₗ h = 0 := by
    have e := T.perturb_proj_comp_homotopy δ hsq hU
    rwa [hTh] at e
  have hp'τh : p' ∘ₗ τ ∘ₗ h = 0 := by
    have h1 := c.map_koszulTwist_comp_reducedTensorWordsHomotopy G H hh hincl hproj
    rw [h1, LinearMap.comp_neg, ← LinearMap.comp_assoc, hp'h, LinearMap.zero_comp]
    abel
  have hp'π : p' ∘ₗ π = p := by
    have e := T.perturb_proj_comp_incl δ hsq hU
    rw [c.reducedTensorWords_incl G H hdM hh hincl hproj] at e
    have hπ : π = ReducedTensorWords.map (R := R) c.incl ∘ₗ p := by
      simp only [π, p, ReducedTensorWords.map_comp]
    rw [hπ, ← LinearMap.comp_assoc, e, LinearMap.id_comp]
  have hp'ττ : p' ∘ₗ τ ∘ₗ τ = p' := by
    rw [← ReducedTensorWords.map_comp, G.koszulTwist_comp_self, ReducedTensorWords.map_id,
      LinearMap.comp_id]
  -- The co-Leibniz rules for `p`, for the homotopy `h`, and for the perturbation `δ`.
  have hΔp : deconcatenation R N ∘ₗ p = TensorProduct.map p p ∘ₗ deconcatenation R M :=
    isCoalgHom_iff.mp (isCoalgHom_map c.proj)
  have hΔh : deconcatenation R M ∘ₗ h =
      (TensorProduct.map h π + TensorProduct.map τ h) ∘ₗ deconcatenation R M :=
    c.deconcatenation_comp_reducedTensorWordsHomotopy G
  have hΔδ : deconcatenation R M ∘ₗ δ =
      (TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ deconcatenation R M := by
    rw [isGradedCoderivation_iff.mp hδ, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_def,
      LinearMap.add_comp]
  -- `Δ p'` composed with `1 + δ h` is `(p ⊗ p) Δ`.
  have h1 : deconcatenation R N ∘ₗ p' + deconcatenation R N ∘ₗ p' ∘ₗ δ ∘ₗ h =
      TensorProduct.map p p ∘ₗ deconcatenation R M := by
    rw [← hΔp, ← hfix, LinearMap.comp_add]
  -- So is `(p' ⊗ p') Δ`.
  have h2 : TensorProduct.map p' p' ∘ₗ deconcatenation R M +
      TensorProduct.map p' p' ∘ₗ deconcatenation R M ∘ₗ δ ∘ₗ h =
        TensorProduct.map p p ∘ₗ deconcatenation R M := by
    have hΔδh : deconcatenation R M ∘ₗ δ ∘ₗ h =
        ((TensorProduct.map δ LinearMap.id + TensorProduct.map τ δ) ∘ₗ
          (TensorProduct.map h π + TensorProduct.map τ h)) ∘ₗ deconcatenation R M := by
      rw [← LinearMap.comp_assoc, hΔδ, LinearMap.comp_assoc, hΔh, LinearMap.comp_assoc]
    rw [hΔδh]
    simp only [LinearMap.add_comp, LinearMap.comp_add, ← LinearMap.comp_assoc,
      ← TensorProduct.map_comp, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, hp'π, hp'h, hp'τh, hp'ττ, TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, LinearMap.zero_comp, add_zero, zero_add]
    rw [← hfix]
    simp only [TensorProduct.map_add_left, TensorProduct.map_add_right, LinearMap.add_comp]
    abel
  rw [isCoalgHom_iff]
  have hsurj := ((Module.End.isUnit_iff _).mp hU).2
  rw [hTh] at hsurj
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨w, rfl⟩ := hsurj z
  have e1 := LinearMap.congr_fun h1 w
  have e2 := LinearMap.congr_fun h2 w
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at e1 e2
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, LinearMap.comp_apply,
    map_add, e1, e2]

include hsq hU in
/-- **The perturbed tensor-trick differential is a coderivation.**  Perturbing the tensor-trick
contraction by an odd graded coderivation `δ` which lowers tensor length, the perturbed
differential `D' = D + p X i` of `Tᶜ(N)` is again a graded coderivation for the Koszul signs of
the grading of `N`. -/
theorem isGradedCoderivation_reducedTensorWords_perturbedDifferential
    (hδ : IsGradedCoderivation G 1 δ)
    (hδdeg : LinearMap.IsHomogeneous δ (gradedPiece G) (gradedPiece G) 1)
    (hδfil : ∀ n, Submodule.map δ (filtration R M (n + 1)) ≤ filtration R M n) :
    IsGradedCoderivation H 1
      ((c.reducedTensorWords G H hdM hh hincl hproj).perturbedDifferential δ) := by
  -- Strategy: `i' D' = (D + δ) i'`, where `i'` is a coalgebra morphism commuting with the Koszul
  -- twists and `D + δ` is a graded coderivation.  Hence `(i' ⊗ i')` intertwines the two sides of
  -- the co-Leibniz rule for `D'`, and `i' ⊗ i'` has the left inverse `p' ⊗ p'`.
  set T := c.reducedTensorWords G H hdM hh hincl hproj
  set i := ReducedTensorWords.map (R := R) c.incl
  set h := c.reducedTensorWordsHomotopy G
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
  set τN := ReducedTensorWords.map (R := R) (H.koszulTwist 1)
  set i' := (T.perturb δ hsq hU).incl
  set D' := T.perturbedDifferential δ
  set b := gradedCoderiv G (dM ∘ₗ letter R M) 1 + δ
  have hcoalg : deconcatenation R M ∘ₗ i' = TensorProduct.map i' i' ∘ₗ deconcatenation R N :=
    isCoalgHom_iff.mp (c.isCoalgHom_reducedTensorWords_perturb_incl hdM hh hincl hproj hsq hU hδ
      hδfil)
  have hfix : i' + h ∘ₗ δ ∘ₗ i' = i :=
    c.reducedTensorWords_perturb_incl_add hdM hh hincl hproj hsq hU
  have hτh : τ ∘ₗ h = -(h ∘ₗ τ) :=
    c.map_koszulTwist_comp_reducedTensorWordsHomotopy G H hh hincl hproj
  have hτδ : τ ∘ₗ δ = -(δ ∘ₗ τ) := by
    rw [hδdeg.map_koszulTwist_comp 1, mul_one, Int.negOnePow_one, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one]
    exact neg_one_smul R (δ ∘ₗ τ)
  have hτi : τ ∘ₗ i = i ∘ₗ τN := by
    have hτincl : G.koszulTwist 1 ∘ₗ c.incl = c.incl ∘ₗ H.koszulTwist 1 := by
      simpa using hincl.koszulTwist_comp 1
    simp only [τ, i, τN, ← ReducedTensorWords.map_comp, hτincl]
  -- `i'` commutes with the twists, since both `τ i'` and `i' τ` solve `F + h δ F = i τ`.
  have hinj : Function.Injective (1 + h * δ : Module.End R (ReducedTensorWords R M)) := by
    refine ((Module.End.isUnit_iff _).mp
      (Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _ fun z ↦ ?_)).1
    refine ReducedTensorWords.exists_pow_apply_eq_zero_of_filtration_lowering R M _
      (fun n ↦ ?_) z
    rw [Module.End.mul_eq_comp, Submodule.map_comp]
    exact (Submodule.map_mono (hδfil n)).trans (c.reducedTensorWordsHomotopy_filtration G n)
  have hτi' : τ ∘ₗ i' = i' ∘ₗ τN := by
    refine LinearMap.ext fun z ↦ hinj ?_
    have e1 := LinearMap.congr_fun hfix z
    have e2 := LinearMap.congr_fun hfix (τN z)
    have e3 := LinearMap.congr_fun hτi z
    have e4 := LinearMap.congr_fun hτh (δ (i' z))
    have e5 := LinearMap.congr_fun hτδ (i' z)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply] at e1 e2 e3 e4 e5
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply,
      LinearMap.comp_apply, e2]
    rw [← e3, ← e1, map_add, e4, e5, map_neg, neg_neg]
  -- `D'` is conjugate to the coderivation `D + δ` by the coalgebra morphism `i'`.
  have hb : IsGradedCoderivation G 1 b :=
    (mem_gradedCoderivations G).1 ((gradedCoderivations G 1).add_mem
      ((mem_gradedCoderivations G).2 (isGradedCoderivation_gradedCoderiv G _ 1))
      ((mem_gradedCoderivations G).2 hδ))
  have hbi' : b ∘ₗ i' = i' ∘ₗ D' := (T.perturb δ hsq hU).dM_comp_incl
  have hΔb : deconcatenation R M ∘ₗ b =
      (TensorProduct.map b LinearMap.id + TensorProduct.map τ b) ∘ₗ deconcatenation R M := by
    rw [isGradedCoderivation_iff.mp hb, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_def,
      LinearMap.add_comp]
  rw [isGradedCoderivation_iff, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_def,
    ← LinearMap.add_comp]
  have key : TensorProduct.map i' i' ∘ₗ deconcatenation R N ∘ₗ D' =
      TensorProduct.map i' i' ∘ₗ (TensorProduct.map D' LinearMap.id + TensorProduct.map τN D') ∘ₗ
        deconcatenation R N := by
    rw [← LinearMap.comp_assoc, ← hcoalg, LinearMap.comp_assoc, ← hbi', ← LinearMap.comp_assoc,
      hΔb, LinearMap.comp_assoc, hcoalg]
    simp only [← LinearMap.comp_assoc, LinearMap.add_comp, LinearMap.comp_add,
      ← TensorProduct.map_comp, hbi', hτi', LinearMap.id_comp, LinearMap.comp_id]
  have hleft : TensorProduct.map (T.perturb δ hsq hU).proj (T.perturb δ hsq hU).proj ∘ₗ
      TensorProduct.map i' i' = LinearMap.id := by
    rw [← TensorProduct.map_comp, (T.perturb δ hsq hU).proj_comp_incl, TensorProduct.map_id]
  simpa only [← LinearMap.comp_assoc, hleft, LinearMap.id_comp] using
    congrArg (TensorProduct.map (T.perturb δ hsq hU).proj (T.perturb δ hsq hU).proj ∘ₗ ·) key

end LinearSpecialContraction

end TauCeti
