/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# The tensor trick

A special contraction of `(M, d)` onto `(N, d')` induces a special contraction of the reduced
tensor coalgebras `Tᶜ(M) = ⨁_{n ≥ 1} M^{⊗ n}` onto `Tᶜ(N)`.  The endomorphisms on words are the
letterwise extensions of `d` and `d'`, the degree-one graded coderivations
`ReducedTensorWords.gradedCoderiv G (d ∘ letter) 1` whose only Taylor component is `d` on single
letters; on a word they apply `d` to one letter at a time, with the Koszul sign of the letters it
passes.  When `d` and `d'` square to zero, these extensions are differentials.  The inclusion and
projection act letterwise, and the homotopy is

`H = ∑_j τ^{⊗ j} ⊗ h ⊗ (i p)^{⊗ (n - j - 1)}`

on words of length `n`, where `τ = InternalGrading.koszulTwist G 1` is the Koszul sign of moving
the odd map `h` past a letter.  Cross terms of `d H + H d` cancel because `d` and `h` are odd and
`i p` commutes with `d` and with `τ`, while the diagonal terms telescope to `1 - (i p)^{⊗ n}`.
The side conditions of the letters give those of the words.

This is the input of homological transfer along a contraction of an `A∞` algebra onto a
retract such as its cohomology: the bar differential of the algebra is the letterwise extension
of its unary operation plus a perturbation which shortens words, so the perturbation lemma
applies to the contraction of bar constructions produced here.

## Main definitions

* `TauCeti.LinearSpecialContraction.reducedTensorWordsHomotopy`: the homotopy `H` on reduced tensor
  words.
* `TauCeti.LinearSpecialContraction.reducedTensorWords`: the induced special contraction of the
  reduced tensor coalgebras.

## Main results

* `TauCeti.LinearSpecialContraction.reducedTensorWordsHomotopy_of`: the value of `H` on an
  arbitrary homogeneous tensor word.
* `TauCeti.LinearSpecialContraction.reducedTensorWordsHomotopy_of_tprod`: the value of `H` on a pure
  tensor word.

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

/-! ### Families of letter maps acting around one slot -/

/-- The family of letter maps acting by `f` before position `j`, by `g` at position `j`, and by
`k` after it. -/
private def slotFamily {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (n : ℕ) (f g k : P →ₗ[R] Q) (j : ℕ) : Fin n → P →ₗ[R] Q :=
  fun i ↦ if i.val < j then f else if i.val = j then g else k

private theorem slotFamily_apply {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] (n : ℕ) (f g k : P →ₗ[R] Q) (j : ℕ) (i : Fin n) :
    slotFamily n f g k j i = if i.val < j then f else if i.val = j then g else k :=
  (rfl)

/-- The sum over all positions of the tensor maps of `slotFamily`. -/
private noncomputable def slotSum (n : ℕ) (f g k : Module.End R M) :
    Module.End R (TensorPower R n M) :=
  ∑ j ∈ Finset.range n, PiTensorProduct.map (slotFamily n f g k j)

/-- Two tensor maps whose factors agree away from one position add up to the tensor map with the
sum of their factors at that position. -/
private theorem map_add_map_eq {n : ℕ} (A B : Fin n → M →ₗ[R] M) (k : Fin n)
    (h : ∀ i, i ≠ k → A i = B i) :
    PiTensorProduct.map A + PiTensorProduct.map B =
      PiTensorProduct.map (Function.update A k (A k + B k)) := by
  have hB : B = Function.update A k (B k) := by
    funext i
    by_cases hi : i = k
    · subst hi
      simp
    · simp [Function.update_of_ne hi, h i hi]
  rw [PiTensorProduct.map_update_add, Function.update_eq_self, ← hB]

/-! ### The contraction identity on words of one length -/

section Core

variable {τ d h P : Module.End R M}

/-- Off the diagonal, the cross terms of `D H + H D` cancel. -/
private theorem slot_cross_eq_zero (hdτ : d ∘ₗ τ + τ ∘ₗ d = 0) (hhτ : τ ∘ₗ h + h ∘ₗ τ = 0)
    (hτP : τ ∘ₗ P = P ∘ₗ τ) (hdP : d ∘ₗ P = P ∘ₗ d) {n p j : ℕ} (hp : p < n) (hj : j < n)
    (hpj : p ≠ j) :
    PiTensorProduct.map (slotFamily n τ d LinearMap.id p) ∘ₗ
        PiTensorProduct.map (slotFamily n τ h P j) +
      PiTensorProduct.map (slotFamily n τ h P j) ∘ₗ
        PiTensorProduct.map (slotFamily n τ d LinearMap.id p) = 0 := by
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rcases lt_or_gt_of_ne hpj with hlt | hgt
  · -- `d` acts before `h`: the two sides differ only at position `p`, by `d τ` against `τ d`
    rw [map_add_map_eq _ _ ⟨p, hp⟩ fun i hi ↦ ?_]
    · rw [← PiTensorProduct.mapMultilinear_apply]
      refine MultilinearMap.map_coord_zero _ ⟨p, hp⟩ ?_
      simpa [slotFamily_apply, hlt] using hdτ
    · have hi' : i.val ≠ p := fun h ↦ hi (Fin.ext h)
      simp only [slotFamily_apply]
      split_ifs <;> first | omega | simp
  · -- `h` acts before `d`: the two sides differ only at position `j`, by `τ h` against `h τ`
    rw [map_add_map_eq _ _ ⟨j, hj⟩ fun i hi ↦ ?_]
    · rw [← PiTensorProduct.mapMultilinear_apply]
      refine MultilinearMap.map_coord_zero _ ⟨j, hj⟩ ?_
      simpa [slotFamily_apply, hgt] using hhτ
    · have hi' : i.val ≠ j := fun h ↦ hi (Fin.ext h)
      simp only [slotFamily_apply]
      split_ifs <;> first | omega | exact hτP | exact hdP | simp

/-- On the diagonal, `D H + H D` contributes one step of the telescope from `(i p)^{⊗ n}` to the
identity. -/
private theorem slot_diag_eq (hττ : τ ∘ₗ τ = LinearMap.id)
    (hdh : d ∘ₗ h + h ∘ₗ d = LinearMap.id - P) {n p : ℕ} (hp : p < n) :
    PiTensorProduct.map (slotFamily n τ d LinearMap.id p) ∘ₗ
        PiTensorProduct.map (slotFamily n τ h P p) +
      PiTensorProduct.map (slotFamily n τ h P p) ∘ₗ
        PiTensorProduct.map (slotFamily n τ d LinearMap.id p) =
      PiTensorProduct.map (slotFamily n LinearMap.id LinearMap.id P p) -
        PiTensorProduct.map (slotFamily n LinearMap.id P P p) := by
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp,
    map_add_map_eq _ _ ⟨p, hp⟩ fun i hi ↦ ?_]
  · have hk : (slotFamily n τ d LinearMap.id p ⟨p, hp⟩ ∘ₗ slotFamily n τ h P p ⟨p, hp⟩ +
        slotFamily n τ h P p ⟨p, hp⟩ ∘ₗ slotFamily n τ d LinearMap.id p ⟨p, hp⟩) =
        LinearMap.id - P := by
      simpa [slotFamily_apply] using hdh
    have hsub := (PiTensorProduct.mapMultilinear R (fun _ : Fin n ↦ M) (fun _ ↦ M)).map_update_sub
      (fun i ↦ slotFamily n τ d LinearMap.id p i ∘ₗ slotFamily n τ h P p i) ⟨p, hp⟩
      LinearMap.id P
    simp only [PiTensorProduct.mapMultilinear_apply] at hsub
    rw [hk, hsub]
    congr 2 <;> funext i <;> by_cases hi : i = ⟨p, hp⟩
    all_goals first
      | (subst hi
         simp [slotFamily_apply])
      | (have hi' : i.val ≠ p := fun h ↦ hi (Fin.ext h)
         rw [Function.update_of_ne hi]
         simp only [slotFamily_apply]
         split_ifs <;> first | omega | exact hττ | simp)
  · have hi' : i.val ≠ p := fun h ↦ hi (Fin.ext h)
    simp only [slotFamily_apply]
    split_ifs <;> first | omega | simp

/-- The contraction identity `D H + H D = 1 - (i p)^{⊗ n}` on words of length `n`. -/
private theorem slotSum_mul_add (hττ : τ ∘ₗ τ = LinearMap.id) (hdτ : d ∘ₗ τ + τ ∘ₗ d = 0)
    (hhτ : τ ∘ₗ h + h ∘ₗ τ = 0) (hτP : τ ∘ₗ P = P ∘ₗ τ) (hdP : d ∘ₗ P = P ∘ₗ d)
    (hdh : d ∘ₗ h + h ∘ₗ d = LinearMap.id - P) (n : ℕ) :
    slotSum n τ d LinearMap.id ∘ₗ slotSum n τ h P +
        slotSum n τ h P ∘ₗ slotSum n τ d LinearMap.id =
      LinearMap.id - PiTensorProduct.map fun _ : Fin n ↦ P := by
  simp only [slotSum, ← Module.End.mul_eq_comp, Finset.sum_mul_sum]
  rw [Finset.sum_comm (s := Finset.range n), ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, Module.End.mul_eq_comp]
  have hterm : ∀ j ∈ Finset.range n, ∑ p ∈ Finset.range n,
      (PiTensorProduct.map (slotFamily n τ d LinearMap.id p) ∘ₗ
          PiTensorProduct.map (slotFamily n τ h P j) +
        PiTensorProduct.map (slotFamily n τ h P j) ∘ₗ
          PiTensorProduct.map (slotFamily n τ d LinearMap.id p)) =
      PiTensorProduct.map (slotFamily n LinearMap.id P P (j + 1)) -
        PiTensorProduct.map (slotFamily n LinearMap.id P P j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.sum_eq_single j (fun p hp hpj ↦ slot_cross_eq_zero hdτ hhτ hτP hdP
      (Finset.mem_range.mp hp) hj hpj) (fun h ↦ absurd (Finset.mem_range.mpr hj) h)]
    rw [slot_diag_eq hττ hdh hj]
    congr 2
    funext i
    simp only [slotFamily_apply]
    split_ifs <;> first | omega | rfl
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub (fun j ↦ PiTensorProduct.map (slotFamily n LinearMap.id P P j))]
  congr 1
  · rw [← PiTensorProduct.map_id]
    congr 1
    funext i
    simp [slotFamily_apply, i.isLt]
  · congr 1
    funext i
    simp only [slotFamily_apply]
    split_ifs <;> first | omega | rfl

end Core

/-! ### Operators on reduced tensor words acting length by length -/

/-- On words of length `n`, the letterwise extension of `d` is
`∑_p τ^{⊗ p} ⊗ d ⊗ 1^{⊗ (n - p - 1)}`. -/
private theorem gradedCoderiv_comp_letter_comp_of (G : InternalGrading R M) (d : Module.End R M)
    (n : {n : ℕ // 0 < n}) :
    gradedCoderiv G (d ∘ₗ letter R M) 1 ∘ₗ of R M n =
      of R M n ∘ₗ slotSum n.1 (G.koszulTwist 1) d LinearMap.id := by
  obtain ⟨n, hn⟩ := n
  refine PiTensorProduct.ext (MultilinearMap.ext fun x ↦ ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, slotSum,
    LinearMap.sum_apply, map_sum, PiTensorProduct.map_tprod,
    gradedCoderiv_comp_letter_of_tprod G d 1 hn x]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg _ (congrArg _ (funext fun i ↦ ?_))
  simp only [slotFamily_apply]
  split_ifs <;> rfl

private theorem gradedCoderiv_comp_letter_of (G : InternalGrading R M) (d : Module.End R M)
    (n : {n : ℕ // 0 < n}) (z : TensorPower R n.1 M) :
    gradedCoderiv G (d ∘ₗ letter R M) 1 (of R M n z) =
      of R M n (slotSum n.1 (G.koszulTwist 1) d LinearMap.id z) :=
  LinearMap.congr_fun (gradedCoderiv_comp_letter_comp_of G d n) z

/-- Letterwise extensions of two odd maps intertwined by a degree-zero map are intertwined by its
tensor powers. -/
private theorem slotSum_comp_map {G : InternalGrading R M} {H : InternalGrading R N}
    {f : N →ₗ[R] M} (hf : LinearMap.IsHomogeneous f H.piece G.piece 0) {dM : Module.End R M}
    {dN : Module.End R N} (hd : dM ∘ₗ f = f ∘ₗ dN) (n : ℕ) :
    slotSum n (G.koszulTwist 1) dM LinearMap.id ∘ₗ PiTensorProduct.map (fun _ ↦ f) =
      PiTensorProduct.map (fun _ ↦ f) ∘ₗ slotSum n (H.koszulTwist 1) dN LinearMap.id := by
  have hτ : G.koszulTwist 1 ∘ₗ f = f ∘ₗ H.koszulTwist 1 := by
    simpa using hf.koszulTwist_comp 1
  refine PiTensorProduct.ext (MultilinearMap.ext fun x ↦ ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, slotSum,
    LinearMap.sum_apply, map_sum, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg _ (funext fun i ↦ ?_)
  simp only [slotFamily_apply]
  split_ifs
  · exact LinearMap.congr_fun hτ (x i)
  · exact LinearMap.congr_fun hd (x i)
  · rfl

namespace LinearSpecialContraction

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)

/-- The tensor-trick homotopy on reduced tensor words: on words of length `n` it is
`∑_j τ^{⊗ j} ⊗ h ⊗ (i p)^{⊗ (n - j - 1)}`, where `τ` is the Koszul twist of parameter one for
the grading `G`. -/
noncomputable def reducedTensorWordsHomotopy (G : InternalGrading R M) :
    Module.End R (ReducedTensorWords R M) :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    of R M n ∘ₗ ∑ j ∈ Finset.range n.1, PiTensorProduct.map fun i : Fin n.1 ↦
      if i.val < j then G.koszulTwist 1 else if i.val = j then c.homotopy else c.incl ∘ₗ c.proj

private theorem reducedTensorWordsHomotopy_of_slotSum (G : InternalGrading R M)
    (n : {n : ℕ // 0 < n})
    (z : TensorPower R n.1 M) :
    c.reducedTensorWordsHomotopy G (of R M n z) =
      of R M n (slotSum n.1 (G.koszulTwist 1) c.homotopy (c.incl ∘ₗ c.proj) z) :=
  toModule_of R M _ n z

/-- The tensor-trick homotopy on an arbitrary word of length `n`, expanded as the sum of its
single-slot actions. -/
@[simp]
theorem reducedTensorWordsHomotopy_of (G : InternalGrading R M) (n : {n : ℕ // 0 < n})
    (z : TensorPower R n.1 M) :
    c.reducedTensorWordsHomotopy G (of R M n z) =
      of R M n ((∑ j ∈ Finset.range n.1, PiTensorProduct.map fun i : Fin n.1 ↦
        if i.val < j then G.koszulTwist 1
        else if i.val = j then c.homotopy else c.incl ∘ₗ c.proj) z) := by
  rw [c.reducedTensorWordsHomotopy_of_slotSum G n z]
  rfl

/-- The tensor-trick homotopy on a pure tensor word: the sum over positions `j` of the word with
the letters before `j` Koszul-twisted, `h` applied at `j`, and `i p` applied after `j`. -/
theorem reducedTensorWordsHomotopy_of_tprod (G : InternalGrading R M) (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → M) :
    c.reducedTensorWordsHomotopy G (of R M n (PiTensorProduct.tprod R x)) =
      ∑ j ∈ Finset.range n.1, of R M n (PiTensorProduct.tprod R fun i ↦
        if i.val < j then G.koszulTwist 1 (x i)
        else if i.val = j then c.homotopy (x i) else c.incl (c.proj (x i))) := by
  simp only [reducedTensorWordsHomotopy_of, LinearMap.sum_apply, map_sum,
    PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg _ (congrArg _ (funext fun i ↦ ?_))
  split_ifs <;> rfl

/-- The contraction identity for the tensor-trick homotopy against the letterwise differential,
on words of each length. -/
private theorem slotSum_contraction (G : InternalGrading R M) (H : InternalGrading R N)
    (hdM : LinearMap.IsHomogeneous dM G.piece G.piece 1)
    (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
    (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
    (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0) (n : ℕ) :
    slotSum n (G.koszulTwist 1) dM LinearMap.id ∘ₗ
        slotSum n (G.koszulTwist 1) c.homotopy (c.incl ∘ₗ c.proj) +
      slotSum n (G.koszulTwist 1) c.homotopy (c.incl ∘ₗ c.proj) ∘ₗ
        slotSum n (G.koszulTwist 1) dM LinearMap.id =
      LinearMap.id -
        PiTensorProduct.map (fun _ ↦ c.incl) ∘ₗ PiTensorProduct.map fun _ ↦ c.proj := by
  have hdτ : dM ∘ₗ G.koszulTwist 1 + G.koszulTwist 1 ∘ₗ dM = 0 := by
    rw [hdM.koszulTwist_comp 1]
    simp
  have hhτ : G.koszulTwist 1 ∘ₗ c.homotopy + c.homotopy ∘ₗ G.koszulTwist 1 = 0 := by
    rw [hh.koszulTwist_comp 1]
    simp
  have hτincl : G.koszulTwist 1 ∘ₗ c.incl = c.incl ∘ₗ H.koszulTwist 1 := by
    simpa using hincl.koszulTwist_comp 1
  have hτproj : H.koszulTwist 1 ∘ₗ c.proj = c.proj ∘ₗ G.koszulTwist 1 := by
    simpa using hproj.koszulTwist_comp 1
  have hτP : G.koszulTwist 1 ∘ₗ (c.incl ∘ₗ c.proj) = (c.incl ∘ₗ c.proj) ∘ₗ G.koszulTwist 1 := by
    rw [← LinearMap.comp_assoc, hτincl, LinearMap.comp_assoc, hτproj, LinearMap.comp_assoc]
  have hdP : dM ∘ₗ (c.incl ∘ₗ c.proj) = (c.incl ∘ₗ c.proj) ∘ₗ dM := by
    rw [← LinearMap.comp_assoc, c.dM_comp_incl, LinearMap.comp_assoc, ← c.proj_comp_dM,
      LinearMap.comp_assoc]
  rw [slotSum_mul_add (G.koszulTwist_comp_self 1) hdτ hhτ hτP hdP
    c.dM_comp_homotopy_add_homotopy_comp_dM n, PiTensorProduct.map_comp]

/-- **The tensor trick.** A special contraction of `(M, dM)` onto `(N, dN)` by graded maps of the
expected degrees induces a special contraction of the reduced tensor coalgebras, whose
endomorphisms are the letterwise extensions of `dM` and `dN` with the Koszul signs of `G` and `H`.
When `dM` and `dN` square to zero, these extensions are differentials.  The inclusion and
projection act letterwise, and the homotopy is `reducedTensorWordsHomotopy`. -/
noncomputable def reducedTensorWords (G : InternalGrading R M) (H : InternalGrading R N)
    (hdM : LinearMap.IsHomogeneous dM G.piece G.piece 1)
    (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
    (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
    (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0) :
    LinearSpecialContraction (gradedCoderiv G (dM ∘ₗ letter R M) 1)
      (gradedCoderiv H (dN ∘ₗ letter R N) 1) where
  incl := ReducedTensorWords.map (R := R) c.incl
  proj := ReducedTensorWords.map (R := R) c.proj
  homotopy := c.reducedTensorWordsHomotopy G
  dM_comp_incl := linearMap_ext R N fun n x ↦ by
    have h := LinearMap.congr_fun (slotSum_comp_map hincl c.dM_comp_incl n.1)
      (PiTensorProduct.tprod R x)
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, map_of, gradedCoderiv_comp_letter_of, h]
  proj_comp_dM := linearMap_ext R M fun n x ↦ by
    have h := LinearMap.congr_fun (slotSum_comp_map hproj c.proj_comp_dM.symm n.1)
      (PiTensorProduct.tprod R x)
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, map_of, gradedCoderiv_comp_letter_of, h]
  proj_comp_incl := by
    rw [← ReducedTensorWords.map_comp, c.proj_comp_incl, ReducedTensorWords.map_id]
  dM_comp_homotopy_add_homotopy_comp_dM := linearMap_ext R M fun n x ↦ by
    have h := LinearMap.congr_fun (c.slotSum_contraction G H hdM hh hincl hproj n.1)
      (PiTensorProduct.tprod R x)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_of, gradedCoderiv_comp_letter_of,
      reducedTensorWordsHomotopy_of_slotSum, ← map_add, ← map_sub, h]
  homotopy_comp_incl := linearMap_ext R N fun n x ↦ by
    simp only [LinearMap.comp_apply, map_of_tprod, reducedTensorWordsHomotopy_of_tprod,
      LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [(PiTensorProduct.tprod R).map_coord_zero ⟨j, Finset.mem_range.mp hj⟩ (by simp), map_zero]
  proj_comp_homotopy := linearMap_ext R M fun n x ↦ by
    simp only [LinearMap.comp_apply, reducedTensorWordsHomotopy_of_tprod, map_sum, map_of_tprod,
      LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [(PiTensorProduct.tprod R).map_coord_zero ⟨j, Finset.mem_range.mp hj⟩ (by simp), map_zero]
  homotopy_comp_homotopy := linearMap_ext R M fun n x ↦ by
    simp only [LinearMap.comp_apply, reducedTensorWordsHomotopy_of_tprod, map_sum,
      LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.mem_range] at hj hk
    rcases lt_trichotomy k j with hkj | rfl | hkj
    · rw [(PiTensorProduct.tprod R).map_coord_zero ⟨j, hj⟩ (by simp [hkj.not_gt, hkj.ne']),
        map_zero]
    · rw [(PiTensorProduct.tprod R).map_coord_zero ⟨k, hk⟩ (by simp), map_zero]
    · rw [(PiTensorProduct.tprod R).map_coord_zero ⟨k, hk⟩ (by simp [hkj.not_gt, hkj.ne']),
        map_zero]

variable (G : InternalGrading R M) (H : InternalGrading R N)
  (hdM : LinearMap.IsHomogeneous dM G.piece G.piece 1)
  (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0)

/-- The inclusion of the tensor-trick contraction is the letterwise inclusion. -/
@[simp]
theorem reducedTensorWords_incl :
    (c.reducedTensorWords G H hdM hh hincl hproj).incl = ReducedTensorWords.map (R := R) c.incl :=
  (rfl)

/-- The projection of the tensor-trick contraction is the letterwise projection. -/
@[simp]
theorem reducedTensorWords_proj :
    (c.reducedTensorWords G H hdM hh hincl hproj).proj = ReducedTensorWords.map (R := R) c.proj :=
  (rfl)

/-- The homotopy of the tensor-trick contraction is `reducedTensorWordsHomotopy`. -/
@[simp]
theorem reducedTensorWords_homotopy :
    (c.reducedTensorWords G H hdM hh hincl hproj).homotopy = c.reducedTensorWordsHomotopy G :=
  (rfl)

end LinearSpecialContraction

end TauCeti
