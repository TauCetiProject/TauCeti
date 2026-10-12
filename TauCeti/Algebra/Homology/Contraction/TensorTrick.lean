/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear
public import TauCeti.LinearAlgebra.PiTensorProduct.Map
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
* `TauCeti.LinearSpecialContraction.deconcatenation_comp_reducedTensorWordsHomotopy`: `H` is a
  coderivation homotopy, `Δ H = (H ⊗ i p + τ ⊗ H) Δ`.
* `TauCeti.LinearSpecialContraction.map_koszulTwist_comp_reducedTensorWordsHomotopy`: `H`
  anticommutes with the letterwise Koszul twist.

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
    rw [PiTensorProduct.map_add_map_eq_map_update _ _ ⟨p, hp⟩ fun i hi ↦ ?_]
    · rw [← PiTensorProduct.mapMultilinear_apply]
      refine MultilinearMap.map_coord_zero _ ⟨p, hp⟩ ?_
      simpa [slotFamily_apply, hlt] using hdτ
    · have hi' : i.val ≠ p := fun h ↦ hi (Fin.ext h)
      simp only [slotFamily_apply]
      split_ifs <;> first | omega | simp
  · -- `h` acts before `d`: the two sides differ only at position `j`, by `τ h` against `h τ`
    rw [PiTensorProduct.map_add_map_eq_map_update _ _ ⟨j, hj⟩ fun i hi ↦ ?_]
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
    PiTensorProduct.map_add_map_eq_map_update _ _ ⟨p, hp⟩ fun i hi ↦ ?_]
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

/-- On a single letter the tensor-trick homotopy is the homotopy of the contraction. -/
@[simp]
theorem reducedTensorWordsHomotopy_ofLetter (G : InternalGrading R M) (a : M) :
    c.reducedTensorWordsHomotopy G (ofLetter R M a) = ofLetter R M (c.homotopy a) := by
  rw [ofLetter_eq_of_tprod, ofLetter_eq_of_tprod, c.reducedTensorWordsHomotopy_of_tprod G 1]
  simp

/-- On a two-letter word the tensor-trick homotopy is `h ⊗ i p + τ ⊗ h`, where `τ` is the Koszul
twist of parameter one. -/
theorem reducedTensorWordsHomotopy_of_two (G : InternalGrading R M) (a b : M) :
    c.reducedTensorWordsHomotopy G (of R M (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])) =
      of R M (2 : ℕ+) (PiTensorProduct.tprod R ![c.homotopy a, c.incl (c.proj b)]) +
        of R M (2 : ℕ+) (PiTensorProduct.tprod R ![G.koszulTwist 1 a, c.homotopy b]) := by
  have h := c.reducedTensorWordsHomotopy_of_tprod G ⟨2, two_pos⟩ ![a, b]
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  refine h.trans ?_
  congr 3 <;> funext i <;> fin_cases i <;> simp

/-- The tensor-trick homotopy lowers the total degree of words by one when the homotopy of the
contraction has degree `-1` and its inclusion and projection have degree zero. -/
theorem isHomogeneous_reducedTensorWordsHomotopy (G : InternalGrading R M)
    {H : InternalGrading R N} (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
    (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
    (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0) :
    LinearMap.IsHomogeneous (c.reducedTensorWordsHomotopy G) (gradedPiece G) (gradedPiece G)
      (-1) := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ c.reducedTensorWordsHomotopy G w ∈ gradedPiece G (D + -1)) hz ?_ ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    rw [c.reducedTensorWordsHomotopy_of_tprod G ⟨n, hn⟩ x]
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    have hjn : j < n := Finset.mem_range.mp hj
    have hsum : (∑ i : Fin n, (𝒟 i - if i.val = j then 1 else 0)) = D + -1 := by
      rw [Finset.sum_sub_distrib, hD, Finset.sum_eq_single (⟨j, hjn⟩ : Fin n)
        (fun i _ hi ↦ ite_eq_right fun h ↦ hi (Fin.ext h)) (by simp)]
      simp [sub_eq_add_neg]
    rw [← hsum]
    refine mem_gradedPiece_of_tprod G hn _ _ fun i ↦ ?_
    split_ifs with h₁ h₂ h₂
    · omega
    · simpa [sub_eq_add_neg] using hh.map_mem (hx i)
    · simpa using G.koszulTwist_mem_piece (hx i) 1
    · simpa using hincl.map_mem (hproj.map_mem (hx i))
  · rw [map_zero]
    exact zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro a u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-! ### The tensor-trick homotopy and deconcatenation -/

/-- The letters of the summand of the tensor-trick homotopy acting by `h` at position `J`. -/
private noncomputable def slotTuple (G : InternalGrading R M) {n : ℕ} (x : Fin n → M) (J : ℕ) :
    Fin n → M := fun i ↦
  if i.val < J then G.koszulTwist 1 (x i) else if i.val = J then c.homotopy (x i)
  else c.incl (c.proj (x i))

/-- The tensor-trick homotopy on a block of a pure tensor word. -/
private theorem reducedTensorWordsHomotopy_subword (G : InternalGrading R M) {n : ℕ} (x : Fin n → M)
    (a b : ℕ) :
    c.reducedTensorWordsHomotopy G (subword R x a b) =
      ∑ j ∈ Finset.range b, subword R (c.slotTuple G x (a + j)) a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  by_cases hab : a + b ≤ n
  · rw [subword_eq_of_tprod R x hb hab, reducedTensorWordsHomotopy_of_tprod]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [subword_eq_of_tprod R _ hb hab]
    refine of_tprod_congr R M hb rfl fun i ↦ ?_
    simp only [slotTuple, Fin.cast_eq_self]
    split_ifs <;> first | omega | rfl
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
    exact (Finset.sum_eq_zero fun j _ ↦ subword_eq_zero_of_lt_add R _ (by omega)).symm

/-- **The tensor-trick homotopy is a coderivation homotopy.**  Cutting `H z` either cuts to the
right of the letter carrying `h`, where the letters already carry `i p`, or cuts to its left,
where the letters passed by `h` carry the Koszul twist:

`Δ H = (H ⊗ (i p)) Δ + (τ ⊗ H) Δ`. -/
theorem deconcatenation_comp_reducedTensorWordsHomotopy (G : InternalGrading R M) :
    deconcatenation R M ∘ₗ c.reducedTensorWordsHomotopy G =
      (TensorProduct.map (c.reducedTensorWordsHomotopy G)
          (ReducedTensorWords.map (R := R) (c.incl ∘ₗ c.proj)) +
        TensorProduct.map (ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (c.reducedTensorWordsHomotopy G)) ∘ₗ deconcatenation R M := by
  refine linearMap_ext R M fun ⟨n, hn⟩ x ↦ ?_
  have hΔ (y : Fin n → M) : deconcatenation R M (subword R y 0 n) =
      ∑ k ∈ Finset.range n, subword R y 0 k ⊗ₜ[R] subword R y k (n - k) := by
    simpa using map_deconcatenation_subword R LinearMap.id LinearMap.id y 0 n
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [of_tprod_eq_subword R hn x, reducedTensorWordsHomotopy_subword, map_sum,
    map_deconcatenation_subword, map_deconcatenation_subword, ← Finset.sum_add_distrib]
  simp only [hΔ, zero_add]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [← Finset.sum_range_add_sum_Ico _ hk.le, Finset.sum_Ico_eq_sum_range,
    reducedTensorWordsHomotopy_subword, reducedTensorWordsHomotopy_subword,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_subword, map_subword]
  simp only [zero_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    congr 1
    refine subword_congr R _ _ (by omega) (by omega) fun l hl ↦ ?_
    simp only [slotTuple, LinearMap.comp_apply]
    split_ifs <;> first | omega | rfl
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    congr 1
    refine subword_congr R _ _ (by omega) (by omega) fun l hl ↦ ?_
    simp only [slotTuple]
    split_ifs <;> first | omega | rfl

/-- The tensor-trick homotopy anticommutes with the letterwise Koszul twist: it moves one odd map
`h` past the letters it acts on. -/
theorem map_koszulTwist_comp_reducedTensorWordsHomotopy (G : InternalGrading R M)
    (H : InternalGrading R N)
    (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
    (hincl : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
    (hproj : LinearMap.IsHomogeneous c.proj G.piece H.piece 0) :
    ReducedTensorWords.map (R := R) (G.koszulTwist 1) ∘ₗ c.reducedTensorWordsHomotopy G =
      -(c.reducedTensorWordsHomotopy G ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) := by
  have hhτ : G.koszulTwist 1 ∘ₗ c.homotopy + c.homotopy ∘ₗ G.koszulTwist 1 = 0 := by
    rw [hh.koszulTwist_comp 1]
    simp
  have hτincl : G.koszulTwist 1 ∘ₗ c.incl = c.incl ∘ₗ H.koszulTwist 1 := by
    simpa using hincl.koszulTwist_comp 1
  have hτproj : H.koszulTwist 1 ∘ₗ c.proj = c.proj ∘ₗ G.koszulTwist 1 := by
    simpa using hproj.koszulTwist_comp 1
  have hτP : G.koszulTwist 1 ∘ₗ (c.incl ∘ₗ c.proj) = (c.incl ∘ₗ c.proj) ∘ₗ G.koszulTwist 1 := by
    rw [← LinearMap.comp_assoc, hτincl, LinearMap.comp_assoc, hτproj, LinearMap.comp_assoc]
  refine eq_neg_of_add_eq_zero_left (linearMap_ext R M (N := ReducedTensorWords R M) fun n x ↦ ?_)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_of,
    reducedTensorWordsHomotopy_of, ← map_add]
  convert map_zero (of R M n)
  simp only [LinearMap.sum_apply, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  rw [← LinearMap.comp_apply (PiTensorProduct.map _) (PiTensorProduct.map _),
    ← LinearMap.comp_apply (PiTensorProduct.map _) (PiTensorProduct.map _), ← LinearMap.add_apply]
  refine (LinearMap.congr_fun ?_ _).trans (LinearMap.zero_apply _)
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp,
    PiTensorProduct.map_add_map_eq_map_update _ _ ⟨j, hj⟩ fun i hi ↦ ?_]
  · rw [← PiTensorProduct.mapMultilinear_apply]
    refine MultilinearMap.map_coord_zero _ ⟨j, hj⟩ ?_
    simpa using hhτ
  · have hi' : i.val ≠ j := fun h ↦ hi (Fin.ext h)
    split_ifs
    · rfl
    · exact hτP

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
