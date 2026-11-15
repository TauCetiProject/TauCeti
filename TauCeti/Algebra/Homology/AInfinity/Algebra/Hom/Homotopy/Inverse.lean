/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Transformation
public import TauCeti.Algebra.Homology.Contraction.Linear.Homology

/-!
# Homotopy equivalences and homotopy inverses of A-infinity algebras

An `A∞` morphism `f : A ⟶ B` is a *homotopy equivalence* (`AInfinityHom.IsHomotopyEquiv`) when
there exists an `A∞` morphism `g : B ⟶ A` together with homotopies `id_A ~ g ∘ f` and
`id_B ~ f ∘ g`.  Passing to arity one extracts a homogeneous `LinearHomotopyEquiv` between the
unary differentials `(A, m₁)` and `(B, m₁)` with forward map `f₁`, and passing to cohomology shows
that every homotopy equivalence is a quasi-isomorphism.

Conversely, suppose `f₁` underlies a homogeneous `LinearHomotopyEquiv` `e` between `(A, m₁)` and
`(B, m₁)` over an arbitrary commutative ring `R`.  Following Lefèvre-Hasegawa (Théorème 1.3.1.2),
one constructs an `A∞` morphism `g : B ⟶ A` and a right homotopy `H : id_B ~ f ∘ g` simultaneously
by induction along the conilpotence filtration of `Tᶜ(sB)`:

* At stage `n`, if `G ∘ b_B - b_A ∘ G` and `(1 - F ∘ G) - (b_B ∘ H + H ∘ b_B)` vanish on words of
  length at most `n`, then on words of length `n + 1` both defects take primitive values `m` and
  `r`, and the nilpotency `b² = 0` forces `(m, r)` to satisfy the coupled cocycle equations
  `m₁ ∘ m + m ∘ b_B^1 = 0` and `m₁ ∘ r - r ∘ b_B^1 = f₁ ∘ m`.
* Applying Vogt's adjoint normalization (`LinearHomotopyEquiv.coupledLift` and
  `LinearHomotopyEquiv.coupledHomotopy`) kills both defects on words of length `n + 1` without
  disturbing lengths `≤ n`.  Taking `stabilisingLimit` yields `f.homotopyInverse` (with linear
  part `e.inv`) and `f.homotopyInverseRight` (with linear homotopy `e.adjointHomotopyInv`).
* Postcomposing the closed degree-zero reduced transformation `id_A - g ∘ f` with `f` gives
  `f - f ∘ g ∘ f`, which is bounded by `f.homotopyInverseRight.compLeft f`.  Lifting along
  `compRight f` (`AInfinityHom.exists_reducedTransformationDifferential_eq_of_compRight`) produces
  the left homotopy `f.homotopyInverseLeft : id_A ~ g ∘ f`.

Thus over any commutative ring `R`, an `A∞` morphism is a homotopy equivalence if and only if its
linear part underlies a homogeneous `LinearHomotopyEquiv`
(`isHomotopyEquiv_iff_exists_linearHomotopyEquiv`), and homotopy equivalences are closed under
composition (`IsHomotopyEquiv.comp`).

Over a field `K`, every graded differential vector space contracts onto its cohomology
(`InternalGrading.homologyContraction`), so every quasi-isomorphism induces a homogeneous
`LinearHomotopyEquiv` on `(A, m₁) → (B, m₁)` (`LinearHomotopyEquiv.ofHomologyMapBijective`).
Specializing the commutative-ring construction yields the **Whitehead theorem for `A∞` algebras
over a field**: an `A∞` morphism over a field is a homotopy equivalence if and only if it is a
quasi-isomorphism (`isHomotopyEquiv_iff_isQuasiIso`).

## Main definitions

* `TauCeti.AInfinityHom.IsHomotopyEquiv`: an `A∞` morphism admitting a two-sided homotopy inverse.
* `TauCeti.AInfinityHom.homotopyInverse`: the `A∞` homotopy inverse constructed from a homogeneous
  `LinearHomotopyEquiv` on the linear part.
* `TauCeti.AInfinityHom.homotopyInverseRight` and `TauCeti.AInfinityHom.homotopyInverseLeft`: the
  accompanying homotopies `id_B ~ f ∘ g` and `id_A ~ g ∘ f`.
* `TauCeti.AInfinityHom.IsQuasiIso.homotopyInverse`, `homotopyInverseRight`, and
  `homotopyInverseLeft`: the `A∞` homotopy inverse and homotopies of a quasi-isomorphism over a
  field.

## Main results

* `TauCeti.AInfinityHom.IsHomotopyEquiv.isQuasiIso`: every `A∞` homotopy equivalence is a
  quasi-isomorphism.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyEquiv`: over a commutative ring,
  `f` is an `A∞` homotopy equivalence iff `f₁` underlies a homogeneous `LinearHomotopyEquiv`.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`: `A∞` homotopy equivalences compose.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, an `A∞` morphism is a
  homotopy equivalence iff it is a quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, thèse de doctorat, Université Paris 7 (2003),
  Chapitre 1, Théorème 1.3.1.2.
* R. M. Vogt, *A note on homotopy equivalences*, Proc. Amer. Math. Soc. 32 (1972), 627--629.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### Comparison with `LinearMap.homologyMap` and arity-one homogeneity -/

/-- The linear part of an `A∞` morphism intertwines the unary differentials. -/
theorem linearPart_comp_differential (f : AInfinityHom AA BB) :
    f.linearPart ∘ₗ AA.differential = BB.differential ∘ₗ f.linearPart :=
  LinearMap.ext fun a ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AInfinityAlgebra.differential_apply,
      AInfinityAlgebra.differential_apply, f.linearPart_m_one]

/-- Under `cohomologyEquivHomology`, `cohomologyMap` corresponds to `LinearMap.homologyMap` of the
linear part. -/
theorem cohomologyEquivHomology_cohomologyMap (f : AInfinityHom AA BB) (c : AA.Cohomology) :
    BB.cohomologyEquivHomology (f.cohomologyMap c) =
      _root_.LinearMap.homologyMap f.linearPart AA.differential_comp_self_eq_zero
        BB.differential_comp_self_eq_zero f.linearPart_comp_differential
        (AA.cohomologyEquivHomology c) := by
  obtain ⟨x, hx, rfl⟩ := AA.exists_cohomologyClass_eq c
  rw [cohomologyMap_cohomologyClass, BB.cohomologyEquivHomology_cohomologyClass,
    AA.cohomologyEquivHomology_cohomologyClass, _root_.LinearMap.homologyπ_apply,
    _root_.LinearMap.homologyπ_apply, _root_.LinearMap.homologyMap_mk]

/-- An `A∞` morphism is a quasi-isomorphism if and only if its linear part induces a bijection on
`LinearMap.homology`. -/
theorem isQuasiIso_iff_bijective_homologyMap (f : AInfinityHom AA BB) :
    f.IsQuasiIso ↔
      Function.Bijective
        (_root_.LinearMap.homologyMap f.linearPart AA.differential_comp_self_eq_zero
          BB.differential_comp_self_eq_zero f.linearPart_comp_differential) := by
  let hMap := _root_.LinearMap.homologyMap f.linearPart AA.differential_comp_self_eq_zero
    BB.differential_comp_self_eq_zero f.linearPart_comp_differential
  have hcomm : ⇑BB.cohomologyEquivHomology ∘ ⇑f.cohomologyMap =
      ⇑hMap ∘ ⇑AA.cohomologyEquivHomology := by
    funext c
    exact f.cohomologyEquivHomology_cohomologyMap c
  rw [isQuasiIso_def,
    ← Function.Bijective.of_comp_iff' BB.cohomologyEquivHomology.bijective ⇑f.cohomologyMap,
    hcomm,
    Function.Bijective.of_comp_iff ⇑hMap AA.cohomologyEquivHomology.bijective]

/-- The arity-one component of an `A∞` homotopy is homogeneous of degree `-1`. -/
theorem Homotopy.isHomogeneous_linearHomotopy {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.linearHomotopy AA.grading.piece BB.grading.piece (-1) := by
  rw [LinearMap.isHomogeneous_def]
  intro p a ha
  simpa only [sub_eq_add_neg] using h.linearHomotopy_mem ha

/-! ### Homotopy equivalences -/

/-- An `A∞` morphism `f : A ⟶ B` is a **homotopy equivalence** when there exists an `A∞` morphism
`g : B ⟶ A` together with homotopies `id_A ~ g ∘ f` and `id_B ~ f ∘ g`. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (AInfinityHom.id AA) (g.comp f)) ∧
      Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g))

/-- An `A∞` morphism is a homotopy equivalence exactly when it has a two-sided homotopy inverse. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (AInfinityHom.id AA) (g.comp f)) ∧
          Nonempty (Homotopy (AInfinityHom.id BB) (f.comp g)) :=
  Iff.rfl

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv := by
  refine ⟨AInfinityHom.id AA, ?_, ?_⟩
  · rw [comp_id]
    exact ⟨Homotopy.refl _⟩
  · rw [comp_id]
    exact ⟨Homotopy.refl _⟩

/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  obtain ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf
  refine ⟨g, ?_, ?_⟩
  · rw [hg₁]
    exact ⟨Homotopy.refl _⟩
  · rw [hg₂]
    exact ⟨Homotopy.refl _⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  have hgf : g.cohomologyMap.comp f.cohomologyMap = NonUnitalAlgHom.id R AA.Cohomology := by
    rw [← cohomologyMap_comp, ← hL.cohomologyMap_eq, cohomologyMap_id]
  have hfg : f.cohomologyMap.comp g.cohomologyMap = NonUnitalAlgHom.id R BB.Cohomology := by
    rw [← cohomologyMap_comp, ← hR.cohomologyMap_eq, cohomologyMap_id]
  rw [isQuasiIso_def]
  exact Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap,
    fun x ↦ DFunLike.congr_fun hgf x, fun y ↦ DFunLike.congr_fun hfg y⟩

/-- Passing to arity one extracts a homogeneous `LinearHomotopyEquiv` between `(A, m₁)` and
`(B, m₁)` from an `A∞` homotopy equivalence. -/
theorem IsHomotopyEquiv.exists_linearHomotopyEquiv {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) :
    ∃ e : LinearHomotopyEquiv AA.differential BB.differential,
      e.hom = f.linearPart ∧
        LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0 ∧
        LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1) ∧
        LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1) := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  refine ⟨{
    hom := f.linearPart
    inv := g.linearPart
    homotopyHom := hL.linearHomotopy
    homotopyInv := hR.linearHomotopy
    dN_comp_hom := f.linearPart_comp_differential.symm
    dM_comp_inv := g.linearPart_comp_differential.symm
    dM_comp_homotopyHom_add_homotopyHom_comp_dM := LinearMap.ext fun a ↦ by
      have h := (hL.linearPart_sub_linearPart a).symm
      rw [linearPart_id, linearPart_comp, ← AInfinityAlgebra.differential_apply,
        ← AInfinityAlgebra.differential_apply] at h
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply]
      exact h
    dN_comp_homotopyInv_add_homotopyInv_comp_dN := LinearMap.ext fun b ↦ by
      have h := (hR.linearPart_sub_linearPart b).symm
      rw [linearPart_id, linearPart_comp, ← AInfinityAlgebra.differential_apply,
        ← AInfinityAlgebra.differential_apply] at h
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply]
      exact h
  }, rfl, g.isHomogeneous_linearPart, hL.isHomogeneous_linearHomotopy,
    hR.isHomogeneous_linearHomotopy⟩

/-! ### Recursive construction of a homotopy inverse -/

section Construction

private noncomputable abbrev stageBarHomotopy (f : AInfinityHom AA BB)
    (tG : ReducedTensorWords R B →ₗ[R] A) (tH : ReducedTensorWords R B →ₗ[R] B) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
    (f.barMap ∘ₗ ReducedTensorWords.coalgHom R tG) tH

private noncomputable abbrev stageMorphismDefect (AA : AInfinityAlgebra R A)
    (BB : AInfinityAlgebra R B) (tG : ReducedTensorWords R B →ₗ[R] A) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  ReducedTensorWords.coalgHom R tG ∘ₗ BB.barDifferential -
    AA.barDifferential ∘ₗ ReducedTensorWords.coalgHom R tG

private noncomputable abbrev stageHomotopyDefect (f : AInfinityHom AA BB)
    (tG : ReducedTensorWords R B →ₗ[R] A) (tH : ReducedTensorWords R B →ₗ[R] B) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  (LinearMap.id - f.barMap ∘ₗ ReducedTensorWords.coalgHom R tG) -
    (BB.barDifferential ∘ₗ stageBarHomotopy f tG tH +
      stageBarHomotopy f tG tH ∘ₗ BB.barDifferential)

/-- Stage `n` of the recursive construction of an `A∞` homotopy inverse `g : B ⟶ A` and right
homotopy `H : id_B ~ f ∘ g`. -/
private structure InverseStage (f : AInfinityHom AA BB) (n : ℕ) where
  tG : ReducedTensorWords R B →ₗ[R] A
  tH : ReducedTensorWords R B →ₗ[R] B
  htG : LinearMap.IsHomogeneous tG
    (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  htH : LinearMap.IsHomogeneous tH
    (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)
  hM : ∀ w ∈ ReducedTensorWords.filtration R B n, stageMorphismDefect AA BB tG w = 0
  hR : ∀ w ∈ ReducedTensorWords.filtration R B n, stageHomotopyDefect f tG tH w = 0

private noncomputable def inverseStageZero (f : AInfinityHom AA BB) : InverseStage f 0 where
  tG := 0
  tH := 0
  htG := LinearMap.isHomogeneous_zero _ _ _
  htH := LinearMap.isHomogeneous_zero _ _ _
  hM w hw := by
    rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hw
    rw [hw, map_zero]
  hR w hw := by
    rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hw
    rw [hw, map_zero]

private noncomputable def inverseStageSucc {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    (n : ℕ) (S : InverseStage f n) : InverseStage f (n + 1) := by
  let G := ReducedTensorWords.coalgHom R S.tG
  let H := stageBarHomotopy f S.tG S.tH
  let M := stageMorphismDefect AA BB S.tG
  let R_def := stageHomotopyDefect f S.tG S.tH
  let L := ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩
  let u : ReducedTensorWords R B →ₗ[R] A := (ReducedTensorWords.letter R A ∘ₗ M) ∘ₗ L
  let v : ReducedTensorWords R B →ₗ[R] B := (ReducedTensorWords.letter R B ∘ₗ R_def) ∘ₗ L
  have hGc : ReducedTensorWords.IsCoalgHom R G := ReducedTensorWords.isCoalgHom_coalgHom S.tG
  have hG₀ : LinearMap.IsHomogeneous G
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 0 :=
    ReducedTensorWords.isHomogeneous_coalgHom S.htG
  have hFGc : ReducedTensorWords.IsCoalgHom R (f.barMap ∘ₗ G) := f.isCoalgHom_barMap.comp hGc
  have hFG₀ : LinearMap.IsHomogeneous (f.barMap ∘ₗ G)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hG₀
  have hHc : ReducedTensorWords.IsGradedCoderivationAlong (BB.grading.shift 1) 1
      LinearMap.id (f.barMap ∘ₗ G) H :=
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong
      (ReducedTensorWords.isCoalgHom_id B) hFGc S.tH
  have hH₁ : LinearMap.IsHomogeneous H
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1) :=
    ReducedTensorWords.isHomogeneous_gradedCoderivAlong (LinearMap.isHomogeneous_id _) hFG₀ S.htH
  have hMc : ReducedTensorWords.IsGradedCoderivationAlong (BB.grading.shift 1) 1 G G M :=
    (hGc.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential).sub
      (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hGc hG₀)
  have hM_hom : LinearMap.IsHomogeneous M
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 1 :=
    LinearMap.IsHomogeneous.sub
      (by simpa only [add_zero] using hG₀.comp BB.isHomogeneous_barDifferential)
      (by simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp hG₀)
  have hR_hom : LinearMap.IsHomogeneous R_def
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 :=
    ((LinearMap.isHomogeneous_id _).sub hFG₀).sub
      (LinearMap.IsHomogeneous.add
        (by simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp hH₁)
        (by simpa only [add_neg_cancel] using hH₁.comp BB.isHomogeneous_barDifferential))
  have hf_sh : LinearMap.IsHomogeneous e.hom
      (AA.grading.shift 1).piece (BB.grading.shift 1).piece 0 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 (he ▸ f.isHomogeneous_linearPart)
  have hg_sh : LinearMap.IsHomogeneous e.inv
      (BB.grading.shift 1).piece (AA.grading.shift 1).piece 0 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hinv
  have hhA_sh : LinearMap.IsHomogeneous e.homotopyHom
      (AA.grading.shift 1).piece (AA.grading.shift 1).piece (-1) :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hhA
  have hhB_sh : LinearMap.IsHomogeneous e.homotopyInv
      (BB.grading.shift 1).piece (BB.grading.shift 1).piece (-1) :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hhB
  have hu_hom : LinearMap.IsHomogeneous u
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece (0 + 1) := by
    simpa only [zero_add, add_zero] using
      ((ReducedTensorWords.isHomogeneous_letter (AA.grading.shift 1)).comp hM_hom).comp
        (ReducedTensorWords.isHomogeneous_lengthProj _ _)
  have hv_hom : LinearMap.IsHomogeneous v
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [add_zero] using
      ((ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp hR_hom).comp
        (ReducedTensorWords.isHomogeneous_lengthProj _ _)
  let x : ReducedTensorWords R B →ₗ[R] A := e.coupledLift u v
  let z : ReducedTensorWords R B →ₗ[R] B := e.coupledHomotopy u v
  have hx_hom : LinearMap.IsHomogeneous x
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 :=
    e.isHomogeneous_coupledLift hg_sh hhA_sh hu_hom hv_hom
  have hz_hom : LinearMap.IsHomogeneous z
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) :=
    e.isHomogeneous_coupledHomotopy hf_sh hg_sh hhA_sh hhB_sh hu_hom hv_hom
  -- Primitivity of `M` and `R_def` on `filtration R B (n + 1)`.
  have hM_prim : ∀ {y}, y ∈ ReducedTensorWords.filtration R B (n + 1) →
      M y = ReducedTensorWords.ofLetter R A (ReducedTensorWords.letter R A (M y)) :=
    fun hy ↦ hMc.apply_eq_ofLetter_of_mem_filtration_succ S.hM hy
  have hR_prim : ∀ {y}, y ∈ ReducedTensorWords.filtration R B (n + 1) →
      R_def y = ReducedTensorWords.ofLetter R B (ReducedTensorWords.letter R B (R_def y)) := by
    intro y hy
    refine hHc.sub_sub_comp_add_comp_eq_ofLetter_of_mem_filtration hH₁
      (by rw [one_mul, Int.negOnePow_neg, Int.negOnePow_one])
      BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential
      (by rw [one_mul, Int.negOnePow_one])
      BB.isGradedCoderivation_barDifferential (ReducedTensorWords.isCoalgHom_id B) hFGc
      (LinearMap.isHomogeneous_id _) (fun _ _ ↦ rfl) (fun w hw ↦ ?_) S.hR hy
    have hwM : G (BB.barDifferential w) = AA.barDifferential (G w) := by
      have h := S.hM w hw
      dsimp only [stageMorphismDefect] at h
      rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply] at h
      exact sub_eq_zero.1 h
    rw [LinearMap.comp_apply, LinearMap.comp_apply, f.barDifferential_barMap, hwM]
  -- Coupled cocycle equations for `(u, v)` with sign `s = -1`.
  have hu_eq : AA.differential ∘ₗ u -
      (-1 : ℤˣ) • (u ∘ₗ BB.unaryBarDifferential) = 0 := by
    refine LinearMap.ext fun y ↦ ?_
    have hLy := ReducedTensorWords.lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ y
    have hhigh : BB.higherBarDifferential (L y) ∈ ReducedTensorWords.filtration R B n :=
      BB.higherBarDifferential_filtration n ⟨L y, hLy, rfl⟩
    have hcomm : L (BB.unaryBarDifferential y) = BB.unaryBarDifferential (L y) :=
      LinearMap.congr_fun (BB.lengthProj_comp_unaryBarDifferential ⟨n + 1, n.succ_pos⟩) y
    have hM_sq : AA.barDifferential (M (L y)) + M (BB.barDifferential (L y)) = 0 := by
      have hbA : AA.barDifferential (AA.barDifferential (G (L y))) = 0 :=
        LinearMap.congr_fun AA.barDifferential_sq (G (L y))
      have hbB : BB.barDifferential (BB.barDifferential (L y)) = 0 :=
        LinearMap.congr_fun BB.barDifferential_sq (L y)
      dsimp only [M, stageMorphismDefect]
      rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, map_sub, hbA, hbB, map_zero]
      abel
    have hval := congrArg (ReducedTensorWords.letter R A) hM_sq
    rw [map_add, map_zero, hM_prim hLy, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      AA.letter_comp_barDifferential, AInfinityAlgebra.taylor_ofLetter,
      ← AInfinityAlgebra.differential_apply, BB.barDifferential_eq_unary_add_higher,
      LinearMap.add_apply, map_add, map_add, S.hM _ hhigh, map_zero, add_zero] at hval
    rw [Units.neg_smul, one_smul, sub_neg_eq_add]
    dsimp only [u]
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, hcomm]
    exact hval
  have hv_eq : BB.differential ∘ₗ v +
      (-1 : ℤˣ) • (v ∘ₗ BB.unaryBarDifferential) = e.hom ∘ₗ u := by
    refine LinearMap.ext fun y ↦ ?_
    have hLy := ReducedTensorWords.lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ y
    have hhigh : BB.higherBarDifferential (L y) ∈ ReducedTensorWords.filtration R B n :=
      BB.higherBarDifferential_filtration n ⟨L y, hLy, rfl⟩
    have hcomm : L (BB.unaryBarDifferential y) = BB.unaryBarDifferential (L y) :=
      LinearMap.congr_fun (BB.lengthProj_comp_unaryBarDifferential ⟨n + 1, n.succ_pos⟩) y
    have hR_comm : BB.barDifferential (R_def (L y)) - R_def (BB.barDifferential (L y)) =
        f.barMap (M (L y)) := by
      have hbB₁ : BB.barDifferential (BB.barDifferential (f.stageBarHomotopy S.tG S.tH (L y))) =
          0 := LinearMap.congr_fun BB.barDifferential_sq (f.stageBarHomotopy S.tG S.tH (L y))
      have hbB₂ : BB.barDifferential (BB.barDifferential (L y)) = 0 :=
        LinearMap.congr_fun BB.barDifferential_sq (L y)
      dsimp only [R_def, stageHomotopyDefect, M, stageMorphismDefect]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap, hbB₁, hbB₂, map_zero]
      abel
    have hval := congrArg (ReducedTensorWords.letter R B) hR_comm
    rw [map_sub, hR_prim hLy, hM_prim hLy,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R B), BB.letter_comp_barDifferential,
      AInfinityAlgebra.taylor_ofLetter, ← AInfinityAlgebra.differential_apply,
      barMap_ofLetter, ReducedTensorWords.letter_ofLetter, ← he,
      BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, map_add,
      S.hR _ hhigh, map_zero, add_zero] at hval
    rw [Units.neg_smul, one_smul, ← sub_eq_add_neg]
    dsimp only [u, v]
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      hcomm]
    exact hval
  -- Vanishing of `x` and `z`, and agreement of `(G', H')` with `(G, H)`, on `filtration R B n`.
  have hx_zero : ∀ w ∈ ReducedTensorWords.filtration R B n, x w = 0 := fun w hw ↦ by
    have hLw : L w = 0 :=
      ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R B n.lt_succ_self hw
    simp only [x, LinearHomotopyEquiv.coupledLift_def, u, v, LinearMap.add_apply,
      LinearMap.comp_apply, hLw, map_zero, add_zero]
  have hz_zero : ∀ w ∈ ReducedTensorWords.filtration R B n, z w = 0 := fun w hw ↦ by
    have hLw : L w = 0 :=
      ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R B n.lt_succ_self hw
    simp only [z, LinearHomotopyEquiv.coupledHomotopy_def, u, v, LinearMap.sub_apply,
      LinearMap.comp_apply, hLw, map_zero, sub_zero]
  let tG' := S.tG + x
  let tH' := S.tH + z
  let G' := ReducedTensorWords.coalgHom R tG'
  let H' := stageBarHomotopy f tG' tH'
  have hG'c : ReducedTensorWords.IsCoalgHom R G' := ReducedTensorWords.isCoalgHom_coalgHom tG'
  have hG'_eq : ∀ w ∈ ReducedTensorWords.filtration R B n, G' w = G w := fun w hw ↦
    hG'c.apply_eq_of_mem_filtration hGc
      (fun y hy ↦ by
        rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
          ReducedTensorWords.letter_comp_coalgHom,
          ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
          ReducedTensorWords.letter_comp_coalgHom, LinearMap.add_apply, hx_zero y hy, add_zero])
      hw
  have hG'_succ : ∀ {y}, y ∈ ReducedTensorWords.filtration R B (n + 1) →
      G' y = G y + ReducedTensorWords.ofLetter R A (x y) := by
    intro y hy
    have hsub := (hG'c.isGradedCoderivationAlong_sub (G := BB.grading.shift 1) hGc)
      |>.apply_eq_ofLetter_of_mem_filtration_succ
        (fun w hw ↦ by rw [LinearMap.sub_apply, hG'_eq w hw, sub_self]) hy
    rw [LinearMap.sub_apply, map_sub,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      ReducedTensorWords.letter_comp_coalgHom,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      ReducedTensorWords.letter_comp_coalgHom,
      LinearMap.add_apply, add_sub_cancel_left] at hsub
    exact eq_add_of_sub_eq' hsub
  have hH'c : ReducedTensorWords.IsGradedCoderivationAlong (BB.grading.shift 1) 1
      LinearMap.id (f.barMap ∘ₗ G') H' :=
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong
      (ReducedTensorWords.isCoalgHom_id B) (f.isCoalgHom_barMap.comp hG'c) tH'
  have hH'_eq : ∀ w ∈ ReducedTensorWords.filtration R B n, H' w = H w := fun w hw ↦
    hH'c.apply_eq_of_mem_filtration_of_apply_eq hHc (fun _ _ ↦ rfl)
      (fun y hy ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply,
          hG'_eq y (ReducedTensorWords.filtration_monotone R B (Nat.sub_le n 1) hy)])
      (fun y hy ↦ by
        rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
          ReducedTensorWords.letter_comp_gradedCoderivAlong,
          ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
          ReducedTensorWords.letter_comp_gradedCoderivAlong,
          LinearMap.add_apply, hz_zero y hy, add_zero]) hw
  have hH'_succ : ∀ {y}, y ∈ ReducedTensorWords.filtration R B (n + 1) →
      H' y = H y + ReducedTensorWords.ofLetter R B (z y) := by
    intro y hy
    have hsub := hH'c.sub_apply_eq_ofLetter_of_mem_filtration_succ hHc (fun _ _ ↦ rfl)
      (fun w hw ↦ by rw [LinearMap.comp_apply, LinearMap.comp_apply, hG'_eq w hw]) hH'_eq hy
    rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
      ReducedTensorWords.letter_comp_gradedCoderivAlong,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
      ReducedTensorWords.letter_comp_gradedCoderivAlong,
      LinearMap.add_apply, add_sub_cancel_left] at hsub
    exact eq_add_of_sub_eq' hsub
  refine ⟨tG', tH', S.htG.add hx_hom, S.htH.add hz_hom, ?_, ?_⟩
  · have hx_sol := e.dM_comp_coupledLift_add_smul hu_eq hv_eq
    intro y hy
    have hby := BB.barDifferential_mem_filtration hy
    have hhigh : BB.higherBarDifferential y ∈ ReducedTensorWords.filtration R B n :=
      BB.higherBarDifferential_filtration n ⟨y, hy, rfl⟩
    have hM_zero : ∀ w ∈ ReducedTensorWords.filtration R B n,
        (ReducedTensorWords.letter R A ∘ₗ M) w = 0 := fun w hw ↦ by
      rw [LinearMap.comp_apply, S.hM w hw, map_zero]
    have hu_y : ReducedTensorWords.letter R A (M y) = u y :=
      (ReducedTensorWords.apply_lengthProj_of_mem_filtration R B hM_zero hy).symm
    have hx_by : x (BB.barDifferential y) = x (BB.unaryBarDifferential y) := by
      rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, hx_zero _ hhigh,
        add_zero]
    have hx_sol_y : AA.differential (x y) - x (BB.unaryBarDifferential y) = u y := by
      have h := LinearMap.congr_fun hx_sol y
      rwa [Units.neg_smul, one_smul, ← sub_eq_add_neg, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.comp_apply] at h
    -- Fold `coalgHom R tG'` to `G'` so `hG'_succ` rewrites both occurrences.
    change G' (BB.barDifferential y) - AA.barDifferential (G' y) = 0
    rw [hG'_succ hby, hG'_succ hy, hx_by, map_add, AInfinityAlgebra.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply]
    have hsplit : (G (BB.barDifferential y) +
          ReducedTensorWords.ofLetter R A (x (BB.unaryBarDifferential y))) -
        (AA.barDifferential (G y) + ReducedTensorWords.ofLetter R A (AA.differential (x y))) =
        M y -
          ReducedTensorWords.ofLetter R A
            (AA.differential (x y) - x (BB.unaryBarDifferential y)) := by
      dsimp only [M, stageMorphismDefect]
      rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub]
      abel
    rw [hsplit, hM_prim hy, hu_y, hx_sol_y, sub_self]
  · have hz_sol := e.sub_hom_comp_coupledLift hu_eq hv_eq
    intro y hy
    have hby := BB.barDifferential_mem_filtration hy
    have hhigh : BB.higherBarDifferential y ∈ ReducedTensorWords.filtration R B n :=
      BB.higherBarDifferential_filtration n ⟨y, hy, rfl⟩
    have hR_zero : ∀ w ∈ ReducedTensorWords.filtration R B n,
        (ReducedTensorWords.letter R B ∘ₗ R_def) w = 0 := fun w hw ↦ by
      rw [LinearMap.comp_apply, S.hR w hw, map_zero]
    have hv_y : ReducedTensorWords.letter R B (R_def y) = v y :=
      (ReducedTensorWords.apply_lengthProj_of_mem_filtration R B hR_zero hy).symm
    have hz_by : z (BB.barDifferential y) = z (BB.unaryBarDifferential y) := by
      rw [BB.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, hz_zero _ hhigh,
        add_zero]
    have hz_sol_y : v y - e.hom (x y) =
        BB.differential (z y) + z (BB.unaryBarDifferential y) := by
      have h := LinearMap.congr_fun hz_sol y
      rwa [Units.neg_smul, one_smul, sub_neg_eq_add, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply] at h
    -- Fold `coalgHom R tG'` and `stageBarHomotopy f tG' tH'` to `G'` and `H'`.
    change (y - f.barMap (G' y)) -
        (BB.barDifferential (H' y) + H' (BB.barDifferential y)) = 0
    rw [hG'_succ hy, hH'_succ hy, hH'_succ hby, hz_by, map_add, barMap_ofLetter, ← he,
      map_add, AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply]
    have hsplit : (y - (f.barMap (G y) + ReducedTensorWords.ofLetter R B (e.hom (x y)))) -
        ((BB.barDifferential (H y) + ReducedTensorWords.ofLetter R B (BB.differential (z y))) +
          (H (BB.barDifferential y) +
            ReducedTensorWords.ofLetter R B (z (BB.unaryBarDifferential y)))) =
        R_def y -
          ReducedTensorWords.ofLetter R B
            (e.hom (x y) + (BB.differential (z y) + z (BB.unaryBarDifferential y))) := by
      dsimp only [R_def, stageHomotopyDefect]
      rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_add, map_add]
      abel
    rw [hsplit, hR_prim hy, hv_y, ← hz_sol_y, ← map_sub]
    have hcancel : v y - (e.hom (x y) + (v y - e.hom (x y))) = 0 := by abel
    rw [hcancel, map_zero]

private theorem inverseStageSucc_tG_eq {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    (n : ℕ) (S : InverseStage f n) {w : ReducedTensorWords R B}
    (hw : w ∈ ReducedTensorWords.filtration R B n) :
    (inverseStageSucc e he hinv hhA hhB n S).tG w = S.tG w := by
  have hLw : ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩ w = 0 :=
    ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R B n.lt_succ_self hw
  simp only [inverseStageSucc, LinearHomotopyEquiv.coupledLift_def, LinearMap.add_apply,
    LinearMap.comp_apply, hLw, map_zero, add_zero]

private theorem inverseStageSucc_tH_eq {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    (n : ℕ) (S : InverseStage f n) {w : ReducedTensorWords R B}
    (hw : w ∈ ReducedTensorWords.filtration R B n) :
    (inverseStageSucc e he hinv hhA hhB n S).tH w = S.tH w := by
  have hLw : ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩ w = 0 :=
    ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R B n.lt_succ_self hw
  simp only [inverseStageSucc, LinearHomotopyEquiv.coupledHomotopy_def, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, hLw, map_zero, sub_zero, add_zero]

private noncomputable def inverseStageSeq (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    ∀ n, InverseStage f n :=
  Nat.rec (inverseStageZero f) fun n S ↦ inverseStageSucc e he hinv hhA hhB n S

private theorem inverseStageSeq_one (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    inverseStageSeq f e he hinv hhA hhB 1 =
      inverseStageSucc e he hinv hhA hhB 0 (inverseStageZero f) :=
  rfl

private theorem inverseStageSeq_tG_stab (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    ∀ n, ∀ w ∈ ReducedTensorWords.filtration R B n,
      (inverseStageSeq f e he hinv hhA hhB (n + 1)).tG w =
        (inverseStageSeq f e he hinv hhA hhB n).tG w :=
  fun n _ hw ↦
    inverseStageSucc_tG_eq e he hinv hhA hhB n (inverseStageSeq f e he hinv hhA hhB n) hw

private theorem inverseStageSeq_tH_stab (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    ∀ n, ∀ w ∈ ReducedTensorWords.filtration R B n,
      (inverseStageSeq f e he hinv hhA hhB (n + 1)).tH w =
        (inverseStageSeq f e he hinv hhA hhB n).tH w :=
  fun n _ hw ↦
    inverseStageSucc_tH_eq e he hinv hhA hhB n (inverseStageSeq f e he hinv hhA hhB n) hw

/-- **An `A∞` homotopy inverse from a linear homotopy equivalence on `(A, m₁) → (B, m₁)`.**
Given an `A∞` morphism `f : A ⟶ B` over any commutative ring whose linear part `f₁` underlies a
homogeneous `LinearHomotopyEquiv` `e` between `(A, m₁)` and `(B, m₁)`, `f.homotopyInverse` is an
`A∞` morphism `B ⟶ A` with linear part `e.inv`, equipped with right and left homotopies
`f.homotopyInverseRight` and `f.homotopyInverseLeft`. -/
noncomputable def homotopyInverse (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    AInfinityHom BB AA := by
  let seqG : ℕ → ReducedTensorWords R B →ₗ[R] A :=
    fun n ↦ (inverseStageSeq f e he hinv hhA hhB n).tG
  have hstabG := inverseStageSeq_tG_stab f e he hinv hhA hhB
  let tG := ReducedTensorWords.stabilisingLimit seqG
  have htG : LinearMap.IsHomogeneous tG
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 :=
    ReducedTensorWords.isHomogeneous_stabilisingLimit hstabG
      fun n ↦ (inverseStageSeq f e he hinv hhA hhB n).htG
  refine
    { barMap := ReducedTensorWords.coalgHom R tG
      isCoalgHom_barMap := ReducedTensorWords.isCoalgHom_coalgHom tG
      isHomogeneous_barMap := ReducedTensorWords.isHomogeneous_coalgHom htG
      barDifferential_comp_barMap := ?_ }
  refine LinearMap.ext fun w ↦ ?_
  obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R B w
  have hbw := BB.barDifferential_mem_filtration hn
  have hGn :=
    ReducedTensorWords.coalgHom_stabilisingLimit_apply_of_mem_filtration (t := seqG) hstabG hn
  have hGnb :=
    ReducedTensorWords.coalgHom_stabilisingLimit_apply_of_mem_filtration (t := seqG) hstabG hbw
  have hM := (inverseStageSeq f e he hinv hhA hhB n).hM w hn
  dsimp only [stageMorphismDefect] at hM
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply] at hM
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hGn, hGnb]
  exact (sub_eq_zero.1 hM).symm

/-- The linear part of `f.homotopyInverse` is the chain-homotopy inverse `e.inv`. -/
@[simp]
theorem linearPart_homotopyInverse (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    (f.homotopyInverse e he hinv hhA hhB).linearPart = e.inv := by
  refine LinearMap.ext fun b ↦ ?_
  let w := ReducedTensorWords.ofLetter R B b
  have hw : w ∈ ReducedTensorWords.filtration R B 1 :=
    ReducedTensorWords.ofLetter_mem_filtration R B b
  have hLw : ReducedTensorWords.lengthProj R B ⟨1, zero_lt_one⟩ w = w :=
    ReducedTensorWords.apply_lengthProj_of_mem_filtration R B (f := LinearMap.id)
      (fun z hz ↦ by
        rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hz
        rw [hz, LinearMap.id_apply]) hw
  rw [linearPart_apply, taylor_def, homotopyInverse, LinearMap.comp_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_coalgHom,
    ReducedTensorWords.stabilisingLimit_apply_of_mem_filtration
      (t := fun k ↦ (inverseStageSeq f e he hinv hhA hhB k).tG)
      (inverseStageSeq_tG_stab f e he hinv hhA hhB) hw,
    inverseStageSeq_one]
  simp only [inverseStageZero, inverseStageSucc, LinearHomotopyEquiv.coupledLift_def,
    stageMorphismDefect, stageHomotopyDefect, stageBarHomotopy, hLw, w,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    LinearMap.id_apply, AInfinityAlgebra.barDifferential_ofLetter,
    ReducedTensorWords.coalgHom_ofLetter, ReducedTensorWords.gradedCoderivAlong_ofLetter,
    ReducedTensorWords.letter_ofLetter, map_zero, sub_zero, add_zero, zero_add]

/-- **The right homotopy `id_B ~ f ∘ f.homotopyInverse`.** -/
noncomputable def homotopyInverseRight (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    Homotopy (AInfinityHom.id BB) (f.comp (f.homotopyInverse e he hinv hhA hhB)) := by
  let g := f.homotopyInverse e he hinv hhA hhB
  let seqG : ℕ → ReducedTensorWords R B →ₗ[R] A :=
    fun n ↦ (inverseStageSeq f e he hinv hhA hhB n).tG
  let seqH : ℕ → ReducedTensorWords R B →ₗ[R] B :=
    fun n ↦ (inverseStageSeq f e he hinv hhA hhB n).tH
  have hstabG := inverseStageSeq_tG_stab f e he hinv hhA hhB
  have hstabH := inverseStageSeq_tH_stab f e he hinv hhA hhB
  let tH := ReducedTensorWords.stabilisingLimit seqH
  have htH : LinearMap.IsHomogeneous tH
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) :=
    ReducedTensorWords.isHomogeneous_stabilisingLimit hstabH
      fun n ↦ (inverseStageSeq f e he hinv hhA hhB n).htH
  let H := ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1
    (AInfinityHom.id BB).barMap (f.comp g).barMap tH
  have hHc : ReducedTensorWords.IsGradedCoderivationAlong (BB.grading.shift 1) 1
      (AInfinityHom.id BB).barMap (f.comp g).barMap H :=
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong
      (AInfinityHom.id BB).isCoalgHom_barMap (f.comp g).isCoalgHom_barMap tH
  have hH₁ : LinearMap.IsHomogeneous H
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1) :=
    ReducedTensorWords.isHomogeneous_gradedCoderivAlong
      (AInfinityHom.id BB).isHomogeneous_barMap (f.comp g).isHomogeneous_barMap htH
  refine
    { barHomotopy := H
      isGradedCoderivationAlong_barHomotopy := hHc
      isHomogeneous_barHomotopy := hH₁
      barMap_sub_barMap := ?_ }
  refine LinearMap.ext fun w ↦ ?_
  obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R B w
  have hbw := BB.barDifferential_mem_filtration hn
  have hG_agree : ∀ {u}, u ∈ ReducedTensorWords.filtration R B n →
      g.barMap u =
        ReducedTensorWords.coalgHom R (inverseStageSeq f e he hinv hhA hhB n).tG u := by
    intro u hu
    dsimp only [g, homotopyInverse]
    exact ReducedTensorWords.coalgHom_stabilisingLimit_apply_of_mem_filtration (t := seqG) hstabG hu
  have hH_agree : ∀ {u}, u ∈ ReducedTensorWords.filtration R B n →
      H u = stageBarHomotopy f (inverseStageSeq f e he hinv hhA hhB n).tG
        (inverseStageSeq f e he hinv hhA hhB n).tH u := by
    intro u hu
    have hHn_c : ReducedTensorWords.IsGradedCoderivationAlong (BB.grading.shift 1) 1
        LinearMap.id
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (inverseStageSeq f e he hinv hhA hhB n).tG)
        (stageBarHomotopy f (inverseStageSeq f e he hinv hhA hhB n).tG
          (inverseStageSeq f e he hinv hhA hhB n).tH) :=
      ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong
        (ReducedTensorWords.isCoalgHom_id B)
        (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom _)) _
    exact hHc.apply_eq_of_mem_filtration_of_apply_eq hHn_c (fun _ _ ↦ by rw [barMap_id])
      (fun v hv ↦ by
        rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply,
          hG_agree (ReducedTensorWords.filtration_monotone R B (Nat.sub_le n 1) hv)])
      (fun v hv ↦ by
        rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
          ReducedTensorWords.letter_comp_gradedCoderivAlong,
          ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
          ReducedTensorWords.letter_comp_gradedCoderivAlong,
          ReducedTensorWords.stabilisingLimit_apply_of_mem_filtration (t := seqH) hstabH hv]) hu
  have hR := (inverseStageSeq f e he hinv hhA hhB n).hR w hn
  dsimp only [stageHomotopyDefect] at hR
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply] at hR
  rw [LinearMap.sub_apply, barMap_id, LinearMap.id_apply, barMap_comp, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hG_agree hn, hH_agree hn,
    hH_agree hbw]
  exact sub_eq_zero.1 hR

/-- The arity-one component of `f.homotopyInverseRight` is Vogt's adjoint-normalized homotopy
`e.adjointHomotopyInv`. -/
@[simp]
theorem linearHomotopy_homotopyInverseRight (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    (f.homotopyInverseRight e he hinv hhA hhB).linearHomotopy = e.adjointHomotopyInv := by
  refine LinearMap.ext fun b ↦ ?_
  let w := ReducedTensorWords.ofLetter R B b
  have hw : w ∈ ReducedTensorWords.filtration R B 1 :=
    ReducedTensorWords.ofLetter_mem_filtration R B b
  have hLw : ReducedTensorWords.lengthProj R B ⟨1, zero_lt_one⟩ w = w :=
    ReducedTensorWords.apply_lengthProj_of_mem_filtration R B (f := LinearMap.id)
      (fun z hz ↦ by
        rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hz
        rw [hz, LinearMap.id_apply]) hw
  rw [Homotopy.linearHomotopy_apply, Homotopy.taylor_def, homotopyInverseRight,
    LinearMap.comp_apply, ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
    ReducedTensorWords.letter_comp_gradedCoderivAlong,
    ReducedTensorWords.stabilisingLimit_apply_of_mem_filtration
      (t := fun k ↦ (inverseStageSeq f e he hinv hhA hhB k).tH)
      (inverseStageSeq_tH_stab f e he hinv hhA hhB) hw,
    inverseStageSeq_one]
  simp only [inverseStageZero, inverseStageSucc, LinearHomotopyEquiv.coupledHomotopy_def,
    stageMorphismDefect, stageHomotopyDefect, stageBarHomotopy, hLw, w,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    LinearMap.id_apply, AInfinityAlgebra.barDifferential_ofLetter,
    ReducedTensorWords.coalgHom_ofLetter, ReducedTensorWords.gradedCoderivAlong_ofLetter,
    ReducedTensorWords.letter_ofLetter, map_zero, sub_zero, add_zero, zero_add]

/-- **The left homotopy `id_A ~ f.homotopyInverse ∘ f`.**  Obtained by lifting the closed
degree-zero reduced transformation `id_A - g ∘ f` along postcomposition with `f`. -/
noncomputable def homotopyInverseLeft (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    Homotopy (AInfinityHom.id AA) ((f.homotopyInverse e he hinv hhA hhB).comp f) := by
  let g := f.homotopyInverse e he hinv hhA hhB
  let hR := f.homotopyInverseRight e he hinv hhA hhB
  let k₁ := AInfinityHom.id AA
  let k₂ := g.comp f
  let U : reducedTransformationCochains k₁ k₂ ((-1 : ℤ) + 1) :=
    ⟨k₁.barMap - k₂.barMap, barMap_sub_barMap_mem_reducedTransformationCochains k₁ k₂⟩
  have hU : reducedTransformationDifferential k₁ k₂ ((-1 : ℤ) + 1) U = 0 :=
    reducedTransformationDifferential_barMap_sub_barMap k₁ k₂
  have heq₁ : (AInfinityHom.id BB).comp f = f.comp k₁ := by
    rw [id_comp, comp_id]
  have heq₂ : (f.comp g).comp f = f.comp k₂ := comp_assoc f g f
  let hRf : Homotopy (f.comp k₁) (f.comp k₂) := heq₁ ▸ heq₂ ▸ hR.compLeft f
  let V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) (-1) :=
    (Homotopy.equivCochains hRf).1
  have hV : reducedTransformationDifferential (f.comp k₁) (f.comp k₂) (-1) V =
      reducedTransformationCochains.compRight f ((-1 : ℤ) + 1) U := by
    apply Subtype.ext
    rw [(Homotopy.equivCochains hRf).2, reducedTransformationCochains.coe_compRight]
    simp only [U, barMap_comp, LinearMap.comp_sub]
  let hlift := exists_reducedTransformationDifferential_eq_of_compRight e he hinv hhA hhB hU hV
  exact Homotopy.equivCochains.symm
    ⟨hlift.choose, congrArg Subtype.val hlift.choose_spec.choose_spec.1⟩

end Construction

/-! ### Characterizations and closure properties -/

/-- On cohomology, `f` and `f.homotopyInverse` are right inverses. -/
@[simp]
theorem cohomologyMap_comp_homotopyInverse (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    f.cohomologyMap.comp (f.homotopyInverse e he hinv hhA hhB).cohomologyMap =
      NonUnitalAlgHom.id R BB.Cohomology := by
  rw [← cohomologyMap_comp, ← (f.homotopyInverseRight e he hinv hhA hhB).cohomologyMap_eq,
    cohomologyMap_id]

/-- On cohomology, `f.homotopyInverse` and `f` are left inverses. -/
@[simp]
theorem cohomologyMap_homotopyInverse_comp (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    (f.homotopyInverse e he hinv hhA hhB).cohomologyMap.comp f.cohomologyMap =
      NonUnitalAlgHom.id R AA.Cohomology := by
  rw [← cohomologyMap_comp, ← (f.homotopyInverseLeft e he hinv hhA hhB).cohomologyMap_eq,
    cohomologyMap_id]

/-- Over any commutative ring, an `A∞` morphism whose linear part underlies a homogeneous
`LinearHomotopyEquiv` is an `A∞` homotopy equivalence. -/
theorem isHomotopyEquiv_of_linearHomotopyEquiv {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    f.IsHomotopyEquiv :=
  ⟨f.homotopyInverse e he hinv hhA hhB,
    ⟨f.homotopyInverseLeft e he hinv hhA hhB⟩,
    ⟨f.homotopyInverseRight e he hinv hhA hhB⟩⟩

/-- The homotopy inverse `f.homotopyInverse` is itself an `A∞` homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_homotopyInverse (f : AInfinityHom AA BB)
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1)) :
    (f.homotopyInverse e he hinv hhA hhB).IsHomotopyEquiv :=
  ⟨f,
    ⟨f.homotopyInverseRight e he hinv hhA hhB⟩,
    ⟨f.homotopyInverseLeft e he hinv hhA hhB⟩⟩

/-- **Characterization of `A∞` homotopy equivalences over a commutative ring.**  An `A∞` morphism
`f : A ⟶ B` is a homotopy equivalence if and only if its linear part `f₁` underlies a homogeneous
`LinearHomotopyEquiv` between `(A, m₁)` and `(B, m₁)`. -/
theorem isHomotopyEquiv_iff_exists_linearHomotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ e : LinearHomotopyEquiv AA.differential BB.differential,
        e.hom = f.linearPart ∧
          LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0 ∧
          LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1) ∧
          LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1) :=
  ⟨IsHomotopyEquiv.exists_linearHomotopyEquiv,
    fun ⟨e, he, hinv, hhA, hhB⟩ ↦ f.isHomotopyEquiv_of_linearHomotopyEquiv e he hinv hhA hhB⟩

/-- `A∞` homotopy equivalences are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨ef, hef, hinvf, hhAf, hhBf⟩ := hf.exists_linearHomotopyEquiv
  obtain ⟨eg, heg, hinvg, hhBg, hhCg⟩ := hg.exists_linearHomotopyEquiv
  have hefh : LinearMap.IsHomogeneous ef.hom AA.grading.piece BB.grading.piece 0 := by
    rw [hef]
    exact f.isHomogeneous_linearPart
  have hegh : LinearMap.IsHomogeneous eg.hom BB.grading.piece CC.grading.piece 0 := by
    rw [heg]
    exact g.isHomogeneous_linearPart
  refine isHomotopyEquiv_of_linearHomotopyEquiv (ef.trans eg) ?_
    (by
      rw [LinearHomotopyEquiv.trans_inv]
      simpa only [add_zero] using hinvf.comp hinvg)
    (LinearHomotopyEquiv.isHomogeneous_trans_homotopyHom hefh hinvf hhAf hhBg)
    (LinearHomotopyEquiv.isHomogeneous_trans_homotopyInv hegh hinvg hhBf hhCg)
  rw [LinearHomotopyEquiv.trans_hom, hef, heg, linearPart_comp]

end CommRing

/-! ### Homotopy inverses of quasi-isomorphisms over a field -/

section Field

variable {K : Type uR} {A : Type uA} {B : Type uB}
  [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

namespace IsQuasiIso

private noncomputable def linearHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearHomotopyEquiv AA.differential BB.differential :=
  LinearHomotopyEquiv.ofHomologyMapBijective
    AA.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ AA.differential_mem_piece hx)
      AA.differential_comp_self_eq_zero
    BB.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ BB.differential_mem_piece hx)
      BB.differential_comp_self_eq_zero
    f.linearPart_comp_differential
    ((f.isQuasiIso_iff_bijective_homologyMap).1 hf)

private theorem linearHomotopyEquiv_hom {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.linearHomotopyEquiv.hom = f.linearPart :=
  LinearHomotopyEquiv.ofHomologyMapBijective_hom _ _ _ _ _ _ _ _

private theorem isHomogeneous_linearHomotopyEquiv_inv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.linearHomotopyEquiv.inv BB.grading.piece AA.grading.piece 0 :=
  LinearHomotopyEquiv.isHomogeneous_ofHomologyMapBijective_inv
    AA.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ AA.differential_mem_piece hx)
      AA.differential_comp_self_eq_zero
    BB.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ BB.differential_mem_piece hx)
      BB.differential_comp_self_eq_zero
    f.isHomogeneous_linearPart f.linearPart_comp_differential
    ((f.isQuasiIso_iff_bijective_homologyMap).1 hf)

private theorem isHomogeneous_linearHomotopyEquiv_homotopyHom {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.linearHomotopyEquiv.homotopyHom
      AA.grading.piece AA.grading.piece (-1) :=
  LinearHomotopyEquiv.isHomogeneous_ofHomologyMapBijective_homotopyHom
    AA.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ AA.differential_mem_piece hx)
      AA.differential_comp_self_eq_zero
    BB.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ BB.differential_mem_piece hx)
      BB.differential_comp_self_eq_zero
    f.isHomogeneous_linearPart f.linearPart_comp_differential
    ((f.isQuasiIso_iff_bijective_homologyMap).1 hf)

private theorem isHomogeneous_linearHomotopyEquiv_homotopyInv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.linearHomotopyEquiv.homotopyInv
      BB.grading.piece BB.grading.piece (-1) :=
  LinearHomotopyEquiv.isHomogeneous_ofHomologyMapBijective_homotopyInv
    AA.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ AA.differential_mem_piece hx)
      AA.differential_comp_self_eq_zero
    BB.grading (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ BB.differential_mem_piece hx)
      BB.differential_comp_self_eq_zero
    f.isHomogeneous_linearPart f.linearPart_comp_differential
    ((f.isQuasiIso_iff_bijective_homologyMap).1 hf)

/-- **An `A∞` homotopy inverse of a quasi-isomorphism over a field.** -/
noncomputable def homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHom BB AA :=
  f.homotopyInverse hf.linearHomotopyEquiv hf.linearHomotopyEquiv_hom
    hf.isHomogeneous_linearHomotopyEquiv_inv
    hf.isHomogeneous_linearHomotopyEquiv_homotopyHom
    hf.isHomogeneous_linearHomotopyEquiv_homotopyInv

/-- The right homotopy `id_B ~ f ∘ hf.homotopyInverse` over a field. -/
noncomputable def homotopyInverseRight {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (AInfinityHom.id BB) (f.comp hf.homotopyInverse) :=
  f.homotopyInverseRight hf.linearHomotopyEquiv hf.linearHomotopyEquiv_hom
    hf.isHomogeneous_linearHomotopyEquiv_inv
    hf.isHomogeneous_linearHomotopyEquiv_homotopyHom
    hf.isHomogeneous_linearHomotopyEquiv_homotopyInv

/-- The left homotopy `id_A ~ hf.homotopyInverse ∘ f` over a field. -/
noncomputable def homotopyInverseLeft {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (AInfinityHom.id AA) (hf.homotopyInverse.comp f) :=
  f.homotopyInverseLeft hf.linearHomotopyEquiv hf.linearHomotopyEquiv_hom
    hf.isHomogeneous_linearHomotopyEquiv_inv
    hf.isHomogeneous_linearHomotopyEquiv_homotopyHom
    hf.isHomogeneous_linearHomotopyEquiv_homotopyInv

/-- On cohomology, `f` and `hf.homotopyInverse` are right inverses. -/
@[simp]
theorem cohomologyMap_comp_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.cohomologyMap.comp hf.homotopyInverse.cohomologyMap = NonUnitalAlgHom.id K BB.Cohomology :=
  f.cohomologyMap_comp_homotopyInverse _ _ _ _ _

/-- On cohomology, `hf.homotopyInverse` and `f` are left inverses. -/
@[simp]
theorem cohomologyMap_homotopyInverse_comp {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.cohomologyMap.comp f.cohomologyMap = NonUnitalAlgHom.id K AA.Cohomology :=
  f.cohomologyMap_homotopyInverse_comp _ _ _ _ _

/-- Over a field, every `A∞` quasi-isomorphism is a homotopy equivalence. -/
theorem isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) : f.IsHomotopyEquiv :=
  ⟨hf.homotopyInverse, ⟨hf.homotopyInverseLeft⟩, ⟨hf.homotopyInverseRight⟩⟩

/-- The homotopy inverse of a quasi-isomorphism over a field is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.IsHomotopyEquiv :=
  ⟨f, ⟨hf.homotopyInverseRight⟩, ⟨hf.homotopyInverseLeft⟩⟩

/-- The homotopy inverse of a quasi-isomorphism over a field is a quasi-isomorphism. -/
@[simp]
theorem isQuasiIso_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.IsQuasiIso :=
  hf.isHomotopyEquiv_homotopyInverse.isQuasiIso

end IsQuasiIso

/-- **Whitehead theorem for `A∞` algebras over a field.**  Over a field, an `A∞` morphism is a
homotopy equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end Field

end AInfinityHom

end TauCeti
