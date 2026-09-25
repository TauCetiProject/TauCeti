/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Graded coderivations of the coaugmented tensor coalgebra

`TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation` packages the `q`-twisted co-Leibniz
rule for the reduced tensor coalgebra `T = ⨁_{n ≥ 1} M^{⊗ n}`.  The coaugmented tensor coalgebra
`TauCeti.TensorWords = ⨁_{n ≥ 0} M^{⊗ n}` adds the empty word, and the module and bimodule theories
need `b` there as well, because a coderivation over `b` of a cofree comodule cuts a word at its two
ends as well.  This file provides the coaugmented counterpart: the letterwise maps
`TauCeti.TensorWords.map` that carry the Koszul twist to tensor words, the total-letter-degree
pieces, and the `q`-twisted co-Leibniz identity of an endomorphism of tensor words.

As in the reduced case the sign is carried by the letterwise extension of the Koszul twist, which
on the degree-`D` piece is scalar multiplication by `(-1)^(q * D)` and fixes the empty word, so the
identity takes the sign-free shape

`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ`

in which `τ = TensorWords.map (InternalGrading.koszulTwist G q)` acts on the left half of every cut.
The coaugmented coproduct has the two degenerate cuts of each word, so a `q`-twisted coderivation
of the coaugmented coalgebra is expected to annihilate the empty word: each degenerate cut is then
read off the term in which the nonempty half is differentiated, and vanishes in the other.  The
predicate `TensorWords.IsGradedCoderivation G q` is this `q`-twisted co-Leibniz condition alone; it
does not include homogeneity of `b`, and it depends only on the parity of `q`.

## Main definitions

* `TauCeti.TensorWords.map`: apply a linear map to every letter of a tensor word.
* `TauCeti.TensorWords.gradedPiece`: the words whose letters have total degree `D`.
* `TauCeti.TensorWords.IsGradedCoderivation`: the `q`-twisted co-Leibniz identity of an endomorphism
  of tensor words.

## Main results

* `TauCeti.TensorWords.iSup_gradedPiece_eq_top`: the total-degree pieces span the coaugmented
  tensor coalgebra, so an identity of linear maps out of tensor words may be checked piecewise.
* `TauCeti.TensorWords.mem_gradedPiece_of_reducedInclusion`: the total-degree pieces of the
  reduced tensor coalgebra embed into the coaugmented ones.
* `TauCeti.TensorWords.map_koszulTwist_apply_of_mem`: on the degree-`D` piece the letterwise Koszul
  twist is scalar multiplication by `(-1) ^ (q * D)`.

Getzler--Jones, Sections 1--2, and Keller, Section 3.6, supply the suspended bar convention these
identities encode.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace TensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Letterwise maps -/

/-- Apply a linear map to every letter of a tensor word, the empty word included. -/
noncomputable def map (f : M →ₗ[R] M) : TensorWords R M →ₗ[R] TensorWords R M :=
  DirectSum.lmap fun _ ↦ PiTensorProduct.map fun _ ↦ f

/-- Mapping a word of a fixed length applies the tensor power of the map in that length. -/
@[simp]
theorem map_of (f : M →ₗ[R] M) (n : ℕ) (x : TensorPower R n M) :
    map f (of R M n x) = of R M n (PiTensorProduct.map (fun _ ↦ f) x) := by
  rw [map, of_def]
  simp

/-- Mapping a pure tensor applies the map to each of its letters. -/
theorem map_of_tprod (f : M →ₗ[R] M) (n : ℕ) (x : Fin n → M) :
    map f (of R M n (PiTensorProduct.tprod R x)) =
      of R M n (PiTensorProduct.tprod R fun i ↦ f (x i)) := by
  simp [map_of]

/-- Mapping the empty word leaves the empty word unchanged. -/
@[simp]
theorem map_one (f : M →ₗ[R] M) : map f (1 : TensorWords R M) = 1 := by
  rw [one_eq_of_zero, map_of, PiTensorProduct.map_tprod]
  have hempty : PiTensorProduct.tprod R (fun i : Fin 0 => f (i.elim0))
      = PiTensorProduct.tprod R (fun i : Fin 0 => (i.elim0 : M)) :=
    (LinearEquiv.symm_apply_apply
      (PiTensorProduct.isEmptyEquiv (R := R) (ι := Fin 0) (s := fun _ : Fin 0 => M))
      _).symm.trans (by
          simp only [PiTensorProduct.isEmptyEquiv_apply_tprod,
            PiTensorProduct.isEmptyEquiv_symm_apply, one_smul]
          exact congrArg (PiTensorProduct.tprod R) (funext fun i => rfl))
  exact congrArg (of R M 0) hempty

/-! ### The grading by total letter degree -/

/-- The words of total degree `D`: the span of the pure tensor words whose letters lie in
homogeneous pieces the degrees of which add up to `D`. -/
noncomputable def gradedPiece (G : InternalGrading R M) (D : ℤ) :
    Submodule R (TensorWords R M) :=
  Submodule.span R {z | ∃ (n : ℕ) (𝒟 : Fin n → ℤ) (x : Fin n → M),
    (∀ i, x i ∈ G.piece (𝒟 i)) ∧ (∑ i, 𝒟 i) = D ∧
      z = of R M n (PiTensorProduct.tprod R x)}

/-- Induction on membership in `gradedPiece`: a consumer may apply this in place of
`Submodule.span_induction`, whose span is sealed behind the definition. -/
theorem gradedPiece_induction {G : InternalGrading R M} {D : ℤ}
    {motive : TensorWords R M → Prop} {z : TensorWords R M}
    (hz : z ∈ gradedPiece G D)
    (mem : ∀ (n : ℕ) (𝒟 : Fin n → ℤ) (x : Fin n → M),
      (∀ i, x i ∈ G.piece (𝒟 i)) → (∑ i, 𝒟 i) = D →
        motive (of R M n (PiTensorProduct.tprod R x)))
    (zero : motive 0)
    (add : ∀ u v, u ∈ gradedPiece G D → v ∈ gradedPiece G D → motive u → motive v →
      motive (u + v))
    (smul : ∀ (a : R) u, u ∈ gradedPiece G D → motive u → motive (a • u)) :
    motive z := by
  induction hz using Submodule.span_induction with
  | mem _ hw =>
    obtain ⟨n, 𝒟, x, hx, hD, rfl⟩ := hw
    exact mem n 𝒟 x hx hD
  | zero => exact zero
  | add u v hu hv ihu ihv => exact add u v hu hv ihu ihv
  | smul a u hu ih => exact smul a u hu ih

/-- A pure tensor word of homogeneous letters of degrees `𝒟 i` lies in the graded piece of total
degree `∑ i, 𝒟 i`. -/
theorem mem_gradedPiece_of_tprod (G : InternalGrading R M) {n : ℕ}
    (x : Fin n → M) (𝒟 : Fin n → ℤ) (h𝒟 : ∀ i, x i ∈ G.piece (𝒟 i)) :
    of R M n (PiTensorProduct.tprod R x) ∈ gradedPiece G (∑ i, 𝒟 i) :=
  Submodule.subset_span ⟨n, 𝒟, x, h𝒟, rfl, rfl⟩

/-- The words of a fixed length generate all tensor words. -/
private theorem iSup_range_of : ⨆ n : ℕ, LinearMap.range (of R M n) = ⊤ := by
  simpa only [of_def, DirectSum.lof] using
    (DFinsupp.iSup_range_lsingle (R := R) (M := fun n : ℕ ↦ TensorPower R n M))

/-- The total-degree pieces span the coaugmented tensor words.  In particular, an equality of
linear maps out of tensor words may be checked separately on these pieces. -/
theorem iSup_gradedPiece_eq_top (G : InternalGrading R M) :
    ⨆ D : ℤ, gradedPiece G D = ⊤ := by
  classical
  apply le_antisymm le_top
  rw [← iSup_range_of]
  refine iSup_le fun n ↦ ?_
  rintro z ⟨z, rfl⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul]
      apply Submodule.smul_mem
      let support : Fin n → Finset ℤ := fun i ↦ (DirectSum.decompose G.piece (x i)).support
      let component : (i : Fin n) → ℤ → M :=
        fun i p ↦ DirectSum.decompose G.piece (x i) p
      have hx (i : Fin n) : ∑ p ∈ support i, component i p = x i := by
        exact DirectSum.sum_support_decompose G.piece (x i)
      have htuple :
          PiTensorProduct.tprod R x =
            ∑ degree ∈ Fintype.piFinset support,
              PiTensorProduct.tprod R (fun i ↦ component i (degree i)) := by
        rw [← (PiTensorProduct.tprod R).map_sum_finset]
        congr 1
        funext i
        exact (hx i).symm
      rw [htuple, map_sum]
      refine Submodule.sum_mem _ fun degree _hdegree ↦ ?_
      refine Submodule.mem_iSup_of_mem (∑ i, degree i) ?_
      apply mem_gradedPiece_of_tprod G
      intro i
      exact (DirectSum.decompose G.piece (x i) (degree i)).property
  | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- On the total-degree-`D` piece of tensor words, applying the Koszul twist to every letter is
scalar multiplication by `(-1) ^ (q * D)`. -/
theorem map_koszulTwist_apply_of_mem (G : InternalGrading R M) {D : ℤ}
    {z : TensorWords R M} (hz : z ∈ gradedPiece G D) (q : ℤ) :
    map (G.koszulTwist q) z = (((q * D).negOnePow : ℤ) : R) • z := by
  refine gradedPiece_induction
    (motive := fun z ↦ map (G.koszulTwist q) z = (((q * D).negOnePow : ℤ) : R) • z) hz
    ?_ (by simp) ?_ ?_
  · intro n degree x hx hD
    rw [map_of_tprod]
    have htuple : (fun i ↦ G.koszulTwist q (x i)) =
        fun i ↦ ((((q * degree i).negOnePow : ℤ) : R) • x i) := by
      funext i
      exact G.koszulTwist_apply_of_mem (hx i) q
    have hsign :
        (((q * ∑ i, degree i).negOnePow : ℤ) : R) =
          ∏ i, (((q * degree i).negOnePow : ℤ) : R) := by
      simp only [← negOnePowCast_eq_intCast, Finset.mul_sum, negOnePowCast_sum]
    rw [htuple, (PiTensorProduct.tprod R).map_smul_univ, map_smul, ← hD, ← hsign]
  · intro u v _ _ hu hv
    simp only [map_add, hu, hv, smul_add]
  · intro c u _ hu
    simp only [map_smul, hu, smul_smul, mul_comm]

/-- A word of the reduced tensor coalgebra is a coaugmented word of the same total degree, so the
reduced degree pieces embed into the coaugmented ones. -/
theorem mem_gradedPiece_of_reducedInclusion {G : InternalGrading R M} {D : ℤ}
    {w : ReducedTensorWords R M} (hw : w ∈ ReducedTensorWords.gradedPiece G D) :
    reducedInclusion R M w ∈ gradedPiece G D := by
  refine ReducedTensorWords.gradedPiece_induction
    (motive := fun w ↦ reducedInclusion R M w ∈ gradedPiece G D) hw ?_ ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    rw [reducedInclusion_of]
    rw [← hD]
    exact mem_gradedPiece_of_tprod G x 𝒟 hx
  · rw [map_zero]
    exact zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-! ### The `q`-twisted co-Leibniz identity -/

/-- A degree-`q` graded coderivation of the coaugmented tensor coalgebra: an endomorphism `b`
satisfying the co-Leibniz rule with the Koszul sign of the left cut half,

`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ`,

in which `τ = TensorWords.map (InternalGrading.koszulTwist G q)` is the letterwise extension of the
Koszul twist and acts on the left half of every cut, exactly as in
`TauCeti.ReducedTensorWords.IsGradedCoderivation`.  Unlike the reduced coproduct, the coaugmented
one cuts a word of positive length at its two ends as well, so a coderivation of this kind is
expected to annihilate the empty word: each degenerate cut is then read off the term in which the
nonempty half is differentiated, the other term vanishing on it.  This is only the twisted
co-Leibniz condition, not a homogeneity requirement on `b`; the latter is recorded by
`TauCeti.TensorWords.gradedPiece`. -/
def IsGradedCoderivation (G : InternalGrading R M) (q : ℤ)
    (b : TensorWords R M →ₗ[R] TensorWords R M) : Prop :=
  deconcatenation R M ∘ₗ b =
    LinearMap.rTensor (TensorWords R M) b ∘ₗ deconcatenation R M +
      (LinearMap.lTensor (TensorWords R M) b ∘ₗ
          LinearMap.rTensor (TensorWords R M)
            (map (InternalGrading.koszulTwist G q))) ∘ₗ
        deconcatenation R M

variable {G : InternalGrading R M} {q : ℤ} {b : TensorWords R M →ₗ[R] TensorWords R M}

/-- The co-Leibniz identity of a graded coderivation, as a reusable `Iff`: this exposes the body of
the predicate to consumers in other modules, for which the definition's body is not exposed. -/
theorem isGradedCoderivation_iff :
    IsGradedCoderivation G q b ↔
      (deconcatenation R M ∘ₗ b =
        LinearMap.rTensor (TensorWords R M) b ∘ₗ deconcatenation R M +
          (LinearMap.lTensor (TensorWords R M) b ∘ₗ
              LinearMap.rTensor (TensorWords R M)
                (map (InternalGrading.koszulTwist G q))) ∘ₗ
            deconcatenation R M) :=
  Iff.rfl

/-- The co-Leibniz identity of a graded coderivation, applied to an element. -/
theorem IsGradedCoderivation.deconcatenation_apply (hb : IsGradedCoderivation G q b)
    (z : TensorWords R M) :
    deconcatenation R M (b z) =
      LinearMap.rTensor (TensorWords R M) b (deconcatenation R M z) +
        LinearMap.lTensor (TensorWords R M) b
          (LinearMap.rTensor (TensorWords R M)
            (map (InternalGrading.koszulTwist G q)) (deconcatenation R M z)) := by
  have h := congrArg (fun f : _ →ₗ[_] _ => f z) (isGradedCoderivation_iff.mp hb)
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] using h

end TensorWords

end TauCeti
