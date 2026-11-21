/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.Algebra.Homology.LinearHomComplex.Composition

/-!
# The dual-tensor comparison of cochain complexes of modules

Let `A` and `B` be cochain complexes of modules over a commutative ring `R`, and let
`A∨ = Hom(A, R[0])` be the `R`-linear Hom complex from `A` to the tensor unit `R[0]`, the dual
complex. Its term of degree `q` consists of the linear forms on `A^(-q)`, and its differential is
`d f = (-1)^(q + 1) f ∘ d_A`, the differential of Mathlib's `CochainComplex.HomComplex`
(`TauCeti.cochainToTensorUnitLinearEquiv_δ`). This file constructs the **dual-tensor comparison**

`TauCeti.linearHomComplexDualTensor R A B : B ⊗ A∨ ⟶ Hom(A, B)`,

which sends `b ⊗ φ`, for `b ∈ Bᵖ` and `φ ∈ (A∨)^q`, to the cochain `a ↦ φ(a) • b` of degree
`p + q`. No sign enters: in the Koszul convention, `φ` already stands next to its argument. It is
the complex-level form of Mathlib's contraction `dualTensorHom`. Reading a functional on an
external kernel `A ⊗ B∨` as an operator from `A` to `B` ends with this map; it must first be
preceded by the identification of `(A ⊗ B∨)∨` with `B∨∨ ⊗ A∨` and the inverse of the bidual map
on `B`, neither of which is in this file.

The comparison is built from structure that already exists rather than by hand:

* Cochains out of the tensor unit are elements: `Hom(R[0], K) ≅ K`, by evaluation at `1`
  (`TauCeti.linearHomComplexFromTensorUnitIso`), with no sign, since `R[0]` has zero
  differential. Its degreewise form is `TauCeti.cochainFromTensorUnitLinearEquiv`, from Mathlib's
  `CochainComplex.HomComplex.Cochain.fromSingleLinearEquiv`. Dually, the terms of `A∨` are the
  linear forms: `TauCeti.cochainToTensorUnitLinearEquiv` identifies `(A∨)^q` with the dual of
  `A^(-q)`, from Mathlib's `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv`.
* The comparison is composition of cochains `Hom(R[0], B) ⊗ Hom(A, R[0]) ⟶ Hom(A, B)`
  (`TauCeti.linearHomComplexComp`) after this identification, so it is a morphism of complexes
  and it is natural in `A` and in `B` (`TauCeti.linearHomComplexDualTensor_naturality_source`,
  `TauCeti.linearHomComplexDualTensor_naturality_target`).

## Main results

* `TauCeti.linearHomComplexDualTensor_ιTensorObj_tmul`,
  `TauCeti.linearHomComplexDualTensor_ιTensorObj_tmul_v` and
  `TauCeti.linearHomComplexDualTensor_ιTensorObj_tmul_v_eq_zero`: the value on `b ⊗ φ`, whose
  only nonzero component is `a ↦ φ(a) • b` on `A^(-q)`.
* `TauCeti.isIso_linearHomComplexDualTensor`: if every term of `A` is a finitely generated
  projective module and only finitely many terms are nonzero, the comparison is an isomorphism
  of complexes for every `B`. In degree `n` it is the sum over `i` of the contractions
  `Bⁱ⁺ⁿ ⊗ (Aⁱ)∨ ⟶ Hom(Aⁱ, Bⁱ⁺ⁿ)`, which are bijective by Mathlib's `dualTensorHomEquiv`, and the
  finiteness of `A` makes the direct sum over `i` agree with the product of the Hom complex.
  `TauCeti.isIso_linearHomComplexDualTensor_of_isStrictlyGE_of_isStrictlyLE` states this for
  bounded complexes. Without finiteness the comparison need not be surjective: the Hom complex is
  a product over `i`, while the tensor product is a direct sum.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on the Hom and tensor
  complexes and their sign conventions.
* Mathlib's `LinearAlgebra.Contraction` (`dualTensorHom`, `dualTensorHomEquiv`) for the
  degreewise comparison, and Joël Riou's `CochainComplex.HomComplex` and its single-complex API
  for the Hom complex.
-/

public section

open CategoryTheory Limits MonoidalCategory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct

namespace TauCeti

universe v

variable (R : Type v) [CommRing R]

/-- Cochains of degree `n` from the tensor unit `R[0]` to `K` are the elements of `Kⁿ`: such a
cochain is a single map `R ⟶ Kⁿ`, determined by its value at `1`. -/
noncomputable def cochainFromTensorUnitLinearEquiv (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) : Cochain (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K n ≃ₗ[R] K.X n :=
  (Cochain.fromSingleLinearEquiv (zero_add n)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R (K.X n)))

variable {R}

/-- A cochain `z` of degree `n` from the tensor unit corresponds to the value at `1` of its
component `R ⟶ Kⁿ` on degree `0`. -/
@[simp]
lemma cochainFromTensorUnitLinearEquiv_apply (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (z : Cochain (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K n) :
    cochainFromTensorUnitLinearEquiv R K n z =
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv ≫
        z.v 0 n (zero_add n)).hom 1 :=
  (rfl)

/-- A cochain from the tensor unit given by a map `f : R ⟶ Kⁿ` corresponds to `f 1`. -/
lemma cochainFromTensorUnitLinearEquiv_fromSingleMk (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) (f : 𝟙_ (ModuleCat.{v} R) ⟶ K.X n) :
    cochainFromTensorUnitLinearEquiv R K n (Cochain.fromSingleMk f (zero_add n)) = f.hom 1 :=
  congrArg (fun g : 𝟙_ (ModuleCat.{v} R) ⟶ K.X n => g.hom 1)
    (Cochain.fromSingleEquiv_fromSingleMk f (zero_add n))

/-- The cochain from the tensor unit corresponding to `x ∈ Kⁿ` is the map `r ↦ r • x`. -/
@[simp]
lemma cochainFromTensorUnitLinearEquiv_symm_apply (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) (x : K.X n) :
    (cochainFromTensorUnitLinearEquiv R K n).symm x =
      Cochain.fromSingleMk (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) x))
        (zero_add n) :=
  (cochainFromTensorUnitLinearEquiv R K n).symm_apply_eq.2 <| by
    rw [cochainFromTensorUnitLinearEquiv_fromSingleMk]
    exact (one_smul R x).symm

/-- Evaluation at `1` intertwines the differential of the Hom complex out of the tensor unit with
the differential of `K`. -/
lemma cochainFromTensorUnitLinearEquiv_δ (K : CochainComplex (ModuleCat.{v} R) ℤ) (n m : ℤ)
    (z : Cochain (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K n) :
    cochainFromTensorUnitLinearEquiv R K m (δ n m z) =
      (K.d n m).hom (cochainFromTensorUnitLinearEquiv R K n z) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  rw [Cochain.δ_fromSingleMk f (zero_add n) m m (zero_add m),
    cochainFromTensorUnitLinearEquiv_fromSingleMk, cochainFromTensorUnitLinearEquiv_fromSingleMk,
    ModuleCat.hom_comp, LinearMap.comp_apply]

variable (R) in
/-- **Cochains out of the tensor unit.** The `R`-linear Hom complex from the tensor unit `R[0]` to
`K` is isomorphic to `K`, by evaluating a cochain at `1`. -/
noncomputable def linearHomComplexFromTensorUnitIso (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplex R (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainFromTensorUnitLinearEquiv R K n).toModuleIso) fun n m _ => by
      ext z
      exact (cochainFromTensorUnitLinearEquiv_δ K n m z).symm

/-- The isomorphism `linearHomComplexFromTensorUnitIso` evaluates a cochain of degree `n` at
`1`. -/
@[simp]
lemma linearHomComplexFromTensorUnitIso_hom_f_apply (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (z : ModuleCat.of R (Cochain (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K n)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexFromTensorUnitIso R K).hom.f n) z) =
      cochainFromTensorUnitLinearEquiv R K n z :=
  (rfl)

/-- The inverse of `linearHomComplexFromTensorUnitIso` sends `x ∈ Kⁿ` to the cochain
`r ↦ r • x`. -/
@[simp]
lemma linearHomComplexFromTensorUnitIso_inv_f_apply (K : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (x : K.X n) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexFromTensorUnitIso R K).inv.f n) x) =
      ((cochainFromTensorUnitLinearEquiv R K n).symm x :
        ModuleCat.of R (Cochain (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K n)) :=
  (rfl)

/-- Evaluation at `1` is natural in the target complex. -/
@[reassoc]
lemma linearHomComplexFromTensorUnitIso_hom_naturality {K₁ K₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (ψ : K₁ ⟶ K₂) :
    linearHomComplexPostcomp R _ ψ ≫ (linearHomComplexFromTensorUnitIso R K₂).hom =
      (linearHomComplexFromTensorUnitIso R K₁).hom ≫ ψ := by
  ext n (z : ModuleCat.of R (Cochain (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) K₁ n))
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  simp [← Cochain.fromSingleMk_postcomp]

/-- The inverse of evaluation at `1` is natural in the target complex. -/
@[reassoc]
lemma linearHomComplexFromTensorUnitIso_inv_naturality {K₁ K₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (ψ : K₁ ⟶ K₂) :
    ψ ≫ (linearHomComplexFromTensorUnitIso R K₂).inv =
      (linearHomComplexFromTensorUnitIso R K₁).inv ≫ linearHomComplexPostcomp R _ ψ :=
  ((Iso.inv_comp_eq _).2 (by
    rw [← Category.assoc, ← linearHomComplexFromTensorUnitIso_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id])).symm

variable (R) in
/-- Cochains of degree `q` from `A` to the tensor unit `R[0]` are the linear forms on `Aⁱ`, for
`i + q = 0`: such a cochain is a single map `Aⁱ ⟶ R`. These are the terms of the dual complex
`A∨ = Hom(A, R[0])`. -/
noncomputable def cochainToTensorUnitLinearEquiv (A : CochainComplex (ModuleCat.{v} R) ℤ)
    {i q : ℤ} (hi : i + q = 0) :
    Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q ≃ₗ[R] Module.Dual R (A.X i) :=
  (Cochain.toSingleLinearEquiv hi).trans ModuleCat.homLinearEquiv

/-- A cochain `φ` of degree `q` to the tensor unit corresponds to its component `Aⁱ ⟶ R`, for
`i + q = 0`. -/
@[simp]
lemma cochainToTensorUnitLinearEquiv_apply (A : CochainComplex (ModuleCat.{v} R) ℤ) {i q : ℤ}
    (hi : i + q = 0) (φ : Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q) :
    cochainToTensorUnitLinearEquiv R A hi φ = (Cochain.toSingleEquiv hi φ).hom :=
  (rfl)

/-- The cochain to the tensor unit corresponding to a linear form `f` on `Aⁱ` is the single cochain
given by `f`. -/
@[simp]
lemma cochainToTensorUnitLinearEquiv_symm_apply (A : CochainComplex (ModuleCat.{v} R) ℤ)
    {i q : ℤ} (hi : i + q = 0) (f : Module.Dual R (A.X i)) :
    (cochainToTensorUnitLinearEquiv R A hi).symm f = Cochain.toSingleMk (ModuleCat.ofHom f) hi :=
  (rfl)

/-- The differential of the dual complex: for `i + q = 0` and `i' + q' = 0`, the linear form of
`δ φ` on `A^i'` is `(-1)^q'` times the linear form of `φ` composed with `d_A : A^i' ⟶ Aⁱ`. -/
lemma cochainToTensorUnitLinearEquiv_δ (A : CochainComplex (ModuleCat.{v} R) ℤ)
    {i i' q q' : ℤ} (hi : i + q = 0) (hi' : i' + q' = 0)
    (φ : Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q) :
    cochainToTensorUnitLinearEquiv R A hi' (δ q q' φ) =
      q'.negOnePow • cochainToTensorUnitLinearEquiv R A hi φ ∘ₗ (A.d i' i).hom := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective φ i hi
  rw [Cochain.δ_toSingleMk f hi q' i' hi']
  simp

variable (R) in
/-- The **dual-tensor comparison** `B ⊗ Hom(A, R[0]) ⟶ Hom(A, B)` of cochain complexes of
`R`-modules. It sends `b ⊗ φ`, for `b ∈ Bᵖ` and a cochain `φ` of degree `q` from `A` to `R[0]`, to
the cochain `a ↦ φ(a) • b` of degree `p + q`, with no sign: it is composition of cochains,
`Hom(R[0], B) ⊗ Hom(A, R[0]) ⟶ Hom(A, B)`, after identifying `B` with `Hom(R[0], B)`. -/
noncomputable def linearHomComplexDualTensor (A B : CochainComplex (ModuleCat.{v} R) ℤ) :
    B ⊗ linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) ⟶
      linearHomComplex R A B :=
  (linearHomComplexFromTensorUnitIso R B).inv ▷ _ ≫ linearHomComplexComp R A _ B

/-- The dual-tensor comparison is composition after identifying `B` with `Hom(R[0], B)`. -/
lemma linearHomComplexDualTensor_def (A B : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplexDualTensor R A B =
      (linearHomComplexFromTensorUnitIso R B).inv ▷ _ ≫ linearHomComplexComp R A _ B :=
  (rfl)

/-- On the summand `Bᵖ ⊗ Hom(A, R[0])^q`, the dual-tensor comparison sends `b ⊗ φ` to the
composite of `φ` with the cochain `r ↦ r • b`. -/
lemma linearHomComplexDualTensor_ιTensorObj_tmul (A B : CochainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (b : B.X p)
    (φ : ModuleCat.of R (Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom
        (HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h ≫
          (linearHomComplexDualTensor R A B).f n) (b ⊗ₜ φ)) =
      (φ.comp ((cochainFromTensorUnitLinearEquiv R B p).symm b) (by omega) :
        ModuleCat.of R (Cochain A B n)) := by
  rw [linearHomComplexDualTensor_def, HomologicalComplex.comp_f,
    HomologicalComplex.ι_whiskerRight_assoc]
  have hι := ι_linearHomComplexComp R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) B p q n h
  rw [HomologicalComplex.ιTensorObj, hι, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, linearHomComplexFromTensorUnitIso_inv_f_apply]
  exact cochainCompTensor_tmul R A _ B p q n h _ φ

/-- The dual-tensor comparison of `b ⊗ φ`, for `b ∈ Bᵖ` and `φ` of degree `q`, has as component
on `Aⁱ` with `i + q = 0` the map `a ↦ φ(a) • b`. -/
@[simp]
lemma linearHomComplexDualTensor_ιTensorObj_tmul_v (A B : CochainComplex (ModuleCat.{v} R) ℤ)
    {p q n : ℤ} (h : p + q = n) (b : B.X p)
    (φ : ModuleCat.of R (Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q)) {i : ℤ}
    (hi : i + q = 0) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexDualTensor R A B).f n)
        ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom (b ⊗ₜ φ)) :
        ModuleCat.of R (Cochain A B n)).v i p (by omega) =
      Cochain.toSingleEquiv hi φ ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R (B.X p) b) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    linearHomComplexDualTensor_ιTensorObj_tmul, Cochain.comp_v _ _ _ i 0 p hi (zero_add p),
    cochainFromTensorUnitLinearEquiv_symm_apply, Cochain.fromSingleMk_v,
    Cochain.toSingleEquiv_apply, Category.assoc]
  -- The tensor unit of `ModuleCat R` is `ModuleCat.of R R`, but the two single complexes are
  -- presented differently on the two sides.
  rfl

/-- The dual-tensor comparison of `b ⊗ φ`, for `φ` of degree `q`, vanishes on `Aⁱ` unless
`i + q = 0`. -/
@[simp]
lemma linearHomComplexDualTensor_ιTensorObj_tmul_v_eq_zero
    (A B : CochainComplex (ModuleCat.{v} R) ℤ) {p q n : ℤ} (h : p + q = n) (b : B.X p)
    (φ : ModuleCat.of R (Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q)) {i j : ℤ}
    (hij : i + n = j) (hi : i + q ≠ 0) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexDualTensor R A B).f n)
        ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom (b ⊗ₜ φ)) :
        ModuleCat.of R (Cochain A B n)).v i j hij = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    linearHomComplexDualTensor_ιTensorObj_tmul, Cochain.comp_v _ _ _ i (i + q) j rfl (by omega),
    cochainFromTensorUnitLinearEquiv_symm_apply,
    Cochain.fromSingleMk_v_eq_zero _ _ _ _ _ hi, Limits.comp_zero]

/-- The dual-tensor comparison is natural in the source complex `A`, contravariantly on both
sides. -/
@[reassoc]
lemma linearHomComplexDualTensor_naturality_source {A₁ A₂ : CochainComplex (ModuleCat.{v} R) ℤ}
    (φ : A₁ ⟶ A₂) (B : CochainComplex (ModuleCat.{v} R) ℤ) :
    B ◁ linearHomComplexPrecomp R φ _ ≫ linearHomComplexDualTensor R A₁ B =
      linearHomComplexDualTensor R A₂ B ≫ linearHomComplexPrecomp R φ B := by
  rw [linearHomComplexDualTensor_def, linearHomComplexDualTensor_def, whisker_exchange_assoc,
    linearHomComplexComp_naturality_source, Category.assoc]

/-- The dual-tensor comparison is natural in the target complex `B`. -/
@[reassoc]
lemma linearHomComplexDualTensor_naturality_target (A : CochainComplex (ModuleCat.{v} R) ℤ)
    {B₁ B₂ : CochainComplex (ModuleCat.{v} R) ℤ} (ψ : B₁ ⟶ B₂) :
    ψ ▷ _ ≫ linearHomComplexDualTensor R A B₂ =
      linearHomComplexDualTensor R A B₁ ≫ linearHomComplexPostcomp R A ψ := by
  rw [linearHomComplexDualTensor_def, linearHomComplexDualTensor_def, ← comp_whiskerRight_assoc,
    linearHomComplexFromTensorUnitIso_inv_naturality, comp_whiskerRight_assoc,
    linearHomComplexComp_naturality_target, Category.assoc]

section Isomorphism

variable (A B : CochainComplex (ModuleCat.{v} R) ℤ)

/-- On a summand `Bᵖ ⊗ Hom(A, R[0])^q`, the component on `Aⁱ` with `i + q = 0` of the dual-tensor
comparison is Mathlib's contraction `dualTensorHom`, after identifying `Hom(A, R[0])^q` with the
dual of `Aⁱ`. -/
private lemma vLinearMap_linearHomComplexDualTensor {p q n : ℤ} (h : p + q = n) {i : ℤ}
    (hi : i + q = 0) (t : ↑(B.X p) ⊗[R] ↑((linearHomComplex R A (𝟙_ _)).X q)) :
    Cochain.vLinearMap A B n i p (by omega) (((linearHomComplexDualTensor R A B).f n).hom
        ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t)) =
      dualTensorHom R (A.X i) (B.X p) (TensorProduct.comm R _ _ (TensorProduct.map LinearMap.id
        (cochainToTensorUnitLinearEquiv R A hi).toLinearMap t)) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b φ =>
    rw [Cochain.vLinearMap_apply, linearHomComplexDualTensor_ιTensorObj_tmul_v A B h b φ hi]
    ext a
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe,
      TensorProduct.comm_tmul, dualTensorHom_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, cochainToTensorUnitLinearEquiv_apply]
    exact LinearMap.toSpanSingleton_apply ..

/-- On a summand `Bᵖ ⊗ Hom(A, R[0])^q`, the dual-tensor comparison vanishes on `Aⁱ` unless
`i + q = 0`. -/
private lemma vLinearMap_linearHomComplexDualTensor_eq_zero {p q n : ℤ} (h : p + q = n)
    {i j : ℤ} (hij : i + n = j) (hi : i + q ≠ 0)
    (t : ↑(B.X p) ⊗[R] ↑((linearHomComplex R A (𝟙_ _)).X q)) :
    Cochain.vLinearMap A B n i j hij (((linearHomComplexDualTensor R A B).f n).hom
        ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t)) = 0 := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul b φ =>
    rw [Cochain.vLinearMap_apply,
      linearHomComplexDualTensor_ιTensorObj_tmul_v_eq_zero A B h b φ hij hi, ModuleCat.hom_zero]

variable [∀ i, Module.Finite R (A.X i)] [∀ i, Module.Projective R (A.X i)]

/-- Under finite projectivity of `Aⁱ`, the contraction of `Bᵖ ⊗ Hom(A, R[0])^q` onto
`Aⁱ →ₗ Bᵖ`, for `i + q = 0`, is a linear equivalence. -/
private noncomputable def dualTensorSummandEquiv {p q i : ℤ} (hi : i + q = 0) :
    (↑(B.X p) ⊗[R] ↑((linearHomComplex R A (𝟙_ _)).X q)) ≃ₗ[R] (A.X i →ₗ[R] B.X p) :=
  (TensorProduct.congr (LinearEquiv.refl R _) (cochainToTensorUnitLinearEquiv R A hi)).trans
    ((TensorProduct.comm R _ _).trans (dualTensorHomEquiv R (A.X i) (B.X p)))

private lemma vLinearMap_linearHomComplexDualTensor_eq {p q n : ℤ} (h : p + q = n) {i : ℤ}
    (hi : i + q = 0) (t : ↑(B.X p) ⊗[R] ↑((linearHomComplex R A (𝟙_ _)).X q)) :
    Cochain.vLinearMap A B n i p (by omega) (((linearHomComplexDualTensor R A B).f n).hom
        ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t)) =
      dualTensorSummandEquiv A B hi t := by
  simp [dualTensorSummandEquiv, vLinearMap_linearHomComplexDualTensor A B h hi t,
    ← toLinearMap_dualTensorHomEquiv, TensorProduct.congr]

/-- The inverse of the dual-tensor comparison in degree `n`, when `Aⁱ` vanishes for `i ∉ S`: the
component of a cochain on `Aⁱ` is sent back to the summand `Bⁱ⁺ⁿ ⊗ Hom(A, R[0])⁻ⁱ`. -/
private noncomputable def dualTensorInv (S : Finset ℤ) (n : ℤ) :
    Cochain A B n →ₗ[R] (B ⊗ linearHomComplex R A (𝟙_ _)).X n :=
  ∑ i ∈ S, (HomologicalComplex.ιTensorObj B (linearHomComplex R A _) (i + n) (-i) n
      (by omega)).hom ∘ₗ (dualTensorSummandEquiv A B (add_neg_cancel i)).symm.toLinearMap ∘ₗ
    Cochain.vLinearMap A B n i (i + n) rfl

/-- The inverse undoes the dual-tensor comparison on every summand. -/
private lemma dualTensorInv_linearHomComplexDualTensor (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (A.X i)) {p q n : ℤ} (h : p + q = n)
    (t : ↑(B.X p) ⊗[R] ↑((linearHomComplex R A (𝟙_ _)).X q)) :
    dualTensorInv A B S n (((linearHomComplexDualTensor R A B).f n).hom
        ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t)) =
      (HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t := by
  have key (i : ℤ) (hi : i + q = 0) :
      (HomologicalComplex.ιTensorObj B (linearHomComplex R A _) (i + n) (-i) n (by omega)).hom
          ((dualTensorSummandEquiv A B (add_neg_cancel i)).symm
            (Cochain.vLinearMap A B n i (i + n) rfl (((linearHomComplexDualTensor R A B).f n).hom
              ((HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t)))) =
        (HomologicalComplex.ιTensorObj B (linearHomComplex R A _) p q n h).hom t := by
    obtain rfl : q = -i := by omega
    obtain rfl : p = i + n := by omega
    rw [vLinearMap_linearHomComplexDualTensor_eq A B h hi, LinearEquiv.symm_apply_apply]
  rw [dualTensorInv, LinearMap.sum_apply, Finset.sum_eq_single (-q)]
  · exact key (-q) (neg_add_cancel q)
  · intro i _ hiq
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      vLinearMap_linearHomComplexDualTensor_eq_zero A B h rfl (by omega), map_zero,
      map_zero]
  · intro hq
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      Cochain.vLinearMap_eq_zero_of_isZero rfl (hS _ hq), map_zero, map_zero]

/-- The dual-tensor comparison undoes the inverse on every cochain. -/
private lemma linearHomComplexDualTensor_dualTensorInv (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (A.X i)) (n : ℤ) (z : Cochain A B n) :
    ((linearHomComplexDualTensor R A B).f n).hom (dualTensorInv A B S n z) = z := by
  refine Cochain.ext _ _ fun i j hij => ModuleCat.hom_ext ?_
  rw [← Cochain.vLinearMap_apply, ← Cochain.vLinearMap_apply]
  obtain rfl : j = i + n := hij.symm
  rw [dualTensorInv, LinearMap.sum_apply, map_sum, map_sum, Finset.sum_eq_single i]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      vLinearMap_linearHomComplexDualTensor_eq A B _ (add_neg_cancel i),
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  · intro k _ hki
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      vLinearMap_linearHomComplexDualTensor_eq_zero A B _ rfl (by omega)]
  · intro hi
    exact Cochain.vLinearMap_eq_zero_of_isZero rfl (hS _ hi) _

end Isomorphism

/-- **The dual-tensor comparison is an isomorphism for finite complexes of finite projective
modules.** If every term of `A` is a finitely generated projective `R`-module and only finitely
many terms of `A` are nonzero, then `B ⊗ Hom(A, R[0]) ⟶ Hom(A, B)` is an isomorphism of
complexes, for every complex `B`. -/
theorem isIso_linearHomComplexDualTensor (A B : CochainComplex (ModuleCat.{v} R) ℤ)
    [∀ i, Module.Finite R (A.X i)] [∀ i, Module.Projective R (A.X i)] (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (A.X i)) : IsIso (linearHomComplexDualTensor R A B) := by
  have (n : ℤ) : IsIso ((linearHomComplexDualTensor R A B).f n) := by
    refine ⟨ModuleCat.ofHom (dualTensorInv A B S n), ?_, ?_⟩
    · refine HomologicalComplex.mapBifunctor.hom_ext fun p q h =>
        ModuleCat.MonoidalCategory.tensor_ext fun b φ => ?_
      exact dualTensorInv_linearHomComplexDualTensor A B S hS h (b ⊗ₜ φ)
    · exact ModuleCat.hom_ext (LinearMap.ext (linearHomComplexDualTensor_dualTensorInv A B S hS n))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The dual-tensor comparison is an isomorphism when `A` is a bounded complex of finitely
generated projective `R`-modules. -/
theorem isIso_linearHomComplexDualTensor_of_isStrictlyGE_of_isStrictlyLE
    (A B : CochainComplex (ModuleCat.{v} R) ℤ) [∀ i, Module.Finite R (A.X i)]
    [∀ i, Module.Projective R (A.X i)] (a b : ℤ) [CochainComplex.IsStrictlyGE A a]
    [CochainComplex.IsStrictlyLE A b] :
    IsIso (linearHomComplexDualTensor R A B) :=
  isIso_linearHomComplexDualTensor A B (Finset.Icc a b) fun i hi => by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
    exact hi.elim (fun h => CochainComplex.isZero_of_isStrictlyGE A a i h)
      (fun h => CochainComplex.isZero_of_isStrictlyLE A b i h)

end TauCeti
