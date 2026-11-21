/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Embeddings
public import TauCeti.RepresentationTheory.GaloisLattice.Basic

/-!
# The character lattice of the Serre torus of a CM field

Let `L` be a CM field, `ℚ^al` the algebraic closure of `ℚ`, and `E = Hom_ℚ(L, ℚ^al)` its set of
embeddings, on which `Gal(ℚ^al/ℚ)` acts by postcomposition and complex conjugation `c` of `L` acts
by precomposition, `φ ↦ φ ∘ c`. The **Serre torus** `S^L` is the `ℚ`-torus whose character lattice
is the Galois sublattice of the permutation lattice `ℤ[E]`
```
X^*(S^L) = {χ ∈ ℤ[E] | (σ - 1)(c + 1) χ = 0 for every σ ∈ Gal(ℚ^al/ℚ)}.
```
Since `Gal(ℚ^al/ℚ)` acts transitively on `E`, the condition says that the sum `χ(φ) + χ(φ ∘ c)` of
the coefficients on each conjugate pair of embeddings is a constant, the **weight** of `χ`.

This file constructs that lattice as an integral Galois lattice over `ℚ`, together with the
functional `χ ↦ χ(ι₀)` attached to an embedding `ι₀ : L → ℚ^al`. This functional is the universal
cocharacter `μ^L` of `S^L`: it is fixed by the stabilizer of `ι₀`, and with the lift `τ` of
complex conjugation it satisfies `(σ - 1)(τ + 1) μ^L = 0`. Conversely, a functional `μ` on any
integral `Gal(ℚ^al/ℚ)`-representation `M` with these two properties is `μ^L ∘ f` for a unique
equivariant `f : M → X^*(S^L)`. Through the anti-equivalence between tori and Galois lattices this
is the universal property of `(S^L, μ^L)` among `ℚ`-tori with a cocharacter defined over `ι₀(L)`
satisfying the Serre relation.

## Main definitions

* `TauCeti.SerreTorus.conjEmbedding L`: the involution `φ ↦ φ ∘ c` of `E`.
* `TauCeti.SerreTorus.conj L`: the induced involution of `ℤ[E]`.
* `TauCeti.SerreTorus.characterSubrep L`: the sublattice `X^*(S^L)` of `ℤ[E]`.
* `TauCeti.SerreTorus.characterLattice L`: `X^*(S^L)` as an object of `GaloisLatticeCat ℚ`.
* `TauCeti.SerreTorus.weight L`: the weight `X^*(S^L) → ℤ`.
* `TauCeti.SerreTorus.universalCocharacter L ι₀`: the functional `χ ↦ χ(ι₀)` on `X^*(S^L)`.
* `TauCeti.SerreTorus.lift ρ ι₀ τ μ`: the equivariant map from a representation `ρ` to
  `X^*(S^L)` attached to a functional `μ` satisfying the Serre relation.

## Main results

* `TauCeti.SerreTorus.mem_characterSubrep_iff`: `χ ∈ X^*(S^L)` exactly when the sums
  `χ(φ) + χ(φ ∘ c)` are all equal.
* `TauCeti.SerreTorus.mem_characterSubrep_iff_forall_smul`: equivalently, `(c + 1) χ` is fixed by
  every `σ ∈ Gal(ℚ^al/ℚ)`, which is the defining relation of Milne and Shih.
* `TauCeti.SerreTorus.characterSubrep_eq_top_of_finrank_eq_two`: for an imaginary quadratic field
  `X^*(S^L)` is the whole permutation lattice `ℤ[E]`, the character lattice of `Res_{L/ℚ} 𝔾ₘ`.
* `TauCeti.SerreTorus.universalCocharacter_add_dual_eq_weight`: `μ^L + τ μ^L` is the weight.
* `TauCeti.SerreTorus.universalCocharacter_comp_lift` and `TauCeti.SerreTorus.eq_lift`: the
  universal property of `μ^L`; `TauCeti.SerreTorus.dual_universalCocharacter_comp_of_smul_eq` and
  `TauCeti.SerreTorus.dual_universalCocharacter_comp_add_dual` show that its hypotheses are
  necessary.

## References

* J. S. Milne and K.-y. Shih, *Langlands's construction of the Taniyama group*, in *Hodge cycles,
  motives, and Shimura varieties*, Lecture Notes in Math. 900 (1982), §1, equations (1.1)–(1.3),
  pp. 230–232.
* J. S. Milne, *Complex multiplication* (2006), Chapter I, §5, *The Serre group*.
-/

public section

open NumberField MonoidAlgebra

namespace TauCeti.SerreTorus

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

/-- The involution `φ ↦ φ ∘ c` of the embeddings of a CM field `L` into `ℚ^al`, where `c` is the
complex conjugation of `L`. -/
noncomputable def conjEmbedding (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) : L →ₐ[ℚ] AlgebraicClosure ℚ :=
  φ.comp ((IsCMField.complexConj L).restrictScalars ℚ).toAlgHom

variable {L}

@[simp]
theorem conjEmbedding_apply (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) (x : L) :
    conjEmbedding L φ x = φ (IsCMField.complexConj L x) :=
  (rfl)

/-- Conjugating an embedding twice gives it back. -/
@[simp]
theorem conjEmbedding_conjEmbedding (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    conjEmbedding L (conjEmbedding L φ) = φ := by
  ext x
  simp

theorem conjEmbedding_involutive : Function.Involutive (conjEmbedding L) :=
  conjEmbedding_conjEmbedding

/-- Conjugation of embeddings commutes with the Galois action. -/
@[simp]
theorem conjEmbedding_smul (σ : Field.absoluteGaloisGroup ℚ) (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    conjEmbedding L (σ • φ) = σ • conjEmbedding L φ :=
  (Field.absoluteGaloisGroup.smul_algHom_comp σ φ _).symm

/-- No embedding of a CM field is fixed by complex conjugation. -/
theorem conjEmbedding_ne (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) : conjEmbedding L φ ≠ φ := by
  intro h
  apply IsCMField.complexConj_ne_one L
  ext x
  exact φ.injective (by simpa using DFunLike.congr_fun h x)

variable (L)

/-- The involution of `ℤ[E]` induced by complex conjugation of the embeddings. -/
noncomputable def conj : ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ] →ₗ[ℤ] ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ] :=
  (coeffLinearEquiv ℤ).symm.toLinearMap ∘ₗ Finsupp.lmapDomain ℤ ℤ (conjEmbedding L) ∘ₗ
    (coeffLinearEquiv ℤ).toLinearMap

variable {L}

@[simp]
theorem coeff_conj (χ : ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ]) (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    (conj L χ).coeff φ = χ.coeff (conjEmbedding L φ) := by
  simp only [conj, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    coeffLinearEquiv_symm_apply, coeff_ofCoeff, Finsupp.lmapDomain_apply, coeffLinearEquiv_apply]
  rw [← conjEmbedding_conjEmbedding φ,
    Finsupp.mapDomain_apply_of_injective conjEmbedding_involutive.injective,
    conjEmbedding_conjEmbedding]

variable (L)

/-- The character lattice of the Serre torus `S^L`, as a subrepresentation of the permutation
lattice `ℤ[E]`: the characters `χ` whose sums `χ(φ) + χ(φ ∘ c)` over conjugate pairs of
embeddings are all equal. See `mem_characterSubrep_iff_forall_smul` for the equivalent relation
`(σ - 1)(c + 1) χ = 0` of Milne and Shih. -/
noncomputable def characterSubrep :
    Subrepresentation (Representation.ofMulAction ℤ (Field.absoluteGaloisGroup ℚ)
      (L →ₐ[ℚ] AlgebraicClosure ℚ)) where
  toSubmodule :=
    { carrier := {χ | ∃ w : ℤ, ∀ φ, χ.coeff φ + χ.coeff (conjEmbedding L φ) = w}
      add_mem' := by
        rintro χ ψ ⟨v, hv⟩ ⟨w, hw⟩
        exact ⟨v + w, fun φ ↦ by simp only [coeff_add, Finsupp.add_apply, ← hv φ, ← hw φ]; ring⟩
      zero_mem' := ⟨0, fun φ ↦ by simp⟩
      smul_mem' := by
        rintro n χ ⟨w, hw⟩
        exact ⟨n * w, fun φ ↦ by simp [← hw φ, mul_add]⟩ }
  apply_mem_toSubmodule := by
    rintro σ χ ⟨w, hw⟩
    exact ⟨w, fun φ ↦ by
      simp only [Representation.coeff_ofMulAction, ← conjEmbedding_smul, hw]⟩

variable {L}

theorem mem_characterSubrep_iff {χ : ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ]} :
    χ ∈ characterSubrep L ↔ ∃ w : ℤ, ∀ φ, χ.coeff φ + χ.coeff (conjEmbedding L φ) = w :=
  Iff.rfl

/-- **The Serre relation.** A character lies in `X^*(S^L)` exactly when `(c + 1) χ` is fixed by
every element of `Gal(ℚ^al/ℚ)`, that is, when `(σ - 1)(c + 1) χ = 0` for every `σ`. -/
theorem mem_characterSubrep_iff_forall_smul {χ : ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ]} :
    χ ∈ characterSubrep L ↔
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        Representation.ofMulAction ℤ _ _ σ (χ + conj L χ) = χ + conj L χ := by
  rw [mem_characterSubrep_iff]
  constructor
  · rintro ⟨w, hw⟩ σ
    ext φ
    simp only [Representation.coeff_ofMulAction, coeff_add, coeff_conj, Finsupp.add_apply,
      hw]
  · intro h
    obtain ⟨φ₀⟩ := (inferInstance : Nonempty (L →ₐ[ℚ] AlgebraicClosure ℚ))
    refine ⟨χ.coeff φ₀ + χ.coeff (conjEmbedding L φ₀), fun φ ↦ ?_⟩
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Field.absoluteGaloisGroup ℚ) φ₀ φ
    have := congr_arg (fun ψ ↦ ψ.coeff (σ • φ₀)) (h σ)
    simpa [Representation.coeff_ofMulAction] using this.symm

/-- `Gal(ℚ^al/ℚ)` acts on the coefficients of a character of `S^L` through its action on the
embeddings. -/
@[simp]
theorem coeff_toRepresentation_apply (σ : Field.absoluteGaloisGroup ℚ)
    (χ : (characterSubrep L).toSubmodule) (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    ((characterSubrep L).toRepresentation σ χ).val.coeff φ = χ.val.coeff (σ⁻¹ • φ) :=
  Representation.coeff_ofMulAction σ χ.val φ

omit [IsCMField L] in
/-- An element of `Gal(ℚ^al/ℚ)` fixing every embedding of `L` fixes every vector of `ℤ[E]`. -/
private theorem ofMulAction_eq_self_of_forall_smul_eq {σ : Field.absoluteGaloisGroup ℚ}
    (hσ : ∀ φ : L →ₐ[ℚ] AlgebraicClosure ℚ, σ • φ = φ) (χ : ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ]) :
    Representation.ofMulAction ℤ _ _ σ χ = χ := by
  ext φ
  rw [Representation.coeff_ofMulAction, ← hσ φ, inv_smul_smul, hσ φ]

variable (L)

-- The body is exposed so that the representation of `characterLattice L` is
-- `(characterSubrep L).toRepresentation` by definition: equivariant maps into it, as in
-- `TauCeti.SerreTorus.homEquiv`, are stated against that representation.
/-- **The character lattice of the Serre torus** `S^L`, as an integral Galois lattice over `ℚ`. -/
@[expose] noncomputable def characterLattice : GaloisLatticeCat ℚ where
  obj := Rep.of (characterSubrep L).toRepresentation
  property := by
    refine (galoisLatticeProperty_iff _ _).2
      ⟨⟨inferInstanceAs (Module.Free ℤ (characterSubrep L).toSubmodule),
        inferInstanceAs (Module.Finite ℤ (characterSubrep L).toSubmodule)⟩, fun χ ↦ ?_⟩
    -- The vectors fixed by every embedding stabilizer form an open subgroup.
    let H : Subgroup (Field.absoluteGaloisGroup ℚ) :=
      { carrier := {σ | (characterSubrep L).toRepresentation σ χ = χ}
        one_mem' := by simp
        mul_mem' := fun {σ τ} hσ hτ ↦ by
          rw [Set.mem_ofPred_eq] at hσ hτ ⊢
          rw [map_mul, mul_apply_eq_comp, hτ, hσ]
        inv_mem' := fun {σ} hσ ↦ by
          rw [Set.mem_ofPred_eq] at hσ ⊢
          conv_lhs => rw [← hσ]
          exact Representation.inv_self_apply _ σ χ }
    have hle : ⨅ φ : L →ₐ[ℚ] AlgebraicClosure ℚ, MulAction.stabilizer _ φ ≤ H := fun σ hσ ↦ by
      rw [Subgroup.mem_iInf] at hσ
      exact Subtype.ext (ofMulAction_eq_self_of_forall_smul_eq hσ χ.val)
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun φ ↦ φ.isOpen_stabilizer_absoluteGaloisGroup

/-- The underlying module of `characterLattice L` is `characterSubrep L`. -/
theorem characterLattice_obj :
    (characterLattice L).obj = Rep.of (characterSubrep L).toRepresentation :=
  (rfl)

/-- **The weight** of a character of `S^L`: the common value of the sums `χ(φ) + χ(φ ∘ c)`. -/
noncomputable def weight : (characterSubrep L).toSubmodule →ₗ[ℤ] ℤ :=
  let φ₀ := Classical.arbitrary (L →ₐ[ℚ] AlgebraicClosure ℚ)
  (Finsupp.lapply φ₀ + Finsupp.lapply (conjEmbedding L φ₀)) ∘ₗ
    (coeffLinearEquiv ℤ).toLinearMap ∘ₗ (characterSubrep L).toSubmodule.subtype

variable {L}

/-- The sum of the coefficients of a character of `S^L` on each conjugate pair of embeddings is
its weight. -/
theorem coeff_add_coeff_conjEmbedding (χ : (characterSubrep L).toSubmodule)
    (φ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    χ.val.coeff φ + χ.val.coeff (conjEmbedding L φ) = weight L χ := by
  obtain ⟨w, hw⟩ := χ.property
  simp [weight, hw]

/-- The weight is invariant under `Gal(ℚ^al/ℚ)`. -/
@[simp]
theorem weight_apply_toRepresentation (σ : Field.absoluteGaloisGroup ℚ)
    (χ : (characterSubrep L).toSubmodule) :
    weight L ((characterSubrep L).toRepresentation σ χ) = weight L χ := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (L →ₐ[ℚ] AlgebraicClosure ℚ))
  rw [← coeff_add_coeff_conjEmbedding _ φ, ← coeff_add_coeff_conjEmbedding _ (σ⁻¹ • φ)]
  simp

/-- **`S^L` of an imaginary quadratic field.** If `[L : ℚ] = 2`, every character satisfies the
Serre relation, so `X^*(S^L)` is the whole permutation lattice `ℤ[E]`, the character lattice of
`Res_{L/ℚ} 𝔾ₘ`. -/
theorem characterSubrep_eq_top_of_finrank_eq_two (h : Module.finrank ℚ L = 2) :
    characterSubrep L = ⊤ := by
  classical
  obtain ⟨φ₀⟩ := (inferInstance : Nonempty (L →ₐ[ℚ] AlgebraicClosure ℚ))
  have hcard : Fintype.card (L →ₐ[ℚ] AlgebraicClosure ℚ) = 2 := by
    rw [AlgHom.card, h]
  -- The two embeddings are `φ₀` and its conjugate.
  have hpair : ∀ φ, φ = φ₀ ∨ φ = conjEmbedding L φ₀ := by
    intro φ
    by_contra! hne
    have : ({φ₀, conjEmbedding L φ₀, φ} : Finset _).card ≤ 2 :=
      hcard ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using
        ⟨(conjEmbedding_ne φ₀).symm, hne.1.symm⟩),
      Finset.card_pair (Ne.symm hne.2)] at this
    omega
  refine eq_top_iff.2 fun χ _ ↦ ⟨χ.coeff φ₀ + χ.coeff (conjEmbedding L φ₀), fun φ ↦ ?_⟩
  rcases hpair φ with rfl | rfl
  · rfl
  · rw [conjEmbedding_conjEmbedding, add_comm]

variable (L) in
/-- **The universal cocharacter** `μ^L` of `S^L` attached to an embedding `ι₀ : L → ℚ^al`, as the
functional `χ ↦ χ(ι₀)` on the character lattice. -/
noncomputable def universalCocharacter (ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.Dual ℤ (characterSubrep L).toSubmodule :=
  Finsupp.lapply ι₀ ∘ₗ (coeffLinearEquiv ℤ).toLinearMap ∘ₗ
    (characterSubrep L).toSubmodule.subtype

@[simp]
theorem universalCocharacter_apply (ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ)
    (χ : (characterSubrep L).toSubmodule) :
    universalCocharacter L ι₀ χ = χ.val.coeff ι₀ :=
  (rfl)

/-- The universal cocharacter is defined over `ι₀(L)`: it is fixed by the stabilizer of `ι₀`. -/
theorem dual_universalCocharacter_of_smul_eq {ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ}
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : σ • ι₀ = ι₀) :
    (characterSubrep L).toRepresentation.dual σ (universalCocharacter L ι₀) =
      universalCocharacter L ι₀ := by
  ext χ
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    universalCocharacter_apply, coeff_toRepresentation_apply, inv_inv, hσ]

/-- **The weight relation.** If `τ ∈ Gal(ℚ^al/ℚ)` lifts complex conjugation along `ι₀`, then
`μ^L + τ μ^L` is the weight. Since the weight is `Gal(ℚ^al/ℚ)`-invariant, `μ^L` satisfies the Serre
relation `(σ - 1)(τ + 1) μ^L = 0`. -/
theorem universalCocharacter_add_dual_eq_weight {ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ}
    {τ : Field.absoluteGaloisGroup ℚ} (hτ : τ • ι₀ = conjEmbedding L ι₀) :
    universalCocharacter L ι₀ +
        (characterSubrep L).toRepresentation.dual τ (universalCocharacter L ι₀) =
      weight L := by
  ext χ
  simp only [LinearMap.add_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, universalCocharacter_apply, coeff_toRepresentation_apply, inv_inv, hτ]
  exact coeff_add_coeff_conjEmbedding χ ι₀

/-- The weight is fixed by the contragredient action of `Gal(ℚ^al/ℚ)`. -/
theorem dual_weight (σ : Field.absoluteGaloisGroup ℚ) :
    (characterSubrep L).toRepresentation.dual σ (weight L) = weight L := by
  ext χ
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

section lift

/-! ### The universal property of the universal cocharacter -/

variable {M : Type*} [AddCommGroup M] [Module ℤ M]
  (ρ : Representation ℤ (Field.absoluteGaloisGroup ℚ) M)
  {ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ} {τ : Field.absoluteGaloisGroup ℚ} {μ : Module.Dual ℤ M}

omit [IsCMField L] in
/-- A Galois element carrying `ι₀` to `φ`. -/
private theorem exists_smul_eq (ι₀ φ : L →ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ σ : Field.absoluteGaloisGroup ℚ, σ • ι₀ = φ :=
  MulAction.exists_smul_eq _ ι₀ φ

/-- Auxiliary construction for `lift`: the vector of `ℤ[E]` attached to `m : M` by a functional
`μ`, whose coefficient at `σ • ι₀` is `μ(σ⁻¹ m)` for a choice of such `σ`. -/
private noncomputable def liftAux (ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ) (μ : Module.Dual ℤ M) :
    M →ₗ[ℤ] ℤ[L →ₐ[ℚ] AlgebraicClosure ℚ] :=
  (coeffLinearEquiv ℤ).symm.toLinearMap ∘ₗ
    (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm.toLinearMap ∘ₗ
      LinearMap.pi fun φ ↦ μ ∘ₗ ρ (exists_smul_eq ι₀ φ).choose⁻¹

omit [IsCMField L] in
/-- If `μ` is fixed by the stabilizer of `ι₀`, the coefficient of `liftAux` at `σ • ι₀` is
`μ(σ⁻¹ m)` for every `σ`, not only for the chosen one. -/
private theorem coeff_liftAux (hstab : ∀ σ, σ • ι₀ = ι₀ → ρ.dual σ μ = μ)
    (σ : Field.absoluteGaloisGroup ℚ) (m : M) :
    (liftAux ρ ι₀ μ m).coeff (σ • ι₀) = μ (ρ σ⁻¹ m) := by
  set s := (exists_smul_eq ι₀ (σ • ι₀)).choose
  have hs : (σ⁻¹ * s) • ι₀ = ι₀ := by
    rw [mul_smul, (exists_smul_eq ι₀ (σ • ι₀)).choose_spec, inv_smul_smul]
  have h := LinearMap.congr_fun (hstab _ hs) (ρ σ⁻¹ m)
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    mul_inv_rev, inv_inv, ← mul_apply_eq_comp, ← map_mul] at h
  simpa [liftAux] using h

omit [IsCMField L] in
/-- `liftAux` is equivariant. -/
private theorem liftAux_apply (hstab : ∀ σ, σ • ι₀ = ι₀ → ρ.dual σ μ = μ)
    (g : Field.absoluteGaloisGroup ℚ) (m : M) :
    liftAux ρ ι₀ μ (ρ g m) = Representation.ofMulAction ℤ _ _ g (liftAux ρ ι₀ μ m) := by
  ext φ
  obtain ⟨σ, rfl⟩ := exists_smul_eq ι₀ φ
  rw [Representation.coeff_ofMulAction, smul_smul, coeff_liftAux ρ hstab,
    coeff_liftAux ρ hstab, mul_inv_rev, inv_inv, map_mul, mul_apply_eq_comp]

/-- Under the Serre relation, `liftAux` takes values in the Serre character lattice: the pair of
embeddings `σ • ι₀` and `σ • τ • ι₀` contributes `(μ + τ μ)(σ⁻¹ m)`, which the relation makes
independent of `σ`. -/
private theorem liftAux_mem (hτ : τ • ι₀ = conjEmbedding L ι₀)
    (hstab : ∀ σ, σ • ι₀ = ι₀ → ρ.dual σ μ = μ)
    (hrel : ∀ σ, ρ.dual σ (μ + ρ.dual τ μ) = μ + ρ.dual τ μ) (m : M) :
    liftAux ρ ι₀ μ m ∈ characterSubrep L := by
  refine ⟨(μ + ρ.dual τ μ) m, fun φ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq ι₀ φ
  have h := LinearMap.congr_fun (hrel σ) m
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    LinearMap.add_apply] at h
  rw [conjEmbedding_smul, ← hτ, smul_smul, coeff_liftAux ρ hstab, coeff_liftAux ρ hstab,
    mul_inv_rev, map_mul, mul_apply_eq_comp, h, LinearMap.add_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply]

variable (ι₀ τ μ) in
/-- **The map to the Serre character lattice** attached to a functional `μ` on an integral
`Gal(ℚ^al/ℚ)`-representation `M` that is fixed by the stabilizer of `ι₀` and satisfies the Serre
relation `(σ - 1)(τ + 1) μ = 0` for a lift `τ` of complex conjugation. Its value at `m` has
coefficient `μ(σ⁻¹ m)` at `σ • ι₀`; see `coeff_lift`. -/
noncomputable def lift (hτ : τ • ι₀ = conjEmbedding L ι₀)
    (hstab : ∀ σ, σ • ι₀ = ι₀ → ρ.dual σ μ = μ)
    (hrel : ∀ σ, ρ.dual σ (μ + ρ.dual τ μ) = μ + ρ.dual τ μ) :
    ρ.IntertwiningMap (characterSubrep L).toRepresentation :=
  LinearMap.intertwiningMap_of_isIntertwiningMap ρ (characterSubrep L).toRepresentation
    (LinearMap.codRestrict (characterSubrep L).toSubmodule (liftAux ρ ι₀ μ)
      (liftAux_mem ρ hτ hstab hrel))
    fun g m ↦ Subtype.ext (liftAux_apply ρ hstab g m)

variable (hτ : τ • ι₀ = conjEmbedding L ι₀) (hstab : ∀ σ, σ • ι₀ = ι₀ → ρ.dual σ μ = μ)
  (hrel : ∀ σ, ρ.dual σ (μ + ρ.dual τ μ) = μ + ρ.dual τ μ)

/-- The coefficient of `lift` at the embedding `σ • ι₀` is `μ(σ⁻¹ m)`. -/
theorem coeff_lift (σ : Field.absoluteGaloisGroup ℚ) (m : M) :
    (lift ρ ι₀ τ μ hτ hstab hrel m).val.coeff (σ • ι₀) = μ (ρ σ⁻¹ m) :=
  coeff_liftAux ρ hstab σ m

/-- **The universal property, existence.** `μ` factors through the universal cocharacter along
`lift`. -/
@[simp]
theorem universalCocharacter_comp_lift :
    universalCocharacter L ι₀ ∘ₗ (lift ρ ι₀ τ μ hτ hstab hrel).toLinearMap = μ := by
  ext m
  simpa using coeff_lift ρ hτ hstab hrel 1 m

/-- **The universal property, uniqueness.** An equivariant map to the Serre character lattice is
determined by its composite with the universal cocharacter. -/
theorem eq_lift (f : ρ.IntertwiningMap (characterSubrep L).toRepresentation)
    (hf : universalCocharacter L ι₀ ∘ₗ f.toLinearMap = μ) :
    f = lift ρ ι₀ τ μ hτ hstab hrel := by
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun m ↦ Subtype.ext ?_)
  ext φ
  obtain ⟨σ, rfl⟩ := exists_smul_eq ι₀ φ
  have h := Representation.IntertwiningMap.isIntertwining _ _ f σ⁻¹ m
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  rw [coeff_lift, ← hf, LinearMap.comp_apply, universalCocharacter_apply,
    Representation.IntertwiningMap.toLinearMap_apply, h, coeff_toRepresentation_apply, inv_inv]

/-- Precomposition with an equivariant map commutes with the contragredient actions. -/
private theorem dual_comp (f : ρ.IntertwiningMap (characterSubrep L).toRepresentation)
    (σ : Field.absoluteGaloisGroup ℚ) (ν : Module.Dual ℤ (characterSubrep L).toSubmodule) :
    ρ.dual σ (ν ∘ₗ f.toLinearMap) =
      (characterSubrep L).toRepresentation.dual σ ν ∘ₗ f.toLinearMap := by
  ext m
  simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]

/-- **The universal property, necessity.** The composite of the universal cocharacter with an
equivariant map is fixed by the stabilizer of `ι₀`. -/
theorem dual_universalCocharacter_comp_of_smul_eq
    (f : ρ.IntertwiningMap (characterSubrep L).toRepresentation)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : σ • ι₀ = ι₀) :
    ρ.dual σ (universalCocharacter L ι₀ ∘ₗ f.toLinearMap) =
      universalCocharacter L ι₀ ∘ₗ f.toLinearMap := by
  rw [dual_comp, dual_universalCocharacter_of_smul_eq hσ]

/-- **The universal property, necessity.** The composite of the universal cocharacter with an
equivariant map satisfies the Serre relation. -/
theorem dual_universalCocharacter_comp_add_dual
    (f : ρ.IntertwiningMap (characterSubrep L).toRepresentation)
    (hτ : τ • ι₀ = conjEmbedding L ι₀) (σ : Field.absoluteGaloisGroup ℚ) :
    ρ.dual σ (universalCocharacter L ι₀ ∘ₗ f.toLinearMap +
        ρ.dual τ (universalCocharacter L ι₀ ∘ₗ f.toLinearMap)) =
      universalCocharacter L ι₀ ∘ₗ f.toLinearMap +
        ρ.dual τ (universalCocharacter L ι₀ ∘ₗ f.toLinearMap) := by
  rw [dual_comp, ← LinearMap.add_comp, universalCocharacter_add_dual_eq_weight hτ, dual_comp,
    dual_weight]

end lift

end TauCeti.SerreTorus
