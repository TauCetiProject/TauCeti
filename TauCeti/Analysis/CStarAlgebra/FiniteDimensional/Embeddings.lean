/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.RingTheory.Idempotents.Basic
import TauCeti.RingTheory.Idempotents.Matrix

/-!
# Orthogonal idempotent bounds and commutative matrix embeddings

Applying `TauCeti.CStarWedderburnPresentation` and `OrthogonalIdempotents.card_le_of_cstarMatrix`,
this file bounds the cardinality of orthogonal idempotent families and commutative product
embeddings in algebras admitting a C⋆-Wedderburn presentation, and characterizes when a finite
commutative C⋆-algebra embeds (possibly nonunitally) into a matrix C⋆-algebra:

* In a unital algebra `A` with presentation `P : CStarWedderburnPresentation A`, any finite family
  of pairwise orthogonal nonzero idempotents has size at most `∑ i, P.degree i`.
* Without assuming a unit on `A`, any injective nonunital ring homomorphism `(ι → R) → A` from a
  finite product over a nontrivial semiring `R` satisfies `Fintype.card ι ≤ ∑ i, P.degree i`.
* `ι → ℂ` admits an injective `NonUnitalStarAlgHom` into `CStarMatrix κ κ ℂ` if and only if
  `Fintype.card ι ≤ Fintype.card κ`.
* Any commutative finite-dimensional complex C⋆-algebra `A` admitting an injective nonunital ring
  homomorphism into `CStarMatrix n n K` (over a domain `K` satisfying `StrongRankCondition`)
  satisfies `Module.finrank ℂ A ≤ Fintype.card n`.

## Main results

* `TauCeti.CStarWedderburnPresentation.card_le_sum_degree_of_orthogonalIdempotents`: orthogonal
  idempotent bound in a unital algebra with a C⋆-Wedderburn presentation.
* `TauCeti.CStarWedderburnPresentation.card_le_sum_degree_of_injective`: rank bound for injective
  nonunital homomorphisms from `ι → R` into a (possibly nonunital) algebra with a C⋆-Wedderburn
  presentation.
* `CStarAlgebra.exists_injective_nonUnitalStarAlgHom_cstarMatrix_iff`: `ι → ℂ` embeds as a
  nonunital `⋆`-algebra into `CStarMatrix κ κ ℂ` iff `Fintype.card ι ≤ Fintype.card κ`.
* `CStarAlgebra.finrank_le_card_of_injective_cstarMatrix`: dimension bound for commutative
  finite-dimensional C⋆-algebras embedding into `CStarMatrix n n K`.
-/

public section

open scoped BigOperators

universe u

namespace TauCeti.CStarWedderburnPresentation

/-- In a unital algebra admitting a `CStarWedderburnPresentation`, any finite family of pairwise
orthogonal nonzero idempotents has cardinality at most `∑ i, P.degree i`. -/
theorem card_le_sum_degree_of_orthogonalIdempotents {A : Type u} [Semiring A] [SMul ℂ A] [Star A]
    (P : CStarWedderburnPresentation A) {ι : Type*} [Fintype ι] {e : ι → A}
    (he : OrthogonalIdempotents e) (hne : ∀ k, e k ≠ 0) :
    Fintype.card ι ≤ ∑ i, P.degree i := by
  classical
  let S (i : Fin P.blockCount) := {k : ι // P.matrixStarAlgEquiv (e k) i ≠ 0}
  have hcard (i : Fin P.blockCount) : Fintype.card (S i) ≤ P.degree i := by
    let φ_i : A →+* Matrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
      (Pi.evalRingHom _ i).comp P.matrixStarAlgEquiv.toRingEquiv.toRingHom
    have he_i : OrthogonalIdempotents (fun k : S i ↦ φ_i (e k.val)) :=
      (he.map φ_i).embedding ⟨Subtype.val, Subtype.val_injective⟩
    simpa only [Fintype.card_fin] using he_i.card_le_of_matrix fun k ↦ k.property
  have hex (k : ι) : ∃ i, P.matrixStarAlgEquiv (e k) i ≠ 0 := by
    refine Function.ne_iff.mp fun h ↦ hne k (EquivLike.injective P.matrixStarAlgEquiv ?_)
    exact h.trans (map_zero P.matrixStarAlgEquiv).symm
  let g : ι → Σ i, S i := fun k ↦ ⟨(hex k).choose, ⟨k, (hex k).choose_spec⟩⟩
  have hg : Function.Injective g := fun _ _ h ↦ congrArg (fun x ↦ x.snd.val) h
  calc
    Fintype.card ι ≤ Fintype.card (Σ i, S i) := Fintype.card_le_of_injective g hg
    _ = ∑ i, Fintype.card (S i) := Fintype.card_sigma
    _ ≤ ∑ i, P.degree i := Finset.sum_le_sum fun i _ ↦ hcard i

/-- If a finite product `ι → R` over a nontrivial semiring `R` embeds via a (possibly nonunital)
ring homomorphism into a (possibly nonunital) algebra `A` admitting a
`CStarWedderburnPresentation`, then `Fintype.card ι ≤ ∑ i, P.degree i`. -/
theorem card_le_sum_degree_of_injective {A : Type u} [NonUnitalNonAssocSemiring A] [SMul ℂ A]
    [Star A] (P : CStarWedderburnPresentation A) {ι R F : Type*} [Fintype ι] [Semiring R]
    [Nontrivial R] [FunLike F (ι → R) A] [NonUnitalRingHomClass F (ι → R) A] (φ : F)
    (hφ : Function.Injective φ) : Fintype.card ι ≤ ∑ i, P.degree i := by
  classical
  let Q : CStarWedderburnPresentation (∀ i, CStarMatrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ) :=
    { blockCount := P.blockCount, degree := P.degree, equiv := .refl ℂ _ }
  let ψ : (ι → R) →ₙ+* ∀ i, CStarMatrix (Fin (P.degree i)) (Fin (P.degree i)) ℂ :=
    P.equiv.toRingEquiv.toNonUnitalRingHom.comp (NonUnitalRingHomClass.toNonUnitalRingHom φ)
  have hψ : Function.Injective ψ := fun _ _ h ↦ hφ (P.equiv.injective h)
  have he : OrthogonalIdempotents (ψ ∘ (Pi.single (M := fun _ : ι ↦ R) · 1)) :=
    (OrthogonalIdempotents.single (fun _ : ι ↦ R)).map' ψ
  refine Q.card_le_sum_degree_of_orthogonalIdempotents he fun k hk ↦ ?_
  have hk0 : (Pi.single k 1 : ι → R) = 0 := hψ (hk.trans (map_zero ψ).symm)
  exact one_ne_zero (α := R) (by simpa using congrFun hk0 k)

end TauCeti.CStarWedderburnPresentation

namespace CStarAlgebra

/-- The finite-dimensional commutative C⋆-algebra `ι → ℂ` admits an injective (possibly nonunital)
`⋆`-algebra homomorphism into `CStarMatrix κ κ ℂ` if and only if
`Fintype.card ι ≤ Fintype.card κ`. -/
theorem exists_injective_nonUnitalStarAlgHom_cstarMatrix_iff {ι κ : Type*} [Fintype ι]
    [Fintype κ] :
    (∃ φ : (ι → ℂ) →⋆ₙₐ[ℂ] CStarMatrix κ κ ℂ, Function.Injective φ) ↔
      Fintype.card ι ≤ Fintype.card κ := by
  classical
  refine ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun hle ↦ ?_⟩
  · have he : OrthogonalIdempotents (φ ∘ (Pi.single (M := fun _ : ι ↦ ℂ) · 1)) :=
      (OrthogonalIdempotents.single (fun _ : ι ↦ ℂ)).map' φ
    refine he.card_le_of_cstarMatrix fun k hk ↦ ?_
    have hk0 : (Pi.single k 1 : ι → ℂ) = 0 := hφ (hk.trans (map_zero φ).symm)
    exact one_ne_zero (α := ℂ) (by simpa using congrFun hk0 k)
  · have emb : ι ↪ κ :=
      (Fintype.equivFin ι).toEmbedding.trans
        ((Fin.castLEEmb hle).trans (Fintype.equivFin κ).symm.toEmbedding)
    let extHom : (ι → ℂ) →⋆ₙₐ[ℂ] (κ → ℂ) :=
      { toFun f := Function.extend emb f 0
        map_smul' r f := by simpa using Function.extend_smul r emb f (0 : κ → ℂ)
        map_zero' := by ext k; by_cases hk : ∃ i, emb i = k <;> simp [Function.extend_def, hk]
        map_add' f g := by simpa using Function.extend_add emb f g (0 : κ → ℂ) 0
        map_mul' f g := by simpa using Function.extend_mul emb f g (0 : κ → ℂ) 0
        map_star' f := by ext k; by_cases hk : ∃ i, emb i = k <;> simp [Function.extend_def, hk] }
    let diagHom : (κ → ℂ) →⋆ₐ[ℂ] Matrix κ κ ℂ :=
      { Matrix.diagonalAlgHom ℂ with map_star' f := (Matrix.diagonal_conjTranspose f).symm }
    let φ : (ι → ℂ) →⋆ₙₐ[ℂ] CStarMatrix κ κ ℂ :=
      CStarMatrix.ofMatrixStarAlgEquiv.toNonUnitalStarAlgHom.comp
        (diagHom.toNonUnitalStarAlgHom.comp extHom)
    refine ⟨φ, CStarMatrix.ofMatrixStarAlgEquiv.injective.comp <|
      Matrix.diagonal_injective.comp fun f g hfg ↦ funext fun i ↦ ?_⟩
    have hfg' : Function.extend emb f 0 (emb i) = Function.extend emb g 0 (emb i) :=
      congrFun hfg (emb i)
    simpa only [emb.injective.extend_apply] using hfg'

/-- Any commutative finite-dimensional complex C⋆-algebra `A` admitting an injective (possibly
nonunital) ring homomorphism into `CStarMatrix n n K` over a domain `K` satisfying
`StrongRankCondition` has complex dimension at most `Fintype.card n`. -/
theorem finrank_le_card_of_injective_cstarMatrix {A : Type u} [NonUnitalCStarAlgebra A]
    [FiniteDimensional ℂ A] [IsMulCommutative A] {K n F : Type*} [Ring K] [IsDomain K]
    [StrongRankCondition K] [Fintype n] [FunLike F A (CStarMatrix n n K)]
    [NonUnitalRingHomClass F A (CStarMatrix n n K)] (φ : F) (hφ : Function.Injective φ) :
    Module.finrank ℂ A ≤ Fintype.card n := by
  classical
  obtain ⟨e⟩ := (isMulCommutative_iff_nonempty_starAlgEquiv_fun A).mp inferInstance
  let ψ : (Fin (Module.finrank ℂ A) → ℂ) →ₙ+* CStarMatrix n n K :=
    (NonUnitalRingHomClass.toNonUnitalRingHom φ).comp e.symm.toRingEquiv.toNonUnitalRingHom
  have hψ : Function.Injective ψ := fun _ _ h ↦ e.symm.injective (hφ h)
  have he : OrthogonalIdempotents
      (ψ ∘ (Pi.single (M := fun _ : Fin (Module.finrank ℂ A) ↦ ℂ) · 1)) :=
    (OrthogonalIdempotents.single (fun _ : Fin (Module.finrank ℂ A) ↦ ℂ)).map' ψ
  simpa only [Fintype.card_fin] using he.card_le_of_cstarMatrix fun k hk ↦
    one_ne_zero (α := ℂ) (by
      have hk0 := hψ (hk.trans (map_zero ψ).symm)
      simpa using congrFun hk0 k)

end CStarAlgebra
