/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Basis
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Killing
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Serre.Presentation
public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism
public import TauCeti.Algebra.Lie.Presentation.Serre.Injective
public import TauCeti.Algebra.Lie.Subalgebra.LieSpan

/-!
# The type-D Serre presentation of the split orthogonal Lie algebra

The explicit split orthogonal matrices `TauCeti.TypeDStd.rootGenerator` and
`TauCeti.TypeDStd.cartanGenerator` satisfy Serre's relations for the Bourbaki-numbered Cartan
matrix `CartanMatrix.D n`, which gives the homomorphism `TauCeti.TypeDStd.serreRepresentation`
out of the presented Lie algebra. Over a field of characteristic zero this homomorphism is an
isomorphism (`TauCeti.TypeDStd.serreEquiv`): the numbered generators generate the matrix algebra,
and Serre's theorem for the Lie algebra basis `TauCeti.TypeDStd.lieBasis`, whose Killing form is
nondegenerate by `TauCeti.TypeDStd.isKilling_typeD`, gives injectivity. No dimension count is
used.

Every permutation `σ` of the nodes preserving the Cartan matrix induces the automorphism
`TauCeti.serreDiagramAut` of the presented algebra. Transporting it along `serreEquiv` gives the
automorphism `TauCeti.TypeDStd.diagramAut` of the matrix algebra, which permutes the numbered
Cartan, raising and lowering matrices along `σ`. It preserves the diagonal Cartan subalgebra and
the standard positive Borel subalgebra. For the exchange of the two fork nodes it is the native
conjugation `TauCeti.typeDGraphLieEquiv` by the swap of the last hyperbolic pair, and for `D₄` the
triality permutation `TauCeti.trialityPermD4` gives an automorphism of order dividing three
(`TauCeti.TypeDStd.trialityAut`).

## Main definitions

* `TauCeti.TypeDStd.serreEquiv`: the Serre presentation
  `Matrix.ToLieAlgebra K (CartanMatrix.D n) ≃ₗ⁅K⁆ LieAlgebra.Orthogonal.typeD (Fin n) K`.
* `TauCeti.TypeDStd.diagramAut`: the diagram automorphism of the matrix algebra induced by a
  symmetry of the Cartan matrix.
* `TauCeti.TypeDStd.trialityAut`: the triality automorphism of the matrix algebra of type `D₄`.

## Main results

* `TauCeti.TypeDStd.serreRepresentation_bijective`: Serre's theorem for the matrix realization.
* `TauCeti.TypeDStd.lieHom_ext`: a Lie homomorphism out of the matrix algebra is determined by
  its values on the numbered raising and lowering matrices.
* `TauCeti.TypeDStd.diagramAut_rootGenerator` and `TauCeti.TypeDStd.diagramAut_cartanGenerator`:
  the diagram automorphism permutes the numbered generators.
* `TauCeti.TypeDStd.map_diagramAut_typeDDiagonalCartan` and
  `TauCeti.TypeDStd.map_diagramAut_borel`: it preserves the Cartan and positive Borel subalgebras.
* `TauCeti.TypeDStd.diagramAut_refl`, `TauCeti.TypeDStd.diagramAut_symm` and
  `TauCeti.TypeDStd.diagramAut_trans`: the group law of the permutations.
* `TauCeti.TypeDStd.diagramAut_graphPermD`: for the fork exchange it is the native graph
  involution.
* `TauCeti.TypeDStd.trialityAut_trialityAut_trialityAut`: triality has order dividing three.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
-/

public section

open scoped Matrix

namespace TauCeti.TypeDStd

open LieAlgebra.Orthogonal

variable {K : Type*} [Field K] (n : ℕ) (hn : 4 ≤ n)

section NeZero

variable [NeZero (2 : K)]

/-- The matrix realization of the type-`D` Serre presentation is surjective: the numbered raising
and lowering matrices generate the split orthogonal Lie algebra. -/
theorem serreRepresentation_surjective :
    Function.Surjective (serreRepresentation (K := K) n hn) := by
  rw [TauCeti.eq_serreLift (g := serreRepresentation (K := K) n hn)
    (h := isSerreSystem_rootGenerator (K := K) n hn) (fun i => by simp) fun i => by simp]
  exact serreLift_surjective _ (lieSpan_rootGenerator_eq_top n hn)

/-- **A Lie homomorphism out of the split type-`D` matrix algebra is determined by its values on
the numbered raising and lowering matrices.** -/
theorem lieHom_ext {L : Type*} [LieRing L] [LieAlgebra K L]
    {f g : typeD (Fin n) K →ₗ⁅K⁆ L}
    (h : ∀ k, f (rootGenerator n hn k) = g (rootGenerator n hn k)) : f = g := by
  have hcomp : f.comp (serreRepresentation n hn) = g.comp (serreRepresentation n hn) :=
    TauCeti.serre_hom_ext (fun i => by simpa using h (.inl i)) fun i => by simpa using h (.inr i)
  ext x
  obtain ⟨y, rfl⟩ := serreRepresentation_surjective n hn x
  exact DFunLike.congr_fun hcomp y

end NeZero

variable [CharZero K]

/-- **Serre's theorem for the split type-`D` matrix algebra**: its realization of the Serre
presentation is injective. -/
theorem serreRepresentation_injective :
    Function.Injective (serreRepresentation (K := K) n hn) := by
  let _ := isKilling_typeD (K := K) n hn
  have hCM : (lieBasis (K := K) n hn).Aᵀ = CartanMatrix.D n := by
    rw [lieBasis_A_eq]
    exact CartanMatrix.D_isSymm n
  have hS : IsSerreSystem K (CartanMatrix.D n) (lieBasis (K := K) n hn).h
      (lieBasis (K := K) n hn).e (lieBasis (K := K) n hn).f :=
    hCM ▸ isSerreSystem_lieBasis _
  have heq : serreRepresentation (K := K) n hn = serreLift hS :=
    TauCeti.eq_serreLift (fun i => by simp) fun i => by simp
  rw [heq]
  exact (lieBasis n hn).serreLift_injective_of_A_transpose_eq hCM hS

/-- **The matrix realization of the type-`D` Serre presentation is bijective.** -/
theorem serreRepresentation_bijective :
    Function.Bijective (serreRepresentation (K := K) n hn) :=
  ⟨serreRepresentation_injective n hn, serreRepresentation_surjective n hn⟩

/-- **The Serre presentation of the split type-`D` matrix algebra**: the isomorphism from the Lie
algebra presented by Serre's relations for `CartanMatrix.D n` sending the numbered Cartan,
raising and lowering generators to the explicit split orthogonal matrices. -/
noncomputable def serreEquiv :
    Matrix.ToLieAlgebra K (CartanMatrix.D n) ≃ₗ⁅K⁆ typeD (Fin n) K :=
  LieEquiv.ofBijective (serreRepresentation n hn) (serreRepresentation_bijective n hn)

/-- The Serre presentation of the matrix algebra is the matrix realization. -/
@[simp]
theorem coe_serreEquiv : ⇑(serreEquiv (K := K) n hn) = serreRepresentation n hn :=
  (rfl)

/-- The underlying homomorphism of the Serre presentation is the matrix realization. -/
@[simp]
theorem serreEquiv_toLieHom :
    (serreEquiv (K := K) n hn).toLieHom = serreRepresentation n hn :=
  (rfl)

/-- The inverse presentation sends a numbered coroot matrix to the presented Cartan generator. -/
@[simp]
theorem serreEquiv_symm_cartanGenerator (i : Fin n) :
    (serreEquiv (K := K) n hn).symm (cartanGenerator n hn i) =
      serreH K (CartanMatrix.D n) i := by
  rw [LieEquiv.symm_apply_eq, coe_serreEquiv, serreRepresentation_serreH]

/-- The inverse presentation sends a numbered raising matrix to the presented positive
generator. -/
@[simp]
theorem serreEquiv_symm_rootGenerator_inl (i : Fin n) :
    (serreEquiv (K := K) n hn).symm (rootGenerator n hn (.inl i)) =
      serreE K (CartanMatrix.D n) i := by
  rw [LieEquiv.symm_apply_eq, coe_serreEquiv, serreRepresentation_serreE]

/-- The inverse presentation sends a numbered lowering matrix to the presented negative
generator. -/
@[simp]
theorem serreEquiv_symm_rootGenerator_inr (i : Fin n) :
    (serreEquiv (K := K) n hn).symm (rootGenerator n hn (.inr i)) =
      serreF K (CartanMatrix.D n) i := by
  rw [LieEquiv.symm_apply_eq, coe_serreEquiv, serreRepresentation_serreF]

/-! ### Diagram automorphisms -/

section Diagram

variable {σ τ : Equiv.Perm (Fin n)}

/-- **The diagram automorphism of the split type-`D` matrix algebra** induced by a permutation
`σ` of the nodes preserving `CartanMatrix.D n`: the automorphism `TauCeti.serreDiagramAut` of the
Serre presentation, transported along `TauCeti.TypeDStd.serreEquiv`. -/
noncomputable def diagramAut (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n) :
    typeD (Fin n) K ≃ₗ⁅K⁆ typeD (Fin n) K :=
  ((serreEquiv n hn).symm.trans (serreDiagramAut K (CartanMatrix.D n) hσ)).trans
    (serreEquiv n hn)

/-- The diagram automorphism is the Serre diagram automorphism read through the presentation. -/
theorem diagramAut_apply (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n)
    (x : typeD (Fin n) K) :
    diagramAut n hn hσ x =
      serreEquiv n hn (serreDiagramAut K (CartanMatrix.D n) hσ ((serreEquiv n hn).symm x)) :=
  (rfl)

/-- The diagram automorphism permutes the numbered raising and lowering matrices along `σ`. -/
@[simp]
theorem diagramAut_rootGenerator (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n)
    (k : Fin n ⊕ Fin n) :
    diagramAut (K := K) n hn hσ (rootGenerator n hn k) =
      rootGenerator n hn (Sum.map σ σ k) := by
  rcases k with i | i <;> simp [diagramAut]

/-- The diagram automorphism permutes the numbered coroot matrices along `σ`. -/
@[simp]
theorem diagramAut_cartanGenerator (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n)
    (i : Fin n) :
    diagramAut (K := K) n hn hσ (cartanGenerator n hn i) = cartanGenerator n hn (σ i) := by
  simp [diagramAut]

/-- `TauCeti.TypeDStd.diagramAut` is the unique Lie endomorphism permuting the numbered raising
and lowering matrices along `σ`. -/
theorem eq_diagramAut {hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n}
    {g : typeD (Fin n) K →ₗ⁅K⁆ typeD (Fin n) K}
    (h : ∀ k, g (rootGenerator n hn k) = rootGenerator n hn (Sum.map σ σ k)) :
    g = (diagramAut n hn hσ).toLieHom :=
  lieHom_ext n hn fun k => by rw [h, LieEquiv.coe_toLieHom, diagramAut_rootGenerator]

/-- The identity permutation induces the identity automorphism. -/
@[simp]
theorem diagramAut_refl :
    diagramAut (K := K) n hn (submatrix_perm_refl (CartanMatrix.D n)) = LieEquiv.refl :=
  LieEquiv.ext fun x => DFunLike.congr_fun (eq_diagramAut (g := LieHom.id) n hn fun k => by
    rcases k with i | i <;> simp).symm x

/-- The inverse of a diagram automorphism is the diagram automorphism of the inverse
permutation. -/
theorem diagramAut_symm (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n) :
    (diagramAut (K := K) n hn hσ).symm = diagramAut n hn (submatrix_perm_symm hσ) :=
  LieEquiv.ext fun x => by
    rw [LieEquiv.symm_apply_eq]
    have h : (diagramAut (K := K) n hn hσ).toLieHom.comp
        (diagramAut n hn (submatrix_perm_symm hσ)).toLieHom = LieHom.id :=
      lieHom_ext n hn fun k => by rcases k with i | i <;> simp
    exact (DFunLike.congr_fun h x).symm

/-- Diagram automorphisms compose along the composition of permutations. -/
theorem diagramAut_trans (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n)
    (hτ : (CartanMatrix.D n).submatrix τ τ = CartanMatrix.D n) :
    (diagramAut (K := K) n hn hσ).trans (diagramAut n hn hτ) =
      diagramAut n hn (submatrix_perm_trans hσ hτ) := by
  refine LieEquiv.ext fun x => DFunLike.congr_fun (eq_diagramAut (g := ((diagramAut n hn hσ).trans
    (diagramAut n hn hτ)).toLieHom) n hn fun k => ?_) x
  rcases k with i | i <;> simp

/-- The diagram automorphism maps the diagonal Cartan subalgebra onto itself. -/
theorem map_diagramAut_typeDDiagonalCartan
    (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n) :
    (typeDDiagonalCartan K (Fin n)).map (diagramAut n hn hσ).toLieHom =
      typeDDiagonalCartan K (Fin n) := by
  rw [typeDDiagonalCartan_eq_lieSpan_cartanGenerator n hn]
  exact LieSubalgebra.map_lieSpan_range_of_surjective _ σ.surjective fun i => by simp

/-- The diagram automorphism maps the standard positive Borel subalgebra, spanned by the diagonal
Cartan subalgebra and the numbered raising matrices, onto itself. -/
theorem map_diagramAut_borel (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n) :
    (typeDDiagonalCartan K (Fin n) ⊔
        LieSubalgebra.lieSpan K (typeD (Fin n) K)
          (Set.range fun i => rootGenerator n hn (.inl i))).map (diagramAut n hn hσ).toLieHom =
      typeDDiagonalCartan K (Fin n) ⊔
        LieSubalgebra.lieSpan K (typeD (Fin n) K)
          (Set.range fun i => rootGenerator n hn (.inl i)) := by
  rw [(LieSubalgebra.gc_map_comap (f := (diagramAut n hn hσ).toLieHom)).l_sup,
    map_diagramAut_typeDDiagonalCartan, LieSubalgebra.map_lieSpan_range_of_surjective _
      (g := fun i => rootGenerator (K := K) n hn (.inl i)) σ.surjective fun i => by simp]

/-- **The fork exchange induces the native graph involution**: the diagram automorphism of the
permutation exchanging the two fork nodes is conjugation by the swap of the last hyperbolic
pair. -/
theorem diagramAut_graphPermD
    (hσ : (CartanMatrix.D n).submatrix (graphPermD n (by omega)) (graphPermD n (by omega)) =
      CartanMatrix.D n) :
    diagramAut (K := K) n hn hσ = typeDGraphLieEquiv (forkRight n hn) K := by
  refine (LieEquiv.ext fun x => DFunLike.congr_fun (eq_diagramAut (hσ := hσ)
    (g := (typeDGraphLieEquiv (forkRight n hn) K).toLieHom) n hn fun k => ?_) x).symm
  exact typeDGraphLieEquiv_rootGenerator K n hn k

end Diagram

/-! ### Triality -/

-- `TauCeti.D4Triality.reindex_cartanMatrix` states this for `Matrix.reindex`, which is
-- `Matrix.submatrix` along the inverse permutation.
private theorem submatrix_trialityPermD4 :
    (CartanMatrix.D 4).submatrix trialityPermD4 trialityPermD4 = CartanMatrix.D 4 := by
  ext i j
  simpa only [Matrix.submatrix_apply, DynkinType.cartanMatrix_D] using
    cartanMatrix_D4_trialityPermD4 i j

/-- **The triality automorphism of the split orthogonal Lie algebra of type `D₄`**: the diagram
automorphism cycling the three outer nodes `0 → 2 → 3 → 0` and fixing the central node `1`. -/
noncomputable def trialityAut : typeD (Fin 4) K ≃ₗ⁅K⁆ typeD (Fin 4) K :=
  diagramAut 4 le_rfl submatrix_trialityPermD4

/-- Triality is the diagram automorphism of the triality permutation. -/
theorem trialityAut_eq_diagramAut
    (h : (CartanMatrix.D 4).submatrix trialityPermD4 trialityPermD4 = CartanMatrix.D 4) :
    trialityAut (K := K) = diagramAut 4 le_rfl h :=
  (rfl)

/-- Triality permutes the numbered raising and lowering matrices along `trialityPermD4`. -/
@[simp]
theorem trialityAut_rootGenerator (k : Fin 4 ⊕ Fin 4) :
    trialityAut (K := K) (rootGenerator 4 le_rfl k) =
      rootGenerator 4 le_rfl (Sum.map trialityPermD4 trialityPermD4 k) :=
  diagramAut_rootGenerator 4 le_rfl _ k

/-- Triality permutes the numbered coroot matrices along `trialityPermD4`. -/
@[simp]
theorem trialityAut_cartanGenerator (i : Fin 4) :
    trialityAut (K := K) (cartanGenerator 4 le_rfl i) =
      cartanGenerator 4 le_rfl (trialityPermD4 i) :=
  diagramAut_cartanGenerator 4 le_rfl _ i

/-- **Triality has order dividing three.** -/
@[simp]
theorem trialityAut_trialityAut_trialityAut (x : typeD (Fin 4) K) :
    trialityAut (trialityAut (trialityAut x)) = x := by
  have h : (trialityAut (K := K)).toLieHom.comp
      ((trialityAut (K := K)).toLieHom.comp (trialityAut (K := K)).toLieHom) = LieHom.id :=
    lieHom_ext 4 le_rfl fun k => by rcases k with i | i <;> simp
  exact DFunLike.congr_fun h x

end TauCeti.TypeDStd
