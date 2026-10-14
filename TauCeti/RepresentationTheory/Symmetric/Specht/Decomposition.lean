/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Reading
public import TauCeti.LinearAlgebra.Trace.Idempotent
public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.OfModule
public import TauCeti.RepresentationTheory.QuasiIdempotent
public import TauCeti.RepresentationTheory.Symmetric.Specht.Character
public import TauCeti.RepresentationTheory.Symmetric.Specht.Comparison
public import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Character
public import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent
public import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality

/-!
# The Young-symmetrizer decomposition of a representation of the symmetric group

Let `k` be a field of characteristic zero and `M` a finite-dimensional representation of the
symmetric group `S_d` over `k`. For each partition `μ` of `d`, let `c_μ ∈ k[S_d]` be the Young
symmetrizer of the row-superstandard tableau of `μ` (`Nat.Partition.youngSymmetrizer`). This file
proves that `M` decomposes along these elements as

`⨁_μ k[S_d] c_μ ⊗ c_μ M ≅ M`,   `a ⊗ w ↦ a · w`,

an isomorphism of representations of `S_d` acting on the left factors
(`Representation.youngSymmetrizerEquiv`). The left factor `k[S_d] c_μ` is the Specht module of `μ`
in its ideal presentation, of dimension `f^μ = dim S^μ`
(`Nat.Partition.finrank_span_youngSymmetrizer`), and the right factor `c_μ M` is its multiplicity
space: the intertwining maps `k[S_d] c_μ → M` are identified with `c_μ M` by evaluation at `c_μ`
(`Representation.spanSingletonHomEquivRange`). Applied to the tensor power `(kⁿ)^{⊗d}`, where
`c_μ (kⁿ)^{⊗d}` is the Weyl module of `μ`, this is the Schur-Weyl decomposition of
`TauCeti/RepresentationTheory/ClassicalGroups/WeylModule/Decomposition.lean`.

## The argument

Nothing beyond the existing character theory of `S_d` is used; in particular the decomposition
does not go through a classification of the simple `k[S_d]`-modules, and `k` need not be a
splitting field.

* **The dimension count.** The Young symmetrizer satisfies `c_μ² = (d! / f^μ) c_μ`, so its action
  on `M` is a scaled projection onto `c_μ M` and `(d! / f^μ) dim (c_μ M) = tr (c_μ | M)`. Pairing
  `c_μ` with the class function `χ_M` is pairing the Specht character `χ^μ` with it, up to the
  factor `f^μ`, so `d! dim (c_μ M) = ∑_σ χ^μ(σ) χ_M(σ)`
  (`Representation.factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizer`). Summing against
  the degrees and using column orthogonality `∑_μ f^μ χ^μ(σ) = d! [σ = 1]` gives
  `dim M = ∑_μ f^μ dim (c_μ M)`
  (`Representation.finrank_eq_sum_finrank_spechtModule_mul_finrank_range`).
* **Generation.** The image `N` of the evaluation map contains every `c_μ M`, because
  `c_μ m = c_μ · ((f^μ / d!) c_μ m)`, and it is `S_d`-stable. Every Young symmetrizer therefore
  acts as zero on `M / N`, and the dimension count applied to `M / N` gives `M / N = 0`.
* **Injectivity.** The source has dimension `∑_μ f^μ dim (c_μ M) = dim M`, so the surjective
  evaluation map is bijective.

## Main definitions

* `Nat.Partition.youngSymmetrizer`: the Young symmetrizer of a partition `μ` of `d`, in `k[S_d]`.
* `Representation.youngSymmetrizerEval`: the evaluation map `⨁_μ k[S_d] c_μ ⊗ c_μ M → M`.
* `Representation.youngSymmetrizerEquiv`: the evaluation map as an equivalence of representations
  of `S_d`.

## Main results

* `Nat.Partition.youngSymmetrizer_mul_self`: `c_μ² = (d! / f^μ) c_μ`.
* `Nat.Partition.finrank_span_youngSymmetrizer`: `dim (k[S_d] c_μ) = f^μ`.
* `Representation.factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizer`:
  `d! dim (c_μ M) = ∑_σ χ^μ(σ) χ_M(σ)`, so `dim (c_μ M)` is the multiplicity of `χ^μ` in `χ_M`.
* `Representation.finrank_eq_sum_finrank_spechtModule_mul_finrank_range`:
  `dim M = ∑_μ f^μ dim (c_μ M)`.
* `Representation.youngSymmetrizerEval_surjective` and
  `Representation.youngSymmetrizerEval_bijective`: the Young-symmetrizer images generate `M`, and
  the evaluation map is an isomorphism.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 4 (Young
  symmetrizers) and Lecture 6, §6.1 (the decomposition of a tensor power under `S_d × GL(V)`).
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7.
-/

public section

open Module
open scoped DirectSum TensorProduct

namespace Nat.Partition

open TauCeti

variable {d : ℕ} (μ : d.Partition) (k : Type*)

section CommSemiring

variable [CommSemiring k] [Algebra ℚ k]

/-- **The Young symmetrizer of a partition** `μ` of `d`, as an element of `k[S_d]`: the Young
symmetrizer `c_t = a_t b_t` of the row-superstandard tableau `t` of the diagram of `μ`, transported
to `k` and with the labels of the diagram identified with `Fin d` along
`YoungDiagram.card_ofPartition`. This is the identification along which `TauCeti.spechtModule μ`
is a representation of `S_d`. -/
noncomputable def youngSymmetrizer : MonoidAlgebra k (Equiv.Perm (Fin d)) :=
  MonoidAlgebra.domCongr k k (finCongr (YoungDiagram.card_ofPartition μ)).permCongrHom
    (YoungTableau.youngSymmetrizerOver k
      (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau)

/-- The Young symmetrizer of a partition is the transported Young symmetrizer of the
row-superstandard tableau of its diagram. -/
theorem youngSymmetrizer_def :
    μ.youngSymmetrizer k =
      MonoidAlgebra.domCongr k k (finCongr (YoungDiagram.card_ofPartition μ)).permCongrHom
        (YoungTableau.youngSymmetrizerOver k
          (StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition μ)).toTableau) :=
  (rfl)

/-- **The Young symmetrizer is quasi-idempotent**: `c_μ² = (d! / f^μ) c_μ`, where `f^μ` is the
dimension of the Specht module `S^μ`. -/
theorem youngSymmetrizer_mul_self :
    μ.youngSymmetrizer k * μ.youngSymmetrizer k =
      algebraMap ℚ k ((d.factorial : ℚ) / finrank ℚ (spechtModule μ)) • μ.youngSymmetrizer k := by
  have hd : ((YoungDiagram.ofPartition μ).card.factorial : ℚ) = d.factorial := by
    rw [YoungDiagram.card_ofPartition]
  rw [youngSymmetrizer_def, ← map_mul, YoungTableau.youngSymmetrizerOver_sq, map_smul,
    YoungTableau.finrank_spechtIdeal_eq_spechtSubrepresentation, hd]

/-- The coefficient of the identity in the Young symmetrizer is `1`. -/
theorem youngSymmetrizer_coeff_one : (μ.youngSymmetrizer k).coeff 1 = 1 := by
  rw [youngSymmetrizer_def, MonoidAlgebra.coeff_domCongr, map_one,
    YoungTableau.youngSymmetrizerOver_coeff, YoungTableau.youngSymmetrizer_coeff_one, map_one]

end CommSemiring

section Field

variable [Field k] [CharZero k]

/-- **The left ideal `k[S_d] c_μ` has the dimension `f^μ` of the Specht module.** Its character
at the identity, multiplied by `d! / f^μ`, is `d!` times the coefficient `1` of the identity in
`c_μ` (`Representation.mul_char_ofModule'_span_singleton`). -/
theorem finrank_span_youngSymmetrizer :
    finrank k (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))) =
      finrank ℚ (spechtModule μ) := by
  have hf : (finrank ℚ (spechtModule μ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (finrank_spechtModule_pos μ).ne'
  have hd : (d.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
  have h := Representation.mul_char_ofModule'_span_singleton (μ.youngSymmetrizer_mul_self k) 1
  simp only [inv_one, mul_one, inv_mul_cancel, youngSymmetrizer_coeff_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, Representation.char_one,
    map_div₀, map_natCast] at h
  apply Nat.cast_injective (R := k)
  field_simp at h
  linear_combination h

end Field

end Nat.Partition

namespace Representation

open TauCeti

variable {k : Type*} [Field k] [CharZero k] {d : ℕ} {M : Type*} [AddCommGroup M] [Module k M]

/-- **The dimension of the image of the Young symmetrizer of a tableau**, through the Specht
character: for a tableau `t` of shape `μ` and a finite-dimensional representation `M` of
`S_{|μ|}`, `|μ|! · dim (c_t M) = ∑_σ χ^μ(σ) χ_M(σ)`. -/
theorem factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizerOver
    [FiniteDimensional k M] {D : YoungDiagram} (t : YoungTableau D)
    (ρ : Representation k (Equiv.Perm (Fin D.card)) M) :
    (D.card.factorial : k) * finrank k (LinearMap.range
        (ρ.asAlgebraHom (YoungTableau.youngSymmetrizerOver k t))) =
      ∑ σ, (spechtSubrepresentation D).toRepresentation.character σ • ρ.character σ := by
  have hf : (finrank ℚ (spechtSubrepresentation D).toSubmodule : ℚ) ≠ 0 := by
    rw [← YoungTableau.finrank_spechtIdeal_eq_spechtSubrepresentation t]
    exact_mod_cast (YoungTableau.finrank_spechtIdeal_pos t).ne'
  set f : ℚ := (finrank ℚ (spechtSubrepresentation D).toSubmodule : ℚ)
  -- the action of `c_t` squares to `(|μ|! / f) • c_t`, so its trace is that scalar times its rank
  have hsq : ρ.asAlgebraHom (YoungTableau.youngSymmetrizerOver k t) *
      ρ.asAlgebraHom (YoungTableau.youngSymmetrizerOver k t) =
        algebraMap ℚ k ((D.card.factorial : ℚ) / f) •
          ρ.asAlgebraHom (YoungTableau.youngSymmetrizerOver k t) := by
    rw [← map_mul, YoungTableau.youngSymmetrizerOver_sq, map_smul,
      YoungTableau.finrank_spechtIdeal_eq_spechtSubrepresentation]
  have htrace := TauCeti.LinearMap.trace_eq_mul_finrank_range hsq
  -- the same trace is the pairing of the coefficients of `c_t` with the character of `M`
  have hsum : LinearMap.trace k M (ρ.asAlgebraHom (YoungTableau.youngSymmetrizerOver k t)) =
      ∑ σ, (YoungTableau.youngSymmetrizer t).coeff σ • ρ.character σ := by
    simp_rw [asAlgebraHom_eq_sum, map_sum, map_smul, YoungTableau.youngSymmetrizerOver_coeff,
      algebraMap_smul, character]
  rw [YoungTableau.sum_char_spechtSubrepresentation_smul t ρ.character fun g σ => ρ.char_conj g σ,
    ← hsum, htrace, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hf, map_natCast]

variable (ρ : Representation k (Equiv.Perm (Fin d)) M)

/-- **The dimension of the image of a Young symmetrizer.** For a partition `μ` of `d` and a
finite-dimensional representation `M` of `S_d`, `d! · dim (c_μ M) = ∑_σ χ^μ(σ) χ_M(σ)`: the
dimension of `c_μ M` is the multiplicity of the Specht character `χ^μ` in the character of `M`. -/
theorem factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizer [FiniteDimensional k M]
    (μ : d.Partition) :
    (d.factorial : k) * finrank k (LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))) =
      ∑ σ, (spechtChar μ σ : k) * ρ.character σ := by
  have hd : ((YoungDiagram.ofPartition μ).card.factorial : k) = d.factorial := by
    rw [YoungDiagram.card_ofPartition]
  rw [Nat.Partition.youngSymmetrizer_def, asAlgebraHom_domCongr, ← hd,
    factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizerOver]
  -- reindex the sum from the labels of the diagram to `Fin d`
  refine Fintype.sum_equiv (finCongr (YoungDiagram.card_ofPartition μ)).permCongrHom.toEquiv _ _
    fun τ => ?_
  have hτ : (finCongr (YoungDiagram.card_ofPartition μ).symm).permCongr
      ((finCongr (YoungDiagram.card_ofPartition μ)).permCongr τ) = τ := by
    ext i
    simp
  rw [← map_intCast (algebraMap ℚ k), spechtChar_cast, character_spechtModule_apply,
    ← Algebra.smul_def]
  simp [character, hτ]

/-- **The dimension count.** A finite-dimensional representation `M` of `S_d` has dimension
`∑_μ f^μ dim (c_μ M)`, the sum over the partitions `μ` of `d` of the dimension of the Specht module
`S^μ` times the dimension of the image of its Young symmetrizer. -/
theorem finrank_eq_sum_finrank_spechtModule_mul_finrank_range [FiniteDimensional k M] :
    finrank k M = ∑ μ : d.Partition, finrank ℚ (spechtModule μ) *
      finrank k (LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))) := by
  have hd : (d.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
  apply Nat.cast_injective (R := k)
  refine mul_left_cancel₀ hd ?_
  push_cast
  simp_rw [Finset.mul_sum, mul_left_comm (d.factorial : k),
    factorial_mul_finrank_range_asAlgebraHom_youngSymmetrizer, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  -- column orthogonality leaves only the identity permutation
  have h (σ : Equiv.Perm (Fin d)) := congrArg (Int.cast : ℤ → k)
    (sum_finrank_spechtModule_mul_spechtChar σ)
  push_cast at h
  simp_rw [h, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, char_one]

/-- **The Young-symmetrizer evaluation map** `⨁_μ k[S_d] c_μ ⊗ c_μ M → M`, sending `a ⊗ w` in the
summand of `μ` to `a · w`. It is an isomorphism
(`Representation.youngSymmetrizerEval_bijective`). -/
noncomputable def youngSymmetrizerEval :
    (⨁ μ : d.Partition,
      (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))) ⊗[k]
        LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))) →ₗ[k] M :=
  DirectSum.toModule k d.Partition M fun μ => TensorProduct.lift
    (ρ.asAlgebraHom.toLinearMap.compl₁₂
      ((Ideal.span {μ.youngSymmetrizer k}).subtype.restrictScalars k)
      (LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))).subtype)

/-- The evaluation map sends `a ⊗ w` in the summand of `μ` to `a · w`. -/
@[simp]
theorem youngSymmetrizerEval_lof_tmul (μ : d.Partition)
    (a : (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))))
    (w : LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))) :
    ρ.youngSymmetrizerEval (DirectSum.lof k d.Partition _ μ (a ⊗ₜ w)) =
      ρ.asAlgebraHom (a : MonoidAlgebra k (Equiv.Perm (Fin d))) w := by
  simp [youngSymmetrizerEval]

/-- The image of the Young symmetrizer `c_μ` lies in the image of the evaluation map. -/
private theorem asAlgebraHom_youngSymmetrizer_mem_range_youngSymmetrizerEval (μ : d.Partition)
    (m : M) :
    ρ.asAlgebraHom (μ.youngSymmetrizer k) m ∈ LinearMap.range ρ.youngSymmetrizerEval := by
  have hκ : algebraMap ℚ k ((d.factorial : ℚ) / finrank ℚ (spechtModule μ)) ≠ 0 := by
    rw [map_ne_zero]
    exact div_ne_zero (Nat.cast_ne_zero.mpr d.factorial_ne_zero)
      (Nat.cast_ne_zero.mpr (finrank_spechtModule_pos μ).ne')
  set κ := algebraMap ℚ k ((d.factorial : ℚ) / finrank ℚ (spechtModule μ))
  set c := ρ.asAlgebraHom (μ.youngSymmetrizer k)
  refine ⟨DirectSum.lof k d.Partition _ μ
    (spanSingletonGenerator (μ.youngSymmetrizer k) ⊗ₜ ⟨κ⁻¹ • c m, κ⁻¹ • m, map_smul c _ _⟩), ?_⟩
  rw [youngSymmetrizerEval_lof_tmul, coe_spanSingletonGenerator, map_smul, ← Module.End.mul_apply,
    ← map_mul, μ.youngSymmetrizer_mul_self k, map_smul, LinearMap.smul_apply, smul_smul,
    inv_mul_cancel₀ hκ, one_smul]

/-- **The evaluation map is `S_d`-equivariant**, for the action of `S_d` on the left factors
`k[S_d] c_μ` by left multiplication. -/
theorem youngSymmetrizerEval_comp (σ : Equiv.Perm (Fin d)) :
    ρ.youngSymmetrizerEval ∘ₗ (Representation.directSum fun μ : d.Partition =>
      (ofModule' (k := k) (G := Equiv.Perm (Fin d))
        (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d))))).tprod
      (trivial k (Equiv.Perm (Fin d)) (LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k)))))
        σ = ρ σ ∘ₗ ρ.youngSymmetrizerEval := by
  refine DirectSum.linearMap_ext k fun μ => TensorProduct.ext' fun a w => ?_
  simp [TauCeti.Representation.ofModule'_apply, smul_eq_mul, map_mul]

/-- **The images of the Young symmetrizers generate.** Every vector of a finite-dimensional
representation of `S_d` is a sum of vectors `a · w` with `a ∈ k[S_d] c_μ` and `w ∈ c_μ M`. -/
theorem youngSymmetrizerEval_surjective [FiniteDimensional k M] :
    Function.Surjective ρ.youngSymmetrizerEval := by
  set N := LinearMap.range ρ.youngSymmetrizerEval
  have hN : ∀ σ, N ≤ N.comap (ρ σ) := by
    rintro σ _ ⟨x, rfl⟩
    exact ⟨_, LinearMap.congr_fun (ρ.youngSymmetrizerEval_comp σ) x⟩
  -- every Young symmetrizer kills the quotient by the image, which therefore has dimension zero
  have hzero : finrank k (M ⧸ N) = 0 := by
    rw [(ρ.quotient N hN).finrank_eq_sum_finrank_spechtModule_mul_finrank_range]
    refine Finset.sum_eq_zero fun μ _ => ?_
    suffices h : (ρ.quotient N hN).asAlgebraHom (μ.youngSymmetrizer k) = 0 by
      rw [h, LinearMap.range_zero, finrank_bot, mul_zero]
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := N.mkQ_surjective q
    rw [asAlgebraHom_quotient_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ρ.asAlgebraHom_youngSymmetrizer_mem_range_youngSymmetrizerEval μ m
  have hfin := N.finrank_quotient_add_finrank
  rw [hzero, zero_add] at hfin
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hfin)

/-- The source of the evaluation map has the dimension of `M`, by the dimension count. -/
private theorem finrank_directSum_span_youngSymmetrizer_tensorProduct_range
    [FiniteDimensional k M] :
    finrank k (⨁ μ : d.Partition,
      (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))) ⊗[k]
        LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))) = finrank k M := by
  rw [Module.finrank_directSum, ρ.finrank_eq_sum_finrank_spechtModule_mul_finrank_range]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Module.finrank_tensorProduct, Nat.Partition.finrank_span_youngSymmetrizer]

/-- **The Young-symmetrizer evaluation map is bijective**: every finite-dimensional
representation `M` of `S_d` is `⨁_μ k[S_d] c_μ ⊗ c_μ M`. -/
theorem youngSymmetrizerEval_bijective [FiniteDimensional k M] :
    Function.Bijective ρ.youngSymmetrizerEval := by
  refine ⟨?_, ρ.youngSymmetrizerEval_surjective⟩
  -- Rank-nullity needs an additive group structure on the source. Instance search does not find
  -- one through the tensor product with the ideal `k[S_d] c_μ` as left factor, so supply the one
  -- coming from the field of scalars, which extends the existing additive monoid structure.
  let := Module.addCommMonoidToAddCommGroup k (M := ⨁ μ : d.Partition,
    (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))) ⊗[k]
      LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k)))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ρ.finrank_directSum_span_youngSymmetrizer_tensorProduct_range).mpr
    ρ.youngSymmetrizerEval_surjective

/-- **The Young-symmetrizer decomposition of a representation of `S_d`**: the evaluation map as an
equivalence `⨁_μ k[S_d] c_μ ⊗ c_μ M ≅ M` of representations of `S_d`, which acts on the source by
left multiplication on the factors `k[S_d] c_μ` and trivially on the multiplicity spaces
`c_μ M`. -/
noncomputable def youngSymmetrizerEquiv [FiniteDimensional k M] :
    (Representation.directSum fun μ : d.Partition =>
      (ofModule' (k := k) (G := Equiv.Perm (Fin d))
        (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d))))).tprod
      (trivial k (Equiv.Perm (Fin d))
        (LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))))).Equiv ρ :=
  .mk (LinearEquiv.ofBijective ρ.youngSymmetrizerEval ρ.youngSymmetrizerEval_bijective)
    ρ.youngSymmetrizerEval_comp

/-- The decomposition is the evaluation map. -/
@[simp]
theorem youngSymmetrizerEquiv_apply [FiniteDimensional k M]
    (x : ⨁ μ : d.Partition,
      (Ideal.span {μ.youngSymmetrizer k} : Ideal (MonoidAlgebra k (Equiv.Perm (Fin d)))) ⊗[k]
        LinearMap.range (ρ.asAlgebraHom (μ.youngSymmetrizer k))) :
    ρ.youngSymmetrizerEquiv x = ρ.youngSymmetrizerEval x :=
  (rfl)

end Representation
