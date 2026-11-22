/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective
public import TauCeti.Algebra.WordFiltration.Rees

/-!
# The symmetric-algebra fibre of the PBW Rees algebra

For a Lie algebra free over a commutative ring, quotienting its PBW Rees algebra by the
central parameter gives the symmetric algebra. The quotient map sends `j(x) = ι(x)t`
to the symmetric generator `x`. In particular, it is not ambient evaluation at zero,
which kills `j(x)`.

The comparison composes the generic word-filtration symbol map with the inverse of the
native PBW equivalence `pbwAssociatedGradedEquiv`. Its coefficientwise kernel description
records precisely the loss of one filtration step needed to divide a commutator by the
parameter and then take its symbol. We also record naturality of `reesZeroFiberMap` and
of `reesSpecializationZero` and `reesZeroFiberEquiv` along Lie algebra homomorphisms.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

open TauCeti.Algebra.wordFiltration

private noncomputable def wordReesEquiv : reesAlgebra R L ≃ₐ[R]
    Rees (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap :=
  Subalgebra.equivOfEq _ _ (by
    unfold reesAlgebra Rees
    congr 1
    funext n
    exact pbwFiltration_def R L n)

private theorem coe_wordReesEquiv (p : reesAlgebra R L) :
    (wordReesEquiv R L p : Polynomial (_root_.UniversalEnvelopingAlgebra R L)) = p :=
  (rfl)

private theorem wordReesEquiv_reesParameter :
    wordReesEquiv R L (reesParameter R L) =
      coeffSubalgebra.X
        (TauCeti.Algebra.wordFiltration
          (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap)
        (TauCeti.Algebra.one_mem_wordFiltration _ 1) := by
  apply Subtype.ext
  simp [coe_wordReesEquiv]

section ZeroFiberMap

variable {L} {M : Type w} {N : Type x}
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

/-- The `R`-algebra map on `t = 0` Rees quotients induced by a Lie algebra homomorphism, requiring
no freeness hypothesis on `L` or `M`. -/
noncomputable def reesZeroFiberMap (f : L →ₗ⁅R⁆ M) :
    (reesAlgebra R L ⧸ Ideal.span {reesParameter R L}) →ₐ[R]
      (reesAlgebra R M ⧸ Ideal.span {reesParameter R M}) :=
  Ideal.quotientMapₐ (Ideal.span {reesParameter R M}) ((reesMap R f).restrictScalars R) <|
    Ideal.span_le.mpr <| by
      rintro p (rfl : p = reesParameter R L)
      simp

@[simp]
theorem reesZeroFiberMap_mk (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    reesZeroFiberMap R f (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (reesMap R f p) :=
  (rfl)

@[simp]
theorem reesZeroFiberMap_id :
    reesZeroFiberMap R (LieHom.id : L →ₗ⁅R⁆ L) =
      AlgHom.id R (reesAlgebra R L ⧸ Ideal.span {reesParameter R L}) := by
  ext q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

@[simp]
theorem reesZeroFiberMap_comp (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ N) :
    reesZeroFiberMap R (g.comp f) =
      (reesZeroFiberMap R g).comp (reesZeroFiberMap R f) := by
  ext q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

end ZeroFiberMap

variable [Module.Free R L]

/-- The zero-parameter specialization of the PBW Rees algebra to the symmetric algebra. -/
noncomputable def reesSpecializationZero : reesAlgebra R L →ₐ[R] SymmetricAlgebra R L :=
  (pbwAssociatedGradedEquiv R L).symm.toAlgHom.comp
    ((reesSymbol (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap).comp
      (wordReesEquiv R L).toAlgHom)

/-- A linear Rees generator specializes to the corresponding symmetric generator. -/
@[simp]
theorem reesSpecializationZero_reesGenerator (x : L) :
    reesSpecializationZero R L (reesGenerator R L x) = SymmetricAlgebra.ι R L x := by
  have hj : wordReesEquiv R L (reesGenerator R L x) =
      coeffSubalgebra.monomial
        (TauCeti.Algebra.wordFiltration
          (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap)
        1 (_root_.UniversalEnvelopingAlgebra.ι R x)
        (TauCeti.Algebra.apply_mem_wordFiltration_one _ x) := by
    apply Subtype.ext
    simp [coe_wordReesEquiv]
  simp only [reesSpecializationZero, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [hj, reesSymbol_monomial]
  apply (pbwAssociatedGradedEquiv R L).symm_apply_eq.mpr
  simp [pbwGradedGenerator_apply]

/-- The PBW zero specialization is surjective. -/
theorem reesSpecializationZero_surjective : Function.Surjective (reesSpecializationZero R L) :=
  (pbwAssociatedGradedEquiv R L).symm.surjective.comp
    ((reesSymbol_surjective (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap).comp
      (wordReesEquiv R L).surjective)

/-- A Rees polynomial specializes to zero exactly when every coefficient has lower PBW degree. -/
theorem reesSpecializationZero_eq_zero_iff (p : reesAlgebra R L) :
    reesSpecializationZero R L p = 0 ↔
      ∀ n, (p : Polynomial (_root_.UniversalEnvelopingAlgebra R L)).coeff n ∈
        pbwFiltrationPrevious R L n := by
  simp only [reesSpecializationZero, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    EmbeddingLike.map_eq_zero_iff, reesSymbol_eq_zero_iff, coe_wordReesEquiv,
    pbwFiltrationPrevious_def]

/-- The central Rees parameter specializes to zero. -/
@[simp]
theorem reesSpecializationZero_reesParameter :
    reesSpecializationZero R L (reesParameter R L) = 0 := by
  simp [reesSpecializationZero, wordReesEquiv_reesParameter]

/-- The kernel of PBW zero specialization is the ideal generated by the central parameter. -/
theorem ker_reesSpecializationZero :
    RingHom.ker (reesSpecializationZero R L : reesAlgebra R L →+* SymmetricAlgebra R L) =
      Ideal.span {reesParameter R L} := by
  ext p
  simp only [RingHom.mem_ker, AlgHom.coe_toRingHom, reesSpecializationZero,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, EmbeddingLike.map_eq_zero_iff]
  rw [reesSymbol_eq_zero_iff_exists_X_mul_eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨(wordReesEquiv R L).symm q, (wordReesEquiv R L).injective ?_⟩
    simpa [wordReesEquiv_reesParameter, (coeffSubalgebra.commute_X _ _ q).eq] using hq
  · rintro ⟨q, rfl⟩
    refine ⟨wordReesEquiv R L q, ?_⟩
    simp [wordReesEquiv_reesParameter, (coeffSubalgebra.commute_X _ _ _).eq]

/-- An element of `reesAlgebra R L` specializes to `0` in `SymmetricAlgebra R L` if and only if it
is divisible by `reesParameter R L`. -/
theorem reesSpecializationZero_eq_zero_iff_exists_reesParameter_mul (p : reesAlgebra R L) :
    reesSpecializationZero R L p = 0 ↔ ∃ q : reesAlgebra R L, reesParameter R L * q = p := by
  rw [← AlgHom.coe_toRingHom, ← RingHom.mem_ker, ker_reesSpecializationZero,
    Ideal.mem_span_singleton']
  exact exists_congr fun q ↦ by rw [(coeffSubalgebra.commute_X _ _ q).eq]

/-- The PBW zero fibre is canonically the symmetric algebra, without a choice of basis. -/
noncomputable def reesZeroFiberEquiv :
    (reesAlgebra R L ⧸ Ideal.span {reesParameter R L}) ≃ₐ[R] SymmetricAlgebra R L :=
  (Ideal.quotientEquivAlgOfEq R (ker_reesSpecializationZero R L).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (reesSpecializationZero_surjective R L))

/-- The zero-fibre equivalence is induced by zero specialization. -/
@[simp]
theorem reesZeroFiberEquiv_mk (p : reesAlgebra R L) :
    reesZeroFiberEquiv R L (Ideal.Quotient.mk _ p) = reesSpecializationZero R L p := by
  exact (congrArg
    (Ideal.quotientKerAlgEquivOfSurjective (reesSpecializationZero_surjective R L))
    (Ideal.quotientEquivAlgOfEq_mk R (ker_reesSpecializationZero R L).symm p)).trans
      (Ideal.quotientKerAlgEquivOfSurjective_mk (reesSpecializationZero_surjective R L) p)

/-- The inverse comparison lifts each symmetric generator to the class of its Rees generator. -/
@[simp]
theorem reesZeroFiberEquiv_symm_ι (x : L) :
    (reesZeroFiberEquiv R L).symm (SymmetricAlgebra.ι R L x) =
      Ideal.Quotient.mk _ (reesGenerator R L x) := by
  apply (reesZeroFiberEquiv R L).symm_apply_eq.mpr
  simp

section Functoriality

variable {L} {M : Type w} [LieRing M] [LieAlgebra R M] [Module.Free R M]

/-- **Naturality of `reesSpecializationZero`.** For Lie algebras free as `R`-modules, zero
specialization intertwines `reesMap R f` with `SymmetricAlgebra.map R f.toLinearMap`. -/
theorem reesSpecializationZero_comp_reesMap (f : L →ₗ⁅R⁆ M) :
    (reesSpecializationZero R M).comp ((reesMap R f).restrictScalars R) =
      (SymmetricAlgebra.map R f.toLinearMap).comp (reesSpecializationZero R L) :=
  reesAlgebra_algHom_ext (by simp) (fun x ↦ by simp)

@[simp]
theorem reesSpecializationZero_reesMap (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    reesSpecializationZero R M (reesMap R f p) =
      SymmetricAlgebra.map R f.toLinearMap (reesSpecializationZero R L p) :=
  AlgHom.congr_fun (reesSpecializationZero_comp_reesMap R f) p

/-- **Naturality of `reesZeroFiberEquiv`.** -/
@[simp]
theorem reesZeroFiberEquiv_map (f : L →ₗ⁅R⁆ M)
    (q : reesAlgebra R L ⧸ Ideal.span {reesParameter R L}) :
    reesZeroFiberEquiv R M (reesZeroFiberMap R f q) =
      SymmetricAlgebra.map R f.toLinearMap (reesZeroFiberEquiv R L q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

end Functoriality

end TauCeti.UniversalEnvelopingAlgebra
