/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.LinearAlgebra.Matrix.Nonsingular.Basic
public import TauCeti.LinearAlgebra.Matrix.Trace.Basic
public import TauCeti.RingTheory.Semisimple.Trace.Form

/-!
# The regular discriminant of a possibly noncommutative algebra

Let `S` be an algebra over a commutative ring `R`, not necessarily commutative. The *regular
discriminant* of a finite family `b` in `S` is the Gram determinant `det (tr (L_{b i * b j}))` of
the regular trace form `Algebra.regularTraceForm R S`, where `tr (L_x)` is the trace over `R` of
left multiplication by `x` on all of `S`. It is not the reduced trace of a central simple algebra:
for `S = ℚ` the regular trace of `1` is `1`, and for `S = M_n(ℚ)` it is `n²`. For commutative `S`
the regular discriminant is Mathlib's `Algebra.discr`.

The regular discriminant of a `ℤ`-basis of an order `O` in a finite-dimensional division algebra
over `ℚ` is the invariant in Masser and Wüstholz's class-index bound: every full `O`-stable lattice
in `Dᵉ` contains a copy of `Oᵉ` whose index is bounded in terms of `|disc O|`. This file
establishes what that bound uses about it. The discriminant does not depend on the choice of
`ℤ`-basis; passing to a subring of finite index `I` multiplies it by `I ^ 2`; it is the image of
the regular discriminant over `ℚ` of the same family, the trace being taken on the whole rational
algebra; and it is nonzero when that rational algebra is semisimple, for instance a division
algebra. Semisimplicity cannot be dropped: in `ℤ[ε] = ℤ[X] / (X²)` with basis `1, ε` the regular
trace form has Gram matrix `diag(2, 0)`, so the discriminant vanishes. Its sign is not fixed:
`ℤ[i]` with basis `1, i` has regular discriminant `-4`.

## Main definitions

* `Algebra.regularDiscr R b`: the determinant of the matrix `tr (L_{b i * b j})` of regular traces,
  for a finite family `b` in `S`.

## Main results

* `Algebra.regularDiscr_eq_discr`: for commutative `S` it is `Algebra.discr R b`.
* `Algebra.regularDiscr_of_matrix_vecMul`: replacing `b` by the combinations `b ᵥ* P` multiplies
  the regular discriminant by `det P ^ 2`.
* `Algebra.regularDiscr_eq_regularDiscr`: two `ℤ`-bases have the same regular discriminant.
* `Algebra.regularTraceForm_algHom_apply`: an injective algebra map between finite free algebras of
  the same rank preserves the regular trace form, although it need not be surjective.
* `Subring.regularDiscr_eq_relIndex_sq_mul`: if `O' ≤ O` are subrings with `ℤ`-bases of the same
  size, the regular discriminant of `O'` is `[O : O'] ^ 2` times that of `O`.
* `Algebra.algebraMap_regularDiscr`: if `S` is a finite free `R`-algebra embedded in an algebra `E`
  over the fraction field `K` of `R` so as to span it, the regular discriminant of a family in `S`
  maps to its regular discriminant in `E` over `K`.
* `Algebra.regularDiscr_ne_zero`: in that situation, if `K` has characteristic zero and `E` is
  semisimple, the regular discriminant of every `R`-basis of `S` is nonzero.

## References

* D. W. Masser and G. Wüstholz, *Factorization estimates for abelian varieties*, Publ. Math.
  IHÉS 81 (1995), §2, where the regular-trace discriminant of an order enters the class-index
  lemma.

The basis-change results follow Mathlib's `Algebra.discr_of_matrix_vecMul` and
`Algebra.discr_eq_discr` for commutative algebras.
-/

public section

open LinearMap Matrix Module Submodule

namespace Algebra

section Basic

variable (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The **regular discriminant** of a finite family `b` in an `R`-algebra `S`, which need not be
commutative: the determinant of the matrix `tr (L_{b i * b j})` of the regular trace form, where
`tr (L_x)` is the trace over `R` of left multiplication by `x` on `S`. For commutative `S` this is
`Algebra.discr R b` (`Algebra.regularDiscr_eq_discr`). -/
noncomputable def regularDiscr (b : ι → S) : R :=
  (Matrix.of fun i j => regularTraceForm R S (b i) (b j)).det

theorem regularDiscr_def (b : ι → S) :
    regularDiscr R b = (Matrix.of fun i j => regularTraceForm R S (b i) (b j)).det :=
  (rfl)

/-- The regular discriminant of a basis is the determinant of the matrix of the regular trace form
in that basis. -/
theorem regularDiscr_eq_det_toMatrix_regularTraceForm (b : Basis ι R S) :
    regularDiscr R b = (BilinForm.toMatrix b (regularTraceForm R S)).det := by
  rw [regularDiscr_def]
  congr 1
  exact Matrix.ext fun i j => by rw [of_apply, BilinForm.toMatrix_apply]

/-- For a commutative algebra the regular discriminant is Mathlib's discriminant. -/
theorem regularDiscr_eq_discr {S : Type*} [CommRing S] [Algebra R S] (b : ι → S) :
    regularDiscr R b = discr R b := by
  rw [regularDiscr_def, discr_def, regularTraceForm_eq_traceForm, traceMatrix]

variable {R}

/-- Reindexing a family does not change its regular discriminant. -/
theorem regularDiscr_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : ι → S)
    (e : ι ≃ ι') : regularDiscr R (b ∘ e.symm) = regularDiscr R b := by
  rw [regularDiscr_def, regularDiscr_def, ← det_reindex_self e]
  exact congrArg det (Matrix.ext fun i j => by simp)

/-- Replacing a family `b` by the combinations `b ᵥ* P`, with `P` a matrix over `R`, multiplies the
regular discriminant by `det P ^ 2`. -/
theorem regularDiscr_of_matrix_vecMul (b : ι → S) (P : Matrix ι ι R) :
    regularDiscr R (b ᵥ* P.map (algebraMap R S)) = P.det ^ 2 * regularDiscr R b := by
  have hcol (j : ι) : (b ᵥ* P.map (algebraMap R S)) j = ∑ i, P i j • b i := by
    simp [vecMul, dotProduct, Algebra.smul_def, Algebra.commutes]
  have hgram : (Matrix.of fun i j => regularTraceForm R S ((b ᵥ* P.map (algebraMap R S)) i)
      ((b ᵥ* P.map (algebraMap R S)) j)) =
      Pᵀ * (Matrix.of fun i j => regularTraceForm R S (b i) (b j)) * P := by
    refine Matrix.ext fun i j => ?_
    simp only [hcol, of_apply, Matrix.mul_apply, transpose_apply, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [regularDiscr_def, hgram, det_mul, det_mul, det_transpose, regularDiscr_def]
  ring

/-- The regular discriminant of a family `v` is `det (b.toMatrix v) ^ 2` times that of a basis `b`.
-/
theorem regularDiscr_eq_det_toMatrix_sq_mul (b : Basis ι R S) (v : ι → S) :
    regularDiscr R v = (b.toMatrix v).det ^ 2 * regularDiscr R b := by
  rw [← regularDiscr_of_matrix_vecMul, Basis.toMatrix_map_vecMul]

/-- **Two `ℤ`-bases have the same regular discriminant.** -/
theorem regularDiscr_eq_regularDiscr (b b' : Basis ι ℤ S) :
    regularDiscr ℤ b = regularDiscr ℤ b' := by
  have hu : IsUnit (b'.toMatrix b).det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl ℤ S) b b'
  rw [regularDiscr_eq_det_toMatrix_sq_mul b', Int.isUnit_sq hu, one_mul]

section AlgHom

variable {S' : Type*} [Ring S'] [Algebra R S']

omit [Fintype ι] [DecidableEq ι] in
/-- The regular trace form is preserved by an injective algebra map between algebras with bases of
the same finite size. -/
private theorem regularTraceForm_algHom_apply_of_basis [Finite ι] (f : S' →ₐ[R] S)
    (hf : Function.Injective f) (b' : Basis ι R S') (b : Basis ι R S) (x y : S') :
    regularTraceForm R S (f x) (f y) = regularTraceForm R S' x y := by
  classical
  have := Fintype.ofFinite ι
  have hP : b.toMatrix (f ∘ b') = LinearMap.toMatrix b' b f.toLinearMap := by
    ext i j
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Function.comp_apply,
      AlgHom.toLinearMap_apply]
  have hdet := b.det_mem_nonZeroDivisors
    (b'.linearIndependent.map' f.toLinearMap (LinearMap.ker_eq_bot.2 hf))
  rw [Basis.det_apply, AlgHom.coe_toLinearMap, hP] at hdet
  rw [regularTraceForm_apply, regularTraceForm_apply, ← map_mul,
    LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace R b']
  refine Matrix.trace_eq_of_mul_eq_mul hdet ?_
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  congr 1
  ext z
  simp [mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- **An injective algebra map between finite free algebras of the same rank preserves the regular
trace form**, although its image may be a proper sublattice: for `x` in `S'`, left multiplication
by `f x` on `S` and by `x` on `S'` have the same trace. -/
theorem regularTraceForm_algHom_apply [Module.Free R S] [Module.Finite R S] [Module.Free R S']
    [Module.Finite R S'] (f : S' →ₐ[R] S) (hf : Function.Injective f)
    (hrank : finrank R S' = finrank R S) (x y : S') :
    regularTraceForm R S (f x) (f y) = regularTraceForm R S' x y := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  exact regularTraceForm_algHom_apply_of_basis f hf (finBasisOfFinrankEq R S' hrank)
    (finBasis R S) x y

/-- The regular discriminant of a basis `b'` of `S'` is `det (b.toMatrix (f ∘ b')) ^ 2` times that
of a basis `b` of `S`, for an injective algebra map `f : S' → S`. -/
theorem regularDiscr_eq_det_toMatrix_comp_sq_mul (f : S' →ₐ[R] S) (hf : Function.Injective f)
    (b' : Basis ι R S') (b : Basis ι R S) :
    regularDiscr R b' = (b.toMatrix (f ∘ b')).det ^ 2 * regularDiscr R b := by
  rw [← regularDiscr_eq_det_toMatrix_sq_mul, regularDiscr_def, regularDiscr_def]
  simp only [Function.comp_apply, regularTraceForm_algHom_apply_of_basis f hf b' b]

end AlgHom

end Basic

section FractionRing

variable {R K S E : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Ring S] [Algebra R S] [Ring E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  {ι : Type*}

/-- The `K`-basis of `E` formed by the image of an `R`-basis of `S` under an injective algebra map
whose image spans `E`. -/
private noncomputable def basisOfSpan (f : S →ₐ[R] E) (hf : Function.Injective f)
    (hspan : span K (Set.range f) = ⊤) (b : Basis ι R S) : Basis ι K E :=
  .mk ((LinearIndependent.iff_fractionRing R K).1 (b.linearIndependent.map'
    f.toLinearMap (LinearMap.ker_eq_bot.2 hf))) <| by
      rw [top_le_iff, ← hspan, Set.range_comp, ← span_span_of_tower R, ← Submodule.map_span,
        b.span_eq, Submodule.map_top, LinearMap.coe_range, AlgHom.coe_toLinearMap]

private theorem basisOfSpan_apply (f : S →ₐ[R] E) (hf : Function.Injective f)
    (hspan : span K (Set.range f) = ⊤) (b : Basis ι R S) (i : ι) :
    basisOfSpan f hf hspan b i = f (b i) := by
  simp [basisOfSpan]

private theorem basisOfSpan_repr_apply [Finite ι] (f : S →ₐ[R] E) (hf : Function.Injective f)
    (hspan : span K (Set.range f) = ⊤) (b : Basis ι R S) (s : S) (i : ι) :
    (basisOfSpan f hf hspan b).repr (f s) i = algebraMap R K (b.repr s i) := by
  have := Fintype.ofFinite ι
  have hs : f s = ∑ j, algebraMap R K (b.repr s j) • basisOfSpan f hf hspan b j := by
    calc f s = f (∑ j, b.repr s j • b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, basisOfSpan_apply, algebraMap_smul]
  rw [hs, Basis.repr_sum_self]

/-- **The regular trace of an order is the rational regular trace.** Let `S` be a finite free
`R`-algebra and `f : S → E` an injective algebra map into an algebra `E` over the fraction field `K`
of `R`, whose image spans `E` over `K`. Then the regular trace form of `S` over `R` maps to that of
`E` over `K`. -/
theorem algebraMap_regularTraceForm [Module.Free R S] [Module.Finite R S] (f : S →ₐ[R] E)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) (x y : S) :
    algebraMap R K (regularTraceForm R S x y) = regularTraceForm K E (f x) (f y) := by
  classical
  let b := Free.chooseBasis R S
  let bK := basisOfSpan f hf hspan b
  have hmat : LinearMap.toMatrix bK bK (lmul K E (f (x * y))) =
      (LinearMap.toMatrix b b (lmul R S (x * y))).map (algebraMap R K) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      basisOfSpan_apply, coe_lmul_eq_mul, coe_lmul_eq_mul, LinearMap.mul_apply',
      LinearMap.mul_apply', ← map_mul, basisOfSpan_repr_apply]
  rw [regularTraceForm_apply, regularTraceForm_apply, ← map_mul,
    LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace K bK, hmat,
    AddMonoidHom.map_trace]

variable [Fintype ι] [DecidableEq ι]

/-- In the situation of `Algebra.algebraMap_regularTraceForm`, the regular discriminant over `R` of
a family in `S` maps to the regular discriminant over `K` of its image in `E`. -/
theorem algebraMap_regularDiscr [Module.Free R S] [Module.Finite R S] (f : S →ₐ[R] E)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) (b : ι → S) :
    algebraMap R K (regularDiscr R b) = regularDiscr K (f ∘ b) := by
  rw [regularDiscr_def, regularDiscr_def, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, of_apply,
    algebraMap_regularTraceForm f hf hspan, Function.comp_apply, Function.comp_apply]

/-- **The regular discriminant of an order in a semisimple algebra is nonzero.** Let `S` be an
`R`-algebra with a finite basis `b`, embedded by an injective algebra map `f` in an algebra `E` over
the fraction field `K` of `R` so that its image spans `E`. If `K` has characteristic zero and `E`
is semisimple, then the regular discriminant of `b` is nonzero. This applies to an order in a
finite-dimensional division algebra over `ℚ`. -/
theorem regularDiscr_ne_zero [CharZero K] [IsSemisimpleRing E] (f : S →ₐ[R] E)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) (b : Basis ι R S) :
    regularDiscr R b ≠ 0 := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  let bK := basisOfSpan f hf hspan b
  have := Module.Finite.of_basis bK
  have hK : regularDiscr K (f ∘ b) ≠ 0 := by
    have hb : f ∘ b = bK := funext fun i => (basisOfSpan_apply f hf hspan b i).symm
    rw [hb, regularDiscr_eq_det_toMatrix_regularTraceForm,
      ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
    exact TauCeti.nondegenerate_regularTraceForm
  rw [← algebraMap_regularDiscr f hf hspan] at hK
  exact fun h => hK (by rw [h, map_zero])

end FractionRing

end Algebra

namespace Subring

variable {D : Type*} [Ring D] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The regular discriminant of a subring of finite index.** If `O' ≤ O` are subrings of a ring
with `ℤ`-bases of the same size, the regular discriminant of `O'` is `[O : O'] ^ 2` times that of
`O`. -/
theorem regularDiscr_eq_relIndex_sq_mul {O' O : Subring D} (h : O' ≤ O) (b' : Basis ι ℤ O')
    (b : Basis ι ℤ O) :
    Algebra.regularDiscr ℤ b' =
      (O'.toAddSubgroup.relIndex O.toAddSubgroup : ℤ) ^ 2 * Algebra.regularDiscr ℤ b := by
  let f : O' →ₐ[ℤ] O := (Subring.inclusion h).toIntAlgHom
  have hidx : O'.toAddSubgroup.relIndex O.toAddSubgroup = (b.toMatrix (f ∘ b')).det.natAbs := by
    rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h b' b]
    -- `Basis.det` is the determinant of `Basis.toMatrix`, and `O` and `O'` are their own
    -- `ℤ`-submodules `O.toAddSubgroup.toIntSubmodule` up to definitional unfolding
    rfl
  rw [Algebra.regularDiscr_eq_det_toMatrix_comp_sq_mul f (Subring.inclusion_injective h) b' b,
    hidx, Int.natCast_natAbs, sq_abs]

end Subring
