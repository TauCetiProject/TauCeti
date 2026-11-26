/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.LinearAlgebra.Submodule.Zeta
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.GeneralizedIndex

/-!
# Lattices in the finite adeles of a CM field, their discriminants, and sums over sublattices

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô` the integral ones, `κ` a finite set and
`x ↦ conj x` the complex conjugation, which acts on `𝔸_f` place by place
(`NumberField.IsCMField.finiteAdeleConj`). An `Ô`-submodule `L` of `𝔸_f^κ` is a *lattice of rank
`r`* if it is the `Ô`-span of the columns of `B = x a`, with `x` a `κ × r` matrix over `E` with
independent columns and `a ∈ GL_r(𝔸_f)` (`NumberField.IsCMField.IsLatticeOfRank`). Its
*discriminant* is `d_r(L) = [det(B^*B)]^(1/2)`, with `B^*` the conjugate transpose and `[·]` the
generalised index (`NumberField.IsCMField.discriminant`); it does not depend on the choice of `B`,
because two such matrices spanning `L` differ by a matrix in `GL_r(Ô)`, whose determinant has
index `1`.

The results are the parts (a)–(d) of section 1.1 of the roadmap
`ShortGRH/RemainingAndMainTermsOfSecondMoments`, except the statements on saturated lattices in
(a).

* (b) An `Ô`-submodule `M` of finite index of a lattice `L` of rank `r` is a lattice of rank `r`,
  and `d_r(M) = d_r(L)·[L : M]` (`NumberField.IsCMField.IsLatticeOfRank.of_le`). In the
  coordinates of a basis `B` of `L`, `M` is a submodule of finite index of `Ô^r`; since the ideals
  of finite index of `Ô` are principal, it is the image of a lower triangular matrix `A` with
  `[Ô^r : M] = ∏ᵢ [Ô : (A i i)] = [det A]`, so `B A` is a basis of `M`.
* (c) `∑_{M ⊂ L} [L : M]^(-(r+μ)) ≤ ζ_Ô(μ)^r` over the submodules of finite index of a lattice of
  rank `r`, with `ζ_Ô(μ) = ∑_I [Ô : I]^(-μ)` over the ideals of finite index
  (`NumberField.IsCMField.IsLatticeOfRank.submoduleZeta_le`), from (d), which is
  `Module.submoduleZeta_pi_le` together with
  `IsDedekindDomain.FiniteAdeleRing.isPrincipal_of_cardQuot_ne_zero`.

The transport of finite adeles along a field isomorphism preserves the integral finite adeles
(`TauCeti.GlobalNumberFields.finiteAdeleEquiv_mem_integralAdeles_iff`), so the generalised index
is invariant under complex conjugation.

## Main declarations

* `NumberField.IsCMField.finiteAdeleConj`: complex conjugation on the finite adeles.
* `NumberField.IsCMField.gramDet`: the Gram determinant `det(B^*B)` of an adelic matrix.
* `NumberField.IsCMField.IsLatticeOfRank`, `NumberField.IsCMField.discriminant`: lattices of rank
  `r` in `𝔸_f^κ` and their discriminants.
* `NumberField.IsCMField.discriminant_span_col`: the discriminant computed from any basis.
* `NumberField.IsCMField.IsLatticeOfRank.discriminant_pos`: the discriminant is positive.
* `NumberField.IsCMField.IsLatticeOfRank.of_le`: part (b).
* `NumberField.IsCMField.IsLatticeOfRank.submoduleZeta_le`: part (c).

## References

* E. Hey, *Analytische Zahlentheorie in Systemen hyperkomplexer Zahlen*, Dissertation,
  Göttingen, 1929.

## Attribution

`NumberField.IsCMField.IsLatticeOfRank`, `NumberField.IsCMField.discriminant`,
`NumberField.IsCMField.IsLatticeOfRank.of_le` and
`NumberField.IsCMField.IsLatticeOfRank.submoduleZeta_le` are adapted from
`New.Filling.IsLatticeOfRank`, `New.Filling.discriminant`,
`New.Filling.IsLatticeOfRank.of_le_and_discriminant_eq_mul_index` and
`New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le` in the file
`src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). There `E` is
also assumed to contain a primitive root of unity of order `5040`; nothing here needs it.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.FiniteAdeleRing
open Matrix
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Transport of finite adeles along a field isomorphism carries integral finite adeles to
integral finite adeles: it is continuous, it carries the dense image of `𝓞_K` into `𝓞_L`, and the
integral finite adeles are closed. -/
theorem finiteAdeleEquiv_mem_integralAdeles (e : K ≃+* L) {x : 𝔸ᶠ[K]}
    (hx : x ∈ integralAdeles (𝓞 K) K) :
    finiteAdeleEquiv K L e x ∈ integralAdeles (𝓞 L) L := by
  have h_closed : IsClosed
      {y : integralAdeles (𝓞 K) K | finiteAdeleEquiv K L e y ∈ integralAdeles (𝓞 L) L} :=
    (isClosed_integralAdeles (𝓞 L) L).preimage
      ((continuous_finiteAdeleEquiv K L e).comp continuous_subtypeVal)
  refine (denseRange_algebraMap_integralAdeles (𝓞 K) K).induction_on
    (p := fun y : integralAdeles (𝓞 K) K ↦
      finiteAdeleEquiv K L e y ∈ integralAdeles (𝓞 L) L) ⟨x, hx⟩ h_closed fun r ↦ ?_
  have hr : IsIntegral ℤ (e r) := (RingOfIntegers.isIntegral_coe r).map e.toRingHom.toIntAlgHom
  change finiteAdeleEquiv K L e (algebraMap K 𝔸ᶠ[K] (r : K)) ∈ _
  rw [finiteAdeleEquiv_algebraMap]
  exact (algebraMap_mem_integralAdeles_iff (R := 𝓞 L) (e r)).2 ⟨⟨e r, hr⟩, rfl⟩

/-- Transport of finite adeles along a field isomorphism preserves integrality. -/
theorem finiteAdeleEquiv_mem_integralAdeles_iff (e : K ≃+* L) {x : 𝔸ᶠ[K]} :
    finiteAdeleEquiv K L e x ∈ integralAdeles (𝓞 L) L ↔ x ∈ integralAdeles (𝓞 K) K := by
  refine ⟨fun hx ↦ ?_, finiteAdeleEquiv_mem_integralAdeles e⟩
  simpa [← finiteAdeleEquiv_symm] using finiteAdeleEquiv_mem_integralAdeles e.symm hx

end TauCeti.GlobalNumberFields

namespace NumberField.IsCMField

open TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

variable (E) in
/-- Complex conjugation on the finite adeles of a CM field, acting place by place. -/
def finiteAdeleConj : 𝔸ᶠ[E] ≃+* 𝔸ᶠ[E] :=
  finiteAdeleEquiv E E (complexConj E).toRingEquiv

/-- Complex conjugation on the finite adeles extends that of `E`. -/
@[simp]
theorem finiteAdeleConj_algebraMap (x : E) :
    finiteAdeleConj E (algebraMap E 𝔸ᶠ[E] x) = algebraMap E 𝔸ᶠ[E] (complexConj E x) :=
  finiteAdeleEquiv_algebraMap E E _ x

/-- Complex conjugation preserves the integral finite adeles. -/
theorem finiteAdeleConj_mem_integralAdeles_iff {x : 𝔸ᶠ[E]} :
    finiteAdeleConj E x ∈ integralAdeles (𝓞 E) E ↔ x ∈ integralAdeles (𝓞 E) E :=
  finiteAdeleEquiv_mem_integralAdeles_iff _

/-- The generalised index is invariant under complex conjugation. -/
@[simp]
theorem genIndex_finiteAdeleConj (a : 𝔸ᶠ[E]) : genIndex E (finiteAdeleConj E a) = genIndex E a :=
  genIndex_map _ (fun _ ↦ finiteAdeleConj_mem_integralAdeles_iff) a

variable {κ : Type*} [Fintype κ] {r : ℕ}

/-- The Gram determinant `det(B^*B)` of a matrix `B` over the finite adeles of a CM field, where
`B^*` is the conjugate transpose for complex conjugation. -/
def gramDet (B : Matrix κ (Fin r) 𝔸ᶠ[E]) : 𝔸ᶠ[E] :=
  ((B.map (finiteAdeleConj E))ᵀ * B).det

/-- Changing the columns of `B` by a square matrix `M` multiplies the Gram determinant by
`conj (det M) · det M`. -/
theorem gramDet_mul (B : Matrix κ (Fin r) 𝔸ᶠ[E]) (M : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) :
    gramDet (B * M) = finiteAdeleConj E M.det * gramDet B * M.det := by
  have h_map : (B * M).map (finiteAdeleConj E) =
      B.map (finiteAdeleConj E) * M.map (finiteAdeleConj E) :=
    Matrix.map_mul (f := (finiteAdeleConj E).toRingHom)
  rw [gramDet, gramDet, h_map, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ B, det_mul,
    det_mul, det_transpose, ← mul_assoc]
  congr 2
  exact (RingHom.map_det (finiteAdeleConj E).toRingHom M).symm

/-- Changing the columns of `B` by a square matrix `M` multiplies the generalised index of the
Gram determinant by `[det M]²`. -/
theorem genIndex_gramDet_mul (B : Matrix κ (Fin r) 𝔸ᶠ[E]) (M : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) :
    genIndex E (gramDet (B * M)) = genIndex E M.det ^ 2 * genIndex E (gramDet B) := by
  rw [gramDet_mul, map_mul, map_mul, genIndex_finiteAdeleConj]
  ring

omit [IsCMField E] [Fintype κ] in
/-- If the columns of `C` lie in the `Ô`-span of the columns of `B`, then `C = B U` for a matrix
`U` with integral entries. -/
theorem exists_mul_map_eq_of_span_le {m n : Type*} [Fintype m] {B : Matrix κ m 𝔸ᶠ[E]}
    {C : Matrix κ n 𝔸ᶠ[E]}
    (h : Submodule.span (integralAdeles (𝓞 E) E) (Set.range C.col) ≤
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)) :
    ∃ U : Matrix m n (integralAdeles (𝓞 E) E), B * U.map Subtype.val = C := by
  choose c hc using fun j ↦
    Submodule.mem_span_range_iff_exists_fun _ |>.1 (h (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Matrix.of fun i j ↦ c j i, Matrix.ext fun k j ↦ ?_⟩
  have := congrFun (hc j) k
  simp only [Finset.sum_apply, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, col_apply] at this
  simp only [Matrix.mul_apply, map_apply, of_apply, ← this, mul_comm]

omit [NumberField E] [IsCMField E] in
/-- A matrix over `E` with independent columns has a left inverse. -/
theorem exists_mul_eq_one_of_linearIndependent {x : Matrix κ (Fin r) E}
    (hx : LinearIndependent E x.col) : ∃ l : Matrix (Fin r) κ E, l * x = 1 := by
  classical
  obtain ⟨g, hg⟩ := x.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hx))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' x, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
    LinearMap.toMatrix'_id]

omit [IsCMField E] in
/-- The matrix `x a`, with `x` over `E` with independent columns and `a` invertible over the
finite adeles, has a left inverse. -/
theorem exists_mul_eq_one_of_linearIndependent_of_isUnit {x : Matrix κ (Fin r) E}
    (hx : LinearIndependent E x.col) (a : GL (Fin r) 𝔸ᶠ[E]) :
    ∃ l : Matrix (Fin r) κ 𝔸ᶠ[E],
      l * (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])) = 1 := by
  obtain ⟨l, hl⟩ := exists_mul_eq_one_of_linearIndependent hx
  refine ⟨((a⁻¹ : GL (Fin r) 𝔸ᶠ[E]) : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) *
    l.map (algebraMap E 𝔸ᶠ[E]), ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (l.map _), ← Matrix.map_mul, hl,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  exact a.inv_mul

omit [IsCMField E] in
/-- An integral square matrix with an integral right inverse has a determinant of generalised
index `1`. -/
theorem genIndex_det_map_eq_one {U V : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)}
    (h : U.map Subtype.val * V.map Subtype.val = (1 : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])) :
    genIndex E (U.map Subtype.val).det = 1 := by
  let ι := (integralAdeles (𝓞 E) E).val.toRingHom
  have hUV : U * V = 1 := Matrix.map_injective Subtype.val_injective <| by
    change (U * V).map ι = (1 : Matrix (Fin r) (Fin r) _).map ι
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
    exact h
  have h_unit : IsUnit U.det := .of_mul_eq_one V.det (by rw [← det_mul, hUV, det_one])
  have h_det : (U.map Subtype.val).det = (U.det : 𝔸ᶠ[E]) :=
    (RingHom.map_det ι U).symm
  rw [h_det, genIndex_eq_cardQuot (h_unit.map ι), Ideal.span_singleton_eq_top.2 h_unit,
    Submodule.cardQuot_top, Nat.cast_one]

/-- Two matrices over the finite adeles whose columns span the same `Ô`-submodule, the first with
a left inverse, have Gram determinants of the same generalised index. -/
theorem genIndex_gramDet_eq_of_span_eq {B C : Matrix κ (Fin r) 𝔸ᶠ[E]}
    (hB : ∃ l : Matrix (Fin r) κ 𝔸ᶠ[E], l * B = 1)
    (h : Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col) =
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range C.col)) :
    genIndex E (gramDet B) = genIndex E (gramDet C) := by
  obtain ⟨l, hl⟩ := hB
  obtain ⟨U, rfl⟩ := exists_mul_map_eq_of_span_le h.ge
  obtain ⟨V, hV⟩ := exists_mul_map_eq_of_span_le h.le
  have hUV : U.map Subtype.val * V.map Subtype.val = (1 : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) :=
    calc U.map Subtype.val * V.map Subtype.val
      _ = l * B * (U.map Subtype.val * V.map Subtype.val) := by rw [hl, Matrix.one_mul]
      _ = l * (B * U.map Subtype.val * V.map Subtype.val) := by
        rw [Matrix.mul_assoc l, Matrix.mul_assoc B]
      _ = 1 := by rw [hV, hl]
  rw [genIndex_gramDet_mul, genIndex_det_map_eq_one hUV, one_pow, one_mul]

/-- An `Ô`-submodule `L` of `𝔸_f^κ` is a **lattice of rank `r`** if it is the `Ô`-span of the
columns of `x a`, where `x` is a `κ × r` matrix over the CM field `E` with independent columns (of
rank `r`) and `a ∈ GL_r(𝔸_f)`. -/
def IsLatticeOfRank (r : ℕ) (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) : Prop :=
  ∃ (x : Matrix κ (Fin r) E) (a : GL (Fin r) 𝔸ᶠ[E]), LinearIndependent E x.col ∧
    Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col) = L

open Classical in
/-- The **discriminant** `d_r(L) = [det(B^*B)]^(1/2)` of a lattice `L` of rank `r`, for a basis
`B = x a` of `L` as in `IsLatticeOfRank`; here `[·]` is the generalised index. It does not depend
on the choice of `B` (`discriminant_span_col`). It is `0` if `L` is not a lattice of rank `r`. -/
def discriminant (r : ℕ) (L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])) : ℝ :=
  if h : IsLatticeOfRank r L then
    √(genIndex E (gramDet (h.choose.map (algebraMap E 𝔸ᶠ[E]) *
      (h.choose_spec.choose : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]))) : ℝ)
  else 0

/-- The discriminant of the lattice spanned by the columns of `x a` is `[det((x a)^*(x a))]^(1/2)`.
-/
theorem discriminant_span_col {x : Matrix κ (Fin r) E} (hx : LinearIndependent E x.col)
    (a : GL (Fin r) 𝔸ᶠ[E]) :
    discriminant r (Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)) =
      √(genIndex E (gramDet (x.map (algebraMap E 𝔸ᶠ[E]) *
        (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]))) : ℝ) := by
  have hL : IsLatticeOfRank r (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])).col)) :=
    ⟨x, a, hx, rfl⟩
  rw [discriminant, dite_eq_left hL]
  obtain ⟨hy, h_span⟩ := hL.choose_spec.choose_spec
  rw [genIndex_gramDet_eq_of_span_eq
    (exists_mul_eq_one_of_linearIndependent_of_isUnit hy hL.choose_spec.choose) h_span]

open ComplexOrder in
/-- The Gram determinant `det(x^*x)` of a matrix `x` over the CM field `E` with independent
columns is not zero: at a complex embedding it is the Gram determinant of independent vectors for a
positive definite hermitian form. -/
theorem det_gram_ne_zero {x : Matrix κ (Fin r) E} (hx : LinearIndependent E x.col) :
    ((x.map (complexConj E))ᵀ * x).det ≠ 0 := by
  classical
  obtain ⟨l, hl⟩ := exists_mul_eq_one_of_linearIndependent hx
  let φ : E →+* ℂ := Classical.choice inferInstance
  have h_map : ((x.map (complexConj E))ᵀ * x).map φ = (x.map φ)ᴴ * x.map φ := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [conjTranspose_apply]
  intro h_zero
  obtain ⟨v, hv, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.2
    (show ((x.map φ)ᴴ * x.map φ).det = 0 by
      rw [← h_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h_zero, map_zero])
  rw [conjTranspose_mul_self_mulVec_eq_zero] at hv_zero
  refine hv ?_
  have h_inv : l.map φ * x.map φ = 1 := by
    rw [← Matrix.map_mul, hl, Matrix.map_one _ (map_zero φ) (map_one φ)]
  rw [← Matrix.one_mulVec v, ← h_inv, ← Matrix.mulVec_mulVec, hv_zero, Matrix.mulVec_zero]

/-- The discriminant of a lattice of rank `r` is positive. -/
theorem IsLatticeOfRank.discriminant_pos {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hL : IsLatticeOfRank r L) : 0 < discriminant r L := by
  obtain ⟨x, a, hx, rfl⟩ := hL
  have h_gram : gramDet (x.map (algebraMap E 𝔸ᶠ[E])) =
      algebraMap E 𝔸ᶠ[E] ((x.map (complexConj E))ᵀ * x).det := by
    have h_conj : (x.map (algebraMap E 𝔸ᶠ[E])).map (finiteAdeleConj E) =
        (x.map (complexConj E)).map (algebraMap E 𝔸ᶠ[E]) := by
      ext i j : 1
      simp
    rw [gramDet, h_conj, ← Matrix.transpose_map, ← Matrix.map_mul, RingHom.map_det]
    rfl
  rw [discriminant_span_col hx, genIndex_gramDet_mul, h_gram, genIndex_algebraMap]
  refine Real.sqrt_pos.2 (Rat.cast_pos.2 (mul_pos (pow_pos (genIndex_units_pos a.det) 2) ?_))
  exact abs_pos.2 ((Algebra.norm_ne_zero_iff).2 (det_gram_ne_zero hx))

/-- The `Ô`-linear map `Ô^r → 𝔸_f^κ` sending `c` to `∑ⱼ cⱼ Bⱼ`, for the columns `Bⱼ` of `B`. -/
private abbrev colMap (B : Matrix κ (Fin r) 𝔸ᶠ[E]) :
    (Fin r → integralAdeles (𝓞 E) E) →ₗ[integralAdeles (𝓞 E) E] κ → 𝔸ᶠ[E] :=
  Fintype.linearCombination (integralAdeles (𝓞 E) E) B.col

omit [IsCMField E] [Fintype κ] in
private theorem colMap_apply (B : Matrix κ (Fin r) 𝔸ᶠ[E]) (c : Fin r → integralAdeles (𝓞 E) E) :
    colMap B c = B *ᵥ fun j ↦ (c j : 𝔸ᶠ[E]) := by
  funext k
  simp [Fintype.linearCombination_apply, Finset.sum_apply, Subalgebra.smul_def, mulVec,
    dotProduct, mul_comm]

omit [IsCMField E] [Fintype κ] in
private theorem colMap_col (B : Matrix κ (Fin r) 𝔸ᶠ[E])
    (A : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)) (j : Fin r) :
    colMap B (A.col j) = (B * A.map Subtype.val).col j := by
  rw [colMap_apply]
  funext k
  simp [mulVec, dotProduct, Matrix.mul_apply]

omit [IsCMField E] [Fintype κ] in
/-- In the coordinates of `B`, the columns of `B A` span the image of the columns of `A`. -/
private theorem map_colMap_span_col (B : Matrix κ (Fin r) 𝔸ᶠ[E])
    (A : Matrix (Fin r) (Fin r) (integralAdeles (𝓞 E) E)) :
    (LinearMap.range A.mulVecLin).map (colMap B) =
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range (B * A.map Subtype.val).col) := by
  rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
  congr 2
  exact funext (colMap_col B A)

omit [IsCMField E] in
/-- A diagonal entry of a triangular basis matrix of a submodule of finite index of `Ô^r`
generates an ideal of finite index, so it is a unit of the finite adeles. -/
private theorem isUnit_coe_of_cardQuot_ne_zero {g : integralAdeles (𝓞 E) E}
    (hg : (Ideal.span {g}).cardQuot ≠ 0) : IsUnit (g : 𝔸ᶠ[E]) := by
  obtain ⟨g', hg', h_eq⟩ := exists_eq_span_singleton_of_cardQuot_ne_zero hg
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (h_eq ▸ Ideal.mem_span_singleton_self g')
  refine isUnit_of_mul_isUnit_right (x := (d : 𝔸ᶠ[E])) ?_
  rw [← Subalgebra.coe_mul, hd]
  exact hg'

omit [IsCMField E] [Fintype κ] in
/-- Let `B` be a matrix over the finite adeles, and `M` an `Ô`-submodule of finite index of the
`Ô`-span of its columns. Then `M` is spanned by the columns of `B A` for a
square matrix `A` with invertible determinant, and `[det A]` is the index of `M`. -/
theorem exists_span_col_mul_eq {B : Matrix κ (Fin r) 𝔸ᶠ[E]}
    {M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hM : M ≤ Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col))
    (h_index : M.toAddSubgroup.relIndex
      (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup ≠ 0) :
    ∃ A : Matrix (Fin r) (Fin r) 𝔸ᶠ[E], IsUnit A.det ∧
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range (B * A).col) = M ∧
      genIndex E A.det = M.toAddSubgroup.relIndex
        (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup := by
  -- Pull `M` back to `Ô^r` along the coordinates of `B` and take a triangular basis there.
  have h_range : LinearMap.range (colMap B) =
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col) :=
    Fintype.range_linearCombination _ _
  have h_comap : (M.comap (colMap B)).cardQuot = M.toAddSubgroup.relIndex
      (Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col)).toAddSubgroup := by
    rw [← h_range]
    exact M.toAddSubgroup.index_comap (colMap B).toAddMonoidHom
  obtain ⟨A, hA_tri, hA_range, hA_index⟩ :=
    Submodule.exists_isLowerTriangular_range_mulVecLin_eq
      (fun I hI ↦ isPrincipal_of_cardQuot_ne_zero hI) _ (h_comap.trans_ne h_index)
  have h_entry (i : Fin r) : (Ideal.span {A i i}).cardQuot ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (hA_index ▸ h_comap ▸ h_index) i (Finset.mem_univ i)
  have h_det : (A.map Subtype.val).det = ∏ i, (A i i : 𝔸ᶠ[E]) := by
    change ((integralAdeles (𝓞 E) E).val.toRingHom.mapMatrix A).det = _
    rw [← RingHom.map_det, det_of_isLowerTriangular _ hA_tri, map_prod]
    rfl
  refine ⟨A.map Subtype.val, ?_, ?_, ?_⟩
  · rw [h_det]
    exact IsUnit.prod_univ_iff.2 fun i ↦ isUnit_coe_of_cardQuot_ne_zero (h_entry i)
  · rw [← map_colMap_span_col, hA_range, Submodule.map_comap_eq_self (h_range ▸ hM)]
  · rw [h_det, map_prod, ← h_comap, hA_index, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ ↦
      genIndex_eq_cardQuot (isUnit_coe_of_cardQuot_ne_zero (h_entry i))

/-- **Sublattices of finite index.** An `Ô`-submodule `M` of finite index of a lattice `L` of rank
`r` is a lattice of rank `r`, and `d_r(M) = d_r(L)·[L : M]`. -/
theorem IsLatticeOfRank.of_le {L M : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hL : IsLatticeOfRank r L) (hML : M ≤ L)
    (h_index : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    IsLatticeOfRank r M ∧
      discriminant r M = discriminant r L * M.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨x, a, hx, rfl⟩ := hL
  obtain ⟨A, hA_unit, hA_span, hA_index⟩ := exists_span_col_mul_eq hML h_index
  let u : GL (Fin r) 𝔸ᶠ[E] := ((Matrix.isUnit_iff_isUnit_det A).2 hA_unit).unit
  have h_basis : x.map (algebraMap E 𝔸ᶠ[E]) * ((a * u : GL (Fin r) 𝔸ᶠ[E]) : Matrix _ _ _) =
      x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) * A := by
    rw [Units.val_mul, Matrix.mul_assoc]
    rfl
  have hM : IsLatticeOfRank r M := ⟨x, a * u, hx, by rw [h_basis, hA_span]⟩
  refine ⟨hM, ?_⟩
  have h_dM : discriminant r M = √(genIndex E (gramDet (x.map (algebraMap E 𝔸ᶠ[E]) *
      (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E]) * A)) : ℝ) := by
    rw [← hA_span, ← h_basis, discriminant_span_col hx, h_basis]
  rw [h_dM, discriminant_span_col hx, genIndex_gramDet_mul, ← Rat.cast_natCast, ← hA_index,
    Rat.cast_mul, Rat.cast_pow,
    Real.sqrt_mul' _ (Rat.cast_nonneg.2 (genIndex_nonneg _)),
    Real.sqrt_sq (Rat.cast_nonneg.2 (genIndex_nonneg _)), mul_comm]

omit [IsCMField E] [Fintype κ] in
/-- **Sums over sublattices.** For a lattice `L` of rank `r` and every `μ ∈ ℕ`,
`∑_{M ⊂ L} [L : M]^(-(r+μ)) ≤ ζ_Ô(μ)^r`, the sum running over the submodules of finite index of
`L` and `ζ_Ô(μ) = ∑_I [Ô : I]^(-μ)` over the ideals of finite index of `Ô`. -/
theorem IsLatticeOfRank.submoduleZeta_le {L : Submodule (integralAdeles (𝓞 E) E) (κ → 𝔸ᶠ[E])}
    (hL : IsLatticeOfRank r L) (μ : ℕ) :
    Module.submoduleZeta (integralAdeles (𝓞 E) E) L (r + μ) ≤
      Module.submoduleZeta (integralAdeles (𝓞 E) E) (integralAdeles (𝓞 E) E) μ ^ r := by
  obtain ⟨x, a, -, rfl⟩ := hL
  set B := x.map (algebraMap E 𝔸ᶠ[E]) * (a : Matrix (Fin r) (Fin r) 𝔸ᶠ[E])
  have h_range : LinearMap.range (colMap B) =
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range B.col) :=
    Fintype.range_linearCombination _ _
  have h_surj : Function.Surjective ((colMap B).codRestrict _ fun c ↦
      h_range ▸ LinearMap.mem_range_self (colMap B) c) := by
    rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := (h_range ▸ hy : y ∈ LinearMap.range (colMap B))
    exact ⟨c, rfl⟩
  exact (Module.submoduleZeta_le_of_surjective h_surj _).trans
    (Module.submoduleZeta_pi_le (fun I hI ↦ isPrincipal_of_cardQuot_ne_zero hI) r μ)

end NumberField.IsCMField
