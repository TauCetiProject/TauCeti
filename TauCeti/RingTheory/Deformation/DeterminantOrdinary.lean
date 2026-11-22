/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Basis.Triangular
import TauCeti.LinearAlgebra.ExtensionBasis
import TauCeti.LinearAlgebra.Matrix.Triangular.OrderedProduct
import TauCeti.RepresentationTheory.CharSpace

/-!
# Determinant-ordinary equations and ordered flags

Let `ρ : G →* GL (Fin n) A` be a representation and `χ₀, …, χ_{n-1} : G →* Aˣ` characters. The
*determinant-ordinary equations* say that for every `g` the characteristic polynomial of `ρ g` is
`∏ i, (X - χᵢ g)`, and that for every tuple `(g₀, …, g_{n-1})` the ordered product
`(ρ g₀ - χ₀ g₀) * ⋯ * (ρ g_{n-1} - χ_{n-1} g_{n-1})` vanishes. They cut out the
determinant-ordinary quotients of lifting rings of Galois representations.

The equations hold whenever a single change of basis `B` makes every `ρ g` upper triangular with
diagonal `χ₀ g, …, χ_{n-1} g` in this order, over any commutative ring. Over a field the converse
holds when the characters are pairwise distinct: the equations recover a stable full flag with the
prescribed graded characters in the prescribed order. Over the nonreduced ring `ℤ/9` this fails:
the trivial rank-2 representation of the free group on one generator (sending the generator to
`1 ∈ GL₂(ℤ/9)`) satisfies the equations for the two characters sending the generator to `4` and
to `7`.

Both conditions are invariant under conjugating `ρ` by an element of `GL (Fin n) A`, and both
are preserved by a change of coefficients along a ring homomorphism `A →+* A'`; the equations
also descend along an injective one.

The proof of the converse over a field `F` runs on an abstract finite-dimensional representation
`V`. The vectors on which `G` acts by `χ₀` form an invariant subspace `U` containing the images
of all ordered products for `χ₁, …, χ_{n-1}`, so these products vanish on `V ⧸ U`. By induction
the trace of `ρ g` is `∑ i, cᵢ * χᵢ g` for natural numbers `cᵢ` with `∑ i, cᵢ = dim V`. Comparing
with the characteristic polynomial, linear independence of distinct characters forces every `cᵢ`
to be `1` in `F`, hence nonzero, hence equal to `1`. Then `U` is a line, and a basis of `V ⧸ U`
adapted to the flag lifts to one of `V`.

## Main definitions

* `TauCeti.Deformation.IsDetOrdinary ρ χ`: the characteristic-polynomial and ordered-product
  equations.
* `TauCeti.Deformation.HasOrderedTriangularization ρ χ`: some `B : GL (Fin n) A` conjugates every
  `ρ g` to an upper-triangular matrix with diagonal `χ₀ g, …, χ_{n-1} g`.

## Main results

* `TauCeti.Deformation.isDetOrdinary_conj_iff` and
  `TauCeti.Deformation.hasOrderedTriangularization_conj_iff`: invariance under conjugation.
* `TauCeti.Deformation.IsDetOrdinary.map` and `TauCeti.Deformation.HasOrderedTriangularization.map`:
  preservation under change of coefficients; `TauCeti.Deformation.isDetOrdinary_map_iff`: the
  equations also descend along an injective ring homomorphism.
* `TauCeti.Deformation.isDetOrdinary_of_isUpperTriangular`: a representation by upper-triangular
  matrices with diagonal `χ₀ g, …, χ_{n-1} g` satisfies the determinant-ordinary equations.
* `TauCeti.Deformation.HasOrderedTriangularization.isDetOrdinary`: an ordered triangularization
  satisfies the determinant-ordinary equations, over any commutative ring.
* `TauCeti.Deformation.IsDetOrdinary.hasOrderedTriangularization`: over a field, the
  determinant-ordinary equations for pairwise distinct characters give an ordered
  triangularization.
* `TauCeti.Deformation.isDetOrdinary_iff_hasOrderedTriangularization`: the two conditions agree
  over a field for pairwise distinct characters.

## References

* P. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. Le Hung, J. Newton, P. Scholze,
  R. Taylor, J. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  §6.2.6, Lemma 6.2.11.
-/

public section

open Matrix Module Polynomial

namespace TauCeti.Deformation

section CommRing

variable {A G : Type*} [CommRing A] [Monoid G] {n : ℕ}

/-- The *determinant-ordinary equations* for a representation `ρ : G →* GL (Fin n) A` and
characters `χ₀, …, χ_{n-1}`: every characteristic polynomial of `ρ` is `∏ i, (X - χᵢ g)`, and
every ordered product `(ρ g₀ - χ₀ g₀) * ⋯ * (ρ g_{n-1} - χ_{n-1} g_{n-1})` vanishes. Neither
family implies the other, even over a field: for distinct `χ₀, χ₁`, the representation
`χ₀ ⊕ χ₀` has all ordered products zero but the wrong characteristic polynomial. -/
structure IsDetOrdinary (ρ : G →* GL (Fin n) A) (χ : Fin n → G →* Aˣ) : Prop where
  /-- The characteristic polynomial of `ρ g` is `∏ i, (X - χᵢ g)`. -/
  charpoly_eq (g : G) :
    (ρ g : Matrix (Fin n) (Fin n) A).charpoly = ∏ i, (X - C ((χ i g : Aˣ) : A))
  /-- The ordered product `(ρ g₀ - χ₀ g₀) * ⋯ * (ρ g_{n-1} - χ_{n-1} g_{n-1})` vanishes. -/
  list_prod_eq_zero (g : Fin n → G) :
    (List.ofFn fun i ↦ (ρ (g i) : Matrix (Fin n) (Fin n) A) -
      ((χ i (g i) : Aˣ) : A) • (1 : Matrix (Fin n) (Fin n) A)).prod = 0

/-- An *ordered triangularization* of `ρ : G →* GL (Fin n) A` by the characters
`χ₀, …, χ_{n-1}`: a single `B : GL (Fin n) A` such that every `B⁻¹ * ρ g * B` is upper triangular
with diagonal `χ₀ g, …, χ_{n-1} g`. Equivalently, the columns of `B` span a `G`-stable full flag
of direct summands on whose graded pieces `G` acts by `χ₀, …, χ_{n-1}` in this order. -/
def HasOrderedTriangularization (ρ : G →* GL (Fin n) A) (χ : Fin n → G →* Aˣ) : Prop :=
  ∃ B : GL (Fin n) A, ∀ g,
    ((B⁻¹ * ρ g * B : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).IsUpperTriangular ∧
      ∀ i, ((B⁻¹ * ρ g * B : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i i = (χ i g : A)

theorem hasOrderedTriangularization_iff {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ} :
    HasOrderedTriangularization ρ χ ↔ ∃ B : GL (Fin n) A, ∀ g,
      ((B⁻¹ * ρ g * B : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).IsUpperTriangular ∧
        ∀ i, ((B⁻¹ * ρ g * B : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i i = (χ i g : A) :=
  Iff.rfl

/-- The determinant-ordinary equations are invariant under conjugating `ρ` by `B`. -/
theorem IsDetOrdinary.conj {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (h : IsDetOrdinary ρ χ) (B : GL (Fin n) A) :
    IsDetOrdinary ((MulAut.conj B : GL (Fin n) A →* GL (Fin n) A).comp ρ) χ := by
  refine ⟨fun g ↦ ?_, fun g ↦ ?_⟩
  · simpa [Matrix.coe_units_inv] using h.charpoly_eq g
  · -- conjugation by `B` is multiplicative and sends `ρ g - c • 1` to `B * ρ g * B⁻¹ - c • 1`
    have hmap := map_list_prod (MulDistribMulAction.toMonoidHom (Matrix (Fin n) (Fin n) A)
      (ConjAct.toConjAct B)) (List.ofFn fun i ↦ (ρ (g i) : Matrix (Fin n) (Fin n) A) -
        ((χ i (g i) : Aˣ) : A) • 1)
    simpa [List.map_ofFn, Function.comp_def, ConjAct.units_smul_def, mul_sub, sub_mul,
      h.list_prod_eq_zero g] using hmap.symm

/-- `ρ` satisfies the determinant-ordinary equations exactly when its conjugate by `B` does. -/
@[simp]
theorem isDetOrdinary_conj_iff {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (B : GL (Fin n) A) :
    IsDetOrdinary ((MulAut.conj B : GL (Fin n) A →* GL (Fin n) A).comp ρ) χ ↔ IsDetOrdinary ρ χ :=
  ⟨fun h ↦ by convert h.conj B⁻¹; exact MonoidHom.ext fun g ↦ by simp [mul_assoc],
    fun h ↦ h.conj B⟩

/-- Ordered triangularizations are carried along conjugation of `ρ` by `B`. -/
theorem HasOrderedTriangularization.conj {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (h : HasOrderedTriangularization ρ χ) (B : GL (Fin n) A) :
    HasOrderedTriangularization ((MulAut.conj B : GL (Fin n) A →* GL (Fin n) A).comp ρ) χ := by
  obtain ⟨C, hC⟩ := h
  exact ⟨B * C, fun g ↦ by simpa [mul_assoc] using hC g⟩

/-- `ρ` has an ordered triangularization exactly when its conjugate by `B` does. -/
@[simp]
theorem hasOrderedTriangularization_conj_iff {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (B : GL (Fin n) A) :
    HasOrderedTriangularization ((MulAut.conj B : GL (Fin n) A →* GL (Fin n) A).comp ρ) χ ↔
      HasOrderedTriangularization ρ χ :=
  ⟨fun h ↦ by convert h.conj B⁻¹; exact MonoidHom.ext fun g ↦ by simp [mul_assoc],
    fun h ↦ h.conj B⟩

/-- A ring homomorphism `φ` sending each `c i • 1` to `d i • 1` sends the ordered product
`(M₀ - c₀ • 1) * ⋯ * (M_{m-1} - c_{m-1} • 1)` to
`(φ M₀ - d₀ • 1) * ⋯ * (φ M_{m-1} - d_{m-1} • 1)`. -/
private theorem map_list_prod_ofFn_sub_smul_one {R S B C Φ : Type*} [Ring R] [Ring S] [SMul B R]
    [SMul C S] [FunLike Φ R S] [RingHomClass Φ R S] (φ : Φ) {m : ℕ} (M : Fin m → R)
    {c : Fin m → B} {d : Fin m → C} (hφ : ∀ i, φ (c i • 1) = d i • 1) :
    φ (List.ofFn fun i ↦ M i - c i • 1).prod = (List.ofFn fun i ↦ φ (M i) - d i • 1).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_sub, hφ]

section Map

variable {A' : Type*} [CommRing A']

/-- `f.mapMatrix` sends the scalar matrix `a • 1` to `f a • 1`. -/
private theorem mapMatrix_smul_one (f : A →+* A') (a : A) :
    f.mapMatrix (a • (1 : Matrix (Fin n) (Fin n) A)) = f a • 1 := by
  rw [f.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul f),
    Matrix.map_one _ (map_zero f) (map_one f)]

/-- The determinant-ordinary equations are preserved by a change of coefficients along
`f : A →+* A'`. -/
theorem IsDetOrdinary.map {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (h : IsDetOrdinary ρ χ) (f : A →+* A') :
    IsDetOrdinary ((GeneralLinearGroup.map f).comp ρ)
      fun i ↦ (Units.map (f : A →* A')).comp (χ i) := by
  refine ⟨fun g ↦ ?_, fun g ↦ ?_⟩
  · simp [charpoly_map, h.charpoly_eq g, Polynomial.map_prod]
  · have := congrArg f.mapMatrix (h.list_prod_eq_zero g)
    rw [map_list_prod_ofFn_sub_smul_one f.mapMatrix _ fun i ↦ mapMatrix_smul_one f _,
      map_zero] at this
    simpa using this

/-- Along an injective `f : A →+* A'`, the determinant-ordinary equations hold over `A` exactly
when they hold after the change of coefficients. -/
theorem isDetOrdinary_map_iff {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ} {f : A →+* A'}
    (hf : Function.Injective f) :
    IsDetOrdinary ((GeneralLinearGroup.map f).comp ρ)
        (fun i ↦ (Units.map (f : A →* A')).comp (χ i)) ↔ IsDetOrdinary ρ χ := by
  refine ⟨fun h ↦ ⟨fun g ↦ Polynomial.map_injective f hf ?_, fun g ↦ Matrix.map_injective hf ?_⟩,
    fun h ↦ h.map f⟩
  · simpa [← charpoly_map, Polynomial.map_prod] using h.charpoly_eq g
  · -- `Matrix.map_injective` leaves `fun M ↦ M.map f` unapplied; rewrite it as `f.mapMatrix`
    beta_reduce
    rw [← f.mapMatrix_apply, ← f.mapMatrix_apply, map_zero,
      map_list_prod_ofFn_sub_smul_one f.mapMatrix _ fun i ↦ mapMatrix_smul_one f _]
    simpa using h.list_prod_eq_zero g

/-- Ordered triangularizations are preserved by a change of coefficients along `f : A →+* A'`. -/
theorem HasOrderedTriangularization.map {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (h : HasOrderedTriangularization ρ χ) (f : A →+* A') :
    HasOrderedTriangularization ((GeneralLinearGroup.map f).comp ρ)
      fun i ↦ (Units.map (f : A →* A')).comp (χ i) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨GeneralLinearGroup.map f B, fun g ↦ ?_⟩
  have hBf : ((GeneralLinearGroup.map f B)⁻¹ * GeneralLinearGroup.map f (ρ g) *
      GeneralLinearGroup.map f B : GL (Fin n) A') =
      GeneralLinearGroup.map f (B⁻¹ * ρ g * B) := by
    simp only [map_mul, map_inv]
  rw [MonoidHom.comp_apply, hBf, GeneralLinearGroup.val_map_apply]
  exact ⟨(hB g).1.map f, fun i ↦ by rw [Matrix.map_apply, (hB g).2 i]; simp⟩

end Map

/-- A representation by upper-triangular matrices whose diagonal entries are
`χ₀ g, …, χ_{n-1} g` satisfies the determinant-ordinary equations. -/
theorem isDetOrdinary_of_isUpperTriangular {ρ : G →* GL (Fin n) A} {χ : Fin n → G →* Aˣ}
    (h : ∀ g, (ρ g : Matrix (Fin n) (Fin n) A).IsUpperTriangular ∧
      ∀ i, (ρ g : Matrix (Fin n) (Fin n) A) i i = (χ i g : A)) :
    IsDetOrdinary ρ χ := by
  refine ⟨fun g ↦ by simp [charpoly_of_isUpperTriangular _ (h g).1, (h g).2], fun g ↦ ?_⟩
  refine list_prod_ofFn_eq_zero_of_isUpperTriangular (fun t ↦ ?_) fun t ↦ ?_
  · rw [smul_one_eq_diagonal]
    exact (h (g t)).1.sub (blockTriangular_diagonal _)
  · simpa [sub_eq_zero] using (h (g t)).2 t

/-- **Ordered triangularizations satisfy the determinant-ordinary equations**, over any
commutative ring. -/
theorem HasOrderedTriangularization.isDetOrdinary {ρ : G →* GL (Fin n) A}
    {χ : Fin n → G →* Aˣ} (h : HasOrderedTriangularization ρ χ) : IsDetOrdinary ρ χ := by
  obtain ⟨B, hB⟩ := h
  -- conjugating by `B⁻¹` makes every `ρ g` triangular
  rw [← isDetOrdinary_conj_iff B⁻¹]
  exact isDetOrdinary_of_isUpperTriangular fun g ↦ by simpa using hB g

end CommRing

section Field

variable {F G : Type*} [Field F] [Monoid G]

section Representation

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The ordered product `(ρ g₀ - χ₀ g₀) ∘ ⋯ ∘ (ρ g_{m-1} - χ_{m-1} g_{m-1})`. -/
private noncomputable def orderedProd {m : ℕ} (ρ : Representation F G V) (χ : Fin m → G →* F)
    (g : Fin m → G) : V →ₗ[F] V :=
  (List.ofFn fun i ↦ ρ (g i) - χ i (g i) • 1).prod

private theorem orderedProd_succ {m : ℕ} (ρ : Representation F G V) (χ : Fin (m + 1) → G →* F)
    (g : Fin (m + 1) → G) :
    orderedProd ρ χ g = (ρ (g 0) - χ 0 (g 0) • 1) * orderedProd ρ (Fin.tail χ) (Fin.tail g) := by
  simp only [orderedProd, List.ofFn_succ, List.prod_cons, Fin.tail]

/-- Ordered products commute with passing to the quotient by an invariant subspace. -/
private theorem orderedProd_quotient_mkQ {m : ℕ} (ρ : Representation F G V) (W : Submodule F V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (χ : Fin m → G →* F) (g : Fin m → G) (v : V) :
    orderedProd (ρ.quotient W hW) χ g (W.mkQ v) = W.mkQ (orderedProd ρ χ g v) := by
  induction m with
  | zero => simp [orderedProd]
  | succ m ih =>
      rw [orderedProd_succ, orderedProd_succ, mul_apply_eq_comp, ih, mul_apply_eq_comp]
      simp

/-- Ordered products for `χ₁, …, χₘ` vanish on the quotient by the vectors on which `G` acts
through `χ₀`, when all ordered products for `χ₀, …, χₘ` vanish on `V`. -/
private theorem orderedProd_quotient_charSpace_eq_zero {m : ℕ} (ρ : Representation F G V)
    (χ : Fin (m + 1) → G →* F) (h : ∀ g, orderedProd ρ χ g = 0) (g : Fin m → G) :
    orderedProd (ρ.quotient _ (ρ.charSpace_le_comap (χ 0))) (Fin.tail χ) g = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [orderedProd_quotient_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Representation.mem_charSpace]
  intro g₀
  have := LinearMap.congr_fun (h (Fin.cons g₀ g)) v
  rw [orderedProd_succ, mul_apply_eq_comp] at this
  simpa [sub_eq_zero] using this

/-- If `G` acts through `χ₀` on an invariant line `U`, a basis of `V ⧸ U` adapted to
`χ₁, …, χₘ` lifts to a basis of `V` adapted to `χ₀, …, χₘ`. -/
private theorem exists_basis_of_quotient [FiniteDimensional F V] {m : ℕ}
    (ρ : Representation F G V) (χ : Fin (m + 1) → G →* F) {U : Submodule F V}
    (hU : ∀ g, U ≤ U.comap (ρ g)) (hχU : U ≤ ρ.charSpace (χ 0)) (hU1 : finrank F U = 1)
    (b' : Basis (Fin m) F (V ⧸ U))
    (hb' : ∀ g j, ρ.quotient U hU g (b' j) - Fin.tail χ j g • b' j ∈ b'.flag j.castSucc) :
    ∃ b : Basis (Fin (m + 1)) F V, ∀ g j, ρ g (b j) - χ j g • b j ∈ b.flag j.castSucc := by
  -- `b` is a basis vector `u` of `U` followed by lifts of `b'`
  let bU := Module.finBasisOfFinrankEq F U hU1
  let b := (TauCeti.extensionBasis U bU b').reindex (finCongr (add_comm 1 m))
  set u : U := bU 0
  have hu0 : (u : V) ≠ 0 := by simpa using bU.ne_zero 0
  have hUspan : U = F ∙ (u : V) :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr u.property)
      (by rw [finrank_span_singleton hu0, hU1])).symm
  have hb0 : b 0 = u := by
    have h0 : (finCongr (add_comm 1 m)).symm 0 = Fin.castAdd m 0 := Fin.ext (by simp)
    rw [← TauCeti.extensionBasis_castAdd U bU b' 0, Basis.reindex_apply, h0]
  have hbs (i : Fin m) : U.mkQ (b i.succ) = b' i := by
    have hi : (finCongr (add_comm 1 m)).symm i.succ = Fin.natAdd 1 i := Fin.ext (by simp [add_comm])
    rw [← TauCeti.extensionBasis_natAdd_mkQ U bU b' i, Basis.reindex_apply, Submodule.mkQ_apply,
      hi]
  refine ⟨b, fun g j ↦ ?_⟩
  induction j using Fin.cases with
  | zero =>
      rw [hb0, (Representation.mem_charSpace.mp (hχU u.property)) g, sub_self]
      exact Submodule.zero_mem _
  | succ j =>
      -- the image in `V ⧸ U` lies in `b'.flag j.castSucc`, and `U` lies in the flag of `b`
      have hUW : U ≤ b.flag j.succ.castSucc := by
        rw [hUspan, Submodule.span_singleton_le_iff_mem, ← hb0]
        exact b.self_mem_flag (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos j))
      have hmap : b'.flag j.castSucc ≤ (b.flag j.succ.castSucc).map U.mkQ := by
        refine b'.flag_le_iff.mpr fun i hi ↦ ⟨b i.succ, b.self_mem_flag ?_, hbs i⟩
        rw [Fin.castSucc_lt_castSucc_iff] at hi ⊢
        exact Fin.succ_lt_succ_iff.mpr hi
      have hq : ρ.quotient U hU g (b' j) = U.mkQ (ρ g (b j.succ)) := by
        rw [← hbs j]
        simp
      rw [← sup_eq_right.mpr hUW, ← Submodule.comap_map_mkQ]
      refine hmap ?_
      convert hb' g j using 1
      rw [hq, map_sub, map_smul, hbs, Fin.tail]

/-- **The trace formula for vanishing ordered products.** If all ordered products for the
characters `χ₀, …, χ_{m-1}` vanish on `V`, then `trace (ρ g) = ∑ i, cᵢ * χᵢ g` for natural numbers
`cᵢ` with `∑ i, cᵢ = dim V`. When every `cᵢ` is `1`, `V` has a basis `b` in which
`ρ g (b j) - χⱼ g • b j` lies in the span `b.flag j.castSucc` of the earlier basis vectors. -/
private theorem exists_trace_eq_of_orderedProd_eq_zero (m : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (ρ : Representation F G V) (χ : Fin m → G →* F), (∀ g, orderedProd ρ χ g = 0) →
      ∃ c : Fin m → ℕ, ∑ i, c i = finrank F V ∧
        (∀ g, LinearMap.trace F V (ρ g) = ∑ i, (c i : F) * χ i g) ∧
        ((∀ i, c i = 1) → ∃ b : Basis (Fin m) F V,
          ∀ g j, ρ g (b j) - χ j g • b j ∈ b.flag j.castSucc) := by
  induction m with
  | zero =>
      intro V _ _ _ ρ χ h
      -- the empty ordered product is the identity, so `V = 0`
      have h1 : (1 : V →ₗ[F] V) = 0 := by simpa [orderedProd] using h Fin.elim0
      have h0 (x : V) : x = 0 := by simpa using LinearMap.congr_fun h1 x
      have : Subsingleton V := ⟨fun x y ↦ (h0 x).trans (h0 y).symm⟩
      refine ⟨Fin.elim0, by simp [Module.finrank_zero_of_subsingleton], fun g ↦ ?_,
        fun _ ↦ ⟨Basis.empty V, fun _ j ↦ j.elim0⟩⟩
      rw [show ρ g = 0 from Subsingleton.elim _ _, map_zero]
      simp
  | succ m ih =>
      intro V _ _ _ ρ χ h
      -- pass to the quotient by the vectors on which `G` acts through `χ₀`
      obtain ⟨c', hc'sum, hc'tr, hc'b⟩ := ih _ (ρ.quotient _ (ρ.charSpace_le_comap (χ 0)))
        (Fin.tail χ) (orderedProd_quotient_charSpace_eq_zero ρ χ h)
      refine ⟨Fin.cons (finrank F (ρ.charSpace (χ 0))) c', ?_, fun g ↦ ?_, fun hc ↦ ?_⟩
      · rw [Fin.sum_cons, hc'sum, add_comm, Submodule.finrank_quotient_add_finrank]
      · rw [ρ.trace_eq_finrank_charSpace_mul_add (χ 0), hc'tr, Fin.sum_univ_succ]
        simp [Fin.tail]
      · obtain ⟨b', hb'⟩ := hc'b fun i ↦ by simpa using hc i.succ
        exact exists_basis_of_quotient ρ χ _ le_rfl (by simpa using hc 0) b' hb'

end Representation

variable {n : ℕ}

/-- A basis of `Fin n → F` adapted to `ρ` and `χ₀, …, χ_{n-1}` gives an ordered
triangularization. -/
private theorem hasOrderedTriangularization_of_basis {ρ : G →* GL (Fin n) F}
    {χ : Fin n → G →* Fˣ} (b : Basis (Fin n) F (Fin n → F))
    (hb : ∀ g j, Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) F) (b j) - (χ j g : F) • b j ∈
      b.flag j.castSucc) :
    HasOrderedTriangularization ρ χ := by
  -- the change of basis from the standard basis `e` to `b`
  let e := Pi.basisFun F (Fin n)
  let := e.invertibleToMatrix b
  let B : GL (Fin n) F := unitOfInvertible (e.toMatrix b)
  refine ⟨B, fun g ↦ ?_⟩
  have hconj : ((B⁻¹ * ρ g * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      LinearMap.toMatrix b b (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) F)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b e b e,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Units.val_mul, Units.val_mul,
      val_inv_unitOfInvertible, val_unitOfInvertible,
      invOf_eq_right_inv (e.toMatrix_mul_toMatrix_flip b)]
  rw [hconj]
  exact ⟨b.toMatrix_isUpperTriangular_of_sub_smul_mem_flag (hb g),
    b.toMatrix_apply_self_of_sub_smul_mem_flag (hb g)⟩

/-- **Determinant-ordinary equations give an ordered flag.** Over a field, if `ρ` satisfies the
determinant-ordinary equations for pairwise distinct characters `χ₀, …, χ_{n-1}`, then a single
change of basis makes every `ρ g` upper triangular with diagonal `χ₀ g, …, χ_{n-1} g`. -/
theorem IsDetOrdinary.hasOrderedTriangularization {ρ : G →* GL (Fin n) F}
    {χ : Fin n → G →* Fˣ} (h : IsDetOrdinary ρ χ) (hχ : Function.Injective χ) :
    HasOrderedTriangularization ρ χ := by
  -- transport `ρ` and `χ` to a representation on `Fin n → F` and `F`-valued characters
  set ρV : Representation F G (Fin n → F) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) F ≃ₐ[F] _).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ)
  have hlin (M : Matrix (Fin n) (Fin n) F) : Matrix.toLinAlgEquiv' M = Matrix.toLin' M :=
    LinearMap.ext fun v ↦ by rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  have hρV (g : G) : ρV g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) F) := by
    simp [ρV, hlin]
  set χV : Fin n → G →* F := fun i ↦ (Units.coeHom F).comp (χ i)
  have hprod (g : Fin n → G) : orderedProd ρV χV g = 0 := by
    have := congrArg (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) F ≃ₐ[F] _)
      (h.list_prod_eq_zero g)
    rw [map_list_prod_ofFn_sub_smul_one _ _ fun i ↦ by rw [map_smul, map_one], map_zero] at this
    simpa [orderedProd, hρV, hlin, χV] using this
  obtain ⟨c, hcsum, hctr, hcb⟩ := exists_trace_eq_of_orderedProd_eq_zero n (Fin n → F) ρV χV hprod
  -- linear independence of the distinct characters forces `c i = 1` in `F`
  have hχV : Function.Injective χV := fun i j hij ↦ hχ <| MonoidHom.ext fun g ↦
    Units.ext (DFunLike.congr_fun hij g)
  have hcF : ∀ i, ((c i : F) - 1) = 0 := by
    refine Fintype.linearIndependent_iff.mp
      ((linearIndependent_monoidHom G F).comp χV hχV) _ (funext fun g ↦ ?_)
    have htr := hctr g
    rw [hρV, Matrix.trace_toLin'_eq, trace_eq_neg_charpoly_nextCoeff, h.charpoly_eq,
      prod_X_sub_C_nextCoeff, neg_neg] at htr
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, sub_mul,
      one_mul, Finset.sum_sub_distrib, Pi.zero_apply]
    rw [← htr]
    simp [χV]
  -- so every `c i` is positive, and the `c i` sum to `n`
  have hpos (i : Fin n) : 1 ≤ c i := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
    simpa [h0] using hcF i
  have hc1 (i : Fin n) : c i = 1 :=
    ((Finset.sum_eq_sum_iff_of_le fun i _ ↦ hpos i).mp (by simp [hcsum]) i (Finset.mem_univ _)).symm
  obtain ⟨b, hb⟩ := hcb hc1
  exact hasOrderedTriangularization_of_basis b fun g j ↦ by simpa [hρV, χV] using hb g j

/-- **Determinant-ordinary equations and ordered flags agree over a field.** For pairwise distinct
characters `χ₀, …, χ_{n-1}`, the representation `ρ` satisfies the determinant-ordinary equations
exactly when a single change of basis makes every `ρ g` upper triangular with diagonal
`χ₀ g, …, χ_{n-1} g`. -/
theorem isDetOrdinary_iff_hasOrderedTriangularization {ρ : G →* GL (Fin n) F}
    {χ : Fin n → G →* Fˣ} (hχ : Function.Injective χ) :
    IsDetOrdinary ρ χ ↔ HasOrderedTriangularization ρ χ :=
  ⟨fun h ↦ h.hasOrderedTriangularization hχ, HasOrderedTriangularization.isDetOrdinary⟩

end Field

end TauCeti.Deformation
