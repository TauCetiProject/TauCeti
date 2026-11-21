/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular.OrderedProduct
import TauCeti.LinearAlgebra.Trace.Exact

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
the identity representation of the free group on one generator satisfies the equations for the
two characters sending the generator to `4` and to `7`.

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
every ordered product `(ρ g₀ - χ₀ g₀) * ⋯ * (ρ g_{n-1} - χ_{n-1} g_{n-1})` vanishes. Over a
nonreduced ring the two families are independent. -/
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

/-- **Ordered triangularizations satisfy the determinant-ordinary equations**, over any
commutative ring. -/
theorem HasOrderedTriangularization.isDetOrdinary {ρ : G →* GL (Fin n) A}
    {χ : Fin n → G →* Aˣ} (h : HasOrderedTriangularization ρ χ) : IsDetOrdinary ρ χ := by
  obtain ⟨B, hB⟩ := h
  -- `T g` is the triangular form of `ρ g`, and `ρ g = B * T g * B⁻¹`.
  set T : G → Matrix (Fin n) (Fin n) A := fun g ↦ ((B⁻¹ * ρ g * B : GL (Fin n) A) : _)
  have hρ (g : G) : (ρ g : Matrix (Fin n) (Fin n) A) = B * T g * (B⁻¹ : GL (Fin n) A) := by
    simp only [T, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  refine ⟨fun g ↦ ?_, fun g ↦ ?_⟩
  · rw [hρ, mul_assoc, charpoly_mul_comm, mul_assoc, Units.inv_mul, mul_one,
      charpoly_of_isUpperTriangular _ (hB g).1]
    simp only [(hB g).2]
  · -- `ρ g - c • 1` is the conjugate of `T g - c • 1` by `B`, and conjugation is multiplicative
    have hconj (c : A) (g : G) : (ρ g : Matrix (Fin n) (Fin n) A) - c • 1 =
        ConjAct.toConjAct B • (T g - c • 1) := by
      rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, mul_sub, sub_mul, mul_smul_comm,
        mul_one, smul_mul_assoc, Units.mul_inv, hρ]
    have hmap := map_list_prod (MulDistribMulAction.toMonoidHom (Matrix (Fin n) (Fin n) A)
      (ConjAct.toConjAct B)) (List.ofFn fun i ↦ T (g i) - ((χ i (g i) : Aˣ) : A) • 1)
    rw [List.map_ofFn] at hmap
    simp only [Function.comp_def, MulDistribMulAction.toMonoidHom_apply, ← hconj] at hmap
    rw [← hmap, list_prod_ofFn_eq_zero_of_isUpperTriangular, smul_zero]
    · intro t
      rw [smul_one_eq_diagonal]
      exact (hB (g t)).1.sub (blockTriangular_diagonal _)
    · intro t
      rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, sub_eq_zero]
      exact (hB (g t)).2 t

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

/-- The vectors on which `G` acts through the character `c`. -/
private noncomputable def charSpace (ρ : Representation F G V) (c : G →* F) : Submodule F V :=
  ⨅ g, Module.End.eigenspace (ρ g) (c g)

private theorem mem_charSpace {ρ : Representation F G V} {c : G →* F} {v : V} :
    v ∈ charSpace ρ c ↔ ∀ g, ρ g v = c g • v := by
  simp [charSpace]

private theorem charSpace_le_comap (ρ : Representation F G V) (c : G →* F) (h : G) :
    charSpace ρ c ≤ (charSpace ρ c).comap (ρ h) := by
  intro v hv
  rw [Submodule.mem_comap, mem_charSpace]
  rw [mem_charSpace] at hv
  intro g
  rw [← mul_apply_eq_comp, ← map_mul, hv, hv, map_mul, mul_smul]

/-- Ordered products commute with passing to the quotient by an invariant subspace. -/
private theorem orderedProd_quotient_mkQ {m : ℕ} (ρ : Representation F G V) (W : Submodule F V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (χ : Fin m → G →* F) (g : Fin m → G) (v : V) :
    orderedProd (ρ.quotient W hW) χ g (W.mkQ v) = W.mkQ (orderedProd ρ χ g v) := by
  induction m with
  | zero => simp [orderedProd]
  | succ m ih =>
      rw [orderedProd_succ, orderedProd_succ, mul_apply_eq_comp, ih, mul_apply_eq_comp]
      simp

/-- A matrix of `f` in a basis `b` is upper triangular with diagonal `c` when each `f (b j)` is
`c j • b j` modulo the span `b.flag j.castSucc` of the earlier basis vectors. -/
private theorem toMatrix_isUpperTriangular_of_mem_flag {m : ℕ} (b : Basis (Fin m) F V)
    (f : V →ₗ[F] V) (c : Fin m → F) (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) :
    (LinearMap.toMatrix b b f).IsUpperTriangular ∧ ∀ i, LinearMap.toMatrix b b f i i = c i := by
  have key (i j : Fin m) (hij : j ≤ i) :
      LinearMap.toMatrix b b f i j = c j * (Finsupp.single j 1 : Fin m →₀ F) i := by
    have hi := b.mem_flag_iff_repr_eq_zero.mp (h j) i (Fin.castSucc_le_castSucc_iff.mpr hij)
    rw [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, Basis.repr_self, smul_eq_mul,
      sub_eq_zero] at hi
    rw [LinearMap.toMatrix_apply, hi]
  refine ⟨fun i j hji ↦ ?_, fun i ↦ ?_⟩
  · have hji' : j < i := hji
    rw [key i j hji'.le, Finsupp.single_eq_of_ne hji'.ne', mul_zero]
  · rw [key i i le_rfl, Finsupp.single_eq_same, mul_one]

/-- Ordered products for `χ₁, …, χₘ` vanish on the quotient by the vectors on which `G` acts
through `χ₀`, when all ordered products for `χ₀, …, χₘ` vanish on `V`. -/
private theorem orderedProd_quotient_charSpace_eq_zero {m : ℕ} (ρ : Representation F G V)
    (χ : Fin (m + 1) → G →* F) (h : ∀ g, orderedProd ρ χ g = 0) (g : Fin m → G) :
    orderedProd (ρ.quotient _ (charSpace_le_comap ρ (χ 0))) (Fin.tail χ) g = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [orderedProd_quotient_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, mem_charSpace]
  intro g₀
  have := LinearMap.congr_fun (h (Fin.cons g₀ g)) v
  rw [orderedProd_succ, mul_apply_eq_comp] at this
  simpa [sub_eq_zero] using this

/-- The trace of `ρ g` splits along the vectors on which `G` acts through `c`. -/
private theorem trace_eq_finrank_charSpace_mul_add [FiniteDimensional F V]
    (ρ : Representation F G V) (c : G →* F) (g : G) :
    LinearMap.trace F V (ρ g) = finrank F (charSpace ρ c) * c g +
      LinearMap.trace F _ (ρ.quotient _ (charSpace_le_comap ρ c) g) := by
  have hU (v) (hv : v ∈ charSpace ρ c) : ρ g v ∈ charSpace ρ c := charSpace_le_comap ρ c g hv
  have hres : (ρ g).restrict hU = c g • LinearMap.id := by
    ext ⟨v, hv⟩
    simp [LinearMap.restrict_apply, (mem_charSpace.mp hv) g]
  rw [LinearMap.trace_eq_add_of_exact (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) (fN := (ρ g).restrict hU)
    (fQ := ρ.quotient _ (charSpace_le_comap ρ c) g) (by ext; simp) (by ext; simp), hres,
    map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

/-- A nonzero vector of `U` followed by lifts of a basis of `V ⧸ U` is linearly independent. -/
private theorem linearIndependent_finCons_surjInv {m : ℕ} {U : Submodule F V} {u : V}
    (hu : u ∈ U) (hu0 : u ≠ 0) (b' : Basis (Fin m) F (V ⧸ U)) :
    LinearIndependent F
      (Fin.cons u fun j ↦ Function.surjInv U.mkQ_surjective (b' j) : Fin (m + 1) → V) := by
  have hs (x : V ⧸ U) : U.mkQ (Function.surjInv U.mkQ_surjective x) = x :=
    Function.surjInv_eq U.mkQ_surjective x
  refine LinearIndependent.finCons (LinearIndependent.of_comp U.mkQ ?_) fun hmem ↦ ?_
  · convert b'.linearIndependent
    ext j
    exact hs (b' j)
  · obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
    have h0 : ∑ j, a j • b' j = 0 := by
      have := congrArg U.mkQ ha
      simpa [map_sum, hs, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu] using this
    have ha0 := Fintype.linearIndependent_iff.mp b'.linearIndependent a h0
    exact hu0 (by simp [← ha, ha0])

/-- If `G` acts through `χ₀` on an invariant line `U`, a basis of `V ⧸ U` adapted to
`χ₁, …, χₘ` lifts to a basis of `V` adapted to `χ₀, …, χₘ`. -/
private theorem exists_basis_of_quotient [FiniteDimensional F V] {m : ℕ}
    (ρ : Representation F G V) (χ : Fin (m + 1) → G →* F) {U : Submodule F V}
    (hU : ∀ g, U ≤ U.comap (ρ g)) (hχU : U ≤ charSpace ρ (χ 0)) (hU1 : finrank F U = 1)
    (b' : Basis (Fin m) F (V ⧸ U))
    (hb' : ∀ g j, ρ.quotient U hU g (b' j) - Fin.tail χ j g • b' j ∈ b'.flag j.castSucc) :
    ∃ b : Basis (Fin (m + 1)) F V, ∀ g j, ρ g (b j) - χ j g • b j ∈ b.flag j.castSucc := by
  obtain ⟨u, hu⟩ : ∃ u : U, u ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hU1]; exact Nat.one_pos)
  have hu0 : (u : V) ≠ 0 := by simpa using hu
  have hUspan : U = F ∙ (u : V) :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr u.property)
      (by rw [finrank_span_singleton hu0, hU1])).symm
  have hcard : Fintype.card (Fin (m + 1)) = finrank F V := by
    rw [← U.finrank_quotient_add_finrank, Module.finrank_eq_card_basis b', hU1,
      Fintype.card_fin, Fintype.card_fin]
  -- `b` is `u` followed by lifts of `b'`
  set b := basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_finCons_surjInv u.property hu0 b') hcard
  have hb0 : b 0 = u := by simp [b]
  have hbs (i : Fin m) : U.mkQ (b i.succ) = b' i := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Fin.cons_succ]
    exact Function.surjInv_eq U.mkQ_surjective (b' i)
  refine ⟨b, fun g j ↦ ?_⟩
  induction j using Fin.cases with
  | zero =>
      rw [hb0, (mem_charSpace.mp (hχU u.property)) g, sub_self]
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
      obtain ⟨c', hc'sum, hc'tr, hc'b⟩ := ih _ (ρ.quotient _ (charSpace_le_comap ρ (χ 0)))
        (Fin.tail χ) (orderedProd_quotient_charSpace_eq_zero ρ χ h)
      refine ⟨Fin.cons (finrank F (charSpace ρ (χ 0))) c', ?_, fun g ↦ ?_, fun hc ↦ ?_⟩
      · rw [Fin.sum_cons, hc'sum, add_comm, Submodule.finrank_quotient_add_finrank]
      · rw [trace_eq_finrank_charSpace_mul_add ρ (χ 0), hc'tr, Fin.sum_univ_succ]
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
  let B : GL (Fin n) F := ⟨e.toMatrix b, b.toMatrix e, e.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip e⟩
  refine ⟨B, fun g ↦ ?_⟩
  have hconj : ((B⁻¹ * ρ g * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      LinearMap.toMatrix b b (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) F)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b e b e,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Units.val_mul, Units.val_mul,
      Units.inv_mk]
  rw [hconj]
  exact toMatrix_isUpperTriangular_of_mem_flag b _ (fun i ↦ (χ i g : F)) (hb g)

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
    rw [map_list_prod, List.map_ofFn, map_zero] at this
    simpa [orderedProd, hρV, hlin, χV, Function.comp_def, Module.End.one_eq_id] using this
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
  have hc1 : ∀ i, c i = 1 := by
    intro i₀
    by_contra hi₀
    have hpos : ∀ i, 1 ≤ c i := fun i ↦ Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
      simpa [h0] using hcF i
    have := Finset.sum_lt_sum (s := Finset.univ) (fun i _ ↦ hpos i)
      ⟨i₀, Finset.mem_univ _, lt_of_le_of_ne (hpos i₀) (Ne.symm hi₀)⟩
    simp [hcsum] at this
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
