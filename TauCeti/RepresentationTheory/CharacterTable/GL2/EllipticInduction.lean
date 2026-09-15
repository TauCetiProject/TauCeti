/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.indClassFun` is the object computed here.
public import TauCeti.RepresentationTheory.Induction.ClassFunction
-- `TauCeti.GL2NonSplitTorus`, `TauCeti.diagGL` and `TauCeti.jordanGL` occur in the statements
-- below, and the centralizer of an elliptic element is what pins the two contributing cosets.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer
-- Non-public: the conjugacy classification of the non-scalar elements of `GL₂` is used only
-- inside the proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: the `q`-power map on a quadratic extension of a finite field, whose fixed points
-- are the base field, is used only inside the proofs.
import TauCeti.FieldTheory.Finite.FrobeniusFixed
-- Non-public: `TauCeti.smul_quotientGroup_mk_eq_self_iff` is used only inside a proof.
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# The class function of `GL₂(𝔽_q)` induced from the non-split torus

Let `E/F` be a quadratic extension of a finite field with `q` elements and let
`T = TauCeti.GL2NonSplitTorus F E hE` be the resulting elliptic torus of `GL₂(F)`, a copy of `Eˣ`.
This file computes the induced class function `TauCeti.indClassFun T f` on the four families of
conjugacy classes of `GL₂(F)`: at a central scalar `a` it is `[GL₂(F) : T] = q (q - 1)` copies of
`f(a)`, it vanishes on the split semisimple and the non-semisimple families, and at an elliptic
element coming from `u : Eˣ` outside `F` it is `f(u) + f(u^q)`.

Applied to a character `θ` of `Eˣ` this is the character of `Ind_{Eˣ}^{GL₂(F)} θ`, one of the two
induced characters whose difference is the cuspidal (discrete series) character attached to a
character of `Eˣ` in general position; the other is induced from the product of the centre with the
unipotent radical. Its degree is the difference of the two inducing indices,
`[GL₂(F) : Z·U] - [GL₂(F) : Eˣ] = (q² - 1) - q (q - 1) = q - 1`.

## The geometry behind the four values

Everything follows from which conjugates of an element land in `T`, and `T` is small: away from the
scalars its elements have no eigenvalue in `F`
(`TauCeti.GL2NonSplitTorus.det_sub_algebraMap_ne_zero`).

* A **scalar** matrix is central, so every conjugate of it lies in `T`, and the sum has one equal
  summand for each of the `[GL₂(F) : T]` cosets.
* A **split semisimple** or **non-semisimple** element is non-scalar with an eigenvalue in `F`, and
  both properties are conjugation invariant, so no conjugate of it meets `T` at all.
* An **elliptic** element `u : Eˣ` outside `F` meets `T` in exactly the two points `u` and `u^q`:
  a conjugate of it inside `T` has the same trace and norm as `u`, and the only elements of `E`
  with those invariants are the two roots `u, u^q` of `X² - Tr(u) X + N(u)`
  (`TauCeti.GL2NonSplitTorus.isConj_gl2NonSplitTorusHom_iff`). The centralizer of an elliptic
  element being `T` itself, those two points contribute one coset each.

## Main results

* `TauCeti.GL2NonSplitTorus.indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero`: the induced class
  function vanishes on a non-scalar element with an eigenvalue in `F`.
* `TauCeti.GL2NonSplitTorus.indClassFun_scalar`,
  `TauCeti.GL2NonSplitTorus.indClassFun_diagGL`,
  `TauCeti.GL2NonSplitTorus.indClassFun_jordanGL` and
  `TauCeti.GL2NonSplitTorus.indClassFun_gl2NonSplitTorusHom`: **the four values**, on the central,
  split semisimple, non-semisimple and elliptic normal forms.

That the four normal forms exhaust the conjugacy classes is
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses`; as in
`TauCeti/RepresentationTheory/CharacterTable/GL2/CharacterValues.lean`, the values below are
stated at the normal forms themselves rather than assembled into a single case distinction. None
of the four is a `simp` lemma: they evaluate a class function at a normal form, and neither side
is a normal form for `simp`.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
-/

public section

open Matrix

namespace TauCeti

namespace GL2NonSplitTorus

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {k : Type*} [AddCommMonoid k] (hE : Module.finrank F E = 2)

variable [Finite F]

/-- **The induced class function vanishes on a non-scalar element with an eigenvalue in `F`**: no
coset contributes, by `TauCeti.GL2NonSplitTorus.conj_notMem_of_det_sub_algebraMap_eq_zero`. -/
theorem indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero (f : GL2NonSplitTorus F E hE → k)
    {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) {a : F}
    (ha : ((g : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a).det = 0) :
    indClassFun (GL2NonSplitTorus F E hE) f g = 0 := by
  classical
  rw [indClassFun_apply]
  exact Finset.sum_eq_zero fun t _ =>
    dite_eq_right (conj_notMem_of_det_sub_algebraMap_eq_zero hE hg ha _)

/-! ### The four values -/

/-- **The induced class function at a central element**: every conjugate of a scalar matrix is
itself and lies in the torus, so each of the `[GL₂(F) : T]` cosets contributes the same value.
Over a field with `q` elements the index is `q (q - 1)` by
`TauCeti.GL2NonSplitTorus.index_eq`. -/
theorem indClassFun_scalar (f : GL2NonSplitTorus F E hE → k) (a : Fˣ) :
    indClassFun (GL2NonSplitTorus F E hE) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      (GL2NonSplitTorus F E hE).index •
        f ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, scalar_mem hE a⟩ := by
  classical
  have hconj : ∀ x : GL (Fin 2) F,
      x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * x =
        Matrix.GeneralLinearGroup.scalar (Fin 2) a := fun x => by
    rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute a x, ← mul_assoc, inv_mul_cancel,
      one_mul]
  let _ : Fintype (GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) := Fintype.ofFinite _
  rw [indClassFun_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.sum_eq_card_nsmul fun t _ => by rw [hconj, dite_eq_left (scalar_mem hE a)]

/-- **The induced class function vanishes on the split semisimple classes**: an invertible
diagonal matrix with distinct entries is non-scalar and has its entries as eigenvalues in `F`. -/
theorem indClassFun_diagGL (f : GL2NonSplitTorus F E hE → k) {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    indClassFun (GL2NonSplitTorus F E hE) f (diagGL t) = 0 := by
  refine indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero hE f
    (notMem_range_scalar_diagGL ht) (a := (t 0 : F)) ?_
  have hsub : ((diagGL t : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (t 0 : F)) =
      !![0, 0; 0, (t 1 : F) - (t 0 : F)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_matrix_apply, diagGL_coe]
  rw [hsub, Matrix.det_fin_two_of, mul_zero, zero_mul, sub_zero]

/-- **The induced class function vanishes on the non-semisimple classes**: a Jordan block with
`b ≠ 0` is non-scalar and has its repeated diagonal entry as an eigenvalue in `F`. -/
theorem indClassFun_jordanGL (f : GL2NonSplitTorus F E hE → k) (a : Fˣ) {b : F} (hb : b ≠ 0) :
    indClassFun (GL2NonSplitTorus F E hE) f (jordanGL a b) = 0 := by
  refine indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero hE f
    (notMem_range_scalar_jordanGL hb) (a := (a : F)) ?_
  have hsub : ((jordanGL a b : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (a : F)) = !![0, b; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_jordanGL, Matrix.algebraMap_matrix_apply]
  rw [hsub, Matrix.det_fin_two_of, mul_zero, mul_zero, sub_zero]

/-! ### The elliptic classes -/

section Elliptic

variable {u : Eˣ}

/-- There is a conjugator taking an elliptic torus element to its Frobenius conjugate, and this
conjugator represents a nontrivial coset and normalizes the torus. -/
private theorem exists_frobenius_conjugator_normalizes
    (hu : (u : E) ∉ Set.range (algebraMap F E)) :
    ∃ d : GL (Fin 2) F,
      d⁻¹ * GL2NonSplitTorusHom F E hE u * d =
        GL2NonSplitTorusHom F E hE (u ^ Nat.card F) ∧
      d ∉ GL2NonSplitTorus F E hE ∧
      ∀ y ∈ GL2NonSplitTorus F E hE, d⁻¹ * y * d ∈ GL2NonSplitTorus F E hE := by
  have hupow : ((u ^ Nat.card F : Eˣ) : E) ∉ Set.range (algebraMap F E) := by
    rw [Units.val_pow_eq_pow_val]
    exact FiniteField.pow_natCard_notMem_range_algebraMap hE hu
  have hune : (u ^ Nat.card F : Eˣ) ≠ u := fun h =>
    FiniteField.pow_natCard_ne hu (by rw [← Units.val_pow_eq_pow_val, h])
  have hmemT : ∀ y : GL (Fin 2) F, y ∈ GL2NonSplitTorus F E hE ↔
      GL2NonSplitTorusHom F E hE u * y = y * GL2NonSplitTorusHom F E hE u := by
    intro y
    rw [← centralizer_gl2NonSplitTorusHom hE hu, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h _ rfl, fun h z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h⟩
  have hmemT' : ∀ y : GL (Fin 2) F, y ∈ GL2NonSplitTorus F E hE ↔
      GL2NonSplitTorusHom F E hE (u ^ Nat.card F) * y =
        y * GL2NonSplitTorusHom F E hE (u ^ Nat.card F) := by
    intro y
    rw [← centralizer_gl2NonSplitTorusHom hE hupow, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h _ rfl, fun h z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp
    ((isConj_gl2NonSplitTorusHom_iff hE (v := u ^ Nat.card F) hu).mpr (Or.inr rfl))
  refine ⟨c⁻¹, ?_, ?_, ?_⟩
  · rw [inv_inv]
    exact hc
  · intro hmem
    refine hune (gl2NonSplitTorusHom_injective hE ?_)
    rw [← hc]
    have hcomm := (hmemT c⁻¹).mp hmem
    calc c * GL2NonSplitTorusHom F E hE u * c⁻¹
        = c * (GL2NonSplitTorusHom F E hE u * c⁻¹) := by group
      _ = c * (c⁻¹ * GL2NonSplitTorusHom F E hE u) := by rw [hcomm]
      _ = GL2NonSplitTorusHom F E hE u := by group
  · intro y hy
    have hcomm := (hmemT y).mp hy
    refine (hmemT' _).mpr ?_
    rw [← hc]
    calc c * GL2NonSplitTorusHom F E hE u * c⁻¹ * (c * y * c⁻¹)
        = c * (GL2NonSplitTorusHom F E hE u * y) * c⁻¹ := by group
      _ = c * (y * GL2NonSplitTorusHom F E hE u) * c⁻¹ := by rw [hcomm]
      _ = c * y * c⁻¹ * (c * GL2NonSplitTorusHom F E hE u * c⁻¹) := by group

/-- If conjugation by `x` carries an elliptic element into the torus, the coset of `x` is either
the identity coset or that of a chosen Frobenius conjugator. -/
private theorem quotient_eq_one_or_frobenius_conjugator_of_conj_mem
    (hu : (u : E) ∉ Set.range (algebraMap F E)) {d x : GL (Fin 2) F}
    (hdg : d⁻¹ * GL2NonSplitTorusHom F E hE u * d =
      GL2NonSplitTorusHom F E hE (u ^ Nat.card F))
    (hdnorm : ∀ y ∈ GL2NonSplitTorus F E hE, d⁻¹ * y * d ∈ GL2NonSplitTorus F E hE)
    (hx : x⁻¹ * GL2NonSplitTorusHom F E hE u * x ∈ GL2NonSplitTorus F E hE) :
    (x : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) = ((1 : GL (Fin 2) F) : _) ∨
      (x : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) = (d : _) := by
  have hmemT : ∀ y : GL (Fin 2) F, y ∈ GL2NonSplitTorus F E hE ↔
      GL2NonSplitTorusHom F E hE u * y = y * GL2NonSplitTorusHom F E hE u := by
    intro y
    rw [← centralizer_gl2NonSplitTorusHom hE hu, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h _ rfl, fun h z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h⟩
  obtain ⟨w, hw⟩ := (mem_iff hE).mp hx
  have hconj : IsConj (GL2NonSplitTorusHom F E hE u) (GL2NonSplitTorusHom F E hE w) :=
    isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]; exact hw.symm⟩
  rcases (isConj_gl2NonSplitTorusHom_iff hE hu).mp hconj with h | h
  · refine Or.inl ?_
    rw [QuotientGroup.eq, mul_one]
    refine Subgroup.inv_mem _ ((hmemT x).mpr ?_)
    have hxg : x⁻¹ * GL2NonSplitTorusHom F E hE u * x =
        GL2NonSplitTorusHom F E hE u := by rw [← hw, h]
    calc GL2NonSplitTorusHom F E hE u * x
        = x * (x⁻¹ * GL2NonSplitTorusHom F E hE u * x) := by group
      _ = x * GL2NonSplitTorusHom F E hE u := by rw [hxg]
  · refine Or.inr ?_
    rw [QuotientGroup.eq]
    have hxd : x⁻¹ * GL2NonSplitTorusHom F E hE u * x =
        d⁻¹ * GL2NonSplitTorusHom F E hE u * d := by rw [hdg, ← hw, h]
    have hmem : d * x⁻¹ ∈ GL2NonSplitTorus F E hE := by
      refine (hmemT _).mpr ?_
      calc GL2NonSplitTorusHom F E hE u * (d * x⁻¹)
          = d * (d⁻¹ * GL2NonSplitTorusHom F E hE u * d) * d⁻¹ * (d * x⁻¹) := by group
        _ = d * (x⁻¹ * GL2NonSplitTorusHom F E hE u * x) * d⁻¹ * (d * x⁻¹) := by
          rw [hxd]
        _ = d * x⁻¹ * GL2NonSplitTorusHom F E hE u := by group
    have hconjmem := hdnorm _ hmem
    have hrw : d⁻¹ * (d * x⁻¹) * d = x⁻¹ * d := by group
    rwa [hrw] at hconjmem

/-- **The induced class function at an elliptic element.** For `u : Eˣ` outside `F` exactly two
cosets contribute, the trivial one and the one that conjugates `u` to `u^q`, so the value is
`f(u) + f(u^q)`.

The two cosets are pinned by two facts: the elements of the torus conjugate to `u` are `u` and
`u^q` (`TauCeti.GL2NonSplitTorus.isConj_gl2NonSplitTorusHom_iff`), and the centralizer of an
elliptic element is the whole torus
(`TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`), so each of the two accounts for a
single coset. -/
theorem indClassFun_gl2NonSplitTorusHom (f : GL2NonSplitTorus F E hE → k)
    (hu : (u : E) ∉ Set.range (algebraMap F E)) :
    indClassFun (GL2NonSplitTorus F E hE) f (GL2NonSplitTorusHom F E hE u) =
      f (unitsEquiv hE u) + f (unitsEquiv hE (u ^ Nat.card F)) := by
  classical
  have hgmem : GL2NonSplitTorusHom F E hE u ∈ GL2NonSplitTorus F E hE :=
    (mem_iff hE).mpr ⟨u, rfl⟩
  have hgmem' : GL2NonSplitTorusHom F E hE (u ^ Nat.card F) ∈ GL2NonSplitTorus F E hE :=
    (mem_iff hE).mpr ⟨_, rfl⟩
  obtain ⟨d, hdg, hdT, hdnorm⟩ := exists_frobenius_conjugator_normalizes hE hu
  have hne : ((1 : GL (Fin 2) F) : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) ≠
      (d : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) := by
    intro h
    rw [QuotientGroup.eq, inv_one, one_mul] at h
    exact hdT h
  -- the torus is abelian, so every function on it is invariant under conjugation
  have hcomm : ∀ y z : (GL2NonSplitTorus F E hE), z * y * z⁻¹ = y := by
    intro y z
    obtain ⟨p, hp⟩ := (mem_iff hE).mp y.2
    obtain ⟨r, hr⟩ := (mem_iff hE).mp z.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hp, ← hr, ← map_inv, ← map_mul,
      ← map_mul, mul_comm r p, mul_assoc, mul_inv_cancel, mul_one]
  rw [indClassFun_eq_sum_of_smul_eq_self_mem f _
    ({((1 : GL (Fin 2) F) : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE),
      (d : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE)} : Finset _) ?_, Finset.sum_pair hne]
  · congr 1
    · rw [indTerm_eq_of_mk_eq_of_conj (fun y z => congrArg f (hcomm y z)) _ _
          (1 : GL (Fin 2) F) (QuotientGroup.out_eq' _), indTerm_one,
        dite_eq_left hgmem]
      exact congrArg f (Subtype.ext (coe_unitsEquiv_apply hE u).symm)
    · rw [indTerm_eq_of_mk_eq_of_conj (fun y z => congrArg f (hcomm y z)) _ _ d
          (QuotientGroup.out_eq' _), indTerm_apply, hdg,
        dite_eq_left hgmem']
      exact congrArg f (Subtype.ext (coe_unitsEquiv_apply hE _).symm)
  · intro t ht
    rw [← QuotientGroup.out_eq' t] at ht ⊢
    rcases quotient_eq_one_or_frobenius_conjugator_of_conj_mem hE hu hdg hdnorm
      ((smul_quotientGroup_mk_eq_self_iff _ _ _).mp ht) with h | h <;> simp [h]

end Elliptic

end GL2NonSplitTorus

end TauCeti
