/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.SimilarityClass
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The ring of class functions on all square matrices over a finite field

For a field `k`, the *Hall algebra* `TauCeti.HallAlgebra k` is the space of complex functions on
the similarity classes of square matrices over `k` of all sizes, invertible or not
(`TauCeti.SimilarityClass k`). For finite `k` its product is
`(A ∗ A′)(g) = Σ_W A(g|_W) · A′(g|_{V/W})`, the sum over the `g`-invariant subspaces `W` of the
space `V` on which `g` acts. This is Green's form of parabolic (Harish-Chandra) induction of class
functions of the groups `GL_n(k)`; the identification with induction from block upper triangular
subgroups is not proved here.

## Main definitions

* `TauCeti.HallAlgebra k`: the complex functions on similarity classes over `k`.
* `TauCeti.HallAlgebra.constOne`: the constant function `𝟙` with value `1`.
* `TauCeti.HallAlgebra.rankPart n A`: the function `A|_n`, equal to `A` on classes of size `n` and
  to `0` elsewhere.
* `TauCeti.HallAlgebra.toClassFunction A n`: the class function `g ↦ A(g)` on `GL_n(k)`.
* `TauCeti.HallAlgebra.moebius`: the inverse `μ` of `𝟙` for the product.
* `TauCeti.HallAlgebra.eigenvalueSum K η`: the class function `β_η`, the sum of `η : K → ℂ` over
  the roots in a field `K ⊇ k` of the characteristic polynomial.
* `TauCeti.HallAlgebra.greenCuspidal K η`: Green's cuspidal function `C_η = (β_η · μ) ∗ 𝟙`.

## Main results

* `TauCeti.HallAlgebra.mul_ofEnd`: the product at the class of any endomorphism `g` is the sum
  over the `g`-invariant subspaces, whatever the space on which `g` acts.
* `TauCeti.HallAlgebra.instCommRing`, `TauCeti.HallAlgebra.instAlgebra`: for finite `k`, the
  product makes `HallAlgebra k` a commutative `ℂ`-algebra, with unit the indicator of the
  classes of size `0`. Associativity compares two sums over chains `U ≤ W` of invariant subspaces;
  commutativity holds because `g` is similar to its transpose (`ofEnd_dualMap`), for which the
  annihilators exchange the roles of `W` and `V ⧸ W`.
* `TauCeti.HallAlgebra.isUnit_constOne`: `𝟙` is invertible, since `(1 - 𝟙)^m` vanishes on the
  classes of size less than `m`, so the geometric series in `1 - 𝟙` is finite on each class.
* `TauCeti.HallAlgebra.greenCuspidal_ofEnd`: `C_η` at the class of `g` is the sum of `β_η · μ` at
  the classes of `g` on the `g`-invariant subspaces.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed. (1995), Chapters II
  and IV.
* Z. Chen, arXiv:2408.06191, Proposition 3.2 (the ring on all square matrices).
* Adapted from `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.Hall`, `New.Hall.constOne`, `New.Hall.rankPart`, `New.Hall.evalGL`, `New.Hall.moebius`,
  `New.Hall.mulMoebius`, `New.Hall.brauerLift`, `New.Hall.greenCuspidal`, `New.Hall.mul_apply`,
  `New.Hall.mul_simClassOf`, `New.Hall.mul_apply_eq_zero_of_dim_lt`, the `CommRing` and
  `Algebra ℂ` instances, `New.Hall.one_sub_constOne_pow_apply_eq_zero` and
  `New.Hall.isUnit_constOne`. The inverse of `𝟙` is built here from truncated geometric series
  rather than from a topology.
-/

public section

open Module TauCeti.SimilarityClass

namespace TauCeti

/-- The *Hall algebra* `𝓗(k)`: the complex functions on the similarity classes of square
matrices over `k` of all sizes. For finite `k` its product is the induction product over
invariant subspaces (`TauCeti.HallAlgebra.mul_ofEnd`).

The definition is reducible at implicit transparency, so that `A c` is type-correct when
rewriting, while instance search does not see the pointwise product of functions. -/
@[expose, implicit_reducible]
def HallAlgebra (k : Type*) [Field k] : Type _ :=
  SimilarityClass k → ℂ

namespace HallAlgebra

variable {k : Type*} [Field k]

/-- Class functions are added pointwise. -/
instance : AddCommGroup (HallAlgebra k) :=
  inferInstanceAs (AddCommGroup (SimilarityClass k → ℂ))

/-- Complex scalars act pointwise on class functions. -/
instance : Module ℂ (HallAlgebra k) :=
  inferInstanceAs (Module ℂ (SimilarityClass k → ℂ))

/-- Two functions on similarity classes are equal if they agree at every class. -/
@[ext]
theorem ext {F H : HallAlgebra k} (h : ∀ c, F c = H c) : F = H :=
  funext h

/-- Two functions on similarity classes are equal if they agree at the class of every
endomorphism of every `Fin n → k`. -/
theorem ext_ofEnd {F H : HallAlgebra k}
    (h : ∀ (n : ℕ) (g : Module.End k (Fin n → k)), F (ofEnd g) = H (ofEnd g)) : F = H :=
  ext fun c ↦ by rw [← ofEnd_rep c, h]

/-- The zero class function vanishes at every class. -/
@[simp]
theorem zero_apply (c : SimilarityClass k) : (0 : HallAlgebra k) c = 0 :=
  (rfl)

/-- Class functions are added pointwise. -/
@[simp]
theorem add_apply (F H : HallAlgebra k) (c : SimilarityClass k) : (F + H) c = F c + H c :=
  (rfl)

/-- Class functions are negated pointwise. -/
@[simp]
theorem neg_apply (F : HallAlgebra k) (c : SimilarityClass k) : (-F) c = -F c :=
  (rfl)

/-- Class functions are subtracted pointwise. -/
@[simp]
theorem sub_apply (F H : HallAlgebra k) (c : SimilarityClass k) : (F - H) c = F c - H c :=
  (rfl)

/-- Complex scalars act pointwise. -/
@[simp]
theorem smul_apply (a : ℂ) (F : HallAlgebra k) (c : SimilarityClass k) : (a • F) c = a * F c :=
  (rfl)

/-- Values of a finite sum of class functions. -/
@[simp]
theorem finset_sum_apply {ι : Type*} (s : Finset ι) (F : ι → HallAlgebra k)
    (c : SimilarityClass k) : (∑ i ∈ s, F i) c = ∑ i ∈ s, F i c :=
  Finset.sum_apply c s F

/-- The constant function `𝟙` with value `1` on every class, of every size. -/
def constOne : HallAlgebra k :=
  fun _ ↦ 1

/-- The value of `𝟙` at every class is `1`. -/
@[simp]
theorem constOne_apply (c : SimilarityClass k) : (constOne : HallAlgebra k) c = 1 :=
  (rfl)

/-- The rank-`n` part `A|_n` of `A`: equal to `A` on the classes of size `n` and to `0` on the
others. -/
def rankPart (n : ℕ) (F : HallAlgebra k) : HallAlgebra k :=
  fun c ↦ if c.dim = n then F c else 0

/-- The value of `A|_n` at a class. -/
@[simp]
theorem rankPart_apply (n : ℕ) (F : HallAlgebra k) (c : SimilarityClass k) :
    rankPart n F c = if c.dim = n then F c else 0 :=
  (rfl)

/-- The unit of the Hall algebra: the indicator of the classes of size `0`. -/
instance : One (HallAlgebra k) :=
  ⟨rankPart 0 constOne⟩

/-- The unit `1` is the indicator of the classes of size `0`. -/
@[simp]
theorem one_apply (c : SimilarityClass k) : (1 : HallAlgebra k) c = if c.dim = 0 then 1 else 0 :=
  (rfl)

/-- The value of `A` at the class of `g`, as a class function on `GL_n(k)`. -/
noncomputable def toClassFunction (F : HallAlgebra k) (n : Type*) [Fintype n] [DecidableEq n] :
    ClassFunction ℂ (GL n k) where
  val g := F (ofEnd (Matrix.toLin' (g : Matrix n n k)))
  property := ClassFunction.mem_iff.2 fun g h ↦ by
    -- Conjugating by `h` is conjugating the endomorphism `toLin' g` by `toLin' h`.
    refine congrArg F (ofEnd_eq_of_apply_eq (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
      fun x ↦ ?_).symm
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The class function `g ↦ A(g)` on `GL_n(k)` takes the value of `A` at the class of `g`. -/
@[simp]
theorem toClassFunction_apply (F : HallAlgebra k) {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n k) : (F.toClassFunction n).val g = F (ofEnd (Matrix.toLin' (g : Matrix n n k))) :=
  (rfl)

/-! ### The product -/

section Mul

/-- The *induction product*: `(A ∗ A′)(c)` is the sum, over the subspaces `W` invariant under the
chosen representative `g` of `c`, of `A` at the class of `g` on `W` times `A′` at the class of
`g` on the quotient by `W`. By `mul_ofEnd` any representative gives the same sum. The sum is a
`finsum`; it is meant for finite `k`, where there are finitely many invariant subspaces. For
infinite `k` the `finsum` may be a junk `0`. The lemmas of this section hold for any field, while
the ring laws (`instCommRing`, `instAlgebra`) and `isUnit_constOne` assume `Finite k`. -/
noncomputable instance : Mul (HallAlgebra k) where
  mul F H c := ∑ᶠ W : c.rep.invtSubmodule,
    F (ofEnd (c.rep.invtRestrict W.prop)) * H (ofEnd (c.rep.invtQuot W.prop))

variable {V V' : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup V'] [Module k V'] [Module.Finite k V'] {g : Module.End k V}
  {g' : Module.End k V'}

/-- The sum defining the product is the same for endomorphisms intertwined by a linear
isomorphism. -/
private theorem finsum_invtSubmodule_congr (F H : HallAlgebra k) (e : V ≃ₗ[k] V')
    (he : ∀ x, e (g x) = g' (e x)) :
    ∑ᶠ W : g.invtSubmodule, F (ofEnd (g.invtRestrict W.prop)) * H (ofEnd (g.invtQuot W.prop)) =
      ∑ᶠ U : g'.invtSubmodule,
        F (ofEnd (g'.invtRestrict U.prop)) * H (ofEnd (g'.invtQuot U.prop)) := by
  have he' (x : V') : e.symm (g' x) = g (e.symm x) := by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  -- Preimage under `e` and under `e⁻¹` are inverse bijections of the invariant subspaces.
  let E : g'.invtSubmodule ≃ g.invtSubmodule :=
    { toFun U := ⟨_, Submodule.comap_mem_invtSubmodule e.toLinearMap he U.prop⟩
      invFun W := ⟨_, Submodule.comap_mem_invtSubmodule e.symm.toLinearMap he' W.prop⟩
      left_inv U := by ext; simp
      right_inv W := by ext; simp }
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun U ↦ ?_
  simp only [E, Equiv.coe_fn_mk]
  rw [ofEnd_invtRestrict_comap e.toLinearMap he e.injective U.prop (by simp),
    ofEnd_invtQuot_comap e.toLinearMap he e.surjective U.prop]

/-- The product at the class of an endomorphism `g` of any finite-dimensional space `V` is the sum,
over the `g`-invariant subspaces `W`, of `A` at the class of `g` on `W` times `A′` at the class of
`g` on `V ⧸ W`. -/
theorem mul_ofEnd (F H : HallAlgebra k) (g : Module.End k V) :
    (F * H) (ofEnd g) =
      ∑ᶠ W : g.invtSubmodule,
        F (ofEnd (g.invtRestrict W.prop)) * H (ofEnd (g.invtQuot W.prop)) := by
  obtain ⟨e, he⟩ := ofEnd_eq_iff.1 (ofEnd_rep (ofEnd g))
  exact finsum_invtSubmodule_congr F H e he

/-- `mul_ofEnd` as a sum over a finite type. -/
theorem mul_ofEnd_eq_sum [Fintype g.invtSubmodule] (F H : HallAlgebra k) :
    (F * H) (ofEnd g) =
      ∑ W : g.invtSubmodule, F (ofEnd (g.invtRestrict W.prop)) * H (ofEnd (g.invtQuot W.prop)) := by
  rw [mul_ofEnd, finsum_eq_sum_of_fintype]

/-- If `A` vanishes on classes of size less than `m` and `A′` on classes of size less than `n`,
then `A ∗ A′` vanishes on classes of size less than `m + n`. -/
theorem mul_apply_eq_zero_of_dim_lt {F H : HallAlgebra k} {m n : ℕ}
    (hF : ∀ c : SimilarityClass k, c.dim < m → F c = 0)
    (hH : ∀ c : SimilarityClass k, c.dim < n → H c = 0) (c : SimilarityClass k)
    (hc : c.dim < m + n) : (F * H) c = 0 := by
  -- The sizes of `W` and of the quotient add up to `c.dim < m + n`, so one factor vanishes.
  rw [← ofEnd_rep c, mul_ofEnd]
  refine finsum_eq_zero_of_forall_eq_zero fun W ↦ ?_
  have h_dims := (W : Submodule k (Fin c.dim → k)).finrank_quotient_add_finrank
  rw [finrank_fin_fun] at h_dims
  rcases lt_or_ge (finrank k W) m with h_lt | h_ge
  · rw [hF _ (by simpa using h_lt), zero_mul]
  · rw [hH _ (by simp; omega), mul_zero]

/-- The value of `A ∗ A′` at a class `c` only depends on the values of `A′` at classes of size at
most `c.dim`. -/
theorem mul_apply_congr_right (F : HallAlgebra k) {H H' : HallAlgebra k} (c : SimilarityClass k)
    (h : ∀ c' : SimilarityClass k, c'.dim ≤ c.dim → H c' = H' c') : (F * H) c = (F * H') c := by
  rw [← ofEnd_rep c, mul_ofEnd, mul_ofEnd]
  refine finsum_congr fun W ↦ ?_
  rw [h]
  simpa using (W : Submodule k (Fin c.dim → k)).finrank_quotient_le

end Mul

/-! ### The ring laws -/

section Ring

attribute [local instance low] Fintype.ofFinite

variable {V : Type*} [AddCommGroup V] [Module k V]

variable [Finite k] [Module.Finite k V]

omit [Finite k] in
/-- The induction product with `0` on the left vanishes. -/
protected theorem zero_mul (F : HallAlgebra k) : 0 * F = 0 :=
  ext_ofEnd fun _ g ↦ by simp [mul_ofEnd]

omit [Finite k] in
/-- The induction product with `0` on the right vanishes. -/
protected theorem mul_zero (F : HallAlgebra k) : F * 0 = 0 :=
  ext_ofEnd fun _ g ↦ by simp [mul_ofEnd]

/-- The induction product distributes over sums on the right. -/
protected theorem left_distrib (F G H : HallAlgebra k) : F * (G + H) = F * G + F * H := by
  refine ext_ofEnd fun _ g ↦ ?_
  simp [mul_ofEnd_eq_sum, mul_add, Finset.sum_add_distrib]

/-- The induction product distributes over sums on the left. -/
protected theorem right_distrib (F G H : HallAlgebra k) : (F + G) * H = F * H + G * H := by
  refine ext_ofEnd fun _ g ↦ ?_
  simp [mul_ofEnd_eq_sum, add_mul, Finset.sum_add_distrib]

/-- The indicator of the classes of size `0` is a left unit for the induction product. -/
protected theorem one_mul (F : HallAlgebra k) : 1 * F = F := by
  refine ext_ofEnd fun _ g ↦ ?_
  -- Only `W = ⊥` contributes, and there the quotient map is the identity.
  rw [mul_ofEnd_eq_sum, Finset.sum_eq_single ⟨⊥, Module.End.invtSubmodule.bot_mem g⟩
    (fun W _ hW ↦ ?_) (by simp)]
  · rw [one_apply, ite_eq_left (by simp), one_mul, ofEnd_invtQuot_eq_of_surjective (g' := g)
      LinearMap.id (fun _ ↦ rfl) _ Function.surjective_id (by simp)]
  · have : W.val ≠ ⊥ := fun h ↦ hW (Subtype.ext h)
    simp [one_apply, Submodule.finrank_eq_zero, this]

/-- The indicator of the classes of size `0` is a right unit for the induction product. -/
protected theorem mul_one (F : HallAlgebra k) : F * 1 = F := by
  refine ext_ofEnd fun _ g ↦ ?_
  -- Only `W = ⊤` contributes, and there the restriction is `g` itself.
  rw [mul_ofEnd_eq_sum, Finset.sum_eq_single ⟨⊤, Module.End.invtSubmodule.top_mem g⟩
    (fun W _ hW ↦ ?_) (by simp)]
  · rw [one_apply, ite_eq_left (by simp [finrank_zero_of_subsingleton]), mul_one,
      ofEnd_invtRestrict_eq_of_injective (g := g) LinearMap.id (fun _ ↦ rfl) _
        Function.injective_id (by simp)]
  · have : W.val ≠ ⊤ := fun h ↦ hW (Subtype.ext h)
    have h_add := W.val.finrank_quotient_add_finrank
    have h_lt := Submodule.finrank_lt this
    rw [one_apply, ite_eq_right (by simp; omega), mul_zero]

/-- The term of a chain `U ≤ W` of invariant subspaces in the two iterated products. -/
private noncomputable def chainTerm (F G H : HallAlgebra k) (g : Module.End k V)
    (U W : g.invtSubmodule) : ℂ :=
  F (ofEnd (g.invtRestrict U.prop)) * G (ofEnd ((g.invtRestrict W.prop).invtQuot
    (Submodule.comap_mem_invtSubmodule W.val.subtype (g.coe_invtRestrict_apply W.prop) U.prop))) *
    H (ofEnd (g.invtQuot W.prop))

open scoped Classical in
/-- `((A ∗ B) ∗ C)(g)` is the sum of `chainTerm` over the chains `U ≤ W`, grouped by `W`. -/
private theorem mul_mul_ofEnd_term (F G H : HallAlgebra k) (g : Module.End k V)
    (W : g.invtSubmodule) [Fintype g.invtSubmodule] :
    (F * G) (ofEnd (g.invtRestrict W.prop)) * H (ofEnd (g.invtQuot W.prop)) =
      ∑ U ∈ Finset.univ.filter (fun U : g.invtSubmodule ↦ U.val ≤ W.val),
        chainTerm F G H g U W := by
  -- The invariant subspaces of `g` on `W` are the invariant subspaces of `g` inside `W`.
  rw [mul_ofEnd_eq_sum, Finset.sum_mul,
    ← Finset.filter_true_of_mem (s := Finset.univ)
      (p := fun U' ↦ LinearMap.ker W.val.subtype ≤ U'.val)
      (by simp),
    LinearMap.sum_invtSubmodule_comap W.val.subtype (g.coe_invtRestrict_apply W.prop)]
  simp only [Submodule.range_subtype]
  refine Finset.sum_congr rfl fun U hU ↦ ?_
  rw [chainTerm, ofEnd_invtRestrict_comap _ (g.coe_invtRestrict_apply W.prop)
    W.val.injective_subtype U.prop (by simpa using (Finset.mem_filter.1 hU).2)]

open scoped Classical in
/-- `(A ∗ (B ∗ C))(g)` is the sum of `chainTerm` over the chains `U ≤ W`, grouped by `U`. -/
private theorem mul_ofEnd_mul_term (F G H : HallAlgebra k) (g : Module.End k V)
    (U : g.invtSubmodule) [Fintype g.invtSubmodule] :
    F (ofEnd (g.invtRestrict U.prop)) * (G * H) (ofEnd (g.invtQuot U.prop)) =
      ∑ W ∈ Finset.univ.filter (fun W : g.invtSubmodule ↦ U.val ≤ W.val),
        chainTerm F G H g U W := by
  -- The invariant subspaces of `g` on `V ⧸ U` are the images of those containing `U`.
  have key := LinearMap.sum_invtSubmodule_comap U.val.mkQ
    (fun x ↦ (g.invtQuot_mk U.prop x).symm) (chainTerm F G H g U)
  rw [U.val.ker_mkQ, Finset.filter_true_of_mem (s := Finset.univ)
    (p := fun W' : (g.invtQuot U.prop).invtSubmodule ↦ W'.val ≤ LinearMap.range U.val.mkQ)
    (by simp)] at key
  rw [mul_ofEnd_eq_sum, Finset.mul_sum, key]
  refine Finset.sum_congr rfl fun W' _ ↦ ?_
  rw [chainTerm, ofEnd_invtQuot_invtRestrict_comap_mkQ U.prop W'.prop,
    ofEnd_invtQuot_comap _ (fun x ↦ (g.invtQuot_mk U.prop x).symm) U.val.mkQ_surjective W'.prop,
    mul_assoc]

/-- The induction product is associative. -/
protected theorem mul_assoc (F G H : HallAlgebra k) : F * G * H = F * (G * H) := by
  classical
  refine ext_ofEnd fun _ g ↦ ?_
  -- Both sides are sums over the chains `U ≤ W` of invariant subspaces.
  rw [mul_ofEnd_eq_sum, mul_ofEnd_eq_sum]
  simp only [mul_mul_ofEnd_term, mul_ofEnd_mul_term]
  exact Finset.sum_comm' (by simp)

/-- The induction product is commutative. -/
protected theorem mul_comm (F H : HallAlgebra k) : F * H = H * F := by
  refine ext_ofEnd fun _ g ↦ ?_
  -- Replace `g` by its transpose on the left; annihilators match the invariant subspaces of `g`
  -- and of its transpose, exchanging subspaces and quotients.
  conv_lhs => rw [← ofEnd_dualMap g]
  rw [mul_ofEnd_eq_sum, mul_ofEnd_eq_sum]
  let E : g.invtSubmodule ≃ Module.End.invtSubmodule g.dualMap :=
    { toFun W := ⟨_, Submodule.dualAnnihilator_mem_invtSubmodule W.prop⟩
      invFun W := ⟨_, Submodule.dualCoannihilator_mem_invtSubmodule W.prop⟩
      left_inv W := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
      right_inv W := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq }
  refine (Fintype.sum_equiv E _ _ fun W ↦ ?_).symm
  simp only [E, Equiv.coe_fn_mk, ofEnd_invtRestrict_dualAnnihilator W.prop,
    ofEnd_invtQuot_dualAnnihilator W.prop, mul_comm]

/-- For finite `k`, the induction product makes the class functions on all square matrices a
commutative ring, with unit the indicator of the classes of size `0`. -/
noncomputable instance instCommRing : CommRing (HallAlgebra k) where
  __ := (inferInstance : AddCommGroup (HallAlgebra k))
  mul_assoc := HallAlgebra.mul_assoc
  one_mul := HallAlgebra.one_mul
  mul_one := HallAlgebra.mul_one
  zero_mul := HallAlgebra.zero_mul
  mul_zero := HallAlgebra.mul_zero
  left_distrib := HallAlgebra.left_distrib
  right_distrib := HallAlgebra.right_distrib
  mul_comm := HallAlgebra.mul_comm

/-- For finite `k`, the class functions on all square matrices form a `ℂ`-algebra under the
induction product, with `ℂ` acting pointwise. -/
noncomputable instance instAlgebra : Algebra ℂ (HallAlgebra k) :=
  Algebra.ofModule
    (fun a F H ↦ ext_ofEnd fun _ g ↦ by
      -- Scalars come out of every term of the sum defining the product.
      simp [mul_ofEnd_eq_sum, Finset.mul_sum, mul_assoc])
    (fun a F H ↦ ext_ofEnd fun _ g ↦ by
      simp [mul_ofEnd_eq_sum, Finset.mul_sum, mul_left_comm])

/-! ### The constant function `𝟙` is a unit -/

/-- `(1 - 𝟙)^m` vanishes on the classes of size less than `m`. -/
theorem one_sub_constOne_pow_apply_eq_zero (m : ℕ) (c : SimilarityClass k) (hc : c.dim < m) :
    ((1 - constOne : HallAlgebra k) ^ m) c = 0 := by
  induction m generalizing c with
  | zero => exact absurd hc (Nat.not_lt_zero _)
  | succ m ih =>
    -- `1 - 𝟙` vanishes in size `0`, and such bounds add under products.
    rw [pow_succ]
    refine mul_apply_eq_zero_of_dim_lt ih (fun c hc ↦ ?_) c hc
    simp [one_apply, show c.dim = 0 by omega]

/-- The constant function `𝟙` is invertible for the induction product. -/
theorem isUnit_constOne : IsUnit (constOne : HallAlgebra k) := by
  -- The geometric series in `E = 1 - 𝟙` is finite at each class, since `E ^ i` vanishes on the
  -- classes of size less than `i`; its sum inverts `𝟙 = 1 - E`.
  let E : HallAlgebra k := 1 - constOne
  let μ : HallAlgebra k := fun c ↦ ∑ i ∈ Finset.range (c.dim + 1), (E ^ i) c
  refine IsUnit.of_mul_eq_one μ (ext fun c ↦ ?_)
  have h_trunc : ((constOne : HallAlgebra k) * μ) c =
      ((constOne : HallAlgebra k) * ∑ i ∈ Finset.range (c.dim + 1), E ^ i) c := by
    refine mul_apply_congr_right _ c fun c' hc' ↦ ?_
    rw [finset_sum_apply]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i hi hi' ↦ ?_
    exact one_sub_constOne_pow_apply_eq_zero i c' (by simp at hi hi'; omega)
  have h_one : (constOne : HallAlgebra k) = 1 - E := by simp [E]
  rw [h_trunc, h_one, mul_neg_geom_sum, sub_apply,
    one_sub_constOne_pow_apply_eq_zero _ c (by omega), sub_zero]

/-- The inverse `μ = 𝟙⁻¹` of the constant function `𝟙` for the induction product. -/
noncomputable def moebius : HallAlgebra k :=
  Ring.inverse constOne

/-- `μ` is a right inverse of `𝟙`. -/
@[simp]
theorem constOne_mul_moebius : (constOne : HallAlgebra k) * moebius = 1 :=
  Ring.mul_inverse_cancel _ isUnit_constOne

/-- `μ` is a left inverse of `𝟙`. -/
@[simp]
theorem moebius_mul_constOne : (moebius : HallAlgebra k) * constOne = 1 :=
  Ring.inverse_mul_cancel _ isUnit_constOne

end Ring

/-! ### Green's cuspidal functions -/

section Green

variable (K : Type*) [Field K] [Algebra k K]

/-- The eigenvalue sum `β_η` of a function `η : K → ℂ` on a field `K ⊇ k`: the class function
sending a class to the sum of `η` over the roots in `K` of its characteristic polynomial, counted
with multiplicity. -/
noncomputable def eigenvalueSum (η : K → ℂ) : HallAlgebra k :=
  fun c ↦ ((c.charpoly.aroots K).map η).sum

/-- The eigenvalue sum at the class of `g` is the sum of `η` over the roots of the
characteristic polynomial of `g`. -/
@[simp]
theorem eigenvalueSum_ofEnd (η : K → ℂ) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (g : Module.End k V) :
    eigenvalueSum K η (ofEnd g) = ((g.charpoly.aroots K).map η).sum := by
  rw [eigenvalueSum, charpoly_ofEnd]

/-- *Green's cuspidal function* `C_η = (β_η · μ) ∗ 𝟙`, where `β_η · μ` is the pointwise product of
the eigenvalue sum with the inverse `μ` of `𝟙`, and `∗` the induction product. -/
noncomputable def greenCuspidal [Finite k] (η : K → ℂ) : HallAlgebra k :=
  -- `HallAlgebra k` is by definition `SimilarityClass k → ℂ`, so the pointwise product is a
  -- function into `ℂ`; the `show` makes `*` the induction product rather than the pointwise one.
  (show HallAlgebra k from fun c ↦ eigenvalueSum K η c * moebius c) * constOne

/-- Green's cuspidal function is `F ∗ 𝟙` for the pointwise product `F = β_η · μ`. -/
theorem greenCuspidal_eq_mul_constOne [Finite k] (η : K → ℂ) {F : HallAlgebra k}
    (hF : ∀ c, F c = eigenvalueSum K η c * moebius c) : greenCuspidal K η = F * constOne := by
  rw [ext hF, greenCuspidal]

/-- Green's cuspidal function at the class of `g` is the sum, over the `g`-invariant subspaces `W`,
of `β_η · μ` at the class of `g` on `W`. -/
theorem greenCuspidal_ofEnd [Finite k] (η : K → ℂ) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (g : Module.End k V) :
    greenCuspidal K η (ofEnd g) =
      ∑ᶠ W : g.invtSubmodule, eigenvalueSum K η (ofEnd (g.invtRestrict W.prop)) *
        moebius (ofEnd (g.invtRestrict W.prop)) := by
  simp [greenCuspidal_eq_mul_constOne K η (F := fun c ↦ eigenvalueSum K η c * moebius c)
    fun _ ↦ rfl, mul_ofEnd, constOne_apply]

end Green

end HallAlgebra

end TauCeti
