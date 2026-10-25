/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Trace
-- Private: the `changeForm`, constant-term, monomial and dimension lemmas below are used only
-- inside proofs.
import TauCeti.Algebra.CharP.Invertible
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# The scalar-part trace of a Clifford algebra

Over a commutative ring in which `2` is invertible, Mathlib's `CliffordAlgebra.equivExterior`
identifies `CliffordAlgebra Q` with `ExteriorAlgebra R M` as a module. Reading off the degree-zero
component on the exterior side gives a linear functional

  `CliffordAlgebra.scalarTrace Q : CliffordAlgebra Q →ₗ[R] R`,

the *scalar part* `τ` of a multivector. It is normalized by `τ 1 = 1`, kills every generator, and
on a product of two generators returns the symmetric bilinear form of `Q`:
`τ (ι Q a * ι Q b) = QuadraticMap.associated Q a b`.

Although it is defined without any finiteness, `τ` behaves like a trace: it is invariant under the
grade involution and under reversion, it vanishes on the odd part, and it is cyclic,
`τ (x * y) = τ (y * x)`. When `M` is spanned by pairwise orthogonal vectors these properties
characterize it: every cyclic functional invariant under the grade involution is a multiple of
`τ`. Applied to the trace of the left regular representation this gives the regular-trace
formula: over a field in which `2` is invertible, for every quadratic form on a
finite-dimensional space, `τ x = 2 ^ (-finrank K V) * trace (x * ·)`. In particular `τ` is
preserved by every algebra isomorphism between Clifford algebras of finite-dimensional spaces.

## Main definitions

* `CliffordAlgebra.scalarTrace`: the scalar part of a multivector.

## Main results

* `CliffordAlgebra.scalarTrace_one`, `CliffordAlgebra.scalarTrace_ι` and
  `CliffordAlgebra.scalarTrace_ι_mul_ι`: the values on `1`, on a generator and on a product of two
  generators.
* `CliffordAlgebra.scalarTrace_involute` and `CliffordAlgebra.scalarTrace_reverse`: invariance
  under the grade involution and under reversion.
* `CliffordAlgebra.scalarTrace_eq_zero_of_mem_evenOdd_one`: the scalar part of an odd element is
  zero.
* `CliffordAlgebra.scalarTrace_mul_comm`: cyclicity, `τ (x * y) = τ (y * x)`.
* `CliffordAlgebra.scalarTrace_prod_map_ι_append_cons_eq_zero`: a product of vectors with a factor
  orthogonal to all the others has scalar part zero.
* `CliffordAlgebra.eq_smul_scalarTrace`: for `M` spanned by pairwise orthogonal vectors, every
  cyclic functional invariant under the grade involution is `f 1 • τ`.
* `CliffordAlgebra.trace_mulLeft_eq_finrank_mul_scalarTrace`: the regular-trace formula for a
  finite free module spanned by pairwise orthogonal vectors, and its field form
  `CliffordAlgebra.trace_mulLeft_eq_two_pow_mul_scalarTrace`, with no hypothesis on the form.
* `CliffordAlgebra.scalarTrace_eq_of_algEquiv`: over a field, the scalar part is preserved by
  algebra isomorphisms between Clifford algebras of finite-dimensional spaces.

## Implementation notes

The invariances are transported from the exterior algebra, where the constant term
`ExteriorAlgebra.algebraMapInv` is visibly invariant, along `equivExterior`; this needs that
`equivExterior` intertwines the grade involutions and the reversions
(`CliffordAlgebra.equivExterior_involute`, `CliffordAlgebra.equivExterior_reverse`). Cyclicity
reduces, by induction on the left factor, to moving one generator `ι Q m` from the left of `x` to
its right; Mathlib's `CliffordAlgebra.changeForm_ι_mul` and its right-handed counterpart
`CliffordAlgebra.changeForm_mul_ι` turn the two scalar parts into the constant terms of a left and
a right contraction, which agree by `ExteriorAlgebra.algebraMapInv_contractRight`.

The characterization needs no basis of the Clifford algebra: the products of the spanning
orthogonal vectors span it (`CliffordAlgebra.span_prod_map_ι_sublist_eq_top`), and a cyclic
functional invariant under the grade involution kills each nonempty such product, because the
product is either odd or anticommutes with its first factor.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators and the change of form.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  (Q : QuadraticForm R M)

/-- The **scalar part** of an element of a Clifford algebra: its degree-zero component under the
module isomorphism `CliffordAlgebra.equivExterior` with the exterior algebra. -/
noncomputable def scalarTrace : CliffordAlgebra Q →ₗ[R] R :=
  ExteriorAlgebra.algebraMapInv.toLinearMap ∘ₗ (equivExterior Q).toLinearMap

/-- The scalar part is the constant term of the image in the exterior algebra. -/
theorem scalarTrace_apply (x : CliffordAlgebra Q) :
    scalarTrace Q x = ExteriorAlgebra.algebraMapInv (equivExterior Q x) :=
  (rfl)

variable {Q}

@[simp]
theorem scalarTrace_algebraMap (r : R) :
    scalarTrace Q (algebraMap R (CliffordAlgebra Q) r) = r := by
  simp [scalarTrace_apply]

@[simp]
theorem scalarTrace_one : scalarTrace Q 1 = 1 := by
  simpa using scalarTrace_algebraMap (Q := Q) 1

@[simp]
theorem scalarTrace_ι (m : M) : scalarTrace Q (ι Q m) = 0 := by
  simp [scalarTrace_apply]

/-- The scalar part of a product of two generators is the symmetric bilinear form of `Q`. -/
@[simp]
theorem scalarTrace_ι_mul_ι (a b : M) :
    scalarTrace Q (ι Q a * ι Q b) = QuadraticMap.associated Q a b := by
  simp [scalarTrace_apply, changeForm_ι_mul_ι]

/-- The scalar part is invariant under the grade involution. -/
@[simp]
theorem scalarTrace_involute (x : CliffordAlgebra Q) :
    scalarTrace Q (involute x) = scalarTrace Q x := by
  rw [scalarTrace_apply, equivExterior_involute, ExteriorAlgebra.algebraMapInv_involute,
    scalarTrace_apply]

/-- The scalar part is invariant under reversion. -/
@[simp]
theorem scalarTrace_reverse (x : CliffordAlgebra Q) :
    scalarTrace Q (reverse x) = scalarTrace Q x := by
  rw [scalarTrace_apply, equivExterior_reverse, ExteriorAlgebra.algebraMapInv_reverse,
    scalarTrace_apply]

/-- The scalar part of an odd element is zero. -/
theorem scalarTrace_eq_zero_of_mem_evenOdd_one {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 1) :
    scalarTrace Q x = 0 :=
  TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R) <| by
    rw [← map_neg, ← involute_eq_of_mem_odd hx, scalarTrace_involute]

/-- A generator can be moved from the left to the right of `x` without changing the scalar part:
both scalar parts are minus the constant term of contracting `equivExterior Q x` against
`QuadraticMap.associated (-Q) m`, once from the left and once from the right. -/
private theorem scalarTrace_ι_mul (m : M) (x : CliffordAlgebra Q) :
    scalarTrace Q (ι Q m * x) = scalarTrace Q (x * ι Q m) := by
  simp only [scalarTrace_apply, equivExterior_ι_mul, equivExterior_mul_ι, map_sub, map_mul,
    ExteriorAlgebra.algebraMapInv_ι, zero_mul, mul_zero,
    ExteriorAlgebra.algebraMapInv_contractRight]

/-- **Cyclicity of the scalar part**: `τ (x * y) = τ (y * x)`. -/
theorem scalarTrace_mul_comm (x y : CliffordAlgebra Q) :
    scalarTrace Q (x * y) = scalarTrace Q (y * x) := by
  induction x using CliffordAlgebra.left_induction generalizing y with
  | algebraMap r => rw [Algebra.commutes]
  | add x x' hx hx' => rw [add_mul, mul_add, map_add, map_add, hx, hx']
  | ι_mul x m hx => rw [mul_assoc, scalarTrace_ι_mul, mul_assoc, hx, mul_assoc]

/-! ### Uniqueness and the regular trace -/

/-- A cyclic functional invariant under the grade involution vanishes on `ι Q a * p`, for `p` a
product of vectors orthogonal to `a`. If the number of factors of `p` is even, `ι Q a * p` is odd,
so the grade involution negates it; if it is odd, `ι Q a` anticommutes with `p`, so cyclicity
negates it. -/
private theorem apply_ι_mul_prod_eq_zero (f : CliffordAlgebra Q →ₗ[R] R)
    (hmul : ∀ x y, f (x * y) = f (y * x)) (hinv : ∀ x, f (involute x) = f x)
    {a : M} {l : List M} (h : ∀ x ∈ l, Q.IsOrtho x a) :
    f (ι Q a * (l.map (ι Q)).prod) = 0 := by
  refine TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R) ?_
  rcases Nat.even_or_odd l.length with he | ho
  · have hprod := involute_prod_map_ι (Q := Q) (a :: l)
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ, he.neg_one_pow, one_mul,
      neg_one_smul] at hprod
    nth_rewrite 1 [← hinv]
    rw [hprod, map_neg]
  · nth_rewrite 1 [hmul]
    rw [prod_map_ι_mul_ι_of_forall_isOrtho h, ho.neg_one_pow, neg_one_smul, map_neg]

/-- **A product with a factor orthogonal to all the others has scalar part zero**: if the factor
`a` of `l₁ ++ a :: l₂` is orthogonal to every other factor, then `τ` vanishes on the product.
Cyclicity moves `l₁` behind the remaining factors, so that `a` comes first. -/
theorem scalarTrace_prod_map_ι_append_cons_eq_zero {l₁ l₂ : List M} {a : M}
    (h : ∀ x ∈ l₁ ++ l₂, Q.IsOrtho x a) :
    scalarTrace Q ((l₁ ++ a :: l₂).map (ι Q)).prod = 0 := by
  rw [List.map_append, List.prod_append, scalarTrace_mul_comm, List.map_cons, List.prod_cons,
    mul_assoc, ← List.prod_append, ← List.map_append]
  exact apply_ι_mul_prod_eq_zero _ scalarTrace_mul_comm scalarTrace_involute fun x hx ↦
    h x (List.mem_append.mpr (List.mem_append.mp hx).symm)

/-- **The scalar part is the unique normalized cyclic functional invariant under the grade
involution**, as soon as `M` is spanned by a list of pairwise orthogonal vectors: every such
functional `f` is `f 1 • scalarTrace Q`. Both sides vanish on every product of at least one of the
spanning vectors, and these products span the Clifford algebra. -/
theorem eq_smul_scalarTrace {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) (f : CliffordAlgebra Q →ₗ[R] R)
    (hmul : ∀ x y, f (x * y) = f (y * x)) (hinv : ∀ x, f (involute x) = f x) :
    f = f 1 • scalarTrace Q := by
  refine LinearMap.ext_on (span_prod_map_ι_sublist_eq_top hspan) ?_
  rintro _ ⟨t, ht, rfl⟩
  cases t with
  | nil => simp
  | cons a t =>
    have horth : ∀ x ∈ t, Q.IsOrtho x a := fun x hx =>
      QuadraticMap.isOrtho_comm.mp (List.rel_of_pairwise_cons (hl.sublist ht) hx)
    simp only [List.map_cons, List.prod_cons, LinearMap.smul_apply, smul_eq_mul,
      apply_ι_mul_prod_eq_zero f hmul hinv horth,
      apply_ι_mul_prod_eq_zero (scalarTrace Q) scalarTrace_mul_comm scalarTrace_involute horth,
      mul_zero]

/-- **The scalar part is the normalized trace of the left regular representation**, for a finite
free module spanned by a list of pairwise orthogonal vectors:
`trace (x * ·) = finrank R (CliffordAlgebra Q) * scalarTrace Q x`. -/
theorem trace_mulLeft_eq_finrank_mul_scalarTrace [Module.Free R M] [Module.Finite R M]
    {l : List M} (hl : l.Pairwise Q.IsOrtho) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤)
    (x : CliffordAlgebra Q) :
    LinearMap.trace R (CliffordAlgebra Q) (LinearMap.mulLeft R x) =
      Module.finrank R (CliffordAlgebra Q) * scalarTrace Q x := by
  have hlmul (y : CliffordAlgebra Q) :
      LinearMap.mul R (CliffordAlgebra Q) y = LinearMap.mulLeft R y :=
    LinearMap.ext fun z => by simp
  have h := LinearMap.congr_fun (eq_smul_scalarTrace hl hspan
    (LinearMap.trace R (CliffordAlgebra Q) ∘ₗ (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap)
    (fun x y => by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      LinearMap.trace_mul_comm])
    (fun x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.coe_lmul_eq_mul, hlmul]
      rw [← involuteEquiv_apply, ← AlgEquiv.linearEquivConj_mulLeft, LinearMap.trace_conj'])) x
  simpa [hlmul, LinearMap.mulLeft_one, LinearMap.trace_one] using h

section Field

open Module

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

/-- **The scalar part is the normalized regular trace**: over a field in which `2` is invertible,
for every quadratic form on a finite-dimensional space,
`trace (x * ·) = 2 ^ finrank K V * scalarTrace Q x`. Every such form has an orthogonal basis, so
`CliffordAlgebra.trace_mulLeft_eq_finrank_mul_scalarTrace` applies. -/
theorem trace_mulLeft_eq_two_pow_mul_scalarTrace (x : CliffordAlgebra Q) :
    LinearMap.trace K (CliffordAlgebra Q) (LinearMap.mulLeft K x) =
      2 ^ finrank K V * scalarTrace Q x := by
  obtain ⟨l, hl, hspan⟩ := QuadraticMap.exists_list_pairwise_isOrtho Q
  rw [trace_mulLeft_eq_finrank_mul_scalarTrace hl hspan, finrank_eq_two_pow, Nat.cast_pow,
    Nat.cast_ofNat]

/-- The scalar part as the normalized regular trace,
`scalarTrace Q x = (2 ^ finrank K V)⁻¹ * trace (x * ·)`. -/
theorem scalarTrace_eq_inv_two_pow_mul_trace_mulLeft (x : CliffordAlgebra Q) :
    scalarTrace Q x =
      (2 ^ finrank K V)⁻¹ * LinearMap.trace K (CliffordAlgebra Q) (LinearMap.mulLeft K x) := by
  rw [trace_mulLeft_eq_two_pow_mul_scalarTrace,
    inv_mul_cancel_left₀ (pow_ne_zero _ (isUnit_of_invertible (2 : K)).ne_zero)]

/-- **The scalar part is invariant under algebra isomorphisms** between Clifford algebras of
finite-dimensional spaces: `scalarTrace Q' (e x) = scalarTrace Q x`. Both sides are normalized
regular traces, and the two spaces have the same dimension since their Clifford algebras do. -/
theorem scalarTrace_eq_of_algEquiv {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V'] {Q' : QuadraticForm K V'}
    (e : CliffordAlgebra Q ≃ₐ[K] CliffordAlgebra Q') (x : CliffordAlgebra Q) :
    scalarTrace Q' (e x) = scalarTrace Q x := by
  have hdim : finrank K V' = finrank K V := by
    have h := e.toLinearEquiv.finrank_eq
    rw [finrank_eq_two_pow, finrank_eq_two_pow] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  rw [scalarTrace_eq_inv_two_pow_mul_trace_mulLeft, scalarTrace_eq_inv_two_pow_mul_trace_mulLeft,
    hdim, ← AlgEquiv.linearEquivConj_mulLeft, LinearMap.trace_conj']

end Field

end CliffordAlgebra
