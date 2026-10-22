/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Points

import Mathlib.Algebra.Group.End
import TauCeti.Algebra.Polynomial.Laurent.Polynomial

/-!
# The dynamic parabolic, unipotent and Levi subgroups of a cocharacter

Let `H` be a commutative Hopf algebra over `R`, so that `Spec H` is an affine group scheme `G`,
and let `l : H →ₐc[R] R[T;T⁻¹]` be a **cocharacter**, that is, a homomorphism of group schemes
`𝔾ₘ → G` written contravariantly on coordinate rings. The *dynamic method* attaches to `l`
three subgroups
of the convolution group `G(A) = H →ₐ[R] A` of `A`-points, for every commutative `R`-algebra `A`,
using only limits of one-parameter conjugation and no root data:

* the **parabolic** `P(l)(A)`: the points `g` for which `t ↦ l(t) · g · l(t)⁻¹` extends over
  `t = 0`;
* the **Levi** `Z(l)(A)`: the points centralized by `l`;
* the **unipotent** subgroup `U(l)(A)`: the points whose limit at `t = 0` is the identity.

Everything is phrased on the functor of points, which is where these conditions are honest: the
conjugate of `g` by the *generic* point `l(T)` is a point of `G` with values in the Laurent
polynomial ring `A[T;T⁻¹]`, and `g` lies in `P(l)(A)` exactly when that conjugate lies in the
image of the points with values in `A[X]`. Since `A[X] → A[T;T⁻¹]` is injective the extension is
unique, so extending and then evaluating at `X = 0` is a group homomorphism
`limit : P(l)(A) → G(A)`, whose kernel is `U(l)(A)`.

The main theorem is the **Levi decomposition on points**: `limit` takes values in `Z(l)(A)` and
restricts to the identity there, so it is a retraction of `P(l)(A)` onto `Z(l)(A)`. Consequently
`U(l)(A)` and `Z(l)(A)` generate `P(l)(A)`, meet trivially, and the resulting factorization is
unique; `U(l)(A)` is moreover normalized by `P(l)(A)`. That `limit g` is centralized by `l` is
the generic identity `l(T) · F(X) · l(T)⁻¹ = F(T · X)` over `A[X][T;T⁻¹]`, proved by comparing
two substitutions inside `A[T;T⁻¹][T';T'⁻¹]`, where the cocycle relation
`l(T · T') = l(T) · l(T')` is available; specializing that identity at `X = 0` gives the
statement.

All three subgroups are preserved by change of value algebra, so they are subgroup functors of
the functor of points, and `limit` is natural. Representability of these subfunctors by closed
subschemes is not addressed here. For a commutative affine group the whole construction
degenerates: `P(l)` and `Z(l)` are everything and `U(l)` is trivial.

## Main declarations

* `TauCeti.Cocharacter.conjugate`: conjugation by the generic point `l(T)`.
* `TauCeti.Cocharacter.parabolic`, `TauCeti.Cocharacter.levi` and
  `TauCeti.Cocharacter.unipotent`: the three dynamic subgroups.
* `TauCeti.Cocharacter.limit`: the limit homomorphism `P(l)(A) → G(A)`.
* `TauCeti.Cocharacter.limit_of_mem_levi` and `TauCeti.Cocharacter.limit_mem_levi`: the limit is
  a retraction of the dynamic parabolic onto its Levi subgroup.
* `TauCeti.Cocharacter.coeff_coeff_conjugate_conjugate`: the cocycle identity for conjugation by
  the generic point, on coefficients.
* `TauCeti.Cocharacter.unipotent_sup_levi`, `TauCeti.Cocharacter.unipotent_inf_levi`,
  `TauCeti.Cocharacter.conj_mem_unipotent` and
  `TauCeti.Cocharacter.eq_of_unipotent_mul_levi_eq`: the Levi decomposition.
* `TauCeti.Cocharacter.parabolic_le_comap`, `TauCeti.Cocharacter.levi_le_comap` and
  `TauCeti.Cocharacter.unipotent_le_comap`: the three subgroups are subgroup functors.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

The polynomial and Laurent point maps are developed for bialgebras in
`TauCeti.Algebra.AlgebraicGroup.Dynamic.Points`. The subgroup constructions here additionally
use the antipode, and are formulated for possibly noncommutative Hopf algebras as well.
-/

public section

open WithConv

namespace TauCeti

namespace Cocharacter

variable {R H A B : Type*} [CommSemiring R] [Semiring H]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

variable [_root_.HopfAlgebra R H]

/-! ### Conjugation by the generic point -/

variable (A) in
/-- **Conjugation by the generic point of a cocharacter**: the group homomorphism
`G(A) → G(A[T;T⁻¹])` sending an `A`-point `g` to `l(T) · g · l(T)⁻¹`. -/
noncomputable def conjugate (l : H →ₐc[R] LaurentPolynomial R) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] LaurentPolynomial A) :=
  (MulAut.conj (genericPoint A l)).toMonoidHom.comp (constPoint A)

/-- Conjugation by the generic point acts as `g ↦ l(T) · g · l(T)⁻¹`. -/
@[simp]
theorem conjugate_apply (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] A)) :
    conjugate A l g = genericPoint A l * constPoint A g * (genericPoint A l)⁻¹ := by
  rw [conjugate, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

section Naturality

variable (φ : A →ₐ[R] B) (l : H →ₐc[R] LaurentPolynomial R)

/-- **Conjugation by the generic point, pushed forward along an arbitrary homomorphism `ψ` out of
`A[T;T⁻¹]`**: it becomes conjugation by the value of the cocharacter at the image of `T`. -/
theorem mapValue_conjugate {C : Type*} [CommSemiring C] [Algebra R C]
    (ψ : LaurentPolynomial A →ₐ[R] C) (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue ψ (conjugate A l g) =
      pointsHom C l (Units.map ψ.toMonoidHom (LaurentPolynomial.genericUnit A)) *
        AlgHom.mapValue (ψ.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A))) g *
        (pointsHom C l (Units.map ψ.toMonoidHom (LaurentPolynomial.genericUnit A)))⁻¹ := by
  rw [conjugate_apply, map_mul, map_mul, map_inv, genericPoint_eq_pointsHom,
    mapValue_pointsHom, constPoint_apply, ← AlgHom.mapValue_apply, AlgHom.mapValue_comp,
    MonoidHom.comp_apply]

/-- Evaluating generic conjugation at the Laurent parameter one recovers the original point. -/
theorem mapValue_laurentEval_one_conjugate (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue ((laurentEval (R := A) (1 : Aˣ)).restrictScalars R)
      (conjugate A l g) = g := by
  set e : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) (1 : Aˣ)).restrictScalars R
  rw [mapValue_conjugate]
  have hu : Units.map e.toMonoidHom (LaurentPolynomial.genericUnit A) = 1 := by
    ext
    simp [e]
  have hc : e.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) = AlgHom.id R A := by
    ext a
    simp [e]
  rw [hu, hc]
  simp

/-- **Conjugation by the generic point is natural in the value algebra.** -/
theorem mapValue_conjugate_mapAlgHom (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (conjugate A l g) =
      conjugate B l (AlgHom.mapValue φ g) := by
  simp only [conjugate_apply, map_mul, map_inv, mapValue_genericPoint, mapValue_constPoint]

end Naturality

/-! ### The dynamic parabolic and its limit homomorphism -/

variable (A) in
/-- **The dynamic parabolic subgroup `P(l)(A)`**: the `A`-points `g` of the affine group such
that the conjugate `l(T) · g · l(T)⁻¹` extends over the origin, that is, lies in the image of
the `A[X]`-points. Geometrically, these are the points for which `lim_{t → 0} l(t) g l(t)⁻¹`
exists. -/
noncomputable def parabolic (l : H →ₐc[R] LaurentPolynomial R) :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  (ofPolyPoint (R := R) (H := H) A).range.comap (conjugate A l)

variable {l : H →ₐc[R] LaurentPolynomial R}

/-- Membership in the dynamic parabolic is the existence of an extension over the origin. -/
theorem mem_parabolic_iff {g : WithConv (H →ₐ[R] A)} :
    g ∈ parabolic A l ↔ ∃ F : WithConv (H →ₐ[R] Polynomial A), ofPolyPoint A F = conjugate A l g :=
  Iff.rfl

/-- An extension over the origin exhibits membership in the dynamic parabolic. -/
theorem mem_parabolic_of_eq {g : WithConv (H →ₐ[R] A)} {F : WithConv (H →ₐ[R] Polynomial A)}
    (hF : ofPolyPoint A F = conjugate A l g) : g ∈ parabolic A l :=
  ⟨F, hF⟩

/-- Membership in the dynamic parabolic is the vanishing of every negative coefficient of the
conjugation family. -/
theorem mem_parabolic_iff_forall_coeff_conjugate_eq_zero {g : WithConv (H →ₐ[R] A)} :
    g ∈ parabolic A l ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → ((conjugate A l g).ofConv h).coeff n = 0 := by
  rw [mem_parabolic_iff, ← exists_algHom_toLaurent_comp_eq_iff]
  constructor
  · rintro ⟨F, hF⟩
    rw [ofPolyPoint_apply] at hF
    exact ⟨F.ofConv, congrArg ofConv hF⟩
  · rintro ⟨F, hF⟩
    refine ⟨toConv F, ?_⟩
    rw [ofPolyPoint_apply]
    exact congrArg toConv hF

variable (A l) in
/-- The unique `A[X]`-point extending the conjugate of a point of the dynamic parabolic. -/
noncomputable def extend : parabolic A l →* WithConv (H →ₐ[R] Polynomial A) :=
  (MonoidHom.ofInjective (ofPolyPoint_injective (R := R) (H := H) A)).symm.toMonoidHom.comp
    (MonoidHom.codRestrict ((conjugate A l).comp (parabolic A l).subtype) _ fun g => g.2)

/-- The chosen extension does induce the conjugate it extends. -/
@[simp]
theorem ofPolyPoint_extend (g : parabolic A l) :
    ofPolyPoint A (extend A l g) = conjugate A l (g : WithConv (H →ₐ[R] A)) := by
  have := (MonoidHom.ofInjective (ofPolyPoint_injective (R := R) (H := H) A)).apply_symm_apply
    (⟨conjugate A l (g : WithConv (H →ₐ[R] A)), g.2⟩ : (ofPolyPoint (R := R) (H := H) A).range)
  exact congrArg Subtype.val this

/-- The extension over the origin is unique. -/
theorem extend_unique {g : parabolic A l} {F : WithConv (H →ₐ[R] Polynomial A)}
    (hF : ofPolyPoint A F = conjugate A l (g : WithConv (H →ₐ[R] A))) : extend A l g = F :=
  ofPolyPoint_injective A (by rw [ofPolyPoint_extend, hF])

variable (A l) in
/-- **The limit homomorphism** `P(l)(A) → G(A)`, `g ↦ lim_{t → 0} l(t) g l(t)⁻¹`. It is a group
homomorphism because it is the composite of two group homomorphisms: extension over the origin
and evaluation there. -/
noncomputable def limit : parabolic A l →* WithConv (H →ₐ[R] A) :=
  (evalZeroPoint A).comp (extend A l)

/-- The limit is the extension over the origin, evaluated there. -/
theorem limit_apply (g : parabolic A l) : limit A l g = evalZeroPoint A (extend A l g) := by
  rw [limit, MonoidHom.comp_apply]

/-- The dynamic limit evaluates the constant coefficient of the conjugation family. -/
theorem limit_apply_eq_coeff_conjugate (g : parabolic A l) (h : H) :
    (limit A l g).ofConv h = ((conjugate A l g.1).ofConv h).coeff 0 := by
  rw [← ofPolyPoint_extend g, ofPolyPoint_apply, limit_apply, evalZeroPoint_apply]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_toLaurentAlg, Polynomial.coe_aeval_eq_eval,
    ← Polynomial.coeff_zero_eq_eval_zero, LaurentPolynomial.coeff_toLaurent]
  exact (Finsupp.mapDomain_apply_of_injective
    (Nat.castEmbedding (R := ℤ)).injective _ 0).symm

/-- Evaluating the extending conjugation family at one recovers the original point. -/
@[simp]
theorem toConv_aeval_one_comp_extend (g : parabolic A l) :
    toConv (((Polynomial.aeval (1 : A)).restrictScalars R).comp (extend A l g).ofConv) =
      g.1 := by
  rw [← AlgHom.mapValue_apply]
  let e : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) (1 : Aˣ)).restrictScalars R
  have he : e.comp (Polynomial.toLaurentAlg.restrictScalars R) =
      (Polynomial.aeval (1 : A)).restrictScalars R := by
    ext a <;> simp [e]
  rw [← he, AlgHom.mapValue_comp, MonoidHom.comp_apply,
    AlgHom.mapValue_apply (Polynomial.toLaurentAlg.restrictScalars R),
    ← ofPolyPoint_apply, ofPolyPoint_extend]
  exact mapValue_laurentEval_one_conjugate l g.1

/-! ### The Levi and unipotent parts -/

variable (A) in
/-- **The dynamic Levi subgroup `Z(l)(A)`**: the `A`-points centralized by the cocharacter, that
is, those fixed by conjugation by the generic point `l(T)`. -/
noncomputable def levi (l : H →ₐc[R] LaurentPolynomial R) :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  MonoidHom.eqLocus (conjugate A l) (constPoint A)

/-- Membership in the Levi subgroup means being fixed by conjugation by `l(T)`. -/
theorem mem_levi_iff {g : WithConv (H →ₐ[R] A)} :
    g ∈ levi A l ↔ conjugate A l g = constPoint A g :=
  Iff.rfl

/-- The Levi subgroup is contained in the dynamic parabolic: a fixed point extends by a
constant. -/
theorem levi_le_parabolic : levi A l ≤ parabolic A l := fun g hg =>
  mem_parabolic_of_eq (F := constPolyPoint A g) <| by
    rw [ofPolyPoint_constPolyPoint]
    exact (mem_levi_iff.mp hg).symm

/-- The extension of a point of the Levi subgroup is the constant point. -/
theorem extend_of_mem_levi {g : WithConv (H →ₐ[R] A)} (hg : g ∈ levi A l) :
    extend A l ⟨g, levi_le_parabolic hg⟩ = constPolyPoint A g :=
  extend_unique <| by
    rw [ofPolyPoint_constPolyPoint]
    exact (mem_levi_iff.mp hg).symm

/-- The limit homomorphism restricts to the identity on the Levi subgroup: it is a retraction of
the dynamic parabolic onto its Levi part. -/
theorem limit_of_mem_levi {g : WithConv (H →ₐ[R] A)} (hg : g ∈ levi A l) :
    limit A l ⟨g, levi_le_parabolic hg⟩ = g := by
  rw [limit_apply, extend_of_mem_levi hg, evalZeroPoint_constPolyPoint]

variable (A l) in
/-- **The dynamic unipotent subgroup `U(l)(A)`**: the points of the dynamic parabolic whose limit
is the identity. It is the kernel of the limit homomorphism, hence normal in `P(l)(A)`. -/
noncomputable def unipotent : Subgroup (WithConv (H →ₐ[R] A)) :=
  (limit A l).ker.map (parabolic A l).subtype

/-- Membership in the dynamic unipotent subgroup means lying in the parabolic with trivial
limit. -/
theorem mem_unipotent_iff {g : WithConv (H →ₐ[R] A)} :
    g ∈ unipotent A l ↔ ∃ hg : g ∈ parabolic A l, limit A l ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

/-- The dynamic unipotent subgroup is contained in the dynamic parabolic. -/
theorem unipotent_le_parabolic : unipotent A l ≤ parabolic A l :=
  Subgroup.map_subtype_le _

/-- The dynamic unipotent subgroup meets the Levi subgroup trivially. -/
theorem unipotent_inf_levi : unipotent A l ⊓ levi A l = ⊥ := by
  refine le_antisymm (fun g hg => ?_) bot_le
  obtain ⟨hgP, hg1⟩ := mem_unipotent_iff.mp hg.1
  rw [Subgroup.mem_bot, ← limit_of_mem_levi hg.2, ← hg1]

/-! ### Cocharacter values, and the commutative case -/

/-- **The values of the cocharacter lie in its own Levi subgroup.** They commute with the generic
point because the multiplicative group is commutative. -/
theorem pointsHom_mem_levi (u : Aˣ) : pointsHom A l u ∈ levi A l := by
  set v := Units.map (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).toMonoidHom u
  have h : constPoint A (pointsHom A l u) = pointsHom (LaurentPolynomial A) l v := by
    rw [constPoint_apply, ← AlgHom.mapValue_apply]
    exact mapValue_pointsHom _ l u
  rw [mem_levi_iff, conjugate_apply, h, genericPoint_eq_pointsHom,
    (pointsHom_commute (A := LaurentPolynomial A) l (LaurentPolynomial.genericUnit A) v).eq,
    mul_assoc,
    mul_inv_cancel, mul_one]

/-- For a commutative affine group every point is fixed by conjugation, so the dynamic Levi
subgroup attached to any cocharacter is everything. -/
theorem levi_eq_top [Coalgebra.IsCocomm R H] : levi A l = ⊤ :=
  eq_top_iff.mpr fun g _ => by
    rw [mem_levi_iff, conjugate_apply, mul_comm (genericPoint A l), mul_assoc, mul_inv_cancel,
      mul_one]

/-- For a commutative affine group the dynamic parabolic attached to any cocharacter is
everything. -/
theorem parabolic_eq_top [Coalgebra.IsCocomm R H] : parabolic A l = ⊤ :=
  eq_top_iff.mpr ((levi_eq_top (A := A) (l := l)).symm.le.trans levi_le_parabolic)

/-- For a commutative affine group the dynamic unipotent subgroup attached to any cocharacter is
trivial. -/
theorem unipotent_eq_bot [Coalgebra.IsCocomm R H] : unipotent A l = ⊥ := by
  have h := unipotent_inf_levi (A := A) (l := l)
  rwa [levi_eq_top, inf_top_eq] at h

/-! ### Functoriality of the dynamic subgroups in the value algebra -/

section Functoriality

variable (φ : A →ₐ[R] B)

/-- **The dynamic parabolic is a subgroup functor**: it is preserved by change of value
algebra. -/
theorem parabolic_le_comap : parabolic A l ≤ (parabolic B l).comap (AlgHom.mapValue φ) := by
  intro g hg
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  refine Subgroup.mem_comap.mpr
    (mem_parabolic_of_eq (F := AlgHom.mapValue (Polynomial.mapAlgHom φ) F) ?_)
  rw [← mapValue_ofPolyPoint, hF, mapValue_conjugate_mapAlgHom]

/-- The Levi subgroup is preserved by change of value algebra. -/
theorem levi_le_comap : levi A l ≤ (levi B l).comap (AlgHom.mapValue φ) := fun g hg => by
  rw [Subgroup.mem_comap, mem_levi_iff, ← mapValue_conjugate_mapAlgHom, mem_levi_iff.mp hg,
    mapValue_constPoint]

/-- The extension over the origin is natural in the value algebra. -/
theorem extend_mapValue (g : parabolic A l) :
    extend B l ⟨AlgHom.mapValue φ (g : WithConv (H →ₐ[R] A)), parabolic_le_comap φ g.2⟩ =
      AlgHom.mapValue (Polynomial.mapAlgHom φ) (extend A l g) :=
  extend_unique (by
    rw [← mapValue_ofPolyPoint, ofPolyPoint_extend, mapValue_conjugate_mapAlgHom])

/-- The limit homomorphism is natural in the value algebra. -/
theorem mapValue_limit (g : parabolic A l) :
    AlgHom.mapValue φ (limit A l g) =
      limit B l ⟨AlgHom.mapValue φ (g : WithConv (H →ₐ[R] A)), parabolic_le_comap φ g.2⟩ := by
  rw [limit_apply, limit_apply, extend_mapValue, mapValue_evalZeroPoint]

/-- The unipotent subgroup is preserved by change of value algebra. -/
theorem unipotent_le_comap : unipotent A l ≤ (unipotent B l).comap (AlgHom.mapValue φ) := by
  intro g hg
  obtain ⟨hgP, hg1⟩ := mem_unipotent_iff.mp hg
  refine Subgroup.mem_comap.mpr (mem_unipotent_iff.mpr ⟨parabolic_le_comap φ hgP, ?_⟩)
  rw [← mapValue_limit φ ⟨g, hgP⟩, hg1, map_one]

end Functoriality

/-! ### The limit lies in the Levi subgroup -/

section LeviRetraction

variable (R A) in
/-- The unit `T · T'` of `A[T;T⁻¹][T';T'⁻¹]`, the product of the two Laurent variables. -/
private noncomputable def prodUnit : (LaurentPolynomial (LaurentPolynomial A))ˣ :=
  Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
      (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom
        (LaurentPolynomial.genericUnit A) *
    LaurentPolynomial.genericUnit (LaurentPolynomial A)

variable (R A) in
/-- The substitution `T ↦ T · T'`, as an `R`-algebra homomorphism
`A[T;T⁻¹] → A[T;T⁻¹][T';T'⁻¹]`. -/
private noncomputable def prodSubst :
    LaurentPolynomial A →ₐ[R] LaurentPolynomial (LaurentPolynomial A) :=
  (laurentEval (R := A) (prodUnit R A)).restrictScalars R

variable (R A) in
/-- The substitution `X ↦ T · X`, as an `R`-algebra homomorphism `A[X] → A[X][T;T⁻¹]`. -/
private noncomputable def scaleSubst :
    Polynomial A →ₐ[R] LaurentPolynomial (Polynomial A) :=
  (Polynomial.aeval (R := A)
    (LaurentPolynomial.C (Polynomial.X : Polynomial A) * LaurentPolynomial.T 1)).restrictScalars R

private theorem scaleSubst_C (a : A) :
    scaleSubst R A (Polynomial.C a) = LaurentPolynomial.C (Polynomial.C a) := by
  simp [scaleSubst]

private theorem scaleSubst_X :
    scaleSubst R A Polynomial.X =
      LaurentPolynomial.C (Polynomial.X : Polynomial A) * LaurentPolynomial.T 1 := by
  simp [scaleSubst]

private theorem prodSubst_C (a : A) :
    prodSubst R A (LaurentPolynomial.C a) = LaurentPolynomial.C (LaurentPolynomial.C a) :=
  laurentEval_C (R := A) _ a

private theorem prodSubst_T :
    prodSubst R A (LaurentPolynomial.T 1) =
      (prodUnit R A : LaurentPolynomial (LaurentPolynomial A)) :=
  (laurentEval_T (R := A) (prodUnit R A) 1).trans (by rw [zpow_one])

private theorem map_prodSubst_genericUnit :
    Units.map (prodSubst R A).toMonoidHom (LaurentPolynomial.genericUnit A) = prodUnit R A :=
  Units.ext (by
    rw [Units.coe_map, LaurentPolynomial.genericUnit_val]
    exact prodSubst_T)

private theorem prodSubst_comp_const :
    (prodSubst R A).comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      (IsScalarTower.toAlgHom R (LaurentPolynomial A)
        (LaurentPolynomial (LaurentPolynomial A))).comp
          (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) :=
  AlgHom.ext fun a => prodSubst_C (R := R) a

private theorem prodUnit_val :
    (prodUnit R A : LaurentPolynomial (LaurentPolynomial A)) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1 := by
  rw [prodUnit, Units.val_mul, Units.coe_map]
  simp

private theorem prodSubst_comp_toLaurent :
    (prodSubst R A).comp (Polynomial.toLaurentAlg.restrictScalars R) =
      (AddMonoidAlgebra.mapAlgHom ℤ
        (Polynomial.toLaurentAlg.restrictScalars R)).comp (scaleSubst R A) := by
  ext a <;>
    simp [prodSubst_C, prodSubst_T, scaleSubst_C, scaleSubst_X, prodUnit_val]

private theorem mapAlgHom_evalZero_comp_scaleSubst :
    (AddMonoidAlgebra.mapAlgHom ℤ ((Polynomial.aeval (0 : A)).restrictScalars R)).comp
        (scaleSubst R A) =
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).comp
        ((Polynomial.aeval (0 : A)).restrictScalars R) := by
  ext a <;> simp [scaleSubst_C, scaleSubst_X]

/-- **The cocycle identity for generic conjugation**: conjugating by `l(T)` and then by `l(T')`
is conjugating by `l(T · T')`. -/
private theorem conjugate_conjugate (g : WithConv (H →ₐ[R] A)) :
    conjugate (LaurentPolynomial A) l (conjugate A l g) =
      AlgHom.mapValue (prodSubst R A) (conjugate A l g) := by
  rw [conjugate_apply, constPoint_apply, ← AlgHom.mapValue_apply,
    mapValue_conjugate, genericPoint_eq_pointsHom]
  have hconj (a b x : WithConv (H →ₐ[R]
      LaurentPolynomial (LaurentPolynomial A))) :
      a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
    simpa only [MulAut.conj_apply, MulAut.mul_apply] using
      congrArg (fun f : MulAut _ => f x)
        ((MulAut.conj : _ →* MulAut _).map_mul a b)
  rw [← hconj, ← map_mul, mapValue_conjugate, map_prodSubst_genericUnit,
    prodSubst_comp_const, prodUnit,
    mul_comm (Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
      (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom
        (LaurentPolynomial.genericUnit A))
      (LaurentPolynomial.genericUnit (LaurentPolynomial A))]

/-- The substitution `T ↦ T · T'` sends the monomial `a Tⁿ` to `(a Tⁿ) T'ⁿ`. -/
private theorem prodSubst_C_mul_T (a : A) (n : ℤ) :
    prodSubst R A (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T n) *
        LaurentPolynomial.T n := by
  have hT : prodSubst R A (LaurentPolynomial.T n) =
      LaurentPolynomial.C (LaurentPolynomial.T n) * LaurentPolynomial.T n := by
    have hc : Commute (Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
        (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom (LaurentPolynomial.genericUnit A))
        (LaurentPolynomial.genericUnit (LaurentPolynomial A)) :=
      Units.ext (mul_comm _ _)
    rw [prodSubst, AlgHom.restrictScalars_apply, laurentEval_T, prodUnit, hc.mul_zpow,
      Units.val_mul, ← map_zpow, Units.coe_map, LaurentPolynomial.genericUnit_zpow_val,
      LaurentPolynomial.genericUnit_zpow_val]
    simp
  rw [map_mul, prodSubst_C, hT, map_mul, mul_assoc]

/-- The coefficients of the substitution `T ↦ T · T'` are concentrated on the diagonal. -/
private theorem coeff_coeff_prodSubst (p : LaurentPolynomial A) (m n : ℤ) :
    ((prodSubst R A p).coeff n).coeff m = if m = n then p.coeff n else 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
      split_ifs <;> simp
  | C_mul_T k a =>
      rw [prodSubst_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp_all [-LaurentPolynomial.single_eq_C_mul_T]

/-- **The cocycle identity for generic conjugation, on coefficients.** Conjugating
`l(T) · g · l(T)⁻¹` once more by `l(T')` only produces monomials in `T · T'`: the coefficient of
`T'ⁿ Tᵐ` is the coefficient of `Tⁿ` in `l(T) · g · l(T)⁻¹` when `m = n`, and zero otherwise. -/
theorem coeff_coeff_conjugate_conjugate (g : WithConv (H →ₐ[R] A)) (h : H) (m n : ℤ) :
    (((conjugate (LaurentPolynomial A) l (conjugate A l g)).ofConv h).coeff n).coeff m =
      if m = n then ((conjugate A l g).ofConv h).coeff n else 0 := by
  rw [conjugate_conjugate, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    coeff_coeff_prodSubst]

/-- **The limit of a point of the dynamic parabolic lies in the Levi subgroup.** Together with
`limit_of_mem_levi` this exhibits the limit homomorphism as a retraction of the dynamic parabolic
onto its Levi subgroup. -/
theorem limit_mem_levi (g : parabolic A l) : limit A l g ∈ levi A l := by
  have hF : AlgHom.mapValue (Polynomial.toLaurentAlg.restrictScalars R) (extend A l g) =
      conjugate A l (g : WithConv (H →ₐ[R] A)) := by
    rw [AlgHom.mapValue_apply, ← ofPolyPoint_apply, ofPolyPoint_extend]
  -- The generic identity `l(T) · F(X) · l(T)⁻¹ = F(T · X)` over `A[X][T;T⁻¹]`.
  have key : conjugate (Polynomial A) l (extend A l g) =
      AlgHom.mapValue (scaleSubst R A) (extend A l g) := by
    have hinj : Function.Injective (AddMonoidAlgebra.mapAlgHom ℤ
        (Polynomial.toLaurentAlg.restrictScalars R : Polynomial A →ₐ[R] LaurentPolynomial A)) :=
      AddMonoidAlgebra.map_injective _ Polynomial.toLaurent_injective
    refine AlgHom.mapValue_injective hinj ?_
    have hl : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ
          (Polynomial.toLaurentAlg.restrictScalars R))
          (conjugate (Polynomial A) l (extend A l g)) =
        conjugate (LaurentPolynomial A) l (conjugate A l (g : WithConv (H →ₐ[R] A))) := by
      rw [mapValue_conjugate_mapAlgHom, hF]
    have hr : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ
          (Polynomial.toLaurentAlg.restrictScalars R))
          (AlgHom.mapValue (scaleSubst R A) (extend A l g)) =
        AlgHom.mapValue (prodSubst R A) (conjugate A l (g : WithConv (H →ₐ[R] A))) := by
      rw [← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, ← prodSubst_comp_toLaurent,
        AlgHom.mapValue_comp, MonoidHom.comp_apply, hF]
    rw [hl, hr]
    exact conjugate_conjugate _
  -- Specialize the generic identity at `X = 0`.
  rw [mem_levi_iff, limit_apply]
  simp only [evalZeroPoint_apply, constPoint_apply, ← AlgHom.mapValue_apply]
  rw [← mapValue_conjugate_mapAlgHom, key,
    ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, mapAlgHom_evalZero_comp_scaleSubst,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

end LeviRetraction

/-! ### The Levi decomposition of the dynamic parabolic -/

/-- Dividing a point of the dynamic parabolic by its limit lands in the unipotent part. -/
theorem mul_limit_inv_mem_unipotent {g : WithConv (H →ₐ[R] A)} (hg : g ∈ parabolic A l) :
    g * (limit A l ⟨g, hg⟩)⁻¹ ∈ unipotent A l := by
  have hz : limit A l ⟨g, hg⟩ ∈ levi A l := limit_mem_levi ⟨g, hg⟩
  have hmem : g * (limit A l ⟨g, hg⟩)⁻¹ ∈ parabolic A l :=
    mul_mem hg (inv_mem (levi_le_parabolic hz))
  refine mem_unipotent_iff.mpr ⟨hmem, ?_⟩
  have hsplit : (⟨g * (limit A l ⟨g, hg⟩)⁻¹, hmem⟩ : parabolic A l) =
      ⟨g, hg⟩ * (⟨limit A l ⟨g, hg⟩, levi_le_parabolic hz⟩ : parabolic A l)⁻¹ := rfl
  rw [hsplit, map_mul, map_inv, limit_of_mem_levi hz, mul_inv_cancel]

/-- **The dynamic Levi decomposition, on points**: every point of the dynamic parabolic is a
point of its unipotent part times a point of its Levi part. -/
theorem exists_mem_unipotent_mem_levi {g : WithConv (H →ₐ[R] A)} (hg : g ∈ parabolic A l) :
    ∃ u ∈ unipotent A l, ∃ z ∈ levi A l, g = u * z :=
  ⟨g * (limit A l ⟨g, hg⟩)⁻¹, mul_limit_inv_mem_unipotent hg, limit A l ⟨g, hg⟩,
    limit_mem_levi ⟨g, hg⟩, (inv_mul_cancel_right g _).symm⟩

/-- The unipotent part and the Levi part generate the dynamic parabolic. -/
theorem unipotent_sup_levi : unipotent A l ⊔ levi A l = parabolic A l := by
  refine le_antisymm (sup_le unipotent_le_parabolic levi_le_parabolic) fun g hg => ?_
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mem_unipotent_mem_levi hg
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hz)

/-- The dynamic unipotent subgroup is normalized by the dynamic parabolic: it is the kernel of a
homomorphism defined on the parabolic. -/
theorem conj_mem_unipotent {p u : WithConv (H →ₐ[R] A)} (hp : p ∈ parabolic A l)
    (hu : u ∈ unipotent A l) : p * u * p⁻¹ ∈ unipotent A l := by
  obtain ⟨huP, hu1⟩ := mem_unipotent_iff.mp hu
  have hmem : p * u * p⁻¹ ∈ parabolic A l := mul_mem (mul_mem hp huP) (inv_mem hp)
  refine mem_unipotent_iff.mpr ⟨hmem, ?_⟩
  have hsplit : (⟨p * u * p⁻¹, hmem⟩ : parabolic A l) =
      (⟨p, hp⟩ : parabolic A l) * ⟨u, huP⟩ * (⟨p, hp⟩ : parabolic A l)⁻¹ := rfl
  rw [hsplit, map_mul, map_mul, map_inv, hu1, mul_one, mul_inv_cancel]

/-- Generic conjugation carries a dynamic unipotent point to a dynamic unipotent point
with Laurent-polynomial values. -/
theorem conjugate_mem_unipotent {g : WithConv (H →ₐ[R] A)} (hg : g ∈ unipotent A l) :
    conjugate A l g ∈ unipotent (LaurentPolynomial A) l := by
  rw [conjugate_apply, genericPoint_eq_pointsHom]
  apply conj_mem_unipotent
    (levi_le_parabolic (pointsHom_mem_levi (LaurentPolynomial.genericUnit A)))
  simpa only [Subgroup.mem_comap, constPoint_apply, AlgHom.mapValue_apply] using
    unipotent_le_comap (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) hg

/-- The Levi decomposition of a point of the dynamic parabolic is unique. -/
theorem eq_of_unipotent_mul_levi_eq {u₁ u₂ z₁ z₂ : WithConv (H →ₐ[R] A)}
    (hu₁ : u₁ ∈ unipotent A l) (hu₂ : u₂ ∈ unipotent A l)
    (hz₁ : z₁ ∈ levi A l) (hz₂ : z₂ ∈ levi A l) (h : u₁ * z₁ = u₂ * z₂) :
    u₁ = u₂ ∧ z₁ = z₂ := by
  have hcross : u₂⁻¹ * u₁ = z₂ * z₁⁻¹ := by
    have h' := congrArg (fun t => u₂⁻¹ * t * z₁⁻¹) h
    simpa [mul_assoc] using h'
  have hbot : u₂⁻¹ * u₁ ∈ unipotent A l ⊓ levi A l :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hu₂) hu₁, hcross ▸ mul_mem hz₂ (inv_mem hz₁)⟩
  rw [unipotent_inf_levi, Subgroup.mem_bot, inv_mul_eq_one] at hbot
  refine ⟨hbot.symm, ?_⟩
  rw [hbot] at h
  exact mul_left_cancel h

end Cocharacter

end TauCeti

namespace BialgHom

open TauCeti TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable {A : Type w} [CommSemiring A] [Algebra R A]

/-- A dynamic Levi point commutes with every value of its cocharacter over the same algebra.
The converse requires testing after extensions of the value algebra. -/
theorem commute_pointsHom_of_mem_levi (l : H →ₐc[R] LaurentPolynomial R)
    {g : WithConv (H →ₐ[R] A)} (hg : g ∈ levi A l) (t : Aˣ) :
    Commute g (pointsHom A l t) := by
  let ψ : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) t).restrictScalars R
  have hconst : ψ.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      AlgHom.id R A := by
    ext a
    simp [ψ]
  have hunit : Units.map ψ.toMonoidHom (LaurentPolynomial.genericUnit A) = t := by
    ext
    simp [ψ]
  have h := congrArg (AlgHom.mapValue (H := H) ψ) (mem_levi_iff.mp hg)
  have heval : AlgHom.mapValue ψ (Cocharacter.constPoint A g) = g := by
    ext a
    simp [constPoint_apply, ψ]
  simp only [mapValue_conjugate, hunit, hconst, AlgHom.mapValue_id,
    MonoidHom.id_apply, heval] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

end BialgHom
