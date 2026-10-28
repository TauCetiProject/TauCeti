/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Space
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank

/-!
# Intersection numbers of line bundles with curves

Let `X` be a scheme, `k` a field and `ι : C ⟶ X` a morphism from a scheme `C` over `k`, typically
the inclusion of a proper curve in `X`, such as an irreducible component of the special fibre of
a model of a curve over a discrete valuation ring with residue field `k`. The intersection number
of a line bundle `L` on `X` with `C` is the degree of its restriction to `C`,

`(L · C) = deg_k (ι^* L) = χ(C, ι^* L) - χ(C, 𝒪_C)`,

where the degree is the Euler-characteristic degree `LineBundleClass.eulerDegree`. For a Cartier
divisor `D` on an integral scheme the intersection number `(D · C)` is that of the class
`D.toLineBundleClass` of `𝒪_X(D)`, and for an effective Cartier divisor with ideal sheaf
`I = 𝒪_X(-D)` it is that of the inverse of the class of `I`. Defining the pairing through line
bundles makes it compatible with pullback and invariant under linear equivalence, with no
hypothesis on `X`: a principal Cartier divisor has trivial class
(`Scheme.CartierDivisor.toLineBundleClass_principalCartierDivisor`), and the trivial class has
intersection number zero with every curve (`LineBundleClass.intersectionNumber_one`).

When `D` is an effective Cartier divisor whose inverse image `D ∩ C` on `C` is again an effective
Cartier divisor, that is, when `C` meets `D` properly, the intersection number is computed by the
scheme-theoretic intersection: on a proper curve `C` over `k` with finite-dimensional `H⁰` and
`H¹` of `𝒪_C`, the subscheme `D ∩ C` is finite over `k` and

`(-D · C) = -dim_k Γ(D ∩ C, 𝒪_{D ∩ C})`.

On such a curve, singular, reducible or nonreduced as it may be, twisting by `D` is additive:
`(L(-D) · C) = (L · C) + (-D · C)` and `(L(D) · C) = (L · C) + (D · C)` for every line bundle `L`
whose restriction to `C` has finite-dimensional `H⁰` and `H¹`, and
`(D · C) = dim_k Γ(D ∩ C, 𝒪_{D ∩ C}) ≥ 0`. On a regular model, this computes the intersection
numbers of a component `C` of the special fibre with the other components, which are effective
Cartier divisors meeting `C` properly. Full additivity of `L ↦ (L · C)` holds on a proper integral
curve whose codimension-one local rings are discrete valuation rings; for curves with singular
points, additivity on all of `Pic X` is not proved here.

Two effective Cartier divisors `D` and `E` on `X` which are proper curves over `k`, and which meet
properly in the sense that each cuts out an effective Cartier divisor on the other, have
`(-D · E) = (-E · D)`, both being `-dim_k Γ(D ∩ E, 𝒪_{D ∩ E})` for the same intersection
`D ∩ E = D ×_X E`, and so also `(D · E) = (E · D)`. The structures of `D` and `E` as schemes over
`k` need only agree on `D ∩ E`, as they do for curves in the special fibre of a scheme over a
discrete valuation ring with residue field `k`. For two distinct components of the special fibre
of a regular model, which are effective Cartier divisors meeting properly, these are the
off-diagonal entries of the intersection matrix.

## Main declarations

* `LineBundleClass.intersectionNumber k ι a`: the intersection number `(a · C)` of a line-bundle
  class `a` on `X` with `ι : C ⟶ X`;
* `LineBundleClass.intersectionNumber_pullback`: compatibility with pullback along a morphism
  `g : X ⟶ Y`, `(g^* a · C) = (a · (ι ≫ g))` with `C` mapping to `Y` by `ι ≫ g` (the cycle-level
  projection formula, with the degree of `C` over its image, is not proved here);
* `LineBundleClass.intersectionNumber_eq_zero_of_eq_comp`: every class has intersection number
  zero with a curve contracted to a point; combined with `intersectionNumber_pullback` applied to
  `ι ≫ g`, so does every pullback along a morphism `g` contracting the curve;
* `LineBundleClass.intersectionNumber_mk_toInvertibleSheaf`: `(-D · C) = -dim_k Γ(D ∩ C)` for an
  effective Cartier divisor `D` meeting a proper curve `C` properly;
* `LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf`: `(D · C) = dim_k Γ(D ∩ C)` for
  an effective Cartier divisor `D` meeting a proper curve `C` properly;
* `LineBundleClass.intersectionNumber_mk_mul_mk_toInvertibleSheaf` and
  `LineBundleClass.intersectionNumber_mk_mul_inv_mk_toInvertibleSheaf`: additivity of twisting a
  line bundle by an effective Cartier divisor meeting a proper curve properly;
* `LineBundleClass.intersectionNumber_mul` and `LineBundleClass.intersectionNumber_inv`:
  additivity on a regular proper integral curve, bundled as
  `LineBundleClass.intersectionNumberHom k ι : Pic X →+ ℤ`;
* `LineBundleClass.intersectionNumber_mk_toInvertibleSheaf_comm` and
  `LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_comm`: `(-D · E) = (-E · D)` and
  `(D · E) = (E · D)` for effective Cartier divisors `D` and `E` meeting properly.

## References

* [The Stacks Project, Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ): degrees of invertible
  modules on proper curves, and
  [Section 55.9](https://stacks.math.columbia.edu/tag/0C9U), where the intersection numbers of the
  components of the special fibre of a regular model are the degrees `deg(𝒪_X(Cᵢ)|_{Cⱼ})`.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1, on intersection numbers of
  divisors with vertical curves on arithmetic surfaces.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable (k : Type u) [Field k] {X Y C : Scheme.{u}} [C.Over (Spec (.of k))] (ι : C ⟶ X)

/-- The **intersection number** `(a · C)` of a line-bundle class `a` on `X` with a scheme `C` over
the field `k` mapping to `X` by `ι`: the Euler-characteristic degree over `k` of the pullback of
`a` to `C`. For a proper curve `C` this is the degree of the restriction of `a` to `C`. -/
def intersectionNumber (a : LineBundleClass X) : ℤ :=
  eulerDegree k (pullback ι a)

/-- The intersection number is the degree of the pulled-back class. -/
lemma intersectionNumber_def (a : LineBundleClass X) :
    intersectionNumber k ι a = eulerDegree k (pullback ι a) :=
  (rfl)

/-- The intersection number of the class of `L` is the degree of the pullback of `L`. -/
lemma intersectionNumber_mk (L : InvertibleSheaf X) :
    intersectionNumber k ι (mk L) = ((InvertibleSheaf.pullback ι).obj L).eulerDegree k := by
  rw [intersectionNumber_def, pullback_mk, eulerDegree_mk]

/-- The trivial class has intersection number zero with every curve. -/
@[simp]
lemma intersectionNumber_one : intersectionNumber k ι (1 : LineBundleClass X) = 0 := by
  rw [intersectionNumber_def, pullback_one, eulerDegree_one]

/-- **Compatibility with pullback.** The intersection number of the pullback of a class `a` along
`g : X ⟶ Y` with `ι : C ⟶ X` is the intersection number of `a` with `ι ≫ g`. -/
@[simp]
lemma intersectionNumber_pullback (g : X ⟶ Y) (a : LineBundleClass Y) :
    intersectionNumber k ι (pullback g a) = intersectionNumber k (ι ≫ g) a := by
  rw [intersectionNumber_def, intersectionNumber_def, pullback_comp]

/-- **Contracted curves.** If `ι` factors through a scheme `T` all of whose points specialize to
one point, for instance the spectrum of a local ring or of the residue field of a point of `X`,
then every class has intersection number zero with `C`. -/
theorem intersectionNumber_eq_zero_of_eq_comp {T : Scheme.{u}} (h : C ⟶ T) (j : T ⟶ X)
    (w : ι = h ≫ j) {t : T} (ht : ∀ y : T, y ⤳ t) (a : LineBundleClass X) :
    intersectionNumber k ι a = 0 := by
  rw [intersectionNumber_def, w, ← pullback_comp, eq_one_of_forall_specializes ht (pullback j a),
    pullback_one, eulerDegree_one]

section Effective

variable [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C).obj 1)]

/-- **Intersecting with an effective Cartier divisor.** Let `D` be an effective Cartier divisor on
`X` with ideal sheaf `I = 𝒪_X(-D)`, and let `C` be a proper curve over `k` with finite-dimensional
`H⁰(C, 𝒪_C)` and `H¹(C, 𝒪_C)`, on which the inverse image `D ∩ C` of `D` is an effective Cartier
divisor. Then `(-D · C) = -dim_k Γ(D ∩ C, 𝒪_{D ∩ C})`, the dimension being the rank of the finite
morphism `D ∩ C ⟶ Spec k` at the point `s`. -/
theorem intersectionNumber_mk_toInvertibleSheaf {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hI' : (I.comap ι).IsEffectiveCartier) (s : Spec (.of k)) :
    intersectionNumber k ι (mk hI.toInvertibleSheaf) =
      -(((I.comap ι).subschemeι ≫ C ↘ Spec (.of k)).finrank s : ℤ) := by
  -- Over a field every effective Cartier divisor is relative, hence finite on a proper curve.
  have : IsFinite ((I.comap ι).subschemeι ≫ C ↘ Spec (.of k)) := hI'.isFinite_subschemeι_comp
  rw [intersectionNumber_def, hI.pullback_mk_toInvertibleSheaf hI', eulerDegree_mk]
  exact hI'.eulerDegree_toInvertibleSheaf k _ s

/-- **Intersecting with `𝒪_X(D)`.** Let `D` be an effective Cartier divisor on `X` with ideal
sheaf `I = 𝒪_X(-D)`, so that `𝒪_X(D)` has class the inverse of that of `I`. On a proper curve `C`
over `k` with finite-dimensional `H⁰(C, 𝒪_C)` and `H¹(C, 𝒪_C)`, if `C` meets `D` properly then
`(D · C) = dim_k Γ(D ∩ C, 𝒪_{D ∩ C})`. In particular `(D · C) ≥ 0`. The curve `C` may be
singular, reducible or nonreduced. -/
theorem intersectionNumber_inv_mk_toInvertibleSheaf {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hI' : (I.comap ι).IsEffectiveCartier) (s : Spec (.of k)) :
    intersectionNumber k ι (mk hI.toInvertibleSheaf)⁻¹ =
      ((I.comap ι).subschemeι ≫ C ↘ Spec (.of k)).finrank s := by
  have : IsFinite ((I.comap ι).subschemeι ≫ C ↘ Spec (.of k)) := hI'.isFinite_subschemeι_comp
  rw [intersectionNumber_def, pullback_inv, hI.pullback_mk_toInvertibleSheaf hI']
  exact hI'.eulerDegree_inv_mk_toInvertibleSheaf k _ s

variable {I : X.IdealSheafData} (L : InvertibleSheaf X)
  [FiniteDimensional k (Cohomology ((InvertibleSheaf.pullback ι).obj L).obj 0)]
  [FiniteDimensional k (Cohomology ((InvertibleSheaf.pullback ι).obj L).obj 1)]

/-- **Additivity along an effective Cartier divisor.** Let `D` be an effective Cartier divisor on
`X` with ideal sheaf `I = 𝒪_X(-D)` meeting a proper curve `C` over `k` properly, where `C` has
finite-dimensional `H⁰` and `H¹` of its structure sheaf. For a line bundle `L` on `X` whose
restriction to `C` has finite-dimensional `H⁰` and `H¹`, `(L(-D) · C) = (L · C) + (-D · C)`. The
curve `C` may be singular, reducible or nonreduced. -/
theorem intersectionNumber_mk_mul_mk_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (hI' : (I.comap ι).IsEffectiveCartier) :
    intersectionNumber k ι (mk L * mk hI.toInvertibleSheaf) =
      intersectionNumber k ι (mk L) + intersectionNumber k ι (mk hI.toInvertibleSheaf) := by
  have : IsFinite ((I.comap ι).subschemeι ≫ C ↘ Spec (.of k)) := hI'.isFinite_subschemeι_comp
  rw [intersectionNumber_def, pullback_mul, pullback_mk, hI.pullback_mk_toInvertibleSheaf hI',
    hI'.eulerDegree_mk_mul_mk_toInvertibleSheaf k, intersectionNumber_mk, intersectionNumber_def,
    hI.pullback_mk_toInvertibleSheaf hI', eulerDegree_mk]

/-- **Additivity along the inverse of an effective Cartier divisor.** Let `D` be an effective
Cartier divisor on `X` with ideal sheaf `I = 𝒪_X(-D)` meeting a proper curve `C` over `k`
properly, where `C` has finite-dimensional `H⁰` and `H¹` of its structure sheaf. For a line
bundle `L` on `X` whose restriction to `C` has finite-dimensional `H⁰` and `H¹`,
`(L(D) · C) = (L · C) + (D · C)`. -/
theorem intersectionNumber_mk_mul_inv_mk_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (hI' : (I.comap ι).IsEffectiveCartier) :
    intersectionNumber k ι (mk L * (mk hI.toInvertibleSheaf)⁻¹) =
      intersectionNumber k ι (mk L) + intersectionNumber k ι (mk hI.toInvertibleSheaf)⁻¹ := by
  have : IsFinite ((I.comap ι).subschemeι ≫ C ↘ Spec (.of k)) := hI'.isFinite_subschemeι_comp
  rw [intersectionNumber_def, pullback_mul, pullback_mk, pullback_inv,
    hI.pullback_mk_toInvertibleSheaf hI', hI'.eulerDegree_mk_mul_inv_mk_toInvertibleSheaf k,
    hI'.eulerDegree_toInvertibleSheaf k _ default, intersectionNumber_mk,
    intersectionNumber_inv_mk_toInvertibleSheaf k ι hI hI' default, sub_neg_eq_add]

end Effective

section Regular

variable [IsIntegral C]
  [∀ y : CodimensionOnePoint C, IsDiscreteValuationRing (C.presheaf.stalk (y : C))]
  [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C).obj 1)]

/-- **Additivity of the intersection number** with a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings and whose `H¹(C, 𝒪_C)` is
finite-dimensional. -/
@[simp]
theorem intersectionNumber_mul (a b : LineBundleClass X) :
    intersectionNumber k ι (a * b) = intersectionNumber k ι a + intersectionNumber k ι b := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  simp only [intersectionNumber_def, pullback_mul]
  exact eulerDegree_mul k (coheight_le_of_relativeDimensionLE_of_field (d := 1) (C ↘ Spec (.of k)))
    _ _

/-- The inverse class has the opposite intersection number with a proper integral curve whose
codimension-one local rings are discrete valuation rings. -/
@[simp]
theorem intersectionNumber_inv (a : LineBundleClass X) :
    intersectionNumber k ι a⁻¹ = -intersectionNumber k ι a := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  rw [intersectionNumber_def, intersectionNumber_def, pullback_inv]
  exact eulerDegree_inv k (coheight_le_of_relativeDimensionLE_of_field (d := 1) (C ↘ Spec (.of k)))
    _

/-- The intersection number with a proper integral curve whose codimension-one local rings are
discrete valuation rings, as a homomorphism `Pic X →+ ℤ` on the additively written Picard
group. -/
def intersectionNumberHom : Additive (LineBundleClass X) →+ ℤ :=
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of k))
  have : IsNoetherian C := {}
  have : Fact (∀ y : C, Order.coheight y ≤ 1) :=
    ⟨coheight_le_of_relativeDimensionLE_of_field (d := 1) (C ↘ Spec (.of k))⟩
  (eulerDegreeHom k C).comp (MonoidHom.toAdditive (pullbackHom ι))

/-- The intersection-number homomorphism evaluates to the intersection number. -/
@[simp]
lemma intersectionNumberHom_apply (a : Additive (LineBundleClass X)) :
    intersectionNumberHom k ι a = intersectionNumber k ι a.toMul := by
  rw [intersectionNumberHom, AddMonoidHom.comp_apply, eulerDegreeHom_apply,
    MonoidHom.toAdditive_apply_apply, pullbackHom_apply, toMul_ofMul, intersectionNumber_def]

end Regular

section Symmetric

variable {D E : X.IdealSheafData} [D.subscheme.Over (Spec (.of k))]
  [E.subscheme.Over (Spec (.of k))]

section Effective

variable [IsProper (D.subscheme ↘ Spec (.of k))]
  [RelativeDimensionLE 1 (D.subscheme ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial D.subscheme).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial D.subscheme).obj 1)]
  [IsProper (E.subscheme ↘ Spec (.of k))]
  [RelativeDimensionLE 1 (E.subscheme ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial E.subscheme).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial E.subscheme).obj 1)]

/-- **Symmetry of the intersection pairing of effective Cartier divisors.** Let `D` and `E` be
effective Cartier divisors on `X` which are proper curves over `k` with finite-dimensional `H⁰`
and `H¹` of their structure sheaves, whose structure morphisms to `Spec k` agree on `D ×_X E`, and
which meet properly: the inverse image of each on the other is an effective Cartier divisor. Then
`(-D · E) = (-E · D)`, both sides being `-dim_k Γ(D ∩ E, 𝒪_{D ∩ E})`. -/
theorem intersectionNumber_mk_toInvertibleSheaf_comm (hD : D.IsEffectiveCartier)
    (hE : E.IsEffectiveCartier) (hDE : (D.comap E.subschemeι).IsEffectiveCartier)
    (hED : (E.comap D.subschemeι).IsEffectiveCartier)
    (w : pullback.fst E.subschemeι D.subschemeι ≫ E.subscheme ↘ Spec (.of k) =
      pullback.snd E.subschemeι D.subschemeι ≫ D.subscheme ↘ Spec (.of k)) :
    intersectionNumber k E.subschemeι (mk hD.toInvertibleSheaf) =
      intersectionNumber k D.subschemeι (mk hE.toInvertibleSheaf) := by
  -- Over a field every effective Cartier divisor is relative, hence finite on a proper curve.
  have : IsFinite ((E.comap D.subschemeι).subschemeι ≫ D.subscheme ↘ Spec (.of k)) :=
    hED.isFinite_subschemeι_comp
  rw [intersectionNumber_mk_toInvertibleSheaf k _ hD hDE default,
    intersectionNumber_mk_toInvertibleSheaf k _ hE hED default,
    Scheme.IdealSheafData.finrank_comap_subschemeι_comm _ _ w]

/-- **Symmetry of the intersection pairing on curves.** Let `D` and `E` be effective Cartier
divisors on `X` which are proper curves over `k` with finite-dimensional `H⁰` and `H¹` of their
structure sheaves, whose structure morphisms to `Spec k` agree on `D ×_X E`, and which meet
properly. Then `(D · E) = (E · D)`, both sides being `dim_k Γ(D ∩ E, 𝒪_{D ∩ E})`. -/
theorem intersectionNumber_inv_mk_toInvertibleSheaf_comm (hD : D.IsEffectiveCartier)
    (hE : E.IsEffectiveCartier) (hDE : (D.comap E.subschemeι).IsEffectiveCartier)
    (hED : (E.comap D.subschemeι).IsEffectiveCartier)
    (w : pullback.fst E.subschemeι D.subschemeι ≫ E.subscheme ↘ Spec (.of k) =
      pullback.snd E.subschemeι D.subschemeι ≫ D.subscheme ↘ Spec (.of k)) :
    intersectionNumber k E.subschemeι (mk hD.toInvertibleSheaf)⁻¹ =
      intersectionNumber k D.subschemeι (mk hE.toInvertibleSheaf)⁻¹ := by
  have : IsFinite ((E.comap D.subschemeι).subschemeι ≫ D.subscheme ↘ Spec (.of k)) :=
    hED.isFinite_subschemeι_comp
  rw [intersectionNumber_inv_mk_toInvertibleSheaf k _ hD hDE default,
    intersectionNumber_inv_mk_toInvertibleSheaf k _ hE hED default,
    Scheme.IdealSheafData.finrank_comap_subschemeι_comm _ _ w]

end Effective

end Symmetric

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
