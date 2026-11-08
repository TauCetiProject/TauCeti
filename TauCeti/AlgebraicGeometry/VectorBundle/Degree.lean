/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.Curves.Cohomology
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# The degree of a vector bundle on a curve

Let `X` be a scheme over a field `k` and `E` a finite locally free sheaf of constant rank `r` on
`X`. Its degree is

`deg E := χ(X, E) - r · χ(X, 𝒪_X)`,

where `χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` is the degree-`2` truncation
`Scheme.Modules.eulerCharBelow k X M 2` of the Euler characteristic. On a proper scheme of
dimension at most one over `k` this is the degree of `E` in the sense of the Stacks Project,
Definition 0AYR: by Grothendieck vanishing `H¹` is the top cohomology there, so the truncation is
the full Euler characteristic. As for `InvertibleSheaf.eulerDegree`, no hypothesis is needed to
form the invariant, which takes junk values when the cohomology is infinite-dimensional or does
not vanish above degree one.

The degree is normalised by the trivial bundle, is additive in short exact sequences of vector
bundles (Stacks, Lemma 0AYS) and is unchanged by extension of the ground field (Stacks,
Lemma 0B59). In rank one it is the Euler-characteristic degree of a line bundle, and hence, on a
proper integral curve whose codimension-one local rings are discrete valuation rings,
`deg 𝒪_X(D) = Σ_y D(y) [κ(y) : k]` for a Weil divisor `D` (Stacks, Lemma 0AYY).

Twisting by a line bundle `L` changes the degree by `r · deg L`: on a proper integral curve,
possibly singular, `deg (E ⊗ L) = deg E + r · deg L`, the case of rank-one `V` of Stacks,
Lemma 0AYX. Writing `L` as a difference of effective Cartier divisors reduces this to twisting by
`𝒪_X(-D)` for an effective Cartier divisor `D`. There the exact sequence
`0 ⟶ E(-D) ⟶ E ⟶ E|_D ⟶ 0` and the triviality of `E|_D` on the finite scheme `D` give
`χ(E(-D)) = χ(E) - r · dim_k Γ(D, 𝒪_D)` (`Scheme.IdealSheafData.eulerCharBelow_tensor_sheaf`).

## Main declarations

* `FiniteLocallyFreeSheaf.FixedRank.vectorBundleDegree k E`: the degree
  `χ(X, E) - r · χ(X, 𝒪_X)` of a finite locally free sheaf of constant rank `r`;
* `FixedRank.vectorBundleDegree_congr`: the degree is an isomorphism invariant;
* `FixedRank.vectorBundleDegree_free`: the trivial bundle `𝒪_X^r` has degree zero;
* `FixedRank.vectorBundleDegree_eq_eulerDegree_toInvertible` and
  `FixedRank.vectorBundleDegree_toFixedRankOne_obj`: in rank one the degree is
  `InvertibleSheaf.eulerDegree`;
* `FixedRank.vectorBundleDegree_eq_relativeDegree`: the degree of `𝒪_X(D)` is the degree of the
  divisor `D`;
* `FixedRank.vectorBundleDegree_add_of_shortExact`: additivity in a short exact sequence, given
  finite-dimensionality of the cohomology it reads and vanishing of `H²` of the subbundle, and
  `FixedRank.vectorBundleDegree_add_of_shortExact_of_isCurveOver`, where these hypotheses are
  discharged on a proper integral curve whose codimension-one local rings are discrete valuation
  rings;
* `FixedRank.vectorBundleDegree_baseChange`: the degree of the pullback of `E` to `X_K` for a
  field extension `K / k` is the degree of `E`;
* `FixedRank.vectorBundleDegree_twist_toInvertibleSheaf`: `deg E(-D) = deg E - r · deg D` for an
  effective Cartier divisor `D` finite over `k`, on any scheme over `k`;
* `FixedRank.vectorBundleDegree_twist`, `FixedRank.vectorBundleDegree_twist_of_isEffective` and
  `FixedRank.finiteDimensional_cohomology_twist`: on a proper integral curve,
  `deg (E ⊗ L) = deg E + r · deg L` for every line bundle `L`, `deg E(D) = deg E + r · deg D` for
  an effective Cartier divisor `D`, and twisting preserves finiteness of cohomology.

## References

* [The Stacks Project, Section 33.44, Degrees on curves](https://stacks.math.columbia.edu/tag/0AYR):
  Definition 0AYR and Lemmas 0AYS, 0AYX, 0AYY.
* [The Stacks Project, Lemma 0B59](https://stacks.math.columbia.edu/tag/0B59): invariance of the
  degree under extension of the ground field.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order Scheme.Modules
open Module (finrank)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf.FixedRank

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] {r : ℕ}

/-- The degree `χ(X, E) - r · χ(X, 𝒪_X)` of a finite locally free sheaf `E` of constant rank `r`
on a scheme over a field `k`, using the degree-`2` truncation
`χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` of the Euler characteristic.

On a proper scheme of dimension at most one over `k`, cohomology is finite-dimensional and
vanishes above degree one, and this is the degree of the vector bundle `E`. No hypothesis is
needed to form the invariant; elsewhere it has the junk values of
`Scheme.Modules.eulerCharBelow`. -/
def vectorBundleDegree (E : FixedRank X r) : ℤ :=
  eulerCharBelow k X E.obj.obj 2 - r * eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2

/-- The defining formula of the degree of a vector bundle. -/
lemma vectorBundleDegree_def (E : FixedRank X r) :
    vectorBundleDegree k E =
      eulerCharBelow k X E.obj.obj 2 -
        r * eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 :=
  (rfl)

/-- The degree of a vector bundle expanded in terms of the dimensions of `H⁰` and `H¹`. -/
lemma vectorBundleDegree_eq_finrank_sub (E : FixedRank X r) :
    vectorBundleDegree k E =
      ((finrank k (Scheme.Modules.Cohomology E.obj.obj 0) : ℤ) -
          (finrank k (Scheme.Modules.Cohomology E.obj.obj 1) : ℤ)) -
        r * ((finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) : ℤ) -
          (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ)) := by
  rw [vectorBundleDegree_def, eulerCharBelow_two, eulerCharBelow_two]

/-- Vector bundles of the same rank with isomorphic underlying sheaves have the same degree. -/
lemma vectorBundleDegree_congr {E F : FixedRank X r} (e : E.obj.obj ≅ F.obj.obj) :
    vectorBundleDegree k E = vectorBundleDegree k F := by
  rw [vectorBundleDegree_def, vectorBundleDegree_def, eulerCharBelow_congr k e]

variable (X r) in
/-- **The trivial vector bundle has degree zero**: `deg 𝒪_X^r = 0`. No finiteness hypothesis is
needed, since `χ(X, 𝒪_X^r) = r · χ(X, 𝒪_X)` holds for the truncated Euler characteristic as it
stands. -/
@[simp]
lemma vectorBundleDegree_free : vectorBundleDegree k (FixedRank.free X r) = 0 := by
  simp [vectorBundleDegree_def, free_obj, FiniteLocallyFreeSheaf.free_obj, eulerCharBelow_free]

/-- **The degree in rank one** is the Euler-characteristic degree `χ(L) - χ(𝒪_X)` of the
corresponding line bundle. -/
lemma vectorBundleDegree_eq_eulerDegree_toInvertible (E : FixedRank X 1) :
    vectorBundleDegree k E = ((toInvertible X).obj E).eulerDegree k := by
  rw [vectorBundleDegree_def, InvertibleSheaf.eulerDegree_def, toInvertible_obj_obj, Nat.cast_one,
    one_mul]

/-- The degree of a line bundle regarded as a vector bundle of rank one is its
Euler-characteristic degree. -/
@[simp]
lemma vectorBundleDegree_toFixedRankOne_obj (L : InvertibleSheaf X) :
    vectorBundleDegree k ((InvertibleSheaf.toFixedRankOne X).obj L) = L.eulerDegree k := by
  rw [vectorBundleDegree_def, InvertibleSheaf.eulerDegree_def,
    InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj, Nat.cast_one, one_mul]

/-- **The degree of `𝒪_X(D)`.** On a proper integral curve over `k` whose codimension-one local
rings are discrete valuation rings and with `H¹(X, 𝒪_X)` finite-dimensional, a vector bundle `E`
of rank one with `E ≅ 𝒪_X(D)` has degree `deg D = Σ_y D(y) [κ(y) : k]`. -/
theorem vectorBundleDegree_eq_relativeDegree [IsIntegral X] [IsLocallyNoetherian X]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    [IsProper (X ↘ Spec (.of k))] (hX : ∀ y : X, coheight y ≤ 1)
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    {E : FixedRank X 1} {D : SchemeWeilDivisor X} (e : E.obj.obj ≅ SchemeWeilDivisor.sheaf D) :
    vectorBundleDegree k E = SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D := by
  rw [vectorBundleDegree_eq_eulerDegree_toInvertible]
  exact InvertibleSheaf.eulerDegree_eq_relativeDegree k hX (eqToIso (toInvertible_obj_obj X E) ≪≫ e)

section ShortExact

variable {r₁ r₂ r₃ : ℕ} {E₁ : FixedRank X r₁} {E₂ : FixedRank X r₂} {E₃ : FixedRank X r₃}
  {f : E₁.obj.obj ⟶ E₂.obj.obj} {g : E₂.obj.obj ⟶ E₃.obj.obj} {w : f ≫ g = 0}

/-- **Additivity of the degree in short exact sequences.** For a short exact sequence
`0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` of vector bundles of constant ranks `r₁`, `r₂ = r₁ + r₃` and `r₃`, with
`H¹(X, E₁)`, `H⁰(X, E₂)` and `H¹(X, E₂)` finite-dimensional and `H²(X, E₁) = 0`, the degrees add
up: `deg E₂ = deg E₁ + deg E₃`. -/
theorem vectorBundleDegree_add_of_shortExact (hS : (ShortComplex.mk f g w).ShortExact)
    (hr : r₂ = r₁ + r₃) [FiniteDimensional k (Scheme.Modules.Cohomology E₁.obj.obj 1)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E₂.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E₂.obj.obj 1)]
    (hvan : Subsingleton (Scheme.Modules.Cohomology E₁.obj.obj 2)) :
    vectorBundleDegree k E₂ = vectorBundleDegree k E₁ + vectorBundleDegree k E₃ := by
  have h := eulerCharBelow_eq_add k hS 2
    (fun i hi hi₀ ↦ by obtain rfl : i = 1 := (by omega); infer_instance)
    (fun i hi ↦ by interval_cases i <;> infer_instance) hvan
  subst hr
  rw [vectorBundleDegree_def, vectorBundleDegree_def, vectorBundleDegree_def]
  push_cast
  linear_combination h

/-- **Additivity of the degree on a curve.** On a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings, the degree is additive in every short
exact sequence `0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` of vector bundles of constant ranks `r₁`, `r₂ = r₁ + r₃`
and `r₃`. -/
theorem vectorBundleDegree_add_of_shortExact_of_isCurveOver [X.IsCurveOver k]
    [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    (hS : (ShortComplex.mk f g w).ShortExact) (hr : r₂ = r₁ + r₃) :
    vectorBundleDegree k E₂ = vectorBundleDegree k E₁ + vectorBundleDegree k E₃ := by
  have := finiteDimensional_cohomology_of_isCurveOver k E₁.obj.obj 1
  have := finiteDimensional_cohomology_of_isCurveOver k E₂.obj.obj 0
  have := finiteDimensional_cohomology_of_isCurveOver k E₂.obj.obj 1
  exact vectorBundleDegree_add_of_shortExact k hS hr
    (subsingleton_cohomology_of_two_le_of_isCurveOver k E₁.obj.obj 2 le_rfl)

end ShortExact

section BaseChange

variable {k} {K : Type u} [Field K] [Algebra k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
  {g : Y ⟶ X}

/-- **The degree is invariant under extension of the ground field.** For a field extension
`K / k`, presented as a pullback square `Y = X ×_k K` with projection `g : Y ⟶ X`, the pullback
`g^* E` of a vector bundle `E` of constant rank `r` has the same degree over `K` as `E` has over
`k`. The scheme `X` need only be quasi-compact with affine diagonal, for instance proper over `k`;
it need not be a curve, irreducible or geometrically connected. -/
theorem vectorBundleDegree_baseChange
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))] (E : FixedRank X r) :
    vectorBundleDegree K ((pullback g).obj E) = vectorBundleDegree k E := by
  -- The pullback of the structure sheaf `𝒪_X` is the structure sheaf `𝒪_Y`.
  let e : (Scheme.Modules.pullback g).obj (InvertibleSheaf.trivial X).obj ≅
      (InvertibleSheaf.trivial Y).obj :=
    (Scheme.Modules.pullback g).mapIso (InvertibleSheaf.trivialObjIsoUnit X) ≪≫
      Scheme.Modules.pullbackObjUnitIso g ≪≫ (InvertibleSheaf.trivialObjIsoUnit Y).symm
  rw [vectorBundleDegree_def, vectorBundleDegree_def, pullback_obj_obj,
    FiniteLocallyFreeSheaf.pullback_obj_obj, ← eulerCharBelow_congr K e 2,
    eulerCharBelow_pullback_eq_of_isPullback H, eulerCharBelow_pullback_eq_of_isPullback H]

end BaseChange

section Twist

/-- **Twisting by `𝒪_X(-D)` lowers the degree by `r · deg D`.** Let `I ⊆ 𝒪_X` be the ideal sheaf
of an effective Cartier divisor `D` finite over `k`, so that `I = 𝒪_X(-D)` is a line bundle, and let
`E` be a vector bundle of constant rank `r` with `H⁰(X, E)` and `H¹(X, E)` finite-dimensional. Then
`deg (E ⊗ 𝒪_X(-D)) = deg E - r · dim_k Γ(D, 𝒪_D)`, the dimension being written as the rank of
`D ⟶ Spec k` at the point `s`. No integrality, properness or regularity of `X` is needed. -/
theorem vectorBundleDegree_twist_toInvertibleSheaf {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))] (E : FixedRank X r)
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 1)] (s : Spec (.of k)) :
    vectorBundleDegree k (E.twist hI.toInvertibleSheaf) =
      vectorBundleDegree k E - r * (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  rw [vectorBundleDegree_def, vectorBundleDegree_def, twist_obj_obj,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj,
    Scheme.IdealSheafData.eulerCharBelow_tensor_sheaf k I E s]
  ring

section Curve

variable [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]

/-- Twisting by a line bundle `L` on an integral proper curve preserves finiteness of `H⁰` and
`H¹`, and changes the degree by `r · deg L`. Write `[L] = [𝒪_X(D₁)] [𝒪_X(D₂)]⁻¹` with `D₁` and
`D₂` effective; then `(E ⊗ L) ⊗ 𝒪_X(-D₁) ≅ E ⊗ 𝒪_X(-D₂)`, and both sides are computed by
`vectorBundleDegree_twist_toInvertibleSheaf`. Only the degree formula needs `H⁰(X, 𝒪_X)` and
`H¹(X, 𝒪_X)` finite-dimensional. -/
private theorem finiteDimensional_cohomology_twist_and_vectorBundleDegree_twist
    (E : FixedRank X r) [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 1)] (L : InvertibleSheaf X) :
    (∀ i < 2, FiniteDimensional k (Scheme.Modules.Cohomology (E.twist L).obj.obj i)) ∧
      ∀ [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0)]
        [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)],
        vectorBundleDegree k (E.twist L) = vectorBundleDegree k E + r * L.eulerDegree k := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨D₁, D₂, hD₁, hD₂, hD⟩ :=
    Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k)))
    (LineBundleClass.mk L)
  have hI₁ := hD₁.isEffectiveCartier_sectionsIdealSheaf
  have hI₂ := hD₂.isEffectiveCartier_sectionsIdealSheaf
  have : IsFinite (hD₁.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)) :=
    hI₁.isFinite_subschemeι_comp
  have : IsFinite (hD₂.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)) :=
    hI₂.isFinite_subschemeι_comp
  -- `L ⊗ 𝒪_X(-D₁) ≅ 𝒪_X(-D₂)`, since `[L] [𝒪_X(D₁)]⁻¹ = [𝒪_X(D₂)]⁻¹`.
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp
    (show LineBundleClass.mk (InvertibleSheaf.tensorProduct L hI₁.toInvertibleSheaf) =
        LineBundleClass.mk hI₂.toInvertibleSheaf by
      rw [LineBundleClass.mk_tensorProduct, hD₁.mk_toInvertibleSheaf_sectionsIdealSheaf,
        hD₂.mk_toInvertibleSheaf_sectionsIdealSheaf, ← hD, mul_right_comm, mul_inv_cancel, one_mul])
  -- Hence `(E ⊗ L) ⊗ 𝒪_X(-D₁) ≅ E ⊗ 𝒪_X(-D₂)`.
  let e' : ((E.twist L).twist hI₁.toInvertibleSheaf).obj.obj ≅
      (E.twist hI₂.toInvertibleSheaf).obj.obj :=
    (Scheme.Modules.isFiniteLocallyFree X).ι.mapIso ((toFiniteLocallyFree X r).mapIso
      (twistTensorProductIso E L _ ≪≫ twistCongr (Iso.refl E) (ObjectProperty.isoMk _ e)))
  -- `E ⊗ 𝒪_X(-D₂)`, hence `(E ⊗ L) ⊗ 𝒪_X(-D₁)`, hence `E ⊗ L` has finite `H⁰` and `H¹`.
  have hiff (I : X.IdealSheafData) (hI : I.IsEffectiveCartier)
      [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))] (F : FixedRank X r) :
      (∀ i < 2, FiniteDimensional k
          (Scheme.Modules.Cohomology (F.twist hI.toInvertibleSheaf).obj.obj i)) ↔
        ∀ i < 2, FiniteDimensional k (Scheme.Modules.Cohomology F.obj.obj i) := by
    rw [twist_obj_obj, Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]
    exact Scheme.IdealSheafData.finiteDimensional_cohomology_tensor_sheaf_iff I
  have hfin : ∀ i < 2, FiniteDimensional k (Scheme.Modules.Cohomology (E.twist L).obj.obj i) :=
    (hiff _ hI₁ _).mp fun i hi ↦ (finiteDimensional_cohomology_congr k e' i).mpr
      ((hiff _ hI₂ E).mpr (fun j hj ↦ by interval_cases j <;> infer_instance) i hi)
  refine ⟨hfin, fun {_ _} ↦ ?_⟩
  have := hfin 0 (by norm_num)
  have := hfin 1 (by norm_num)
  have h₁ := vectorBundleDegree_twist_toInvertibleSheaf k hI₁ (E.twist L) default
  have h₂ := vectorBundleDegree_twist_toInvertibleSheaf k hI₂ E default
  have h₃ := vectorBundleDegree_congr k e'
  -- `deg L = deg 𝒪_X(D₁) - deg 𝒪_X(D₂)`, the degrees of the effective divisors.
  have hL : L.eulerDegree k =
      (hD₁.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)).finrank default -
        (hD₂.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)).finrank default := by
    rw [← LineBundleClass.eulerDegree_mk, ← hD, LineBundleClass.eulerDegree_mul_of_isIntegral,
      LineBundleClass.eulerDegree_inv_of_isIntegral, hD₁.eulerDegree_toLineBundleClass k,
      hD₂.eulerDegree_toLineBundleClass k, sub_eq_add_neg]
  rw [hL]
  linear_combination h₂ - h₁ + h₃

/-- **Twisting preserves finiteness of cohomology.** On an integral scheme `X`, proper over `k`
with fibres of dimension at most one, if a vector bundle `E` of constant rank has
finite-dimensional `H⁰` and `H¹`, then so does its twist `E ⊗ L` by any line bundle `L`. -/
theorem finiteDimensional_cohomology_twist (E : FixedRank X r)
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 1)] (L : InvertibleSheaf X) {i : ℕ}
    (hi : i < 2) : FiniteDimensional k (Scheme.Modules.Cohomology (E.twist L).obj.obj i) :=
  (finiteDimensional_cohomology_twist_and_vectorBundleDegree_twist k E L).1 i hi

variable [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **Twisting by a line bundle.** On an integral scheme `X`, proper over `k` with fibres of
dimension at most one and with finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, let `E` be a
vector bundle of constant rank `r` with finite-dimensional `H⁰` and `H¹`. Then for every line bundle
`L`, `deg (E ⊗ L) = deg E + r · deg L`. This is the case of rank-one `V` of
`deg (E ⊗ V) = r · deg V + rank V · deg E` (Stacks, Lemma 0AYX). The curve `X` may be singular. -/
theorem vectorBundleDegree_twist (E : FixedRank X r)
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 1)] (L : InvertibleSheaf X) :
    vectorBundleDegree k (E.twist L) = vectorBundleDegree k E + r * L.eulerDegree k :=
  (finiteDimensional_cohomology_twist_and_vectorBundleDegree_twist k E L).2

/-- **Twisting by an effective divisor.** On an integral scheme `X`, proper over `k` with fibres of
dimension at most one and with finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, let `D` be an
effective Cartier divisor and `E` a vector bundle of constant rank `r` with finite-dimensional `H⁰`
and `H¹`. Then `deg E(D) = deg E + r · deg D`, where `E(D) = E ⊗ 𝒪_X(D)` and `deg D` is
`dim_k Γ(D, 𝒪_D)`, the rank of `D ⟶ Spec k` at the point `s`. -/
theorem vectorBundleDegree_twist_of_isEffective {D : Scheme.CartierDivisor X} (hD : D.IsEffective)
    (E : FixedRank X r) [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 1)] {L : InvertibleSheaf X}
    (hL : LineBundleClass.mk L = D.toLineBundleClass) (s : Spec (.of k)) :
    vectorBundleDegree k (E.twist L) = vectorBundleDegree k E +
      r * (hD.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  rw [vectorBundleDegree_twist, ← LineBundleClass.eulerDegree_mk, hL,
    hD.eulerDegree_toLineBundleClass k s]

end Curve

end Twist

end FiniteLocallyFreeSheaf.FixedRank

end

end AlgebraicGeometry

end TauCeti
