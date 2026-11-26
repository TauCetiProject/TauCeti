/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.MayerVietoris
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Semilocal
public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct

/-!
# The Euler characteristic of an ideal sheaf

Let `X` be a scheme over a field `k` and `I ⊆ 𝒪_X` an ideal sheaf whose closed subscheme
`D = V(I)` is finite over `k`, of rank `dim_k Γ(D, 𝒪_D)`. The exact sequence
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_D ⟶ 0` and the vanishing of higher cohomology on the affine Noetherian
scheme `D` give

  `χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_sheaf`), where `χ` is the degree-`2` truncation
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional; then
`H⁰(X, I)` and `H¹(X, I)` are finite-dimensional too
(`Scheme.IdealSheafData.finiteDimensional_cohomology_sheaf`).

More generally, for a vector bundle `E` of constant rank `r` on `X`, tensoring the sequence with
`E` gives `0 ⟶ E ⊗ I ⟶ E ⟶ E ⊗ ι_* 𝒪_D ⟶ 0`. By the projection formula the last term is the
direct image of the pullback of `E` to `D` (`Scheme.IdealSheafData.tensorPushforwardSubschemeIso`),
so its cohomology is that of the pullback of `E` to `D`
(`Scheme.IdealSheafData.finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff`,
`Scheme.IdealSheafData.subsingleton_cohomology_tensor_pushforwardSubscheme_iff` and
`Scheme.IdealSheafData.eulerCharBelow_tensor_pushforwardSubscheme`). The pullback is
a vector bundle of rank `r` on a scheme finite over `k`
and hence free (`FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isFinite`), so the last
term has finite-dimensional `H⁰`, no cohomology in positive degrees and Euler characteristic
`r · dim_k Γ(D, 𝒪_D)`
(`Scheme.IdealSheafData.finiteDimensional_cohomology_zero_tensor_pushforwardSubscheme`,
`Scheme.IdealSheafData.subsingleton_cohomology_succ_tensor_pushforwardSubscheme` and
`Scheme.IdealSheafData.eulerCharBelow_tensor_pushforwardSubscheme_eq_mul_finrank`). So `E ⊗ I` has
finite-dimensional `H⁰` and `H¹` exactly when `E` does
(`Scheme.IdealSheafData.finiteDimensional_cohomology_tensor_sheaf_iff`), has vanishing `Hⁿ` for
a given `n ≥ 2` exactly when `E` does
(`Scheme.IdealSheafData.subsingleton_cohomology_tensor_sheaf_iff`), and then

  `χ(E ⊗ I) = χ(E) - r · dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_tensor_sheaf`). No hypothesis on `X` is needed.

The same argument applies to the Mayer–Vietoris sequence
`0 ⟶ 𝒪_{V(I ⊓ J)} ⟶ 𝒪_{V(I)} ⊞ 𝒪_{V(J)} ⟶ 𝒪_{V(I ⊔ J)} ⟶ 0`
(`Scheme.IdealSheafData.shortExact_mayerVietoris`) of two closed subschemes meeting in a scheme
`V(I ⊔ J)` finite over `k`. Tensoring it with `E`, if the restrictions of `E` to `V(I)` and
`V(J)` have finite-dimensional `H⁰` and `H¹` then so does its restriction to `V(I ⊓ J)`
(`FiniteLocallyFreeSheaf.FixedRank.finiteDimensional_cohomology_pullback_subschemeι_inf`), and

  `χ(E|_{V(I ⊓ J)}) + r · dim_k Γ(V(I ⊔ J), 𝒪) = χ(E|_{V(I)}) + χ(E|_{V(J)})`

(`FiniteLocallyFreeSheaf.FixedRank.eulerCharBelow_pullback_subschemeι_inf_add`).

The rank is Mathlib's `Scheme.Hom.finrank` of the finite morphism `D ⟶ Spec k`, evaluated at a
point of `Spec k`; it is `dim_k Γ(D, 𝒪_D)` by
`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`.

## References

* R. Hartshorne, *Algebraic Geometry*: Lemma III.2.10 and Theorem III.3.5 (the cohomology of
  `𝒪_D`), and the proof of Theorem IV.1.3 (Riemann–Roch), where degrees are computed from the
  same kind of exact sequence.
* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ): degrees on
  proper curves, and the change of Euler characteristic under twisting by an effective Cartier
  divisor.
* [The Stacks Project, Lemma 33.4.6, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J): the
  exact sequence `0 → 𝒪_{Y ∪ Z} → 𝒪_Y × 𝒪_Z → 𝒪_{Y ∩ Z} → 0` of two closed subschemes.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] (I : X.IdealSheafData)

/-- For the structure of scheme over `k` on `V(I)` given by `V(I) ⟶ X ⟶ Spec k`, the `k`-algebra
structure on its global functions is the map of global sections of that morphism. -/
private lemma algebraMap_eq :
    letI : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
    algebraMap k Γ(I.subscheme, ⊤) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ X ↘ Spec (.of k)).appTop).hom := by
  exact RingHom.ext fun r ↦ baseRingToGlobalSections_apply k I.subscheme r

/-- The projection formula for the closed immersion `ι : V(I) ⟶ X`:
`E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* (ι^* E)` for a vector bundle `E` on `X`. -/
def tensorPushforwardSubschemeIso (E : FiniteLocallyFreeSheaf X) :
    E.obj ⊗ I.pushforwardSubscheme ≅ (Scheme.Modules.pushforward I.subschemeι).obj
      ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj :=
  -- The projection formula is stated for the monoidal unit of `V(I).Modules`.
  eqToIso (congrArg (fun F ↦ E.obj ⊗ (Scheme.Modules.pushforward I.subschemeι).obj F)
      (TauCeti.SheafOfModules.tensorUnit_eq I.subscheme.sheaf).symm) ≪≫
    FiniteLocallyFreeSheaf.tensorPushforwardUnitIso I.subschemeι E

/-- `χ(X, E ⊗ ι_* 𝒪_{V(I)}) = χ(V(I), ι^* E)` for a vector bundle `E` on `X`: by the projection
formula `E ⊗ ι_* 𝒪_{V(I)}` is the direct image of `ι^* E` along the closed immersion `ι`. -/
theorem eulerCharBelow_tensor_pushforwardSubscheme (E : FiniteLocallyFreeSheaf X) (n : ℕ) :
    eulerCharBelow k X (E.obj ⊗ I.pushforwardSubscheme) n =
      eulerCharBelow k I.subscheme
        ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj n := by
  rw [eulerCharBelow_congr k (I.tensorPushforwardSubschemeIso E) n,
    Scheme.Hom.eulerCharBelow_pushforward I.subschemeι k]

/-- `H^i(X, E ⊗ ι_* 𝒪_{V(I)})` is finite-dimensional over `k` exactly when `H^i(V(I), ι^* E)` is,
for a vector bundle `E` on `X`: by the projection formula `E ⊗ ι_* 𝒪_{V(I)}` is the direct image
of `ι^* E` along the closed immersion `ι`. -/
theorem finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff
    (E : FiniteLocallyFreeSheaf X) (i : ℕ) :
    FiniteDimensional k (Cohomology (E.obj ⊗ I.pushforwardSubscheme) i) ↔
      FiniteDimensional k
        (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj i) :=
  (finiteDimensional_cohomology_congr k (I.tensorPushforwardSubschemeIso E) i).trans
    (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k _ i)

/-- `H^i(X, E ⊗ ι_* 𝒪_{V(I)})` vanishes exactly when `H^i(V(I), ι^* E)` does, for a vector bundle
`E` on `X`: by the projection formula `E ⊗ ι_* 𝒪_{V(I)}` is the direct image of `ι^* E` along the
closed immersion `ι`. -/
theorem subsingleton_cohomology_tensor_pushforwardSubscheme_iff (E : FiniteLocallyFreeSheaf X)
    (i : ℕ) : Subsingleton (Cohomology (E.obj ⊗ I.pushforwardSubscheme) i) ↔
      Subsingleton
        (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E).obj i) :=
  Equiv.subsingleton_congr <|
    ((cohomologyFunctor X i).mapIso
      (I.tensorPushforwardSubschemeIso E)).addCommGroupIsoToAddEquiv.toEquiv.trans
        (cohomologyPushforwardIso I.subschemeι _ i).addCommGroupIsoToAddEquiv.toEquiv

section Finite

variable [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))]

/-- `H⁰` of the direct image `ι_* 𝒪_{V(I)}` of the structure sheaf of a closed subscheme finite
over `k` is finite-dimensional. -/
private lemma finiteDimensional_cohomology_zero_pushforward :
    FiniteDimensional k (Cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)) 0) := by
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  let _ : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
  have : Module.Finite k Γ(M, ⊤) :=
    -- The base-ring module structure on the global sections of `𝒪_{V(I)}` is the one given by
    -- the algebra structure, both being restriction of scalars along
    -- `baseRingToGlobalSections`.
    (I.subschemeι ≫ X ↘ Spec (.of k)).moduleFinite_appTop (algebraMap_eq k I)
  refine (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k M 0).mpr ?_
  exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv k I.subscheme M).symm

include k in
/-- `H¹` of the direct image `ι_* 𝒪_{V(I)}` of the structure sheaf of a closed subscheme finite
over `k` vanishes, the closed subscheme being affine. -/
private lemma subsingleton_cohomology_one_pushforward :
    Subsingleton (Cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)) 1) := by
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  have := subsingleton_cohomology_succ_of_isAffineHom (I.subscheme ↘ Spec (.of k)) M 0
  exact (cohomologyPushforwardIso I.subschemeι M 1).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- The truncated Euler characteristic of the direct image `ι_* 𝒪_{V(I)}` is the rank of the
closed subscheme `V(I)` over `k`. -/
private lemma eulerCharBelow_pushforward (s : Spec (.of k)) :
    eulerCharBelow k X ((Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)) 2 =
      (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  rw [Scheme.Hom.eulerCharBelow_pushforward_structureSheaf I.subschemeι k s 1,
    comp_over I.subschemeι (Spec (.of k))]

section Tensor

variable {r : ℕ} (E : FiniteLocallyFreeSheaf.FixedRank X r)

/-- The direct image `ι_* 𝒪_{V(I)}^r` of the free sheaf of rank `r` on the closed subscheme
`V(I)`. -/
private abbrev freePushforward (r : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (FiniteLocallyFreeSheaf.FixedRank.free I.subscheme r).obj.obj

include k in
/-- On the closed subscheme `V(I)`, finite over `k`, every vector bundle of constant rank `r` is
trivial (`FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isFinite`); so tensoring
`ι_* 𝒪_{V(I)}` with a vector bundle `E` of rank `r` on `X`, which by the projection formula is the
direct image of the pullback of `E` to `V(I)`, gives `ι_* 𝒪_{V(I)}^r`. -/
private lemma nonempty_tensor_pushforward_iso :
    Nonempty (E.obj.obj ⊗ I.pushforwardSubscheme ≅ freePushforward I r) := by
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  obtain ⟨e⟩ := FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isFinite k
    ((FiniteLocallyFreeSheaf.FixedRank.pullback I.subschemeι).obj E)
  exact ⟨I.tensorPushforwardSubschemeIso E.obj ≪≫
    (Scheme.Modules.pushforward I.subschemeι).mapIso
      (eqToIso (congrArg (·.obj)
          (FiniteLocallyFreeSheaf.FixedRank.pullback_obj_obj I.subschemeι E).symm) ≪≫
        (Scheme.Modules.isFiniteLocallyFree _).ι.mapIso
          ((FiniteLocallyFreeSheaf.isConstantRank _ r).ι.mapIso e))⟩

/-- `H⁰` of `ι_* 𝒪_{V(I)}^r` is finite-dimensional. -/
private lemma finiteDimensional_cohomology_zero_freePushforward :
    FiniteDimensional k (Cohomology (freePushforward I r) 0) := by
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  have : HasBiproduct (C := I.subscheme.Modules) fun _ : ULift.{u} (Fin r) ↦ M :=
    HasBiproduct.of_hasCoproduct _
  have : Module.Finite k (Cohomology M 0) :=
    (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k M 0).mp
      (finiteDimensional_cohomology_zero_pushforward k I)
  -- `𝒪_{V(I)}^r` is the biproduct of `r` copies of `𝒪_{V(I)}`.
  let e : (⨁ fun _ : ULift.{u} (Fin r) ↦ M) ≅
      (FiniteLocallyFreeSheaf.FixedRank.free I.subscheme r).obj.obj :=
    TauCeti.SheafOfModules.biproductIsoFree (R := I.subscheme.sheaf) _ ≪≫
      eqToIso (by rw [FiniteLocallyFreeSheaf.FixedRank.free_obj, FiniteLocallyFreeSheaf.free_obj])
  refine (Scheme.Hom.moduleFinite_cohomology_pushforward_iff I.subschemeι k _ 0).mpr ?_
  exact Module.Finite.equiv ((cohomologyBiproductLinearEquiv k (fun _ ↦ M) 0).symm ≪≫ₗ
    cohomologyBaseLinearEquivOfIso k e 0)

include k in
/-- `ι_* 𝒪_{V(I)}^r` has no cohomology in positive degrees, the closed subscheme being affine. -/
private lemma subsingleton_cohomology_succ_freePushforward (n : ℕ) :
    Subsingleton (Cohomology (freePushforward I r) (n + 1)) := by
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  let M := (FiniteLocallyFreeSheaf.FixedRank.free I.subscheme r).obj.obj
  have := subsingleton_cohomology_succ_of_isAffineHom (I.subscheme ↘ Spec (.of k)) M n
  exact (cohomologyPushforwardIso I.subschemeι M
    (n + 1)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- The truncated Euler characteristic of `ι_* 𝒪_{V(I)}^r` is `r` times the rank of the closed
subscheme `V(I)` over `k`. -/
private lemma eulerCharBelow_freePushforward (s : Spec (.of k)) :
    eulerCharBelow k X (freePushforward I r) 2 =
      r * (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  let M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  rw [← eulerCharBelow_pushforward k I s, Scheme.Hom.eulerCharBelow_pushforward,
    Scheme.Hom.eulerCharBelow_pushforward I.subschemeι k M,
    FiniteLocallyFreeSheaf.FixedRank.free_obj, FiniteLocallyFreeSheaf.free_obj,
    eulerCharBelow_free, Fintype.card_ulift, Fintype.card_fin]

/-- The right unitor `E ⊗ 𝒪_X ≅ E`, with `𝒪_X` written as the structure sheaf
`SheafOfModules.unit X.ringCatSheaf` appearing in the exact sequence of `V(I)` rather than as the
monoidal unit `𝟙_ X.Modules`; the two agree by `TauCeti.SheafOfModules.tensorUnit_eq`. -/
private def tensorUnitIso : E.obj.obj ⊗ SheafOfModules.unit X.ringCatSheaf ≅ E.obj.obj :=
  eqToIso (congrArg (E.obj.obj ⊗ ·) (TauCeti.SheafOfModules.tensorUnit_eq X.sheaf).symm) ≪≫
    ρ_ E.obj.obj

/-- The exact sequence of `V(I)` tensored with `E`:
`0 ⟶ E ⊗ I ⟶ E ⊗ 𝒪_X ⟶ E ⊗ ι_* 𝒪_{V(I)} ⟶ 0`. -/
private abbrev tensorSequence : ShortComplex X.Modules :=
  (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft E.obj.obj)

/-- `E` is finite locally free, so tensoring with it preserves the exact sequence of `V(I)`. -/
private lemma shortExact_tensorSequence : (tensorSequence I E).ShortExact :=
  I.shortExact_tensor_toPushforwardSubscheme E.obj.obj

omit [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))] in
/-- The middle term of the tensored sequence is `E ⊗ 𝒪_X ≅ E`. -/
private lemma finiteDimensional_cohomology_tensorSequence_X₂_iff (i : ℕ) :
    FiniteDimensional k (Cohomology (tensorSequence I E).X₂ i) ↔
      FiniteDimensional k (Cohomology E.obj.obj i) :=
  finiteDimensional_cohomology_congr k (tensorUnitIso E) i

/-- If `V(I)` is finite over `k` and `E` is a vector bundle of constant rank, then
`H⁰(X, E ⊗ ι_* 𝒪_{V(I)})` is finite-dimensional, as `E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}^r`. -/
theorem finiteDimensional_cohomology_zero_tensor_pushforwardSubscheme :
    FiniteDimensional k (Cohomology (E.obj.obj ⊗ I.pushforwardSubscheme) 0) := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I E
  exact (finiteDimensional_cohomology_congr k e₃ 0).mpr
    (finiteDimensional_cohomology_zero_freePushforward k I)

include k in
/-- If `V(I)` is finite over `k` and `E` is a vector bundle of constant rank, then
`H^(n + 1)(X, E ⊗ ι_* 𝒪_{V(I)})` vanishes, as `E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}^r`. -/
theorem subsingleton_cohomology_succ_tensor_pushforwardSubscheme (n : ℕ) :
    Subsingleton (Cohomology (E.obj.obj ⊗ I.pushforwardSubscheme) (n + 1)) := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I E
  have := subsingleton_cohomology_succ_freePushforward k I (r := r) n
  exact (cohomologyBaseLinearEquivOfIso k e₃ (n + 1)).subsingleton

/-- If `V(I)` is finite over `k` and `E` is a vector bundle of constant rank `r`, then
`χ(X, E ⊗ ι_* 𝒪_{V(I)}) = r · dim_k Γ(V(I), 𝒪_{V(I)})`, the dimension being the rank of
`V(I) ⟶ Spec k` at the point `s`. -/
theorem eulerCharBelow_tensor_pushforwardSubscheme_eq_mul_finrank (s : Spec (.of k)) :
    eulerCharBelow k X (E.obj.obj ⊗ I.pushforwardSubscheme) 2 =
      r * (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I E
  rw [eulerCharBelow_congr k e₃ 2, eulerCharBelow_freePushforward k I s]

variable {k E} in
/-- **Twisting by an ideal sheaf preserves finiteness of cohomology.** If `I ⊆ 𝒪_X` cuts out a
closed subscheme finite over the field `k` and `E` is a vector bundle of constant rank on `X`,
then `H⁰` and `H¹` of `E ⊗ I` are finite-dimensional exactly when those of `E` are. -/
theorem finiteDimensional_cohomology_tensor_sheaf_iff :
    (∀ i < 2, FiniteDimensional k (Cohomology (E.obj.obj ⊗ I.sheaf) i)) ↔
      ∀ i < 2, FiniteDimensional k (Cohomology E.obj.obj i) := by
  have hS := shortExact_tensorSequence I E
  have h₂ := finiteDimensional_cohomology_tensorSequence_X₂_iff k I E
  have : FiniteDimensional k (Cohomology (tensorSequence I E).X₃ 0) :=
    finiteDimensional_cohomology_zero_tensor_pushforwardSubscheme k I E
  have : Subsingleton (Cohomology (tensorSequence I E).X₃ 1) :=
    subsingleton_cohomology_succ_tensor_pushforwardSubscheme k I E 0
  -- The first term `(tensorLeft E.obj.obj).obj I.sheaf` of the sequence is `E.obj.obj ⊗ I.sheaf`
  -- by `tensorLeft_obj`, which holds by `rfl`.
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩ <;> obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · have : FiniteDimensional k (Cohomology (tensorSequence I E).X₁ 0) := h 0 hi
    exact (h₂ 0).mp (finiteDimensional_cohomology_X₂ k X hS 0)
  · have : FiniteDimensional k (Cohomology (tensorSequence I E).X₁ 1) := h 1 hi
    exact (h₂ 1).mp (finiteDimensional_cohomology_X₂ k X hS 1)
  · -- `H⁰(E ⊗ I)` is a subspace of `H⁰(E)`.
    have : FiniteDimensional k (Cohomology (tensorSequence I E).X₂ 0) := (h₂ 0).mpr (h 0 hi)
    have := hS.mono_f
    exact finiteDimensional_cohomology_zero_of_mono k X (tensorSequence I E).f
  · have : FiniteDimensional k (Cohomology (tensorSequence I E).X₂ 1) := (h₂ 1).mpr (h 1 hi)
    exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl

variable {E} in
include k in
/-- **Twisting by an ideal sheaf preserves vanishing of higher cohomology.** If `I ⊆ 𝒪_X` cuts out
a closed subscheme finite over the field `k` and `E` is a vector bundle of constant rank on `X`,
then for `n ≥ 2` the cohomology `Hⁿ(E ⊗ I)` vanishes exactly when `Hⁿ(E)` does. -/
theorem subsingleton_cohomology_tensor_sheaf_iff {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton (Cohomology (E.obj.obj ⊗ I.sheaf) n) ↔ Subsingleton (Cohomology E.obj.obj n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have hS := shortExact_tensorSequence I E
  -- The last term `E ⊗ ι_* 𝒪_{V(I)}` of the sequence has no cohomology in positive degrees, and
  -- the middle term is `E ⊗ 𝒪_X ≅ E`.
  have h₃ (j : ℕ) : Subsingleton (Cohomology (tensorSequence I E).X₃ (j + 1)) :=
    subsingleton_cohomology_succ_tensor_pushforwardSubscheme k I E j
  have h₂ := (cohomologyBaseLinearEquivOfIso k (tensorUnitIso E)
    (m + 1 + 1)).toEquiv.subsingleton_congr
  exact ⟨fun h ↦ h₂.mp (subsingleton_cohomology_X₂ hS _ h (h₃ _)),
    fun h ↦ subsingleton_cohomology_X₁ hS (m + 1) (m + 1 + 1) rfl (h₃ m) (h₂.mpr h)⟩

/-- **The Euler characteristic of a twisted ideal sheaf.** If `I ⊆ 𝒪_X` cuts out a closed
subscheme `D` finite over the field `k` and `E` is a vector bundle of constant rank `r` on `X`
with finite-dimensional `H⁰(X, E)` and `H¹(X, E)`, then `χ(E ⊗ I) = χ(E) - r · dim_k Γ(D, 𝒪_D)`,
with `χ = dim H⁰ - dim H¹` and the dimension of `Γ(D, 𝒪_D)` written as the rank of `D ⟶ Spec k` at
the point `s`. For the trivial line bundle this is `eulerCharBelow_sheaf`. -/
theorem eulerCharBelow_tensor_sheaf [FiniteDimensional k (Cohomology E.obj.obj 0)]
    [FiniteDimensional k (Cohomology E.obj.obj 1)] (s : Spec (.of k)) :
    eulerCharBelow k X (E.obj.obj ⊗ I.sheaf) 2 =
      eulerCharBelow k X E.obj.obj 2 - r * (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  have hS := shortExact_tensorSequence I E
  have : Subsingleton (Cohomology (tensorSequence I E).X₃ 1) :=
    subsingleton_cohomology_succ_tensor_pushforwardSubscheme k I E 0
  have h₂ (i : ℕ) (hi : i < 2) : FiniteDimensional k (Cohomology (tensorSequence I E).X₂ i) := by
    refine (finiteDimensional_cohomology_tensorSequence_X₂_iff k I E i).mpr ?_
    interval_cases i <;> infer_instance
  have h₁ (i : ℕ) (hi : i < 2) (_ : 0 < i) :
      FiniteDimensional k (Cohomology (tensorSequence I E).X₁ i) :=
    (finiteDimensional_cohomology_tensor_sheaf_iff (k := k) I (E := E)).mpr
      (fun j hj ↦ by interval_cases j <;> infer_instance) i hi
  have hδ : cohomologyδBaseLinear k X hS 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have h : eulerCharBelow k X (E.obj.obj ⊗ SheafOfModules.unit X.ringCatSheaf) 2 =
      eulerCharBelow k X (E.obj.obj ⊗ I.sheaf) 2 +
      eulerCharBelow k X (E.obj.obj ⊗ I.pushforwardSubscheme) 2 :=
    eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1 h₁ h₂ hδ
  -- The terms of the sequence are `E ⊗ I`, `E ⊗ 𝒪_X ≅ E` and `E ⊗ ι_* 𝒪_{V(I)}`.
  rw [eulerCharBelow_congr k (tensorUnitIso E) 2,
    eulerCharBelow_tensor_pushforwardSubscheme_eq_mul_finrank k I E s] at h
  exact eq_sub_of_add_eq h.symm

end Tensor

section FiniteCohomology

variable [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The Euler characteristic of an ideal sheaf.** If `I ⊆ 𝒪_X` cuts out a closed subscheme
`D` finite over the field `k`, and `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are finite-dimensional, then
`χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`, with `χ = dim H⁰ - dim H¹` and the dimension of `Γ(D, 𝒪_D)`
written as the rank of `D ⟶ Spec k` at the point `s`. No dimension or properness hypothesis on
`X` is needed. -/
theorem eulerCharBelow_sheaf (s : Spec (.of k)) :
    eulerCharBelow k X I.sheaf 2 =
      eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 -
        (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  -- `𝒪_X` is a vector bundle of rank one.
  let E := (InvertibleSheaf.toFixedRankOne X).obj (InvertibleSheaf.trivial X)
  have hE : E.obj.obj = (InvertibleSheaf.trivial X).obj := by
    rw [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj]
  have : FiniteDimensional k (Cohomology E.obj.obj 0) := hE ▸ inferInstance
  have : FiniteDimensional k (Cohomology E.obj.obj 1) := hE ▸ inferInstance
  have h := eulerCharBelow_tensor_sheaf k I E s
  rw [hE, Nat.cast_one, one_mul] at h
  rw [← h]
  -- `I` is `𝒪_X ⊗ I`.
  exact eulerCharBelow_congr k
    (whiskerRightIso (InvertibleSheaf.trivialObjIsoUnit X) I.sheaf ≪≫ λ_ _).symm 2

/-- **An ideal sheaf of finite colength has finite-dimensional cohomology.** If `I ⊆ 𝒪_X` cuts out
a closed subscheme finite over the field `k`, and `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are
finite-dimensional, then so are `H⁰(X, I)` and `H¹(X, I)`. -/
theorem finiteDimensional_cohomology_sheaf {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology I.sheaf i) := by
  -- `𝒪_X` is a vector bundle of rank one, and `I` is `𝒪_X ⊗ I`.
  let E := (InvertibleSheaf.toFixedRankOne X).obj (InvertibleSheaf.trivial X)
  have hE : E.obj.obj = (InvertibleSheaf.trivial X).obj := by
    rw [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj]
  have h := (finiteDimensional_cohomology_tensor_sheaf_iff (k := k) I (E := E)).mpr
    (fun j hj ↦ by rw [hE]; interval_cases j <;> infer_instance) i hi
  rw [hE] at h
  exact (finiteDimensional_cohomology_congr k
    (whiskerRightIso (InvertibleSheaf.trivialObjIsoUnit X) I.sheaf ≪≫ λ_ _) i).mp h

end FiniteCohomology

end Finite

end

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### Euler characteristics along the Mayer–Vietoris sequence -/

section MayerVietoris

variable {r : ℕ} (E : FiniteLocallyFreeSheaf.FixedRank X r) (I J : X.IdealSheafData)
  [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))]
  (hI : ∀ i < 2, FiniteDimensional k
    (Cohomology ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E.obj).obj i))
  (hJ : ∀ i < 2, FiniteDimensional k
    (Cohomology ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj E.obj).obj i))

/-- The Mayer–Vietoris sequence of `V(I)` and `V(J)` tensored with `E`. -/
private abbrev tensorMayerVietoris : ShortComplex X.Modules :=
  (mayerVietoris I J).map (tensorLeft E.obj.obj)

private lemma shortExact_tensorMayerVietoris : (tensorMayerVietoris E I J).ShortExact :=
  shortExact_map_tensorLeft E.obj.obj (shortExact_mayerVietoris I J)

/-- The middle term of the tensored sequence is `E ⊗ 𝒪_{V(I)} ⊞ E ⊗ 𝒪_{V(J)}`. -/
private def tensorMayerVietorisX₂Iso :
    (tensorMayerVietoris E I J).X₂ ≅
      (E.obj.obj ⊗ I.pushforwardSubscheme) ⊞ (E.obj.obj ⊗ J.pushforwardSubscheme) :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft E.obj.obj)
  eqToIso (by rw [ShortComplex.map_X₂, mayerVietoris_X₂]) ≪≫
    (tensorLeft E.obj.obj).mapBiprod I.pushforwardSubscheme J.pushforwardSubscheme

omit [IsFinite ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k))] in
include hI hJ in
private lemma finiteDimensional_cohomology_tensorMayerVietoris_X₂ {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology (tensorMayerVietoris E I J).X₂ i) := by
  have := (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k I E.obj i).mpr
    (hI i hi)
  have := (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k J E.obj i).mpr
    (hJ i hi)
  exact (finiteDimensional_cohomology_congr k (tensorMayerVietorisX₂Iso E I J) i).mpr
    inferInstance

include hI hJ in
private lemma finiteDimensional_cohomology_tensorMayerVietoris_X₁ {i : ℕ} (hi : i < 2) :
    FiniteDimensional k (Cohomology (tensorMayerVietoris E I J).X₁ i) := by
  have hS := shortExact_tensorMayerVietoris E I J
  have h₂ (i : ℕ) (hi : i < 2) :=
    finiteDimensional_cohomology_tensorMayerVietoris_X₂ k E I J hI hJ hi
  have : FiniteDimensional k (Cohomology (tensorMayerVietoris E I J).X₃ 0) := by
    rw [ShortComplex.map_X₃, mayerVietoris_X₃]
    exact finiteDimensional_cohomology_zero_tensor_pushforwardSubscheme k (I ⊔ J) E
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · have := hS.mono_f
    have := h₂ 0 (by omega)
    exact finiteDimensional_cohomology_zero_of_mono k X (tensorMayerVietoris E I J).f
  · have := h₂ 1 (by omega)
    exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl

include hI hJ in
/-- **Finiteness of cohomology on a union.** If the closed subschemes `V(I)` and `V(J)` meet in a
scheme finite over `k`, and the restrictions of a vector bundle `E` to them have
finite-dimensional cohomology, then so do `H⁰` and `H¹` of its restriction to `V(I ⊓ J)`. -/
theorem FiniteLocallyFreeSheaf.FixedRank.finiteDimensional_cohomology_pullback_subschemeι_inf
    {i : ℕ} (hi : i < 2) : FiniteDimensional k
      (Cohomology ((FiniteLocallyFreeSheaf.pullback (I ⊓ J).subschemeι).obj E.obj).obj i) :=
  (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k (I ⊓ J) E.obj i).mp <| by
    have := finiteDimensional_cohomology_tensorMayerVietoris_X₁ k E I J hI hJ hi
    rwa [ShortComplex.map_X₁, mayerVietoris_X₁] at this

include hI hJ in
/-- **Euler characteristics on a union of closed subschemes.** If the closed subschemes `V(I)`
and `V(J)` of `X` meet in a scheme finite over `k`, and the restrictions of a vector bundle `E` of
constant rank `r` to them have finite-dimensional cohomology, then
`χ(E|_{V(I ⊓ J)}) + r · dim_k Γ(V(I ⊔ J), 𝒪) = χ(E|_{V(I)}) + χ(E|_{V(J)})`, with
`χ = dim H⁰ - dim H¹` and the dimension written as the rank of `V(I ⊔ J) ⟶ Spec k` at `s`. -/
theorem FiniteLocallyFreeSheaf.FixedRank.eulerCharBelow_pullback_subschemeι_inf_add
    (s : Spec (.of k)) :
    eulerCharBelow k (I ⊓ J).subscheme
        ((FiniteLocallyFreeSheaf.pullback (I ⊓ J).subschemeι).obj E.obj).obj 2 +
        r * ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k)).finrank s =
      eulerCharBelow k I.subscheme
          ((FiniteLocallyFreeSheaf.pullback I.subschemeι).obj E.obj).obj 2 +
        eulerCharBelow k J.subscheme
          ((FiniteLocallyFreeSheaf.pullback J.subschemeι).obj E.obj).obj 2 := by
  have hS := shortExact_tensorMayerVietoris E I J
  have h₃ : Subsingleton (Cohomology (tensorMayerVietoris E I J).X₃ 1) := by
    rw [ShortComplex.map_X₃, mayerVietoris_X₃]
    exact subsingleton_cohomology_succ_tensor_pushforwardSubscheme k (I ⊔ J) E 0
  -- The connecting map out of `H¹` of the last term, which vanishes, is zero.
  have hδ : cohomologyδBaseLinear k X hS 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by
      rw [h₃.elim x 0, map_zero, LinearMap.zero_apply]
  have h := eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1
    (fun i hi _ ↦ finiteDimensional_cohomology_tensorMayerVietoris_X₁ k E I J hI hJ hi)
    (fun i hi ↦ finiteDimensional_cohomology_tensorMayerVietoris_X₂ k E I J hI hJ hi) hδ
  rw [eulerCharBelow_congr k (tensorMayerVietorisX₂Iso E I J) 2,
    eulerCharBelow_biprod k _ _ 2
      (fun i hi ↦ (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k I E.obj i).mpr
        (hI i hi))
      (fun i hi ↦ (finiteDimensional_cohomology_tensor_pushforwardSubscheme_iff k J E.obj i).mpr
        (hJ i hi)),
    eulerCharBelow_tensor_pushforwardSubscheme, eulerCharBelow_tensor_pushforwardSubscheme] at h
  -- The first and last terms are `E ⊗ 𝒪_{V(I ⊓ J)}` and `E ⊗ 𝒪_{V(I ⊔ J)}`.
  have h₁ : eulerCharBelow k X (tensorMayerVietoris E I J).X₁ 2 =
      eulerCharBelow k (I ⊓ J).subscheme
        ((FiniteLocallyFreeSheaf.pullback (I ⊓ J).subschemeι).obj E.obj).obj 2 := by
    rw [ShortComplex.map_X₁, mayerVietoris_X₁]
    exact eulerCharBelow_tensor_pushforwardSubscheme k (I ⊓ J) E.obj 2
  have h₃ : eulerCharBelow k X (tensorMayerVietoris E I J).X₃ 2 =
      r * ((I ⊔ J).subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
    rw [ShortComplex.map_X₃, mayerVietoris_X₃]
    exact eulerCharBelow_tensor_pushforwardSubscheme_eq_mul_finrank k (I ⊔ J) E s
  rw [h₁, h₃] at h
  exact h.symm

end MayerVietoris

end

end TauCeti.AlgebraicGeometry
