/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional.

More generally, for a vector bundle `E` of constant rank `r` on `X`, tensoring the sequence with
`E` gives `0 ⟶ E ⊗ I ⟶ E ⟶ E ⊗ ι_* 𝒪_D ⟶ 0`. By the projection formula the last term is the
direct image of the pullback of `E` to `D`, a vector bundle of rank `r` on a scheme finite over `k`
and hence free (`FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isFinite`). So `E ⊗ I` has
finite-dimensional `H⁰` and `H¹` exactly when `E` does
(`Scheme.IdealSheafData.finiteDimensional_cohomology_tensor_sheaf_iff`), and then

  `χ(E ⊗ I) = χ(E) - r · dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_tensor_sheaf`). No hypothesis on `X` is needed.

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
    Nonempty (E.obj.obj ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) ≅ freePushforward I r) := by
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  obtain ⟨e⟩ := FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isFinite k
    ((FiniteLocallyFreeSheaf.FixedRank.pullback I.subschemeι).obj E)
  -- The projection formula is stated for the monoidal unit of `V(I).Modules`.
  have hu : 𝟙_ I.subscheme.Modules = SheafOfModules.unit I.subscheme.ringCatSheaf :=
    TauCeti.SheafOfModules.tensorUnit_eq I.subscheme.sheaf
  rw [← hu]
  exact ⟨FiniteLocallyFreeSheaf.tensorPushforwardUnitIso I.subschemeι E.obj ≪≫
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
/-- `H¹` of `ι_* 𝒪_{V(I)}^r` vanishes, the closed subscheme being affine. -/
private lemma subsingleton_cohomology_one_freePushforward :
    Subsingleton (Cohomology (freePushforward I r) 1) := by
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  let M := (FiniteLocallyFreeSheaf.FixedRank.free I.subscheme r).obj.obj
  have := subsingleton_cohomology_succ_of_isAffineHom (I.subscheme ↘ Spec (.of k)) M 0
  exact (cohomologyPushforwardIso I.subschemeι M 1).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

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

/-- `H⁰` of the last term `E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}^r` is finite-dimensional. -/
private lemma finiteDimensional_cohomology_zero_tensorSequence_X₃ :
    FiniteDimensional k (Cohomology (tensorSequence I E).X₃ 0) := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I E
  exact (finiteDimensional_cohomology_congr k e₃ 0).mpr
    (finiteDimensional_cohomology_zero_freePushforward k I)

include k in
/-- `H¹` of the last term `E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}^r` vanishes. -/
private lemma subsingleton_cohomology_one_tensorSequence_X₃ :
    Subsingleton (Cohomology (tensorSequence I E).X₃ 1) := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I E
  have := subsingleton_cohomology_one_freePushforward k I (r := r)
  exact (cohomologyBaseLinearEquivOfIso k e₃ 1).subsingleton

variable {k E} in
/-- **Twisting by an ideal sheaf preserves finiteness of cohomology.** If `I ⊆ 𝒪_X` cuts out a
closed subscheme finite over the field `k` and `E` is a vector bundle of constant rank on `X`,
then `H⁰` and `H¹` of `E ⊗ I` are finite-dimensional exactly when those of `E` are. -/
theorem finiteDimensional_cohomology_tensor_sheaf_iff :
    (∀ i < 2, FiniteDimensional k (Cohomology (E.obj.obj ⊗ I.sheaf) i)) ↔
      ∀ i < 2, FiniteDimensional k (Cohomology E.obj.obj i) := by
  have hS := shortExact_tensorSequence I E
  have h₂ := finiteDimensional_cohomology_tensorSequence_X₂_iff k I E
  have := finiteDimensional_cohomology_zero_tensorSequence_X₃ k I E
  have := subsingleton_cohomology_one_tensorSequence_X₃ k I E
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
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I E
  have := subsingleton_cohomology_one_tensorSequence_X₃ k I E
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
      eulerCharBelow k X (E.obj.obj ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) 2 :=
    eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1 h₁ h₂ hδ
  -- The terms of the sequence are `E ⊗ I`, `E ⊗ 𝒪_X ≅ E` and
  -- `E ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}^r`.
  rw [eulerCharBelow_congr k (tensorUnitIso E) 2, eulerCharBelow_congr k e₃ 2,
    eulerCharBelow_freePushforward k I s] at h
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

end FiniteCohomology

end Finite

end

end AlgebraicGeometry.Scheme.IdealSheafData
