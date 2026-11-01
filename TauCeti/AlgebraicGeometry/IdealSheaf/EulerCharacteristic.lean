/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorSequence
public import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# The Euler characteristic of an ideal sheaf

Let `X` be a scheme over a field `k` and `I ⊆ 𝒪_X` an ideal sheaf whose closed subscheme
`D = V(I)` is finite over `k`, of rank `dim_k Γ(D, 𝒪_D)`. The exact sequence
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_D ⟶ 0` and the vanishing of higher cohomology on the affine Noetherian
scheme `D` give

  `χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_sheaf`), where `χ` is the degree-`2` truncation
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional.

More generally, for a line bundle `L` on `X`, tensoring the sequence with `L` gives
`0 ⟶ L ⊗ I ⟶ L ⟶ L ⊗ ι_* 𝒪_D ⟶ 0`. By the projection formula the last term is the direct image
of the pullback of `L` to `D`, a line bundle on a discrete scheme and hence trivial. So `L ⊗ I`
has finite-dimensional `H⁰` and `H¹` exactly when `L` does
(`Scheme.IdealSheafData.finiteDimensional_cohomology_tensor_sheaf_iff`), and then

  `χ(L ⊗ I) = χ(L) - dim_k Γ(D, 𝒪_D)`

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
    letI : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
    letI : Algebra k Γ(I.subscheme, ⊤) := (baseRingToGlobalSections k I.subscheme).toAlgebra
    algebraMap k Γ(I.subscheme, ⊤) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ X ↘ Spec (.of k)).appTop).hom := by
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  exact RingHom.ext fun r ↦ baseRingToGlobalSections_apply k I.subscheme r

section Finite

variable [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))]

/-- `H⁰` of the direct image `ι_* 𝒪_{V(I)}` of the structure sheaf of a closed subscheme finite
over `k` is finite-dimensional. -/
private lemma finiteDimensional_cohomology_zero_pushforward :
    FiniteDimensional k (Cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)) 0) := by
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : I.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
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
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
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
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ X ↘ Spec (.of k)⟩
  have : I.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  let _ : IsFinite (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)))
  rw [Scheme.Hom.eulerCharBelow_pushforward_structureSheaf I.subschemeι k s 1,
    comp_over I.subschemeι (Spec (.of k))]

section Tensor

variable (L : InvertibleSheaf X)

include k in
/-- On the closed subscheme `V(I)`, finite over `k` and hence discrete, every line bundle is
trivial; so tensoring `ι_* 𝒪_{V(I)}` with a line bundle `L` on `X`, which by the projection formula
is the direct image of the pullback of `L` to `V(I)`, does not change it. -/
private lemma nonempty_tensor_pushforward_iso :
    Nonempty (L.obj ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) := by
  have : IsLocallyArtinian I.subscheme :=
    .of_locallyQuasiFinite (I.subschemeι ≫ X ↘ Spec (.of k))
  obtain ⟨e⟩ := LineBundleClass.mk_eq_one_iff.mp
    (Subsingleton.elim (LineBundleClass.mk ((InvertibleSheaf.pullback I.subschemeι).obj L)) 1)
  -- The projection formula is stated for the monoidal unit of `V(I).Modules`.
  have hu : 𝟙_ I.subscheme.Modules = SheafOfModules.unit I.subscheme.ringCatSheaf :=
    TauCeti.SheafOfModules.tensorUnit_eq I.subscheme.sheaf
  rw [← hu]
  exact ⟨FiniteLocallyFreeSheaf.tensorPushforwardUnitIso I.subschemeι
      ((InvertibleSheaf.toFiniteLocallyFree X).obj L) ≪≫
    (Scheme.Modules.pushforward I.subschemeι).mapIso
      (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj _ _) ≪≫
        eqToIso (InvertibleSheaf.pullback_obj_obj _ _).symm ≪≫ e)⟩

/-- The right unitor `L ⊗ 𝒪_X ≅ L`, with `𝒪_X` written as the structure sheaf
`SheafOfModules.unit X.ringCatSheaf` appearing in the exact sequence of `V(I)` rather than as the
monoidal unit `𝟙_ X.Modules`; the two agree by `TauCeti.SheafOfModules.tensorUnit_eq`. -/
private def tensorUnitIso : L.obj ⊗ SheafOfModules.unit X.ringCatSheaf ≅ L.obj :=
  eqToIso (congrArg (L.obj ⊗ ·) (TauCeti.SheafOfModules.tensorUnit_eq X.sheaf).symm) ≪≫ ρ_ L.obj

/-- The exact sequence of `V(I)` tensored with `L`:
`0 ⟶ L ⊗ I ⟶ L ⊗ 𝒪_X ⟶ L ⊗ ι_* 𝒪_{V(I)} ⟶ 0`. -/
private abbrev tensorSequence : ShortComplex X.Modules :=
  (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft L.obj)

/-- `L` is finite locally free, so tensoring with it preserves the exact sequence of `V(I)`. -/
private lemma shortExact_tensorSequence : (tensorSequence I L).ShortExact :=
  I.shortExact_tensor_toPushforwardSubscheme ((InvertibleSheaf.toFiniteLocallyFree X).obj L).obj

omit [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))] in
/-- The middle term of the tensored sequence is `L ⊗ 𝒪_X ≅ L`. -/
private lemma finiteDimensional_cohomology_tensorSequence_X₂_iff (i : ℕ) :
    FiniteDimensional k (Cohomology (tensorSequence I L).X₂ i) ↔
      FiniteDimensional k (Cohomology L.obj i) :=
  finiteDimensional_cohomology_congr k (tensorUnitIso L) i

/-- `H⁰` of the last term `L ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}` is finite-dimensional. -/
private lemma finiteDimensional_cohomology_zero_tensorSequence_X₃ :
    FiniteDimensional k (Cohomology (tensorSequence I L).X₃ 0) := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I L
  exact (finiteDimensional_cohomology_congr k e₃ 0).mpr
    (finiteDimensional_cohomology_zero_pushforward k I)

include k in
/-- `H¹` of the last term `L ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}` vanishes. -/
private lemma subsingleton_cohomology_one_tensorSequence_X₃ :
    Subsingleton (Cohomology (tensorSequence I L).X₃ 1) := by
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I L
  have := subsingleton_cohomology_one_pushforward k I
  exact (cohomologyBaseLinearEquivOfIso k e₃ 1).subsingleton

variable {k L} in
/-- **Twisting by an ideal sheaf preserves finiteness of cohomology.** If `I ⊆ 𝒪_X` cuts out a
closed subscheme finite over the field `k` and `L` is a line bundle on `X`, then `H⁰` and `H¹` of
`L ⊗ I` are finite-dimensional exactly when those of `L` are. -/
theorem finiteDimensional_cohomology_tensor_sheaf_iff :
    (∀ i < 2, FiniteDimensional k (Cohomology (L.obj ⊗ I.sheaf) i)) ↔
      ∀ i < 2, FiniteDimensional k (Cohomology L.obj i) := by
  have hS := shortExact_tensorSequence I L
  have h₂ := finiteDimensional_cohomology_tensorSequence_X₂_iff k I L
  have := finiteDimensional_cohomology_zero_tensorSequence_X₃ k I L
  have := subsingleton_cohomology_one_tensorSequence_X₃ k I L
  -- The first term `(tensorLeft L.obj).obj I.sheaf` of the sequence is `L.obj ⊗ I.sheaf` by
  -- `tensorLeft_obj`, which holds by `rfl`.
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩ <;> obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · have : FiniteDimensional k (Cohomology (tensorSequence I L).X₁ 0) := h 0 hi
    exact (h₂ 0).mp (finiteDimensional_cohomology_X₂ k X hS 0)
  · have : FiniteDimensional k (Cohomology (tensorSequence I L).X₁ 1) := h 1 hi
    exact (h₂ 1).mp (finiteDimensional_cohomology_X₂ k X hS 1)
  · -- `H⁰(L ⊗ I)` is a subspace of `H⁰(L)`.
    have : FiniteDimensional k (Cohomology (tensorSequence I L).X₂ 0) := (h₂ 0).mpr (h 0 hi)
    have := hS.mono_f
    exact finiteDimensional_cohomology_zero_of_mono k X (tensorSequence I L).f
  · have : FiniteDimensional k (Cohomology (tensorSequence I L).X₂ 1) := (h₂ 1).mpr (h 1 hi)
    exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl

/-- **The Euler characteristic of a twisted ideal sheaf.** If `I ⊆ 𝒪_X` cuts out a closed
subscheme `D` finite over the field `k` and `L` is a line bundle on `X` with finite-dimensional
`H⁰(X, L)` and `H¹(X, L)`, then `χ(L ⊗ I) = χ(L) - dim_k Γ(D, 𝒪_D)`, with `χ = dim H⁰ - dim H¹`
and the dimension of `Γ(D, 𝒪_D)` written as the rank of `D ⟶ Spec k` at the point `s`. For the
trivial line bundle this is `eulerCharBelow_sheaf`. -/
theorem eulerCharBelow_tensor_sheaf [FiniteDimensional k (Cohomology L.obj 0)]
    [FiniteDimensional k (Cohomology L.obj 1)] (s : Spec (.of k)) :
    eulerCharBelow k X (L.obj ⊗ I.sheaf) 2 =
      eulerCharBelow k X L.obj 2 - (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  have hS := shortExact_tensorSequence I L
  obtain ⟨e₃⟩ := nonempty_tensor_pushforward_iso k I L
  have := subsingleton_cohomology_one_tensorSequence_X₃ k I L
  have h₂ (i : ℕ) (hi : i < 2) : FiniteDimensional k (Cohomology (tensorSequence I L).X₂ i) := by
    refine (finiteDimensional_cohomology_tensorSequence_X₂_iff k I L i).mpr ?_
    interval_cases i <;> infer_instance
  have h₁ (i : ℕ) (hi : i < 2) (_ : 0 < i) :
      FiniteDimensional k (Cohomology (tensorSequence I L).X₁ i) :=
    (finiteDimensional_cohomology_tensor_sheaf_iff (k := k) I (L := L)).mpr
      (fun j hj ↦ by interval_cases j <;> infer_instance) i hi
  have hδ : cohomologyδBaseLinear k X hS 1 2 rfl = 0 :=
    LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have h : eulerCharBelow k X (L.obj ⊗ SheafOfModules.unit X.ringCatSheaf) 2 =
      eulerCharBelow k X (L.obj ⊗ I.sheaf) 2 +
      eulerCharBelow k X (L.obj ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) 2 :=
    eulerCharBelow_eq_add_of_cohomologyδ_eq_zero k hS 1 h₁ h₂ hδ
  -- The terms of the sequence are `L ⊗ I`, `L ⊗ 𝒪_X ≅ L` and `L ⊗ ι_* 𝒪_{V(I)} ≅ ι_* 𝒪_{V(I)}`.
  rw [eulerCharBelow_congr k (tensorUnitIso L) 2, eulerCharBelow_congr k e₃ 2,
    eulerCharBelow_pushforward k I s] at h
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
  rw [← eulerCharBelow_tensor_sheaf k I (InvertibleSheaf.trivial X) s]
  -- `I` is `𝒪_X ⊗ I`.
  exact eulerCharBelow_congr k
    (whiskerRightIso (InvertibleSheaf.trivialObjIsoUnit X) I.sheaf ≪≫ λ_ _).symm 2

end FiniteCohomology

end Finite

end

end AlgebraicGeometry.Scheme.IdealSheafData
