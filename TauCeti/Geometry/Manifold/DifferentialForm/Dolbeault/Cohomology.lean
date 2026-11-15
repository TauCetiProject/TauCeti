/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Complex
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Holomorphic
import TauCeti.Geometry.Manifold.Complex.Compact

/-!
# Functoriality and degree zero of Dolbeault cohomology

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)` and let `F` be a complex normed space. The
Dolbeault cohomology `H^(p,q)_∂bar(M; F)`, `TauCeti.dolbeaultCohomology E M F p q`, is the
cohomology of the Dolbeault complex `TauCeti.dolbeaultComplex E M F p`, with the class map
`TauCeti.dolbeaultCohomology.mk` from the `∂bar`-closed forms of type `(p,q)`.

A holomorphic map of complex manifolds is a smooth map of the underlying real manifolds which is
pseudoholomorphic for their almost complex structures. Pullback along it preserves `∂bar`-closed
and `∂bar`-exact forms of type `(p,q)`, so it induces complex-linear maps on Dolbeault cohomology,
contravariantly functorial in the map. Continuous complex-linear coefficient maps also induce
maps on closed forms and cohomology, covariantly functorial in the coefficients and commuting
with holomorphic pullback.

In degree `q = 0` there are no `∂bar`-exact forms, so `H^(p,0)_∂bar(M; F)` is the space of
`∂bar`-closed forms of type `(p,0)`, the holomorphic `p`-forms. For `p = 0` these are the
holomorphic functions `M → F` when the model `E` is finite-dimensional and `F` is complete.

## Main declarations

* `TauCeti.Dolbeault.closedForms.mpullback`: pullback of `∂bar`-closed forms of type `(p,q)` along
  a holomorphic map, with `mpullback_id`, `mpullback_comp` and `mpullback_mem_exactForms`.
* `TauCeti.dolbeaultCohomology.map`: the map induced by a holomorphic map, with `map_mk`, `map_id`
  and `map_comp`.
* `TauCeti.Dolbeault.closedForms.mapCoeff`: coefficient change on closed forms, with identity,
  composition, exactness preservation and compatibility with pullback.
* `TauCeti.dolbeaultCohomology.mapCoeff`: induced coefficient change on cohomology, with
  `mapCoeff_mk`, `mapCoeff_id`, `mapCoeff_comp` and `map_mapCoeff`.
* `TauCeti.dolbeaultCohomology.mkZeroEquiv`: `H^(p,0)_∂bar(M; F)` is the space of `∂bar`-closed
  forms of type `(p,0)`.
* `TauCeti.dolbeaultCohomology.zeroZeroEquiv`: `H^(0,0)_∂bar(M; F)` is the space of holomorphic
  functions `M → F`.
* `TauCeti.dolbeaultCohomology.zeroZeroEquivOfCompactSpace`: on a compact connected complex
  manifold, `H^(0,0)_∂bar(M; F)` is `F`, the space of constants.

## Implementation notes

The map induced by a holomorphic map descends pullback of closed forms along the surjective class
map with `LinearMap.liftOfSurjective`, as `TauCeti.deRhamCohomology.map` in
`TauCeti.Geometry.Manifold.DeRham.Map`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §2.
-/

public section

noncomputable section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure Dolbeault

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Holomorphic `p`-forms -/

namespace dolbeaultCohomology

/-- **`H^(p,0)` is the space of holomorphic `p`-forms.** The class map identifies the
`∂bar`-closed forms of type `(p,0)` with the Dolbeault cohomology `H^(p,0)_∂bar(M; F)`. -/
def mkZeroEquiv (p : ℕ) : closedForms E M F p 0 ≃ₗ[ℂ] dolbeaultCohomology E M F p 0 :=
  LinearEquiv.ofBijective (mk p 0)
    ⟨LinearMap.ker_eq_bot.1 <| by
      rw [ker_mk, exactForms_zero, Submodule.comap_bot, Submodule.ker_subtype],
      mk_surjective p 0⟩

/-- The identification of `H^(p,0)` with the `∂bar`-closed forms of type `(p,0)` is the class
map. -/
@[simp]
theorem mkZeroEquiv_apply (p : ℕ) (φ : closedForms E M F p 0) : mkZeroEquiv p φ = mk p 0 φ :=
  (rfl)

variable (E M F) in
/-- The `∂bar`-closed forms of type `(0,0)` are the smooth functions killed by `∂bar`. -/
private def closedFormsZeroZeroEquiv :
    closedForms E M F 0 0 ≃ₗ[ℂ] LinearMap.ker ((ofComplexManifold E M).delBar (F := F) (k := 0))
    where
  toFun φ := ⟨φ.1.1, (mem_closedForms 0 0 φ.1).1 φ.2⟩
  invFun φ := ⟨⟨φ.1, ((ofComplexManifold E M).mem_typeForms 0 0 φ.1).2
    (SmoothForm.isOfType_zero_zero φ.1 _)⟩, (mem_closedForms 0 0 _).2 φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [FiniteDimensional ℂ E] [CompleteSpace F]

variable (E M F) in
/-- **`H^(0,0)` is the space of holomorphic functions.** On a complex manifold with
finite-dimensional model, the Dolbeault cohomology `H^(0,0)_∂bar(M; F)` is the space of holomorphic
functions `M → F`, the complex `C^∞` maps. -/
def zeroZeroEquiv : dolbeaultCohomology E M F 0 0 ≃ₗ[ℂ] C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ, F), F⟯ :=
  (mkZeroEquiv 0).symm ≪≫ₗ closedFormsZeroZeroEquiv E M F ≪≫ₗ kerDelBarZeroEquiv E M F

/-- The holomorphic function of the class of a `∂bar`-closed function is the function itself. -/
@[simp]
theorem zeroZeroEquiv_mk (φ : closedForms E M F 0 0) (x : M) :
    zeroZeroEquiv E M F (mk 0 0 φ) x = φ.1.1.1 x 0 := by
  rw [zeroZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← mkZeroEquiv_apply,
    LinearEquiv.symm_apply_apply, kerDelBarZeroEquiv_apply]
  rfl

section CompactSpace

variable [CompactSpace M] [PreconnectedSpace M] [Nonempty M]

variable (E M F) in
/-- **`H^(0,0)` of a compact connected complex manifold is the space of constants.** The
holomorphic functions on a compact connected complex manifold with finite-dimensional model are
constant, so evaluation identifies `H^(0,0)_∂bar(M; F)` with `F`. -/
def zeroZeroEquivOfCompactSpace : dolbeaultCohomology E M F 0 0 ≃ₗ[ℂ] F :=
  zeroZeroEquiv E M F ≪≫ₗ holomorphicEquivOfCompactSpace 𝓘(ℂ, E) M

/-- The constant corresponding to the class of a `∂bar`-closed function on a compact connected
complex manifold is the value of that function at any point. This is not a `simp` lemma, since the
point `x` is free on the right. -/
theorem zeroZeroEquivOfCompactSpace_mk (φ : closedForms E M F 0 0) (x : M) :
    zeroZeroEquivOfCompactSpace E M F (mk 0 0 φ) = φ.1.1.1 x 0 := by
  rw [← zeroZeroEquiv_mk, zeroZeroEquivOfCompactSpace, LinearEquiv.trans_apply,
    holomorphicEquivOfCompactSpace_apply _ x]

/-- The class corresponding to a vector `c` is the class of the constant function `c`. -/
@[simp]
theorem zeroZeroEquiv_zeroZeroEquivOfCompactSpace_symm_apply (c : F) (x : M) :
    zeroZeroEquiv E M F ((zeroZeroEquivOfCompactSpace E M F).symm c) x = c := by
  rw [zeroZeroEquivOfCompactSpace, LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply,
    holomorphicEquivOfCompactSpace_symm_apply]

end CompactSpace

end dolbeaultCohomology

/-! ### Functoriality -/

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ∞ M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace E'' M''] [IsManifold 𝓘(ℂ, E'') ∞ M'']

namespace Dolbeault.closedForms

/-- Pullback of `∂bar`-closed forms of type `(p,q)` along a holomorphic map `f`, given as a smooth
map of the underlying real manifolds whose differential is complex-linear. -/
def mpullback {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ) :
    closedForms E' M' F p q →ₗ[ℂ] closedForms E M F p q where
  toFun φ := ⟨⟨SmoothForm.mpullback f hf φ.1.1, ((ofComplexManifold E M).mem_typeForms p q _).2
      ((((ofComplexManifold E' M').mem_typeForms p q _).1 φ.1.2).mpullback hf hJ)⟩, by
    rw [mem_closedForms, ← mpullback_delBar _ hf hJ, (mem_closedForms p q φ.1).1 φ.2, map_zero]⟩
  map_add' φ ψ := Subtype.ext <| Subtype.ext <| map_add _ φ.1.1 ψ.1.1
  map_smul' c φ := Subtype.ext <| Subtype.ext <| SmoothForm.mpullback_smul f hf c φ.1.1

/-- The underlying smooth form of the pullback of a `∂bar`-closed form is its pullback. -/
@[simp]
theorem coe_mpullback {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ)
    (φ : closedForms E' M' F p q) :
    (mpullback hf hJ p q φ).1.1 = SmoothForm.mpullback f hf φ.1.1 :=
  (rfl)

/-- Pullback of `∂bar`-closed forms along the identity is the identity. -/
@[simp]
theorem mpullback_id (p q : ℕ) :
    mpullback (F := F) (f := id) contMDiff_id (isPseudoholomorphic_id (ofComplexManifold E M))
      p q = LinearMap.id :=
  LinearMap.ext fun φ ↦ Subtype.ext <| Subtype.ext <|
    LinearMap.congr_fun SmoothForm.mpullback_id φ.1.1

/-- Pullback of `∂bar`-closed forms reverses composition. -/
theorem mpullback_comp {f : M → M'} {g : M' → M''} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f)
    (hg : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E'') ∞ g)
    (hJ' : IsPseudoholomorphic (ofComplexManifold E' M') (ofComplexManifold E'' M'') g)
    (p q : ℕ) :
    mpullback (F := F) (hg.comp hf) (hJ'.comp hJ) p q =
      mpullback hf hJ p q ∘ₗ mpullback hg hJ' p q :=
  LinearMap.ext fun φ ↦ Subtype.ext <| Subtype.ext <|
    LinearMap.congr_fun (SmoothForm.mpullback_comp f g hf hg) φ.1.1

/-- Pullback along a holomorphic map preserves `∂bar`-exact forms. -/
theorem mpullback_mem_exactForms {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ)
    (φ : closedForms E' M' F p q) (hφ : φ.1 ∈ exactForms E' M' F p q) :
    (mpullback hf hJ p q φ).1 ∈ exactForms E M F p q := by
  cases q with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hφ ⊢
    refine Subtype.ext ?_
    rw [coe_mpullback, hφ, Submodule.coe_zero, map_zero, Submodule.coe_zero]
  | succ q =>
    obtain ⟨ψ, hψ⟩ := (mem_exactForms_succ p q φ.1).1 hφ
    exact (mem_exactForms_succ p q _).2
      ⟨⟨SmoothForm.mpullback f hf ψ.1, ((ofComplexManifold E M).mem_typeForms p q _).2
        ((((ofComplexManifold E' M').mem_typeForms p q _).1 ψ.2).mpullback hf hJ)⟩, by
        rw [← mpullback_delBar _ hf hJ, hψ, coe_mpullback]⟩

end Dolbeault.closedForms

namespace dolbeaultCohomology

/-- Pullback followed by the class map kills the `∂bar`-exact forms. -/
private theorem ker_mk_le_ker_mk_comp_mpullback {f : M → M'}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ) :
    LinearMap.ker (mk (E := E') (M := M') (F := F) p q) ≤
      LinearMap.ker ((mk p q).comp (closedForms.mpullback hf hJ p q)) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker, LinearMap.comp_apply, mk_eq_zero_iff]
  exact closedForms.mpullback_mem_exactForms hf hJ p q φ hφ

/-- The complex-linear map on Dolbeault cohomology induced by a holomorphic map `f`, given as a
smooth map of the underlying real manifolds whose differential is complex-linear: it pulls back
classes along `f`. -/
def map {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ) :
    dolbeaultCohomology E' M' F p q →ₗ[ℂ] dolbeaultCohomology E M F p q :=
  LinearMap.liftOfSurjective (M := closedForms E' M' F p q)
    (M₂ := dolbeaultCohomology E' M' F p q) (M₃ := dolbeaultCohomology E M F p q) (f := mk p q)
    (mk_surjective p q)
    ⟨(mk p q).comp (closedForms.mpullback hf hJ p q), ker_mk_le_ker_mk_comp_mpullback hf hJ p q⟩

/-- The map induced by a holomorphic map sends the class of a `∂bar`-closed form to the class of
its pullback. -/
@[simp]
theorem map_mk {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f) (p q : ℕ)
    (φ : closedForms E' M' F p q) :
    map hf hJ p q (mk p q φ) = mk p q (closedForms.mpullback hf hJ p q φ) :=
  LinearMap.equivOfSurjective_apply _ _

/-- The map on Dolbeault cohomology induced by the identity is the identity. -/
@[simp]
theorem map_id (p q : ℕ) :
    map (F := F) (f := id) contMDiff_id (isPseudoholomorphic_id (ofComplexManifold E M)) p q =
      LinearMap.id := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  rw [map_mk, closedForms.mpullback_id, LinearMap.id_apply, LinearMap.id_apply]

/-- The maps on Dolbeault cohomology induced by holomorphic maps reverse composition. -/
theorem map_comp {f : M → M'} {g : M' → M''} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f)
    (hg : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E'') ∞ g)
    (hJ' : IsPseudoholomorphic (ofComplexManifold E' M') (ofComplexManifold E'' M'') g)
    (p q : ℕ) :
    map (F := F) (hg.comp hf) (hJ'.comp hJ) p q = map hf hJ p q ∘ₗ map hg hJ' p q := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  rw [LinearMap.comp_apply, map_mk, map_mk, map_mk,
    closedForms.mpullback_comp hf hJ hg hJ', LinearMap.comp_apply]

end dolbeaultCohomology

end Pullback

/-! ### Coefficient functoriality -/

section Coefficients

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

namespace Dolbeault.closedForms

/-- Applying a continuous complex-linear map to the coefficients of a closed type form. -/
def mapCoeff (L : F →L[ℂ] G) (p q : ℕ) :
    closedForms E M F p q →ₗ[ℂ] closedForms E M G p q where
  toFun φ := ⟨⟨SmoothForm.mapCoeff (L.restrictScalars ℝ) φ.1.1,
    (ofComplexManifold E M).mapCoeff_mem_typeForms
      (fun _ _ ↦ L.map_smul _ _) φ.1.2⟩, by
      rw [mem_closedForms, ← mapCoeff_delBar _ (fun _ _ ↦ L.map_smul _ _),
        (mem_closedForms p q φ.1).1 φ.2, map_zero]⟩
  map_add' _ _ := Subtype.ext <| Subtype.ext <| map_add _ _ _
  map_smul' c φ := Subtype.ext <| Subtype.ext <|
    SmoothForm.mapCoeff_smul_of_map_smul _ (fun _ ↦ L.map_smul c _) φ.1.1

/-- The underlying smooth form is obtained by applying the coefficient map pointwise. -/
@[simp]
theorem coe_mapCoeff (L : F →L[ℂ] G) (p q : ℕ) (φ : closedForms E M F p q) :
    (mapCoeff L p q φ).1.1 = SmoothForm.mapCoeff (L.restrictScalars ℝ) φ.1.1 := (rfl)

/-- The identity coefficient map fixes closed forms. -/
@[simp]
theorem mapCoeff_id (p q : ℕ) :
    mapCoeff (E := E) (M := M) (ContinuousLinearMap.id ℂ F) p q = LinearMap.id := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.congr_fun SmoothForm.mapCoeff_id φ.1.1

/-- Coefficient changes on closed forms respect composition. -/
theorem mapCoeff_comp (L : F →L[ℂ] G) (K : G →L[ℂ] H) (p q : ℕ) :
    mapCoeff (E := E) (M := M) (K.comp L) p q =
      (mapCoeff K p q).comp (mapCoeff L p q) := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.congr_fun
    (SmoothForm.mapCoeff_comp (K.restrictScalars ℝ) (L.restrictScalars ℝ)) φ.1.1

/-- Coefficient maps carry exact type forms to exact type forms. -/
theorem mapCoeff_mem_exactForms (L : F →L[ℂ] G) (p q : ℕ)
    (φ : closedForms E M F p q) (hφ : φ.1 ∈ exactForms E M F p q) :
    (mapCoeff L p q φ).1 ∈ exactForms E M G p q := by
  cases q with
  | zero =>
    have hzero : φ.1 = 0 := by simpa using hφ
    have hφzero : φ = 0 := Subtype.ext hzero
    rw [hφzero, map_zero, Submodule.coe_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨ψ, hψ⟩ := (mem_exactForms_succ p q φ.1).1 hφ
    refine (mem_exactForms_succ p q _).2 ⟨⟨SmoothForm.mapCoeff (L.restrictScalars ℝ) ψ.1,
      (ofComplexManifold E M).mapCoeff_mem_typeForms
        (fun _ _ ↦ L.map_smul _ _) ψ.2⟩, ?_⟩
    rw [← mapCoeff_delBar _ (fun _ _ ↦ L.map_smul _ _), hψ, coe_mapCoeff]

end Dolbeault.closedForms

namespace dolbeaultCohomology

/-- The complex-linear map on Dolbeault cohomology induced by a continuous complex-linear
coefficient map. -/
def mapCoeff (L : F →L[ℂ] G) (p q : ℕ) :
    dolbeaultCohomology E M F p q →ₗ[ℂ] dolbeaultCohomology E M G p q :=
  LinearMap.liftOfSurjective (f := mk (E := E) (M := M) (F := F) p q)
    (mk_surjective p q) ⟨(mk p q).comp (closedForms.mapCoeff L p q), by
      intro φ hφ
      rw [LinearMap.mem_ker, LinearMap.comp_apply, mk_eq_zero_iff]
      exact closedForms.mapCoeff_mem_exactForms L p q φ ((mk_eq_zero_iff p q φ).1 hφ)⟩

/-- On a closed representative, the induced coefficient map is its pointwise coefficient map. -/
@[simp]
theorem mapCoeff_mk (L : F →L[ℂ] G) (p q : ℕ) (φ : closedForms E M F p q) :
    mapCoeff L p q (mk p q φ) = mk p q (closedForms.mapCoeff L p q φ) :=
  LinearMap.equivOfSurjective_apply _ _

/-- The identity coefficient map induces the identity on cohomology. -/
@[simp]
theorem mapCoeff_id (p q : ℕ) :
    mapCoeff (E := E) (M := M) (ContinuousLinearMap.id ℂ F) p q = LinearMap.id := by
  apply LinearMap.ext
  intro c
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  rw [mapCoeff_mk, closedForms.mapCoeff_id, LinearMap.id_apply, LinearMap.id_apply]

/-- Successive coefficient changes induce the coefficient change of the composite. -/
theorem mapCoeff_comp (L : F →L[ℂ] G) (K : G →L[ℂ] H) (p q : ℕ) :
    mapCoeff (E := E) (M := M) (K.comp L) p q =
      (mapCoeff K p q).comp (mapCoeff L p q) := by
  apply LinearMap.ext
  intro c
  obtain ⟨φ, rfl⟩ := mk_surjective p q c
  simp only [LinearMap.comp_apply, mapCoeff_mk, closedForms.mapCoeff_comp]

end dolbeaultCohomology

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ∞ M']
  {f : M → M'} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ f)
  (hJ : IsPseudoholomorphic (ofComplexManifold E M) (ofComplexManifold E' M') f)

/-- Coefficient change commutes with holomorphic pullback on closed type forms. -/
@[simp]
theorem Dolbeault.closedForms.mpullback_mapCoeff (L : F →L[ℂ] G) (p q : ℕ)
    (φ : closedForms E' M' F p q) :
    closedForms.mpullback hf hJ p q (closedForms.mapCoeff L p q φ) =
      closedForms.mapCoeff L p q (closedForms.mpullback hf hJ p q φ) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [closedForms.coe_mpullback, closedForms.coe_mapCoeff]
  exact SmoothForm.mpullback_mapCoeff (L.restrictScalars ℝ) f hf φ.1.1

/-- Coefficient change commutes with holomorphic pullback on Dolbeault cohomology. -/
@[simp]
theorem dolbeaultCohomology.map_mapCoeff (L : F →L[ℂ] G) (p q : ℕ)
    (c : dolbeaultCohomology E' M' F p q) :
    map hf hJ p q (mapCoeff L p q c) = mapCoeff L p q (map hf hJ p q c) := by
  obtain ⟨φ, rfl⟩ := dolbeaultCohomology.mk_surjective p q c
  simp only [dolbeaultCohomology.mapCoeff_mk, dolbeaultCohomology.map_mk,
    closedForms.mpullback_mapCoeff]

end Coefficients

end TauCeti
