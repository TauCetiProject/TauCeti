/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
public import TauCeti.Analysis.Normed.Operator.PositiveDeterminant

/-!
# Linear maps act on local homology by the sign of their determinant

Let `E` be a finite-dimensional real normed space and `f : E →L[ℝ] E` a continuous linear map
which sends nonzero vectors to nonzero vectors, that is, an invertible linear map. Then `f`
induces a map of pairs `(E, E ∖ {0}) ⟶ (E, E ∖ {0})`, and the induced map on the local homology
`Hₖ(E, E ∖ {0})` at the origin is multiplication by the sign `±1` of `det f`
(`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`), in every degree and for every
coefficient object. Equivalently, the restriction of `f` to `E ∖ {0}` acts on the reduced homology
of `E ∖ {0}` by the same sign
(`TauCeti.reducedSingularHomologyFunctor_map_continuousLinearMap_compl_zero`).
In particular, `f` preserves each generator of `H_d(E, E ∖ {0}; ℤ) ≅ ℤ`, `d = dim E`, exactly
when `det f > 0`, and exchanges the two generators when `det f < 0`.

This is the linear case of the comparison between the local homology orientations of a manifold
and the orientations of its tangent spaces: the derivative of a chart transition acts on local
homology by the sign of its Jacobian.

The proof has two steps.

* A map of positive determinant is joined to the identity by a path of linear maps of positive
  determinant (`ContinuousLinearMap.exists_contDiff_det_pos`). This path is a homotopy of maps of
  pairs from the identity, so the map acts as the identity.
* In a Euclidean space a map `f` of negative determinant is `(f ∘ r) ∘ r` for a hyperplane
  reflection `r`, where `f ∘ r` has positive determinant. The reflection commutes with radial
  projection of `E ∖ {0}` onto the unit sphere, on whose homology it acts by `-1`
  (`TauCeti.reducedSingularHomologyFunctor_map_reflection_unitSphereMap`), and the reduced
  connecting morphism of `(E, E ∖ {0})`, an isomorphism since `E` is contractible, carries this
  to local homology. A general finite-dimensional real normed space is reduced to the Euclidean
  case by a continuous linear equivalence, which does not change determinants.

## Main results

* `TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`: an invertible continuous linear map
  acts on `Hₖ(E, E ∖ {0})` by `sign (det f)`.
* `TauCeti.reducedSingularHomologyFunctor_map_continuousLinearMap_compl_zero`: it acts on the
  reduced homology of `E ∖ {0}` by `sign (det f)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the degree of a reflection of a sphere and of the antipodal map, and Section 3.3,
  local orientations.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Normed

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The map of pairs `(E, E ∖ {0}) ⟶ (E, E ∖ {0})` induced by a continuous linear map `f` that
sends nonzero vectors to nonzero vectors. -/
private abbrev complZeroMap (f : E →L[ℝ] E) (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) :
    TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E)) ⟶ TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E)) :=
  TopPair.ofSubsetMap (TopCat.ofHom (f : C(E, E))) hf

/-- The subspace component of `complZeroMap f hf` is the restriction of `f` to `E ∖ {0}`. -/
private lemma snd_complZeroMap (f : E →L[ℝ] E) (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) :
    TopPair.Hom.snd (complZeroMap f hf) =
      TopCat.ofHom ⟨hf.restrict, (map_continuous f).restrict hf⟩ := by
  ext x
  exact Subtype.ext (TopPair.ofSubsetMap_snd_apply (TopCat.ofHom (f : C(E, E))) hf x)

/-- **A linear map of positive determinant acts trivially on local homology at the origin.** A
path of maps of positive determinant from the identity to `f` is a homotopy of maps of pairs
`(E, E ∖ {0}) ⟶ (E, E ∖ {0})`. -/
private lemma singularHomologyMap_complZeroMap_of_det_pos [FiniteDimensional ℝ E]
    (f : E →L[ℝ] E) (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) (hdet : 0 < f.det) (k : ℕ) :
    TopPair.singularHomologyMap (complZeroMap f hf) R k = 𝟙 _ := by
  obtain ⟨γ, hγ, hγ0, hγ1, hγdet⟩ := f.exists_contDiff_det_pos hdet
  let H : ContinuousMap.Homotopy (ContinuousMap.id E) (f : C(E, E)) :=
    { toFun p := γ p.1 p.2
      continuous_toFun :=
        (hγ.continuous.comp (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd
      map_zero_left x := by simp [hγ0]
      map_one_left x := by simp [hγ1] }
  have h := (TopPair.ofSubsetHomotopy (g₀ := 𝟙 (TopCat.of E))
    (g₁ := TopCat.ofHom (f : C(E, E))) (B := ({0}ᶜ : Set E)) (B' := ({0}ᶜ : Set E)) H fun τ _ hx ↦
      ((γ τ).toContinuousLinearEquivOfDetNeZero (hγdet τ).ne').map_ne_zero_iff.2 hx
    ).congr_singularHomologyMap R k
  rw [TopPair.ofSubsetMap_id (X := TopCat.of E) (B := ({0}ᶜ : Set E)) fun _ hx ↦ hx,
    TopPair.singularHomologyMap_id] at h
  exact h.symm

/-- A map of pairs `g : (E, E ∖ {0}) ⟶ (E, E ∖ {0})` acts on `Hₖ₊₁(E, E ∖ {0})` by an integer `s`
exactly when its restriction to `E ∖ {0}` acts on the reduced homology `H~ₖ(E ∖ {0})` by `s`: the
reduced connecting morphism of the pair is a natural isomorphism between the two. -/
private lemma singularHomologyMap_succ_eq_smul_iff
    (g : TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E)) ⟶ TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E)))
    (s : ℤ) (k : ℕ) :
    TopPair.singularHomologyMap g R (k + 1) = s • 𝟙 _ ↔
      (reducedSingularHomologyFunctor R k).map (TopPair.Hom.snd g) = s • 𝟙 _ := by
  have := @TopPair.isIso_reducedSingularHomologyδ_of_contractibleSpace _ _ _ _
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))) R (inferInstanceAs (ContractibleSpace E)) k
  have hδ := TopPair.reducedSingularHomologyδ_naturality R g k
  constructor
  · intro h
    rw [h, Preadditive.zsmul_comp, Category.id_comp] at hδ
    rw [← cancel_epi ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k),
      hδ, Preadditive.comp_zsmul, Category.comp_id]
  · intro h
    rw [h, Preadditive.comp_zsmul, Category.comp_id] at hδ
    rw [← cancel_mono ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k),
      ← hδ, Preadditive.zsmul_comp, Category.id_comp]

/-- If the conjugate `e ∘ f ∘ e⁻¹` of `f` by a continuous linear equivalence `e : E ≃L[ℝ] F` acts
on `Hₖ(F, F ∖ {0})` by an integer `s`, then `f` acts on `Hₖ(E, E ∖ {0})` by `s`. -/
private lemma singularHomologyMap_complZeroMap_of_conj {F : Type w} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (f : E →L[ℝ] E) (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ)
    (hf' : Set.MapsTo ((e : E →L[ℝ] F).comp (f.comp (e.symm : F →L[ℝ] E))) ({0}ᶜ : Set F) {0}ᶜ)
    (s : ℤ) (k : ℕ)
    (h : TopPair.singularHomologyMap (complZeroMap _ hf') R k = s • 𝟙 _) :
    TopPair.singularHomologyMap (complZeroMap f hf) R k = s • 𝟙 _ := by
  let ε := TopPair.ofSubsetMap (TopCat.ofHom (e : C(E, F))) (B := ({0}ᶜ : Set E))
    (B' := ({0}ᶜ : Set F)) fun _ hx ↦ e.map_ne_zero_iff.2 hx
  let ε' := TopPair.ofSubsetMap (TopCat.ofHom (e.symm : C(F, E))) (B := ({0}ᶜ : Set F))
    (B' := ({0}ᶜ : Set E)) fun _ hx ↦ e.symm.map_ne_zero_iff.2 hx
  have hinv : ε ≫ ε' = 𝟙 _ :=
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq (g'' := 𝟙 (TopCat.of E)) _ _
      (fun _ hx ↦ hx) (by ext x; simp)).trans (TopPair.ofSubsetMap_id _)
  have hsq : complZeroMap f hf ≫ ε = ε ≫ complZeroMap _ hf' :=
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (by ext x; simp)
  calc TopPair.singularHomologyMap (complZeroMap f hf) R k
      = TopPair.singularHomologyMap (complZeroMap f hf ≫ ε ≫ ε') R k := by
        rw [hinv, Category.comp_id]
    _ = TopPair.singularHomologyMap ε R k ≫ TopPair.singularHomologyMap (complZeroMap _ hf') R k ≫
          TopPair.singularHomologyMap ε' R k := by
        rw [← Category.assoc, hsq, Category.assoc, TopPair.singularHomologyMap_comp,
          TopPair.singularHomologyMap_comp]
    _ = s • 𝟙 _ := by
        rw [h, Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul,
          ← TopPair.singularHomologyMap_comp, hinv, TopPair.singularHomologyMap_id]

end Normed

section Euclidean

variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A hyperplane reflection of a real inner product space of dimension `n + 1` acts by `-1` on
the local homology `Hₙ₊₁(F, F ∖ {0})`: it commutes with radial projection onto the unit sphere,
on whose homology it acts by `-1`. -/
private lemma singularHomologyMap_complZeroMap_reflection {n : ℕ} (hF : finrank ℝ F = n + 1)
    {v : F} (hv : v ≠ 0) (hr : Set.MapsTo ((ℝ ∙ v)ᗮ.reflection : F →L[ℝ] F) ({0}ᶜ : Set F) {0}ᶜ) :
    TopPair.singularHomologyMap (complZeroMap _ hr) R (n + 1) = (-1 : ℤ) • 𝟙 _ := by
  rw [singularHomologyMap_succ_eq_smul_iff, snd_complZeroMap]
  let ρ := complSingletonHomotopyEquivSphere (0 : F)
  -- Radial projection onto the unit sphere commutes with the reflection.
  have hsq : TopCat.ofHom ⟨hr.restrict, (map_continuous _).restrict hr⟩ ≫ TopCat.ofHom ρ.toFun =
      TopCat.ofHom ρ.toFun ≫ TopCat.ofHom ⟨(ℝ ∙ v)ᗮ.reflection.toLinearIsometry.unitSphereMap,
        (ℝ ∙ v)ᗮ.reflection.toLinearIsometry.continuous_unitSphereMap⟩ := by
    ext x
    -- Evaluate the restriction before `simp` normalizes the coercion of the reflection, on which
    -- the proof of `hr` inside the restriction depends.
    simp only [ρ, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, Set.MapsTo.val_restrict_apply,
      coe_complSingletonHomotopyEquivSphere_apply, LinearIsometry.coe_unitSphereMap_apply, sub_zero]
    simp
  have hρ := ((reducedSingularHomologyFunctor R n).map_comp _ _).symm.trans
    ((congrArg (reducedSingularHomologyFunctor R n).map hsq).trans
      ((reducedSingularHomologyFunctor R n).map_comp _ _))
  rw [reducedSingularHomologyFunctor_map_reflection_unitSphereMap R hF hv] at hρ
  have : IsIso ((reducedSingularHomologyFunctor R n).map (TopCat.ofHom ρ.toFun)) := by
    rw [← ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom]
    infer_instance
  refine (cancel_mono ((reducedSingularHomologyFunctor R n).map (TopCat.ofHom ρ.toFun))).1
    (hρ.trans ?_)
  rw [Preadditive.comp_neg, Category.comp_id, neg_one_smul]
  exact ((Preadditive.neg_comp _ _).trans (congrArg Neg.neg (Category.id_comp _))).symm

/-- **A linear map of negative determinant acts by `-1` on top local homology**, in a real inner
product space of dimension `n + 1`. Composing with a hyperplane reflection reduces to positive
determinant. -/
private lemma singularHomologyMap_complZeroMap_of_det_neg {n : ℕ} (hF : finrank ℝ F = n + 1)
    (f : F →L[ℝ] F) (hf : Set.MapsTo f ({0}ᶜ : Set F) {0}ᶜ) (hdet : f.det < 0) :
    TopPair.singularHomologyMap (complZeroMap f hf) R (n + 1) = (-1 : ℤ) • 𝟙 _ := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let r : F →L[ℝ] F := (ℝ ∙ v)ᗮ.reflection
  have hr : Set.MapsTo r ({0}ᶜ : Set F) {0}ᶜ := fun _ hx ↦
    (ℝ ∙ v)ᗮ.reflection.map_ne_zero_iff.2 hx
  have hfr : Set.MapsTo (f.comp r) ({0}ᶜ : Set F) {0}ᶜ := fun _ hx ↦ hf (hr hx)
  have hdetr : r.det = -1 := by
    have hr' : (r : F →ₗ[ℝ] F) = (ℝ ∙ v)ᗮ.reflection.toLinearMap := LinearMap.ext fun _ ↦ rfl
    rw [ContinuousLinearMap.det, hr', Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hv, pow_one]
  have hpos : 0 < (f.comp r).det := by
    have : (f.comp r).det = f.det * r.det := by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    rw [this, hdetr]
    linarith
  -- Since `r ∘ r = 1`, the map `f` factors as `r` followed by `f ∘ r`.
  have hfac : complZeroMap r hr ≫ complZeroMap (f.comp r) hfr = complZeroMap f hf :=
    TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq hr hfr hf (by ext x; simp [r])
  rw [← hfac, TopPair.singularHomologyMap_comp,
    singularHomologyMap_complZeroMap_of_det_pos R _ _ hpos, Category.comp_id]
  exact singularHomologyMap_complZeroMap_reflection R hF hv hr

end Euclidean

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **An invertible linear map acts on local homology by the sign of its determinant.** Let `E`
be a finite-dimensional real normed space and `f : E →L[ℝ] E` a continuous linear map sending
nonzero vectors to nonzero vectors, that is, an invertible one. Then the map of pairs
`(E, E ∖ {0}) ⟶ (E, E ∖ {0})` induced by `f` acts on `Hₖ(E, E ∖ {0})` by `sign (det f) = ±1`, in
every degree `k`. -/
theorem singularHomologyMap_continuousLinearMap_compl_zero (f : E →L[ℝ] E)
    (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) (k : ℕ) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap (TopCat.ofHom (f : C(E, E))) hf) R k =
      (SignType.sign f.det : ℤ) • 𝟙 _ := by
  -- Since `f` is injective, its determinant is nonzero.
  have hker : LinearMap.ker (f : E →ₗ[ℝ] E) = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun x hx ↦ not_not.1 fun h ↦ hf h hx
  rcases ((LinearMap.isUnit_iff_isUnit_det _).1
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)).ne_zero.lt_or_gt with hdet | hdet
  · rw [sign_neg hdet]
    -- A map of negative determinant forces `E ≠ 0`; outside the top degree the group vanishes.
    obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n + 1 := Nat.exists_eq_succ_of_ne_zero fun h ↦ by
      have h1 : f.det = 1 := LinearMap.det_eq_one_of_finrank_eq_zero h _
      linarith
    by_cases hk : k = n + 1
    · subst hk
      let e := ContinuousLinearEquiv.ofFinrankEq
        (hn.trans (finrank_euclideanSpace_ulift_fin.{w} (n + 1)).symm)
      have hconj : ((e : E →L[ℝ] EuclideanSpace ℝ (ULift (Fin (n + 1)))).comp
          (f.comp (e.symm : EuclideanSpace ℝ (ULift (Fin (n + 1))) →L[ℝ] E))).det = f.det := by
        simp [ContinuousLinearMap.det]
      exact singularHomologyMap_complZeroMap_of_conj R e f hf
        (fun _ hy ↦ e.map_ne_zero_iff.2 (hf (e.symm.map_ne_zero_iff.2 hy))) _ _
        (singularHomologyMap_complZeroMap_of_det_neg R (finrank_euclideanSpace_ulift_fin (n + 1))
          _ _ (hconj ▸ hdet))
    · exact (isZero_singularHomology_complSingleton_of_ne R (OpenPartialHomeomorph.refl E)
        (Set.mem_univ (0 : E)) hn hk).eq_of_src _ _
  · rw [sign_pos hdet, SignType.coe_one, one_smul]
    exact singularHomologyMap_complZeroMap_of_det_pos R f hf hdet k

/-- **An invertible linear map acts on the reduced homology of the punctured space by the sign of
its determinant.** The restriction to `E ∖ {0}` of a continuous linear map `f : E →L[ℝ] E` sending
nonzero vectors to nonzero vectors acts on the reduced homology of `E ∖ {0}` by
`sign (det f) = ±1`, in every degree. -/
theorem reducedSingularHomologyFunctor_map_continuousLinearMap_compl_zero (f : E →L[ℝ] E)
    (hf : Set.MapsTo f ({0}ᶜ : Set E) {0}ᶜ) (k : ℕ) :
    (reducedSingularHomologyFunctor R k).map
        (TopCat.ofHom ⟨hf.restrict, (map_continuous f).restrict hf⟩) =
      (SignType.sign f.det : ℤ) • 𝟙 _ := by
  have h := (singularHomologyMap_succ_eq_smul_iff R (complZeroMap f hf) _ k).1
    (singularHomologyMap_continuousLinearMap_compl_zero R f hf (k + 1))
  rwa [snd_complZeroMap] at h

end TauCeti
