/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ConformalSymplecticNormal
public import TauCeti.Geometry.Contact.Levi
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
public import TauCeti.Geometry.Manifold.VectorBundle.ConstantRank
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Subbundle
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# The conformal symplectic normal bundle of an isotropic immersion

Let `D` be a smooth contact structure on a Hausdorff manifold `M`, and let `f : N → M` be a smooth
isotropic immersion: `f` is horizontal for `D` (`TauCeti.IsHorizontalMap`) and its differentials
are injective. At each `y : N` the conformal symplectic normal space
`(T_y N)^⊥ ⧸ T_y N` (`TauCeti.ConformalSymplecticNormal`) is the quotient of the Levi orthogonal
`(T_y N)^⊥ ⊆ D_(f y)` of the tangent image by the tangent image, with the nondegenerate form
induced by the Levi form, valued in the contact line. This file shows that these spaces form a
smooth vector bundle over a nonempty `N`, of rank `dim M - 2 dim N - 1`: the conformal symplectic
normal bundle of `f`, the normal data of the isotropic neighbourhood theorem.

* **The Levi orthogonal.** `TauCeti.leviOrthogonal J D f y ⊆ T_(f y) M` is the Levi orthogonal of
  the tangent image. If a smooth one-form `α` has kernel `D` near `f y`, it consists of the vectors
  `v` with `α (v) = 0` and `dα (df_y w, v) = 0` for every `w ∈ T_y N`
  (`TauCeti.mem_leviOrthogonal_iff_of_ker_eq`), and it has dimension `dim M - dim N - 1`
  (`TauCeti.IsHorizontalMap.finrank_leviOrthogonal_add`).
* **Local frames.** Near each point of `N`, with a local contact form `α` defining `D` and a local
  frame `eᵢ` of `TN`, the Levi orthogonals are the kernels of the smooth bundle map
  `f^* TM → ℝ^(1 + dim N)`, `v ↦ (α (v), (dα (df eᵢ, v))ᵢ)`, which is fibrewise onto by the
  dimension count. So they form a smooth subbundle of `f^* TM`
  (`TauCeti.hasLocalContMDiffSubbundleFrames_leviOrthogonal`), and, read in `D`, of the pullback
  `f^* D` of the contact structure (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`).
* **The bundle.** The tangent images form a smooth subbundle of the bundle of Levi orthogonals, and
  the quotient is the conformal symplectic normal bundle
  (`TauCeti.conformalSymplecticNormalPrebundle`), a smooth vector bundle
  (`TauCeti.contMDiffVectorBundle_conformalSymplecticNormalPrebundle`).

The bundle is defined from `D` alone: no contact form or coorientation is chosen, so it applies to
contact structures that are not the kernel of any global one-form. Local defining forms enter only
the proof that local frames exist.

## Main definitions

* `TauCeti.leviOrthogonal`: the Levi orthogonal of the tangent image of a map.
* `TauCeti.conformalSymplecticNormalPrebundle`: the conformal symplectic normal bundle of a smooth
  isotropic immersion, as a vector prebundle with fibres `TauCeti.ConformalSymplecticNormal`.

## Main results

* `TauCeti.hasLocalContMDiffSubbundleFrames_leviOrthogonal`,
  `TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`: the Levi orthogonals of a smooth
  isotropic immersion have smooth local frames.
* `TauCeti.contMDiffVectorBundle_conformalSymplecticNormalPrebundle`: the conformal symplectic
  normal bundle is a smooth vector bundle of rank `dim M - 2 dim N - 1`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle).
* S. Courte and S. Guillermou, *Introduction to symplectic and contact geometry*, course notes,
  Université Grenoble Alpes (2018), Proposition 3.5, p. 35 (the conformal symplectic normal bundle
  with values in the contact line).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (local frame criteria for subbundles and quotient bundles).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : N → M} {y : N}

/-! ### The Levi orthogonal of the tangent image -/

variable (J D f y) in
/-- The **Levi orthogonal** of the tangent image of `f : N → M` at `y` for a hyperplane field `D`:
the vectors `v ∈ D_(f y)` with `L_D (w, v) = 0` for every `w ∈ D_(f y)` in the tangent image
`df_y (T_y N)`, as a subspace of `T_(f y) M`. It is the image in `T_(f y) M` of the orthogonal
whose quotient is the conformal symplectic normal space `TauCeti.ConformalSymplecticNormal`. -/
def leviOrthogonal : Submodule ℝ (TangentSpace I (f y)) :=
  (((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
    (distributionLeviForm D (f y))).map (D (f y)).subtype

/-- A vector lies in the Levi orthogonal of the tangent image exactly when it lies in `D` and the
Levi form pairs every tangent image vector in `D` with it to zero. -/
theorem mem_leviOrthogonal_iff {v : TangentSpace I (f y)} :
    v ∈ leviOrthogonal J D f y ↔ ∃ h : v ∈ D (f y), ∀ w : D (f y),
      (w : TangentSpace I (f y)) ∈ LinearMap.range (mfderiv J I f y).toLinearMap →
        distributionLeviForm D (f y) w ⟨v, h⟩ = 0 := by
  simp only [leviOrthogonal, Submodule.mem_map, Submodule.subtype_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.property, fun w hw ↦ hu w hw⟩
  · rintro ⟨h, hv⟩
    exact ⟨⟨v, h⟩, fun w hw ↦ hv w hw, rfl⟩

/-- The Levi orthogonal lies in `D`. -/
theorem leviOrthogonal_le : leviOrthogonal J D f y ≤ D (f y) := fun _ hv ↦
  (mem_leviOrthogonal_iff.1 hv).1

section LocalForm

/-- **The Levi orthogonal in terms of a local defining form.** Let `D` have a `C¹` local frame
near `f y` and let the smooth one-form `α` have kernel `D` near `f y`. For a map `f` horizontal
for `D`, a vector `v` lies in the Levi orthogonal of the tangent image of `f` at `y` exactly when
`α (v) = 0` and `dα (df_y w, v) = 0` for every `w ∈ T_y N`. -/
theorem mem_leviOrthogonal_iff_of_ker_eq {k : ℕ} (hD : IsContMDiffDistribution I 1 k D)
    (hf : IsHorizontalMap J D f) {α : SmoothForm I M ℝ 1}
    (hα : ∀ᶠ z in 𝓝 (f y), RoughForm.ker α.val z = D z) {v : TangentSpace I (f y)} :
    v ∈ leviOrthogonal J D f y ↔ α.val (f y) ![v] = 0 ∧
      ∀ w : TangentSpace J y, mextDeriv α.val (f y) ![mfderiv J I f y w, v] = 0 := by
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.1 hD (f y)
  have hαd : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) z (α.val z)) (f y) :=
    α.contMDiff.mdifferentiableAt (by simp)
  have hDα : ∀ᶠ z in 𝓝 (f y), D z ≤ RoughForm.ker α.val z := hα.mono fun _ h ↦ h.ge
  have hker : ∀ u : TangentSpace I (f y), u ∈ D (f y) ↔ α.val (f y) ![u] = 0 := fun u ↦ by
    rw [← hα.self_of_nhds, RoughForm.mem_ker]
  -- The Levi form vanishes on a pair of vectors of `D` exactly when `dα` does.
  have hL : ∀ u w : D (f y), distributionLeviForm D (f y) u w = 0 ↔
      mextDeriv α.val (f y) ![(u : TangentSpace I (f y)), (w : TangentSpace I (f y))] = 0 := by
    intro u w
    obtain ⟨w', hw'⟩ := (D (f y)).mkQ_surjective (distributionLeviForm D (f y) u w)
    rw [← RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm hX (hU.mem_nhds hxU) hαd
      hDα hw', ← hw', ← hker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [mem_leviOrthogonal_iff]
  constructor
  · rintro ⟨hvD, hv⟩
    refine ⟨(hker v).1 hvD, fun w ↦ ?_⟩
    exact (hL ⟨_, hf.range_mfderiv_le y ⟨w, rfl⟩⟩ ⟨v, hvD⟩).1 (hv _ ⟨w, rfl⟩)
  · rintro ⟨hv₀, hv⟩
    refine ⟨(hker v).2 hv₀, fun w ⟨w₀, hw₀⟩ ↦ ?_⟩
    refine (hL w ⟨v, _⟩).2 ?_
    rw [← hw₀]
    exact hv w₀

/-- **The Levi orthogonal in terms of a local defining form and a basis.** If the smooth one-form
`α` has kernel `D` near `f y`, then `v` lies in the Levi orthogonal of the tangent image of a
horizontal map `f` at `y` exactly when `α (v) = 0` and `dα (df_y (b i), v) = 0` for every member
of a basis `b` of `T_y N`. -/
theorem mem_leviOrthogonal_iff_of_basis {k : ℕ} (hD : IsContMDiffDistribution I 1 k D)
    (hf : IsHorizontalMap J D f) {α : SmoothForm I M ℝ 1}
    (hα : ∀ᶠ z in 𝓝 (f y), RoughForm.ker α.val z = D z) {ι : Type*}
    (b : Module.Basis ι ℝ (TangentSpace J y)) {v : TangentSpace I (f y)} :
    v ∈ leviOrthogonal J D f y ↔ α.val (f y) ![v] = 0 ∧
      ∀ i, mextDeriv α.val (f y) ![mfderiv J I f y (b i), v] = 0 := by
  rw [mem_leviOrthogonal_iff_of_ker_eq hD hf hα]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ h (b i), fun h w ↦ ?_⟩
  -- `w ↦ dα (df_y w, v)` is linear and vanishes on the basis `b`.
  let L : TangentSpace J y →ₗ[ℝ] ℝ :=
    (((mextDeriv α.val (f y)).toContinuousMultilinearMap.toContinuousLinearMap
      ![0, v] 0).comp (mfderiv J I f y) : TangentSpace J y →L[ℝ] ℝ)
  have hL (w : TangentSpace J y) : L w = mextDeriv α.val (f y) ![mfderiv J I f y w, v] := by
    have hu : Function.update ![(0 : TangentSpace I (f y)), v] 0 (mfderiv J I f y w) =
        ![mfderiv J I f y w, v] := by
      funext j
      fin_cases j <;> rfl
    -- `toContinuousLinearMap` evaluates the form with the given slot updated, by definition.
    change (mextDeriv α.val (f y)).toContinuousMultilinearMap
      (Function.update ![0, v] 0 (mfderiv J I f y w)) = _
    rw [hu]
    rfl
  have hL0 : L = 0 := b.ext fun i ↦ by rw [hL, LinearMap.zero_apply]; exact h i
  rw [← hL, hL0, LinearMap.zero_apply]

/-- **The dimension of the Levi orthogonal.** For an isotropic map `f` into a contact manifold
with injective differential at `y`, the Levi orthogonal of the tangent image has dimension
`dim M - dim N - 1`. -/
theorem IsHorizontalMap.finrank_leviOrthogonal_add [FiniteDimensional ℝ E] {n : ℕ∞ω}
    [IsManifold I (n + 1) M] [IsManifold J 2 N] (hD : IsContactDistribution I n D) (hn : 1 ≤ n)
    (hf : IsHorizontalMap J D f) (hfy : ContMDiffAt J I 2 f y)
    (hinj : Injective (mfderiv J I f y)) :
    finrank ℝ (leviOrthogonal J D f y) + (finrank ℝ E' + 1) = finrank ℝ E := by
  have hcsn := hf.finrank_conformalSymplecticNormal_add hD hn hfy hinj
  set Wt := (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype
  set B := distributionLeviForm D (f y)
  -- `W^⊥ ⧸ W` is the conformal symplectic normal space, and `W ≤ W^⊥` has dimension `dim N`.
  have h1 : finrank ℝ (leviOrthogonal J D f y) = finrank ℝ (Wt.orthogonalBilin B) :=
    Submodule.finrank_map_subtype_eq _ _
  have h2 := Submodule.finrank_quotient_add_finrank (Wt.comap (Wt.orthogonalBilin B).subtype)
  have h3 : finrank ℝ (Wt.comap (Wt.orthogonalBilin B).subtype) = finrank ℝ Wt :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hf.le_orthogonalBilin hD hn hfy))
  have h4 : finrank ℝ Wt = finrank ℝ E' := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hf.range_mfderiv_le y)),
      LinearMap.finrank_range_of_inj hinj]
    rfl
  have h5 : finrank ℝ (ConformalSymplecticNormal J D f y) =
      finrank ℝ (Wt.orthogonalBilin B ⧸ Wt.comap (Wt.orthogonalBilin B).subtype) := rfl
  omega

end LocalForm

/-! ### Local frames of the Levi orthogonal -/

section Frames

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

variable (f) in
/-- The bundle map `f^* TM → ℝ^(k + 1)`, `v ↦ (α (v), (dα (Y i, v))ᵢ)`, of a one-form `α` and
sections `Y i` of `f^* TM`. Where `α` defines a contact structure `D` and the `Y i` form a basis of
the tangent image of `f`, its kernel is the Levi orthogonal. -/
private def leviOrthogonalMap {k : ℕ} (α : SmoothForm I M ℝ 1)
    (Y : Fin k → Π y, TangentSpace I (f y)) (y : N) :
    ((f : N → M) *ᵖ (TangentSpace I)) y →L[ℝ] Bundle.Trivial N (Fin (k + 1) → ℝ) y :=
  ContinuousLinearMap.pi (Fin.cons (SmoothForm.degreeOneEquiv α (f y)) fun i ↦
    ((mextDerivₗ I 1 α).val (f y)).toContinuousMultilinearMap.toContinuousLinearMap ![Y i y, 0] 1)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
  [IsManifold J ∞ N] [T2Space M] [TopologicalSpace N] [ContinuousMapClass K N M] in
private theorem leviOrthogonalMap_apply {k : ℕ} {f : K} (α : SmoothForm I M ℝ 1)
    (Y : Fin k → Π y, TangentSpace I (f y)) (y : N) (v : ((f : N → M) *ᵖ (TangentSpace I)) y) :
    leviOrthogonalMap f α Y y v =
      Fin.cons (α.val (f y) ![v]) fun i ↦ (mextDerivₗ I 1 α).val (f y) ![Y i y, v] := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact SmoothForm.degreeOneEquiv_apply_apply_vec α (f y) v
  · have hu : Function.update ![Y i y, (0 : TangentSpace I (f y))] 1 v = ![Y i y, v] := by
      funext j
      fin_cases j <;> rfl
    -- `toContinuousLinearMap` evaluates the form with the given slot updated, by definition.
    change ((mextDerivₗ I 1 α).val (f y)).toContinuousMultilinearMap
      (Function.update ![Y i y, 0] 1 v) = _
    rw [hu]
    rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] in
/-- The bundle map `TauCeti.leviOrthogonalMap` is smooth at every point where the sections `Y i`
are smooth as maps into `TM`: its components are a one-form and a two-form evaluated along smooth
maps into `TM`. -/
private theorem contMDiffAt_leviOrthogonalMap {k : ℕ} {f : K} (hf : ContMDiff J I ∞ f)
    (α : SmoothForm I M ℝ 1) {Y : Fin k → Π y, TangentSpace I (f y)} {y : N}
    (hY : ∀ i, ContMDiffAt J I.tangent ∞
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) (f y) (Y i y)) y) :
    letI := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := E) (E := TangentSpace I)
      (IB := I) (IB' := J) hf
    ContMDiffAt J (J.prod 𝓘(ℝ, E →L[ℝ] (Fin (k + 1) → ℝ))) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] (Fin (k + 1) → ℝ))
        (E := fun y ↦ ((f : N → M) *ᵖ (TangentSpace I)) y →L[ℝ]
          Bundle.Trivial N (Fin (k + 1) → ℝ) y) y (leviOrthogonalMap f α Y y)) y := by
  refine (contMDiffAt_hom_bundle_iff _ y).2 fun v ↦ ?_
  -- The induced map of total spaces, `(y, v) ↦ (y, α (v), (dα (Y i, v))ᵢ)`.
  have hb : ContMDiffAt (J.prod 𝓘(ℝ, E)) I ∞
      (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦ f p.proj) ⟨y, v⟩ :=
    hf.contMDiffAt.comp (⟨y, v⟩ : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)))
      (contMDiffAt_proj (F := E) ((f : N → M) *ᵖ (TangentSpace I)))
  have hsnd : ContMDiffAt (J.prod 𝓘(ℝ, E)) I.tangent ∞
      (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦
        TotalSpace.mk' E (E := TangentSpace I) (f p.proj) p.snd) ⟨y, v⟩ :=
    Bundle.Pullback.contMDiff_lift f hf _
  refine (Bundle.Trivial.contMDiffAt_mk_iff (I := J) (F := Fin (k + 1) → ℝ)
    (b := fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦ p.proj)
    (f := fun p ↦ leviOrthogonalMap f α Y p.proj p.snd)).2
    ⟨contMDiffAt_proj (IB := J) (F := E) ((f : N → M) *ᵖ (TangentSpace I)), ?_⟩
  refine (contMDiffAt_pi_module_iff.2 fun j ↦ ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun p ↦ leviOrthogonalMap_apply α Y p.proj p.snd)
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp only [Fin.cons_zero]
    have hα : ContMDiffAt (J.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (f p.proj)
          (SmoothForm.degreeOneEquiv α (f p.proj))) ⟨y, v⟩ :=
      ((SmoothForm.degreeOneEquiv α).contMDiff (f y)).comp
        (⟨y, v⟩ : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I))) hb
    exact (hα.clm_bundle_apply_scalar hsnd).congr_of_eventuallyEq (Eventually.of_forall
      fun p ↦ (SmoothForm.degreeOneEquiv_apply_apply_vec α (f p.proj) p.snd).symm)
  · simp only [Fin.cons_succ]
    have hYp : ContMDiffAt (J.prod 𝓘(ℝ, E)) I.tangent ∞
        (fun p : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)) ↦
          TotalSpace.mk' E (E := TangentSpace I) (f p.proj) (Y i p.proj)) ⟨y, v⟩ :=
      (hY i).comp (⟨y, v⟩ : TotalSpace E ((f : N → M) *ᵖ (TangentSpace I)))
        (contMDiffAt_proj (F := E) ((f : N → M) *ᵖ (TangentSpace I)))
    exact (Bundle.Trivial.contMDiffAt_mk_iff.1
      ((mextDerivₗ I 1 α).contMDiffAt_eval₂ hYp hsnd)).2.congr_of_eventuallyEq
        (Eventually.of_forall fun p ↦
          (SmoothBundleForm.eval₂_apply (mextDerivₗ I 1 α) (f p.proj) (Y i p.proj) p.snd).symm)

/-- **Local frames of the Levi orthogonal.** Near every point of `N`, the Levi orthogonals of the
tangent images of a smooth isotropic immersion `f` are the kernels of the smooth fibrewise
surjective bundle map `TauCeti.leviOrthogonalMap` built from a local contact form `α` defining
`D` and the pushforward of a local frame of `TN`. Hence they have smooth local frames. -/
private theorem exists_isSubbundleFrameOn_leviOrthogonal (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) (y₀ : N) :
    ∃ U : Set N, IsOpen U ∧ y₀ ∈ U ∧
      ∃ X : Fin (finrank ℝ E - finrank ℝ (Fin (finrank ℝ E' + 1) → ℝ)) →
          (Π y, ((f : N → M) *ᵖ (TangentSpace I)) y),
        IsSubbundleFrameOn (E := (f : N → M) *ᵖ (TangentSpace I)) E (leviOrthogonal J D f) X U ∧
          ∀ i, ContMDiffOn J (J.prod 𝓘(ℝ, E)) ∞
            (fun y ↦ TotalSpace.mk' E (E := (f : N → M) *ᵖ (TangentSpace I)) y (X i y)) U := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨W, hW, hy₀W, α, hα⟩ := hD.exists_smoothForm_ker_eq_isContactFormAt (f y₀)
  let eN := trivializationAt E' (TangentSpace J) y₀
  let b := Module.finBasis ℝ E'
  -- The pushforward of the local frame of `TN` given by the trivialization `eN`.
  let Y (i : Fin (finrank ℝ E')) (y : N) : TangentSpace I (f y) :=
    mfderiv J I f y (eN.localFrame b i y)
  have hY (i : Fin (finrank ℝ E')) : ContMDiffOn J I.tangent ∞
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) (f y) (Y i y)) eN.baseSet := fun y hy ↦
    ((ContMDiff.contMDiff_tangentMap hf (m := ∞) le_rfl).contMDiffAt.comp y
      ((eN.contMDiffOn_localFrame_baseSet (I := J) (n := ∞) b i).contMDiffAt
        (eN.open_baseSet.mem_nhds hy))).contMDiffWithinAt
  let A := leviOrthogonalMap f α Y
  let S := eN.baseSet ∩ (f : N → M) ⁻¹' W
  have hS : IsOpen S := eN.open_baseSet.inter (hW.preimage (map_continuous f))
  -- On `S`, the kernel of `A` is the Levi orthogonal.
  have hker (y : N) (hy : y ∈ S) : (A y).ker = leviOrthogonal J D f y := by
    ext v
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, leviOrthogonalMap_apply]
    refine Iff.trans ?_ (mem_leviOrthogonal_iff_of_basis (v := v)
      (hD.isContMDiffDistribution.of_le (by simp)) hfD
      (eventually_of_mem (hW.mem_nhds hy.2) fun z hz ↦ (hα z hz).1) (eN.basisAt b hy.1)).symm
    simp only [funext_iff, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, Y,
      eN.localFrame_apply_of_mem_baseSet b hy.1, mextDerivₗ_apply]
  -- On `S`, the bundle map is onto, by counting dimensions.
  have hsurj (y : N) (hy : y ∈ S) : Surjective (A y) := by
    have : FiniteDimensional ℝ (((f : N → M) *ᵖ (TangentSpace I)) y) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    have hr := LinearMap.finrank_range_add_finrank_ker (A y).toLinearMap
    have h1 : finrank ℝ (LinearMap.ker (A y).toLinearMap) + (finrank ℝ E' + 1) = finrank ℝ E := by
      rw [show LinearMap.ker (A y).toLinearMap = leviOrthogonal J D f y from hker y hy]
      exact hfD.finrank_leviOrthogonal_add hD (by simp) (hf.contMDiffAt.of_le (by simp)) (hinj y)
    have hF : finrank ℝ (Bundle.Trivial N (Fin (finrank ℝ E' + 1) → ℝ) y) = finrank ℝ E' + 1 :=
      Module.finrank_fin_fun ℝ
    have hE : finrank ℝ (((f : N → M) *ᵖ (TangentSpace I)) y) = finrank ℝ E := rfl
    refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq ?_)
    omega
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := E) (E := TangentSpace I)
    (IB := I) (IB' := J) hf
  obtain ⟨U, hUS, hU, hy₀U, X, hX, hXs⟩ := exists_isSubbundleFrameOn_ker_of_surjective hS
    (fun y hy ↦ (contMDiffAt_leviOrthogonalMap hf α fun i ↦
      (hY i).contMDiffAt (eN.open_baseSet.mem_nhds hy.1)).contMDiffWithinAt) hsurj
    ⟨FiberBundle.mem_baseSet_trivializationAt' y₀, hy₀W⟩
  exact ⟨U, hU, hy₀U, X, ⟨hX.continuousOn, hX.linearIndependent,
    fun hy ↦ (hX.span_eq hy).trans (hker _ (hUS hy))⟩, hXs⟩

/-- **The Levi orthogonal has smooth local frames.** For a smooth isotropic immersion `f` into a
smooth contact manifold, the Levi orthogonals of the tangent images form a smooth subbundle of
`f^* TM` of rank `dim M - dim N - 1`. -/
theorem hasLocalContMDiffSubbundleFrames_leviOrthogonal (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    HasLocalContMDiffSubbundleFrames (E := (f : N → M) *ᵖ (TangentSpace I)) J ∞ E
      (Fin (finrank ℝ E - (finrank ℝ E' + 1))) (leviOrthogonal J D f) := by
  refine hasLocalContMDiffSubbundleFrames_iff.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, hy₀, X, hX, hXs⟩ := exists_isSubbundleFrameOn_leviOrthogonal hD hf hfD hinj y₀
  have hr : finrank ℝ E - (finrank ℝ E' + 1) =
      finrank ℝ E - finrank ℝ (Fin (finrank ℝ E' + 1) → ℝ) := by
    rw [Module.finrank_fin_fun]
  refine ⟨U, hU, hy₀, fun i ↦ X (Fin.cast hr i), ⟨fun i ↦ hX.continuousOn _,
    fun hy ↦ (hX.linearIndependent hy).comp _ (Fin.cast_injective hr), fun hy ↦ ?_⟩,
    fun i ↦ hXs _⟩
  rw [← hX.span_eq hy, ← (finCongr hr).surjective.range_comp]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J ∞ N]
  [T2Space M] in
/-- A section of the pullback `f^* D` of a smooth distribution is smooth as soon as it is smooth
as a section of `f^* TM`. -/
private theorem contMDiffAt_pullback_distribution_mk {k : ℕ} (hD : IsContMDiffDistribution I ∞ k D)
    {f : K} (hf : ContMDiff J I ∞ f) {w : Π y, D (f y)} {y₀ : N}
    (hw : ContMDiffAt J (J.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E
      (E := (f : N → M) *ᵖ (TangentSpace I)) y (w y : TangentSpace I (f y))) y₀) :
    letI := hD.fiberBundle
    ContMDiffAt J (J.prod 𝓘(ℝ, Fin k → ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Fin k → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x) y (w y)) y₀ := by
  let := hD.fiberBundle
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact (Bundle.Pullback.contMDiffAt_iff f hf.contMDiffAt).2 ⟨contMDiffAt_id,
    hD.contMDiffAt_totalSpace_mk ((Bundle.Pullback.contMDiffAt_iff f hf.contMDiffAt).1 hw).2
      fun y ↦ (w y).property⟩

/-- **The Levi orthogonal inside the contact structure has smooth local frames.** For a smooth
isotropic immersion `f` into a smooth contact manifold `(M, D)`, the Levi orthogonals
`(T_y N)^⊥ ⊆ D_(f y)` of the tangent images form a smooth subbundle, of rank
`dim M - dim N - 1`, of the pullback `f^* D` of the contact structure, regarded as a vector bundle
(`TauCeti.IsContMDiffDistribution.fiberBundle`). Its quotients by the tangent images are the
conformal symplectic normal spaces. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalBilin (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    HasLocalContMDiffSubbundleFrames (E := (f : N → M) *ᵖ fun x ↦ D x) J ∞
      (Fin (finrank ℝ E - 1) → ℝ) (Fin (finrank ℝ E - (finrank ℝ E' + 1))) fun y ↦
        ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
          (distributionLeviForm D (f y)) := by
  let := hD.isContMDiffDistribution.fiberBundle
  classical
  refine hasLocalContMDiffSubbundleFrames_iff.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, hy₀, X, hX, hXs⟩ :=
    hasLocalContMDiffSubbundleFrames_iff.1 (hasLocalContMDiffSubbundleFrames_leviOrthogonal hD hf
      hfD hinj) y₀
  have hXD {y : N} (hy : y ∈ U) (i) : X i y ∈ D (f y) :=
    leviOrthogonal_le ((hX.span_eq hy).le (Submodule.subset_span ⟨i, rfl⟩))
  -- The frame, read in `D`; it is set to zero off `U`.
  let X' (i) (y : N) : D (f y) := if h : X i y ∈ D (f y) then ⟨X i y, h⟩ else 0
  have hX' {y : N} (hy : y ∈ U) (i) : (X' i y : TangentSpace I (f y)) = X i y := by
    simp only [X', hXD hy i, ↓reduceDIte]
    rfl
  have hsmooth (i) : ContMDiffOn J (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Fin (finrank ℝ E - 1) → ℝ)
        (E := (f : N → M) *ᵖ fun x ↦ D x) y (X' i y)) U := fun y hy ↦
    (contMDiffAt_pullback_distribution_mk hD.isContMDiffDistribution hf <|
      ((hXs i).contMDiffAt (hU.mem_nhds hy)).congr_of_eventuallyEq <|
        eventually_of_mem (hU.mem_nhds hy) fun z hz ↦ by
          -- The fibres of the pullback are those of `TM`; restated there so that `rw` applies.
          change (⟨z, (X' i z : TangentSpace I (f z))⟩ :
            TotalSpace E ((f : N → M) *ᵖ (TangentSpace I))) = ⟨z, X i z⟩
          rw [hX' hz]).contMDiffWithinAt
  refine ⟨U, hU, hy₀, X', ⟨fun i ↦ (hsmooth i).continuousOn, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩,
    hsmooth⟩
  · refine LinearIndependent.of_comp (D (f y)).subtype ?_
    -- The fibres of `f^* D` are the subspaces `D (f y)`; restated there so that `simp` applies.
    change LinearIndependent ℝ fun i ↦ ((X' i y : D (f y)) : TangentSpace I (f y))
    simp only [hX' hy]
    exact hX.linearIndependent hy
  · refine Submodule.map_injective_of_injective (D (f y)).injective_subtype ?_
    -- The fibres of `f^* D` are the subspaces `D (f y)`; restated there so that `rw` applies.
    change Submodule.map (D (f y)).subtype
      (Submodule.span ℝ (Set.range fun i ↦ (X' i y : D (f y)))) = leviOrthogonal J D f y
    rw [Submodule.map_span, ← Set.range_comp]
    -- The composite with the inclusion of `D` is the coercion to `TM`.
    change Submodule.span ℝ (Set.range fun i ↦ (X' i y : TangentSpace I (f y))) =
      leviOrthogonal J D f y
    simp only [hX' hy]
    exact hX.span_eq hy

end Frames

/-! ### The conformal symplectic normal bundle -/

section Bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

variable (J D) in
/-- The Levi orthogonals of the tangent images of `f` in `D`, as subspaces of the fibres of the
pullback `f^* D`. -/
private abbrev leviOrthogonalPullback (f : N → M) (y : N) :
    Submodule ℝ ((f *ᵖ fun x ↦ D x) y) :=
  ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
    (distributionLeviForm D (f y))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] in
/-- A basis `t` of the tangent image of a horizontal map `f` at `y`, read in the Levi orthogonal
of the tangent image inside `D`, is a basis of the tangent image there. -/
private theorem linearIndependent_and_span_eq_comap_range (hfD : IsHorizontalMap J D f) {y : N}
    (hiso : (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype ≤
      leviOrthogonalPullback J D f y)
    {ι : Type*} {t : ι → TangentSpace I (f y)} (ht : LinearIndependent ℝ t)
    (hspan : Submodule.span ℝ (Set.range t) = LinearMap.range (mfderiv J I f y).toLinearMap)
    {z : ι → leviOrthogonalPullback J D f y}
    (hz : ∀ i, (D (f y)).subtype (z i).val = t i) :
    LinearIndependent ℝ z ∧ Submodule.span ℝ (Set.range z) =
      ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype := by
  -- Both sides are compared through the injective inclusion into `T_(f y) M`.
  let L : leviOrthogonalPullback J D f y →ₗ[ℝ] TangentSpace I (f y) :=
    (D (f y)).subtype ∘ₗ (leviOrthogonalPullback J D f y).subtype
  have hL : Injective L := (D (f y)).injective_subtype.comp Subtype.val_injective
  have hLz : L ∘ z = t := funext hz
  refine ⟨LinearIndependent.of_comp L (hLz ▸ ht), Submodule.map_injective_of_injective hL ?_⟩
  rw [Submodule.map_span, ← Set.range_comp, hLz, hspan]
  ext v
  simp only [Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨⟨⟨v, hfD.range_mfderiv_le y hv⟩, hiso hv⟩, hv, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact hu

open Classical in
/-- The tangent images of a smooth isotropic immersion have smooth local frames inside the bundle
of their Levi orthogonals (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`). -/
private theorem hasLocalContMDiffSubbundleFrames_comap_range (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    HasLocalContMDiffSubbundleFrames J ∞ (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
      (Fin (finrank ℝ E')) (E := fun y ↦ leviOrthogonalPullback J D f y)
      fun y ↦ ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold J ((∞ : WithTop ℕ∞) + 1) N := IsManifold.of_le (n := ∞) (by simp)
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  have hW := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := hW.fiberBundle
  have hiso (y : N) : (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype ≤
      leviOrthogonalPullback J D f y :=
    hfD.le_orthogonalBilin hD (by simp) (hf.contMDiffAt.of_le (by simp))
  refine hasLocalContMDiffSubbundleFrames_iff.2 fun y₀ ↦ ?_
  obtain ⟨U, hU, hy₀, T, hT, hTs⟩ := hasLocalContMDiffSubbundleFrames_iff.1
    (ContMDiff.hasLocalContMDiffSubbundleFrames_range_mfderiv (m := ∞) hf le_rfl hinj) y₀
  have hTr {y : N} (hy : y ∈ U) (i) :
      T i y ∈ LinearMap.range (mfderiv J I f y).toLinearMap :=
    (hT.span_eq hy).le (Submodule.subset_span ⟨i, rfl⟩)
  -- The frame of the tangent images, read in the Levi orthogonals; it is set to zero off `U`.
  let Z (i) (y : N) : leviOrthogonalPullback J D f y :=
    if h : T i y ∈ LinearMap.range (mfderiv J I f y).toLinearMap then
      ⟨⟨T i y, hfD.range_mfderiv_le y h⟩, hiso y h⟩ else 0
  -- The values of `Z` in `D`.
  let zD (i) (y : N) : D (f y) := (Z i y).val
  have hZ {y : N} (hy : y ∈ U) (i) : (zD i y : TangentSpace I (f y)) = T i y := by
    simp only [zD, Z, hTr hy i, ↓reduceDIte]
    rfl
  have hsmooth (i) : ContMDiffOn J (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
        (E := fun y ↦ leviOrthogonalPullback J D f y) y (Z i y)) U := by
    refine hW.contMDiffOn_totalSpace_mk (b := id) (w := fun y ↦ zD i y) le_rfl
      (fun y hy ↦ ?_) fun y ↦ (Z i y).property
    refine (contMDiffAt_pullback_distribution_mk hD.isContMDiffDistribution hf ?_).contMDiffWithinAt
    refine ((hTs i).contMDiffAt (hU.mem_nhds hy)).congr_of_eventuallyEq <|
      eventually_of_mem (hU.mem_nhds hy) fun z hz ↦ ?_
    -- The fibres of the pullback are those of `TM`; restated there so that `rw` applies.
    change (⟨z, (zD i z : TangentSpace I (f z))⟩ :
      TotalSpace E ((f : N → M) *ᵖ (TangentSpace I))) = ⟨z, T i z⟩
    rw [hZ hz]
  have hbasis {y : N} (hy : y ∈ U) := linearIndependent_and_span_eq_comap_range hfD (hiso y)
    (hT.linearIndependent hy) (hT.span_eq hy) (z := (Z · y)) (hZ hy)
  exact ⟨U, hU, hy₀, Z, ⟨fun i ↦ (hsmooth i).continuousOn, fun hy ↦ (hbasis hy).1,
    fun hy ↦ (hbasis hy).2⟩, hsmooth⟩

omit [FiniteDimensional ℝ E'] [T2Space M] [ContinuousMapClass K N M] in
/-- The ranks of the subbundles in the construction of the conformal symplectic normal bundle: the
tangent image of rank `dim N` inside the Levi orthogonal of rank `dim M - dim N - 1`, with
quotient of rank `dim M - 2 dim N - 1`. -/
private theorem card_add_card_eq_finrank [Nonempty N] (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    Fintype.card (Fin (finrank ℝ E')) + Fintype.card (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1)) =
      finrank ℝ (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  let y : N := Classical.arbitrary N
  have h := hfD.finrank_conformalSymplecticNormal_add hD (by simp)
    (hf.contMDiffAt.of_le (by simp)) (hinj y)
  rw [Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun]
  omega

/-- **The conformal symplectic normal bundle.** Let `f : N → M` be a smooth isotropic immersion of
a nonempty manifold into a smooth contact manifold `(M, D)`. Its conformal symplectic normal spaces
`(T_y N)^⊥ ⧸ T_y N` (`TauCeti.ConformalSymplecticNormal`) form a vector prebundle over `N`, of rank
`dim M - 2 dim N - 1`: the quotient of the bundle of Levi orthogonals of the tangent images, a
smooth subbundle of `f^* D` (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalBilin`), by the
tangent images. Its pretrivializations are those of smooth local frames of the quotient, and it is
a smooth vector bundle
(`TauCeti.contMDiffVectorBundle_conformalSymplecticNormalPrebundle`). -/
def conformalSymplecticNormalPrebundle [Nonempty N] (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    VectorPrebundle ℝ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) :=
  letI := hD.isContMDiffDistribution.fiberBundle
  letI := hD.isContMDiffDistribution.vectorBundle
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).contMDiffVectorBundle
  (hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj).quotientPrebundle
    (card_add_card_eq_finrank hD hf hfD hinj)

/-- **The conformal symplectic normal bundle is a smooth vector bundle.** For a smooth isotropic
immersion `f : N → M` of a nonempty manifold into a smooth contact manifold `(M, D)`, the
conformal symplectic normal spaces `(T_y N)^⊥ ⧸ T_y N`, with the topology and atlas of
`TauCeti.conformalSymplecticNormalPrebundle`, form a smooth vector bundle of rank
`dim M - 2 dim N - 1` over `N`. -/
theorem contMDiffVectorBundle_conformalSymplecticNormalPrebundle [Nonempty N]
    (hD : IsContactDistribution I ∞ D) {f : K} (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toVectorBundle
    ContMDiffVectorBundle ∞ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) J := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).contMDiffVectorBundle
  exact (hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj
    ).contMDiffVectorBundle_quotientPrebundle
    (card_add_card_eq_finrank hD hf hfD hinj)

end Bundle

end TauCeti
