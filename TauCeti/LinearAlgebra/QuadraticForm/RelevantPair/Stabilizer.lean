/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Basic

/-!
# Stabilizer embeddings and isometry transport for orthogonal relevant pairs

Given an orthogonal relevant pair `P : OrthogonalRelevantPair Q_W Q_V j` with finite-dimensional
domain `W`, the orthogonal decomposition `V ≃qᵢ W ⊥ W^⊥` induces an injective group
homomorphism `SO(Q_W) →* SO(Q_V)` acting trivially on `W^⊥`. Transporting relevant pairs and
framed relevant pairs along isometric equivalences intertwines these stabilizer embeddings.

## Main definitions

* `TauCeti.OrthogonalRelevantPair.stabilizerHom`: the stabilizer embedding `SO(Q_W) →* SO(Q_V)`
  acting as the identity on `W^⊥`.
* `TauCeti.FramedOrthogonalRelevantPair.stabilizerHom`: the stabilizer embedding of a framed
  relevant pair.
* `TauCeti.OrthogonalRelevantPair.map`, `TauCeti.FramedOrthogonalRelevantPair.map`: transport along
  isometric equivalences.

## Main results

* `TauCeti.OrthogonalRelevantPair.stabilizerHom_injective`,
  `TauCeti.OrthogonalRelevantPair.mem_range_stabilizerHom_iff`: `stabilizerHom` is injective, with
  image the subgroup of `SO(Q_V)` fixing `W^⊥` pointwise.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_specialOrthogonalGroupCongr`: any intertwining pair
  of isometries intertwines the stabilizer embeddings.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_map`: transporting a relevant pair intertwines its
  stabilizer embedding.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

namespace TauCeti

/-! ### Stabilizer embedding `SO(Q_W) →* SO(Q_V)` -/

namespace OrthogonalRelevantPair

section Stabilizer

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (P : OrthogonalRelevantPair Q_W Q_V j)

/-- The stabilizer embedding `SO(Q_W) →* SO(Q_V)`, extending an element of `SO(Q_W)` by the
identity on the orthogonal complement `W^⊥`. -/
noncomputable def stabilizerHom :
    specialOrthogonalGroup Q_W →* specialOrthogonalGroup Q_V :=
  have := P.finiteDimensional_orthogonal
  (P.ambientIsometryEquiv.specialOrthogonalGroupCongr :
      specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)) →*
        specialOrthogonalGroup Q_V).comp
    ((specialOrthogonalGroupProd Q_W (Q_V.restrict P.orthogonal)).comp
      (MonoidHom.inl (specialOrthogonalGroup Q_W)
        (specialOrthogonalGroup (Q_V.restrict P.orthogonal))))

@[simp]
theorem stabilizerHom_apply_embed (g : specialOrthogonalGroup Q_W) (w : W) :
    (P.stabilizerHom g : V ≃ₗ[K] V) (P.embed w) = P.embed ((g : W ≃ₗ[K] W) w) := by
  have := P.finiteDimensional_orthogonal
  simp [stabilizerHom, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]

@[simp]
theorem stabilizerHom_apply_of_mem_orthogonal (g : specialOrthogonalGroup Q_W)
    {v : V} (hv : v ∈ P.orthogonal) :
    (P.stabilizerHom g : V ≃ₗ[K] V) v = v := by
  have := P.finiteDimensional_orthogonal
  have hu : P.ambientIsometryEquiv.symm v = (0, ⟨v, hv⟩) :=
    P.ambientIsometryEquiv_symm_of_mem_orthogonal ⟨v, hv⟩
  simp [stabilizerHom, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, hu]

/-- The stabilizer embedding `SO(Q_W) →* SO(Q_V)` is injective. -/
theorem stabilizerHom_injective : Function.Injective P.stabilizerHom := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  apply P.embed_injective
  have hw := congrArg (fun f : specialOrthogonalGroup Q_V ↦ (f : V ≃ₗ[K] V) (P.embed w)) h
  simpa using hw

private theorem mem_range_embed_of_fix_orthogonal {h : specialOrthogonalGroup Q_V}
    (hfix : ∀ v ∈ P.orthogonal, (h : V ≃ₗ[K] V) v = v) (w : W) :
    (h : V ≃ₗ[K] V) (P.embed w) ∈ LinearMap.range P.embed.toLinearMap := by
  have hBnd : Q_V.polarBilin.Nondegenerate := nondegenerate_polar_iff.mpr P.nondegenerate_codomain
  have horth : (P.orthogonal).orthogonalBilin Q_V.polarBilin =
      LinearMap.range P.embed.toLinearMap :=
    LinearMap.BilinForm.orthogonal_orthogonal_of_isCompl Q_V.polarBilin
      Q_V.isSymm_polarBilin.isRefl hBnd.2 _ P.isCompl_orthogonal
  rw [← horth, Submodule.mem_orthogonalBilin]
  intro u hu
  have hpol := polar_apply_of_mem_orthogonalGroup
    (specialOrthogonalGroup_le_orthogonalGroup Q_V h.property) u (P.embed w)
  rw [hfix u hu, QuadraticMap.polar_comm Q_V u (P.embed w),
    P.mem_orthogonal_iff.mp hu w] at hpol
  simpa [QuadraticMap.polarBilin_apply_apply] using hpol

private theorem exists_specialOrthogonalGroupProd_one_of_fix
    [FiniteDimensional K P.orthogonal]
    (h' : specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)))
    (hinvariant :
      ∀ w : W, ((h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0)).2 = 0)
    (hfix' : ∀ u : P.orthogonal,
      (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u) = (0, u)) :
    ∃ g₁ : specialOrthogonalGroup Q_W,
      specialOrthogonalGroupProd Q_W (Q_V.restrict P.orthogonal) (g₁, 1) = h' := by
  have hblock2 :
      LinearMap.snd K W P.orthogonal ∘ₗ
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal).toLinearMap ∘ₗ
          LinearMap.inr K W P.orthogonal = LinearMap.id := by
    ext u
    simp [hfix' u]
  have hmemO :
      (⟨h', specialOrthogonalGroup_le_orthogonalGroup _ h'.property⟩ :
          orthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal))) ∈
        (orthogonalGroupProd Q_W (Q_V.restrict P.orthogonal)).range :=
    (mem_range_orthogonalGroupProd_iff Q_W (Q_V.restrict P.orthogonal)).mpr
      ⟨hinvariant, fun u ↦ by simp [hfix' u]⟩
  obtain ⟨⟨f₁, f₂⟩, hf⟩ := hmemO
  have hcoe : (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) =
      (f₁ : W ≃ₗ[K] W).prodCongr (f₂ : P.orthogonal ≃ₗ[K] P.orthogonal) := by
    have hval := (congrArg Subtype.val hf).symm
    rwa [coe_orthogonalGroupProd] at hval
  have hf₂ : (f₂ : P.orthogonal ≃ₗ[K] P.orthogonal) = LinearEquiv.refl K P.orthogonal := by
    ext u
    have hu := congrArg
      (fun φ : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal ↦ (φ (0, u)).2) hcoe
    simpa [hfix' u] using hu.symm
  have hdet : LinearEquiv.det (f₁ : W ≃ₗ[K] W) = 1 := by
    have hdet' := det_coe_specialOrthogonalGroup h'
    rw [hcoe, LinearEquiv.det_prodCongr, hf₂, LinearEquiv.det_refl, mul_one] at hdet'
    exact hdet'
  have hblock1 :
      LinearMap.fst K W P.orthogonal ∘ₗ
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal).toLinearMap ∘ₗ
          LinearMap.inl K W P.orthogonal = (f₁ : W ≃ₗ[K] W).toLinearMap := by
    ext w
    simp [hcoe]
  have hprod : h' ∈ (specialOrthogonalGroupProd Q_W (Q_V.restrict P.orthogonal)).range := by
    refine (mem_range_specialOrthogonalGroupProd_iff Q_W (Q_V.restrict P.orthogonal)).mpr
      ⟨hinvariant, fun u ↦ by simp [hfix' u], ?_, by simp [hblock2]⟩
    rw [hblock1, ← LinearEquiv.coe_det, hdet, Units.val_one]
  obtain ⟨⟨g₁, g₂⟩, hg⟩ := hprod
  have hg₂ : g₂ = 1 := by
    ext u
    have hu := congrArg
      (fun φ : specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)) ↦
        ((φ : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u)).2) hg
    simpa [hfix' u] using hu
  exact ⟨g₁, by simpa [hg₂] using hg⟩

/-- **Image of the stabilizer embedding.** An element of `SO(Q_V)` lies in the image of
`P.stabilizerHom` if and only if it fixes `W^⊥` pointwise. -/
theorem mem_range_stabilizerHom_iff {h : specialOrthogonalGroup Q_V} :
    h ∈ P.stabilizerHom.range ↔ ∀ v ∈ P.orthogonal, (h : V ≃ₗ[K] V) v = v := by
  constructor
  · rintro ⟨g, rfl⟩ v hv
    exact P.stabilizerHom_apply_of_mem_orthogonal g hv
  · intro hfix
    have := P.finiteDimensional_orthogonal
    set e := P.ambientIsometryEquiv
    set h' : specialOrthogonalGroup (Q_W.prod (Q_V.restrict P.orthogonal)) :=
      e.symm.specialOrthogonalGroupCongr h
    have hinvariant :
        ∀ w : W, ((h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0)).2 = 0 := by
      intro w
      obtain ⟨w', hw'⟩ := P.mem_range_embed_of_fix_orthogonal hfix w
      have heq : (h : V ≃ₗ[K] V) (e (w, 0)) = e (w', 0) := by
        simpa [e] using hw'.symm
      have h'' : (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0) = (w', 0) := by
        simp only [h']
        rw [IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, IsometryEquiv.symm_symm,
          heq, e.symm_apply_apply]
      rw [h'']
    have hfix' : ∀ u : P.orthogonal,
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u) = (0, u) := by
      intro u
      have heq : (h : V ≃ₗ[K] V) (e (0, u)) = e (0, u) := by
        simpa [e] using hfix u u.property
      simp only [h']
      rw [IsometryEquiv.coe_specialOrthogonalGroupCongr_apply, IsometryEquiv.symm_symm,
        heq, e.symm_apply_apply]
    obtain ⟨g₁, hmain⟩ := P.exists_specialOrthogonalGroupProd_one_of_fix h' hinvariant hfix'
    refine ⟨g₁, ?_⟩
    have hcongr := congrArg e.specialOrthogonalGroupCongr hmain
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun φ : specialOrthogonalGroup Q_V ↦ (φ : V ≃ₗ[K] V) v) hcongr
    simpa [stabilizerHom, h', e, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply] using hv

end Stabilizer

end OrthogonalRelevantPair

namespace FramedOrthogonalRelevantPair

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}
  (F : FramedOrthogonalRelevantPair Q_W Q_V j)

/-- The stabilizer embedding `SO(Q_W) →* SO(Q_V)` of a framed relevant pair. -/
noncomputable abbrev stabilizerHom :
    specialOrthogonalGroup Q_W →* specialOrthogonalGroup Q_V :=
  F.toOrthogonalRelevantPair.stabilizerHom

@[simp]
theorem stabilizerHom_apply_lineVector (g : specialOrthogonalGroup Q_W) :
    (F.stabilizerHom g : V ≃ₗ[K] V) F.lineVector = F.lineVector :=
  F.toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g F.lineVector_mem_orthogonal

theorem stabilizerHom_apply_hyperbolicMap (g : specialOrthogonalGroup Q_W)
    (x : Fin j → Fin 2 → K) :
    (F.stabilizerHom g : V ≃ₗ[K] V) (F.hyperbolicMap x) = F.hyperbolicMap x :=
  F.toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g
    (F.hyperbolicMap_mem_orthogonal x)

end FramedOrthogonalRelevantPair

/-! ### Transport along isometries and intertwining of stabilizers -/

namespace OrthogonalRelevantPair

section Map

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V W' V' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  [AddCommGroup W'] [Module K W'] [AddCommGroup V'] [Module K V']
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V}
  {Q_W' : QuadraticForm K W'} {Q_V' : QuadraticForm K V'} {j : ℕ}

/-- Transport an orthogonal relevant pair along isometric equivalences of the domain and
codomain. -/
noncomputable def map (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    OrthogonalRelevantPair Q_W' Q_V' j where
  embed := e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)
  nondegenerate_domain := e_W.nondegenerate_iff.mp P.nondegenerate_domain
  exists_complement := by
    have hrange :
        LinearMap.range (e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)).toLinearMap =
          (LinearMap.range P.embed.toLinearMap).map e_V.toLinearMap := by
      ext v'
      simp only [QuadraticMap.Isometry.toLinearMap_comp, LinearMap.mem_range,
        LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
        Submodule.mem_map]
      refine ⟨fun ⟨w', hw'⟩ ↦ ?_, ?_⟩
      · exact ⟨P.embed (e_W.symm w'), ⟨e_W.symm w', rfl⟩, hw'⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨e_W w, by simp⟩
    have horth :
        P.orthogonal.map e_V.toLinearMap =
          LinearMap.BilinForm.orthogonal Q_V'.polarBilin
            (LinearMap.range
              (e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)).toLinearMap) := by
      rw [hrange]
      exact e_V.map_orthogonal_polarBilin (LinearMap.range P.embed.toLinearMap)
    have hsub : (Q_V.restrict P.orthogonal).IsometryEquiv
        (Q_V'.restrict
          (LinearMap.BilinForm.orthogonal Q_V'.polarBilin
            (LinearMap.range
              (e_V.toIsometry.comp (P.embed.comp e_W.symm.toIsometry)).toLinearMap))) :=
      { toLinearEquiv := e_V.toLinearEquiv.ofSubmodules _ _ horth
        map_app' u := by
          -- Expose the restricted form evaluation on the submodule isomorphism.
          change Q_V' (e_V.toLinearEquiv.ofSubmodules _ _ horth u : V') = Q_V (u : V)
          rw [LinearEquiv.ofSubmodules_apply]
          exact e_V.map_app (u : V) }
    obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
    exact ⟨c, ⟨hsub.symm.trans e⟩⟩

@[simp]
theorem map_embed (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (P.map e_W e_V).embed w' = e_V (P.embed (e_W.symm w')) :=
  (rfl)

@[simp]
theorem map_refl (P : OrthogonalRelevantPair Q_W Q_V j) :
    P.map (IsometryEquiv.refl Q_W) (IsometryEquiv.refl Q_V) = P := by
  ext w
  rfl

theorem map_trans {W'' V'' : Type*} [AddCommGroup W''] [Module K W'']
    [AddCommGroup V''] [Module K V''] {Q_W'' : QuadraticForm K W''}
    {Q_V'' : QuadraticForm K V''} (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (e_W' : Q_W'.IsometryEquiv Q_W'') (e_V' : Q_V'.IsometryEquiv Q_V'') :
    (P.map e_W e_V).map e_W' e_V' = P.map (e_W.trans e_W') (e_V.trans e_V') := by
  ext w''
  simp only [map_embed]
  have hsymm : (e_W.trans e_W').symm w'' = e_W.symm (e_W'.symm w'') :=
    (e_W.trans e_W').symm_apply_eq.mpr (by simp)
  rw [hsymm]
  rfl

theorem mem_map_orthogonal_iff (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') {v' : V'} :
    v' ∈ (P.map e_W e_V).orthogonal ↔ e_V.symm v' ∈ P.orthogonal := by
  simp only [mem_orthogonal_iff, map_embed]
  refine ⟨fun h w ↦ ?_, fun h w' ↦ ?_⟩
  · have hw := h (e_W w)
    rw [e_W.symm_apply_apply] at hw
    rw [← e_V.polar_apply, e_V.apply_symm_apply]
    exact hw
  · conv_lhs => rw [← e_V.apply_symm_apply v']
    rw [e_V.polar_apply]
    exact h (e_W.symm w')

/-- **Intertwining of stabilizer embeddings.** Any pair of isometric equivalences `(e_W, e_V)`
intertwining the embeddings of two relevant pairs `P` and `P'` intertwines their stabilizer
embeddings `SO(Q_W) →* SO(Q_V)` and `SO(Q_W') →* SO(Q_V')`. -/
theorem stabilizerHom_specialOrthogonalGroupCongr [FiniteDimensional K W] [FiniteDimensional K W']
    {j' : ℕ} (P : OrthogonalRelevantPair Q_W Q_V j)
    (P' : OrthogonalRelevantPair Q_W' Q_V' j')
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (hcomm : e_V.toIsometry.comp P.embed = P'.embed.comp e_W.toIsometry)
    (g : specialOrthogonalGroup Q_W) :
    e_V.specialOrthogonalGroupCongr (P.stabilizerHom g) =
      P'.stabilizerHom (e_W.specialOrthogonalGroupCongr g) := by
  have himg (w : W) : e_V (P.embed w) = P'.embed (e_W w) :=
    DFunLike.congr_fun hcomm w
  have horth {v' : V'} (hv' : v' ∈ P'.orthogonal) : e_V.symm v' ∈ P.orthogonal := by
    rw [mem_orthogonal_iff]
    intro w
    rw [← e_V.polar_apply, e_V.apply_symm_apply, himg w]
    exact P'.mem_orthogonal_iff.mp hv' (e_W w)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v'
  -- Verify equality on the complementary decomposition `range P'.embed ⊕ P'.orthogonal`.
  obtain ⟨⟨w', u'⟩, rfl⟩ := P'.ambientIsometryEquiv.toLinearEquiv.surjective v'
  rw [QuadraticMap.IsometryEquiv.coe_toLinearEquiv, P'.ambientIsometryEquiv_apply]
  simp only [map_add, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]
  rw [P'.stabilizerHom_apply_embed, P'.stabilizerHom_apply_of_mem_orthogonal _ u'.property]
  congr 1
  · have hsymm : e_V.symm (P'.embed w') = P.embed (e_W.symm w') :=
      e_V.symm_apply_eq.mpr (by simpa using (himg (e_W.symm w')).symm)
    rw [hsymm, P.stabilizerHom_apply_embed, himg,
      IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]
  · rw [P.stabilizerHom_apply_of_mem_orthogonal g (horth u'.property), e_V.apply_symm_apply]

/-- Transporting a relevant pair along `(e_W, e_V)` intertwines the stabilizer embeddings. -/
theorem stabilizerHom_map [FiniteDimensional K W] [FiniteDimensional K W']
    (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (g : specialOrthogonalGroup Q_W) :
    (P.map e_W e_V).stabilizerHom (e_W.specialOrthogonalGroupCongr g) =
      e_V.specialOrthogonalGroupCongr (P.stabilizerHom g) := by
  refine (stabilizerHom_specialOrthogonalGroupCongr P (P.map e_W e_V) e_W e_V ?_ g).symm
  ext w
  simp

end Map

end OrthogonalRelevantPair

namespace FramedOrthogonalRelevantPair

section Map

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V W' V' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  [AddCommGroup W'] [Module K W'] [AddCommGroup V'] [Module K V']
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V}
  {Q_W' : QuadraticForm K W'} {Q_V' : QuadraticForm K V'} {j : ℕ}

private theorem map_orthogonal_eq (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range F.embed.toLinearMap)).map
        e_V.toLinearMap =
      LinearMap.BilinForm.orthogonal Q_V'.polarBilin
        (LinearMap.range
          (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap) := by
  have hrange :
      LinearMap.range (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap =
        (LinearMap.range F.embed.toLinearMap).map e_V.toLinearMap := by
    ext v'
    simp only [QuadraticMap.Isometry.toLinearMap_comp, LinearMap.mem_range,
      LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
      Submodule.mem_map]
    refine ⟨fun ⟨w', hw'⟩ ↦ ⟨F.embed (e_W.symm w'), ⟨e_W.symm w', rfl⟩, hw'⟩, ?_⟩
    rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨e_W w, by simp⟩
  rw [hrange]
  exact e_V.map_orthogonal_polarBilin (LinearMap.range F.embed.toLinearMap)

private noncomputable def mapSubmoduleEquiv (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (Q_V.restrict
        (LinearMap.BilinForm.orthogonal Q_V.polarBilin
          (LinearMap.range F.embed.toLinearMap))).IsometryEquiv
      (Q_V'.restrict
        (LinearMap.BilinForm.orthogonal Q_V'.polarBilin
          (LinearMap.range
            (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap))) where
  toFun u := ⟨e_V u, by
    rw [← map_orthogonal_eq F e_W e_V]
    exact Submodule.mem_map_of_mem u.property⟩
  invFun u' := ⟨e_V.symm u', by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨w, rfl⟩
    have hu' := LinearMap.BilinForm.mem_orthogonal_iff.mp u'.property
      ((e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)) (e_W w)) ⟨e_W w, rfl⟩
    rw [QuadraticMap.polarBilin_apply_apply, ← e_V.polar_apply, e_V.apply_symm_apply]
    simpa [QuadraticMap.polarBilin_apply_apply] using hu'⟩
  left_inv _ := Subtype.ext (e_V.symm_apply_apply _)
  right_inv _ := Subtype.ext (e_V.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (e_V.map_add _ _)
  map_smul' _ _ := Subtype.ext (e_V.map_smul _ _)
  map_app' u := e_V.map_app (u : V)

/-- Transport a framed orthogonal relevant pair along isometric equivalences `(e_W, e_V)`. -/
noncomputable def map (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    FramedOrthogonalRelevantPair Q_W' Q_V' j where
  embed := e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)
  nondegenerate_domain := e_W.nondegenerate_iff.mp F.nondegenerate_domain
  lineCoeff := F.lineCoeff
  complementEquiv := (mapSubmoduleEquiv F e_W e_V).symm.trans F.complementEquiv

@[simp]
theorem map_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.map e_W e_V := by
  ext w'
  simp
  rfl

@[simp]
theorem map_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (F.map e_W e_V).embed w' = e_V (F.embed (e_W.symm w')) :=
  (rfl)

@[simp]
theorem map_lineCoeff (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).lineCoeff = F.lineCoeff :=
  (rfl)

@[simp]
theorem map_complementEquiv_symm (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (y : (Fin j → Fin 2 → K) × K) :
    ((F.map e_W e_V).complementEquiv.symm y : V') = e_V (F.complementEquiv.symm y : V) := by
  set u : LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range F.embed.toLinearMap) :=
    F.complementEquiv.symm y
  have hu : e_V (u : V) ∈ LinearMap.BilinForm.orthogonal Q_V'.polarBilin
      (LinearMap.range (e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)).toLinearMap) := by
    rw [← map_orthogonal_eq F e_W e_V]
    exact Submodule.mem_map_of_mem u.property
  have hinv : (mapSubmoduleEquiv F e_W e_V).symm ⟨e_V (u : V), hu⟩ = u :=
    Subtype.ext (e_V.symm_apply_apply (u : V))
  have hsub_u : (F.map e_W e_V).complementEquiv ⟨e_V (u : V), hu⟩ = y :=
    (congrArg F.complementEquiv hinv).trans (F.complementEquiv.apply_symm_apply y)
  exact congrArg Subtype.val ((F.map e_W e_V).complementEquiv.symm_apply_eq.mpr hsub_u.symm)

@[simp]
theorem map_lineVector (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).lineVector = e_V F.lineVector := by
  rw [(F.map e_W e_V).lineVector_eq, F.lineVector_eq]
  exact F.map_complementEquiv_symm e_W e_V (0, 1)

@[simp]
theorem map_refl (F : FramedOrthogonalRelevantPair Q_W Q_V j) :
    F.map (IsometryEquiv.refl Q_W) (IsometryEquiv.refl Q_V) = F := by
  ext y
  · rfl
  · simp

theorem map_trans {W'' V'' : Type*} [AddCommGroup W''] [Module K W'']
    [AddCommGroup V''] [Module K V''] {Q_W'' : QuadraticForm K W''}
    {Q_V'' : QuadraticForm K V''} (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (e_W' : Q_W'.IsometryEquiv Q_W'') (e_V' : Q_V'.IsometryEquiv Q_V'') :
    (F.map e_W e_V).map e_W' e_V' = F.map (e_W.trans e_W') (e_V.trans e_V') := by
  ext y
  · simp only [map_embed]
    have hsymm : (e_W.trans e_W').symm y = e_W.symm (e_W'.symm y) :=
      (e_W.trans e_W').symm_apply_eq.mpr (by simp)
    rw [hsymm]
    rfl
  · simp

end Map

end FramedOrthogonalRelevantPair

end TauCeti
