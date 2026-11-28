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
* `TauCeti.OrthogonalRelevantPair.orthogonal_map`,
  `TauCeti.OrthogonalRelevantPair.mapOrthogonalEquiv`: transporting a relevant pair carries `W^⊥`
  to the transported orthogonal complement.
* `TauCeti.OrthogonalRelevantPair.specialOrthogonalGroupCongr_stabilizerHom`: any intertwining pair
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
      e.specialOrthogonalGroupCongr.symm h
    have hinvariant :
        ∀ w : W, ((h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0)).2 = 0 := by
      intro w
      obtain ⟨w', hw'⟩ := P.mem_range_embed_of_fix_orthogonal hfix w
      have h'' : (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (w, 0) = (w', 0) := by
        simp [h', e, ← hw']
      rw [h'']
    have hfix' : ∀ u : P.orthogonal,
        (h' : (W × P.orthogonal) ≃ₗ[K] W × P.orthogonal) (0, u) = (0, u) := by
      intro u
      simp [h', e, hfix u u.property]
    obtain ⟨g₁, hmain⟩ :=
      QuadraticMap.exists_specialOrthogonalGroupProd_one_of_fix Q_W (Q_V.restrict P.orthogonal)
        h' hinvariant hfix'
    refine ⟨g₁, ?_⟩
    have hcongr := congrArg e.specialOrthogonalGroupCongr hmain
    simpa [stabilizerHom, h'] using hcongr

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
    obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
    exact ⟨c, ⟨(e_V.orthogonalRangeCompEquiv P.embed e_W).symm.trans e⟩⟩

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
  have hsymm : (e_W.trans e_W').symm w'' = e_W.symm (e_W'.symm w'') :=
    (e_W.trans e_W').symm_apply_eq.mpr (by simp)
  simp [hsymm, IsometryEquiv.trans_apply]

/-- Transporting a relevant pair maps its orthogonal complement by the codomain equivalence. -/
theorem orthogonal_map (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (P.map e_W e_V).orthogonal = P.orthogonal.map e_V.toLinearMap :=
  (P.embed.map_orthogonal_comp_isometryEquiv e_W e_V).symm

/-- The codomain equivalence restricts to an isometric equivalence between the orthogonal
complements of `P` and `P.map e_W e_V`. -/
noncomputable def mapOrthogonalEquiv (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (Q_V.restrict P.orthogonal).IsometryEquiv
      (Q_V'.restrict (P.map e_W e_V).orthogonal) :=
  e_V.ofSubmodules P.orthogonal (P.map e_W e_V).orthogonal (P.orthogonal_map e_W e_V).symm

@[simp]
theorem coe_mapOrthogonalEquiv_apply (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (u : P.orthogonal) :
    ((P.mapOrthogonalEquiv e_W e_V u : (P.map e_W e_V).orthogonal) : V') = e_V (u : V) :=
  e_V.coe_ofSubmodules_apply (P.orthogonal_map e_W e_V).symm u

@[simp]
theorem coe_mapOrthogonalEquiv_symm_apply (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (u : (P.map e_W e_V).orthogonal) :
    (((P.mapOrthogonalEquiv e_W e_V).symm u : P.orthogonal) : V) = e_V.symm (u : V') :=
  e_V.coe_ofSubmodules_symm_apply (P.orthogonal_map e_W e_V).symm u

theorem mem_map_orthogonal_iff (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') {v' : V'} :
    v' ∈ (P.map e_W e_V).orthogonal ↔ e_V.symm v' ∈ P.orthogonal := by
  simp [P.orthogonal_map e_W e_V]

/-- **Intertwining of stabilizer embeddings.** Any pair of isometric equivalences `(e_W, e_V)`
intertwining the embeddings of two relevant pairs `P` and `P'` intertwines their stabilizer
embeddings `SO(Q_W) →* SO(Q_V)` and `SO(Q_W') →* SO(Q_V')`. -/
theorem specialOrthogonalGroupCongr_stabilizerHom [FiniteDimensional K W] [FiniteDimensional K W']
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
  refine (specialOrthogonalGroupCongr_stabilizerHom P (P.map e_W e_V) e_W e_V ?_ g).symm
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

/-- Transport a framed orthogonal relevant pair along isometric equivalences `(e_W, e_V)`. -/
noncomputable def map (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    FramedOrthogonalRelevantPair Q_W' Q_V' j where
  embed := e_V.toIsometry.comp (F.embed.comp e_W.symm.toIsometry)
  nondegenerate_domain := e_W.nondegenerate_iff.mp F.nondegenerate_domain
  lineCoeff := F.lineCoeff
  complementEquiv := (e_V.orthogonalRangeCompEquiv F.embed e_W).symm.trans F.complementEquiv

@[simp]
theorem map_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (F.map e_W e_V).embed w' = e_V (F.embed (e_W.symm w')) :=
  (rfl)

@[simp]
theorem map_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.map e_W e_V := by
  ext w'
  simp

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
  let eSub := e_V.orthogonalRangeCompEquiv F.embed e_W
  have hu : (eSub.symm.trans F.complementEquiv) (eSub (F.complementEquiv.symm y)) = y := by
    rw [IsometryEquiv.trans_apply, eSub.symm_apply_apply, F.complementEquiv.apply_symm_apply]
  have hsymm := congrArg Subtype.val ((F.map e_W e_V).complementEquiv.symm_apply_eq.mpr hu.symm)
  exact hsymm.trans (e_V.coe_orthogonalRangeCompEquiv_apply F.embed e_W _)

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
  · have hsymm : (e_W.trans e_W').symm y = e_W.symm (e_W'.symm y) :=
      (e_W.trans e_W').symm_apply_eq.mpr (by simp)
    simp [hsymm, IsometryEquiv.trans_apply]
  · simp [IsometryEquiv.trans_apply]

end Map

end FramedOrthogonalRelevantPair

end TauCeti
