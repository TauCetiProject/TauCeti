/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Map
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Basic

/-!
# Stabilizer embeddings and intertwining for orthogonal relevant pairs

Given an orthogonal relevant pair `P : OrthogonalRelevantPair Q_W Q_V j` with finite-dimensional
domain `W`, the orthogonal decomposition `V ≃qᵢ W ⊥ W^⊥` induces an injective group
homomorphism `SO(Q_W) →* SO(Q_V)` acting trivially on `W^⊥`. Transporting relevant pairs along
isometric equivalences (defined in `TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Map`)
intertwines these stabilizer embeddings.

## Main definitions

* `TauCeti.OrthogonalRelevantPair.stabilizerHom`: the stabilizer embedding `SO(Q_W) →* SO(Q_V)`
  acting as the identity on `W^⊥`.
* `TauCeti.FramedOrthogonalRelevantPair.stabilizerHom`: the stabilizer embedding of a framed
  relevant pair.

## Main results

* `TauCeti.OrthogonalRelevantPair.stabilizerHom_injective`,
  `TauCeti.OrthogonalRelevantPair.mem_range_stabilizerHom_iff`: `stabilizerHom` is injective, with
  image the subgroup of `SO(Q_V)` fixing `W^⊥` pointwise.
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

/-- On the embedded subspace `range P.embed`, `P.stabilizerHom g` acts via `g`. -/
@[simp]
theorem stabilizerHom_apply_embed (g : specialOrthogonalGroup Q_W) (w : W) :
    (P.stabilizerHom g : V ≃ₗ[K] V) (P.embed w) = P.embed ((g : W ≃ₗ[K] W) w) := by
  have := P.finiteDimensional_orthogonal
  simp [stabilizerHom, IsometryEquiv.coe_specialOrthogonalGroupCongr_apply]

/-- On the orthogonal complement `W^⊥`, `P.stabilizerHom g` acts as the identity. -/
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
      QuadraticMap.exists_specialOrthogonalGroupProd_one_of_preserves_inl_of_fixes_inr
        Q_W (Q_V.restrict P.orthogonal) h' hinvariant hfix'
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

/-- The stabilizer embedding fixes the distinguished line vector `F.lineVector`. -/
@[simp]
theorem stabilizerHom_apply_lineVector (g : specialOrthogonalGroup Q_W) :
    (F.stabilizerHom g : V ≃ₗ[K] V) F.lineVector = F.lineVector :=
  F.toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g F.lineVector_mem_orthogonal

/-- The stabilizer embedding fixes every vector in the framed hyperbolic summand. -/
@[simp]
theorem stabilizerHom_apply_hyperbolicMap (g : specialOrthogonalGroup Q_W)
    (x : Fin j → Fin 2 → K) :
    (F.stabilizerHom g : V ≃ₗ[K] V) (F.hyperbolicMap x) = F.hyperbolicMap x :=
  F.toOrthogonalRelevantPair.stabilizerHom_apply_of_mem_orthogonal g
    (F.hyperbolicMap_mem_orthogonal x)

end FramedOrthogonalRelevantPair

/-! ### Intertwining of stabilizer embeddings -/

namespace OrthogonalRelevantPair

section Intertwining

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V W' V' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
  [AddCommGroup W'] [Module K W'] [AddCommGroup V'] [Module K V']
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V}
  {Q_W' : QuadraticForm K W'} {Q_V' : QuadraticForm K V'} {j : ℕ}

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

end Intertwining

end OrthogonalRelevantPair

end TauCeti
