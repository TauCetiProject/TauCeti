/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Basic

/-!
# Isometry transport for orthogonal relevant pairs

Transporting unframed and framed orthogonal relevant pairs along isometric equivalences `(e_W, e_V)`
of the domain and codomain quadratic spaces, together with identity/composition functoriality and
the induced maps on orthogonal complements, inverse framings, and distinguished line vectors.

## Main definitions

* `TauCeti.OrthogonalRelevantPair.map`, `TauCeti.FramedOrthogonalRelevantPair.map`: transport of
  relevant pairs along isometric equivalences `(e_W, e_V)`.

## Main results

* `TauCeti.OrthogonalRelevantPair.map_refl`, `TauCeti.OrthogonalRelevantPair.map_trans`,
  `TauCeti.FramedOrthogonalRelevantPair.map_refl`, `TauCeti.FramedOrthogonalRelevantPair.map_trans`:
  identity and composition laws for transport.
* `TauCeti.OrthogonalRelevantPair.orthogonal_map`: transporting a relevant pair carries `W^⊥` to
  the transported orthogonal complement via `e_V`.
* `TauCeti.FramedOrthogonalRelevantPair.map_complementEquiv_symm_apply`,
  `TauCeti.FramedOrthogonalRelevantPair.map_lineVector`: transport applies `e_V` to the original
  ambient vectors of the inverse framing and distinguished line generator.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

namespace TauCeti

/-! ### Transport of unframed relevant pairs -/

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

/-- Evaluating the transported embedding on `w'` applies `e_V ∘ P.embed ∘ e_W.symm`. -/
@[simp]
theorem map_embed_apply (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (P.map e_W e_V).embed w' = e_V (P.embed (e_W.symm w')) :=
  (rfl)

/-- Transporting an orthogonal relevant pair along identity equivalences leaves it unchanged. -/
@[simp]
theorem map_refl (P : OrthogonalRelevantPair Q_W Q_V j) :
    P.map (IsometryEquiv.refl Q_W) (IsometryEquiv.refl Q_V) = P := by
  ext w
  have hsymm : (IsometryEquiv.refl Q_W).symm w = w :=
    (IsometryEquiv.refl Q_W).symm_apply_eq.mpr rfl
  simp [hsymm]

/-- Transporting an orthogonal relevant pair is functorial under composition of equivalences. -/
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

/-- A vector lies in the orthogonal complement of `P.map e_W e_V` if and only if its preimage
under `e_V` lies in `P.orthogonal`. -/
theorem mem_map_orthogonal_iff (P : OrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') {v' : V'} :
    v' ∈ (P.map e_W e_V).orthogonal ↔ e_V.symm v' ∈ P.orthogonal := by
  simp [P.orthogonal_map e_W e_V]

end Map

end OrthogonalRelevantPair

/-! ### Transport of framed relevant pairs -/

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

/-- Evaluating the transported embedding of a framed pair on `w'` applies
`e_V ∘ F.embed ∘ e_W.symm`. -/
@[simp]
theorem map_embed_apply (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') (w' : W') :
    (F.map e_W e_V).embed w' = e_V (F.embed (e_W.symm w')) :=
  (rfl)

/-- Forgetting the framing commutes with transport along `(e_W, e_V)`. -/
@[simp]
theorem map_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.map e_W e_V := by
  ext w'
  simp

/-- Transport preserves the distinguished line coefficient `lineCoeff`. -/
@[simp]
theorem map_lineCoeff (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).lineCoeff = F.lineCoeff :=
  (rfl)

/-- Transporting a framed pair applies the codomain isometry `e_V` to the ambient vector
produced by the inverse framing `F.complementEquiv.symm`. -/
@[simp]
theorem map_complementEquiv_symm_apply (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V')
    (y : (Fin j → Fin 2 → K) × K) :
    ((F.map e_W e_V).complementEquiv.symm y : V') = e_V (F.complementEquiv.symm y : V) := by
  let eSub := e_V.orthogonalRangeCompEquiv F.embed e_W
  have hu : (eSub.symm.trans F.complementEquiv) (eSub (F.complementEquiv.symm y)) = y := by
    rw [IsometryEquiv.trans_apply, eSub.symm_apply_apply, F.complementEquiv.apply_symm_apply]
  have hsymm := congrArg Subtype.val ((F.map e_W e_V).complementEquiv.symm_apply_eq.mpr hu.symm)
  exact hsymm.trans (e_V.coe_orthogonalRangeCompEquiv_apply F.embed e_W _)

/-- Transporting a framed pair applies the codomain isometry `e_V` to the distinguished line
vector `F.lineVector`. -/
@[simp]
theorem map_lineVector (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (e_W : Q_W.IsometryEquiv Q_W') (e_V : Q_V.IsometryEquiv Q_V') :
    (F.map e_W e_V).lineVector = e_V F.lineVector := by
  rw [(F.map e_W e_V).lineVector_eq, F.lineVector_eq]
  exact F.map_complementEquiv_symm_apply e_W e_V (0, 1)

/-- Transporting a framed orthogonal relevant pair along identity equivalences leaves it
unchanged. -/
@[simp]
theorem map_refl (F : FramedOrthogonalRelevantPair Q_W Q_V j) :
    F.map (IsometryEquiv.refl Q_W) (IsometryEquiv.refl Q_V) = F := by
  ext y
  · have hsymm : (IsometryEquiv.refl Q_W).symm y = y :=
      (IsometryEquiv.refl Q_W).symm_apply_eq.mpr rfl
    simp [hsymm]
  · simp

/-- Transporting a framed orthogonal relevant pair is functorial under composition of
equivalences. -/
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
