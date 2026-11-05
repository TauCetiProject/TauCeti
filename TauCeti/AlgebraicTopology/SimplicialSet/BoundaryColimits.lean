/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The boundary of a standard simplex as a colimit

The boundary `∂Δ[n + 1]` is the union of the `n + 2` faces of codimension one of `Δ[n + 1]`,
glued along their faces of codimension two. Consequently a map `∂Δ[n + 1] ⟶ X` is the same as a
family of `n + 2` maps `Δ[n] ⟶ X`, its faces, which agree on the common faces: the face of `j`
opposite to its vertex `k - 1` is the face of `k` opposite to its vertex `j`, for `j < k`.
This is the analogue for boundaries of Mathlib's description of horns in
`Mathlib.AlgebraicTopology.SimplicialSet.HornColimits`, and the proofs follow it.

## Main definitions and results

* `SSet.boundary.multicoequalizerDiagram`: `∂Δ[n]` is the multicoequalizer of its faces of
  codimension one along the faces of codimension two.
* `SSet.boundary.IsCompatible`: the compatibility condition on a family of faces.
* `SSet.boundary.IsCompatible.desc`: the map `∂Δ[n + 1] ⟶ X` glued from a compatible family of
  faces, characterised by `SSet.boundary.IsCompatible.ι_desc`.
* `SSet.boundary.IsCompatible.of_hom`: the faces of a map `∂Δ[n + 1] ⟶ X` are compatible.
* `SSet.boundary.eq_ι_comp_iff`: a map `∂Δ[n + 1] ⟶ X` is the restriction of a simplex `σ`
  exactly when its faces are the faces of `σ`.
-/

public section

universe u

namespace SSet

open CategoryTheory Limits Simplicial

namespace boundary

variable {n : ℕ}

/-- The multicoequalizer diagram which expresses `∂Δ[n]` as the gluing of all faces of
codimension one of the standard simplex along the faces of codimension two. -/
lemma multicoequalizerDiagram (n : ℕ) :
    Subcomplex.MulticoequalizerDiagram (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex)
      (ι := Fin (n + 1)) (fun j ↦ stdSimplex.face {j}ᶜ)
      (fun j k ↦ stdSimplex.face {j, k}ᶜ) where
  iSup_eq := by rw [boundary_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- The boundary is a multicoequalizer of the faces of codimension one of the standard simplex
along the faces of codimension two. -/
noncomputable def isColimit (n : ℕ) :
    IsColimit ((multicoequalizerDiagram.{u} n).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram n).isColimit'

variable {X : SSet.{u}}

/-- A family of maps `Δ[n] ⟶ X` indexed by `Fin (n + 2)` is compatible when it consists of the
faces of a map `∂Δ[n + 1] ⟶ X`: for `j < k`, the face of `f j` opposite to the vertex `k - 1`
agrees with the face of `f k` opposite to the vertex `j`. There is no condition for `n = 0`. -/
protected def IsCompatible (f : Fin (n + 2) → (Δ[n] ⟶ X)) : Prop :=
  match n with
  | 0 => True
  | n + 1 => ∀ (j k : Fin (n + 3)) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
        stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k

@[simp]
lemma isCompatible_zero_iff_true (f : Fin 2 → (Δ[0] ⟶ X)) :
    boundary.IsCompatible f ↔ True := Iff.rfl

@[simp]
lemma isCompatible_iff (f : Fin (n + 3) → (Δ[n + 1] ⟶ X)) :
    boundary.IsCompatible f ↔ ∀ (j k : Fin (n + 3)) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
        stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k := Iff.rfl

namespace IsCompatible

/-- The faces of a map out of the boundary are compatible. -/
lemma of_hom (g : (∂Δ[n + 1] : SSet) ⟶ X) :
    boundary.IsCompatible (fun j ↦ ι j ≫ g) := by
  obtain _ | n := n
  · simp
  · rw [isCompatible_iff]
    intro j k hjk
    simp only [← Category.assoc]
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Category.assoc, ι_ι, ι_ι,
      Fin.pred_succ, Fin.castPred_castSucc, stdSimplex.δ_comp_δ (by grind)]

variable {f : Fin (n + 2) → (Δ[n] ⟶ X)}

lemma δ_pred_comp {f : Fin (n + 3) → (Δ[n + 1] ⟶ X)} (hf : boundary.IsCompatible f)
    (j k : Fin (n + 3)) (hjk : j < k := by grind) :
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k :=
  hf j k hjk

/-- Auxiliary definition for `SSet.boundary.IsCompatible.desc`. -/
private noncomputable def multicofork (hf : boundary.IsCompatible f) :
    Multicofork ((multicoequalizerDiagram.{u} (n + 1)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun j ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ f j) (by
    rintro ⟨⟨a, b⟩, hab : a < b⟩
    -- The legs of the multispan diagram are inclusions of faces; `change` exposes them, since the
    -- diagram is indexed by the subtype of pairs `a < b`, which `rw` cannot see through.
    change Subcomplex.homOfLE (show stdSimplex.face {a, b}ᶜ ≤ stdSimplex.face {a}ᶜ by
          simp [stdSimplex.face_le_face_iff]) ≫ (stdSimplex.faceSingletonComplIso a).inv ≫ f a =
      Subcomplex.homOfLE (show stdSimplex.face {a, b}ᶜ ≤ stdSimplex.face {b}ᶜ by
          simp [stdSimplex.face_le_face_iff]) ≫ (stdSimplex.faceSingletonComplIso b).inv ≫ f b
    obtain _ | n := n
    · -- For `n = 0`, the two faces of `∂Δ[1]` meet in the empty face.
      ext ⟨⟨m⟩⟩ ⟨x, hx⟩
      have := (stdSimplex.mem_face_iff _ _).1 hx 0
      revert this hab
      generalize x 0 = c
      fin_cases a <;> fin_cases b <;> fin_cases c <;> simp
    · rw [stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc _ _
          hab, stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc
          _ _ hab, hf.δ_pred_comp a b hab])

lemma exists_desc (hf : boundary.IsCompatible f) :
    ∃ (φ : (∂Δ[n + 1] : SSet) ⟶ X), ∀ (j : Fin (n + 2)), ι j ≫ φ = f j := by
  let φ : (∂Δ[n + 1] : SSet) ⟶ X := (isColimit.{u} (n + 1)).desc hf.multicofork
  have h (j : Fin (n + 2)) :
      boundary.faceι j ≫ φ = (stdSimplex.faceSingletonComplIso j).inv ≫ f j :=
    (isColimit.{u} (n + 1)).fac hf.multicofork (.right j)
  refine ⟨φ, fun j ↦ ?_⟩
  have hj := h j
  rw [← faceSingletonComplIso_inv_ι, Category.assoc] at hj
  have := (stdSimplex.faceSingletonComplIso j).hom ≫= hj
  rwa [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc] at this

/-- The map `∂Δ[n + 1] ⟶ X` glued from a compatible family of faces `Δ[n] ⟶ X`. -/
noncomputable def desc (hf : boundary.IsCompatible f) : (∂Δ[n + 1] : SSet) ⟶ X :=
  hf.exists_desc.choose

@[reassoc (attr := simp)]
lemma ι_desc (hf : boundary.IsCompatible f) (j : Fin (n + 2)) :
    ι j ≫ hf.desc = f j :=
  hf.exists_desc.choose_spec j

end IsCompatible

/-- A map `σ₀ : ∂Δ[n + 1] ⟶ X` is the restriction of `σ : Δ[n + 1] ⟶ X` exactly when every face
of the simplex `σ` is the corresponding face of `σ₀`. -/
lemma eq_ι_comp_iff (σ₀ : (∂Δ[n + 1] : SSet) ⟶ X) (σ : Δ[n + 1] ⟶ X) :
    σ₀ = ∂Δ[n + 1].ι ≫ σ ↔ ∀ j, yonedaEquiv (ι j ≫ σ₀) = X.δ j (yonedaEquiv σ) := by
  refine ⟨?_, fun h ↦ hom_ext fun j ↦ yonedaEquiv.injective ?_⟩
  · rintro rfl j
    rw [ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp]
  · rw [ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp, h]

end boundary

end SSet
