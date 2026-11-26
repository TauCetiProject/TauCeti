/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.FoamWithBoundary.Basic
import TauCeti.GroupTheory.Perm.Basic

/-!
# Isomorphisms, boundary transport, and empty unlabelled prefoam

This file defines structure-preserving isomorphisms between unlabelled prefoams (`IsoOver` over a
boundary web isomorphism and `Iso` fixing a boundary web), establishes their groupoid laws and
preservation of combinatorial invariants (`nextSide`, `sideCycle`, `sideWord`,
`numBoundaryComponents`, `facetEulerChar`, `IsNilvalent`), and constructs carrier relabelling
(`relabelOver`), boundary transport (`mapBoundary`), and the empty closed prefoam (`empty`).

## Main definitions

* `TauCeti.FoamWithBoundary.IsoOver`: prefoam isomorphism over `φ : W.Iso V`.
* `TauCeti.FoamWithBoundary.Iso`: boundary-fixing prefoam isomorphism over `W`.
* `TauCeti.FoamWithBoundary.relabelOver`, `relabelOverIso`: relabel carriers and transport the
  boundary along `φ : W.Iso V`.
* `TauCeti.FoamWithBoundary.mapBoundary`, `mapBoundaryIso`: transport a prefoam along a boundary
  web isomorphism `φ : W.Iso V`.
* `TauCeti.FoamWithBoundary.empty`: the empty closed prefoam.

## References

* H. Goertz, L. Marino, and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Definitions 2.1 and 3.1.
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of $\mathfrak{sl}_N$-foams*,
  arXiv:1702.04140v3, Definition 2.1 and Remark 2.2.
-/

public section

namespace TauCeti

universe u v w t

namespace FoamWithBoundary

private theorem cornerSideEquiv_comp (dir : Bool)
    {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool) (chirality₂ : Vertex₂ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (seamEnds₂ : (Vertex₂ × Fin 4) ⊕ W₂.Vertex ≃ Seam₂ × Bool)
    (h_inl₁ : ∀ v k,
      (seamEnds₁ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₁ v)).ends (k, 0)).2)
    (h_inr₁ : ∀ w, (seamEnds₁ (Sum.inr w)).2 = (W₁.ends (w, 0)).2)
    (h_inl₂ : ∀ v k,
      (seamEnds₂ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₂ v)).ends (k, 0)).2)
    (h_inr₂ : ∀ w, (seamEnds₂ (Sum.inr w)).2 = (W₂.ends (w, 0)).2)
    (h_chir : ∀ v, chirality₂ (eV v) = chirality₁ v)
    (h_seam : ∀ x,
      seamEnds₂ (Sum.map (Prod.map eV id) φ.vertex x) = Prod.map eS id (seamEnds₁ x))
    (c : (Vertex₁ × Fin 6) ⊕ (W₁.Vertex × Fin 3)) :
    cornerSideEquiv dir chirality₂ seamEnds₂ h_inl₂ h_inr₂
        (((eV.prodCongr (Equiv.refl (Fin 6))).sumCongr
          (φ.vertex.prodCongr (Equiv.refl (Fin 3)))) c) =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge)
        (cornerSideEquiv dir chirality₁ seamEnds₁ h_inl₁ h_inr₁ c) := by
  rcases c with ⟨v, e⟩ | ⟨w, i⟩
  · simp only [Equiv.sumCongr_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Sum.map_inl,
      Prod.map_apply, cornerSideEquiv_inl, h_chir v]
    set ki := (ClosedWeb.tetWeb (chirality₁ v)).ends.symm (e, dir)
    have hse := congrArg Prod.fst (h_seam (Sum.inl (v, ki.1)))
    simp only [Sum.map_inl, Prod.map_apply, Prod.map_fst, id_eq] at hse
    rw [hse]
  · simp only [Equiv.sumCongr_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Sum.map_inr,
      Prod.map_apply, cornerSideEquiv_inr, φ.map_ends_apply w i]
    have hse := congrArg Prod.fst (h_seam (Sum.inr w))
    simp only [Sum.map_inr, Prod.map_fst] at hse
    cases (W₁.ends (w, i)).2 == dir <;> simp [hse]

private theorem nextSidePerm_eq_permCongr
    {Vertex₁ Seam₁ : Type u} {W₁ : ClosedWeb.{u}}
    {Vertex₂ Seam₂ : Type v} {W₂ : ClosedWeb.{v}}
    (φ : W₁.Iso W₂) (eV : Vertex₁ ≃ Vertex₂) (eS : Seam₁ ≃ Seam₂)
    (chirality₁ : Vertex₁ → Bool) (chirality₂ : Vertex₂ → Bool)
    (seamEnds₁ : (Vertex₁ × Fin 4) ⊕ W₁.Vertex ≃ Seam₁ × Bool)
    (seamEnds₂ : (Vertex₂ × Fin 4) ⊕ W₂.Vertex ≃ Seam₂ × Bool)
    (h_inl₁ : ∀ v k,
      (seamEnds₁ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₁ v)).ends (k, 0)).2)
    (h_inr₁ : ∀ w, (seamEnds₁ (Sum.inr w)).2 = (W₁.ends (w, 0)).2)
    (h_inl₂ : ∀ v k,
      (seamEnds₂ (Sum.inl (v, k))).2 = !((ClosedWeb.tetWeb (chirality₂ v)).ends (k, 0)).2)
    (h_inr₂ : ∀ w, (seamEnds₂ (Sum.inr w)).2 = (W₂.ends (w, 0)).2)
    (h_chir : ∀ v, chirality₂ (eV v) = chirality₁ v)
    (h_seam : ∀ x,
      seamEnds₂ (Sum.map (Prod.map eV id) φ.vertex x) = Prod.map eS id (seamEnds₁ x)) :
    nextSidePerm chirality₂ seamEnds₂ h_inl₂ h_inr₂ =
      ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge).permCongr
        (nextSidePerm chirality₁ seamEnds₁ h_inl₁ h_inr₁) := by
  set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
  ext y
  obtain ⟨x, rfl⟩ := eSide.surjective y
  obtain ⟨c, rfl⟩ := (cornerSideEquiv true chirality₁ seamEnds₁ h_inl₁ h_inr₁).surjective x
  have hcs (dir : Bool) := cornerSideEquiv_comp dir φ eV eS chirality₁ chirality₂
    seamEnds₁ seamEnds₂ h_inl₁ h_inr₁ h_inl₂ h_inr₂ h_chir h_seam c
  rw [Equiv.permCongr_apply, eSide.symm_apply_apply, ← hcs true, nextSidePerm_apply,
    nextSidePerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hcs false]


/-! ### Isomorphisms, relabelling, boundary transport, and empty prefoam -/

/-- A combinatorial prefoam isomorphism from `F : FoamWithBoundary W` to `G : FoamWithBoundary V`
lying over a boundary web isomorphism `φ : W.Iso V`. -/
@[ext]
structure IsoOver {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (φ : W.Iso V)
    (F : FoamWithBoundary W) (G : FoamWithBoundary V) : Type (max u v) where
  /-- Bijection on interior singular vertices. -/
  vertex : F.Vertex ≃ G.Vertex
  /-- Bijection on interval seams. -/
  seam : F.Seam ≃ G.Seam
  /-- Bijection on circular seams. -/
  seamCircle : F.SeamCircle ≃ G.SeamCircle
  /-- Bijection on facets. -/
  facet : F.Facet ≃ G.Facet
  /-- Bijection on boundary components. -/
  boundary : F.Boundary ≃ G.Boundary
  /-- Preservation of vertex chiralities. -/
  map_chirality : ∀ v, G.chirality (vertex v) = F.chirality v
  /-- Compatibility with seam-end incidence and orientations. -/
  map_seamEnds : ∀ x,
    G.seamEnds (Sum.map (Prod.map vertex id) φ.vertex x) = Prod.map seam id (F.seamEnds x)
  /-- Preservation of facet genus. -/
  map_genus : ∀ f, G.genus (facet f) = F.genus f
  /-- Compatibility with the boundary-to-facet map. -/
  map_boundaryFacet : ∀ b, G.boundaryFacet (boundary b) = facet (F.boundaryFacet b)
  /-- Compatibility with segmented side boundary assignments. -/
  map_sideBoundary : ∀ x,
    G.sideBoundary (Sum.map (Prod.map seam id) φ.edge x) = boundary (F.sideBoundary x)
  /-- Compatibility with vertex-free circle side boundary assignments. -/
  map_circleBoundary : ∀ z,
    G.circleBoundary (Sum.map (Prod.map seamCircle id) φ.circle z) = boundary (F.circleBoundary z)

attribute [simp] IsoOver.map_chirality IsoOver.map_genus IsoOver.map_boundaryFacet

/-- A boundary-fixing isomorphism of prefoams over the same closed web `W`. -/
abbrev Iso {W : ClosedWeb.{u}} (F G : FoamWithBoundary W) : Type u :=
  F.IsoOver (ClosedWeb.Iso.refl W) G

namespace IsoOver

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} {U : ClosedWeb.{w}} {T : ClosedWeb.{t}}

section Cast

variable {φ₁ φ₂ φ₃ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}

/-- Reindex the underlying boundary web isomorphism along an equality. -/
def cast (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) : F.IsoOver φ₂ G := by subst h; exact ψ

@[simp] theorem cast_vertex (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).vertex = ψ.vertex := by subst h; rfl
@[simp] theorem cast_seam (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).seam = ψ.seam := by subst h; rfl
@[simp] theorem cast_seamCircle (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).seamCircle = ψ.seamCircle := by subst h; rfl
@[simp] theorem cast_facet (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).facet = ψ.facet := by subst h; rfl
@[simp] theorem cast_boundary (h : φ₁ = φ₂) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h).boundary = ψ.boundary := by subst h; rfl
@[simp] theorem cast_rfl (ψ : F.IsoOver φ₁ G) : ψ.cast rfl = ψ := (rfl)
@[simp] theorem cast_cast (h₁ : φ₁ = φ₂) (h₂ : φ₂ = φ₃) (ψ : F.IsoOver φ₁ G) :
    (ψ.cast h₁).cast h₂ = ψ.cast (h₁.trans h₂) := by subst h₁ h₂; rfl

end Cast

section InducedEquiv

variable {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V} (ψ : F.IsoOver φ G)

/-- Equivalence on segmented sides induced by `ψ : F.IsoOver φ G`. -/
def sideEquiv : F.Side ≃ G.Side :=
  (ψ.seam.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge

theorem sideEquiv_def :
    ψ.sideEquiv = (ψ.seam.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge := (rfl)

@[simp] theorem sideEquiv_inl (s : F.Seam) (i : Fin 3) :
    ψ.sideEquiv (Sum.inl (s, i)) = Sum.inl (ψ.seam s, i) := (rfl)
@[simp] theorem sideEquiv_inr (e : W.Edge) :
    ψ.sideEquiv (Sum.inr e) = Sum.inr (φ.edge e) := (rfl)
@[simp] theorem sideEquiv_symm_inl (s : G.Seam) (i : Fin 3) :
    ψ.sideEquiv.symm (Sum.inl (s, i)) = Sum.inl (ψ.seam.symm s, i) := (rfl)
@[simp] theorem sideEquiv_symm_inr (e : V.Edge) :
    ψ.sideEquiv.symm (Sum.inr e) = Sum.inr (φ.edge.symm e) := (rfl)

@[simp] theorem map_sideBoundary_sideEquiv (x : F.Side) :
    G.sideBoundary (ψ.sideEquiv x) = ψ.boundary (F.sideBoundary x) := by
  simpa [sideEquiv_def] using ψ.map_sideBoundary x

/-- Equivalence on circle sides induced by `ψ : F.IsoOver φ G`. -/
def circleSideEquiv : F.CircleSide ≃ G.CircleSide :=
  (ψ.seamCircle.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle

theorem circleSideEquiv_def :
    ψ.circleSideEquiv = (ψ.seamCircle.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle := (rfl)

@[simp] theorem circleSideEquiv_inl (c : F.SeamCircle) (i : Fin 3) :
    ψ.circleSideEquiv (Sum.inl (c, i)) = Sum.inl (ψ.seamCircle c, i) := (rfl)
@[simp] theorem circleSideEquiv_inr (c : W.Circle) :
    ψ.circleSideEquiv (Sum.inr c) = Sum.inr (φ.circle c) := (rfl)
@[simp] theorem circleSideEquiv_symm_inl (c : G.SeamCircle) (i : Fin 3) :
    ψ.circleSideEquiv.symm (Sum.inl (c, i)) = Sum.inl (ψ.seamCircle.symm c, i) := (rfl)
@[simp] theorem circleSideEquiv_symm_inr (c : V.Circle) :
    ψ.circleSideEquiv.symm (Sum.inr c) = Sum.inr (φ.circle.symm c) := (rfl)

@[simp] theorem map_circleBoundary_circleSideEquiv (z : F.CircleSide) :
    G.circleBoundary (ψ.circleSideEquiv z) = ψ.boundary (F.circleBoundary z) := by
  simpa [circleSideEquiv_def] using ψ.map_circleBoundary z

/-- Equivalence on corners induced by `ψ : F.IsoOver φ G`. -/
def cornerEquiv : F.Corner ≃ G.Corner :=
  (ψ.vertex.prodCongr (Equiv.refl (Fin 6))).sumCongr (φ.vertex.prodCongr (Equiv.refl (Fin 3)))

theorem cornerEquiv_def : ψ.cornerEquiv =
    (ψ.vertex.prodCongr (Equiv.refl (Fin 6))).sumCongr
      (φ.vertex.prodCongr (Equiv.refl (Fin 3))) := (rfl)

@[simp] theorem cornerEquiv_inl (v : F.Vertex) (e : Fin 6) :
    ψ.cornerEquiv (Sum.inl (v, e)) = Sum.inl (ψ.vertex v, e) := (rfl)
@[simp] theorem cornerEquiv_inr (w : W.Vertex) (i : Fin 3) :
    ψ.cornerEquiv (Sum.inr (w, i)) = Sum.inr (φ.vertex w, i) := (rfl)
@[simp] theorem cornerEquiv_symm_inl (v : G.Vertex) (e : Fin 6) :
    ψ.cornerEquiv.symm (Sum.inl (v, e)) = Sum.inl (ψ.vertex.symm v, e) := (rfl)
@[simp] theorem cornerEquiv_symm_inr (w : V.Vertex) (i : Fin 3) :
    ψ.cornerEquiv.symm (Sum.inr (w, i)) = Sum.inr (φ.vertex.symm w, i) := (rfl)

end InducedEquiv

/-- Identity isomorphism of `F` over `ClosedWeb.Iso.refl W`. -/
def refl (F : FoamWithBoundary W) : F.Iso F where
  vertex := Equiv.refl _
  seam := Equiv.refl _
  seamCircle := Equiv.refl _
  facet := Equiv.refl _
  boundary := Equiv.refl _
  map_chirality _ := rfl
  map_seamEnds x := by rcases x with ⟨v, k⟩ | w <;> simp
  map_genus _ := rfl
  map_boundaryFacet _ := rfl
  map_sideBoundary x := by rcases x with ⟨s, i⟩ | e <;> simp
  map_circleBoundary z := by rcases z with ⟨c, i⟩ | c <;> simp

@[simp] theorem refl_vertex (F : FoamWithBoundary W) : (refl F).vertex = Equiv.refl _ := (rfl)
@[simp] theorem refl_seam (F : FoamWithBoundary W) : (refl F).seam = Equiv.refl _ := (rfl)
@[simp] theorem refl_seamCircle (F : FoamWithBoundary W) :
    (refl F).seamCircle = Equiv.refl _ := (rfl)
@[simp] theorem refl_facet (F : FoamWithBoundary W) : (refl F).facet = Equiv.refl _ := (rfl)
@[simp] theorem refl_boundary (F : FoamWithBoundary W) : (refl F).boundary = Equiv.refl _ := (rfl)

/-- Inverse isomorphism over `φ.symm`. -/
def symm {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V}
    (ψ : F.IsoOver φ G) : G.IsoOver φ.symm F where
  vertex := ψ.vertex.symm
  seam := ψ.seam.symm
  seamCircle := ψ.seamCircle.symm
  facet := ψ.facet.symm
  boundary := ψ.boundary.symm
  map_chirality v := by
    have h := ψ.map_chirality (ψ.vertex.symm v)
    rw [ψ.vertex.apply_symm_apply] at h
    exact h.symm
  map_seamEnds y := by
    set x : (F.Vertex × Fin 4) ⊕ W.Vertex :=
      Sum.map (Prod.map ψ.vertex.symm id) φ.symm.vertex y
    have hxy : Sum.map (Prod.map ψ.vertex id) φ.vertex x = y := by
      rcases y with ⟨v, k⟩ | w <;> simp [x]
    have h := ψ.map_seamEnds x
    rw [hxy] at h
    rcases hp : F.seamEnds x with ⟨s, b⟩
    rw [hp] at h
    rw [h]
    simp
  map_genus f := by
    have h := ψ.map_genus (ψ.facet.symm f)
    rw [ψ.facet.apply_symm_apply] at h
    exact h.symm
  map_boundaryFacet b := ψ.facet.injective (by
    rw [ψ.facet.apply_symm_apply, ← ψ.map_boundaryFacet, ψ.boundary.apply_symm_apply])
  map_sideBoundary y := ψ.boundary.injective (by
    set x : F.Side := Sum.map (Prod.map ψ.seam.symm id) φ.symm.edge y
    have hxy : Sum.map (Prod.map ψ.seam id) φ.edge x = y := by
      rcases y with ⟨s, i⟩ | e <;> simp [x]
    rw [ψ.boundary.apply_symm_apply, ← ψ.map_sideBoundary x, hxy])
  map_circleBoundary z := ψ.boundary.injective (by
    set x : F.CircleSide := Sum.map (Prod.map ψ.seamCircle.symm id) φ.symm.circle z
    have hxz : Sum.map (Prod.map ψ.seamCircle id) φ.circle x = z := by
      rcases z with ⟨c, i⟩ | c <;> simp [x]
    rw [ψ.boundary.apply_symm_apply, ← ψ.map_circleBoundary x, hxz])

/-- Composition of prefoam isomorphisms over `φ₁.trans φ₂`. -/
def trans {φ₁ : W.Iso V} {φ₂ : V.Iso U}
    {F : FoamWithBoundary W} {G : FoamWithBoundary V} {H : FoamWithBoundary U}
    (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) : F.IsoOver (φ₁.trans φ₂) H where
  vertex := ψ₁.vertex.trans ψ₂.vertex
  seam := ψ₁.seam.trans ψ₂.seam
  seamCircle := ψ₁.seamCircle.trans ψ₂.seamCircle
  facet := ψ₁.facet.trans ψ₂.facet
  boundary := ψ₁.boundary.trans ψ₂.boundary
  map_chirality v := by simp
  map_seamEnds x := by
    have h := ψ₂.map_seamEnds (Sum.map (Prod.map ψ₁.vertex id) φ₁.vertex x)
    rw [ψ₁.map_seamEnds] at h
    rcases x with ⟨v, k⟩ | w <;> simpa [Prod.map] using h
  map_genus f := by simp
  map_boundaryFacet b := by simp
  map_sideBoundary x := by
    have h := ψ₂.map_sideBoundary (Sum.map (Prod.map ψ₁.seam id) φ₁.edge x)
    rw [ψ₁.map_sideBoundary] at h
    rcases x with ⟨s, i⟩ | e <;> simpa using h
  map_circleBoundary z := by
    have h := ψ₂.map_circleBoundary (Sum.map (Prod.map ψ₁.seamCircle id) φ₁.circle z)
    rw [ψ₁.map_circleBoundary] at h
    rcases z with ⟨c, i⟩ | c <;> simpa using h

section Groupoid

variable {φ : W.Iso V} {φ₁ : W.Iso V} {φ₂ : V.Iso U} {φ₃ : U.Iso T}
  {F : FoamWithBoundary W} {G : FoamWithBoundary V}
  {H : FoamWithBoundary U} {K : FoamWithBoundary T}

@[simp] theorem symm_vertex (ψ : F.IsoOver φ G) : ψ.symm.vertex = ψ.vertex.symm := (rfl)
@[simp] theorem symm_seam (ψ : F.IsoOver φ G) : ψ.symm.seam = ψ.seam.symm := (rfl)
@[simp] theorem symm_seamCircle (ψ : F.IsoOver φ G) :
    ψ.symm.seamCircle = ψ.seamCircle.symm := (rfl)
@[simp] theorem symm_facet (ψ : F.IsoOver φ G) : ψ.symm.facet = ψ.facet.symm := (rfl)
@[simp] theorem symm_boundary (ψ : F.IsoOver φ G) : ψ.symm.boundary = ψ.boundary.symm := (rfl)

@[simp] theorem trans_vertex (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).vertex = ψ₁.vertex.trans ψ₂.vertex := (rfl)
@[simp] theorem trans_seam (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).seam = ψ₁.seam.trans ψ₂.seam := (rfl)
@[simp] theorem trans_seamCircle (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).seamCircle = ψ₁.seamCircle.trans ψ₂.seamCircle := (rfl)
@[simp] theorem trans_facet (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).facet = ψ₁.facet.trans ψ₂.facet := (rfl)
@[simp] theorem trans_boundary (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).boundary = ψ₁.boundary.trans ψ₂.boundary := (rfl)

@[simp] theorem symm_symm (ψ : F.IsoOver φ G) : ψ.symm.symm.cast φ.symm_symm = ψ := by ext <;> simp
@[simp] theorem refl_symm (F : FoamWithBoundary W) :
    (refl F).symm.cast ClosedWeb.Iso.refl_symm = refl F := by ext <;> simp
@[simp] theorem symm_trans (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) :
    (ψ₁.trans ψ₂).symm.cast (ClosedWeb.Iso.symm_trans φ₁ φ₂) = ψ₂.symm.trans ψ₁.symm := by
  ext <;> simp
@[simp] theorem refl_trans (ψ : F.IsoOver φ G) :
    ((refl F).trans ψ).cast (ClosedWeb.Iso.refl_trans φ) = ψ := by ext <;> simp
@[simp] theorem trans_refl (ψ : F.IsoOver φ G) :
    (ψ.trans (refl G)).cast (ClosedWeb.Iso.trans_refl φ) = ψ := by ext <;> simp
@[simp] theorem symm_trans_self (ψ : F.IsoOver φ G) :
    (ψ.symm.trans ψ).cast (ClosedWeb.Iso.symm_trans_self φ) = refl G := by ext <;> simp
@[simp] theorem self_trans_symm (ψ : F.IsoOver φ G) :
    (ψ.trans ψ.symm).cast (ClosedWeb.Iso.self_trans_symm φ) = refl F := by ext <;> simp
theorem trans_assoc (ψ₁ : F.IsoOver φ₁ G) (ψ₂ : G.IsoOver φ₂ H) (ψ₃ : H.IsoOver φ₃ K) :
    ((ψ₁.trans ψ₂).trans ψ₃).cast (ClosedWeb.Iso.trans_assoc φ₁ φ₂ φ₃) =
      ψ₁.trans (ψ₂.trans ψ₃) := by ext <;> simp

end Groupoid

section Preservation

variable {φ : W.Iso V} {F : FoamWithBoundary W} {G : FoamWithBoundary V} (ψ : F.IsoOver φ G)

/-- Every isomorphism commutes with `cornerSide dir` (`cornerIncoming` and `cornerOutgoing`). -/
@[simp] theorem map_cornerSide (dir : Bool) (c : F.Corner) :
    G.cornerSide dir (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerSide dir c) := by
  rw [cornerSide_def, cornerSide_def]
  exact cornerSideEquiv_comp dir φ ψ.vertex ψ.seam F.chirality G.chirality F.seamEnds G.seamEnds
    F.seamEnds_inl_snd F.seamEnds_inr_snd G.seamEnds_inl_snd G.seamEnds_inr_snd
    ψ.map_chirality ψ.map_seamEnds c

/-- Every isomorphism commutes with `cornerIncoming`. -/
theorem map_cornerIncoming (c : F.Corner) :
    G.cornerIncoming (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerIncoming c) :=
  ψ.map_cornerSide true c

/-- Every isomorphism commutes with `cornerOutgoing`. -/
theorem map_cornerOutgoing (c : F.Corner) :
    G.cornerOutgoing (ψ.cornerEquiv c) = ψ.sideEquiv (F.cornerOutgoing c) :=
  ψ.map_cornerSide false c

theorem nextSide_eq_permCongr : G.nextSide = ψ.sideEquiv.permCongr F.nextSide := by
  rw [nextSide_def, nextSide_def]
  exact nextSidePerm_eq_permCongr φ ψ.vertex ψ.seam F.chirality G.chirality F.seamEnds G.seamEnds
    F.seamEnds_inl_snd F.seamEnds_inr_snd G.seamEnds_inl_snd G.seamEnds_inr_snd
    ψ.map_chirality ψ.map_seamEnds

/-- Every isomorphism intertwines `nextSide` via `sideEquiv`. -/
@[simp] theorem map_nextSide (x : F.Side) :
    G.nextSide (ψ.sideEquiv x) = ψ.sideEquiv (F.nextSide x) := by
  rw [ψ.nextSide_eq_permCongr, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Every isomorphism commutes with `signedSegment`, relabelling seams and boundary edges while
preserving orientation signs. -/
@[simp] theorem map_signedSegment (x : F.Side) :
    G.signedSegment (ψ.sideEquiv x) =
      Prod.map (Sum.map ψ.seam φ.edge) id (F.signedSegment x) := by
  rcases x with ⟨s, i⟩ | e <;> simp

/-- Every isomorphism transports cyclic side orbits via `sideEquiv`. -/
@[simp] theorem map_sideCycle (x : F.Side) :
    G.sideCycle (ψ.sideEquiv x) = (F.sideCycle x).map ψ.sideEquiv := by
  rw [sideCycle_def, sideCycle_def]
  exact Function.Semiconj.periodicOrbit_apply (fun y ↦ (ψ.map_nextSide y).symm)
    ψ.sideEquiv.injective x

/-- Every isomorphism transports signed cyclic boundary words by relabelling seams and boundary
edges while preserving orientation signs. -/
@[simp] theorem map_sideWord (x : F.Side) :
    G.sideWord (ψ.sideEquiv x) =
      (F.sideWord x).map (Prod.map (Sum.map ψ.seam φ.edge) id) := by
  rw [sideWord_def, sideWord_def, ψ.map_sideCycle]
  induction F.sideCycle x with
  | nil => rfl
  | cons a l _ =>
    simp only [Cycle.map_coe, List.map_map]
    congr 1
    exact List.map_congr_left fun y _ ↦ ψ.map_signedSegment y

/-- Equivalence of boundary component fibres over `f` and `ψ.facet f`. -/
def facetBoundaryEquiv (f : F.Facet) : F.FacetBoundary f ≃ G.FacetBoundary (ψ.facet f) :=
  Equiv.subtypeEquiv ψ.boundary fun b ↦ by rw [ψ.map_boundaryFacet, ψ.facet.apply_eq_iff_eq]

@[simp] theorem facetBoundaryEquiv_apply_coe (f : F.Facet) (b : F.FacetBoundary f) :
    (ψ.facetBoundaryEquiv f b).val = ψ.boundary b.val := (rfl)
@[simp] theorem facetBoundaryEquiv_symm_apply_coe
    (f : F.Facet) (b : G.FacetBoundary (ψ.facet f)) :
    ((ψ.facetBoundaryEquiv f).symm b).val = ψ.boundary.symm b.val := (rfl)

/-- Isomorphisms preserve the number of boundary components of each facet. -/
@[simp] theorem map_numBoundaryComponents (f : F.Facet) :
    G.numBoundaryComponents (ψ.facet f) = F.numBoundaryComponents f := by
  rw [numBoundaryComponents_def, numBoundaryComponents_def]
  exact (Nat.card_congr (ψ.facetBoundaryEquiv f)).symm

/-- Isomorphisms preserve the Euler characteristic of each facet. -/
@[simp] theorem map_facetEulerChar (f : F.Facet) :
    G.facetEulerChar (ψ.facet f) = F.facetEulerChar f := by
  simp only [facetEulerChar_def, ψ.map_genus, ψ.map_numBoundaryComponents]

/-- Isomorphisms preserve nilvalence. -/
theorem isNilvalent_congr (ψ : F.IsoOver φ G) : F.IsNilvalent ↔ G.IsNilvalent := by
  rw [isNilvalent_def, isNilvalent_def]
  exact and_congr ψ.vertex.isEmpty_congr
    (and_congr ψ.seam.isEmpty_congr ψ.seamCircle.isEmpty_congr)

end Preservation

end IsoOver

namespace Iso

variable {W : ClosedWeb.{u}} {F G H K : FoamWithBoundary W}

/-- Identity boundary-fixing isomorphism. -/
abbrev refl (F : FoamWithBoundary W) : F.Iso F := IsoOver.refl F

/-- Inverse of a boundary-fixing isomorphism. -/
def symm (ψ : F.Iso G) : G.Iso F :=
  IsoOver.cast ClosedWeb.Iso.refl_symm (IsoOver.symm ψ)

@[simp] theorem symm_vertex (ψ : F.Iso G) : (Iso.symm ψ).vertex = ψ.vertex.symm := by simp [symm]
@[simp] theorem symm_seam (ψ : F.Iso G) : (Iso.symm ψ).seam = ψ.seam.symm := by simp [symm]
@[simp] theorem symm_seamCircle (ψ : F.Iso G) :
    (Iso.symm ψ).seamCircle = ψ.seamCircle.symm := by simp [symm]
@[simp] theorem symm_facet (ψ : F.Iso G) : (Iso.symm ψ).facet = ψ.facet.symm := by simp [symm]
@[simp] theorem symm_boundary (ψ : F.Iso G) :
    (Iso.symm ψ).boundary = ψ.boundary.symm := by simp [symm]

/-- Composition of boundary-fixing isomorphisms. -/
def trans (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) : F.Iso H :=
  IsoOver.cast (ClosedWeb.Iso.refl_trans _) (IsoOver.trans ψ₁ ψ₂)

@[simp] theorem trans_vertex (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).vertex = ψ₁.vertex.trans ψ₂.vertex := by simp [trans]
@[simp] theorem trans_seam (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).seam = ψ₁.seam.trans ψ₂.seam := by simp [trans]
@[simp] theorem trans_seamCircle (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).seamCircle = ψ₁.seamCircle.trans ψ₂.seamCircle := by simp [trans]
@[simp] theorem trans_facet (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).facet = ψ₁.facet.trans ψ₂.facet := by simp [trans]
@[simp] theorem trans_boundary (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    (Iso.trans ψ₁ ψ₂).boundary = ψ₁.boundary.trans ψ₂.boundary := by simp [trans]

@[simp] theorem symm_symm (ψ : F.Iso G) : Iso.symm (Iso.symm ψ) = ψ := by ext <;> simp
@[simp] theorem refl_symm (F : FoamWithBoundary W) : Iso.symm (Iso.refl F) = Iso.refl F := by
  ext <;> simp
@[simp] theorem symm_trans (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) :
    Iso.symm (Iso.trans ψ₁ ψ₂) = Iso.trans (Iso.symm ψ₂) (Iso.symm ψ₁) := by ext <;> simp
@[simp] theorem refl_trans (ψ : F.Iso G) : Iso.trans (Iso.refl F) ψ = ψ := by ext <;> simp
@[simp] theorem trans_refl (ψ : F.Iso G) : Iso.trans ψ (Iso.refl G) = ψ := by ext <;> simp
@[simp] theorem symm_trans_self (ψ : F.Iso G) : Iso.trans (Iso.symm ψ) ψ = Iso.refl G := by
  ext <;> simp
@[simp] theorem self_trans_symm (ψ : F.Iso G) : Iso.trans ψ (Iso.symm ψ) = Iso.refl F := by
  ext <;> simp
theorem trans_assoc (ψ₁ : F.Iso G) (ψ₂ : G.Iso H) (ψ₃ : H.Iso K) :
    Iso.trans (Iso.trans ψ₁ ψ₂) ψ₃ = Iso.trans ψ₁ (Iso.trans ψ₂ ψ₃) := by ext <;> simp

end Iso

/-! ### Transport along boundary web isomorphisms and the empty prefoam -/

section Relabel

private theorem relabel_map_seamEnds {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (φ : W.Iso V) {Vertex' Seam' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam')
    (x : (F.Vertex × Fin 4) ⊕ W.Vertex) :
    ((((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans F.seamEnds).trans
      (eS.prodCongr (Equiv.refl Bool))) (Sum.map (Prod.map eV id) φ.vertex x) =
      Prod.map eS id (F.seamEnds x) := by
  rcases x with ⟨v, k⟩ | w <;> simp [Prod.map]

private theorem relabel_seamEnds_inl_snd {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (φ : W.Iso V) {Vertex' Seam' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (v : Vertex') (k : Fin 4) :
    (((((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans F.seamEnds).trans
      (eS.prodCongr (Equiv.refl Bool))) (Sum.inl (v, k))).2 =
      !((ClosedWeb.tetWeb ((F.chirality ∘ eV.symm) v)).ends (k, 0)).2 := by
  simp [F.seamEnds_inl_snd (eV.symm v) k]

private theorem relabel_seamEnds_inr_snd {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}
    (F : FoamWithBoundary W) (φ : W.Iso V) {Vertex' Seam' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (w : V.Vertex) :
    (((((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans F.seamEnds).trans
      (eS.prodCongr (Equiv.refl Bool))) (Sum.inr w)).2 = (V.ends (w, 0)).2 := by
  have hw := congrArg Prod.snd (φ.map_ends_apply (φ.vertex.symm w) 0)
  rw [φ.vertex.apply_symm_apply] at hw
  simpa [hw] using F.seamEnds_inr_snd (φ.vertex.symm w)

/-- Relabel all internal carrier types of `F` and transport its boundary along `φ : W.Iso V`. -/
abbrev relabelOver {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (F : FoamWithBoundary W) (φ : W.Iso V)
    {Vertex' Seam' SeamCircle' Facet' Boundary' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (eSC : F.SeamCircle ≃ SeamCircle')
    (eF : F.Facet ≃ Facet') (eB : F.Boundary ≃ Boundary') : FoamWithBoundary V where
  Vertex := Vertex'
  Seam := Seam'
  SeamCircle := SeamCircle'
  Facet := Facet'
  Boundary := Boundary'
  finite_vertex := Finite.of_equiv F.Vertex eV
  finite_seam := Finite.of_equiv F.Seam eS
  finite_seamCircle := Finite.of_equiv F.SeamCircle eSC
  finite_facet := Finite.of_equiv F.Facet eF
  finite_boundary := Finite.of_equiv F.Boundary eB
  chirality := F.chirality ∘ eV.symm
  seamEnds := (((eV.symm.prodCongr (Equiv.refl (Fin 4))).sumCongr φ.vertex.symm).trans
    F.seamEnds).trans (eS.prodCongr (Equiv.refl Bool))
  seamEnds_inl_snd := by exact relabel_seamEnds_inl_snd F φ eV eS
  seamEnds_inr_snd := by exact relabel_seamEnds_inr_snd F φ eV eS
  genus := F.genus ∘ eF.symm
  boundaryFacet := eF ∘ F.boundaryFacet ∘ eB.symm
  sideBoundary :=
    eB ∘ F.sideBoundary ∘ ((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge).symm
  circleBoundary :=
    eB ∘ F.circleBoundary ∘ ((eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle).symm
  sideBoundary_eq_iff x y := by
    have hnp := nextSidePerm_eq_permCongr φ eV eS F.chirality (F.chirality ∘ eV.symm) F.seamEnds _
      F.seamEnds_inl_snd F.seamEnds_inr_snd
      (relabel_seamEnds_inl_snd F φ eV eS) (relabel_seamEnds_inr_snd F φ eV eS)
      (fun v ↦ by simp) (relabel_map_seamEnds F φ eV eS)
    rw [hnp]
    set eSide := (eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge
    dsimp only [Function.comp_apply]
    rw [eB.apply_eq_iff_eq, F.sideBoundary_eq_iff, ← F.nextSide_def]
    exact (Equiv.Perm.sameCycle_permCongr_iff (σ := F.nextSide) eSide).symm
  circleBoundary_injective := eB.injective.comp
    (F.circleBoundary_injective.comp
      ((eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle).symm.injective)
  sideBoundary_ne_circleBoundary x z h :=
    F.sideBoundary_ne_circleBoundary _ _ (eB.injective h)
  boundary_surjective b := by
    rcases F.boundary_surjective (eB.symm b) with ⟨x, hx⟩ | ⟨z, hz⟩
    · refine Or.inl ⟨((eS.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.edge) x, ?_⟩
      simp only [Function.comp_apply, Equiv.symm_apply_apply, hx, eB.apply_symm_apply]
    · refine Or.inr ⟨((eSC.prodCongr (Equiv.refl (Fin 3))).sumCongr φ.circle) z, ?_⟩
      simp only [Function.comp_apply, Equiv.symm_apply_apply, hz, eB.apply_symm_apply]

/-- Canonical isomorphism from `F` to `F.relabelOver φ eV eS eSC eF eB` over `φ`. -/
def relabelOverIso {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (F : FoamWithBoundary W) (φ : W.Iso V)
    {Vertex' Seam' SeamCircle' Facet' Boundary' : Type v}
    (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (eSC : F.SeamCircle ≃ SeamCircle')
    (eF : F.Facet ≃ Facet') (eB : F.Boundary ≃ Boundary') :
    F.IsoOver φ (F.relabelOver φ eV eS eSC eF eB) where
  vertex := eV
  seam := eS
  seamCircle := eSC
  facet := eF
  boundary := eB
  map_chirality v := by simp [relabelOver]
  map_seamEnds := relabel_map_seamEnds F φ eV eS
  map_genus f := by simp [relabelOver]
  map_boundaryFacet b := by simp [relabelOver]
  map_sideBoundary x := by rcases x with ⟨s, i⟩ | e <;> simp [relabelOver]
  map_circleBoundary z := by rcases z with ⟨c, i⟩ | c <;> simp [relabelOver]

section RelabelSimp

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}} (F : FoamWithBoundary W) (φ : W.Iso V)
  {Vertex' Seam' SeamCircle' Facet' Boundary' : Type v}
  (eV : F.Vertex ≃ Vertex') (eS : F.Seam ≃ Seam') (eSC : F.SeamCircle ≃ SeamCircle')
  (eF : F.Facet ≃ Facet') (eB : F.Boundary ≃ Boundary')

@[simp] theorem relabelOverIso_vertex : (F.relabelOverIso φ eV eS eSC eF eB).vertex = eV := (rfl)
@[simp] theorem relabelOverIso_seam : (F.relabelOverIso φ eV eS eSC eF eB).seam = eS := (rfl)
@[simp] theorem relabelOverIso_seamCircle :
    (F.relabelOverIso φ eV eS eSC eF eB).seamCircle = eSC := (rfl)
@[simp] theorem relabelOverIso_facet : (F.relabelOverIso φ eV eS eSC eF eB).facet = eF := (rfl)
@[simp] theorem relabelOverIso_boundary :
    (F.relabelOverIso φ eV eS eSC eF eB).boundary = eB := (rfl)

end RelabelSimp

/-- Transport a prefoam `F : FoamWithBoundary W` along a boundary web isomorphism `φ : W.Iso V`
within the same universe. -/
abbrev mapBoundary {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V) :
    FoamWithBoundary V :=
  F.relabelOver φ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

/-- Canonical isomorphism `F.IsoOver φ (F.mapBoundary φ)`. -/
def mapBoundaryIso {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V) :
    F.IsoOver φ (F.mapBoundary φ) :=
  F.relabelOverIso φ (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

section MapBoundarySimp
variable {W V : ClosedWeb.{u}} (F : FoamWithBoundary W) (φ : W.Iso V)
@[simp] theorem mapBoundaryIso_vertex : (F.mapBoundaryIso φ).vertex = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_seam : (F.mapBoundaryIso φ).seam = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_seamCircle : (F.mapBoundaryIso φ).seamCircle = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_facet : (F.mapBoundaryIso φ).facet = Equiv.refl _ := (rfl)
@[simp] theorem mapBoundaryIso_boundary : (F.mapBoundaryIso φ).boundary = Equiv.refl _ := (rfl)
end MapBoundarySimp

end Relabel

/-- The empty closed prefoam. -/
abbrev empty : ClosedFoam.{u} where
  Vertex := PEmpty
  Seam := PEmpty
  SeamCircle := PEmpty
  Facet := PEmpty
  Boundary := PEmpty
  chirality := PEmpty.elim
  seamEnds := Equiv.equivOfIsEmpty _ _
  seamEnds_inl_snd v := v.elim
  seamEnds_inr_snd w := w.elim
  genus := PEmpty.elim
  boundaryFacet := PEmpty.elim
  sideBoundary := isEmptyElim
  circleBoundary := isEmptyElim
  sideBoundary_eq_iff x := isEmptyElim x
  circleBoundary_injective z := isEmptyElim z
  sideBoundary_ne_circleBoundary x := isEmptyElim x
  boundary_surjective b := b.elim

@[simp] theorem isNilvalent_empty : (empty.{u}).IsNilvalent := by
  rw [isNilvalent_def]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end FoamWithBoundary

end TauCeti
